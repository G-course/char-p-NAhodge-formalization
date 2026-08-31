# Characteristic-`p` nonabelian Hodge formalization

This repository is a work-in-progress Lean 4 formalization of foundations
for the Ogus--Vologodsky and Lan--Sheng--Zuo constructions in positive
characteristic.  It uses mathlib's categories of schemes, ringed spaces,
and sheaves of modules.

The repository does **not** currently claim a complete formalization of the
Ogus--Vologodsky equivalence.  The results already proved, and the precise
boundary between proved constructions and conditional interfaces, are
listed below.

## Main results

### 1. Tensor products and internal Hom

The tensor product and internal Hom of sheaves of modules are constructed
as independent foundations, together with the tensor--Hom adjunction

$$
\operatorname{Hom}_{\mathcal O_X}
  (M\otimes_{\mathcal O_X}N,P)
\cong
\operatorname{Hom}_{\mathcal O_X}
  \left(M,\underline{\operatorname{Hom}}_{\mathcal O_X}(N,P)\right).
$$

| Result | Lean entry |
| --- | --- |
| Tensor product of module sheaves and its universal property | `CommRingSheaf.tensorObj`, `CommRingSheaf.tensorHomEquiv` |
| Tensor bifunctor | `CommRingSheaf.tensorBifunctor` |
| Internal Hom module sheaf | `CommRingSheaf.internalHom` |
| Tensor--Hom equivalence | `CommRingSheaf.tensorInternalHomEquiv` |
| Tensor--Hom adjunction | `CommRingSheaf.tensorHomAdjunction` |
| Global sections of internal Hom on an affine scheme | `SchemeTensor.affineInternalHomIso` |
| $\widetilde M\otimes\widetilde N\cong\widetilde{M\otimes_RN}$ | `SchemeTensor.affineTensorIso` |

The affine internal-Hom result is the precise formula

$$
\Gamma\!\left(\operatorname{Spec}R,
  \underline{\operatorname{Hom}}(\widetilde N,P)\right)
\cong
\operatorname{Hom}_R
  \left(N,\Gamma(\operatorname{Spec}R,P)\right).
$$

No claim is made that internal Hom is quasicoherent in general; that is not
a theorem proved by this repository.

### 2. Filtered colimits, inverse image, sheafification, and pullback

The proof that pullback preserves tensor products is organized through the
full chain of filtered-colimit, stalk, inverse-image, extension-of-scalars,
and sheafification comparisons.

| Result | Lean entry |
| --- | --- |
| Tensor products commute with filtered colimits over varying base rings | `FilteredColimitTensor.tensorIso` |
| Stalks commute with tensor products | `StalkTensor.tensorIso` |
| Sheafification commutes naturally with tensor products | `SheafificationTensor.comparisonNatIso` |
| Explicit inverse-image--pushforward adjunction | `InverseImageAdjunction.adjunction` |
| $f^{-1}$ commutes naturally with tensor products | `InverseImageTensor.inverseImageTensorNatIso` |
| Extension-of-scalars--restriction-of-scalars adjunction | `CommRingSheaf.extensionRestrictionPresheafAdjunction` |
| Extension of scalars commutes naturally with tensor products | `CommRingSheaf.extensionTensorPresheafNatIso` |
| Explicit sheaf pullback agrees with mathlib pullback | `RingedSpace.explicitPullbackIso` |
| Explicit sheaf pullback--pushforward adjunction | `RingedSpace.explicitPullbackAdjunction` |
| $f^*$ commutes naturally with tensor products | `RingedSpace.pullbackTensorNatIso` |

The intermediate mathematical statements include

$$
\varinjlim_i(M_i\otimes_{A_i}N_i)
\cong
\left(\varinjlim_iM_i\right)
\otimes_{\varinjlim_iA_i}
\left(\varinjlim_iN_i\right),
$$

$$
(M\otimes_{\mathcal O_X}N)_x
\cong
M_x\otimes_{\mathcal O_{X,x}}N_x,
$$

and

$$
a(P\otimes Q)\cong a(P)\otimes a(Q).
$$

The final natural isomorphism on ringed spaces is

$$
f^*(M\otimes_{\mathcal O_Y}N)
\cong
f^*M\otimes_{\mathcal O_X}f^*N.
$$

### 3. Positive-characteristic geometry and $p$-curvature

The repository also contains a substantial positive-characteristic
differential-algebra foundation.

| Result | Lean entry |
| --- | --- |
| Absolute Frobenius of a characteristic-$p$ scheme | `AlgebraicGeometry.Scheme.absoluteFrobenius` |
| Absolute Frobenius is affine | `AlgebraicGeometry.Scheme.absoluteFrobenius_isAffineHom` |
| The map on functions over an open is $a\mapsto a^p$ | `AlgebraicGeometry.Scheme.absoluteFrobenius_app_apply` |
| Affine-local Frobenius-twist formula for Frobenius pullback | `FrobeniusPullback.restrictedTopIso` |
| Canonical flat connection on Frobenius extension of scalars | `StandardFrobeniusPullback.canonicalConnection` |
| Sectionwise linear $p$-curvature and its sheaf-morphism forms | `pCurvature`, `pCurvatureEndomorphismOn`, `pCurvatureEndomorphism` |
| Additivity in the vector field | `pCurvature_add_vectorField` |
| Frobenius semilinearity $\psi(aD)=a^p\psi(D)$ | `pCurvature_smul_vectorField` |
| Bundled Frobenius-semilinear map | `pCurvatureFrobeniusSemilinear` |
| Jacobson formula | `add_pow_eq_add_pow_add_jacobson` |
| Hochschild scalar formulas | `smul_operator_pow_prime`, `restrictedPowerField_smul` |

For fixed $D$, `pCurvature` is linear in module sections.
`pCurvatureEndomorphismOn` packages the construction as an
$\mathcal O_U$-linear morphism over an arbitrary open $U$;
`pCurvatureEndomorphism` is its global-vector-field version.

### 4. Current state of the LSZ construction

#### Verified algebraic components

- The LSZ word-nilpotence convention: every word of length $p$ in tangent
  contractions acts by zero.
- Joint nilpotence consequences used by truncated exponentials:
  `IsWordNilpotent.linear_joint`.
- The truncated-exponential addition formula:
  `TruncatedExp.exp_add_of_commute_of_jointNilpotent`.
- Inverse identities and the resulting linear automorphism:
  `TruncatedExp.exp_mul_exp_neg_eq_one` and
  `TruncatedExp.moduleEndLinearEquiv`.
- The canonical connection on Frobenius pullback:
  `StandardFrobeniusPullback.canonicalConnection`.
- Once the divided-Frobenius identities are supplied, the LSZ correction
  term satisfies the restriction, Leibniz, flatness, and naturality
  calculations and produces an integrable connection:
  `GlobalDividedFrobeniusData.connection`.
- The corresponding unrestricted functor is packaged as
  `GlobalFrobeniusLift.globalLSZFunctor`.

#### Conditional interfaces

- `Atlas.DescentData.lszFunctor` produces the cover-dependent LSZ functor
  once complete descent data is supplied.
- `Atlas.ComparisonData.natIso` and
  `Atlas.ComparisonData.lszFunctor_choice_independent` prove that supplied
  local comparison identities yield a natural isomorphism between the two
  cover-dependent functors.
- The repository does not yet construct all `DescentData` and
  `ComparisonData` automatically from one $W_2(k)$-lifting and chosen local
  Frobenius liftings.
- An inverse functor and the complete LSZ/Ogus--Vologodsky equivalence have
  not yet been formalized.

## Source layout

All Lean modules live under `LSZ/`.  The main groups are:

- tensor products, internal Hom, and ringed spaces: `SheafTensor`,
  `SheafInternalHom`, `FilteredColimitTensor`, `InverseImage*`,
  `PullbackPresheaf*`, `SheafificationTensor`, and `RingedSpacePullback`;
- schemes and Frobenius: `SchemeTensor`, `SchemeObjects`,
  `AbsoluteFrobenius`, and `FrobeniusPullback`;
- characteristic-$p$ differential geometry: `Geometry`, `VectorFields`,
  `TangentSheaf`, `PCurvature`, and `RestrictedIdentities`;
- LSZ construction and descent: `WittLift`, `AffineFrobenius`,
  `GlobalFunctor`, `CoverFunctor`, `Gauge`, and `ChoiceIndependence`.

`LSZ.lean` is the public aggregate import.

## Building

Install `elan`, then run:

```bash
lake update
lake exe cache get
lake build
```

The Lean version is fixed by `lean-toolchain`, and the mathlib revision is
fixed in `lakefile.toml` and `lake-manifest.json`.

## Verification policy

The source compiles without `sorry`, `admit`, or additional axioms.  GitHub
Actions runs `lake build` on every push and pull request.

## License

Licensed under the Apache License, Version 2.0.  See `LICENSE`.
