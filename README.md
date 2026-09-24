# Characteristic-`p` nonabelian Hodge formalization

This repository is a work-in-progress Lean 4 formalization of foundations
for the Ogus--Vologodsky and Lan--Sheng--Zuo constructions in positive
characteristic. It uses mathlib's categories of schemes, ringed spaces, and
sheaves of modules.

The repository does **not** currently claim a complete formalization of the
Ogus--Vologodsky equivalence. The results already proved, and the precise
boundary between proved constructions and conditional interfaces, are
listed below.

## Main results

### 1. Tensor products and internal Hom

The tensor product and internal Hom of sheaves of modules are constructed
as independent foundations, together with the tensor--Hom adjunction

$$
\mathrm{Hom}_{\mathcal O_X}
  (M\otimes_{\mathcal O_X}N,P)
\cong
\mathrm{Hom}_{\mathcal O_X}
  \left(M,\underline{\mathrm{Hom}}_{\mathcal O_X}(N,P)\right).
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
\Gamma\!\left(\mathrm{Spec}R,
  \underline{\mathrm{Hom}}(\widetilde N,P)\right)
\cong
\mathrm{Hom}_R
  \left(N,\Gamma(\mathrm{Spec}R,P)\right).
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
| A smooth $W_2(k)$-lift with its actual special-fibre identification | `SmoothScheme.W₂Lift` |
| A geometric Frobenius lift reducing to absolute Frobenius | `SmoothScheme.FrobeniusLift` |
| The induced special-fibre morphism, constructed by the pullback universal property | `SmoothScheme.FrobeniusLift.specialFiberMap` |
| A lifted Frobenius fixes the underlying topological space | `SmoothScheme.FrobeniusLift.liftFrob_apply` |
| Same-open endomorphism of the lifted structure presheaf | `SmoothScheme.FrobeniusLift.presheafEnd` |
| The special fibre and its $W_2(k)$-lift have homeomorphic underlying spaces | `SmoothScheme.W₂Lift.specialFiberHomeomorph` |
| Affine opens of the lift induce an affine cover of $X$ | `SmoothScheme.W₂Lift.affineOpen_cover` |
| Smooth affine $W_2(k)$-algebras extracted from the lift | `SmoothScheme.FrobeniusLift.affineRing`, `affineSmooth` |
| Frobenius maps on those affine algebras are Witt-Frobenius semilinear | `SmoothScheme.FrobeniusLift.affineMap_base` |
| Affine-local Frobenius-twist formula for Frobenius pullback | `FrobeniusPullback.restrictedTopIso` |
| Absolute-Frobenius pullback preserves quasicoherence | `FrobeniusPullback.carrier_isQuasicoherent` |
| Objectwise Frobenius extension followed by sheafification equals mathlib pullback | `SmoothScheme.directFrobeniusPullbackIso` |
| Canonical flat connection on Frobenius extension of scalars | `StandardFrobeniusPullback.canonicalConnection` |
| Restriction-compatible canonical derivative on the direct Frobenius-pullback presheaf | `SmoothScheme.directCanonicalNablaAdd_naturality` |
| Sheafified canonical derivative, with scalar-linearity, Leibniz, and flatness | `SmoothScheme.directCanonicalSheafNabla`, `directCanonicalSheafNabla_smul_vectorField`, `directCanonicalSheafNabla_leibniz`, `directCanonicalSheafNabla_flat` |
| Bundled quasicoherent module with its canonical flat connection | `SmoothScheme.directCanonicalConnection` |
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

`StandardFrobeniusPullback` works directly on mathlib's
`ModuleCat.extendScalars (algebraFrobenius k A p)`.  The canonical
connection is constructed from the tensor-product universal property on
that object; there is no second Frobenius-pullback tensor model and no
comparison isomorphism used to transport the connection.

For a smooth scheme, `directFrobeniusPullbackPresheaf` applies this same
mathlib extension-of-scalars object on every open.  Its sheafification is
naturally isomorphic to `Scheme.Modules.pullback` by
`directFrobeniusPullbackIso`.  The canonical derivative is defined on this
direct presentation and is proved compatible with restriction before
sheafification.  It then descends to `directCanonicalSheafNabla`; its
scalar-linearity in vector fields, Leibniz identity, and flatness are proved
on the resulting sheaf, and `directCanonicalConnection` packages the
quasicoherent Frobenius pullback with this connection.

### 4. Current state of the LSZ construction

#### Genuine affine Frobenius-lift construction

Fix a perfect field $k$ of characteristic $p$, a smooth $W_2(k)$-algebra
$B$, and a Frobenius lift $\Phi:B\to B$. Write

$$
A=k\otimes_{W_2(k)}B.
$$

The repository now constructs the divided differential and its dual from
$\Phi$ itself; they are not additional inputs. For every unrestricted
integrable Higgs module on $A$, it then constructs

$$
\nabla=\nabla^{\mathrm{can}}+F^*\theta\circ\zeta
$$

as an integrable connection and packages the construction as a functor.

| Result | Lean entry |
| --- | --- |
| Divided differential on the special fibre from the actual lift | `AffineWittLift.Frobenius.specialFiberDividedDifferential` |
| Dual divided Frobenius $\zeta:T_A\to F_A^*T_A$ | `AffineWittLift.Frobenius.dividedFrobeniusZeta` |
| Closedness of $\zeta$ | `AffineWittLift.Frobenius.dividedFrobeniusZeta_closed` |
| Packaged divided-differential datum | `AffineWittLift.Frobenius.dividedDifferentialData` |
| Resulting integrable connection | `AffineWittLift.Frobenius.connection` |
| Resulting affine LSZ functor | `AffineWittLift.Frobenius.functor` |
| Strongly nilpotent Higgs and flat categories | `AffineObject.NilpotentHiggs`, `AffineObject.NilpotentFlat` |
| LSZ functor between the strongly nilpotent categories | `AffineWittLift.Frobenius.nilpotentFunctor` |
| Underlying module is Frobenius extension of scalars | `AffineWittLift.Frobenius.connection_carrier` |
| Frobenius extension preserves finite generation and projectivity | `AffineFrobeniusLift.pullback_finite`, `AffineFrobeniusLift.pullback_projective` |
| Explicit connection formula | `AffineWittLift.Frobenius.connection_nabla_apply` |
| Comparison with the general affine p-curvature construction | `AffineWittLift.Frobenius.pCurvature_eq_affine` |

The same affine input is also compared with the geometric lifting data; the
special-fibre morphism is constructed and its reduction to absolute
Frobenius is proved rather than assumed:

| Result | Lean entry |
| --- | --- |
| Smooth affine special fibre $\mathrm{Spec}(k\otimes_{W_2(k)}B)$ | `AffineWittLift.specialFiberSmoothScheme` |
| Its geometric $W_2(k)$-lift | `AffineWittLift.toSchemeW₂Lift` |
| Explicit map on the pullback special fibre | `AffineWittLift.Frobenius.specialFiberMap` |
| Comparison with the tensor-product $p$-power Frobenius | `AffineWittLift.Frobenius.pullbackSpecIso_conjugation` |
| Reduction is the absolute Frobenius | `AffineWittLift.Frobenius.specialFiberMap_reduction` |
| Resulting genuine scheme-theoretic Frobenius lift | `AffineWittLift.Frobenius.toSchemeFrobeniusLift` |

The nilpotence convention is the strong LSZ convention: every composite of
$p$ arbitrary Higgs contractions vanishes. This property is proved to
survive Frobenius extension of scalars for arbitrary pulled tangent vectors:

| Result | Lean entry |
| --- | --- |
| Strong nilpotence of the full pulled Higgs action | `AffineFrobeniusLift.pulledAction_wordNilpotent` |
| P-curvature as the Higgs action on the Cartier defect | `AffineFrobeniusLift.pCurvature_eq_pulledAction_cartierDefect` |
| Strong nilpotence of p-curvature for any divided differential | `AffineFrobeniusLift.pCurvature_wordNilpotent` |
| Strong nilpotence for the connection from the actual lift | `AffineWittLift.Frobenius.pCurvature_wordNilpotent` |

Thus the last theorem states that every word of length $p$ in arbitrary
p-curvature contractions of the constructed connection is zero. The proof
does not replace this condition by the weaker assertion $\psi(D)^p=0$ for
one fixed vector field.

Finite-projective duals under base change, needed to transpose the divided
cotangent map, are handled by `FiniteProjectiveDualBaseChange.equiv`.

For a genuine geometric $W_2(k)$-lift, no affine covering is supplied as
extra input.  The special-fibre projection is proved to be a surjective
closed immersion, hence a homeomorphism.  The affine opens of the lift
therefore induce the canonical affine cover
`SmoothScheme.W₂Lift.affineOpen_cover` of $X$.  On each such open,
`SmoothScheme.FrobeniusLift.affineRing` is proved to be a smooth
$W_2(k)$-algebra, and the same-open map induced by the lifted Frobenius is
proved semilinear for Witt Frobenius by
`SmoothScheme.FrobeniusLift.affineMap_base`.

On an arbitrary smooth separated positive-characteristic scheme, the
strong word-nilpotent object categories themselves use the canonical
vector fields constructed from the scheme:
`SmoothScheme.NilpotentHiggs` and `SmoothScheme.NilpotentFlat`.  In
particular, these definitions do not ask the caller to provide a tangent
sheaf or a restricted-power operation.

#### Other verified algebraic components

- Joint nilpotence consequences used by truncated exponentials:
  `IsWordNilpotent.linear_joint`.
- The truncated-exponential addition formula:
  `TruncatedExp.exp_add_of_commute_of_jointNilpotent`.
- Inverse identities and the resulting linear automorphism:
  `TruncatedExp.exp_mul_exp_neg_eq_one` and
  `TruncatedExp.moduleEndLinearEquiv`.
- The conditional global formula produces an integrable connection once
  scheme-level divided-Frobenius data is supplied:
  `GlobalDividedFrobeniusData.connection`.
- The corresponding conditional unrestricted functor is
  `GlobalFrobeniusLift.globalLSZFunctor`.

#### Conditional global and descent interfaces

- `Atlas.DescentData.lszFunctor` produces the cover-dependent LSZ functor
  once complete descent data is supplied.
- `Atlas.ComparisonData.natIso` and
  `Atlas.ComparisonData.lszFunctor_choice_independent` prove that supplied
  local comparison identities yield a natural isomorphism between two
  cover-dependent functors.
- The genuine construction above is currently affine. The repository does
  not yet prove the remaining special-fibre comparison and localization
  compatibilities needed to glue the newly extracted affine maps into a
  scheme-level LSZ functor. It also does not yet construct all
  `GlobalDividedFrobeniusData`, `DescentData`, and `ComparisonData`
  automatically from one $W_2(k)$-lift and chosen local Frobenius liftings.
- An inverse functor and the complete LSZ/Ogus--Vologodsky equivalence have
  not yet been formalized.

## Source layout

All Lean modules live under `LSZ/`. The main groups are:

- tensor products, internal Hom, and ringed spaces: `SheafTensor`,
  `SheafInternalHom`, `FilteredColimitTensor`, `InverseImage*`,
  `PullbackPresheaf*`, `SheafificationTensor`, and `RingedSpacePullback`;
- schemes and Frobenius: `SchemeTensor`, `SchemeObjects`,
  `AbsoluteFrobenius`, `FrobeniusPullback`, `DirectFrobeniusPullback`,
  `GeometricWittLift`, and `GeometricFrobeniusLift`;
- characteristic-$p$ differential geometry: `Geometry`, `VectorFields`,
  `TangentSheaf`, `PCurvature`, `GeometricCanonicalConnection`,
  `GeometricNilpotentObjects`, and `RestrictedIdentities`;
- genuine affine Frobenius-lift construction and its geometric comparison:
  `AffineWittLift`, `GeometricWittLift`, `AffineWittScheme`,
  `FiniteProjectiveDualBaseChange`, and `AffineWittLSZ`;
- LSZ global and descent interfaces: `WittLift`, `AffineFrobenius`,
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

The source compiles without `sorry`, `admit`, or additional axioms. GitHub
Actions runs `lake build` on every push and pull request.

## License

Licensed under the Apache License, Version 2.0. See `LICENSE`.
