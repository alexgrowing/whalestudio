import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.GRepresents
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.OrbitVanishingLocal

noncomputable section

namespace UpperTheory.V.U3

open Matrix IsLocalRing UpperTheory.V.Alg MvPowerSeries

section Local

variable {O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] {H : Type} [Group H] [TopologicalSpace H]
  {η : H →* ℤˣ} {Ψ : H →* Oˣ} (U : Univ (GCond.noCondition O η Ψ)) (I : Ideal U.R)

def IsBase {Γ R : Type} [Group Γ] [CommRing R] [Algebra O R] (η : Γ →* ℤˣ) (Ψ : Γ →* Oˣ) (r : Γ →* GG 3 R)
    (x : R →ₐ[O] O) : Prop := push x r = r0 η Ψ

def ConjStable : Prop :=
  ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (r r' : GLift O η Ψ R) (h : GL (Fin 3) R),
    CongOne (maximalIdeal R) h → r'.hom = conjBy h r.hom → OnI U I R r → OnI U I R r'

def locDims (j : ℤ) : ℕ :=
  if j = -2 then 1 else if j = -1 then 2 else if j = 0 then 3 else if j = 1 then 4 else if j = 2 then 2 else 0

structure LocChart (x : U.R →ₐ[O] O) {τ : Type} (w : τ → ℤ) (φ : U.R →ₐ[O] MvPowerSeries τ (FractionRing O)) :
    Prop where
  ker : RingHom.ker φ = I
  graded : ∀ g a b, φ ((U.r.hom g).mat a b) ∈ wtPart (FractionRing O) w (wt a b)
  const : ∀ f, constantCoeff (φ f) = algebraMap O (FractionRing O) (x f)
  onto : ∀ i, ∃ f : U.R, coeff (Finsupp.single i 1) (φ f) ≠ 0 ∧ ∀ i', i' ≠ i → coeff (Finsupp.single i' 1) (φ f) = 0
  inj : ∀ f, x f = 0 → (∀ i, coeff (Finsupp.single i 1) (φ f) = 0) →
    ∃ c : O, c ≠ 0 ∧ c • f ∈ RingHom.ker x ^ 2 ⊔ I

structure LocGood : Prop where
  conj : ConjStable U I
  chart : ∃ (x : U.R →ₐ[O] O) (τ : Type) (_ : Fintype τ) (w : τ → ℤ) (φ : U.R →ₐ[O] MvPowerSeries τ (FractionRing O)),
    IsBase η Ψ U.r.hom x ∧ LocChart U I x w φ ∧ ∀ j, Nat.card {i // w i = j} = locDims j

end Local

section Model

variable {O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] {Γ H : Type} [Group Γ] [TopologicalSpace Γ]
  [Group H] [TopologicalSpace H] {η : Γ →* ℤˣ} {Ψ : Γ →* Oˣ} {N : Set Γ} {ι : H →* Γ} {hι : Continuous ι}
  {U : Univ (GCond.noCondition O (η.comp ι) (Ψ.comp ι))} {I : Ideal U.R} {c g₁ : Γ}

variable (N hι U I c g₁) in

abbrev SRing : Type 1 := Univ (NormCond c g₁ (BoxCond N ι hι U I))

def EntWt {G R Q : Type} [Group G] [CommRing R] [Algebra O R] [AddCommGroup Q] [Module O Q] (r : G →* GG 3 R) (j : ℤ)
    (D : R →ₗ[O] Q) : Prop := ∀ g a b, wt a b ≠ j → D ((r g).mat a b) = 0

structure Model (S : SRing N hι U I c g₁) (K : Type) [NormedField K] [Algebra O K] : Type 1 where
  A : Type
  [cr : CommRing A]
  [al : Algebra O A]
  𝒜 : ℤ → Submodule O A
  [gr : GradedAlgebra 𝒜]
  x : A →ₐ[O] O
  wring : IsWRing 𝒜 x
  r : ℕ
  s : ℕ
  r' : ℕ
  s' : ℕ
  m : ℕ
  Q : Eqns 𝒜 x r s r' s' m
  one_le : 1 ≤ r
  smooth : SmoothPt 𝒜 x (mDims r s r' s' m)
  q : A →ₐ[O] S.R
  ker_q : RingHom.ker q = Q.ideal
  x₀ : S.R →ₐ[O] O
  base : IsBase η Ψ S.r.hom x₀
  x₀_q : x₀.comp q = x
  ent : ∀ g a b, ∃ f ∈ 𝒜 (wt a b), q f = (S.r.hom g).mat a b
  dense : ∀ j, ∀ f ∈ 𝒜 j, ∀ n : ℕ, ∃ y ∈ Submodule.span O (entMon S.r.hom j), q f - y ∈ maximalIdeal S.R ^ n
  pts : M2 𝒜 Q.ideal → ∀ ξ : A →ₐ[O] K, OnS Q.ideal ξ →
    ∃ (t : Kˣ) (f : S.R →ₐ[O] K), IsLocPt f ∧ act 𝒜 (tz t) ξ = f.comp q
  der : M2 𝒜 Q.ideal → ∀ f : S.R →ₐ[O] K, IsLocPt f → ∀ D ∈ PtDer (f.comp q) K, (∀ y ∈ Q.ideal, D y = 0) →
    ∃ F : S.R →ₐ[O] DualNumber K, dualFst F = f ∧ ∀ y, (F (q y)).snd = D y
  lift : ∀ a : O, a ≠ 0 → ∀ D ∈ PtDer x₀ (O ⧸ Ideal.span {a}), EntWt S.r.hom (-1) D →
    ∀ xl : U.R →ₐ[O] O, IsBase (η.comp ι) (Ψ.comp ι) U.r.hom xl → ∀ D₁ ∈ PtDer xl O, (∀ y ∈ I, D₁ y = 0) →
    EntWt U.r.hom (-1) D₁ →
    (∀ h a' b', Ideal.Quotient.mk _ (D₁ ((U.r.hom h).mat a' b')) = D ((S.r.hom (ι h)).mat a' b')) →
    ∃ D' ∈ PtDer x O, HasWt 𝒜 (-1) D' ∧ ∀ f, D (q f) = Ideal.Quotient.mk _ (D' f)

attribute [instance] Model.cr Model.al Model.gr

def Model.len {S : SRing N hι U I c g₁} {K : Type} [NormedField K] [Algebra O K] (M : Model S K) : ℕ∞ :=
  cotLen M.x M.𝒜 (-1) M.Q.F

variable (η) in

def TwoPt {R K : Type} [CommRing R] [Algebra O R] [IsLocalRing R] [NormedField K] [Algebra O K] (r : Γ →* GG 3 R)
    (f : R →ₐ[O] K) : Prop := IsLocPt f ∧ ¬ Upper η (push f r) ∧ ¬ Lower η (push f r)

def CoversPt {R K : Type} [CommRing R] [Algebra O R] [IsLocalRing R] [NormedField K] [Algebra O K] (η : Γ →* ℤˣ)
    (r : Γ →* GG 3 R) (T : Finset (R →ₐ[O] K)) : Prop :=
  (∀ f ∈ T, TwoPt η r f) ∧ ∀ f : R →ₐ[O] K, TwoPt η r f → ∃ f' ∈ T, ∃ t : Kˣ, push f r = conjBy (tor K t) (push f' r)

def trDiff {R K : Type} [CommRing R] [Algebra O R] [CommRing K] [Algebra O K] (η : Γ →* ℤˣ) (Ψ : Γ →* Oˣ)
    (r : Γ →* GG 3 R) (σ : Γ) (f : R →ₐ[O] K) : K :=
  f (r σ).mat.trace - algebraMap O K (r0 η Ψ σ).mat.trace

variable (η Ψ N ι c g₁) in

def shaCoc (a : O) : Set (Γ → Matrix (Fin 3) (Fin 3) (O ⧸ Ideal.span {a})) :=
  {γ | IsLocallyConstant γ ∧ (∀ g, γ g ∈ gw _ (-1)) ∧
    IsCoc ((GG.map (Ideal.Quotient.mk (Ideal.span {a}))).comp (r0 η Ψ)) γ ∧
    NormCoc c g₁ ((GG.map (Ideal.Quotient.mk (Ideal.span {a}))).comp (r0 η Ψ)) γ ∧ (∀ g ∈ N, γ g = 0) ∧
    ∃ X ∈ gw (O ⧸ Ideal.span {a}) (-1), ∀ h,
      γ (ι h) = cob ((GG.map (Ideal.Quotient.mk (Ideal.span {a}))).comp (r0 η Ψ)) X (ι h)}

end Model

end UpperTheory.V.U3
