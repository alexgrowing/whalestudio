import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj nonZeroDivisors

namespace GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree

section Adelic

variable {L : Type} [Field L] [NumberField L]

def adDeg (r : HeightOneSpectrum (𝓞 L) → ℝ) (N : (L →+* ℂ) → ℝ) : ℝ :=
  (∑ᶠ 𝔭, r 𝔭 * Real.log (Ideal.absNorm 𝔭.asIdeal) - (1 / 2) * ∑ σ, Real.log (N σ)) / Module.finrank ℚ L

example : adDeg (L := L) 0 1 = 0 := by simp [adDeg]

example : adDeg (L := L) 0 (fun _ => 4) = -Real.log 2 := by
  have h : (Module.finrank ℚ L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  simp only [adDeg, Pi.zero_apply, zero_mul, finsum_zero, Finset.sum_const, Finset.card_univ,
    NumberField.Embeddings.card, nsmul_eq_mul, h4]
  field_simp
  ring

end Adelic

section Eigen

variable {R O : Type} [CommRing R] [CommRing O] {G : Over (Sp R)} [GrpObj G]

def IsEigVec (act : OAct O G) (χ : O →+* R) (v : epsR R ⟶ G) : Prop :=
  IsTangent v ∧ ∀ a, (v ≫ act.act a).left = spMap (epsScaleR (χ a)) ≫ v.left

def IsEigBasis (act : OAct O G) (χ : O →+* R) {m : ℕ} (v : Fin m → (epsR R ⟶ G)) : Prop :=
  (∀ i, IsEigVec act χ (v i)) ∧ ∀ w, IsEigVec act χ w → ∃! c : Fin m → R, IsLieComb c v w

end Eigen

section Local

variable {L : Type} [Field L] [NumberField L] (A : Over (Sp L)) [GrpObj A] {m : ℕ}

def IsLocOrd (v : Fin m → (epsR L ⟶ A)) (𝔭 : HeightOneSpectrum (𝓞 L)) (r : ℝ) : Prop :=
  ∃ (V K' : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K') (_ : Algebra V K')
    (_ : IsFractionRing V K') (em : L →+* K') (e : ℕ)
    (G : Over (Sp V)) (_ : GrpObj G) (A' : Over (Sp K')) (_ : GrpObj A')
    (φG : A'.left ⟶ G.left) (φA : A'.left ⟶ A.left)
    (v' : Fin m → (epsR K' ⟶ A')) (u : Fin m → (epsR V ⟶ G)) (u' : Fin m → (epsR K' ⟶ A'))
    (M : Matrix (Fin m) (Fin m) K') (n : ℤ),
    0 < e ∧ (∀ x : L, (IsDiscreteValuationRing.maximalIdeal V).valuation K' (em x) = 𝔭.valuation L x ^ e) ∧
    IsSemiAbelian G ∧ IsGrpPullback A' G (spMap (algebraMap V K')) φG ∧ IsGrpPullback A' A (spMap em) φA ∧
    (∀ i, IsVecOver em φA (v i) (v' i)) ∧
    (∀ k, IsTangent (u k) ∧ IsVecOver (algebraMap V K') φG (u k) (u' k) ∧
      ∃ c : Fin m → K', IsLieComb c v' (u' k)) ∧
    (∀ (w : epsR V ⟶ G) (w' : epsR K' ⟶ A'), IsTangent w → IsVecOver (algebraMap V K') φG w w' →
      (∃ c : Fin m → K', IsLieComb c v' w') → ∃! a : Fin m → V, IsLieComb a u w) ∧
    (∀ i, IsLieComb (M i) u' (v' i)) ∧
    (IsDiscreteValuationRing.maximalIdeal V).valuation K' M.det = WithZero.exp (-n) ∧ r = (n : ℝ) / e

def IsArchSq (𝓛 : LB A.left) (v : Fin m → (epsR L ⟶ A)) (σ : L →+* ℂ) (N : ℝ) : Prop :=
  ∃ (A' : Over (Sp ℂ)) (_ : GrpObj A') (φ : A'.left ⟶ A.left) (g : ℕ) (u : HolUnif A' (𝓛.pull φ) g)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) (v' : Fin m → (epsR ℂ ⟶ A')) (W : Fin m → Fin g → ℂ),
    IsGrpPullback A' A (spMap σ) φ ∧ u.IsAH Hm χ ∧ (∀ i, IsVecOver σ φ (v i) (v' i) ∧ u.IsDiff (W i) (v' i)) ∧
    0 < N ∧ (N : ℂ) = (Matrix.of fun i k => (Real.pi : ℂ) * (W i ⬝ᵥ Hm.mulVec (star (W k)))).det

end Local

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

section Lines

variable {L : Type} [Field L] [NumberField L]

def IsEigLine (t : SAB H (Sp L)) (τ : E →+* L) (m : ℕ) (r : HeightOneSpectrum (𝓞 L) → ℝ) (N : (L →+* ℂ) → ℝ) : Prop :=
  ∃ v : Fin m → (epsR L ⟶ t.G), IsEigBasis t.act (τ.comp (algebraMap (𝓞 E) E)) v ∧
    (∀ 𝔭, IsLocOrd t.G v 𝔭 (r 𝔭)) ∧ (∀ σ, IsArchSq t.G t.PP.L v σ (N σ)) ∧ (Function.support r).Finite

def IsEigDeg (t : SAB H (Sp L)) (τ : E →+* L) (m : ℕ) (δ : ℝ) : Prop :=
  ∃ r N, IsEigLine t τ m r N ∧ δ = adDeg r N

def ordIdeal (τ : E →+* L) (𝔞 : Ideal (𝓞 E)) (𝔭 : HeightOneSpectrum (𝓞 L)) : ℤ :=
  FractionalIdeal.count L 𝔭
    ((𝔞.map (RingOfIntegers.mapRingHom τ) : Ideal (𝓞 L)) : FractionalIdeal (𝓞 L)⁰ L)

def ordTwist (H : Host E) (τ : E →+* L) (𝔭 : HeightOneSpectrum (𝓞 L)) : ℤ :=
  (ordIdeal τ (differentIdeal ℤ (𝓞 E)) 𝔭 - ordIdeal τ (Ideal.span {H.rt}) 𝔭) - ordIdeal τ (Ideal.span {H.rt}) 𝔭

def IsFlatDeg (t : SAB H (Sp L)) (τ τ' : E →+* L) (p q : ℕ) (δ : ℝ) : Prop :=
  ∃ r N r' N', IsEigLine t τ p r N ∧ IsEigLine t τ' q r' N' ∧
    δ = adDeg (fun 𝔭 => r 𝔭 - r' 𝔭 - q * (ordTwist H τ 𝔭 : ℝ)) (fun σ => N σ / N' σ)

end Lines

def embIn {l : Level H} (c : Coeff l) {L : Type} [Field L] (j : c.F →+* L) (τ : E →+* ℂ) : E →+* L :=
  j.comp (τ.codRestrict c.F (c.conj τ))

def cOne (H : Host E) (p q : ℕ) (logOm : ℝ) : ℝ :=
  -(((p : ℝ) - q) / 2 * logOm) - q * (2 * Real.log √(H.d : ℝ) - Real.log (rootDiscr E))

def IsHostField (H : Host E) : Prop :=
  IsAbelianGalois ℚ E ∧
  ∀ w : HeightOneSpectrum (𝓞 E), w.asIdeal ∣ differentIdeal ℤ (𝓞 E) →
    w.asIdeal.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ w.asIdeal ∧
    ∀ ℓ : ℕ, ℓ.Prime → (ℓ : 𝓞 E) ∈ w.asIdeal →
      (ℓ ≠ H.d ∧ IsSquare (-(H.d : ZMod ℓ))) ∨ (ℓ = H.d ∧ ¬ w.asIdeal ^ 3 ∣ Ideal.span {(ℓ : 𝓞 E)})

def AtAllPoints (H : Host E)
    (Q : ∀ (L : Type) [Field L] [NumberField L], SAB H (Sp L) → (E →+* L) → (E →+* L) → ℕ → ℕ → Prop) : Prop :=
  ∀ (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (L : Type) [Field L] [NumberField L] (j : c.F →+* L)
    (y : Sp L ⟶ Xo.XF c), y ≫ pullback.snd _ _ = spMap j →
    ∀ (t : SAB H (Sp L)), Nonempty (SABMap t Xo.univ.t (y ≫ pullback.fst _ _)) →
    ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 → Q L t (embIn c j τ) (embIn c j (conjEmb τ)) D.p D.q

def LinesExist (H : Host E) : Prop :=
  AtAllPoints H fun _ _ _ t τ τ' p q => (∃ r N, IsEigLine t τ p r N) ∧ ∃ r' N', IsEigLine t τ' q r' N'

def LieDegAt (H : Host E) (logOm : ℝ) : Prop :=
  AtAllPoints H fun _ _ _ t τ τ' p q => ∀ δ δ', IsEigDeg t τ p δ → IsEigDeg t τ' q δ' →
    δ - δ' = ((p : ℝ) - q) / 2 * logOm

def FlatDegAt (H : Host E) (logOm : ℝ) : Prop :=
  AtAllPoints H fun _ _ _ t τ τ' p q => ∀ δ, IsFlatDeg t τ τ' p q δ → δ = -cOne H p q logOm

def BoundAt (H : Host E) (logOm : ℝ) : Prop :=
  ∀ p q : ℕ, |cOne H p q logOm + ((p : ℝ) - q) * logOm / 2| ≤ q * Real.log (rootDiscr E)

def DegreeTheorem : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), IsHostField H →
    ∀ [NeZero H.d] (χ : DirichletCharacter ℂ H.d), IsKroneckerChar χ →
      LinesExist H ∧ LieDegAt H (CM.logOm E χ).re ∧ FlatDegAt H (CM.logOm E χ).re ∧ BoundAt H (CM.logOm E χ).re

example (H : Host E) (p : ℕ) (x : ℝ) : cOne H p 0 x = -(p / 2 * x) := by simp [cOne]

example {L : Type} [Field L] [NumberField L] (A : Over (Sp L)) [GrpObj A] (𝓛 : LB A.left)
    (v : Fin 0 → (epsR L ⟶ A)) (σ : L →+* ℂ) (N : ℝ) (h : IsArchSq A 𝓛 v σ N) : N = 1 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, h⟩ := h
  rw [Matrix.det_isEmpty] at h
  exact_mod_cast h

end GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree
