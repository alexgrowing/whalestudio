import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatHomOfGAdSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAHaarUnfoldingMeasure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentCoordinatesInverse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalClosedBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHyperbolicPlaneRestrictedForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalCoordinateHomeomorph
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.IwStabCoord

open Matrix GlobalTheory.ThK.UnipDom

theorem frame_mulVec_expand {A : Type} [CommRing A] {b : ℕ} (x y : Fin (b + 2) → A) (ι : Matrix (Fin (b + 2)) (Fin b) A)
    (w : Fin b ⊕ Fin 2 → A) :
    GlobalTheory.IwEmb.frame x y ι *ᵥ w = ι *ᵥ (fun i => w (Sum.inl i)) + w (Sum.inr 0) • x + w (Sum.inr 1) • y := by
  ext i
  simp [GlobalTheory.IwEmb.frame, GlobalTheory.LeviElem.cols2, mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two]
  ring

set_option maxHeartbeats 1000000 in

theorem stab_iota : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n n₁ : ℕ) (X Y : Spc F E n) (X₁ : Spc F E n₁) (H : Plane E n n₁) (r s i₀ i₁ : ℕ), B.IsGood σ → X.IsHerm σ B r s → H.IsAdapted σ B (reS X Y) X₁ i₀ i₁ → ∀ p ∈ GlobalTheory.IwLine.lineStab σ X.J H.x, ∃ G : Matrix (Fin n₁) (Fin n₁) (AE F E), ∀ z : Fin n₁ → AE F E, ∃ a : AE F E, mat p *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ (G *ᵥ z) + a • incV F H.x := by
  intro F E _ _ _ _ _ σ B n n₁ X Y X₁ H r s i₀ i₁ hB hX hH p hp
  obtain rfl := hH.rank
  obtain ⟨α, hα⟩ := hp
  have hs : ∀ z : E, σ (σ z) = z := GlobalTheory.ThK.UnipDom.Inverse.sigma_sigma hB.cm
  have hL : Submodule.span E ((reS X Y).L : Set (Fin (n₁ + 2) → E)) = ⊤ := hX.lat.span_eq_top
  choose a b c hdec using fun j : Fin (n₁ + 2) =>
    GlobalTheory.IterBochner.exists_decomp B H (reS X Y) X₁ hH hL (Pi.single j 1)
  set P : Matrix (Fin (n₁ + 2)) (Fin n₁ ⊕ Fin 2) E := GlobalTheory.IwEmb.frame H.x H.y H.ι with hP
  set R : Matrix (Fin n₁ ⊕ Fin 2) (Fin (n₁ + 2)) E :=
    Matrix.of fun k i => Sum.elim (fun t => c i t) (fun t => ![a i, b i] t) k with hR
  have hPR : P * R = 1 := by
    ext i i'
    have e := congrFun (hdec i') i
    rw [Matrix.one_apply]
    rw [Pi.single_apply] at e
    rw [e]
    simp only [hP, hR, GlobalTheory.IwEmb.frame, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.fromCols_apply_inl,
      Matrix.fromCols_apply_inr, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr, GlobalTheory.LeviElem.cols2, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
    ring
  have hRP : R * P = 1 := (Matrix.mul_eq_one_comm_of_equiv finSumFinEquiv.symm).1 hPR
  set f : E →+* AE F E := inclR (F := F) (E := E) (AF F) with hf
  have hPf : P.map f = GlobalTheory.IwEmb.frame (incV F H.x) (incV F H.y) (incM F H.ι) := by
    ext i (k | k)
    · rfl
    · fin_cases k <;> rfl
  have hQP' : R.map f * GlobalTheory.IwEmb.frame (incV F H.x) (incV F H.y) (incM F H.ι) = 1 := by
    rw [← hPf, ← Matrix.map_mul, hRP, Matrix.map_one _ (map_zero f) (map_one f)]
  set Q := R.map f with hQ
  have hFQ := GlobalTheory.IwEmb.frame_mul_Q hQP'
  have hrec : ∀ v, GlobalTheory.IwEmb.frame (incV F H.x) (incV F H.y) (incM F H.ι) *ᵥ (Q *ᵥ v) = v := fun v => by
    rw [mulVec_mulVec, hFQ, one_mulVec]

  have hfyx : form σ X.J H.y H.x = 1 := by
    have e : form σ X.J H.y H.x = σ (form σ X.J H.x H.y) := by
      simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hs, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
      rw [← hX.herm k l, hs]; ring
    rw [e]
    have := hH.xy
    change form σ X.J H.x H.y = 1 at this
    rw [this, map_one]
  have hιx : ∀ z, fA σ X.J (incM F H.ι *ᵥ z) (incV F H.x) = 0 := fun z =>
    GlobalTheory.UnipChart.fA_iota_left (H := H) H.x (fun u => (hH.orth u).1) z
  have hxx : fA σ X.J (incV F H.x) (incV F H.x) = 0 := by
    rw [GlobalTheory.ThK.UnipDom.Inverse.fA_incV]
    have := hH.xx
    change form σ X.J H.x H.x = 0 at this
    rw [this, map_zero]
  have hyx : fA σ X.J (incV F H.y) (incV F H.x) = 1 := by
    rw [GlobalTheory.ThK.UnipDom.Inverse.fA_incV, hfyx, map_one]

  have hcoord : ∀ v, fA σ X.J v (incV F H.x) = (Q *ᵥ v) (Sum.inr 1) := by
    intro v
    have hv : v = GlobalTheory.IwEmb.frame (incV F H.x) (incV F H.y) (incM F H.ι) *ᵥ (Q *ᵥ v) := (hrec v).symm
    conv_lhs => rw [hv, frame_mulVec_expand]
    rw [GlobalTheory.ThK.UnipDom.Inverse.fA_add_left, GlobalTheory.ThK.UnipDom.Inverse.fA_add_left,
      GlobalTheory.ThK.UnipDom.Inverse.fA_smul_left, GlobalTheory.ThK.UnipDom.Inverse.fA_smul_left, hιx, hxx, hyx]
    ring
  refine ⟨GlobalTheory.IwEmb.gam Q (incM F H.ι) (mat p), fun z => ⟨(Q *ᵥ (mat p *ᵥ (incM F H.ι *ᵥ z))) (Sum.inr 0), ?_⟩⟩
  set w := Q *ᵥ (mat p *ᵥ (incM F H.ι *ᵥ z)) with hw
  have hw1 : w (Sum.inr 1) = 0 := by
    rw [hw, ← hcoord]
    have h1 : fA σ X.J (mat p *ᵥ (incM F H.ι *ᵥ z)) (mat p *ᵥ incV F H.x) = 0 := by
      rw [GlobalTheory.ThK.UnipDom.Inverse.fA_mulVec, hιx]
    rw [hα, GlobalTheory.ThK.UnipDom.MatEq.fA_smul_right] at h1
    have hu : IsUnit (cA σ (α : AE F E)) := (α.isUnit).map (cA σ)
    exact (hu.mul_right_eq_zero).1 h1
  have hwι : (fun i => w (Sum.inl i)) = GlobalTheory.IwEmb.gam Q (incM F H.ι) (mat p) *ᵥ z := by
    funext i
    simp only [hw, GlobalTheory.IwEmb.gam, mulVec_mulVec]
    rw [← Matrix.mul_assoc]
    rfl
  calc mat p *ᵥ (incM F H.ι *ᵥ z) = GlobalTheory.IwEmb.frame (incV F H.x) (incV F H.y) (incM F H.ι) *ᵥ w := by
        rw [hw, hrec]
    _ = _ := by rw [frame_mulVec_expand, hw1, hwι, zero_smul, add_zero]

end GlobalTheory.IwStabCoord
