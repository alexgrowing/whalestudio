import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianSquareIntegrableAll
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevTransportHer

open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerD

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC

section Shift

def shIdx {r : ℕ} (i : Fin (r + 1)) : {l : Fin (r - i) // (0 : Fin (r - i + 1)).val ≤ l.val} ≃ {l : Fin r // i.val ≤ l.val} where
  toFun l := ⟨⟨l.1.val + i.val, by have := l.1.isLt; have := i.isLt; omega⟩, Nat.le_add_left _ _⟩
  invFun l := ⟨⟨l.1.val - i.val, by have := l.1.isLt; have := l.2; omega⟩, Nat.zero_le _⟩
  left_inv l := by
    apply Subtype.ext; apply Fin.ext
    show l.1.val + i.val - i.val = l.1.val
    omega
  right_inv l := by
    apply Subtype.ext; apply Fin.ext
    show l.1.val - i.val + i.val = l.1.val
    have := l.2; omega

def shEq {r : ℕ} (i : Fin (r + 1)) : Cf (r - i) 0 ≃ᵐ Cf r i :=
  MeasurableEquiv.piCongrLeft (fun _ => ℂ) (shIdx i)

theorem shEq_mp {r : ℕ} (i : Fin (r + 1)) : MeasurePreserving (shEq i) volume volume :=
  volume_measurePreserving_piCongrLeft (fun _ => ℂ) (shIdx i)

theorem shEq_apply {r : ℕ} (i : Fin (r + 1)) (c' : Cf (r - i) 0) (l : {l : Fin r // i.val ≤ l.val}) :
    shEq i c' l = c' ((shIdx i).symm l) := by
  unfold shEq
  rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
  rfl

theorem shiftCf_glue {r : ℕ} (i : Fin (r + 1)) (c'' : Fin (r - i) → ℂ) (c' : Cf (r - i) 0) :
    Formalism.FourierDecayAlt.P.PTie.shiftCf i (glue 0 c'' c') = shEq i c' := by
  funext l
  rw [shEq_apply]
  simp [Formalism.FourierDecayAlt.P.PTie.shiftCf, shIdx]
  rfl

theorem wtI_shEq {r : ℕ} (i : Fin (r + 1)) (c' : Cf (r - i) 0) : wtI i (shEq i c') = wtI 0 c' := by
  unfold wtI
  congr 1
  simp_rw [shEq_apply]
  exact Fintype.prod_equiv (shIdx i).symm _ _ fun l => rfl

end Shift

section Transfer

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem level_square_integrable_of_transport {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    {π' : Mx k r → (Wq →L[ℂ] Wq)} (μ : Measure (Mt k r)) (i : Fin (r + 1)) (c : Fin r → ℂ)
    {zi zi' : Fin (2 * (r - i) + k + 1) → ℂ} {πi : Mx k (r - i) → (Wp →L[ℂ] Wp)} {πi' : Mx k (r - i) → (Wq →L[ℂ] Wq)}
    (μi : Measure (Mt k (r - i))) (T : RadSp k r z z' π π' →ₗ[ℂ] RadSp k (r - i) zi zi' πi πi') (κ : ℝ) (hκ : 0 < κ)
    (hT : ∀ Φ Ψ c'', pairAt μi (T Φ) (T Ψ) c'' = (κ : ℂ) * pairAt μ Φ Ψ (glue i c (Formalism.FourierDecayAlt.P.PTie.shiftCf i c'')))
    (v : RadSp k r z z' π π') (c'' : Fin (r - i) → ℂ) (h : LevelSquareIntegrable μi 0 (T v) c'') : LevelSquareIntegrable μ i v c := by
  unfold LevelSquareIntegrable at h ⊢
  have e : (fun c' : Cf r i => wtI i c' * pairAt μ v v (glue i c c')) ∘ (shEq i) =
      fun c' => (κ : ℂ)⁻¹ * (wtI 0 c' * pairAt μi (T v) (T v) (glue 0 c'' c')) := by
    funext c'
    simp only [Function.comp_apply]
    rw [hT, shiftCf_glue, wtI_shEq]
    have : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
    field_simp
  have h2 := h.const_mul ((κ : ℂ)⁻¹)
  rw [← e] at h2
  exact ((shEq_mp i).integrable_comp_emb (shEq i).measurableEmbedding).mp h2

end Transfer

section Lev

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def HermitianSquareIntegrableLevelZero : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    HermitianSquareIntegrableAt (S := S) P z z' π π' μ L st l0 D 0

theorem act_tr {k r k' r' : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    {π' : Mx k r → (Wq →L[ℂ] Wq)} {zi zi' : Fin (2 * r' + k' + 1) → ℂ} {πi : Mx k' r' → (Wp →L[ℂ] Wp)}
    {πi' : Mx k' r' → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]
    (T : RadSp k r z z' π π' →ₗ[ℂ] RadSp k' r' zi zi' πi πi') {M : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))}
    {M' : SlopeTestRemainingChoices S (Pr (RadSp k' r' zi zi' πi πi'))} (h : Formalism.FourierDecayAlt.P.PBH.ARel T M M')
    (x : Ix S → RadSp k r z z' π π') (a : Ix S) : T (act M x a) = act M' (fun b => T (x b)) a := by
  unfold act
  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  have := congrArg (fun f => f (x b)) (h a b).1
  simpa using this.symm

end Lev

end Formalism.FourierDecayAlt.P5.HerD
