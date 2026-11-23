import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdmissibleOfPlaces

open Finset NumberField
open scoped ComplexConjugate ComplexOrder

namespace Formalism.FourierDecayAlt.P.PBA

open Formalism.FourierDecayAlt

noncomputable section

theorem pair_prob {W : Type} {s t : Finset W} {a b : W → ℝ} (ha : TB.IsProb s a) (hb : TB.IsProb t b) :
    TB.IsProb (s ×ˢ t) (fun x => a x.1 * b x.2) := by
  refine ⟨fun x => mul_nonneg (ha.1 _) (hb.1 _), fun x hx => ?_, ?_⟩
  · rw [Finset.mem_product, not_and_or] at hx
    rcases hx with h | h
    · simp [ha.2.1 _ h]
    · simp [hb.2.1 _ h]
  · rw [Finset.sum_product]
    simp_rw [← Finset.mul_sum, hb.2.2, mul_one]
    exact ha.2.2

theorem sum_pair {W : Type} (s t : Finset W) (a b f g : W → ℝ) (hb : ∑ y ∈ t, b y = 1)
    (ha : ∑ x ∈ s, a x = 1) :
    ∑ x ∈ s ×ˢ t, a x.1 * b x.2 * ((f x.1 + g x.2) / 2) =
      ((∑ x ∈ s, a x * f x) + ∑ y ∈ t, b y * g y) / 2 := by
  have key : ∀ x, ∑ y ∈ t, a x * b y * ((f x + g y) / 2) =
      (a x * f x + a x * ∑ y ∈ t, b y * g y) / 2 := by
    intro x
    have split : ∀ y, a x * b y * ((f x + g y) / 2) =
        (a x * f x / 2) * b y + (a x / 2) * (b y * g y) := by
      intro y; ring
    simp_rw [split, Finset.sum_add_distrib, ← Finset.mul_sum, hb]
    ring
  rw [Finset.sum_product]
  simp_rw [key]
  rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.sum_mul, ha]
  ring

theorem mix_sum {X W : Type} (Y : Finset X) (Ws : Finset W) (κ : X → X → ℂ) (c : ℂ) (p : W → ℂ)
    (G : W → X → X → ℂ) :
    ∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * (c * ∑ w ∈ Ws, p w * G w h h') =
      c * ∑ w ∈ Ws, p w * ∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * G w h h' := by
  simp_rw [Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun h' _ => ?_
  ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq)

theorem av_eq (v : Fin S.f) (x : E) : S.base.av v x = ‖S.σ v x‖ := by
  show (S.pl v) x = ‖S.emb v x‖
  rw [← S.hemb v]
  rfl

theorem loc_join (σ : E →+* ℂ) (h : TB.Pt E) (s : ℕ) (t : E) :
    C.loc σ (TB.join h s t) = C.loc σ h ++ [(s, σ t)] := by
  simp only [C.loc, TB.join, List.map_append, List.map_cons, List.map_nil]

theorem ptSize_loc (σ : E →+* ℂ) (h : TB.Pt E) : D.ptSize (C.loc σ h) = TB.level h := by
  simp only [D.ptSize, C.loc, TB.level, List.map_map]
  rfl

theorem sizeAt_nonneg (v : Fin S.f) (a : List C.Letter) : 0 ≤ S.sizeAt v a := by
  unfold C.HidaSetting.sizeAt
  apply List.prod_nonneg
  intro x hx
  obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
  exact abs_nonneg _

theorem gN_psd (hpos : C.ThmPPos S) (v : Fin S.f) {ε : ℝ} (hε : 0 < ε) {i : ℕ} (hi : i ≤ S.G.r + 1) (w0 : S.W)
    (Y : Finset C.LPt) : TB.PSDOn Y (KB.gN S v ε i (w0.1 v)) := by
  have h := hpos v ε hε i hi w0 Y
  unfold TB.PSDOn at h ⊢
  have heq : (Matrix.of fun x y : Y => KB.gN S v ε i (w0.1 v) x y) =
      (((S.sizeAt v (w0.1 v))⁻¹ : ℝ) : ℂ) • Matrix.of fun x y : Y => S.gramLoc v ε i (w0.1 v) x y := by
    ext x y
    simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, KB.gN, div_eq_inv_mul,
      Complex.ofReal_inv]
  rw [heq]
  exact h.smul (Complex.zero_le_real.mpr (inv_nonneg.mpr (sizeAt_nonneg S v _)))

theorem Nst_eq {ε : ℝ} {i : ℕ} (hi : i ≤ S.G.r + 1) (s : ℕ) (w : S.W) (Y : Finset (TB.Pt E))
    (κ : TB.Pt E → TB.Pt E → ℂ) (t t' : E) :
    S.base.Nst ε i s w Y κ t t' = ∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, KB.gN S v ε i (w.1 v)
      (C.loc (S.σ v) h ++ [(s, S.σ v t)]) (C.loc (S.σ v) h' ++ [(s, S.σ v t')]) := by
  have hsz : ((C.Word.size S.P w.1 : ℝ) : ℂ) = ∏ v, ((S.sizeAt v (w.1 v) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_prod]
    rfl
  show (∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * S.gram ε i w.1 (TB.join h s t) (TB.join h' s t')) /
      ((C.Word.size S.P w.1 : ℝ) : ℂ) = _
  simp only [C.HidaSetting.gram, if_pos hi, loc_join, KB.gN, Finset.prod_div_distrib, hsz,
    Finset.sum_div, mul_div_assoc]

end

end Formalism.FourierDecayAlt.P.PBA
