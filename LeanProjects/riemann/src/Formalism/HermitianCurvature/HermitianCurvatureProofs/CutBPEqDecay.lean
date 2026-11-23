import Formalism.HermitianCurvature.HermitianCurvatureProofs.Cut_BPEq
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaCongrRight
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutFpmDecay

namespace Formalism.FourierDecayAlt.P.CutBPEq

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TBB Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.CutBP2
open scoped ContDiff

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section clm

variable {k r : ℕ} {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E']
  [NormedSpace ℂ E']

theorem op_clm (Φ : E →L[ℂ] E') (b : Bool) {X : Mat k r} (hX : inLie k r X) {G : Mat k r → E}
    (hG : CkOn ((1 : ℕ) : ℕ∞) (GV k r) G) {g : Mat k r} (hg : g ∈ GV k r) :
    Formalism.FourierDecayAlt.P.B4.op b X (fun h => Φ (G h)) g = Φ (Formalism.FourierDecayAlt.P.B4.op b X G g) := by
  unfold Formalism.FourierDecayAlt.P.B4.op
  have hd : DifferentiableAt ℝ (fun t : ℝ => G (Formalism.FourierDecayAlt.P.B4.cv b X t g)) 0 :=
    Formalism.FourierDecayAlt.P.B4.ckOn_diff 0 b hG hX hg
  exact ((Φ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd.hasDerivAt).deriv

theorem ckOn_clm {m : ℕ∞} (Φ : E →L[ℂ] E') {G : Mat k r → E} (hG : CkOn m (GV k r) G) :
    CkOn m (GV k r) (fun h => Φ (G h)) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hg, hf', heq⟩ := hG g₀ hg₀
  refine ⟨U, fun h => Φ (f' h), hU, hg, ?_, fun g hgU hgV => by show Φ (G g) = Φ (f' g); rw [heq g hgU hgV]⟩
  exact (Φ.restrictScalars ℝ).contDiff.comp_contDiffOn hf'

theorem W_clm (Φ : E →L[ℂ] E') (w : List (Bool × Mat k r)) (hw : Formalism.FourierDecayAlt.P.B4.AllLie w) {G : Mat k r → E}
    (hG : CkOn ((w.length : ℕ) : ℕ∞) (GV k r) G) :
    ∀ g ∈ GV k r, Formalism.FourierDecayAlt.P.B4.W w (fun h => Φ (G h)) g = Φ (Formalism.FourierDecayAlt.P.B4.W w G g) := by
  induction w generalizing G with
  | nil =>
    intro g _
    rfl
  | cons x w ih =>
    intro g hg
    have hx : inLie k r x.2 := hw x List.mem_cons_self
    have hw' : Formalism.FourierDecayAlt.P.B4.AllLie w := fun y hy => hw y (List.mem_cons_of_mem _ hy)
    have hGw : CkOn ((w.length : ℕ) : ℕ∞) (GV k r) G := Formalism.FourierDecayAlt.P.B4.ckOn_mono (by simp) hG
    have hG1 : CkOn ((1 : ℕ) : ℕ∞) (GV k r) (Formalism.FourierDecayAlt.P.B4.W w G) :=
      Formalism.FourierDecayAlt.P.B4.smooth_on_of_word_derivatives w hw' 1 (by simpa [Nat.add_comm] using hG)
    rw [Formalism.FourierDecayAlt.P.B4.W_cons, Formalism.FourierDecayAlt.P.B4.W_cons,
      Formalism.FourierDecayAlt.P.B4.op_congr x.1 hx (fun h hh => ih hw' hGw h hh) g hg]
    exact op_clm Φ x.1 hx hG1 hg

theorem ccle_clm {A c : ℝ} {m : ℕ} (Φ : E →L[ℂ] E') {G : Mat k r → E} (hG : CCle A m G c) :
    CCle A m (fun h => Φ (G h)) (‖Φ‖ * c) := by
  obtain ⟨hk, hb⟩ := hG
  refine ⟨ckOn_clm Φ hk, fun u v hu hv hl g hg => ?_⟩
  have hw : Formalism.FourierDecayAlt.P.B4.AllLie (Formalism.FourierDecayAlt.P.B4.lr u v) :=
    Formalism.FourierDecayAlt.P.SliceLastLevel.allLie_lr' (fun X hX => (hu X hX).1) (fun X hX => (hv X hX).1)
  have hlen : (Formalism.FourierDecayAlt.P.B4.lr u v).length = u.length + v.length := by simp [Formalism.FourierDecayAlt.P.B4.lr]
  have hGk : CkOn (((Formalism.FourierDecayAlt.P.B4.lr u v).length : ℕ) : ℕ∞) (GV k r) G :=
    Formalism.FourierDecayAlt.P.B4.ckOn_mono (by omega) hk
  rw [Formalism.FourierDecayAlt.P.B4.dLR_eq, W_clm Φ _ hw hGk g hg, ← Formalism.FourierDecayAlt.P.B4.dLR_eq]
  have h1 := hb u v hu hv hl g hg
  have hgN : 0 ≤ gN g ^ A := Real.rpow_nonneg (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_pos hg).le _
  calc gN g ^ A * ‖Φ (dLR u v G g)‖ ≤ gN g ^ A * (‖Φ‖ * ‖dLR u v G g‖) :=
        mul_le_mul_of_nonneg_left (Φ.le_opNorm _) hgN
    _ = ‖Φ‖ * (gN g ^ A * ‖dLR u v G g‖) := by ring
    _ ≤ ‖Φ‖ * c := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)

end clm

section sum

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem rw_zero_fnE {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] :
    ∀ v : List (B.Mat k r), B.Rw v (0 : B.Mat k r → E) = 0
  | [] => rfl
  | X :: v => by
    show Formalism.REAL.RdV X (B.Rw v 0) = 0
    rw [rw_zero_fnE v]
    funext g
    simp [Formalism.REAL.RdV]

theorem dLR_zero_fnE {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (v : List (B.Mat k r)) :
    ∀ u : List (B.Mat k r), B.dLR u v (0 : B.Mat k r → E) = 0
  | [] => rw_zero_fnE v
  | X :: u => by
    show B.LdV X (B.dLR u v 0) = 0
    rw [dLR_zero_fnE v u]
    funext g
    simp [B.LdV]

theorem inCC_zero_fnE (A : ℝ) (m : ℕ) : B.InCC A m (0 : B.Mat k r → (Wq →L[ℂ] Wp)) := by
  refine ⟨0, fun g₀ _ => ⟨Set.univ, 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun g _ _ => rfl⟩,
    fun u v _ _ _ g _ => ?_⟩
  rw [dLR_zero_fnE v u]
  simp

theorem inCC_finsum {A : ℝ} {m : ℕ} : ∀ {n : ℕ} (F : Fin n → Mat k r → (Wq →L[ℂ] Wp)),
    (∀ i, InCC A m (F i)) → InCC A m (fun g => ∑ i, F i g)
  | 0, F, _ => by
    have e : (fun g => ∑ i : Fin 0, F i g) = (0 : Mat k r → (Wq →L[ℂ] Wp)) := by funext g; simp
    rw [e]; exact inCC_zero_fnE A m
  | n + 1, F, h => by
    have e : (fun g => ∑ i : Fin (n + 1), F i g) = fun g => F 0 g + ∑ i : Fin n, F i.succ g := by
      funext g; exact Fin.sum_univ_succ _
    rw [e]
    obtain ⟨c₁, h₁⟩ := h 0
    obtain ⟨c₂, h₂⟩ := inCC_finsum (fun i : Fin n => F i.succ) (fun i => h i.succ)
    exact ⟨c₁ + c₂, Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_add h₁ h₂⟩

end sum

theorem shifted_decay : FpmShDecay := by
  intro P Wp Wq Wq' _ _ _ _ _ _ _ _ _ u u' q f A A₀ d p₀ hf hA m
  obtain ⟨n, c, L, hc, hAe⟩ := hA
  set Gp : B.Mat P.k P.r → ℂ := fun g => ((Gf P.k P.r q.T.base.z q.T.base.z' g ^ p₀ : ℝ) : ℂ) with hGp
  have e : fpmSh q f A p₀ = fun g => ∑ i, (Gp g * c i g) • (f g).comp (L i) := by
    funext g
    ext v
    simp [fpmSh, hAe g, map_sum, map_smul, Finset.smul_sum, smul_smul, hGp]
  rw [e]
  refine inCC_finsum _ fun i => ?_
  set Φ : (Wq →L[ℂ] Wp) →L[ℂ] (Wq' →L[ℂ] Wp) := (ContinuousLinearMap.compL ℂ Wq' Wq Wp).flip (L i)
  have hΦ : ∀ x, Φ x = x.comp (L i) := fun x => rfl
  have hgood : Formalism.FourierDecayAlt.P.JCx2.pdGood Wp Wq' ((2 * P.r + 2) * p₀ + d) (fun g => Gp g * c i g) :=
    Formalism.FourierDecayAlt.P.JCx2.pd_good_mul le_rfl (Formalism.FourierDecayAlt.P.CutBP.pd_good_Gpow q.T.base.z q.T.base.z' p₀)
      (Formalism.FourierDecayAlt.P.CutBP.pd_good_of_poly (hc i))
  obtain ⟨K, -, hK⟩ := hgood.2 (A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - d) m
  obtain ⟨b, hb⟩ := hf m
  have hb' := ccle_clm Φ hb
  have hA' : A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - d + (((2 * P.r + 2) * p₀ + d : ℕ) : ℝ) = A₀ := by
    push_cast; ring
  rw [← hA'] at hb'
  exact ⟨K * (‖Φ‖ * b), hK _ _ hb'⟩

end

end Formalism.FourierDecayAlt.P.CutBPEq
