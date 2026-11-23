import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.WordSpans.WordSpan
import Development.WeilBound.CoreStatements.BranchingTraces.ContinuousEmb
import Development.WeilBound.CoreStatements.OrbitDecayEstimates.CurveDerivativeDecay.LipschitzEstimate

noncomputable section

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ComplexConjugate

namespace PositivityTheory.RgHe.SM

open Formalism.REAL Formalism.MainNotions.S PositivityTheory.UnitaryDecomposition Formalism.FourierDecayAlt.P.CapelliAbstractCharacter CompanionTheory.D.DSIC

def wp {V : Type} [AddCommGroup V] [Module ℂ V] {m : ℕ} (E : Fin m → Fin m → Module.End ℂ V) (w : List (Fin m × Fin m)) :
    Module.End ℂ V :=
  (w.map fun p => E p.1 p.2).prod

theorem norm_entry_le {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (i j : Fin m) : ‖M i j‖ ≤ Real.sqrt (hs M) := by
  refine Real.le_sqrt_of_sq_le ?_
  unfold hs
  exact (Finset.single_le_sum (f := fun j => ‖M i j‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (f := fun i => ∑ j, ‖M i j‖ ^ 2) (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity)
      (Finset.mem_univ i))

theorem hs_nonneg' {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) : 0 ≤ hs M :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

theorem um_inv_eq {m : ℕ} {ε : Fin m → Bool} (g : UJ ε) : um g⁻¹ = Jm ε * (um g)ᴴ * Jm ε := by
  have hg : (um g)ᴴ * Jm ε * um g = Jm ε := g.2
  have e : um g * um g⁻¹ = 1 := by
    show ((g : (Matrix (Fin m) (Fin m) ℂ)ˣ) : Matrix (Fin m) (Fin m) ℂ) * (((g⁻¹ : UJ ε) : (Matrix (Fin m) (Fin m) ℂ)ˣ) : Matrix (Fin m) (Fin m) ℂ) = 1
    rw [Subgroup.coe_inv, Units.mul_inv]
  calc um g⁻¹ = Jm ε * Jm ε * um g⁻¹ := by rw [Jm_mul_self, Matrix.one_mul]
    _ = Jm ε * ((um g)ᴴ * Jm ε * um g) * um g⁻¹ := by rw [hg]
    _ = Jm ε * (um g)ᴴ * Jm ε * (um g * um g⁻¹) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [e, Matrix.mul_one]

theorem hs_inv' {m : ℕ} {ε : Fin m → Bool} (g : UJ ε) : hs (um g⁻¹) = hs (um g) := by
  rw [um_inv_eq]
  unfold hs
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply, norm_mul, norm_star]
  split_ifs <;> simp

theorem one_le_hs' {m : ℕ} {ε : Fin m → Bool} (hm : 1 ≤ m) (g : UJ ε) : 1 ≤ hs (um g) := by
  have j : Fin m := ⟨0, hm⟩
  have h := congrArg (fun M => ‖M j j‖) (show (um g)ᴴ * Jm ε * um g = Jm ε from g.2)
  have h1 : ‖Jm ε j j‖ = 1 := by simp only [Jm, Matrix.diagonal_apply_eq]; split_ifs <;> simp
  simp only [h1] at h
  have h2 : 1 ≤ ∑ i, ‖um g i j‖ ^ 2 := by
    rw [← h, Matrix.mul_apply]
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    rw [Jm, Matrix.mul_diagonal, norm_mul, norm_mul, Matrix.conjTranspose_apply, norm_star]
    split_ifs <;> simp [sq]
  exact h2.trans (Finset.sum_le_sum fun i _ =>
    Finset.single_le_sum (f := fun k => ‖um g i k‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j))

section Grow

variable {m : ℕ} {ε : Fin m → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin m) (Fin m) ℂ → (H →L[ℂ] H)} {S : Submodule ℂ H} {E : Fin m → Fin m → Module.End ℂ S}

theorem inv_cancel' (hU : IsURepOn (UJset ε) σ) (g : UJ ε) (y : H) : σ (um g) (σ (um g⁻¹) y) = y := by
  have e : um g * um g⁻¹ = 1 := by
    show ((g : (Matrix (Fin m) (Fin m) ℂ)ˣ) : Matrix (Fin m) (Fin m) ℂ) * (((g⁻¹ : UJ ε) : (Matrix (Fin m) (Fin m) ℂ)ˣ) : Matrix (Fin m) (Fin m) ℂ) = 1
    rw [Subgroup.coe_inv, Units.mul_inv]
  have := hU.1.2 _ g.2 _ (g⁻¹).2
  rw [e, hU.1.1] at this
  exact (DFunLike.congr_fun this y).symm

theorem inv_cancel'' (hU : IsURepOn (UJset ε) σ) (g : UJ ε) (y : H) : σ (um g⁻¹) (σ (um g) y) = y := by
  have := inv_cancel' hU g⁻¹ y
  rwa [inv_inv] at this

theorem um_inv_inv (g : UJ ε) : (um g⁻¹)⁻¹ = um g := by
  rw [← um_inv, inv_inv]

theorem gen_step (hS : IsSmMod ε σ S E) (hU : IsURepOn (UJset ε) σ) (g : UJ ε) (v : S) (a b : Fin m) :
    (E a b ⟨σ (um g) v, hS.stab _ g.2 _ v.2⟩ : H) = ∑ c, ∑ d, (um g⁻¹ c a * um g b d) • σ (um g) (E c d v : H) := by
  have h := hS.conj (um g⁻¹) (g⁻¹).2 a b ⟨σ (um g) v, hS.stab _ g.2 _ v.2⟩ v (inv_cancel'' hU g v).symm
  rw [um_inv_inv] at h
  have h2 := congrArg (σ (um g)) h
  rw [inv_cancel' hU] at h2
  rw [h2, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_sum]
  exact Finset.sum_congr rfl fun d _ => map_smul _ _ _

theorem continuous_um : Continuous fun g : UJ ε => um g := Units.continuous_val.comp continuous_subtype_val

theorem continuous_um_inv : Continuous fun g : UJ ε => um g⁻¹ := continuous_um.comp continuous_inv

theorem word_growth (hS : IsSmMod ε σ S E) (hU : IsURepOn (UJset ε) σ) (w : List (Fin m × Fin m)) :
    ∀ v : S, Continuous (fun g : UJ ε => (wp E w ⟨σ (um g) v, hS.stab _ g.2 _ v.2⟩ : H)) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ g : UJ ε, ‖(wp E w ⟨σ (um g) v, hS.stab _ g.2 _ v.2⟩ : H)‖ ≤ C * hs (um g) ^ w.length := by
  induction w using List.reverseRecOn with
  | nil =>
    intro v
    refine ⟨?_, ‖(v : H)‖, norm_nonneg _, fun g => ?_⟩
    · simp only [wp, List.map_nil, List.prod_nil, Module.End.one_apply]
      exact (hU.2.2 v).comp_continuous continuous_um fun g => g.2
    · simp only [wp, List.map_nil, List.prod_nil, Module.End.one_apply, List.length_nil, pow_zero, mul_one]
      exact le_of_eq (hU.2.1 _ g.2 v)
  | append_singleton w p ih =>
    intro v
    have e1 : ∀ g : UJ ε, (wp E (w ++ [p]) ⟨σ (um g) v, hS.stab _ g.2 _ v.2⟩ : H) =
        ∑ c, ∑ d, (um g⁻¹ c p.1 * um g p.2 d) • (wp E w ⟨σ (um g) (E c d v), hS.stab _ g.2 _ (E c d v).2⟩ : H) := by
      intro g
      have hx : E p.1 p.2 ⟨σ (um g) v, hS.stab _ g.2 _ v.2⟩ =
          ∑ c, ∑ d, (um g⁻¹ c p.1 * um g p.2 d) • (⟨σ (um g) (E c d v), hS.stab _ g.2 _ (E c d v).2⟩ : S) := by
        apply Subtype.ext
        rw [gen_step hS hU g v p.1 p.2, Submodule.coe_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Submodule.coe_sum]
        rfl
      simp only [wp, List.map_append, List.map_cons, List.map_nil, List.prod_append, List.prod_cons, List.prod_nil,
        mul_one, Module.End.mul_apply]
      rw [hx, map_sum, Submodule.coe_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [map_sum, Submodule.coe_sum]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [map_smul, Submodule.coe_smul]
    choose hc C hC0 hC using fun c d => ih (E c d v)
    refine ⟨?_, ∑ c, ∑ d, C c d, Finset.sum_nonneg fun c _ => Finset.sum_nonneg fun d _ => hC0 c d, fun g => ?_⟩
    · simp only [e1]
      refine continuous_finsetSum _ fun c _ => continuous_finsetSum _ fun d _ => ?_
      refine Continuous.smul ?_ (hc c d)
      exact ((continuous_um_inv.matrix_elem c p.1).mul (continuous_um.matrix_elem p.2 d))
    · rw [e1]
      have hg1 : 0 ≤ hs (um g) := hs_nonneg' _
      have hco : ∀ c d, ‖um g⁻¹ c p.1 * um g p.2 d‖ ≤ hs (um g) := fun c d => by
        rw [norm_mul]
        have h1 := norm_entry_le (um g⁻¹) c p.1
        have h2 := norm_entry_le (um g) p.2 d
        rw [hs_inv'] at h1
        calc _ ≤ Real.sqrt (hs (um g)) * Real.sqrt (hs (um g)) :=
              mul_le_mul h1 h2 (norm_nonneg _) (Real.sqrt_nonneg _)
          _ = hs (um g) := Real.mul_self_sqrt hg1
      refine (norm_sum_le _ _).trans ?_
      rw [List.length_append, List.length_singleton, pow_succ, Finset.sum_mul]
      refine Finset.sum_le_sum fun c _ => (norm_sum_le _ _).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun d _ => ?_
      rw [norm_smul]
      calc _ ≤ hs (um g) * (C c d * hs (um g) ^ w.length) :=
            mul_le_mul (hco c d) (hC c d g) (norm_nonneg _) hg1
        _ = _ := by ring

end Grow

section Span

variable {m : ℕ} {ε : Fin m → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin m) (Fin m) ℂ → (H →L[ℂ] H)} {S : Submodule ℂ H} {E : Fin m → Fin m → Module.End ℂ S}

theorem ap_of_mem (T : Module.End ℂ S) {x : H} (hx : x ∈ S) : ap T x = (T ⟨x, hx⟩ : H) := by
  unfold ap; rw [dif_pos hx]

theorem ap_add (T₁ T₂ : Module.End ℂ S) (x : H) : ap (T₁ + T₂) x = ap T₁ x + ap T₂ x := by
  unfold ap; split_ifs <;> simp

theorem ap_smul (c : ℂ) (T : Module.End ℂ S) (x : H) : ap (c • T) x = c • ap T x := by
  unfold ap; split_ifs <;> simp

theorem ap_zero (x : H) : ap (0 : Module.End ℂ S) x = 0 := by
  unfold ap; split_ifs <;> simp

theorem span_growth (hm : 1 ≤ m) (hS : IsSmMod ε σ S E) (hU : IsURepOn (UJset ε) σ) (L : ℕ) (T : Module.End ℂ S)
    (hT : T ∈ wordSpan E L) : ∀ v : S, Continuous (fun g : UJ ε => ap T (σ (um g) v)) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ g : UJ ε, ‖ap T (σ (um g) v)‖ ≤ C * hs (um g) ^ L := by
  induction hT using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    intro v
    obtain ⟨hc, C, hC0, hC⟩ := word_growth hS hU w v
    refine ⟨?_, C, hC0, fun g => ?_⟩
    · have e : (fun g : UJ ε => ap (wp E w) (σ (um g) v)) =
          fun g => (wp E w ⟨σ (um g) v, hS.stab _ g.2 _ v.2⟩ : H) := funext fun g => ap_of_mem _ _
      change Continuous (fun g : UJ ε => ap (wp E w) (σ (um g) v))
      rw [e]
      exact hc
    · rw [ap_of_mem _ (hS.stab _ g.2 _ v.2)]
      exact (hC g).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (one_le_hs' hm g) hw) hC0)
  | zero =>
    intro v
    refine ⟨?_, 0, le_rfl, fun g => ?_⟩
    · simp only [ap_zero]; exact continuous_const
    · simp [ap_zero]
  | add x y _ _ hx hy =>
    intro v
    obtain ⟨h1, C1, hC1, hb1⟩ := hx v
    obtain ⟨h2, C2, hC2, hb2⟩ := hy v
    refine ⟨?_, C1 + C2, add_nonneg hC1 hC2, fun g => ?_⟩
    · simp only [ap_add]; exact h1.add h2
    · rw [ap_add, add_mul]; exact (norm_add_le _ _).trans (add_le_add (hb1 g) (hb2 g))
  | smul c x _ hx =>
    intro v
    obtain ⟨h1, C1, hC1, hb1⟩ := hx v
    refine ⟨?_, ‖c‖ * C1, mul_nonneg (norm_nonneg _) hC1, fun g => ?_⟩
    · simp only [ap_smul]; exact h1.const_smul c
    · rw [ap_smul, norm_smul, mul_assoc]; exact mul_le_mul_of_nonneg_left (hb1 g) (norm_nonneg _)

theorem span_adj (hS : IsSmMod ε σ S E) (L : ℕ) (T : Module.End ℂ S) (hT : T ∈ wordSpan E L) :
    ∃ T' : Module.End ℂ S, ∀ x y : S, ⟪(y : H), (T x : H)⟫_ℂ = ⟪(T' y : H), (x : H)⟫_ℂ := by
  have gen : ∀ a b, ∀ x y : S, ⟪(y : H), (E a b x : H)⟫_ℂ = ⟪(((sgn ε a b : ℂ) • E b a y : S) : H), (x : H)⟫_ℂ := by
    intro a b x y
    have h := hS.unit a b x y
    rw [← inner_conj_symm, ← Submodule.coe_inner, h, map_mul, Submodule.coe_smul, inner_smul_left, Complex.conj_ofReal,
      inner_conj_symm, Submodule.coe_inner]
  have word : ∀ w : List (Fin m × Fin m), ∃ T' : Module.End ℂ S, ∀ x y : S,
      ⟪(y : H), (wp E w x : H)⟫_ℂ = ⟪(T' y : H), (x : H)⟫_ℂ := by
    intro w
    induction w with
    | nil => exact ⟨1, fun x y => by simp [wp]⟩
    | cons p w ih =>
      obtain ⟨T', hT'⟩ := ih
      refine ⟨T' * ((sgn ε p.1 p.2 : ℂ) • E p.2 p.1), fun x y => ?_⟩
      simp only [wp, List.map_cons, List.prod_cons, Module.End.mul_apply] at hT' ⊢
      rw [gen, hT']
      rfl
  induction hT using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, -, rfl⟩ := hx
    exact word w
  | zero => exact ⟨0, fun x y => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨T1, h1⟩ := hx
    obtain ⟨T2, h2⟩ := hy
    exact ⟨T1 + T2, fun a b => by simp [h1, h2]⟩
  | smul c x _ hx =>
    obtain ⟨T1, h1⟩ := hx
    exact ⟨(starRingEnd ℂ c) • T1, fun a b => by
      simp only [LinearMap.smul_apply, Submodule.coe_smul, inner_smul_right, inner_smul_left, h1, Complex.conj_conj]⟩

end Span

section ZeroSec

variable {n : ℕ} {ε : Fin (n + 1) → Bool} {ε' : Fin n → Bool} {e : Fin n ⊕ Unit ≃ Fin (n + 1)}

theorem hs_emb (M : Matrix (Fin n) (Fin n) ℂ) : hs (emb e M) = hs M + 1 := by
  unfold hs emb
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [← Equiv.sum_comp e]
  simp only [Equiv.symm_apply_apply]
  have : ∀ x : Fin n ⊕ Unit, ∑ j, ‖Matrix.fromBlocks M 0 0 (1 : Matrix Unit Unit ℂ) x (e.symm j)‖ ^ 2 =
      ∑ y, ‖Matrix.fromBlocks M 0 0 (1 : Matrix Unit Unit ℂ) x y‖ ^ 2 := fun x => by
    rw [← Equiv.sum_comp e]; simp only [Equiv.symm_apply_apply]
  simp [this, Fintype.sum_sum_type]

theorem continuous_embU (hF : Fits ε ε' e) : Continuous (embU hF) := by
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · exact continuous_emb
  · exact continuous_emb.comp continuous_inv

theorem continuous_hs_um {m : ℕ} {ε₀ : Fin m → Bool} : Continuous fun g : UJ ε₀ => hs (um g) := by
  unfold hs
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    ((continuous_um.matrix_elem i j).norm).pow 2

theorem zero_proof : Zero := by
  intro n ε ε' e H _ _ _ π S E hF hn hS hU hD ν hν c L C hc hcb hzero T hT η b
  have := hν
  have hn1 : 1 ≤ n + 1 := by omega
  obtain ⟨hFc, CT, hCT0, hCT⟩ := span_growth hn1 hS hU L T hT η
  have hIntR := CompanionTheory.Lime.T3.analytic_estimates.2.2.1
  set a : ℝ := (n : ℝ) ^ 2 + 1 with ha
  set C' : ℝ := max C 0 with hC'
  have hcb' : ∀ h, ‖c h‖ ≤ C' * hs (um h) ^ (-(a + L)) := fun h =>
    (hcb h).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (hs_nonneg' _) _))
  set K₀ : ℝ := C' * CT * 2 ^ L with hK₀
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hK₀0 : 0 ≤ K₀ := mul_nonneg (mul_nonneg hC'0 hCT0) (by positivity)

  have hX : ∀ h : UJ ε', ‖ap T (π (emb e (um h)) η)‖ ≤ CT * 2 ^ L * hs (um h) ^ L := fun h => by
    have h1 := hCT (embU hF h)
    have h2 : hs (um (embU hF h)) = hs (um h) + 1 := hs_emb (um h)
    have h3 : 1 ≤ hs (um h) := one_le_hs' hn h
    rw [h2] at h1
    refine h1.trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hCT0
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) L
  have hXc : Continuous fun h : UJ ε' => ap T (π (emb e (um h)) η) := hFc.comp (continuous_embU hF)
  have hrp : ∀ h : UJ ε', hs (um h) ^ (-(a + L)) * hs (um h) ^ L = hs (um h) ^ (-a) := fun h => by
    have hpos : 0 < hs (um h) := lt_of_lt_of_le one_pos (one_le_hs' hn h)
    rw [← Real.rpow_natCast, ← Real.rpow_add hpos]
    congr 1; ring
  have bound : ∀ b : H, ∀ h : UJ ε', ‖c h * ⟪b, ap T (π (emb e (um h)) η)⟫_ℂ‖ ≤ K₀ * ‖b‖ * hs (um h) ^ (-a) := by
    intro b h
    rw [norm_mul]
    calc _ ≤ (C' * hs (um h) ^ (-(a + L))) * (‖b‖ * (CT * 2 ^ L * hs (um h) ^ L)) :=
          mul_le_mul (hcb' h) ((norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hX h) (norm_nonneg _)))
            (norm_nonneg _) (mul_nonneg hC'0 (Real.rpow_nonneg (hs_nonneg' _) _))
      _ = K₀ * ‖b‖ * (hs (um h) ^ (-(a + L)) * hs (um h) ^ L) := by rw [hK₀]; ring
      _ = _ := by rw [hrp]
  have integ : ∀ b : H, Integrable (fun h : UJ ε' => c h * ⟪b, ap T (π (emb e (um h)) η)⟫_ℂ) ν := fun b =>
    (hIntR n ε' ν hν hn _ (K₀ * ‖b‖) a (hc.mul (continuous_const.inner hXc)) le_rfl (bound b)).1

  have hw : Integrable (fun h : UJ ε' => hs (um h) ^ (-a)) ν := by
    have hcw : Continuous fun h : UJ ε' => ((hs (um h) ^ (-a) : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp (continuous_hs_um.rpow_const fun h =>
        Or.inl (lt_of_lt_of_le one_pos (one_le_hs' hn h)).ne')
    have := (hIntR n ε' ν hν hn _ 1 a hcw le_rfl fun h => by
      rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (hs_nonneg' _) _), one_mul]).1
    simpa using this.re
  refine ⟨integ b, ?_⟩

  set Λ : H → ℂ := fun b => ∫ h : UJ ε', c h * ⟪b, ap T (π (emb e (um h)) η)⟫_ℂ ∂ν with hΛ
  obtain ⟨T', hT'⟩ := span_adj hS L T hT
  have hS0 : ∀ b ∈ S, Λ b = 0 := by
    intro b hb
    have e1 : ∀ h : UJ ε', c h * ⟪b, ap T (π (emb e (um h)) η)⟫_ℂ =
        c h * ⟪(T' ⟨b, hb⟩ : H), π (emb e (um h)) η⟫_ℂ := fun h => by
      have hm : π (emb e (um h)) η ∈ S := hS.stab _ (embU hF h).2 _ η.2
      rw [ap_of_mem _ hm, hT' ⟨_, hm⟩ ⟨b, hb⟩]
    simp only [hΛ, e1]
    exact hzero _ _

  have hlip : ∀ b b' : H, ‖Λ b - Λ b'‖ ≤ (K₀ * ∫ h, hs (um h) ^ (-a) ∂ν) * ‖b - b'‖ := by
    intro b b'
    have e1 : Λ b - Λ b' = ∫ h : UJ ε', c h * ⟪b - b', ap T (π (emb e (um h)) η)⟫_ℂ ∂ν := by
      simp only [hΛ]
      rw [← integral_sub (integ b) (integ b')]
      refine integral_congr_ae (.of_forall fun h => ?_)
      simp only [inner_sub_left, mul_sub]
    rw [e1]
    refine (norm_integral_le_of_norm_le (hw.const_mul (K₀ * ‖b - b'‖)) (.of_forall fun h => bound _ h)).trans
      (le_of_eq ?_)
    rw [integral_const_mul]; ring
  have hcont : Continuous Λ := by
    refine LipschitzWith.continuous (K := Real.toNNReal (K₀ * ∫ h, hs (um h) ^ (-a) ∂ν))
      (LipschitzWith.of_dist_le_mul fun b b' => ?_)
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (mul_nonneg hK₀0 (integral_nonneg fun h =>
      Real.rpow_nonneg (hs_nonneg' _) _))]
    exact hlip b b'
  have hcl : IsClosed {b : H | Λ b = 0} := isClosed_eq hcont continuous_const
  have hall : closure (S : Set H) ⊆ {b : H | Λ b = 0} := closure_minimal (fun b hb => hS0 b hb) hcl
  rw [hD.closure_eq] at hall
  exact hall (Set.mem_univ b)

end ZeroSec

end PositivityTheory.RgHe.SM
