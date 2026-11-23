import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EncardBiUnionLe
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardIntegralFramesFixedLiftLeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSublatticeLiftsModuloFixingUnipotentStatement

noncomputable section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC GlobalTheory.LoopC.FrEqv
open scoped ENNReal Classical

namespace GlobalTheory.LoopC.FrEx

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

theorem hT_swap {x y : S.V} (h : S.hT x y = 0) : S.hT y x = 0 := by
  have := S.herm.eq x y
  rw [h, map_zero] at this
  exact this.symm

theorem mem_orth {U : Submodule E S.V} {y : S.V} : y ∈ orth S U ↔ ∀ x ∈ U, S.hT x y = 0 := by
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]

def moveFl (n : S.V ≃ₗ[E] S.V) (hn : n ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T) : LFlag S r T :=
  ⟨⟨fun a => n (F.fl.e a), n F.fl.z,
    F.fl.e_indep.map' (n : S.V →ₗ[E] S.V) n.ker,
    fun a b => (hn _ _).trans (F.fl.e_iso a b), fun a => (hn _ _).trans (F.fl.z_orth a),
    (hn _ _).trans F.fl.z_norm⟩, n F.fl.z⟩

theorem frame_moveFl (n : S.V ≃ₗ[E] S.V) (hn : n ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T) (b : Fin (r + 1)) :
    frame (moveFl n hn F) b = n (frame F b) := by
  refine Fin.lastCases ?_ (fun a => ?_) b <;> simp [frame, FlagG.fvec, moveFl]

theorem eq_zero_of_orth_frame (F : LFlag S r T) (F' : LFlag S r T') (b₀ : Fin (r + 1))
    (hd : (((ZhatL F F').submatrix Fin.castSucc id).submatrix id b₀.succAbove).det ≠ 0)
    {x : S.V} (hx : x ∈ Xsp F) (h : ∀ b, S.hT x (frame F' b) = 0) : x = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hx
  have h0 : (fun a => star (c a)) = 0 := by
    refine Matrix.eq_zero_of_vecMul_eq_zero hd ?_
    funext b
    have := h (b₀.succAbove b)
    simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      starRingEnd_apply] at this
    simpa [Matrix.vecMul, dotProduct, Zhat, brS, FlagG.fvec] using this
  have : ∀ a, c a = 0 := fun a => by simpa using congrFun h0 a
  simp [this]

theorem orth_frame_of_mem_Thp {Λ : Submodule (𝓞 E) S.V} {F : LFlag S r T} {F' : LFlag S r T'}
    (hl : IsLift Λ F') (he : ∀ a, F'.fl.e a ∈ Λ) {θ : S.V} (hθ : θ ∈ Thp Λ F F') (b : Fin (r + 1)) :
    S.hT θ (frame F' b) = 0 := by
  refine hT_swap (mem_orth.1 hθ.2 _ (Submodule.subset_span ?_))
  refine Fin.lastCases ?_ (fun a => ?_) b
  · have : frame F' (Fin.last r) = F'.zt := by simp [frame, FlagG.fvec, hl.2]
    rw [this]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  · have : frame F' a.castSucc = F'.fl.e a := by simp [frame, FlagG.fvec]
    rw [this]
    exact Submodule.mem_sup_left (Submodule.mem_sup_right ⟨he a, Submodule.subset_span ⟨a, rfl⟩⟩)

end Gen

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

theorem eq_zero_of_span_E {x : (hS D).V} (hx : x ∈ Submodule.span D.host.E (Set.range D.sp.hypE))
    (h : ∀ a, (hS D).hT x (D.sp.hypF a) = 0) : x = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hx
  have : ∀ a, c a = 0 := fun a => by
    have := h a
    simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      D.sp.hyp_ef] at this
    simpa using this
  simp [this]

theorem eq_zero_of_span_F {x : (hS D).V} (hx : x ∈ Submodule.span D.host.E (Set.range D.sp.hypF))
    (h : ∀ a, (hS D).hT (D.sp.hypE a) x = 0) : x = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hx
  have : ∀ a, c a = 0 := fun a => by
    have := h a
    simp only [map_sum, map_smul, smul_eq_mul, D.sp.hyp_ef] at this
    simpa using this
  simp [this]

theorem YS_le {y : (hS D).V} (hy : y ∈ YS D) : y ∈ Submodule.span D.host.E (Set.range D.sp.hypF) := by
  have : YS D ≤ toO (hS D) (Submodule.span D.host.E (Set.range D.sp.hypF)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, x, _, rfl⟩
    exact Submodule.smul_mem (Submodule.span D.host.E (Set.range D.sp.hypF)) x (Submodule.subset_span ⟨a, rfl⟩)
  exact this hy

theorem XS_le {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) {y : (hS D).V} (hy : y ∈ XS D F0) : y ∈ F0.X := by
  have : XS D F0 ≤ toO (hS D) F0.X := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, x, _, rfl⟩
    exact Submodule.smul_mem F0.X x (Submodule.subset_span ⟨a, rfl⟩)
  exact this hy

theorem iXY_mem_of_split {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (he : F0.e = D.sp.hypE) {Λ : LatV D}
    (hs : IsSplit D F0 Λ) (p : (D.sp.X 0).V) {θ : (hS D).V} (hθ : θ ∈ Λ) (hx : θ - D.sp.iXY 0 p ∈ F0.X) :
    D.sp.iXY 0 p ∈ Λ := by
  have hθ' := hθ
  rw [hs] at hθ'
  obtain ⟨_, h1, y, hy, rfl⟩ := Submodule.mem_sup.1 hθ'
  obtain ⟨a, ha, w, hw, rfl⟩ := Submodule.mem_sup.1 h1
  have haX := XS_le D F0 ha
  have hX : ∀ x ∈ F0.X, ∀ i, (hS D).hT (D.sp.hypE i) x = 0 := fun x hx i =>
    mem_orth.1 (X_le_orth (F := lf D F0) hx) _ (Submodule.subset_span ⟨i, by rw [← he]⟩)
  have hwE : ∀ i, (hS D).hT (D.sp.hypE i) w = 0 := fun i =>
    mem_orth.1 hw.2 _ (Submodule.subset_span (Or.inl ⟨i, rfl⟩))
  have hwF : ∀ i, (hS D).hT (D.sp.hypF i) w = 0 := fun i =>
    mem_orth.1 hw.2 _ (Submodule.subset_span (Or.inr ⟨i, rfl⟩))
  have hy0 : y = 0 := by
    refine eq_zero_of_span_F D (YS_le D hy) fun i => ?_
    have h1 := hX _ hx i
    have h2 : (hS D).hT (D.sp.hypE i) (D.sp.iXY 0 p) = 0 := hT_swap (D.sp.hyp_orthX i p).1
    rw [map_sub, map_add, map_add, h2, hX a haX i, hwE i] at h1
    simpa using h1
  subst hy0
  have h3 : w - D.sp.iXY 0 p ∈ F0.X := by
    have := F0.X.sub_mem hx haX
    convert this using 1
    abel
  have h4 : w - D.sp.iXY 0 p = 0 := by
    refine eq_zero_of_span_E D (by rw [← he]; exact h3) fun i => ?_
    rw [map_sub, LinearMap.sub_apply, hT_swap (hwF i)]
    have := (D.sp.hyp_orthX i p).2
    simpa using this
  rw [← sub_eq_zero.1 h4]
  exact hw.1

theorem exists_lift {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (he : F0.e = D.sp.hypE) {Λ : LatV D}
    (hs : IsSplit D F0 Λ) (P : LatW D) (Z : GramM D) (b₀ : Fin (D.R.rS + 1)) (hb : rowMinor D Z b₀ ≠ 0)
    {F' : Fg D T'} (hF : F' ∈ ExSet D Λ (lf D F0) T' Z P) :
    ∃ φ : P →ₗ[𝓞 D.host.E] (hS D).V, (∀ p, φ p ∈ XLam Λ (lf D F0)) ∧
      ∀ (p : P) b, (hS D).hT (D.sp.iXY 0 (p : (D.sp.X 0).V) + φ p) (frame F' b) = 0 := by
  obtain ⟨hl, hE, hZ, hP⟩ := hF
  have ex : ∀ p : P, ∃ x, x ∈ XLam Λ (lf D F0) ∧
      ∀ b, (hS D).hT (D.sp.iXY 0 (p : (D.sp.X 0).V) + x) (frame F' b) = 0 := by
    intro p
    obtain ⟨θ, hθ, x, hx, e⟩ := Submodule.mem_sup.1 (hP p.2)
    have e' : θ + x = D.sp.iXY 0 (p : (D.sp.X 0).V) := e
    have hx' : x ∈ F0.X := hx
    have h1 : θ - D.sp.iXY 0 (p : (D.sp.X 0).V) ∈ F0.X := by
      rw [← e']; simpa using hx'
    refine ⟨θ - D.sp.iXY 0 (p : (D.sp.X 0).V),
      ⟨Λ.sub_mem hθ.1 (iXY_mem_of_split D F0 he hs _ hθ.1 h1), h1⟩, fun b => ?_⟩
    rw [add_sub_cancel]
    exact orth_frame_of_mem_Thp hl hE hθ b
  choose f hf1 hf2 using ex
  have uniq : ∀ x ∈ F0.X, (∀ b, (hS D).hT x (frame F' b) = 0) → x = 0 := fun x hx h =>
    eq_zero_of_orth_frame (lf D F0) F' b₀ (by rw [hZ]; exact hb) hx h
  have hfX : ∀ p, f p ∈ F0.X := fun p => (hf1 p).2
  refine ⟨⟨⟨f, fun p q => ?_⟩, fun c p => ?_⟩, hf1, hf2⟩
  · rw [← sub_eq_zero]
    refine uniq _ (F0.X.sub_mem (hfX _) (F0.X.add_mem (hfX _) (hfX _))) fun b => ?_
    have h1 := hf2 (p + q) b
    have h2 := hf2 p b
    have h3 := hf2 q b
    simp only [Submodule.coe_add, map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply] at h1 h2 h3 ⊢
    linear_combination h1 - h2 - h3
  · show f (c • p) = c • f p
    have e1 : c • f p = algebraMap _ D.host.E c • f p := (algebraMap_smul D.host.E c (f p)).symm
    have e2 : ((c • p : P) : (D.sp.X 0).V) = algebraMap _ D.host.E c • (p : (D.sp.X 0).V) :=
      (algebraMap_smul D.host.E c (p : (D.sp.X 0).V)).symm
    rw [e1, ← sub_eq_zero]
    refine uniq _ (F0.X.sub_mem (hfX _) (F0.X.smul_mem _ (hfX _))) fun b => ?_
    have h1 := hf2 (c • p) b
    have h2 := hf2 p b
    rw [e2] at h1
    simp only [map_add, map_sub, map_smul, LinearMap.map_smulₛₗ, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, smul_eq_mul] at h1 h2 ⊢
    linear_combination h1 - (starRingEnd D.host.E) (algebraMap _ D.host.E c) * h2

theorem cntCl_ExSet_le : ∀ (D : D7) (u u' : D.what₂.Word) (F0 : Fb D u) (Λ : LatV D), Stand D u u' → IsBase D u F0 → IsRowLat D F0 Λ → IsSplit D F0 Λ → ∀ (P : LatW D) (Z : GramM D) (s : ℕ) (De Q : ℝ), 1 ≤ s → s ≤ D.R.k → SubOK D (L0X D Λ (lf D F0)) P s De → QOK D u u' Z Q → (cntCl (ExSet D Λ (lf D F0) ((Tu D u' : ℕ) : D.host.E) Z P) (TEqv D Λ (lf D F0)) : ℝ≥0∞) ≤ ENNReal.ofReal (frB D s (NT D u) De Q) := by
  intro D u u' F0 Λ hst hb hrow hsp P Z s De Q hs1 hsk hsub hQ
  obtain ⟨reps, hcard, hreps, hall⟩ := GlobalTheory.T.exists_sublattice_lifts_modulo_fixing_unipotent D u u' F0 Λ hst hb hrow hsp P s De hsub
  obtain ⟨b₀, hb₀, -⟩ := hQ.2.2.1
  have h1 := cntCl_le_sum (TEqv_equivalence D Λ (lf D F0) (T' := ((Tu D u' : ℕ) : D.host.E))) reps
    (ExSet D Λ (lf D F0) ((Tu D u' : ℕ) : D.host.E) Z P)
    (fun φ => FixSet D Λ (lf D F0) ((Tu D u' : ℕ) : D.host.E) Z P φ) (by
      intro F' hF'
      obtain ⟨φ, hφ, hφ'⟩ := exists_lift D F0 hb.1 hsp P Z b₀ hb₀ hF'
      obtain ⟨φ₀, h₀, n, ⟨hn, hnf⟩, hnp⟩ := hall φ hφ
      obtain ⟨hl, hE, hZ, -⟩ := hF'
      refine ⟨φ₀, h₀, moveFl n hn.1.1 F', ⟨⟨(aut_mem_iff hn.1 _).2 hl.1, rfl⟩,
        fun a => (aut_mem_iff hn.1 _).2 (hE a), ?_, fun p b => ?_⟩, n, hn, 1,
        fun a b h => Matrix.one_apply_ne h.ne', fun a => by simp, ?_⟩
      · rw [← hZ]
        funext a b
        change (hS D).hT (frame (lf D F0) a) (frame (moveFl n hn.1.1 F') b) =
          (hS D).hT (frame (lf D F0) a) (frame F' b)
        rw [frame_moveFl, ← hn.1.1 (frame (lf D F0) a) (frame F' b), hnf]
      · rw [frame_moveFl, ← hnp, hn.1.1]
        exact hφ' p b
      · rw [frameAct_one]
        funext b
        exact frame_moveFl _ _ _ b)
  have h2 : (cntCl (ExSet D Λ (lf D F0) ((Tu D u' : ℕ) : D.host.E) Z P) (TEqv D Λ (lf D F0)) : ℝ≥0∞) ≤
      ∑ φ ∈ reps, (cntCl (FixSet D Λ (lf D F0) ((Tu D u' : ℕ) : D.host.E) Z P φ) (TEqv D Λ (lf D F0)) : ℝ≥0∞) := by
    have := ENat.toENNReal_le.2 h1
    refine this.trans (le_of_eq ?_)
    exact map_sum ENat.toENNRealRingHom _ _
  refine h2.trans ((Finset.sum_le_card_nsmul _ _ _ fun φ hφ =>
    GlobalTheory.T.card_integral_frames_fixed_lift_le D u u' F0 Λ hst hb hrow hsp P φ Z s De Q hs1 hsk (hreps φ hφ) hsub hQ).trans ?_)
  have hnn : 0 ≤ NT D u ^ (2 * D.R.rS) * De ^ D.R.rS := le_trans (Nat.cast_nonneg _) hcard
  rw [frB, ENNReal.ofReal_mul hnn, nsmul_eq_mul]
  gcongr
  rw [← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal hcard

end GlobalTheory.LoopC.FrEx

end
