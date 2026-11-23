import Mathlib
import GroundTheory.AutomorphicForms.CompactSelfAdjoint
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TrDefs
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.CutIrr
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.JointNe

noncomputable section

open GroundTheory.Automorphic UpperTheory.ConvolutionTheory.C

namespace UpperTheory.ConvolutionTheory.L1

section
variable {Γ G H : Type} [Group Γ] [TopologicalSpace Γ] [Group G] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H] {π : UnitaryRep Γ H} {V : Submodule ℂ H} {m : ℕ}
  {ι : Fin (m + 1) → G →* Γ} {E : H →L[ℂ] H} {A : Fin (m + 1) → H →L[ℂ] H} {U : H ≃ₗᵢ[ℂ] H}

private lemma mem_eigIn {W : Submodule ℂ H} {T : H →L[ℂ] H} {c : ℝ} {v : H} :
    v ∈ eigIn W T c ↔ v ∈ W ∧ T v = (c : ℂ) • v := by
  simp [eigIn, Submodule.mem_inf, Module.End.mem_eigenspace_iff]

private lemma closed_eigIn {W : Submodule ℂ H} (hW : IsClosed (W : Set H)) (T : H →L[ℂ] H) (c : ℝ) :
    IsClosed (eigIn W T c : Set H) := by
  have : (eigIn W T c : Set H) = (W : Set H) ∩ {v | T v = (c : ℂ) • v} := by
    ext v
    exact mem_eigIn
  rw [this]
  exact hW.inter (isClosed_eq T.continuous (continuous_const_smul _))

private lemma A_cut (h : Slots π V m ι E A U) (i : Fin (m + 1)) {v : H} (hv : v ∈ eigIn V E 1) :
    A i v ∈ eigIn V E 1 := by
  obtain ⟨h1, h2⟩ := mem_eigIn.1 hv
  simp only [Complex.ofReal_one, one_smul] at h2
  refine mem_eigIn.2 ⟨h.A_mem i v h1, ?_⟩
  rw [← h.A_E, h2]
  simp

private lemma U_cut (h : Slots π V m ι E A U) {v : H} (hv : v ∈ eigIn V E 1) :
    U v ∈ eigIn V E 1 := by
  obtain ⟨h1, h2⟩ := mem_eigIn.1 hv
  simp only [Complex.ofReal_one, one_smul] at h2
  refine mem_eigIn.2 ⟨?_, ?_⟩
  · rw [← h.U_mem]
    exact Submodule.mem_map_of_mem h1
  · rw [← h.U_E, h2]
    simp

private lemma fin_gen (x : Fin (m + 1)) : ∃ n : ℕ, n • (1 : Fin (m + 1)) = x := by
  induction x using Fin.induction with
  | zero => exact ⟨0, by simp⟩
  | succ a ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, by rw [succ_nsmul, hn, Fin.coeSucc_eq_succ]⟩

private lemma ne_all (h : Slots π V m ι E A U) {i : Fin (m + 1)}
    (hi : ∃ v ∈ eigIn V E 1, A i v ≠ 0) (j : Fin (m + 1)) : ∃ v ∈ eigIn V E 1, A j v ≠ 0 := by
  have step : ∀ n : ℕ, ∃ v ∈ eigIn V E 1, A (i - n • (1 : Fin (m + 1))) v ≠ 0 := by
    intro n
    induction n with
    | zero => simpa using hi
    | succ n ih =>
      obtain ⟨v, hv, hne⟩ := ih
      refine ⟨U v, U_cut h hv, ?_⟩
      have e : i - (n + 1) • (1 : Fin (m + 1)) + 1 = i - n • (1 : Fin (m + 1)) := by
        rw [succ_nsmul]
        abel
      have := h.U_A (i - (n + 1) • (1 : Fin (m + 1))) v
      rw [e] at this
      rw [← this]
      simpa using hne
  obtain ⟨n, hn⟩ := fin_gen (i - j)
  have := step n
  rwa [hn, sub_sub_cancel] at this

private lemma list_comm_A (h : Slots π V m ι E A U) (k : Fin (m + 1)) (L : List (Fin (m + 1))) (v : H) :
    A k ((L.map A).prod v) = (L.map A).prod (A k v) := by
  induction L generalizing v with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.prod_cons, ContinuousLinearMap.mul_apply]
    rw [h.A_A, ih]

private lemma list_comm_π (h : Slots π V m ι E A U) {k : Fin (m + 1)} {L : List (Fin (m + 1))}
    (hk : k ∉ L) (g : G) (v : H) :
    (L.map A).prod (π (ι k g) v) = π (ι k g) ((L.map A).prod v) := by
  induction L generalizing v with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.prod_cons, ContinuousLinearMap.mul_apply]
    have hka : a ≠ k := fun e => hk (by simp [e])
    have hkL : k ∉ L := fun e => hk (by simp [e])
    rw [ih hkL, h.A_ι a k hka]

private lemma list_mem (h : Slots π V m ι E A U) (L : List (Fin (m + 1))) {v : H}
    (hv : v ∈ eigIn V E 1) : (L.map A).prod v ∈ eigIn V E 1 := by
  induction L with
  | nil => simpa using hv
  | cons a L ih =>
    simp only [List.map_cons, List.prod_cons, ContinuousLinearMap.mul_apply]
    exact A_cut h a ih

private lemma list_sa (h : Slots π V m ι E A U) (L : List (Fin (m + 1))) :
    IsSelfAdjoint (L.map A).prod := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have hc : (L.map A).prod * A a = A a * (L.map A).prod := by
      ext v
      simp only [ContinuousLinearMap.mul_apply]
      exact (list_comm_A h a L v).symm
    simp only [List.map_cons, List.prod_cons]
    rw [isSelfAdjoint_iff, star_mul, ih.star_eq, (IsSelfAdjoint.of_nonneg (h.A_pos a)).star_eq, hc]

private lemma list_zero (h : Slots π V m ι E A U) {k : Fin (m + 1)} {L : List (Fin (m + 1))}
    (hk : k ∈ L) {w : H} (hw : A k w = 0) : (L.map A).prod w = 0 := by
  induction L with
  | nil => simp at hk
  | cons a L ih =>
    simp only [List.map_cons, List.prod_cons, ContinuousLinearMap.mul_apply]
    rcases List.mem_cons.1 hk with e | e
    · subst e
      rw [list_comm_A h, hw, map_zero]
    · rw [ih e, map_zero]

private lemma list_ne (h : Slots π V m ι E A U) (hall : ∀ j, ∃ v ∈ eigIn V E 1, A j v ≠ 0)
    (hne : ∃ v ∈ eigIn V E 1, v ≠ 0) (L : List (Fin (m + 1))) (hL : L.Nodup) :
    ∃ v ∈ eigIn V E 1, (L.map A).prod v ≠ 0 := by
  induction L with
  | nil => simpa using hne
  | cons k L ih =>
    obtain ⟨u, hu, hQ⟩ := ih (List.nodup_cons.1 hL).2
    have hk : k ∉ L := (List.nodup_cons.1 hL).1
    obtain ⟨hcl, hinv, hirr⟩ := cutIrr Γ G H π V m ι E A U h
    by_contra hcon
    push_neg at hcon
    simp only [List.map_cons, List.prod_cons, ContinuousLinearMap.mul_apply] at hcon
    let M : Submodule ℂ H :=
      { carrier := {w | w ∈ eigIn V E 1 ∧ ∀ g, A k (π (ι k g) w) = 0}
        add_mem' := fun {a b} ha hb => ⟨Submodule.add_mem _ ha.1 hb.1, fun g => by
          rw [map_add, map_add, ha.2, hb.2, add_zero]⟩
        zero_mem' := ⟨Submodule.zero_mem _, fun g => by simp⟩
        smul_mem' := fun c a ha => ⟨Submodule.smul_mem _ c ha.1, fun g => by
          rw [map_smul, map_smul, ha.2, smul_zero]⟩ }
    have hMmem : ∀ w, w ∈ M ↔ w ∈ eigIn V E 1 ∧ ∀ g, A k (π (ι k g) w) = 0 := fun w => Iff.rfl
    have hMle : M ≤ eigIn V E 1 := fun w hw => hw.1
    have hMcl : IsClosed (M : Set H) := by
      have : (M : Set H) = (eigIn V E 1 : Set H) ∩ ⋂ g, {w | A k (π (ι k g) w) = 0} := by
        ext w
        simp [hMmem]
      rw [this]
      refine hcl.inter (isClosed_iInter fun g => ?_)
      exact isClosed_eq ((A k).continuous.comp (π (ι k g)).continuous) continuous_const
    have hMinv : ∀ i g, ∀ v ∈ M, π (ι i g) v ∈ M := by
      intro i g v hv
      refine ⟨hinv i g v hv.1, fun g' => ?_⟩
      by_cases e : i = k
      · subst e
        rw [← UnitaryRep.map_mul_apply, ← map_mul]
        exact hv.2 _
      · have hc : ι k g' * ι i g = ι i g * ι k g' := (h.ι_comm k i (Ne.symm e) g' g)
        rw [← UnitaryRep.map_mul_apply, hc, UnitaryRep.map_mul_apply, h.A_ι k i (Ne.symm e), hv.2, map_zero]
    have hQM : (L.map A).prod u ∈ M := by
      refine ⟨list_mem h L hu, fun g => ?_⟩
      rw [← list_comm_π h hk]
      exact hcon _ (hinv k g u hu)
    rcases hirr M hMle hMcl hMinv with e | e
    · rw [e] at hQM
      exact hQ ((Submodule.mem_bot ℂ).1 hQM)
    · obtain ⟨v, hv, hAv⟩ := hall k
      rw [← e] at hv
      have := hv.2 1
      simp only [map_one, UnitaryRep.map_one_apply] at this
      exact hAv this

private lemma fd_of_compact {T : H →L[ℂ] H} (hT : IsCompactOperator T) {x : ℂ} (hx : x ≠ 0)
    (P : Submodule ℂ H) (hP : IsClosed (P : Set H)) (hTP : ∀ v ∈ P, T v = x • v) :
    FiniteDimensional ℂ P := by
  have hC : IsCompact (closure (T '' Metric.closedBall 0 1)) :=
    hT.isCompact_closure_image_closedBall 1
  have hK : IsCompact ((fun z : H => x⁻¹ • z) '' closure (T '' Metric.closedBall 0 1)) :=
    hC.image (continuous_const_smul _)
  have hK' := hP.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  refine FiniteDimensional.of_isCompact_closedBall ℂ (c := (0 : P)) (r := 1) one_pos
    (hK'.of_isClosed_subset Metric.isClosed_closedBall ?_)
  intro p hp
  refine ⟨T p, subset_closure ⟨p, ?_, rfl⟩, ?_⟩
  · simpa using hp
  · simp only
    rw [hTP p p.2, smul_smul, inv_mul_cancel₀ hx, one_smul]

private lemma prj_fix {W : Submodule ℂ H} {v : H} (hv : v ∈ W) : prj W v = v :=
  (Submodule.starProjection_eq_self_iff).2 (Submodule.le_topologicalClosure _ hv)

private lemma prj_mem {W : Submodule ℂ H} (hW : IsClosed (W : Set H)) (v : H) : prj W v ∈ W := by
  have : prj W v ∈ W.topologicalClosure := by
    rw [prj, Submodule.starProjection_apply]
    exact Submodule.coe_mem _
  rwa [hW.submodule_topologicalClosure_eq] at this

private lemma spectral_ne {T : H →L[ℂ] H} (hT : IsCompactOperator T) (hsa : IsSelfAdjoint T) {u : H}
    (hu : T u ≠ 0) : ∃ (x : ℝ) (v : H), x ≠ 0 ∧ v ≠ 0 ∧ T v = (x : ℂ) • v := by
  obtain ⟨s, b, l, -, hb, hsum, -⟩ :=
    CompactSelfAdjoint.exists_hilbertBasis_eigenvectors_hasSum hT hsa
  by_cases hl : ∃ i, l i ≠ 0
  · obtain ⟨j, hj⟩ := hl
    exact ⟨l j, b j, hj, b.orthonormal.ne_zero j, hb j⟩
  · exfalso
    push_neg at hl
    apply hu
    rw [← (hsum u).tsum_eq]
    simp [hl]

end

end UpperTheory.ConvolutionTheory.L1

theorem UpperTheory.ConvolutionTheory.L1.jointEx :
    UpperTheory.ConvolutionTheory.L1.JointEx := by
  intro Γ G H _ _ _ _ _ _ π V m ι E A U h hcomp
  have hofn : List.ofFn A = (List.finRange (m + 1)).map A := List.ofFn_eq_map
  obtain ⟨hcl, -, -⟩ := cutIrr Γ G H π V m ι E A U h
  have hfd : ∀ x : ℝ, x ≠ 0 → FiniteDimensional ℂ (prodEig V E A x) := by
    intro x hx
    refine fd_of_compact hcomp (x := (x : ℂ)) (by exact_mod_cast hx) _ (closed_eigIn hcl _ _) ?_
    intro v hv
    obtain ⟨h1, h2⟩ := mem_eigIn.1 hv
    rw [ContinuousLinearMap.comp_apply, prj_fix h1]
    exact h2
  refine ⟨fun x hx => hfd x hx.ne', ?_⟩
  rintro ⟨i, v₀, hv₀, hne⟩
  have hall := ne_all h ⟨v₀, hv₀, hne⟩
  have hne0 : ∃ v ∈ eigIn V E 1, v ≠ 0 := ⟨v₀, hv₀, fun e => hne (by simp [e])⟩
  obtain ⟨u, hu, hQu⟩ := list_ne h hall hne0 (List.finRange (m + 1)) (List.nodup_finRange _)
  rw [← hofn] at hQu
  have hQmem : ∀ v ∈ eigIn V E 1, (List.ofFn A).prod v ∈ eigIn V E 1 := by
    intro v hv
    rw [hofn]
    exact list_mem h _ hv
  have hQsa : IsSelfAdjoint (List.ofFn A).prod := by
    rw [hofn]
    exact list_sa h _
  have hPm : ∀ v, prj (eigIn V E 1) v ∈ eigIn V E 1 := prj_mem hcl
  have hPsa : IsSelfAdjoint (prj (eigIn V E 1)) := isSelfAdjoint_starProjection _
  have hTeq : (List.ofFn A).prod ∘L prj (eigIn V E 1) =
      prj (eigIn V E 1) ∘L (List.ofFn A).prod ∘L prj (eigIn V E 1) := by
    ext v
    simp only [ContinuousLinearMap.comp_apply]
    exact (prj_fix (hQmem _ (hPm v))).symm
  have hTsa : IsSelfAdjoint ((List.ofFn A).prod ∘L prj (eigIn V E 1)) := by
    rw [hTeq]
    have := hQsa.conj_adjoint (prj (eigIn V E 1))
    rwa [ContinuousLinearMap.isSelfAdjoint_iff'.1 hPsa] at this
  obtain ⟨lj, bj, hj, hv0, hTv⟩ := spectral_ne hcomp hTsa (u := u)
    (by rwa [ContinuousLinearMap.comp_apply, prj_fix hu])
  have hjc : (lj : ℂ) ≠ 0 := by exact_mod_cast hj
  rw [ContinuousLinearMap.comp_apply] at hTv
  have hvm : bj ∈ eigIn V E 1 := by
    have e : bj = (lj : ℂ)⁻¹ • (List.ofFn A).prod (prj (eigIn V E 1) (bj)) := by
      rw [hTv, smul_smul, inv_mul_cancel₀ hjc, one_smul]
    rw [e]
    exact Submodule.smul_mem _ _ (hQmem _ (hPm _))
  rw [prj_fix hvm] at hTv
  have hmemP : bj ∈ prodEig V E A lj := mem_eigIn.2 ⟨hvm, hTv⟩
  haveI := hfd lj hj
  have hinv : ∀ w ∈ prodEig V E A lj, (A 0 : H →ₗ[ℂ] H) w ∈ prodEig V E A lj := by
    intro w hw
    obtain ⟨h1, h2⟩ := mem_eigIn.1 hw
    refine mem_eigIn.2 ⟨A_cut h 0 h1, ?_⟩
    have := list_comm_A h 0 (List.finRange (m + 1)) w
    rw [← hofn] at this
    change (List.ofFn A).prod (A 0 w) = (lj : ℂ) • A 0 w
    rw [← this, h2, map_smul]
  haveI : Nontrivial (prodEig V E A lj) :=
    ⟨⟨⟨bj, hmemP⟩, 0, fun e => hv0 (congrArg Subtype.val e)⟩⟩
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue ((A 0 : H →ₗ[ℂ] H).restrict hinv)
  obtain ⟨w, hw⟩ := hc.exists_hasEigenvector
  have hw1 : A 0 (w : H) = c • (w : H) := by
    have := congrArg Subtype.val (Module.End.HasEigenvector.apply_eq_smul hw)
    simpa using this
  have hw0 : (w : H) ≠ 0 := fun e => hw.2 (Subtype.ext e)
  have hEv : Module.End.HasEigenvalue (A 0 : H →ₗ[ℂ] H) c :=
    Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 hw1, hw0⟩
  obtain ⟨r, rfl⟩ :=
    CompactSelfAdjoint.exists_real_of_hasEigenvalue (IsSelfAdjoint.of_nonneg (h.A_pos 0)) hEv
  obtain ⟨hwc, hwQ⟩ := mem_eigIn.1 w.2
  have hr0 : 0 ≤ r := by
    have hp := (ContinuousLinearMap.nonneg_iff_isPositive _).1 (h.A_pos 0)
    have h3 := hp.re_inner_nonneg_right (w : H)
    have h4 : 0 < ‖(w : H)‖ ^ 2 := by positivity
    have h5 : RCLike.re (inner ℂ (w : H) ((r : ℂ) • (w : H))) = r * ‖(w : H)‖ ^ 2 := by
      rw [inner_smul_right, ← inner_self_eq_norm_sq (𝕜 := ℂ) (w : H)]
      first
        | exact RCLike.re_ofReal_mul _ _
        | simp
    rw [hw1] at h3
    have h6 : 0 ≤ r * ‖(w : H)‖ ^ 2 := h5 ▸ h3
    by_contra hneg
    push_neg at hneg
    nlinarith
  have hrne : r ≠ 0 := by
    rintro rfl
    have hz : A 0 (w : H) = 0 := by simp [hw1]
    have := list_zero h (List.mem_finRange 0) hz
    rw [← hofn, hwQ] at this
    exact (smul_ne_zero hjc hw0) this
  refine ⟨r, lt_of_le_of_ne hr0 (Ne.symm hrne), ?_⟩
  refine jointNe Γ G H π V m ι E A U h 0 r fun e => ?_
  have hmem : (w : H) ∈ eigIn (eigIn V E 1) (A 0) r := mem_eigIn.2 ⟨hwc, hw1⟩
  rw [e] at hmem
  exact hw0 ((Submodule.mem_bot ℂ).1 hmem)
