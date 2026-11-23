import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TraceDistributionsGL.PhiIndep
import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.LeviTransposeDistributions.BoundOneTwo
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TraceDistributionsGL.DetUpdateRowOneLast

noncomputable section

open Matrix MeasureTheory Topology Filter ValuativeRel GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi GlobalTheory.BZMir

set_option linter.unusedSectionVars false

namespace PositivityTheory.RgUd.AB.BoxIntegration

open PositivityTheory.RgUd.AB

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Act

variable {n : ℕ}

def actP (g : GL (Fin (n + 1)) k) (p : Mx k n × Vc k n) : Mx k n × Vc k n :=
  (cj g⁻¹ p.1, (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k)ᵀ *ᵥ p.2)

theorem cj_apply (g : GL (Fin (n + 1)) k) (x : Mx k n) :
    cj g x = (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) * x * ((g⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) := rfl

theorem cj_one (x : Mx k n) : cj (1 : GL (Fin (n + 1)) k) x = x := by
  simp [cj_apply]

theorem cj_mul (g h : GL (Fin (n + 1)) k) (x : Mx k n) : cj (g * h) x = cj g (cj h x) := by
  simp only [cj_apply, _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc]

theorem polyAction_one₂ (p : Mx k n × Vc k n) : actP (1 : GL (Fin (n + 1)) k) p = p := by
  simp [actP, cj_one]

theorem polyAction_mul (g h : GL (Fin (n + 1)) k) (p : Mx k n × Vc k n) : actP (g * h) p = actP h (actP g p) := by
  simp only [actP, _root_.mul_inv_rev, cj_mul, Units.val_mul, transpose_mul, mulVec_mulVec]

theorem actP_inv_actP (g : GL (Fin (n + 1)) k) (p : Mx k n × Vc k n) : actP g⁻¹ (actP g p) = p := by
  rw [← polyAction_mul, mul_inv_cancel, polyAction_one₂]

theorem continuous_actP : Continuous fun q : GL (Fin (n + 1)) k × (Mx k n × Vc k n) => actP q.1 q.2 := by
  unfold actP cj
  refine Continuous.prodMk ?_ ?_
  · simp only [inv_inv]
    exact ((Units.continuous_coe_inv.comp continuous_fst).matrix_mul
      (continuous_fst.comp continuous_snd)).matrix_mul (Units.continuous_val.comp continuous_fst)
  · exact (Units.continuous_val.comp continuous_fst).matrix_transpose.matrix_mulVec (continuous_snd.comp continuous_snd)

theorem eventually_actP_eq {F : Mx k n × Vc k n → ℂ} (hF : F ∈ SB (Mx k n × Vc k n)) :
    ∀ᶠ g in 𝓝 (1 : GL (Fin (n + 1)) k), ∀ p, F (actP g p) = F p := by
  have h1 : ∀ᶠ g in 𝓝 (1 : GL (Fin (n + 1)) k), ∀ p ∈ tsupport F, F (actP g p) = F p := by
    refine IsCompact.eventually_forall_of_forall_eventually hF.2 fun p _ => ?_
    have h2 : IsLocallyConstant fun q : GL (Fin (n + 1)) k × (Mx k n × Vc k n) => (F (actP q.1 q.2), F q.2) :=
      (hF.1.comp_continuous continuous_actP).prodMk (hF.1.comp_continuous continuous_snd)
    filter_upwards [h2.eventually_eq ((1 : GL (Fin (n + 1)) k), p)] with q hq
    simp only [Prod.mk.injEq, polyAction_one₂] at hq
    rw [hq.1, hq.2]
  have h3 : ∀ᶠ g in 𝓝 (1 : GL (Fin (n + 1)) k), ∀ p ∈ tsupport F, F (actP g⁻¹ p) = F p := by
    have ht : Tendsto (fun g : GL (Fin (n + 1)) k => g⁻¹) (𝓝 1) (𝓝 1) := by
      simpa using (continuous_inv.tendsto (1 : GL (Fin (n + 1)) k))
    exact ht.eventually h1
  filter_upwards [h1, h3] with g hg hg' p
  by_cases hp : p ∈ tsupport F
  · exact hg p hp
  by_cases hq : actP g p ∈ tsupport F
  · have := hg' _ hq
    rw [actP_inv_actP] at this
    exact this.symm
  · rw [image_eq_zero_of_notMem_tsupport hp, image_eq_zero_of_notMem_tsupport hq]

end Act

section Phi

variable {n : ℕ}

theorem vecMul_eLast (M : Matrix (Fin (n + 1)) (Fin (n + 1)) k) : vecMul (eLast k n) M = fun j => M (Fin.last n) j := by
  funext j
  simp [vecMul, dotProduct, eLast, Pi.single_apply]

def cjHomeo (g : GL (Fin (n + 1)) k) : Mx k n ≃ₜ Mx k n where
  toFun := cj g
  invFun := cj g⁻¹
  left_inv x := by rw [← cj_mul, inv_mul_cancel, cj_one]
  right_inv x := by rw [← cj_mul, mul_inv_cancel, cj_one]
  continuous_toFun := by
    unfold cj
    exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  continuous_invFun := by
    unfold cj
    exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

theorem slice_snd_mem {F : Mx k n × Vc k n → ℂ} (hF : F ∈ SB (Mx k n × Vc k n)) (w : Vc k n) :
    (fun y => F (y, w)) ∈ SB (Mx k n) := by
  haveI := t2Space k
  refine ⟨hF.1.comp_continuous (f := fun y => (y, w)) (by fun_prop),
    HasCompactSupport.intro (IsCompact.image hF.2 continuous_fst) fun y hy => ?_⟩
  exact image_eq_zero_of_notMem_tsupport fun h => hy ⟨_, h, rfl⟩

theorem comp_cj_mem {f : Mx k n → ℂ} (hf : f ∈ SB (Mx k n)) (g : GL (Fin (n + 1)) k) : f ∘ cj g ∈ SB (Mx k n) :=
  ⟨hf.1.comp_continuous (cjHomeo g).continuous, hf.2.comp_homeomorph (cjHomeo g)⟩

theorem sec_row {w : Vc k n} {s : GL (Fin (n + 1)) k} (hs : ∀ j, (s : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) j = w j) :
    ∀ j, ((sec w : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) j = w j := by
  have hex : ∃ s' : GL (Fin (n + 1)) k, ∀ j, (s' : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) j = w j := ⟨s, hs⟩
  unfold sec
  rw [dif_pos hex]
  exact hex.choose_spec

theorem phi_eq_of_row {Λ : (Mx k n → ℂ) →ₗ[ℂ] ℂ} (hP : PInvX Λ) {F : Mx k n × Vc k n → ℂ} (hF : F ∈ SB (Mx k n × Vc k n))
    (s : GL (Fin (n + 1)) k) {w : Vc k n} (hs : ∀ j, (s : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) j = w j)
    (hw : w ≠ 0) : phi Λ F w = Λ (fun x => F (cj s⁻¹ x, w)) := by
  unfold phi
  rw [if_neg hw]
  set t := (sec w : GL (Fin (n + 1)) k) with ht
  have htr := sec_row hs
  have hp : s * t⁻¹ ∈ Mir k n := by
    show vecMul (eLast k n) ((s * t⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) = eLast k n
    have e1 : vecMul (eLast k n) (s : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
        vecMul (eLast k n) (t : Matrix (Fin (n + 1)) (Fin (n + 1)) k) := by
      rw [vecMul_eLast, vecMul_eLast]
      funext j
      rw [hs j, ht, htr j]
    rw [Units.val_mul, ← vecMul_vecMul, e1, vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, vecMul_one]
  have hpi : (s * t⁻¹)⁻¹ ∈ Mir k n := (Mir k n).inv_mem hp
  have hH := comp_cj_mem (slice_snd_mem hF w) t⁻¹
  have key := hP _ hpi _ hH
  have e : ((fun y => F (y, w)) ∘ cj t⁻¹) ∘ cj (s * t⁻¹)⁻¹ = fun x => F (cj s⁻¹ x, w) := by
    funext x
    simp only [Function.comp_apply]
    rw [← cj_mul]
    congr 2
    group
  rw [e] at key
  rw [key]
  rfl

theorem phi_eventually_eq {Λ : (Mx k n → ℂ) →ₗ[ℂ] ℂ} (hP : PInvX Λ) {F : Mx k n × Vc k n → ℂ}
    (hF : F ∈ SB (Mx k n × Vc k n)) {w₀ : Vc k n} (hw₀ : w₀ ≠ 0) : ∀ᶠ w in 𝓝 w₀, phi Λ F w = phi Λ F w₀ := by
  obtain ⟨s₀, hs₀⟩ := PositivityTheory.RgUd.AB.Pf.exists_last_row w₀ hw₀
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hw₀
  let Mf : Vc k n → Matrix (Fin (n + 1)) (Fin (n + 1)) k := fun w =>
    1 + vecMulVec (Pi.single i (w₀ i)⁻¹) (w - w₀)
  have hMc : Continuous Mf := continuous_const.add (Continuous.matrix_vecMulVec continuous_const (continuous_id.sub continuous_const))
  have hM0 : Mf w₀ = 1 := by simp [Mf]
  obtain ⟨W, hW1, hW⟩ := (eventually_actP_eq hF).exists_mem
  have hE := PositivityTheory.PfBern.cocyclesToWachVectorsExponent.isOpenEmbedding_valGL (k := k) (m := n + 1)
  have hO : Units.val '' W ∈ 𝓝 (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) := by
    have := hE.isOpenMap.image_mem_nhds hW1
    simpa using this
  have h1 : ∀ᶠ w in 𝓝 w₀, Mf w ∈ Units.val '' W := by
    have := hMc.continuousAt (x := w₀)
    rw [ContinuousAt, hM0] at this
    exact this hO
  filter_upwards [h1, eventually_ne_nhds hw₀ |>.mono fun _ h => h, isOpen_ne.mem_nhds hw₀] with w hw _ hw0
  obtain ⟨g, hgW, hg⟩ := hw
  have hrow : ∀ j, ((s₀ * g : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) j = w j := by
    have e1 : vecMul (eLast k n) ((s₀ * g : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) = w := by
      rw [Units.val_mul, ← vecMul_vecMul, vecMul_eLast, hg]
      have e2 : (fun j => (s₀ : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) j) = w₀ := funext hs₀
      rw [e2]
      simp only [Mf, vecMul_add, vecMul_one, vecMul_vecMulVec]
      have e3 : w₀ ⬝ᵥ Pi.single i (w₀ i)⁻¹ = 1 := by
        rw [dotProduct_single, mul_inv_cancel₀ hi]
      rw [e3, one_smul]
      abel
    intro j
    have := congrFun e1 j
    rw [vecMul_eLast] at this
    exact this
  have hw0' : w ≠ 0 := hw0
  rw [phi_eq_of_row hP hF (s₀ * g) hrow hw0', phi_eq_of_row hP hF s₀ hs₀ hw₀]
  congr 1
  funext x
  have hwg : w = (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k)ᵀ *ᵥ w₀ := by
    rw [mulVec_transpose]
    have e2 : (fun j => (s₀ : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) j) = w₀ := funext hs₀
    rw [← e2, ← vecMul_eLast, vecMul_vecMul, ← Units.val_mul, vecMul_eLast]
    funext j
    exact (hrow j).symm
  have := hW g hgW (cj s₀⁻¹ x, w₀)
  simp only [actP] at this
  rw [_root_.mul_inv_rev, cj_mul, hwg]
  exact this

theorem phi_eq_zero_of_notMem {Λ : (Mx k n → ℂ) →ₗ[ℂ] ℂ} {F : Mx k n × Vc k n → ℂ} {w : Vc k n}
    (hw : w ∉ Prod.snd '' tsupport F) : phi Λ F w = 0 := by
  unfold phi
  split_ifs
  · rfl
  · have : (fun x => F (cj (sec w)⁻¹ x, w)) = 0 := by
      funext x
      exact image_eq_zero_of_notMem_tsupport fun h => hw ⟨_, h, rfl⟩
    rw [this, map_zero]

theorem phi_zero {Λ : (Mx k n → ℂ) →ₗ[ℂ] ℂ} {F : Mx k n × Vc k n → ℂ} : phi Λ F 0 = 0 := by
  simp [phi]

theorem exists_box_phi_smul {Λ : (Mx k n → ℂ) →ₗ[ℂ] ℂ} (hP : PInvX Λ) {F : Mx k n × Vc k n → ℂ}
    (hF : F ∈ SB (Mx k n × Vc k n)) : ∃ s : kˣ, ∀ w ∈ box (Fin (n + 1)) s, ∀ c : kˣ, c • w ∈ box (Fin (n + 1)) s →
      phi Λ F (c • w) = phi Λ F w := by
  obtain ⟨s, hs⟩ := GlobalTheory.SplitDict.exists_box_invariant_snd hF
  have h0 : ∀ u ∈ box (Fin (n + 1)) s, ∀ y, F (y, u) = F (y, 0) := fun u hu y => by
    have := hs u hu (y, 0)
    simpa using this
  refine ⟨s, fun w hw c hc => ?_⟩
  by_cases hw0 : w = 0
  · subst hw0
    simp
  have hcw : c • w ≠ 0 := fun h => hw0 (by simpa using congrArg (fun v => c⁻¹ • v) h)
  obtain ⟨t, ht⟩ := PositivityTheory.RgUd.AB.Pf.exists_last_row w hw0
  let sc : GL (Fin (n + 1)) k := Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) c
  have hrow : ∀ j, ((sc * t : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) j = (c • w) j := by
    intro j
    simp [sc, ht j, Units.smul_def]
  rw [phi_eq_of_row hP hF (sc * t) hrow hcw, phi_eq_of_row hP hF t ht hw0]
  congr 1
  funext x
  have hcj : cj (sc * t)⁻¹ x = cj t⁻¹ x := by
    rw [_root_.mul_inv_rev, cj_mul]
    congr 1
    ext a b
    simp [sc, cj_apply, Matrix.GeneralLinearGroup.scalar, Matrix.diagonal_mul, Matrix.mul_diagonal]
    field_simp
  rw [hcj, h0 _ hc, h0 _ hw]

end Phi

section Fin

variable {X Y : Type*} [TopologicalSpace X]

theorem finite_image_of_eventually {f : X → Y} {K : Set X} (hK : IsCompact K)
    (h : ∀ x ∈ K, ∀ᶠ y in 𝓝 x, f y = f x) : (f '' K).Finite := by
  obtain ⟨t, htK, hcov⟩ := hK.elim_nhds_subcover (fun x => {y | f y = f x}) (fun x hx => h x hx)
  refine (t.finite_toSet.image f).subset ?_
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 (hcov hy)
  exact ⟨x, hx, hyx.symm⟩

end Fin

section Range

variable {n : ℕ}

theorem zero_mem_box (s : kˣ) : (0 : Vc k n) ∈ box (Fin (n + 1)) s := by
  intro i _
  simp [cball]

theorem exists_smul_shell {s : kˣ} {r : k} (hr0 : r ≠ 0) (hr1 : valuation k r < 1) {w : Vc k n}
    (hw0 : w ≠ 0) : ∃ c : kˣ, c • w ∈ box (Fin (n + 1)) s ∧ c • w ∉ box (Fin (n + 1)) (s * Units.mk0 r hr0) := by
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun j => valuation k (w j)) Finset.univ_nonempty
  have hwi : w i ≠ 0 := by
    intro h
    apply hw0
    funext j
    have := hi j (Finset.mem_univ j)
    rw [h, map_zero] at this
    simpa using le_antisymm this zero_le'
  refine ⟨s * (Units.mk0 (w i) hwi)⁻¹, ?_, ?_⟩
  · intro j _
    show valuation k (((s * (Units.mk0 (w i) hwi)⁻¹ : kˣ) : k) * w j) ≤ valuation k (s : k)
    have hv : valuation k (w i) ≠ 0 := by simpa using hwi
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, map_mul, map_inv₀]
    rw [mul_assoc]
    calc valuation k (s : k) * ((valuation k (w i))⁻¹ * valuation k (w j))
        ≤ valuation k (s : k) * ((valuation k (w i))⁻¹ * valuation k (w i)) :=
          by gcongr; exact hi j (Finset.mem_univ j)
      _ = valuation k (s : k) := by rw [inv_mul_cancel₀ hv, mul_one]
  · intro h
    have := h i (Set.mem_univ i)
    change valuation k (((s * (Units.mk0 (w i) hwi)⁻¹ : kˣ) : k) * w i) ≤ valuation k (((s * Units.mk0 r hr0 : kˣ)) : k) at this
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0] at this
    rw [mul_assoc, inv_mul_cancel₀ hwi, mul_one, map_mul] at this
    have hs : 0 < valuation k (s : k) := by simp [zero_lt_iff]
    have := lt_of_le_of_lt this (by rw [mul_comm]; exact mul_lt_of_lt_one_left hs hr1)
    exact lt_irrefl _ this

theorem finite_range_phi {Λ : (Mx k n → ℂ) →ₗ[ℂ] ℂ} (hP : PInvX Λ) {F : Mx k n × Vc k n → ℂ}
    (hF : F ∈ SB (Mx k n × Vc k n)) : (Set.range (phi Λ F)).Finite := by
  haveI := GlobalTheory.SplitWeil.t2Space (k := k)
  obtain ⟨s, hs⟩ := exists_box_phi_smul hP hF
  obtain ⟨r, hr, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
  have hr0 : r ≠ 0 := by simpa using hr
  set Q := Prod.snd '' tsupport F with hQdef
  have hQ : IsCompact Q := hF.2.image continuous_snd
  set B := box (Fin (n + 1)) s with hBdef
  set B' := box (Fin (n + 1)) (s * Units.mk0 r hr0) with hB'def
  have hBo : IsOpen B := isOpen_box s
  have hB'o : IsOpen B' := isOpen_box _
  have hK1 : IsCompact (Q ∩ Bᶜ) := hQ.inter_right hBo.isClosed_compl
  have hK2 : IsCompact (B ∩ B'ᶜ) := (isCompact_box s).inter_right hB'o.isClosed_compl
  have hf1 : (phi Λ F '' (Q ∩ Bᶜ)).Finite := finite_image_of_eventually hK1 fun x hx =>
    phi_eventually_eq hP hF fun h => hx.2 (h ▸ zero_mem_box s)
  have hf2 : (phi Λ F '' (B ∩ B'ᶜ)).Finite := finite_image_of_eventually hK2 fun x hx =>
    phi_eventually_eq hP hF fun h => hx.2 (h ▸ zero_mem_box _)
  refine ((Set.finite_singleton (0 : ℂ)).union (hf1.union hf2)).subset ?_
  rintro _ ⟨w, rfl⟩
  by_cases hw0 : w = 0
  · left; rw [hw0]; exact phi_zero
  by_cases hwB : w ∈ B
  · obtain ⟨c, hc1, hc2⟩ := exists_smul_shell (s := s) hr0 hr1 hw0
    right; right
    exact ⟨c • w, ⟨hc1, hc2⟩, hs w hwB c hc1⟩
  by_cases hwQ : w ∈ Q
  · right; left; exact ⟨w, ⟨hwQ, hwB⟩, rfl⟩
  · left; exact phi_eq_zero_of_notMem hwQ

end Range

section Meas

variable {n : ℕ} [MeasurableSpace k] [BorelSpace k]

theorem measurable_phi {Λ : (Mx k n → ℂ) →ₗ[ℂ] ℂ} (hP : PInvX Λ) {F : Mx k n × Vc k n → ℂ}
    (hF : F ∈ SB (Mx k n × Vc k n)) : Measurable (phi Λ F) := by
  haveI := GlobalTheory.SplitWeil.t2Space (k := k)
  haveI := GlobalTheory.SplitWeil.secondCountable (k := k)
  intro S _
  have hU : IsOpen (phi Λ F ⁻¹' S ∩ {w | w ≠ 0}) := by
    rw [isOpen_iff_mem_nhds]
    rintro w ⟨hwS, hw0⟩
    filter_upwards [phi_eventually_eq hP hF hw0, isOpen_ne.mem_nhds hw0] with y hy hy0
    exact ⟨by show phi Λ F y ∈ S; rw [hy]; exact hwS, hy0⟩
  have e : phi Λ F ⁻¹' S = (phi Λ F ⁻¹' S ∩ {w | w ≠ 0}) ∪ (phi Λ F ⁻¹' S ∩ {0}) := by
    ext w
    by_cases hw : w = 0 <;> simp [hw]
  rw [e]
  refine hU.measurableSet.union ?_
  by_cases h0 : (0 : Vc k n) ∈ phi Λ F ⁻¹' S
  · rw [Set.inter_eq_right.2 (Set.singleton_subset_iff.2 h0)]
    exact isClosed_singleton.measurableSet
  · rw [Set.inter_singleton_eq_empty.2 h0]
    exact MeasurableSet.empty

end Meas

end PositivityTheory.RgUd.AB.BoxIntegration

namespace PositivityTheory.RgUd.AB.Pf

open PositivityTheory.RgUd.AB PositivityTheory.RgUd.AB.BoxIntegration

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem phiInt : PhiInt k := by
  intro _ _ ν _ n Λ hP F hF
  haveI := GlobalTheory.SplitWeil.t2Space (k := k)
  haveI := GlobalTheory.SplitWeil.secondCountable (k := k)
  obtain ⟨M, hM⟩ := ((finite_range_phi hP hF).image norm).bddAbove
  have hM' : ∀ w, ‖phi Λ F w‖ ≤ M := fun w => hM ⟨_, ⟨w, rfl⟩, rfl⟩
  set Q := Prod.snd '' tsupport F with hQdef
  have hQ : IsCompact Q := hF.2.image continuous_snd
  have hQm : MeasurableSet Q := hQ.isClosed.measurableSet
  have hQfin : (Measure.pi fun _ : Fin (n + 1) => ν) Q < ⊤ := hQ.measure_lt_top
  refine Integrable.mono' (g := Q.indicator fun _ => M) ?_ (measurable_phi hP hF).aestronglyMeasurable
    (Filter.Eventually.of_forall fun w => ?_)
  · exact (integrableOn_const hQfin.ne).integrable_indicator hQm
  · by_cases hw : w ∈ Q
    · rw [Set.indicator_of_mem hw]
      exact hM' w
    · rw [Set.indicator_of_notMem hw, phi_eq_zero_of_notMem hw, norm_zero]

end PositivityTheory.RgUd.AB.Pf
