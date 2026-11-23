import Development.WeilBound.ThetaLifts.EigenvalueEndgame.CuspidalAverages.ZariskiLocallyAffineLine

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace PositivityTheory.ThKEnd.Cusp

open Filter Topology GlobalTheory.WeilM Matrix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ}

variable (k) in
theorem local_field_t2Space : T2Space k := by
  letI := IsTopologicalAddGroup.rightUniformSpace k
  haveI := isUniformAddGroup_of_addCommGroup (G := k)
  infer_instance

variable (k) in
theorem loc_neBot : NeBot (𝓝[≠] (0 : k)) := by
  rw [← mem_closure_iff_nhdsWithin_neBot, mem_closure_iff_nhds]
  intro s hs
  obtain ⟨r, hr, hrs⟩ := (IsValuativeTopology.hasBasis_nhds_zero' k).mem_iff.mp hs
  obtain ⟨p, hp0, hp⟩ := Valuation.IsNontrivial.exists_lt_one (v := ValuativeRel.valuation k)
  obtain ⟨y, rfl⟩ := ValuativeRel.valuation_surjective r
  have hy : y ≠ 0 := by simpa using hr
  refine ⟨y * p, hrs ?_, mul_ne_zero hy (by simpa using hp0)⟩
  show ValuativeRel.valuation k (y * p) < _
  rw [map_mul]
  exact mul_lt_of_lt_one_right (zero_lt_iff.2 hr) hp

variable (k n d) in

def intM : AddSubgroup (Matrix (Fin n) (Fin d) k) where
  carrier := {Y | ∀ a b, ValuativeRel.valuation k (Y a b) ≤ 1}
  zero_mem' := fun a b => by simp
  add_mem' := fun {x y} hx hy a b => Valuation.map_add_le _ (hx a b) (hy a b)
  neg_mem' := fun {x} hx a b => by simpa using hx a b

theorem intM_open : IsOpen (intM k n d : Set (Matrix (Fin n) (Fin d) k)) := by
  refine AddSubgroup.isOpen_of_mem_nhds _ (g := 0) ?_
  have h : {x : k | ValuativeRel.valuation k x < 1} ∈ 𝓝 (0 : k) := (IsValuativeTopology.hasBasis_nhds_zero' k).mem_of_mem one_ne_zero
  have h2 : ∀ᶠ Y : Matrix (Fin n) (Fin d) k in 𝓝 0, ∀ a b, ValuativeRel.valuation k (Y a b) < 1 :=
    eventually_all.2 fun a => eventually_all.2 fun b =>
      (show Continuous fun Y : Matrix (Fin n) (Fin d) k => Y a b by fun_prop).continuousAt.eventually_mem
        (s := {x : k | ValuativeRel.valuation k x < 1}) h
  exact h2.mono fun Y hY a b => (hY a b).le

theorem intM_compact : IsCompact (intM k n d : Set (Matrix (Fin n) (Fin d) k)) := by
  have h := isCompact_univ_pi fun _ : Fin n => isCompact_univ_pi fun _ : Fin d => IsNonarchimedeanLocalField.isCompact_closedBall k 1
  have e : (intM k n d : Set (Matrix (Fin n) (Fin d) k)) =
      Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin d => {x : k | ValuativeRel.valuation k x ≤ 1} :=
    Set.ext fun Y => ⟨fun h a _ b _ => h a b, fun h a b => h a trivial b trivial⟩
  rw [e]
  exact h

def colL (i : Fin d) (ρ : Fin d → k) : Matrix (Fin n) (Fin d) k →ₗ[k] Matrix (Fin n) (Fin d) k where
  toFun Y := vecMulVec (fun a => Y a i) ρ
  map_add' Y Z := by ext a b; simp [vecMulVec_apply, add_mul]
  map_smul' c Y := by ext a b; simp [vecMulVec_apply, mul_assoc]

theorem colL_apply (i : Fin d) (ρ : Fin d → k) (Y : Matrix (Fin n) (Fin d) k) (a b) : colL i ρ Y a b = Y a i * ρ b := rfl

theorem colL_colL {i j : Fin d} {ρ ρ' : Fin d → k} (h : ρ' i = 0) (Y : Matrix (Fin n) (Fin d) k) : colL i ρ (colL j ρ' Y) = 0 := by
  ext a b; simp [colL_apply, h]

theorem colL_cont (i : Fin d) {ρ : Matrix (Fin n) (Fin d) k → Fin d → k} {Y₀ : Matrix (Fin n) (Fin d) k} (h : ContinuousAt ρ Y₀) (v) :
    ContinuousAt (fun p : Matrix (Fin n) (Fin d) k × Matrix (Fin n) (Fin d) k => colL i (ρ p.1) p.2) (Y₀, v) :=
  continuousAt_pi.2 fun a => continuousAt_pi.2 fun b => by
    have h1 : ContinuousAt (fun p : Matrix (Fin n) (Fin d) k × Matrix (Fin n) (Fin d) k => ρ p.1 b) (Y₀, v) :=
      ContinuousAt.comp (g := fun Y => ρ Y b) (f := Prod.fst) (continuousAt_pi.1 h b) continuousAt_fst
    exact (show Continuous fun p : Matrix (Fin n) (Fin d) k × Matrix (Fin n) (Fin d) k => p.2 a i by fun_prop).continuousAt.mul h1

theorem sb_sq {φ : Matrix (Fin n) (Fin d) k → ℂ} (hφ : φ ∈ SB _) (C : Matrix (Fin n) (Fin d) k →ₗ[k] Matrix (Fin n) (Fin d) k)
    (hc : Continuous C) (h : ∀ v, C (C v) = 0) : (fun y => φ (y + C y)) ∈ SB (Matrix (Fin n) (Fin d) k) := by
  haveI := local_field_t2Space k
  exact sb_comp hφ (f := fun y => y + C y) (g := fun y => y - C y) (by fun_prop) (by fun_prop) fun x => by simp [h]

theorem exists_ne_one {ψ : AddChar k ℂ} (h : ψ ≠ 1) : ∃ t, ψ t ≠ 1 := by
  by_contra e
  push Not at e
  exact h (AddChar.ext _ _ e)

variable {ψ : AddChar k ℂ} {i₀ i₁ i₂ : Fin d} {ξ : kˣ →* ℂˣ} {l : (Matrix (Fin n) (Fin d) k → ℂ) →ₗ[ℂ] ℂ}

theorem killsM {U : Set (Matrix (Fin n) (Fin d) k)} (h : ∀ Y₀ ∈ U, ∃ Ω ∈ 𝓝 Y₀, Kills l Ω) : Kills l U := by
  haveI := loc_neBot k
  exact kills_of_local (V := Matrix (Fin n) (Fin d) k) k (Λ := intM k n d) (intM_open (k := k) (n := n) (d := d))
    (intM_compact (k := k) (n := n) (d := d)) l h

theorem deadM {U : Set (Matrix (Fin n) (Fin d) k)} (hU : Kills l U) (Y₀ : Matrix (Fin n) (Fin d) k)
    (A B : Matrix (Fin n) (Fin d) k → Matrix (Fin n) (Fin d) k →ₗ[k] Matrix (Fin n) (Fin d) k)
    (hA : ∀ v, ContinuousAt (fun p : Matrix (Fin n) (Fin d) k × Matrix (Fin n) (Fin d) k => A p.1 p.2) (Y₀, v))
    (hB : ∀ v, ContinuousAt (fun p : Matrix (Fin n) (Fin d) k × Matrix (Fin n) (Fin d) k => B p.1 p.2) (Y₀, v))
    (hA0 : ∀ v, A Y₀ (A Y₀ v) = 0) (hB0 : ∀ v, B Y₀ (B Y₀ v) = 0) (hAB : ∀ v, A Y₀ (B Y₀ v) = B Y₀ (A Y₀ v))
    (h : ∀ᶠ Y in 𝓝 Y₀, Y ∉ U → ((∀ v, A Y (A Y v) = 0) ∧ (∀ v, B Y (B Y v) = 0) ∧ Y + B Y Y + A Y (Y + B Y Y) = Y ∧
      ∃ c : ℂ, c ≠ 1 ∧ ∀ φ ∈ SB (Matrix (Fin n) (Fin d) k), l (fun y => φ (y + B Y y + A Y (y + B Y y))) = c * l φ)) :
    ∃ Ω ∈ 𝓝 Y₀, Kills l Ω := by
  haveI := loc_neBot k
  exact dead (V := Matrix (Fin n) (Fin d) k) (k := k) (Λ₀ := intM k n d) (intM_open (k := k) (n := n) (d := d))
    (intM_compact (k := k) (n := n) (d := d)) l hU Y₀ A B hA hB hA0 hB0 hAB (h.mono fun Y hY => or_iff_not_imp_left.2 hY)

theorem exists_rows {x y : Fin n → k} (h : LinearIndependent k ![x, y]) :
    ∃ μ ν : Fin n → k, μ ⬝ᵥ x = 0 ∧ μ ⬝ᵥ y = 1 ∧ ν ⬝ᵥ x = 1 := by
  have key : ∀ j : Fin 2, ∃ μ : Fin n → k, ∀ i, μ ⬝ᵥ ![x, y] i = if j = i then 1 else 0 := fun j => by
    obtain ⟨g, hg⟩ := LinearMap.exists_extend ((Finsupp.lapply j : (Fin 2 →₀ k) →ₗ[k] k) ∘ₗ h.repr)
    refine ⟨fun a => g (Pi.single a 1), fun i => ?_⟩
    have h1 : g (![x, y] i) = if j = i then 1 else 0 := by
      have := LinearMap.congr_fun hg ⟨![x, y] i, Submodule.subset_span ⟨i, rfl⟩⟩
      rw [LinearMap.comp_apply, LinearMap.comp_apply, h.repr_eq_single i _ rfl] at this
      simpa [Finsupp.single_apply, eq_comm] using this
    rw [← h1, LinearMap.pi_apply_eq_sum_univ g, dotProduct]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [smul_eq_mul, mul_comm]
    congr 2
    funext b
    simp [Pi.single_apply, eq_comm]
  obtain ⟨μ, hμ⟩ := key 1
  obtain ⟨ν, hν⟩ := key 0
  exact ⟨μ, ν, by simpa using hμ 0, by simpa using hμ 1, by simpa using hν 0⟩

theorem kills_indep (hψ : ψ ≠ 1) (hL : LeftLaw ξ l) (hC : ColLaw ψ {i₀} i₀ i₁ l) :
    Kills l {Y | LinearIndependent k ![fun a => Y a i₀, fun a => Y a i₁]} := by
  obtain ⟨t, ht⟩ := exists_ne_one hψ
  refine killsM fun Y₀ hY => ?_
  obtain ⟨μ, ν, h1, h2, h3⟩ := exists_rows hY
  let c₀ : Matrix (Fin n) (Fin d) k → Fin n → k := fun Y a => Y a i₀
  let c₁ : Matrix (Fin n) (Fin d) k → Fin n → k := fun Y a => Y a i₁
  let Dt : Matrix (Fin n) (Fin d) k → k := fun Y => (ν ⬝ᵥ c₀ Y) * (μ ⬝ᵥ c₁ Y) - (μ ⬝ᵥ c₀ Y) * (ν ⬝ᵥ c₁ Y)
  let lam : Matrix (Fin n) (Fin d) k → Fin n → k := fun Y => (Dt Y)⁻¹ • ((ν ⬝ᵥ c₀ Y) • μ - (μ ⬝ᵥ c₀ Y) • ν)
  have cD : Continuous Dt := by simp only [Dt, c₀, c₁]; fun_prop
  have hD : Dt Y₀ ≠ 0 := by simp only [Dt, c₀, c₁, h1, h2, h3]; simp
  have cl : ContinuousAt lam Y₀ := (cD.continuousAt.inv₀ hD).smul (by simp only [c₀]; fun_prop)
  have l0 : ∀ Y, lam Y ⬝ᵥ c₀ Y = 0 := fun Y => by
    simp only [lam, smul_dotProduct, sub_dotProduct, smul_eq_mul]; ring
  have l1 : ∀ Y, Dt Y ≠ 0 → lam Y ⬝ᵥ c₁ Y = 1 := fun Y hY => by
    simp only [lam, smul_dotProduct, sub_dotProduct, smul_eq_mul]
    exact inv_mul_cancel₀ hY
  let N : Matrix (Fin n) (Fin d) k → Matrix (Fin n) (Fin n) k := fun Y => vecMulVec (-t • c₀ Y) (lam Y)
  have hN : ∀ Y, N Y * N Y = 0 := fun Y => by
    simp only [N, vecMulVec_mul_vecMulVec, dotProduct_smul, l0]; simp
  let A : Matrix (Fin n) (Fin d) k → Matrix (Fin n) (Fin d) k →ₗ[k] Matrix (Fin n) (Fin d) k := fun Y =>
    { toFun := fun v => N Y * v, map_add' := Matrix.mul_add _, map_smul' := fun c v => Matrix.mul_smul _ c v }
  have hA : ∀ Y v, A Y v = N Y * v := fun _ _ => rfl
  have hAA : ∀ Y v, A Y (A Y v) = 0 := fun Y v => by rw [hA, hA, ← Matrix.mul_assoc, hN, Matrix.zero_mul]
  let ρ : Matrix (Fin n) (Fin d) k → Fin d → k := fun Y b => t * (lam Y ⬝ᵥ fun a => Y a b)
  have r0 : ∀ Y, ρ Y i₀ = 0 := fun Y => by simp only [ρ]; rw [l0 Y, mul_zero]
  have cN : ContinuousAt N Y₀ := continuousAt_pi.2 fun a => continuousAt_pi.2 fun b =>
    (show Continuous fun Y => (-t • c₀ Y) a by simp only [c₀]; fun_prop).continuousAt.mul (continuousAt_pi.1 cl b)
  have hAe : ∀ Y v a b, A Y v a b = -t * Y a i₀ * (lam Y ⬝ᵥ fun a => v a b) := fun Y v a b => by
    simp only [hA, N, c₀, mul_apply, vecMulVec_apply, dotProduct, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, mul_assoc]
  refine deadM (U := ∅) (fun φ _ h => by
    rw [show φ = 0 from funext fun y => by by_contra e; exact h y e, map_zero]) Y₀ A (fun Y => colL i₀ (ρ Y)) (fun v => ?_)
    (fun v => ?_) (hAA Y₀) (fun v => colL_colL (r0 Y₀) v) (fun v => ?_) ?_
  · have e : ContinuousAt (fun p : Matrix (Fin n) (Fin d) k × Matrix (Fin n) (Fin d) k => (N p.1, p.2)) (Y₀, v) :=
      (ContinuousAt.comp (g := N) (f := Prod.fst) cN continuousAt_fst).prodMk continuousAt_snd
    exact ContinuousAt.comp (g := fun q : Matrix (Fin n) (Fin n) k × Matrix (Fin n) (Fin d) k => q.1 * q.2)
      (continuous_fst.matrix_mul continuous_snd).continuousAt e
  · refine colL_cont i₀ (ρ := ρ) (continuousAt_pi.2 fun b => continuousAt_const.mul ?_) v
    exact ContinuousAt.comp (g := fun q : (Fin n → k) × (Fin n → k) => q.1 ⬝ᵥ q.2) (f := fun Y => (lam Y, fun a => Y a b))
      (continuous_fst.dotProduct continuous_snd).continuousAt (cl.prodMk (continuous_pi fun a =>
        show Continuous fun Y : Matrix (Fin n) (Fin d) k => Y a b by fun_prop).continuousAt)
  · ext a b
    simp only [hA, colL_apply, mul_apply, Finset.sum_mul, mul_assoc]
  · filter_upwards [cD.continuousAt.eventually_ne hD] with Y hDY
    refine fun _ => ⟨hAA Y, colL_colL (r0 Y), ?_, ψ t, ht, fun φ hφ => ?_⟩
    · ext a b
      have e : (lam Y ⬝ᵥ fun a => Y a b + Y a i₀ * ρ Y b) = lam Y ⬝ᵥ fun a => Y a b := by
        have := l0 Y
        simp only [dotProduct, mul_add, Finset.sum_add_distrib, ← mul_assoc, ← Finset.sum_mul, c₀] at this ⊢
        rw [this, zero_mul, add_zero]
      simp only [Matrix.add_apply, hAe, colL_apply, e]
      simp only [ρ]
      ring
    · let γ : GL (Fin n) k := ⟨1 + N Y, 1 - N Y, by rw [add_mul, mul_sub, mul_sub, hN]; simp, by rw [sub_mul, mul_add, mul_add, hN]; simp⟩
      have hγ : Matrix.GeneralLinearGroup.det γ = 1 := Units.ext (by
        show (1 + N Y).det = 1
        simp only [N]
        rw [vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, dotProduct_smul, l0]; simp)
      have e1 := hL φ hφ γ
      rw [hγ, map_one, Units.val_one, one_mul] at e1
      have e0 : ∀ y : Matrix (Fin n) (Fin d) k, γ.1 * y = y + A Y y := fun y => by
        show (1 + N Y) * y = _
        rw [Matrix.add_mul, Matrix.one_mul, hA]
      simp only [e0] at e1
      have e2 := hC _ (sb_sq hφ (A Y) (continuous_const.matrix_mul continuous_id) (hAA Y)) (ρ Y) (by simpa using r0 Y)
      rw [e1, show ρ Y i₁ = t from by simp only [ρ]; rw [l1 Y hDY, mul_one]] at e2
      exact e2

theorem locSupp : LocSupp := fun _ _ _ _ _ _ _ _ hψ _ _ _ _ _ hL hC φ hφ h =>
  kills_indep hψ hL hC φ hφ fun y hy => by
    by_contra e
    exact hy (h y e)

theorem kills_ne (hψ : ψ ≠ 1) (h01 : i₀ ≠ i₁) (h02 : i₀ ≠ i₂) (h12 : i₁ ≠ i₂) (hL : LeftLaw ξ l) (hC : ColLaw ψ {i₀} i₀ i₁ l)
    (hC' : ColLaw ψ {i₀, i₁} i₁ i₂ l) : Kills l {Y | (fun a => Y a i₀) ≠ 0} := by
  obtain ⟨t, ht⟩ := exists_ne_one hψ
  refine killsM fun Y₀ hY => ?_
  obtain ⟨a₀, ha⟩ : ∃ a, Y₀ a i₀ ≠ 0 := Function.ne_iff.1 hY
  have cc : Continuous fun Y : Matrix (Fin n) (Fin d) k => Y a₀ i₀ := by fun_prop
  let ρ : Matrix (Fin n) (Fin d) k → Fin d → k := fun Y => Pi.single i₂ (-t * (Y a₀ i₁ * (Y a₀ i₀)⁻¹))
  have cρ : ContinuousAt ρ Y₀ :=
    ContinuousAt.comp (g := fun x : k => (Pi.single i₂ x : Fin d → k)) (continuous_single i₂).continuousAt
      (continuousAt_const.mul ((show Continuous fun Y : Matrix (Fin n) (Fin d) k => Y a₀ i₁ by fun_prop).continuousAt.mul
        (cc.continuousAt.inv₀ ha)))
  have s0 : ∀ x : k, (Pi.single i₂ x : Fin d → k) i₀ = 0 := fun x => Pi.single_eq_of_ne h02 _
  have s1 : ∀ x : k, (Pi.single i₂ x : Fin d → k) i₁ = 0 := fun x => Pi.single_eq_of_ne h12 _
  refine deadM (kills_indep hψ hL hC) Y₀ (fun _ => colL i₁ (Pi.single i₂ t)) (fun Y => colL i₀ (ρ Y))
    (fun v => ?_) (fun v => ?_) (fun v => ?_) (fun v => ?_) (fun v => ?_) ?_
  · exact colL_cont i₁ (ρ := fun _ => Pi.single i₂ t) continuousAt_const v
  · exact colL_cont i₀ (ρ := ρ) cρ v
  · exact colL_colL (s1 _) v
  · exact colL_colL (s0 _) v
  · exact (colL_colL (s1 _) v).trans (colL_colL (s0 _) v).symm
  filter_upwards [cc.continuousAt.eventually_ne ha] with Y hY
  refine fun hd => ⟨colL_colL (s1 _), colL_colL (s0 _), ?_, ψ t, ht, fun φ hφ => ?_⟩
  · have hx : (fun a => Y a i₀) ≠ 0 := fun e => hY (congrFun e a₀)
    obtain ⟨s, hs⟩ : ∃ s : k, s • (fun a => Y a i₀) = fun a => Y a i₁ := by
      by_contra e
      push Not at e
      exact hd ((LinearIndependent.pair_iff' hx).2 e)
    have hs' : ∀ a, Y a i₁ = s * Y a i₀ := fun a => (congrFun hs a).symm
    ext a b
    simp only [Matrix.add_apply, colL_apply, ρ, s1, hs', Pi.single_apply]
    split_ifs
    · field_simp
      ring
    · simp
  · have e1 := hC' φ hφ (Pi.single i₂ t) (by rintro s (rfl | rfl); exacts [s0 _, s1 _])
    have e2 := hC _ (sb_sq hφ (colL i₁ (Pi.single i₂ t)) (continuous_matrix fun a b =>
      show Continuous fun Y : Matrix (Fin n) (Fin d) k => Y a i₁ * (Pi.single i₂ t : Fin d → k) b by fun_prop) (colL_colL (s1 _))) (ρ Y) (by simpa using s0 _)
    rw [show ρ Y i₁ = 0 from s1 _, AddChar.map_zero_eq_one, one_mul] at e2
    rw [Pi.single_eq_same] at e1
    exact e2.trans e1

theorem locThree : LocThree := by
  intro k _ _ _ _ n d ψ hψ i₀ i₁ i₂ h01 h02 h12 ξ l hL hC hC' φ hφ
  obtain ⟨t, ht⟩ := exists_ne_one hψ
  refine killsM (l := l) (U := Set.univ) (fun Y₀ _ => ?_) φ hφ fun _ _ => trivial
  have s0 : (Pi.single i₁ t : Fin d → k) i₀ = 0 := Pi.single_eq_of_ne h01 _
  refine deadM (kills_ne hψ h01 h02 h12 hL hC hC') Y₀ (fun _ => 0) (fun _ => colL i₀ (Pi.single i₁ t))
    (fun _ => ?_) (fun v => ?_) (fun _ => ?_) (fun v => ?_) (fun v => ?_) (Eventually.of_forall fun Y hd => ?_)
  · simpa using continuousAt_const
  · exact colL_cont i₀ (ρ := fun _ => Pi.single i₁ t) continuousAt_const v
  · simp
  · exact colL_colL s0 v
  · simp
  refine ⟨fun _ => by simp, fun v => colL_colL s0 v, ?_, ψ t, ht, fun φ hφ => ?_⟩
  · have hx : ∀ a, Y a i₀ = 0 := congrFun (not_not.1 hd)
    ext a b
    simp [colL_apply, hx]
  · have e := hC φ hφ (Pi.single i₁ t) (by simpa using s0)
    rw [Pi.single_eq_same] at e
    simp only [LinearMap.zero_apply, add_zero]
    exact e

end PositivityTheory.ThKEnd.Cusp

end
