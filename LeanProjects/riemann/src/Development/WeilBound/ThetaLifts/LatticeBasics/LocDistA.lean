import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactOpenAddSubgroup

open MeasureTheory Filter Topology GlobalTheory.WeilM

namespace GlobalTheory.ThK.Dbl.LD

theorem sb_chart {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] {U : Set X} {T : Set Y} (hU : IsOpen U)
    {e : X → Y} {r : Y → X} (ce : ContinuousOn e U) (cr : ContinuousOn r T) (hre : ∀ x ∈ U, r (e x) = x)
    (hr : ∀ y ∈ T, r y ∈ U) {F : Y → ℂ} (hF : F ∈ SB Y) (hT : ∀ y ∉ T, F y = 0) {G : X → ℂ}
    (h1 : ∀ x ∈ U, G x = F (e x)) (h0 : ∀ x ∉ U, G x = 0) : G ∈ SB X := by
  have hcl : IsClosed (Function.support F) := (hF.1.isClopen_fiber 0).compl.isClosed
  have hc : IsCompact (Function.support F) := hF.2.of_isClosed_subset hcl subset_closure
  have hsub : Function.support F ⊆ T := fun y hy => by_contra fun h => hy (hT y h)
  have hC : IsCompact (r '' Function.support F) := hc.image_of_continuousOn (cr.mono hsub)
  have hz : ∀ x ∉ r '' Function.support F, G x = 0 := fun x hx => by
    by_cases hxU : x ∈ U
    · rw [h1 x hxU]; exact by_contra fun h => hx ⟨e x, h, hre x hxU⟩
    · exact h0 x hxU
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_, HasCompactSupport.intro hC hz⟩
  by_cases hxU : x ∈ U
  · filter_upwards [(ce.continuousAt (hU.mem_nhds hxU)).eventually (hF.1.eventually_eq (e x)), hU.mem_nhds hxU] with y a b
    rw [h1 y b, h1 x hxU, a]
  · have : x ∉ r '' Function.support F := by rintro ⟨y, hy, rfl⟩; exact hxU (hr y (hsub hy))
    filter_upwards [hC.isClosed.isOpen_compl.mem_nhds this] with y hy
    rw [hz y hy, h0 x hxU]

theorem sb_comp {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] (e : X → Y) (r : Y → X)
    (ce : Continuous e) (cr : Continuous r) (hre : ∀ x, r (e x) = x) {F : Y → ℂ} (hF : F ∈ SB Y) :
    (fun x => F (e x)) ∈ SB X :=
  sb_chart (U := Set.univ) (T := Set.univ) isOpen_univ ce.continuousOn cr.continuousOn (fun x _ => hre x)
    (fun _ _ => trivial) hF (fun _ h => absurd trivial h) (fun _ _ => rfl) (fun _ h => absurd trivial h)

theorem sb_tens {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] [T2Space Y] {f : X → ℂ} {g : Y → ℂ}
    (hf : f ∈ SB X) (hg : g ∈ SB Y) : (fun z : X × Y => f z.1 * g z.2) ∈ SB (X × Y) := by
  refine ⟨(hf.1.comp_continuous continuous_fst).mul (hg.1.comp_continuous continuous_snd),
    HasCompactSupport.intro (IsCompact.prod hf.2 hg.2) fun z hz => ?_⟩
  rcases not_and_or.1 hz with h | h
  · rw [image_eq_zero_of_notMem_tsupport h, zero_mul]
  · rw [image_eq_zero_of_notMem_tsupport h, mul_zero]

theorem sb_cut {X : Type} [TopologicalSpace X] [T2Space X] {A : Set X} (hA : IsClopen A) {f : X → ℂ} (hf : f ∈ SB X) :
    A.indicator f ∈ SB X := by
  have : A.indicator f = fun x => A.indicator (fun _ => (1 : ℂ)) x * f x := by
    ext x; by_cases h : x ∈ A <;> simp [h]
  rw [this]
  exact ⟨(LocallyConstant.charFn ℂ hA).isLocallyConstant.mul hf.1, HasCompactSupport.mul_left hf.2⟩

theorem sb_unif {X P : Type} [TopologicalSpace X] [TopologicalSpace P] {φ : X → ℂ} (hφ : φ ∈ SB X) (a : P → X → X) (p : P)
    (ha : Continuous fun z : P × X => a z.1 z.2) (h0 : ∀ x, a p x = x) :
    ∀ᶠ k in 𝓝 p, ∀ x ∈ tsupport φ, φ (a k x) = φ x := by
  apply IsCompact.eventually_forall_of_forall_eventually hφ.2
  intro y _
  have e := hφ.1.eventually_eq y
  have t1 : Tendsto (fun z : P × X => a z.1 z.2) (𝓝 (p, y)) (𝓝 y) := by simpa [h0] using ha.tendsto (p, y)
  filter_upwards [t1.eventually e, (continuous_snd.tendsto (p, y)).eventually e] with z h1 h2
  rw [h1, h2]

theorem kill_tens {X V : Type} [TopologicalSpace X] [T2Space X] [AddCommGroup V] [TopologicalSpace V]
    [NonarchimedeanAddGroup V] [LocallyCompactSpace V] [T2Space V] (S : Set X) (l : (X × V → ℂ) →ₗ[ℂ] ℂ)
    (h : ∀ f ∈ SB X, (∀ x ∉ S, f x = 0) → ∀ g ∈ SB V, l (fun z => f z.1 * g z.2) = 0)
    {F : X × V → ℂ} (hF : F ∈ SB (X × V)) (hS : ∀ z : X × V, z.1 ∉ S → F z = 0) : l F = 0 := by
  classical
  obtain ⟨K₁, hK₁⟩ := NonarchimedeanAddGroup.is_nonarchimedean _
    (sb_unif hF (fun (k : V) z => (z.1, z.2 + k)) 0 (by fun_prop) (by simp))
  obtain ⟨K₀, hK₀⟩ := HaarUniq.exists_compact_openAddSubgroup (V := V)
  set K := K₀ ⊓ K₁
  have hK : IsCompact (K : Set V) := hK₀.of_isClosed_subset K.isClosed (fun x hx => hx.1)
  have hinv : ∀ k ∈ K, ∀ x v, F (x, v + k) = F (x, v) := fun k hk x v => by
    by_cases hx : (x, v) ∈ tsupport F
    · exact hK₁ hk.2 _ hx
    · by_cases hx' : (x, v + k) ∈ tsupport F
      · simpa using (hK₁ (neg_mem hk.2 : -k ∈ K₁) _ hx').symm
      · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx']
  haveI : DiscreteTopology (V ⧸ K.toAddSubgroup) := QuotientAddGroup.discreteTopology K.isOpen
  have hfin : ((fun z : X × V => (z.2 : V ⧸ K.toAddSubgroup)) '' tsupport F).Finite :=
    (IsCompact.image hF.2 (QuotientAddGroup.continuous_mk.comp continuous_snd)).finite_of_discrete
  have hmem : ∀ (x : V) (q : V ⧸ K.toAddSubgroup), x + -q.out ∈ (K : Set V) ↔ q = (x : V ⧸ K.toAddSubgroup) := by
    intro x q
    conv_rhs => rw [← QuotientAddGroup.out_eq' q, QuotientAddGroup.eq]
    rw [add_comm]; rfl
  have : F = ∑ q ∈ hfin.toFinset, fun z : X × V =>
      F (z.1, q.out) * Set.indicator (K : Set V) (fun _ => (1 : ℂ)) (z.2 + -q.out) := by
    ext ⟨x, v⟩
    have hx : F (x, (v : V ⧸ K.toAddSubgroup).out) = F (x, v) := by
      rw [← hinv _ ((hmem v _).2 rfl) x]; congr 2; abel
    rw [Finset.sum_apply, Finset.sum_eq_single (v : V ⧸ K.toAddSubgroup)]
    · rw [Set.indicator_of_mem ((hmem v _).2 rfl), hx, mul_one]
    · intro q _ hq
      rw [Set.indicator_of_notMem (fun h => hq ((hmem v q).1 h)), mul_zero]
    · intro h
      rw [hx, image_eq_zero_of_notMem_tsupport (f := F) (x := (x, v)), zero_mul]
      exact fun hs => h (hfin.mem_toFinset.2 ⟨_, hs, rfl⟩)
  rw [this, map_sum]
  refine Finset.sum_eq_zero fun q _ => ?_
  exact h (fun x => F (x, q.out)) (sb_comp (fun x => (x, q.out)) Prod.fst (by fun_prop) (by fun_prop) (fun _ => rfl) hF)
    (fun x hx => hS _ hx) (fun v => Set.indicator (K : Set V) (fun _ => (1 : ℂ)) (v + -q.out))
    (sb_comp (fun v => v + -q.out) (fun v => v + q.out) (by fun_prop) (by fun_prop) (by simp) (HaarUniq.indicator_mem K hK))

theorem kill_loc {V : Type} [AddCommGroup V] [TopologicalSpace V] [NonarchimedeanAddGroup V] [T2Space V]
    (l : (V → ℂ) →ₗ[ℂ] ℂ) {φ : V → ℂ} (hφ : φ ∈ SB V)
    (h : ∀ x, φ x ≠ 0 → ∃ U ∈ 𝓝 x, ∀ ψ ∈ SB V, (∀ y ∉ U, ψ y = 0) → l ψ = 0) : l φ = 0 := by
  have hcl : IsClosed (Function.support φ) := (hφ.1.isClopen_fiber 0).compl.isClosed
  have hc : IsCompact (Function.support φ) := hφ.2.of_isClosed_subset hcl subset_closure
  have : ∃ A, IsClopen A ∧ Function.support φ ⊆ A ∧ ∀ ψ ∈ SB V, (∀ y ∉ A, ψ y = 0) → l ψ = 0 := by
    refine hc.induction_on (p := fun s => ∃ A, IsClopen A ∧ s ⊆ A ∧ ∀ ψ ∈ SB V, (∀ y ∉ A, ψ y = 0) → l ψ = 0)
      ⟨∅, isClopen_empty, subset_rfl, fun ψ _ h => ?_⟩ ?_ ?_ ?_
    · rw [show ψ = 0 from funext fun y => h y (by simp), map_zero]
    · rintro s t hst ⟨A, h1, h2, h3⟩; exact ⟨A, h1, hst.trans h2, h3⟩
    · rintro s t ⟨A, h1, h2, h3⟩ ⟨B, k1, k2, k3⟩
      refine ⟨A ∪ B, h1.union k1, Set.union_subset_union h2 k2, fun ψ hψ h => ?_⟩
      rw [← Set.indicator_self_add_compl A ψ, map_add, h3 _ (sb_cut h1 hψ) (fun y hy => Set.indicator_of_notMem hy _),
        k3 _ (sb_cut h1.compl hψ), add_zero]
      intro y hy
      by_cases hA : y ∈ A
      · exact Set.indicator_of_notMem (not_not.2 hA) _
      · rw [Set.indicator_of_mem hA]; exact h y (not_or.2 ⟨hA, hy⟩)
    · intro x hx
      obtain ⟨U, hU, hl⟩ := h x hx
      have : (fun k => k + x) ⁻¹' U ∈ 𝓝 (0 : V) := (continuous_add_right x).continuousAt.preimage_mem_nhds (by simpa using hU)
      obtain ⟨K, hK⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ this
      have hA : IsClopen ((fun y => y - x) ⁻¹' (K : Set V)) := K.isClopen.preimage (by fun_prop)
      refine ⟨_, mem_nhdsWithin_of_mem_nhds (hA.isOpen.mem_nhds (by simp)), _, hA, subset_rfl,
        fun ψ hψ h0 => hl ψ hψ fun y hy => h0 y fun hy' => hy ?_⟩
      simpa using hK hy'
  obtain ⟨A, -, h2, h3⟩ := this
  exact h3 φ hφ fun y hy => by_contra fun h => hy (h2 h)

def Bump {V : Type} [Zero V] [TopologicalSpace V] (g : V → ℂ) : Prop := g ∈ SB V ∧ (∀ x, g x = 0 ∨ g x = 1) ∧ g 0 = 1

theorem exists_bump (V : Type) [AddCommGroup V] [TopologicalSpace V] [NonarchimedeanAddGroup V] [LocallyCompactSpace V]
    [T2Space V] : ∃ g : V → ℂ, Bump g := by
  obtain ⟨K, hK⟩ := HaarUniq.exists_compact_openAddSubgroup (V := V)
  refine ⟨_, HaarUniq.indicator_mem K hK, fun x => ?_, Set.indicator_of_mem K.zero_mem _⟩
  by_cases h : x ∈ (K : Set V) <;> simp [h]

theorem bump_ratio {V : Type} [AddCommGroup V] [TopologicalSpace V] [NonarchimedeanAddGroup V] [LocallyCompactSpace V]
    [T2Space V] {g₀ g₁ : V → ℂ} (h₀ : Bump g₀) (h₁ : Bump g₁) : ∃ s : ℝ, 0 < s ∧ ∀ m : (V → ℂ) →ₗ[ℂ] ℂ,
      (∀ φ ∈ SB V, ∀ a : V, m (fun x => φ (x + a)) = m φ) → m g₀ = s * m g₁ ∧ (m g₀ = 0 → ∀ g ∈ SB V, m g = 0) := by
  borelize V
  let μ : Measure V := Measure.addHaar
  have pos : ∀ g : V → ℂ, Bump g → ∃ s : ℝ, 0 < s ∧ ∫ x, g x ∂μ = s := fun g hg => by
    refine ⟨∫ x, (g x).re ∂μ, ?_, ?_⟩
    · refine (Complex.continuous_re.comp hg.1.1.continuous).integral_pos_of_hasCompactSupport_nonneg_nonzero
        (hg.1.2.comp_left (g := Complex.re) rfl) (fun x => ?_) (x := 0) (by simp [hg.2.2])
      rcases hg.2.1 x with h | h <;> simp [h]
    · rw [← integral_complex_ofReal]
      congr 1; ext x; rcases hg.2.1 x with h | h <;> simp [h]
  obtain ⟨a, ha, ea⟩ := pos _ h₀
  obtain ⟨b, hb, eb⟩ := pos _ h₁
  refine ⟨a / b, div_pos ha hb, fun m hm => ?_⟩
  obtain ⟨c, hc⟩ := HaarUniq.exists_eq_mul_integral V μ m hm
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  rw [hc _ h₀.1, hc _ h₁.1, ea, eb]
  refine ⟨by push_cast; field_simp, fun h g hg => ?_⟩
  rw [hc g hg, (mul_eq_zero.1 h).resolve_right ha', zero_mul]

theorem nonarch_pi (ι V : Type) [Finite ι] [AddCommGroup V] [TopologicalSpace V] [NonarchimedeanAddGroup V] :
    NonarchimedeanAddGroup (ι → V) where
  is_nonarchimedean U hU := by
    rw [nhds_pi, Filter.mem_pi] at hU
    obtain ⟨I, -, t, ht, hU⟩ := hU
    choose K hK using fun i => NonarchimedeanAddGroup.is_nonarchimedean (t i) (ht i)
    exact ⟨⟨AddSubgroup.pi Set.univ fun i => (K i).toAddSubgroup, isOpen_set_pi Set.finite_univ fun i _ => (K i).isOpen⟩,
      fun x hx => hU fun i _ => hK i (hx i trivial)⟩

end GlobalTheory.ThK.Dbl.LD
