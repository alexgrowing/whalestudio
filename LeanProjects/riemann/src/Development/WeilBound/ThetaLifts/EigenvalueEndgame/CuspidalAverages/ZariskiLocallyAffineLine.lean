import Development.WeilBound.ThetaLifts.EigenvalueEndgame.CuspidalAverages.KeyThree

noncomputable section

set_option linter.unusedSectionVars false

namespace PositivityTheory.ThKEnd.Cusp

open Filter Topology GlobalTheory.WeilM

variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]

def Kills (l : (V → ℂ) →ₗ[ℂ] ℂ) (U : Set V) : Prop := ∀ φ ∈ SB V, (∀ y, φ y ≠ 0 → y ∈ U) → l φ = 0

def cosI (L : AddSubgroup V) (x : V) : V → ℂ := Set.indicator {y | y - x ∈ L} 1

theorem cosI_of_mem {L : AddSubgroup V} {x y : V} (h : y - x ∈ L) : cosI L x y = 1 :=
  Set.indicator_of_mem (show y ∈ {y | y - x ∈ L} from h) _

theorem cosI_of_not {L : AddSubgroup V} {x y : V} (h : y - x ∉ L) : cosI L x y = 0 :=
  Set.indicator_of_notMem (show y ∉ {y | y - x ∈ L} from h) _

theorem cosI_mem {L : AddSubgroup V} (ho : IsOpen (L : Set V)) (hc : IsCompact (L : Set V)) (x : V) : cosI L x ∈ SB V := by
  have h1 : IsClopen {y | y - x ∈ L} :=
    IsClopen.preimage (f := fun y => y - x) ⟨L.isClosed_of_isOpen ho, ho⟩ (by fun_prop)
  refine ⟨(LocallyConstant.indicator (1 : LocallyConstant V ℂ) h1).2,
    HasCompactSupport.intro' (hc.image (f := fun v => v + x) (by fun_prop)) ?_ fun y hy => cosI_of_not fun e => hy ⟨y - x, e, by simp⟩⟩
  convert h1.1 using 1
  ext y
  exact ⟨by rintro ⟨v, hv, rfl⟩; simpa using hv, fun e => ⟨y - x, e, by simp⟩⟩

theorem sb_comp {X : Type} [TopologicalSpace X] [T2Space X] {φ : X → ℂ} (hφ : φ ∈ SB X) {f g : X → X} (hf : Continuous f)
    (hg : Continuous g) (h : ∀ x, g (f x) = x) : (fun x => φ (f x)) ∈ SB X :=
  ⟨hφ.1.comp_continuous hf, HasCompactSupport.intro (hφ.2.isCompact.image hg) fun x hx => by
    by_contra e
    exact hx ⟨f x, subset_closure e, h x⟩⟩

theorem decomp (l : (V → ℂ) →ₗ[ℂ] ℂ) (L : AddSubgroup V) (s : Finset V) : ∀ φ : V → ℂ, (∀ x, ∀ v ∈ L, φ (x + v) = φ x) →
    (∀ y, φ y ≠ 0 → ∃ c ∈ s, y - c ∈ L) → (∀ x, φ x ≠ 0 → l (cosI L x) = 0) → l φ = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro φ _ h0 _
    have : φ = 0 := funext fun y => by by_contra e; simpa using h0 y e
    rw [this, map_zero]
  | insert c s _ ih =>
    intro φ hφ h0 h1
    have e0 : ∀ y, y - c ∈ L → (φ - φ c • cosI L c) y = 0 := fun y hy => by
      have := hφ c _ hy
      rw [add_sub_cancel] at this
      simp [cosI_of_mem hy, this]
    have e1 : ∀ y, y - c ∉ L → (φ - φ c • cosI L c) y = φ y := fun y hy => by simp [cosI_of_not hy]
    have h2 := ih (φ - φ c • cosI L c) (fun x v hv => by
      by_cases hx : x - c ∈ L
      · rw [e0 x hx, e0 _ (by convert add_mem hx hv using 1; abel)]
      · rw [e1 x hx, e1 _ fun e => hx (by convert sub_mem e hv using 1; abel), hφ x v hv]) (fun y hy => by
      by_cases hx : y - c ∈ L
      · exact (hy (e0 y hx)).elim
      · rw [e1 y hx] at hy
        obtain ⟨c', hc', e⟩ := h0 y hy
        rcases Finset.mem_insert.1 hc' with rfl | hc'
        · exact (hx e).elim
        · exact ⟨c', hc', e⟩) fun y hy => by
      by_cases hx : y - c ∈ L
      · exact (hy (e0 y hx)).elim
      · rw [e1 y hx] at hy
        exact h1 y hy
    rw [map_sub, map_smul, sub_eq_zero] at h2
    rw [h2]
    by_cases hc : φ c = 0
    · rw [hc, zero_smul]
    · rw [h1 c hc, smul_zero]

variable {k : Type} [Field k] [TopologicalSpace k] [Module k V] [ContinuousSMul k V]

def scl (a : k) (Λ : AddSubgroup V) : AddSubgroup V where
  carrier := {v | a⁻¹ • v ∈ Λ}
  zero_mem' := by simp
  add_mem' := fun {x y} hx hy => by
    show a⁻¹ • (x + y) ∈ Λ
    rw [smul_add]; exact add_mem hx hy
  neg_mem' := fun {x} hx => by
    show a⁻¹ • (-x) ∈ Λ
    rw [smul_neg]; exact neg_mem hx

theorem mem_scl {a : k} {Λ : AddSubgroup V} {v : V} : v ∈ scl a Λ ↔ a⁻¹ • v ∈ Λ := Iff.rfl

theorem scl_open {Λ : AddSubgroup V} (ho : IsOpen (Λ : Set V)) (a : k) : IsOpen (scl a Λ : Set V) :=
  ho.preimage (f := fun v : V => a⁻¹ • v) (by fun_prop)

theorem scl_compact {Λ : AddSubgroup V} (hc : IsCompact (Λ : Set V)) {a : k} (ha : a ≠ 0) : IsCompact (scl a Λ : Set V) := by
  convert hc.image (f := fun v : V => a • v) (by fun_prop) using 1
  ext v
  refine ⟨fun h => ⟨_, h, by simp [smul_smul, ha]⟩, ?_⟩
  rintro ⟨w, hw, rfl⟩
  simpa [mem_scl, smul_smul, ha] using hw

theorem near {Λ : AddSubgroup V} (hc : IsCompact (Λ : Set V)) {Y₀ : V} {Ω : Set V} (hΩ : Ω ∈ 𝓝 Y₀) :
    ∀ᶠ z : k × V in 𝓝 (0, Y₀), z.1 ≠ 0 → ∀ v ∈ scl z.1 Λ, z.2 + v ∈ Ω := by
  have h : ∀ᶠ z : k × V in 𝓝 (0, Y₀), ∀ w ∈ (Λ : Set V), z.2 + z.1 • w ∈ Ω :=
    hc.eventually_forall_of_forall_eventually fun w _ => by
      have hh : Continuous fun p : (k × V) × V => p.1.2 + p.1.1 • p.2 := by fun_prop
      exact hh.continuousAt.eventually_mem (by simpa using hΩ)
  filter_upwards [h] with z hz h0 v hv
  simpa [smul_smul, h0] using hz _ hv

variable [NeBot (𝓝[≠] (0 : k))]

theorem small {Λ : AddSubgroup V} (ho : IsOpen (Λ : Set V)) (hc : IsCompact (Λ : Set V)) (l : (V → ℂ) →ₗ[ℂ] ℂ) {φ : V → ℂ}
    (hφ : φ ∈ SB V) (h : ∀ Y₀, φ Y₀ ≠ 0 → ∃ Ω ∈ 𝓝 Y₀, ∀ a : k, a ≠ 0 → ∀ x, (∀ v ∈ scl a Λ, x + v ∈ Ω) → l (cosI (scl a Λ) x) = 0) :
    l φ = 0 := by
  have hK : IsCompact {y | φ y ≠ 0} :=
    hφ.2.isCompact.of_isClosed_subset (hφ.1.isClopen_fiber 0).compl.1 subset_closure
  have h1 : ∀ᶠ a : k in 𝓝 0, ∀ x ∈ {y | φ y ≠ 0}, a ≠ 0 → (∀ v ∈ scl a Λ, φ (x + v) = φ x) ∧ l (cosI (scl a Λ) x) = 0 :=
    hK.eventually_forall_of_forall_eventually fun Y₀ hY => by
      obtain ⟨Ω, hΩ, hh⟩ := h Y₀ hY
      filter_upwards [near (k := k) hc hΩ, near (k := k) hc ((hφ.1.isOpen_fiber (φ Y₀)).mem_nhds rfl)] with z e1 e2 h0
      refine ⟨fun v hv => ?_, hh _ h0 _ (e1 h0)⟩
      have a1 : φ (z.2 + v) = φ Y₀ := e2 h0 v hv
      have a2 : φ (z.2 + 0) = φ Y₀ := e2 h0 0 (zero_mem _)
      rw [a1, ← a2, add_zero]
  obtain ⟨a, ha, ha0⟩ := ((h1.filter_mono (nhdsWithin_le_nhds (s := {0}ᶜ))).and self_mem_nhdsWithin).exists
  have ha0 : a ≠ 0 := ha0
  obtain ⟨s, -, hs⟩ := hK.elim_nhds_subcover (fun c => {y | y - c ∈ scl a Λ}) fun c _ =>
    ((scl_open ho a).preimage (f := fun y => y - c) (by fun_prop)).mem_nhds (by simp)
  refine decomp l (scl a Λ) s φ (fun x v hv => ?_) (fun y hy => by simpa using hs hy) fun x hx => (ha x hx ha0).2
  by_cases hx : φ x = 0
  · by_contra e
    have := (ha (x + v) (fun e' => e (e'.trans hx.symm)) ha0).1 (-v) (neg_mem hv)
    rw [add_neg_cancel_right] at this
    exact e this.symm
  · exact (ha x hx ha0).1 v hv

theorem kills_of_local (k : Type) [Field k] [TopologicalSpace k] [Module k V] [ContinuousSMul k V] [NeBot (𝓝[≠] (0 : k))] {Λ : AddSubgroup V} (ho : IsOpen (Λ : Set V)) (hc : IsCompact (Λ : Set V)) (l : (V → ℂ) →ₗ[ℂ] ℂ) {U : Set V}
    (h : ∀ Y₀ ∈ U, ∃ Ω ∈ 𝓝 Y₀, Kills l Ω) : Kills l U := fun φ hφ hU =>
  small (k := k) ho hc l hφ fun Y₀ hY => by
    obtain ⟨Ω, hΩ, hh⟩ := h Y₀ (hU _ hY)
    refine ⟨Ω, hΩ, fun a ha x hx => hh _ (cosI_mem (scl_open ho a) (scl_compact hc ha) x) fun y hy => ?_⟩
    have := hx (y - x) (by by_contra e; exact hy (cosI_of_not e))
    rwa [add_sub_cancel] at this

theorem kills_interior {Λ : AddSubgroup V} (ho : IsOpen (Λ : Set V)) (hc : IsCompact (Λ : Set V)) (l : (V → ℂ) →ₗ[ℂ] ℂ) {U Ω : Set V}
    (hU : Kills l U) (h : ∀ Y ∈ Ω, Y ∈ U ∨ ∃ (s : V →ₗ[k] V) (c : ℂ), c ≠ 1 ∧ s Y = Y ∧ (∀ v, s v ∈ Λ ↔ v ∈ Λ) ∧
      ∀ φ ∈ SB V, l (fun y => φ (s y)) = c * l φ) : Kills l (interior Ω) := fun φ hφ hs =>
  small (k := k) ho hc l hφ fun Y₀ hY => by
    refine ⟨Ω, mem_interior_iff_mem_nhds.1 (hs _ hY), fun a ha x hx => ?_⟩
    have hm := cosI_mem (scl_open ho a) (scl_compact hc ha) x
    by_cases hh : ∀ y, y - x ∈ scl a Λ → y ∈ U
    · exact hU _ hm fun y hy => hh y (by by_contra e; exact hy (cosI_of_not e))
    · push Not at hh
      obtain ⟨y, hy, hyU⟩ := hh
      obtain ⟨s, c, hc1, hsy, hΛ, hl⟩ := (h y (by simpa using hx _ hy)).resolve_left hyU
      have e : (fun z => cosI (scl a Λ) x (s z)) = cosI (scl a Λ) x := by
        funext z
        have i1 : ∀ w, w - x ∈ scl a Λ ↔ w - y ∈ scl a Λ := fun w =>
          ⟨fun e => by convert sub_mem e hy using 1; abel, fun e => by convert add_mem e hy using 1; abel⟩
        have i2 : s z - x ∈ scl a Λ ↔ z - x ∈ scl a Λ := by
          rw [i1, i1, mem_scl, mem_scl, ← hΛ (a⁻¹ • (z - y)), map_smul, map_sub, hsy]
        by_cases hz : z - x ∈ scl a Λ
        · rw [cosI_of_mem hz, cosI_of_mem (i2.2 hz)]
        · rw [cosI_of_not hz, cosI_of_not fun e => hz (i2.1 e)]
      have := hl _ hm
      rw [e] at this
      have h2 : (c - 1) * l (cosI (scl a Λ) x) = 0 := by rw [sub_mul, ← this]; ring
      exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hc1)

theorem dead {Λ₀ : AddSubgroup V} (ho : IsOpen (Λ₀ : Set V)) (hc : IsCompact (Λ₀ : Set V)) (l : (V → ℂ) →ₗ[ℂ] ℂ) {U : Set V}
    (hU : Kills l U) (Y₀ : V) (A B : V → V →ₗ[k] V) (hA : ∀ v, ContinuousAt (fun p : V × V => A p.1 p.2) (Y₀, v))
    (hB : ∀ v, ContinuousAt (fun p : V × V => B p.1 p.2) (Y₀, v)) (hA0 : ∀ v, A Y₀ (A Y₀ v) = 0) (hB0 : ∀ v, B Y₀ (B Y₀ v) = 0)
    (hAB : ∀ v, A Y₀ (B Y₀ v) = B Y₀ (A Y₀ v))
    (h : ∀ᶠ Y in 𝓝 Y₀, Y ∈ U ∨ ((∀ v, A Y (A Y v) = 0) ∧ (∀ v, B Y (B Y v) = 0) ∧ Y + B Y Y + A Y (Y + B Y Y) = Y ∧
      ∃ c : ℂ, c ≠ 1 ∧ ∀ φ ∈ SB V, l (fun y => φ (y + B Y y + A Y (y + B Y y))) = c * l φ)) : ∃ Ω ∈ 𝓝 Y₀, Kills l Ω := by
  have cA : Continuous (A Y₀) := continuous_iff_continuousAt.2 fun v =>
    ContinuousAt.comp (g := fun p : V × V => A p.1 p.2) (f := fun w => (Y₀, w)) (hA v) (by fun_prop)
  have cB : Continuous (B Y₀) := continuous_iff_continuousAt.2 fun v =>
    ContinuousAt.comp (g := fun p : V × V => B p.1 p.2) (f := fun w => (Y₀, w)) (hB v) (by fun_prop)
  let Λ : AddSubgroup V := Λ₀ ⊓ Λ₀.comap (A Y₀).toAddMonoidHom ⊓ Λ₀.comap (B Y₀).toAddMonoidHom ⊓
    Λ₀.comap ((A Y₀).comp (B Y₀)).toAddMonoidHom
  have hm : ∀ v, v ∈ Λ ↔ ((v ∈ Λ₀ ∧ A Y₀ v ∈ Λ₀) ∧ B Y₀ v ∈ Λ₀) ∧ A Y₀ (B Y₀ v) ∈ Λ₀ := fun v => Iff.rfl
  have ho' : IsOpen (Λ : Set V) :=
    ((ho.inter (ho.preimage cA)).inter (ho.preimage cB)).inter (ho.preimage (cA.comp cB))
  have hc' : IsCompact (Λ : Set V) := hc.of_isClosed_subset (Λ.isClosed_of_isOpen ho') fun v hv => ((hm v).1 hv).1.1.1
  have eA : ∀ᶠ Y in 𝓝 Y₀, ∀ v ∈ (Λ : Set V), A Y v ∈ Λ :=
    hc'.eventually_forall_of_forall_eventually fun v hv => (hA v).eventually_mem (ho'.mem_nhds (by
      obtain ⟨⟨⟨_, a2⟩, _⟩, a4⟩ := (hm v).1 hv
      refine (hm _).2 ⟨⟨⟨a2, ?_⟩, ?_⟩, ?_⟩
      · rw [hA0]; exact zero_mem _
      · rwa [← hAB]
      · rw [← hAB, hA0]; exact zero_mem _))
  have eB : ∀ᶠ Y in 𝓝 Y₀, ∀ v ∈ (Λ : Set V), B Y v ∈ Λ :=
    hc'.eventually_forall_of_forall_eventually fun v hv => (hB v).eventually_mem (ho'.mem_nhds (by
      obtain ⟨⟨⟨_, _⟩, a3⟩, a4⟩ := (hm v).1 hv
      refine (hm _).2 ⟨⟨⟨a3, a4⟩, ?_⟩, ?_⟩
      · rw [hB0]; exact zero_mem _
      · rw [hB0, map_zero]; exact zero_mem _))
  have key : ∀ C : V →ₗ[k] V, (∀ v ∈ (Λ : Set V), C v ∈ Λ) → (∀ v, C (C v) = 0) → ∀ v, v + C v ∈ Λ ↔ v ∈ Λ := fun C h1 h2 v =>
    ⟨fun e => by
      have := sub_mem e (h1 _ e)
      rwa [map_add, h2, add_zero, add_sub_cancel_right] at this, fun e => add_mem e (h1 v e)⟩
  refine ⟨_, interior_mem_nhds.2 ((h.and eA).and eB), kills_interior (k := k) ho' hc' l hU fun Y hY => ?_⟩
  obtain ⟨⟨hY | ⟨a1, a2, a3, c, a4, a5⟩, b1⟩, b2⟩ := hY
  · exact Or.inl hY
  · exact Or.inr ⟨(LinearMap.id + A Y).comp (LinearMap.id + B Y), c, a4, a3, fun v => (key _ b1 a1 _).trans (key _ b2 a2 v), a5⟩

end PositivityTheory.ThKEnd.Cusp

end
