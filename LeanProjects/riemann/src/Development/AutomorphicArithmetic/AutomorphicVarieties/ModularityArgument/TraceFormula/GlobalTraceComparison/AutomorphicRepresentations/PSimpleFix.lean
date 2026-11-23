import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.SlotBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.FinprodSplitAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.UnitHecke
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevOpMemFixed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupportOutFinite

open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.SimpleFixedVectors

open GlobalTheory.PRep GlobalTheory.BCT GlobalTheory.TwTrLevel

section

variable {G : Type} [Group G]

private def Mg (N : Subgroup G) (g : G) : Subgroup G := N ⊓ N.comap (MulAut.conj g⁻¹).toMonoidHom

private theorem mem_Mg (N : Subgroup G) (g m : G) : m ∈ Mg N g ↔ m ∈ N ∧ g⁻¹ * m * g ∈ N := by
  simp [Mg, Subgroup.mem_comap, MulAut.conj_apply]

private def dc (N : Subgroup G) (g : G) : Set G := {y | ∃ a ∈ N, ∃ b ∈ N, y = a * g * b}

private theorem dc_left (N : Subgroup G) (g : G) {k : G} (hk : k ∈ N) (x : G) : k * x ∈ dc N g ↔ x ∈ dc N g := by
  constructor
  · rintro ⟨a, ha, b, hb, e⟩
    refine ⟨k⁻¹ * a, N.mul_mem (N.inv_mem hk) ha, b, hb, ?_⟩
    simp only [mul_assoc] at e ⊢
    rw [eq_inv_mul_iff_mul_eq]
    exact e
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨k * a, N.mul_mem hk ha, b, hb, by simp only [mul_assoc]⟩

private theorem dc_right (N : Subgroup G) (g : G) {k : G} (hk : k ∈ N) (x : G) : x * k ∈ dc N g ↔ x ∈ dc N g := by
  constructor
  · rintro ⟨a, ha, b, hb, e⟩
    refine ⟨a, ha, b * k⁻¹, N.mul_mem hb (N.inv_mem hk), ?_⟩
    rw [← mul_assoc, ← e]
    simp
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha, b * k, N.mul_mem hb hk, by simp only [mul_assoc]⟩

variable [TopologicalSpace G] [IsTopologicalGroup G]

private theorem isOpen_Mg (N : Subgroup G) (hNo : IsOpen (N : Set G)) (g : G) : IsOpen (Mg N g : Set G) := by
  have e : (Mg N g : Set G) = (N : Set G) ∩ (fun m => g⁻¹ * m * g) ⁻¹' (N : Set G) := by
    ext m
    simp [mem_Mg]
  rw [e]
  exact hNo.inter (hNo.preimage (by fun_prop))

private theorem hecke_dc (N : Subgroup G) (hNc : IsCompact (N : Set G)) (g : G) :
    IsHecke N ((dc N g).indicator 1) := by
  refine ⟨?_, ?_⟩
  · have hc : IsCompact (dc N g) := by
      have e : dc N g = (fun p : G × G => p.1 * g * p.2) '' ((N : Set G) ×ˢ (N : Set G)) := by
        ext y
        constructor
        · rintro ⟨a, ha, b, hb, rfl⟩
          exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩
        · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
          exact ⟨a, ha, b, hb, rfl⟩
      rw [e]
      exact (hNc.prod hNc).image (by fun_prop)
    exact hc.closure_of_subset Set.support_indicator_subset
  · intro k hk x
    constructor
    · by_cases h : x ∈ dc N g
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((dc_left N g hk x).2 h)]
        rfl
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem fun h' => h ((dc_left N g hk x).1 h')]
    · by_cases h : x ∈ dc N g
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((dc_right N g hk x).2 h)]
        rfl
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem fun h' => h ((dc_right N g hk x).1 h')]

variable {V : Type} [AddCommGroup V] [Module ℂ V]

private theorem fixed_Mg (ρ : Representation ℂ G V) (N : Subgroup G) (g : G) (x : V) (hx : x ∈ fixed ρ N) :
    ρ g x ∈ fixed ρ (Mg N g) := by
  rw [mem_fixed_iff] at hx ⊢
  intro m hm
  have h := hx _ ((mem_Mg N g m).1 hm).2
  have e : m * g = g * (g⁻¹ * m * g) := by group
  rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply, h]

private theorem lv_dc (ρ : Representation ℂ G V) (N : Subgroup G) (hNo : IsOpen (N : Set G))
    (hNc : IsCompact (N : Set G)) (g : G) (x : V) (hx : x ∈ fixed ρ N) :
    levOp ρ N N ((dc N g).indicator 1) LinearMap.id x =
      ∑ᶠ j : N ⧸ (Mg N g).subgroupOf N, ρ (j.out : G) (ρ g x) := by
  have hH := hecke_dc N hNc g
  have hs := finite_supp N hNo _ hH.1
  have hx' := (mem_fixed_iff ρ N x).1 hx
  rw [levOp_apply ρ N N _ _ x hs, Subgroup.relIndex_self]
  simp only [Nat.cast_one, inv_one, one_smul, LinearMap.id_apply]
  set f : G → ℂ := (dc N g).indicator 1 with hf
  set F : G → V := fun y => f y • ρ y x with hF
  have hFr : ∀ y, ∀ h ∈ N, F (y * h) = F y := by
    intro y h hh
    simp only [hF, (hH.2 h hh y).2, map_mul, Module.End.mul_apply, hx' h hh]
  let Φ : N ⧸ (Mg N g).subgroupOf N → G ⧸ N := fun j => QuotientGroup.mk ((j.out : G) * g)
  have hinj : Function.Injective Φ := by
    intro a b hab
    have h1 : ((a.out : G) * g)⁻¹ * ((b.out : G) * g) ∈ N := QuotientGroup.eq.1 hab
    rw [← QuotientGroup.out_eq' a, ← QuotientGroup.out_eq' b]
    refine QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 ((mem_Mg N g _).2 ⟨?_, ?_⟩))
    · exact N.mul_mem (N.inv_mem (a.out).2) (b.out).2
    · have e : g⁻¹ * (((a.out⁻¹ * b.out : N)) : G) * g = ((a.out : G) * g)⁻¹ * ((b.out : G) * g) := by
        simp [mul_assoc]
      rw [e]
      exact h1
  have hsup : Function.support (fun q : G ⧸ N => F q.out) ⊆ Set.range Φ := by
    intro q hq
    have hne : f q.out ≠ 0 := by
      intro h0
      exact hq (by simp [hF, h0])
    have hmem : q.out ∈ dc N g := by
      by_contra hn
      exact hne (Set.indicator_of_notMem hn _)
    obtain ⟨a, ha, b, hb, e⟩ := hmem
    obtain ⟨m, hm⟩ := QuotientGroup.mk_out_eq_mul ((Mg N g).subgroupOf N) (⟨a, ha⟩ : N)
    refine ⟨QuotientGroup.mk ⟨a, ha⟩, ?_⟩
    have hm' := (mem_Mg N g _).1 (Subgroup.mem_subgroupOf.1 m.2)
    show QuotientGroup.mk (((QuotientGroup.mk (⟨a, ha⟩ : N) : N ⧸ (Mg N g).subgroupOf N).out : G) * g) = q
    rw [hm, ← QuotientGroup.out_eq' q, e]
    refine QuotientGroup.eq.2 ?_
    have e2 : ((((⟨a, ha⟩ : N) * (m : N) : N) : G) * g)⁻¹ * (a * g * b) =
        (g⁻¹ * ((m : N) : G) * g)⁻¹ * b := by
      simp [mul_assoc]
    rw [e2]
    exact N.mul_mem (N.inv_mem hm'.2) hb
  change ∑ᶠ q : G ⧸ N, F q.out = _
  have hR : ∑ᶠ q ∈ Set.range Φ, F (Quotient.out q) = ∑ᶠ q : G ⧸ N, F (Quotient.out q) := by
    rw [← finsum_mem_inter_support (fun q : G ⧸ N => F (Quotient.out q)) (Set.range Φ), Set.inter_eq_right.2 hsup,
      finsum_mem_support]
  rw [← hR, finsum_mem_range hinj]
  refine finsum_congr fun j => ?_
  have h1 : F (Φ j).out = F ((j.out : G) * g) := out_eq_of_inv N F (fun y h hh => hFr y h hh) _
  rw [h1]
  have hmem : (j.out : G) * g ∈ dc N g := ⟨j.out, (j.out).2, 1, N.one_mem, by simp⟩
  simp [hF, hf, Set.indicator_of_mem hmem, map_mul, Module.End.mul_apply]

private theorem avg_dc (ρ : Representation ℂ G V) (N : Subgroup G) (hNo : IsOpen (N : Set G))
    (hNc : IsCompact (N : Set G)) (g : G) (x : V) (hx : x ∈ fixed ρ N) [Finite (N ⧸ (Mg N g).subgroupOf N)] :
    avgOp ρ N (Mg N g) (ρ g x) =
      (((Mg N g).relIndex N : ℕ) : ℂ)⁻¹ • levOp ρ N N ((dc N g).indicator 1) LinearMap.id x := by
  rw [avgOp_apply, lv_dc ρ N hNo hNc g x hx]

private theorem avg_level (ρ : Representation ℂ G V) (N M M' : Subgroup G) (hNo : IsOpen (N : Set G))
    (hNc : IsCompact (N : Set G)) (hMo : IsOpen (M : Set G)) (hM'o : IsOpen (M' : Set G)) (hMN : M ≤ N)
    (hle : M' ≤ M) (v : V) (hv : v ∈ fixed ρ M) : avgOp ρ N M' v = avgOp ρ N M v := by
  haveI h1 := finite_quot N N M' hNc hNo hM'o le_rfl
  haveI h2 := finite_quot N N M hNc hNo hMo le_rfl
  haveI h3 := finite_quot N M M' hNc hMo hM'o hMN
  haveI h4 := finite_quot N N (Mg N 1) hNc hNo (isOpen_Mg N hNo 1) le_rfl
  have hH := hecke_dc N hNc 1
  have hHM : IsHecke M ((dc N 1).indicator 1) := ⟨hH.1, fun k hk y => hH.2 k (hMN hk) y⟩
  have hvM' : v ∈ fixed ρ M' := by
    rw [mem_fixed_iff] at hv ⊢
    exact fun h hh => hv h (hle hh)
  have e1 := levOp_le ρ N N M' (hle.trans hMN) le_rfl hNo hM'o _ hH v hvM'
  have e2 := levOp_le ρ N M M' hle hMN hMo hM'o _ hHM v hvM'
  rw [avgOp_fix ρ M M' v hv] at e2
  have e3 := levOp_le ρ N N M hMN le_rfl hNo hMo _ hH v hv
  have back : ∀ y ∈ fixed ρ N, y = (((Mg N 1).relIndex N : ℕ) : ℂ)⁻¹ •
      levOp ρ N N ((dc N 1).indicator 1) LinearMap.id y := by
    intro y hy
    rw [← avg_dc ρ N hNo hNc 1 y hy, map_one, Module.End.one_apply, avgOp_fix ρ N _ y hy]
  rw [back _ (avgOp_mem ρ N M' v hvM'), back _ (avgOp_mem ρ N M v hv), ← e1, e2, e3]

private theorem core (ρ : Representation ℂ G V) (N : Subgroup G) (hNo : IsOpen (N : Set G))
    (hNc : IsCompact (N : Set G))
    (hirr : ∀ W : Submodule ℂ V, (∀ g x, x ∈ W → ρ g x ∈ W) → W = ⊥ ∨ W = ⊤)
    (W : Submodule ℂ V) (hW : W ≤ fixed ρ N)
    (hst : ∀ f, IsHecke N f → ∀ x ∈ W, levOp ρ N N f LinearMap.id x ∈ W) : W = ⊥ ∨ W = fixed ρ N := by
  by_cases hb : W = ⊥
  · exact Or.inl hb
  refine Or.inr (le_antisymm hW ?_)
  obtain ⟨x, hxW, hx0⟩ := (Submodule.ne_bot_iff W).1 hb
  have hxN := hW hxW
  let O : Submodule ℂ V := Submodule.span ℂ (Set.range fun g : G => ρ g x)
  have hxO : x ∈ O := Submodule.subset_span ⟨1, by simp⟩
  have hO : O = ⊤ := by
    have hinv : ∀ g y, y ∈ O → ρ g y ∈ O := by
      intro g y hy
      refine Submodule.span_induction (p := fun y _ => ρ g y ∈ O) ?_ ?_ ?_ ?_ hy
      · rintro _ ⟨a, rfl⟩
        refine Submodule.subset_span ⟨g * a, ?_⟩
        simp [map_mul, Module.End.mul_apply]
      · simp
      · intro a b _ _ ha hb
        rw [map_add]
        exact O.add_mem ha hb
      · intro c a _ ha
        rw [map_smul]
        exact O.smul_mem c ha
    rcases hirr O hinv with h | h
    · exact absurd (by simpa [h] using hxO) hx0
    · exact h
  have hp : ∀ v ∈ O, ∃ M : Subgroup G, IsOpen (M : Set G) ∧ M ≤ N ∧ v ∈ fixed ρ M ∧ avgOp ρ N M v ∈ W := by
    intro v hv
    refine Submodule.span_induction (p := fun v _ => ∃ M : Subgroup G, IsOpen (M : Set G) ∧ M ≤ N ∧
      v ∈ fixed ρ M ∧ avgOp ρ N M v ∈ W) ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨g, rfl⟩
      haveI := finite_quot N N (Mg N g) hNc hNo (isOpen_Mg N hNo g) le_rfl
      refine ⟨Mg N g, isOpen_Mg N hNo g, inf_le_left, fixed_Mg ρ N g x hxN, ?_⟩
      show avgOp ρ N (Mg N g) (ρ g x) ∈ W
      rw [avg_dc ρ N hNo hNc g x hxN]
      exact W.smul_mem _ (hst _ (hecke_dc N hNc g) x hxW)
    · exact ⟨N, hNo, le_rfl, (fixed ρ N).zero_mem, by simp⟩
    · rintro a b _ _ ⟨M₁, ho₁, hl₁, hf₁, hw₁⟩ ⟨M₂, ho₂, hl₂, hf₂, hw₂⟩
      have ho : IsOpen ((M₁ ⊓ M₂ : Subgroup G) : Set G) := ho₁.inter ho₂
      have hm : ∀ (M : Subgroup G) (y : V), M₁ ⊓ M₂ ≤ M → y ∈ fixed ρ M → y ∈ fixed ρ (M₁ ⊓ M₂) := by
        intro M y hle hy
        rw [mem_fixed_iff] at hy ⊢
        exact fun h hh => hy h (hle hh)
      refine ⟨M₁ ⊓ M₂, ho, inf_le_left.trans hl₁,
        (fixed ρ _).add_mem (hm _ _ inf_le_left hf₁) (hm _ _ inf_le_right hf₂), ?_⟩
      rw [map_add, avg_level ρ N M₁ _ hNo hNc ho₁ ho hl₁ inf_le_left a hf₁,
        avg_level ρ N M₂ _ hNo hNc ho₂ ho hl₂ inf_le_right b hf₂]
      exact W.add_mem hw₁ hw₂
    · rintro c a _ ⟨M, ho, hl, hf, hw⟩
      refine ⟨M, ho, hl, (fixed ρ M).smul_mem c hf, ?_⟩
      rw [map_smul]
      exact W.smul_mem c hw
  intro z hz
  obtain ⟨M, ho, hl, -, hw⟩ := hp z (hO ▸ Submodule.mem_top)
  haveI := finite_quot N N M hNc hNo ho le_rfl
  rwa [avgOp_fix ρ N M z hz] at hw

end

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.SimpleFixedVectors

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.simpleFix_pf :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.CvOp → SimpleFix := by
  intro _ E _ _ _ n w τ N hNo hNle
  have hKc := (UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.unitHecke E n 0 0 w).2.2.2.1
  have hNc : IsCompact (N : Set (GlobalTheory.BCT.GLw n w)) :=
    hKc.of_isClosed_subset (Subgroup.isClosed_of_isOpen N hNo) hNle
  obtain ⟨-, hirr⟩ := (GlobalTheory.CuspRep.isIrreducible_iff τ.ρ).1 τ.irred
  refine ⟨fun f hf x hx => GlobalTheory.TraceLevel.levOp_mem_fixed τ.ρ N N N f hf hNo le_rfl x hx, ?_⟩
  exact fun W hW hst => UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.SimpleFixedVectors.core τ.ρ N hNo hNc hirr W hW hst
