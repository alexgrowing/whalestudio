import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHilbertSchmidtOfFiniteDimensional
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.OpTrace

namespace GlobalTheory.CharIndep

theorem exists_smul_eq_self_and_smul_eq_zero {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [IsSimpleModule R M] [IsSimpleModule R N]
    (h1 : ∀ f : M →ₗ[R] N, f = 0) (h2 : ∀ f : N →ₗ[R] M, f = 0) (s : Finset M) (t : Finset N) :
    ∃ r : R, (∀ m ∈ s, r • m = m) ∧ ∀ n ∈ t, r • n = 0 := by
  classical
  let p : Module.End (Module.End R (M × N)) (M × N) :=
    { toFun := fun x => (x.1, 0)
      map_add' := fun x y => by simp
      map_smul' := fun φ x => by
        have a1 : (φ (x.1, 0)).2 = 0 :=
          congr($(h1 (LinearMap.snd R M N ∘ₗ φ ∘ₗ LinearMap.inl R M N)) x.1)
        have a2 : (φ (0, x.2)).1 = 0 :=
          congr($(h2 (LinearMap.fst R M N ∘ₗ φ ∘ₗ LinearMap.inr R M N)) x.2)
        have a3 : φ x = φ (x.1, 0) + φ (0, x.2) := by rw [← map_add]; simp
        simp only [Module.End.smul_def, RingHom.id_apply]
        ext
        · simp [a3, a2]
        · simp [a1] }
  have : IsSemisimpleModule R (M × N) := by
    have hs := IsSemisimpleModule.sup (IsSemisimpleModule.range (LinearMap.inl R M N))
      (IsSemisimpleModule.range (LinearMap.inr R M N))
    rw [LinearMap.sup_range_inl_inr] at hs
    exact IsSemisimpleModule.congr Submodule.topEquiv.symm
  obtain ⟨r, hr⟩ := jacobson_density p
    (s.image (fun m => (m, (0 : N))) ∪ t.image (fun n => ((0 : M), n)))
  refine ⟨r, fun m hm => ?_, fun n hn => ?_⟩
  · have := hr (m, 0) (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hm))
    exact (congrArg Prod.fst this).symm
  · have := hr (0, n) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hn))
    exact (congrArg Prod.snd this).symm

theorem exists_smoothOp_eq_comp {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    [μ.IsMulLeftInvariant] {f₀ : G → ℂ} (hf : IsLocallyConstant f₀) (hc : HasCompactSupport f₀)
    (a : MonoidAlgebra ℂ G) :
    ∃ f : G → ℂ, IsLocallyConstant f ∧ HasCompactSupport f ∧
      ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V), IsSmooth ρ →
        smoothOp ρ μ f = ρ.asAlgebraHom a ∘ₗ smoothOp ρ μ f₀ := by
  induction a using MonoidAlgebra.induction_on with
  | of g =>
    have h1 : IsLocallyConstant fun x => f₀ (g⁻¹ * x) :=
      hf.comp_continuous (continuous_const.mul continuous_id)
    have h2 : HasCompactSupport fun x => f₀ (g⁻¹ * x) :=
      hc.comp_homeomorph (Homeomorph.mulLeft g⁻¹)
    refine ⟨_, h1, h2, fun V _ _ ρ hρ => ?_⟩
    ext v
    refine eq_of_forall_dual fun l => ?_
    rw [hρ.map_smoothOp h1 h2 l, ← integral_mul_left_eq_self _ g]
    simpa using (hρ.map_smoothOp (μ := μ) hf hc (l ∘ₗ ρ g) v).symm
  | add a b ha hb =>
    obtain ⟨f, f1, f2, f3⟩ := ha
    obtain ⟨f', f1', f2', f3'⟩ := hb
    refine ⟨f + f', f1.add f1', f2.add f2', fun V _ _ ρ hρ => ?_⟩
    rw [hρ.smoothOp_add f1 f2 f1' f2', f3 V ρ hρ, f3' V ρ hρ, map_add, LinearMap.add_comp]
  | smul c a ha =>
    obtain ⟨f, f1, f2, f3⟩ := ha
    refine ⟨c • f, f1.comp (c • ·), f2.comp_left (g := (c • ·)) (smul_zero c),
      fun V _ _ ρ hρ => ?_⟩
    rw [hρ.smoothOp_smul f1 f2, f3 V ρ hρ, map_smul, LinearMap.smul_comp]

theorem exists_asAlgebraHom_eq {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (π : Representation ℂ G V) (π' : Representation ℂ G W)
    [π.IsIrreducible] [π'.IsIrreducible] [IsEmpty (π.Equiv π')] (S : Submodule ℂ V)
    (T : Submodule ℂ W) [FiniteDimensional ℂ S] [FiniteDimensional ℂ T] :
    ∃ a : MonoidAlgebra ℂ G, (∀ v ∈ S, π.asAlgebraHom a v = v) ∧
      ∀ w ∈ T, π'.asAlgebraHom a w = 0 := by
  have : IsEmpty (π'.Equiv π) := ⟨fun e => IsEmpty.false (α := π.Equiv π') e.symm⟩
  have s1 := (Representation.IntertwiningMap.equivLinearMapAsModule π π').toEquiv.symm.subsingleton
  have s2 := (Representation.IntertwiningMap.equivLinearMapAsModule π' π).toEquiv.symm.subsingleton
  obtain ⟨s, hs⟩ := (Submodule.fg_iff_finiteDimensional S).2 inferInstance
  obtain ⟨t, ht⟩ := (Submodule.fg_iff_finiteDimensional T).2 inferInstance
  obtain ⟨a, h1, h2⟩ := exists_smul_eq_self_and_smul_eq_zero (R := MonoidAlgebra ℂ G)
    (M := π.asModule) (N := π'.asModule) (fun f => Subsingleton.elim _ _)
    (fun f => Subsingleton.elim _ _) s t
  refine ⟨a, fun v hv => ?_, fun w hw => ?_⟩
  · rw [← hs] at hv
    exact LinearMap.eqOn_span (f := π.asAlgebraHom a) (g := LinearMap.id) (fun x hx => h1 x hx) hv
  · rw [← ht] at hw
    exact LinearMap.eqOn_span (f := π'.asAlgebraHom a) (g := 0) (fun x hx => h2 x hx) hw

theorem nonempty_equiv_of_smoothTrace_eq : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], (∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (π : Representation ℂ G V) (π' : Representation ℂ G W), IsAdmissible π → IsAdmissible π' → π.IsIrreducible → π'.IsIrreducible → (∀ f : G → ℂ, IsLocallyConstant f → HasCompactSupport f → smoothTrace π μ f = smoothTrace π' μ f) → Nonempty (π.Equiv π') := by
  intro G _ _ _ _ _ _ μ _ _ hG V _ _ W _ _ π π' hπ hπ' hi hi' htr
  by_contra hne
  have : IsEmpty (π.Equiv π') := not_nonempty_iff.1 hne
  have : Nontrivial V := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) π.asModule
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨K, ho, hK, hKv⟩ := hG _ ((hπ.1 v).mem_nhds (by simp))
  have hvK : v ∈ fixed π K := mem_fixed.2 fun k hk => hKv hk
  have := hπ.2 K ho hK
  have := hπ'.2 K ho hK
  have hf : IsLocallyConstant ((K : Set G).indicator fun _ => (1 : ℂ)) := by
    rw [IsLocallyConstant.iff_exists_open]
    intro g
    by_cases hg : g ∈ (K : Set G)
    · exact ⟨K, ho, hg, fun x hx => by simp only [Set.indicator_of_mem, hx, hg]⟩
    · exact ⟨(K : Set G)ᶜ, (K.isClosed_of_isOpen ho).isOpen_compl, hg, fun x hx => by
        rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hg]⟩
  have hc : HasCompactSupport ((K : Set G).indicator fun _ => (1 : ℂ)) :=
    HasCompactSupport.intro hK fun x hx => Set.indicator_of_notMem hx _
  have hl : ∀ k ∈ K, ∀ g, (K : Set G).indicator (fun _ => (1 : ℂ)) (k * g) =
      (K : Set G).indicator (fun _ => (1 : ℂ)) g := fun k hk g => by
    by_cases hg : g ∈ (K : Set G)
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (K.mul_mem hk hg)]
    · rw [Set.indicator_of_notMem hg,
        Set.indicator_of_notMem fun h => hg ((K.mul_mem_cancel_left hk).1 h)]
  obtain ⟨a, ha, ha'⟩ := exists_asAlgebraHom_eq π π' (fixed π K) (fixed π' K)
  obtain ⟨f, f1, f2, f3⟩ := exists_smoothOp_eq_comp μ hf hc a
  have e1 : smoothOp π μ f = smoothOp π μ ((K : Set G).indicator fun _ => (1 : ℂ)) := by
    rw [f3 V π hπ.1]
    ext x
    exact ha _ (hπ.1.smoothOp_mem_fixed hf hc hl x)
  have e2 : smoothOp π' μ f = 0 := by
    rw [f3 W π' hπ'.1]
    ext x
    exact ha' _ (hπ'.1.smoothOp_mem_fixed hf hc hl x)
  have e3 := htr f f1 f2
  have e4 := hπ.smoothTrace_indicator (μ := μ) ho hK
  have e5 : smoothTrace π' μ f = 0 := by
    rw [smoothTrace, e2, finRankTrace_eq _ ⊥ (by simp)]
    rw [Subsingleton.elim (LinearMap.restrict _ _) 0, map_zero]
  rw [e5, smoothTrace, e1, ← smoothTrace, e4] at e3
  have : Nontrivial (fixed π K) := ⟨⟨⟨v, hvK⟩, 0, fun h => hv (congrArg Subtype.val h)⟩⟩
  have p1 : 0 < Module.finrank ℂ (fixed π K) := Module.finrank_pos
  have p2 : μ.real K ≠ 0 :=
    ENNReal.toReal_ne_zero.2 ⟨ho.measure_ne_zero μ ⟨1, K.one_mem⟩, hK.measure_ne_top⟩
  exact mul_ne_zero (by exact_mod_cast p2) (by exact_mod_cast p1.ne') e3

end GlobalTheory.CharIndep
