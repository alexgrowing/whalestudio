import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective

open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct Topology

namespace GlobalTheory.CompanionTheory.ProdSub

section Abstract

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

theorem mem_fixed_iff_forall {π : Representation ℂ G V} {K : Subgroup G} {x : V} :
    x ∈ fixed π K ↔ ∀ k ∈ K, π k x = x := by
  show (∀ h : K, π h x = ((1 : K →* ℂˣ) h : ℂ) • x) ↔ _
  simp only [MonoidHom.one_apply, Units.val_one, one_smul]
  exact ⟨fun h k hk => h ⟨k, hk⟩, fun h k => h k k.2⟩

theorem fixed_sup_eq_zero [TopologicalSpace G] [IsTopologicalGroup G] {π : Representation ℂ G V}
    (hπ : IsSmooth π) {K : Subgroup G} (hK : IsCompact (K : Set G)) {A B : Submodule ℂ V}
    (hA : ∀ g, ∀ ⦃x⦄, x ∈ A → π g x ∈ A) (hB : ∀ g, ∀ ⦃x⦄, x ∈ B → π g x ∈ B)
    (hA0 : ∀ x ∈ A, x ∈ fixed π K → x = 0) (hB0 : ∀ x ∈ B, x ∈ fixed π K → x = 0)
    {x : V} (hx : x ∈ A ⊔ B) (hf : x ∈ fixed π K) : x = 0 := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
  let S : Subrepresentation π := ⟨B, hB⟩
  have hS : IsSmooth S.toRepresentation := by
    intro w
    have e : {g | S.toRepresentation g w = w} = {g | π g w = w} := by
      ext g
      exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    rw [e]
    exact hπ w
  have hinv : ∀ h ∈ K, ((A.mkQ).comp B.subtype) (S.toRepresentation h ⟨b, hb⟩) =
      ((A.mkQ).comp B.subtype) ⟨b, hb⟩ := by
    intro h hh
    have hx' := (mem_fixed_iff_forall.mp hf) h hh
    rw [map_add] at hx'
    have e : (S.toRepresentation h ⟨b, hb⟩ : V) = π h b := rfl
    have e2 : π h b - b = a - π h a := by
      rw [sub_eq_sub_iff_add_eq_add, add_comm, hx']
    show A.mkQ ((S.toRepresentation h ⟨b, hb⟩ : V)) = A.mkQ b
    rw [e, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, e2]
    exact A.sub_mem ha (hA h ha)
  obtain ⟨v, hvK, hv⟩ := GlobalTheory.SmGL.IwahoriOnto.exists_fixed_map_eq hS hK ((A.mkQ).comp B.subtype) ⟨b, hb⟩ hinv
  have hvK' : (v : V) ∈ fixed π K := by
    rw [mem_fixed_iff_forall] at hvK ⊢
    intro k hk
    exact congrArg Subtype.val (hvK k hk)
  have hv0 : (v : V) = 0 := hB0 v v.2 hvK'
  have hbA : b ∈ A := by
    have h1 : A.mkQ (v : V) = A.mkQ b := hv
    rw [hv0, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, zero_sub] at h1
    simpa using A.neg_mem h1
  exact hA0 _ (A.add_mem ha hbA) hf

theorem exists_irreducible_of_fixed {π : Representation ℂ G V} {K : Subgroup G} {W : Submodule ℂ V}
    (hW : ∀ g, ∀ ⦃x⦄, x ∈ W → π g x ∈ W) (hW0 : W ≠ ⊥)
    (hfin : FiniteDimensional ℂ ↥(W ⊓ fixed π K))
    (hnz : ∀ A : Submodule ℂ V, (∀ g, ∀ ⦃x⦄, x ∈ A → π g x ∈ A) → A ≠ ⊥ →
      ∃ x ∈ A, x ∈ fixed π K ∧ x ≠ 0) :
    ∃ (S : Subrepresentation π) (u : V), u ∈ S.toSubmodule ∧ u ≠ 0 ∧ u ∈ fixed π K ∧
      S.toRepresentation.IsIrreducible ∧ FiniteDimensional ℂ (fixed S.toRepresentation K) := by
  classical
  haveI := hfin
  have hfinM : ∀ M : Submodule ℂ V, M ≤ W → FiniteDimensional ℂ ↥(M ⊓ fixed π K) :=
    fun M hM => Submodule.finiteDimensional_of_le (inf_le_inf_right (fixed π K) hM)
  have hex : ∃ n, ∃ M : Submodule ℂ V, (∀ g, ∀ ⦃x⦄, x ∈ M → π g x ∈ M) ∧ M ≤ W ∧ M ≠ ⊥ ∧
      Module.finrank ℂ ↥(M ⊓ fixed π K) = n := ⟨_, W, hW, le_rfl, hW0, rfl⟩
  obtain ⟨M0, hM0inv, hM0W, hM0ne, hM0d⟩ := Nat.find_spec hex
  have hmin : ∀ M : Submodule ℂ V, (∀ g, ∀ ⦃x⦄, x ∈ M → π g x ∈ M) → M ≤ W → M ≠ ⊥ →
      Module.finrank ℂ ↥(M0 ⊓ fixed π K) ≤ Module.finrank ℂ ↥(M ⊓ fixed π K) := by
    intro M hMinv hMW hMne
    rw [hM0d]
    exact Nat.find_min' hex ⟨M, hMinv, hMW, hMne, rfl⟩
  haveI := hfinM M0 hM0W
  let S1 : Submodule ℂ V := Submodule.span ℂ {x | ∃ g, ∃ y ∈ M0 ⊓ fixed π K, x = π g y}
  have hS1inv : ∀ g, ∀ ⦃x⦄, x ∈ S1 → π g x ∈ S1 := by
    intro g x hx
    have hle : S1 ≤ S1.comap (π g) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨g', y, hy, rfl⟩
      show π g (π g' y) ∈ S1
      rw [← Module.End.mul_apply, ← map_mul]
      exact Submodule.subset_span ⟨g * g', y, hy, rfl⟩
    exact hle hx
  have hS1M0 : S1 ≤ M0 := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨g, y, hy, rfl⟩
    exact hM0inv g hy.1
  have hF0S1 : M0 ⊓ fixed π K ≤ S1 := fun y hy =>
    Submodule.subset_span ⟨1, y, hy, by rw [map_one, Module.End.one_apply]⟩
  have hkey : ∀ T : Submodule ℂ V, (∀ g, ∀ ⦃x⦄, x ∈ T → π g x ∈ T) → T ≤ S1 → T ≠ ⊥ → S1 ≤ T := by
    intro T hTinv hTS1 hTne
    have hTM0 : T ≤ M0 := hTS1.trans hS1M0
    have hle : T ⊓ fixed π K ≤ M0 ⊓ fixed π K := inf_le_inf_right (fixed π K) hTM0
    have heq : T ⊓ fixed π K = M0 ⊓ fixed π K :=
      Submodule.eq_of_le_of_finrank_le hle (hmin T hTinv (hTM0.trans hM0W) hTne)
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨g, y, hy, rfl⟩
    have hy' : y ∈ T ⊓ fixed π K := by rw [heq]; exact hy
    exact hTinv g hy'.1
  obtain ⟨u, huM0, huF, hu0⟩ := hnz M0 hM0inv hM0ne
  have huS1 : u ∈ S1 := hF0S1 ⟨huM0, huF⟩
  let S : Subrepresentation π := ⟨S1, hS1inv⟩
  refine ⟨S, u, huS1, hu0, huF, ?_, ?_⟩
  · show IsSimpleOrder (Subrepresentation S.toRepresentation)
    refine { exists_pair_ne := ⟨⊥, ⊤, ?_⟩, eq_bot_or_eq_top := ?_ }
    · intro h
      have hmem : (⟨u, huS1⟩ : ↥S1) ∈ (⊤ : Subrepresentation S.toRepresentation).toSubmodule :=
        Submodule.mem_top
      rw [← h] at hmem
      have h0 : (⟨u, huS1⟩ : ↥S1) = 0 := (Submodule.mem_bot ℂ).mp hmem
      exact hu0 (congrArg Subtype.val h0)
    · intro X
      by_cases hX : X.toSubmodule = ⊥
      · left
        exact Subrepresentation.ext hX
      · right
        apply Subrepresentation.ext
        show X.toSubmodule = ⊤
        let T : Submodule ℂ V := X.toSubmodule.map S1.subtype
        have hTinv : ∀ g, ∀ ⦃x⦄, x ∈ T → π g x ∈ T := by
          rintro g _ ⟨y, hy, rfl⟩
          exact ⟨S.toRepresentation g y, X.apply_mem_toSubmodule g hy, rfl⟩
        have hTS1 : T ≤ S1 := Submodule.map_subtype_le S1 _
        have hTne : T ≠ ⊥ := by
          intro hT
          apply hX
          rw [eq_bot_iff]
          intro y hy
          have hyT : (y : V) ∈ T := ⟨y, hy, rfl⟩
          rw [hT] at hyT
          exact (Submodule.mem_bot ℂ).mpr (Subtype.ext ((Submodule.mem_bot ℂ).mp hyT))
        have hST := hkey T hTinv hTS1 hTne
        rw [eq_top_iff]
        intro y _
        obtain ⟨y', hy', hyy'⟩ := hST y.2
        have hyy : y' = y := Subtype.ext hyy'
        rw [← hyy]
        exact hy'
  · have hle : (fixed S.toRepresentation K).map S1.subtype ≤ W ⊓ fixed π K := by
      rintro _ ⟨y, hy0, rfl⟩
      have hy : y ∈ fixed S.toRepresentation K := hy0
      refine ⟨hM0W (hS1M0 y.2), ?_⟩
      show (y : V) ∈ fixed π K
      rw [mem_fixed_iff_forall] at hy ⊢
      intro k hk
      exact congrArg Subtype.val (hy k hk)
    haveI : FiniteDimensional ℂ ↥((fixed S.toRepresentation K).map S1.subtype) :=
      Submodule.finiteDimensional_of_le hle
    exact LinearEquiv.finiteDimensional
      (Submodule.equivMapOfInjective S1.subtype Subtype.val_injective _).symm

end Abstract

theorem inl_inr_comm {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (G × H) V) (g : G) (h : H) (x : V) :
    ρ (g, 1) (ρ (1, h) x) = ρ (1, h) (ρ (g, 1) x) := by
  have hc : ((g, 1) * (1, h) : G × H) = (1, h) * (g, 1) := Prod.ext (by simp) (by simp)
  rw [← Module.End.mul_apply, ← map_mul, hc, map_mul, Module.End.mul_apply]

section Product

variable {G H V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [AddCommGroup V] [Module ℂ V]

theorem exists_fixed_of_ne_bot (ρ : Representation ℂ (G × H) V) (hi : ρ.IsIrreducible)
    (hs : IsSmooth (ρ.comp (MonoidHom.inl G H))) {K : Subgroup G} (hK : IsCompact (K : Set G))
    {v : V} (hv : v ≠ 0) (hvK : v ∈ fixed (ρ.comp (MonoidHom.inl G H)) K)
    (A : Submodule ℂ V) (hA : ∀ g, ∀ ⦃x⦄, x ∈ A → (ρ.comp (MonoidHom.inl G H)) g x ∈ A) (hA0 : A ≠ ⊥) :
    ∃ x ∈ A, x ∈ fixed (ρ.comp (MonoidHom.inl G H)) K ∧ x ≠ 0 := by
  classical
  by_contra hcon
  have hno : ∀ x ∈ A, x ∈ fixed (ρ.comp (MonoidHom.inl G H)) K → x = 0 := by
    intro x hxA hxK
    by_contra hx0
    exact hcon ⟨x, hxA, hxK, hx0⟩
  have hinl : ∀ (g : G) (x : V), (ρ.comp (MonoidHom.inl G H)) g x = ρ (g, 1) x := fun g x => rfl
  have hinv1 : ∀ (h : H) (y : V), ρ (1, h⁻¹) (ρ (1, h) y) = y := by
    intro h y
    rw [← Module.End.mul_apply, ← map_mul]
    have e : ((1, h⁻¹) * (1, h) : G × H) = 1 := Prod.ext (by simp) (by simp)
    rw [e, map_one, Module.End.one_apply]
  let T : H → Submodule ℂ V := fun h => A.map (ρ (1, h))
  have hTinv : ∀ h, ∀ g, ∀ ⦃x⦄, x ∈ T h → (ρ.comp (MonoidHom.inl G H)) g x ∈ T h := by
    rintro h g _ ⟨a, ha, rfl⟩
    rw [hinl, inl_inr_comm]
    exact ⟨ρ (g, 1) a, hA g ha, rfl⟩
  have hT0 : ∀ h, ∀ x ∈ T h, x ∈ fixed (ρ.comp (MonoidHom.inl G H)) K → x = 0 := by
    rintro h _ ⟨a, ha, rfl⟩ hxK
    have haK : a ∈ fixed (ρ.comp (MonoidHom.inl G H)) K := by
      rw [mem_fixed_iff_forall] at hxK ⊢
      intro k hk
      have e := hxK k hk
      rw [hinl, inl_inr_comm] at e
      have e2 := congrArg (ρ (1, h⁻¹)) e
      rwa [hinv1, hinv1] at e2
    show ρ (1, h) a = 0
    rw [hno a ha haK, map_zero]
  have hP : ∀ s : Finset H,
      (∀ g, ∀ ⦃x⦄, x ∈ ⨆ h ∈ s, T h → (ρ.comp (MonoidHom.inl G H)) g x ∈ ⨆ h ∈ s, T h) ∧
      (∀ x ∈ ⨆ h ∈ s, T h, x ∈ fixed (ρ.comp (MonoidHom.inl G H)) K → x = 0) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · have e : (⨆ h ∈ (∅ : Finset H), T h) = ⊥ := by simp
      rw [e]
      refine ⟨fun g x hx => ?_, fun x hx _ => (Submodule.mem_bot ℂ).mp hx⟩
      rw [(Submodule.mem_bot ℂ).mp hx, map_zero]
      exact Submodule.zero_mem _
    · intro a s _ ih
      rw [Finset.iSup_insert]
      refine ⟨?_, ?_⟩
      · intro g x hx
        obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
        rw [map_add]
        exact Submodule.add_mem_sup (hTinv a g hy) (ih.1 g hz)
      · intro x hx hxK
        exact fixed_sup_eq_zero hs hK (hTinv a) ih.1 (hT0 a) ih.2 hx hxK
  let B : Submodule ℂ V := ⨆ h, T h
  have hBinv : ∀ (gh : G × H) ⦃x : V⦄, x ∈ B → ρ gh x ∈ B := by
    intro gh x hx
    have hle : B ≤ B.comap (ρ gh) := by
      refine iSup_le fun h => ?_
      rintro _ ⟨a, ha, rfl⟩
      show ρ gh (ρ (1, h) a) ∈ B
      have e : gh * (1, h) = (1, gh.2 * h) * (gh.1, 1) := Prod.ext (by simp) (by simp)
      rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply]
      exact (le_iSup T (gh.2 * h)) ⟨ρ (gh.1, 1) a, hA gh.1 ha, rfl⟩
    exact hle hx
  have hAB : A ≤ B := by
    intro a ha
    refine (le_iSup T 1) ⟨a, ha, ?_⟩
    show ρ (1, 1) a = a
    rw [Prod.mk_one_one, map_one, Module.End.one_apply]
  haveI : IsSimpleOrder (Subrepresentation ρ) := hi
  let SB : Subrepresentation ρ := ⟨B, hBinv⟩
  have hSB : SB = ⊤ := by
    rcases IsSimpleOrder.eq_bot_or_eq_top SB with h | h
    · exfalso
      apply hA0
      have hB : B = ⊥ := congrArg Subrepresentation.toSubmodule h
      rw [hB] at hAB
      exact le_bot_iff.mp hAB
    · exact h
  have hvB : v ∈ B := by
    have hB : B = ⊤ := congrArg Subrepresentation.toSubmodule hSB
    rw [hB]
    exact Submodule.mem_top
  obtain ⟨s, hs'⟩ := (Submodule.mem_iSup_iff_exists_finset).mp hvB
  exact hv ((hP s).2 v hs' hvK)

end Product

theorem exists_irreducible_sub_inl : ∀ {G H V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [AddCommGroup V] [Module ℂ V], (∀ U ∈ 𝓝 (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U) → (∀ U ∈ 𝓝 (1 : H), ∃ K : Subgroup H, IsOpen (K : Set H) ∧ IsCompact (K : Set H) ∧ (K : Set H) ⊆ U) → ∀ ρ : Representation ℂ (G × H) V, IsAdmissible ρ → ρ.IsIrreducible → ∃ (K : Subgroup G) (S : Subrepresentation (ρ.comp (MonoidHom.inl G H))) (u : V), IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ u ∈ S.toSubmodule ∧ u ≠ 0 ∧ (∀ x ∈ K, ρ (x, 1) u = u) ∧ S.toRepresentation.IsIrreducible ∧ FiniteDimensional ℂ (fixed S.toRepresentation K) := by
  intro G H V _ _ _ _ _ _ _ _ hG hH ρ hadm hi
  haveI : IsSimpleOrder (Subrepresentation ρ) := hi
  obtain ⟨v, hv0⟩ : ∃ v : V, v ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply (bot_ne_top : (⊥ : Subrepresentation ρ) ≠ ⊤)
    apply Subrepresentation.ext
    ext x
    rw [hcon x]
    exact ⟨fun _ => Submodule.zero_mem _, fun _ => Submodule.zero_mem _⟩
  have hU : {gh : G × H | ρ gh v = v} ∈ 𝓝 ((1 : G), (1 : H)) :=
    (hadm.1 v).mem_nhds (by show ρ (1, 1) v = v; rw [Prod.mk_one_one, map_one, Module.End.one_apply])
  obtain ⟨U1, hU1, U2, hU2, hUU⟩ := mem_nhds_prod_iff.mp hU
  obtain ⟨K1, hK1o, hK1c, hK1U⟩ := hG U1 hU1
  obtain ⟨K2, hK2o, hK2c, hK2U⟩ := hH U2 hU2
  have hfix : ∀ k1 ∈ K1, ∀ k2 ∈ K2, ρ (k1, k2) v = v := fun k1 hk1 k2 hk2 =>
    hUU ⟨hK1U hk1, hK2U hk2⟩
  have hinl : ∀ (g : G) (x : V), (ρ.comp (MonoidHom.inl G H)) g x = ρ (g, 1) x := fun g x => rfl
  let W : Submodule ℂ V := fixed (ρ.comp (MonoidHom.inr G H)) K2
  have hW : ∀ g, ∀ ⦃x⦄, x ∈ W → (ρ.comp (MonoidHom.inl G H)) g x ∈ W := by
    intro g x hx
    have hx' : x ∈ fixed (ρ.comp (MonoidHom.inr G H)) K2 := hx
    show _ ∈ fixed (ρ.comp (MonoidHom.inr G H)) K2
    rw [mem_fixed_iff_forall] at hx' ⊢
    intro k hk
    have e := hx' k hk
    show ρ (1, k) (ρ (g, 1) x) = ρ (g, 1) x
    rw [← inl_inr_comm]
    exact congrArg (ρ (g, 1)) e
  have hvW : v ∈ W := by
    show v ∈ fixed (ρ.comp (MonoidHom.inr G H)) K2
    rw [mem_fixed_iff_forall]
    intro k hk
    exact hfix 1 (one_mem K1) k hk
  have hW0 : W ≠ ⊥ := by
    intro h
    apply hv0
    have hvW' := hvW
    rw [h] at hvW'
    exact (Submodule.mem_bot ℂ).mp hvW'
  have hvK : v ∈ fixed (ρ.comp (MonoidHom.inl G H)) K1 := by
    rw [mem_fixed_iff_forall]
    intro k hk
    exact hfix k hk 1 (one_mem K2)
  have hprodO : IsOpen ((K1.prod K2 : Subgroup (G × H)) : Set (G × H)) := by
    rw [Subgroup.coe_prod]
    exact hK1o.prod hK2o
  have hprodC : IsCompact ((K1.prod K2 : Subgroup (G × H)) : Set (G × H)) := by
    rw [Subgroup.coe_prod]
    exact hK1c.prod hK2c
  haveI hfprod : FiniteDimensional ℂ ↥(fixed ρ (K1.prod K2)) := hadm.2 _ hprodO hprodC
  have hfin : FiniteDimensional ℂ ↥(W ⊓ fixed (ρ.comp (MonoidHom.inl G H)) K1) := by
    refine Submodule.finiteDimensional_of_le (S₂ := fixed ρ (K1.prod K2)) ?_
    rintro x ⟨hxW0, hxK0⟩
    have hxW : x ∈ fixed (ρ.comp (MonoidHom.inr G H)) K2 := hxW0
    have hxK : x ∈ fixed (ρ.comp (MonoidHom.inl G H)) K1 := hxK0
    show x ∈ fixed ρ (K1.prod K2)
    rw [mem_fixed_iff_forall] at hxW hxK ⊢
    rintro ⟨k1, k2⟩ ⟨hk1, hk2⟩
    have e : ((k1, k2) : G × H) = (k1, 1) * (1, k2) := Prod.ext (by simp) (by simp)
    rw [e, map_mul, Module.End.mul_apply]
    have e2 : ρ (1, k2) x = x := hxW k2 hk2
    have e3 : ρ (k1, 1) x = x := hxK k1 hk1
    rw [e2, e3]
  have hs : IsSmooth (ρ.comp (MonoidHom.inl G H)) := by
    intro x
    have hc : Continuous fun g : G => ((g, 1) : G × H) := by fun_prop
    exact (hadm.1 x).preimage hc
  have hnz : ∀ A : Submodule ℂ V, (∀ g, ∀ ⦃x⦄, x ∈ A → (ρ.comp (MonoidHom.inl G H)) g x ∈ A) → A ≠ ⊥ →
      ∃ x ∈ A, x ∈ fixed (ρ.comp (MonoidHom.inl G H)) K1 ∧ x ≠ 0 :=
    fun A hA hA0 => exists_fixed_of_ne_bot ρ hi hs hK1c hv0 hvK A hA hA0
  obtain ⟨S, u, huS, hu0, huK, hSirr, hSfin⟩ := exists_irreducible_of_fixed hW hW0 hfin hnz
  exact ⟨K1, S, u, hK1o, hK1c, huS, hu0, fun x hx => (mem_fixed_iff_forall.mp huK) x hx, hSirr, hSfin⟩

end GlobalTheory.CompanionTheory.ProdSub
