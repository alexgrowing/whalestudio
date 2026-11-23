import Development.EtaleCohomology.CohomologicalPurity.LeafFreeCokPfSurj

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
namespace LateralTheory.CohomologicalPurity

theorem exact_app_of_π {R : Type} [CommRing R] {F G : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} (f : F ⟶ G)
    (V : Scheme.{0}ᵒᵖ) (m : G.obj V) (hm : (cokernel.π f).app V m = 0) : ∃ n, f.app V n = m := by
  let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have hS : S.Exact := S.exact_of_g_is_cokernel (cokernelIsCokernel f)
  have h2 := hS.map ((evaluation _ _).obj V)
  rw [ShortComplex.moduleCat_exact_iff] at h2
  exact h2 m hm

theorem mapDomain_apply_eq_sum {α β M : Type*} [AddCommMonoid M] [DecidableEq β] (v : α →₀ M) (f : α → β) (t : β) :
    Finsupp.mapDomain f v t = ∑ a ∈ v.support with f a = t, v a := by
  classical
  unfold Finsupp.mapDomain
  rw [Finsupp.sum_apply, Finsupp.sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finsupp.single_apply]

theorem core {α β γ M : Type*} [AddCommMonoid M] (v : α →₀ M) (f : α → β) (r : α → γ)
    (Q : β → Prop) (P : γ → Prop)
    (hv : ∀ t, ¬ Q t → Finsupp.mapDomain f v t = 0)
    (hQ : ∀ a, Q (f a) → P (r a))
    (hP : ∀ a₁ a₂, f a₁ = f a₂ → P (r a₁) → P (r a₂))
    (h : ∀ a₁ ∈ v.support, ∀ a₂ ∈ v.support, f a₁ = f a₂ → r a₁ = r a₂ ∨ P (r a₁)) :
    ∀ z, ¬ P z → Finsupp.mapDomain r v z = 0 := by
  classical
  intro z hz
  rw [mapDomain_apply_eq_sum]
  set s' := v.support.filter (fun a => r a = z)
  rw [← Finset.sum_fiberwise_of_maps_to (s := s') (t := s'.image f) (g := f)
    (fun a ha => Finset.mem_image_of_mem f ha)]
  refine Finset.sum_eq_zero fun t ht => ?_
  obtain ⟨a₀, ha₀, rfl⟩ := Finset.mem_image.1 ht
  have ha₀' := Finset.mem_filter.1 ha₀
  have hQ0 : ¬ Q (f a₀) := fun hq => hz (ha₀'.2 ▸ hQ a₀ hq)
  have e : (s'.filter fun a => f a = f a₀) = v.support.filter (fun a => f a = f a₀) := by
    ext a
    simp only [s', Finset.mem_filter]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      refine ⟨⟨h1, ?_⟩, h3⟩
      rcases h a h1 a₀ ha₀'.1 h3 with e | p
      · rw [e, ha₀'.2]
      · exact absurd (ha₀'.2 ▸ hP a a₀ h3 p) hz
  rw [e]
  have := mapDomain_apply_eq_sum v f (f a₀)
  rw [hv _ hQ0] at this
  convert this.symm

theorem exists_covering_finset {T : Scheme.{0}} {ι : Type*} (s : Finset ι)
    (Pr : ι → ∀ ⦃V : Scheme.{0}⦄, (V ⟶ T) → Prop)
    (hPr : ∀ p ∈ s, ∃ S ∈ Scheme.etaleTopology T, ∀ ⦃V : Scheme.{0}⦄ (g : V ⟶ T), S g → Pr p g) :
    ∃ S ∈ Scheme.etaleTopology T, ∀ p ∈ s, ∀ ⦃V : Scheme.{0}⦄ (g : V ⟶ T), S g → Pr p g := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨⊤, Scheme.etaleTopology.top_mem T, by simp⟩
  | insert q s hq ih =>
    obtain ⟨S₁, h₁, H₁⟩ := ih (fun p hp => hPr p (Finset.mem_insert_of_mem hp))
    obtain ⟨S₂, h₂, H₂⟩ := hPr q (Finset.mem_insert_self q s)
    refine ⟨S₁ ⊓ S₂, Scheme.etaleTopology.intersection_covering h₁ h₂, ?_⟩
    intro p hp V g hg
    rcases Finset.mem_insert.1 hp with rfl | hp
    · exact H₂ g hg.2
    · exact H₁ p hp g hg.1

theorem mem_range_mapDomain {α β M : Type*} [AddCommMonoid M] (u : α → β) (w : β →₀ M)
    (hw : ∀ z, (¬ ∃ x, u x = z) → w z = 0) : ∃ n : α →₀ M, Finsupp.mapDomain u n = w := by
  have hmem : w ∈ Finsupp.supported M ℕ (u '' Set.univ) := by
    rw [Finsupp.mem_supported]
    intro z hz
    by_contra hc
    exact (Finsupp.mem_support_iff.1 hz) (hw z (fun ⟨x, hx⟩ => hc ⟨x, trivial, hx⟩))
  rw [← Finsupp.lmapDomain_supported] at hmem
  obtain ⟨n, _, hn⟩ := hmem
  exact ⟨n, hn⟩

theorem leafFreeCokInj : LeafFreeCokInj := by
  intro R _ A' B' A B i' i a b w h1 h3
  have key : ∀ (T : Scheme.{0}) (z : (cokernel ((freeP R).map i')).obj (op T)),
      (pcok R i' i a b w).app (op T) z = 0 → Presheaf.equalizerSieve z 0 ∈ Scheme.etaleTopology T := by
    intro T z hz
    obtain ⟨v, rfl⟩ := π_app_surj R i' (op T) z
    rw [pcok_π_apply] at hz
    obtain ⟨n, hn⟩ := exact_app_of_π _ _ _ hz
    have hn' : Finsupp.mapDomain (fun x : ULift.{1} (A.obj (op T)) => ULift.up (i.app (op T) x.down)) n =
        Finsupp.mapDomain (fun x : ULift.{1} (B'.obj (op T)) => ULift.up (b.app (op T) x.down)) v := hn
    let Pr : (ULift.{1} (B'.obj (op T)) × ULift.{1} (B'.obj (op T))) → ∀ ⦃V : Scheme.{0}⦄, (V ⟶ T) → Prop :=
      fun p V g => b.app (op T) p.1.down = b.app (op T) p.2.down →
        B'.map g.op p.1.down = B'.map g.op p.2.down ∨
          ∃ x : A.obj (op V), i.app (op V) x = b.app (op V) (B'.map g.op p.1.down)
    obtain ⟨S, hS, HS⟩ := exists_covering_finset (v.support ×ˢ v.support) Pr (by
      intro p _
      by_cases he : b.app (op T) p.1.down = b.app (op T) p.2.down
      · obtain ⟨S, hS, H⟩ := h3 T p.1.down p.2.down he
        exact ⟨S, hS, fun V g hg _ => H g hg⟩
      · exact ⟨⊤, Scheme.etaleTopology.top_mem T, fun V g _ he' => absurd he' he⟩)
    refine Scheme.etaleTopology.superset_covering ?_ hS
    intro V g hg
    show (cokernel ((freeP R).map i')).map g.op _ = (cokernel ((freeP R).map i')).map g.op 0
    rw [map_zero, ← NatTrans.naturality_apply]
    have hcore := core v (fun x : ULift.{1} (B'.obj (op T)) => (ULift.up.{1} (b.app (op T) x.down) : ULift.{1} (B.obj (op T))))
      (fun x : ULift.{1} (B'.obj (op T)) => ULift.up (B'.map g.op x.down))
      (fun t : ULift.{1} (B.obj (op T)) => ∃ x, i.app (op T) x = t.down) (fun z => ∃ x', i'.app (op V) x' = z.down)
      (by
        intro t ht
        have := Finsupp.mapDomain_notin_range n t (by
          rintro ⟨x, hx⟩
          exact ht ⟨x.down, congrArg ULift.down hx⟩)
        exact (DFunLike.congr_fun hn' t).symm.trans this)
      (by
        rintro a₀ ⟨x, hx⟩
        obtain ⟨x', hx'⟩ := h1 T a₀.down x hx
        exact ⟨A'.map g.op x', by rw [FunctorToTypes.naturality, hx']⟩)
      (by
        rintro a₁ a₂ he ⟨x', hx'⟩
        have he' : b.app (op T) a₁.down = b.app (op T) a₂.down := congrArg ULift.down he
        refine h1 V (B'.map g.op a₂.down) (a.app (op V) x') ?_
        have := ConcreteCategory.congr_hom (NatTrans.congr_app w (op V)) x'
        simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at this
        rw [← this, hx', FunctorToTypes.naturality, FunctorToTypes.naturality, he'])
      (by
        intro a₁ ha₁ a₂ ha₂ he
        rcases HS (a₁, a₂) (Finset.mem_product.2 ⟨ha₁, ha₂⟩) g hg (congrArg ULift.down he) with e | ⟨x, hx⟩
        · left; exact congrArg ULift.up e
        · right; exact h1 V _ x hx)
    obtain ⟨n', hn''⟩ := mem_range_mapDomain (fun x : ULift.{1} (A'.obj (op V)) => ULift.up (i'.app (op V) x.down)) _
      (fun z hz => hcore z (fun ⟨x', hx'⟩ => hz ⟨ULift.up x', congrArg ULift.up hx' |>.trans rfl⟩))
    have e2 : ((freeP R).obj B').map g.op v = ((freeP R).map i').app (op V) n' := hn''.symm
    rw [e2]
    exact π_freeP_apply R i' (op V) n'
  constructor
  intro X x y hxy
  cases X with | op T =>
  refine Scheme.etaleTopology.superset_covering ?_ (key T (x - y) (by rw [map_sub, hxy, sub_self]))
  intro V g hg
  have hg' : (cokernel ((freeP R).map i')).map g.op (x - y) = (cokernel ((freeP R).map i')).map g.op 0 := hg
  rw [map_sub, map_zero, sub_eq_zero] at hg'
  exact hg'

theorem LeafFreeCokInj_of : LeafFreeCokInj := leafFreeCokInj

end LateralTheory.CohomologicalPurity
