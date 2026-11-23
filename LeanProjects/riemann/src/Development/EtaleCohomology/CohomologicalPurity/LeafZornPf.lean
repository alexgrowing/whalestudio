import Development.EtaleCohomology.CohomologicalPurity.LeafClCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.ZornPf
open LateralTheory.CohomologicalPurity.Cl

theorem rs_rs {R : Type} [CommRing R] {G : Shv R} {X : Scheme.{0}} {U V W : X.Opens} (h1 : U ≤ V) (h2 : V ≤ W)
    (a : Sec G W.toScheme) : rs h1 (rs h2 a) = rs (h1.trans h2) a := by
  change (G.obj.map (X.homOfLE h1).op).hom ((G.obj.map (X.homOfLE h2).op).hom a) = (G.obj.map (X.homOfLE _).op).hom a
  rw [← Scheme.homOfLE_homOfLE X h1 h2, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem rs_refl {R : Type} [CommRing R] {G : Shv R} {X : Scheme.{0}} {U : X.Opens} (h : U ≤ U)
    (a : Sec G U.toScheme) : rs h a = a := by
  change (G.obj.map (X.homOfLE h).op).hom a = a
  rw [Scheme.homOfLE_rfl X U]
  simp

theorem rs_sub {R : Type} [CommRing R] {G : Shv R} {X : Scheme.{0}} {U V : X.Opens} (h : U ≤ V)
    (a b : Sec G V.toScheme) : rs h (a - b) = rs h a - rs h b := map_sub _ _ _

theorem rs_add {R : Type} [CommRing R] {G : Shv R} {X : Scheme.{0}} {U V : X.Opens} (h : U ≤ V)
    (a b : Sec G V.toScheme) : rs h (a + b) = rs h a + rs h b := map_add _ _ _

theorem glue {R : Type} [CommRing R] (G : Shv R) {X : Scheme.{0}} {A : Type*} (V : A → X.Opens)
    (s : ∀ k, Sec G (V k).toScheme) (hc : ∀ k l, rs inf_le_left (s k) = rs inf_le_right (s l)) :
    ∃ c : Sec G (⨆ k, V k).toScheme, ∀ k, rs (le_iSup V k) c = s k := by
  have hG : Presheaf.IsSheaf (Scheme.etaleTopology) (G.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) :=
    (Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget (ModuleCat.{1} (ULift.{1} R)))).1 G.cond
  have hmem : Sieve.generate (Presieve.ofArrows (fun k => (V k).toScheme) (fun k => X.homOfLE (le_iSup V k)))
      ∈ Scheme.etaleTopology (⨆ k, V k).toScheme := by
    apply Precoverage.generate_mem_toGrothendieck
    refine (Scheme.ofArrows_mem_precoverage_iff (P := (@Etale : MorphismProperty Scheme.{0}))).2 ⟨fun x => ?_, fun i => ?_⟩
    · have hx : (x.1 : X) ∈ ⨆ k, V k := x.2
      rw [TopologicalSpace.Opens.mem_iSup] at hx
      obtain ⟨k, hk⟩ := hx
      refine ⟨k, ⟨⟨x.1, hk⟩, ?_⟩⟩
      apply Subtype.ext
      exact Scheme.homOfLE_apply (le_iSup V k) ⟨x.1, hk⟩
    · infer_instance
  have hS := hG.isSheafFor _ hmem
  rw [← Presieve.isSheafFor_iff_generate, Presieve.isSheafFor_arrows_iff] at hS
  obtain ⟨c, hc', -⟩ := hS s (by
    intro i j Z gi gj e
    have e' : gi ≫ (V i).ι = gj ≫ (V j).ι := by
      have := congrArg (· ≫ (⨆ k, V k).ι) e
      simpa using this
    have hr : Set.range (gi ≫ (V i).ι) ⊆ Set.range (V i ⊓ V j).ι := by
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Opens.range_ι]
      refine ⟨?_, ?_⟩
      · have : (gi ≫ (V i).ι) z ∈ Set.range (V i).ι := ⟨gi z, rfl⟩
        rwa [Scheme.Opens.range_ι] at this
      · rw [e']
        have : (gj ≫ (V j).ι) z ∈ Set.range (V j).ι := ⟨gj z, rfl⟩
        rwa [Scheme.Opens.range_ι] at this
    let l := IsOpenImmersion.lift (V i ⊓ V j).ι (gi ≫ (V i).ι) hr
    have hl : l ≫ (V i ⊓ V j).ι = gi ≫ (V i).ι := IsOpenImmersion.lift_fac _ _ _
    have li : gi = l ≫ X.homOfLE (inf_le_left : V i ⊓ V j ≤ V i) := by
      rw [← cancel_mono (V i).ι, Category.assoc, Scheme.homOfLE_ι, hl]
    have lj : gj = l ≫ X.homOfLE (inf_le_right : V i ⊓ V j ≤ V j) := by
      rw [← cancel_mono (V j).ι, Category.assoc, Scheme.homOfLE_ι, hl, e']
    change (G.obj.map gi.op).hom (s i) = (G.obj.map gj.op).hom (s j)
    rw [li, lj, op_comp, op_comp, Functor.map_comp, Functor.map_comp, ModuleCat.hom_comp, ModuleCat.hom_comp,
      LinearMap.comp_apply, LinearMap.comp_apply]
    exact congrArg (G.obj.map l.op).hom (hc i j))
  exact ⟨c, hc'⟩

theorem LeafZorn_of : LeafZorn := by
  intro R _ G X N hres hloc hfl W A V h a hcov hcomp
  let P : (Σ T : X.Opens, Sec G T.toScheme) → Prop :=
    fun p => ∀ k, rs inf_le_left p.2 - rs inf_le_right (a k) ∈ N (p.1 ⊓ V k)
  let r : {p // P p} → {p // P p} → Prop := fun p q => ∃ hh : p.1.1 ≤ q.1.1, rs hh q.1.2 = p.1.2
  have htrans : ∀ {p q s : {p // P p}}, r p q → r q s → r p s := by
    rintro p q s ⟨h1, e1⟩ ⟨h2, e2⟩
    exact ⟨h1.trans h2, by rw [← e1, ← e2, rs_rs]⟩
  have hchain : ∀ C : Set {p // P p}, IsChain r C → ∃ ub, ∀ p ∈ C, r p ub := by
    intro C hC
    let Vc : C → X.Opens := fun p => p.1.1.1
    obtain ⟨c, hc⟩ := glue G Vc (fun p : C => p.1.1.2) (by
      intro p q
      by_cases hpq : p.1 = q.1
      · obtain rfl : p = q := Subtype.ext hpq
        rfl
      · rcases hC p.2 q.2 hpq with ⟨hh, e⟩ | ⟨hh, e⟩
        · show rs inf_le_left p.1.1.2 = rs inf_le_right q.1.1.2
          rw [← e, rs_rs]
        · show rs inf_le_left p.1.1.2 = rs inf_le_right q.1.1.2
          rw [← e, rs_rs])
    refine ⟨⟨⟨⨆ p, Vc p, c⟩, fun k => ?_⟩, fun p hp => ⟨le_iSup Vc ⟨p, hp⟩, hc ⟨p, hp⟩⟩⟩
    apply hloc
    intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    change x ∈ (⨆ p, Vc p) at hx1
    rw [TopologicalSpace.Opens.mem_iSup] at hx1
    obtain ⟨p, hp⟩ := hx1
    have h' : Vc p ⊓ V k ≤ (⨆ p, Vc p) ⊓ V k := inf_le_inf_right _ (le_iSup Vc p)
    refine ⟨Vc p ⊓ V k, h', ⟨hp, hx2⟩, ?_⟩
    have key : rs h' (rs inf_le_left c - rs inf_le_right (a k)) =
        rs inf_le_left p.1.1.2 - rs inf_le_right (a k) := by
      rw [rs_sub, rs_rs, rs_rs, show rs (h'.trans inf_le_left) c = rs inf_le_left (rs (le_iSup Vc p) c) by
        rw [rs_rs], hc p]
    rw [key]
    exact p.1.2 k
  obtain ⟨m, hm⟩ := exists_maximal_of_chains_bounded hchain htrans
  have hVT : ∀ k, V k ≤ m.1.1 := by
    intro k
    have hd := m.2 k
    obtain ⟨n, hn, hnd⟩ := hfl _ _ inf_le_right _ hd
    let Vb : Bool → X.Opens := fun b => Bool.rec (V k) m.1.1 b
    have hn' := congrArg (rs (inf_comm (V k) m.1.1).le) hnd
    rw [rs_rs, rs_sub, rs_rs, rs_rs] at hn'
    obtain ⟨e, he⟩ := glue G Vb (fun b => Bool.rec (motive := fun b => Sec G (Vb b).toScheme) (a k + n) m.1.2 b) (by
      intro i j
      cases i <;> cases j
      · rfl
      · show rs inf_le_left (a k + n) = rs inf_le_right m.1.2
        rw [rs_add, hn']
        abel
      · show rs inf_le_left m.1.2 = rs inf_le_right (a k + n)
        rw [rs_add, hnd]
        abel
      · rfl)
    have hP : P ⟨⨆ b, Vb b, e⟩ := by
      intro l
      apply hloc
      intro x hx
      obtain ⟨hx1, hx2⟩ := hx
      change x ∈ (⨆ b, Vb b) at hx1
      rw [TopologicalSpace.Opens.mem_iSup] at hx1
      obtain ⟨b, hb⟩ := hx1
      have h' : Vb b ⊓ V l ≤ (⨆ b, Vb b) ⊓ V l := inf_le_inf_right _ (le_iSup Vb b)
      refine ⟨Vb b ⊓ V l, h', ⟨hb, hx2⟩, ?_⟩
      have key : rs h' (rs inf_le_left e - rs inf_le_right (a l)) =
          rs inf_le_left (rs (le_iSup Vb b) e) - rs inf_le_right (a l) := by
        rw [rs_sub, rs_rs, rs_rs, rs_rs]
      rw [key, he b]
      cases b
      · show rs inf_le_left (a k + n) - rs inf_le_right (a l) ∈ N (V k ⊓ V l)
        rw [rs_add, show rs inf_le_left (a k) + rs inf_le_left n - rs inf_le_right (a l) =
          (rs inf_le_left (a k) - rs inf_le_right (a l)) + rs inf_le_left n by abel]
        exact add_mem (hcomp k l) (hres _ _ _ n hn)
      · exact m.2 l
    obtain ⟨hh, -⟩ := hm ⟨_, hP⟩ ⟨le_iSup Vb true, he true⟩
    exact (le_iSup Vb false).trans hh
  have hWT : W ≤ m.1.1 := by
    intro x hx
    obtain ⟨k, hk⟩ := hcov x hx
    exact hVT k hk
  refine ⟨rs hWT m.1.2, fun k => ?_⟩
  have hk : V k ≤ m.1.1 ⊓ V k := le_inf (hVT k) le_rfl
  have key : rs hk (rs inf_le_left m.1.2 - rs inf_le_right (a k)) = rs (h k) (rs hWT m.1.2) - a k := by
    rw [rs_sub, rs_rs, rs_rs, rs_rs, rs_refl]
  rw [← key]
  exact hres _ _ hk _ (m.2 k)

end LateralTheory.CohomologicalPurity.ZornPf
