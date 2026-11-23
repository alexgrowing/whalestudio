import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOpenNonzeroLocusOfUniversallyClosed

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon.FinAffAmple

variable {X : Scheme.{0}} {M : LB X}

theorem mem_secAdd_iff_right {s t : M.Sec} {x : X} (ht : x ∉ nonzeroLocus t) :
    x ∈ nonzeroLocus (DVR.SecOps.secAdd s t) ↔ x ∈ nonzeroLocus s := by
  by_cases hc : ∃ k, x ∈ M.U k
  · obtain ⟨k, hk⟩ := hc
    rw [GlobalTheory.mem_nonzeroLocus_iff_basicOpen _ hk, GlobalTheory.mem_nonzeroLocus_iff_basicOpen _ hk] at *
    change x ∈ X.basicOpen (s.f k + t.f k) ↔ _
    rw [Scheme.mem_basicOpen _ _ _ hk, Scheme.mem_basicOpen _ _ _ hk] at *
    rw [map_add]
    have hm : (ConcreteCategory.hom (X.presheaf.germ (M.U k) x hk)) (t.f k) ∈ IsLocalRing.maximalIdeal _ :=
      (IsLocalRing.mem_maximalIdeal _).2 ht
    have := Ideal.add_mem_iff_left (IsLocalRing.maximalIdeal _)
      (a := (ConcreteCategory.hom (X.presheaf.germ (M.U k) x hk)) (s.f k)) hm
    rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff] at this
    exact not_iff_not.1 this
  · push_neg at hc
    exact ⟨fun h => absurd (GlobalTheory.exists_chart_of_mem_nonzeroLocus h) (by simpa using hc),
      fun h => absurd (GlobalTheory.exists_chart_of_mem_nonzeroLocus h) (by simpa using hc)⟩

theorem mem_secAdd_iff_left {s t : M.Sec} {x : X} (hs : x ∉ nonzeroLocus s) :
    x ∈ nonzeroLocus (DVR.SecOps.secAdd s t) ↔ x ∈ nonzeroLocus t := by
  have e : DVR.SecOps.secAdd s t = DVR.SecOps.secAdd t s := DVR.SecOps.sec_ext fun i => add_comm (s.f i) (t.f i)
  rw [e]
  exact mem_secAdd_iff_right hs

theorem exists_sec_forall_mem (T : Finset X) (t : X → M.Sec) (ht : ∀ x ∈ T, x ∈ nonzeroLocus (t x))
    (ht' : ∀ x ∈ T, ∀ y ∈ T, y ≠ x → y ∉ nonzeroLocus (t x)) :
    ∃ g : M.Sec, ∀ x ∈ T, x ∈ nonzeroLocus g := by
  classical
  suffices H : ∀ T' : Finset X, T' ⊆ T → ∃ g : M.Sec, ∀ x ∈ T, (x ∈ nonzeroLocus g ↔ x ∈ T') by
    obtain ⟨g, hg⟩ := H T subset_rfl
    exact ⟨g, fun x hx => (hg x hx).2 hx⟩
  intro T'
  induction T' using Finset.induction_on with
  | empty =>
    intro _
    refine ⟨DVR.SecOps.secZero, fun x _ => ?_⟩
    rw [GlobalTheory.nonzeroLocus_secZero]
    simp
  | insert a T' ha ih =>
    intro hsub
    obtain ⟨g, hg⟩ := ih ((Finset.subset_insert a T').trans hsub)
    have haT : a ∈ T := hsub (Finset.mem_insert_self a T')
    refine ⟨DVR.SecOps.secAdd g (t a), fun x hx => ?_⟩
    by_cases hxa : x = a
    · subst hxa
      rw [mem_secAdd_iff_left (fun h => ha ((hg x hx).1 h))]
      simpa using ht x haT
    · rw [mem_secAdd_iff_right (ht' a haT x hx hxa), hg x hx, Finset.mem_insert]
      simp [hxa]

theorem exists_specializes_minimal {Z : Type*} [TopologicalSpace Z] [T0Space Z] (F : Finset Z) {x : Z}
    (hx : x ∈ F) : ∃ y ∈ F, x ⤳ y ∧ ∀ z ∈ F, y ⤳ z → z = y := by
  classical
  obtain ⟨y, hy, hmin⟩ := Finset.exists_min_image (F.filter (x ⤳ ·)) (fun y => (F.filter (y ⤳ ·)).card)
    ⟨x, Finset.mem_filter.2 ⟨hx, specializes_refl x⟩⟩
  obtain ⟨hyF, hxy⟩ := Finset.mem_filter.1 hy
  refine ⟨y, hyF, hxy, fun z hz hyz => ?_⟩
  have hsub : F.filter (z ⤳ ·) ⊆ F.filter (y ⤳ ·) := fun w hw => by
    obtain ⟨hwF, hzw⟩ := Finset.mem_filter.1 hw
    exact Finset.mem_filter.2 ⟨hwF, hyz.trans hzw⟩
  have hle := hmin z (Finset.mem_filter.2 ⟨hz, hxy.trans hyz⟩)
  have heq := Finset.eq_of_subset_of_card_le hsub hle
  have hzy : z ⤳ y := (Finset.mem_filter.1 (heq ▸ Finset.mem_filter.2 ⟨hyF, specializes_refl y⟩ :
    y ∈ F.filter (z ⤳ ·))).2
  exact (hyz.antisymm hzy).eq.symm

theorem finAff_of_isAmpleLB {Y : Scheme.{0}} (f : X ⟶ Y) [IsAffine Y] [UniversallyClosed f] {L : LB X}
    (h : IsAmpleLB L) : FinAff X := by
  classical
  intro F
  let F' := F.filter (fun x => ∀ z ∈ F, x ⤳ z → z = x)
  let V : X → X.Opens := fun x =>
    ⟨(⋃ y ∈ F'.erase x, closure ({y} : Set X))ᶜ, (isClosed_biUnion_finset fun _ _ => isClosed_closure).isOpen_compl⟩
  have hV : ∀ x ∈ F', x ∈ V x := by
    intro x hx hmem
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 hmem
    obtain ⟨hyx, hyF'⟩ := Finset.mem_erase.1 hy
    have hyx' : y ⤳ x := specializes_iff_mem_closure.2 hxy
    exact hyx ((Finset.mem_filter.1 hyF').2 x (Finset.mem_filter.1 hx).1 hyx').symm
  have hV' : ∀ x ∈ F', ∀ y ∈ F', y ≠ x → y ∉ V x := fun x _ y hy hyx hmem =>
    hmem (Set.mem_iUnion₂.2 ⟨y, Finset.mem_erase.2 ⟨hyx, hy⟩, subset_closure rfl⟩)
  choose n hn s hs hsV _ using fun x : F' => h.exists_affine_le (hV x.1 x.2)
  obtain ⟨N, hN, t, ht⟩ := exists_common_pow n hn s
  let tt : X → (lbPow L N).Sec := fun x => if hx : x ∈ F' then t ⟨x, hx⟩ else DVR.SecOps.secZero
  have htt : ∀ x (hx : x ∈ F'), nonzeroLocus (tt x) = nonzeroLocus (s ⟨x, hx⟩) := fun x hx => by
    simp only [tt, dif_pos hx, ht]
  obtain ⟨g, hg⟩ := exists_sec_forall_mem F' tt (fun x hx => (htt x hx).symm ▸ hs ⟨x, hx⟩)
    (fun x hx y hy hyx hmem => hV' x hx y hy hyx (hsV ⟨x, hx⟩ ((htt x hx) ▸ hmem)))
  refine ⟨nonzeroLocus g, h.isAffineOpen_nonzeroLocus f hN g, fun x hx => ?_⟩
  obtain ⟨y, hyF, hxy, hmin⟩ := exists_specializes_minimal F hx
  exact hxy.mem_open (nonzeroLocus g).isOpen (hg y (Finset.mem_filter.2 ⟨hyF, hmin⟩))

theorem finAff_of_relAmple : ∀ (R : Type) [CommRing R] (B : Over (Sp R)) [GrpObj B], IsAbelianScheme B →
    ∀ L : LB B.left, L.IsLB → Out.RelAmple B L → FinAff B.left := by
  intro R _ B _ hB L hL hA
  have := hB.proper
  exact finAff_of_isAmpleLB B.hom (isAmpleLB_of_relAmple_of_isAffine B hL hA)

end GlobalTheory.DualCon.FinAffAmple
