import Development.AutomorphicArithmetic.CupPullbacks.ConstCompSingle

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC UpperTheory.Pbf

private theorem unit_on_basicOpen (T : Scheme.{0}) (a : Γ(T, ⊤)) :
    IsUnit ((T.basicOpen a).ι.appTop.hom a) := by
  have hb := Scheme.Opens.ι_preimage_self (T.basicOpen a)
  rw [Scheme.preimage_basicOpen] at hb
  apply RingedSpace.isUnit_of_isUnit_germ _ ⊤
  intro x hx
  have hx' : x ∈ (T.basicOpen a).toScheme.basicOpen
      ((ConcreteCategory.hom ((T.basicOpen a).ι.app ⊤)) a) := by
    rw [hb]
    trivial
  exact (Scheme.mem_basicOpen _ _ x hx).mp hx'

private theorem mem_basicOpen_or (T : Scheme.{0}) (a b : Γ(T, ⊤)) (h : Ideal.span {a, b} = ⊤) (u : T) :
    u ∈ T.basicOpen a ∨ u ∈ T.basicOpen b := by
  have h1 : (1 : Γ(T, ⊤)) ∈ Ideal.span {a, b} := h ▸ Submodule.mem_top
  obtain ⟨x, y, hxy⟩ := Ideal.mem_span_pair.mp h1
  have hu : IsUnit (ConcreteCategory.hom (T.presheaf.germ ⊤ u trivial) (x * a) +
      ConcreteCategory.hom (T.presheaf.germ ⊤ u trivial) (y * b)) := by
    rw [← map_add, hxy, map_one]
    exact isUnit_one
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hu with hx | hy
  · left
    rw [Scheme.mem_basicOpen_top]
    rw [map_mul] at hx
    exact isUnit_of_mul_isUnit_right hx
  · right
    rw [Scheme.mem_basicOpen_top]
    rw [map_mul] at hy
    exact isUnit_of_mul_isUnit_right hy

theorem UpperTheory.locally_isUnit_or_isUnit_of_span_pair_eq_top :
    ∀ (T : Scheme.{0}) (a b : Γ(T, ⊤)), Ideal.span {a, b} = ⊤ → Loc T fun V g => IsUnit (g.appTop.hom a) ∨ IsUnit (g.appTop.hom b) := by
  intro T a b h
  let U : Bool → T.Opens := fun i => bif i then T.basicOpen a else T.basicOpen b
  have hU : TopologicalSpace.IsOpenCover U := by
    apply eq_top_iff.mpr
    intro u _
    rcases mem_basicOpen_or T a b h u with hu | hu
    · exact TopologicalSpace.Opens.mem_iSup.mpr ⟨true, hu⟩
    · exact TopologicalSpace.Opens.mem_iSup.mpr ⟨false, hu⟩
  let C := T.openCoverOfIsOpenCover U hU
  refine ⟨Sieve.ofArrows C.X C.f,
    Scheme.zariskiTopology_le_etaleTopology _ (Scheme.Cover.mem_grothendieckTopology C), ?_⟩
  intro V g hg
  obtain ⟨i, c, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ g).mp hg
  cases i
  · right
    rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
    exact (unit_on_basicOpen T b).map c.appTop.hom
  · left
    rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
    exact (unit_on_basicOpen T a).map c.appTop.hom
