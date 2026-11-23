import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenConnectedComponentOfNoetherianSpace
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem eq_one_of_divisible {P Q : Type*} [CommGroup P] [Finite Q] (c : P → Q)
    (hc : ∀ a b t : P, c a = c b → c (a * t) = c (b * t))
    (hd : ∀ n : ℕ, n ≠ 0 → ∀ x : P, ∃ y : P, y ^ n = x) (x : P) : c x = c 1 := by
  let H : Subgroup P :=
    { carrier := {a | c a = c 1}
      one_mem' := rfl
      mul_mem' := fun {a b} ha hb => by
        have := hc a 1 b ha
        rw [_root_.one_mul] at this
        exact this.trans hb
      inv_mem' := fun {a} ha => by
        have := hc a 1 a⁻¹ ha
        rw [_root_.mul_inv_cancel, _root_.one_mul] at this
        exact this.symm }
  have hinj : Function.Injective (fun q : P ⧸ H => c q.out) := by
    intro q r hqr
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' r, QuotientGroup.eq]
    have := hc _ _ (q.out)⁻¹ hqr
    simp only [mul_inv_cancel] at this
    change c _ = c 1
    rw [mul_comm, this.symm]
  have : Finite (P ⧸ H) := Finite.of_injective _ hinj
  have hi : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  obtain ⟨y, rfl⟩ := hd _ hi x
  exact Subgroup.pow_index_mem H y

theorem connectedSpace_of_divisible : ∀ (K : Type) [Field K] [IsAlgClosed K] (G : Over (Sp K)) [GrpObj G] [IsCommMonObj G], LocallyOfFiniteType G.hom → QuasiCompact G.hom → (∀ n : ℕ, n ≠ 0 → ∀ x : 𝟙_ (Over (Sp K)) ⟶ G, ∃ y : 𝟙_ (Over (Sp K)) ⟶ G, y ^ n = x) → ConnectedSpace G.left := by
  intro K _ _ G _ _ hl hq hd
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  have : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  have : IsNoetherian G.left := {}
  have := LocallyOfFiniteType.jacobsonSpace G.hom
  let pt : (𝟙_ (Over (Sp K))).left := IsLocalRing.closedPoint K
  let F : (𝟙_ (Over (Sp K)) ⟶ G) → G.left := fun x => x.left pt
  have hopen : ∀ x : G.left, IsOpen (connectedComponent x) :=
    fun x => isOpen_connectedComponent_of_noetherianSpace x
  have : DiscreteTopology (_root_.ConnectedComponents G.left) :=
    ConnectedComponents.discreteTopology_iff.2 hopen
  have : Finite (_root_.ConnectedComponents G.left) := finite_of_compact_of_discrete
  let c : (𝟙_ (Over (Sp K)) ⟶ G) → _root_.ConnectedComponents G.left := fun x => F x
  have htr : ∀ a t : 𝟙_ (Over (Sp K)) ⟶ G,
      F (a * t) = (GrpObj.mulRight t).hom.left (F a) := by
    intro a t
    have h : a ≫ (GrpObj.mulRight t).hom = a * t := by
      simp [comp_lift_assoc, Hom.mul_def]
    simp only [F, ← h, Over.comp_left, Scheme.Hom.comp_apply]
  have hc : ∀ a b t, c a = c b → c (a * t) = c (b * t) := by
    intro a b t hab
    have := congrArg (Continuous.connectedComponentsMap (GrpObj.mulRight t).hom.left.continuous) hab
    simpa [c, htr] using this
  have hall := eq_one_of_divisible c hc hd
  have hsurj : ∀ x : G.left, IsClosed {x} → ∃ a, F a = x := by
    intro x hx
    refine ⟨Over.homMk (pointOfClosedPoint G.hom x hx) (pointOfClosedPoint_comp G.hom x hx), ?_⟩
    exact pointOfClosedPoint_apply G.hom x hx _
  have huniv : connectedComponent (F 1) = Set.univ := by
    by_contra hne
    obtain ⟨x, hx, hcl⟩ := nonempty_inter_closedPoints (Set.nonempty_compl.2 hne)
      (IsOpen.isLocallyClosed isClosed_connectedComponent.isOpen_compl)
    obtain ⟨a, rfl⟩ := hsurj x hcl
    apply hx
    have h1 : connectedComponent (F a) = connectedComponent (F 1) :=
      ConnectedComponents.coe_eq_coe.1 (hall a)
    rw [← h1]
    exact mem_connectedComponent
  exact connectedSpace_iff_connectedComponent.2 ⟨F 1, huniv⟩

end GlobalTheory.CompanionTheory.Ar.Approx
