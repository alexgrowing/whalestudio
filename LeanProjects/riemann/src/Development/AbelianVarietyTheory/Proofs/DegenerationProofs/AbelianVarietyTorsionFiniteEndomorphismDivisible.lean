import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsEqPowOfTorsionCompEqOne

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.TorsionDivisible

theorem hom_ext_of_rationalPoints {K : Type} [Field K] [IsAlgClosed K] {X Y : Over (Sp K)}
    [IsReduced X.left] [LocallyOfFiniteType X.hom] [IsProper Y.hom] (f g : X ⟶ Y)
    (h : ∀ x : 𝟙_ (Over (Sp K)) ⟶ X, x ≫ f = x ≫ g) : f = g := by
  have : LocallyOfFiniteType (f.left ≫ Y.hom) := by rw [Over.w]; infer_instance
  refine Over.OverMorphism.ext (ext_of_apply_eq (K := K) Y.hom Set.univ
    isOpen_univ.isLocallyClosed dense_univ (fun x _ hx => ?_) (by rw [Over.w, Over.w]))
  let p : 𝟙_ (Over (Sp K)) ⟶ X :=
    Over.homMk (pointOfClosedPoint (K := K) X.hom x hx) (pointOfClosedPoint_comp (K := K) X.hom x hx)
  have h1 : pointOfClosedPoint (K := K) X.hom x hx ≫ f.left =
      pointOfClosedPoint (K := K) X.hom x hx ≫ g.left := congrArg CommaMorphism.left (h p)
  have h2 : f.left (pointOfClosedPoint (K := K) X.hom x hx (IsLocalRing.closedPoint K)) =
      g.left (pointOfClosedPoint (K := K) X.hom x hx (IsLocalRing.closedPoint K)) :=
    congrArg (fun φ => φ (IsLocalRing.closedPoint K)) h1
  have h3 := pointOfClosedPoint_apply (K := K) X.hom x hx (IsLocalRing.closedPoint K)
  exact (congrArg f.left h3).symm.trans (h2.trans (congrArg g.left h3))

theorem finite_fibre_points {K : Type} [Field K] [IsAlgClosed K]
    {X Y : Over (Sp K)} [LocallyOfFiniteType X.hom] (f : X ⟶ Y)
    [IsFinite f.left] (y : 𝟙_ (Over (Sp K)) ⟶ Y) :
    Finite {x : 𝟙_ (Over (Sp K)) ⟶ X // x ≫ f = y} := by
  have hfin : (f.left ⁻¹' {y.left (IsLocalRing.closedPoint K)}).Finite :=
    f.left.finite_preimage_singleton _
  have := hfin.to_subtype
  refine Finite.of_injective
    (fun x => (⟨x.1.left (IsLocalRing.closedPoint K), by
      have h := congrArg (fun u => u.left (IsLocalRing.closedPoint K)) x.2
      exact h⟩ : (f.left ⁻¹' {y.left (IsLocalRing.closedPoint K)}))) ?_
  intro a b hab
  refine Subtype.ext (Over.OverMorphism.ext ?_)
  exact ext_of_apply_closedPoint_eq (K := K) X.hom (Over.w a.1) (Over.w b.1)
    (congrArg Subtype.val hab)

theorem finite_torsion_and_divisible :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B], IsAbelianScheme B → ∀ n : ℕ, (n : k) ≠ 0 → Finite {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} ∧ ∀ f : B ⟶ B, IsMonHom f → (∀ x : (𝟙_ (Over (Sp k)) ⟶ B), x ^ n = 1 → x ≫ f = 1) → ∃ g : B ⟶ B, IsMonHom g ∧ f = g ^ n := by
  intro k _ _ B _ hB n hn
  have := hB.comm
  have := hB.smooth
  have := hB.proper
  have := hB.geomConnected
  have hu : IsUnit (n : Γ(Sp k, ⊤)) := by
    simpa using (isUnit_iff_ne_zero.2 hn).map (Scheme.ΓSpecIso (.of k)).inv.hom
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := GrpTangent.finiteEtale_mulN_torsion B hu
  refine ⟨?_, fun f hf hker => ?_⟩
  · have := finite_fibre_points (mulN B n) 1
    exact Finite.of_equiv _ (Equiv.subtypeEquivRight (p := fun x => x ≫ mulN B n = 1) fun x => by
      rw [GrpTangent.comp_mulN])
  · have : ConnectedSpace B.left := GeometricallyConnected.connectedSpace_of_subsingleton B.hom
    have hc : IsClopen (Set.range (mulN B n).left) :=
      ⟨(mulN B n).left.isClosedMap.isClosed_range, (mulN B n).left.isOpenMap.isOpen_range⟩
    have h5 : Surjective (mulN B n).left :=
      ⟨Set.range_eq_univ.mp (hc.eq_univ (Set.range_nonempty _))⟩
    have : IsReduced (torsion B n).left := isReduced_of_smooth_of_isReduced (torsion B n).hom
    have hι : torsion.ι B n ≫ mulN B n = 1 := by
      rw [Hom.one_def]
      exact pullback.condition.trans (congrArg (· ≫ η[B]) (toUnit_unique _ _))
    have h6 : torsion.ι B n ≫ f = 1 := hom_ext_of_rationalPoints _ _ fun x => by
      rw [← Category.assoc, MonObj.comp_one]
      refine hker _ ?_
      rw [← GrpTangent.comp_mulN, Category.assoc, hι, MonObj.comp_one]
    have h7 : ∀ (T : Over (Sp k)) (x : T ⟶ B), x ^ n = 1 → x ≫ f = 1 := fun T x hx => by
      have e : x ≫ mulN B n = toUnit T ≫ η[B] := by rw [GrpTangent.comp_mulN, hx, Hom.one_def]
      obtain ⟨y, e'⟩ : ∃ y : T ⟶ torsion B n, y ≫ torsion.ι B n = x :=
        ⟨pullback.lift x (toUnit T) e, pullback.lift_fst _ _ _⟩
      rw [← e', Category.assoc, h6, MonObj.comp_one]
    have hm : Out.mulA B n = mulN B n := (GrpTangent.mulN_eq_pow B n).symm
    have : Etale (Out.mulA B n).left := hm ▸ h2
    have : IsFinite (Out.mulA B n).left := hm ▸ h1
    have : Surjective (Out.mulA B n).left := hm ▸ h5
    obtain ⟨φ, hφ⟩ := DivisibleHom.exists_factor n f h7
    have : IsMonHom (Out.mulA B n ≫ φ) := hφ ▸ hf
    have : IsMonHom φ := DivisibleHom.isMonHom_of_factor n φ
    exact ⟨φ, this, by rw [← hφ, DivisibleHom.mulA_comp]⟩

end GlobalTheory.TorsionDivisible
