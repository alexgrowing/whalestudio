import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPtGenMat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open CategoryTheory.Limits

namespace GlobalTheory.FlagQ

theorem geometricallyConnected_genericFibre : ∀ (ι : Type) [Fintype ι] (N : ℕ),
    GeometricallyConnected (pullback.snd (GlobalTheory.FlagZ.flStr ι N) (spMap (algebraMap ℤ ℚ))) := by
  intro ι _ N
  set f := GlobalTheory.FlagZ.flStr ι N with hf
  set g : Sp ℚ ⟶ Sp ℤ := spMap (algebraMap ℤ ℚ) with hg
  have hP : IsProper f := by
    obtain ⟨M, i, hi, e⟩ := GlobalTheory.FlagZ.isProjOver_str (ι := ι) (N := N) Prod.fst Prod.snd
    have := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str ℤ M
    change IsProper (GlobalTheory.FlagZ.str Prod.fst Prod.snd)
    rw [← e]; infer_instance
  have hb : IsPreimmersion g :=
    IsPreimmersion.of_isLocalization (R := CommRingCat.of ℤ) (S := ℚ) (nonZeroDivisors ℤ)
  have hbf : Flat g := by
    rw [hg, Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat ℚ (nonZeroDivisors ℤ))
  have h1 : IsPreimmersion (pullback.fst f g) :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) (IsPullback.of_hasPullback _ _).flip hb

  let x : Sp ℚ ⟶ GlobalTheory.FlagZ.Fl ι N := GlobalTheory.FlagZ.flagPt Prod.fst Prod.snd (fun _ => (1 : GL (Fin N) ℚ))
  have hx : x ≫ f = g := GlobalTheory.FlagZ.toZ_ext _ _
  let s : Sp ℚ ⟶ pullback f g := pullback.lift x (𝟙 _) (by rw [hx, Category.id_comp])

  let ξ := genericPoint (GlobalTheory.FlagZ.Fl ι N)
  let y : Sp ℚ := IsLocalRing.closedPoint ℚ
  have hξ : f ξ ∈ Set.range g := by
    have h0 : ξ ⤳ x y := (genericPoint_spec (GlobalTheory.FlagZ.Fl ι N)).specializes (Set.mem_univ _)
    have h2 : f ξ ⤳ g y := by
      have := h0.map f.continuous
      rwa [← Scheme.Hom.comp_apply, hx] at this
    obtain ⟨z, -, hz⟩ := Flat.generalizingMap g h2
    exact ⟨z, hz⟩
  have hS : _root_.IsPreconnected (Set.range (pullback.fst f g)) := by
    rw [Scheme.Pullback.range_fst]
    refine (IsIrreducible.isConnected (isIrreducible_iff_closure.1 ?_)).isPreconnected
    have : closure (f ⁻¹' Set.range g) = Set.univ :=
      have hcl : closure ({ξ} : Set (GlobalTheory.FlagZ.Fl ι N)) = Set.univ := genericPoint_spec (GlobalTheory.FlagZ.Fl ι N)
      Set.eq_univ_of_univ_subset (hcl ▸ closure_mono (Set.singleton_subset_iff.2 hξ))
    rw [this]
    exact IrreducibleSpace.isIrreducible_univ _
  have hC : ConnectedSpace ↥(Limits.pullback f g) := by
    have hp : PreconnectedSpace ↥(Limits.pullback f g) := ⟨by
      rw [← (pullback.fst f g).isEmbedding.isInducing.isPreconnected_image, Set.image_univ]
      exact hS⟩
    exact { toPreconnectedSpace := hp, toNonempty := ⟨s y⟩ }
  exact GlobalTheory.RatPointConn.geometricallyConnected_of_ratPoint ℚ (Over.mk (pullback.snd f g))
    (inferInstanceAs (LocallyOfFiniteType (pullback.snd f g)))
    (inferInstanceAs (QuasiCompact (pullback.snd f g))) hC ⟨Over.homMk s (pullback.lift_snd _ _ _)⟩

end GlobalTheory.FlagQ
