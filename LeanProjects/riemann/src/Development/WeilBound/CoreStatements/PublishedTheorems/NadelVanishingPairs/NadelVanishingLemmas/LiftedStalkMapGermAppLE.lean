import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLifted
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ModPSquaredStalkSurjective
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.EtaleCoordinatesFlatLiftStatement
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.LocalRingImageStalkMap
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsFrobeniusLiftStalk
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SncChartEquationsDifferUnit
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.FrobeniusLiftUnitTimesCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogLiftPpZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogLiftOfUnitMemMap

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.DI

theorem lifted_stalkMap_germ_appLE {Y Z : Scheme.{0}} (f : Z ⟶ Y) (W : Y.Opens) (W' : Z.Opens)
    (h : W' ≤ f ⁻¹ᵁ W) (z : Z) (hz : z ∈ W') (s : Γ(Y, W)) :
    (f.stalkMap z).hom ((Y.presheaf.germ W (f z) (h hz)).hom s) =
      (Z.presheaf.germ W' z hz).hom ((f.appLE W W' h).hom s) := by
  have h1 := Scheme.Hom.germ_stalkMap_apply f W z (h hz) s
  have h2 := TopCat.Presheaf.germ_res_apply Z.presheaf (homOfLE h) z hz ((f.app W).hom s)
  exact h1.trans h2.symm

theorem isLifted_of_sncCharts : ∀ (p : ℕ) [Fact p.Prime] (Y X : Scheme.{0}) [IsIntegral X] (g : Y ⟶ Sp (ZMod (p ^ 2))) (f : X ⟶ Sp (ZMod p)) (π : X ⟶ Y), IsPullback π f g (spMap (ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p))) → ∀ {n s : ℕ} (L : Fin s → LB Y) (σ : ∀ i, (L i).Sec), (∀ i, (L i).IsLB) → ∀ {ι : Type} [Nonempty ι] (C : ι → SncChart g n L σ) (Z : Set X) (U : ι → X.Opens) (hU : ∀ i, U i ≤ π ⁻¹ᵁ (C i).U) (hgen : ∀ i, genericPoint X ∈ U i) (x : ι → Fin n → X.functionFieldˣ) (J : ι → Finset (Fin n)), (∀ i l, (x i l : X.functionField) = fnOf (U i) (hgen i) ((π.appLE (C i).U (U i) (hU i)).hom ((C i).t l))) → (∀ i l, l ∈ J i → ∃ c, (C i).e c = some l) → (∀ i, IsLogChart Z (U i) (x i) (J i)) → IsLifted p Z U x := by
  intro p _ Y X _ q f π hpb n s L σ hL ι _ C Z U hU hgen x J hx hJ hchart
  obtain ⟨i₁⟩ := ‹Nonempty ι›
  have hη : ∀ i, π (genericPoint X) ∈ (C i).U := fun i => hU i (hgen i)
  let πK : Y.presheaf.stalk (π (genericPoint X)) →+* X.functionField := (π.stalkMap (genericPoint X)).hom
  have hflat : IsFlatLift p πK :=
    GlobalTheory.T.etale_coordinates_flat_lift p Y X q f π hpb (C i₁).U (C i₁).t (C i₁).affine (C i₁).etale (genericPoint X) (hη i₁)
  have hpK : (p : X.functionField) = 0 := by
    have h0 := (hflat.ker (p : Y.presheaf.stalk (π (genericPoint X)))).2 ⟨1, by ring⟩
    simpa using h0
  haveI : CharP X.functionField p := (CharP.charP_iff_prime_eq_zero Fact.out).2 hpK
  have hpp := logLift_pp_zero p πK hflat
  choose F hF1 hF2 hF3 using fun i =>
    GlobalTheory.T.exists_frobenius_lift_stalk p q (C i).U (C i).t (C i).affine (C i).etale (π (genericPoint X)) (hη i)

  have hlift : ∀ i l, πK ((Y.presheaf.germ (C i).U (π (genericPoint X)) (hη i)).hom ((C i).t l)) =
      (x i l : X.functionField) := by
    intro i l
    rw [hx i l]
    exact lifted_stalkMap_germ_appLE π (C i).U (U i) (hU i) (genericPoint X) (hgen i) ((C i).t l)
  refine ⟨Y.presheaf.stalk (π (genericPoint X)), inferInstance, πK, F, hflat, ?_, ?_, ?_⟩
  · intro i z
    obtain ⟨w, hw⟩ := hF1 i z
    rw [hw, map_add, map_pow, map_mul, map_natCast, hpK, zero_mul, add_zero]
  · intro i l
    exact ⟨_, hlift i l, hF2 i l⟩
  intro y t hyt a ha
  rcases t.eq_empty_or_nonempty with rfl | ⟨i₀, hi₀⟩
  · obtain ⟨z, hz⟩ := hflat.surj (a : X.functionField)
    exact ⟨z, hz, fun i hi => absurd hi (Finset.notMem_empty i)⟩
  have hsp : π (genericPoint X) ⤳ π y :=
    ((genericPoint_spec X).specializes (Set.mem_univ y)).map π.continuous
  have hsurj := (GlobalTheory.T.mod_p_squared_stalk_surjective p Y X q f π hpb y).1
  have hloc := GlobalTheory.T.local_ring_image_stalk_map π y hsp hsurj
  set At := stalkIm hsp with hAt
  have hmap : (locRing y : Set X.functionField) = (At.map πK : Set X.functionField) := by
    ext c
    rw [SetLike.mem_coe, hloc, SetLike.mem_coe, Subring.mem_map]
  have hstab : ∀ i ∈ t, ∀ z ∈ At, ∃ w ∈ At, F i z = z ^ p + p * w :=
    fun i hi z hz => hF3 i (π y) (hU i (hyt i hi)) hsp z hz
  obtain ⟨u, m, hu, rfl⟩ := ((hchart i₀).logUnit y (hyt i₀ hi₀) a).1 ha
  rw [hmap]

  have hu0 : (u : X.functionField) ≠ 0 := u.ne_zero
  have hU1 : LogLift p πK F t (At.map πK : Set X.functionField) (u : X.functionField) := by
    have h2 := (unitAt_iff hu0).1 hu
    refine logLift_of_unit_mem_map p πK F t At hflat hstab _ hu0 ?_ ?_
    · exact Subring.mem_map.2 ((hloc _).1 h2.1)
    · exact Subring.mem_map.2 ((hloc _).1 h2.2)

  have hcoord : ∀ j ∈ J i₀, LogLift p πK F t (At.map πK : Set X.functionField) (x i₀ j : X.functionField) := by
    intro j hj
    obtain ⟨c, hc⟩ := hJ i₀ j hj
    refine ⟨_, hlift i₀ j, fun i hi => ?_⟩
    obtain ⟨v, hv⟩ := GlobalTheory.T.snc_chart_equations_differ_unit q L σ hL (C i₀) (C i) (π y) (hU i₀ (hyt i₀ hi₀)) (hU i (hyt i hi)) c
    rw [hc] at hv
    change (Y.presheaf.germ (C i₀).U (π y) (hU i₀ (hyt i₀ hi₀))).hom ((C i₀).t j) = _ at hv
    have hv' := congrArg (Y.presheaf.stalkSpecializes hsp).hom hv
    have e1 : ∀ (V : Y.Opens) (hV : π y ∈ V) (r : Γ(Y, V)),
        (Y.presheaf.stalkSpecializes hsp).hom ((Y.presheaf.germ V (π y) hV).hom r) =
          (Y.presheaf.germ V (π (genericPoint X)) (hsp.mem_open V.isOpen hV)).hom r :=
      fun V hV r => TopCat.Presheaf.germ_stalkSpecializes_apply Y.presheaf hV hsp r
    rw [map_mul] at hv'
    have hv2 : (Y.presheaf.germ (C i₀).U (π (genericPoint X)) (hη i₀)).hom ((C i₀).t j) =
        (Y.presheaf.stalkSpecializes hsp).hom (v : Y.presheaf.stalk (π y)) *
          (Y.presheaf.germ (C i).U (π (genericPoint X)) (hη i)).hom (((C i).e c).elim 1 (C i).t) := by
      refine (e1 _ _ _).symm.trans (hv'.trans ?_)
      congr 1
      exact e1 _ _ _
    set sv := (Y.presheaf.stalkSpecializes hsp).hom (v : Y.presheaf.stalk (π y)) with hsv
    set sv' := (Y.presheaf.stalkSpecializes hsp).hom ((v⁻¹ : (Y.presheaf.stalk (π y))ˣ) :
      Y.presheaf.stalk (π y)) with hsv'
    have hsvA : sv ∈ At := ⟨_, rfl⟩
    have hsv'A : sv' ∈ At := ⟨_, rfl⟩
    have hvv : sv * sv' = 1 := by rw [hsv, hsv', ← map_mul, Units.mul_inv, map_one]
    have hkey : ∀ o : Option (Fin n),
        F i ((Y.presheaf.germ (C i).U (π (genericPoint X)) (hη i)).hom (o.elim 1 (C i).t)) =
          ((Y.presheaf.germ (C i).U (π (genericPoint X)) (hη i)).hom (o.elim 1 (C i).t)) ^ p := by
      rintro (_ | l)
      · show F i ((Y.presheaf.germ (C i).U (π (genericPoint X)) (hη i)).hom 1) = _
        simp
      · exact hF2 i l
    obtain ⟨w, hwA, hw⟩ := GlobalTheory.T.frobenius_lift_unit_times_coord p At (F i) sv sv' _ hpp hsv'A hvv (hstab i hi sv hsvA) (hkey ((C i).e c))
    refine ⟨w, Subring.mem_map.2 ⟨w, hwA, rfl⟩, ?_⟩
    rw [hv2]
    exact hw
  rw [Units.val_mul, Units.coe_prod]
  refine logLift_mul p πK F t _ hflat hU1 ?_
  refine Finset.prod_induction _ (LogLift p πK F t (At.map πK : Set X.functionField))
    (fun _ _ => logLift_mul p πK F t _ hflat) (logLift_one p πK F t _) (fun j hj => ?_)
  rw [Units.val_zpow_eq_zpow_val]
  exact logLift_zpow p πK F t _ hflat (x i₀ j).ne_zero (hcoord j hj) (m j)

end GlobalTheory.DI
