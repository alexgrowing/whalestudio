import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.Final
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.PhiHIterSmul
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.PhiAIter
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.EqZeroOfCoord
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.EPin
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.GalAwayCongr
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.PullbackFinRelation
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernUnique
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PAffFin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison UpperTheory.Ru.crystallineComparison

private theorem UpperTheory.Ru.crystallineComparison.quasiCompact_of_proj {R : Type} [CommRing R] {X : Scheme.{0}}
    {f : X ⟶ Spec (CommRingCat.of R)} (h : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver f) : QuasiCompact f := by
  refine Exists.elim h fun N hN => Exists.elim hN fun i hi => ?_
  have : IsProper (ReciprocityTheory.ChartRestriction.G.Geo.Tor.PSpace.str R N) := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str R N
  have : IsClosedImmersion i := hi.1
  rw [← hi.2]
  infer_instance

theorem UpperTheory.Ru.crystallineComparison.final :
    UpperTheory.Ru.crystallineComparison.Final := by
  unfold UpperTheory.Ru.crystallineComparison.Final
  intro l _ K _ _ _ r f hf hx hC ϖ hϖ M hM n j T hr hPt A hA B₀
  obtain ⟨Amp, N, F, hFacts, hEt, hLaws, ⟨bm⟩, ⟨pm⟩, hfN, hTeich, hall⟩ := hC
  refine Exists.elim (CrystallineSemistableComparison.E.etMap l K) fun e he => ?_
  refine Exists.elim (UpperTheory.Ru.crystallineComparison.ePin l K Model.Sm Amp e he) fun e' hcomp => ?_
  refine Exists.elim (UpperTheory.Ru.crystallineComparison.pbIota l K B₀) fun ι hι' => ?_
  have hInj : InjE B₀ e M j :=
    UpperTheory.Ru.crystallineComparison.injOf l K B₀ ι hι'.1 hι'.2.1 hι'.2.2.1 Model.Sm Amp hFacts hEt hLaws e e' bm pm hcomp M hM j
  have hAbs : AbsInv B₀ e M j f ϖ :=
    UpperTheory.Ru.crystallineComparison.absInvOf l K r B₀ (UpperTheory.Ru.crystallineComparison.pbInv l K B₀ r) e he M hM f N j hx hfN hTeich F
      (hall M hM j).1 (hall M hM j).2 ϖ hϖ.not_isUnit
  have hP : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver M.p := hM.1.1
  have hSm : Smooth M.p := hM.2
  have hQC : QuasiCompact M.p := UpperTheory.Ru.crystallineComparison.quasiCompact_of_proj hP
  have hAff : UpperTheory.Gal.crystallineComparison.AffFin M.X := UpperTheory.Gal.crystallineComparison.affFin_of (OK l K) M.X M.p hP
  exact UpperTheory.Ru.crystallineComparison.top l K ϖ hϖ e he M hSm hQC hAff f n j hf T hr hPt A hA B₀ hInj hAbs
