import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.PatchOneAlt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CrystallineAllOfGood
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RealGal
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.V.Af.Bc (res)
open UpperTheory.Gal.Int.Core

theorem UpperTheory.Gal.Int.Core.downCrys_holds :
    SphDown .crys := by
  intro E Ω _ _ _ _ _ _ l _ ι a π Q P hPc r w B hB hQ1 hyp
  have hAF := GlobalTheory.automorphicFormsFiniteGL
  intro Pr AI hT A hA O _ _ _ Bw hj σ hσ hsph
  have hdec := hQ1 A hA
  have hjK := GlobalTheory.RealGal.bridge_j_mem_Kw_of_dec_le E Ω Q.K l A O Bw hdec
  obtain ⟨Bw', e1, e2, e3⟩ := UpperTheory.V.Af.Cq.exBridge E Q.K Ω l A O Bw hjK
  have hj' : Induces Bw' := fun x => by rw [e2]; exact hj x
  obtain ⟨w', h', i, hi⟩ := GlobalTheory.PlaceIsoDec.exists_placeIso_of_dec_le_range E Ω Q.K w A hA hdec
  have hund : w'.under (𝓞 E) = w := by
    have := GlobalTheory.PlaceIsoDec.liesOver_of_isPlaceOver hA h'
    ext1
    exact this.over.symm
  obtain ⟨c, -, -, hq, -⟩ := GlobalTheory.WeilTransport.weil_equiv E Ω A w hA Q.K Ω A w' h' (RingEquiv.refl Ω) (algebraMap E Q.K) i hi
  have hB' : (CG.mk P).HasSat w' B := by
    have := hPc.sat w' 1 B (by rw [pow_one, hund, hq]) (by rw [hund]; exact hB)
    simpa using this
  obtain ⟨σ', hσ', -⟩ := GlobalTheory.CuspRep.LocEx.exists_isLocComp hAF Q.K a P w'
  obtain ⟨e, he⟩ := hPc.loc w w' i hi.cont hi.loc σ σ' hσ hσ'
  have hsph' := (GlobalTheory.CompletionIso.iwahori_spherical_transfer E Q.K w w' i hi.cont a σ σ' e he).2 hsph
  have hcr : ClauseAt .crys P ι (r.comp (UpperTheory.V.Af.Bc.res E Ω Q.K)) w' := hyp w' hund hB'
  exact (GlobalTheory.RealGal.dRSstCrysPstJumps_descend E Ω Q.K l Pr A O Bw Bw' e1 e2 e3 a r).2.2.1
    (hcr Pr AI hT A h' O Bw' hj' σ' hσ' hsph')
