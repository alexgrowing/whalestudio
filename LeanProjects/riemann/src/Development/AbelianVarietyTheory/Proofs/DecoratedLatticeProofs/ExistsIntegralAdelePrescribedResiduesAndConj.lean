import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagLevelCharacterEqPsiDivN
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsTransportAdelicCorrection
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV Formalism.L2.SG.InstExistsPf GlobalTheory.FlagBasis
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ConjResidueSurj
open GlobalTheory.IdemSupport

theorem sigInt_oToS {D : D7} (a : 𝓞 D.host.E) :
    sigInt (instOf D) (oToS D.host.F D.host.E a) = oToS D.host.F D.host.E (cO D a) :=
  Subtype.ext (Formalism.L2.SG.Pf.unitaryCongruence.sigA_inclE (instOf D) (a : D.host.E))

theorem exists_res_and_conj (D : D7) (Pg : Finset (Pl D.host.E))
    (h : ∀ PP ∈ Pg, ∀ PP' ∈ Pg, ¬ Formalism.IndefR.Lev.IsConjPl (D := D) PP PP')
    (u u' : ∀ PP : Pl D.host.E, kP PP) :
    ∃ s : Formalism.L2.Herm.intAf D.host.F D.host.E, ∀ PP ∈ Pg,
      resS D.host.F PP s = u PP ∧ resS D.host.F PP (sigInt (instOf D) s) = u' PP := by
  classical
  choose a ha using fun PP : Pl D.host.E => Ideal.Quotient.mk_surjective (I := PP.asIdeal) (u PP)
  choose a' ha' using fun PP : Pl D.host.E => Ideal.Quotient.mk_surjective (I := PP.asIdeal) (u' PP)
  have hout : ∀ PP ∈ Pg, cP PP ∉ Pg := fun PP hPP h' =>
    h PP hPP _ h' ((isConjPl_iff _ _).2 rfl)
  let T : Finset (Pl D.host.E) := Pg ∪ Pg.image cP
  let x : Pl D.host.E → 𝓞 D.host.E := fun Q => if Q ∈ Pg then a Q else cO D (a' (cP Q))
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := T)
    (fun Q : Pl D.host.E => Q.asIdeal) (fun _ => 1) (fun Q _ => Q.prime)
    (fun Q _ Q' _ hne e => hne (HeightOneSpectrum.ext e)) (fun Q => x Q.1)
  refine ⟨oToS D.host.F D.host.E y, fun PP hPP => ⟨?_, ?_⟩⟩
  · have h1 := hy PP (Finset.mem_union_left _ hPP)
    rw [pow_one] at h1
    have h2 : x PP = a PP := if_pos hPP
    rw [resS_oToS, ← ha PP, ← h2]
    exact Ideal.Quotient.eq.2 h1
  · have h1 := hy (cP PP) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hPP))
    rw [pow_one] at h1
    have h2 : x (cP PP) = cO D (a' PP) := by
      have : x (cP PP) = cO D (a' (cP (cP PP))) := if_neg (hout PP hPP)
      rw [this, GlobalTheory.StdFrames.cP_cP]
    have h3 : y - cO D (a' PP) ∈ (cP PP).asIdeal := h2 ▸ h1
    rw [mem_cP, map_sub, cO_cO] at h3
    rw [sigInt_oToS, resS_oToS, ← ha' PP]
    exact Ideal.Quotient.eq.2 h3

end GlobalTheory.ConjResidueSurj
