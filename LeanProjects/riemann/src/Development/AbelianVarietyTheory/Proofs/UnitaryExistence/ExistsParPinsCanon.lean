import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.ValSetAlgSubset
import Formalism.LocalToGlobal.ProjectiveLattices.IntAll
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.VolProofs
import Formalism.LocalToGlobal.ProjectiveLattices.LevelPb
import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModuliSchemePolarizedAbelianLevel
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

noncomputable section

namespace GlobalTheory.Member.ParExist

theorem datLaws_all (D : D7) : ∀ j, InR D j → ∃ hI : DatInt D j, DatLaws D j hI :=
  fun j hj => ⟨datInt_holds D j,
    { unimod := efW_unimod_holds D j _, rank := latW_rank D j hj, dom := datDom_holds D j hj _ }⟩

def parAtLevel (D : D7) (hF : OFull D) (hz : OZeta D) (hN : N1ab) (l : Level (hostOfRecord D))
    (hl : l.M = D.host.g 0 * D.host.g 1 ∧ l.A = 1) : Par D where
  H := hostOfRecord D
  l := l
  c :=
    { F := FO D
      fin := inferInstance
      conj := fun τ a => conj_mem_FO D τ a
      zeta_mem := by
        have h := (coeffFieldOfRecord D (hU := unramBridge D.host.E (cmUnram_conj D)) hz).zeta_mem
        have h1 : (levelG D (hU := unramBridge D.host.E (cmUnram_conj D))).M' = l.M' := by
          simp [Level.M', levelG, levelOfPs, hl.1, hl.2]
        rw [h1] at h
        exact h
      le := by
        have h := (coeffFieldOfRecord D (hU := unramBridge D.host.E (cmUnram_conj D)) hz).le
        have h1 : KA l = KA (levelG D (hU := unramBridge D.host.E (cmUnram_conj D))) := by
          unfold KA
          rw [hl.2]
          rfl
        rw [h1]
        exact h }
  Dw := datumAtLift D _ (datLaws_all D)
  Xo := fun j => Classical.choice (hN D.host.E _ (datumAtLift D _ (datLaws_all D) j) l (datumAtLift_pq_pos D _ (datLaws_all D) j))
  eO := eOf D hF

theorem exists_par_pins_canon (D : D7) (hF : OFull D) (hz : OZeta D)
    (pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K))
    (hg : ∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (pb k).asIdeal) :
    ∃ Q : Par D, Q.Pins ∧ Q.Canon ∧ (∀ j, 1 ≤ (Q.Dw j).p + (Q.Dw j).q) ∧
      Q.l.Mb = ∏ k, (pb k).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) := by
  obtain ⟨l, hl, hb⟩ := levelPb_exists D pb hg
  refine ⟨parAtLevel D hF hz GlobalTheory.Moduli.moduli_scheme_exists l hl, ?_, ⟨rfl, fun j hj => ?_⟩, fun j => datumAtLift_pq_pos D _ (datLaws_all D) j, hb⟩
  · refine ⟨⟨rfl, rfl, rfl, tauEmb_sqrt D⟩, hl, eOf_spec D hF, fun j hj => ?_⟩
    show IsDatW D j (datumAtLift D _ (datLaws_all D) j)
    unfold datumAtLift
    rw [dif_pos hj]
    exact isDatW_datumOf D _ j _ _
  · show ∃ hP hd, HEq (datumAtLift D _ (datLaws_all D) j) (datumOfRecord D j hj hP hd)
    unfold datumAtLift
    rw [dif_pos hj]
    exact ⟨Formalism.IndefR.Fin.factPrincipalDatum, datDom_holds D j hj _, HEq.rfl⟩

end GlobalTheory.Member.ParExist
