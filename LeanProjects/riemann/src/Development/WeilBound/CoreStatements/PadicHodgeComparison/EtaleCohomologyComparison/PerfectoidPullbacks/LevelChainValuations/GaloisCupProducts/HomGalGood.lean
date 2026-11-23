import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.GaloisCupProducts.HomGalGoodRHof
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.GaloisCupProducts.NmHONmPullBBMap
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.TwistAcrisZeroPreservesFiltration

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section

set_option maxHeartbeats 1000000

open CategoryTheory AlgebraicGeometry Limits GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Kap

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

section
variable {m : ℕ} {L : Lev (per l K) m} (hL : L.Good) (g : K.fixingSubgroup) (M : Model l K)

namespace GaloisEquivariantMaps

open LevelPullbackIdentities in

def etaGal (s : ℕ) (hQ : ∀ T, QB L M s T → QA L M s (((nmB M hL).mor 0).obj T)) :
    (nmS (nmGB hL g M) 1 s).o.G ⋙ (smB M s hL hQ).o.G ⟶ (smB M s hL hQ).o.G ⋙ (nmS (nmGA hL g M) l s).o.G where
  app T := ObjectProperty.homMk (mkH (RingHom.id T.obj.B) (fun r => congrArg T.obj.i (hL.σ_ι g r).symm)
    (DPMorphism.id T.obj.δ).isDPMorphism (fun _ h => h)
    (Subtype.ext (Prod.ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun a =>
      (qid _ (fun _ h => h) _).trans (congrArg (fun b => T.obj.y.1.1 (Ideal.Quotient.mk _ b)) (hL.σ_ι g a).symm)))
      ((spec_qid _ (fun _ h => h) _).trans (by
        show ((T.obj.y.1.2 ≫ 𝟙 M.gen) ≫ pullback.fst _ _ : _ ⟶ M.X) = (T.obj.y.1.2 ≫ pullback.fst _ _) ≫ 𝟙 M.X
        simp)))))
  naturality _ _ f := ObjectProperty.hom_ext _ (CrystallineSemistableComparison.Pb.hom_ext rfl)

end GaloisEquivariantMaps

theorem nmHO_nmGB_bMap (s : ℕ) (hQ : ∀ T, QB L M s T → QA L M s (((nmB M hL).mor 0).obj T)) (j : ℕ) (z : HO (QA L M s) j) :
    nmHO (nmGB hL g M) 1 s j (bMap M s hL hQ j z) = bMap M s hL hQ j (nmHO (nmGA hL g M) l s j z) := by
  have i1 : RingHomCompTriple L.ι (L.σB g) ((L.σB g).comp L.ι) := ⟨rfl⟩
  have i2 : RingHomCompTriple (L.σA g) L.ι ((L.σB g).comp L.ι) := ⟨RingHom.ext fun a => hL.σ_ι g a⟩
  have e₁ := CrystallineSemistableComparison.pull_pull ((L.σB g).comp L.ι) (smB M s hL hQ).o (nmS (nmGB hL g M) 1 s).o j z
  have e₂ := CrystallineSemistableComparison.pull_pull ((L.σB g).comp L.ι) (nmS (nmGA hL g M) l s).o (smB M s hL hQ).o j z
  exact e₁.trans ((CrystallineSemistableComparison.P.prism ((smB M s hL hQ).o.comp (σ'' := (L.σB g).comp L.ι) (nmS (nmGB hL g M) 1 s).o)
    ((nmS (nmGA hL g M) l s).o.comp (σ'' := (L.σB g).comp L.ι) (smB M s hL hQ).o)
    (GaloisEquivariantMaps.etaGal hL g M s hQ) (fun T x => rfl) j z).trans e₂.symm)

variable (s : ℕ) (hQ : ∀ T, QB L M s T → QA L M s (((nmB M hL).mor 0).obj T))
  (rH : ∀ n j, M.Hc false n j →ₛₗ[L.lam] HM (QA L M s) none ((l : L.A) ^ n) j)

theorem homGal_good_of_galRed (hr : GalRed hL g M s rH) : (homGal hL g M s hQ rH).Good where
  ℓ := rfl
  lam c := hL.σ_lam g c
  ι a := (hL.σ_ι g a).symm
  o k := hL.σB_K g k
  tS n j x := ((M.galH false j (IntermediateField.fixingSubgroupEquiv K g)).comm n x).symm
  r n j x := hr n j x
  red n j z := nmHM_redM _ l s none n j z
  b j z := nmHO_nmGB_bMap hL g M s hQ j z
  μ j v := (nm_muB (nmGB hL g M) (Category.id_comp _) 1 s (hL.σB_K g) j v).trans (congrArg _ (pullR_id' M.q j v))

end

section
variable {m : ℕ} {L : Lev (per l K) m}
  (d : ∀ n, RedIn (B.DD false (PAlg.base l) n) (B.κb (okToOC l K) false n) L.γ l n)
  (hc : ∀ n (c : Acris l), (d n).ρ ((PAlg.base l).cris n c) = Ideal.Quotient.mk _ (L.lam c))

theorem galRed_rHof (hL : L.Good) (g : K.fixingSubgroup) (M : Model l K) (s : ℕ) : GalRed hL g M s (rHof d hc M s) := by
  intro n j x
  exact (red_nm (d n) (d n) s (nmGA hL g M) _ _ _ _ _ (hc n) (hc n) _ _ (fun _ _ => (Category.comp_id _).symm)
    (by
      intro y
      obtain ⟨c, rfl⟩ := ((RL.base_acr (PAlg.base l) PAlg.isBase_base).2 n).1 y
      rw [PAlg.galBase_cris, hc, hc]
      exact (congrArg (Ideal.Quotient.mk _) (hL.σ_lam g c)).symm) none j x).symm

end

end CrystallineSemistableComparison.Pb.Kap
