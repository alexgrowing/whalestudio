import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirVolumeRatios.VolumeClassRepresentatives.ZsCovFin
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirVolumeRatios.VolumeClassRepresentatives.ZsCovInf

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta

namespace Formalism.L2.S.S7.ZsCovMeas

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D} (fr : Formalism.IndefR.Eqv.UI.Frames D V)

def cdProd : ENNReal := ∏ v, (D.s.cdScale V.rank (fr.ε v) : ENNReal)

def muV (μf : Measure (Formalism.IndefR.Eqv.UI.instV fr).Gf) [SigmaFinite μf] : Measure (GA D V) :=
  cdProd fr • ((Formalism.IndefR.Eqv.UI.instV fr).muA μf).map (Formalism.IndefR.Eqv.UI.brg fr)

theorem isHaar_muV (hc0 : ∀ v, D.s.cdScale V.rank (fr.ε v) ≠ 0)
    (μf : Measure (Formalism.IndefR.Eqv.UI.instV fr).Gf) [μf.IsHaarMeasure] [SigmaFinite μf] :
    (muV fr μf).IsHaarMeasure := by
  obtain ⟨k1, k2, k3, k4, k5⟩ := Formalism.IndefR.Eqv.ga_facts D V
  have hμi : (Measure.pi fun v => Formalism.REAL.muG ((Formalism.IndefR.Eqv.UI.instV fr).ε v)).IsHaarMeasure :=
    Measure.pi.isHaarMeasure _
  have hμA : ((Formalism.IndefR.Eqv.UI.instV fr).muA μf).IsHaarMeasure := Measure.prod.instIsHaarMeasure _ _
  have hmapH : (((Formalism.IndefR.Eqv.UI.instV fr).muA μf).map (Formalism.IndefR.Eqv.UI.brg fr)).IsHaarMeasure :=
    (Formalism.IndefR.Eqv.UI.brg fr).toMulEquiv.isHaarMeasure_map _ (Formalism.IndefR.Eqv.UI.brg fr).continuous
      (Formalism.IndefR.Eqv.UI.brg fr).symm.continuous
  have hc0' : cdProd fr ≠ 0 := Finset.prod_ne_zero_iff.2 fun v _ => by simpa using hc0 v
  have hct : cdProd fr ≠ ⊤ := ENNReal.prod_ne_top fun v _ => ENNReal.coe_ne_top
  exact Measure.IsHaarMeasure.smul _ hc0' hct

theorem isVolMeas_muV (hcd : cdScaleTie D) (hΛ : fr.Λ = Formalism.IndefR.Eqv.UI.Lv D V) {P Q : ℕ}
    (e : ∀ v, Fin P ⊕ Fin Q ≃ Fin V.rank) (h1 : ∀ v i, fr.ε v (e v (Sum.inl i)) = true)
    (h2 : ∀ v j, fr.ε v (e v (Sum.inr j)) = false) (hc0 : ∀ v, D.s.cdScale V.rank (fr.ε v) ≠ 0)
    (μf : Measure (Formalism.IndefR.Eqv.UI.instV fr).Gf) [μf.IsHaarMeasure] [SigmaFinite μf]
    (hK : μf (Formalism.IndefR.Eqv.UI.instV fr).Kset = 1) :
    IsVolMeas D V P Q (muV fr μf) := by
  obtain ⟨k1, k2, k3, k4, k5⟩ := Formalism.IndefR.Eqv.ga_facts D V
  refine ⟨isHaar_muV fr hc0 μf, ?_⟩
  refine ⟨⟨Formalism.IndefR.Eqv.thetaC D, Formalism.IndefR.Eqv.isInfFam_thetaC D⟩, fun θ hθ => ?_⟩
  rw [Formalism.IndefR.Eqv.eq_thetaC D hθ]
  refine ⟨⟨fun ρ => ((fr.P (Formalism.L2.Host.tauPl D ρ))⁻¹).submatrix (e (Formalism.L2.Host.tauPl D ρ)) id, fun ρ => ?_⟩,
    fun A hA => ?_⟩
  · set v := Formalism.L2.Host.tauPl D ρ with hv
    have h := Formalism.IndefR.Eqv.MF.sq_gram (e v).symm (((fr.P v)⁻¹).submatrix (e v) id)
    rw [ZsCovInf.signs_eq (e v) (h1 v) (h2 v)] at h
    have hsub : (((fr.P v)⁻¹).submatrix (e v) id).submatrix (e v).symm id = (fr.P v)⁻¹ := by
      ext i j; simp
    rw [hsub] at h
    rw [← h]
    have h' := Formalism.IndefR.Eqv.MF.inv_frame (Formalism.IndefR.Eqv.P_isUnit_det fr v) (fr.spec v)
    rw [h']
    simp only [hv, Formalism.IndefR.Eqv.UI.phiV, Equiv.symm_apply_apply]
    rfl
  intro B hB
  set c : ∀ v, Formalism.REAL.UJ (fr.ε v) := fun v =>
    ZsCovInf.cEl fr v (hA ((Formalism.L2.Host.tauPl D).symm v)) (e v) (h1 v) (h2 v) with hcdef
  let S' : ∀ v : InfinitePlace D.host.F, Set (Formalism.REAL.UJ (fr.ε v)) := fun v =>
    (fun g : Formalism.REAL.UJ (fr.ε v) => c v * g * (c v)⁻¹) ⁻¹'
      (PI.UnitaryGroupMassFormula.CdHaarScale.Main.phi (e v) (h1 v) (h2 v) '' B ((Formalism.L2.Host.tauPl D).symm v))
  have hpre : (Formalism.IndefR.Eqv.UI.brg fr) ⁻¹' {h : GA D V | (∀ y, y ∈ latHat D.host.F D.host.E (L0c D V) ↔
        (finMat D.sp.cm.sig V.gram h).mulVec y ∈ latHat D.host.F D.host.E (L0c D V)) ∧
      ∀ ρ, ∃ b ∈ B ρ, UpqT.mat b * A ρ = A ρ * infMat D.sp.cm.sig V.gram (Formalism.IndefR.Eqv.thetaC D ρ) h} =
      ((Set.univ.pi S' : Set (∀ v : InfinitePlace D.host.F, Formalism.REAL.UJ (fr.ε v))) :
        Set (Formalism.IndefR.Eqv.UI.instV fr).Ginf) ×ˢ (Formalism.IndefR.Eqv.UI.instV fr).Kset := by
    ext x
    show (_ ∧ _) ↔ (_ ∧ _)
    refine (and_congr (ZsCovFin.finCond_brg fr hΛ x) Iff.rfl).trans (and_comm.trans (and_congr ?_ Iff.rfl))
    constructor
    · intro h v _
      exact (ZsCovInf.infCond fr v (hA ((Formalism.L2.Host.tauPl D).symm v)) (e v) (h1 v) (h2 v) x _).1
        (h ((Formalism.L2.Host.tauPl D).symm v))
    · intro h ρ
      have := (ZsCovInf.infCond fr (Formalism.L2.Host.tauPl D ρ) (hA ((Formalism.L2.Host.tauPl D).symm (Formalism.L2.Host.tauPl D ρ)))
        (e _) (h1 _) (h2 _) x _).2 (h (Formalism.L2.Host.tauPl D ρ) (Set.mem_univ _))
      rw [Equiv.symm_apply_apply] at this
      exact this
  have hmap := (Formalism.IndefR.Eqv.UI.brg fr).toHomeomorph.toMeasurableEquiv.map_apply
    (μ := (Formalism.IndefR.Eqv.UI.instV fr).muA μf) {h : GA D V | (∀ y, y ∈ latHat D.host.F D.host.E (L0c D V) ↔
        (finMat D.sp.cm.sig V.gram h).mulVec y ∈ latHat D.host.F D.host.E (L0c D V)) ∧
      ∀ ρ, ∃ b ∈ B ρ, UpqT.mat b * A ρ = A ρ * infMat D.sp.cm.sig V.gram (Formalism.IndefR.Eqv.thetaC D ρ) h}
  have hmeas : muV fr μf {h : GA D V | (∀ y, y ∈ latHat D.host.F D.host.E (L0c D V) ↔
        (finMat D.sp.cm.sig V.gram h).mulVec y ∈ latHat D.host.F D.host.E (L0c D V)) ∧
      ∀ ρ, ∃ b ∈ B ρ, UpqT.mat b * A ρ = A ρ * infMat D.sp.cm.sig V.gram (Formalism.IndefR.Eqv.thetaC D ρ) h} =
      cdProd fr * ((∏ v : InfinitePlace D.host.F, Formalism.REAL.muG (fr.ε v) (S' v)) *
        μf (Formalism.IndefR.Eqv.UI.instV fr).Kset) := by
    rw [muV, Measure.smul_apply, smul_eq_mul]
    congr 1
    refine (hmap.trans (congrArg _ hpre)).trans ?_
    exact (Measure.prod_prod _ _).trans (congrArg (· * μf (Formalism.IndefR.Eqv.UI.instV fr).Kset) (Measure.pi_pi _ _))
  rw [hmeas, hK, mul_one, cdProd, ← Finset.prod_mul_distrib]
  have hv : ∀ v, (D.s.cdScale V.rank (fr.ε v) : ENNReal) * Formalism.REAL.muG (fr.ε v) (S' v) =
      D.cd.cd P Q (B ((Formalism.L2.Host.tauPl D).symm v)) := fun v => by
    rw [← ZsCovInf.measAt hcd (e v) (h1 v) (h2 v) (c v) _ (hB _), Measure.smul_apply, smul_eq_mul]
  calc _ = ∏ v, D.cd.cd P Q (B ((Formalism.L2.Host.tauPl D).symm v)) := Finset.prod_congr rfl fun v _ => hv v
    _ = _ := Fintype.prod_equiv (Formalism.L2.Host.tauPl D).symm _ _ fun v => rfl

end Formalism.L2.S.S7.ZsCovMeas
