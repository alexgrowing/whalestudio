import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPointsLieOverDistinctPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteAdeleProjectionIntegralReduction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartCharacterTrivialOnStandardPairStabilizer
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AfsplitB
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdForm

noncomputable section
namespace GlobalTheory.FinPl.SplitPhi
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem pr_e (p : SplitPt D k) : p.pr p.e = 1 := by
  have h := p.sec_pr 1
  rw [mul_one] at h
  rw [← h, p.pr_sec, map_one]

theorem prV_toEAf_e_ne (p : SplitPt D k) {w : HeightOneSpectrum (𝓞 D.host.F)} (hw : w ≠ p.v) :
    Formalism.UG.prV (E := D.host.E) w (toEAf D p.e) = 0 := by
  obtain ⟨ε, hε, he⟩ := p.above
  obtain ⟨h1, h2, -⟩ := p.split
  have : p.e = algebraMap (AF D.host.F) (AE D) ε * p.e := by
    rw [← he, add_mul, h1, mul_comm (cA D p.e), h2, add_zero]
  rw [this]
  exact GlobalTheory.AdForm.ChiStd.prV_toEAf_idem_mul hε hw _

theorem prV_toEAf_eps (p : SplitPt D k) {ε : AF D.host.F} (hε : IsPlaceIdem D p.v ε) :
    Formalism.UG.prV (E := D.host.E) p.v (toEAf D (algebraMap (AF D.host.F) (AE D) ε)) = 1 := by
  obtain ⟨α, rfl, h1, -⟩ := hε
  have h1' : (Formalism.UG.evalV D.host.F p.v) ((sndA D.host.F) (pairA D.host.F 0 α)) = 1 := h1
  rw [Algebra.TensorProduct.algebraMap_apply]
  simp [Formalism.IndefR.Datum.toEAf, finPart, Formalism.UG.prV]
  rw [h1']
  rfl

theorem prF_eq_zero (p : SplitPt D k) {PP : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt p.e PP)
    (y : EAf D) (hy : Formalism.UG.prV (E := D.host.E) p.v y = 0) : p.prF he y = 0 := by
  have h0 : toEAf D p.e * y = 0 := by
    refine Formalism.UG.P.afsplit_inj _ fun w => ?_
    rw [map_mul]
    by_cases hw : w = p.v
    · subst hw; rw [hy, mul_zero]
    · rw [prV_toEAf_e_ne p hw, zero_mul]
  have : p.prF he y = p.prF he (toEAf D p.e * y) := by
    rw [map_mul, p.prF_toEAf he, pr_e, one_mul]
  rw [this, h0, map_zero]

theorem prF_IE_prV (p : SplitPt D k) {PP : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt p.e PP)
    (y : EAf D) : p.prF he (Formalism.UG.P.afsplitIE p.v (Formalism.UG.prV (E := D.host.E) p.v y)) = p.prF he y := by
  rw [← sub_eq_zero, ← map_sub]
  apply prF_eq_zero p he
  rw [map_sub, Formalism.UG.P.afsplit_prV_IE, sub_self]

def phi (p : SplitPt D k) {PP : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt p.e PP) :
    D.host.E ⊗[D.host.F] p.v.adicCompletion D.host.F →+* k where
  toFun x := p.prF he (Formalism.UG.P.afsplitIE p.v x)
  map_one' := by
    have := prF_IE_prV p he 1
    rw [map_one (Formalism.UG.prV (E := D.host.E) p.v), map_one (p.prF he)] at this
    exact this
  map_mul' x y := by simp only [map_mul]
  map_zero' := by simp only [map_zero]
  map_add' x y := by simp only [map_add]

theorem phi_apply (p : SplitPt D k) {PP : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt p.e PP)
    (x : D.host.E ⊗[D.host.F] p.v.adicCompletion D.host.F) :
    phi p he x = p.prF he (Formalism.UG.P.afsplitIE p.v x) := rfl

theorem phi_prV (p : SplitPt D k) {PP : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt p.e PP)
    (a : AE D) : phi p he (Formalism.UG.prV (E := D.host.E) p.v (toEAf D a)) = p.pr a := by
  rw [phi_apply, prF_IE_prV, p.prF_toEAf he]

theorem phi_inclE (p : SplitPt D k) {PP : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt p.e PP)
    (c : D.host.E) : phi p he (Formalism.UG.inclE (F := D.host.F) (p.v.adicCompletion D.host.F) c) = p.pr (incA D c) := by
  rw [← phi_prV p he]
  rfl

theorem tensInt_iff (v : HeightOneSpectrum (𝓞 D.host.F)) (z : D.host.E ⊗[D.host.F] v.adicCompletion D.host.F) :
    z ∈ Formalism.UG.tensInt (F := D.host.F) (v.adicCompletion D.host.F) (Formalism.UG.intOE D.host.E)
        (v.adicCompletionIntegers D.host.F).toSubring ↔
      Formalism.UG.P.afsplitIE v z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  refine ⟨Formalism.UG.P.afsplit_IE_int v z, fun h => ?_⟩
  have := Formalism.UG.P.afsplit_prV_int v _ h
  rwa [Formalism.UG.P.afsplit_prV_IE] at this

theorem sigR_sigR (z : EAf D) : Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)
    (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => exact congrArg (· ⊗ₜ[D.host.F] x) (star_star a)
  | add a b ha hb => rw [RingHom.map_add, RingHom.map_add, ha, hb]

theorem toEAf_cA (a : AE D) : toEAf D (cA D a) = Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) (toEAf D a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp only [RingHom.map_zero]
  | add a b ha hb => simp only [RingHom.map_add, ha, hb]
  | tmul y e => rfl

theorem sigR_mem_iff (s : EAf D) : Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) s ∈
    Formalism.L2.Herm.intAf D.host.F D.host.E ↔ s ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  refine ⟨fun h => ?_, GlobalTheory.LevSplit.sigR_int⟩
  have := GlobalTheory.LevSplit.sigR_int h
  rwa [sigR_sigR] at this

theorem one_sub_e_mul (p : SplitPt D k) (y : EAf D)
    (hy : ∀ w, w ≠ p.v → Formalism.UG.prV (E := D.host.E) w y = 0) :
    (1 - toEAf D p.e) * y = toEAf D (cA D p.e) * y := by
  obtain ⟨ε, hε, he⟩ := p.above
  rw [← sub_eq_zero, ← sub_mul, sub_sub, ← RingHom.map_add, he]
  refine Formalism.UG.P.afsplit_inj _ fun w => ?_
  rw [map_mul]
  by_cases hw : w = p.v
  · subst hw; rw [map_sub, map_one, prV_toEAf_eps p hε, sub_self, zero_mul]
  · rw [hy w hw, mul_zero]

theorem sigR_inclE (v : HeightOneSpectrum (𝓞 D.host.F)) (c : D.host.E) :
    Formalism.UG.sigR (sigD D) (v.adicCompletion D.host.F) (Formalism.UG.inclE (F := D.host.F) (v.adicCompletion D.host.F) c) =
      Formalism.UG.inclE (F := D.host.F) (v.adicCompletion D.host.F) (sigD D c) := by
  simp only [Formalism.UG.sigR, Formalism.UG.inclE, Algebra.TensorProduct.includeLeftRingHom_apply, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq]

theorem exists_ringHom_int : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (PP : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt p.e PP →
    ∃ φ : D.host.E ⊗[D.host.F] p.v.adicCompletion D.host.F →+* k,
      (∀ a : AE D, φ (Formalism.UG.prV (E := D.host.E) p.v (toEAf D a)) = p.pr a) ∧
      (∀ c : D.host.E, φ (Formalism.UG.inclE (F := D.host.F) (p.v.adicCompletion D.host.F) c) = p.pr (incA D c)) ∧
      (∀ c : D.host.E, φ (Formalism.UG.sigR (sigD D) (p.v.adicCompletion D.host.F)
          (Formalism.UG.inclE (F := D.host.F) (p.v.adicCompletion D.host.F) c)) = p.pr (incA D (sigD D c))) ∧
      ∀ z, z ∈ Formalism.UG.tensInt (F := D.host.F) (p.v.adicCompletion D.host.F) (Formalism.UG.intOE D.host.E)
          (p.v.adicCompletionIntegers D.host.F).toSubring ↔
        φ z ∈ 𝒪[k] ∧ φ (Formalism.UG.sigR (sigD D) (p.v.adicCompletion D.host.F) z) ∈ 𝒪[k] := by
  intro D k _ _ _ _ p PP he
  refine ⟨phi p he, phi_prV p he, phi_inclE p he, fun c => by rw [sigR_inclE]; exact phi_inclE p he (sigD D c), fun z => ?_⟩
  set y := Formalism.UG.P.afsplitIE p.v z with hy
  have hsup : ∀ w, w ≠ p.v → Formalism.UG.prV (E := D.host.E) w y = 0 := fun w hw =>
    Formalism.UG.P.afsplit_prV_IE_ne p.v w hw z
  have hsig : Formalism.UG.P.afsplitIE p.v (Formalism.UG.sigR (sigD D) (p.v.adicCompletion D.host.F) z) =
      Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) y := by
    rw [hy]; exact (Formalism.UG.P.afsplit_sigR_IE (sigD D) p.v z).symm
  have h1 := tensInt_iff p.v z
  have h2 := p.mem_intAf_iff he y
  have h3 := one_sub_e_mul p y hsup
  have h4 := p.prF_mem_iff he (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) y)
  have h5 : toEAf D (cA D p.e) * y = Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)
      (toEAf D p.e * Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) y) := by
    rw [RingHom.map_mul, sigR_sigR, toEAf_cA]
  refine h1.trans (h2.trans ?_)
  rw [h3, h5, sigR_mem_iff, ← h4]
  have e1 : phi p he z = p.prF he y := phi_apply p he z
  have e2 : phi p he (Formalism.UG.sigR (sigD D) (p.v.adicCompletion D.host.F) z) =
      p.prF he (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) y) := (phi_apply p he _).trans (congrArg _ hsig)
  rw [e1, e2]
  exact and_comm

end GlobalTheory.FinPl.SplitPhi
