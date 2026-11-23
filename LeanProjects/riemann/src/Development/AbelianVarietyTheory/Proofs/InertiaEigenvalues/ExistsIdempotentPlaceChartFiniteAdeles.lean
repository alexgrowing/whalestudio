import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasShape
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockVectorsKilledHeisenbergAverageIsotropic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNonvanishingFiniteDatumDefiniteLift
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEqMulOfResSNeOne
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef

namespace GlobalTheory.DownLift.SplitCoef

variable {D : D7}

theorem toEAf_idem_mul_eq_zero {e : AE D} (he : IsSplitIdem D e) (a : AE D) :
    toEAf D (e * a) = 0 ↔ e * a = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, map_zero]⟩
  apply GlobalTheory.SplitScalar.adele_ext
  · rw [map_mul, GlobalTheory.SplitScalar.infPart_splitIdem he, zero_mul, map_zero]
  · rw [map_zero]
    change (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E) (finPart D (e * a)) = 0 at h
    exact (map_eq_zero_iff _ (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).injective).1 h

theorem residue_eq_zero_iff_val_lt {v : HeightOneSpectrum (𝓞 D.host.F)} (o : GlobalTheory.SplitHecke.Ov D v) :
    IsLocalRing.residue (GlobalTheory.SplitHecke.Ov D v) o = 0 ↔ Valued.v (o : Fv D.host.F v) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
  exact ⟨fun h => lt_of_le_of_ne o.2 h, fun h => h.ne⟩

set_option maxHeartbeats 1000000 in

theorem exists_levChart : ∀ (D : D7) (e : AE D) (PP : Pl D.host.E), Formalism.L2.NTheta.IsIdemAt e PP →
    ∃ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : Formalism.IndefR.Lev.EAf D →+* Fv D.host.F v)
      (ι : kP PP ≃+* IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v)), LevChart e PP v φ ι := by
  intro D e PP he
  obtain ⟨v, π, hπ⟩ := GlobalTheory.SplitChart.exists_chart e he.1
  obtain ⟨φ, hφ, hres⟩ := GlobalTheory.ThetaSupport.exists_chart_levels he hπ
  obtain ⟨hi, hi1⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D e PP he
  have hπe : π e = 1 := by
    have h0 : π (1 - e) = 0 := (hπ.2.1 _).2 (by rw [mul_sub, mul_one, he.1.1, sub_self])
    rw [map_sub, map_one, sub_eq_zero] at h0
    exact h0.symm
  have hint_iff : ∀ a : AE D, toEAf D (e * a) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔
      π a ∈ v.adicCompletionIntegers D.host.F := by
    intro a
    rw [← GlobalTheory.SplitHecke.isInt_Ov, ← hπ.2.2.2 a]
    exact ⟨GlobalTheory.PlaceDatum.finPart_mem_of_toEAf, GlobalTheory.IdemRes.toEAf_mem_of_finPart⟩
  have hsurj : Function.Surjective φ := fun y => by
    obtain ⟨a, ha⟩ := hπ.1 y
    exact ⟨toEAf D a, by rw [hφ, ha]⟩
  have hint : ∀ s : Formalism.L2.Herm.intAf D.host.F D.host.E, φ s ∈ v.adicCompletionIntegers D.host.F := by
    intro s
    obtain ⟨a, ha⟩ := GlobalTheory.AdjDatumNe.toEAf_surjective (D := D) (s : Formalism.IndefR.Datum.EAf D)
    rw [← ha, hφ, ← hint_iff, map_mul, ha]
    exact mul_mem hi s.2
  let g : Formalism.L2.Herm.intAf D.host.F D.host.E →+* IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v) :=
    (IsLocalRing.residue (GlobalTheory.SplitHecke.Ov D v)).comp
      ((φ.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype).codRestrict (v.adicCompletionIntegers D.host.F) hint)
  have hg : ∀ s, g s = IsLocalRing.residue (GlobalTheory.SplitHecke.Ov D v) ⟨φ s, hint s⟩ := fun s => rfl
  have hrsurj : Function.Surjective (resS D.host.F PP) := fun q => by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
    exact ⟨_, resS_oToS PP x⟩
  have hker : RingHom.ker (resS D.host.F PP) ≤ RingHom.ker g := fun s hs => by
    rw [RingHom.mem_ker] at hs ⊢
    rw [hg, residue_eq_zero_iff_val_lt]
    exact hres s hs
  let ι₀ : kP PP →+* IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v) :=
    RingHom.liftOfRightInverse (resS D.host.F PP) (Function.surjInv hrsurj) (Function.rightInverse_surjInv hrsurj) ⟨g, hker⟩
  have hι₀ : ∀ s, ι₀ (resS D.host.F PP s) = g s := fun s =>
    RingHom.liftOfRightInverse_comp_apply _ _ _ _ s
  haveI := PP.isMaximal
  letI : Field (kP PP) := Ideal.Quotient.field PP.asIdeal
  have hbij : Function.Bijective ι₀ := by
    refine ⟨RingHom.injective ι₀, fun r => ?_⟩
    obtain ⟨o, rfl⟩ := IsLocalRing.residue_surjective r
    obtain ⟨z, hz⟩ := hsurj (o : Fv D.host.F v)
    obtain ⟨a, rfl⟩ := GlobalTheory.AdjDatumNe.toEAf_surjective (D := D) z
    have hm : toEAf D e * toEAf D a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
      rw [← map_mul, hint_iff, ← hφ, hz]
      exact o.2
    refine ⟨resS D.host.F PP ⟨_, hm⟩, ?_⟩
    rw [hι₀, hg]
    congr 1
    apply Subtype.ext
    show φ (toEAf D e * toEAf D a) = (o : Fv D.host.F v)
    rw [map_mul, hz, hφ e, hπe, one_mul]
  refine ⟨v, φ, RingEquiv.ofBijective ι₀ hbij, hsurj, fun z => ?_, fun z => ?_, fun s o ho => ?_⟩
  · obtain ⟨a, rfl⟩ := GlobalTheory.AdjDatumNe.toEAf_surjective (D := D) z
    rw [hφ, hπ.2.1, ← map_mul, toEAf_idem_mul_eq_zero he.1]
  · obtain ⟨a, rfl⟩ := GlobalTheory.AdjDatumNe.toEAf_surjective (D := D) z
    rw [← map_mul, hint_iff, hφ]
  · change ι₀ (resS D.host.F PP s) = _
    rw [hι₀, hg]
    congr 1
    exact Subtype.ext ho.symm

end GlobalTheory.DownLift.SplitCoef
