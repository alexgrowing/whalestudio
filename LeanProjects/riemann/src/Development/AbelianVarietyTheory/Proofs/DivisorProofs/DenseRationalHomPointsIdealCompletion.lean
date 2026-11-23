import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IpEqZeroOfHeisEigen
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentApproximation.AddDense

open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio
open scoped nonZeroDivisors
open GlobalTheory.CosetOrth

noncomputable section

namespace GlobalTheory.CosetOrthDens

section General

variable {E : Type} [Field E] [NumberField E]

theorem inHat_algebraMap_iff {I : FractionalIdeal (𝓞 E)⁰ E} (hI : I ≠ 0) (x : E) :
    InHat I (algebraMap E (FiniteAdeleRing (𝓞 E) E) x) ↔ x ∈ I :=
  (GlobalTheory.Idele.mem_adelicIdeal_iff hI).symm.trans (GlobalTheory.Idele.algebraMap_mem_adelicIdeal hI x)

theorem isOpen_inHat_one : IsOpen {x : FiniteAdeleRing (𝓞 E) E | InHat 1 x} := by
  have h := RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
    (A := fun v => (v.adicCompletionIntegers E : Set (v.adicCompletion E))) fun v => Valued.isOpen_valuationSubring _
  have e : {x : FiniteAdeleRing (𝓞 E) E | InHat 1 x} =
      {x : FiniteAdeleRing (𝓞 E) E | ∀ v, x v ∈ (v.adicCompletionIntegers E : Set (v.adicCompletion E))} := by
    ext x
    exact inHat_one_iff x
  rw [e]
  exact h

theorem isOpen_inHat {I : FractionalIdeal (𝓞 E)⁰ E} (hI : I ≠ 0) : IsOpen {x : FiniteAdeleRing (𝓞 E) E | InHat I x} := by
  obtain ⟨c, hc0, hc⟩ := FractionalIdeal.exists_ne_zero_mem_isInteger hI
  set a : E := algebraMap (𝓞 E) E c with ha
  have ha0 : a ≠ 0 := by simpa [ha] using hc0
  rw [isOpen_iff_mem_nhds]
  intro y hy
  have hcont : Continuous fun x : FiniteAdeleRing (𝓞 E) E => (x - y) * algebraMap E (FiniteAdeleRing (𝓞 E) E) a⁻¹ :=
    (continuous_id.sub continuous_const).mul continuous_const
  refine Filter.mem_of_superset ((isOpen_inHat_one.preimage hcont).mem_nhds ?_) fun x hx => ?_
  · show InHat 1 ((y - y) * _)
    rw [sub_self, zero_mul]
    exact inHat_zero 1
  · have h1 := InHat.mul_left hx ((inHat_algebraMap_iff hI a).2 hc)
    rw [mul_assoc, ← map_mul, inv_mul_cancel₀ ha0, map_one, mul_one] at h1
    have h2 := h1.add hy
    rwa [sub_add_cancel] at h2

end General

variable {D : D7}

def lift (D : D7) (s : FA D) : AE D :=
  GlobalTheory.LFun.extZero D.host.F D.host.E ((GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).symm s)

theorem continuous_lift : Continuous (lift D) :=
  GlobalTheory.LFun.continuous_extZero.comp GlobalTheory.LFun.continuous_finAdEquiv_symm

theorem infPart_lift (s : FA D) : infPart D (lift D s) = 0 := GlobalTheory.LFun.infTens_extZero _

theorem fe_lift (s : FA D) : fe D (lift D s) = s := by
  have : finPart D (lift D s) = (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).symm s := GlobalTheory.LFun.finTens_extZero _
  rw [fe_apply, this, RingEquiv.apply_symm_apply]

theorem lift_fe {x : AE D} (hx : infPart D x = 0) : lift D (fe D x) = x := by
  refine sub_eq_zero.1 (GlobalTheory.LatVac.eq_zero_of_parts _ ?_ ?_)
  · rw [RingHom.map_sub, infPart_lift, hx, sub_self]
  · apply (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).injective
    rw [map_zero, ← fe_apply, map_sub, fe_lift, sub_self]

theorem lift_algebraMap (γ : D.host.E) :
    lift D (algebraMap D.host.E (FA D) γ) = pairA D.host.F 0 1 ⊗ₜ[D.host.F] γ := by
  have h1 : infPart D (pairA D.host.F 0 1 ⊗ₜ[D.host.F] γ) = 0 := by
    show (0 : Ainf D.host.F) ⊗ₜ[D.host.F] γ = 0
    exact TensorProduct.zero_tmul _ _
  have h2 : fe D (pairA D.host.F 0 1 ⊗ₜ[D.host.F] γ) = algebraMap D.host.E (FA D) γ := by
    show GlobalTheory.LFun.toFinAd D.host.F D.host.E ((1 : Af D.host.F) ⊗ₜ[D.host.F] γ) = _
    rw [GlobalTheory.LFun.toFinAd_tmul, map_one, one_mul]
  rw [← h2, lift_fe h1]

theorem exists_finPt_sub_mem : ∀ {D : D7} (S T : HSp D) (r : D.host.E) (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E), r ≠ 0 → I ≠ 0 →
  ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∀ u : WO S T, HatPt r I u →
  ∃ z : Matrix (Fin T.rank) (Fin S.rank) D.host.E, (∀ i j, z i j ∈ I) ∧ u - finPt (S := S) (T := T) rfl rfl r z ∈ U := by
  intro D S T r I hr hI U hU u hu
  haveI hg : IsTopologicalAddGroup (WO S T) := inferInstance
  haveI : ContinuousSub (WO S T) := IsTopologicalAddGroup.to_continuousSub
  let Φ : (Fin T.rank → Fin S.rank → FA D) → WO S T := fun y =>
    Matrix.of fun i j => lift D (algebraMap D.host.E (FA D) r⁻¹ * y i j)
  have hΦ : Continuous Φ := continuous_matrix fun i j =>
    continuous_lift.comp (continuous_const.mul ((continuous_apply j).comp (continuous_apply i)))
  have hd : DenseRange (Pi.map fun (_ : Fin T.rank) => Pi.map fun (_ : Fin S.rank) => algebraMap D.host.E (FA D)) :=
    DenseRange.piMap fun _ => DenseRange.piMap fun _ =>
      PI.UnipApproxD.IntegersDenseFiniteAdeles.denseRange (R := 𝓞 D.host.E) (K := D.host.E)
  have hO : IsOpen ({y | u - Φ y ∈ U} ∩ ⋂ i, ⋂ j, {y : Fin T.rank → Fin S.rank → FA D | InHat I (y i j)}) :=
    (hU.preimage (continuous_const.sub hΦ)).inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (isOpen_inHat hI).preimage (f := fun y : Fin T.rank → Fin S.rank → FA D => y i j)
        ((continuous_apply j).comp (continuous_apply i)))
  have h0 : Φ (fun i j => algebraMap D.host.E (FA D) r * fe D (u i j)) = u := by
    funext i j
    show lift D (algebraMap D.host.E (FA D) r⁻¹ * (algebraMap D.host.E (FA D) r * fe D (u i j))) = u i j
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hr, map_one, one_mul]
    exact lift_fe (congrFun (congrFun hu.1 i) j)
  obtain ⟨z, hz1, hz2⟩ := hd.exists_mem_open hO ⟨fun i j => algebraMap D.host.E (FA D) r * fe D (u i j), by
    show u - Φ _ ∈ U
    rw [h0, sub_self]
    exact U.zero_mem, Set.mem_iInter.2 fun i => Set.mem_iInter.2 fun j => hu.2 i j⟩
  refine ⟨Matrix.of fun i j => -z i j, fun i j => ?_, ?_⟩
  · have : z i j ∈ I := (inHat_algebraMap_iff hI _).1 (Set.mem_iInter.1 (Set.mem_iInter.1 hz2 i) j)
    exact (I : Submodule (𝓞 D.host.E) D.host.E).neg_mem this
  · have e : finPt (S := S) (T := T) rfl rfl r (Matrix.of fun i j => -z i j) =
        Φ (Pi.map (fun (_ : Fin T.rank) => Pi.map fun (_ : Fin S.rank) => algebraMap D.host.E (FA D)) z) := by
      funext i j
      show pairA D.host.F 0 1 ⊗ₜ[D.host.F] (-(r⁻¹ * -z i j)) =
        lift D (algebraMap D.host.E (FA D) r⁻¹ * algebraMap D.host.E (FA D) (z i j))
      rw [← map_mul, lift_algebraMap, mul_neg, neg_neg]
    rw [e]
    exact hz1

end GlobalTheory.CosetOrthDens
