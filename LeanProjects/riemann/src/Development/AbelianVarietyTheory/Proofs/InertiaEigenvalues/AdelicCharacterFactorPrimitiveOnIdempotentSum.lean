import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentSumIntegralDivUniformisersIffReductionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralLiftResiduesIdempotentSumStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameMatricesIntegralOfMemCompletedLattice
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
noncomputable section

namespace GlobalTheory.IdemCharLift

theorem exists_factor {M ι : Type} [AddCommGroup M] (k : ι → Type) [∀ i, AddCommGroup (k i)]
    (χ : AddChar M ℂ) (Q : Finset ι) (R : ∀ i, M →+ k i)
    (hker : ∀ m, (∀ i ∈ Q, R i m = 0) → χ m = 1)
    (hlift : ∀ Y : ∀ i, k i, ∃ m, ∀ i ∈ Q, R i m = Y i) :
    ∃ ψP : ∀ i, AddChar (k i) ℂ, ∀ m, χ m = ∏ i ∈ Q, ψP i (R i m) := by
  classical
  choose L hL using hlift
  have key : ∀ m m', (∀ i ∈ Q, R i m = R i m') → χ m = χ m' := by
    intro m m' h
    have h1 := hker (m - m') (fun i hi => by rw [map_sub, h i hi, sub_self])
    calc χ m = χ ((m - m') + m') := by rw [sub_add_cancel]
      _ = χ m' := by rw [AddChar.map_add_eq_mul, h1, one_mul]
  let ψP : ∀ i, AddChar (k i) ℂ := fun i =>
    { toFun := fun a => χ (L (Pi.single i a))
      map_zero_eq_one' := by
        rw [← AddChar.map_zero_eq_one χ]
        refine key _ _ fun j hj => ?_
        rw [hL _ j hj, map_zero, Pi.single_zero, Pi.zero_apply]
      map_add_eq_mul' := fun a b => by
        rw [← AddChar.map_add_eq_mul]
        refine key _ _ fun j hj => ?_
        rw [hL _ j hj, map_add, hL _ j hj, hL _ j hj, Pi.single_add, Pi.add_apply] }
  refine ⟨ψP, fun m => ?_⟩
  have hs : χ m = χ (∑ i ∈ Q, L (Pi.single i (R i m))) := by
    refine key _ _ fun j hj => ?_
    rw [map_sum, Finset.sum_congr rfl (fun i _ => hL (Pi.single i (R i m)) j hj),
      Finset.sum_eq_single j (fun i _ hij => Pi.single_eq_of_ne (Ne.symm hij) _) (fun h => absurd hj h),
      Pi.single_eq_same]
  have hprod : ∀ (s : Finset ι) (f : ι → M), χ (∑ i ∈ s, f i) = ∏ i ∈ s, χ (f i) := by
    intro s f
    refine Finset.induction_on s ?_ ?_
    · rw [Finset.sum_empty, Finset.prod_empty, AddChar.map_zero_eq_one]
    · intro a s ha ih
      rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]
  rw [hs, hprod]
  rfl

end GlobalTheory.IdemCharLift

namespace GlobalTheory.IdemCharLift

def supG (D : D7) (e : AE D) (ϖ : 𝓞 D.host.E) : AddSubgroup (AE D) where
  carrier := {Z | e * Z = Z ∧ toEAf D (incA D (ϖ : D.host.E) * Z) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E}
  zero_mem' := ⟨mul_zero e, by rw [mul_zero, RingHom.map_zero]; exact zero_mem _⟩
  add_mem' := fun {a b} ha hb => ⟨by rw [mul_add, ha.1, hb.1], by rw [mul_add, RingHom.map_add]; exact add_mem ha.2 hb.2⟩
  neg_mem' := fun {a} ha => ⟨by rw [mul_neg, ha.1], by rw [mul_neg, RingHom.map_neg]; exact neg_mem ha.2⟩

def resG (D : D7) (e : AE D) (ϖ : 𝓞 D.host.E) (PP : Pl D.host.E) : supG D e ϖ →+ kP PP where
  toFun m := resS D.host.F PP ⟨toEAf D (incA D (ϖ : D.host.E) * m), m.2.2⟩
  map_zero' := by
    rw [← map_zero (resS D.host.F PP)]
    exact congrArg _ (Subtype.ext (by simp))
  map_add' a b := by
    rw [← map_add (resS D.host.F PP)]
    exact congrArg _ (Subtype.ext (by simp [mul_add]))

def chiA (D : D7) (ψ : AddChar (AF D.host.F) ℂ) : AddChar (AE D) ℂ :=
  ψ.compAddMonoidHom ((Algebra.trace (AF D.host.F) (AE D)).toAddMonoidHom.comp (AddMonoidHom.mulLeft (incA D D.host.xi0)))

theorem toEAf_surj (D : D7) : Function.Surjective (toEAf D) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, RingHom.map_zero _⟩
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, RingHom.map_add _ _ _⟩
  | tmul x a => exact ⟨pairA D.host.F 0 a ⊗ₜ[D.host.F] x, rfl⟩

end GlobalTheory.IdemCharLift

namespace GlobalTheory.IdemCharLift

theorem factor_prim : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (Q : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Q → ∀ ϖ : 𝓞 D.host.E, ϖ ≠ 0 → (∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) → (∀ Z : AE D, e * Z = Z → (toEAf D Z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ ∀ Z' : AE D, e * Z' = Z' → toEAf D Z' ∈ Formalism.L2.Herm.intAf D.host.F D.host.E → ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * (Z * Z'))) = 1)) → ∃ ψP : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ, (∀ PP ∈ Q, (ψP PP).IsPrimitive) ∧ ∀ Z : AE D, e * Z = Z → ∀ h : toEAf D (incA D (ϖ : D.host.E) * Z) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * Z)) = ∏ PP ∈ Q.attach, ψP PP.1 (resS D.host.F PP.1 ⟨toEAf D (incA D (ϖ : D.host.E) * Z), h⟩) := by
  intro D ψ Q e he ϖ hϖ0 hϖ H
  have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have heI : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    GlobalTheory.LatHalfInt.toEAf_mem_of_finPart (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, hee]))
  obtain ⟨⟨es, hes, hsum⟩, hc⟩ := he
  have hc' : (∑ PP ∈ Q, es PP) * cA D (∑ PP ∈ Q, es PP) = 0 := hsum ▸ hc
  have hϖE : (ϖ : D.host.E) ≠ 0 := by exact_mod_cast hϖ0
  have hinv : incA D ((ϖ : D.host.E)⁻¹) * incA D (ϖ : D.host.E) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hϖE, map_one]
  have hdiv : ∀ m : supG D e ϖ, (toEAf D (m : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔
      ∀ PP ∈ Q, resG D e ϖ PP m = 0) := by
    intro m
    have h1 := GlobalTheory.T.idempotentSum_integral_div_uniformisers_iff_reduction_zero D Q es (fun _ => ϖ) hes hc' (fun PP hP => hϖ PP hP)
      (toEAf D (incA D (ϖ : D.host.E) * m)) m.2.2
      (by rw [← hsum, ← map_mul, ← mul_assoc, mul_comm e, mul_assoc, m.2.1])
    have h2 : toEAf D (∑ PP ∈ Q, es PP * incA D ((ϖ : D.host.E)⁻¹)) * toEAf D (incA D (ϖ : D.host.E) * m) =
        toEAf D m := by
      rw [← Finset.sum_mul, ← hsum, ← map_mul]
      congr 1
      calc e * incA D ((ϖ : D.host.E)⁻¹) * (incA D (ϖ : D.host.E) * m)
          = (incA D ((ϖ : D.host.E)⁻¹) * incA D (ϖ : D.host.E)) * (e * m) := by ring
        _ = m := by rw [hinv, one_mul, m.2.1]
    rw [h2] at h1
    exact h1
  have hker : ∀ m : supG D e ϖ, (∀ PP ∈ Q, resG D e ϖ PP m = 0) →
      ((chiA D ψ).compAddMonoidHom (supG D e ϖ).subtype) m = 1 := by
    intro m hm
    have h1 := (H m m.2.1).1 ((hdiv m).2 hm) e hee heI
    rw [mul_comm (m : AE D) e, m.2.1] at h1
    exact h1
  have hlift : ∀ Y : ∀ PP : Pl D.host.E, kP PP, ∃ m : supG D e ϖ, ∀ PP ∈ Q, resG D e ϖ PP m = Y PP := by
    intro Y
    obtain ⟨N, hN, hNe, hNY⟩ := GlobalTheory.T.exists_integral_lift_residues_idempotentSum D Q es hes hc' Y
    obtain ⟨w, hw⟩ := toEAf_surj D N
    have hm1 : e * (e * incA D ((ϖ : D.host.E)⁻¹) * w) = e * incA D ((ϖ : D.host.E)⁻¹) * w := by
      rw [← mul_assoc, ← mul_assoc, hee]
    have hm0 : incA D (ϖ : D.host.E) * (e * incA D ((ϖ : D.host.E)⁻¹) * w) = e * w := by
      calc incA D (ϖ : D.host.E) * (e * incA D ((ϖ : D.host.E)⁻¹) * w)
          = (incA D ((ϖ : D.host.E)⁻¹) * incA D (ϖ : D.host.E)) * (e * w) := by ring
        _ = e * w := by rw [hinv, one_mul]
    have hm2 : toEAf D (incA D (ϖ : D.host.E) * (e * incA D ((ϖ : D.host.E)⁻¹) * w)) = N := by
      rw [hm0, map_mul, hw, hsum]
      exact hNe
    refine ⟨⟨_, hm1, hm2 ▸ hN⟩, fun PP hP => ?_⟩
    rw [← hNY PP hP]
    show resS D.host.F PP ⟨_, _⟩ = resS D.host.F PP ⟨N, hN⟩
    exact congrArg _ (Subtype.ext hm2)
  obtain ⟨ψP, hψP⟩ := exists_factor (fun PP : Pl D.host.E => kP PP)
    ((chiA D ψ).compAddMonoidHom (supG D e ϖ).subtype) Q (resG D e ϖ) hker hlift
  refine ⟨ψP, fun PP hP => ?_, fun Z hZ h => ?_⟩
  · haveI := PP.isMaximal
    letI := Ideal.Quotient.field PP.asIdeal
    refine AddChar.IsPrimitive.of_ne_one fun h1 => ?_
    obtain ⟨m1, hm1⟩ := hlift (Pi.single PP 1)
    have hnI : toEAf D (m1 : AE D) ∉ Formalism.L2.Herm.intAf D.host.F D.host.E := fun hI => by
      have h3 := (hdiv m1).1 hI PP hP
      rw [hm1 PP hP, Pi.single_eq_same] at h3
      exact one_ne_zero h3
    obtain ⟨Z', hZ'e, hZ'I, hne⟩ : ∃ Z' : AE D, e * Z' = Z' ∧ toEAf D Z' ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧
        ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * ((m1 : AE D) * Z'))) ≠ 1 := by
      by_contra hcon
      push_neg at hcon
      exact hnI ((H m1 m1.2.1).2 hcon)
    let m2 : supG D e ϖ := ⟨(m1 : AE D) * Z', by rw [← mul_assoc, m1.2.1],
      by rw [← mul_assoc, map_mul]; exact mul_mem m1.2.2 hZ'I⟩
    have hres : ∀ QQ : Pl D.host.E, resG D e ϖ QQ m2 =
        resG D e ϖ QQ m1 * resS D.host.F QQ ⟨toEAf D Z', hZ'I⟩ := by
      intro QQ
      show resS D.host.F QQ ⟨_, _⟩ = resS D.host.F QQ ⟨_, _⟩ * resS D.host.F QQ ⟨_, _⟩
      rw [← map_mul]
      exact congrArg _ (Subtype.ext (by
        show toEAf D (incA D (ϖ : D.host.E) * ((m1 : AE D) * Z')) = toEAf D (incA D (ϖ : D.host.E) * m1) * toEAf D Z'
        rw [← map_mul, mul_assoc]))
    have h2 := hψP m2
    rw [Finset.prod_eq_single PP (fun QQ hQ hQP => by
        rw [hres, hm1 QQ hQ, Pi.single_eq_of_ne hQP, zero_mul, AddChar.map_zero_eq_one])
      (fun h => absurd hP h), h1, AddChar.one_apply] at h2
    exact hne h2
  · exact (hψP ⟨Z, hZ, h⟩).trans (Finset.prod_attach Q (fun PP => ψP PP (resG D e ϖ PP ⟨Z, hZ, h⟩))).symm

end GlobalTheory.IdemCharLift
