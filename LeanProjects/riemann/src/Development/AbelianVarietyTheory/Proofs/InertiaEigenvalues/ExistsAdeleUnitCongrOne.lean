import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.RationalRayLevels
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoordLattice
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneVectorCcOfSiegelWeil
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnitRootCong

open Formalism.MainNotions.StandardLattice

section Gen

variable {F : Type} [Field F] [NumberField F]

def mkAf (g : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (hg : ∀ v, g v ∈ v.adicCompletionIntegers F) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F :=
  ⟨g, Filter.Eventually.of_forall hg⟩

theorem evalV_mkAf (g : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (hg : ∀ v, g v ∈ v.adicCompletionIntegers F) (v : HeightOneSpectrum (𝓞 F)) :
    evalV F v (mkAf g hg) = g v := rfl

theorem mkAf_mem (g : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (hg : ∀ v, g v ∈ v.adicCompletionIntegers F) : mkAf g hg ∈ intAf F := fun v => by
  rw [evalV_mkAf]; exact hg v

theorem val_eq_one_of_mul (v : HeightOneSpectrum (𝓞 F)) {a b : v.adicCompletion F}
    (ha : Valued.v a ≤ 1) (hb : Valued.v b ≤ 1) (hab : Valued.v (a * b) = 1) : Valued.v a = 1 := by
  refine le_antisymm ha ?_
  calc (1 : _) = Valued.v a * Valued.v b := by rw [← map_mul, hab]
    _ ≤ Valued.v a * 1 := mul_le_mul_right hb (Valued.v a)
    _ = Valued.v a := mul_one _

theorem val_le_one {v : HeightOneSpectrum (𝓞 F)} {a : v.adicCompletion F}
    (ha : a ∈ v.adicCompletionIntegers F) : Valued.v a ≤ 1 :=
  (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).1 ha

theorem mem_of_val {v : HeightOneSpectrum (𝓞 F)} {a : v.adicCompletion F}
    (ha : Valued.v a ≤ 1) : a ∈ v.adicCompletionIntegers F :=
  (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).2 ha

theorem val_natCast_le (v : HeightOneSpectrum (𝓞 F)) (k : ℕ) : Valued.v (k : v.adicCompletion F) ≤ 1 :=
  val_le_one (natCast_mem (HeightOneSpectrum.adicCompletionIntegers F v) k)

theorem val_unit_of_rel (v : HeightOneSpectrum (𝓞 F)) (k : ℕ) {t q r : v.adicCompletion F}
    (hm : Valued.v (((2 * k + 1 : ℕ) : v.adicCompletion F)) < 1)
    (ht : Valued.v t ≤ 1) (hq : Valued.v q ≤ 1) (hr : Valued.v r ≤ 1)
    (h4 : (4 : v.adicCompletion F) = t * q + ((2 * k + 1 : ℕ) : v.adicCompletion F) * r) :
    Valued.v (-(k : v.adicCompletion F) * t) = 1 := by
  set M : v.adicCompletion F := ((2 * k + 1 : ℕ) : v.adicCompletion F) with hM
  have hk : Valued.v (k : v.adicCompletion F) ≤ 1 := val_natCast_le v k
  have h2k : Valued.v (2 * (k : v.adicCompletion F)) = 1 := by
    have e : 2 * (k : v.adicCompletion F) = -1 + M := by rw [hM]; push_cast; ring
    rw [e, Valuation.map_add_eq_of_lt_left Valued.v (by rw [Valuation.map_neg, map_one]; exact hm),
      Valuation.map_neg, map_one]
  have hsq : (2 * (k : v.adicCompletion F)) ^ 2 = (-(k : v.adicCompletion F) * t) * (-(k : v.adicCompletion F) * q) +
      M * ((k : v.adicCompletion F) ^ 2 * r) := by
    linear_combination (k : v.adicCompletion F) ^ 2 * h4
  have hsmall : Valued.v (M * ((k : v.adicCompletion F) ^ 2 * r)) < 1 := by
    rw [map_mul]
    calc Valued.v M * Valued.v ((k : v.adicCompletion F) ^ 2 * r) ≤ Valued.v M * 1 := by
          refine mul_le_mul_right ?_ _
          rw [map_mul, map_pow]
          calc Valued.v (k : v.adicCompletion F) ^ 2 * Valued.v r ≤ 1 * 1 := by
                gcongr
                exact pow_le_one₀ zero_le' hk
            _ = 1 := one_mul 1
      _ < 1 := by rw [mul_one]; exact hm
  have hprod : Valued.v ((-(k : v.adicCompletion F) * t) * (-(k : v.adicCompletion F) * q)) = 1 := by
    have e : (-(k : v.adicCompletion F) * t) * (-(k : v.adicCompletion F) * q) =
        (2 * (k : v.adicCompletion F)) ^ 2 + -(M * ((k : v.adicCompletion F) ^ 2 * r)) := by
      rw [hsq]; ring
    have hv1 : Valued.v ((2 * (k : v.adicCompletion F)) ^ 2) = 1 := by rw [map_pow, h2k, one_pow]
    rw [e, Valuation.map_add_eq_of_lt_left Valued.v (by rw [Valuation.map_neg, hv1]; exact hsmall), hv1]
  refine val_eq_one_of_mul v ?_ ?_ hprod
  · rw [map_mul, Valuation.map_neg]
    calc Valued.v (k : v.adicCompletion F) * Valued.v t ≤ 1 * 1 := by gcongr
      _ = 1 := one_mul 1
  · rw [map_mul, Valuation.map_neg]
    calc Valued.v (k : v.adicCompletion F) * Valued.v q ≤ 1 * 1 := by gcongr
      _ = 1 := one_mul 1

end Gen

end GlobalTheory.UnitRootCong

namespace GlobalTheory.UnitRootCong

open Formalism.MainNotions.StandardLattice

set_option maxHeartbeats 2000000 in

theorem exists_adele_unit_congr_one : ∀ (D : D7) (m : ℕ), Odd m → ∀ (z y : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ), (y : Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D → ((y⁻¹ : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D → (y : Af D.host.F ⊗[D.host.F] D.host.E) = z * sigR (Af D.host.F) D.sp.cm.sig (y : Af D.host.F ⊗[D.host.F] D.host.E) → (∃ w ∈ intAE D, (z : Af D.host.F ⊗[D.host.F] D.host.E) - 1 = m • w) → ∃ (b : (Af D.host.F)ˣ) (y' : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ), (y' : Af D.host.F ⊗[D.host.F] D.host.E) = (y : Af D.host.F ⊗[D.host.F] D.host.E) * ((b : Af D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E)) ∧ (y' : Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D ∧ ((y'⁻¹ : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D ∧ ∃ w ∈ intAE D, (y' : Af D.host.F ⊗[D.host.F] D.host.E) - 1 = m • w := by
  classical
  intro D m hm z y hyI hyiI hyz hzw
  obtain ⟨w, hwI, hw⟩ := hzw
  obtain ⟨k, rfl⟩ := hm
  have hE := GlobalTheory.AdelicU.isCMExt_host D
  set M : ℕ := 2 * k + 1 with hMdef
  set yv : Af D.host.F ⊗[D.host.F] D.host.E := (y : Af D.host.F ⊗[D.host.F] D.host.E) with hyv
  set yi : Af D.host.F ⊗[D.host.F] D.host.E := ((y⁻¹ : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E) with hyi
  have hyy : yv * yi = 1 := y.mul_inv
  set s := sigR (Af D.host.F) D.sp.cm.sig yv with hs
  have hsI : s ∈ intAE D := GlobalTheory.PlaceIdem.sig_mem D hyI
  set T := Algebra.trace (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) with hT
  set ι := algebraMap (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) with hι
  have ht : yv + s = ι (T yv) := GlobalTheory.GaussMean.OneVec.add_sigR _ hE yv
  have hw' : (z : Af D.host.F ⊗[D.host.F] D.host.E) - 1 = (M : Af D.host.F ⊗[D.host.F] D.host.E) * w := by
    rw [hw, nsmul_eq_mul]
  have E3 : 2 * yv = ι (T yv) + (M : Af D.host.F ⊗[D.host.F] D.host.E) * (w * s) := by
    linear_combination ht + hyz + s * hw'

  have hιI : ∀ a ∈ intAf D.host.F, ι a ∈ intAE D := fun a ha =>
    AddSubgroup.subset_closure ⟨a, ha, 1, by simp [hι, Algebra.TensorProduct.algebraMap_apply]⟩
  have hmulI : ∀ {a b}, a ∈ intAE D → b ∈ intAE D → a * b ∈ intAE D := fun ha hb =>
    GlobalTheory.HostAdeleIso.intAE_mul_mem D ha hb
  have hoI : (1 : Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D := by
    simpa using hιI 1 GlobalTheory.SplitHeckeLabel.one_mem_intAf
  have hnI : ∀ n : ℕ, (n : Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D := fun n => by
    rw [← nsmul_one]; exact nsmul_mem hoI n
  have hrI : w * s * yi ∈ intAE D := hmulI (hmulI hwI hsI) hyiI

  have hTl : ∀ (a : Af D.host.F) x, T (ι a * x) = a * T x := fun a x => by
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  have hT2 : T (ι 2) = 4 := by
    have h1 := GlobalTheory.GaussMean.OneVec.half_trace (Af D.host.F) hE (2 : Af D.host.F)
    have h2 := GlobalTheory.GaussMean.OneVec.half_two (F := D.host.F) (Af D.host.F)
    linear_combination 2 * h1 - T (ι 2) * h2
  have R1 : (4 : Af D.host.F) = T yv * T yi + (M : Af D.host.F) * T (w * s * yi) := by
    have e : ι 2 = ι (T yv) * yi + ι (M : Af D.host.F) * (w * s * yi) := by
      rw [map_ofNat, map_natCast]
      linear_combination yi * E3 - 2 * hyy
    rw [← hT2, e, map_add, hTl, hTl]

  let P : HeightOneSpectrum (𝓞 D.host.F) → Prop := fun v => Valued.v ((M : v.adicCompletion D.host.F)) < 1
  have hunit : ∀ v, P v → Valued.v (-(k : v.adicCompletion D.host.F) * evalV D.host.F v (T yv)) = 1 := fun v hv => by
    refine val_unit_of_rel v k hv (val_le_one (GlobalTheory.SplitHeckeLabel.trace_mem_intAf hyI v))
      (val_le_one (GlobalTheory.SplitHeckeLabel.trace_mem_intAf hyiI v))
      (val_le_one (GlobalTheory.SplitHeckeLabel.trace_mem_intAf hrI v)) ?_
    have := congrArg (evalV D.host.F v) R1
    simp only [map_add, map_mul, map_natCast, map_ofNat] at this
    exact this
  have hMone : ∀ v, ¬ P v → Valued.v ((M : v.adicCompletion D.host.F)) = 1 := fun v hv =>
    le_antisymm (val_natCast_le v M) (not_lt.1 hv)
  have hMne : ∀ v, ¬ P v → (M : v.adicCompletion D.host.F) ≠ 0 := fun v hv h => by
    have := hMone v hv; rw [h, map_zero] at this; exact zero_ne_one this
  let eg : ∀ v : HeightOneSpectrum (𝓞 D.host.F), v.adicCompletion D.host.F := fun v => if P v then 1 else 0
  let fg : ∀ v : HeightOneSpectrum (𝓞 D.host.F), v.adicCompletion D.host.F :=
    fun v => if P v then 0 else (M : v.adicCompletion D.host.F)⁻¹
  let cg : ∀ v : HeightOneSpectrum (𝓞 D.host.F), v.adicCompletion D.host.F :=
    fun v => if P v then -(k : v.adicCompletion D.host.F) * evalV D.host.F v (T yv) else 1
  let dg : ∀ v : HeightOneSpectrum (𝓞 D.host.F), v.adicCompletion D.host.F :=
    fun v => if P v then (-(k : v.adicCompletion D.host.F) * evalV D.host.F v (T yv))⁻¹ else 1
  have heg : ∀ v, eg v ∈ v.adicCompletionIntegers D.host.F := fun v => by
    by_cases hv : P v <;> simp only [eg, hv, if_true, if_false] <;> [exact one_mem _; exact zero_mem _]
  have hfg : ∀ v, fg v ∈ v.adicCompletionIntegers D.host.F := fun v => by
    by_cases hv : P v <;> simp only [fg, hv, if_true, if_false]
    · exact zero_mem _
    · exact mem_of_val (by rw [map_inv₀, hMone v hv, inv_one])
  have hcg : ∀ v, cg v ∈ v.adicCompletionIntegers D.host.F := fun v => by
    by_cases hv : P v <;> simp only [cg, hv, if_true, if_false]
    · exact mem_of_val (hunit v hv).le
    · exact one_mem _
  have hdg : ∀ v, dg v ∈ v.adicCompletionIntegers D.host.F := fun v => by
    by_cases hv : P v <;> simp only [dg, hv, if_true, if_false]
    · exact mem_of_val (by rw [map_inv₀, hunit v hv, inv_one])
    · exact one_mem _
  set e := mkAf eg heg
  set f := mkAf fg hfg
  set c := mkAf cg hcg
  set d := mkAf dg hdg
  have hcd : c * d = 1 := GlobalTheory.SplitHeckeLabel.af_ext fun v => by
    rw [map_mul, map_one, evalV_mkAf, evalV_mkAf]
    by_cases hv : P v <;> simp only [cg, dg, hv, if_true, if_false, mul_one]
    refine mul_inv_cancel₀ fun h0 => ?_
    have := hunit v hv; rw [h0, map_zero] at this; exact zero_ne_one this
  have hef : e + (M : Af D.host.F) * f = 1 := GlobalTheory.SplitHeckeLabel.af_ext fun v => by
    rw [map_add, map_mul, map_one, map_natCast, evalV_mkAf, evalV_mkAf]
    by_cases hv : P v <;> simp only [eg, fg, hv, if_true, if_false, mul_zero, add_zero, zero_add]
    exact mul_inv_cancel₀ (hMne v hv)
  have hce : c = e * (-(k : Af D.host.F) * T yv) + (M : Af D.host.F) * f := GlobalTheory.SplitHeckeLabel.af_ext fun v => by
    rw [map_add, map_mul, map_mul, map_mul, map_neg, map_natCast, map_natCast, evalV_mkAf, evalV_mkAf, evalV_mkAf]
    by_cases hv : P v <;> simp only [eg, fg, cg, hv, if_true, if_false, mul_zero, add_zero, zero_add, one_mul, zero_mul]
    exact (mul_inv_cancel₀ (hMne v hv)).symm
  have E1 : ι e + (M : Af D.host.F ⊗[D.host.F] D.host.E) * ι f = 1 := by
    have := congrArg ι hef; rwa [map_add, map_mul, map_natCast, map_one] at this
  have E2 : ι c = ι e * (-(k : Af D.host.F ⊗[D.host.F] D.host.E) * ι (T yv)) + (M : Af D.host.F ⊗[D.host.F] D.host.E) * ι f := by
    rw [hce, map_add, map_mul, map_mul, map_mul, map_neg, map_natCast, map_natCast]
  have E4 : ι c * ι d = 1 := by rw [← map_mul, hcd, map_one]
  set W := ι e * (yv - (k : Af D.host.F ⊗[D.host.F] D.host.E) * (w * s)) + ι f * (yv - 1) with hW
  have hmain : yv - ι c = (M : Af D.host.F ⊗[D.host.F] D.host.E) * W := by
    have hM : (M : Af D.host.F ⊗[D.host.F] D.host.E) = 2 * (k : Af D.host.F ⊗[D.host.F] D.host.E) + 1 := by
      rw [hMdef]; push_cast; ring
    rw [hW]
    linear_combination (-1 : Af D.host.F ⊗[D.host.F] D.host.E) * E2 - yv * E1 - (k : Af D.host.F ⊗[D.host.F] D.host.E) * ι e * E3 - ι e * yv * hM
  have hWI : W ∈ intAE D := by
    rw [hW]
    refine add_mem (hmulI (hιI _ (mkAf_mem eg heg)) (sub_mem hyI (hmulI (hnI k) (hmulI hwI hsI))))
      (hmulI (hιI _ (mkAf_mem fg hfg)) (sub_mem hyI hoI))
  let b : (Af D.host.F)ˣ := ⟨d, c, by rw [mul_comm]; exact hcd, hcd⟩
  refine ⟨b, y * Units.map ι.toMonoidHom b, ?_, ?_, ?_, W * ι d, ?_, ?_⟩
  · rw [Units.val_mul, Units.coe_map]
    rfl
  · exact hmulI hyI (hιI _ (mkAf_mem dg hdg))
  · rw [mul_inv_rev, Units.val_mul, ← map_inv, Units.coe_map]
    exact hmulI (hιI _ (mkAf_mem cg hcg)) hyiI
  · exact hmulI hWI (hιI _ (mkAf_mem dg hdg))
  · rw [Units.val_mul, Units.coe_map, nsmul_eq_mul]
    show yv * ι d - 1 = _
    linear_combination ι d * hmain + E4

end GlobalTheory.UnitRootCong
