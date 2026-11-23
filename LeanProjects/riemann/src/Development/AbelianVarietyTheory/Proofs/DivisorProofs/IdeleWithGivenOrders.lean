import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCharEqValZpow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TmulMemLocId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuedCompW
open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnrEuler GlobalTheory.LocIdeal
open GlobalTheory.Doubling (absE)
open Formalism.L2.Host (aboveF)
open GlobalTheory.TateUnr

noncomputable section

namespace GlobalTheory.TateUnr

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_unif_above (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) :
    ∃ a : 𝓞 E, w.intValuation a = WithZero.exp (-1) ∧
      ∀ w' : HeightOneSpectrum (𝓞 E), w'.under (𝓞 F) = v → w' ≠ w → w'.intValuation a = 1 := by
  classical
  obtain ⟨π, hπ, hπ2⟩ : ∃ π ∈ w.asIdeal, π ∉ w.asIdeal ^ 2 := by
    have := Ideal.pow_right_strictAnti w.asIdeal w.ne_bot w.isPrime.ne_top (show 1 < 2 by norm_num)
    simp only [pow_one] at this
    obtain ⟨π, h1, h2⟩ := Set.exists_of_ssubset this
    exact ⟨π, h1, h2⟩
  let s : Finset (HeightOneSpectrum (𝓞 E)) := insert w (Formalism.L2.Host.finite_aboveF (L := E) F v).toFinset
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := s) (fun i => i.asIdeal)
    (fun i => if i = w then 2 else 1) (fun i _ => i.prime) (fun i _ j _ hij h => hij (HeightOneSpectrum.ext h))
    (fun i => if i.1 = w then π else 1)
  have hw := hy w (Finset.mem_insert_self _ _)
  simp only [if_pos rfl] at hw
  have hyw : y ∈ w.asIdeal := by
    have := Ideal.pow_le_self two_ne_zero hw
    simpa using w.asIdeal.add_mem this hπ
  have hyw2 : y ∉ w.asIdeal ^ 2 := fun h => hπ2 (by simpa using (w.asIdeal ^ 2).sub_mem h hw)
  refine ⟨y, ?_, fun w' hw' hne => ?_⟩
  · have h1 := (w.intValuation_le_pow_iff_mem y 1).2 (by simpa using hyw)
    have h2 : ¬ w.intValuation y ≤ WithZero.exp (-((2 : ℕ) : ℤ)) := fun h => hyw2 ((w.intValuation_le_pow_iff_mem y 2).1 h)
    have h0 : w.intValuation y ≠ 0 := by
      intro h; exact h2 (by rw [h]; exact zero_le')
    rw [← WithZero.exp_log h0] at h1 h2 ⊢
    rw [WithZero.exp_le_exp] at h1 h2
    congr 1
    push_cast at h1 h2
    omega
  · have h' := hy w' (Finset.mem_insert_of_mem ((Formalism.L2.Host.finite_aboveF (L := E) F v).mem_toFinset.2 hw'))
    simp only [if_neg hne, pow_one] at h'
    refine (HeightOneSpectrum.intValuation_eq_one_iff).mpr fun hyw' => ?_
    exact w'.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using w'.asIdeal.sub_mem hyw' h'))

open Classical in

theorem ordV_surjective (v : Pl F) (k : aboveF (L := E) F v → ℤ) : ∃ l : idelesAt E (evFin F v), ordV v l = k := by
  choose a ha ha' using fun w : aboveF (L := E) F v => exists_unif_above v w.1
  have ha0 : ∀ w, ((a w : 𝓞 E) : E) ≠ 0 := fun w h => by
    have h1 := ha w
    rw [show a w = 0 from by exact_mod_cast h, map_zero] at h1
    exact WithZero.exp_ne_zero h1.symm
  let c : Eˣ := ∏ w, (Units.mk0 _ (ha0 w)) ^ (k w)
  let x : (Fv F v ⊗[F] E)ˣ := Units.map (inclR (F := F) (Fv F v)).toMonoidHom c
  refine ⟨⟨GlobalTheory.Doubling.ideleAt F E v x, ideleAt_mem v x⟩, funext fun w => ?_⟩
  have hw : w.1.under (𝓞 F) = v := mem_aboveF.1 w.2
  have hcomp : ((compW hw ⟨GlobalTheory.Doubling.ideleAt F E v x, ideleAt_mem v x⟩ : (w.1.adicCompletion E)ˣ) : w.1.adicCompletion E) =
      algebraMap E _ (c : E) := by
    rw [compW_apply]
    have e : compFin F E v ((GlobalTheory.Doubling.ideleAt F E v x : (AE F E)ˣ) : AE F E) = (x : Fv F v ⊗[F] E) :=
      congrArg Units.val (GlobalTheory.Doubling.unitFin_ideleAt_self v x)
    rw [e]
    show toCompl hw ((1 : Fv F v) ⊗ₜ[F] (c : E)) = _
    rw [toCompl_tmul, map_one, one_mul]
  have hval : w.1.valuation E (c : E) = WithZero.exp (-k w) := by
    simp only [c, Units.coe_prod, Units.val_zpow_eq_zpow_val, Units.val_mk0, map_prod, map_zpow₀]
    rw [Finset.prod_eq_single w (fun b _ hb => ?_) (fun h => absurd (Finset.mem_univ w) h)]
    · rw [HeightOneSpectrum.valuation_of_algebraMap, ha, ← WithZero.exp_zsmul]
      congr 1; simp
    · rw [HeightOneSpectrum.valuation_of_algebraMap, ha' b w.1 hw (fun e => hb (Subtype.ext e.symm)), one_zpow]
  show ordW hw _ = k w
  rw [ordW, hcomp]
  show -WithZero.log (Valued.v (((c : E)) : w.1.adicCompletion E)) = _
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hval, WithZero.log_exp, neg_neg]

end GlobalTheory.TateUnr
