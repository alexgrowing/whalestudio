import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValAtOfUnder

noncomputable section

open scoped TensorProduct NNReal nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnrEuler
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)

namespace GlobalTheory.UnrTate

open Classical in

theorem exists_uniformizer_unit_off {E : Type} [Field E] [NumberField E] (S : Finset (HeightOneSpectrum (𝓞 E)))
    (w₀ : HeightOneSpectrum (𝓞 E)) :
    ∃ y : 𝓞 E, ∀ w ∈ S, w.intValuation y = WithZero.exp (if w = w₀ then (-1 : ℤ) else 0) := by
  classical
  obtain ⟨π, hπ⟩ := w₀.intValuation_exists_uniformizer
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S)
    (fun w : HeightOneSpectrum (𝓞 E) => w.asIdeal) (fun _ => 2) (fun w _ => w.prime)
    (fun w _ w' _ h h' => h (HeightOneSpectrum.ext h')) (fun w => if w.1 = w₀ then π else 1)
  refine ⟨y, fun w hw => ?_⟩
  have h := hy w hw
  have h2 : w.intValuation (y - if w = w₀ then π else 1) ≤ WithZero.exp (-((2 : ℕ) : ℤ)) :=
    (w.intValuation_le_pow_iff_mem _ 2).2 h
  have h3 : w.intValuation (if w = w₀ then π else 1) = WithZero.exp (if w = w₀ then (-1 : ℤ) else 0) := by
    split_ifs with hh
    · subst hh; exact hπ
    · simp
  have h4 : w.intValuation (y - if w = w₀ then π else 1) < w.intValuation (if w = w₀ then π else 1) := by
    refine lt_of_le_of_lt h2 ?_
    rw [h3, WithZero.exp_lt_exp]
    split_ifs <;> norm_num
  rw [← h3]
  exact Valuation.map_eq_of_sub_lt _ h4

theorem exists_valuation_eq_exp {E : Type} [Field E] [NumberField E] (S : Finset (HeightOneSpectrum (𝓞 E)))
    (k : HeightOneSpectrum (𝓞 E) → ℤ) :
    ∃ b : Eˣ, ∀ w ∈ S, w.valuation E (b : E) = WithZero.exp (-k w) := by
  classical
  choose y hy using exists_uniformizer_unit_off S
  have key : ∀ w ∈ S, w.valuation E (∏ u ∈ S, (algebraMap (𝓞 E) E (y u)) ^ k u) = WithZero.exp (-k w) := by
    intro w hw
    rw [map_prod, Finset.prod_eq_single w]
    · rw [map_zpow₀, HeightOneSpectrum.valuation_of_algebraMap, hy w w hw, if_pos rfl, ← WithZero.exp_zsmul]
      simp
    · intro u _ hne
      rw [map_zpow₀, HeightOneSpectrum.valuation_of_algebraMap, hy u w hw, if_neg (Ne.symm hne)]
      simp
    · intro h; exact absurd hw h
  by_cases h0 : (∏ u ∈ S, (algebraMap (𝓞 E) E (y u)) ^ k u) = 0
  · refine ⟨1, fun w hw => ?_⟩
    have := key w hw
    rw [h0, map_zero] at this
    exact absurd this.symm WithZero.exp_ne_zero
  · exact ⟨Units.mk0 _ h0, key⟩

theorem exists_unit_ordAt_eq :
    ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl F) (k : HeightOneSpectrum (𝓞 E) → ℤ), ∃ x : (Fv F v ⊗[F] E)ˣ, ∀ w ∈ Formalism.L2.Host.aboveF (L := E) F v, GlobalTheory.UnrTate.ordAt v w x = k w := by
  intro F E _ _ _ _ _ v k
  obtain ⟨b, hb⟩ := exists_valuation_eq_exp (Formalism.L2.Host.aboveF (L := E) F v) k
  refine ⟨Units.map (Algebra.TensorProduct.includeRight : E →ₐ[F] Fv F v ⊗[F] E).toMonoidHom b, fun w hw => ?_⟩
  have h := valAt_one_tmul v w (GlobalTheory.LFun.mem_aboveF.1 hw) b
  have h' : Valued.v (algebraMap E (w.adicCompletion E) b) = w.valuation E (b : E) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w (b : E)
  rw [valAt_eq_exp, h', hb w hw] at h
  exact neg_injective (WithZero.exp_injective h)

end GlobalTheory.UnrTate

end
