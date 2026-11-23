import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingPreservesSupportedUnitarySubgro
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CharConjFixedEqOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

noncomputable section
open IsDedekindDomain NumberField
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

namespace GlobalTheory.IwaFixed

open GlobalTheory.FinPlLoc

variable {D : D7}

theorem evalV_single_same (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v) :
    evalV F v (singleV F v y) = y := by
  classical
  exact RestrictedProduct.single_eq_same (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v y

theorem evalV_single_ne (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v)
    {w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) : evalV F w (singleV F v y) = 0 := by
  classical
  exact RestrictedProduct.single_eq_of_ne (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) y h

def intIn (D : D7) (v : Pl D) : v.adicCompletionIntegers D.host.F →+* Fv D.host.F v ⊗[D.host.F] D.host.E :=
  (algebraMap (Fv D.host.F v) (Fv D.host.F v ⊗[D.host.F] D.host.E)).comp (algebraMap _ (Fv D.host.F v))

theorem integral_compFin (v : Pl D) {z : Af D.host.F ⊗[D.host.F] D.host.E} (hz : z ∈ intAE D) :
    (intIn D v).IsIntegralElem (GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D v z) := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, o, rfl⟩ := hz
    have e : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D v (a ⊗ₜ[D.host.F] (o : D.host.E)) =
        intIn D v ⟨evalV D.host.F v a, ha v⟩ *
          (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Fv D.host.F v ⊗[D.host.F] D.host.E) (o : D.host.E) := by
      show Algebra.TensorProduct.map (evalV D.host.F v) (AlgHom.id _ _) (a ⊗ₜ[D.host.F] (o : D.host.E)) =
        (evalV D.host.F v a ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : Fv D.host.F v) ⊗ₜ[D.host.F] (o : D.host.E))
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rfl
    rw [e]
    refine RingHom.IsIntegralElem.mul _ (RingHom.isIntegralElem_map _) ?_
    obtain ⟨p, hp, hpo⟩ : IsIntegral ℤ (o : D.host.E) := o.2
    refine ⟨p.map (Int.castRingHom _), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have h := congrArg (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Fv D.host.F v ⊗[D.host.F] D.host.E).toRingHom hpo
    rw [Polynomial.hom_eval₂, map_zero] at h
    rw [RingHom.ext_int ((intIn D v).comp (Int.castRingHom _)) ((Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Fv D.host.F v ⊗[D.host.F] D.host.E).toRingHom.comp (algebraMap ℤ D.host.E))]
    exact h
  | zero => rw [map_zero]; exact RingHom.isIntegralElem_zero _
  | add z z' _ _ h h' => rw [map_add]; exact RingHom.IsIntegralElem.add _ h h'
  | neg z _ h => rw [map_neg]; exact RingHom.IsIntegralElem.neg _ h

theorem mem_int_of_integral (v : Pl D) (a : Fv D.host.F v)
    (h : (intIn D v).IsIntegralElem (a ⊗ₜ[D.host.F] (1 : D.host.E))) : a ∈ v.adicCompletionIntegers D.host.F := by
  obtain ⟨p, hp, hpa⟩ := h
  have hinj : Function.Injective (algebraMap (Fv D.host.F v) (Fv D.host.F v ⊗[D.host.F] D.host.E)) :=
    RingHom.injective _
  have hi : IsIntegral (v.adicCompletionIntegers D.host.F) a := by
    refine ⟨p, hp, hinj ?_⟩
    rw [Polynomial.hom_eval₂, map_zero]
    exact hpa
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
  rw [← hy]
  exact y.2

theorem exists_inv (v : Pl D) {x : AE D} (hx : x ∈ idAt D (· = v)) (u : (v.adicCompletionIntegers D.host.F)ˣ)
    (hu : compAt D v x = ((u : v.adicCompletionIntegers D.host.F) : Fv D.host.F v) ⊗ₜ[D.host.F] (1 : D.host.E)) :
    ∃ y ∈ intAt D (· = v), x * y = idem D (· = v) := by
  classical
  obtain ⟨c, hci, hc⟩ : ∃ c : Fv D.host.F v, c ∈ v.adicCompletionIntegers D.host.F ∧ (u.val.1 : Fv D.host.F v) * c = 1 :=
    ⟨u.inv.1, u.inv.2, congrArg Subtype.val u.val_inv⟩
  refine ⟨pairA D.host.F 0 (singleV D.host.F v c) ⊗ₜ[D.host.F] (1 : D.host.E), ⟨?_, ?_⟩, ?_⟩
  · exact pair_mem_idAt _ _ (fun w hw => evalV_single_ne _ v c hw) _
  · rw [finPart_pair]
    refine AddSubgroup.subset_closure ⟨singleV D.host.F v c, fun w => ?_, 1, rfl⟩
    by_cases hw : w = v
    · subst hw; rw [evalV_single_same]; exact hci
    · rw [evalV_single_ne _ v c hw]; exact zero_mem _
  · rw [← sub_eq_zero]
    apply eq_zero_of_comp
    · rw [map_sub, map_mul, infPart_of_idAt hx, infPart_of_idAt (idem_mem_idAt _), zero_mul, sub_zero]
    · intro w
      rw [map_sub, map_mul, compAt_idem]
      by_cases hw : w = v
      · subst hw
        rw [hu, compAt_pair, evalV_single_same, if_pos rfl, Algebra.TensorProduct.tmul_mul_tmul, mul_one, hc,
          ← Algebra.TensorProduct.one_def, sub_self]
      · rw [compAt_of_idAt hx hw, if_neg hw, zero_mul, sub_zero]

theorem fixed_unit_or : ∀ (D : D7) (v : Pl D) (ε : AE D), Tame D v → ε * ε = ε → cA D ε = ε → ε ∈ intAt D (· = v) →
    (∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) → ∀ x ∈ intAt D (· = v), cA D x = x →
    (∃ y ∈ intAt D (· = v), x * y = ε) ∨ (∃ y ∈ intAt D (· = v), (ε - x) * y = ε) := by
  intro D v ε _ _ _ hε hid x hx hfix
  classical
  have hεe : ε = idem D (· = v) := by
    have h1 := (hid _).1 (idem_mem_idAt (· = v))
    have h2 := (mem_idAt_iff (· = v) ε).1 hε.1
    rw [← h2, mul_comm, h1]
  subst hεe
  obtain ⟨b, hb⟩ := GlobalTheory.CharConjFixed.fixed_mem D x hfix
  have hcomp : compAt D v x = evalV D.host.F v (sndA D.host.F b) ⊗ₜ[D.host.F] (1 : D.host.E) := by
    rw [← hb]
    show Algebra.TensorProduct.map (evalV D.host.F v) (AlgHom.id _ _)
      (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id _ _) (b ⊗ₜ[D.host.F] (1 : D.host.E))) = _
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]
    rfl
  have hint : evalV D.host.F v (sndA D.host.F b) ∈ v.adicCompletionIntegers D.host.F := by
    apply mem_int_of_integral
    rw [← hcomp]
    exact integral_compFin v hx.2
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (⟨_, hint⟩ : v.adicCompletionIntegers D.host.F) with ⟨u, hu⟩ | ⟨u, hu⟩
  · left
    refine exists_inv v hx.1 u ?_
    rw [hu, hcomp]
  · right
    refine exists_inv v (sub_mem (idem_mem_idAt _) hx.1) u ?_
    rw [hu, map_sub, compAt_idem, if_pos rfl, hcomp, Algebra.TensorProduct.one_def, ← TensorProduct.sub_tmul]
    rfl

end GlobalTheory.IwaFixed

end
