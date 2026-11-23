import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsSecDegreeGe
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsSecFiniteUnit
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsSecRankSpecialize
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Assembly
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Imports
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PChowFormHomog
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace SecDegreeGe

variable {k R S : Type*} [CommRing k] [CommRing R] [CommRing S] {n e : ℕ}

theorem eval_specRest (ψ : k →+* R) (f : MvPolynomial (Fin (e + 1) × Fin n) k)
    (y : Vertical.Par e n → R) (v : Fin n → R) :
    eval v (Vertical.specRest ψ f y) =
      eval₂ ψ (fun ij => Fin.cases (motive := fun _ => R) (v ij.2)
        (fun i => y (.inl (i, ij.2))) ij.1) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [Vertical.specRest]
  | add p q hp hq => simp only [Vertical.specRest] at hp hq ⊢; simp [hp, hq]
  | mul_X p ij hp =>
    simp only [Vertical.specRest] at hp ⊢
    obtain ⟨i, j⟩ := ij
    induction i using Fin.cases with
    | zero => simp [hp]
    | succ i => simp [hp]

theorem map_eval_specRest (ψ : k →+* R) (φ : R →+* S) (f : MvPolynomial (Fin (e + 1) × Fin n) k)
    (y : Vertical.Par e n → R) :
    φ (eval (fun j => y (.inr j)) (Vertical.specRest ψ f y)) =
      eval (fun j => φ (y (.inr j))) (Vertical.specRest (φ.comp ψ) f (φ ∘ y)) := by
  rw [eval_specRest, eval_specRest, MvPolynomial.eval₂_comp_left]
  congr 1
  funext ⟨i, j⟩
  induction i using Fin.cases with
  | zero => rfl
  | succ i => rfl

end SecDegreeGe

open SecDegreeGe in

theorem SecDegreeGe.proof (hFin : SecFiniteUnit.Statement) (hSpec : SecRankSpecialize.Statement) :
    SecDegreeGe.Statement := by
  intro k E _ _ _ _ n e δ Q g y hQ hg hδ hne
  refine ⟨hFin k E n e δ Q g y hg hδ (isUnit_iff_ne_zero.2 hne), ?_⟩

  let 𝔭 : Ideal (MvPolynomial (Vertical.Par e n) E) := RingHom.ker (eval y)
  have : 𝔭.IsPrime := RingHom.ker_isPrime _
  let R := Localization.AtPrime 𝔭
  have : IsDomain R :=
    IsLocalization.isDomain_localization (Ideal.primeCompl_le_nonZeroDivisors 𝔭)
  let K := FractionRing (MvPolynomial (Vertical.Par e n) E)
  have : IsScalarTower k R K := IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply k (MvPolynomial (Vertical.Par e n) E) R,
      ← IsScalarTower.algebraMap_apply (MvPolynomial (Vertical.Par e n) E) R K,
      ← IsScalarTower.algebraMap_apply k (MvPolynomial (Vertical.Par e n) E) K]
  let π : R →+* E := IsLocalization.lift (M := 𝔭.primeCompl) (g := eval y)
    (fun s => isUnit_iff_ne_zero.2 fun h => s.2 (RingHom.mem_ker.2 h))
  have hπ : ∀ p, π (algebraMap (MvPolynomial (Vertical.Par e n) E) R p) = eval y p := fun p => IsLocalization.lift_eq _ _
  let _ : Algebra R E := π.toAlgebra
  let Y : Vertical.Par e n → R := fun p => algebraMap (MvPolynomial (Vertical.Par e n) E) R (X p)
  have hπY : algebraMap R E ∘ Y = y := funext fun p => by
    simp [RingHom.algebraMap_toAlgebra, Y, hπ]
  have hπk : (algebraMap R E).comp (algebraMap k R) = algebraMap k E := by
    ext a
    show π (algebraMap k R a) = algebraMap k E a
    rw [IsScalarTower.algebraMap_apply k (MvPolynomial (Vertical.Par e n) E) R, hπ,
      MvPolynomial.algebraMap_apply, eval_C]
  have hsurj : Function.Surjective (algebraMap R E) := fun a =>
    ⟨algebraMap (MvPolynomial (Vertical.Par e n) E) R (C a), by simp [RingHom.algebraMap_toAlgebra, hπ]⟩

  have hunit : IsUnit (eval (fun j => Y (.inr j)) (Vertical.specRest (algebraMap k R) g Y)) := by
    have h1 := map_eval_specRest (algebraMap k R) (algebraMap R E) g Y
    rw [hπk, hπY] at h1
    have hker : RingHom.ker (algebraMap R E) = IsLocalRing.maximalIdeal R := by
      haveI := RingHom.ker_isMaximal_of_surjective _ hsurj
      exact IsLocalRing.eq_maximalIdeal this
    by_contra hu
    have hm : eval (fun j => Y (.inr j)) (Vertical.specRest (algebraMap k R) g Y) ∈
        RingHom.ker (algebraMap R E) := by
      rw [hker]; exact (IsLocalRing.mem_maximalIdeal _).2 hu
    have hv : (fun j => algebraMap R E (Y (.inr j))) = fun j => y (.inr j) :=
      funext fun j => congrFun hπY (.inr j)
    rw [RingHom.mem_ker, h1, hv] at hm
    exact hne hm
  have hB := hFin k R n e δ Q g Y hg hδ hunit
  have hle := hSpec R K E n e (Q.map (MvPolynomial.map (algebraMap k R))) Y hsurj hB
  have hmapK : (Q.map (MvPolynomial.map (algebraMap k R))).map (MvPolynomial.map (algebraMap R K)) =
      Q.map (MvPolynomial.map (algebraMap k K)) := by
    rw [Ideal.map_map]
    congr 1
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_) <;>
      simp [← IsScalarTower.algebraMap_apply]
  have hmapE : (Q.map (MvPolynomial.map (algebraMap k R))).map (MvPolynomial.map (algebraMap R E)) =
      Q.map (MvPolynomial.map (algebraMap k E)) := by
    rw [Ideal.map_map]
    congr 1
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
    · simp only [RingHom.coe_comp, Function.comp_apply, map_C]
      exact congrArg C (RingHom.congr_fun hπk a)
    · simp
  rw [hmapK, hmapE, hπY] at hle

  have hind : AlgebraicIndependent k (algebraMap R K ∘ Y) := by
    have h0 : AlgebraicIndependent k (X : Vertical.Par e n → MvPolynomial (Vertical.Par e n) E) :=
      (MvPolynomial.algebraicIndependent_X _ _).restrictScalars
        (FaithfulSMul.algebraMap_injective k E)
    let f : MvPolynomial (Vertical.Par e n) E →ₐ[k] K :=
      (IsScalarTower.toAlgHom k R K).comp
        (IsScalarTower.toAlgHom k (MvPolynomial (Vertical.Par e n) E) R)
    have hinj : Function.Injective f :=
      (IsFractionRing.injective R K).comp
        (IsLocalization.injective R (Ideal.primeCompl_le_nonZeroDivisors 𝔭))
    have h1 : AlgebraicIndependent k (f ∘ X) := h0.map' hinj
    have heq : f ∘ X = algebraMap R K ∘ Y := funext fun p => rfl
    rwa [heq] at h1
  have hgen := Vertical.ChowSecDegree.proof
    (Vertical.ChowNormForm.proof
      (Vertical.ChowNormFormGeneric.proof Vertical.SecAlgFinite.full Vertical.GenSecDomain.full
        Vertical.GenSecSeparable.full Vertical.ChowSecDvd.full Vertical.NormFormIrreducible.full
        Vertical.GenChowIrreducible.full Vertical.NormFormDvd.full)
      Vertical.SecAlgFieldChange.full)
    Vertical.ChowFormHomog.full Vertical.NormFormEval.full k K n e Q g (algebraMap R K ∘ Y) hind hQ hg
  have hdeg : δ = chowDegree Q (e + 1) :=
    Vertical.chowForm_degree_unique (Nat.succ_pos e) hg hg hδ
      (Vertical.ChowFormHomog.full k n (e + 1) Q g hg)
  rw [hgen] at hle
  exact hdeg ▸ hle

end

end GroundTheory.Heights₂.Heights
