import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanQ
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.PairLine

section Cont

variable {G : Type} [Group G] [TopologicalSpace G] {LL : Type} [Field LL] [TopologicalSpace LL]
  [IsTopologicalRing LL]

theorem cont_form {V : Type} [AddCommGroup V] [Module LL V] [FiniteDimensional LL V]
    [TopologicalSpace V] [IsModuleTopology LL V] (f : V →ₗ[LL] LL) : Continuous f :=
  IsModuleTopology.continuous_of_linearMap f

theorem cont_act {V : Type} [AddCommGroup V] [Module LL V] [FiniteDimensional LL V]
    [TopologicalSpace V] [IsModuleTopology LL V] (ρ : Representation LL G V)
    (hρ : ∀ x, Continuous fun g => ρ g x) : Continuous fun p : G × V => ρ p.1 p.2 := by
  haveI : ContinuousSMul LL V := IsModuleTopology.toContinuousSMul LL V
  haveI : ContinuousAdd V := IsModuleTopology.toContinuousAdd LL V
  let b := Module.finBasis LL V
  have h : (fun p : G × V => ρ p.1 p.2) = fun p => ∑ i, b.repr p.2 i • ρ p.1 (b i) := by
    funext p
    conv_lhs => rw [← b.sum_repr p.2]
    simp only [map_sum, map_smul]
  rw [h]
  refine continuous_finset_sum _ fun i _ => ?_
  exact ((cont_form ((Finsupp.lapply i).comp b.repr.toLinearMap)).comp continuous_snd).smul
    ((hρ (b i)).comp continuous_fst)

theorem cont_bil {V V' : Type} [AddCommGroup V] [Module LL V] [FiniteDimensional LL V]
    [TopologicalSpace V] [IsModuleTopology LL V] [AddCommGroup V'] [Module LL V']
    [FiniteDimensional LL V'] [TopologicalSpace V'] [IsModuleTopology LL V']
    (m : V →ₗ[LL] V' →ₗ[LL] LL) : Continuous fun q : V × V' => m q.1 q.2 := by
  let b := Module.finBasis LL V
  have h : (fun q : V × V' => m q.1 q.2) = fun q => ∑ i, b.repr q.1 i * m (b i) q.2 := by
    funext q
    conv_lhs => rw [← b.sum_repr q.1]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul]
  rw [h]
  refine continuous_finset_sum _ fun i _ => ?_
  exact ((cont_form ((Finsupp.lapply i).comp b.repr.toLinearMap)).comp continuous_fst).mul
    ((cont_form (m (b i))).comp continuous_snd)

end Cont

theorem exists_pair : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDual1 (P.PD K) A.ρ A'.ρ m → ∃ β : ↥(continuousCocycles A.ρ) →ₗ[LL] ↥(continuousCocycles A'.ρ) →ₗ[LL] LL, ∀ a b, β a b = 0 ↔ CobL (P.PD K) (cupL A'.ρ m a.1 b.1) := by
  intro hT l _ P K LL _ _ _ O _ _ hO A A' m hm
  obtain ⟨Z, inv, hZ, hinv⟩ := GlobalTheory.InvLine.exists_inv hT l P K LL O hO
  haveI : IsTopologicalRing LL := hO.2.2.2.1
  have hmem : ∀ (a : ↥(continuousCocycles A.ρ)) (b : ↥(continuousCocycles A'.ρ)), cupL A'.ρ m a.1 b.1 ∈ Z := by
    intro a b
    obtain ⟨ha, ha'⟩ : Continuous a.1 ∧ ∀ g h, a.1 (g * h) = a.1 g + A.ρ g (a.1 h) := a.2
    obtain ⟨hb, hb'⟩ : Continuous b.1 ∧ ∀ g h, b.1 (g * h) = b.1 g + A'.ρ g (b.1 h) := b.2
    rw [hZ]
    refine ⟨?_, fun g h k => ?_⟩
    · have h1 : Continuous fun p : ↥(GK K) × ↥(GK K) => A'.ρ p.1 (b.1 p.2) :=
        (cont_act A'.ρ A'.cont).comp (continuous_fst.prodMk (hb.comp continuous_snd))
      exact (cont_bil m).comp ((ha.comp continuous_fst).prodMk h1)
    · simp only [cupL]
      rw [← hm.1 g (a.1 h) (A'.ρ h (b.1 k)), ha', hb', map_mul, Module.End.mul_apply]
      simp only [map_add, LinearMap.add_apply]
      ring
  refine ⟨LinearMap.mk₂ LL (fun a b => inv ⟨cupL A'.ρ m a.1 b.1, hmem a b⟩) ?_ ?_ ?_ ?_,
    fun a b => ?_⟩
  · intro a a' b
    rw [← map_add]; congr 1; apply Subtype.ext; funext p
    simp [cupL]
  · intro c a b
    rw [← map_smul]; congr 1; apply Subtype.ext; funext p
    simp [cupL]
  · intro a b b'
    rw [← map_add]; congr 1; apply Subtype.ext; funext p
    simp [cupL]
  · intro c a b
    rw [← map_smul]; congr 1; apply Subtype.ext; funext p
    simp [cupL]
  · rw [LinearMap.mk₂_apply]
    exact hinv _

end GlobalTheory.PairLine
