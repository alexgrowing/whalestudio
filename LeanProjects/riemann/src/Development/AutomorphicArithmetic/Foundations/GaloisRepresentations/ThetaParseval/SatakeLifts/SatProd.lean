import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.PairOfLiftAlt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSeriesSatakeParameters
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL UpperTheory.Gal.TP.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem tprod_ne_zero' {ι : Type} [Fintype ι] {X : ι → Type} [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)]
    (x : ∀ i, X i) (hx : ∀ i, x i ≠ 0) : PiTensorProduct.tprod ℂ x ≠ 0 := by
  have hl : ∀ i, ∃ l : Module.Dual ℂ (X i), l (x i) ≠ 0 := fun i => by
    by_contra hc
    push_neg at hc
    exact hx i ((Module.forall_dual_apply_eq_zero_iff ℂ (x i)).1 hc)
  choose l hl using hl
  intro h
  have h1 := congrArg (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap l)) h
  rw [PiTensorProduct.lift.tprod, map_zero] at h1
  simp only [MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply] at h1
  exact (Finset.prod_ne_zero_iff.2 fun i _ => hl i) h1

private theorem hasSat_pair {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {d : Fin 2 → ℕ}
    {X : Fin 2 → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    (π : ∀ a, Representation ℂ (GL (Fin (d a)) (w.adicCompletion K)) (X a))
    (hs : ∀ a, IsSmooth (π a)) (hi : ∀ a, (π a).IsIrreducible) (S : Fin 2 → Multiset ℂˣ)
    (hS : ∀ a, GlobalTheory.LFun.HasSatGL w (π a) (S a)) :
    GlobalTheory.LFun.HasSatGL w (prod₂ (π 0) (π 1)) (S 0 + S 1) := by
  obtain ⟨E⟩ := GlobalTheory.LocGL.nonempty_prod₂_equiv_multiProd (Fin.sum_univ_two d) π
  refine GlobalTheory.PrinSat.hasSatGL_of_equiv E ?_
  have hKO : ∀ m, GlobalTheory.LFun.KGL w m = KO (w.adicCompletion K) (Fin m) :=
    fun m => (SphCompletion.KO_completion w m).symm
  constructor
  · choose x hx using fun a => (hS a).exists_vec
    have hfix : ∀ g : Levi (w.adicCompletion K) (fun a => Fin (d a)), (∀ a, g a ∈ KO (w.adicCompletion K) (Fin (d a))) →
        piTensor π g (PiTensorProduct.tprod ℂ x) = PiTensorProduct.tprod ℂ x := fun g hg => by
      rw [piTensor_tprod]
      congr 1
      funext a
      have := (hx a).2.1
      rw [hKO] at this
      exact GlobalTheory.LGrp.mem_fixed.1 this _ (hg a)
    obtain ⟨f, hf, h1⟩ := GlobalTheory.SatInd.exists_fixed_apply_one (stdBlocks d (Fin.sum_univ_two d)) hfix
    refine (Submodule.ne_bot_iff _).2 ⟨f, ?_, ?_⟩
    · rw [hKO]; exact hf
    · rintro rfl
      exact tprod_ne_zero' x (fun a => (hx a).1) h1.symm
  · intro f hf h0
    obtain ⟨T, hT, hv⟩ := GlobalTheory.SatInd.exists_sat_multiProd (Fin.sum_univ_two d) hs hi hf h0
    have hTS : ∀ a, T a = S a := fun a => (hT a).unique (hS a)
    rw [Fin.sum_univ_two, hTS, hTS] at hv
    exact hv

private structure Bun (k : Type) [Field k] [TopologicalSpace k] where
  n : ℕ
  V : Type
  [acg : AddCommGroup V]
  [mod : Module ℂ V]
  ρ : Representation ℂ (GL (Fin n) k) V

attribute [local instance] Bun.acg Bun.mod

theorem UpperTheory.Gal.TP.Loc.satProd :
    UpperTheory.Gal.TP.Loc.SatProd := by
  intro K _ _ w r t V _ _ W _ _ σ τ hσ hσi hτ hτi B C hB hC
  let F : Fin 2 → Bun (w.adicCompletion K) := ![⟨r, V, σ⟩, ⟨t, W, τ⟩]
  refine hasSat_pair w (d := fun a => (F a).n) (X := fun a => (F a).V) (fun a => (F a).ρ) ?_ ?_ ![B, C] ?_
  · exact Fin.forall_fin_two.2 ⟨hσ, hτ⟩
  · exact Fin.forall_fin_two.2 ⟨hσi, hτi⟩
  · exact Fin.forall_fin_two.2 ⟨hB, hC⟩
