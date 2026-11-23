import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.EllFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.CasComm
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ArchimedeanCompact.OneTmulMemCenter
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CapCommuteRtInfGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasInfCharInfCharOfCommute
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

namespace UpperTheory.V.Cj.H.CasimirOperatorShift

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

private theorem comm_of_zalg {z o : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) (ho : ∀ τ u, Commute (cap τ u) o) :
    Commute z o := by
  refine Algebra.adjoin_induction (p := fun x _ => Commute x o) ?_ (fun r => Algebra.commutes r _)
    (fun _ _ _ _ hx hy => hx.add_left hy) (fun _ _ _ _ hx hy => hx.mul_left hy) hz
  rintro _ ⟨τ, u, rfl⟩
  exact ho τ u

private theorem uC_sh (r : ℝ) (X : Lie E a) : Cm.uC E a (shift (Cm.ιC E a) r X) = shift (lie E a) r X := by
  rw [shift_apply, shift_apply, map_add, Cm.uC_ιC, ← algebraMap_smul ℂ (r * ell E a X) (1 : Cm.UC E a), map_smul,
    map_one, algebraMap_smul]

private theorem cas_mem {n : ℕ} {e : Fin n → Herm E a} (he : IsFrame e) (r : ℝ) :
    cas (shift (lie E a) r) e ∈ Zalg E a := by
  have hL : IsLieHom (shift (Cm.ιC E a) r) := (ellFacts E a).2.2.2 _ _ r Cm.isLieHom_ιC
  have hX : ∀ X, Commute (cas (shift (Cm.ιC E a) r) e) (Cm.ιC E a X) := fun X => by
    have h := casComm E a n e he _ _ hL X
    have h' : Cm.ιC E a X = shift (Cm.ιC E a) r X - (r * ell E a X) • 1 := by rw [shift_apply, add_sub_cancel_right]
    rw [h']
    exact h.sub_right ((Commute.one_right _).smul_right _)
  have hle : Algebra.adjoin ℂ {x : Cm.UC E a | ∃ τ i j, x = Cm.genC τ i j} ≤
      Subalgebra.centralizer ℂ {cas (shift (Cm.ιC E a) r) e} := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨τ, i, j, rfl⟩ _ rfl
    exact (((hX _).sub_right ((hX _).smul_right _)).smul_right _).eq
  rw [Cm.adjoin_genC] at hle
  rw [Cm.Zalg_eq_map]
  exact ⟨_, Subalgebra.mem_center_iff.2 fun x => (hle Algebra.mem_top _ rfl).symm,
    by simp only [cas, map_sum, map_sub, map_mul, uC_sh, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]⟩

private theorem cap_rt (τ : E →+* ℂ) (u : ℂ) (g : GA E a) : Commute (cap τ u) (rt E a g) := by
  rw [← infGL_mul_finGL g, map_mul]
  exact (GlobalTheory.CapAdInv.cap_commute_rt_infGL E a τ u _).mul_right (commute_cap_finRep τ u _)

private theorem sh_apply (r : ℝ) (X : Lie E a) (φ : Sm E a) :
    shift (lie E a) r X φ = lie E a X φ + ((r * ell E a X : ℝ) : ℂ) • φ := by
  rw [shift_apply]; rfl

end UpperTheory.V.Cj.H.CasimirOperatorShift

open UpperTheory.V.Cj.H.CasimirOperatorShift in
theorem UpperTheory.V.Cj.H.casOp :
    UpperTheory.V.Cj.H.CasOp := by
  intro E _ _ _ a n e he r c
  have hz := cas_mem he r
  have hc : ∀ o : Module.End ℂ (Sm E a), (∀ τ u, Commute (cap τ u) o) → Commute o (casA r c e) := fun o ho =>
    (comm_of_zalg hz ho).symm.sub_right ((Commute.one_right _).smul_right _)
  refine ⟨fun X => hc _ fun τ u => commute_cap_lie τ u X, fun g => hc _ fun τ u => cap_rt τ u g, fun N hN => ?_⟩
  have hs : ∀ X, ∀ φ ∈ N, shift (lie E a) r X φ ∈ N := fun X φ hφ => by
    rw [sh_apply]
    exact N.add_mem (hN X φ hφ) (N.smul_mem _ hφ)
  refine ⟨fun φ hφ => ?_, fun T hT φ hφ => ?_⟩
  · simp only [casA, cas, LinearMap.sub_apply, LinearMap.sum_apply, Module.End.mul_apply, LinearMap.smul_apply,
      Module.End.one_apply]
    exact N.sub_mem (N.sum_mem fun j _ => N.sub_mem (hs _ _ (hs _ _ hφ)) (hs _ _ (hs _ _ hφ))) (N.smul_mem _ hφ)
  · have ht : ∀ X, ∀ φ ∈ N, shift (lie E a) r X (T φ) = T (shift (lie E a) r X φ) := fun X φ hφ => by
      rw [sh_apply, sh_apply, hT.lie X φ hφ, map_add, map_smul]
    simp only [casA, cas, LinearMap.sub_apply, LinearMap.sum_apply, Module.End.mul_apply, LinearMap.smul_apply,
      Module.End.one_apply, map_sub, map_sum, map_smul]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ht _ _ hφ, ht _ _ (hs _ _ hφ), ht _ _ hφ, ht _ _ (hs _ _ hφ)]
