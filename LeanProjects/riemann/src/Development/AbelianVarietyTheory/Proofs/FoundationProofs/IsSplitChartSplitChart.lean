import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOne

noncomputable section

namespace GlobalTheory.LFun.SplitTie

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.LFun.SplitChart
open Formalism.MainNotions.SchurIrreducible (IsSplit)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
  {n : ℕ} {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} {V : Type} [AddCommGroup V] [Module ℂ V]

section Transport

def glEquiv {A B : Type} [CommRing A] [CommRing B] (n : ℕ) (ψ : A ≃+* B) : GL (Fin n) A ≃* GL (Fin n) B :=
  Units.mapEquiv ψ.mapMatrix.toMulEquiv

variable {ψ : Fv F v ≃+* w.adicCompletion E}

theorem mem_KGL_iff (h3 : ∀ a, Valued.v (ψ a) = Valued.v a) (x : GL (Fin n) (Fv F v)) :
    x ∈ KGL v n ↔ glEquiv n ψ x ∈ KGL w n := (bc_mem_KGL_iff h3).symm

theorem Tj_comp (h3 : ∀ a, Valued.v (ψ a) = Valued.v a) (ϖ : Fv F v) (j : ℕ) :
    Tj ℂ n (Ov E w) (ψ ϖ) j ∘ glEquiv n ψ = Tj ℂ n (Ov F v) ϖ j := by
  have hd : diagJ n (ψ ϖ) j = ψ.mapMatrix (diagJ n ϖ j) := by
    rw [RingEquiv.mapMatrix_apply, diagJ, diagJ, Matrix.diagonal_map (map_zero _)]
    congr 1
    funext i
    split_ifs <;> simp
  have hv : ∀ x : GL (Fin n) (Fv F v), (glEquiv n ψ x).1 = ψ.mapMatrix x.1 := fun _ => rfl
  refine (funext fun g => (Set.indicator_comp_right (g := 1) (glEquiv n ψ)).symm).trans (congrArg (Set.indicator · 1) ?_)
  ext g
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, (glEquiv n ψ).surjective.exists, ← mem_KGL_iff h3, hd, hv, ← map_mul,
    EmbeddingLike.apply_eq_iff_eq]

theorem isSatVecGL_comp_symm (h3 : ∀ a, Valued.v (ψ a) = Valued.v a) (hq : qV E w = qV F v)
    (ρ : Representation ℂ (GL (Fin n) (Fv F v)) V) (x : V) (B : Multiset ℂˣ) :
    IsSatVecGL w (ρ.comp (glEquiv n ψ).symm.toMonoidHom) x B ↔ IsSatVecGL v ρ x B := by
  unfold IsSatVecGL
  rw [mem_fixed_comp_symm (glEquiv n ψ) (mem_KGL_iff h3), hq, ψ.surjective.forall]
  refine and_congr_right fun _ => and_congr_right fun hx => and_congr_right fun _ => forall_congr' fun ϖ => ?_
  have hu : IsUnifV E w (ψ ϖ) ↔ IsUnifV F v ϖ := by unfold IsUnifV; rw [h3]
  rw [hu]
  refine forall_congr' fun hϖ => forall₂_congr fun j _ => ?_
  rw [heckeVec_comp_symm (glEquiv n ψ) (mem_KGL_iff h3) (Tj_mem_hecke (hu.2 hϖ) j).1 hx, Tj_comp h3]

end Transport

variable [Algebra F E] {σ : E →ₐ[F] E} {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)}

section Compl

variable (τ : E →ₐ[F] Fv F v) (hw : (splitPrime τ).under (𝓞 F) = v)

theorem complMap_bijective : Function.Bijective (complMap hw) := by
  obtain ⟨ψ, h1, -⟩ := exists_equiv_complMap τ hw
  exact (funext h1 : ⇑ψ = complMap hw) ▸ ψ.bijective

theorem valued_complMap (a : Fv F v) : Valued.v (complMap hw a) = Valued.v a := by
  obtain ⟨ψ, h1, -, h3, -⟩ := exists_equiv_complMap τ hw
  rw [← h1, h3]

theorem complMap_apply_emb (x : E) : complMap hw (τ x) = algebraMap E _ x := by
  obtain ⟨ψ, h1, h2, -⟩ := exists_equiv_complMap τ hw
  rw [← h1, h2]

def complEquiv : Fv F v ≃+* (splitPrime τ).adicCompletion E :=
  RingEquiv.ofBijective (complMap hw) (complMap_bijective τ hw)

theorem complEquiv_apply (a : Fv F v) : complEquiv τ hw a = complMap hw a := rfl

theorem toCompl_eq_complMap (y : Fv F v ⊗[F] E) : toCompl hw y = complMap hw (splitProj τ y) :=
  toCompl_eq (ψ := complEquiv τ hw) (fun _ => rfl) (complMap_apply_emb τ hw) y

theorem qV_splitPrime : qV E (splitPrime τ) = qV F v := absNorm_splitPrime τ

end Compl

variable (h : IsCMExt F E σ) (hJ : IsHermND σ J) (τ : E →ₐ[F] Fv F v) (hw : (splitPrime τ).under (𝓞 F) = v)
  (β : GL (Fin n) (Fv F v))

def splitChart : GLoc σ J v ≃* GL (Fin n) ((splitPrime τ).adicCompletion E) :=
  (splitEquivIn h hJ τ β).toMulEquiv.trans (glEquiv n (complEquiv τ hw))

variable {τ β}

variable (hL : IsSelfDualAt σ J L v) (hβ : IsSplitBasis τ L β)
include hL hβ

end GlobalTheory.LFun.SplitTie

end
