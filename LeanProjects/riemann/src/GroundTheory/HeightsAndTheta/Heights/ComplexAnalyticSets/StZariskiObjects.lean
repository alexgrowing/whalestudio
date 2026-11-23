import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StZariskiAnalyticNormality
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology Filter

noncomputable section

def holGermValue {σ : Type} [Fintype σ] (w : σ → ℂ) : holGerms w →+* ℂ :=
  (Germ.valueRingHom (x := w)).comp (holGerms w).subtype

def holGermPointIdeal {σ : Type} [Fintype σ] (w : σ → ℂ) : Ideal (holGerms w) :=
  RingHom.ker (holGermValue w)

def polyPointIdeal {σ : Type} [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) :
    Ideal (MvPolynomial σ ℂ ⧸ I) :=
  (RingHom.ker (MvPolynomial.eval w)).map (Ideal.Quotient.mk I)

def germQuotPointIdeal {σ : Type} [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) :
    Ideal (holGerms w ⧸ I.map (polyGerm w)) :=
  (holGermPointIdeal w).map (Ideal.Quotient.mk _)

theorem holGermValue_polyGerm {σ : Type} [Fintype σ] (w : σ → ℂ) (q : MvPolynomial σ ℂ) :
    holGermValue w (polyGerm w q) = eval w q := rfl

theorem polyPointIdeal_isMaximal {σ : Type} [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ)
    (hw : w ∈ zeroSetIn I) : (polyPointIdeal I w).IsMaximal := by
  have hmax : (RingHom.ker (MvPolynomial.eval w)).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ fun a => ⟨C a, eval_C a⟩
  have hle : I ≤ RingHom.ker (MvPolynomial.eval w) := fun q hq => RingHom.mem_ker.2 (hw q hq)
  refine (Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective hmax).resolve_left ?_
  intro htop
  have h := Ideal.comap_map_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective (RingHom.ker (MvPolynomial.eval w))
  rw [htop, Ideal.comap_top, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.2 hle] at h
  exact hmax.ne_top h.symm

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
