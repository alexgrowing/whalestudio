import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ApplyIdeleMapInfIdeleNegOne
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.MuProps

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

omit [NumberField E] [IsCMField E] in
theorem atEmb_emb (w : InfinitePlace E) (z : ℂ) : atEmb w.embedding z = Pi.single w z := by
  unfold atEmb; simp [InfinitePlace.mk_embedding]

theorem chiInf_expU_single {μ : HChar E} {e : InfinitePlace E → ℤ} (h : IsMu μ e) (v : InfinitePlace E) (z : ℂ) :
    ((chiInf μ (expU (Pi.single v z)) : ℂˣ) : ℂ) =
      Complex.exp ((e v : ℂ) / 2 * z + (-(e v : ℂ) / 2) * starRingEnd ℂ z) := by
  rw [h.2.2.2.2, Finset.prod_eq_single v]
  · change (Complex.exp ((Pi.single v z : Cinf E) v) / ((‖Complex.exp ((Pi.single v z : Cinf E) v)‖ : ℝ) : ℂ)) ^ e v = _
    rw [Pi.single_eq_same, Complex.norm_exp, Complex.ofReal_exp, ← Complex.exp_sub, ← Complex.exp_int_mul]
    congr 1
    have := Complex.add_conj z
    push_cast at this
    linear_combination ((e v : ℂ) / 2) * this
  · intro u _ hu
    change (Complex.exp ((Pi.single v z : Cinf E) u) / ((‖Complex.exp ((Pi.single v z : Cinf E) u)‖ : ℝ) : ℂ)) ^ e u = 1
    rw [Pi.single_eq_of_ne hu]
    simp
  · simp

theorem expo_emb {μ : HChar E} {e : InfinitePlace E → ℤ} (h : IsMu μ e) (v : InfinitePlace E) :
    expo μ v.embedding = (e v : ℂ) / 2 :=
  expo_eq_of_exp μ v.embedding _ (-(e v : ℂ) / 2) fun z => by
    rw [atEmb_emb]; exact chiInf_expU_single h v z

theorem expo_conj {μ : HChar E} {e : InfinitePlace E → ℤ} (h : IsMu μ e) (v : InfinitePlace E) :
    expo μ (ComplexEmbedding.conjugate v.embedding) = -(e v : ℂ) / 2 :=
  expo_eq_of_exp μ _ _ ((e v : ℂ) / 2) fun z => by
    rw [atEmb_conj, atEmb_emb, chiInf_expU_single h v]
    congr 1
    simp only [Complex.conj_conj]
    ring

theorem dchi_single {μ : HChar E} {e : InfinitePlace E → ℤ} (h : IsMu μ e) (v : InfinitePlace E) (w : ℂ) :
    dchi μ (Pi.single v w) = (w.im : ℂ) * dchi μ (Pi.single v Complex.I) := by
  have h1 := expo_emb h v
  have h2 := expo_conj h v
  simp only [expo, atEmb_conj, atEmb_emb, map_one, Complex.conj_I, Pi.single_neg, map_neg] at h1 h2
  have hd1 : dchi μ (Pi.single v 1) = 0 := by linear_combination h1 + h2
  rw [← atEmb_emb, atEmb_eq, map_add, map_smul, map_smul, atEmb_emb, atEmb_emb, hd1]
  rw [smul_zero, zero_add, Complex.real_smul]

theorem dchi_neg_star {μ : HChar E} {e : InfinitePlace E → ℤ} (h : IsMu μ e) (z : Cinf E) :
    dchi μ (-star z) = dchi μ z := by
  conv_lhs => rw [← Finset.univ_sum_single (-star z)]
  conv_rhs => rw [← Finset.univ_sum_single z]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [dchi_single h v, dchi_single h v (z v), Pi.neg_apply, Pi.star_apply, Complex.neg_im, Complex.star_def, Complex.conj_im, neg_neg]

theorem finId_conjFin (u : (Af E)ˣ) :
    finId E (Units.map (conjFin (IsCMField.complexConj E).toRingEquiv).toMonoidHom u) =
      Units.map (conjAd E).toMonoidHom (finId E u) := by
  refine Units.ext (Prod.ext ?_ ?_)
  · change (1 : InfiniteAdeleRing E) - 0 + 0 = (infEq E) (starRingEnd (Cinf E) ((infEq E).symm ((1 : InfiniteAdeleRing E) - 0 + 0)))
    simp
  · change (1 : Af E) - 1 + conjFin (IsCMField.complexConj E).toRingEquiv (u : Af E) =
      conjFin (IsCMField.complexConj E).toRingEquiv ((1 : Af E) - 1 + (u : Af E))
    simp

theorem mu_mul_conj {μ : HChar E} {e : InfinitePlace E → ℤ} (h : IsMu μ e) (x : Neutral.B1.Ideles E) :
    μ.1 x * μ.1 (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj (maximalRealSubfield E) E x) = 1 := by
  rw [← map_mul, ← GlobalTheory.GalOfCusp.ideleMap_ideleNorm, h.2.1]
  have := congrArg (fun c : HChar E => c.1 x) (GlobalTheory.GalOfCusp.compNorm_quadChar E)
  exact this

theorem thetaInv {μ : HChar E} {e : InfinitePlace E → ℤ} (h : IsMu μ e) (a : ℕ) : ThetaInv a μ := by
  refine CG.thetaInv_of (fun u => ?_) (dchi_neg_star h)
  rw [map_inv, finId_conjFin, ← GlobalTheory.PolChar.ideleConj_eq, map_inv]
  have := mu_mul_conj h (finId E u)
  exact inv_eq_of_mul_eq_one_left this

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (μ : HChar E) (e : InfinitePlace E → ℤ), IsMu μ e → (∀ a, ThetaInv a μ) ∧ (∀ v : InfinitePlace E, expo μ v.embedding = (e v : ℂ) / 2) ∧ ∀ v : InfinitePlace E, expo μ (ComplexEmbedding.conjugate v.embedding) = -(e v : ℂ) / 2 :=
  fun _ _ _ _ _ _ _ h => ⟨thetaInv h, expo_emb h, expo_conj h⟩

end GlobalTheory.BCT.MuProps
