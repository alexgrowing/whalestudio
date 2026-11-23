import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianLinkMapAdditiveRationalEquivariant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianAdjointLawsStandardCharacter
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLineLinkGramSimilitudeBijective

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.KapVac

variable {D : D7}

theorem lnk_simil {L : HSp D} {ζ ζ' : Fin L.rank → D.host.E} (h : IsLineVec L ζ') (l : Lnk L ζ L ζ') :
    l.τᴴ ⬝ (L.gram ⬝ l.τ) = (((1 : ℤ) : D.host.E) * (D.host.xi0 * star D.host.xi0)) • L.gram := by
  rw [Int.cast_one, one_mul]
  have e : star ζ' ⬝ᵥ (l.τᴴ ⬝ (L.gram ⬝ l.τ)) *ᵥ ζ' =
      star ζ' ⬝ᵥ ((D.host.xi0 * star D.host.xi0) • L.gram) *ᵥ ζ' := by
    rw [← Matrix.mulVec_mulVec, dotProduct_mulVec, ← Matrix.star_mulVec, ← Matrix.mulVec_mulVec, l.map, Matrix.smul_mulVec,
      dotProduct_smul, smul_eq_mul, ← l.norm, star_neg, Matrix.mulVec_neg, neg_dotProduct_neg]
  have hu : Unique (Fin L.rank) := by rw [h.1]; infer_instance
  have h2 := h.2
  simp only [dotProduct, Matrix.mulVec, Fintype.sum_unique] at e h2
  funext i j
  rw [Subsingleton.elim i default, Subsingleton.elim j default]
  have a : star ζ' default ≠ 0 := left_ne_zero_of_mul h2
  have b : ζ' default ≠ 0 := right_ne_zero_of_mul (right_ne_zero_of_mul h2)
  have c := mul_left_cancel₀ a e
  exact mul_right_cancel₀ b c

theorem lnk_tau_ne {L : HSp D} {ζ ζ' : Fin L.rank → D.host.E} (h : IsLineVec L ζ') (l : Lnk L ζ L ζ') : l.τ ≠ 0 := by
  intro h0
  have e := l.map
  rw [h0, Matrix.zero_mulVec] at e
  have hz : ζ = 0 := neg_eq_zero.mp e.symm
  have n : D.host.xi0 * star D.host.xi0 * (star ζ' ⬝ᵥ L.gram *ᵥ ζ') = 0 := by
    rw [← l.norm, hz]; simp
  rcases mul_eq_zero.1 n with h1 | h1
  · rcases mul_eq_zero.1 h1 with h3 | h3
    · exact GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D h3
    · exact GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D (star_eq_zero.1 h3)
  · exact h.2 h1

theorem kap_surj {L : HSp D} {ζ ζ' : Fin L.rank → D.host.E} (h : IsLineVec L ζ') (l : Lnk L ζ L ζ') (S : HSp D) :
    Function.Surjective (l.κ S) := by
  obtain ⟨σ, _, hτσ⟩ := GlobalTheory.Unf.LinkGram.exists_inv_of_rank_one h.1 h.1 l.τ (lnk_tau_ne h l)
  intro x
  refine ⟨(rat σ : Mx D L.rank L.rank) ⬝ GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj L S x, ?_⟩
  rw [Lnk.κ, ← Matrix.mul_assoc, ← rat_mul, hτσ, rat_one, Matrix.one_mul, GlobalTheory.Unf.LinkGram.ofAdj_starAdj]

theorem kap_add {L : HSp D} {ζ ζ' : Fin L.rank → D.host.E} (h : IsLineVec L ζ') (l : Lnk L ζ L ζ') (S : HSp D)
    (v w : WO S L) : l.κ S (v + w) = l.κ S v + l.κ S w :=
  (GlobalTheory.LinkKappa.kappa_props D L L S l.τ 1 (lnk_simil h l) (l.κ S) (fun _ => rfl)).1 v w

theorem kap_sympl {L : HSp D} {ζ ζ' : Fin L.rank → D.host.E} (h : IsLineVec L ζ') (l : Lnk L ζ L ζ') (S : HSp D)
    (v w : WO S L) : symplOH L S (l.κ S v) (l.κ S w) = -symplOH S L v w := by
  have e := (GlobalTheory.LinkKappa.kappa_props D L L S l.τ 1 (lnk_simil h l) (l.κ S) (fun _ => rfl)).2.2.2.2.1 v w
  unfold symplOH
  rw [e, Int.cast_one, one_mul, mul_neg]

theorem kap_heis (ψ : AddChar (AF D.host.F) ℂ) (hψ : ∀ x, ‖ψ x‖ = 1) {L : HSp D} {ζ ζ' : Fin L.rank → D.host.E}
    (h : IsLineVec L ζ') (l : Lnk L ζ L ζ') (S : HSp D) (Ξ : WO L S → ℂ) (w' : WO S L)
    (hw : heisO ψ S L w' (fun w => star (Ξ (l.κ S w))) = fun w => star (Ξ (l.κ S w))) :
    heisO ψ L S (l.κ S w') Ξ = Ξ := by
  funext x
  obtain ⟨v, rfl⟩ := kap_surj h l S x
  have e := congrFun hw v
  simp only [heisO] at e
  have e2 := congrArg (starRingEnd ℂ) e
  rw [map_mul, GlobalTheory.AdjLawPf.conj_psi ψ hψ] at e2
  simp only [starRingEnd_apply, star_star] at e2
  simp only [heisO]
  rw [kap_sympl h l, ← kap_add h l]
  exact e2

theorem half_mul_left {m n k : ℕ} {e : AE D} (M : Mx D m n) {x : Mx D n k} (hx : IsHalf e x) : IsHalf e (M ⬝ x) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [mul_left_comm, hx]

theorem half_mul_right {m n k : ℕ} {e : AE D} {x : Mx D m n} (hx : IsHalf e x) (M : Mx D n k) : IsHalf e (x ⬝ M) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [← mul_assoc, hx]

theorem half_smul {m n : ℕ} {e : AE D} (c : AE D) {x : Mx D m n} (hx : IsHalf e x) : IsHalf e (c • x) := by
  intro i j
  rw [Matrix.smul_apply, smul_eq_mul, mul_left_comm, hx]

theorem half_adj {m n : ℕ} {e : AE D} {x : Mx D m n} (hx : IsHalf e x) : IsHalf (cA D e) (adj x) := by
  intro i j
  show cA D e * cA D (x j i) = cA D (x j i)
  rw [← map_mul, hx]

theorem split_conj {e : AE D} (he : IsSplitIdem D e) : IsSplitIdem D (cA D e) := by
  obtain ⟨h1, h2, v, ε, hv, h3⟩ := he
  exact ⟨by rw [← map_mul, h1], by rw [GlobalTheory.DualPairCheck.cA_cA, mul_comm, h2], v, ε, hv,
    by rw [GlobalTheory.DualPairCheck.cA_cA, add_comm, h3]⟩

theorem kap_half {L : HSp D} {ζ ζ' : Fin L.rank → D.host.E} (h : IsLineVec L ζ') (l : Lnk L ζ L ζ') (S : HSp D)
    {e : AE D} {w : WO S L} (hh : IsHalf e (l.κ S w)) : IsHalf (cA D e) w := by
  obtain ⟨σ, hστ, _⟩ := GlobalTheory.Unf.LinkGram.exists_inv_of_rank_one h.1 h.1 l.τ (lnk_tau_ne h l)
  have h1 : IsHalf (cA D e) (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj L S (l.κ S w)) :=
    half_smul _ (half_mul_left _ (half_mul_right (half_adj hh) _))
  rw [Lnk.κ, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj_ofAdj] at h1
  have h2 := half_mul_left (rat σ : Mx D L.rank L.rank) h1
  rwa [← Matrix.mul_assoc, ← rat_mul, hστ, rat_one, Matrix.one_mul] at h2

theorem kappa_vac : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), (∀ x, ‖ψ x‖ = 1) → ∀ (L S : HSp D) (ζ ζ' : Fin L.rank → D.host.E), IsLineVec L ζ' → ∀ (l : Lnk L ζ L ζ') (Λ : AddSubgroup (WO S L)) (Ξ : WO L S → ℂ), IsLatVac (heisO ψ S L) Λ (fun w => star (Ξ (l.κ S w))) → ∀ w ∈ Λ, heisO ψ L S (2 • l.κ S w) Ξ = Ξ ∧ ∀ e, IsSplitIdem D e → IsHalf e (l.κ S w) → heisO ψ L S (l.κ S w) Ξ = Ξ := by
  intro D ψ hψ L S ζ ζ' h l Λ Ξ hv w hw
  refine ⟨?_, fun e he hh => ?_⟩
  · have e2 : (2 • l.κ S w : WO L S) = l.κ S (2 • w) := by rw [two_nsmul, two_nsmul, kap_add h l]
    rw [e2]
    exact kap_heis ψ hψ h l S Ξ _ (hv.1 w hw)
  · exact kap_heis ψ hψ h l S Ξ w (hv.2 (cA D e) (split_conj he) w hw (kap_half h l S hh))

end GlobalTheory.KapVac
