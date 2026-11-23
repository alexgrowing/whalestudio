import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianLinkMapAdditiveRationalEquivariant
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLineLinkGramSimilitudeBijective
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.LinkInvTheta

open GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule (ofAdj starAdj starAdj_ofAdj)

variable {D : D7}

theorem star_psi {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (a : AF D.host.F) : star (ψ a) = ψ (-a) := by
  have h1 : ‖ψ a‖ = 1 := hψ.1.2.1 a
  have h2 : ψ a * star (ψ a) = 1 := by
    rw [Complex.star_def, Complex.mul_conj', h1]; simp
  have h3 : ψ a * ψ (-a) = 1 := by rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have h0 : ψ a ≠ 0 := by intro h; rw [h, zero_mul] at h3; exact zero_ne_one h3
  exact mul_left_cancel₀ h0 (h2.trans h3.symm)

theorem map_starAdj_eq_zero {B : Type} [CommRing B] (φ : AE D →+* B) (hφ : ∀ z, φ z = 0 → φ (cA D z) = 0)
    (L S : HSp D) {x : WO L S} (hx : x.map φ = 0) : (starAdj L S x).map φ = 0 := by
  have h1 : (adj x).map φ = 0 := by
    funext i j
    exact hφ (x j i) (congrFun (congrFun hx j) i)
  have h2 := map_mul_eq_zero_right φ (giA L) (map_mul_eq_zero_left φ h1 (gA S))
  funext i j
  have h3 : φ ((giA L ⬝ (adj x ⬝ gA S) : Mx D L.rank S.rank) i j) = 0 := congrFun (congrFun h2 i) j
  show φ (incA D D.host.xi0 * (giA L ⬝ (adj x ⬝ gA S) : Mx D L.rank S.rank) i j) = 0
  rw [map_mul, h3, mul_zero]

theorem continuous_starAdj (L S : HSp D) : Continuous (starAdj L S) := by
  have h1 : Continuous fun x : WO L S => (adj x ⬝ gA S : Mx D L.rank S.rank) :=
    continuous_adj.matrix_mul continuous_const
  have h2 : Continuous fun x : WO L S => (giA L ⬝ (adj x ⬝ gA S) : Mx D L.rank S.rank) :=
    continuous_const.matrix_mul h1
  exact h2.const_smul (incA D D.host.xi0)

theorem starAdj_mem (L S : HSp D) {x : WO L S} (hx : x ∈ ratMx D S.rank L.rank) :
    starAdj L S x ∈ ratMx D L.rank S.rank := by
  obtain ⟨γ, hγ⟩ := mem_ratMx.1 hx
  rw [← hγ, starAdj, giA, gA, ← rat_conjTranspose, ← rat_mul, ← rat_mul, ← rat_smul]
  exact rat_mem _

theorem lnk_simil {L L' : HSp D} {ζ : Fin L.rank → D.host.E} {ζ' : Fin L'.rank → D.host.E} (h : IsLineVec L' ζ')
    (l : Lnk L ζ L' ζ') : l.τᴴ ⬝ (L.gram ⬝ l.τ) = (D.host.xi0 * star D.host.xi0) • L'.gram := by
  have e : star ζ' ⬝ᵥ (l.τᴴ ⬝ (L.gram ⬝ l.τ)) *ᵥ ζ' =
      star ζ' ⬝ᵥ ((D.host.xi0 * star D.host.xi0) • L'.gram) *ᵥ ζ' := by
    rw [← Matrix.mulVec_mulVec, dotProduct_mulVec, ← Matrix.star_mulVec, ← Matrix.mulVec_mulVec, l.map, Matrix.smul_mulVec,
      dotProduct_smul, smul_eq_mul, ← l.norm, star_neg, Matrix.mulVec_neg, neg_dotProduct_neg]
  have hu : Unique (Fin L'.rank) := by rw [h.1]; infer_instance
  have h2 := h.2
  simp only [dotProduct, Matrix.mulVec, Fintype.sum_unique] at e h2
  funext i j
  rw [Subsingleton.elim i default, Subsingleton.elim j default]
  have a : star ζ' default ≠ 0 := left_ne_zero_of_mul h2
  have b : ζ' default ≠ 0 := right_ne_zero_of_mul (right_ne_zero_of_mul h2)
  have c := mul_left_cancel₀ a e
  have c' := mul_right_cancel₀ b c
  exact c'

theorem link_inv_theta : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (L L' S : HSp D) (ζ : Fin L.rank → D.host.E) (ζ' : Fin L'.rank → D.host.E), IsLineVec L ζ → IsLineVec L' ζ' → ∀ l : Lnk L ζ L' ζ', l.τᴴ ⬝ (L.gram ⬝ l.τ) = (D.host.xi0 * star D.host.xi0) • L'.gram ∧ ∀ Φ₀, IsThetaFunO ψ S L' Φ₀ → ∃ Ξ, IsThetaFunO ψ L S Ξ ∧ Φ₀ = fun w => star (Ξ (l.κ S w)) := by
  intro D ψ hψ L L' S ζ ζ' hL hL' l
  have hτ := lnk_simil hL' l
  refine ⟨hτ, fun Φ₀ hΦ => ?_⟩
  have hτ' : l.τᴴ ⬝ (L.gram ⬝ l.τ) = (((1 : ℤ) : D.host.E) * (D.host.xi0 * star D.host.xi0)) • L'.gram := by
    rw [Int.cast_one, one_mul]; exact hτ
  obtain ⟨hadd, -, -, -, hsym, -⟩ := GlobalTheory.LinkKappa.kappa_props D L L' S l.τ 1 hτ' (l.κ S) (fun _ => rfl)
  have hH : ∀ w w', symplOH L S (l.κ S w) (l.κ S w') = -symplOH S L' w w' := fun w w' => by
    unfold symplOH; rw [hsym]; push_cast; ring
  have hτ0 : l.τ ≠ 0 := by
    intro h0
    have e := l.map
    rw [h0, Matrix.zero_mulVec] at e
    have hz : ζ = 0 := neg_eq_zero.mp e.symm
    apply hL.2
    rw [hz]; simp
  obtain ⟨σ, hστ, hτσ⟩ := GlobalTheory.Unf.LinkGram.exists_inv_of_rank_one hL.1 hL'.1 l.τ hτ0
  let g : WO L S → WO S L' := fun x => (rat σ : Mx D L'.rank L.rank) ⬝ starAdj L S x
  have hgk : ∀ w, g (l.κ S w) = w := by
    intro w
    show (rat σ : Mx D L'.rank L.rank) ⬝ starAdj L S (l.κ S w) = w
    rw [Lnk.κ, starAdj_ofAdj, ← Matrix.mul_assoc, ← rat_mul, hστ, rat_one, Matrix.one_mul]
  have hkg : ∀ x, l.κ S (g x) = x := by
    intro x
    show l.κ S ((rat σ : Mx D L'.rank L.rank) ⬝ starAdj L S x) = x
    rw [Lnk.κ, ← Matrix.mul_assoc, ← rat_mul, hτσ, rat_one, Matrix.one_mul, GlobalTheory.Unf.LinkGram.ofAdj_starAdj]
  have gadd : ∀ x y, g (x + y) = g x + g y := fun x y => by
    conv_lhs => rw [← hkg x, ← hkg y, ← hadd, hgk]
  have gH : ∀ x y, symplOH S L' (g x) (g y) = -symplOH L S x y := fun x y => by
    conv_rhs => rw [← hkg x, ← hkg y, hH, neg_neg]
  have gcont : Continuous g := continuous_const.matrix_mul (continuous_starAdj L S)
  have grat : ∀ x ∈ ratMx D S.rank L.rank, g x ∈ ratMx D L'.rank S.rank := fun x hx =>
    ratMx_mul (rat_mem σ) (starAdj_mem L S hx)
  have gfin : ∀ x : WO L S, x.map (finPart D) = 0 → (g x).map (finPart D) = 0 := fun x h =>
    map_mul_eq_zero_right (finPart D) _
      (map_starAdj_eq_zero (finPart D) (fun z hz => by rw [GlobalTheory.LinkKappa.finPart_conj, hz, map_zero]) L S h)
  have ginf : ∀ x : WO L S, x.map (infPart D) = 0 → (g x).map (infPart D) = 0 := fun x h =>
    map_mul_eq_zero_right (infPart D) _
      (map_starAdj_eq_zero (infPart D) (fun z hz => by rw [GlobalTheory.LinkKappa.infPart_conj, hz, map_zero]) L S h)
  let A : WO L S →+ WO S L' := AddMonoidHom.mk' g gadd
  refine ⟨fun x => star (Φ₀ (g x)), ⟨fun γ x => ?_, ?_, continuous_star.comp (hΦ.cont.comp gcont), fun k M h1 h2 x => ?_⟩, ?_⟩
  · obtain ⟨γ', hγ'⟩ := grat (ratW S L γ) ⟨γ, rfl⟩
    have e : g (ratW S L γ) = ratW L' S γ' := hγ'.symm
    show star (Φ₀ (g (ratW S L γ + x))) = ψ (-(symplOH L S (ratW S L γ) x)) * star (Φ₀ (g x))
    rw [gadd, e, hΦ.quasi, star_mul', star_psi hψ, ← e, gH, neg_neg]
  · obtain ⟨U, hU, h⟩ := hΦ.level
    refine ⟨U.comap A, hU.preimage gcont, fun u hu h0 => ?_⟩
    funext x
    have e := congrFun (h _ hu (ginf u h0)) (g x)
    unfold heisO at e ⊢
    show ψ (symplOH L S x u) * star (Φ₀ (g (x + u))) = star (Φ₀ (g x))
    rw [← e, star_mul', star_psi hψ]
    show ψ (symplOH L S x u) * star (Φ₀ (g (x + u))) = ψ (-symplOH S L' (g x) (g u)) * star (Φ₀ (g x + g u))
    rw [gH, neg_neg, gadd]
  · have h3 : ∀ t, (A (M t)).map (finPart D) = 0 := fun t => gfin (M t) (h2 t)
    have := hΦ.smooth k (A.comp M) (gcont.comp h1) h3 (g x)
    have heq : (fun t => Φ₀ (g (x + M t))) = fun t => Φ₀ (g x + A (M t)) :=
      funext fun t => congrArg Φ₀ (gadd x (M t))
    have h4 := (congrArg (ContDiff ℝ _) heq).mpr this
    exact Complex.conjCLE.contDiff.comp h4
  · funext w
    show Φ₀ w = star (star (Φ₀ (g (l.κ S w))))
    rw [hgk, star_star]
end GlobalTheory.LinkInvTheta
end
