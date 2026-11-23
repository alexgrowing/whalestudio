import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqOfConjEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtOfFrameEqOfPointEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrthonormalFramesLieCoordinatesUnitaryStatement

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LieBase
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst GlobalTheory.FramePairGram GlobalTheory.TrueCx Formalism.DegreeFormula Formalism.MJ GlobalTheory.HodgeDomain GlobalTheory.HodgeOnDomain

namespace GlobalTheory.HodgeGenUnf

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {σ : c.F →+* ℂ} {r : ℕ}

theorem relab_mem {U : Formalism.L2.PjFree.Unf Xo c σ r} (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U)
    (k : U.Comp) (τ : GlobalTheory.AllWt.Psi H) : Formalism.L2.PjFree.relab c σ τ.1 ∈ (U.X k).Ψ :=
  ((hU.2.1 k).2 _).2 (((GlobalTheory.Relab.relab_good E H l c σ hσ).2.1 τ.1).2 τ.2)

theorem comb_unitary {U : Formalism.L2.PjFree.Unf Xo c σ r} (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U)
    (k : U.Comp) (x x₁ : (U.X k).dom) (hx : IsOrth (U.X k) x.1) (hx₁ : IsOrth (U.X k) x₁.1)
    (e : (U.un k x₁).x = (U.un k x).x) (τ : E →+* ℂ) (T : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ)
    (hT : ∀ b, Formalism.L2.Pj.IsCombAt (U.un k x).x ((U.un k x).u τ)
      (show Fin (Dw.mult τ) → CAt σ from fun b' => T b' b) ((U.un k x₁).u τ b)) :
    Tᴴ * T = 1 :=
  GlobalTheory.T.orthonormalFrames_lie_coordinates_unitary hσ hU k x x₁ hx hx₁ e τ T hT

theorem uniformisation_component_eq_of_same_modulusPoint {U : Formalism.L2.PjFree.Unf Xo c σ r} (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U)
    {k k' : U.Comp} (x : (U.X k).dom) (x' : (U.X k').dom) (h : (U.un k x).x = (U.un k' x').x) : k' = k := by
  obtain ⟨b, -, -, hb, t, ht⟩ := GlobalTheory.PointOfFrames.exists_frBor U hU hσ k x (U.un k' x') h
  obtain ⟨g0, -, b', -, e⟩ := (hU.2.2.2.1 k k' ⟨_, hb⟩ x').1 ⟨t, ht⟩
  exact congrArg Sigma.fst e

theorem unitary_of_single {Uf : ∀ σ' : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ' r}
    (hE : ∀ σ', σ' ≠ σ → IsEmpty (Uf σ').Comp) (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf (Uf σ))
    {y : CxPts (genStr Z) σ} {f g : EigFrame Z σ (y.1 ≫ genι Z)} (hf : IsHodgeFrame Uf y f) (hg : IsHodgeFrame Uf y g)
    (τ : E →+* ℂ) : (f.co g τ)ᴴ * f.co g τ = 1 := by
  classical
  obtain ⟨ψ, σ', k, x, h1, h2, h3, h4, h5, h6⟩ := hf
  obtain ⟨ψ₁, σ₁, k₁, x₁, g1, g2, g3, g4, g5, g6⟩ := hg
  have e1 : σ = σ' := by_contra fun h => (hE σ' (Ne.symm h)).false k
  have e2 : σ = σ₁ := by_contra fun h => (hE σ₁ (Ne.symm h)).false k₁
  subst e1 e2
  have hid : ∀ {ψ : ℂ →+* ℂ}, (ψ = RingHom.id ℂ ∨ ψ = starRingEnd ℂ) → σ = ψ.comp σ → ψ = RingHom.id ℂ := by
    intro ψ h h'
    rcases h with rfl | rfl
    · rfl
    · exact (not_good_conj c (σ := σ) hσ (h' ▸ hσ)).elim
  obtain rfl := hid h1 h2
  obtain rfl := hid g1 g2
  have hx : (cxPt Z ((Uf σ).un k x)).1 ≫ genι Z = spMap (RingHom.id ℂ) ≫ y.1 ≫ genι Z := by rw [h5, Category.assoc]
  obtain ⟨g', hg'⟩ := g.exists_isMap (RingHom.id ℂ) h2 hx
  have e := x_eq_of_cxPt (g5.trans h5.symm)
  obtain rfl : k = k₁ := (uniformisation_component_eq_of_same_modulusPoint hσ hU x x₁ e.symm).symm
  have key := comb_unitary hσ hU k x x₁ h4 g4 e τ _ (isCombAt_co e (fun τ i => (hg' τ i).trans (g6 τ i).symm) τ)
  rw [h6.co τ hg' hx] at key
  convert key using 2 <;> ext <;> simp

theorem gram_eq_of_single {Uf : ∀ σ' : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ' r}
    (hE : ∀ σ', σ' ≠ σ → IsEmpty (Uf σ').Comp) (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf (Uf σ))
    {b : ℝ} {hb : 0 < b} {G₀ : EigMet Z σ} {y : CxPts (genStr Z) σ} {f : EigFrame Z σ (y.1 ≫ genι Z)}
    (hf : IsHodgeFrame Uf y f) (g : EigFrame Z σ (y.1 ≫ genι Z)) (τ : E →+* ℂ) :
    (EigMet.hodge Uf b hb G₀).gram y g τ = (b : ℂ) • ((f.co g τ)ᴴ * f.co g τ) := by
  have h : ∃ f, IsHodgeFrame Uf y f := ⟨f, hf⟩
  refine (dif_pos h).trans (congrArg _ ?_)
  rw [← h.choose.co_mul f g, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ _ (f.co g τ),
    unitary_of_single hE hσ hU h.choose_spec hf, Matrix.one_mul]

theorem unfFam_empty (U : Formalism.L2.PjFree.Unf Xo c σ r) (σ' : c.F →+* ℂ) (h : σ' ≠ σ) :
    IsEmpty (unfFam U σ').Comp := by
  unfold unfFam
  rw [dif_neg (Ne.symm h)]
  exact inferInstanceAs (IsEmpty Empty)

theorem unfFam_self (U : Formalism.L2.PjFree.Unf Xo c σ r) : unfFam U σ = U := dif_pos rfl

theorem isHodgeFrame_of_eq {Uf : ∀ σ' : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ' r} {U : Formalism.L2.PjFree.Unf Xo c σ r}
    (hq : Uf σ = U) (hσ : Formalism.L2.PjFree.GoodEmb c σ) {k : U.Comp} {x : (U.X k).dom} (hx : IsOrth (U.X k) x.1) :
    IsHodgeFrame (Z := Z) Uf (cxPt Z (U.un k x)) (cxFrame Z (U.un k x)) := by
  subst hq
  exact isHodgeFrame_cxFrame hσ hx

variable (Z) in

theorem hodgeMet_gram_orth {U : Formalism.L2.PjFree.Unf Xo c σ r} (hσ : Formalism.L2.PjFree.GoodEmb c σ)
    (hU : Formalism.L2.PjFree.IsUnf U) {k : U.Comp} {x : (U.X k).dom} (hx : IsOrth (U.X k) x.1) (τ : E →+* ℂ) :
    (hodgeMet Z U).gram (cxPt Z (U.un k x)) (cxFrame Z (U.un k x)) τ = ((2 * Real.pi : ℝ) : ℂ) • 1 := by
  rw [hodgeMet, gram_eq_of_single (unfFam_empty U) hσ ((unfFam_self U).symm ▸ hU)
    (isHodgeFrame_of_eq (unfFam_self U) hσ hx), EigFrame.co_self, conjTranspose_one, Matrix.mul_one]

end GlobalTheory.HodgeGenUnf

namespace GlobalTheory.HodgeGenUnf

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {σ : c.F →+* ℂ}

def letter {U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)} (hσ : Formalism.L2.PjFree.GoodEmb c σ)
    (hU : Formalism.L2.PjFree.IsUnf U) (k : U.Comp) (τ : GlobalTheory.AllWt.Psi H) : (U.X k).Ψ :=
  ⟨Formalism.L2.PjFree.relab c σ τ.1, relab_mem hσ hU k τ⟩

theorem mult_psi (τ : GlobalTheory.AllWt.Psi H) : Dw.mult τ.1 = Dw.p := if_pos τ.2

variable (Z) in

theorem hodgeMet_gram_frame {U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)} (hσ : Formalism.L2.PjFree.GoodEmb c σ)
    (hU : Formalism.L2.PjFree.IsUnf U) (k : U.Comp) (f : (U.X k).dom) (τ : GlobalTheory.AllWt.Psi H) (τ' : (U.X k).Ψ)
    (hτ : τ'.1 = Formalism.L2.PjFree.relab c σ τ.1) (hj : Dw.p ≤ Dw.p + Dw.q) :
    ((hodgeMet Z U).gram (cxPt Z (U.un k f)) (cxFrame Z (U.un k f)) τ.1).submatrix
        (Fin.cast (mult_psi τ).symm) (Fin.cast (mult_psi τ).symm) =
      ((2 * Real.pi : ℝ) : ℂ) • ((coW (U.X k) hj f.1 τ')ᴴ * (hP (moeb (frameCo (U.X k) hj f.1 τ') 0))⁻¹ *
        coW (U.X k) hj f.1 τ') := by
  have hp : (U.X k).p0 = Dw.p + Dw.q - Dw.p := by rw [(hU.2.1 k).1]; omega
  obtain ⟨x1, h1, b, hb, ef⟩ := ortho_holds (Dw.p + Dw.q) (U.X k) f.1 f.2
  let f' : (U.X k).dom := ⟨x1, KU.orth_dom _ h1⟩
  have hz : domPt (U.X k) hj (Equiv.refl (U.X k).Ψ) f.1 = domPt (U.X k) hj (Equiv.refl (U.X k).Ψ) f'.1 := by
    show domPt _ _ _ f.1 = domPt _ _ _ x1
    rw [ef, domPt_rmul _ _ _ hb]
  have hmo : ∀ ρ : (U.X k).Ψ, moeb (frameCo (U.X k) hj f.1 ρ) 0 = moeb (frameCo (U.X k) hj f'.1 ρ) 0 :=
    fun ρ => congrFun hz ρ
  have h1' := fun ρ => PointWell.block_of_moeb_eq _ hj hp f.2 f'.2 ρ (hmo ρ)
  have h2' := fun ρ => PointWell.block_of_moeb_eq _ hj hp f'.2 f.2 ρ (hmo ρ).symm
  have hx : (U.un k f).x = (U.un k f').x := PointWell.pt_eq_of_block hU hσ k f f' h1' h2'
  have hg : (hodgeMet Z U).gram (cxPt Z (U.un k f)) (cxFrame Z (U.un k f)) τ.1 =
      (Matrix.of fun b i : Fin (Dw.mult τ.1) => coef (U.X k) f.1 f'.1 (Formalism.L2.PjFree.relab c σ τ.1) b i)ᴴ *
        (hodgeMet Z U).gram (cxPt Z (U.un k f')) (cxFrame Z (U.un k f')) τ.1 *
        Matrix.of fun b i : Fin (Dw.mult τ.1) => coef (U.X k) f.1 f'.1 (Formalism.L2.PjFree.relab c σ τ.1) b i :=
    eigGram_of_comb (hodgeMet Z U) _ _ hx τ.1 _ (fun i => lie_comb_of_block hU hσ k f f' h1' h2' τ.1 i)
  rw [hg, hodgeMet_gram_orth Z hσ hU (x := f') h1, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, smul_submatrix_sq]
  set e := Fin.cast (mult_psi τ).symm
  have he : Function.Bijective e := (finCongr (mult_psi τ).symm).bijective
  rw [Matrix.submatrix_mul _ _ _ _ _ he, ← conjTranspose_submatrix]
  have hKe : (Matrix.of fun b i : Fin (Dw.mult τ.1) =>
      coef (U.X k) f.1 f'.1 (Formalism.L2.PjFree.relab c σ τ.1) b i).submatrix e e =
      Matrix.of fun b i : Fin Dw.p => coef (U.X k) f.1 f'.1 τ'.1 b i := by
    ext b i; rw [hτ]; rfl
  obtain ⟨hco1, -⟩ := hodge_co (U.X k) hj hp h1 τ'
  rw [hKe, coef_eq_coW_change (U.X k) hj hp f.2 f'.2 τ' (hmo τ'), hmo τ',
    eq_of_conj_eq_one (isUnit_coW _ _ hp f'.2 _) hco1]
  congr 1
  simp only [conjTranspose_mul, Matrix.mul_assoc]

end GlobalTheory.HodgeGenUnf
