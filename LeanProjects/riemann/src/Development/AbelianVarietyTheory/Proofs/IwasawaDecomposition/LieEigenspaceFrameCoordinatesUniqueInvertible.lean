import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TriIff
import Formalism.LocalToGlobal.ProjectiveLattices.MulCMemSec
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.EigCoord

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LieLocBasis GlobalTheory.ShFam.EigLoc GlobalTheory.FlagBundle
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Chart (IsUnivChart sp)

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {R : Type} [CommRing R] {φ : c.F →+* R} {x : Sp R ⟶ Z.X} {n : ℕ}
  {xc : ∀ m : ℕ, sp (R₀ := R) (ReciprocityTheory.ChartRestriction.G.Chart.JetR R (Fin n) m) ⟶ (Over.pullback x).obj Z.t.G}

theorem exists_basis (hx : IsUnivChart _ n xc) (g : EigFrame Z φ x) (τ : E →+* ℂ) :
    ∃ B : Module.Basis (Fin (Dw.mult τ)) R (eig c φ hx τ), ∀ i, g.v τ i = vec Z.t x xc (B i) := by
  choose e he using fun i => vec_exists hx (g.v τ i) (g.tan τ i)
  have hm : ∀ i, e i ∈ eig c φ hx τ := fun i => (vec_eig_iff hx _ _).1 (by rw [← he i]; exact g.eig τ i)
  let b : Fin (Dw.mult τ) → eig c φ hx τ := fun i => ⟨e i, hm i⟩
  have key : ∀ w : eig c φ hx τ, ∃! a : Fin (Dw.mult τ) → R, ∑ j, a j • b j = w := fun w => by
    have h := g.basis τ (vec Z.t x xc w) (vec_tan hx _) ((vec_eig_iff hx _ _).2 w.2)
    rw [show g.v τ = fun j => vec Z.t x xc (e j) from funext he] at h
    simp only [comb_iff hx] at h
    refine (existsUnique_congr fun a => ?_).1 h
    rw [Subtype.ext_iff, eq_comm]
    simp [b]
  have li : LinearIndependent R b := Fintype.linearIndependent_iff.2 fun a ha i =>
    congrFun ((key 0).unique ha (show ∑ j, (0 : Fin (Dw.mult τ) → R) j • b j = 0 by simp)) i
  have sp' : ⊤ ≤ Submodule.span R (Set.range b) := fun w _ =>
    (Submodule.mem_span_range_iff_exists_fun R).2 (key w).exists
  exact ⟨Module.Basis.mk li sp', fun i => by rw [Module.Basis.mk_apply]; exact he i⟩

theorem exists_frame (hx : IsUnivChart _ n xc) (B : ∀ τ, Module.Basis (Fin (Dw.mult τ)) R (eig c φ hx τ)) :
    ∃ g : EigFrame Z φ x, ∀ τ i, g.v τ i = vec Z.t x xc (B τ i) := by
  refine ⟨⟨fun τ i => vec Z.t x xc (B τ i), fun τ i => vec_tan hx _, fun τ i => (vec_eig_iff hx _ _).2 (B τ i).2,
    fun τ w hw he => ?_⟩, fun _ _ => rfl⟩
  obtain ⟨cc, rfl⟩ := vec_exists hx w hw
  let v : eig c φ hx τ := ⟨cc, (vec_eig_iff hx _ _).1 he⟩
  have k : ∀ a, IsCombAtG Z.t x (fun i => vec Z.t x xc (B τ i)) a (vec Z.t x xc cc) ↔ (B τ).equivFun v = a := fun a => by
    rw [comb_iff hx, ← LinearEquiv.eq_symm_apply, Module.Basis.equivFun_symm_apply, Subtype.ext_iff]
    simp [v]
  simp only [k]
  exact existsUnique_eq'

theorem exists_basis_of_isUnit {M ι : Type} [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]
    (B : Module.Basis ι R M) (A : Matrix ι ι R) (h : IsUnit A.det) :
    ∃ B' : Module.Basis ι R M, ∀ i, B' i = ∑ j, A i j • B j := by
  refine ⟨B.map (Matrix.toLinearEquiv B A.transpose (by rwa [Matrix.det_transpose])), fun i => ?_⟩
  simp [Matrix.toLin_self]

theorem isUnit_det_of_basis {M ι : Type} [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]
    (B B' : Module.Basis ι R M) (A : Matrix ι ι R) (h : ∀ i, B' i = ∑ j, A i j • B j) : IsUnit A.det := by
  have e : A = (B.toMatrix B').transpose := by
    ext i j
    rw [Matrix.transpose_apply, Module.Basis.toMatrix_apply, h i, Module.Basis.repr_sum_self]
  rw [e, Matrix.det_transpose]
  exact B.isUnit_det B'

end GlobalTheory.ShFam.EigCoord

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
  GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle GlobalTheory.ShFam.EigLoc GlobalTheory.ShFam.EigCoord GlobalTheory.LieLocBasis in

theorem GlobalTheory.ShFam.EigCoord.coord_spec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (R : Type) [CommRing R] (φ : c.F →+* R) (x : Sp R ⟶ Z.X) (f : EigFrame Z φ x) (R' : Type) [CommRing R'] (φ' : c.F →+* R') (x' : Sp R' ⟶ Z.X) (ψ : R →+* R'), IsLocalRing R' → f.Stable → x' = spMap ψ ≫ x → φ' = ψ.comp φ → (∀ g : EigFrame Z φ' x', (∃! A : Mat Dw.mult R', f.Coord ψ g A) ∧ ∀ A, f.Coord ψ g A → ∀ τ, IsUnit (A τ).det) ∧ ∀ A : Mat Dw.mult R', (∀ τ, IsUnit (A τ).det) → ∃ g : EigFrame Z φ' x', f.Coord ψ g A := by
  intro E _ _ _ H Dw l Xo c O _ β Z R _ φ x f R' _ φ' x' ψ _ hf hx' hφ'
  subst hx' hφ'
  obtain ⟨g₀, hg₀⟩ := hf R' ψ
  obtain ⟨n, xc, hx⟩ := exists_chart Z.t (spMap ψ ≫ x)
  choose B₀ hB₀ using exists_basis hx g₀
  have hv : ∀ τ, (fun k => spMap (dualMap ψ) ≫ f.v τ k) = g₀.v τ := fun τ => funext fun k => (hg₀ τ k).symm
  have key : ∀ (g : EigFrame Z (ψ.comp φ) (spMap ψ ≫ x))
      (B : ∀ τ, Module.Basis (Fin (Dw.mult τ)) R' (eig c (ψ.comp φ) hx τ)),
      (∀ τ i, g.v τ i = vec Z.t _ xc (B τ i)) → ∀ A : Mat Dw.mult R',
        f.Coord ψ g A ↔ ∀ τ i, B τ i = ∑ j, A τ i j • B₀ τ j := fun g B hB A => by
    simp only [EigFrame.Coord, true_and]
    refine forall_congr' fun τ => forall_congr' fun i => ?_
    rw [hv, hB, show g₀.v τ = fun j => vec Z.t _ xc (B₀ τ j) from funext (hB₀ τ), comb_iff hx, Subtype.ext_iff]
    simp
  refine ⟨fun g => ⟨?_, fun A hA τ => ?_⟩, fun A hA => ?_⟩
  · choose A hA hu using fun τ i => g₀.basis τ (g.v τ i) (g.tan τ i) (g.eig τ i)
    refine ⟨A, ⟨rfl, rfl, fun τ i => by rw [hv]; exact hA τ i⟩, fun A' hA' => ?_⟩
    funext τ i
    exact hu τ i _ (by have := hA'.2.2 τ i; rwa [hv] at this)
  · choose B hB using exists_basis hx g
    exact isUnit_det_of_basis (B₀ τ) (B τ) (A τ) ((key g B hB A).1 hA τ)
  · choose B hB using fun τ => exists_basis_of_isUnit (B₀ τ) (A τ) (hA τ)
    obtain ⟨g, hg⟩ := exists_frame hx B
    exact ⟨g, (key g B hg A).2 hB⟩
