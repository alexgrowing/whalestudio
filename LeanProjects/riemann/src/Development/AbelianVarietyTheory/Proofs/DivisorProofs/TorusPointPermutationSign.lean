import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
  IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum polydisc defCoord cWt)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorusRenumber

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}

def permCLE (σ : Equiv.Perm (Fin g)) : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ) :=
  (LinearEquiv.funCongrLeft ℂ ℂ σ).toContinuousLinearEquiv

@[simp] theorem permCLE_apply (σ : Equiv.Perm (Fin g)) (w : Fin g → ℂ) : permCLE σ w = w ∘ σ := rfl

def pre (u : HolUnif A L g) (T : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ)) : HolUnif A L g where
  ex z := u.ex (T z)
  ex_add z w := by rw [map_add, u.ex_add]
  ex_onto y := by
    obtain ⟨x, rfl⟩ := u.ex_onto y
    exact ⟨T.symm x, by simp⟩
  Λ := u.Λ.comap (((T : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)).restrictScalars ℤ)
  ker z := by rw [u.ker]; rfl
  discrete := by
    haveI := u.discrete
    exact DiscreteTopology.of_continuous_injective
      (f := fun x : u.Λ.comap (((T : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)).restrictScalars ℤ)
        ↦ (⟨T x, x.2⟩ : u.Λ))
      (by fun_prop) (fun x y h ↦ Subtype.ext (T.injective (congrArg Subtype.val h)))
  full := by
    have h1 : ((u.Λ.comap (((T : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)).restrictScalars ℤ) :
        Submodule ℤ (Fin g → ℂ)) : Set (Fin g → ℂ)) =
        (T.symm.toLinearEquiv.restrictScalars ℝ : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ)) '' (u.Λ : Set (Fin g → ℂ)) := by
      ext x
      simp only [SetLike.mem_coe, Submodule.mem_comap, Set.mem_image]
      constructor
      · intro hx; exact ⟨T x, hx, by simp⟩
      · rintro ⟨y, hy, rfl⟩; simpa using hy
    rw [h1, Submodule.span_image, u.full, Submodule.map_top, LinearMap.range_eq_top]
    exact (T.symm.toLinearEquiv.restrictScalars ℝ).surjective
  hol U f := ⟨(u.hol U f).1.preimage T.continuous,
    (u.hol U f).2.comp T.differentiableOn (fun _ hz ↦ hz)⟩
  fr i z := u.fr i (T z)
  fr_hol i := (u.fr_hol i).comp T.differentiableOn (fun _ hz ↦ hz)
  fr_ne i z h := u.fr_ne i (T z) h
  fr_compat i j z h := u.fr_compat i j (T z) h

theorem pre_isDiff (u : HolUnif A L g) (T : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ)) (w : Fin g → ℂ)
    (v : epsR ℂ ⟶ A) : (pre u T).IsDiff w v ↔ u.IsDiff (T w) v := by
  have key : ∀ (U : A.left.Opens) (f : Γ(A.left, U)),
      fderiv ℂ (fun z ↦ valAt' ((pre u T).ex z).left U f) 0 w =
        fderiv ℂ (fun z ↦ valAt' (u.ex z).left U f) 0 (T w) := by
    intro U f
    have : (fun z ↦ valAt' ((pre u T).ex z).left U f) = (fun z ↦ valAt' (u.ex z).left U f) ∘ T := rfl
    rw [this, ContinuousLinearEquiv.comp_right_fderiv, map_zero]
    rfl
  unfold HolUnif.IsDiff
  simp only [key]

end GlobalTheory.TorusRenumber

namespace GlobalTheory.TorusRenumber

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}

theorem pre_isAH (u : HolUnif A L g) (T : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ))
    (Hm Hm' : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) (h : u.IsAH Hm χ) (hH : Hm'.IsHermitian)
    (hT : ∀ z l, T z ⬝ᵥ Hm.mulVec (star (T l)) = z ⬝ᵥ Hm'.mulVec (star l)) :
    (pre u T).IsAH Hm' (fun l ↦ χ ⟨T l, l.2⟩) := by
  obtain ⟨-, hpos, hχ, hfr⟩ := h
  refine ⟨hH, fun z hz ↦ ?_, fun l ↦ hχ _, fun l i z hz ↦ ?_⟩
  · rw [← hT]
    exact hpos _ (fun h0 ↦ hz (T.injective (by rw [h0, map_zero])))
  · have := hfr ⟨T l, l.2⟩ i (T z) hz
    change u.fr i (T z) = _ * _ * u.fr i (T (z + l))
    rw [this, hT, hT, map_add]

theorem perm_dot_diagonal (σ : Equiv.Perm (Fin g)) (d : Fin g → ℂ) (z l : Fin g → ℂ) :
    permCLE σ z ⬝ᵥ (Matrix.diagonal d).mulVec (star (permCLE σ l)) =
      z ⬝ᵥ (Matrix.diagonal (d ∘ σ.symm)).mulVec (star l) := by
  simp only [permCLE_apply, Matrix.mulVec_diagonal, dotProduct, Function.comp_apply, Pi.star_apply]
  exact Equiv.sum_comp σ (fun i ↦ z i * (d (σ.symm i) * star (l i))) |>.symm.trans (by simp) |>.symm

end GlobalTheory.TorusRenumber

namespace GlobalTheory.TorusRenumber

theorem isTorusPoint_perm  (F : Type) [Field F] [NumberField F] (e : Fin (Module.finrank ℚ F) ≃ (F →+* ℝ))
    (π : Equiv.Perm (Fin (Module.finrank ℚ F))) (𝔞 𝔟 : FracId F) (z : (F →+* ℝ) → ℂ)
    (X : Obj F (𝔞 * 𝔟⁻¹) (Sp ℂ)) (δ : X.DetOmega)
    (h : IsTorusPoint e 𝔞 𝔟 z X δ) :
      IsTorusPoint (π.trans e) 𝔞 𝔟 z X ((((Equiv.Perm.sign π : ℤˣ) : ℤ) : ℂ) • δ) := by
  obtain ⟨c, u, hc, hlat, hact, ⟨χ, hAH⟩, hdet⟩ := h
  set T := permCLE π.symm with hTdef
  refine ⟨c, pre u T, hc, ?_, ?_, ⟨_, pre_isAH u T _ _ χ hAH ?_ ?_⟩, ?_⟩
  · intro w
    change T w ∈ u.Λ ↔ _
    rw [hlat]
    simp only [hTdef, permCLE_apply, Equiv.trans_apply]
    constructor
    · rintro ⟨m, hm, β, hβ, hw⟩
      refine ⟨m, hm, β, hβ, funext fun i ↦ ?_⟩
      simpa using congrFun hw (π i)
    · rintro ⟨m, hm, β, hβ, rfl⟩
      exact ⟨m, hm, β, hβ, funext fun i ↦ by simp⟩
  · intro a w
    change u.ex (T _) = u.ex (T w) ≫ _
    rw [← hact a (T w)]
    congr 1
    funext j
    simp [hTdef]
  · rw [show (Matrix.diagonal fun i ↦ ((2 * (π.trans e) i (c : F) / (4 * Real.pi ^ 2 * (z ((π.trans e) i)).im) : ℝ) : ℂ)) =
      (Matrix.diagonal fun i ↦ ((2 * e i (c : F) / (4 * Real.pi ^ 2 * (z (e i)).im) : ℝ) : ℂ)).submatrix π π by
        rw [Matrix.submatrix_diagonal_equiv]; rfl]
    exact hAH.1.submatrix π
  · intro w l
    rw [hTdef, perm_dot_diagonal]
    rfl
  · intro v W' hW'
    have hW : ∀ i, u.IsDiff ((W'.submatrix id π.symm) i) (v i).hom := fun i ↦ by
      exact (pre_isDiff u T (W' i) (v i).hom).1 (hW' i)
    rw [AlternatingMap.smul_apply, hdet v _ hW, Matrix.det_permute', Equiv.Perm.sign_symm, smul_eq_mul]
    rcases Int.units_eq_one_or (Equiv.Perm.sign π) with hs | hs <;> simp [hs]

end GlobalTheory.TorusRenumber
