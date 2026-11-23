import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSpMapEv

open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)

namespace GlobalTheory.FlagMod.FieldFlag

theorem exists_mulVec_submatrix_mul_iff {R : Type} [CommRing R] {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    (U : Matrix m n R) (e : Equiv.Perm n) (C : Matrix n n R) (hC : IsUnit C.det) (cv : m → R) :
    (∃ a, (U.submatrix id e * C).mulVec a = cv) ↔ ∃ a, U.mulVec a = cv := by
  have hs : ∀ b, (U.submatrix id e).mulVec b = U.mulVec (b ∘ e.symm) := fun b => by
    have := Matrix.submatrix_mulVec_equiv U b (Equiv.refl m) e
    simpa using this
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨(C.mulVec a) ∘ e.symm, by rw [← Matrix.mulVec_mulVec, hs]⟩
  · rintro ⟨a, rfl⟩
    have hC' : ∀ x, C.mulVec (C⁻¹.mulVec x) = x := fun x => by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hC, Matrix.one_mulVec]
    refine ⟨C⁻¹.mulVec (a ∘ e), ?_⟩
    rw [← Matrix.mulVec_mulVec, hC', hs]
    congr 1
    funext i
    simp

end GlobalTheory.FlagMod.FieldFlag

namespace GlobalTheory.FlagMod.FieldFlag

open MonoidalCategory CartesianMonoidalCategory MonObj

theorem cellFrames_topEigen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)) (A : Atlas Y p) (Z : Scheme.{0}) (π : Z ⟶ Y.X) (g : ∀ en : En Dw.mult, Z ⟶ PSpace c.F (plN A.N en.1)) (κ : ∀ b, Pm Dw.mult → (Sp (CR Dw.mult (A.V b)) ⟶ Z)) [∀ b w, IsOpenImmersion (κ b w)] (hZ : Cells A π g κ) (ht : FlagCellFrameChangeTriangular hZ), (cellFrames hZ ht).TopEigen := by
  intro E _ _ _ H Dw l Xo c Y p A Z π g κ _ hZ ht
  intro S _ _ y hy z hx k hz σ
  obtain ⟨φ, hφ⟩ : ∃ φ, φ = (ev z _ hz).comp (cellθ κ k).toRingHom := ⟨_, rfl⟩
  have hzφ : spMap φ ≫ κ k.1 k.2 = z := hφ ▸ eq_spMap_ev k z hz
  have hxφ : y ≫ Y.j = spMap (φ.comp (cC A k.1)) ≫ tau (A.V k.1).2 := by
    rw [← hx, ← hzφ, Category.assoc, hZ.plk.base, cbase, ← Category.assoc, spMap_comp']
    rfl
  have hV : ⊤ ≤ (y ≫ Y.j) ⁻¹ᵁ (A.k k.1).V := hxφ ▸ le_preimage_comp _ (tau_le (A.V k.1).2 le_rfl)
  have hev : ev (y ≫ Y.j) (A.k k.1).V hV = φ.comp (cC A k.1) := by
    rw [ev_congr hxφ _ hV (hxφ ▸ hV)]
    exact ev_spMap_tau (A.V k.1).2 _ _
  have hM : ⊤ ≤ (y ≫ Y.j) ⁻¹ᵁ (A.k k.1).M.U := (cellFrames hZ ht).inM hz hx
  have huAt : (cellFrames hZ ht).uAt k z hz σ = ((((A.k k.1).u σ).map (ev (y ≫ Y.j) _ hV)).submatrix id (k.2 σ)) *
      (cellMat (A.V k.1) σ).map φ := by
    refine Matrix.ext fun i j => ?_
    show (ev z _ hz) ((cellθ κ k) (uC A k.1 k.2 σ i j)) = _
    have e2 : ∀ x, (ev z _ hz) ((cellθ κ k) x) = φ x := fun x => by rw [hφ]; rfl
    rw [hev, e2, uC]
    exact RingHom.map_matrix_mul _ _ i j φ
  have hdet : IsUnit ((cellMat (A.V k.1) σ).map φ).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, det_cellMat, map_one]
    exact isUnit_one
  refine SetLike.ext fun v => ?_
  obtain ⟨cv, rfl⟩ := (vec (A.k k.1).M.toMChart _ hM).surjective v
  refine Iff.trans ?_ ((vec_mem_eigLie _ _ hM σ cv).trans (((LowRank.pm_gen p (A.k k.1).M.toMChart σ hy hM).1 cv).trans
    ((A.k k.1).fix_iff σ _ hV hM cv))).symm
  rw [mem_initSpan, ← exists_mulVec_submatrix_mul_iff _ (k.2 σ) _ hdet, ← huAt]
  exact ⟨fun ⟨a, _, e⟩ => ⟨a, (vec (A.k k.1).M.toMChart _ hM).injective
      (((cellFrames hZ ht).sum_vecAt k _ hz hx σ a).symm.trans e)⟩,
    fun ⟨a, e⟩ => ⟨a, fun j hj => absurd j.2 (not_lt.2 hj),
      ((cellFrames hZ ht).sum_vecAt k _ hz hx σ a).trans (congrArg (vec (A.k k.1).M.toMChart _ hM) e)⟩⟩

end GlobalTheory.FlagMod.FieldFlag
