import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Formalism.LocalToGlobal.ProjectiveLattices.UnifDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsInvariantNatLengthLattice
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UniformizationPeriodLatticeChange
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DetOfTriangular
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsTangentModuleUniversalGroup
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.VerticalDerivativeInCoordinates

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open scoped Matrix

namespace GlobalTheory.CongrOrbit

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

section Frames

variable {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {S : Type} [CommRing S]

theorem scal_mul (x : Sp S ⟶ Xo.X) (a b : S) (i : (PPx x).ι) :
    scal x (a * b) i = scal x a i * scal x b i := by
  simp [scal, ReciprocityTheory.ChartRestriction.G.Out.liftFun, map_mul]

theorem scal_one (x : Sp S ⟶ Xo.X) (i : (PPx x).ι) : scal x 1 i = 1 := by
  simp [scal, ReciprocityTheory.ChartRestriction.G.Out.liftFun, map_one]

theorem exists_unit_of_generators {x : Sp S ⟶ Xo.X} (s s' : LB.Sec (PPx x))
    (hs : ∀ s'' : LB.Sec (PPx x), ∃! a : S, ∀ i, s''.f i = scal x a i * s.f i)
    (hs' : ∀ s'' : LB.Sec (PPx x), ∃! a : S, ∀ i, s''.f i = scal x a i * s'.f i) :
    ∃ u : Sˣ, ∀ i, s'.f i = scal x (u : S) i * s.f i := by
  obtain ⟨a, ha, -⟩ := hs s'
  obtain ⟨b, hb, -⟩ := hs' s
  obtain ⟨c1, -, hc1⟩ := hs s
  have h1 : b * a = 1 := by
    have e1 : ∀ i, s.f i = scal x (b * a) i * s.f i := fun i => by
      rw [scal_mul, mul_assoc, ← ha i, ← hb i]
    have e2 : ∀ i, s.f i = scal x 1 i * s.f i := fun i => by rw [scal_one, one_mul]
    exact (hc1 _ e1).trans (hc1 _ e2).symm
  exact ⟨⟨a, b, by rw [mul_comm]; exact h1, h1⟩, ha⟩

theorem frBor_of_eq [Algebra c.F S] (y y' : FrPt Xo c S) (hx : y'.x = y.x) (hu : y'.u = y.u) :
    ∃ t : Ix Dw → Sˣ, FrBor t y y' := by
  obtain ⟨x', hover', u', tan', eig', basis', s', gen'⟩ := y'
  simp only at hx hu
  subst hx
  subst hu
  obtain ⟨u0, hu0⟩ := exists_unit_of_generators (x := y.x) y.s s' y.gen gen'
  obtain ⟨N, _, _, v, ρ, hinj, htan, hcomb, -, -⟩ := GlobalTheory.TanMod.exists_tangent_module E H Dw l Xo S y.x
  have hb : ∀ τ i, ∃ m, v m = y.u τ i := fun τ i => (htan _).1 (y.tan τ i)
  choose b hb using hb
  have hu : ∀ τ, y.u τ = fun i => v (b τ i) := fun τ => funext fun i => (hb τ i).symm
  classical
  refine ⟨fun o => match o with
    | none => u0
    | some _ => 1, rfl, fun τ i => ⟨Pi.single i 1, by simp, fun j hj => Pi.single_eq_of_ne hj.ne' _, ?_⟩,
      𝟙 _, Category.id_comp _, Category.id_comp _, ?_⟩
  · dsimp only
    rw [hu τ, hcomb]
    simp [Pi.single_apply]
  · intro i h
    simp only
    rw [← hu0 i]
    simp only [Scheme.Hom.appLE]
    have e : (homOfLE h).op = 𝟙 _ := Subsingleton.elim _ _
    rw [e]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
    rfl

end Frames

theorem perFr_lact {r : ℕ} (X : Data E r) (x : Frame X.Ψ r) (γ : GL (Fin r) E)
    (hγ : ∀ u v, herm X.Gm ((γ : Matrix (Fin r) (Fin r) E) *ᵥ u) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) =
      herm X.Gm u v) (v : Fin r → E) (τ : E →+* ℂ) (i : ℕ) :
    Formalism.L2.PjFree.perFr X (lact γ x) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) τ i =
      Formalism.L2.PjFree.perFr X x v τ i := by
  have hm : ∀ τ : X.Ψ, mat (lact γ x) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ := fun _ => rfl
  unfold Formalism.L2.PjFree.perFr
  simp only [hm, PerMove.emb_mulVec]
  split_ifs with h1 h2 h3 h4
  · have hu : IsUnit ((γ : Matrix (Fin r) (Fin r) E).map τ).det :=
      (Matrix.isUnit_iff_isUnit_det _).1 (γ.isUnit.map τ.mapMatrix)
    rw [Matrix.mul_inv_rev, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu,
      Matrix.mul_one]
  · rfl
  · rw [PerMove.col_mul, PerMove.hermC_unitary _ _ _ hγ]
  · rfl
  · rfl

noncomputable def latAut {r : ℕ} (Λ : Submodule (𝓞 E) (Fin r → E)) (γ : GL (Fin r) E)
    (h : ∀ x, x ∈ Λ ↔ (γ : Matrix (Fin r) (Fin r) E) *ᵥ x ∈ Λ) : Λ ≃ₗ[𝓞 E] Λ where
  toFun a := ⟨(γ : Matrix (Fin r) (Fin r) E) *ᵥ a, (h _).1 a.2⟩
  invFun a := ⟨((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ a, (h _).2 (by
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]; exact a.2)⟩
  map_add' a b := Subtype.ext (Matrix.mulVec_add (γ : Matrix (Fin r) (Fin r) E) (a : Fin r → E) (b : Fin r → E))
  map_smul' s a := Subtype.ext (Matrix.mulVec_smul (γ : Matrix (Fin r) (Fin r) E) s (a : Fin r → E))
  left_inv a := Subtype.ext (by
    simp only
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec])
  right_inv a := Subtype.ext (by
    simp only
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec])

end GlobalTheory.CongrOrbit

namespace GlobalTheory

open CongrOrbit in

theorem congr_lact_mem_orbit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.IsUnf U → l.A = 1 → ∀ k (γ : GL (Fin r) E), IsUStab (U.X k).Gm (U.X k).Λ γ → (∀ x ∈ (U.X k).Λ, ∃ y ∈ (U.X k).Λ, Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) x - x = (l.M : E) • y) → ∀ x ∈ (U.X k).dom, ∃ γ' ∈ (U.X k).Γ, ∃ b ∈ Bor (U.X k).Ψ r, lact γ x = rmul (lact γ' x) b := by
  intro E _ _ _ H Dw l Xo c σ r U hU hA k γ hγ hM x hx
  obtain ⟨-, -, -, hfib, -, g, e, F, ik, φ, hEF, hpt⟩ := hU
  have hx' := dom_lact (U.X k) hx hγ
  obtain ⟨P, hP, hPer, hu, hd, -⟩ := hpt k ⟨x, hx⟩
  obtain ⟨P', hP', hPer', hu', hd', -⟩ := hpt k ⟨_, hx'⟩
  let gam := (φ k).trans ((latAut (U.X k).Λ γ hγ.2).trans (φ k).symm)
  have hgam : ∀ a, (φ k (gam a) : Fin r → E) = (γ : Matrix (Fin r) (Fin r) E) *ᵥ (φ k a : Fin r → E) := by
    intro a
    simp only [gam, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    rfl
  obtain ⟨-, hpt, hex⟩ := FamRigid.ex_eq_of_level_group latMinkowski E H Dw l Xo _ g _ F (ik k) P P' gam 1
    hPer hPer' (fun a b => by
      have := hEF k (gam a) (gam b)
      rw [hgam, hgam, hγ.1, ← hEF] at this
      exact_mod_cast this)
    (fun a _ => by
      obtain ⟨y, hy, he⟩ := hM _ (φ k a).2
      refine ⟨(φ k).symm ⟨y, hy⟩, (φ k).injective (Subtype.ext ?_)⟩
      rw [hgam, map_add, map_nsmul, LinearEquiv.apply_symm_apply, Submodule.coe_add, ← sub_eq_iff_eq_add', he,
        Nat.cast_smul_eq_nsmul]
      rfl)
    (fun a => ⟨gam a - a, by rw [hA, one_smul]; abel⟩)
    (fun a => by
      funext j
      rw [Matrix.one_mulVec, hP, hP', hgam]
      exact perFr_lact _ _ _ hγ.1 _ _ _)
  simp only [Matrix.one_mulVec] at hex
  obtain ⟨γ', hγ', b, hb, he⟩ := (hfib k k ⟨x, hx⟩ ⟨_, hx'⟩).1 (frBor_of_eq _ _
    (hu'.trans (hpt.symm.trans hu.symm)) (by
      funext τ i
      have h1 := hd' τ i
      simp only [hex] at h1
      exact VerticalDeriv.isDerivAt0_unique h1 (hd τ i)))
  exact ⟨γ', hγ', b, hb, eq_of_heq (Sigma.mk.inj he).2⟩

end GlobalTheory
