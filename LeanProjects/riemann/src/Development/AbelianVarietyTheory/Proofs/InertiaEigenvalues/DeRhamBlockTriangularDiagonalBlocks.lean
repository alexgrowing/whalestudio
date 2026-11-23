import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamPeriodRingFieldTPowFiltrationUnitsStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.PMon.SubquotientAlgEquiv

theorem exists_cols_isUnit {F : Type} [CommRing F] (hF : IsField F) {b n : Type} [Fintype b] [DecidableEq b]
    [Fintype n] [DecidableEq n] (X : Matrix b n F) (Z : Matrix n b F) (h : X * Z = 1) :
    ∃ e : b → n, IsUnit (X.submatrix id e) := by
  letI : Field F := hF.toField
  have h1 : X.rank = Fintype.card b := by
    apply le_antisymm (Matrix.rank_le_card_height X)
    have := Matrix.rank_mul_le_left X Z
    rw [h, Matrix.rank_one] at this
    exact this
  have h2 : Module.finrank F (Submodule.span F (Set.range X.col)) = Fintype.card b := by
    rw [← Matrix.rank_eq_finrank_span_cols, h1]
  obtain ⟨κ, e, he, hspan, hli⟩ := exists_linearIndependent' F X.col
  haveI : Finite κ := Finite.of_injective e he
  letI : Fintype κ := Fintype.ofFinite κ
  have h3 : Fintype.card κ = Fintype.card b := by
    rw [← finrank_span_eq_card hli, hspan, h2]
  let τ : b ≃ κ := Fintype.equivOfCardEq h3.symm
  refine ⟨e ∘ τ, ?_⟩
  have h4 : LinearIndependent F (X.submatrix id (e ∘ τ)).col := hli.comp τ τ.injective
  exact Matrix.linearIndependent_cols_iff_isUnit.mp h4

end GlobalTheory.PMon.SubquotientAlgEquiv

end

noncomputable section

namespace GlobalTheory.PMon.SubquotientAlgEquiv

theorem map_mul_algEquiv {R S : Type} [CommRing R] [CommRing S] [Algebra S R] (σ : R ≃ₐ[S] R) {p q s : Type}
    [Fintype q] (M : Matrix p q R) (N : Matrix q s R) : (M * N).map σ = M.map σ * N.map σ :=
  Matrix.map_mul (f := (σ : R →+* R))

theorem map_one_algEquiv {R S : Type} [CommRing R] [CommRing S] [Algebra S R] (σ : R ≃ₐ[S] R) {p : Type}
    [DecidableEq p] : (1 : Matrix p p R).map σ = 1 :=
  Matrix.map_one _ (map_zero σ) (map_one σ)

end GlobalTheory.PMon.SubquotientAlgEquiv

namespace GlobalTheory.PMon

open scoped Matrix

open SubquotientAlgEquiv in

theorem subQuot : SubQuot := by
  intro l _ P AI T a b _ _ _ _ K r ρ ρ₁ ρ₂ c _ hblk hdr
  have hF := (GlobalTheory.T.deRhamPeriodRing_field_tPow_filtration_units l P AI T).1
  have e11 : ∀ m g (i j : a), matD P ρ m g (Sum.inl i) (Sum.inl j) = matD P ρ₁ m g i j := by
    intro m g i j; simp [matD, hblk g]
  have e21 : ∀ m g (i : b) (j : a), matD P ρ m g (Sum.inr i) (Sum.inl j) = 0 := by
    intro m g i j; simp [matD, hblk g]
  have e22 : ∀ m g (i j : b), matD P ρ m g (Sum.inr i) (Sum.inr j) = matD P ρ₂ m g i j := by
    intro m g i j; simp [matD, hblk g]
  refine ⟨fun m => ?_, fun m => ?_⟩
  · obtain ⟨Q, hQ⟩ := hdr m
    have hQQi : (Q : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR) * ((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR) = 1 :=
      Units.mul_inv Q
    have hQiQ : ((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR) * (Q : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR) = 1 :=
      Units.inv_mul Q
    have hinv : ∀ g : ↥(GK K), ((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).map (P.actQdR (g : GQ l)) =
        ((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR) * matD P ρ m g := by
      intro g
      have hs : (Q : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).map (P.actQdR (g : GQ l)) *
          ((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).map (P.actQdR (g : GQ l)) = 1 := by
        rw [← map_mul_algEquiv, hQQi, map_one_algEquiv]
      calc ((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).map (P.actQdR (g : GQ l))
          = (((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR) * (Q : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR)) *
              ((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).map (P.actQdR (g : GQ l)) := by
            rw [hQiQ, Matrix.one_mul]
        _ = ((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR) *
              (matD P ρ m g * (Q : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).map (P.actQdR (g : GQ l))) *
              ((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).map (P.actQdR (g : GQ l)) := by
            rw [hQ g]
        _ = ((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR) * matD P ρ m g *
              ((Q : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).map (P.actQdR (g : GQ l)) *
              ((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).map (P.actQdR (g : GQ l))) := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hs, Matrix.mul_one]
    let Y : Matrix (a ⊕ b) a P.R.BdR := ((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).submatrix id Sum.inl
    let W : Matrix a (a ⊕ b) P.R.BdR := (Q : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).submatrix Sum.inl id
    have hWY : W * Y = 1 := by
      rw [show W * Y = ((Q : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR) *
          ((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR)).submatrix Sum.inl Sum.inl from
        (Matrix.submatrix_mul _ _ Sum.inl id Sum.inl Function.bijective_id).symm, hQQi]
      exact Matrix.submatrix_one _ Sum.inl_injective
    have hYW : Yᵀ * Wᵀ = 1 := by rw [← Matrix.transpose_mul, hWY, Matrix.transpose_one]
    obtain ⟨e, he⟩ := exists_cols_isUnit hF Yᵀ Wᵀ hYW
    have hY' : IsUnit (Y.submatrix e id) := by
      have := (Matrix.isUnit_transpose _).2 he
      simpa [Matrix.transpose_submatrix] using this
    have hσY : ∀ g : ↥(GK K), (Y.submatrix e id).map (P.actQdR (g : GQ l)) = Y.submatrix e id * matD P ρ₁ m g := by
      intro g; ext i j
      have := congrFun (congrFun (hinv g) (e i)) (Sum.inl j)
      simp only [Matrix.map_apply, Matrix.mul_apply, Fintype.sum_sum_type, e11, e21, mul_zero,
        Finset.sum_const_zero, add_zero] at this
      simpa [Y, Matrix.mul_apply] using this
    refine ⟨hY'.unit⁻¹, fun g => ?_⟩
    have hu : ((hY'.unit : GL a P.R.BdR) : Matrix a a P.R.BdR) = Y.submatrix e id := hY'.unit_spec
    have hs : ((hY'.unit : GL a P.R.BdR) : Matrix a a P.R.BdR).map (P.actQdR (g : GQ l)) *
        ((hY'.unit⁻¹ : GL a P.R.BdR) : Matrix a a P.R.BdR).map (P.actQdR (g : GQ l)) = 1 := by
      rw [← map_mul_algEquiv, Units.mul_inv, map_one_algEquiv]
    calc matD P ρ₁ m g * ((hY'.unit⁻¹ : GL a P.R.BdR) : Matrix a a P.R.BdR).map (P.actQdR (g : GQ l))
        = (((hY'.unit⁻¹ : GL a P.R.BdR) : Matrix a a P.R.BdR) * ((hY'.unit : GL a P.R.BdR) : Matrix a a P.R.BdR)) *
            matD P ρ₁ m g * ((hY'.unit⁻¹ : GL a P.R.BdR) : Matrix a a P.R.BdR).map (P.actQdR (g : GQ l)) := by
          rw [Units.inv_mul, Matrix.one_mul]
      _ = ((hY'.unit⁻¹ : GL a P.R.BdR) : Matrix a a P.R.BdR) *
            (((hY'.unit : GL a P.R.BdR) : Matrix a a P.R.BdR) * matD P ρ₁ m g) *
            ((hY'.unit⁻¹ : GL a P.R.BdR) : Matrix a a P.R.BdR).map (P.actQdR (g : GQ l)) := by
          simp only [Matrix.mul_assoc]
      _ = ((hY'.unit⁻¹ : GL a P.R.BdR) : Matrix a a P.R.BdR) *
            ((hY'.unit : GL a P.R.BdR) : Matrix a a P.R.BdR).map (P.actQdR (g : GQ l)) *
            ((hY'.unit⁻¹ : GL a P.R.BdR) : Matrix a a P.R.BdR).map (P.actQdR (g : GQ l)) := by
          rw [hu, hσY g]
      _ = _ := by rw [Matrix.mul_assoc, hs, Matrix.mul_one]
  · obtain ⟨Q, hQ⟩ := hdr m
    have hQQi : (Q : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR) * ((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR) = 1 :=
      Units.mul_inv Q
    let X : Matrix b (a ⊕ b) P.R.BdR := (Q : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).submatrix Sum.inr id
    let Z : Matrix (a ⊕ b) b P.R.BdR := ((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).submatrix id Sum.inr
    have hXZ : X * Z = 1 := by
      rw [show X * Z = ((Q : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR) *
          ((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR)).submatrix Sum.inr Sum.inr from
        (Matrix.submatrix_mul _ _ Sum.inr id Sum.inr Function.bijective_id).symm, hQQi]
      exact Matrix.submatrix_one _ Sum.inr_injective
    obtain ⟨e, he⟩ := exists_cols_isUnit hF X Z hXZ
    refine ⟨he.unit, fun g => ?_⟩
    rw [he.unit_spec]
    ext i j
    have := congrFun (congrFun (hQ g) (Sum.inr i)) (e j)
    simp only [Matrix.map_apply, Matrix.mul_apply, Fintype.sum_sum_type, e21, e22, zero_mul,
      Finset.sum_const_zero, zero_add] at this
    simpa [X, Matrix.mul_apply] using this

end GlobalTheory.PMon

end
