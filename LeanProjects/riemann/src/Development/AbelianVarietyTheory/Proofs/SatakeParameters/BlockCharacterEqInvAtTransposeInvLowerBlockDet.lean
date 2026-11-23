import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValLeOneOfMemKO
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjSPV
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.BlockType GlobalTheory.SplitWeil
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BlockConjDet

open ValuativeRel

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_det_mul_sub_one_lt {r t : ℕ} {h : GL (Fin (r + t)) k} (hh : h ∈ blockGrp k r t) :
    valuation k (((h⁻¹ : GL (Fin (r + t)) k).val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det *
      (h.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det - 1) < 1 := by
  obtain ⟨g, hg⟩ := hh.1
  have hi := ((blockGrp k r t).inv_mem hh).2
  have hinv : (h⁻¹ : GL (Fin (r + t)) k) = Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) g⁻¹ := by
    rw [← hg, map_inv]
  have hC : ∀ (i : Fin t) (j : Fin r),
      (g⁻¹ : GL (Fin (r + t)) 𝒪[k]).val (Fin.natAdd r i) (Fin.castAdd t j) ∈ 𝓂[k] := by
    intro i j
    have := hi (Fin.natAdd r i) j
    have hne : Fin.natAdd r i ≠ Fin.castAdd t j := by
      intro e; have := congrArg Fin.val e; simp at this; omega
    rw [hinv, Matrix.sub_apply, Matrix.one_apply_ne hne, sub_zero] at this
    change valuation k (algebraMap 𝒪[k] k ((g⁻¹ : GL (Fin (r + t)) 𝒪[k]).val (Fin.natAdd r i) (Fin.castAdd t j))) < 1 at this
    exact (IsLocalRing.mem_maximalIdeal _).2 (Valuation.Integer.not_isUnit_iff_valuation_lt_one.mpr this)
  have hres : (((g⁻¹ : GL (Fin (r + t)) 𝒪[k]).val.submatrix (Fin.natAdd r) (Fin.natAdd r)) *
      (g.val.submatrix (Fin.natAdd r) (Fin.natAdd r))).map (IsLocalRing.residue 𝒪[k]) = 1 := by
    ext i j
    have e1 : ((g⁻¹ : GL (Fin (r + t)) 𝒪[k]).val * g.val) (Fin.natAdd r i) (Fin.natAdd r j) =
        (1 : Matrix (Fin (r + t)) (Fin (r + t)) 𝒪[k]) (Fin.natAdd r i) (Fin.natAdd r j) := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [Matrix.mul_apply, Fin.sum_univ_add] at e1
    have hm : ∑ x : Fin r, (g⁻¹ : GL (Fin (r + t)) 𝒪[k]).val (Fin.natAdd r i) (Fin.castAdd t x) *
        g.val (Fin.castAdd t x) (Fin.natAdd r j) ∈ 𝓂[k] :=
      Ideal.sum_mem _ fun x _ => Ideal.mul_mem_right _ _ (hC i x)
    have e2 : (((g⁻¹ : GL (Fin (r + t)) 𝒪[k]).val.submatrix (Fin.natAdd r) (Fin.natAdd r)) *
        (g.val.submatrix (Fin.natAdd r) (Fin.natAdd r))) i j =
        (1 : Matrix (Fin (r + t)) (Fin (r + t)) 𝒪[k]) (Fin.natAdd r i) (Fin.natAdd r j) -
          ∑ x : Fin r, (g⁻¹ : GL (Fin (r + t)) 𝒪[k]).val (Fin.natAdd r i) (Fin.castAdd t x) *
            g.val (Fin.castAdd t x) (Fin.natAdd r j) := by
      simp only [Matrix.mul_apply, Matrix.submatrix_apply]; rw [← e1]; ring
    rw [Matrix.map_apply, e2, map_sub, (IsLocalRing.residue_eq_zero_iff _).2 hm, sub_zero]
    by_cases e : i = j <;> simp [Matrix.one_apply, e]
  have hm : ((g⁻¹ : GL (Fin (r + t)) 𝒪[k]).val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det *
      (g.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det - 1 ∈ 𝓂[k] := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, ← Matrix.det_mul, RingHom.map_det, RingHom.mapMatrix_apply,
      hres, Matrix.det_one, map_one, sub_self]
  have hv := Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp ((IsLocalRing.mem_maximalIdeal _).1 hm)
  have e : ∀ G : GL (Fin (r + t)) 𝒪[k],
      ((Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) G).val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det =
        (((G.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det : 𝒪[k]) : k) := by
    intro G
    rw [show (((G.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det : 𝒪[k]) : k) =
      algebraMap 𝒪[k] k (G.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det from rfl, RingHom.map_det]
    rfl
  rw [hinv, ← hg, e, e]
  simpa only [AddSubgroupClass.coe_sub, MulMemClass.coe_mul, OneMemClass.coe_one] using hv

end

end GlobalTheory.BlockConjDet

namespace GlobalTheory.BlockConjDet

theorem blockChar_eq_inv_detDD : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (r t : ℕ) (c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L), (∀ x, Valued.v (c x) = Valued.v x) → ∀ (a b : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L))), b.val = (a⁻¹ : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L))).val.transpose → Matrix.GeneralLinearGroup.map c.toRingHom a ∈ blockGrp (s.w.adicCompletion L) r t → ∀ ϖ : s.v.adicCompletion (maximalRealSubfield L), Valued.v ϖ = WithZero.exp (-1) → ∀ d : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L)), d.val = Matrix.diagonal (fun i : Fin (r + t) => if (i : ℕ) < r then (1 : s.v.adicCompletion (maximalRealSubfield L)) else ϖ) → ∃ u : (s.v.adicCompletion (maximalRealSubfield L))ˣ, (u : s.v.adicCompletion (maximalRealSubfield L)) = NG.detDD s r (d * b * d⁻¹) ∧ ∀ μ : (s.w.adicCompletion L)ˣ →* ℂˣ, IsTame μ → blockChar μ (Matrix.GeneralLinearGroup.map c.toRingHom a) = (((μ (Units.map c.toMonoidHom u))⁻¹ : ℂˣ) : ℂ) := by
  intro L _ _ _ s r t c _ a b hb ha ϖ hϖ d hd
  have hϖ0 : ϖ ≠ 0 := by
    intro h0; rw [h0, map_zero] at hϖ; exact (WithZero.exp_ne_zero hϖ.symm).elim
  have hdinv : (d⁻¹ : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L))).val =
      Matrix.diagonal (fun i : Fin (r + t) => if (i : ℕ) < r then (1 : s.v.adicCompletion (maximalRealSubfield L)) else ϖ⁻¹) := by
    have h1 : d.val * Matrix.diagonal (fun i : Fin (r + t) =>
        if (i : ℕ) < r then (1 : s.v.adicCompletion (maximalRealSubfield L)) else ϖ⁻¹) = 1 := by
      rw [hd, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1; ext i; split_ifs <;> simp [hϖ0]
    calc (d⁻¹ : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L))).val
        = (d⁻¹ : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L))).val * (d.val * Matrix.diagonal (fun i : Fin (r + t) =>
          if (i : ℕ) < r then (1 : s.v.adicCompletion (maximalRealSubfield L)) else ϖ⁻¹)) := by rw [h1, mul_one]
      _ = _ := by rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  have hDD : NG.detDD s r (d * b * d⁻¹) =
      ((a⁻¹ : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L))).val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det := by
    let e : Fin t ≃ {x : Fin (r + t) // r ≤ x.val} :=
      { toFun := fun i => ⟨Fin.natAdd r i, by simp⟩
        invFun := fun x => ⟨x.1.val - r, by omega⟩
        left_inv := fun i => by ext; simp
        right_inv := fun x => by ext; simp; omega }
    rw [NG.detDD, ← Matrix.det_submatrix_equiv_self e, ← Matrix.det_transpose]
    congr 1
    ext i j
    have hn : ∀ x : Fin t, ¬ ((Fin.natAdd r x : Fin (r + t)) : ℕ) < r := by intro x; simp
    simp only [e, Matrix.transpose_apply, Matrix.submatrix_apply, Matrix.of_apply, Equiv.coe_fn_mk, Units.val_mul,
      hdinv, hd, Matrix.mul_diagonal, Matrix.diagonal_mul, hb]
    rw [if_neg (hn _), if_neg (hn _), mul_comm ϖ, mul_inv_cancel_right₀ hϖ0]
  have hc : c (NG.detDD s r (d * b * d⁻¹)) =
      (((Matrix.GeneralLinearGroup.map c.toRingHom a)⁻¹ : GL (Fin (r + t)) (s.w.adicCompletion L)).val.submatrix
        (Fin.natAdd r) (Fin.natAdd r)).det := by
    rw [hDD, ← map_inv]
    exact RingHom.map_det c.toRingHom _
  have hv := val_det_mul_sub_one_lt ha
  have hne : ∀ x y : s.w.adicCompletion L, ValuativeRel.valuation _ (x * y - 1) < 1 → x ≠ 0 ∧ y ≠ 0 := by
    intro x y h
    constructor <;> rintro rfl <;> simp at h
  obtain ⟨h1, h2⟩ := hne _ _ hv
  have hF : NG.detDD s r (d * b * d⁻¹) ≠ 0 := fun h0 => h1 (by rw [← hc, h0, map_zero])
  refine ⟨Units.mk0 _ hF, rfl, fun μ hμ => ?_⟩
  rw [blockChar_eq μ _ (Units.mk0 _ h2) rfl]
  have ht := hμ (Units.map c.toMonoidHom (Units.mk0 _ hF) * Units.mk0 _ h2) (by
    simp only [Units.val_mul, Units.coe_map, Units.val_mk0]
    rw [show (c.toMonoidHom : _ →* _) (NG.detDD s r (d * b * d⁻¹)) = c (NG.detDD s r (d * b * d⁻¹)) from rfl, hc]
    exact hv)
  rw [map_mul] at ht
  rw [eq_inv_of_mul_eq_one_right ht]

end GlobalTheory.BlockConjDet
