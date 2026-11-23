import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.PolarizedGaloisRepPublished
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GaloisRepOfPolarizedPair
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalConverseGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.AntisymmetrizedProductEqFactorialSmulQdet

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Published GlobalTheory.TheRec GlobalTheory.ContraPair

noncomputable section

namespace GlobalTheory.CapPair

open Formalism.REAL Formalism.HermitianLatticeCounting.P MulOpposite

section Algebra

variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ}

omit [Algebra ℂ A] in

theorem glRel_op {X : Fin n → Fin n → A} (h : Formalism.REAL.GlRel X) : Formalism.REAL.GlRel fun i j => op (X j i) := by
  intro a b c d
  have h1 := congrArg op (h d c b a)
  simp only [op_sub, op_mul, apply_ite op, op_zero] at h1
  rw [h1]
  simp only [eq_comm (a := c) (b := b), eq_comm (a := a) (b := d)]

theorem qdet_op {X : Fin n → Fin n → A} (h : Formalism.REAL.GlRel X) (y : ℂ) :
    qdet (fun i j => op (X j i)) y = op (qdet X y) := by
  have hP : ∀ (arg : Fin n → ℂ) (σ τ : Equiv.Perm (Fin n)), orderedTermProduct (fun i j => op (X j i)) arg σ τ =
      op (orderedTermProduct X (arg ∘ Fin.revPerm) (τ * Fin.revPerm) (σ * Fin.revPerm)) := fun arg σ τ => by
    unfold orderedTermProduct
    rw [op_list_prod, List.map_ofFn]
    congr 1
    refine List.ext_getElem (by simp) fun k h1 h2 => ?_
    have hk : k < n := by simpa using h1
    have e : (⟨n - 1 - k, by omega⟩ : Fin n).rev = ⟨k, hk⟩ := Fin.ext (by rw [Fin.val_rev]; simp only; omega)
    simp only [List.getElem_reverse, List.getElem_ofFn, List.length_ofFn, Function.comp_apply, Equiv.Perm.mul_apply,
      Fin.revPerm_apply, e, Tm, op_add, apply_ite op, op_zero, eq_comm (a := τ _)]
    rfl
  have hS : ∀ arg : Fin n → ℂ, doublyAntisymmetrizedProduct (fun i j => op (X j i)) arg = op (doublyAntisymmetrizedProduct X (arg ∘ Fin.revPerm)) := fun arg => by
    unfold doublyAntisymmetrizedProduct
    rw [Finset.sum_comm, Finset.op_sum]
    refine Fintype.sum_equiv (Equiv.mulRight Fin.revPerm) _ _ fun σ => ?_
    rw [Finset.op_sum]
    refine Fintype.sum_equiv (Equiv.mulRight Fin.revPerm) _ _ fun τ => ?_
    simp only [hP, ← zsmul_eq_mul, op_smul, smul_smul, Equiv.coe_mulRight, Equiv.Perm.sign_mul, Units.val_mul]
    congr 1
    linear_combination (-((Equiv.Perm.sign σ : ℤ) * (Equiv.Perm.sign τ : ℤ))) *
      Int.units_coe_mul_self (Equiv.Perm.sign (Fin.revPerm (n := n)))
  have e := hS fun k => y - (k : ℂ)
  rw [antisymmetrizedProduct_perm_invariant, antisymmetrizedProduct_eq_factorial_smul_qdet _ h, antisymmetrizedProduct_eq_factorial_smul_qdet _ (glRel_op h), op_smul] at e
  exact (IsUnit.mk0 _ (by exact_mod_cast n.factorial_ne_zero)).smul_left_cancel.mp e

theorem qdet_antipode {X : Fin n → Fin n → A} (h : Formalism.REAL.GlRel X) (x : ℂ) :
    qdet (fun i j => -op (X i j)) x = op ((-1 : ℂ) ^ n • qdet X ((n : ℂ) - 1 - x)) := by
  rw [quantumDet_neg_transpose _ (glRel_op h), qdet_op h, op_smul]

theorem qdet_prod {A' : Type} [Ring A'] [Algebra ℂ A'] (X : Fin n → Fin n → A) (Y : Fin n → Fin n → A') (x : ℂ) :
    qdet (fun i j => (X i j, Y i j)) x = (qdet X x, qdet Y x) :=
  Prod.ext (map_qdet (AlgHom.fst ℂ A A') _ _) (map_qdet (AlgHom.snd ℂ A A') _ _)

end Algebra

def adjPairs {M : Type} [AddCommGroup M] [Module ℂ M] (V W : Submodule ℂ M) (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) :
    Subalgebra ℂ (Module.End ℂ M × (Module.End ℂ M)ᵐᵒᵖ) where
  carrier := {z | ∀ (φ : V) (ψ : W), ∃ (h : z.1 φ.1 ∈ V) (h' : z.2.unop ψ.1 ∈ W), B ⟨_, h⟩ ψ = B φ ⟨_, h'⟩}
  mul_mem' {x y} hx hy φ ψ := by
    obtain ⟨h1, -, -⟩ := hy φ ψ
    obtain ⟨h2, h3, e1⟩ := hx ⟨_, h1⟩ ψ
    obtain ⟨_, h4, e2⟩ := hy φ ⟨_, h3⟩
    exact ⟨h2, h4, e1.trans e2⟩
  add_mem' {x y} hx hy φ ψ := by
    obtain ⟨h1, h2, e1⟩ := hx φ ψ
    obtain ⟨h3, h4, e2⟩ := hy φ ψ
    refine ⟨add_mem h1 h3, add_mem h2 h4, ?_⟩
    change B (⟨_, h1⟩ + ⟨_, h3⟩) ψ = B φ (⟨_, h2⟩ + ⟨_, h4⟩)
    rw [map_add, LinearMap.add_apply, map_add, e1, e2]
  algebraMap_mem' c φ ψ := by
    refine ⟨V.smul_mem c φ.2, W.smul_mem c ψ.2, ?_⟩
    change B (c • φ) ψ = B φ (c • ψ)
    rw [map_smul, map_smul, LinearMap.smul_apply]

theorem infChar_conj_of_paired : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (π π' : CuspSub E a),
    Paired π π' conjOp → ∀ (τ : E →+* ℂ) (m m' : Multiset ℂ), π.HasInfChar τ m →
      π'.HasInfChar (NumberField.ComplexEmbedding.conjugate τ) m' → m' = m.map Neg.neg := by
  intro E _ _ _ a π π' ⟨B, hB, _, _, _, hL⟩ τ m m' hm hm'
  let S := adjPairs π.V π'.V B
  have h1 : ∀ i j z, (lieS E a i j (atEmb τ z), -op (lieS E a i j (atEmb (ComplexEmbedding.conjugate τ) z))) ∈ S := by
    intro i j z φ ψ
    have e : star (atEmb τ z) = atEmb (ComplexEmbedding.conjugate τ) z := by
      classical
      rw [atEmb_conj]
      unfold atEmb
      rw [Pi.star_single]
      split_ifs <;> rfl
    have e2 : conjOp (.lie (toL (Matrix.single i j (atEmb τ z))) : Op E a) =
        .lie (toL (Matrix.single i j (atEmb (ComplexEmbedding.conjugate τ) z))) := by
      refine congrArg Op.lie (funext fun k => funext fun l => ?_)
      change star (Matrix.single i j (atEmb τ z) k l) = Matrix.single i j _ k l
      rw [Matrix.single_apply, Matrix.single_apply, apply_ite star, e, star_zero]
    have h := hL (toL (Matrix.single i j (atEmb τ z))) φ ψ
    rw [e2, add_eq_zero_iff_eq_neg, ← map_neg] at h
    exact ⟨π.stable (.lie _) _ φ.2, neg_mem (π'.stable (.lie _) _ ψ.2), h⟩
  have h2 : ∀ i j, (Eop τ i j, -op (Eop (ComplexEmbedding.conjugate τ) i j)) ∈ S := fun i j => by
    convert S.smul_mem (S.sub_mem (h1 i j 1) (S.smul_mem (h1 i j Complex.I) Complex.I)) (1 / 2) using 1
    refine Prod.ext rfl ?_
    simp only [Eop, op_smul, op_sub, Prod.smul_snd, Prod.snd_sub]
    module
  have h3 : ∀ x, qdet (fun i j => (Eop (a := a) τ i j, -op (Eop (ComplexEmbedding.conjugate τ) i j))) x ∈ S := fun x => by
    refine S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
    refine S.add_mem ?_ (h2 _ _)
    split_ifs
    · exact S.algebraMap_mem _
    · exact S.zero_mem
  have h4 : ∀ u, (cap (a := a) τ u, op ((-1 : ℂ) ^ a • cap (a := a) (ComplexEmbedding.conjugate τ) (-u) : Module.End ℂ (Sm E a))) ∈ S := fun u => by
    convert h3 (u + ((a : ℂ) - 1) / 2) using 1
    rw [qdet_prod, qdet_antipode (A := Module.End ℂ (Sm E a)) (glRel_Eop (a := a) (ComplexEmbedding.conjugate τ)), show (a : ℂ) - 1 - (u + ((a : ℂ) - 1) / 2) = -u + ((a : ℂ) - 1) / 2 by ring]
    rfl
  have h5 : π.HasInfChar τ (m'.map Neg.neg) := by
    refine ⟨by rw [Multiset.card_map, hm'.1], fun u φ hφ => ?_⟩
    have e : ((m'.map Neg.neg).map (u + ·)) = (m'.map (-u + ·)).map Neg.neg := by
      rw [Multiset.map_map, Multiset.map_map]
      refine Multiset.map_congr rfl fun z _ => ?_
      simp only [Function.comp_apply]; ring
    rw [e, Multiset.prod_map_neg, Multiset.card_map, hm'.1]
    obtain ⟨h, -⟩ := h4 u ⟨φ, hφ⟩ 0
    refine sub_eq_zero.1 (congrArg Subtype.val (hB (⟨_, h⟩ - ((-1) ^ a * (m'.map (-u + ·)).prod) • ⟨φ, hφ⟩) fun ψ => ?_))
    obtain ⟨_, h', e'⟩ := h4 u ⟨φ, hφ⟩ ψ
    have e3 : (⟨_, h'⟩ : π'.V) = ((-1) ^ a * (m'.map (-u + ·)).prod) • ψ := Subtype.ext (by
      change (-1 : ℂ) ^ a • cap (ComplexEmbedding.conjugate τ) (-u) ψ.1 = _ • ψ.1
      rw [hm'.2 _ _ ψ.2, smul_smul])
    rw [map_sub, LinearMap.sub_apply, e', e3, map_smul, map_smul, LinearMap.smul_apply, sub_self]
  rw [hm.unique h5, Multiset.map_map]
  simp

end GlobalTheory.CapPair

end
