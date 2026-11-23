import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.BlockTriangularOfSubOne
import Formalism.MirabolicMackeyTheory.MirabolicIsMackey

noncomputable section

open GlobalTheory.FiniteGL Formalism.L2.Indef.Tree Formalism.EigenvalueLevelCeiling

namespace PositivityTheory.Mirab.Dim

variable {k : Type} [Field k] [Fintype k] (n : ℕ)

theorem index_uniSub : (uniSub k n).index = ∏ i ∈ Finset.Ico 1 (n + 1), (Fintype.card k ^ i - 1) :=
  index_Uv (kf := fun _ : Unit => k) (mirab_levelGroups (fun _ : Unit => k) n) ()

abbrev Cos (k : Type) [Field k] [Fintype k] (n : ℕ) : Type := Quotient (QuotientGroup.rightRel (uniSub k n))

def cls (x : mirabSub k n) : Cos k n := Quotient.mk (QuotientGroup.rightRel (uniSub k n)) x

def rep (x : mirabSub k n) : mirabSub k n := (cls n x).out

theorem rep_mem (x : mirabSub k n) : x * (rep n x)⁻¹ ∈ uniSub k n :=
  QuotientGroup.rightRel_apply.1 (Quotient.mk_out (s := QuotientGroup.rightRel (uniSub k n)) x)

theorem cls_mul (u : uniSub k n) (x : mirabSub k n) : cls n ((u : mirabSub k n) * x) = cls n x := by
  unfold cls
  refine Quotient.sound (QuotientGroup.rightRel_apply.2 ?_)
  rw [mul_inv_rev, mul_inv_cancel_left]
  exact inv_mem u.2

theorem cls_out (c : Cos k n) : cls n c.out = c := Quotient.out_eq c

variable (ψ₀ : AddChar k ℂ)

def psiExt (y : mirabSub k n) : ℂ := by
  classical exact if h : y ∈ uniSub k n then genericChar n ψ₀ ⟨y, h⟩ else 0

theorem psiExt_of_mem (u : uniSub k n) : psiExt n ψ₀ (u : mirabSub k n) = genericChar n ψ₀ u := by
  unfold psiExt
  rw [dif_pos u.2]

theorem psiExt_mul (u : uniSub k n) (y : mirabSub k n) (hy : y ∈ uniSub k n) :
    psiExt n ψ₀ ((u : mirabSub k n) * y) = genericChar n ψ₀ u * psiExt n ψ₀ y := by
  have h := psiExt_of_mem n ψ₀ (u * ⟨y, hy⟩)
  rw [map_mul, ← psiExt_of_mem n ψ₀ ⟨y, hy⟩] at h
  exact h

theorem psiExt_one : psiExt n ψ₀ 1 = 1 := by
  have h := psiExt_of_mem n ψ₀ 1
  rw [OneMemClass.coe_one, map_one] at h
  exact h

def restr : MirabInducedSpace n ψ₀ →ₗ[ℂ] (Cos k n → ℂ) where
  toFun f c := (f : mirabSub k n → ℂ) c.out
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def extFun (g : Cos k n → ℂ) (x : mirabSub k n) : ℂ := psiExt n ψ₀ (x * (rep n x)⁻¹) * g (cls n x)

theorem extFun_mem (g : Cos k n → ℂ) : extFun n ψ₀ g ∈ MirabInducedSpace n ψ₀ := by
  rw [mem_mirabInducedSpace]
  intro u x
  unfold extFun
  have hr : rep n ((u : mirabSub k n) * x) = rep n x := by unfold rep; rw [cls_mul]
  rw [hr, cls_mul, mul_assoc, psiExt_mul n ψ₀ u _ (rep_mem n x), mul_assoc]

theorem eq_at_rep (f : MirabInducedSpace n ψ₀) (x : mirabSub k n) :
    (f : mirabSub k n → ℂ) x =
      genericChar n ψ₀ ⟨_, rep_mem n x⟩ * (f : mirabSub k n → ℂ) (rep n x) := by
  have h := (mem_mirabInducedSpace n ψ₀ f).1 f.2 ⟨_, rep_mem n x⟩ (rep n x)
  have e : ((⟨_, rep_mem n x⟩ : uniSub k n) : mirabSub k n) * rep n x = x := inv_mul_cancel_right x (rep n x)
  rw [← h, e]

theorem restr_injective : Function.Injective (restr n ψ₀) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro f hf
  apply Subtype.ext
  funext x
  have h0 : (f : mirabSub k n → ℂ) (rep n x) = 0 := congrFun hf (cls n x)
  rw [eq_at_rep n ψ₀ f x, h0, mul_zero]
  rfl

theorem restr_surjective : Function.Surjective (restr n ψ₀) := by
  intro g
  refine ⟨⟨extFun n ψ₀ g, extFun_mem n ψ₀ g⟩, ?_⟩
  funext c
  show extFun n ψ₀ g c.out = g c
  unfold extFun
  have hr : rep n c.out = c.out := by unfold rep; rw [cls_out]
  rw [hr, cls_out, mul_inv_cancel, psiExt_one, one_mul]

theorem finrank_mirabInducedSpace_eq_index (ψ₀ : AddChar k ℂ) :
    Module.finrank ℂ (MirabInducedSpace n ψ₀) = (uniSub k n).index := by
  classical
  have e := LinearEquiv.ofBijective (restr n ψ₀) ⟨restr_injective n ψ₀, restr_surjective n ψ₀⟩
  rw [e.finrank_eq, Module.finrank_fintype_fun_eq_card, Subgroup.index_eq_card, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel (uniSub k n))

theorem finrank_mirabInducedSpace (ψ₀ : AddChar k ℂ) :
    Module.finrank ℂ (MirabInducedSpace n ψ₀) = ∏ i ∈ Finset.Ico 1 (n + 1), (Fintype.card k ^ i - 1) := by
  rw [finrank_mirabInducedSpace_eq_index, index_uniSub]

end PositivityTheory.Mirab.Dim
