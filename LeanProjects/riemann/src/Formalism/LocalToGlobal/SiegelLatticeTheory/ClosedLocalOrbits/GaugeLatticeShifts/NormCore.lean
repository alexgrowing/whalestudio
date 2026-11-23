import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GGMirabolic

noncomputable section

open scoped Classical ComplexConjugate

namespace Formalism.L2.SG.NormCut

section Abs

theorem colSum {G : Type*} [Group G] [Fintype G] (U : Set G) (p : G → ℂ) (h0 : ∀ x, x ∉ U → p x = 0)
    (hr : ∀ x, ∀ w ∈ U, p (x * w) = p x * p w) (hn : ∀ w ∈ U, conj (p w) * p w = 1) (i j : G) :
    ∑ s : G, ∑ s' : G, conj (p (s⁻¹ * i * s')) * p (s⁻¹ * j * s') =
      (Nat.card U : ℂ) * ∑ s : G, conj (p (s⁻¹ * (i * j⁻¹) * s)) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← Equiv.sum_comp (Equiv.mulLeft (j⁻¹ * s))]
  simp only [Equiv.coe_mulLeft]
  have h1 : ∀ w : G, conj (p (s⁻¹ * i * (j⁻¹ * s * w))) * p (s⁻¹ * j * (j⁻¹ * s * w)) =
      if w ∈ U then conj (p (s⁻¹ * (i * j⁻¹) * s)) else 0 := by
    intro w
    have hw : s⁻¹ * j * (j⁻¹ * s * w) = w := by group
    have hw2 : s⁻¹ * i * (j⁻¹ * s * w) = s⁻¹ * (i * j⁻¹) * s * w := by group
    rw [hw, hw2]
    split_ifs with h
    · rw [hr _ w h, map_mul, mul_assoc, hn w h, mul_one]
    · rw [h0 w h, mul_zero]
  simp only [h1]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  have hc : ((Finset.univ.filter fun w => w ∈ U).card : ℂ) = (Nat.card U : ℂ) := by
    rw [Nat.card_eq_fintype_card, ← Set.toFinset_card]
    congr 2
    ext w
    simp
  rw [hc]

theorem orbitSum {G C : Type*} [Group G] [Fintype G] [Fintype C] (A U : Set G) (s : C → G)
    (hb : Function.Bijective (fun x : A × C × U => (x.1 : G) * s x.2.1 * (x.2.2 : G))) (f : G → ℂ)
    (hf : ∀ x, ∀ a ∈ A, ∀ w ∈ U, f (a * x * w) = f x) :
    ∑ x : G, f x = (Nat.card A : ℂ) * (Nat.card U : ℂ) * ∑ c : C, f (s c) := by
  rw [← Function.Bijective.sum_comp hb f]
  simp only [Fintype.sum_prod_type]
  have h1 : ∀ (a : A) (c : C) (w : U), f ((a : G) * s c * (w : G)) = f (s c) :=
    fun a c w => hf (s c) a a.2 w w.2
  simp only [h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

def GamProdSum : Prop :=
  ∀ (ι : Type) [Fintype ι] (Fq : ι → Type) [∀ v, Field (Fq v)] [∀ v, Fintype (Fq v)] (k : ℕ)
    (ψ : ∀ v, AddChar (Fq v) ℂ) (x : ∀ v, GL (Fin k) (Fq v)),
    Formalism.L2.SG.GGMirabolic.gamProd ψ x =
      (∏ v, (Formalism.L2.SG.GGMirabolic.cardU (Fq v) k : ℂ))⁻¹ *
        ∑ y : (∀ v, GL (Fin k) (Fq v)), ∏ v, Formalism.L2.SG.GGMirabolic.psiNat (ψ v) ((y * x * y⁻¹) v) ∧
    Nat.card {x : ∀ v, GL (Fin k) (Fq v) // ∀ v, Formalism.L2.SG.GGMirabolic.IsUni k (x v)} =
      ∏ v, Formalism.L2.SG.GGMirabolic.cardU (Fq v) k

def PsiNatEquiv : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (k : ℕ) (ψ₀ : AddChar F ℂ) (x w : GL (Fin k) F),
    Formalism.L2.SG.GGMirabolic.IsUni k w →
    Formalism.L2.SG.GGMirabolic.psiNat ψ₀ (x * w) =
              Formalism.L2.SG.GGMirabolic.psiNat ψ₀ x * Formalism.L2.SG.GGMirabolic.psiNat ψ₀ w ∧
      Formalism.L2.SG.GGMirabolic.psiNat ψ₀ (w * x) =
        Formalism.L2.SG.GGMirabolic.psiNat ψ₀ w * Formalism.L2.SG.GGMirabolic.psiNat ψ₀ x ∧
      conj (Formalism.L2.SG.GGMirabolic.psiNat ψ₀ w) * Formalism.L2.SG.GGMirabolic.psiNat ψ₀ w = 1

def hsV {Wq Wp : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] (A : Wq →L[ℂ] Wp) :
    PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp) :=
  WithLp.toLp 2 (fun i => A (stdOrthonormalBasis ℂ Wq i))

def blockOf {C C' V V' : Type} [Fintype C] [Fintype C'] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']
    (A : PiLp 2 (fun _ : C' => V') →L[ℂ] PiLp 2 (fun _ : C => V)) (ρ : C) (ρ' : C') : V' →L[ℂ] V :=
  LinearMap.toContinuousLinearMap
    ((PiLp.proj 2 (fun _ : C => V) ρ).toLinearMap ∘ₗ A.toLinearMap ∘ₗ
      (WithLp.linearEquiv 2 ℂ (C' → V')).symm.toLinearMap ∘ₗ LinearMap.single ℂ (fun _ : C' => V') ρ')

def HSBlocks : Prop :=
  ∀ (C C' V V' : Type) [Fintype C] [Fintype C'] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']
    (A B : PiLp 2 (fun _ : C' => V') →L[ℂ] PiLp 2 (fun _ : C => V)),
    inner ℂ (hsV A) (hsV B) =
      ∑ ρ, ∑ ρ', inner ℂ (hsV (blockOf A ρ ρ'))
        (hsV (blockOf B ρ ρ'))

end Abs

end Formalism.L2.SG.NormCut
