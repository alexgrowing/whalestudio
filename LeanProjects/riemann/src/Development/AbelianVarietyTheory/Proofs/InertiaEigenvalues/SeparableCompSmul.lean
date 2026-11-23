import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.NHkRow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodProjectorBaseChangeForms
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangePolynomialAnnihilatesDescentStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCommutationRealExpansionStatement

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.LiftLeaf GlobalTheory.SupLaw
open Formalism.IndefR.NX
open scoped TensorProduct

namespace GlobalTheory.GoodSS

theorem aeval_intertwine {K M N : Type} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (e : M ≃ₗ[K] N) (A : Module.End K M) (B : Module.End K N) (h : ∀ x, e (A x) = B (e x)) (p : K[X]) (x : M) :
    e (Polynomial.aeval A p x) = Polynomial.aeval B p (e x) := by
  have hpow : ∀ n : ℕ, ∀ x, e ((A ^ n) x) = (B ^ n) (e x) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih => intro x; rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq]
  | monomial n a => simp only [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      map_smul, hpow]

theorem separable_comp_smul {K : Type} [Field K] {p : K[X]} (hp : p.Separable) {a : K} (ha : a ≠ 0) :
    (p.comp (Polynomial.C a * Polynomial.X)).Separable := by
  have h1 := IsCoprime.map hp (Polynomial.compRingHom (Polynomial.C a * Polynomial.X))
  rw [Polynomial.coe_compRingHom_apply, Polynomial.coe_compRingHom_apply] at h1
  have h2 : IsCoprime (p.comp (Polynomial.C a * Polynomial.X)) (Polynomial.C a) :=
    ⟨0, Polynomial.C a⁻¹, by rw [zero_mul, zero_add, ← Polynomial.C_mul, inv_mul_cancel₀ ha, Polynomial.C_1]⟩
  have h3 : Polynomial.derivative (p.comp (Polynomial.C a * Polynomial.X)) =
      (Polynomial.derivative p).comp (Polynomial.C a * Polynomial.X) * Polynomial.C a := by
    rw [Polynomial.derivative_comp, Polynomial.derivative_mul, Polynomial.derivative_C, Polynomial.derivative_X,
      zero_mul, zero_add, mul_one, mul_comm]
  show IsCoprime _ _
  rw [h3]
  exact h1.mul_right h2

theorem aeval_smul_comp {K M : Type} [Field K] [AddCommGroup M] [Module K M] (B : Module.End K M) {c : K}
    (hc : c ≠ 0) (p : K[X]) (y : M) :
    Polynomial.aeval (c • B) (p.comp (Polynomial.C c⁻¹ * Polynomial.X)) y = Polynomial.aeval B p y := by
  rw [Polynomial.aeval_comp]
  congr 2
  rw [map_mul, Polynomial.aeval_C, Polynomial.aeval_X, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
    smul_smul, inv_mul_cancel₀ hc, one_smul]

set_option maxHeartbeats 800000 in

theorem hkF_separable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks]
    [Algebra Ks D.what₂.LL] (Rl : Formalism.IndefR.Links.RealDat3 D A3 Ks) (F : Formalism.IndefR.Links.Face3 D A3)
    (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : RatDat D.ntw) (Y : NExpRealS Rl cG S) (H : NExpRealH Rl cG S Y) : CommG D → HkComm D → NExpHeckeRowX Rl cG S Y H (fun j => goodProjW S j D.nexp.eLL0) →
    Rl.Char3 F → Rl.toRealDat.LUnif → Rl.toRealDat.LIntegral →
    (∀ i P P', P ∈ D.ntw.S0 i → IsConjPl D.host P P' → P' ∈ D.ntw.S0 i) →
    (∀ i, placesOver D.host.E 2 ⊆ (D.ntw.S0 i : Set (PlE D.host))) →
    (∀ i, ∀ Q ∈ Rl.Sb, Q ∈ D.ntw.S0 i) →
    ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b k P, HkIdx i k P →
      ∃ p : (FractionRing (D.ntw.O i))[X], p.Separable ∧
        ∀ x ∈ V0 D.nexp i j b, Polynomial.aeval (D.nexp.hkF i j b k P) p x = 0 := by
  intro hG hC hX hR hU hI hS0c hS02 hS0b i hi j hj b k P hk
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
  obtain ⟨q, hqs, hq⟩ := GlobalTheory.T.hecke_commutation_real_expansion Rl F cG S Y H hG hC hX hR hU hI hS0c hS02 hS0b i hi j h1 h2 b k P hk

  set rd : ↥D.LL0 →+* KB S i b := readLL0 S i b with hrd
  set hst := Y.rho j h1 h2
  set hχ := Y.chi j h1 h2
  set T0 := GlobalTheory.GoodSS.opK S j (H.hL j k P) (fun x hx => H.hs j h1 h2 k P x hx) with hT0
  set s := (D.nexp.eAlg i b).coeff.support with hs
  set a : G0g D.nd → ↥D.LL0 := fun g => D.nexp.eLL0 g * (chiL S j hχ (S.eG.symm g))⁻¹ with ha
  set ρ : G0g D.nd → Module.End S.Ks (FmK S j) := fun g => rhoKG S j hst (S.eG.symm g) with hρ

  have hcoef : ∀ g, (D.nexp.eAlg i b).coeff g = rd (D.nexp.eLL0 g) := fun g => by
    rw [D.nexp.eAlg_def]; rfl
  have hsupp : ∀ g, g ∉ s → D.nexp.eLL0 g = 0 := fun g hg => by
    have h0 : (D.nexp.eAlg i b).coeff g = 0 := Finsupp.notMem_support_iff.1 hg
    rw [hcoef] at h0
    exact (map_eq_zero_iff rd rd.injective).1 h0

  have hE' : GlobalTheory.GoodSS.goodProjectorBaseChangeForms S j hst hχ D.nexp.eLL0 = ∑ g ∈ s, a g • LinearMap.baseChange ↥D.LL0 (ρ g) := by
    unfold GlobalTheory.GoodSS.goodProjectorBaseChangeForms
    refine finsum_eq_sum_of_support_subset _ fun g hg => ?_
    by_contra hgs
    exact hg (by simp only [hsupp g hgs, zero_mul, zero_smul])

  have hdesc := GlobalTheory.T.baseChange_polynomial_annihilates_descent S.Ks ↥D.LL0 (KB S i b) (FmK S j) (G0g D.nd) rd (fun _ => rfl) T0 s ρ a q
    (fun z hz => hq z (hE' ▸ hz))
  set c := H.cHk i b k P with hc
  have hc0 : c ≠ 0 := by
    rw [hc, H.cHk_pow]
    exact pow_ne_zero _ (H.cHk_unit i b P).ne_zero

  set B : Module.End (FractionRing (D.ntw.O i)) (Fm S i j b) := LinearMap.baseChange (KB S i b) T0 with hB
  have hAB : ∀ x, Y.eF i j b h1 h2 (D.nexp.hkF i j b k P x) = (c • B) (Y.eF i j b h1 h2 x) := fun x =>
    H.hkEq i j b h1 h2 k P x hk.2.2.2 hk.2.2.1 hk.2.1

  have hE : ∀ x0, Y.eF i j b h1 h2 (eG D.nexp i j b x0) =
      (∑ g ∈ s, rd (a g) • LinearMap.baseChange (KB S i b) (ρ g)) (Y.eF i j b h1 h2 x0) := by
    intro x0
    have hact : ∀ g y, actG S i j b hst hχ g y =
        (rd (chiL S j hχ (S.eG.symm g)))⁻¹ • LinearMap.baseChange (KB S i b) (ρ g) y := fun _ _ => rfl
    rw [eG, MonoidAlgebra.lift_apply, Finsupp.sum, LinearMap.sum_apply, map_sum]
    refine (Finset.sum_congr rfl fun g _ => ?_).trans (LinearMap.sum_apply _ _ _).symm
    change Y.eF i j b h1 h2 ((D.nexp.eAlg i b).coeff g • D.nexp.actG i j b g x0) =
      rd (a g) • LinearMap.baseChange (KB S i b) (ρ g) (Y.eF i j b h1 h2 x0)
    rw [map_smul, Y.act i j b h1 h2 g x0, hact, hcoef]
    have hag : rd (a g) = rd (D.nexp.eLL0 g) * (rd (chiL S j hχ (S.eG.symm g)))⁻¹ := by
      simp only [ha, map_mul, map_inv₀]
    rw [hag]
    exact (mul_smul _ _ _).symm
  refine ⟨(q.map rd).comp (Polynomial.C c⁻¹ * Polynomial.X), ?_, ?_⟩
  · exact separable_comp_smul ((Polynomial.separable_map rd).2 hqs) (inv_ne_zero hc0)
  · rintro x ⟨x0, -, rfl⟩
    apply (Y.eF i j b h1 h2).injective
    rw [map_zero]
    refine (aeval_intertwine (Y.eF i j b h1 h2) _ (c • B) hAB _ _).trans ?_
    refine (aeval_smul_comp B hc0 _ _).trans ?_
    rw [hE]
    exact hdesc _ ⟨_, rfl⟩

end GlobalTheory.GoodSS
