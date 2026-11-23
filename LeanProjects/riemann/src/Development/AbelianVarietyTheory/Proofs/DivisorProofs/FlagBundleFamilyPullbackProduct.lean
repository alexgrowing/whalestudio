import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurveV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootIdx
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumPermApplyZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdIoiSubEqAntisymmMonomial

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open GlobalTheory.CovTestDR
open GlobalTheory.BcEigen
open GlobalTheory.BlockPoint

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BcEigen.FlagTele

section Algebra

variable {ι : Type} (r : ι → ℕ)

private def blockInv (a : ι) : Subalgebra ℝ (MvPolynomial (Σ a, Fin (r a)) ℝ) :=
  ⨅ (i : Fin (r a)) (i' : Fin (r a)) (_ : (i' : ℕ) = i + 1),
    AlgHom.equalizer (mid (⟨a, i⟩ : Σ a, Fin (r a)) ⟨a, i'⟩) (AlgHom.id ℝ _) ⊓
      AlgHom.equalizer (rename (Equiv.swap (⟨a, i⟩ : Σ a, Fin (r a)) ⟨a, i'⟩)) (AlgHom.id ℝ _)

private theorem mem_blockInv {a : ι} {Q : MvPolynomial (Σ a, Fin (r a)) ℝ} : Q ∈ blockInv r a ↔
    ∀ i i' : Fin (r a), (i' : ℕ) = i + 1 → mid (⟨a, i⟩ : Σ a, Fin (r a)) ⟨a, i'⟩ Q = Q ∧
      rename (Equiv.swap (⟨a, i⟩ : Σ a, Fin (r a)) ⟨a, i'⟩) Q = Q := by
  simp only [blockInv, Algebra.mem_iInf, Algebra.mem_inf, AlgHom.mem_equalizer, AlgHom.id_apply]

private theorem X_mem_blockInv {a b : ι} (h : b ≠ a) (j : Fin (r b)) : X (⟨b, j⟩ : Σ a, Fin (r a)) ∈ blockInv r a := by
  have hn (i : Fin (r a)) : (⟨b, j⟩ : Σ a, Fin (r a)) ≠ ⟨a, i⟩ := fun e => h (congrArg Sigma.fst e)
  refine (mem_blockInv r).2 fun i i' _ => ⟨mid_X_of_ne (hn i) (hn i'), ?_⟩
  rw [rename_X, Equiv.swap_apply_of_ne_of_ne (hn i) (hn i')]

private theorem C_mem_blockInv (a : ι) (c : ℝ) : (C c : MvPolynomial (Σ a, Fin (r a)) ℝ) ∈ blockInv r a :=
  (blockInv r a).algebraMap_mem c

private theorem eSum_mem_blockInv (a b : ι) : eSum r b ∈ blockInv r a := by
  by_cases h : b = a
  swap
  · exact Subalgebra.sum_mem _ fun j _ => X_mem_blockInv r h j
  subst h
  have hinj : Function.Injective (@Sigma.mk ι (fun a => Fin (r a)) b) := sigma_mk_injective
  refine (mem_blockInv r).2 fun i i' hi => ⟨?_, ?_⟩
  · have hne : i ≠ i' := fun e => by rw [e] at hi; omega
    have key (f : Fin (r b) → MvPolynomial (Σ a, Fin (r a)) ℝ) :
        ∑ z, f z = f i + f i' + ∑ z ∈ (Finset.univ.erase i).erase i', f z := by
      rw [add_assoc, Finset.add_sum_erase _ _ (Finset.mem_erase.2 ⟨hne.symm, Finset.mem_univ _⟩),
        Finset.add_sum_erase _ _ (Finset.mem_univ _)]
    rw [eSum, map_sum, key, key fun j => X ⟨b, j⟩]
    simp only [mid_X_left, mid_X_right]
    rw [Finset.sum_congr rfl fun z hz => mid_X_of_ne (hinj.ne (Finset.mem_erase.1 (Finset.mem_erase.1 hz).2).1)
      (hinj.ne (Finset.mem_erase.1 hz).1)]
    have h2 : (2 : MvPolynomial (Σ a, Fin (r a)) ℝ) * C (1 / 2) = 1 := by
      rw [← map_ofNat C 2, ← map_mul]; simp
    linear_combination (X ⟨b, i⟩ + X ⟨b, i'⟩) * h2
  · rw [eSum, map_sum]
    simp only [rename_X, hinj.swap_apply]
    exact Equiv.sum_comp (Equiv.swap i i') fun j => (X ⟨b, j⟩ : MvPolynomial (Σ a, Fin (r a)) ℝ)

private theorem monPt_mem_blockInv {a b : ι} (h : b ≠ a) : monPt r b ∈ blockInv r a :=
  Subalgebra.prod_mem _ fun j _ => Subalgebra.pow_mem _ (Subalgebra.neg_mem _ (X_mem_blockInv r h j)) _

private theorem vdm_mem_blockInv {a b : ι} (h : b ≠ a) : C ((r b).factorial : ℝ)⁻¹ * vdm r b ∈ blockInv r a :=
  Subalgebra.mul_mem _ (C_mem_blockInv r a _) (Subalgebra.prod_mem _ fun j _ => Subalgebra.prod_mem _ fun j' _ =>
    Subalgebra.sub_mem _ (X_mem_blockInv r h j') (X_mem_blockInv r h j))

private theorem linE_mem_blockInv [Fintype ι] (a : ι) (s : ι → ℝ) : linE r s ∈ blockInv r a :=
  Subalgebra.sum_mem _ fun b _ => Subalgebra.mul_mem _ (C_mem_blockInv r a _) (eSum_mem_blockInv r a b)

private theorem restrict_swap (Ψ : MvPolynomial (Σ a, Fin (r a)) ℝ →ₗ[ℝ] ℝ) (a : ι)
    (hΨ : ∀ i i' : Fin (r a), (i' : ℕ) = i + 1 → ∀ P,
      Ψ (rename (Equiv.swap (⟨a, i⟩ : Σ a, Fin (r a)) ⟨a, i'⟩) P) = -Ψ P) (S : MvPolynomial (Σ a, Fin (r a)) ℝ)
    (hS : ∀ i i' : Fin (r a), (i' : ℕ) = i + 1 → rename (Equiv.swap (⟨a, i⟩ : Σ a, Fin (r a)) ⟨a, i'⟩) S = S)
    (i i' : Fin (r a)) (hi : (i' : ℕ) = i + 1) (P : MvPolynomial (Fin (r a)) ℝ) :
    Ψ (S * rename (@Sigma.mk ι (fun a => Fin (r a)) a) (rename (Equiv.swap i i') P)) =
      -Ψ (S * rename (@Sigma.mk ι (fun a => Fin (r a)) a) P) := by
  have hinj : Function.Injective (@Sigma.mk ι (fun a => Fin (r a)) a) := sigma_mk_injective
  rw [← hΨ i i' hi, map_mul (rename _), hS i i' hi, rename_rename, rename_rename]
  congr 4
  funext z
  exact (hinj.swap_apply i i' z).symm

private theorem rename_monPt (a : ι) : rename (@Sigma.mk ι (fun a => Fin (r a)) a) (∏ i : Fin (r a), (-X i) ^ (r a - 1 - (i : ℕ))) =
    monPt r a := by
  simp only [map_prod, map_pow, map_neg, rename_X, monPt]

private theorem rename_vdm (a : ι) : rename (@Sigma.mk ι (fun a => Fin (r a)) a)
    (∏ i : Fin (r a), ∏ i' ∈ Finset.Ioi i, (X i' - X i)) = vdm r a := by
  simp only [map_prod, map_sub, rename_X, vdm]

private theorem rename_eSum (a : ι) : rename (@Sigma.mk ι (fun a => Fin (r a)) a) (∑ i : Fin (r a), X i) = eSum r a := by
  simp only [map_sum, rename_X, eSum]

private theorem alt_vdm (Ψ : MvPolynomial (Σ a, Fin (r a)) ℝ →ₗ[ℝ] ℝ) (a : ι)
    (hΨ : ∀ i i' : Fin (r a), (i' : ℕ) = i + 1 → ∀ P,
      Ψ (rename (Equiv.swap (⟨a, i⟩ : Σ a, Fin (r a)) ⟨a, i'⟩) P) = -Ψ P) (Q : MvPolynomial (Σ a, Fin (r a)) ℝ)
    (hQ : Q ∈ blockInv r a) : Ψ (Q * (C ((r a).factorial : ℝ)⁻¹ * vdm r a)) = Ψ (Q * monPt r a) := by
  let ρ : MvPolynomial (Fin (r a)) ℝ →ₐ[ℝ] MvPolynomial (Σ a, Fin (r a)) ℝ := rename (@Sigma.mk ι (fun a => Fin (r a)) a)
  let ψ : MvPolynomial (Fin (r a)) ℝ →ₗ[ℝ] ℝ := Ψ ∘ₗ LinearMap.mulLeft ℝ Q ∘ₗ ρ.toLinearMap
  have hF (P) : ψ P = Ψ (Q * rename (@Sigma.mk ι (fun a => Fin (r a)) a) P) := rfl
  have halt := alt_of_adj' ψ fun i i' hi P => restrict_swap r Ψ a hΨ Q (fun i i' hi => ((mem_blockInv r).1 hQ i i' hi).2) i i' hi P
  have h₁ : Ψ (Q * vdm r a) = (r a).factorial * Ψ (Q * monPt r a) := by
    rw [← rename_vdm, ← rename_monPt, ← hF, ← hF, GlobalTheory.prod_Ioi_sub_eq_antisymm_monomial, map_sum]
    rw [Finset.sum_congr rfl (g := fun _ => ψ (∏ i : Fin (r a), (-X i) ^ (r a - 1 - (i : ℕ)))) fun σ _ => ?_]
    · rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
    · have s2 : ((Equiv.Perm.sign σ : ℤ) : ℝ) * ((Equiv.Perm.sign σ : ℤ) : ℝ) = 1 := by
        rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]; simp
      rw [map_smul, halt, smul_eq_mul, ← mul_assoc, s2, one_mul]
  have h₀ : ((r a).factorial : ℝ) ≠ 0 := by positivity
  rw [mul_left_comm, ← smul_eq_C_mul, map_smul, h₁, smul_eq_mul, inv_mul_cancel_left₀ h₀]

variable [Fintype ι]

private theorem block_square_telescoping_harmonic (Φ Ψ : MvPolynomial (Σ a, Fin (r a)) ℝ →ₗ[ℝ] ℝ) (a : ι)
    (hΨ : ∀ i i' : Fin (r a), (i' : ℕ) = i + 1 → ∀ P,
      Ψ (rename (Equiv.swap (⟨a, i⟩ : Σ a, Fin (r a)) ⟨a, i'⟩) P) = -Ψ P)
    (hΦ : ∀ i i' : Fin (r a), (i' : ℕ) = i + 1 → ∀ (k : ℕ) (M : MvPolynomial (Σ a, Fin (r a)) ℝ),
      Φ ((X ⟨a, i'⟩ - X ⟨a, i⟩) ^ (2 * k) * mid ⟨a, i⟩ ⟨a, i'⟩ M) =
        oddHarm k * Ψ ((X ⟨a, i'⟩ - X ⟨a, i⟩) ^ (2 * k - 1) * mid ⟨a, i⟩ ⟨a, i'⟩ M))
    (Q : MvPolynomial (Σ a, Fin (r a)) ℝ) (hQ : Q ∈ blockInv r a) :
    Φ (sq2 r * Q * (monPt r a - C ((r a).factorial : ℝ)⁻¹ * vdm r a)) =
      -(((r a : ℝ) - 1) / (r a : ℝ) * Ψ (Q * (eSum r a * monPt r a))) := by
  have hinj : Function.Injective (@Sigma.mk ι (fun a => Fin (r a)) a) := sigma_mk_injective
  let ρ : MvPolynomial (Fin (r a)) ℝ →ₐ[ℝ] MvPolynomial (Σ a, Fin (r a)) ℝ := rename (@Sigma.mk ι (fun a => Fin (r a)) a)
  let F (Θ : MvPolynomial (Σ a, Fin (r a)) ℝ →ₗ[ℝ] ℝ) (S : MvPolynomial (Σ a, Fin (r a)) ℝ) :
      MvPolynomial (Fin (r a)) ℝ →ₗ[ℝ] ℝ := Θ ∘ₗ LinearMap.mulLeft ℝ S ∘ₗ ρ.toLinearMap
  have hF (Θ S P) : F Θ S P = Θ (S * rename (@Sigma.mk ι (fun a => Fin (r a)) a) P) := rfl
  have hQs (i i' : Fin (r a)) (hi : (i' : ℕ) = i + 1) := ((mem_blockInv r).1 hQ i i' hi).2
  have hps (i i' : Fin (r a)) (hi : (i' : ℕ) = i + 1) :
      rename (Equiv.swap (⟨a, i⟩ : Σ a, Fin (r a)) ⟨a, i'⟩) (sq2 r * Q) = sq2 r * Q := by
    rw [map_mul (rename _), hQs i i' hi, sq2, map_sum (rename _)]
    simp only [map_pow, rename_X]
    rw [Equiv.sum_comp (Equiv.swap (⟨a, i⟩ : Σ a, Fin (r a)) ⟨a, i'⟩) fun z => (X z ^ 2 : MvPolynomial _ ℝ)]
  have key := block_algebra (r a) (F Φ (sq2 r * Q)) (F Ψ Q) (restrict_swap r Ψ a hΨ Q hQs) fun i i' hi k d M hM hd => by
    have hne : (⟨a, i⟩ : Σ a, Fin (r a)) ≠ ⟨a, i'⟩ := hinj.ne fun e => by rw [e] at hi; omega
    have hlow : oddHarm k * F Ψ (sq2 r * Q) ((X i' - X i) ^ (2 * k - 1) * mid i i' M) = 0 := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp
      have hh := (((isHomogeneous_X ℝ i').sub (isHomogeneous_X ℝ i)).pow (2 * k - 1)).mul (isHomogeneous_mid i i' hM)
      rw [GlobalTheory.T.alternating_functional_low_degree _ _ (alt_of_adj' (F Ψ (sq2 r * Q)) (restrict_swap r Ψ a hΨ _ hps)) _ _ hh (by omega), mul_zero]
    have hu (m : ℕ) : rename (@Sigma.mk ι (fun a => Fin (r a)) a) ((X i' - X i) ^ m * mid i i' M) =
        (X ⟨a, i'⟩ - X ⟨a, i⟩) ^ m * mid ⟨a, i⟩ ⟨a, i'⟩ (rename (@Sigma.mk ι (fun a => Fin (r a)) a) M) := by
      rw [map_mul, map_pow, map_sub, rename_X, rename_X, rename_mid hinj]
    rw [hF, hu] at hlow
    rw [hF, hF, hu, hu]
    exact powerSum_step hne Φ Ψ (hΦ i i' hi) Q _ ((mem_blockInv r).1 hQ i i' hi).1 k hlow
  rw [hF, hF, hF, map_mul (rename _), rename_monPt, rename_vdm, rename_eSum] at key
  have h₀ : ((r a).factorial : ℝ) ≠ 0 := by positivity
  rw [mul_sub, map_sub, mul_left_comm, ← smul_eq_C_mul, map_smul, smul_eq_mul]
  have e : Φ (sq2 r * Q * vdm r a) = (r a).factorial * Φ (sq2 r * Q * monPt r a) +
      ((r a : ℝ) - 1) * ((r a - 1).factorial : ℝ) * Ψ (Q * (eSum r a * monPt r a)) := by linear_combination -key
  rw [e]
  rcases Nat.eq_zero_or_pos (r a) with h | h
  · have : IsEmpty (Fin (r a)) := by rw [h]; infer_instance
    have z : eSum r a = 0 := Finset.sum_of_isEmpty _
    rw [z, zero_mul, mul_zero, map_zero]
    field_simp
    ring
  · have h₁ : (r a : ℝ) ≠ 0 := by positivity
    have h₂ : ((r a - 1).factorial : ℝ) ≠ 0 := by positivity
    rw [← Nat.mul_factorial_pred h.ne']
    push_cast
    field_simp
    ring

omit [Fintype ι] in

private theorem alt_prod (Ψ : MvPolynomial (Σ a, Fin (r a)) ℝ →ₗ[ℝ] ℝ)
    (hΨ : ∀ a Q, Q ∈ blockInv r a → Ψ (Q * (C ((r a).factorial : ℝ)⁻¹ * vdm r a)) = Ψ (Q * monPt r a)) (S : Finset ι)
    (W : MvPolynomial (Σ a, Fin (r a)) ℝ) (hW : ∀ a ∈ S, W ∈ blockInv r a) :
    Ψ (W * ∏ a ∈ S, (C ((r a).factorial : ℝ)⁻¹ * vdm r a)) = Ψ (W * ∏ a ∈ S, monPt r a) := by
  induction S using Finset.induction_on generalizing W with
  | empty => simp
  | insert a S ha ih =>
    have hne (b) (hb : b ∈ S) : a ≠ b := fun e => ha (e ▸ hb)
    rw [Finset.prod_insert ha, Finset.prod_insert ha, ← mul_assoc, ih _ fun b hb =>
      Subalgebra.mul_mem _ (hW b (Finset.mem_insert_of_mem hb)) (vdm_mem_blockInv r (hne b hb)), mul_right_comm,
      hΨ a _ (Subalgebra.mul_mem _ (hW a (Finset.mem_insert_self _ _))
        (Subalgebra.prod_mem _ fun b hb => monPt_mem_blockInv r (hne b hb).symm))]
    congr 1
    ring

private theorem telescope (Φ Ψ : MvPolynomial (Σ a, Fin (r a)) ℝ →ₗ[ℝ] ℝ)
    (hΨ : ∀ a Q, Q ∈ blockInv r a → Ψ (Q * (C ((r a).factorial : ℝ)⁻¹ * vdm r a)) = Ψ (Q * monPt r a))
    (hΦ : ∀ a Q, Q ∈ blockInv r a → Φ (sq2 r * Q * (monPt r a - C ((r a).factorial : ℝ)⁻¹ * vdm r a)) =
      -(((r a : ℝ) - 1) / (r a : ℝ) * Ψ (Q * (eSum r a * monPt r a)))) (S : Finset ι)
    (W : MvPolynomial (Σ a, Fin (r a)) ℝ) (hW : ∀ a ∈ S, W ∈ blockInv r a) :
    Φ (sq2 r * W * (∏ a ∈ S, monPt r a - ∏ a ∈ S, (C ((r a).factorial : ℝ)⁻¹ * vdm r a))) =
      -∑ a ∈ S, ((r a : ℝ) - 1) / (r a : ℝ) * Ψ (eSum r a * W * ∏ a ∈ S, monPt r a) := by
  induction S using Finset.induction_on generalizing W with
  | empty => simp
  | insert a S ha ih =>
    have hne (b) (hb : b ∈ S) : a ≠ b := fun e => ha (e ▸ hb)
    have hWF (b) (hb : b ∈ S) : W * monPt r a ∈ blockInv r b :=
      Subalgebra.mul_mem _ (hW b (Finset.mem_insert_of_mem hb)) (monPt_mem_blockInv r (hne b hb))
    have e₁ := ih _ hWF
    have e₂ := hΦ a _ (Subalgebra.mul_mem _ (hW a (Finset.mem_insert_self _ _))
      (Subalgebra.prod_mem _ fun b hb => vdm_mem_blockInv r (hne b hb).symm))
    have e₃ := alt_prod r Ψ hΨ S (eSum r a * (W * monPt r a)) fun b hb =>
      Subalgebra.mul_mem _ (eSum_mem_blockInv r b a) (hWF b hb)
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    generalize ∏ a ∈ S, (C ((r a).factorial : ℝ)⁻¹ * vdm r a) = G at *
    generalize ∏ a ∈ S, monPt r a = F at *
    generalize C ((r a).factorial : ℝ)⁻¹ * vdm r a = g at *
    rw [show W * G * (eSum r a * monPt r a) = eSum r a * (W * monPt r a) * G by ring, e₃] at e₂
    rw [show sq2 r * W * (monPt r a * F - g * G) = sq2 r * (W * monPt r a) * (F - G) + sq2 r * (W * G) * (monPt r a - g) by ring,
      map_add, e₁, e₂]
    simp only [mul_assoc]
    ring

end Algebra

theorem _root_.GlobalTheory.T.flag_bundle_family_pullback_product : Hypotheses2 → HypothesesH → RegularAlteration → ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B]
    [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d D : ℕ), IsArithVar q d → IsArithVar p D → ∀ (π : Y ⟶ B)
    (w : π ≫ q = p) (ι : Type) [Fintype ι] (E : ι → B.Modules) (r : ι → ℕ) (h : ∀ a, VMetric q (E a) (r a))
    (H : ∀ a, (h a).IsCInf) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), IsFlagBundle π E r fl →
    ∀ Φ Ψ : MvPolynomial (Σ a, Fin (r a)) ℝ →ₗ[ℝ] ℝ,
      IsArFun (fun z : Σ a, Fin (r a) => VMetric.grLB (fl z.1) z.2 ((H z.1).pull π w)) D Φ →
      IsGeoFun (fun z : Σ a, Fin (r a) => VMetric.grLB (fl z.1) z.2 ((H z.1).pull π w)) D Ψ →
      ∀ (s : ι → ℝ) (m : ℕ), Φ (sq2 r * linE r s ^ m * (∏ a, monPt r a - ∏ a, (C ((r a).factorial : ℝ)⁻¹ * vdm r a))) =
        -∑ a, ((r a : ℝ) - 1) / (r a : ℝ) * Ψ (eSum r a * linE r s ^ m * ∏ a, monPt r a) := by
  intro hP _ HR k _ B Y _ _ q p d D hB hY π w ι _ E r h H fl hfl Φ Ψ hΦ hΨ s m
  have HA : ArCalc := hP.p4
  have hS : SwapFl swapG :=
    GlobalTheory.CovTest.SwapFlProof.swapFl_of_swap2 HA _ homog_swapG (GlobalTheory.CovTest.swap2_of_swapRegular HA HR GlobalTheory.T.generic_degree_pullback_formula _ (GlobalTheory.T.arith_calc_swap_regular HA))
  have hG := GlobalTheory.CovTest.GeoSwap.geo_swap HA HR k B Y q p d D hB hY π w ι E r h H fl hfl Ψ hΨ
  refine telescope r Φ Ψ (fun a => alt_vdm r Ψ a (hG a)) (fun a => block_square_telescoping_harmonic r Φ Ψ a (hG a) fun i i' hi =>
    GlobalTheory.T.swap_polynomial_identity _ _ _ (sigma_mk_injective.ne fun e => by rw [e] at hi; omega) D Φ Ψ hΦ.2 hΨ.2 ?_) Finset.univ _
    fun a _ => Subalgebra.pow_mem _ (linE_mem_blockInv r a s) m
  intro n
  convert hS k B Y q p d D hB hY π w ι E r h H fl hfl Φ Ψ hΦ hΨ a i i' hi n

end GlobalTheory.BcEigen.FlagTele

end
