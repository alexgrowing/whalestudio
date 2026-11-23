import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.ContCoef
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwMonoidExt
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.IndexNeZero

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

namespace UpperTheory.V.Z.Sym.Al.ExtChar

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem val_eq (x : kˣ) : valuation k (x : k) = uniformizer k ^ ord k x := by
  have h := UpperTheory.V.Hi.GlAx.val_div_ord x
  rw [Units.val_div_eq_div_val, map_div₀, UpperTheory.V.Hi.GlAx.val_zpow] at h
  exact (div_eq_one_iff_eq (zpow_pos UpperTheory.V.Hi.GlAx.unif_pos _).ne').1 h

private theorem sdom_of_exp (u : Fin n → kˣ) (e : Fin n → ℤ)
    (hv : ∀ i, valuation k (u i : k) = uniformizer k ^ e i) (he : ∀ i j, i < j → e j < e i) : Sig.SDom u := by
  intro i j hij
  rw [hv, hv]
  exact zpow_lt_zpow_right_of_lt_one₀ UpperTheory.V.Hi.GlAx.unif_pos uniformizer_lt_one (he i j hij)

private noncomputable def rho (n : ℕ) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (m : ℤ) : Fin n → kˣ := fun i => UpperTheory.V.Hi.unif k ^ (-(m * (i : ℕ)))

private theorem rho_sdom {m : ℤ} (hm : 0 < m) : Sig.SDom (rho n k m) := by
  refine sdom_of_exp _ (fun i => -(m * ((i : ℕ) : ℤ))) (fun i => UpperTheory.V.Hi.GlAx.val_zpow _) fun i j hij => ?_
  have : ((i : ℕ) : ℤ) < ((j : ℕ) : ℤ) := by exact_mod_cast hij
  nlinarith

private theorem sdom_mul {d d' : Fin n → kˣ} (h : Sig.SDom d) (h' : Sig.SDom d') : Sig.SDom (d * d') := by
  intro i j hij
  simp only [Pi.mul_apply, Units.val_mul, map_mul]
  exact mul_lt_mul'' (h i j hij) (h' i j hij) zero_le' zero_le'

private theorem sdom_mul_unit {d u : Fin n → kˣ} (h : Sig.SDom d) (hu : ∀ i, u i ∈ UpperTheory.V.Hi.Uo k) : Sig.SDom (d * u) := by
  intro i j hij
  have h1 : ∀ i, valuation k (u i : k) = 1 := hu
  simp only [Pi.mul_apply, Units.val_mul, map_mul, h1, mul_one]
  exact h i j hij

private theorem exists_div (t : Fin n → kˣ) : ∃ a b : Fin n → kˣ, Sig.SDom a ∧ Sig.SDom b ∧ t = a * b⁻¹ := by
  let B : ℤ := ∑ i, |ord k (t i)|
  have hB : ∀ i, |ord k (t i)| ≤ B := fun i =>
    Finset.single_le_sum (f := fun i => |ord k (t i)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hm : 0 < 2 * B + 1 := by omega
  refine ⟨t * rho n k (2 * B + 1), rho n k (2 * B + 1), ?_, rho_sdom hm, by simp⟩
  refine sdom_of_exp _ (fun i => ord k (t i) + -((2 * B + 1) * ((i : ℕ) : ℤ))) (fun i => ?_) fun i j hij => ?_
  · rw [Pi.mul_apply, Units.val_mul, map_mul, val_eq, rho, UpperTheory.V.Hi.GlAx.val_zpow,
      zpow_add₀ UpperTheory.V.Hi.GlAx.unif_pos.ne']
  · have h0 : ((i : ℕ) : ℤ) + 1 ≤ ((j : ℕ) : ℤ) := by exact_mod_cast hij
    have h1 := abs_le.1 (hB i)
    have h2 := abs_le.1 (hB j)
    nlinarith

private def P (n : ℕ) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    Submonoid (Fin n → kˣ) where
  carrier := {d | Sig.SDom d ∨ d = 1}
  one_mem' := Or.inr rfl
  mul_mem' := by
    rintro a b (ha | rfl) (hb | rfl)
    · exact Or.inl (sdom_mul ha hb)
    · simpa using Or.inl ha
    · simpa using Or.inl hb
    · simp

private theorem delta_unit (v : Fin n → kˣ) (hv : ∀ i, v i ∈ UpperTheory.V.Hi.Uo k) :
    (deltaHalf k fun _ : Fin n => Unit).comp (leviTorus k (Fin n)).toMonoidHom v = 1 := by
  rw [MonoidHom.comp_apply, deltaHalf_apply]
  refine Finset.prod_eq_one fun a _ => ?_
  have h : Matrix.GeneralLinearGroup.det (leviTorus k (Fin n) v a) = v a := congrFun ((leviTorus k (Fin n)).left_inv v) a
  erw [h]
  exact isUnram_absPow k _ _ (hv a)

end UpperTheory.V.Z.Sym.Al.ExtChar

open UpperTheory.V.Z.Sym.Al.ExtChar in
theorem UpperTheory.V.Z.Sym.Al.extChar :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (χ : (Fin n → kˣ) → ℂ), (∀ d, Sig.SDom d → χ d ≠ 0) → (∀ d d', Sig.SDom d → Sig.SDom d' → χ (d * d') = χ d * χ d') →
        (∀ d u, Sig.SDom d → (∀ i, u i ∈ Hi.Uo k) → χ (d * u) = χ d) →
        ∃ ψ : Fin n → kˣ →* ℂˣ, (∀ i, ∀ u ∈ Hi.Uo k, ψ i u = 1) ∧ ∀ d, Sig.SDom d → χ d = expo ψ d := by
  classical
  intro k _ _ _ _ n χ hne hmul hunit
  let f : (Fin n → kˣ) → ℂ := fun d => if d = 1 then 1 else χ d
  have hf : ∀ d, Sig.SDom d → f d = χ d := by
    intro d hd
    by_cases h1 : d = 1
    · subst h1
      have h2 := hmul 1 1 hd hd
      rw [mul_one] at h2
      have h3 : χ 1 = 1 := by
        have h4 := hne 1 hd
        exact mul_right_cancel₀ h4 (by rw [one_mul]; exact h2.symm)
      simp [f, h3]
    · simp [f, h1]
  have hf1 : f 1 = 1 := by simp [f]
  obtain ⟨θ, hθ, -⟩ := UpperTheory.V.AlgebraTools.monoidExt (Fin n → kˣ) ℂ (P n k) f
    (fun t => by
      obtain ⟨a, b, ha, hb, h⟩ := exists_div t
      exact ⟨a, Or.inl ha, b, Or.inl hb, h⟩)
    hf1
    (by
      rintro a (ha | rfl) b (hb | rfl)
      · rw [hf _ ha, hf _ hb, hf _ (sdom_mul ha hb), hmul _ _ ha hb]
      · rw [mul_one, hf1, mul_one]
      · rw [one_mul, hf1, one_mul]
      · rw [mul_one, hf1, mul_one])
    (by
      rintro a (ha | rfl)
      · rw [hf _ ha]
        exact (hne a ha).isUnit
      · rw [hf1]
        exact isUnit_one)
  have hθχ : ∀ d, Sig.SDom d → (θ d : ℂ) = χ d := fun d hd => (hθ d (Or.inl hd)).trans (hf d hd)
  have hθu : ∀ u : Fin n → kˣ, (∀ i, u i ∈ Hi.Uo k) → θ u = 1 := by
    intro u hu
    obtain ⟨a, -, ha, -, -⟩ := exists_div (1 : Fin n → kˣ)
    have h1 : θ (a * u) = θ a := Units.ext (by
      rw [hθχ _ (sdom_mul_unit ha hu), hθχ _ ha, hunit _ _ ha hu])
    rw [map_mul] at h1
    exact mul_left_cancel (h1.trans (mul_one _).symm)
  let D : (Fin n → kˣ) →* ℂˣ := (deltaHalf k fun _ : Fin n => Unit).comp (leviTorus k (Fin n)).toMonoidHom
  have hsingle : ∀ (i : Fin n) (u : kˣ), u ∈ Hi.Uo k → ∀ j, (Pi.mulSingle i u : Fin n → kˣ) j ∈ Hi.Uo k := by
    intro i u hu j
    by_cases h : j = i
    · subst h; simpa using hu
    · rw [Pi.mulSingle_eq_of_ne h]; exact one_mem _
  refine ⟨fun i => (θ * D).comp (MonoidHom.mulSingle (fun _ : Fin n => kˣ) i), ?_, ?_⟩
  · intro i u hu
    simp only [MonoidHom.comp_apply, MonoidHom.mul_apply, MonoidHom.mulSingle_apply]
    rw [hθu _ (hsingle i u hu), delta_unit _ (hsingle i u hu), one_mul]
  · intro d hd
    have h1 : torusChar (fun i => (θ * D).comp (MonoidHom.mulSingle (fun _ : Fin n => kˣ) i)) d = θ d * D d := by
      rw [torusChar_apply]
      simp only [MonoidHom.comp_apply, MonoidHom.mulSingle_apply]
      rw [← map_prod, Finset.univ_prod_mulSingle, MonoidHom.mul_apply]
    rw [Dict.expo, h1, ← hθχ d hd]
    change (θ d : ℂ) = ((θ d * D d * (D d)⁻¹ : ℂˣ) : ℂ)
    rw [mul_inv_cancel_right]
