import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.WeightChange
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.HeckeGal UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section SlopeTestRemainingChoices
open GlobalTheory.SmGL GlobalTheory.PRep Matrix

private theorem sep_of_irred {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (hρ : ρ.IsIrreducible) (L : V →ₗ[ℂ] ℂ) (hL : L ≠ 0) (v : V) (hv : ∀ g, L (ρ g v) = 0) : v = 0 := by
  let S : Subrepresentation ρ :=
    ⟨{ carrier := {v | ∀ g, L (ρ g v) = 0}
       add_mem' := fun {a b} ha hb g => by simp [ha g, hb g]
       zero_mem' := fun g => by simp
       smul_mem' := fun c a ha g => by simp [ha g] }, fun x a ha g => by
      have := ha (g * x)
      simpa using this⟩
  haveI := hρ
  rcases eq_bot_or_eq_top S with h | h
  · have : v ∈ S.toSubmodule := hv
    rw [h] at this
    exact this
  · exfalso
    apply hL
    ext a
    have : a ∈ S.toSubmodule := by rw [h]; trivial
    simpa using this 1

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem diag_eq (a d : kˣ) :
    diagT k (Fin 2) ![a, d] = GeneralLinearGroup.scalar (Fin 2) d * aff (a / d) 0 := by
  ext i j
  rw [val_diagT]
  fin_cases i <;> fin_cases j <;>
    simp [aff, GeneralLinearGroup.scalar, Matrix.mul_apply, Fin.sum_univ_succ, mul_div_cancel₀]

private theorem cont_diag : Continuous (diagT k (Fin 2)) :=
  (continuous_leviEmb k (points (Fin 2))).comp (continuous_leviTorus k (Fin 2))

private theorem finiteRing_sq_sub_mul_sq_eq_of_card (σ : SmIrr (GL (Fin 2) k)) (μ₁ μ₂ : kˣ →* ℂˣ) (L : σ.V →ₗ[ℂ] ℂ) (hL : L ≠ 0)
    (h : ∀ (a d : kˣ) (x : k) v, L (σ.ρ (GeneralLinearGroup.scalar (Fin 2) d * aff (a / d) x) v) =
      ((μ₁ a * μ₂ d : ℂˣ) : ℂ) * L v) :
    IsSmoothChar μ₁ ∧ IsSmoothChar μ₂ ∧ IsSubquotient σ.ρ (Hi.PS ![μ₁ * absPow k (-1), μ₂]) ∧
      ∀ (z : kˣ) v, σ.ρ (GeneralLinearGroup.scalar (Fin 2) z) v = ((μ₁ z * μ₂ z : ℂˣ) : ℂ) • v := by
  obtain ⟨v₀, hv₀⟩ : ∃ v, L v ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hL (LinearMap.ext hc)
  have hst : ∀ a d : kˣ, σ.ρ (diagT k (Fin 2) ![a, d]) v₀ = v₀ → μ₁ a * μ₂ d = 1 := by
    intro a d had
    have := h a d 0 v₀
    rw [← diag_eq, had] at this
    ext
    exact (mul_eq_right₀ hv₀).1 this.symm
  have hopen : IsOpen {g | σ.ρ g v₀ = v₀} := σ.smooth v₀
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hc : Continuous fun a : kˣ => diagT k (Fin 2) ![a, 1] :=
      cont_diag.comp (continuous_pi fun i => by fin_cases i; exacts [continuous_id, continuous_const])
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset ((hopen.preimage hc).mem_nhds ?_) ?_)
    · have : (![1, 1] : Fin 2 → kˣ) = 1 := by funext i; fin_cases i <;> rfl
      simp [this]
    · intro a ha
      simpa using hst a 1 ha
  · have hc : Continuous fun a : kˣ => diagT k (Fin 2) ![1, a] :=
      cont_diag.comp (continuous_pi fun i => by fin_cases i; exacts [continuous_const, continuous_id])
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset ((hopen.preimage hc).mem_nhds ?_) ?_)
    · have : (![1, 1] : Fin 2 → kˣ) = 1 := by funext i; fin_cases i <;> rfl
      simp [this]
    · intro a ha
      simpa using hst 1 a ha
  · let τ : Representation ℂ (Levi k fun _ : Fin 2 => Unit) ℂ :=
      (ofChar (torusChar fun i => ![μ₁ * absPow k (-1), μ₂] i * absPow k ((((2 : ℕ) : ℂ) - 1) / 2))).comp
        (leviTorus k (Fin 2)).symm.toMonoidHom
    have law : ∀ (p : parab k (points (Fin 2))) (u : σ.V), L (σ.ρ p u) =
        (deltaHalf k (fun _ : Fin 2 => Unit) (leviProj k (points (Fin 2)) p) : ℂ) •
          τ (leviProj k (points (Fin 2)) p) (L u) := by
      intro p u
      set t : Fin 2 → kˣ := (leviTorus k (Fin 2)).symm (leviProj k (points (Fin 2)) p) with ht
      have ht1 : ∀ i, GeneralLinearGroup.det (leviProj k (points (Fin 2)) p i) = t i := fun i => rfl
      have ht2 : ∀ i, (t i : k) = ((p : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) i i := by
        intro i
        rw [← ht1]
        simp
      have h10 : ((p : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) 1 0 = 0 :=
        (mem_borel k).1 p.2 1 0 (by decide)
      have hp : (p : GL (Fin 2) k) = GeneralLinearGroup.scalar (Fin 2) (t 1) *
          aff (t 0 / t 1) (((p : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) 0 1 / t 1) := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [aff, GeneralLinearGroup.scalar, Matrix.mul_apply, Fin.sum_univ_succ, mul_div_cancel₀, ← ht2, h10]
      rw [hp, h]
      show _ = _ • ofChar _ t (L u)
      rw [ofChar_apply, deltaHalf_apply, torusChar_apply, Fin.prod_univ_two, Fin.prod_univ_two, ht1, ht1,
        modExp_fin _ (fun _ => by simp), modExp_fin _ (fun _ => by simp), smul_eq_mul, ← mul_assoc, ← Units.val_mul]
      congr 2
      have e1 : absPow k (-1) = (absPow k (1 / 2))⁻¹ * (absPow k (1 / 2))⁻¹ := by
        rw [← absPow_neg, ← absPow_add]; norm_num
      have e2 : ((((2 : ℕ) : ℤ) - 1 - 2 * ((0 : Fin 2) : ℕ) : ℤ) : ℂ) / 2 = 1 / 2 := by norm_num
      have e3 : ((((2 : ℕ) : ℤ) - 1 - 2 * ((1 : Fin 2) : ℕ) : ℤ) : ℂ) / 2 = -(1 / 2) := by norm_num
      have e4 : (((2 : ℕ) : ℂ) - 1) / 2 = 1 / 2 := by norm_num
      rw [e2, e3, e4, absPow_neg, e1]
      simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
      generalize absPow k (1 / 2) (t 0) = x
      generalize absPow k (1 / 2) (t 1) = y
      ext
      simp only [Units.val_mul, Units.val_inv_eq_inv_val]
      field_simp
    let f : σ.V →ₗ[ℂ] IndSp (points (Fin 2)) τ :=
      { toFun := fun v => ⟨⟨fun g => L (σ.ρ g v), fun p g => by
            refine Eq.trans ?_ (law p (σ.ρ g v))
            show L (σ.ρ (p * g) v) = _
            rw [map_mul, Module.End.mul_apply]⟩,
          mem_smoothPart_of_nhds (Filter.mem_of_superset
            (IsOpen.mem_nhds (σ.smooth v) (by simp)) fun g hg => by
              have hg' : σ.ρ g v = v := hg
              apply Subtype.ext
              funext x
              show L (σ.ρ (x * g) v) = L (σ.ρ x v)
              rw [map_mul, Module.End.mul_apply, hg'])⟩
        map_add' := fun c d => by ext g; simp
        map_smul' := fun c d => by ext g; simp }
    refine IsSubquotient.of_injective (ρ := parInd (points (Fin 2)) τ) ⟨f, fun g => ?_⟩ fun c d hcd => ?_
    · refine LinearMap.ext fun c => Subtype.ext (Subtype.ext (funext fun x => ?_))
      show L (σ.ρ x (σ.ρ g c)) = L (σ.ρ (x * g) c)
      rw [map_mul, Module.End.mul_apply]
    · refine sub_eq_zero.1 (sep_of_irred σ.ρ σ.irred L hL _ fun g => ?_)
      have : L (σ.ρ g c) = L (σ.ρ g d) := congrFun (congrArg (fun φ => φ.1.1) hcd) g
      rw [map_sub, map_sub, this, sub_self]
  · intro z v
    refine sub_eq_zero.1 (sep_of_irred σ.ρ σ.irred L hL _ fun g => ?_)
    have hc : g * GeneralLinearGroup.scalar (Fin 2) z =
        GeneralLinearGroup.scalar (Fin 2) z * aff (z / z) 0 * g := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [aff, GeneralLinearGroup.scalar, Matrix.mul_apply, Fin.sum_univ_succ, mul_comm]
    rw [map_sub, map_sub, ← Module.End.mul_apply, ← map_mul, hc, map_mul, Module.End.mul_apply, h]
    simp

end SlopeTestRemainingChoices

theorem UpperTheory.isSubquotient_principalSeries_of_borel_functional :
    ∀ (F : Type) [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) (σ : SmIrr (GL (Fin 2) (w.adicCompletion F))) (μ₁ μ₂ : (w.adicCompletion F)ˣ →* ℂˣ) (L : σ.V →ₗ[ℂ] ℂ), L ≠ 0 → (∀ (a d : (w.adicCompletion F)ˣ) (x : w.adicCompletion F) v, L (σ.ρ (Matrix.GeneralLinearGroup.scalar (Fin 2) d * aff (a / d) x) v) = ((μ₁ a * μ₂ d : ℂˣ) : ℂ) * L v) → GlobalTheory.SmGL.IsSmoothChar μ₁ ∧ GlobalTheory.SmGL.IsSmoothChar μ₂ ∧ GlobalTheory.SmGL.IsSubquotient σ.ρ (Hi.PS ![μ₁ * GlobalTheory.SmGL.absPow (w.adicCompletion F) (-1), μ₂]) ∧ ∀ (z : (w.adicCompletion F)ˣ) v, σ.ρ (Matrix.GeneralLinearGroup.scalar (Fin 2) z) v = ((μ₁ z * μ₂ z : ℂˣ) : ℂ) • v := by
  intro F _ _ w σ μ₁ μ₂ L hL h
  exact finiteRing_sq_sub_mul_sq_eq_of_card σ μ₁ μ₂ L hL h
