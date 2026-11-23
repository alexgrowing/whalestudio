import Mathlib
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.ClifMod
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.DualEx
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.SkewHermitianOfUnitaryExp
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.EntriesZero
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.TrOnBot
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.EvTSum
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.WeylEv
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.LefForm
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.RhoStrict
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.MultTrOnBot
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.WspOrth

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

private theorem trOn_top_one {V : Type} [AddCommGroup V] [Module ℂ V] [Module.Free ℂ V] (S : Submodule ℂ V)
    [FiniteDimensional ℂ S] : trOn S (1 : Module.End ℂ V) = (Module.finrank ℂ S : ℂ) := by
  unfold trOn
  rw [dif_pos (fun x hx => by simpa using hx)]
  have : (LinearMap.restrict (1 : Module.End ℂ V) (fun x hx => by simpa using hx) : Module.End ℂ S) = 1 := by
    ext x
    rfl
  rw [this, LinearMap.trace_one]

private theorem prod_swap {n : ℕ} (z : Fin n → ℂ) (hz : ∀ a, z a * conj (z a) = 1) :
    (∏ a, ∏ b, (1 + conj (z a) / conj (z b))) = ∏ a, ∏ b, (1 + z a / z b) := by
  have hne : ∀ a, z a ≠ 0 := fun a h => by simpa [h] using hz a
  have hc : ∀ a, conj (z a) = (z a)⁻¹ := fun a => (eq_inv_of_mul_eq_one_right (hz a))
  have key : ∀ a b, conj (z a) / conj (z b) = z b / z a := by
    intro a b
    rw [hc, hc]
    field_simp [hne a, hne b]
  simp_rw [key]
  exact Finset.prod_comm

theorem UpperTheory.RealTr.lefData :
    ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ (E : KMod n) (T : E.V →L[ℂ] E.V), IsLefK lam E T →
      ∃ (E' : KMod n) (e : (E.V →L[ℂ] ℂ) ≃ₗ[ℂ] E'.V) (T' : Module.End ℂ E'.V) (σ' : UK n →* (E'.V →ₗ[ℂ] E'.V)) (F : Fin n → Fin n → Module.End ℂ E'.V)
        (χ : FR n) (s : Finset (Wt n)), (∀ k ξ, e (ξ ∘L E.ρ k⁻¹) = σ' k (e ξ)) ∧ (∀ ξ, e (dualT E T ξ) = T' (e ξ)) ∧ UF F ∧ IsDerivK σ' F ∧
        (∀ a b, T' * F a b = F a b * T') ∧ (∀ ν ∉ s, hw F ν = ⊥) ∧ alt (rhoV n) * χ = alt ((fun a => (lam a : ℝ)) + rhoV n) ∧
        ∀ ν : Wt n, StrictAnti (ν + rhoV n) → trOn (hw F ν) T' = 2 ^ n * cf (chR n * alt (twoL lam)) (ν + rhoV n) ∧
          (Module.finrank ℂ (hw F ν) : ℂ) = 2 ^ n * cf (chR n * (alt ((2 : ℝ) • rhoV n) * (χ * χ))) (ν + rhoV n) := by
  intro n lam hlam E T hL
  obtain ⟨hcomm, hTT, htrace⟩ := hL
  obtain ⟨E', e, T', he1, he2, he3⟩ := dualEx n E T hcomm
  obtain ⟨σ', F, hσ, hUF, hder⟩ := kDer n E'
  have hTρ : ∀ (k : UK n) (v : E'.V), T' (E'.ρ k v) = E'.ρ k (T' v) := by
    intro k v
    obtain ⟨ξ, rfl⟩ := e.surjective v
    rw [← he1, ← he2, ← he2, ← he1]
    congr 1
    ext x
    have hx := congrArg (fun f : E.V →L[ℂ] E.V => f x) (hcomm k⁻¹)
    simp only [ContinuousLinearMap.mul_apply] at hx
    show ξ (E.ρ k⁻¹ (T x)) = ξ (T (E.ρ k⁻¹ x))
    rw [hx]
  have hTF : ∀ a b, T' * F a b = F a b * T' := by
    have hmem : T' ∈ homL F F := by
      refine ((derAt n E'.V σ' F hder).2 E'.V σ' F hder T').1 ?_
      intro k x
      rw [hσ, hσ]
      exact hTρ k x
    intro a b
    ext x
    exact hmem a b x
  have hDom : Dom (fun a => (lam a : ℝ)) := by
    intro a b hab
    have hle := hlam hab.le
    refine ⟨(lam a - lam b).toNat, ?_⟩
    have h0 : ((lam a - lam b).toNat : ℤ) = lam a - lam b := Int.toNat_of_nonneg (by omega)
    have h1 : (((lam a - lam b).toNat : ℕ) : ℝ) = ((lam a - lam b : ℤ) : ℝ) := by exact_mod_cast h0
    rw [h1]
    push_cast
    ring
  obtain ⟨χ, -, hχ⟩ := divEx n _ hDom
  have hStop : Stb F (⊤ : Submodule ℂ E'.V) := fun a b x _ => trivial
  obtain ⟨s, hs, -, -⟩ := wtDec n E'.V F hUF ⊤ inferInstance hStop
  have hCm1 : Cm F ⊤ (1 : Module.End ℂ E'.V) :=
    ⟨fun a b => by rw [one_mul, mul_one], fun x _ => trivial⟩
  have hCmT : Cm F ⊤ T' := ⟨hTF, fun x _ => trivial⟩
  obtain ⟨c₁, hc₁⟩ := chEx n E'.V F hUF ⊤ inferInstance hStop 1
  obtain ⟨cT, hcT⟩ := chEx n E'.V F hUF ⊤ inferInstance hStop T'
  have hkey : ∀ (θ : Wt n) (z : Fin n → ℂ), (∀ a, z a = Complex.exp (Complex.I * (θ a : ℂ))) →
      (Function.Injective fun a => z a ^ 2) →
      evT θ c₁ = (∏ a, ∏ b, (1 + z a / z b)) * weylChar lam z ^ 2 ∧
      evT θ cT = (∏ a, ∏ b, (1 + z a / z b)) * weylChar lam (fun a => z a ^ 2) := by
    intro θ z hz hinj
    have hzn : ∀ a, z a * conj (z a) = 1 := by
      intro a
      rw [Complex.mul_conj, hz a, Complex.normSq_eq_norm_sq, mul_comm, Complex.norm_exp_ofReal_mul_I]
      simp
    have hmemU : diagonal z ∈ unitaryGroup (Fin n) ℂ := by
      rw [mem_unitaryGroup_iff, star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal]
      rw [← diagonal_one]
      congr 1
      funext a
      exact hzn a
    set k : UK n := ⟨diagonal z, hmemU⟩ with hkdef
    have hk : (k : Matrix (Fin n) (Fin n) ℂ) = diagonal fun a => Complex.exp (Complex.I * (θ a : ℂ)) := by
      show diagonal z = _
      congr 1
      funext a
      exact hz a
    have hkinv : ((k⁻¹ : UK n) : Matrix (Fin n) (Fin n) ℂ) = diagonal fun a => conj (z a) := by
      rw [UnitaryGroup.inv_val]
      show star (diagonal z) = _
      rw [star_eq_conjTranspose, diagonal_conjTranspose]
      rfl
    have hinj' : Function.Injective fun a => conj (z a) ^ 2 := by
      intro a b h
      apply hinj
      have h' := congrArg conj h
      simpa [map_pow] using h'
    have hσk : (σ' k : Module.End ℂ E'.V) = ((E'.ρ k : E'.V →L[ℂ] E'.V) : Module.End ℂ E'.V) := by
      ext v
      exact hσ k v
    have hw := (weylEv n lam θ z hz).2.2.2
    obtain ⟨t1, t2⟩ := htrace k⁻¹ (fun a => conj (z a)) hkinv hinj'
    constructor
    · rw [← chEv n E'.V σ' F hUF hder 1 c₁ hCm1 hc₁ θ k hk, mul_one, hσk, (he3 k).1, t1,
        prod_swap z hzn, hw z]
    · rw [← chEv n E'.V σ' F hUF hder T' cT hCmT hcT θ k hk, hσk, (he3 k).2, t2,
        prod_swap z hzn]
      have : (fun a => conj (z a) ^ 2) = fun a => conj (z a ^ 2) := by
        funext a
        rw [map_pow]
      rw [this, hw (fun a => z a ^ 2)]
  obtain ⟨hT, h1⟩ := lefForm n lam c₁ cT χ hχ hkey
  refine ⟨E', e, T', σ', F, χ, s, ?_, he2, hUF, hder, hTF, ?_, hχ, ?_⟩
  · intro k ξ
    rw [he1, hσ]
  · intro ν hν
    rw [eq_bot_iff]
    intro x hx
    have hx' : x ∈ wsp F ν ⊓ ⊤ := ⟨hx.1, trivial⟩
    rw [hs ν hν] at hx'
    exact hx'
  · intro ν hν
    have mT := mult n E'.V F hUF ⊤ inferInstance hStop T' cT hCmT hcT ν hν
    have m1 := mult n E'.V F hUF ⊤ inferInstance hStop 1 c₁ hCm1 hc₁ ν hν
    rw [inf_top_eq] at mT m1
    rw [hT] at mT
    rw [h1] at m1
    constructor
    · rw [← mT]
      simp [cf]
    · rw [← trOn_top_one, ← m1]
      simp [cf]
