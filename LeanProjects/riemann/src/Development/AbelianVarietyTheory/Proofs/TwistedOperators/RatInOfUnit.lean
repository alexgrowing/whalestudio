import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConstRatio

open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle

section Rat

variable {T L : Type} [Field L] (σ : L →+* ℂ) (t₀ : T)

def RatIn (f : T → ℂ) : Prop := ∀ t, f t ≠ 0 ∧ ∃ y : Lˣ, σ y = f t / f t₀

variable {σ t₀}

theorem RatIn.mul {f g : T → ℂ} (hf : RatIn σ t₀ f) (hg : RatIn σ t₀ g) : RatIn σ t₀ fun t => f t * g t := by
  intro t
  obtain ⟨hf0, y, hy⟩ := hf t
  obtain ⟨hg0, z, hz⟩ := hg t
  refine ⟨mul_ne_zero hf0 hg0, y * z, ?_⟩
  rw [Units.val_mul, map_mul, hy, hz, mul_div_mul_comm]

theorem RatIn.inv {f : T → ℂ} (hf : RatIn σ t₀ f) : RatIn σ t₀ fun t => (f t)⁻¹ := by
  intro t
  obtain ⟨hf0, y, hy⟩ := hf t
  refine ⟨inv_ne_zero hf0, y⁻¹, ?_⟩
  rw [map_units_inv, hy, inv_div, inv_div_inv]

theorem ratIn_const {κ : ℂ} (h : κ ≠ 0) : RatIn σ t₀ fun _ => κ := by
  intro _
  exact ⟨h, 1, by rw [Units.val_one, map_one, div_self h]⟩

theorem ratIn_of_unit {f : T → ℂ} (h : ∀ t, ∃ y : Lˣ, σ y = f t) : RatIn σ t₀ f := by
  intro t
  obtain ⟨y, hy⟩ := h t
  obtain ⟨y₀, hy₀⟩ := h t₀
  refine ⟨hy ▸ (map_ne_zero σ).2 y.ne_zero, y * y₀⁻¹, ?_⟩
  rw [Units.val_mul, map_mul, map_units_inv, hy, hy₀, div_eq_mul_inv]

theorem RatIn.of_mul {f g u : T → ℂ} (hg : RatIn σ t₀ g) (hu : RatIn σ t₀ u) (h : ∀ t, f t * u t = g t) : RatIn σ t₀ f := by

  have e : f = fun t => g t * (u t)⁻¹ := funext fun t => by rw [← h t, mul_inv_cancel_right₀ (hu t).1]
  rw [e]
  exact hg.mul hu.inv

theorem ratIn_prod {ι : Type} (s : Finset ι) {f : ι → T → ℂ} (h : ∀ i ∈ s, RatIn σ t₀ (f i)) :
    RatIn σ t₀ fun t => ∏ i ∈ s, f i t := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp only [Finset.prod_empty]
    exact ratIn_const one_ne_zero
  · intro a s ha ih h
    simp only [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end Rat

variable {D : D7}

section Factor

variable {T : Type} {A A' WW : HSp D} (X : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)

def Factor (lam : T → ℂ) : Prop :=
  (∀ t, lam t ≠ 0) ∧
    ∃ (Pi : ModuleCat.{0} ℂ) (p : PolF D WW.rank A.rank →ₗ[ℂ] Pi) (p' : PolF D WW.rank A'.rank →ₗ[ℂ] Pi)
      (J : T → (Pi →ₗ[ℂ] (GA D WW → ℂ))),
      Function.Surjective p ∧ (∀ t, Function.Injective (J t)) ∧
      (∀ t P h, IntegrableOn (X.ker ψ θ t P h) X.fd X.m) ∧
      (∀ t P, X.I ψ θ t P = lam t • J t (p P)) ∧
      (∀ t P', (∀ h, IntegrableOn (X.ker' ψ θ t P' h) X.fd' X.m') → X.I' ψ θ t P' = J t (p' P')) ∧
      ∃ P', p' P' ≠ 0 ∧ ∀ t h, IntegrableOn (X.ker' ψ θ t P' h) X.fd' X.m'

variable {X ψ θ}

theorem Factor.isConst [Nonempty T] {lam : T → ℂ} (h : Factor X ψ θ lam) : X.IsConst ψ θ lam := by
  unfold Factor at h
  obtain ⟨hlam, Pi, p, p', J, hp, hJ, hint, hI, hI', P', hP', hint'⟩ := h

  obtain ⟨P, hPP⟩ := hp (p' P')
  unfold Tri.IsConst
  refine ⟨⟨Classical.arbitrary T, hlam _⟩, P, P', fun t => ⟨fun h => ⟨hint t P h, hint' t h⟩, ?_, fun h => ?_⟩⟩
  · by_contra hcon
    push_neg at hcon
    apply hP'
    apply hJ t
    rw [map_zero, ← hI' t P' (hint' t)]
    funext h
    exact hcon h
  · rw [hI t P, hI' t P' (hint' t), hPP]
    rfl

theorem Factor.eq_mul {lam c : T → ℂ} (h : Factor X ψ θ lam) (hc : X.IsConst ψ θ c) : ∃ κ : ℂ, κ ≠ 0 ∧ ∀ t, c t = κ * lam t := by
  unfold Factor at h
  unfold Tri.IsConst at hc
  obtain ⟨hlam, Pi, p, p', J, -, hJ, -, hI, hI', -⟩ := h
  obtain ⟨⟨t₁, ht₁⟩, P, P', hc⟩ := hc

  have key : ∀ t, lam t • p P = c t • p' P' := by
    intro t
    obtain ⟨hi, -, heq⟩ := hc t
    apply hJ t
    rw [map_smul, map_smul, ← hI t P, ← hI' t P' (fun h => (hi h).2)]
    funext h
    exact heq h
  have hne : p' P' ≠ 0 := by
    intro h0
    obtain ⟨hi, ⟨h₁, hh₁⟩, -⟩ := hc t₁
    apply hh₁
    rw [hI' t₁ P' (fun h => (hi h).2), h0, map_zero]
    rfl
  have hq : ∀ t, p P = ((lam t)⁻¹ * c t) • p' P' := by
    intro t
    rw [← smul_smul, ← key t, inv_smul_smul₀ (hlam t)]
  refine ⟨(lam t₁)⁻¹ * c t₁, mul_ne_zero (inv_ne_zero (hlam t₁)) ht₁, fun t => ?_⟩
  have e := smul_left_injective ℂ hne ((hq t).symm.trans (hq t₁))
  rw [← e]
  field_simp [hlam t]

end Factor

variable {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type} {Fam : FamIn D.what₂.LL G₀ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D Fam Ks}

def Standing (F : Face D Fam) (G : GridPre R) : Prop :=
  R.Char F ∧ G.Is ∧ PrimeToPolarisation G ∧ Formalism.L2.Host.ValLL D R.C ∧ G.ValuesInField ∧
    ∀ t, (R.xiH t).ValuesIn 0 D.what₂.embLL

def NegIdx (V : HSp D) (q : ℕ) : Prop := ∀ τ, Formalism.UG.HasSignature (gramAt D V τ) (V.rank - q) q

def IsStage (G : GridPre R) (i j : Fin D.R.m) (p q : ℕ) {A A' WW : HSp D} (X : Tri T A A' WW) : Prop :=
  p ≤ (D.R.m - (j + 1)) / 2 ∧ q ≤ (D.R.m - j) / 2 ∧
    A.rank + 2 * ((D.R.m - (j + 1)) / 2) = rkV D (i + 1) (j + 1) + 2 * p ∧
    A'.rank + 2 * ((D.R.m - j) / 2) = rkV D i j + 2 * q ∧
    NegIdx A p ∧ NegIdx A' q ∧ NegIdx WW (p + q) ∧
    X.Is R.ψ R.θ (alpha R i j) (beta G i j) (nuH G i j) (places G)

theorem IsStage.exists_half {G : GridPre R} {i j : Fin D.R.m} {p q : ℕ} {A A' WW : HSp D} {X : Tri T A A' WW}
    (h : IsStage G i j p q X) : ∃ e : ℕ, A.rank = A'.rank + 2 * e ∧ 2 ≤ e ∧ e ≤ bigN D := by
  obtain ⟨hp, hq, hA, hA', -⟩ := h
  have hs : sLen D = D.R.r + 6 := rfl
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hN : bigN D = D.R.k + D.R.m * (D.R.t + sLen D + 1) := rfl
  have hm := Nat.mul_le_mul_right (D.R.t + sLen D + 1) D.R.two_le_m
  obtain ⟨a, ha⟩ := D.R.k_even
  obtain ⟨b, hb⟩ := D.R.m_even
  obtain ⟨c, hc⟩ := D.R.t_odd
  have h5 := D.R.rank_add_five_le
  simp only [rkV, add_mul, one_mul] at hA hA'

  refine ⟨(D.R.t + sLen D) / 2 + p + (D.R.m - j) / 2 - q - (D.R.m - (j + 1)) / 2, ?_, ?_, ?_⟩ <;> omega

end GlobalTheory.ConstRatio

end
