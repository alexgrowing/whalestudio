import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LineLatAt

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.LiftModel

variable {D : D7} {u : D.what₂.Word}

def lineLat (L : HSp D) (ζ : Fin L.rank → D.host.E) (𝔠 : FI D) : Lat L :=
  (𝔠 : Submodule (𝓞 D.host.E) D.host.E).map
    ((LinearMap.toSpanSingleton D.host.E (Fin L.rank → D.host.E) ζ).restrictScalars (𝓞 D.host.E))

theorem tmul_mul_incA (α : AF D.host.F) (x z : D.host.E) :
    (α ⊗ₜ[D.host.F] x : AE D) * incA D z = α ⊗ₜ[D.host.F] (x * z) := by
  change (α ⊗ₜ[D.host.F] x : AE D) * (1 ⊗ₜ[D.host.F] z) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]

theorem latV_lineLat (L : HSp D) (ζ : Fin L.rank → D.host.E) (𝔠 : FI D) (v : Pl D) :
    latV L (lineLat L ζ 𝔠) (· = v) =
      (idV 𝔠 v).map (LinearMap.toSpanSingleton (AE D) (Fin L.rank → AE D) (ratV ζ)).toAddMonoidHom := by
  unfold GlobalTheory.FinPl.latV GlobalTheory.FinPl.latMul idV
  rw [AddMonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨α, h1, h2, a, rfl, x, ⟨c, hc, rfl⟩, rfl⟩
    refine ⟨_, ⟨α, h1, h2, c, hc, rfl⟩, ?_⟩
    funext i
    simp [ratV, tmul_mul_incA]
  · rintro ⟨_, ⟨α, h1, h2, c, hc, rfl⟩, rfl⟩
    refine ⟨α, h1, h2, 1, rfl, _, ⟨c, hc, rfl⟩, ?_⟩
    funext i
    simp [ratV, tmul_mul_incA]

theorem lineLatAt_lineLat (L : HSp D) {ζ : Fin L.rank → D.host.E} (hζ : ζ ≠ 0) (𝔠 : FI D) (v : Pl D) :
    LineLatAt L ζ 𝔠 (lineLat L ζ 𝔠) v := by
  intro a _
  rw [latV_lineLat]
  refine ⟨?_, fun h => ⟨a, h, rfl⟩⟩
  rintro ⟨a', h, e⟩
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hζ
  have e1 : a' * incA D (ζ i) = a * incA D (ζ i) := congrFun e i
  have hu : IsUnit (incA D (ζ i)) := (IsUnit.mk0 _ hi).map _
  rwa [← hu.mul_right_cancel e1]

theorem idV_le_idAt (𝔞 : FI D) (v : Pl D) : ∀ a ∈ idV 𝔞 v, a ∈ idAt D (· = v) := by
  intro a ha
  refine (AddSubgroup.closure_le (idAt D (· = v)).toAddSubgroup).2 ?_ ha
  rintro _ ⟨α, -, h2, x, -, rfl⟩
  refine Ideal.mem_inf.2 ⟨?_, Ideal.mem_iInf.2 fun w => ?_⟩
  · change (0 : Ainf D.host.F) ⊗ₜ[D.host.F] x = 0
    exact TensorProduct.zero_tmul _ _
  · change (evalV D.host.F w.1 α) ⊗ₜ[D.host.F] x = 0
    rw [h2 _ w.2, TensorProduct.zero_tmul]

theorem one_tmul_one_ne (F A E : Type) [Field F] [Field A] [Field E] [Algebra F A] [Algebra F E] :
    (1 : A) ⊗ₜ[F] (1 : E) ≠ 0 := one_ne_zero (α := A ⊗[F] E)

theorem idV_ne_bot {𝔞 : FI D} (h : 𝔞 ≠ 0) (v : Pl D) : idV 𝔞 v ≠ ⊥ := by
  classical
  obtain ⟨x, hx, hx0⟩ : ∃ x ∈ 𝔞, x ≠ 0 := by
    by_contra hc
    push Not at hc
    exact h (FractionalIdeal.eq_zero_iff.2 hc)
  have ev : evalV D.host.F v (singleV D.host.F v 1) = 1 := by
    exact RestrictedProduct.single_eq_same (fun w : Pl D => w.adicCompletionIntegers D.host.F) v 1
  have ew : ∀ w, w ≠ v → evalV D.host.F w (singleV D.host.F v 1) = 0 := fun w hw => by
    exact RestrictedProduct.single_eq_of_ne (fun w : Pl D => w.adicCompletionIntegers D.host.F) 1 hw
  intro hb
  have hm : (pairA D.host.F 0 (singleV D.host.F v 1)) ⊗ₜ[D.host.F] x ∈ idV 𝔞 v := by
    refine AddSubgroup.subset_closure ⟨_, fun w => ?_, ew, x, hx, rfl⟩
    by_cases hw : w = v
    · subst hw; rw [ev]; exact one_mem _
    · rw [ew w hw]; exact zero_mem _
  rw [hb, AddSubgroup.mem_bot] at hm
  have h2 := congrArg (fun y => compAt D v (y * incA D x⁻¹)) hm
  simp only [tmul_mul_incA, mul_inv_cancel₀ hx0, zero_mul, map_zero] at h2
  change (evalV D.host.F v (singleV D.host.F v 1)) ⊗ₜ[D.host.F] (1 : D.host.E) = 0 at h2
  rw [ev] at h2
  exact one_tmul_one_ne _ _ _ h2

theorem not_lineLatAt_zero (L : HSp D) {ζ : Fin L.rank → D.host.E} (hζ : ζ ≠ 0) {𝔠 : FI D} (h : 𝔠 ≠ 0) (v : Pl D) :
    ¬ LineLatAt L ζ 𝔠 (lineLat L ζ 0) v := by
  intro hl
  refine idV_ne_bot h v ((AddSubgroup.eq_bot_iff_forall _).2 fun a ha => ?_)
  have h1 := idV_le_idAt _ _ a ha
  have := (lineLatAt_lineLat L hζ 0 v a h1).1 ((hl a h1).2 ha)
  rwa [idV_zero, AddSubgroup.mem_bot] at this

theorem AA_ne (hP : FactPrincipalDatum) : D.host.AA ≠ 0 ∧ D.host.AAbar ≠ 0 ∧ D.host.xi0 ≠ 0 := by
  have h1 := hP D.R D.host
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> simp [h] at h1

theorem cols_odd_even (hP : FactPrincipalDatum) {j σ : ℕ} (h : j + 2 * (σ + 1) + 2 = D.R.m) :
    (∀ i, i < σ → D.host.AA⁻¹ * bI D j (σ + 1) i = D.host.AA * bI D (j + 1 + 1) σ i) ∧
      D.host.AA⁻¹ * bI D j (σ + 1) σ = D.host.AA * cI D (j + 1 + 1) := by
  obtain ⟨hA, hB, -⟩ := AA_ne (D := D) hP
  have key : D.host.AA⁻¹ * (dI D * cI D j) = D.host.AA * cI D (j + 1 + 1) := by
    have e := cI_step D (j := j) (by omega)
    have : dI D * cI D j = D.host.AA * D.host.AAbar * (FractionalIdeal.spanSingleton _ D.host.xi0 * cI D j) := by
      rw [dI]; ring
    rw [this, e]
    field_simp
  refine ⟨fun i hi => ?_, ?_⟩
  · have : σ + 1 - i = σ - i + 1 := by omega
    rw [bI, bI, this, pow_succ, mul_assoc, mul_left_comm, key, mul_left_comm]
  · rw [bI, Nat.add_sub_cancel_left, pow_one, key]

variable {a : XPart D u} {b : YPart a}

theorem norm_link (x y : D.host.E) (j : ℕ) (T : D.host.E) (hl : x = D.host.xi0 * star D.host.xi0 * y)
    (hx : x * (D.host.xi0 * star D.host.xi0) ^ (j / 2) = -T) :
    y * (D.host.xi0 * star D.host.xi0) ^ ((j + 1 + 1) / 2) = -T := by
  have : (j + 1 + 1) / 2 = j / 2 + 1 := by omega
  rw [this, ← hx, hl]; ring

theorem tau_norm {ζ₀ : Fin a.Lz.rank → D.host.E} {τ} (h : b.Sk ζ₀ τ) (j : ℕ) (hj : j + 2 * 0 + 2 = D.R.m) :
    star (τ j hj *ᵥ ζ₀) ⬝ᵥ (b.bes j 0 hj).L.gram *ᵥ (τ j hj *ᵥ ζ₀) =
      -(D.host.xi0 * star D.host.xi0) * (((D.mem u).A.T : ℕ) : D.host.E) := by
  have e : D.R.m / 2 = j / 2 + 1 := by omega
  have n := h.norm j 0 hj
  rw [h.tau j hj, star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, star_pow, e]
  linear_combination (D.host.xi0 * star D.host.xi0) * n

theorem exists_sc {k : Type} [Field k] [ValuativeRel k] {ξ c : k} (hξ : valuation k ξ = 1) (hc : valuation k c = 1) (s : ℕ) :
    ∃ sc : ℕ → k, (∀ j, valuation k (sc j) = 1) ∧ (∀ j, sc (j + 1 + 1) = sc j * ξ) ∧ -(ξ * sc s) = c * ξ ^ ((s + 1 + 1) / 2) := by
  refine ⟨fun j => -(c * ξ ^ (j / 2)), fun j => by simp [hξ, hc], fun j => ?_, ?_⟩
  · have : (j + 1 + 1) / 2 = j / 2 + 1 := by omega
    simp only [this]; ring
  · have : (s + 1 + 1) / 2 = s / 2 + 1 := by omega
    simp only [this]; ring

theorem lineId_of_split {S A L : HSp D} (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (M : Lat S) (LA : Lat A) (LL : Lat L)
    (𝔠 : FI D) (v : Pl D) (h : LineLatAt L ζ 𝔠 LL v) (ho : OrthAt o M LA LL v) : LineId o ζ M 𝔠 v := by
  intro a ha
  have e : ratV (vecB o ζ) = o.jB *ᵥ ratV ζ := by
    funext i
    simp [ratV, vecB, OrthDec.jB, rat, mulVec, dotProduct]
  rw [ho, e, mulVec_smul, mulVec_smul, mulVec_mulVec, mulVec_mulVec, ← h a ha]
  rw [o.pA_jB, o.pB_jB, zero_mulVec, smul_zero, one_mulVec]
  exact and_iff_right (zero_mem _)

end GlobalTheory.SeeSaw.LiftModel

end
