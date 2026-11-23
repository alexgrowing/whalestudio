import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledIntegerPeriodic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRightMemSB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaIntegralEquivariantNonzeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalSchwartzLatticeCombinationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzAveragingLeftInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaIdentityAnalyticContinuationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedSphericalZetaIntegralOneStatement

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit GlobalTheory.GJReg
namespace GlobalTheory.GJReg
theorem span_latInd : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
    (φ : Matrix (Fin n) (Fin n) k → ℂ), φ ∈ SB (Matrix (Fin n) (Fin n) k) →
    (∀ g ∈ KO k (Fin n), ∀ X, φ (g.val * X) = φ X) →
    ∃ (m : ℕ) (c : Fin m → ℂ) (h : Fin m → GL (Fin n) k), φ = ∑ i, c i • latInd (h i) := GlobalTheory.T.spherical_schwartz_lattice_combination
theorem avg_KO : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
    (φ : Matrix (Fin n) (Fin n) k → ℂ), φ ∈ SB (Matrix (Fin n) (Fin n) k) →
    ∃ (m : ℕ) (w : Fin m → ℂ) (u : Fin m → GL (Fin n) k), (∀ i, u i ∈ KO k (Fin n)) ∧ ∑ i, w i = 1 ∧
      ∀ g ∈ KO k (Fin n), ∀ X, ∑ i, w i * φ ((u i).val * (g.val * X)) = ∑ i, w i * φ ((u i).val * X) := GlobalTheory.T.schwartz_averaging_left_invariant
theorem ident_comb : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
    (ν : kˣ →* ℂˣ) (m m' : ℕ) (c : Fin m → ℂ) (h : Fin m → GL (Fin n) k) (c' : Fin m' → ℂ)
    (h' : Fin m' → GL (Fin n) k) (s₀ : ℝ),
    (∀ s : ℂ, s₀ < s.re → ∑ i, c i * chiS ν s (h i) = ∑ i, c' i * chiS ν s (h' i)) →
    ∀ s : ℂ, ∑ i, c i * chiS ν s (h i) = ∑ i, c' i * chiS ν s (h' i) := GlobalTheory.T.zeta_identity_analytic_continuation
theorem gjZ_kInd : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
    [BorelSpace k] (n : ℕ) (ν : kˣ →* ℂˣ) (s : ℂ), IsUnram ν →
    kInd k n ∈ SB (Matrix (Fin n) (Fin n) k) ∧ gjZ ν s (kInd k n) = 1 := GlobalTheory.T.unramified_spherical_zeta_integral_one
end GlobalTheory.GJReg

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit GlobalTheory.GJReg

noncomputable section
namespace GlobalTheory.GJReg

def Comb (k : Type) [Field k] (n : ℕ) : Type := Σ m : ℕ, (Fin m → ℂ) × (Fin m → GL (Fin n) k)

section Comb
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

def Comb.ev (ν : kˣ →* ℂˣ) (r : Comb k n) (s : ℂ) : ℂ := ∑ i, r.2.1 i * chiS ν s (r.2.2 i)

def Comb.app (r r' : Comb k n) : Comb k n := ⟨r.1 + r'.1, (Fin.append r.2.1 r'.2.1, Fin.append r.2.2 r'.2.2)⟩

theorem Comb.ev_app (ν : kˣ →* ℂˣ) (r r' : Comb k n) (s : ℂ) : (r.app r').ev ν s = r.ev ν s + r'.ev ν s := by
  unfold Comb.ev Comb.app
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

def Comb.smul (c : ℂ) (r : Comb k n) : Comb k n := ⟨r.1, (fun i => c * r.2.1 i, r.2.2)⟩

theorem Comb.ev_smul (ν : kˣ →* ℂˣ) (c : ℂ) (r : Comb k n) (s : ℂ) : (r.smul c).ev ν s = c * r.ev ν s := by
  unfold Comb.ev Comb.smul
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => mul_assoc _ _ _

def Comb.tr (g : GL (Fin n) k) (r : Comb k n) : Comb k n := ⟨r.1, (r.2.1, fun i => r.2.2 i * g)⟩

theorem Comb.ev_tr (ν : kˣ →* ℂˣ) (g : GL (Fin n) k) (r : Comb k n) (s : ℂ) :
    (r.tr g).ev ν s = chiS ν s g * r.ev ν s := by
  simp only [Comb.ev, Comb.tr, chiS_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

def Comb.unit : Comb k n := ⟨1, (fun _ => 1, fun _ => 1)⟩

theorem Comb.ev_unit (ν : kˣ →* ℂˣ) (s : ℂ) : (Comb.unit : Comb k n).ev ν s = 1 := by
  show ∑ _i : Fin 1, (1 : ℂ) * chiS ν s 1 = 1
  simp

end Comb

section Forms
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
  {ν : kˣ →* ℂˣ} {z : ℂ} {l : (Matrix (Fin n) (Fin n) k → ℂ) → ℂ}

theorem eqv_zero (hl : IsEqv ν z l) : l 0 = 0 := by
  have h := hl.2.1 0 0 (zero_mem _)
  simpa using h

theorem eqv_sum (hl : IsEqv ν z l) {m : ℕ} (c : Fin m → ℂ) (φ : Fin m → Matrix (Fin n) (Fin n) k → ℂ)
    (hφ : ∀ i, φ i ∈ SB (Matrix (Fin n) (Fin n) k)) : l (∑ i, c i • φ i) = ∑ i, c i * l (φ i) := by
  classical
  refine Finset.induction_on (Finset.univ : Finset (Fin m)) (by simp [eqv_zero hl]) fun a s has ih => ?_
  rw [Finset.sum_insert has, Finset.sum_insert has, hl.1 _ (Submodule.smul_mem _ _ (hφ a)) _
    (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hφ i)), hl.2.1 _ _ (hφ a), ih]

theorem eqv_apply (hl : IsEqv ν z l) (g₁ g₂ : GL (Fin n) k) {φ : Matrix (Fin n) (Fin n) k → ℂ}
    (hφ : φ ∈ SB (Matrix (Fin n) (Fin n) k)) :
    chiS ν z (g₁ * g₂) * l (fun X => φ (g₁.val * X * g₂.val)) = l φ := by
  rw [chiS, gdet_mul]; exact hl.2.2 g₁ g₂ φ hφ

theorem eqv_left_KO (hν : IsUnram ν) (hl : IsEqv ν z l) {g : GL (Fin n) k} (hg : g ∈ KO k (Fin n))
    {φ : Matrix (Fin n) (Fin n) k → ℂ} (hφ : φ ∈ SB (Matrix (Fin n) (Fin n) k)) :
    l (fun X => φ (g.val * X)) = l φ := by
  have h := eqv_apply hl g 1 hφ
  rw [mul_one, chiS_of_mem_KO hν z hg, one_mul] at h
  simpa using h

theorem eqv_latInd (hl : IsEqv ν z l) (g : GL (Fin n) k) :
    l (latInd g) = chiS ν z g * l ((intM k (Fin n) (Fin n)).indicator 1) := by
  have h := eqv_apply hl 1 g⁻¹ indicator_intM_mem_SB
  have e : (fun X => (intM k (Fin n) (Fin n)).indicator (1 : Matrix (Fin n) (Fin n) k → ℂ)
      ((1 : GL (Fin n) k).val * X * (g⁻¹ : GL (Fin n) k).val)) = latInd g := by
    funext X; simp [latInd]
  rw [e, one_mul] at h
  rw [← h, ← mul_assoc, mul_comm (chiS ν z g), chiS_inv_mul, one_mul]

end Forms

section Main
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n : ℕ} {ν : kˣ →* ℂˣ}

def IsRep (ν : kˣ →* ℂˣ) (φ : Matrix (Fin n) (Fin n) k → ℂ) (r : Comb k n) : Prop :=
  ∀ s : ℂ, (n : ℝ) - 1 < s.re → gjZ ν s φ = r.ev ν s * gjZ ν s ((intM k (Fin n) (Fin n)).indicator 1)

theorem gjZ_eqv (hS : IsSmU ν) {s : ℂ} (hs : (n : ℝ) - 1 < s.re) : IsEqv ν s (gjZ (n := n) ν s) :=
  (GlobalTheory.T.zeta_integral_equivariant_nonzero k n ν s hS hs).1

theorem exists_rep (hS : IsSmU ν) (hν : IsUnram ν) {φ : Matrix (Fin n) (Fin n) k → ℂ}
    (hφ : φ ∈ SB (Matrix (Fin n) (Fin n) k)) : ∃ r : Comb k n, IsRep ν φ r := by
  obtain ⟨m, w, u, hu, hw, hinv⟩ := avg_KO k n φ hφ
  set ψ : Matrix (Fin n) (Fin n) k → ℂ := ∑ i, w i • fun X => φ ((u i).val * X) with hψdef
  have hψ : ∀ i, (fun X => φ ((u i).val * X)) ∈ SB (Matrix (Fin n) (Fin n) k) := fun i => mul_left_mem_SB _ hφ
  have hψSB : ψ ∈ SB (Matrix (Fin n) (Fin n) k) := Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hψ i)
  have hψK : ∀ g ∈ KO k (Fin n), ∀ X, ψ (g.val * X) = ψ X := fun g hg X => by
    simpa [hψdef, Finset.sum_apply] using hinv g hg X
  obtain ⟨m', c, h, hc⟩ := span_latInd k n ψ hψSB hψK
  refine ⟨⟨m', (c, h)⟩, fun s hs => ?_⟩
  have hl := gjZ_eqv (n := n) hS hs
  have e1 : gjZ ν s ψ = gjZ ν s φ := by
    rw [hψdef, eqv_sum hl w _ hψ]
    simp only [eqv_left_KO hν hl (hu _) hφ, ← Finset.sum_mul, hw, one_mul]
  rw [← e1, hc, eqv_sum hl c _ fun i => latInd_mem_SB (h i)]
  show _ = (∑ i, c i * chiS ν s (h i)) * _
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by rw [eqv_latInd hl, mul_assoc]

theorem gjZ_int_ne_zero (hS : IsSmU ν) (hν : IsUnram ν) {s : ℂ} (hs : (n : ℝ) - 1 < s.re) :
    gjZ ν s ((intM k (Fin n) (Fin n)).indicator 1) ≠ 0 := by
  obtain ⟨hK, hv⟩ := gjZ_kInd k n ν s hν
  obtain ⟨r, hr⟩ := exists_rep hS hν hK
  intro h0
  have := hr s hs
  rw [hv, h0, mul_zero] at this
  exact one_ne_zero this

theorem rep_unique (hS : IsSmU ν) (hν : IsUnram ν) {φ : Matrix (Fin n) (Fin n) k → ℂ} {r r' : Comb k n}
    (hr : IsRep ν φ r) (hr' : IsRep ν φ r') (s : ℂ) : r.ev ν s = r'.ev ν s :=
  ident_comb k n ν r.1 r'.1 r.2.1 r.2.2 r'.2.1 r'.2.2 ((n : ℝ) - 1) (fun s hs =>
    mul_right_cancel₀ (gjZ_int_ne_zero hS hν hs) ((hr s hs).symm.trans (hr' s hs))) s

def regZ (hS : IsSmU ν) (hν : IsUnram ν) (z : ℂ) (φ : Matrix (Fin n) (Fin n) k → ℂ) : ℂ :=
  open Classical in
  if h : φ ∈ SB (Matrix (Fin n) (Fin n) k) then (Classical.choose (exists_rep hS hν h)).ev ν z else 0

theorem regZ_eq (hS : IsSmU ν) (hν : IsUnram ν) (z : ℂ) {φ : Matrix (Fin n) (Fin n) k → ℂ}
    (hφ : φ ∈ SB (Matrix (Fin n) (Fin n) k)) {r : Comb k n} (hr : IsRep ν φ r) : regZ hS hν z φ = r.ev ν z := by
  rw [regZ, dif_pos hφ]
  exact rep_unique hS hν (Classical.choose_spec (exists_rep hS hν hφ)) hr z

theorem regZ_isEqv (hS : IsSmU ν) (hν : IsUnram ν) (z : ℂ) : IsEqv ν z (regZ (n := n) hS hν z) := by
  refine ⟨fun φ hφ φ' hφ' => ?_, fun c φ hφ => ?_, fun g₁ g₂ φ hφ => ?_⟩
  · obtain ⟨r, hr⟩ := exists_rep hS hν hφ
    obtain ⟨r', hr'⟩ := exists_rep hS hν hφ'
    have hrr : IsRep ν (φ + φ') (r.app r') := fun s hs => by
      rw [(gjZ_eqv hS hs).1 φ hφ φ' hφ', hr s hs, hr' s hs, Comb.ev_app, add_mul]
    rw [regZ_eq hS hν z (Submodule.add_mem _ hφ hφ') hrr, regZ_eq hS hν z hφ hr, regZ_eq hS hν z hφ' hr',
      Comb.ev_app]
  · obtain ⟨r, hr⟩ := exists_rep hS hν hφ
    have hrr : IsRep ν (c • φ) (r.smul c) := fun s hs => by
      rw [(gjZ_eqv hS hs).2.1 c φ hφ, hr s hs, Comb.ev_smul, mul_assoc]
    rw [regZ_eq hS hν z (Submodule.smul_mem _ c hφ) hrr, regZ_eq hS hν z hφ hr, Comb.ev_smul]
  · obtain ⟨r, hr⟩ := exists_rep hS hν hφ
    have hφ' : (fun X => φ (g₁.val * X * g₂.val)) ∈ SB (Matrix (Fin n) (Fin n) k) := by
      have := mul_right_mem_SB g₂ (mul_left_mem_SB g₁ hφ)
      simpa only [Matrix.mul_assoc] using this
    have hrr : IsRep ν (fun X => φ (g₁.val * X * g₂.val)) (r.tr (g₁ * g₂)⁻¹) := fun s hs => by
      have h := eqv_apply (gjZ_eqv hS hs) g₁ g₂ hφ
      rw [Comb.ev_tr, mul_assoc, ← hr s hs, ← h, ← mul_assoc, chiS_inv_mul, one_mul]
    rw [regZ_eq hS hν z hφ' hrr, regZ_eq hS hν z hφ hr, Comb.ev_tr, ← mul_assoc,
      show (ν (gdet g₁ * gdet g₂) : ℂ) * apow (gdet g₁ * gdet g₂) z = chiS ν z (g₁ * g₂) by rw [chiS, gdet_mul],
      mul_comm (chiS ν z (g₁ * g₂)), chiS_inv_mul, one_mul]

theorem regZ_int (hS : IsSmU ν) (hν : IsUnram ν) (z : ℂ) :
    regZ hS hν z ((intM k (Fin n) (Fin n)).indicator 1) = 1 := by
  rw [regZ_eq hS hν z indicator_intM_mem_SB (r := Comb.unit) (fun s hs => by rw [Comb.ev_unit, one_mul]),
    Comb.ev_unit]

end Main

theorem exists_regGJ : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ν : kˣ →* ℂˣ) (z : ℂ), IsSmU ν → IsUnram ν →
    ∃ l : (Matrix (Fin n) (Fin n) k → ℂ) → ℂ, IsEqv ν z l ∧ l ((intM k (Fin n) (Fin n)).indicator 1) = 1 := by
  intro k _ _ _ _ n ν z hS hν
  borelize k
  exact ⟨regZ hS hν z, regZ_isEqv hS hν z, regZ_int hS hν z⟩

end GlobalTheory.GJReg
