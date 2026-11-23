import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShearGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicCoefficientTranslation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SetIntegralInvMulVec
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPairingConductorBoundStatement
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

noncomputable section

namespace GlobalTheory.CompanionTheory.MirPair.ConjEv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem mem_box_iff_forall_valuation_le {m : ℕ} {s : kˣ} {x : Fin m → k} :
    x ∈ GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box m s ↔ ∀ j, valuation k (x j) ≤ valuation k (s : k) :=
  Iff.rfl

theorem exists_mulVec_box (m : ℕ) (g : Matrix (Fin m) (Fin m) k) (t : kˣ) :
    ∃ t' : kˣ, ∀ x ∈ box m t, g *ᵥ x ∈ box m t' := by
  rcases isEmpty_or_nonempty (Fin m) with hm | hm
  · exact ⟨t, fun x _ => mem_box_iff_forall_valuation_le.2 fun j => isEmptyElim j⟩
  obtain ⟨ij, hij⟩ := Finite.exists_max (fun ij : Fin m × Fin m => valuation k (g ij.1 ij.2))
  by_cases h0 : g ij.1 ij.2 = 0
  · refine ⟨t, fun x _ => ?_⟩
    have hg : g = 0 := by
      ext i j
      simpa [h0] using hij (i, j)
    rw [hg, Matrix.zero_mulVec]
    exact zero_mem _
  · refine ⟨Units.mk0 _ h0 * t, fun x hx => ?_⟩
    rw [mem_box_iff_forall_valuation_le] at hx ⊢
    intro i
    show valuation k (∑ j, g i j * x j) ≤ _
    refine Finset.sum_induction _ (fun y => valuation k y ≤ valuation k ((Units.mk0 _ h0 * t : kˣ) : k))
      (fun a b ha hb => (valuation k).map_add_le ha hb) (by simp) (fun j _ => ?_)
    rw [map_mul, Units.val_mul, map_mul, Units.val_mk0]
    exact mul_le_mul' (hij (i, j)) (hx j)

theorem box_mono {m : ℕ} {t t' : kˣ} (h : valuation k (t : k) ≤ valuation k (t' : k)) :
    ∀ x ∈ box m t, x ∈ box m t' := by
  intro x hx
  rw [mem_box_iff_forall_valuation_le] at hx ⊢
  exact fun j => le_trans (hx j) h

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem val_mul_inv_le {c r t : kˣ} (h : valuation k ((c * r⁻¹ : kˣ) : k) ≤ valuation k (t : k)) :
    valuation k ((c * t⁻¹ : kˣ) : k) ≤ valuation k (r : k) := by
  have e1 : c * t⁻¹ = (c * r⁻¹) * (r * t⁻¹) := by
    rw [mul_assoc, inv_mul_cancel_left]
  have e2 : t * (r * t⁻¹) = r := by
    rw [mul_comm r, ← mul_assoc, mul_inv_cancel, one_mul]
  calc valuation k ((c * t⁻¹ : kˣ) : k)
      = valuation k ((c * r⁻¹ : kˣ) : k) * valuation k ((r * t⁻¹ : kˣ) : k) := by
        rw [e1, Units.val_mul, map_mul]
    _ ≤ valuation k (t : k) * valuation k ((r * t⁻¹ : kˣ) : k) := mul_le_mul' h le_rfl
    _ = valuation k (r : k) := by
        rw [← map_mul, ← Units.val_mul, e2]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem wt_mir (ψ : AddChar k Circle) {n : ℕ} (p : Mir k n) (y : Fin (n + 1) → k) :
    wt ψ n (((p : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ y) = wt ψ n y := by
  unfold GlobalTheory.CompanionTheory.MirPair.wt
  rw [GlobalTheory.BZMir.mulVec_last_of_mem k _ p.2]

theorem absPow_succ_val (s : ℕ) (u : kˣ) :
    ((absPow k ((s + 1 : ℕ) : ℂ) u : ℂˣ) : ℂ) = ((absPow k (s : ℂ) u : ℂˣ) : ℂ) * ((nabs k u : ℝ) : ℂ) := by
  rw [show ((s + 1 : ℕ) : ℂ) = (s : ℂ) + 1 by push_cast; ring, GlobalTheory.SmGL.absPow_add,
    MonoidHom.mul_apply, Units.val_mul, GlobalTheory.SmGL.val_absPow k 1, Complex.cpow_one]

variable [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle)
  {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
  (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V')
  (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (s : ℕ)

theorem JJ_conj (hB : TwInv T T' B s) (p : Mir k n) (M : Set (Fin (n + 1) → k)) (v : V) (v' : V') :
    JJ ν ψ T B M (T (levi k (n + 1) (p : GL (Fin (n + 1)) k)) v)
        (T' (levi k (n + 1) (p : GL (Fin (n + 1)) k)) v') =
      ((detChar (Fin (n + 1)) (absPow k ((s + 1 : ℕ) : ℂ)) (p : GL (Fin (n + 1)) k) : ℂˣ) : ℂ) *
        JJ ν ψ T B {y | ((p : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ y ∈ M} v v' := by
  obtain ⟨-, -, hlevi⟩ := GlobalTheory.CompanionTheory.MirPair.coef_rules T T' B s hB
  have hw : ∀ x : Fin (n + 1) → k, GlobalTheory.CompanionTheory.MirPair.wt ψ n x =
      GlobalTheory.CompanionTheory.MirPair.wt ψ n
        ((((p : GL (Fin (n + 1)) k)⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x) := by
    intro x
    have h := GlobalTheory.CompanionTheory.MirPair.ConjEv.wt_mir ψ p⁻¹ x
    rw [Subgroup.coe_inv] at h
    exact h.symm
  have hF := GlobalTheory.CompanionTheory.MirPair.setIntegral_inv_mulVec ν (n + 1) (p : GL (Fin (n + 1)) k) M
    (fun y => GlobalTheory.CompanionTheory.MirPair.wt ψ n y * GlobalTheory.CompanionTheory.MirPair.coef T B v v' y)
  have key : ∀ x : Fin (n + 1) → k,
      GlobalTheory.CompanionTheory.MirPair.wt ψ n x *
                   GlobalTheory.CompanionTheory.MirPair.coef T B (T (GlobalTheory.BZMir.levi k (n + 1) (p : GL (Fin (n + 1)) k)) v)
                     (T' (GlobalTheory.BZMir.levi k (n + 1) (p : GL (Fin (n + 1)) k)) v') x =
        ((GlobalTheory.SmGL.detChar (Fin (n + 1)) (GlobalTheory.SmGL.absPow k (s : ℂ))
            (p : GL (Fin (n + 1)) k) : ℂˣ) : ℂ) *
          (GlobalTheory.CompanionTheory.MirPair.wt ψ n
                       ((((p : GL (Fin (n + 1)) k)⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x) *
            GlobalTheory.CompanionTheory.MirPair.coef T B v v'
              ((((p : GL (Fin (n + 1)) k)⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x)) := by
    intro x
    rw [hlevi, ← hw]
    ring
  unfold GlobalTheory.CompanionTheory.MirPair.JJ
  simp only [key]
  rw [integral_const_mul, hF, ← mul_assoc]
  congr 1
  rw [GlobalTheory.SmGL.detChar_apply, GlobalTheory.SmGL.detChar_apply, GlobalTheory.CompanionTheory.MirPair.ConjEv.absPow_succ_val]

end GlobalTheory.CompanionTheory.MirPair.ConjEv

namespace GlobalTheory.CompanionTheory.MirPair

theorem evVal_conj : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) (c : kˣ) {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V') (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (s : ℕ), Continuous ψ → HasConductor ψ c → IsSmooth T → IsSmooth T' → TwInv T T' B s → ∀ (p : Mir k n) (v : V) (v' : V') (A : ℂ), EvVal ν ψ T B v v' A → EvVal ν ψ T B (T (levi k (n + 1) (p : GL (Fin (n + 1)) k)) v) (T' (levi k (n + 1) (p : GL (Fin (n + 1)) k)) v') (((detChar (Fin (n + 1)) (absPow k ((s + 1 : ℕ) : ℂ)) (p : GL (Fin (n + 1)) k) : ℂˣ) : ℂ) * A) := by
  intro k _ _ _ _ _ _ ν _ ψ c n V V' _ _ _ _ T T' B s hψ hc hT hT' hB p v v' A hA
  obtain ⟨t₀, ht₀⟩ := hA
  obtain ⟨r, hr⟩ := GlobalTheory.T.mirabolic_pairing_conductor_bound ν ψ c T T' B s hψ hc hT hT' hB
    (p : GL (Fin (n + 1)) k) v v'
  obtain ⟨t₁, ht₁₀, ht₁r⟩ : ∃ t₁ : kˣ, valuation k (t₀ : k) ≤ valuation k (t₁ : k) ∧
      valuation k ((c * r⁻¹ : kˣ) : k) ≤ valuation k (t₁ : k) := by
    rcases le_total (valuation k (t₀ : k)) (valuation k ((c * r⁻¹ : kˣ) : k)) with h | h
    · exact ⟨c * r⁻¹, h, le_rfl⟩
    · exact ⟨t₀, le_rfl, h⟩
  obtain ⟨t₂, ht₂⟩ := GlobalTheory.CompanionTheory.MirPair.ConjEv.exists_mulVec_box (n + 1)
    ((p : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) t₁
  refine ⟨t₂, fun t ht => ?_⟩
  rw [GlobalTheory.CompanionTheory.MirPair.ConjEv.JJ_conj ν ψ T T' B s hB p]
  congr 1
  rw [← ht₀ t₁ ht₁₀]
  exact hr t₁ (GlobalTheory.CompanionTheory.MirPair.ConjEv.val_mul_inv_le ht₁r) t
    (fun x hx => GlobalTheory.CompanionTheory.MirPair.ConjEv.box_mono ht _ (ht₂ x hx))

end GlobalTheory.CompanionTheory.MirPair

end
