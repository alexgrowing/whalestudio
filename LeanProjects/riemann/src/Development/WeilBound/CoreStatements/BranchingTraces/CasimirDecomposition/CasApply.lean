import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.ZuckermanGapSmall
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.HaarBumpFunctions.PoulsenSmoothVectorsDense

open Matrix Finset
open scoped InnerProductSpace Classical

noncomputable section

namespace PositivityTheory.UnitaryDecomposition.DecA

open CompanionTheory.Zuck BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData
open PI.UpqRep (IsHCParam)
open PI.ZuckTensor (GapAtLeast)

variable {t : ∀ n : ℕ, (Fin n → Bool) → ℝ} {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}

theorem decReg (S : Steps) (Lb : Lib t) (hk : 1 ≤ k) (b : Bool) {μ : Fin (2 * r + k + 1) → ℝ} {U : URep k r} {h : ℝ}
    (hU : U.R.IsDS ε μ) (hg : GapAtLeast ε μ h) (ht : t _ ε + (((2 * r + k + 1) ^ 2 + 2 : ℕ) : ℝ) + 1 < h)
    (T : {s // IsHCParam (shift b μ s)} → URep k r) (hT : ∀ s, (T s).R.IsDS ε (shift b μ s.1)) :
    ∃ io pr, IsDec (N := M) IsHom (vr k r b, U) (fun s => one (T s)) io pr := by
  have C := S.homCat k r
  have h1 : (1 : ℝ) ≤ (((2 * r + k + 1) ^ 2 + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega)
  have hsimp := S.schur S.infChar k r ε _ _ T ((shift_inj b μ).comp Subtype.val_injective) hT
  have adj' : ∀ U U' : URep k r, ∃ e : (M (vr k r (!b), U) →ₗ[ℂ] M (one U')) ≃ₗ[ℂ] (M (one U) →ₗ[ℂ] M (vr k r b, U')),
      ∀ p, IsHom (vr k r (!b), U) (one U') p ↔ IsHom (one U) (vr k r b, U') (e p) := by
    cases b
    · exact S.adj k r true
    · exact S.adj k r false
  have occ : ∀ s, ∃ i, IsHom (one (T s)) (vr k r b, U) i ∧ i ≠ 0 := by
    intro s
    obtain ⟨T', hT', -, hp⟩ := injV S Lb (!b) (hT s) (gap_shift hg b s.1) (by linarith)
    have hs : IsHCParam (shift (!b) (shift b μ s.1) s.1) := by rw [shift_shift]; exact hU.1
    obtain ⟨p, hp, hp0⟩ := hp ⟨s.1, hs⟩
    have hd : (T' ⟨s.1, hs⟩).R.IsDS ε μ := by simpa only [shift_shift] using hT' ⟨s.1, hs⟩
    obtain ⟨f, g, hf, -, hgf, -⟩ := iso_of S Lb hd hU hg (by linarith)
    obtain ⟨e, he⟩ := adj' (T s) U
    refine ⟨e (f ∘ₗ p), (he _).1 (C.comp _ _ _ _ _ hp hf), fun h0 => hp0 ?_⟩
    have h2 : f ∘ₗ p = 0 := e.map_eq_zero_iff.1 h0
    calc p = (g ∘ₗ f) ∘ₗ p := by rw [hgf, LinearMap.id_comp]
      _ = 0 := by rw [LinearMap.comp_assoc, h2, LinearMap.comp_zero]
  refine S.decOfInj _ _ _ C _ _ _ hsimp ?_ (fun s => ?_) occ
  · obtain ⟨T', hT', hi, -⟩ := injV S Lb b hU hg (by linarith)
    intro x hx
    refine hi x fun s p hp => ?_
    obtain ⟨f, g, hf, -, hgf, -⟩ := iso_of S Lb (hT' s) (hT s) (gap_shift hg b s.1) (by linarith)
    have h2 := hx s _ (C.comp _ _ _ _ _ hp hf)
    have h3 := LinearMap.congr_fun hgf (p x)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at h2 h3
    rw [← h3, h2, map_zero]
  · obtain ⟨T', hT', hi, -⟩ := injV S Lb b (hT s) (gap_shift hg b s.1) (by linarith)
    have cB := S.casDS S.infChar k r ε _ (T s) hk (hT s)
    have m1 : AtMostOne (N := M) IsHom (one U) (vr k r (!b), T s) := by
      have := fun hi' ho' => S.multOne k r (!b) (T s) U _ T' _ _ _ (fun F => (cB F).1) (cB (triv k r)).2
        (S.casDS S.infChar k r ε _ U hk hU (triv k r)).2
        (fun u => (S.casDS S.infChar k r ε _ (T' u) hk (hT' u) (triv k r)).2)
        (fun u => cas_ne hU.1.1 b s.1 u.1) hi' (hsimp.2.1 s) ⟨_, _, hU⟩ ho'
      cases b
      · exact this hi (occ s)
      · exact this hi (occ s)
    obtain ⟨e, he⟩ := S.adj k r b U (T s)
    intro f g hf hg'
    obtain ⟨α, β, hab, h0⟩ := m1 _ _ ((he f).1 hf) ((he g).1 hg')
    refine ⟨α, β, hab, e.map_eq_zero_iff.1 ?_⟩
    rw [map_add, map_smul, map_smul, h0]

def kOp (U : URep k r) : Module.End ℂ (M (vr k r true, U)) :=
  LinearMap.pi fun c => ∑ b, U.dC (Matrix.single c b 1) ∘ₗ LinearMap.proj b

theorem kOp_apply (U : URep k r) (x : M (vr k r true, U)) (c : Fin (2 * r + k + 1)) :
    kOp U x c = ∑ b, U.dC (Matrix.single c b 1) (x b) := by
  simp [kOp, LinearMap.sum_apply]

theorem L_apply (U : URep k r) (a b : Fin (2 * r + k + 1)) (x : M (vr k r true, U)) (c : Fin (2 * r + k + 1)) :
    L (vr k r true, U) (Matrix.single a b 1) x c = U.dC (Matrix.single a b 1) (x c) - if c = b then x a else 0 := by
  have h : (vr k r true, U).1.dC (Matrix.single a b 1) = -(Matrix.single a b (1 : ℂ))ᵀ := (GlobalTheory.T.StandardDifferential k r _).2
  simp only [L, h, LinearMap.add_apply, Pi.add_apply, dOp, mAct, LinearMap.compLeft_apply, Function.comp_apply,
    LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply, sub_eq_add_neg]
  congr 1
  rw [Finset.sum_eq_single a (fun d _ hd => by simp [Matrix.single_apply, hd.symm]) (by simp)]
  by_cases hc : c = b
  · simp [hc]
  · simp [Matrix.single_apply, hc, Ne.symm hc]

theorem cas_apply (U : URep k r) (x : M (vr k r true, U)) (c : Fin (2 * r + k + 1)) :
    cas (vr k r true, U) x c = casR (vr k r true, U) x c - (2 : ℂ) • kOp U x c + ((2 * r + k + 1 : ℕ) : ℂ) • x c := by
  simp only [cas, casR, dOp, LinearMap.compLeft_apply, Function.comp_apply, LinearMap.sum_apply, Finset.sum_apply,
    Module.End.mul_apply, L_apply, kOp_apply, map_sub, Finset.sum_sub_distrib, apply_ite (U.dC _), map_zero]
  have e1 : ∑ a, ∑ b, (if c = a then U.dC (Matrix.single a b 1) (x b) else 0) = ∑ b, U.dC (Matrix.single c b 1) (x b) := by
    rw [Finset.sum_comm]; simp
  have e2 : ∑ a : Fin (2 * r + k + 1), ∑ b, (if c = b then U.dC (Matrix.single b a 1) (x a) - (if True then x b else 0) else 0) =
      ∑ b, U.dC (Matrix.single c b 1) (x b) - ((2 * r + k + 1 : ℕ) : ℂ) • x c := by
    rw [Nat.cast_smul_eq_nsmul]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin]
  rw [e1, e2, two_smul]
  abel

theorem kOp_io {μ : Fin (2 * r + k + 1) → ℝ} {U T : URep k r} (hk : 1 ≤ k) (hU : U.R.IsDS ε μ) (s : Fin (2 * r + k + 1))
    (hT : T.R.IsDS ε (shift true μ s)) (i : M (one T) →ₗ[ℂ] M (vr k r true, U)) (hi : IsHom (one T) (vr k r true, U) i)
    (y : M (one T)) : kOp U (i y) = ((μ s : ℂ) + (((2 * r + k + 1 : ℕ) : ℂ) - 1) / 2) • i y := by
  have S := zuckerman_ingredients
  have hL := S.homLie k r _ _ i (S.okTriv k r) (S.okVr k r true) hi
  have h1 : cas (vr k r true, U) (i y) = i (cas (one T) y) := by
    simp only [cas, LinearMap.sum_apply, Module.End.mul_apply, map_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [← LinearMap.comp_apply (L _ (Matrix.single b a 1)) i, ← hL, LinearMap.comp_apply,
      ← LinearMap.comp_apply (L _ (Matrix.single a b 1)) i, ← hL, LinearMap.comp_apply]
  rw [(S.casDS S.infChar k r ε _ T hk hT (triv k r)).2, casG_shift] at h1
  funext c
  have h2 := cas_apply U (i y) c
  rw [h1, (S.casDS S.infChar k r ε _ U hk hU (vr k r true)).1] at h2
  simp only [LinearMap.smul_apply, LinearMap.id_apply, map_smul, Pi.smul_apply, if_true] at h2 ⊢
  push_cast at h2 ⊢
  linear_combination (norm := module) (1 / 2 : ℂ) • h2

end PositivityTheory.UnitaryDecomposition.DecA
