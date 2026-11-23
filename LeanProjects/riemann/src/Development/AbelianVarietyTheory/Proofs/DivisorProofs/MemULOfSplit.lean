import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DgMatOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenConjStableSubgroupOfSplitLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLevelBlockLevelsSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockLevelsEqIntegralGLOfUnramifiedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUpperTimesUnipotentMulBlockDiagonalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarIntegralNormalizedIntegralMatricesTwoSidedMuStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsHalfBlockDetIntegralGLInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportTwistedConstantTermSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedConstantTermSplitPlaceRegularStatement

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.CtLevel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.CtLevel

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem mem_UL_of_split {n : ℕ} {w : Pl E} (hw : IsSplitAt w) (x : GLw n w) : x ∈ UL n w := by
  rw [UL, if_pos hw]; exact Subgroup.mem_top x

theorem toSub_eq {G : Type} [Group G] (H : Subgroup G) (g : G) (hg : g ∈ H) : toSub H g = ⟨g, hg⟩ := by
  simp [toSub, hg]

theorem ct_inv {a b n : ℕ} (h : a + b = n) (w : Pl E) (N : Subgroup (GLw n w)) (F : GLw n w → ℂ)
    (hNn : ∀ k ∈ GlobalTheory.LFun.KGL w n, ∀ x ∈ N, k⁻¹ * x * k ∈ N)
    (hF : ∀ y ∈ N, ∀ x, F (y * x) = F x ∧ F (x * y) = F x)
    (k : GLw a w × GLw b w) (hk1 : k.1 ∈ GlobalTheory.LFun.KGL w a) (hk2 : k.2 ∈ GlobalTheory.LFun.KGL w b) (hkN : dgM h w k ∈ N)
    (m : GLw a w × GLw b w) : ct h w F (k * m) = ct h w F m ∧ ct h w F (m * k) = ct h w F m := by
  have hab := GlobalTheory.T.absHalf_blockDet_integralGL_invariant E a b w m k hk1 hk2
  constructor
  · unfold ct
    rw [hab.1]
    congr 2
    funext X
    congr 1
    funext κ
    rw [(GlobalTheory.T.blockUpperTimesUnipotent_mul_blockDiagonal E a b n h w m k _).1]
    have e : (κ : GLw n w)⁻¹ * (dgM h w k * blk h w m (Multiplicative.toAdd X)) * κ =
        ((κ : GLw n w)⁻¹ * dgM h w k * κ) * ((κ : GLw n w)⁻¹ * blk h w m (Multiplicative.toAdd X) * κ) := by group
    rw [e, (hF _ (hNn _ κ.2 _ hkN) _).1]
  · unfold ct
    have e : (fun X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) =>
        avg fun κ : GlobalTheory.LFun.KGL w n => F ((κ : GLw n w)⁻¹ * blk h w (m * k) (Multiplicative.toAdd X) * κ)) =
        fun X => avg fun κ : GlobalTheory.LFun.KGL w n => F ((κ : GLw n w)⁻¹ *
          blk h w m (Multiplicative.toAdd (Multiplicative.ofAdd (k.1.val * Multiplicative.toAdd X * (k.2⁻¹).val))) * κ) := by
      funext X
      congr 1
      funext κ
      rw [(GlobalTheory.T.blockUpperTimesUnipotent_mul_blockDiagonal E a b n h w m k _).2]
      have e : (κ : GLw n w)⁻¹ * (blk h w m (k.1.val * Multiplicative.toAdd X * (k.2⁻¹).val) * dgM h w k) * κ =
          ((κ : GLw n w)⁻¹ * blk h w m (k.1.val * Multiplicative.toAdd X * (k.2⁻¹).val) * κ) *
            ((κ : GLw n w)⁻¹ * dgM h w k * κ) := by group
      rw [e, (hF _ (hNn _ κ.2 _ hkN) _).2]
      rfl
    have hh := GlobalTheory.T.haarIntegralNormalized_integralMatrices_twoSidedMul E a b w (fun Y => avg fun κ : GlobalTheory.LFun.KGL w n =>
      F ((κ : GLw n w)⁻¹ * blk h w m (Multiplicative.toAdd Y) * κ)) k.1 k.2⁻¹ hk1 (inv_mem hk2)
    rw [hab.2, e, hh]

theorem ctMu_inv {a b n : ℕ} (h : a + b = n) (w : Pl E) (hw : IsSplitAt w) (N : Subgroup (GLw n w))
    (K' : Subgroup (UL n w)) (μ : (w.adicCompletion E)ˣ →* ℂˣ) (f : UL n w → ℂ) (hf : IsHecke K' f)
    (hNK : N ≤ K'.map (UL n w).subtype) (hNn : ∀ k ∈ GlobalTheory.LFun.KGL w n, ∀ x ∈ N, k⁻¹ * x * k ∈ N)
    (k : GLw a w × GLw b w) (hk : k ∈ (lev₁ h w N μ).prod (lev₂ h w N μ)) (m : GLw a w × GLw b w) :
    ctMu h w μ f (k * m) = ctMu h w μ f m ∧ ctMu h w μ f (m * k) = ctMu h w μ f m := by
  obtain ⟨⟨⟨hk1, hkN1⟩, hkμ1⟩, ⟨⟨hk2, hkN2⟩, hkμ2⟩⟩ := hk
  have hkN : dgM h w k ∈ N := by
    have e : k = (k.1, 1) * (1, k.2) := by ext <;> simp
    rw [e, map_mul]
    exact N.mul_mem hkN1 hkN2
  have hF : ∀ y ∈ N, ∀ x, (fun y => f (toSub (UL n w) y)) (y * x) = (fun y => f (toSub (UL n w) y)) x ∧
      (fun y => f (toSub (UL n w) y)) (x * y) = (fun y => f (toSub (UL n w) y)) x := by
    intro y hy x
    obtain ⟨y', hy', rfl⟩ := hNK hy
    have e1 : toSub (UL n w) ((UL n w).subtype y' * x) = y' * toSub (UL n w) x := by
      rw [toSub_eq _ _ (mem_UL_of_split hw _), toSub_eq _ _ (mem_UL_of_split hw x)]; rfl
    have e2 : toSub (UL n w) (x * (UL n w).subtype y') = toSub (UL n w) x * y' := by
      rw [toSub_eq _ _ (mem_UL_of_split hw _), toSub_eq _ _ (mem_UL_of_split hw x)]; rfl
    exact ⟨by simp only; rw [e1]; exact (hf.2 y' hy' _).1, by simp only; rw [e2]; exact (hf.2 y' hy' _).2⟩
  have hc := ct_inv h w N (fun y => f (toSub (UL n w) y)) hNn hF k hk1 hk2 hkN m
  have hμ1 : μ (GeneralLinearGroup.det k.1) = 1 := hkμ1
  have hμ2 : μ (GeneralLinearGroup.det k.2) = 1 := hkμ2
  unfold ctMu
  rw [hc.1, hc.2]
  simp only [Prod.fst_mul, Prod.snd_mul, map_mul, mul_pow, map_pow, hμ1, hμ2, one_pow, mul_one, one_mul]
  constructor <;> trivial

theorem ctMu_hecke : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n a : ℕ) (ha : a ≤ n) (w : Pl E), IsSplitAt w → ∀ (μ : (w.adicCompletion E)ˣ →* ℂˣ), IsOpen {x | μ x = 1} → ∀ K' : Subgroup (UL n w), IsLevel (MonoidHom.id _) (KL n w) K' → ∃ (K₁ : Subgroup (GLw a w)) (K₂ : Subgroup (GLw (n - a) w)), IsLevel (thL a w) (GlobalTheory.LFun.KGL w a) K₁ ∧ IsLevel (thL (n - a) w) (GlobalTheory.LFun.KGL w (n - a)) K₂ ∧ ((K' = KL n w ∧ ∀ u ∈ (GlobalTheory.LFun.KGL w 1), μ (GeneralLinearGroup.det u) = 1) → K₁ = GlobalTheory.LFun.KGL w a ∧ K₂ = GlobalTheory.LFun.KGL w (n - a)) ∧ ∀ f, IsHecke K' f → IsHecke (K₁.prod K₂) (ctMu (Nat.add_sub_cancel' ha) w μ f) ∧ ((∀ y, f y ≠ 0 → y.1.val.charpoly.Separable) → RegAt2 a (n - a) w (ctMu (Nat.add_sub_cancel' ha) w μ f)) := by
  intro E _ _ _ _ n a ha w hw μ hμ K' hK'
  obtain ⟨N, hNo, hNK, hNn, hNf⟩ := GlobalTheory.T.exists_open_conjStable_subgroup_of_splitLevel E n w K' hw hK'
  have hlev := GlobalTheory.T.isLevel_blockLevels_splitPlace E a (n - a) n (Nat.add_sub_cancel' ha) w N μ hw hNo hμ
  refine ⟨lev₁ (Nat.add_sub_cancel' ha) w N μ, lev₂ (Nat.add_sub_cancel' ha) w N μ, hlev.1, hlev.2, ?_,
    fun f hf => ⟨⟨GlobalTheory.T.hasCompactSupport_twistedConstantTermSplitPlace E a (n - a) n _ w μ f hw hf.1, fun k hk m =>
      ctMu_inv _ w hw N K' μ f hf hNK hNn k hk m⟩, GlobalTheory.T.twistedConstantTermSplitPlace_regular E a (n - a) n _ w μ f hw⟩⟩
  rintro ⟨hK'e, hμ1⟩
  rw [hNf hK'e]
  exact GlobalTheory.T.blockLevels_eq_integralGL_of_unramified E a (n - a) n _ w μ hμ1

end GlobalTheory.BCT.CtLevel
