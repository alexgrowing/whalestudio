import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap

noncomputable section

open scoped TensorProduct Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace PositivityTheory.RL

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def sgnAd (w : InfinitePlace F) : AF F :=
  ((fun v => if v = w then -1 else 1 : InfiniteAdeleRing F), 1)

theorem sgnAd_mul_self (w : InfinitePlace F) : sgnAd w * sgnAd w = 1 := by
  refine Prod.ext (funext fun v => ?_) (mul_one _)
  change (if v = w then (-1 : v.Completion) else 1) * (if v = w then (-1 : v.Completion) else 1) = 1
  split_ifs <;> simp

def sgnId (w : InfinitePlace F) : (AF F)ˣ := ⟨sgnAd w, sgnAd w, sgnAd_mul_self w, sgnAd_mul_self w⟩

theorem at_sgn (w : InfinitePlace F) : At (evI F) (algebraMap (AF F) (AE F E) (sgnAd w) - 1) := by
  intro u hu
  have h1 : u.1 = 0 := (map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective).1 hu
  have h2 : u * (sgnAd w - 1) = 0 := by
    refine Prod.ext ?_ ?_
    · change u.1 * _ = 0
      rw [h1, zero_mul]
    · change u.2 * (1 - 1) = 0
      rw [sub_self, mul_zero]
  rw [← map_one (algebraMap (AF F) (AE F E)), ← map_sub, Algebra.smul_def, ← map_mul, h2, map_zero]

theorem piInf_sgn (w v : InfinitePlace F) (τ : EmbOver E v) :
    piInf τ (algebraMap (AF F) (AE F E) (sgnAd w)) = if v = w then -1 else 1 := by
  change infEmb τ ((if v = w then (-1 : v.Completion) else 1) ⊗ₜ[F] (1 : E)) = _
  rw [infEmb_tmul]
  split_ifs <;> simp

theorem hasExp_sgn {τ : ∀ w : InfinitePlace F, EmbOver E w} {χ : Chr F E} {m : InfinitePlace F → ℤ}
    (h : HasExp τ χ m) (w : InfinitePlace F) :
    (χ (Units.map (algebraMap (AF F) (AE F E) : AF F →* AE F E) (sgnId w)) : ℂ) = (-1) ^ m w := by
  rw [h _ (at_sgn w)]
  change ∏ v, (piInf (τ v) (algebraMap (AF F) (AE F E) (sgnAd w)) /
    ‖piInf (τ v) (algebraMap (AF F) (AE F E) (sgnAd w))‖) ^ m v = _
  simp only [piInf_sgn]
  rw [Finset.prod_eq_single w]
  · simp
  · intro v _ hv
    simp [hv]
  · simp

theorem even_im_hermitian_sub : GlobalTheory.RealLift.Parity := by
  intro F E _ _ _ _ _ σ B a a' G X om om' h w
  have hα := h.chars.resα (sgnId w)
  have hβ := h.chars.resβ (sgnId w)
  rw [hasExp_sgn h.chars.expα] at hα
  rw [hasExp_sgn h.chars.expβ] at hβ
  have he : ((-1 : ℂ)) ^ a' = (-1) ^ a := by
    rcases Nat.even_or_odd a with ha | ha
    · rw [ha.neg_one_pow, ((Nat.even_add.1 h.geo.even).1 ha).neg_one_pow]
    · have : Odd a' := by
        rw [← Nat.not_even_iff_odd] at ha ⊢
        exact fun e => ha ((Nat.even_add.1 h.geo.even).2 e)
      rw [ha.neg_one_pow, this.neg_one_pow]
  have h1 : ((-1 : ℂ)) ^ (B.mα w - B.mβ w) = 1 := by
    rw [zpow_sub₀ (by norm_num), hα, hβ, he]
    split_ifs <;> simp
  by_contra hn
  rw [Int.not_even_iff_odd] at hn
  rw [hn.neg_one_zpow] at h1
  norm_num at h1

end PositivityTheory.RL

end
