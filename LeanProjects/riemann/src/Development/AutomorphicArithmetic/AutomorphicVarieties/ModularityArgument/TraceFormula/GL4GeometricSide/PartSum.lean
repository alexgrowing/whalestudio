import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.InnerEq
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.DiracW
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.LefData
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.HomSurj
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.HarmDom
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.EntriesZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HarmonicOfNormBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RangeStable

open UpperTheory.V.Z.GSp4Splitting PositivityTheory.RgBcC PositivityTheory.RgBcC.RealD PositivityTheory.Rg.BcB.Desc

noncomputable section

namespace UpperTheory.V.Z.GSp4Splitting.LowRankIsomorphism

open Finset UpperTheory.RealTr GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG

variable {n : ℕ}

private theorem part_sum (c : Fin n → Fin n → ℕ) (Q : Fin n → ℝ)
    (hQ : ∀ x, Q x = ∑ a, ∑ b, (c a b : ℝ) * ((if x = a then 1 else 0) - (if x = b then 1 else 0)))
    (S : Finset (Fin n)) :
    ∑ x ∈ S, Q x = ∑ a, ∑ b, (c a b : ℝ) * ((if a ∈ S then 1 else 0) - (if b ∈ S then 1 else 0)) := by
  simp only [hQ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']

private theorem domLE_of {ν m : Fin n → ℝ} (h : inCone (fun a => (a : ℕ)) (m - ν)) : DomLE ν m := by
  obtain ⟨c, hc, hQ⟩ := h
  refine ⟨fun k => ?_, ?_⟩
  · rw [← sub_nonneg, ← Finset.sum_sub_distrib]
    have hs := part_sum c (m - ν) hQ (univ.filter fun a : Fin n => (a : ℕ) < k)
    simp only [Pi.sub_apply] at hs
    rw [hs]
    refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => ?_
    by_cases h0 : c a b = 0
    · simp [h0]
    have hab : (a : ℕ) < b := hc a b h0
    refine mul_nonneg (Nat.cast_nonneg _) ?_
    simp only [mem_filter, mem_univ, true_and]
    split_ifs with h1 h2 h2
    · simp
    · simp
    · omega
    · simp
  · have hs := part_sum c (m - ν) hQ univ
    simp only [Pi.sub_apply, mem_univ, if_true, sub_self, mul_zero, Finset.sum_const_zero,
      Finset.sum_sub_distrib] at hs
    linarith

private theorem int_of (lam : Fin n → ℤ) {ν : Fin n → ℝ} (h : inCone (fun a => (a : ℕ)) (m0 lam - ν)) :
    ∃ z : Fin n → ℤ, ν = wtR z := by
  obtain ⟨c, -, hQ⟩ := h
  refine ⟨fun x => m0Z lam x - ∑ a, ∑ b, (c a b : ℤ) * ((if x = a then 1 else 0) - (if x = b then 1 else 0)), ?_⟩
  funext x
  have hx := hQ x
  simp only [Pi.sub_apply, m0] at hx
  simp only [wtR, m0Z]
  push_cast
  linarith

private theorem harm_of (lam : Fin n → ℤ) (hl : Antitone lam) {ν : Fin n → ℝ} (hν : Antitone ν)
    (h : inCone (fun a => (a : ℕ)) (m0 lam - ν)) (hd : LSq lam ≤ spinSq ν) : ν ∈ harmSet lam := by
  have hle := domLE_of h
  obtain ⟨z, rfl⟩ := int_of lam h
  have hz : Antitone z := fun a b hab => by
    have := hν hab
    simpa [wtR] using this
  rw [harmSet_eq]
  refine Finset.mem_image_of_mem _ (GlobalTheory.T.harmonic_of_norm_bound lam hl z hz hle
    (Tuple.sort fun a => -(wtR z - rhoV n) a) (((rearr n).2.1 (wtR z - rhoV n)).1) ?_)
  refine le_of_eq_of_le ?_ hd
  unfold LSq nsq m0 rhoV
  exact Finset.sum_congr rfl fun a _ => by ring

end UpperTheory.V.Z.GSp4Splitting.LowRankIsomorphism

open UpperTheory.RealTr UpperTheory.V.Z.GSp4Splitting.LowRankIsomorphism in
theorem UpperTheory.V.Z.GSp4Splitting.lowIso2 :
    LowIso := by
  intro n lam hl E T hT V _ _ E1 E2 σ A hc ⟨ν, hne, hcone⟩
  have hK : UF (kF E1 E2) := ⟨GlobalTheory.CompanionTheory.RealCount.KHw.glRel_kF hc.pair, hc.pair.unitK⟩
  have hL : LocF (kF E1 E2) := fun x => by
    obtain ⟨S, h1, h2, -, h3, -⟩ := hc.der.2 x
    exact ⟨S, h1, h2, h3⟩
  have hneK : hw (kF E1 E2) ν ≠ ⊥ := hne
  obtain ⟨-, -, hρ, -, hdom, -⟩ := rearr n
  have hD : Dom ν := (irrCh n V (kF E1 E2) hK hL ν hneK).1
  have hanti : Antitone ν := (hdom ν hD).1
  have hH : ν ∈ harmSet lam :=
    harm_of lam hl hanti hcone (diracW n lam V E1 E2 hc.pair hL hc.ch1 hc.ch2 ν hne)
  obtain ⟨E', e, T', σ', F, χ, s, he, -, hF, hder, -, -, -, hb⟩ := lefData n lam hl E T hT
  have hneF : hw F ν ≠ ⊥ := by
    intro h0
    have ht := (hb ν fun a b hab => add_lt_add_of_le_of_lt (hanti hab.le) (hρ hab)).1
    rw [← (harmDom n lam hl ν hH).2, aux₃ n ν hD, h0, trOn_bot, mul_one] at ht
    exact pow_ne_zero n two_ne_zero ht.symm
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hneF
  obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 hneK
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℂ
    (show (⟨x, hx⟩ : hw F ν) ≠ 0 from fun h => hx0 (congrArg Subtype.val h))
  obtain ⟨t, ht, htφ, -⟩ := homSurj n E'.V V F (kF E1 E2) hF hK hL ν (f.smulRight (⟨y, hy⟩ : hw (kF E1 E2) ν))
  have htx : t x = y := by
    have := htφ ⟨x, hx⟩
    simpa [hf] using this
  have hg := ((derAt n V σ (kF E1 E2) hc.der).2 E'.V σ' F hder t).2 ht
  have hu : t ∘ₗ e.toLinearMap ∈ invA σ E := fun k ξ => by
    show t (e (ξ ∘L E.ρ k⁻¹)) = σ k (t (e ξ))
    rw [he, hg]
  refine (Submodule.ne_bot_iff _).2 ⟨y, ?_, hy0⟩
  refine Submodule.mem_iSup_of_mem ⟨_, hu⟩ ⟨e.symm x, ?_⟩
  show t (e (e.symm x)) = y
  rw [e.apply_symm_apply, htx]
