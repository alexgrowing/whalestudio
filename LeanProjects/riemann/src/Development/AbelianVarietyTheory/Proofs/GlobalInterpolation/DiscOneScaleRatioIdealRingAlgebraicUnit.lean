import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Formalism.LocalToGlobal.PairingIndexBounds.HalvesRecursion.RecursiveLatticeMembership.MemLamOfIff
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsGoodReductionAlgebraicWeierstrassModel
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsRingEquivApplyEqMulOfTranscendental
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormDiscriminantSuperlatticeOddIndexEqStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CmBaseFieldIntegersAndCurveIdealFactsStatement

noncomputable section

namespace GlobalTheory.MomDelta

section Scale

open GlobalTheory.MomOne

def scalePair (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) : PeriodPair :=
  ⟨c * L.ω₁, c * L.ω₂, LinearIndependent.pair_iff.2 fun s t h => by
    have h' : s • L.ω₁ + t • L.ω₂ = 0 := by
      apply mul_left_cancel₀ hc
      simp only [Complex.real_smul] at h ⊢
      linear_combination h
    exact LinearIndependent.pair_iff.1 L.indep s t h'⟩

theorem mem_scalePair (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) (z : ℂ) :
    c * z ∈ (scalePair L c hc).lattice ↔ z ∈ L.lattice := by
  rw [PeriodPair.mem_lattice, PeriodPair.mem_lattice]
  constructor
  · rintro ⟨m, n, h⟩
    refine ⟨m, n, mul_left_cancel₀ hc ?_⟩
    simp only [scalePair] at h
    linear_combination h
  · rintro ⟨m, n, rfl⟩
    exact ⟨m, n, by simp only [scalePair]; ring⟩

theorem G_scale (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) (k : ℕ) :
    L.G k = c ^ k * (scalePair L c hc).G k := by
  let e : (L.lattice : Set ℂ) ≃ ((scalePair L c hc).lattice : Set ℂ) :=
    (Equiv.mulLeft₀ c hc).subtypeEquiv fun w => by
      simpa using (mem_scalePair L c hc w).symm
  have h2 : ∀ P : PeriodPair, P.G k = ∑' w : (P.lattice : Set ℂ), ((w : ℂ) ^ k)⁻¹ := fun _ => rfl
  rw [h2, h2, ← e.tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun w => ?_
  have : ((e w : ((scalePair L c hc).lattice : Set ℂ)) : ℂ) = c * w := rfl
  rw [this, mul_pow, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hc), one_mul]

theorem g₂_scale (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) : (scalePair L c hc).g₂ = L.g₂ / c ^ 4 := by
  simp only [PeriodPair.g₂, G_scale L c hc 4]
  field_simp

theorem g₃_scale (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) : (scalePair L c hc).g₃ = L.g₃ / c ^ 6 := by
  simp only [PeriodPair.g₃, G_scale L c hc 6]
  field_simp

variable {q : ℕ} [Fact q.Prime]

theorem ok_scale (M : Mdl q) (hM : M.Ok) (c : ℂ) (hc : c ≠ 0) :
    (Mdl.mk M.ι (scalePair M.L c hc) (M.c / c) M.W).Ok := by
  obtain ⟨h0, h1, h2, h3, h4, h6, hΔ, hg2, hg3⟩ := hM
  refine ⟨div_ne_zero h0 hc, h1, h2, h3, h4, h6, hΔ, ?_, ?_⟩
  · have : (scalePair M.L c hc).g₂ / (M.c / c) ^ 4 = M.L.g₂ / M.c ^ 4 := by
      rw [g₂_scale]; field_simp
    show M.W.c₄ / 12 = M.ι _
    rw [this]; exact hg2
  · have : (scalePair M.L c hc).g₃ / (M.c / c) ^ 6 = M.L.g₃ / M.c ^ 6 := by
      rw [g₃_scale]; field_simp
    show M.W.c₆ / 216 = M.ι _
    rw [this]; exact hg3

theorem norm_disc_ring (ι : ℂ ≃+* ℂ_[q]) {d : ℕ} (hd : d.Prime) (h16 : d % 16 = 7) (L' : PeriodPair) (N : ℕ)
    (hq : q ≠ 2) (hN : Nat.Coprime N (2 * q)) (hN0 : N ≠ 0)
    (h1 : ∀ z, InOK d z → (N : ℂ) * z ∈ L'.lattice) (h2 : ∀ x ∈ L'.lattice, InOK d x) :
    ‖ι (L'.g₂ ^ 3 - 27 * L'.g₃ ^ 2)‖ = ‖ι (discr d)‖ := by
  have hc : (N : ℂ) ≠ 0 := by exact_mod_cast hN0
  have hL := Basic.isOK_okPair d hd.pos
  obtain ⟨M, hMι, hML, hOk, -⟩ := exists_model d q ι _ hd h16 hL
  have hIs : IsOK d M.L := hML ▸ hL
  subst hMι
  have hk := GlobalTheory.T.norm_discriminant_superlattice_odd_index_eq q (Mdl.mk M.ι (scalePair M.L N hc) (M.c / N) M.W) L' N hq (ok_scale M hOk N hc) hN
    (fun z hz => by
      have e : z = (N : ℂ) * (z / N) := by field_simp
      have hz' : (N : ℂ) * (z / N) ∈ (scalePair M.L N hc).lattice := by rw [← e]; exact hz
      rw [e]
      exact h1 _ ((hIs _).1 ((mem_scalePair M.L N hc _).1 hz')))
    (fun x hx => (mem_scalePair M.L N hc x).2 ((hIs x).2 (h2 x hx)))
  have e : (scalePair M.L N hc).g₂ ^ 3 - 27 * (scalePair M.L N hc).g₃ ^ 2
      = (M.L.g₂ ^ 3 - 27 * M.L.g₃ ^ 2) / (N : ℂ) ^ 12 := by
    rw [g₂_scale, g₃_scale]; field_simp
  have hnorm : ‖M.ι (N : ℂ)‖ = 1 := by
    rw [map_natCast]
    exact Basic.norm_nat_eq_one (Nat.Coprime.symm (Nat.coprime_mul_iff_right.1 hN).2)
  refine hk.trans ?_
  show ‖M.ι ((scalePair M.L N hc).g₂ ^ 3 - 27 * (scalePair M.L N hc).g₃ ^ 2)‖ = _
  rw [e, map_div₀, norm_div, map_pow, norm_pow, hnorm, one_pow, div_one, (Basic.discr_eq hIs).1]

end Scale

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

theorem delta_ratio : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ δ₀ : ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    δ₀ ^ 12 = GlobalTheory.MomOne.discr D.host.d → ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → Nat.Coprime (Ideal.absNorm cc) q →
    δ / δ₀ ∈ Qbar ∧ ∀ ι : ℂ ≃+* ℂ_[q], ‖ι (δ / δ₀)‖ = 1 := by
  intro D cc δ δ₀ hcc hδ hδ₀ q _ hq hNq
  obtain ⟨hdp, h16, hOK, -, hlam⟩ := GlobalTheory.T.cmBaseField_integers_and_curveIdeal_facts D
  obtain ⟨hne, hcop⟩ := hcc
  have hN0 : Ideal.absNorm cc ≠ 0 := fun h => hne (Ideal.absNorm_eq_zero_iff.1 h)
  have hN2 : Nat.Coprime (Ideal.absNorm cc) (2 * q) :=
    Nat.coprime_mul_iff_right.2 ⟨(Nat.coprime_mul_iff_right.1 hcop).1, hNq⟩
  obtain ⟨L', hL'⟩ := Formalism.L2.PairingIndexBounds.Rec.exists_pp D cc hne
  have hmem : ((Ideal.absNorm cc : ℕ) : 𝓞 D.host.K) ∈ cc := Ideal.absNorm_mem cc
  have hΔ : Formalism.MainNotions.TaylorLogMetric.discr (Formalism.MainNotions.TaylorLogMetric.lamOf D cc 1) = L'.g₂ ^ 3 - 27 * L'.g₃ ^ 2 := by
    have h4 := Formalism.L2.PairingIndexBounds.Rec.eisG_eq_G _ L' hL' 2 (by norm_num)
    have h6 := Formalism.L2.PairingIndexBounds.Rec.eisG_eq_G _ L' hL' 3 (by norm_num)
    unfold Formalism.MainNotions.TaylorLogMetric.discr Formalism.MainNotions.TaylorLogMetric.g2 Formalism.MainNotions.TaylorLogMetric.g3
    rw [h4, h6]
    simp [PeriodPair.g₂, PeriodPair.g₃]
  have h1 : ∀ z, GlobalTheory.MomOne.InOK D.host.d z → ((Ideal.absNorm cc : ℕ) : ℂ) * z ∈ L'.lattice := by
    intro z hz
    obtain ⟨x, rfl⟩ := (hOK z).1 hz
    refine (hL' _).1 ((hlam cc 1 hne).2 _ |>.2 ⟨((Ideal.absNorm cc : ℕ) : 𝓞 D.host.K) * x, cc.mul_mem_right x hmem, ?_⟩)
    simp
  have h2 : ∀ x ∈ L'.lattice, GlobalTheory.MomOne.InOK D.host.d x := by
    intro x hx
    obtain ⟨c, -, rfl⟩ := ((hlam cc 1 hne).2 x).1 ((hL' x).2 hx)
    exact (hOK _).2 ⟨c, by simp⟩
  have hne₀ : GlobalTheory.MomOne.discr D.host.d ≠ 0 :=
    (GlobalTheory.MomOne.Basic.discr_eq (GlobalTheory.MomOne.Basic.isOK_okPair _ hdp.pos)).2
  have hδ₀0 : δ₀ ≠ 0 := by
    rintro rfl
    exact hne₀ (by rw [← hδ₀]; simp)
  have key : ∀ ι : ℂ ≃+* ℂ_[q], ‖ι (δ / δ₀)‖ = 1 := by
    intro ι
    have h := norm_disc_ring ι hdp h16 L' _ hq hN2 hN0 h1 h2
    have hδ' : δ ^ 12 = L'.g₂ ^ 3 - 27 * L'.g₃ ^ 2 := by rw [← hΔ]; exact hδ
    rw [← hδ', ← hδ₀, map_pow, map_pow, norm_pow, norm_pow] at h
    have hι₀ : ‖ι δ₀‖ ≠ 0 := by simpa using hδ₀0
    have h12 : ‖ι (δ / δ₀)‖ ^ 12 = 1 := by
      rw [map_div₀, norm_div, div_pow, h, div_self (pow_ne_zero _ hι₀)]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h12
  obtain ⟨ι⟩ := GlobalTheory.MomOne.Basic.nonempty_iso q
  exact ⟨GlobalTheory.MomOne.mem_algebraicClosure_of_norm_le q ι _ 1 fun ι' _ => (key ι').le, key⟩

end GlobalTheory.MomDelta
