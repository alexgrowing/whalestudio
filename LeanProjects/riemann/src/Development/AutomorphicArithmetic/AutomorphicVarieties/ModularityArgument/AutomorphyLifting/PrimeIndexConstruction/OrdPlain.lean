import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.PsOfForm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.PsCent
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.PsPlain
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.LocTransAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.DetCent
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HermitianTwists.CentChar

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.CuspRep
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Win.Birth

private theorem real_core (t L A B : ℝ) (m0 m1 s : ℤ) (ht0 : 0 < t) (ht1 : t < 1)
    (h1 : A * B * t ^ (s + 1) = 1) (h2 : L * t ^ m0 = 1) (h3 : L ^ 2 = t * A ^ 2)
    (h4 : A * t = B ∨ B * t = A) (h5 : m1 + 2 ≤ m0) (h6 : m0 + m1 = s) : False := by
  have hL : L ≠ 0 := by
    rintro rfl
    simp at h2
  have ht : t ≠ 0 := ht0.ne'
  have e0 : L ^ 2 * t ^ (2 * m0) = 1 := by
    have e : t ^ (2 * m0) = (t ^ m0) ^ 2 := by rw [two_mul, zpow_add₀ ht, sq]
    rw [e, ← mul_pow, h2, one_pow]
  have inj : ∀ a b : ℤ, L ^ 2 * t ^ a = 1 → L ^ 2 * t ^ b = 1 → a = b := by
    intro a b ha hb
    have e : t ^ a = t ^ b := mul_left_cancel₀ (pow_ne_zero 2 hL) (ha.trans hb.symm)
    exact zpow_right_injective₀ ht0 ht1.ne e
  rcases h4 with h4 | h4
  · subst h4
    have e : L ^ 2 * t ^ (s + 1) = 1 := by
      rw [h3]
      linear_combination h1
    have := inj _ _ e e0
    omega
  · subst h4
    have e1 : t ^ (s + 1) = t ^ (s - 1) * t ^ 2 := by
      rw [show s + 1 = (s - 1) + 2 by ring, zpow_add₀ ht]
      norm_cast
    have e : L ^ 2 * t ^ (s - 1) = 1 := by
      rw [e1] at h1
      rw [h3]
      linear_combination h1
    have := inj _ _ e e0
    omega

private theorem norm_q {F : Type} [Field F] [NumberField F] {l : ℕ} [hl : Fact l.Prime] (w : Pl F)
    (hw : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal) : 0 < ‖(normV w : Qbar l)‖ ∧ ‖(normV w : Qbar l)‖ < 1 := by
  have e : normV w = Ideal.absNorm w.asIdeal := rfl
  have h1 : 1 < normV w := NumberField.HeightOneSpectrum.one_lt_absNorm w
  have hd : l ∣ normV w := by
    have h2 : Ideal.absNorm w.asIdeal ∣ Ideal.absNorm (Ideal.span {((l : ℕ) : 𝓞 F)}) :=
      Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 hw)
    rw [Ideal.absNorm_span_natCast, ← e] at h2
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hl.out).1 h2
    rw [hk]
    refine dvd_pow_self l ?_
    rintro rfl
    simp [hk] at h1
  refine ⟨norm_pos_iff.2 (Nat.cast_ne_zero.2 (by omega)), ?_⟩
  rw [← map_natCast (algebraMap ℚ_[l] (Qbar l)), norm_algebraMap']
  exact_mod_cast Padic.norm_intCast_lt_one_iff.2 (Int.natCast_dvd_natCast.2 hd)

private theorem norm_of_near {K : Type} [NormedField K] [IsUltrametricDist K] {x a : K} (h : ‖x - a‖ < 1)
    (ha : ‖a‖ = 1) : ‖x‖ = 1 := by
  have e : x = (x - a) + a := by ring
  rw [e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [ha]; exact h.ne), ha]
  exact max_eq_right h.le

private theorem fin2 : ∀ i j : Fin 2, i ≠ j → (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by decide

theorem ordPlain : OrdPlain := by
  intro F Ω _ _ _ _ _ _ l _ ι ξ s c m a π r h v σ hσ
  obtain ⟨ω, hω, -⟩ := UpperTheory.V.Af.Rn.centChar F π
  by_cases hc : c v = 0
  · exact Or.inr ((locTrans F π v).1 (h.sph v hc))
  refine Or.inl ?_
  obtain ⟨hU, hcent⟩ := (locTrans F π v).2 σ hσ
  have hcent' := hcent ω hω
  obtain ⟨hN, hI⟩ := detCent F Ω l ι ξ s π r h.att h.det h.ξ_open ω hω v
  obtain ⟨A, hA⟩ := exists_isPlaceOver Ω v
  obtain ⟨x, hx⟩ : ∃ x : σ.V, x ≠ 0 := by
    obtain ⟨f, hf, -⟩ := hσ
    obtain ⟨y, hy⟩ := DFunLike.ne_iff.1 hf
    refine ⟨y, ?_⟩
    rintro rfl
    simp at hy
  have hq1 : 1 < normV v := NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hlam : ∃ lam : ℂ, HasU v (π.locRep v) (c v) lam ∧ lam ≠ 0 ∧ (((l : ℕ) : 𝓞 F) ∈ v.asIdeal →
      ‖ι.symm lam‖ * ‖(normV v : Qbar l)‖ ^ m v 0 = 1 ∧ m v 1 + 2 ≤ m v 0 ∧ m v 0 + m v 1 = s) := by
    by_cases hl : ((l : ℕ) : 𝓞 F) ∈ v.asIdeal
    · obtain ⟨hc1, h12, hs, ha, ⟨lam, hlU, hnear⟩, -⟩ := h.above v hl
      have e := norm_of_near hnear ha
      have hn : ‖ι.symm lam‖ * ‖(normV v : Qbar l)‖ ^ m v 0 = 1 := by
        rw [← norm_zpow, ← norm_mul]
        exact e
      refine ⟨lam, hc1 ▸ hlU, ?_, fun _ => ⟨hn, h12, hs⟩⟩
      rintro rfl
      simp at hn
    · obtain ⟨lam, hlU, hn⟩ := h.away v hc hl
      refine ⟨lam, hlU, ?_, fun h' => absurd h' hl⟩
      rintro rfl
      simp at hn
  obtain ⟨lam, hlU, hl0, hln⟩ := hlam
  obtain ⟨ψ, hsm, hsub, hun, hsq⟩ := uLoc F v (c v) lam σ hc hl0 ((hU _ _) hlU)
  have hprod : ∀ z, ψ 0 z * ψ 1 z = ω.loc v z := by
    intro z
    have e := (psCent F v σ ψ hsub z x).symm.trans (hcent' z x)
    exact Units.ext (smul_left_injective ℂ hx e)
  refine psPlain F v σ ψ hsm hsub ?_
  rintro i j ⟨hu, hq⟩
  by_cases hij : i = j
  · subst hij
    have h0 : ((ψ i (atFin v (unif v)) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
    have e : ((normV v : ℕ) : ℂ) = 1 := mul_left_cancel₀ h0 (by rw [hq, mul_one])
    have e' : normV v = 1 := by exact_mod_cast e
    omega
  have hu01 : ∀ y, IsUnitAt v y → ψ 1 y = 1 := by
    intro y hy
    rcases fin2 i j hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [← hu y hy, hun y hy]
    · rw [hu y hy, hun y hy]
  by_cases hl : ((l : ℕ) : 𝓞 F) ∈ v.asIdeal
  · obtain ⟨hn, h12, hs⟩ := hln hl
    obtain ⟨ht0, ht1⟩ := norm_q (l := l) v hl
    obtain ⟨N, hN0, hNe⟩ := hN
    have hnorm : ∀ z w : ℂ, ‖ι.symm (z * w)‖ = ‖ι.symm z‖ * ‖ι.symm w‖ := fun z w => by
      rw [map_mul, norm_mul]
    have hqn : ‖ι.symm ((normV v : ℕ) : ℂ)‖ = ‖(normV v : Qbar l)‖ := by rw [map_natCast]
    refine (real_core ‖(normV v : Qbar l)‖ ‖ι.symm lam‖ ‖ι.symm ((ψ 0 (atFin v (unif v)) : ℂˣ) : ℂ)‖
      ‖ι.symm ((ψ 1 (atFin v (unif v)) : ℂˣ) : ℂ)‖ (m v 0) (m v 1) s ht0 ht1 ?_ hn ?_ ?_ h12 hs).elim
    · have e := congrArg (fun z : ℂ => ‖ι.symm z‖) hNe
      simp only [map_pow, norm_pow, map_one, norm_one] at e
      have e2 := (pow_eq_one_iff_of_nonneg (norm_nonneg _) hN0.ne').1 e
      rw [hnorm, ← hprod, Units.val_mul, hnorm, map_zpow₀, norm_zpow, hqn] at e2
      exact e2
    · have e := congrArg (fun z : ℂ => ‖ι.symm z‖) hsq
      simp only [map_pow, norm_pow, map_mul, norm_mul, map_natCast] at e
      exact e
    · have e := congrArg (fun z : ℂ => ‖ι.symm z‖) hq
      simp only [hnorm, hqn] at e
      rcases fin2 i j hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl e
      · exact Or.inr e
  · have hram : Ine (F := F) A ≤ ξ.ker := hI A hA (fun y hy => by
      rw [← hprod, hun y hy, hu01 y hy, one_mul])
    rcases (h.ram v A hA).1 hram with h0 | h0
    · exact absurd h0 hc
    · exact absurd h0 hl

end UpperTheory.V.Z.Win.Birth
