import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.DiscrIdealSmulLeIff
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocFSpanConsBasis
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.SigmaCount

open NumberField Module Filter Topology

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.PinD

section One

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

omit [NumberField K] [NumberField F] in
theorem star_cK (hF : IsFixF K F) (c : F) : star (algebraMap F K c) = algebraMap F K c :=
  (hF _).2 ⟨c, rfl⟩

omit [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [NumberField K] in
theorem smul_form_apply (c : K) (h : V →ₗ⋆[K] V →ₗ[K] K) (x y : V) : (c • h) x y = c * h x y := by
  rfl

omit [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [NumberField K]
  [NumberField F] in
theorem isSymm_of_smul (hF : IsFixF K F) {c : F} (hc : algebraMap F K c ≠ 0)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : (algebraMap F K c • h).IsSymm) : h.IsSymm := by
  refine ⟨fun x y => ?_⟩
  have hxy := hs.eq x y
  rw [smul_form_apply, smul_form_apply, map_mul] at hxy
  have hst : (starRingEnd K) (algebraMap F K c) = algebraMap F K c := star_cK hF c
  rw [hst] at hxy
  exact mul_left_cancel₀ hc hxy

omit [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [NumberField F] in
theorem isTotPosDef_of_smul (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {c : F}
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef (algebraMap F K c • h)) {x₀ : V}
    (h1 : h x₀ x₀ = 1) : IsTotPosDef h := by
  have hx0 : x₀ ≠ 0 := by
    rintro rfl
    simp at h1
  intro x hx φ
  have hreal : ∀ a : K, star a = a → (φ a).im = 0 := by
    intro a ha
    have := hK.2.1 φ a
    rw [ha] at this
    exact Complex.conj_eq_iff_im.1 this.symm
  have hc0 := hd x₀ hx0 φ
  rw [smul_form_apply, h1, mul_one] at hc0
  have hcx := hd x hx φ
  rw [smul_form_apply, map_mul] at hcx
  have hcr : (φ (algebraMap F K c)).im = 0 := hreal _ (star_cK hF c)
  rw [Complex.mul_re, hcr, zero_mul, sub_zero] at hcx
  exact pos_of_mul_pos_right hcx hc0.le

theorem alphaL_eq_of_le (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {k : ℕ} (hk : 2 * vd h L 𝔭 + 2 ≤ k) :
    alphaL h L 𝔭 = (akCount h L 𝔭 k : ℝ) / (Ideal.absNorm 𝔭 : ℝ) ^ (k * finrank K V ^ 2) := by
  exact firstFamilyOperatorEnd.alphaL_eq hK hF hs hd hL hLi h𝔭 (by omega)

theorem alphaL_smul (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {c : 𝓞 F} (hc : c ≠ 0) (hs' : (algebraMap F K (c : F) • h).IsSymm)
    (hd' : IsTotPosDef (algebraMap F K (c : F) • h)) :
    alphaL (algebraMap F K (c : F) • h) L 𝔭 =
      (Ideal.absNorm 𝔭 : ℝ) ^ (vF 𝔭 c * finrank K V ^ 2) * alphaL h L 𝔭 := by
  have hN : (Ideal.absNorm 𝔭 : ℝ) ≠ 0 := by
    rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
    exact Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (NumberField.RingOfIntegers.not_isField F)
  have key : ∀ k, 2 * vd h L 𝔭 + 1 + vF 𝔭 c ≤ k →
      (akCount (algebraMap F K (c : F) • h) L 𝔭 k : ℝ) / (Ideal.absNorm 𝔭 : ℝ) ^ (k * finrank K V ^ 2) =
        (Ideal.absNorm 𝔭 : ℝ) ^ (vF 𝔭 c * finrank K V ^ 2) * alphaL h L 𝔭 := by
    intro k hk
    obtain ⟨m, rfl⟩ : ∃ m, k = m + vF 𝔭 c := ⟨k - vF 𝔭 c, by omega⟩
    rw [PinA.akCount_smul hK hF hs hd hL hLi h𝔭 hc (k := m + vF 𝔭 c) (by omega), Nat.add_sub_cancel,
      firstFamilyOperatorEnd.alphaL_eq hK hF hs hd hL hLi h𝔭 (k := m) (by omega)]
    push_cast
    rw [show (m + vF 𝔭 c) * finrank K V ^ 2 = m * finrank K V ^ 2 + vF 𝔭 c * finrank K V ^ 2 by ring,
      show 2 * vF 𝔭 c * finrank K V ^ 2 = vF 𝔭 c * finrank K V ^ 2 + vF 𝔭 c * finrank K V ^ 2 by ring,
      pow_add, pow_add]
    field_simp <;> ring
  exact (tendsto_const_nhds.congr'
    (Filter.eventually_atTop.2 ⟨_, fun k hk => (key k hk).symm⟩)).limUnder_eq

theorem alphaN_smul (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {c : 𝓞 F} (hc : c ≠ 0) (hs' : (algebraMap F K (c : F) • h).IsSymm)
    (hd' : IsTotPosDef (algebraMap F K (c : F) • h)) (hm : 1 ≤ finrank K V) {n : 𝓞 F} (hn : n ≠ 0) :
    alphaN (algebraMap F K (c : F) • h) L 𝔭 (c * n) =
      (Ideal.absNorm 𝔭 : ℝ) ^ vF 𝔭 c * alphaN h L 𝔭 n := by
  have hN : (Ideal.absNorm 𝔭 : ℝ) ≠ 0 := by
    rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
    exact Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (NumberField.RingOfIntegers.not_isField F)
  have key : ∀ k, 2 * vd h L 𝔭 + 2 * vF 𝔭 n + 2 + vF 𝔭 c ≤ k →
      (nkCount (algebraMap F K (c : F) • h) L 𝔭 k (c * n) : ℝ) /
          (Ideal.absNorm 𝔭 : ℝ) ^ (k * (2 * finrank K V - 1)) =
        (Ideal.absNorm 𝔭 : ℝ) ^ vF 𝔭 c * alphaN h L 𝔭 n := by
    intro k hk
    obtain ⟨m, rfl⟩ : ∃ m, k = m + vF 𝔭 c := ⟨k - vF 𝔭 c, by omega⟩
    rw [PinA.nkCount_smul hK hF hs hd hL hLi h𝔭 hc n (k := m + vF 𝔭 c) (by omega), Nat.add_sub_cancel,
      alphaN_eq_of_le hK hF hs hd hL hLi h𝔭 hn (k := m) (by omega)]
    push_cast
    have h2 : 2 * vF 𝔭 c * finrank K V = vF 𝔭 c * (2 * finrank K V - 1) + vF 𝔭 c := by
      have h3 : 2 * finrank K V = (2 * finrank K V - 1) + 1 := by omega
      calc 2 * vF 𝔭 c * finrank K V = vF 𝔭 c * (2 * finrank K V) := by ring
        _ = vF 𝔭 c * ((2 * finrank K V - 1) + 1) := by rw [← h3]
        _ = _ := by ring
    rw [h2, show (m + vF 𝔭 c) * (2 * finrank K V - 1) =
        m * (2 * finrank K V - 1) + vF 𝔭 c * (2 * finrank K V - 1) by ring, pow_add, pow_add]
    field_simp <;> ring
  exact (tendsto_const_nhds.congr'
    (Filter.eventually_atTop.2 ⟨_, fun k hk => (key k hk).symm⟩)).limUnder_eq

end One

section Two

variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

omit [NumberField K] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem isom_smul {c : K} (hc : c ≠ 0) (h : V →ₗ⋆[K] V →ₗ[K] K) :
    Formalism.HermitianLatticesTheory.isom (c • h) = Formalism.HermitianLatticesTheory.isom h := by
  ext g
  show (∀ x y, (c • h) (g x) (g y) = (c • h) x y) ↔ ∀ x y, h (g x) (g y) = h x y
  simp only [smul_form_apply, mul_right_inj' hc]

def unscale {c : K} (hc : c ≠ 0) (S : VecSplit (c • h) (c • h')) : VecSplit h h' where
  x₀ := S.x₀
  ι := S.ι
  inj := S.inj
  hx₀ := fun e => S.hx₀ (by rw [smul_form_apply, e, mul_zero])
  isom := fun a b => by
    have := S.isom a b
    rw [smul_form_apply, smul_form_apply] at this
    exact mul_left_cancel₀ hc this
  orth := fun a => by
    have := S.orth a
    rw [smul_form_apply] at this
    exact (mul_eq_zero.1 this).resolve_left hc
  cover := S.cover

omit [FiniteDimensional K V] [FiniteDimensional K V'] in
theorem fibLoc_unscale {c : K} (hc : c ≠ 0) (S : VecSplit (c • h) (c • h')) (L : Submodule (𝓞 K) V)
    (𝔭 : Ideal (𝓞 F)) (T : Submodule (𝓞 K) V') :
    fibLoc S L 𝔭 T = fibLoc (unscale hc S) L 𝔭 T := by
  simp only [fibLoc, isom_smul hc]
  rfl

theorem isLocReps_scale (hF : IsFixF K F) {c : 𝓞 F} (hc : algebraMap F K (c : F) ≠ 0)
    (S : VecSplit (algebraMap F K (c : F) • h) (algebraMap F K (c : F) • h'))
    {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {s : Finset (Submodule (𝓞 K) V')}
    (hr : IsLocReps (unscale hc S) L 𝔭 s) : IsLocReps S L 𝔭 s := by
  have hLi' := PinA.isIntegralLat_smul hLi c
  have hiso : Formalism.HermitianLatticesTheory.isom (algebraMap F K (c : F) • h') = Formalism.HermitianLatticesTheory.isom h' := isom_smul hc h'
  refine ⟨fun T hT => ?_, fun T hTl hTi hTf => ?_⟩
  · obtain ⟨h1, -, h3⟩ := hr.1 T hT
    rw [← fibLoc_unscale] at h3
    obtain ⟨C, -, hCi, hC⟩ := UnimodularLocalization.exists_lattice_of_fibLoc_ne_zero S hL hLi' h3
    refine ⟨h1, ?_, h3⟩
    have := GoodPrimeTerms.isIntegralAt_locF h𝔭.isPrime hF hCi
    rwa [hC, h1] at this
  · rw [fibLoc_unscale hc] at hTf
    obtain ⟨C, -, hCi, hC⟩ := UnimodularLocalization.exists_lattice_of_fibLoc_ne_zero (unscale hc S) hL hLi hTf
    have hTi' : IsIntegralAt 𝔭 h' T := by
      have := GoodPrimeTerms.isIntegralAt_locF h𝔭.isPrime hF hCi
      rwa [hC, hTl] at this
    rw [hiso]
    exact hr.2 T hTl hTi' hTf

theorem alphaL_split (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') (h1 : h S.x₀ S.x₀ = 1) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hx : S.x₀ ∈ L)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (hv : vd h L 𝔭 ≤ 1) :
    alphaL h L 𝔭 = alphaN h L 𝔭 1 * alphaL h' (S.cut L) 𝔭 := by
  have hN : (Ideal.absNorm 𝔭 : ℝ) ≠ 0 := by
    rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
    exact Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (NumberField.RingOfIntegers.not_isField F)
  have hdim := S.finrank_add_one
  have hA := alphaL_pos hK hF hs hd hL hLi h𝔭
  have h1𝔭 : (1 : 𝓞 F) ∉ 𝔭 ^ (0 + 1) := by
    rw [zero_add, pow_one]; exact (Ideal.ne_top_iff_one 𝔭).1 h𝔭.ne_top
  have key : ∀ k, 2 * vd h L 𝔭 + 2 ≤ k → alphaN h L 𝔭 1 ≠ 0 ∧
      (akCount h' (S.cut L) 𝔭 k : ℝ) / (Ideal.absNorm 𝔭 : ℝ) ^ (k * finrank K V' ^ 2) =
        alphaL h L 𝔭 / alphaN h L 𝔭 1 := by
    intro k hk
    have eA := firstFamilyOperatorEnd.alphaL_eq hK hF hs hd hL hLi h𝔭 (k := k) (by omega)
    have eB := firstFamilyOperatorEnd.alphaN_eq hK hF hs hd hL hLi h𝔭 h1𝔭 (k := k) (by omega)
    have eS := PinB.akCount_split hK hF hs hd S h1 hL hLi hx h𝔭 hv (k := k) (by omega)
    rw [eS, Nat.cast_mul] at eA
    have hnk : (nkCount h L 𝔭 k 1 : ℝ) ≠ 0 := by
      intro h0
      rw [h0, zero_mul, zero_div] at eA
      linarith
    have hB : alphaN h L 𝔭 1 ≠ 0 := by
      rw [eB]; exact div_ne_zero hnk (pow_ne_zero _ hN)
    refine ⟨hB, ?_⟩
    rw [eA, eB, ← hdim]
    have e1 : k * (finrank K V' + 1) ^ 2 =
        k * (2 * (finrank K V' + 1) - 1) + k * finrank K V' ^ 2 := by
      have : 2 * (finrank K V' + 1) - 1 = 2 * finrank K V' + 1 := by omega
      rw [this]; ring
    rw [e1, pow_add]
    field_simp <;> ring
  obtain ⟨hB, -⟩ := key _ le_rfl
  have hl : alphaL h' (S.cut L) 𝔭 = alphaL h L 𝔭 / alphaN h L 𝔭 1 :=
    (tendsto_const_nhds.congr'
      (Filter.eventually_atTop.2 ⟨_, fun k hk => ((key k hk).2).symm⟩)).limUnder_eq
  rw [hl]
  field_simp

end Two

end Formalism.HermitianLattices.Ext.L3.PinD
