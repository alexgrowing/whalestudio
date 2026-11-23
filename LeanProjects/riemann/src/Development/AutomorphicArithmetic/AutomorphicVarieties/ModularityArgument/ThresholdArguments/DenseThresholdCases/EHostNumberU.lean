import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.LogarithmicNormBounds.HostNumberU
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.NumberU3US
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.HostNumberS
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ThmS6CoreS
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfBridge
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.EHostUnl
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.AutNewformW
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.IsAutCsdA

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
open NumberField Matrix IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.Aut UpperTheory.V.UnitaryThreeInertia
open IsDedekindDomain
open UpperTheory.V.Af in
private def NB (K : Type) [Field K] [NumberField K] [IsCMField K] (c A : ℕ) : Prop :=
    ∀ e : ℕ, 1 ≤ e → ∀ N : ℕ, 1 ≤ N → ∀ (p : ℕ) (w : HeightOneSpectrum (𝓞 K)), p.Prime → (p : 𝓞 K) ∈ w.asIdeal → 7 ≤ p →
      ¬ p ∣ N → ¬ (p : ℤ) ∣ discr K →
    ∀ (Orb : Type) [Fintype Orb] (z : Orb → ℂ), (∀ o, ∃ k : ℕ, 0 < k ∧ z o ^ k = 1) →
      (∀ σ : ℂ ≃+* ℂ, ∃ u : Orb ≃ Orb, ∀ o, z (u o) = σ (z o)) →
    ∃ NN : ℤ, NN ≠ 0 ∧ Real.log |(NN : ℝ)| ≤ c * Fintype.card Orb * ((N : ℝ) * (e + 1)) ^ A * Real.log p ∧
      ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → l ≠ p → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [Algebra K Ω] [IsScalarTower ℚ K Ω]
        [IsAlgClosure K Ω] (ι : Qbar l ≃+* ℂ) (B : ValuationSubring Ω), IsPlaceOver B w →
        ∀ σ : Formalism.ConjugateSelfDual.G K Ω, IsFrob B (normV w) σ →
        ∀ X : Orb → Finset (Formalism.ConjugateSelfDual.G K Ω →* GL (Fin 3) (Qbar l)),
          (∀ o, ∀ ρ ∈ X o, _root_.UpperTheory.V.Z.J.Adm3U_s ι e N ρ ∨ _root_.UpperTheory.V.Z.Win.Dn.Adm2A ι e (N * (discr K).natAbs) ρ) →
          (∀ o, ∀ ρ ∈ X o, ∀ ρ' ∈ X o, RepIso ρ ρ' → ρ = ρ') →
          (∀ o, ∀ ρ ∈ X o, (ρ σ⁻¹ : Matrix (Fin 3) (Fin 3) (Qbar l)).trace ≠ ι.symm (eis3 (normV w) e (z o))) ∧
          ‖((NN : ℤ) : Qbar l)‖ ≤
            ∏ o, ∏ ρ ∈ X o, ‖(ρ σ⁻¹ : Matrix (Fin 3) (Fin 3) (Qbar l)).trace - ι.symm (eis3 (normV w) e (z o))‖
private theorem isFrob_res {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra ℚ Ω] [Algebra K Ω]
    [IsScalarTower ℚ K Ω] (B : ValuationSubring Ω) (q : ℕ) (σ : Formalism.ConjugateSelfDual.G K Ω) :
    IsFrob (F := ℚ) B q (σ.restrictScalars ℚ) ↔ IsFrob B q σ := Iff.rfl
private theorem exists_p (m : ℕ) (hm : 0 < m) : ∃ p : ℕ, p.Prime ∧ p % 4 = 3 ∧ 7 ≤ p ∧ ¬ p ∣ m ∧ p ≤ 12 * m := by
  have h : ∃ p : ℕ, p.Prime ∧ p ∣ 12 * m - 1 ∧ p % 4 = 3 := by
    have h3 : (12 * m - 1) % 4 = 3 := by omega
    generalize 12 * m - 1 = n at h3
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      have hn1 : n ≠ 1 := by omega
      obtain ⟨k, hk⟩ := Nat.minFac_dvd n
      have hp := Nat.minFac_prime hn1
      by_cases h : n.minFac % 4 = 3
      · exact ⟨_, hp, Nat.minFac_dvd n, h⟩
      · have hk3 : k % 4 = 3 := by
          have h1 : n % 4 = (n.minFac % 4) * (k % 4) % 4 := by rw [← Nat.mul_mod, ← hk]
          have : n.minFac % 4 < 4 := Nat.mod_lt _ (by norm_num)
          have : k % 4 < 4 := Nat.mod_lt _ (by norm_num)
          generalize n.minFac % 4 = a at *
          generalize k % 4 = b at *
          interval_cases a <;> interval_cases b <;> omega
        have hlt : k < n := by
          have := hp.two_le
          have hk0 : 0 < k := by omega
          nlinarith
        obtain ⟨p, h1, h2, h4⟩ := ih k hlt hk3
        exact ⟨p, h1, h2.trans (Dvd.intro_left _ hk.symm), h4⟩
  obtain ⟨p, hp, hd, h4⟩ := h
  have hle := Nat.le_of_dvd (by omega) hd
  have hn : ¬ p ∣ 12 * m := fun h => by
    have : p ∣ 12 * m - (12 * m - 1) := Nat.dvd_sub h hd
    rw [show 12 * m - (12 * m - 1) = 1 by omega] at this
    exact hp.one_lt.ne' (Nat.dvd_one.1 this)
  refine ⟨p, hp, h4, ?_, fun h => hn (h.mul_left _), by omega⟩
  have : p ≠ 3 := by
    rintro rfl
    exact hn (Dvd.dvd.mul_right (by norm_num) _)
  omega
private theorem normV_inert {K : Type} [Field K] [NumberField K] (hK : IsQi K) {p : ℕ} (hp : p.Prime) (h4 : p % 4 = 3)
    (w : HeightOneSpectrum (𝓞 K)) (hw : (p : 𝓞 K) ∈ w.asIdeal) : normV w = p ^ 2 := by
  have h : normV w = Ideal.absNorm w.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
  have hd : Ideal.absNorm w.asIdeal ∣ p ^ 2 := by
    have := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 hw)
    rwa [Ideal.absNorm_span_natCast, NumberField.RingOfIntegers.rank, hK.1] at this
  obtain ⟨j, hj, e⟩ := (Nat.dvd_prime_pow hp).1 hd
  rw [h, e]
  interval_cases j
  · exact absurd (Ideal.absNorm_eq_one_iff.1 (by simpa using e)) w.isPrime.ne_top
  · exfalso
    obtain ⟨i, hi⟩ := hK.2
    have hint : IsIntegral ℤ i := ⟨Polynomial.X ^ 2 + 1, by monicity!, by simp [sq, hi]⟩
    let i' : 𝓞 K := ⟨i, hint⟩
    have hi' : i' * i' = -1 := RingOfIntegers.ext (by rw [RingOfIntegers.coe_eq_algebraMap, RingOfIntegers.coe_eq_algebraMap, map_mul, map_neg, map_one]; exact hi)
    haveI := w.isMaximal
    letI := Ideal.Quotient.field w.asIdeal
    haveI : Finite (𝓞 K ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
    letI := Fintype.ofFinite (𝓞 K ⧸ w.asIdeal)
    have hs : IsSquare (-1 : 𝓞 K ⧸ w.asIdeal) := ⟨Ideal.Quotient.mk _ i', by rw [← map_mul, hi']; simp⟩
    rw [FiniteField.isSquare_neg_one_iff] at hs
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card, pow_one] at e
    exact hs (e ▸ h4)
  · rfl
private theorem log_le_of_norm {l : ℕ} [Fact l.Prime] {n : ℤ} (hn : n ≠ 0) :
    -Real.log ‖((n : ℤ) : PadicAlgCl l)‖ ≤ Real.log |(n : ℝ)| := by
  have e : ‖((n : ℤ) : PadicAlgCl l)‖ = ‖((n : ℤ) : ℚ_[l])‖ := by
    rw [← PadicAlgCl.norm_extends, map_intCast]
  have h1 : (1 : ℝ) ≤ |(n : ℝ)| * ‖((n : ℤ) : ℚ_[l])‖ := by
    have hq : ((n : ℤ) : ℚ_[l]) ≠ 0 := by exact_mod_cast hn
    rw [Padic.norm_eq_zpow_neg_valuation hq, Padic.valuation_intCast, _root_.zpow_neg, _root_.zpow_natCast,
      le_mul_inv_iff₀ (by have := (Fact.out : l.Prime).pos; positivity), one_mul]
    have := Int.le_of_dvd (abs_pos.2 hn) ((dvd_abs _ _).2 (padicValInt_dvd (p := l) n))
    exact_mod_cast this
  have hp : 0 < ‖((n : ℤ) : ℚ_[l])‖ := norm_pos_iff.2 (by exact_mod_cast hn)
  have := Real.log_nonneg h1
  rw [Real.log_mul (abs_ne_zero.2 (by exact_mod_cast hn)) hp.ne'] at this
  rw [e]
  linarith
private theorem totDisc_quot {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G)) :
    TotallyDisconnectedSpace (G ⧸ N) := by
  rw [totallyDisconnectedSpace_iff_connectedComponent_one]
  refine Set.eq_singleton_iff_unique_mem.2 ⟨mem_connectedComponent, fun y hy => ?_⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  by_contra hx
  have hx' : x ∉ N := fun h => hx ((QuotientGroup.eq_one_iff x).2 h)
  have ho : IsOpen {g : G | g * x ∉ N} := hN.isOpen_compl.preimage (continuous_mul_const x)
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one ho (by simpa using hx')
  let V : Subgroup (G ⧸ N) := U.toSubgroup.map (QuotientGroup.mk' N)
  have hVo : IsOpen (V : Set (G ⧸ N)) := QuotientGroup.isOpenMap_coe _ U.isOpen'
  have hV : IsClopen (V : Set (G ⧸ N)) := ⟨V.isClosed_of_isOpen hVo, hVo⟩
  obtain ⟨u, hu, hux⟩ := hV.connectedComponent_subset V.one_mem hy
  exact hU (U.toSubgroup.inv_mem hu) (QuotientGroup.eq.1 hux)
section Host
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N]
  {e : ℕ} {ψ : DirichletCharacter c.O N} {o₁ : ℕ} {S : Finset Pl} {A : S → ValuationSubring Ω}
  {F : Frame c.O (Formalism.ConjugateSelfDual.G ℚ Ω) (Gam Ω S) S}
private theorem algClosure (K Ω : Type) [Field K] [NumberField K] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra K Ω]
    [IsScalarTower ℚ K Ω] : IsAlgClosure K Ω :=
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩
private theorem cont_pt (hd : HostData l e ψ o₁) (hF : IsHostFrame Ω c e ψ S A F) {g₁ : Gam Ω S} (hg : F.Marked g₁)
    {r : Gam Ω S →* GG 3 (PadicAlgCl l)} (hr : F.IsCharZeroPt g₁ r) : Continuous (mats r) := by
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  haveI hcl := isClosed_NS Ω (S : Set Pl)
  haveI : CompactSpace (Gam Ω S) := inferInstance
  haveI : TotallyDisconnectedSpace (Gam Ω S) := totDisc_quot _ hcl
  exact (isCharZeroPt_basic F (hostFrame_ok Ω c e ψ o₁ hd S A F hF) g₁ hg r hr).2.2.1
private theorem trace_rz (hF : IsHostFrame Ω c e ψ S A F) (ι : Qbar l ≃+* ℂ) {σ : Formalism.ConjugateSelfDual.G ℚ Ω} {q : ℕ}
    (hσ : ((cycZ ℚ Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) = q) :
    (F.rz (PadicAlgCl l) (toGS Ω _ σ⁻¹)).mat.trace =
      ι.symm (UpperTheory.V.Af.eis3 q e (ι (((UpperTheory.V.Chr.dirG ℚ Ω ψ σ⁻¹ : c.Oˣ) : c.O) : PadicAlgCl l))) := by
  let f : c.Oˣ →* (PadicAlgCl l)ˣ := Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom
  have h1 : F.Ψ (toGS Ω _ σ⁻¹) = (UpperTheory.V.Base.chiO ℚ Ω l c.O σ ^ e)⁻¹ * UpperTheory.V.Chr.dirG ℚ Ω ψ σ⁻¹ := by
    have := DFunLike.congr_fun hF.Ψ σ⁻¹
    rw [MonoidHom.comp_apply, hF.π] at this
    rw [this, UpperTheory.V.Chr.Psi, MonoidHom.mul_apply, _root_.zpow_natCast, MonoidHom.pow_apply, map_inv, inv_pow]
  have h2 : ((f (UpperTheory.V.Base.chiO ℚ Ω l c.O σ) : (PadicAlgCl l)ˣ) : PadicAlgCl l) = q := by
    show algebraMap c.O (PadicAlgCl l) (algebraMap ℤ_[l] c.O ((cycZ ℚ Ω l σ : ℤ_[l]ˣ) : ℤ_[l])) = q
    rw [hσ, map_natCast, map_natCast]
  have h3 : ∀ t : c.Oˣ, ((tor c.O t : Matrix (Fin 3) (Fin 3) c.O).map (algebraMap c.O (PadicAlgCl l))).trace =
      (f t : PadicAlgCl l) + 1 + (f t : PadicAlgCl l)⁻¹ := fun t => by
    rw [← Units.val_inv_eq_inv_val, ← map_inv]
    simp [tor_val, Matrix.trace_fin_three, wt1, f]
  refine (h3 (F.Ψ (toGS Ω _ σ⁻¹))).trans ?_
  rw [h1, map_mul, map_inv, map_pow, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, h2,
    UpperTheory.V.Af.eis3]
  simp only [map_add, map_mul, map_inv₀, map_pow, map_natCast, map_one, RingEquiv.symm_apply_apply, _root_.mul_inv_rev, inv_inv]
  rw [mul_comm (_ ⁻¹) ((q : PadicAlgCl l) ^ e)]
  rfl
variable {K : Type} [Field K] [NumberField K] [IsCMField K] [Algebra K Ω] [IsScalarTower ℚ K Ω]
omit [IsCMField K] in
private theorem ker_lift (hK : IsQi K) (hF : IsHostFrame Ω c e ψ S A F) {g : Gam Ω S} (hg : g ∈ F.η.ker) :
    ∃ s : Formalism.ConjugateSelfDual.G K Ω, toGS Ω _ (s.restrictScalars ℚ) = g := by
  obtain ⟨σ, rfl⟩ : ∃ σ, toGS Ω (S : Set Pl) σ = g := QuotientGroup.mk_surjective g
  have h : σ ∈ (eta4 Ω).ker := by
    rw [← hF.η, hF.π]
    exact hg
  rw [← (gaussian_field_range_eq_ker_quartic_char.2 Ω K hK).1] at h
  obtain ⟨s, rfl⟩ := h
  exact ⟨s, rfl⟩
private theorem adm3 (hK : IsQi K) (hd : HostData l e ψ o₁) (hF : IsHostFrame Ω c e ψ S A F) {ι : Qbar l ≃+* ℂ}
    {g₁ : Gam Ω S} (hg : F.Marked g₁) {r : Gam Ω S →* GG 3 (PadicAlgCl l)} (hr : F.IsCharZeroPt g₁ r) (hI : TypeI F.η r)
    {ρ : Formalism.ConjugateSelfDual.G K Ω →* GL (Fin 3) (Qbar l)}
    (hρ : ∀ s : Formalism.ConjugateSelfDual.G K Ω, (ρ s : Matrix (Fin 3) (Fin 3) (Qbar l)) = (r (toGS Ω _ (s.restrictScalars ℚ))).mat)
    (ha : _root_.UpperTheory.V.Z.Win.IsAutCsdA ι (UpperTheory.V.Af.tw ρ (cycBar K Ω l ^ (-1 : ℤ)))) : _root_.UpperTheory.V.Af.Adm3Alt ι e N ρ := by
  haveI := algClosure K Ω
  haveI : IsGalois K Ω := IsAlgClosure.isGalois K Ω
  refine ⟨⟨top_ne_bot, fun _ _ _ => trivial, fun W _ hW => hI W fun g hg v hv => ?_⟩, by rwa [_root_.zpow_neg_one] at ha,
    ?_, levelAway_of_pt Ω c e ψ o₁ hd S A F hF K hK g₁ hg r hr ρ hρ,
    levelAt_of_pt Ω c e ψ o₁ hd S A F hF K hK g₁ hg r hr ρ hρ⟩
  · obtain ⟨s, rfl⟩ := ker_lift hK hF hg
    have := hW s v hv
    rwa [hρ] at this
  · have h1 : Continuous fun s => (ρ s : Matrix (Fin 3) (Fin 3) (Qbar l)) := by
      rw [funext hρ]
      exact (cont_pt hd hF hg hr).comp ((continuous_quotient_mk' : Continuous (toGS Ω (S : Set Pl))).comp
        (UpperTheory.V.Base.galEmbTop ℚ K Ω).1.continuous)
    refine Units.continuous_iff.2 ⟨h1, ?_⟩
    simp only [← map_inv]
    exact h1.comp continuous_inv
private theorem admissible_unitary_three_point (hP : _root_.UpperTheory.V.Af.HypothesesH') (hU : UpperTheory.V.Z.J.UnlEndLogNorm) [IsAlgClosure K Ω] (hK : IsQi K)
    (hd : HostData l e ψ o₁) (hF : IsHostFrame Ω c e ψ S A F) {ι : Qbar l ≃+* ℂ}
    {g₁ : Gam Ω S} (hg : F.Marked g₁) {r : Gam Ω S →* GG 3 (PadicAlgCl l)} (hr : F.IsCharZeroPt g₁ r) (hI : TypeI F.η r)
    {ρ : Formalism.ConjugateSelfDual.G K Ω →* GL (Fin 3) (Qbar l)}
    (hρ : ∀ s : Formalism.ConjugateSelfDual.G K Ω, (ρ s : Matrix (Fin 3) (Fin 3) (Qbar l)) = (r (toGS Ω _ (s.restrictScalars ℚ))).mat)
    (ha : _root_.UpperTheory.V.Z.Win.IsAutCsdA ι (UpperTheory.V.Af.tw ρ (cycBar K Ω l ^ (-1 : ℤ)))) : _root_.UpperTheory.V.Z.J.Adm3U_s ι e N ρ :=
  ⟨adm3 hK hd hF hg hr hI hρ ha, _root_.UpperTheory.V.Z.J.hostUnlE_alt hP hU K hK Ω l c N e ψ o₁ hd S A F hF g₁ hg r hr hI ρ hρ⟩
omit [IsCMField K] in
private theorem exists_w {p : ℕ} (hp : p.Prime) {B : ValuationSubring Ω} (hB : B.valuation (p : Ω) < 1) :
    ∃ w : HeightOneSpectrum (𝓞 K), IsPlaceOver B w ∧ (p : 𝓞 K) ∈ w.asIdeal := by
  haveI := algClosure K Ω
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨h1, h2, h3, -⟩ := UpperTheory.V.Base.places K Ω p B
  obtain ⟨w, hw⟩ := h1 fun h => (h2 h).2 hB
  exact ⟨w, hw, (h3 w hw).1 hB⟩
private theorem key (hP : _root_.UpperTheory.V.Af.HypothesesH') (hU : UpperTheory.V.Z.J.UnlEndLogNorm) (hK : IsQi K) {a b : ℕ} (hN : NB K a b) (hd : HostData l e ψ o₁) (hF : IsHostFrame Ω c e ψ S A F)
    (ι : Qbar l ≃+* ℂ) {g₁ : Gam Ω S} (hg : F.Marked g₁) {p : ℕ} (hp : p.Prime) (h4 : p % 4 = 3) (h7 : 7 ≤ p)
    (hpl : ¬ p ∣ l * N) {B : ValuationSubring Ω} (hB : B.valuation (p : Ω) < 1) {σ : Formalism.ConjugateSelfDual.G ℚ Ω}
    (hσ : σ ∈ (eta4 Ω).ker) (hfr : IsFrob B (p ^ 2) σ) {I : Type} (s : Finset I)
    (r : I → (Gam Ω S →* GG 3 (PadicAlgCl l))) (hr : ∀ i ∈ s, F.IsCharZeroPt g₁ (r i) ∧ TypeI F.η (r i))
    (ha : ∀ i ∈ s, ∃ ρ : Formalism.ConjugateSelfDual.G K Ω →* GL (Fin 3) (Qbar l),
      (∀ t : Formalism.ConjugateSelfDual.G K Ω, (ρ t : Matrix (Fin 3) (Fin 3) (Qbar l)) = (r i (toGS Ω _ (t.restrictScalars ℚ))).mat) ∧
      _root_.UpperTheory.V.Z.Win.IsAutCsdA ι (UpperTheory.V.Af.tw ρ (cycBar K Ω l ^ (-1 : ℤ))))
    (hi : ∀ i ∈ s, ∀ i' ∈ s, MatIso F.η.ker (mats (r i)) (mats (r i')) → i = i') :
    (∀ i ∈ s, (r i (toGS Ω _ σ⁻¹)).mat.trace ≠ (F.rz (PadicAlgCl l) (toGS Ω _ σ⁻¹)).mat.trace) ∧
    ∑ i ∈ s, -Real.log ‖(r i (toGS Ω _ σ⁻¹)).mat.trace - (F.rz (PadicAlgCl l) (toGS Ω _ σ⁻¹)).mat.trace‖ ≤
      a * N.totient * ((N : ℝ) * (e + 1)) ^ b * Real.log p := by
  classical
  haveI := algClosure K Ω
  obtain ⟨w, hw, hpw⟩ := exists_w (K := K) hp hB
  have hq := normV_inert hK hp h4 w hpw
  obtain ⟨hker, hdisc⟩ := gaussian_field_range_eq_ker_quartic_char.2 Ω K hK
  rw [← hker] at hσ
  obtain ⟨τ, rfl⟩ := hσ
  have hτ : IsFrob B (normV w) τ := by
    rw [hq]
    exact (isFrob_res B _ τ).1 hfr
  have hlp : l ≠ p := by
    rintro rfl
    exact hpl (dvd_mul_right _ _)
  have hlw : (l : 𝓞 K) ∉ w.asIdeal := fun h => by
    have hc : IsCoprime (l : 𝓞 K) (p : 𝓞 K) := Nat.Coprime.cast ((Nat.coprime_primes Fact.out hp).2 hlp)
    obtain ⟨x, y, hxy⟩ := hc
    exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
      (hxy ▸ w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ h) (w.asIdeal.mul_mem_left _ hpw)))
  have htr := trace_rz hF ι (σ := UpperTheory.V.Base.galEmb ℚ K Ω τ) (cycZ_of_isFrob hlw hw hτ)
  haveI : NeZero N.totient := ⟨(Nat.totient_pos.2 (NeZero.pos N)).ne'⟩
  set z₀ := ι (((UpperTheory.V.Chr.dirG ℚ Ω ψ (UpperTheory.V.Base.galEmb ℚ K Ω τ)⁻¹ : c.Oˣ) : c.O) : PadicAlgCl l) with hz₀
  have hz : z₀ ^ N.totient = 1 := by
    rw [hz₀, ← map_pow, ← SubmonoidClass.coe_pow, ← Units.val_pow_eq_pow_val, UpperTheory.V.Chr.dirG, MonoidHom.comp_apply,
      ← map_pow, ZMod.pow_totient]
    simp
  letI : Fintype (rootsOfUnity N.totient ℂ) := Fintype.ofFinite _
  obtain ⟨NN, hN0, hle, H⟩ := hN e hd.e_pos N (NeZero.pos N) p w hp hpw h7 (fun h => hpl (h.mul_left _))
    (by
      rw [hdisc, dvd_neg]
      intro h
      have := Int.le_of_dvd (by norm_num) h
      omega)
    (rootsOfUnity N.totient ℂ) (fun o => ((o : ℂˣ) : ℂ))
    (fun o => ⟨N.totient, NeZero.pos _, (mem_rootsOfUnity' _ _).1 o.2⟩)
    (fun u => ⟨(u.restrictRootsOfUnity N.totient).toEquiv, fun o => by simp⟩)
  rw [← Nat.card_eq_fintype_card, Complex.card_rootsOfUnity] at hle
  choose! ρ hρ haut using ha
  let o₀ : rootsOfUnity N.totient ℂ := rootsOfUnity.mkOfPowEq z₀ hz
  have hiso : ∀ i ∈ s, ∀ i' ∈ s, UpperTheory.V.Af.RepIso (ρ i) (ρ i') → i = i' := by
    rintro i his i' his' ⟨M, hM⟩
    refine hi i his i' his' ⟨M, fun g hg => ?_⟩
    obtain ⟨t, rfl⟩ := ker_lift hK hF hg
    rw [mats, mats, ← hρ i his, ← hρ i' his', hM, ← Units.val_mul, ← Units.val_mul, inv_mul_cancel_right]
  have hmem : ∀ o, ∀ x ∈ (if o = o₀ then s.image ρ else ∅), ∃ i ∈ s, ρ i = x := fun o x hx => by
    split_ifs at hx
    · exact Finset.mem_image.1 hx
    · simp at hx
  obtain ⟨H1, H2⟩ := H l hd.l_odd hlp Ω ι B hw τ hτ (fun o => if o = o₀ then s.image ρ else ∅)
    (fun o x hx => by
      obtain ⟨i, his, rfl⟩ := hmem o x hx
      exact Or.inl (admissible_unitary_three_point hP hU hK hd hF hg (hr i his).1 (hr i his).2 (hρ i his) (haut i his)))
    (fun o x hx x' hx' h => by
      obtain ⟨i, his, rfl⟩ := hmem o x hx
      obtain ⟨i', his', rfl⟩ := hmem o x' hx'
      rw [hiso i his i' his' h])
  have hρτ : ∀ i ∈ s, (ρ i τ⁻¹ : Matrix (Fin 3) (Fin 3) (Qbar l)) =
      (r i (toGS Ω _ (UpperTheory.V.Base.galEmb ℚ K Ω τ)⁻¹)).mat := fun i his => hρ i his _
  have hne : ∀ i ∈ s, (r i (toGS Ω _ (UpperTheory.V.Base.galEmb ℚ K Ω τ)⁻¹)).mat.trace ≠
      (F.rz (PadicAlgCl l) (toGS Ω _ (UpperTheory.V.Base.galEmb ℚ K Ω τ)⁻¹)).mat.trace := fun i his => by
    rw [htr, ← hρτ i his]
    exact H1 o₀ (ρ i) (by rw [if_pos rfl]; exact Finset.mem_image_of_mem _ his)
  refine ⟨hne, le_trans ?_ ((log_le_of_norm (l := l) hN0).trans hle)⟩
  rw [Finset.prod_eq_single o₀ (fun o _ ho => by rw [if_neg ho, Finset.prod_empty]) (by simp), if_pos rfl,
    Finset.prod_image fun i his i' his' h => hiso i his i' his' ⟨1, fun t => by simp [h]⟩,
    Finset.prod_congr rfl fun i his => by rw [hρτ i his]] at H2
  rw [Finset.sum_neg_distrib, neg_le_neg_iff, ← Real.log_prod fun i his => norm_ne_zero_iff.2 (sub_ne_zero.2 (hne i his)),
    htr]
  exact Real.log_le_log (norm_pos_iff.2 (by exact_mod_cast hN0)) H2
end Host
private theorem final_bound (a b l N e p : ℕ) (hl : 3 ≤ l) (hN : 2 ≤ N) (he : 1 ≤ e) (hp : p ≤ 12 * (l * N)) :
    2 * (a * N.totient * ((N : ℝ) * (e + 1)) ^ b * Real.log p) ≤ ((l : ℝ) * N * e) ^ (2 * a + 1 + b + 3) := by
  have hlN : 6 ≤ l * N := Nat.mul_le_mul hl hN
  have hx : l * N ≤ l * N * e := Nat.le_mul_of_pos_right _ he
  have h1 : 2 * a ≤ (l * N * e) ^ (2 * a) := (Nat.lt_pow_self (by omega)).le
  have h2 : N.totient ≤ l * N * e := (Nat.totient_le N).trans ((Nat.le_mul_of_pos_left _ (by omega)).trans hx)
  have h3 : N * (e + 1) ≤ l * N * e := by
    have : N * (e + 1) ≤ N * (l * e) := Nat.mul_le_mul_left _ (by nlinarith)
    nlinarith
  have h4 : p ≤ (l * N * e) ^ 3 := by
    generalize l * N * e = x at hx ⊢
    have : 6 * 6 ≤ x * x := Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  have h5 : 2 * a * N.totient * (N * (e + 1)) ^ b * p ≤ (l * N * e) ^ (2 * a + 1 + b + 3) := by
    rw [pow_add, pow_add, pow_succ]
    exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h1 h2) (Nat.pow_le_pow_left h3 _)) h4
  have h6 : ((2 * a * N.totient * (N * (e + 1)) ^ b * p : ℕ) : ℝ) ≤ (((l * N * e) ^ (2 * a + 1 + b + 3) : ℕ) : ℝ) :=
    Nat.cast_le.2 h5
  push_cast at h6
  refine le_trans ?_ h6
  have h7 : Real.log p ≤ p := Real.log_le_self (Nat.cast_nonneg _)
  calc _ = (2 * a * N.totient * ((N : ℝ) * (e + 1)) ^ b) * Real.log p := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h7 (by positivity)
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.HV GlobalTheory.GalOfCusp UpperTheory.V.Th UpperTheory.V.Z.J
theorem UpperTheory.V.Z.J.hostNumberUE_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → UnlEndLogNorm → _root_.UpperTheory.V.Z.J.NumberU3U_s → _root_.UpperTheory.V.UnitaryThreeInertia.HostNumber_s := by
  intro hP hU hNum K _ _ _ hK
  obtain ⟨a, b, hN⟩ := hNum K hK.1
  refine ⟨2 * a + 1 + b + 3, fun Ω _ _ _ l hl c N _ e ψ o₁ hd S A F hF ι g₁ hg => ?_⟩
  classical
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨p, hp, h4, h7, hpl, hple⟩ := exists_p (l * N) (Nat.mul_pos hl.out.pos (NeZero.pos N))
  obtain ⟨B, hB⟩ := (UpperTheory.V.Chr.placesQ Ω).1 p hp
  obtain ⟨σ, hσ, hfr⟩ : ∃ σ : Formalism.ConjugateSelfDual.G ℚ Ω, σ ∈ (eta4 Ω).ker ∧ IsFrob B (p ^ 2) σ := by
    letI : Algebra K Ω := (IsAlgClosed.lift : K →ₐ[ℚ] Ω).toRingHom.toAlgebra
    haveI : IsScalarTower ℚ K Ω := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
    haveI := algClosure K Ω
    obtain ⟨w, hw, hpw⟩ := exists_w (K := K) hp hB
    obtain ⟨τ, hτ⟩ := exists_isFrob hw
    rw [normV_inert hK hp h4 w hpw] at hτ
    exact ⟨τ.restrictScalars ℚ, (gaussian_field_range_eq_ker_quartic_char.2 Ω K hK).1 ▸ ⟨τ, rfl⟩, (isFrob_res B _ τ).2 hτ⟩
  refine ⟨toGS Ω _ σ⁻¹, fun r hr hI hb => ?_, fun n r hr hi => ?_⟩
  · obtain ⟨inst, tw, hρ⟩ := hb.aut
    exact (key hP hU hK hN hd hF ι hg hp h4 h7 hpl hB hσ hfr (Finset.univ : Finset Unit) (fun _ => r) (fun _ _ => ⟨hr, hI⟩)
      (fun _ _ => hρ) (fun _ _ _ _ _ => rfl)).1 () (Finset.mem_univ _)
  · choose inst tw hρ using fun i => (hr i).2.2.aut
    have hlog : Real.log l ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (by exact_mod_cast hl.out.pos)
      (by exact_mod_cast hl.out.ne_one)
    let j : Fin n → (K →+* Ω) := fun i => @algebraMap K Ω _ _ (inst i)
    have hcard : Fintype.card (K →+* Ω) = 2 := (NumberField.Embeddings.card K Ω).trans hK.1
    rw [Finset.sum_mul]
    simp only [vl1, div_mul_cancel₀ _ hlog]
    rw [← Finset.sum_fiberwise Finset.univ j]
    refine le_trans (Finset.sum_le_card_nsmul _ _ (a * N.totient * ((N : ℝ) * (e + 1)) ^ b * Real.log p) fun f _ => ?_) ?_
    · letI : Algebra K Ω := f.toAlgebra
      haveI : IsScalarTower ℚ K Ω := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
      refine (key hP hU hK hN hd hF ι hg hp h4 h7 hpl hB hσ hfr _ r (fun i _ => ⟨(hr i).1, (hr i).2.1⟩) (fun i hi => ?_)
        (fun i _ i' _ => hi i i')).2
      have e1 : inst i = f.toAlgebra := Algebra.algebra_ext _ _ fun x => DFunLike.congr_fun (Finset.mem_filter.1 hi).2 x
      have h1 := hρ i
      revert h1
      generalize tw i = t
      revert t
      rw [e1]
      exact fun _ h => h
    · rw [Finset.card_univ, hcard, nsmul_eq_mul, Nat.cast_ofNat]
      have h2 := hl.out.two_le
      have h3 := hd.l_odd
      obtain ⟨k, hk⟩ := hd.N_even
      have h5 := NeZero.pos N
      exact final_bound a b l N e p (by omega) (by omega) hd.e_pos hple
end
