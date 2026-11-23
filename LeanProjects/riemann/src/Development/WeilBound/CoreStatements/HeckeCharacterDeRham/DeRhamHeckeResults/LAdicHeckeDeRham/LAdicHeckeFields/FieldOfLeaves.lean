import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterDeRham
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasPeriods
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalMod
import Development.WeilBound.CoreStatements.CrystallinePeriodRings.MaximalIdealEqSpanT
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTateIterateLimitCongruenceStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTateScaledIterateTendsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTateSeriesCommuteLinearStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTateCommutingSeriesUniqueStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTateIterateEventuallyZeroStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTateTorsionApproximationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTateLimitKernelZeroStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemFBOfNear
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TeichmullerNearPowerExistsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTateSeriesDeRhamPeriodStatement
import Development.WeilBound.CoreStatements.HeckeCharacterDeRham.DeRhamHeckeResults.LAdicHeckeDeRham.LAdicHeckeFields.Reduce
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTateNormCyclotomicStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTateEndomorphismSeriesExistsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterValuesIntegralStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformizerPropertiesResidueStatement

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace PositivityTheory.SecR.Hladr2

def TiltLeaf : Prop :=  ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ) (π : ↥(OL K)) (z : ℕ → Om l),
    LTData K χ π z → ∀ μ : ↥K.1 →ₐ[ℚ_[l]] Om l,
    ∃ (r : ↥(OL K) →+* Tl l) (v : ℕ → Tl l),
      (∀ n, v (n + 1) ^ qOf π = v n) ∧ v 0 ≠ 0 ∧ ‖thB l (tch l (v 0))‖ < 1 ∧
      (∀ c, ∃ c', tch l (r c) = oB K μ (c + π * c')) ∧
      (∀ (g : GQ l) (hg : g ∈ GK K) (φ : PowerSeries ↥(OL K)), PowerSeries.constantCoeff φ = 0 →
        ((PowerSeries.coeff 1 φ : ↥(OL K)) : ↥K.1) = ((χ ⟨g, hg⟩ : (↥K.1)ˣ) : ↥K.1) →
        PowerSeries.subst φ (ltSeries π) = PowerSeries.subst (ltSeries π) φ →
        ∀ n D, v n ^ D ∣ actT g (v n) - ∑ i ∈ Finset.range D, r (PowerSeries.coeff i φ) * v n ^ i) ∧
      (μ = K.1.val → ∀ n, ‖thB l (tch l (v n)) - ((z n : Om l) : ℂ_[l])‖ ≤ ‖(((π : ↥K.1) : Om l) : ℂ_[l])‖)

def ProductLeaf : Prop :=  ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ),
    (∀ (g : GQ l) (hg : g ∈ GK K), (∀ u ∈ GroundTheory.PAdicHodge.unramifiedClosure l, g u = u) →
      Algebra.norm ℚ_[l] ((χ ⟨g, hg⟩ : (↥K.1)ˣ) : ↥K.1) =
        (((GroundTheory.PAdicHodge.cycloChar ⊥ (Formalism.Per6.toBot g) : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l])) →
    ∀ t : (↥K.1 →ₐ[ℚ_[l]] Om l) → Formalism.Per6.BdRp l, (∀ μ, PrePer K χ μ (t μ)) →
      ∀ μ, (μ = K.1.val → t μ ∉ FB l 2) ∧ (μ ≠ K.1.val → t μ ∉ FB l 1)

variable {l : ℕ} [Fact l.Prime]

theorem actB_rB (g : GQ l) (x : Om l) : actB g (rB l x) = rB l (g x) :=
  GroundTheory.PAdicHodge.gal_smul_algClToBdR (Formalism.Per6.toBot g) x

theorem actB_tch (g : GQ l) (x : Tl l) : actB g (tch l x) = tch l (actT g x) := by
  change Formalism.Per6.toBot g • (GroundTheory.PAdicHodge.wittToBDeRhamPlus _ l (WittVector.teichmuller l x)) = _
  rw [GroundTheory.PAdicHodge.gal_smul_wittToBDeRhamPlus, GroundTheory.PAdicHodge.AInf.gal_smul_teichmuller]
  rfl

theorem thB_rB (x : Om l) : thB l (rB l x) = ((x : Om l) : ℂ_[l]) :=
  GroundTheory.PAdicHodge.thetaAlgHom_algClToBdR l x

theorem thB_actB_zero (g : GQ l) {x : Formalism.Per6.BdRp l} (hx : thB l x = 0) : thB l (actB g x) = 0 := by
  have h := GroundTheory.PAdicHodge.thetaBDeRhamPlusField_gal_smul (Formalism.Per6.toBot g) x
  have h2 : GroundTheory.PAdicHodge.IsPerfectoidField.thetaBDeRhamPlusField l x = 0 := by
    rw [← hx]; exact (GroundTheory.PAdicHodge.thetaAlgHom_apply l x).symm
  rw [h2, smul_zero] at h
  rw [← h]
  exact GroundTheory.PAdicHodge.thetaAlgHom_apply l _

theorem actB_FB (g : GQ l) (k : ℕ) (x : Formalism.Per6.BdRp l) (hx : x ∈ FB l k) : actB g x ∈ FB l k := by
  have h1 : Ideal.map (actB g) (RingHom.ker (thB l)) ≤ RingHom.ker (thB l) :=
    Ideal.map_le_iff_le_comap.2 fun y hy => thB_actB_zero g hy
  have h2 := Ideal.mem_map_of_mem (actB g) hx
  rw [FB, Ideal.map_pow] at h2
  exact Ideal.pow_right_mono h1 k h2

theorem tch_pow (x : Tl l) (n : ℕ) : tch l (x ^ n) = tch l x ^ n := by
  simp only [tch, map_pow]

theorem near_pow_of_sub {B : Type} [CommRing B] {S : Subring B} {ϖ : B} {a b : B} (ha : a ∈ S) (hb : b ∈ S)
    (h : ∃ s ∈ S, a - b = ϖ * s) (M : ℕ) : ∃ s ∈ S, a ^ M - b ^ M = ϖ * s := by
  obtain ⟨s, hs, e⟩ := h
  obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow (⟨a, ha⟩ : ↥S) ⟨b, hb⟩ M
  refine ⟨s * c, S.mul_mem hs c.2, ?_⟩
  have h3 : a ^ M - b ^ M = (a - b) * (c : B) := by simpa using congrArg Subtype.val hc
  rw [h3, e]; ring

theorem iter_near {B : Type} [CommRing B] {S : Subring B} {ϖ : B} (hϖ : ϖ ∈ S) (q : ℕ) {Q b : B} (hQ : Q ∈ S)
    (hb : b ∈ S) (h : ∃ s ∈ S, Q - b = ϖ * s) (n : ℕ) :
    ltIter ϖ q n Q ∈ S ∧ ∃ s ∈ S, ltIter ϖ q n Q - b ^ (q ^ n) = ϖ * s := by
  induction n with
  | zero => simpa [ltIter] using ⟨hQ, h⟩
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    have e : ltIter ϖ q (n + 1) Q = ϖ * ltIter ϖ q n Q + ltIter ϖ q n Q ^ q := by
      simp only [ltIter, Function.iterate_succ_apply']
    have hbn : b ^ (q ^ n) ∈ S := S.pow_mem hb _
    obtain ⟨s, hs, e2⟩ := near_pow_of_sub h1 hbn h2 q
    refine ⟨by rw [e]; exact S.add_mem (S.mul_mem hϖ h1) (S.pow_mem h1 _), ltIter ϖ q n Q + s,
      S.add_mem h1 hs, ?_⟩
    rw [e, pow_succ q n, pow_mul]
    linear_combination e2

end PositivityTheory.SecR.Hladr2

namespace PositivityTheory.SecR.Hladr2
variable {l : ℕ} [Fact l.Prime]

theorem pre_period (HT : TiltLeaf) (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ) (π : ↥(OL K)) (z : ℕ → Om l)
    (hD : LTData K χ π z) (hc : Continuous (fun g => (((χ g : (↥K.1)ˣ) : ↥K.1) : Om l)))
    (μ : ↥K.1 →ₐ[ℚ_[l]] Om l) : ∃ t, PrePer K χ μ t := by
  have hπ : Irreducible π := hD.1
  obtain ⟨hq2, hlq, hπl, hnπ, hnμ⟩ := GlobalTheory.T.uniformizer_properties_residue K π hπ
  haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  let K' : IntermediateField ℚ_[l] (Om l) := IntermediateField.normalClosure ℚ_[l] ↥K.1 (Om l)
  haveI : FiniteDimensional ℚ_[l] K' := inferInstance
  haveI : Normal ℚ_[l] K' := inferInstance
  obtain ⟨S, hW, hO, hG, hI, hE⟩ := GlobalTheory.CompanionTheory.LTPer.lattice_main K'
  have hμK : ∀ x, μ x ∈ K' := fun x => AlgHom.fieldRange_le_normalClosure μ ⟨x, rfl⟩
  have hint : ∀ c : ↥(OL K), IsIntegral ℤ_[l] (μ (c : ↥K.1)) := fun c =>
    IsIntegral.map (μ.restrictScalars ℤ_[l]) c.2
  have hoB : ∀ c, oB K μ c ∈ S := fun c => hO _ (hμK _) (hint c)
  have hne : μ (π : ↥K.1) ≠ 0 := by
    have h0 : (π : ↥K.1) ≠ 0 := fun h => hπ.ne_zero (Subtype.ext h)
    exact (map_ne_zero_iff μ μ.toRingHom.injective).2 h0
  obtain ⟨E, hnot⟩ := hE _ (hμK _) (hint π) hne (hnμ μ)
  have hϖe : rB l (μ (π : ↥K.1)) = oB K μ π := rfl
  rw [hϖe] at E hnot
  obtain ⟨ϖ', hϖ'⟩ := E.unit.exists_right_inv
  set ϖ := oB K μ π with hϖ
  obtain ⟨r, v, hvq, hv0, hv1, hr, hrg, hrz⟩ := HT K χ π z hD μ
  set q := qOf π with hq
  have hqd : ∃ s ∈ S, (q : Formalism.Per6.BdRp l) = ϖ * s := by
    obtain ⟨d, hd⟩ := hπl
    obtain ⟨q', hq'⟩ := hlq
    refine ⟨oB K μ (d * (q' : ↥(OL K))), hoB _, ?_⟩
    rw [hϖ, ← map_mul, ← mul_assoc, ← hd, hq']
    simp
  have hvS : ∀ n, tch l (v n) ∈ S := fun n => hW _
  have hvB : ∀ n, tch l (v (n + 1)) ^ q = tch l (v n) := fun n => by rw [← tch_pow, hvq]
  obtain ⟨Q, hQS, hQ⟩ := GlobalTheory.T.lubin_tate_iterate_limit_congruence E q hq2 hqd (fun n => tch l (v n)) hvS hvB
  have hθϖ : ‖thB l ϖ‖ < 1 := by
    rw [← hϖe, thB_rB]; exact hnμ μ
  have hθϖ0 : thB l ϖ ≠ 0 := by
    rw [← hϖe, thB_rB]
    exact (map_ne_zero_iff (UniformSpace.Completion.coeRingHom : Om l →+* ℂ_[l])
      (RingHom.injective _)).2 hne
  have hnil0 := GlobalTheory.T.teichmuller_near_power_exists S hW ϖ hθϖ0 (v 0) hv1
  have hQ0 : ∃ s ∈ S, Q - tch l (v 0) = ϖ * s := by
    obtain ⟨a, ha, e⟩ := hQ 0
    exact ⟨a, ha, by simpa [ltIter] using e⟩
  have hnilQ : ∃ M : ℕ, 0 < M ∧ Near S ϖ (FB l 1) 1 (Q ^ M) := by
    obtain ⟨M, hM, s, hs, e⟩ := hnil0
    obtain ⟨s', hs', e'⟩ := near_pow_of_sub hQS (hvS 0) hQ0 M
    refine ⟨M, hM, s + s', S.add_mem hs hs', ?_⟩
    have : Q ^ M - ϖ ^ 1 * (s + s') = tch l (v 0) ^ M - ϖ ^ 1 * s := by
      rw [pow_one] at *
      linear_combination e'
    rwa [this]
  obtain ⟨t, ht⟩ := GlobalTheory.T.lubin_tate_scaled_iterate_tends E ϖ' hϖ' q hq2 Q hQS hnilQ
  have hkerF : ∀ x, thB l x = 0 ↔ x ∈ FB l 1 := fun x => by
    rw [FB, pow_one, RingHom.mem_ker]
  refine ⟨t, ?_, ?_, ?_⟩
  · rintro rfl
    obtain ⟨n, hn⟩ := GlobalTheory.T.lubin_tate_iterate_eventually_zero E ϖ' hϖ' (thB l) hkerF hI hθϖ q hq2 Q hQS hnilQ ht
    obtain ⟨-, s, hs, e⟩ := iter_near E.mem q hQS (hvS 0) hQ0 n
    rw [hn, zero_sub, ← tch_pow] at e
    refine hnot (v 0 ^ (q ^ n)) (pow_ne_zero _ hv0) (-s) (S.neg_mem hs) ?_
    rw [mul_neg, ← e, neg_neg]
  · intro g hg hfix
    obtain ⟨a, ha⟩ := GlobalTheory.T.character_values_integral K χ hc ⟨g, hg⟩
    obtain ⟨φ, hφ0, hφ1, hφc⟩ := GlobalTheory.T.lubin_tate_endomorphism_series_exists K π hπ a
    have hφ1' : ((PowerSeries.coeff 1 φ : ↥(OL K)) : ↥K.1) = ((χ ⟨g, hg⟩ : (↥K.1)ˣ) : ↥K.1) := by
      rw [hφ1, ha]
    have hσϖ : actB g ϖ = ϖ := by
      rw [← hϖe, actB_rB, hfix]
    have hnil : ∀ n, ‖thB l (tch l (v n))‖ < 1 := fun n => by
      have h1 : ∀ n, tch l (v n) ^ (q ^ n) = tch l (v 0) := by
        intro n
        induction n with
        | zero => simp
        | succ n ih => rw [pow_succ', pow_mul, hvB, ih]
      have h2 : ‖thB l (tch l (v n))‖ ^ (q ^ n) < 1 := by
        rw [← norm_pow, ← map_pow, h1]; exact hv1
      by_contra h3
      exact absurd h2 (not_lt.2 (one_le_pow₀ (not_lt.1 h3)))
    have hev1 : ∀ n, EvalMod S (FB l) ϖ (oB K μ) φ (tch l (v n)) (actB g (tch l (v n))) 1 := fun n => by
      rw [actB_tch]
      exact GlobalTheory.T.lubin_tate_series_de_rham_period K μ π S hW hoB E hπl r hr (v n) (actT g (v n)) (hnil n) φ
        (fun D => hrg g hg φ hφ0 hφ1' hφc n D)
    have hevQ := GlobalTheory.T.lubin_tate_commuting_series_unique E (oB K μ) hoB π rfl q hq2 hqd φ hφ0 hφc (actB g) (hG g) (fun k x hx => actB_FB g k x hx)
      hσϖ (fun n => tch l (v n)) hvS hvB hnil0 Q hQS hQ hev1
    have := GlobalTheory.T.lubin_tate_series_commute_linear E ϖ' hϖ' (oB K μ) hoB π rfl q hq2 hqd φ hφ0 hφc (actB g) (hG g)
      (fun k x hx => actB_FB g k x hx) hσϖ Q hQS hnilQ hevQ t ht
    rw [this]
    congr 1
    change rB l (μ (algebraMap ↥(OL K) ↥K.1 (PowerSeries.coeff 1 φ))) = _
    congr 2
  · intro hμ
    have hθQ : thB l Q = 0 := by
      refine GlobalTheory.T.lubin_tate_torsion_approximation E (thB l) hI hθϖ0 hθϖ q hq2 ?_ (fun n => tch l (v n)) hvS (fun n => ((z n : Om l) : ℂ_[l])) ?_ ?_ ?_ Q hQS hQ
      · obtain ⟨s, hs, e⟩ := hqd
        rw [← map_natCast (thB l), e, map_mul, norm_mul]
        exact mul_le_of_le_one_right (norm_nonneg _) (hI s hs)
      · have := hD.2.1
        rw [this]; simp
      · intro n
        have h := hD.2.2.2.1 n
        have h2 := congrArg (UniformSpace.Completion.coeRingHom : Om l →+* ℂ_[l]) h
        rw [map_add, map_mul, map_pow] at h2
        have e : thB l ϖ = (((π : ↥K.1) : Om l) : ℂ_[l]) := by
          rw [← hϖe, thB_rB, hμ]; rfl
        rw [e]
        exact h2
      · intro n
        have e : thB l ϖ = (((π : ↥K.1) : Om l) : ℂ_[l]) := by
          rw [← hϖe, thB_rB, hμ]; rfl
        rw [e]
        exact hrz hμ n
    exact GlobalTheory.T.lubin_tate_limit_kernel_zero E ϖ' hϖ' (thB l) hkerF hI hθϖ q hq2 Q hθQ t ht

end PositivityTheory.SecR.Hladr2

namespace PositivityTheory.SecR.Hladr2
variable {l : ℕ} [Fact l.Prime]

theorem ker_thB : RingHom.ker (thB l) = RingHom.ker (Formalism.Per6.θD l) := by
  ext x
  rw [RingHom.mem_ker, RingHom.mem_ker]
  exact iff_of_eq (congrArg (· = (0 : ℂ_[l])) (GroundTheory.PAdicHodge.thetaAlgHom_apply l x))

theorem σD_algebraMap (g : GQ l) (y : Formalism.Per6.BdRp l) :
    Formalism.Per6.σD g (algebraMap (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l) y) =
      algebraMap (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l) (actB g y) :=
  GroundTheory.PAdicHodge.galBdRField_algebraMap (Formalism.Per6.toBot g) y

theorem fil_iff {P : LocPrime l} {AI : LocAinf l P} (T : LocTied6 l P AI) (K : FinExt l) (n : ℕ) {x : P.R.BdR}
    {y : Formalism.Per6.BdRp l} (h : T.eD x = algebraMap (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l) y) :
    x ∈ (P.PD K).Fil (n : ℤ) ↔ y ∈ FB l n := by
  rw [PositivityTheory.LocInh.filq_tie_fil T K n h, FB, ker_thB]

theorem hasPeriods_main (HT : TiltLeaf) (HP : ProductLeaf) {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (hT : Nonempty (LocTied6 l P AI))
    (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ) (hLT : IsLTChar K χ)
    (hc : Continuous (fun g => (((χ g : (↥K.1)ˣ) : ↥K.1) : Om l))) : HasPeriods P K χ := by
  obtain ⟨T⟩ := hT
  have hN := GlobalTheory.T.lubin_tate_norm_cyclotomic K χ hLT hc
  obtain ⟨π, z, hD⟩ := hLT
  choose t ht using fun μ => pre_period HT K χ π z hD hc μ
  have hP := HP K χ hN t ht
  intro μ
  obtain ⟨y, hy⟩ : ∃ y : P.R.BdR, T.eD y = algebraMap (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l) (t μ) :=
    ⟨_, T.eD.apply_symm_apply _⟩
  have f1 := fil_iff T K 1 hy
  have f2 := fil_iff T K 2 hy
  have f0 := fil_iff T K 0 hy
  rw [Nat.cast_one] at f1
  rw [Nat.cast_ofNat] at f2
  rw [Nat.cast_zero] at f0
  have hF1 : thB l (t μ) = 0 → t μ ∈ FB l 1 := fun h => by
    rw [FB, pow_one]; exact h
  refine ⟨y, ?_, ?_, ?_⟩
  · intro g hg hfix
    apply T.eD.injective
    rw [T.actD, map_mul, hy, PositivityTheory.LocInh.tie_o, σD_algebraMap, (ht μ).2.1 g hg hfix, map_mul]
    rfl
  · intro hμ
    exact ⟨f1.2 (hF1 ((ht μ).2.2 hμ)), fun h => (hP μ).1 hμ (f2.1 h)⟩
  · intro hμ
    refine ⟨f0.2 ?_, fun h => (hP μ).2 hμ (f1.1 h)⟩
    rw [FB, pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top

end PositivityTheory.SecR.Hladr2

theorem PositivityTheory.SecR.Hladr2.field_of_leaves (HT : PositivityTheory.SecR.Hladr2.TiltLeaf) (HP : PositivityTheory.SecR.Hladr2.ProductLeaf) :
    GlobalTheory.Published.HeckeLAdicCharacterDeRham :=
  PositivityTheory.SecR.Hladr.field_of_ltPeriods fun P AI hT K χ hLT hc => PositivityTheory.SecR.Hladr2.hasPeriods_main HT HP P AI hT K χ hLT hc
