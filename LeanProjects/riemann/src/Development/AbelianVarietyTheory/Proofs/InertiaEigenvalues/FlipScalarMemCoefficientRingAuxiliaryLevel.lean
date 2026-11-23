import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFlipDet
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitSupportedClassScalarMemValuationRing
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameHeckeCharSplitSupportedEqProdResidue
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.FlipScalUnit

open Formalism.L2.Host

theorem locK_eq_val_zpow {L : Type} [Field L] [NumberField L] (χ : HChar L) (R : HeightOneSpectrum (𝓞 L))
    (hR : χ.UnrAt R) (m : Lˣ) : χ.locK R m = χ.val R ^ ordF R m := by
  set N := ordF R m with hN
  set u : Lˣ := m * (unif R ^ N)⁻¹ with hu
  have hmu : m = u * unif R ^ N := by rw [hu, inv_mul_cancel_right]
  have hPv : R.valuation L (m : L) = WithZero.exp (-N) := by
    have h0 : R.valuation L (m : L) ≠ 0 := by simp
    rw [hN, ordF, neg_neg]
    exact (WithZero.exp_log h0).symm
  have hatFin : ∀ (x : Lˣ), Valued.v ((atFin R x : (R.adicCompletion L)ˣ) : R.adicCompletion L) = R.valuation L (x : L) :=
    fun x => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' R (x : L)
  have hunit : IsUnitAt R (atFin R u) := by
    have h1 := unif_spec R
    unfold IsUnifAt at h1
    unfold IsUnitAt
    rw [hu, map_mul, map_inv, map_zpow, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, map_mul,
      map_inv₀, map_zpow₀, h1, hatFin, hPv, ← WithZero.exp_zsmul, ← WithZero.exp_neg, ← WithZero.exp_add]
    simp
  have h1 : χ.locK R u = 1 := hR _ hunit
  calc χ.locK R m = χ.locK R (u * unif R ^ N) := by rw [← hmu]
    _ = χ.val R ^ N := by rw [map_mul, map_zpow, h1, one_mul]; rfl

open Formalism.L2.JoinChr in
set_option maxHeartbeats 800000 in

theorem char_flipDet {D : D7} (c : (AE D)ˣ →* Circle) (χ : HChar D.host.E) (hc : ChrEq c χ)
    (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D) (he : IsIdemSum e T) (m : D.host.Eˣ) (x : (AE D)ˣ)
    (hx : (x : AE D) * (e * incA D (m : D.host.E) + (1 - e)) = 1) :
    ((c x : Circle) : ℂ) = ∏ R ∈ T, ((χ.locK R m⁻¹ : ℂˣ) : ℂ) := by
  classical
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨N, hN, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D ι h1 h2
    (GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3) c χ hc
  have hinf : infPart D (x : AE D) = 1 := by
    have h0 := congrArg (infPart D) hx
    simp only [map_mul, map_add, map_sub, map_one, GlobalTheory.PlaceVec.idemSum_infPart he, zero_mul, zero_add, sub_zero,
      mul_one] at h0
    exact h0
  obtain ⟨⟨es, hes, hsum⟩, -⟩ := he
  obtain ⟨ev, hev⟩ : ∃ ev : ∀ R : HeightOneSpectrum (𝓞 D.host.E), AE D →+* R.adicCompletion D.host.E,
      ∀ R z, ev R z = GlobalTheory.CharLocProd.evalAt R (ι (finPart D z)) :=
    ⟨fun R => (GlobalTheory.CharLocProd.evalAt R).comp ((ι : _ →+* _).comp (finPart D)), fun _ _ => rfl⟩
  have hidem : ∀ Q ∈ T, ev Q (es Q) = 1 ∧ ∀ R, R ≠ Q → ev R (es Q) = 0 := by
    intro Q hQ
    simp only [hev]
    refine GlobalTheory.TameSplitChar.idem_apply _ (by rw [← RingEquiv.map_mul, ← RingHom.map_mul, (hes Q hQ).1.1]) Q fun y hy => ?_
    refine ((hes Q hQ).2 y hy).trans (not_congr ((h2 _).trans ?_))
    rw [RingHom.map_mul, RingEquiv.map_mul, show finPart D (incA D ((y : D.host.E)⁻¹)) =
      (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] ((y : D.host.E)⁻¹) from rfl, h1]
    rfl
  have heT : ∀ R ∈ T, ev R e = 1 := by
    intro R hR
    rw [hsum, map_sum, Finset.sum_eq_single R, (hidem R hR).1]
    · intro Q hQ hne; exact (hidem Q hQ).2 R hne.symm
    · intro h; exact absurd hR h
  have heT' : ∀ R, R ∉ T → ev R e = 0 := by
    intro R hR
    rw [hsum, map_sum]
    exact Finset.sum_eq_zero fun Q hQ => (hidem Q hQ).2 R fun h => hR (h ▸ hQ)
  have hinc : ∀ R (k : D.host.E), ev R (incA D k) = algebraMap D.host.E (R.adicCompletion D.host.E) k := by
    intro R k
    rw [hev, show finPart D (incA D k) = (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] k from rfl, h1,
      GlobalTheory.CharLocProd.evalAt_algebraMap]
  have hxT : ∀ R ∈ T, ev R x = algebraMap D.host.E (R.adicCompletion D.host.E) ((m⁻¹ : D.host.Eˣ) : D.host.E) := by
    intro R hR
    have h0 := congrArg (ev R) hx
    simp only [map_mul, map_add, map_sub, map_one, heT R hR, one_mul, sub_self, add_zero, hinc] at h0
    rw [eq_inv_of_mul_eq_one_left h0, Units.val_inv_eq_inv_val, map_inv₀]
  have hxT' : ∀ R, R ∉ T → ev R x = 1 := by
    intro R hR
    have h0 := congrArg (ev R) hx
    simp only [map_mul, map_add, map_sub, map_one, heT' R hR, zero_mul, zero_add, sub_zero, mul_one] at h0
    exact h0
  have hfin : {R : HeightOneSpectrum (𝓞 D.host.E) | R.asIdeal ∣ Ideal.span {(N : 𝓞 D.host.E)}}.Finite :=
    Ideal.finite_factors (by simpa [Ideal.span_singleton_eq_bot] using hN.ne')
  have key := hprod x hinf (T ∪ hfin.toFinset) (fun R => if R ∈ T then m⁻¹ else 1) ?_ ?_
  rotate_left
  · intro R _
    change Valued.v (GlobalTheory.CharLocProd.evalAt R (ι (finPart D x))) = _ ∧
      Valued.v (GlobalTheory.CharLocProd.evalAt R (ι (finPart D x)) - _) ≤ _
    rw [← hev]
    by_cases hR : R ∈ T
    · simp only [if_pos hR]
      rw [hxT R hR, sub_self, map_zero, GlobalTheory.CharLocProd.val_algebraMap]
      exact ⟨rfl, zero_le'⟩
    · simp only [if_neg hR]
      rw [hxT' R hR, Units.val_one, map_one, map_one, map_one, sub_self, map_zero]
      exact ⟨rfl, zero_le'⟩
  · intro R hR
    rw [Finset.mem_union, not_or] at hR
    change Valued.v (GlobalTheory.CharLocProd.evalAt R (ι (finPart D x))) = _ ∧ _
    rw [← hev, hxT' R hR.1, map_one]
    exact ⟨rfl, fun h => hR.2 (hfin.mem_toFinset.2 (Ideal.dvd_span_singleton.2 h))⟩
  rw [key, ← Finset.prod_subset Finset.subset_union_left
    (fun R _ hR => by rw [if_neg hR, map_one, Units.val_one])]
  exact Finset.prod_congr rfl fun R hR => by rw [if_pos hR]

end GlobalTheory.FlipScalUnit

open GlobalTheory.FlipScalUnit in
set_option maxHeartbeats 1600000 in

theorem GlobalTheory.LevelSeries.flipScal_mem_valRing_of_unit : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → Odd W.rank → ∀ (χ : Formalism.L2.Host.HChar D.host.E) (M₀ l pd : ℕ), ChiData χW χ M₀ → l.Prime → Nat.Coprime pd M₀ → Nat.Coprime pd l → Nat.Coprime pd (GlobalTheory.Tow.badN D) → ∀ (k : Type) [Field k] [NumberField k] (σ : k →+* ℂ) (la : HeightOneSpectrum (𝓞 k)) (O : Subring ℂ), ((l : ℕ) : 𝓞 k) ∈ la.asIdeal → ValRing σ la O → ConjIn D σ → χ.ValuesIn (-1 / 2) σ → ∀ (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (eT : AE D) (x : (AE D)ˣ), IsIdemSum eT T → (∀ PP ∈ T, ((pd : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → IsFlipDet V eT pd x → flipScal χW V W T pd x ∈ O := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hv hodd χ M₀ l pd hχ hl hpM hpl hpbad k _ _ σ la O hla hVR hConj hVI T eT x hT
    hpT hx
  classical
  have hpair := hv.1
  have hpd0 : pd ≠ 0 := by
    rintro rfl
    exact hl.one_lt.ne' ((Nat.coprime_zero_left l).1 hpl)
  have hnot : ∀ (a b : ℕ), Nat.Coprime a b → ∀ R : HeightOneSpectrum (𝓞 D.host.E),
      ((a : ℕ) : 𝓞 D.host.E) ∈ R.asIdeal → ((b : ℕ) : 𝓞 D.host.E) ∉ R.asIdeal := by
    intro a b hab R ha hb
    obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hab
    have h1 : (((u * a + v * b : ℤ)) : 𝓞 D.host.E) = 1 := by rw [huv]; simp
    apply R.isPrime.ne_top
    rw [Ideal.eq_top_iff_one, ← h1]
    push_cast
    exact add_mem (Ideal.mul_mem_left _ _ ha) (Ideal.mul_mem_left _ _ hb)
  have hu : ∀ R ∈ T, χ.UnrAt R := fun R hR => hχ.2.1 R (hnot pd M₀ hpM R (hpT R hR))
  have hlR : ∀ R ∈ T, ((l : ℕ) : 𝓞 D.host.E) ∉ R.asIdeal := fun R hR => hnot pd l hpl R (hpT R hR)
  have hO : ∀ m : ℕ, Nat.Coprime m l → ((m : ℂ))⁻¹ ∈ O := fun m hm => by
    have h1 := hVR ((m : k)⁻¹) (by rw [map_inv₀, GlobalTheory.ScalarUnit.val_natCast la hla hm, inv_one])
    simpa using h1
  letI : Algebra k ℂ := σ.toAlgebra
  obtain ⟨A, hA⟩ := ReciprocityTheory.Gal.exists_valuationSubring_over (Ω := ℂ) la
  have hA' : ∀ x : 𝓞 k, A.valuation (σ (x : k)) < 1 ↔ x ∈ la.asIdeal := hA
  have hpA : (l : ℂ) ∈ A.nonunits := by
    rw [ValuationSubring.mem_nonunits_iff]
    have h1 := (hA' (l : 𝓞 k)).2 hla
    simpa using h1
  choose bW hbW using hpair.expW
  have hval : ∀ R ∈ T, ((χ.val R : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm R.asIdeal) : ℝ) : ℂ) ∈ O := by
    intro R hR
    obtain ⟨y, hy⟩ := hVI R (hu R hR)
    have hy' : σ y = ((χ.val R : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm R.asIdeal) : ℝ) : ℂ) := by
      rw [hy, Formalism.L2.Host.HChar.valTw, GlobalTheory.LevelSeriesScal.natCast_cpow_half]
    obtain ⟨h1, -⟩ := GlobalTheory.LevelSeriesScal.val_mul_sqrt_unit D χW χ hχ.1 _ hbW l A hl hpA R (hlR R hR)
    rw [← hy'] at h1
    have hy0 : la.valuation k y ≤ 1 :=
      GlobalTheory.LevelSeriesScal.val_le_one_of_mem σ la A hA' y ((A.valuation_le_one_iff _).2 h1)
    exact hy' ▸ hVR y hy0
  have hNl : ∀ R ∈ T, Nat.Coprime (Ideal.absNorm R.asIdeal) l := by
    intro R hR
    have hle : Ideal.span {((pd : ℕ) : 𝓞 D.host.E)} ≤ R.asIdeal := (Ideal.span_singleton_le_iff_mem _).2 (hpT R hR)
    have hd := Ideal.absNorm_dvd_absNorm_of_le hle
    rw [Ideal.absNorm_span_singleton, ← map_natCast (algebraMap ℤ (𝓞 D.host.E)) pd, Algebra.norm_algebraMap,
      Int.natAbs_pow, Int.natAbs_natCast] at hd
    exact Nat.Coprime.coprime_dvd_left hd (Nat.Coprime.pow_left _ hpl)
  have hN0 : ∀ R : HeightOneSpectrum (𝓞 D.host.E), Ideal.absNorm R.asIdeal ≠ 0 := fun R h =>
    R.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  set mU : D.host.Eˣ := Units.mk0 ((pd : ℕ) : D.host.E) (by exact_mod_cast hpd0) with hmU
  set nR : HeightOneSpectrum (𝓞 D.host.E) → ℕ := fun R =>
    (Associates.mk R.asIdeal).count (Associates.mk (Ideal.span {((pd : ℕ) : 𝓞 D.host.E)})).factors with hnR
  have hord : ∀ R : HeightOneSpectrum (𝓞 D.host.E), Formalism.L2.Host.ordF R mU = (nR R : ℤ) := by
    intro R
    have h0 : ((pd : ℕ) : 𝓞 D.host.E) ≠ 0 := by exact_mod_cast hpd0
    have e1 : ((mU : D.host.Eˣ) : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E ((pd : ℕ) : 𝓞 D.host.E) := by
      rw [hmU, Units.val_mk0, map_natCast]
    unfold Formalism.L2.Host.ordF
    rw [e1, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_def, if_neg h0, WithZero.log_exp,
      neg_neg]
  have hx' : (x : AE D) * (eT * incA D ((mU ^ V.rank : D.host.Eˣ) : D.host.E) + (1 - eT)) = 1 := by
    have h := hx
    unfold IsFlipDet at h
    rwa [Units.val_pow_eq_pow_val, map_pow, hmU, Units.val_mk0, map_natCast]
  have hcx := char_flipDet χW χ hχ.1 T eT hT (mU ^ V.rank) x hx'
  have hcx' : ((χW x : Circle) : ℂ) = ∏ R ∈ T, (((χ.val R : ℂˣ) : ℂ) ^ (nR R * V.rank))⁻¹ := by
    rw [hcx]
    refine Finset.prod_congr rfl fun R hR => ?_
    rw [map_inv, map_pow, locK_eq_val_zpow χ R (hu R hR), hord R, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
      zpow_natCast, Units.val_pow_eq_pow_val, ← pow_mul]
  have hsq : Real.sqrt ((flipIdx V W T pd : ℕ) : ℝ) =
      ∏ R ∈ T, Real.sqrt (Ideal.absNorm R.asIdeal) ^ (nR R * V.rank * W.rank) := by
    have hnn : 0 ≤ ∏ R ∈ T, Real.sqrt (Ideal.absNorm R.asIdeal) ^ (nR R * V.rank * W.rank) :=
      Finset.prod_nonneg fun _ _ => pow_nonneg (Real.sqrt_nonneg _) _
    rw [← Real.sqrt_sq hnn]
    congr 1
    unfold flipIdx
    rw [← Finset.prod_pow]
    push_cast
    refine Finset.prod_congr rfl fun R _ => ?_
    unfold HeightOneSpectrum.maxPowDividing
    have hsN : Real.sqrt (Ideal.absNorm R.asIdeal : ℝ) ^ 2 = (Ideal.absNorm R.asIdeal : ℝ) :=
      Real.sq_sqrt (Nat.cast_nonneg _)
    rw [map_pow, Nat.cast_pow]
    conv_lhs => rw [← hsN]
    simp only [hnR, ← pow_mul]
    ring_nf
  obtain ⟨s, hs⟩ := hodd
  have hfac : flipScal χW V W T pd x = ∏ R ∈ T, ((((χ.val R : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm R.asIdeal) : ℝ) : ℂ)) ^
      (nR R * V.rank) * (((Ideal.absNorm R.asIdeal ^ (nR R * V.rank * (s + 1)) : ℕ) : ℂ))⁻¹) := by
    unfold flipScal
    rw [hcx', hsq, ← Finset.prod_inv_distrib, Complex.ofReal_prod, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun R _ => ?_
    have hs0 : ((Real.sqrt (Ideal.absNorm R.asIdeal) : ℝ) : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero, Real.sqrt_ne_zero']
      exact_mod_cast Nat.pos_of_ne_zero (hN0 R)
    have h2 : ((Real.sqrt (Ideal.absNorm R.asIdeal) : ℝ) : ℂ) ^ 2 = ((Ideal.absNorm R.asIdeal : ℕ) : ℂ) := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      push_cast
      rfl
    rw [inv_inv, Complex.ofReal_pow, Nat.cast_pow, ← h2, hs, mul_pow, ← pow_mul]
    field_simp
    ring
  rw [hfac]
  exact prod_mem fun R hR => O.mul_mem (O.pow_mem (hval R hR) _) (hO _ (Nat.Coprime.pow_left _ (hNl R hR)))
