import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfFree
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DenseRangeUnits
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdditiveCharConductorExists

noncomputable section

namespace PositivityTheory.KCo

open NumberField IsDedekindDomain GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Filter Topology
open Formalism.L2.Host (IsUnitAt atFin)
open Neutral.B1 (Ideles localIdele)
open scoped Pointwise TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_level {w : HeightOneSpectrum (𝓞 E)} (f : (w.adicCompletion E)ˣ →* ℂˣ) (hf : Continuous fun x => (f x : ℂ)) :
    ∃ n : ℕ, ∀ x, IsUnitAt w x → Valued.v ((x : w.adicCompletion E) - 1) ≤ WithZero.exp (-(n : ℤ)) → f x = 1 := by
  have hc : Continuous fun a => ‖(f a : ℂ) - 1‖ := (hf.sub continuous_const).norm
  have h0 : {a : (w.adicCompletion E)ˣ | ‖(f a : ℂ) - 1‖ < 1 / 2} ∈ 𝓝 1 :=
    (isOpen_lt hc continuous_const).mem_nhds (by simp)
  rw [Units.isEmbedding_val₀.nhds_eq_comap, mem_comap] at h0
  obtain ⟨t, ht, hsub⟩ := h0
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.mp ht
  have hγ0 : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := by simp
  refine ⟨(1 - WithZero.log (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)).toNat, fun x hx hx1 => ?_⟩
  refine Units.ext (GlobalTheory.CharConductor.eq_one_of_pow_near_one fun m => ?_)
  rw [← Units.val_pow_eq_pow_val, ← map_pow]
  apply hsub
  apply hγ
  simp only [Set.mem_ofPred_eq, Valuation.restrict_lt_iff_lt_embedding, Units.val_pow_eq_pow_val, Units.val_one]
  have hx' : Valued.v (x : w.adicCompletion E) = 1 := hx
  have h1 : Valued.v ((x : w.adicCompletion E) ^ m - 1) ≤ Valued.v ((x : w.adicCompletion E) - 1) := by
    induction m with
    | zero => simp
    | succ m ih =>
      have e : (x : w.adicCompletion E) ^ (m + 1) - 1 = x ^ m * (x - 1) + (x ^ m - 1) := by ring
      rw [e]
      refine Valuation.map_add_le _ ?_ ih
      rw [map_mul, map_pow, hx', one_pow, one_mul]
  refine (h1.trans hx1).trans_lt ?_
  conv_rhs => rw [← WithZero.exp_log hγ0]
  exact WithZero.exp_lt_exp.mpr (by omega)

theorem valued_atFin (w : HeightOneSpectrum (𝓞 E)) (x : Eˣ) :
    Valued.v ((atFin w x : (w.adicCompletion E)ˣ) : w.adicCompletion E) = w.valuation E x := valued_alg w _

theorem exists_pow_eq_one {w : HeightOneSpectrum (𝓞 E)} (f : (w.adicCompletion E)ˣ →* ℂˣ) (hf : Continuous fun x => (f x : ℂ))
    (π : 𝓞 E) (x : Eˣ) (hx : (x : E) = π) (h : π ∉ w.asIdeal) : ∃ N : ℕ, 0 < N ∧ f (atFin w x) ^ N = 1 := by
  obtain ⟨n, hn⟩ := exists_level f hf
  have hu : w.valuation E (π : E) = 1 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]; exact HeightOneSpectrum.intValuation_eq_one_iff.2 h
  haveI : Finite (𝓞 E ⧸ w.asIdeal ^ n) := Ideal.finiteQuotientOfFreeOfNeBot _ (pow_ne_zero _ w.ne_bot)
  have key : ∀ i j : ℕ, i < j → Ideal.Quotient.mk (w.asIdeal ^ n) (π ^ i) = Ideal.Quotient.mk _ (π ^ j) →
      ∃ N : ℕ, 0 < N ∧ f (atFin w x) ^ N = 1 := fun i j hij e => by
    refine ⟨j - i, by omega, ?_⟩
    rw [← map_pow, ← map_pow]
    refine hn _ (by rw [IsUnitAt, valued_atFin, Units.val_pow_eq_pow_val, map_pow, hx, hu, one_pow]) ?_
    have h1 : π ^ i * (π ^ (j - i) - 1) ∈ w.asIdeal ^ n := by
      rw [mul_sub, ← pow_add, Nat.add_sub_cancel' hij.le, mul_one]
      exact Ideal.Quotient.eq.1 e.symm
    have h2 : w.valuation E ((π ^ i * (π ^ (j - i) - 1) : 𝓞 E) : E) ≤ WithZero.exp (-(n : ℤ)) := by
      rw [HeightOneSpectrum.valuation_of_algebraMap]
      exact (HeightOneSpectrum.intValuation_le_pow_iff_mem _ _ _).2 h1
    have h3 : ((atFin w (x ^ (j - i)) : (w.adicCompletion E)ˣ) : w.adicCompletion E) - 1 =
        algebraMap E _ ((π : E) ^ (j - i) - 1) := by
      rw [map_sub, map_one, ← hx, ← Units.val_pow_eq_pow_val]; rfl
    rw [h3, valued_alg]
    simpa [hu] using h2
  obtain ⟨i, j, hij, e⟩ := Finite.exists_ne_map_eq_of_infinite fun k : ℕ => Ideal.Quotient.mk (w.asIdeal ^ n) (π ^ k)
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h e
  · exact key j i h e.symm

variable (F E) in

def finId : Ideles E →* (AF F ⊗[F] E)ˣ :=
  (ofFinIdele F E).comp ((Units.map (finAdEquiv F E).symm.toRingHom.toMonoidHom).comp
    (Units.map (RingHom.snd (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E)).toMonoidHom))

theorem continuous_finId : Continuous (finId F E) := by
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (AF F ⊗[F] E) := IsModuleTopology.toContinuousAdd (AF F) _
  have h : Continuous fun y : AdeleRing (𝓞 E) E => 1 - extZero F E 1 + extZero F E ((finAdEquiv F E).symm y.2) :=
    continuous_const.add (continuous_extZero.comp (continuous_finAdEquiv_symm.comp continuous_snd))
  exact Units.continuous_iff.2 ⟨h.comp Units.continuous_val, h.comp Units.continuous_coe_inv⟩

def finPr (x : Eˣ) : Ideles E :=
  Units.map (M := E) { toFun := fun y => ((1 : InfiniteAdeleRing E), algebraMap E (FiniteAdeleRing (𝓞 E) E) y)
                       map_one' := Prod.ext rfl (map_one _)
                       map_mul' := fun a b => Prod.ext (mul_one 1).symm (map_mul _ a b) } x

theorem fin_eq_one {χ : Chr F E} (hχ : Continuous χ) (x : Eˣ) (h : ∀ w, locChar χ w (atFin w x) = 1) :
    χ (finId F E (finPr x)) = 1 :=
  GlobalTheory.FrobDense.eq_one_of_local (χ.comp (finId F E)) (hχ.comp continuous_finId) _ rfl fun w =>
    Circle.ext (congrArg Units.val (h w))

theorem arch_eq_one {χ : Chr F E} (hχ : IsHecke F E χ) {τ : ∀ w : InfinitePlace F, EmbOver E w} {m : InfinitePlace F → ℤ}
    (hm : HasExp τ χ m) (x : Eˣ) (h : ∀ w, locChar χ w (atFin w x) = 1) :
    ∏ w, ((τ w).1 x / ‖(τ w).1 x‖) ^ m w = 1 := by
  set a := Units.map (inclR (F := F) (AF F)).toMonoidHom x with ha
  set f := finId F E (finPr x) with hf
  have hfv : (f : AF F ⊗[F] E) = 1 - extZero F E 1 + extZero F E ((finAdEquiv F E).symm (algebraMap E _ (x : E))) := rfl
  have i1 : infTens F E f = 1 := by
    rw [hfv, map_add, map_sub, map_one, infTens_extZero, infTens_extZero, sub_zero, add_zero]
  have f1 : finTens F E f = finTens F E a := by
    rw [hfv, map_add, map_sub, map_one, finTens_extZero, finTens_extZero, sub_self, zero_add, RingEquiv.symm_apply_eq]
    exact ((toFinAd_tmul 1 (x : E)).trans (by rw [map_one, one_mul])).symm
  have e : ((a / f : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * f = a := by rw [← Units.val_mul, div_mul_cancel]
  have i2 : infTens F E (a / f : (AF F ⊗[F] E)ˣ) = infTens F E a := by
    have := congrArg (infTens F E) e
    rwa [map_mul, i1, mul_one] at this
  have f2 : finTens F E (a / f : (AF F ⊗[F] E)ˣ) = 1 := by
    have := congrArg (finTens F E) e
    rw [map_mul, f1] at this
    exact ((a.isUnit.map (finTens F E)).mul_left_inj).1 (this.trans (one_mul _).symm)
  have hA : At (evI F) (((a / f : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1) := fun u hu => by
    have hu1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (hu.trans (map_zero _).symm)
    rw [Algebra.smul_def]
    refine tens_ext ?_ ?_
    · have : infTens F E (algebraMap (AF F) (AF F ⊗[F] E) u) = 0 := by
        change u.1 ⊗ₜ[F] (1 : E) = 0
        rw [hu1, TensorProduct.zero_tmul]
      rw [map_mul, this, zero_mul, map_zero]
    · rw [map_mul, map_sub, f2, map_one, sub_self, mul_zero, map_zero]
  have hc : ∀ w (y : AF F ⊗[F] E), compInf F E w y =
      Algebra.TensorProduct.map (GlobalTheory.AutFunCompare.evW w) (AlgHom.id F E) (infTens F E y) := fun w y => by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => rfl
    | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]
  have hp : ∀ w, piInf (τ w) ((a / f : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) = (τ w).1 x := fun w => by
    change infEmb (τ w) (compInf F E w _) = _
    rw [hc, i2, ← hc]
    change infEmb (τ w) (evInf F w 1 ⊗ₜ[F] (x : E)) = _
    rw [map_one, infEmb_tmul, map_one, one_mul]
  have := hm _ hA
  rw [map_div, hχ.2 x, fin_eq_one hχ.1 x h, div_one] at this
  simp only [hp] at this
  exact this.symm

theorem hasExp_div {χ χ' : Chr F E} {τ : ∀ w : InfinitePlace F, EmbOver E w} {m m' : InfinitePlace F → ℤ}
    (h : HasExp τ χ m) (h' : HasExp τ χ' m') : HasExp τ (χ / χ') (m - m') := fun z hz => by
  rw [MonoidHom.div_apply, Circle.coe_div, h z hz, h' z hz, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  have h0 : piInf (τ w) (z : AE F E) ≠ 0 := (z.isUnit.map _).ne_zero
  rw [Pi.sub_apply, zpow_sub₀ (div_ne_zero h0 (by simpa using h0))]

theorem not_prod [IsGalois ℚ E] (h : IsCMExt F E σ) {v : Pl F} (hv : SplitsFully E v) (P : Ideal (𝓞 E)) [P.IsMaximal]
    [P.LiesOver v.asIdeal] (π : 𝓞 E) (hπ : π ∈ P) (h0 : π ≠ 0) (honly : ∀ Q : Ideal (𝓞 E), Q.IsPrime → π ∈ Q → Q = P)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (m : InfinitePlace F → ℤ) (hm : ∀ w, 0 < m w) :
    ∏ w, ((τ w).1 π / ‖(τ w).1 π‖) ^ m w ≠ 1 := by
  intro e
  obtain ⟨w₀⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hg : ∀ w, ∃ g : Gal(E/ℚ), ∀ x, (τ w₀).1 (g x) = (τ w).1 x := fun w => by
    obtain ⟨g, hg⟩ := ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := ℚ) (τ w₀).1 (τ w).1 (Subsingleton.elim _ _)
    exact ⟨g.symm, fun x => RingHom.congr_fun hg x⟩
  choose g hg using hg
  lift m to InfinitePlace F → ℕ using fun w => (hm w).le
  have hz : ∀ w, (τ w).1 (π : E) ≠ 0 := fun w => (map_ne_zero _).2 (RingOfIntegers.coe_ne_zero_iff.2 h0)
  have e2 : ∏ w, ((τ w).1 (π : E)) ^ m w = ∏ w, ((τ w).1 (σ π)) ^ m w := by
    have e3 : ∏ w, ((τ w).1 (π : E) / (τ w).1 (σ π)) ^ m w = 1 := by
      have := congrArg (· ^ 2) e
      simp only [one_pow, ← Finset.prod_pow, zpow_natCast] at this
      rw [← this]
      refine Finset.prod_congr rfl fun w _ => ?_
      rw [← pow_mul, mul_comm, pow_mul, h.2.2.2]
      congr 1
      rw [div_pow, ← Complex.ofReal_pow, ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, sq, mul_div_mul_left _ _ (hz w)]
      rfl
    simp only [div_pow, Finset.prod_div_distrib] at e3
    exact (div_eq_one_iff_eq (Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ (by
      rw [h.2.2.2]; exact star_ne_zero.2 (hz w)))).1 e3
  have e4 : ∏ w, (g w • π) ^ m w = ∏ w, ((g w * conjQ h) • π) ^ m w := by
    apply RingOfIntegers.ext
    apply (τ w₀).1.injective
    simp only [map_prod, map_pow]
    refine Eq.trans ?_ (e2.trans ?_) <;> refine Finset.prod_congr rfl fun w _ => ?_
    · exact congrArg (· ^ m w) (hg w π)
    · exact congrArg (· ^ m w) (hg w (σ π)).symm
  have g0 : g w₀ = 1 := AlgEquiv.ext fun x => (τ w₀).1.injective (hg w₀ x)
  have h1 : ∏ w, (g w • π) ^ m w ∈ P := Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ w₀)) (by
    rw [g0, one_smul]; exact Ideal.pow_mem_of_mem _ hπ _ (Int.natCast_pos.1 (hm w₀)))
  rw [e4] at h1
  obtain ⟨w, -, hw⟩ := Ideal.IsPrime.prod_mem_iff.1 h1
  have h2 : π ∈ (g w * conjQ h)⁻¹ • P := by
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_inv]
    exact Ideal.IsPrime.mem_of_pow_mem inferInstance _ hw
  have h3 := inv_eq_one.1 (eq_one_of_smul hv P _ (honly _ ((inferInstance : P.IsPrime).smul _) h2))
  have h4 : ∀ x, (τ w₀).1 x = (τ w).1 (σ x) := fun x => by
    rw [← hg w, ← conjQ_apply h, ← AlgEquiv.mul_apply, h3]; rfl
  have h5 : w₀ = w := InfinitePlace.embedding_injective _ (RingHom.ext fun a => by
    rw [← (τ w₀).2, ← (τ w).2, RingHom.comp_apply, RingHom.comp_apply, h4, σ.commutes])
  subst h5
  obtain ⟨x, hx⟩ := exists_cm_conj_ne h
  exact hx ((τ w₀).1.injective (h4 x)).symm

theorem nu_statement : NuSt := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v hv t e
  classical
  haveI := hT.base.galois
  set w := splitPrime t with hw
  have hC := hT.chars
  have hH : IsHecke F E X.ν := ⟨hC.heckeα.1.div' hC.heckeβ.1, fun x => by
    rw [Chars.ν, MonoidHom.div_apply, hC.heckeα.2, hC.heckeβ.2, div_one]⟩
  have hU : ∀ u ∉ above E (X.T : Set (Pl F)), UnrAt X.ν u := fun u hu => by
    rw [Chars.ν, div_eq_mul_inv]; exact (hC.unrα u hu).mul (hC.unrβ u hu).inv
  have hwU : UnrAt X.ν w := hU w (by
    change w.under (𝓞 F) ∉ (X.T : Set (Pl F))
    rw [splitPrime_under]; exact hv.1)

  obtain ⟨ϖ, hϖ⟩ := v.valuation_exists_uniformizer F
  have hϖ0 : ϖ ≠ 0 := fun h => by rw [h, map_zero] at hϖ; exact WithZero.exp_ne_zero hϖ.symm
  let p : Eˣ := Units.mk0 (algebraMap F E ϖ) ((map_ne_zero _).2 hϖ0)
  have hp : w.valuation E p = WithZero.exp (-1 : ℤ) := by
    rw [← valued_apply_eq_valuation]; exact (valued_apply_algebraMap t ϖ).trans hϖ
  have hp1 : locChar X.ν w (atFin w p) = 1 := by
    have := DFunLike.congr_fun e (Units.mk0 (algebraMap F (Fv F v) ϖ) ((map_ne_zero _).2 hϖ0))
    rw [MonoidHom.one_apply] at this
    rw [← this]
    exact congrArg _ (Units.ext (complMap_algebraMap (splitPrime_under t) ϖ).symm)
  have hall : ∀ x : Eˣ, locChar X.ν w (atFin w x) = 1 := fun x => by
    have h0 : w.valuation E x ≠ 0 := (map_ne_zero _).2 x.ne_zero
    have := hwU (atFin w (x * p ^ WithZero.log (w.valuation E x))) (by
      rw [IsUnitAt, valued_atFin, Units.val_mul, map_mul, Units.val_zpow_eq_zpow_val, map_zpow₀, hp, ← WithZero.exp_zsmul]
      conv_lhs => enter [1]; rw [← WithZero.exp_log h0]
      rw [← WithZero.exp_add]; simp)
    rwa [map_mul, map_mul, map_zpow, map_zpow, hp1, one_zpow, mul_one] at this

  obtain ⟨k, hk, π₀, hπ₀⟩ : ∃ k : ℕ, 0 < k ∧ ∃ π₀ : 𝓞 E, w.asIdeal ^ k = Ideal.span {π₀} := by
    let I : nonZeroDivisors (Ideal (𝓞 E)) := ⟨w.asIdeal, mem_nonZeroDivisors_of_ne_zero w.ne_bot⟩
    have h1 : ClassGroup.mk0 (I ^ Nat.card (ClassGroup (𝓞 E))) = 1 := by rw [map_pow, pow_card_eq_one']
    have h2 := (ClassGroup.mk0_eq_one_iff (I ^ Nat.card (ClassGroup (𝓞 E))).2).1 h1
    exact ⟨_, Nat.card_pos, h2.generator, h2.span_singleton_generator.symm⟩
  have hne : π₀ ≠ 0 := fun h => pow_ne_zero k w.ne_bot (by rw [hπ₀, h]; simp)
  have only : ∀ Q : Ideal (𝓞 E), Q.IsPrime → π₀ ∈ Q → Q = w.asIdeal := fun Q hQ h =>
    (w.isMaximal.eq_of_le hQ.ne_top (Ideal.IsPrime.le_of_pow_le (n := k) (hπ₀ ▸ (Ideal.span_singleton_le_iff_mem _).2 h))).symm
  have hin : π₀ ∈ w.asIdeal := Ideal.pow_le_self hk.ne' (hπ₀ ▸ Ideal.mem_span_singleton_self _)
  let x : Eˣ := Units.mk0 (π₀ : E) (RingOfIntegers.coe_ne_zero_iff.2 hne)
  have loc : ∀ u : HeightOneSpectrum (𝓞 E), ∃ N : ℕ, 0 < N ∧ locChar X.ν u (atFin u x) ^ N = 1 := fun u => by
    by_cases hu : u = w
    · exact ⟨1, one_pos, by rw [hu, hall, one_pow]⟩
    · exact exists_pow_eq_one _ (continuous_locChar hH.1 u) π₀ x rfl fun h => hu (HeightOneSpectrum.ext (only _ u.isPrime h))
  choose N hN hN1 using loc
  have hfin : (above E (X.T : Set (Pl F))).Finite :=
    (X.T.finite_toSet.biUnion fun u _ => (Formalism.L2.Host.aboveF (L := E) F u).finite_toSet).subset fun u hu =>
      Set.mem_biUnion hu (mem_aboveF.2 rfl)
  set M := ∏ u ∈ hfin.toFinset, N u with hM
  have hM0 : 0 < M := Finset.prod_pos fun u _ => hN u
  have h1 := arch_eq_one hH (hasExp_div hC.expα hC.expβ) (x ^ M) fun u => by
    rw [map_pow, map_pow]
    by_cases hu : u ∈ hfin.toFinset
    · obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem N hu
      rw [hM, hc, pow_mul, hN1, one_pow]
    · by_cases huw : u = w
      · rw [huw, hall, one_pow]
      · rw [hU u (by simpa using hu) _ (by
          rw [IsUnitAt, valued_atFin]
          change u.valuation E (algebraMap (𝓞 E) E π₀) = 1
          rw [HeightOneSpectrum.valuation_of_algebraMap]
          exact HeightOneSpectrum.intValuation_eq_one_iff.2 fun h => huw (HeightOneSpectrum.ext (only _ u.isPrime h))), one_pow]
  haveI := w.isMaximal
  refine not_prod hT.base.cm hv.2 w.asIdeal (π₀ ^ M) (Ideal.pow_mem_of_mem _ hin _ hM0) (pow_ne_zero _ hne)
    (fun Q hQ h => only Q hQ (hQ.mem_of_pow_mem _ h)) B.emb (B.mα - B.mβ) (fun u => ?_) ?_
  · have := hT.geo.kappa u
    rw [Pi.sub_apply]; omega
  · simpa [x] using h1

end PositivityTheory.KCo
