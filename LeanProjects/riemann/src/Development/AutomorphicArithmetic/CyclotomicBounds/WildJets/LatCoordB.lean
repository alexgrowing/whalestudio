import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicValuationThetaKernelJetBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VwNatCastNonneg
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JetKapIff
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMulAddEqOneOfNotMem
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TensorMapDescent
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.ThreeForms
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section SlopeTestRemainingChoices

variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ}

private theorem lcb_mem_colLat_one (x : Fin n → K) :
    x ∈ colLat (1 : GL (Fin n) K) ↔ ∀ a, x a ∈ (1 : Submodule (𝓞 K) K) := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨j, rfl⟩ := hz
      intro a
      simp only [Units.val_one, Matrix.one_apply]
      split_ifs
      · exact Submodule.mem_one.2 ⟨1, map_one _⟩
      · exact zero_mem _
    | zero => intro a; exact zero_mem _
    | add y z _ _ hy hz => intro a; exact add_mem (hy a) (hz a)
    | smul c y _ hy => intro a; exact Submodule.smul_mem _ c (hy a)
  · intro hx
    choose r hr using fun a => Submodule.mem_one.1 (hx a)
    have : x = ∑ j, r j • fun a => ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a j := by
      funext a
      simp only [Finset.sum_apply, Pi.smul_apply, Units.val_one, Matrix.one_apply, Algebra.smul_def, mul_ite, mul_zero,
        mul_one, Finset.sum_ite_eq, Finset.mem_univ, if_true, hr]
    rw [this]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

private theorem lcb_emb_int (φ : E →+* K) {x : E} (hx : x ∈ (1 : Submodule (𝓞 E) E)) :
    φ x ∈ (1 : Submodule (𝓞 K) K) := by
  obtain ⟨y, rfl⟩ := Submodule.mem_one.1 hx
  have hint : IsIntegral ℤ (φ (algebraMap (𝓞 E) E y)) := (RingOfIntegers.isIntegral_coe y).map φ.toIntAlgHom
  exact Submodule.mem_one.2 ⟨⟨_, (mem_integralClosure_iff ℤ _).2 hint⟩, rfl⟩

private theorem lcb_dot {x y : Fin n → K} (hx : ∀ a, x a ∈ (1 : Submodule (𝓞 K) K))
    (hy : ∀ a, y a ∈ (1 : Submodule (𝓞 K) K)) : x ⬝ᵥ y ∈ (1 : Submodule (𝓞 K) K) := by
  refine Submodule.sum_mem _ fun a _ => ?_
  obtain ⟨r, hr⟩ := Submodule.mem_one.1 (hx a)
  obtain ⟨t, ht⟩ := Submodule.mem_one.1 (hy a)
  exact Submodule.mem_one.2 ⟨r * t, by rw [map_mul, hr, ht]⟩

omit [Fintype ι] in
private theorem lcb_basisAt (emb : ι → E →+* K) (τ : ι) (Λ : Submodule (𝓞 E) (Fin n → E)) (s : ℕ)
    (h1 : ∀ x ∈ Λ, ∀ a, (s • x) a ∈ (1 : Submodule (𝓞 E) E))
    (h2 : ∀ j, s • (Pi.single j 1 : Fin n → E) ∈ Λ) (w : HeightOneSpectrum (𝓞 K)) (hs : (s : 𝓞 K) ∉ w.asIdeal) :
    IsBasisAt w (dualFr (tauLat emb τ Λ)) 1 := by
  apply le_antisymm
  · refine GlobalTheory.TransLoc.localization_le_of_smul_mem w hs fun φ hφ => (lcb_mem_colLat_one _).2 fun j => ?_
    have := hφ _ (Submodule.subset_span ⟨_, h2 j, rfl⟩)
    convert this using 1
    have e : (fun a => emb τ ((s • (Pi.single j 1 : Fin n → E)) a)) = s • (Pi.single j 1 : Fin n → K) := by
      funext a
      by_cases h : a = j
      · subst h; simp
      · simp [h]
    change _ = φ ⬝ᵥ (fun a => emb τ ((s • (Pi.single j 1 : Fin n → E)) a))
    rw [e, dotProduct_smul, dotProduct_single, Nat.cast_smul_eq_nsmul]
    simp
  · refine GlobalTheory.TransLoc.localization_le_of_smul_mem w hs fun φ hφ x hx => ?_
    have hx' : s • x ∈ colLat (1 : GL (Fin n) K) := by
      induction hx using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨y, hy, rfl⟩ := hz
        refine (lcb_mem_colLat_one _).2 fun a => ?_
        have := lcb_emb_int (emb τ) (h1 y hy a)
        simpa using this
      | zero => simp
      | add y z _ _ hy hz => rw [smul_add]; exact Submodule.add_mem _ hy hz
      | smul c y _ hy => rw [smul_comm]; exact Submodule.smul_mem _ c hy
    have := lcb_dot ((lcb_mem_colLat_one _).1 hφ) ((lcb_mem_colLat_one _).1 hx')
    rw [dotProduct_smul] at this
    rw [smul_dotProduct, Nat.cast_smul_eq_nsmul]
    exact this

private theorem lcb_isLattice (Λ : Submodule (𝓞 E) (Fin n → E)) (s : ℕ) (hs : s ≠ 0)
    (h1 : ∀ x ∈ Λ, ∀ a, (s • x) a ∈ (1 : Submodule (𝓞 E) E))
    (h2 : ∀ j, s • (Pi.single j 1 : Fin n → E) ∈ Λ) : Submodule.IsLattice E Λ := by
  have hs' : (s : E) ≠ 0 := Nat.cast_ne_zero.2 hs
  constructor
  · let f : (Fin n → E) →ₗ[𝓞 E] (Fin n → E) := s • LinearMap.id
    have hf : Function.Injective f := by
      intro x y h
      have h' : (s : E) • x = (s : E) • y := by
        rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]; exact h
      exact smul_right_injective _ hs' h'
    refine Submodule.fg_of_fg_map_injective f hf ?_
    refine Submodule.FG.of_le (M := Fin n → E) (T := colLat (1 : GL (Fin n) E)) (Submodule.fg_span (Set.finite_range _)) ?_
    rintro _ ⟨x, hx, rfl⟩
    exact (lcb_mem_colLat_one _).2 (h1 x hx)
  · rw [eq_top_iff, ← (Pi.basisFun E (Fin n)).span_eq, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have : (Pi.basisFun E (Fin n)) j = (s : E)⁻¹ • (s • (Pi.single j 1 : Fin n → E)) := by
      rw [← Nat.cast_smul_eq_nsmul E, inv_smul_smul₀ hs', Pi.basisFun_apply]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (h2 j))

private theorem lcb_desc (φ : K →+* ℂ) (lam : ι → DomWeight n) (i : VVIdx lam) :
    ∃ F : VV K lam, (F : Pol K ι n) ∈ nabStd K lam ∧ GlobalTheory.CoefModel.mapVV φ lam F = bVV ℂ lam i := by
  have key : ∀ τ, ∃ f ∈ nablaSq (𝓞 K) n (lam τ), toK K _ f ∈ nablaSq K n (lam τ) ∧
      MvPolynomial.map φ (toK K _ f) = ssB ℂ (lam τ).natW (i τ) := by
    intro τ
    obtain ⟨k, sz, hsz, I, hsh, -, h⟩ := ((Formalism.GradedWeylDivisibility.sSBasis ℂ n n (lam τ).natW).choose_spec.2 (i τ)).2.2
    have e : toK K _ (Formalism.GradedWeylDivisibility.bideterminant (𝓞 K) sz hsz I) = Formalism.GradedWeylDivisibility.bideterminant K sz hsz I :=
      fk_map_bidet (algebraMap (𝓞 K) K) sz hsz I
    refine ⟨Formalism.GradedWeylDivisibility.bideterminant (𝓞 K) sz hsz I, ?_, ?_, ?_⟩
    · unfold nablaSq
      rw [← hsh]
      exact Formalism.GradedWeylDivisibility.bidetMem (𝓞 K) n n k sz hsz I
    · rw [e]
      unfold nablaSq
      rw [← hsh]
      exact Formalism.GradedWeylDivisibility.bidetMem K n n k sz hsz I
    · rw [e, fk_map_bidet]
      exact h.symm
  choose f hf hf' hf'' using key
  refine ⟨⟨ten fun τ => toK K _ (f τ), Submodule.subset_span ⟨_, hf', rfl⟩⟩,
    Submodule.subset_span ⟨_, fun τ => ⟨f τ, hf τ, rfl⟩, rfl⟩, Subtype.ext ?_⟩
  rw [GlobalTheory.CoefModel.mapVV_coe, bVV_coe]
  change MvPolynomial.map φ (ten fun τ => toK K _ (f τ)) = _
  rw [GlobalTheory.Proof.TensorMapDescent.map_ten]
  exact congrArg ten (funext hf'')

private theorem lcb_loc (emb : ι → E →+* K) (lam : ι → DomWeight n) (Λ : Submodule (𝓞 E) (Fin n → E)) (s : ℕ)
    (h1 : ∀ x ∈ Λ, ∀ a, (s • x) a ∈ (1 : Submodule (𝓞 E) E))
    (h2 : ∀ j, s • (Pi.single j 1 : Fin n → E) ∈ Λ) (w : HeightOneSpectrum (𝓞 K)) (hs : (s : 𝓞 K) ∉ w.asIdeal)
    (F : VV K lam) (hF : (F : Pol K ι n) ∈ nabStd K lam) : F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabAtr emb lam Λ) := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hs (by simp)
  have hL := lcb_isLattice Λ s hs0 h1 h2
  have h := (GlobalTheory.TransLoc.nabDelLoc_free_leVV.1 K ι n lam (fun τ => dualFr (tauLat emb τ Λ))
    (fun τ => GlobalTheory.DualLat.isLattice_dualFr _ (GlobalTheory.TauLat.tauLatLattice E K ι n emb τ Λ hL)) w 1
    (fun τ => lcb_basisAt emb τ Λ s h1 h2 w hs)).1
  change (F : Pol K ι n) ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabP lam fun τ => dualFr (tauLat emb τ Λ))
  rw [h]
  refine ⟨F, ⟨1, fun h1 => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1), by simpa using hF⟩, ?_⟩
  simp [actP, detTwK_one, trAct_one]

private theorem lcb_exists_vw (w : HeightOneSpectrum (𝓞 K)) (m : ℤ) : ∃ s : K, s ≠ 0 ∧ vw w s = m := by
  obtain ⟨ϖ, -, h0, h1, -⟩ := Formalism.DivisionValues.idxChange_unif (K := K) w
  have h0' : algebraMap (𝓞 K) K ϖ ≠ 0 := by simpa using h0
  refine ⟨algebraMap (𝓞 K) K ϖ ^ m, zpow_ne_zero _ h0', ?_⟩
  unfold vw
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · rw [zpow_natCast, ← FractionalIdeal.spanSingleton_pow, FractionalIdeal.count_pow, h1, mul_one]
  · rw [_root_.zpow_neg, zpow_natCast, ← FractionalIdeal.spanSingleton_inv, FractionalIdeal.count_inv,
      ← FractionalIdeal.spanSingleton_pow, FractionalIdeal.count_pow, h1, mul_one]

private theorem lcb_smul_loc {Z : Type} [AddCommGroup Z] [Module K Z] [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z]
    (w : HeightOneSpectrum (𝓞 K)) (M : Submodule (𝓞 K) Z) {a : K} (ha : a = 0 ∨ 0 ≤ vw w a) {x : Z}
    (hx : x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M) : a • x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M := by
  letI : StarRing K := starRingOfComm
  by_cases h0 : a = 0
  · rw [h0, zero_smul]; exact zero_mem _
  have h := Formalism.EigenvalueLevelCeiling.ThreeFormsAlt.mem_OO_of_vw_nonneg w h0 (ha.resolve_left h0)
  rw [Formalism.EigenvalueLevelCeiling.ThreeFormsAlt.mem_localization_iff_mem_span] at hx ⊢
  exact Submodule.smul_mem _ (⟨a, h⟩ : Formalism.EigenvalueLevelCeiling.ThreeFormsAlt.OO w) hx

end SlopeTestRemainingChoices

theorem UpperTheory.WildA.latCoordB :
    ∀ (D : D7) {n : ℕ} (lam : D.what₂.Tau → DomWeight n) (w : PlL D) (l : ℕ), l.Prime → (l : 𝓞 D.what₂.LL) ∈ w.asIdeal →
      ∀ Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E), Formalism.MainNotions.TaylorLogMetric.EqAt D l Λ (Formalism.MainNotions.StandardLatticesGL3.stdL D n) → ∀ (a : ℝ) (v : VV ℂ lam),
      (∀ i, LossLe w ((bVV ℂ lam).repr v i) a) → InLat lam w a Λ v := by
  intro D n lam w l _ hw Λ hΛ a v hv
  obtain ⟨s, hsl, h1, h2⟩ := hΛ
  have hs := GlobalTheory.GO.natCast_notMem_of_coprime hsl w hw
  have h1' : ∀ x ∈ Λ, ∀ b, (s • x) b ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
    intro x hx b
    have := Submodule.mem_pi.1 (h1 x hx) b (Set.mem_univ _)
    rwa [Nat.cast_smul_eq_nsmul] at this
  have h2' : ∀ j, s • (Pi.single j 1 : Fin n → D.host.E) ∈ Λ := by
    intro j
    rw [← Nat.cast_smul_eq_nsmul D.host.E]
    refine h2 _ (Submodule.mem_pi.2 fun b _ => ?_)
    rw [Pi.single_apply]
    split_ifs
    · exact Submodule.mem_one.2 ⟨1, map_one _⟩
    · exact zero_mem _
  choose y hy hy' using hv
  choose F hF hF' using lcb_desc D.what₂.embLL lam
  obtain ⟨s₀, hs₀, hv₀⟩ := lcb_exists_vw w ⌊a⌋
  have hmem : s₀ • ∑ i, y i • F i ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabAtr (labLL D) lam Λ) := by
    rw [Finset.smul_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [smul_smul]
    refine lcb_smul_loc w _ ?_ (lcb_loc (labLL D) lam Λ s h1' h2' w hs (F i) (hF i))
    by_cases h0 : y i = 0
    · left; rw [h0, mul_zero]
    · right
      have h := (hy' i).resolve_left h0
      have h' : -vw w (y i) ≤ ⌊a⌋ := Int.le_floor.2 (by push_cast; linarith)
      have e : vw w (s₀ * y i) = vw w s₀ + vw w (y i) := Formalism.DivisionValues.idxChange_cnt_mul w hs₀ h0
      rw [e, hv₀]
      linarith
  obtain ⟨c, hc, hcx⟩ := (Formalism.L2.Col.mem_locP w _ _).1 hmem
  have hc0 : algebraMap _ D.what₂.LL c ≠ 0 := by
    intro h
    have : c = 0 := by simpa using h
    exact hc (this ▸ w.asIdeal.zero_mem)
  refine ⟨∑ i, y i • F i, algebraMap _ D.what₂.LL c * s₀, ?_, mul_ne_zero hc0 hs₀, ?_, ?_⟩
  · rw [map_sum]
    simp only [LinearMap.map_smulₛₗ, hy, hF']
    exact (bVV ℂ lam).sum_repr v
  · have e : vw w (algebraMap _ D.what₂.LL c * s₀) = vw w (algebraMap _ D.what₂.LL c) + vw w s₀ :=
      Formalism.DivisionValues.idxChange_cnt_mul w hc0 hs₀
    have e0 : vw w (algebraMap _ D.what₂.LL c) = 0 := Formalism.DivisionValues.idxChange_cnt_unit w hc
    rw [e, e0, hv₀, zero_add]
    exact Int.floor_le a
  · rw [mul_smul, algebraMap_smul]
    exact hcx
