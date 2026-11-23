import Mathlib
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.NefRR
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverLaUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RealTowerGeometricAgreement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.NefPolarizationStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RealTowerNefGeneralStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SectionsGenericIndicators
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TowerComponentsCompatibleLawsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericFrameComponentBoundStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithmeticDegreePositiveHermStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformNormSectionCountStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TowerWeightOfZeroStatement
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Plug

theorem count_le {K R Om Ω : Type} [Field K] [NumberField K] [AddCommGroup R] [Module K R] [Field Om] [Algebra K Om]
    [Field Ω] [CharZero Ω] (φ : Om →+* Ω) (V : Submodule K R) (ev : R →ₗ[K] Om)
    (hinj : ∀ v ∈ V, ev v = 0 → v = 0) {d : ℕ} (hd : 0 < d) (f : Fin d → Ω)
    (hf : ∀ a : Fin d → Om, ∑ i, φ (a i) * f i = 0 → a = 0) (w : Ω) (hw : w ≠ 0) (L : AddSubgroup Ω)
    (hL : FiniteDimensional ℚ (Submodule.span ℚ (L : Set Ω)))
    (hmem : ∀ v ∈ V, ∀ i, ∃ N : ℕ, 0 < N ∧ (N : Ω) * (w * φ (ev v) * f i) ∈ L) :
    Cardinal.toENat (Module.rank K V) * ((Module.finrank ℚ K * d : ℕ) : ℕ∞) ≤
      ((Module.finrank ℚ (Submodule.span ℚ (L : Set Ω)) : ℕ) : ℕ∞) := by
  classical
  haveI : CharZero Om := charZero_of_injective_algebraMap (algebraMap K Om).injective
  let bK := Module.finBasis ℚ K
  let ψ : K →+* Ω := φ.comp (algebraMap K Om)
  have hmemW : ∀ v ∈ V, ∀ i, w * φ (ev v) * f i ∈ Submodule.span ℚ (L : Set Ω) := by
    intro v hv i
    obtain ⟨N, hN, hs⟩ := hmem v hv i
    have h1 : (N : Ω) * (w * φ (ev v) * f i) ∈ Submodule.span ℚ (L : Set Ω) := Submodule.subset_span hs
    have h2 := Submodule.smul_mem _ ((N : ℚ)⁻¹) h1
    have hN' : (N : Ω) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    have e : ((N : ℚ)⁻¹) • ((N : Ω) * (w * φ (ev v) * f i)) = w * φ (ev v) * f i := by
      rw [Rat.smul_def]; push_cast; field_simp
    rwa [e] at h2
  have key : ∀ (J : Type) [Fintype J] (v : J → V), LinearIndependent K v →
      Fintype.card J * (Module.finrank ℚ K * d) ≤ Module.finrank ℚ (Submodule.span ℚ (L : Set Ω)) := by
    intro J _ v hv
    let e : J × Fin (Module.finrank ℚ K) × Fin d → Submodule.span ℚ (L : Set Ω) := fun x =>
      ⟨w * φ (ev ((bK x.2.1) • (v x.1 : R))) * f x.2.2, hmemW _ (V.smul_mem _ (v x.1).2) _⟩
    have hli : LinearIndependent ℚ e := by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      have hg' : ∑ x, (g x : Ω) * (w * φ (ev (bK x.2.1 • (v x.1 : R))) * f x.2.2) = 0 := by
        have h0 := congrArg Subtype.val hg
        simpa [Rat.smul_def, e] using h0
      let c : J → Fin d → K := fun a i => ∑ b, (g (a, b, i) : K) * bK b
      let s : Fin d → R := fun i => ∑ a, c a i • (v a : R)
      have hs : ∀ i, s i ∈ V := fun i => Submodule.sum_mem _ fun a _ => V.smul_mem _ (v a).2
      have hphi : ∀ i, φ (ev (s i)) = ∑ a, (∑ b, (g (a, b, i) : Ω) * ψ (bK b)) * φ (ev (v a)) := by
        intro i
        simp only [s, c, map_sum, map_smul, Algebra.smul_def, map_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        simp [ψ, map_ratCast]
      have hterm : ∀ a b i, (g (a, b, i) : Ω) * (w * φ (ev (bK b • (v a : R))) * f i) =
          w * ((g (a, b, i) : Ω) * ψ (bK b) * φ (ev (v a)) * f i) := by
        intro a b i
        simp only [map_smul, Algebra.smul_def, map_mul, ψ, RingHom.comp_apply]
        ring
      have hsum : w * ∑ i, φ (ev (s i)) * f i = 0 := by
        rw [← hg', Fintype.sum_prod_type]
        simp only [Fintype.sum_prod_type, hterm, hphi, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_comm
      have hA : (fun i => ev (s i)) = 0 := hf _ ((mul_eq_zero.1 hsum).resolve_left hw)
      have hs0 : ∀ i, s i = 0 := fun i => hinj _ (hs i) (congrFun hA i)
      have hc : ∀ a i, c a i = 0 := by
        intro a i
        refine Fintype.linearIndependent_iff.1 hv (fun a => c a i) ?_ a
        apply Subtype.ext
        simpa [s] using hs0 i
      rintro ⟨a, b, i⟩
      refine Fintype.linearIndependent_iff.1 bK.linearIndependent (fun b => g (a, b, i)) ?_ b
      simpa [c, Rat.smul_def] using hc a i
    have h3 := hli.fintype_card_le_finrank
    simpa [Fintype.card_prod, mul_assoc] using h3
  have hpos : 0 < Module.finrank ℚ K * d := Nat.mul_pos Module.finrank_pos hd
  have hrank : Module.rank K V ≤ (Module.finrank ℚ (Submodule.span ℚ (L : Set Ω)) : ℕ) := by
    refine rank_le fun s hs => ?_
    have := key s _ hs
    rw [Fintype.card_coe] at this
    exact (Nat.le_mul_of_pos_right _ hpos).trans this
  haveI : Module.Finite K V := Module.rank_lt_aleph0_iff.1 (hrank.trans_lt (Cardinal.nat_lt_aleph0 _))
  rw [← Module.finrank_eq_rank, Cardinal.toENat_nat]
  have := key _ (Module.finBasis K V) (Module.finBasis K V).linearIndependent
  rw [Fintype.card_fin] at this
  exact_mod_cast this

theorem growth_le_of_shift (D : ℕ) (r : ℕ → ℕ∞) (Rk : ℕ → ℕ) (δ k₀ : ℕ) (hδ : 0 < δ)
    (h : ∀ τ, r τ * (δ : ℕ∞) ≤ (Rk (τ + k₀) : ℕ∞)) (L : ℝ)
    (hL : Tendsto (fun τ : ℕ => (D.factorial : ℝ) * (Rk τ : ℝ) / (τ : ℝ) ^ D) atTop (𝓝 L)) :
    GlobalTheory.CompHt.growth D r ≤ ENNReal.ofReal (L / δ) := by
  have hδ' : (δ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hδ.ne'
  let c : ℕ → ℝ := fun τ => (D.factorial : ℝ) * (Rk (τ + k₀) : ℝ) / (((τ + k₀ : ℕ) : ℝ)) ^ D *
    ((((τ + k₀ : ℕ) : ℝ) / τ) ^ D) / δ
  have h1 : Tendsto (fun τ : ℕ => (((τ + k₀ : ℕ) : ℝ) / τ) ^ D) atTop (𝓝 1) := by
    have h2 : Tendsto (fun τ : ℕ => 1 + (k₀ : ℝ) / τ) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)
    have h3 : Tendsto (fun τ : ℕ => (((τ + k₀ : ℕ) : ℝ) / τ)) atTop (𝓝 1) := by
      rw [add_zero] at h2
      refine h2.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with τ hτ
      have : (τ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hτ.ne'
      push_cast
      field_simp
    simpa using h3.pow D
  have hc : Tendsto c atTop (𝓝 (L / δ)) := by
    have h4 := (hL.comp (tendsto_add_atTop_nat k₀)).mul h1
    rw [mul_one] at h4
    exact h4.div_const _
  have hle : ∀ᶠ τ : ℕ in atTop, (D.factorial : ENNReal) * (r τ : ENNReal) / (τ : ENNReal) ^ D ≤ ENNReal.ofReal (c τ) := by
    filter_upwards [eventually_gt_atTop 0] with τ hτ
    have hτ' : (0 : ℝ) < τ := Nat.cast_pos.2 hτ
    have hk : (0 : ℝ) < ((τ + k₀ : ℕ) : ℝ) := Nat.cast_pos.2 (by omega)
    obtain ⟨m, hm⟩ : ∃ m : ℕ, r τ = m := by
      refine ENat.ne_top_iff_exists.1 (fun ht => ?_) |>.imp fun _ e => e.symm
      have := h τ
      rw [ht, ENat.top_mul (Nat.cast_ne_zero.2 hδ.ne')] at this
      exact ENat.coe_ne_top _ (top_le_iff.1 this)
    have hmle : m * δ ≤ Rk (τ + k₀) := by
      have := h τ
      rw [hm] at this
      exact_mod_cast this
    have e1 : (D.factorial : ENNReal) * (r τ : ENNReal) / (τ : ENNReal) ^ D =
        ENNReal.ofReal ((D.factorial : ℝ) * m / (τ : ℝ) ^ D) := by
      rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_pow hτ'.le, hm]
      simp
    rw [e1]
    refine ENNReal.ofReal_le_ofReal ?_
    have e2 : c τ = (D.factorial : ℝ) * (Rk (τ + k₀) : ℝ) / δ / (τ : ℝ) ^ D := by
      simp only [c, div_pow]
      field_simp
    rw [e2]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    have hd : (0 : ℝ) < δ := Nat.cast_pos.2 hδ
    rw [le_div_iff₀ hd, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact_mod_cast hmle
  calc GlobalTheory.CompHt.growth D r ≤ limsup (fun τ => ENNReal.ofReal (c τ)) atTop := limsup_le_limsup hle
    _ = ENNReal.ofReal (L / δ) := ((ENNReal.tendsto_ofReal hc).limsup_eq)

section Deg

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Cmp

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem mInt_combLine_expand {P J : Ideal (MRing ι)} {e : ℕ} (R : AnLogRes P J e) {σ : Type} [Fintype σ]
    (L : σ → HermLine ι) (hL : ∀ a, IsSmoothHerm (L a)) (n : Fin e → σ → ℤ) :
    mInt R.A (fun j => potOf R (PB.combLine L (n j))) (fun _ => 1) =
      ∑ w : Fin e → σ, (∏ i, (n i (w i) : ℝ)) * mInt R.A (fun j => potOf R (L (w j))) (fun _ => 1) := by
  have hP : ∀ a, IsPotential R.A (potOf R (L a)) := fun a => isPotential_potOf R (hL a)
  have h1 : mInt R.A (fun j => potOf R (PB.combLine L (n j))) (fun _ => 1) =
      mInt R.A (fun j => sumPot (fun a => (n j a : ℝ)) fun a => potOf R (L a)) (fun _ => 1) := by
    refine mInt_congr _ (fun j y hy => ?_) fun _ => rfl
    refine ReciprocityTheory.ChartRestriction.G.Geo.maDens_congr fun i => ?_
    filter_upwards [((R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U ((R.A.chart j).symm y))).mem_nhds
      ⟨hy, R.mem_U _⟩] with y' hy'
    have hm := (R.mem _ _ hy'.2).1
    show Real.log (∏ a, (L a).h _ ^ n i a) = ∑ a, (n i a : ℝ) * Real.log ((L a).h _)
    rw [Real.log_prod fun a _ => (zpow_pos ((L a).pos _ hm) _).ne']
    exact Finset.sum_congr rfl fun a _ => Real.log_zpow _ _
  rw [h1, (GlobalTheory.T.monge_ampere_integral_multilinear_expansion e R.X R.A σ Set.univ (fun a => potOf R (L a)) (fun j a => (n j a : ℝ))
    (fun _ => 1) (fun j => by simp) (fun a x _ => isC2At_of_isPotential _ (hP a) x)
    (fun w => mIntegrableCont _ _ (fun i => hP _) _ continuous_const)).2]

theorem ptsIntegral_combLine {P : Ideal (MRing ι)} {e : ℕ} (hE : ResExistsStatement)
    (hP : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar P (e + 1)) {σ : Type} [Fintype σ] (L : σ → HermLine ι)
    (hL : ∀ a, IsSmoothHerm (L a)) (n : Fin e → σ → ℤ) :
    ptsIntegral P (pot fun i => Top.combLine L (n i)) (fun _ => 1) =
      ∑ w : Fin e → σ, (∏ i, (n i (w i) : ℝ)) * ptsIntegral P (pot fun i => L (w i)) (fun _ => 1) := by
  obtain ⟨J, ⟨R⟩⟩ := exists_anLogRes hE hP
  have hs : ∀ i, IsSmoothHerm (Top.combLine L (n i)) := fun i => by
    rw [← PB.combLine_eq_top]; exact isSmoothHerm_combLine hL _
  rw [ptsIntegral_one_eq_mInt hE resBridge R hP hs]
  simp_rw [← PB.combLine_eq_top]
  rw [mInt_combLine_expand R L hL n]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [ptsIntegral_one_eq_mInt hE resBridge R hP fun i => hL (w i)]

variable {Ψ : Type} [Fintype Ψ] {N : ℕ}

theorem geomDeg_combLine_one (hI : PB.Inputs) (M : Top.RootModel Ψ N) (n : Option (Ψ × Fin N) → ℤ)
    (W : Ideal (MRing M.ι)) (hW : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar W 2) :
    geomDeg W (Top.combLine (M.line 1) n) 1 = ∑ j, (n j : ℝ) * geomDeg W (M.line 1 j) 1 := by
  have h := ptsIntegral_combLine (e := 1) hI.resExists hW (M.line 1) (Top.RealGeo.line_smooth M) fun _ => n
  refine h.trans ?_
  refine Fintype.sum_equiv (Equiv.funUnique (Fin 1) _) _ _ fun w => ?_
  have e : (fun i => M.line 1 (w i)) = fun _ => M.line 1 (w default) := funext fun i => by
    rw [Subsingleton.elim i default]
  simp only [Equiv.funUnique_apply, Finset.univ_unique, Finset.prod_singleton, e]
  rfl

theorem geomDeg_combLine_top (hI : PB.Inputs) (M : Top.RootModel Ψ N) (n : Option (Ψ × Fin N) → ℤ) (hn : n none = 0) :
    geomDeg M.P (Top.combLine (M.line 1) n) (Top.dimFl Ψ N) =
      M.δ * M.geoFun (Top.toA ((∑ r, MvPolynomial.C (n (some r) : ℝ) * MvPolynomial.X r) ^ Top.dimFl Ψ N)) := by
  classical
  have hδ : (M.δ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 M.δ_pos.ne'
  have e1 : Top.toA ((∑ r, MvPolynomial.C (n (some r) : ℝ) * MvPolynomial.X r) ^ Top.dimFl Ψ N) =
      (∑ o, MvPolynomial.C (n o : ℝ) * MvPolynomial.X o : Top.RPA Ψ N) ^ Top.dimFl Ψ N := by
    simp only [Top.toA, map_pow, map_sum, map_mul, MvPolynomial.rename_C, MvPolynomial.rename_X, Fintype.sum_option, hn,
      Int.cast_zero, map_zero, zero_mul, zero_add]
  rw [e1, Top.RealGeo.geoFun_pow, Finset.mul_sum]
  have h := ptsIntegral_combLine (e := Top.dimFl Ψ N) hI.resExists M.arith (M.line 1) (Top.RealGeo.line_smooth M)
    fun _ => n
  refine h.trans (Finset.sum_congr rfl fun w _ => ?_)
  obtain ⟨J, ⟨R⟩⟩ := exists_anLogRes hI.resExists M.arith
  by_cases hw : ∃ j, w j = none
  · obtain ⟨j, hj⟩ := hw
    have : ∏ i, (n (w i) : ℝ) = 0 := Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj, hn])
    simp [this]
  · have hc : (∑ j, Finsupp.single (w j) (1 : ℕ)) none = 0 := by
      rw [Finsupp.finset_sum_apply]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [Finsupp.single_apply, if_neg fun h => hw ⟨j, h⟩]
    rw [Top.RealGeo.geoMono_word hI M R w, hc, pow_zero, mul_one,
      ptsIntegral_one_eq_mInt hI.resExists resBridge R M.arith fun i => Top.RealGeo.line_smooth M (w i)]
    field_simp
    rfl
end Deg

theorem chartLatNm_mul {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    {y : (Σ k, ι k) → Ω} {a : K → ℤ} {τ₁ τ₂ : ℕ} {s t : Ω} (hs : s ∈ chartLatNm y a τ₁)
    (ht : t ∈ chartLatNm y a τ₂) : s * t ∈ chartLatNm y a (τ₁ + τ₂) := by
  intro c hc
  have e : s * t * ∏ k, y ⟨k, c k⟩ ^ (-(((τ₁ + τ₂ : ℕ) : ℤ) * a k)) =
      (s * ∏ k, y ⟨k, c k⟩ ^ (-((τ₁ : ℤ) * a k))) * (t * ∏ k, y ⟨k, c k⟩ ^ (-((τ₂ : ℤ) * a k))) := by
    have : ∀ k, y ⟨k, c k⟩ ^ (-(((τ₁ + τ₂ : ℕ) : ℤ) * a k)) =
        y ⟨k, c k⟩ ^ (-((τ₁ : ℤ) * a k)) * y ⟨k, c k⟩ ^ (-((τ₂ : ℤ) * a k)) := fun k => by
      rw [← zpow_add₀ (hc k)]; congr 1; push_cast; ring
    simp only [this, Finset.prod_mul_distrib]
    ring
  rw [e]
  exact mul_mem (hs c hc) (ht c hc)

theorem chartLatNm_smul_one {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    {y : (Σ k, ι k) → Ω} {a : K → ℤ} {n : ℕ} {s : Ω} (hs : s ∈ chartLatNm y ((n : ℤ) • a) 1) :
    s ∈ chartLatNm y a n := by
  intro c hc
  have := hs c hc
  simpa using this

theorem degOf_nsmul {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (u : GlobalTheory.AllWt.Weight Dw) (n : ℕ) :
    degOf RM (n • u) = (n : ℤ) • degOf RM u := by
  have h : ∀ j, nOf (n • u) j = (n : ℤ) * nOf u j := fun j => by
    cases j with
    | none => simp [nOf]
    | some r => simp [nOf]
  funext k
  show (∑ j, nOf (n • u) j • (RM.line 1 j).a) k = (n : ℤ) * (∑ j, nOf u j • (RM.line 1 j).a) k
  simp only [h, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem nonempty_cmType {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) :
    Nonempty (CMType H) := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  by_cases h : τ (H.rt : E) = H.rt0
  · exact ⟨⟨τ, h⟩⟩
  · exact ⟨⟨conjEmb τ, Small.conjEmb_rt_of_ne h⟩⟩

theorem dimFl_pos {Ψ : Type} [Fintype Ψ] [Nonempty Ψ] {N : ℕ} (hN : 2 ≤ N) : 1 ≤ Top.dimFl Ψ N := by
  have h1 : 0 < Fintype.card Ψ := Fintype.card_pos
  have h2 : 1 ≤ N * (N - 1) / 2 := by
    obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 := ⟨N - 2, by omega⟩
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    simp only [Nat.add_sub_cancel, Nat.add_succ_sub_one]
    nlinarith
  exact Nat.mul_pos h1 h2

end GlobalTheory.CompanionTheory.Ar.Plug

theorem GlobalTheory.CompanionTheory.Ar.Plug.growth_le_vol_deg : GlobalTheory.CompanionTheory.Ar.Pub.NefRR → Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ x : ℝ, (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x) → ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : Top.GoodOrigin Y T) (κ : Comp Xo c ≃ T.Comp) (II : IntersectionSystem), CompOf o.toTowerOrigin κ → IsFullIntersectionSystem II → T.Proportional → T.T1 II → ∀ (Z : Comp Xo c) (u : GlobalTheory.AllWt.Weight Dw), (∀ τ, StrictAnti (u τ)) → GlobalTheory.CompHt.growthOn U Z (GlobalTheory.AllWt.wtOf Dw u 0) ≤ ENNReal.ofReal (T.vol (κ Z) * Top.flagDeg (reW u)) := by
  intro hRR hG E _ _ _ H Dw l Xo c r U h e hL x hx Y _ T o κ II hκ hII hP hT1 Z u hu
  have hIn : PB.Inputs := hG.2.2.2.2.2.2.2.2.2.1
  have hjp : T.j = Dw.p := o.toTowerOrigin.j_eq
  have hp : 1 ≤ Dw.p := hjp ▸ T.j_pos
  have hq : 1 ≤ Dw.q := by have := T.j_lt; omega
  obtain ⟨B, hB⟩ := exists_nat_gt (Top.bigB0 (reW u) 1)
  have hB' : Top.bigB0 (reW u) 1 < (B : ℝ) + 1 := hB.trans (lt_add_one _)
  obtain ⟨Fr, ⟨Rd⟩⟩ := GlobalTheory.T.tower_components_compatible_laws E H Dw l Xo c r U h e hL Y T o.toTowerOrigin κ hκ B Z
  have wt := GlobalTheory.T.tower_weight_of_zero E H Dw l Xo c (T.M B (κ Z)) u
  obtain ⟨-, -, wtn, wtc, -, wtd, -, wtw, -⟩ := wt
  have hW : Top.WeightHyp T.j (reW u) 1 := by rw [hjp]; exact wtw hp hq hu
  obtain ⟨k₀, R₀, f, -, -, hfs, hfi, hft⟩ :=
    GlobalTheory.T.generic_frame_component_bound hG E H Dw l Xo c h Y T o B (κ Z) Fr Z Rd II u 1 hII hT1 hW hB'

  have hinj : ∀ (G : WTZ E), G = (G.1, 0) → ∀ v ∈ GlobalTheory.AllWt.cuspOn U Z G, evL h Z v = 0 → v = 0 := by
    intro G hG0 v hv h0
    have hs : v ∈ Rec.secZ Xo c G.1 := by
      have hex : Formalism.L2.Pj.exZ Dw G = Rec.exZ Dw G.1 := by
        funext i
        cases i with
        | none => exact congrArg Prod.snd hG0
        | some x => rfl
      have h1 : v ∈ GlobalTheory.AllWt.secZ Xo c (Formalism.L2.Pj.exZ Dw G) := GlobalTheory.AllWt.cuspW_le_secZ G hv.1
      rw [hex] at h1
      refine ⟨h1.1, fun p t y y' hb => ?_⟩
      rw [h1.2 p t y y' hb]
      simp [Units.coe_prod]
    refine (GlobalTheory.CompanionTheory.Ar.Rec.sections_generic_indicators E H Dw l Xo c r U h e hL).1 G.1 v hs fun Z' => ?_
    by_cases hZ : Z' = Z
    · subst hZ; exact h0
    · exact GlobalTheory.AllWt.evC_eq_zero h hZ hv.2
  let M := T.M B (κ Z)
  letI : Algebra c.F M.Ω := (Rd.φ.comp (algebraMap c.F (Om Z))).toAlgebra
  haveI : CharZero M.Ω := charZero_of_injective_algebraMap (algebraMap c.F M.Ω).injective
  have hN2 : 2 ≤ Dw.p + Dw.q := by omega
  haveI := nonempty_cmType H
  have hD : 1 ≤ Top.dimFl (CMType H) (Dw.p + Dw.q) := dimFl_pos hN2
  have hsm : IsSmoothHerm (Top.combLine (M.line 1) (nOf u)) := by
    rw [← PB.combLine_eq_top]
    exact Cmp.isSmoothHerm_combLine (Top.RealGeo.line_smooth M) _
  have hdom : Top.Dominant (reW u) := fun τ a b hab => by
    have := (hu τ).antitone hab
    show (u τ b : ℝ) ≤ u τ a
    exact_mod_cast this
  have hnef : ∀ W, ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar W 2 → mCoordIdeal M.y ≤ W → 0 ≤ geomDeg W (Top.combLine (M.line 1) (nOf u)) 1 := by
    intro W hW hPW
    have h1 := (GlobalTheory.T.real_tower_nef_general GlobalTheory.T.nef_polarization hIn II hII _ _ T (Top.realOf o.toTowerOrigin) o.smooth o.flat B (κ Z)).1
      (reW u) hdom W hW hPW
    rw [geomDeg_combLine_one hIn M (nOf u) W hW]
    simpa only [wtc] using h1
  obtain ⟨hfin, hlim⟩ := GlobalTheory.T.section_count_tendsto_geomDeg hRR hG II hII M.K M.ι M.Ω M.y _ (Top.combLine (M.line 1) (nOf u)) hD M.arith
    M.birational hsm hnef
  have hgeo : geomDeg (mCoordIdeal M.y) (Top.combLine (M.line 1) (nOf u)) (Top.dimFl (CMType H) (Dw.p + Dw.q)) =
      M.δ * (T.vol (κ Z) * Top.flagDeg (reW u)) := by
    have e1 : (∑ r, MvPolynomial.C (nOf u (some r) : ℝ) * MvPolynomial.X r : Top.RP (CMType H) (Dw.p + Dw.q)) =
        Top.linRoot (reW u) := by
      simp only [Top.linRoot, nOf, reW, Int.cast_neg, map_neg, neg_mul, Finset.sum_neg_distrib, neg_neg]
    have := geomDeg_combLine_top hIn M (nOf u) rfl
    rw [e1] at this
    exact this.trans (by rw [hP.2.1 B (κ Z)]; rfl)
  have hδ : M.δ = Module.finrank ℚ c.F * (o.toTowerOrigin.Or B (κ Z)).Fl.deg := (o.toTowerOrigin.Or B (κ Z)).δ_eq
  have hd : 0 < (o.toTowerOrigin.Or B (κ Z)).Fl.deg := by
    have := M.δ_pos
    rw [hδ] at this
    exact Nat.pos_of_mul_pos_left this |> fun h => h
  have hgauge : ∀ v : GlobalTheory.AllWt.Weight Dw, gauge Rd v ≠ 0 := by
    intro v hv
    refine one_ne_zero (hft v 1 fun i => ?_)
    simp [trOf, hv]
  have hcount : ∀ τ : ℕ, Cardinal.toENat (Module.rank c.F (GlobalTheory.AllWt.cuspOn U Z (τ • GlobalTheory.AllWt.wtOf Dw u 0))) *
      ((M.δ : ℕ) : ℕ∞) ≤
      ((Module.finrank ℚ (Submodule.span ℚ (chartLatNm M.y (degOf M u) (τ + k₀) : Set M.Ω)) : ℕ) : ℕ∞) := by
    intro τ
    rw [hδ]
    refine count_le Rd.φ _ (evL h Z) (hinj _ ?_) hd f hfi (gauge Rd (τ • u)) (hgauge _) _ (hfin _) ?_
    · exact Prod.ext rfl (by simp [GlobalTheory.AllWt.wtOf_snd])
    · intro v hv i
      rw [wtn τ] at hv
      obtain ⟨N, hN, hs⟩ := GlobalTheory.T.uniform_norm_section_count hG E H Dw l Xo c r U h e hL x hx Y T o B (κ Z) Fr Z Rd (τ • u) v hv
      refine ⟨N, hN, ?_⟩
      have hs' : (N : M.Ω) * (gauge Rd (τ • u) * Rd.φ (evC h Z v)) ∈ chartLatNm M.y (degOf M u) τ :=
        chartLatNm_smul_one (by rw [← degOf_nsmul]; exact hs)
      have hf' : f i ∈ chartLatNm M.y (degOf M u) k₀ :=
        chartLatNm_smul_one (by rw [← degOf_nsmul]; exact (hfs i).1)
      have h1 := chartLatNm_mul hs' hf'
      have e2 : (N : M.Ω) * (gauge Rd (τ • u) * Rd.φ (evL h Z v) * f i) =
          (N : M.Ω) * (gauge Rd (τ • u) * Rd.φ (evC h Z v)) * f i := by
        rw [evL_apply]; ring
      rw [e2]
      exact h1
  have hfinal := growth_le_of_shift (Top.dimFl (CMType H) (Dw.p + Dw.q)) _ _ M.δ k₀ M.δ_pos hcount _ hlim
  rw [hgeo, mul_div_cancel_left₀ _ (Nat.cast_ne_zero.2 M.δ_pos.ne')] at hfinal
  rw [GlobalTheory.CompHt.growthOn, wtd]
  exact hfinal
