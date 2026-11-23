import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverLaUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LabelSigBijective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntMemModelSmall
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProdZpowLe
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AllWeightSectionsCompat
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
import Development.AbelianVarietyTheory.Definitions.RegularCharts.NotFamConstZero
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AlgebraicApproximationCompleteDvrStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntegralFrameSubalgebraRelayStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameChartNonzeroDenominatorStatement
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Plug.FinTr.Approx

section Help

theorem exists_loc {R K L : Type} [CommRing R] [IsDomain R] [Field K] [Field L] (i : R →+* K)
    (hi : Function.Injective i) (g : R) (hg : g ≠ 0) (χ : R →+* L) (hχ : χ g ≠ 0) :
    ∃ (A : Subring K) (ev : A →+* L) (hA : ∀ r, i r ∈ A), (i g)⁻¹ ∈ A ∧ (∀ r, ev ⟨i r, hA r⟩ = χ r) ∧
      ∀ x : A, ∃ (a : R) (k : ℕ), ev x * χ g ^ k = χ a := by
  have hig : i g ≠ 0 := (map_ne_zero_iff i hi).2 hg
  let large₂ := Localization.Away g
  let Φ : large₂ →+* K := IsLocalization.Away.lift g (isUnit_iff_ne_zero.2 hig)
  let Ψ : large₂ →+* L := IsLocalization.Away.lift g (isUnit_iff_ne_zero.2 hχ)
  have hΦ : ∀ r, Φ (algebraMap R large₂ r) = i r := fun r => IsLocalization.Away.lift_eq g _ r
  have hΨ : ∀ r, Ψ (algebraMap R large₂ r) = χ r := fun r => IsLocalization.Away.lift_eq g _ r
  have hsurj : ∀ x : large₂, ∃ (a : R) (k : ℕ), x * algebraMap R large₂ g ^ k = algebraMap R large₂ a := by
    intro x
    obtain ⟨⟨a, ⟨s, k, rfl⟩⟩, h⟩ := IsLocalization.surj (Submonoid.powers g) x
    exact ⟨a, k, by simpa using h⟩
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨a, k, h⟩ := hsurj x
    have h1 := congrArg Φ h
    rw [map_mul, hx, zero_mul, hΦ] at h1
    have ha : a = 0 := hi (by rw [← h1, map_zero])
    have hu : IsUnit (algebraMap R large₂ g ^ k) := (IsLocalization.Away.algebraMap_isUnit g).pow k
    rw [ha, map_zero] at h
    exact (hu.mul_left_eq_zero).1 h
  let e : large₂ ≃+* Φ.range := RingEquiv.ofBijective Φ.rangeRestrict
    ⟨fun a b h => hinj (congrArg Subtype.val h), Φ.rangeRestrict_surjective⟩
  have hA : ∀ r, i r ∈ Φ.range := fun r => ⟨algebraMap R large₂ r, hΦ r⟩
  have hev : ∀ x : large₂, (Ψ.comp e.symm.toRingHom) (e x) = Ψ x := fun x => by
    simp
  have hev' : ∀ r, (Ψ.comp e.symm.toRingHom) ⟨i r, hA r⟩ = χ r := fun r => by
    have : (⟨i r, hA r⟩ : Φ.range) = e (algebraMap R large₂ r) := Subtype.ext (hΦ r).symm
    rw [this, hev, hΨ]
  refine ⟨Φ.range, Ψ.comp e.symm.toRingHom, hA, ?_, hev', fun x => ?_⟩
  · obtain ⟨v, hv⟩ := IsLocalization.Away.algebraMap_isUnit (x := g) (S := large₂) |>.exists_right_inv
    refine ⟨v, ?_⟩
    have := congrArg Φ hv
    rw [map_mul, hΦ, map_one] at this
    exact eq_inv_of_mul_eq_one_right this
  · obtain ⟨a, k, h⟩ := hsurj (e.symm x)
    refine ⟨a, k, ?_⟩
    have := congrArg Ψ h
    rw [map_mul, map_pow, hΨ, hΨ] at this
    exact this

theorem inv_mem_of_mul {K : Type} [Field K] {A : Subring K} {a b g : K} (ha : a ≠ 0) (hb : b ∈ A) (hg : g⁻¹ ∈ A)
    (hne : g ≠ 0) (h : a * b = g) : a⁻¹ ∈ A := by
  have : a⁻¹ = b * g⁻¹ := by
    rw [← h]
    have hb0 : b ≠ 0 := fun h0 => hne (by rw [← h, h0, mul_zero])
    field_simp
  rw [this]
  exact A.mul_mem hb hg

theorem vV_units_prod {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
    [IsFractionRing V K] {I : Type} (s : Finset I) (t : I → Kˣ) (e : I → ℤ) :
    vV V (((∏ i ∈ s, t i ^ e i : Kˣ)) : K) = ∑ i ∈ s, e i * vV V ((t i : Kˣ) : K) := by
  classical
  have hz : ∀ (u : Kˣ) (m : ℤ), vV V (((u ^ m : Kˣ)) : K) = m * vV V (u : K) := by
    intro u m
    simp only [vV]
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, WithZero.log_zpow]
    ring_nf
  induction s using Finset.induction_on with
  | empty =>
    have : vV V (1 : K) = 0 := by simp [vV]
    simpa using this
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Units.val_mul,
      vV_mul (Units.ne_zero _) (Units.ne_zero _), hz, ih]

theorem vV_eq_of_close {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
    [IsFractionRing V K] {a a' : K} (ha : a ≠ 0) (h : a' = a ∨ vV V a < vV V (a' - a)) : a' ≠ 0 ∧ vV V a' = vV V a := by
  by_cases he : a' = a
  · subst he
    exact ⟨ha, rfl⟩
  have h : vV V a < vV V (a' - a) := h.resolve_left he
  have hneg : ∀ x : K, vV V (-x) = vV V x := fun x => by simp [vV]
  have hd : a' - a ≠ 0 := sub_ne_zero.2 he
  have h0 : a' ≠ 0 := by
    intro h0
    rw [h0, zero_sub, hneg] at h
    exact lt_irrefl _ h
  refine ⟨h0, ?_⟩
  have h1 := min_le_vV_add (V := V) ha hd (by rwa [add_sub_cancel])
  have h2 := min_le_vV_add (V := V) h0 (neg_ne_zero.2 hd) (by rwa [← sub_eq_add_neg, sub_sub_cancel])
  rw [add_sub_cancel] at h1
  rw [← sub_eq_add_neg, sub_sub_cancel, hneg] at h2
  rcases min_le_iff.1 h1 with h1 | h1 <;> rcases min_le_iff.1 h2 with h2 | h2 <;> omega

theorem nval_transfer {T T' : CDVR} {e₀ e' : ℕ} (he₀ : 0 < e₀) (he' : 0 < e') {I : Type} [Fintype I] (ex : I → ℤ)
    (t₀ : I → T.Frˣ) (t' : I → T'.Frˣ)
    (hvt : ∀ i, ex i ≠ 0 → vV T'.V ((t' i : T'.Frˣ) : T'.Fr) * (e₀ : ℤ) = (e' : ℤ) * vV T.V ((t₀ i : T.Frˣ) : T.Fr))
    {a a' : T.Fr} (φ : T.Fr →+* T'.Fr) (hφ : ∀ x : T.Fr, x ≠ 0 → vV T'.V (φ x) * (e₀ : ℤ) = (e' : ℤ) * vV T.V x)
    (ha : a ≠ 0) (hclose : a' = a ∨ vV T.V a < vV T.V (a' - a)) :
    nval T'.V e' (((∏ i, t' i ^ ex i : T'.Frˣ) : T'.Fr) * φ a') = nval T.V e₀ (((∏ i, t₀ i ^ ex i : T.Frˣ) : T.Fr) * a) := by
  obtain ⟨ha'0, hva⟩ := vV_eq_of_close ha hclose
  have hsum : (e₀ : ℤ) * vV T'.V (((∏ i, t' i ^ ex i : T'.Frˣ)) : T'.Fr) =
      (e' : ℤ) * vV T.V (((∏ i, t₀ i ^ ex i : T.Frˣ)) : T.Fr) := by
    rw [vV_units_prod, vV_units_prod, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h0 : ex i = 0
    · rw [h0]; simp
    · have := hvt i h0
      linear_combination (ex i) * this
  have hW' := Units.ne_zero (∏ i, t' i ^ ex i : T'.Frˣ)
  have hW := Units.ne_zero (∏ i, t₀ i ^ ex i : T.Frˣ)
  have hφa : φ a' ≠ 0 := (map_ne_zero φ).2 ha'0
  have key : vV T'.V (((∏ i, t' i ^ ex i : T'.Frˣ) : T'.Fr) * φ a') * (e₀ : ℤ) =
      (e' : ℤ) * vV T.V (((∏ i, t₀ i ^ ex i : T.Frˣ) : T.Fr) * a) := by
    rw [vV_mul hW' hφa, vV_mul hW ha, ← hva]
    have := hφ _ ha'0
    linear_combination hsum + this
  rw [nval_of_ne (mul_ne_zero hW' hφa), nval_of_ne (mul_ne_zero hW ha)]
  have he'' : (0 : ℝ) < e' := by exact_mod_cast he'
  have he₀' : (0 : ℝ) < e₀ := by exact_mod_cast he₀
  have keyR : (vV T'.V (((∏ i, t' i ^ ex i : T'.Frˣ) : T'.Fr) * φ a') : ℝ) * e₀ =
      e' * (vV T.V (((∏ i, t₀ i ^ ex i : T.Frˣ) : T.Fr) * a) : ℝ) := by exact_mod_cast key
  congr 1
  rw [div_eq_div_iff he''.ne' he₀'.ne']
  linarith

theorem close_of_le {T : CDVR} {a a' : T.Fr} {n' : ℕ} (hn : (vV T.V a + 1).toNat ≤ n')
    (h : a' = a ∨ (n' : ℤ) ≤ vV T.V (a' - a)) : a' = a ∨ vV T.V a < vV T.V (a' - a) := by
  rcases h with h1 | h1
  · exact Or.inl h1
  · refine Or.inr ?_
    have h3 : vV T.V a + 1 ≤ ((vV T.V a + 1).toNat : ℤ) := Int.self_le_toNat _
    have h4 : (((vV T.V a + 1).toNat : ℕ) : ℤ) ≤ (n' : ℤ) := by exact_mod_cast hn
    omega

theorem alg_map {K L : Type} [Field K] [Field L] [iK : Algebra ℤ K] [iL : Algebra ℤ L] (f : K →+* L) {x : K}
    (h : IsAlgebraic ℤ x) : IsAlgebraic ℤ (f x) := by
  obtain rfl : iK = Ring.toIntAlgebra K := Subsingleton.elim _ _
  obtain rfl : iL = Ring.toIntAlgebra L := Subsingleton.elim _ _
  exact h.algHom f.toIntAlgHom

theorem alg_of_loc {L : Type} [Field L] [Algebra ℤ L] {x a g : L} {k : ℕ} (ha : IsAlgebraic ℤ a) (hg : IsAlgebraic ℤ g) (hg0 : g ≠ 0)
    (hx : x * g ^ k = a) : IsAlgebraic ℤ x := by
  have e1 : x = a * (g ^ k)⁻¹ := by
    rw [← hx]
    field_simp
  rw [e1]
  exact ha.mul (hg.pow k).inv

end Help

set_option maxHeartbeats 2000000 in

theorem approx_main : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Z : Comp Xo c) (u : GlobalTheory.AllWt.Weight Dw) (f : Rul Xo c), f ∈ GlobalTheory.AllWt.secZ Xo c (GlobalTheory.AllWt.exOf Dw u 0) → ∀ (B' : Finset (Om Z)) (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e₀ : ℕ), OverLa la T.V io e₀ → ∀ y : IntFr Xo c T io, y.IsAlg → (letI := io.toAlgebra; GlobalTheory.AllWt.LiesOn Z y.1) → evI y f ≠ 0 → ∃ (T' : CDVR) (io' : c.F →+* T'.Fr) (e' : ℕ) (y' : IntFr Xo c T' io') (A : Subring (Om Z)) (ev : A →+* T'.Fr), OverLa la T'.V io' e' ∧ y'.IsAlg ∧ nval T'.V e' (evI y' f) = nval T.V e₀ (evI y f) ∧ (↑B' : Set (Om Z)) ⊆ A ∧ (∀ b ∈ B', b ≠ 0 → b⁻¹ ∈ A) ∧ (∀ x, IsAlgebraic ℤ (ev x)) ∧ FinTr.RegAt h Z io' A ev y'.1 := by
  intro hG E _ _ _ H Dw l Xo c r U h e hCL Y Z u f hf B' la T io e₀ ho y hy hLies hne
  letI := io.toAlgebra
  classical
  obtain ⟨hL, -, -, hAt⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  obtain ⟨C, ψ, z₀, t₀, hm, hb⟩ := hAt h T.Fr y.1
  have hZ : C.Z = Z := by
    have s₀ : Sp T.Fr := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum T.Fr)
    exact comp_eq_of_mem (hLies s₀) (liesOn_chart C hm hb s₀)
  subst hZ
  haveI := C.sm
  obtain ⟨g₀, hg₀, hReg⟩ := GlobalTheory.T.frame_chart_nonzero_denominator E H Dw l Xo c hL h C
  obtain ⟨F, n, hNear⟩ := GlobalTheory.T.integral_frame_subalgebra_relay hG E H Dw l Xo c hCL.intAll Y la T io e₀ ho hy y C.R C.y ψ z₀ t₀ hm hb
  let fS : C.R := evR Xo c f C.y
  have hz₀ : evR Xo c f z₀ = ψ fS := GlobalTheory.Reg.PChartModel.evR_map hL hf.1 ψ hm
  have hy₀ : evI y f = ((∏ i, t₀ i ^ GlobalTheory.AllWt.exOf Dw u 0 i : T.Frˣ) : T.Fr) * ψ fS := by
    rw [← hz₀]
    exact GlobalTheory.FlagTan.evR_frBor hf hb
  have hψf : ψ fS ≠ 0 := fun h0 => hne (by rw [hy₀, h0, mul_zero])
  choose na hna de hde hde0 hfr using C.frac
  let deR : Om C.Z → C.R := fun b => ⟨de b, hde b⟩
  let naR : Om C.Z → C.R := fun b => ⟨na b, hna b⟩
  let g₁ : C.R := ∏ b ∈ B', deR b
  let g₂ : C.R := ∏ b ∈ B'.filter (· ≠ 0), naR b
  let g : C.R := g₀ * g₁ * g₂
  have hde0' : ∀ b, deR b ≠ 0 := fun b hb0 => hde0 b (congrArg Subtype.val hb0)
  have hna0' : ∀ b, b ≠ 0 → naR b ≠ 0 := fun b hb0 h0 => by
    have h1 : na b = 0 := congrArg Subtype.val h0
    have := hfr b
    rw [h1] at this
    exact (mul_ne_zero hb0 (hde0 b)) this
  have hg₁ : g₁ ≠ 0 := Finset.prod_ne_zero_iff.2 fun b _ => hde0' b
  have hg₂ : g₂ ≠ 0 := Finset.prod_ne_zero_iff.2 fun b hb => hna0' b (Finset.mem_filter.1 hb).2
  have hg : g ≠ 0 := mul_ne_zero (mul_ne_zero hg₀ hg₁) hg₂
  let n' : ℕ := max n (vV T.V (ψ fS) + 1).toNat
  obtain ⟨ψ₁, hψ₁c, hψ₁a, hψ₁n, hψ₁g⟩ := GlobalTheory.T.algebraic_approximation_complete_dvr c.F C.R T hy io ψ.toRingHom
    (RingHom.ext fun a => ψ.commutes a) (insert fS F) n' g hg
  let ψ' : C.R →ₐ[c.F] T.Fr := { ψ₁ with commutes' := fun a => RingHom.congr_fun hψ₁c a }
  have hψ' : ∀ x, ψ' x = ψ₁ x := fun _ => rfl
  obtain ⟨z', hz'⟩ := hL.bc _ _ ψ' C.y
  obtain ⟨T', io', e', y', ho', hy', hrest⟩ := hNear ψ' (fun s hs => by
    rcases hψ₁n s (Finset.mem_insert_of_mem hs) with h1 | h1
    · exact Or.inl h1
    · refine Or.inr (le_trans ?_ h1)
      exact_mod_cast le_max_left _ _) z' hz'
  letI := io'.toAlgebra
  obtain ⟨φ, z'', t', hφ, hb', hvφ, hvt⟩ := hrest
  let χ : C.R →+* T'.Fr := φ.toRingHom.comp ψ₁
  have hχg : χ g ≠ 0 := (map_ne_zero φ.toRingHom).2 hψ₁g
  obtain ⟨A, ev, hA, hgA, hevχ, hevx⟩ := exists_loc C.R.val.toRingHom Subtype.val_injective g hg χ hχg
  have hAr : ∀ r : C.R, (r : Om C.Z) ∈ A := hA
  have hgne : ((g : C.R) : Om C.Z) ≠ 0 := fun h0 => hg (Subtype.ext h0)
  have hgA' : ((g : C.R) : Om C.Z)⁻¹ ∈ A := hgA
  have hdvd : ∀ a b : C.R, a ≠ 0 → a * b = g → (a : Om C.Z)⁻¹ ∈ A := fun a b ha hab =>
    inv_mem_of_mul (fun h0 => ha (Subtype.ext h0)) (hAr b) hgA' hgne (congrArg Subtype.val hab)
  have hdeA : ∀ b ∈ B', (de b)⁻¹ ∈ A := fun b hb0 => by
    obtain ⟨w, hw⟩ := Finset.dvd_prod_of_mem deR hb0
    exact hdvd (deR b) (g₀ * w * g₂) (hde0' b) (by
      show deR b * (g₀ * w * g₂) = g₀ * g₁ * g₂
      rw [show g₁ = deR b * w from hw]; ring)
  have hnaA : ∀ b ∈ B', b ≠ 0 → (na b)⁻¹ ∈ A := fun b hb0 hb1 => by
    obtain ⟨w, hw⟩ := Finset.dvd_prod_of_mem naR (show b ∈ B'.filter (· ≠ 0) from Finset.mem_filter.2 ⟨hb0, hb1⟩)
    exact hdvd (naR b) (g₀ * g₁ * w) (hna0' b hb1) (by
      show naR b * (g₀ * g₁ * w) = g₀ * g₁ * g₂
      rw [show g₂ = naR b * w from hw]; ring)
  have hg₀A : ((g₀ : C.R) : Om C.Z)⁻¹ ∈ A := hdvd g₀ (g₁ * g₂) hg₀ (by
    show g₀ * (g₁ * g₂) = g₀ * g₁ * g₂
    ring)
  let ψ₂ : C.R →ₐ[c.F] T'.Fr := φ.comp ψ'
  have hz'' : FrMap ψ₂ C.y z'' := frMap_trans _ _ _ _ φ _ _ _ hz' hφ
  refine ⟨T', io', e', y', A, ev, ho', hy', ?_, ?_, ?_, ?_, ?_⟩
  · have hyv : evI y' f = ((∏ i, t' i ^ GlobalTheory.AllWt.exOf Dw u 0 i : T'.Frˣ) : T'.Fr) * φ (ψ₁ fS) := by
      have h1 : evR Xo c f z'' = ψ₂ fS := GlobalTheory.Reg.PChartModel.evR_map hL hf.1 ψ₂ hz''
      have h2 : evR Xo c f y'.1 = ((∏ i, t' i ^ GlobalTheory.AllWt.exOf Dw u 0 i : T'.Frˣ) : T'.Fr) * evR Xo c f z'' :=
        GlobalTheory.FlagTan.evR_frBor hf hb'
      rw [h1] at h2
      exact h2
    rw [hyv, hy₀]
    refine nval_transfer ho.1 ho'.1 _ t₀ t' (fun i hi => ?_) φ.toRingHom hvφ hψf
      (close_of_le (le_max_right _ _) (hψ₁n fS (Finset.mem_insert_self _ _)))
    rcases i with _ | ⟨τ, i⟩
    · exact absurd (show GlobalTheory.AllWt.exOf Dw u 0 none = 0 by
        show (GlobalTheory.AllWt.wtOf Dw u 0).2 = 0
        rw [GlobalTheory.AllWt.wtOf_snd]; simp) hi
    · exact hvt τ i
  · intro b hb0
    have : b = na b * (de b)⁻¹ := by
      rw [← hfr b]
      field_simp [hde0 b]
    rw [this]
    exact A.mul_mem (hAr (naR b)) (hdeA b hb0)
  · intro b hb0 hb1
    have : b⁻¹ = de b * (na b)⁻¹ := by
      rw [← hfr b]
      have := hde0 b
      field_simp
    rw [this]
    exact A.mul_mem (hAr (deR b)) (hnaA b hb0 hb1)
  · intro x
    obtain ⟨a, k, hx⟩ := hevx x
    have hχa : ∀ a, IsAlgebraic ℤ (χ a) := fun a => alg_map φ.toRingHom (hψ₁a a)
    exact alg_of_loc (hχa a) (hχa g) hχg hx
  · exact hReg A hAr hg₀A T'.Fr io' ev ψ₂ (fun r => (hevχ r).symm) z'' y'.1 t' hz'' hb'

end GlobalTheory.CompanionTheory.Ar.Plug.FinTr.Approx
