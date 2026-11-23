import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SplitLinearModelNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulCutSubOneEntry
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepThetaDatumHalfEqSmul
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPlaceChartOfSplitIdempotent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitSupportedUnitaryComponent
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNsmulActO
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitChartUniformiserAndResidueCard
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelativeLatticeVolumeOfDetValuation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryGroupCharacterOfHeckeChar

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitLinear

open GlobalTheory.PlaceModel GlobalTheory.PlaceDatum GlobalTheory.SplitHecke GlobalTheory.ThetaMove MeasureTheory

theorem exists_reps {G : Type} [AddCommGroup G] (A B : AddSubgroup G) [Finite (B ⧸ A.addSubgroupOf B)] :
    ∃ R : Finset G, R.card = A.relIndex B ∧ (∀ u ∈ R, u ∈ B) ∧ ∀ w ∈ B, ∃! v, v ∈ R ∧ w - v ∈ A := by
  classical
  letI := Fintype.ofFinite (B ⧸ A.addSubgroupOf B)
  have key : ∀ (w : B) (q : B ⧸ A.addSubgroupOf B), (w : G) - (q.out : B) ∈ A ↔ q = QuotientAddGroup.mk w := fun w q => by
    conv_rhs => rw [← q.out_eq', QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    rw [AddSubgroup.coe_add, AddSubgroup.coe_neg, neg_add_eq_sub]
  refine ⟨Finset.univ.image fun q : B ⧸ A.addSubgroupOf B => ((q.out : B) : G), ?_, fun u hu => ?_, fun w hw => ?_⟩
  · refine (Finset.card_image_of_injective _ fun _ _ h => Quotient.out_injective (Subtype.ext h)).trans ?_
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    rfl
  · obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hu
    exact q.out.2
  · refine ⟨_, ⟨Finset.mem_image_of_mem _ (Finset.mem_univ (QuotientAddGroup.mk ⟨w, hw⟩)), (key ⟨w, hw⟩ _).2 rfl⟩, ?_⟩
    rintro _ ⟨hu, h⟩
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hu
    rw [(key ⟨w, hw⟩ q).1 h]

theorem finite_quot {G : Type} [AddCommGroup G] (A B : AddSubgroup G) (hAB : A ≤ B) {N : ℕ}
    (tf : Function.Injective fun t : G => N • t) {R : Set G} (hR : R.Finite)
    (h : ∀ w ∈ B, ∃ r ∈ R, ∃ u ∈ A, N • w = r + N • u) : Finite (B ⧸ A.addSubgroupOf B) := by
  have hP : ((fun t : B => N • (t : G)) ⁻¹' R).Finite := hR.preimage (tf.comp Subtype.val_injective).injOn
  rw [← Set.finite_univ_iff]
  refine (hP.image QuotientAddGroup.mk).subset fun q _ => ?_
  obtain ⟨p, rfl⟩ := QuotientAddGroup.mk_surjective q
  obtain ⟨r, hr, u, hu, e⟩ := h _ p.2
  refine ⟨p - ⟨u, hAB hu⟩, ?_, ?_⟩
  · change N • ((p : G) - u) ∈ R
    rwa [smul_sub, e, add_sub_cancel_right]
  · rw [QuotientAddGroup.mk_sub, (QuotientAddGroup.eq_zero_iff (N := A.addSubgroupOf B) (⟨u, hAB hu⟩ : B)).2 hu, sub_zero]

variable {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ}

theorem isSBHalf_modul {e : AE D} {Λ : AddSubgroup (WO S T)}
    (hLL' : ∀ u ∈ Λ ⊓ half S T e, ∀ y ∈ Λ ⊓ half S T (cA D e), ψ (symplO S T u y) = 1)
    (hden : ∀ y ∈ half S T (cA D e), ∃ k : ℕ, 0 < k ∧ k • y ∈ Λ) {Φ : WO S T → ℂ} (s0 : IsSBHalf e Λ Φ) {y : WO S T}
    (hy' : IsHalf (cA D e) y) : IsSBHalf e Λ fun t => ψ (symplO S T t y) * Φ t := by
  have hy := (isHalf_iff S T).1 hy'
  have hb := isBichar_symplO S T ψ
  obtain ⟨k, hk, hk'⟩ := hden y hy
  obtain ⟨a1, k', hk1, a2, a3⟩ := s0
  refine ⟨fun t ht => a1 t (right_ne_zero_of_mul ht), k * k', Nat.mul_pos hk hk1, fun u hu hh t => ?_,
    fun t ht => ?_⟩
  · have e1 : Φ (t + (k * k') • u) = Φ t := by
      rw [mul_nsmul]
      exact a2 _ (nsmul_mem hu k) ((isHalf_iff S T).2 (nsmul_mem ((isHalf_iff S T).1 hh) k)) t
    have e2 : ψ (symplO S T ((k * k') • u) y) = 1 := by
      rw [mul_nsmul']
      exact (hb.nsmul k _ y).trans (hLL' _ (nsmul_mem (AddSubgroup.mem_inf.2 ⟨hu, (isHalf_iff S T).1 hh⟩) k') _
        ⟨hk', nsmul_mem hy k⟩)
    simp only [e1, symplO_add_left, AddChar.map_add_eq_mul, e2, mul_one]
  · rw [mul_nsmul']
    exact nsmul_mem (a3 t (right_ne_zero_of_mul ht)) k

theorem wave_act (e : AE D) (Λ : AddSubgroup (WO S T)) (g : GA D S) (h : GA D T) (x y : WO S T) :
    (fun t => wave (fun x y : WO S T => ψ (symplO S T x y)) (Λ ⊓ half S T e) x y (actO S T g⁻¹ h⁻¹ t)) =
      fun t => (fun t => ψ (symplO S T t (actO S T g h y)) * halfInd e Λ (actO S T g⁻¹ h⁻¹ t)) (t + actO S T g h x) := by
  funext t
  beta_reduce
  rw [← symplO_actO S T g⁻¹ h⁻¹, act_add, actO_inv_actO, actO_inv_actO, halfInd_eq_ind]
  rfl

theorem om_model_of_base : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (a : AE D) (f₀ : WO S T → ℂ) (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → IsSelfDualC S ΛS → IsSelfDualC T ΛT → a * a = a → infPart D a = 0 → IsThetaFunO ψ S T f₀ → IsPlaceModel ψ (symplO S T) (heisO ψ S T) a (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) 1 f₀ Tm → ∀ (g : GA D S) (h : GA D T) (c : ℂ), om (g, h) f₀ = c • Tm (fun t => halfInd a (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) (actO S T g⁻¹ h⁻¹ t)) → ∀ Φ, IsSBHalf a (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) Φ → om (g, h) (Tm Φ) = c • Tm fun t => Φ (actO S T g⁻¹ h⁻¹ t) := by
  intro D ψ S T χS χT om ΛS ΛT e f₀ Tm hW hS hT he hinf hf hTm g h c hc Φ hΦ
  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hW.std hS hT).1
  have hfin0 := GlobalTheory.LatFinMod.latO_finite_mod D S T _ _ hS.1.fg hT.1.fg fun _ => True
  have he' : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, he]
  have hsm : ∀ a : AE D, a * a = a → ∀ u ∈ latO S T ΛS ΛT fun _ => True,
      a • u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T a := fun a ha u hu =>
    AddSubgroup.mem_inf.2 ⟨GlobalTheory.SplitScalar.idem_smul_mem ha u hu, by rw [mem_half, smul_smul, ha]⟩
  have hden : ∀ y ∈ half S T (cA D e), ∃ k : ℕ, 0 < k ∧ k • y ∈ latO S T ΛS ΛT fun _ => True := fun y hy =>
    exists_nsmul_mem_latO' hS.1 hT.1 y (infPart_of_half (infPart_cA hinf) ((isHalf_iff S T).2 hy))
  have s0 := isSBHalf_actO hS.1 hT.1 g⁻¹ h⁻¹ (GlobalTheory.isSBHalf_halfInd e _)
  generalize latO S T ΛS ΛT (fun _ => True) = Λ at *
  have hLL' : ∀ u ∈ Λ ⊓ half S T e, ∀ y ∈ Λ ⊓ half S T (cA D e), ψ (symplO S T u y) = 1 := fun u hu y hy =>
    (hdual u (infPart_of_half hinf ((isHalf_iff S T).2 hu.2))).1 hu.1 y hy.1
  have hX : ∀ x ∈ half S T e, (∀ y ∈ Λ ⊓ half S T (cA D e), ψ (symplO S T x y) = 1) → x ∈ Λ ⊓ half S T e := by
    intro x hx h
    refine ⟨(hdual x (infPart_of_half hinf ((isHalf_iff S T).2 hx))).2 fun u hu => ?_, hx⟩
    have := h _ (hsm _ he' u hu)
    rwa [← symplO_smul, (mem_half S T).1 hx] at this
  have hfin : ∀ k : ℕ, 0 < k → ∃ R : Set (WO S T), R.Finite ∧
      ∀ t ∈ Λ ⊓ half S T e, ∃ r ∈ R, ∃ u ∈ Λ ⊓ half S T e, t = r + k • u := by
    intro k hk
    obtain ⟨R, hR, h⟩ := hfin0 k hk
    refine ⟨(fun r => e • r) '' R, hR.image _, fun t ht => ?_⟩
    obtain ⟨r, hr, u, hu, htr⟩ := h t ht.1
    refine ⟨_, ⟨r, hr, rfl⟩, e • u, hsm e he u hu, ?_⟩
    have := (mem_half S T).1 ht.2
    rw [← this, htr, smul_add, smul_comm e k u]
  have tf : ∀ k : ℕ, 0 < k → Function.Injective fun t : WO S T => k • t := fun k hk a b hab => by
    rw [← inv_smul_nsmul S T hk a, ← inv_smul_nsmul S T hk b]
    exact congrArg _ hab
  have hb := isBichar_symplO S T ψ
  have hm : Φ ∈ waveSpan (fun x y : WO S T => ψ (symplO S T x y)) (half S T e) (half S T (cA D e)) (Λ ⊓ half S T e) := by
    obtain ⟨h1, k, hk, h2, h3⟩ := hΦ
    exact mem_waveSpan hb inf_le_right inf_le_right hLL' hX (half_div S T e) (half_div S T _) tf hfin Φ
      (fun t ht => (isHalf_iff S T).1 (h1 t ht)) k hk (fun u hu => h2 u hu.1 ((isHalf_iff S T).2 hu.2))
      fun t ht => ⟨h3 t ht, (half S T e).nsmul_mem ((isHalf_iff S T).1 (h1 t ht)) _⟩
  clear hΦ
  induction hm using Submodule.span_induction with
  | mem _ hh =>
    obtain ⟨x, hx, y, hy, rfl⟩ := hh
    have hx' := (isHalf_iff S T).2 hx
    have hy' := (isHalf_iff S T).2 hy
    have hth := GlobalTheory.FinTranslate.isTheta_heisO_fin hW.std.1 (infPart_of_half (infPart_cA hinf) hy') hf
    rw [wave_act, GlobalTheory.SchrodSubst.placeModel_wave hLL' hden hTm hx' hy',
      hTm.trans _ (isSBHalf_modul hLL' hden s0 (isHalf_actO g h hy')) _ (isHalf_actO g h hx'),
      hTm.modul _ s0 _ (isHalf_actO g h hy'), hW.om_heis _ _ _ _ hth, hW.om_heis _ _ _ _ hf, hc, heisO_smul', heisO_smul']
  | zero =>
    change _ = c • Tm 0
    rw [LinearMap.map_zero, LinearMap.map_zero, smul_zero]
  | add f f' _ _ h1 h2 =>
    change _ = c • Tm ((fun x => f (actO S T g⁻¹ h⁻¹ x)) + fun x => f' (actO S T g⁻¹ h⁻¹ x))
    rw [LinearMap.map_add, LinearMap.map_add, LinearMap.map_add, h1, h2, smul_add]
  | smul d f _ h1 =>
    change _ = c • Tm (d • fun x => f (actO S T g⁻¹ h⁻¹ x))
    rw [LinearMap.map_smul, LinearMap.map_smul, LinearMap.map_smul, h1, smul_comm]

variable {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

open GlobalTheory.SplitScalar in

theorem om_eq_sum_lattice {χS χT : (AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (hW : IsWeilDatumO ψ S T χS χT om) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {e : AE D} (he : IsSplitIdem D e)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (hfix : ∀ u ∈ latO S T ΛS ΛT (fun _ => True), IsHalf e u ∨ IsHalf (cA D e) u → heisO ψ S T u f = f)
    {g : GA D S} {h : GA D T} (hg : SuppAt e S g) (hh : SuppAt e T h) {x y : (AE D)ˣ} (hx : IsDetAt e S g x)
    (hy : IsDetAt e T h y) {R : Finset (WO S T)}
    (hR : ∀ u ∈ R, actO S T g⁻¹ h⁻¹ u ∈ latO S T ΛS ΛT (fun _ => True) ∧ IsHalf e u)
    (hRu : ∀ w, actO S T g⁻¹ h⁻¹ w ∈ latO S T ΛS ΛT (fun _ => True) → IsHalf e w →
      ∃! v, v ∈ R ∧ w - v ∈ latO S T ΛS ΛT (fun _ => True))
    (hle : ∀ w ∈ latO S T ΛS ΛT (fun _ => True), IsHalf e w → actO S T g⁻¹ h⁻¹ w ∈ latO S T ΛS ΛT (fun _ => True)) :
    om (g, h) f = ((splitFacO χS χT x y : ℂ) * ((Real.sqrt (R.card : ℝ) : ℝ) : ℂ)⁻¹) • ∑ u ∈ R, heisO ψ S T u f := by
  by_cases hf0 : f = 0
  · subst hf0
    have : ∀ u, heisO ψ S T u 0 = 0 := fun u => (GlobalTheory.SplitScalar.heisL ψ S T u).map_zero
    simp only [map_zero, this, Finset.sum_const_zero, smul_zero]
  have he' := isSplitIdem_conj he
  have hψ := hW.std.1
  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hW.std hS hT).1
  have hst := @GlobalTheory.SplitScalar.idem_smul_mem D S T (ΛS : Set _) (ΛT : Set _) _ he.1
  have hstc := @GlobalTheory.SplitScalar.idem_smul_mem D S T (ΛS : Set _) (ΛT : Set _) _ he'.1
  have hfin := @latO_fin D S T (ΛS : Set _) (ΛT : Set _)
  generalize latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True) = Λ at *
  have hd : ∀ y, IsHalf e y → y ∉ Λ → ∃ l ∈ Λ, IsHalf (cA D e) l ∧ ψ (symplO S T l y) ≠ 1 :=
    fun y hy hn => exists_dual_half he hdual hstc hy hn
  have hd' : ∀ y, IsHalf (cA D e) y → y ∉ Λ → ∃ l ∈ Λ, IsHalf e l ∧ ψ (symplO S T l y) ≠ 1 := fun y hy hn => by
    have := exists_dual_half he' hdual (by rw [GlobalTheory.DualPairCheck.cA_cA]; exact hst) hy hn
    rwa [GlobalTheory.DualPairCheck.cA_cA] at this
  obtain ⟨r, hr, hom⟩ := om_eq_smul_sum hW he (fun u hu => (hdual u (hfin hu)).1 hu) hd hd' hg hh hx hy hR hRu hle
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  obtain ⟨⟨μ, 𝓕, hμ⟩, c, hc⟩ := GlobalTheory.exists_normalise_meanSquare_of_cocompact (WO S T) (ratL T S) K hK hKc f hf.cont hf0
    (by
      rintro _ ⟨γ, rfl⟩ w
      exact (congrArg norm (hf.quasi γ w)).trans (by rw [norm_mul, hψ.2.1, one_mul]))
  have hn : nrm2 μ 𝓕 (c • f) = 1 := hc μ 𝓕 hμ.1 hμ.2.1 hμ.2.2
  have hcf := GlobalTheory.WeilVacMove.isTheta_smul c hf
  have hfix' : ∀ u ∈ Λ, IsHalf e u ∨ IsHalf (cA D e) u → heisO ψ S T u (c • f) = c • f := fun u hu hh => by
    rw [heisO_smul', hfix u hu hh]
  have h1 := hom _ hcf (fun u hu hh => hfix' u hu (Or.inl hh)) fun u hu hh => hfix' u hu (Or.inr hh)
  have h2 : nrm2 μ 𝓕 (om (g, h) (c • f)) = 1 := by
    rw [← hn, nrm2, nrm2, integral_normSq_eq _ (hW.om_pres _ _ hcf).cont.measurable,
      integral_normSq_eq _ hcf.cont.measurable, hW.om_unit μ 𝓕 hμ.1 hμ.2.1 _ _ hcf]
  have h3 := GlobalTheory.HeisOrtho.thetaNormSq_sum_heisenbergTranslates_distinctChars D ψ S T hψ μ 𝓕 hμ _ hcf hn _ R (fun u => u)
    (fun _ => (splitFacO χS χT x y : ℂ)) (fun _ _ => Circle.norm_coe _) (fun u hu u' hu' hne => by
      have hn : u - u' ∉ Λ := fun hm => hne ((hRu u (hR u hu).1 (hR u hu).2).unique
        ⟨hu, by rw [sub_self]; exact zero_mem _⟩ ⟨hu', hm⟩)
      obtain ⟨l, hl, hlh, hlne⟩ := hd _ (isHalf_sub (hR u hu).2 (hR u' hu').2) hn
      exact ⟨l, 1, norm_one, by rw [hfix' l hl (Or.inr hlh), one_smul], psi_skew_ne hlne⟩)
  rw [h1, mul_smul, pairNorm_smul, Finset.smul_sum, h3] at h2
  have h4 : r = (Real.sqrt (R.card : ℝ))⁻¹ := by
    rw [← Real.sqrt_inv, ← eq_inv_of_mul_eq_one_left h2, Real.sqrt_sq hr.le]
  rw [hom f hf (fun u hu hh => hfix u hu (Or.inl hh)) (fun u hu hh => hfix u hu (Or.inr hh)), h4, mul_comm,
    Complex.ofReal_inv]

theorem block_frame_conjugation_identity {R : Type} [CommRing R] {a a' e e' : R} (h1 : a * a' = 0) (h2 : a' * e' = e') :
    (1 - e) * a = (1 - (e + e')) * a := by
  linear_combination e' * h1 - a * h2

theorem mem_iff_parts {Λ : AddSubgroup (WO S T)} {e : AE D} (h1 : ∀ u ∈ Λ, e • u ∈ Λ) (s : WO S T) :
    s ∈ Λ ↔ (1 - e) • s ∈ Λ ∧ e • s ∈ Λ :=
  ⟨fun hs => ⟨by rw [sub_smul, one_smul]; exact sub_mem hs (h1 s hs), h1 s hs⟩, fun hs => by
    have := add_mem hs.1 hs.2
    rwa [← add_smul, sub_add_cancel, one_smul] at this⟩

theorem isHalf_smul' {e : AE D} (he : e * e = e) (u : WO S T) : IsHalf e (e • u) := fun i j => by
  rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, he]

theorem isHalf_mono {a e : AE D} (hae : a * e = e) {u : WO S T} (hu : IsHalf e u) : IsHalf a u := fun i j => by
  rw [← hu i j, ← mul_assoc, hae]

theorem add_mem_parts {Λ : AddSubgroup (WO S T)} {a e : AE D} (hae : a * e = e) (h1 : ∀ u ∈ Λ, e • u ∈ Λ) (t : WO S T)
    {u : WO S T} (hu : IsHalf e u) :
    (t + u ∈ Λ ∧ IsHalf a (t + u)) ↔ (IsHalf a t ∧ (1 - e) • t ∈ Λ) ∧ e • t + u ∈ Λ := by
  have hu' := (mem_half S T).1 ((isHalf_iff S T).1 hu)
  have h0 : (1 - e) • u = 0 := by rw [sub_smul, one_smul, hu', sub_self]
  rw [mem_iff_parts h1, smul_add, smul_add, hu', h0, add_zero, isHalf_iff, isHalf_iff,
    AddSubgroup.add_mem_cancel_right _ ((isHalf_iff S T).1 (isHalf_mono hae hu))]
  exact ⟨fun h => ⟨⟨h.2, h.1.1⟩, h.1.2⟩, fun h => ⟨⟨h.1.2, h.2⟩, h.1.1⟩⟩

theorem off_half {a e : AE D} (hc : a * cA D a = 0) (hae : a * e = e) {s : WO S T} (hs : IsHalf a s) :
    (1 - e) • s = (1 - (e + cA D e)) • s := by
  have h := block_frame_conjugation_identity (e := e) hc ((RingHom.map_mul (cA D) a e).symm.trans (congrArg (cA D) hae))
  rw [← (mem_half S T).1 ((isHalf_iff S T).1 hs), smul_smul, smul_smul, h]

theorem act_mem_parts {Λ : AddSubgroup (WO S T)} {a e : AE D} (hc : a * cA D a = 0) (hae : a * e = e)
    (h1 : ∀ u ∈ Λ, e • u ∈ Λ) {g : GA D S} {h : GA D T} (hg : SuppAt e S g) (hh : SuppAt e T h) (t : WO S T) :
    (actO S T g h t ∈ Λ ∧ IsHalf a (actO S T g h t)) ↔
      (IsHalf a t ∧ (1 - e) • t ∈ Λ) ∧ actO S T g h (e • t) ∈ Λ := by
  have k2 : e • actO S T g h t = actO S T g h (e • t) := by
    unfold actO
    rw [Matrix.mul_smul, Matrix.smul_mul]
  by_cases ht : IsHalf a t
  · rw [mem_iff_parts h1, off_half hc hae (isHalf_actO g h ht), GlobalTheory.SplitScalar.off_smul_actO hg hh,
      ← off_half hc hae ht, k2]
    exact ⟨fun h => ⟨⟨ht, h.1.1⟩, h.1.2⟩, fun h' => ⟨⟨h'.1.2, h'.2⟩, isHalf_actO g h ht⟩⟩
  · exact iff_of_false (fun hh => ht (isHalf_of_act g h hh.2)) fun hh => ht hh.1.1

theorem sum_ite_reps {G : Type} [AddCommGroup G] {Λ X : AddSubgroup G} (A : G →+ G) {R : Finset G}
    (hR : ∀ u ∈ R, A u ∈ Λ ∧ u ∈ X) (hRu : ∀ w, A w ∈ Λ → w ∈ X → ∃! v, v ∈ R ∧ w - v ∈ Λ)
    (hle : ∀ w ∈ Λ, w ∈ X → A w ∈ Λ) {s : G} (hs : s ∈ X) (c : Prop) (p : G → Prop) (q : Prop) [DecidablePred p]
    [Decidable q] (hp : ∀ u ∈ R, p u ↔ c ∧ s + u ∈ Λ) (hq : q ↔ c ∧ A s ∈ Λ) :
    ∑ u ∈ R, (if p u then (1 : ℂ) else 0) = if q then 1 else 0 := by
  by_cases hc : q
  · obtain ⟨v, ⟨hv, hv'⟩, hu⟩ := hRu (-s) (by rw [map_neg]; exact neg_mem (hq.1 hc).2) (neg_mem hs)
    have k : ∀ u : G, -s - u ∈ Λ ↔ s + u ∈ Λ := fun u => by rw [← neg_add', neg_mem_iff]
    rw [if_pos hc, Finset.sum_eq_single_of_mem v hv fun u hu' hne =>
      if_neg fun hh => hne (hu u ⟨hu', (k u).2 ((hp u hu').1 hh).2⟩), if_pos ((hp v hv).2 ⟨(hq.1 hc).1, (k v).1 hv'⟩)]
  · rw [if_neg hc]
    refine Finset.sum_eq_zero fun u hu => if_neg fun hh => hc (hq.2 ⟨((hp u hu).1 hh).1, ?_⟩)
    have := sub_mem (hle _ ((hp u hu).1 hh).2 (add_mem hs (hR u hu).2)) (hR u hu).1
    rwa [map_add, add_sub_cancel_right] at this

theorem sum_halfInd {Λ : AddSubgroup (WO S T)} {a e : AE D} (he : e * e = e) (hc : a * cA D a = 0) (hae : a * e = e)
    (h1 : ∀ u ∈ Λ, e • u ∈ Λ) {g : GA D S} {h : GA D T} (hg : SuppAt e S g) (hh : SuppAt e T h) {R : Finset (WO S T)}
    (hR : ∀ u ∈ R, actO S T g h u ∈ Λ ∧ IsHalf e u)
    (hRu : ∀ w, actO S T g h w ∈ Λ → IsHalf e w → ∃! v, v ∈ R ∧ w - v ∈ Λ)
    (hle : ∀ w ∈ Λ, IsHalf e w → actO S T g h w ∈ Λ) :
    ∑ u ∈ R, (fun t => halfInd a Λ (t + u)) = fun t => halfInd a Λ (actO S T g h t) := by
  funext t
  rw [Finset.sum_apply]
  unfold halfInd
  classical
  exact sum_ite_reps (X := half S T e) (actAdd S T g h) (fun u hu => ⟨(hR u hu).1, (isHalf_iff S T).1 (hR u hu).2⟩)
    (fun w hw hw' => hRu w hw ((isHalf_iff S T).2 hw')) (fun w hw hw' => hle w hw ((isHalf_iff S T).2 hw'))
    ((isHalf_iff S T).1 (isHalf_smul' he t)) _ (fun u => t + u ∈ Λ ∧ IsHalf a (t + u)) _
    (fun u hu => add_mem_parts hae h1 t (hR u hu).2) (act_mem_parts hc hae h1 hg hh t)

theorem finite_enlarge (hS : Submodule.IsLattice D.host.E ΛS) (hT : Submodule.IsLattice D.host.E ΛT) {e : AE D}
    (he : e * e = e) {g : GA D S} {h : GA D T}
    (hle : ∀ w ∈ latO S T ΛS ΛT (fun _ => True), IsHalf e w → actO S T g⁻¹ h⁻¹ w ∈ latO S T ΛS ΛT (fun _ => True)) :
    Finite (↥((latO S T ΛS ΛT fun _ => True).comap (actAdd S T g⁻¹ h⁻¹) ⊓ half S T e) ⧸
      ((latO S T ΛS ΛT fun _ => True) ⊓ half S T e).addSubgroupOf
        ((latO S T ΛS ΛT fun _ => True).comap (actAdd S T g⁻¹ h⁻¹) ⊓ half S T e)) := by
  obtain ⟨N, hN, h1⟩ := exists_nsmul_actO hS hT g h
  obtain ⟨R₀, hR₀, h2⟩ := GlobalTheory.LatFinMod.latO_finite_mod D S T _ _ hS.fg hT.fg (fun _ => True) N hN
  have hst := @GlobalTheory.SplitScalar.idem_smul_mem D S T (ΛS : Set _) (ΛT : Set _) _ he
  refine finite_quot _ _ (fun w hw => ⟨hle w hw.1 ((isHalf_iff S T).2 hw.2), hw.2⟩) (N := N) (fun a b hab => ?_)
    (hR₀.image fun r => e • r) fun w hw => ?_
  · rw [← inv_smul_nsmul S T hN a, ← inv_smul_nsmul S T hN b]
    exact congrArg _ hab
  · have h3 := h1 _ hw.1
    change N • actO S T g h (actO S T g⁻¹ h⁻¹ w) ∈ _ at h3
    rw [act_act_inv] at h3
    obtain ⟨r, hr, u, hu, e1⟩ := h2 _ h3
    refine ⟨_, ⟨r, hr, rfl⟩, e • u, ⟨hst u hu, (isHalf_iff S T).1 (isHalf_smul' he u)⟩, ?_⟩
    rw [← (mem_half S T).1 hw.2, smul_comm N e, e1, smul_add, smul_comm e N u]

theorem suppAt_of {e : AE D} {V : HSp D} {g : GA D V}
    (h : (1 - (e + cA D e)) • mt V g = (1 - (e + cA D e)) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))) :
    SuppAt e V g := by
  rw [← sub_eq_zero, ← smul_sub, sub_smul, one_smul, sub_eq_zero] at h
  exact fun i j => (congrFun (congrFun h i) j).symm

theorem suppAt_inv {e : AE D} {V : HSp D} {g : GA D V} (h : SuppAt e V g) : SuppAt e V g⁻¹ :=
  suppAt_of (GlobalTheory.SplitScalar.off_smul_mt_inv h)

theorem model_sum {Λ : AddSubgroup (WO S T)} {a : AE D} {f₀ : WO S T → ℂ} {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (hTm : IsPlaceModel ψ (symplO S T) (heisO ψ S T) a Λ 1 f₀ Tm) {R : Finset (WO S T)} (hR : ∀ u ∈ R, IsHalf a u) :
    ∑ u ∈ R, heisO ψ S T u f₀ = Tm (∑ u ∈ R, fun t => halfInd a Λ (t + u)) := by
  have v := hTm.vac
  rw [one_smul] at v
  rw [map_sum, ← v]
  exact Finset.sum_congr rfl fun u hu => (hTm.trans _ (GlobalTheory.isSBHalf_halfInd a _) u (hR u hu)).symm

theorem om_base_enlarge : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (a : AE D) (f₀ : WO S T → ℂ) (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → IsSelfDualC S ΛS → IsSelfDualC T ΛT → a * a = a → infPart D a = 0 → IsThetaFunO ψ S T f₀ → IsPlaceModel ψ (symplO S T) (heisO ψ S T) a (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) 1 f₀ Tm → a * cA D a = 0 → IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) f₀ → ∀ e : AE D, IsSplitIdem D e → a * e = e → ∀ (g : GA D S) (h : GA D T), SuppAt e S g → SuppAt e T h → ∀ x y : (AE D)ˣ, IsDetAt e S g x → IsDetAt e T h y → (∀ w ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), IsHalf e w → actO S T g⁻¹ h⁻¹ w ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)) → om (g, h) f₀ = ((splitFacO χS χT x y : ℂ) * ((Real.sqrt ((((latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ⊓ GlobalTheory.PlaceModel.half S T e).relIndex ((latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True).comap (GlobalTheory.SplitHecke.actAdd S T g⁻¹ h⁻¹) ⊓ GlobalTheory.PlaceModel.half S T e) : ℕ) : ℝ) : ℝ) : ℂ)⁻¹) • Tm fun t => halfInd a (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) (actO S T g⁻¹ h⁻¹ t) := by
  intro D ψ S T χS χT om ΛS ΛT a f₀ Tm hW hS hT ha hinf hf hTm hc hv e he hae g h hg hh x y hx hy hle
  haveI := finite_enlarge hS.1 hT.1 he.1 hle
  obtain ⟨R, r1, r2, r3⟩ := exists_reps ((latO S T ΛS ΛT fun _ => True) ⊓ half S T e)
    ((latO S T ΛS ΛT fun _ => True).comap (actAdd S T g⁻¹ h⁻¹) ⊓ half S T e)
  have hR : ∀ u ∈ R, actO S T g⁻¹ h⁻¹ u ∈ latO S T ΛS ΛT (fun _ => True) ∧ IsHalf e u := fun u hu =>
    ⟨(r2 u hu).1, (isHalf_iff S T).2 (r2 u hu).2⟩
  have hRu : ∀ w, actO S T g⁻¹ h⁻¹ w ∈ latO S T ΛS ΛT (fun _ => True) → IsHalf e w →
      ∃! v, v ∈ R ∧ w - v ∈ latO S T ΛS ΛT (fun _ => True) := fun w hw hwe =>
    (existsUnique_congr fun v => and_congr_right fun hv =>
      ⟨fun h => h.1, fun h => ⟨h, (isHalf_iff S T).1 (GlobalTheory.SplitScalar.isHalf_sub hwe (hR v hv).2)⟩⟩).1
      (r3 w ⟨hw, (isHalf_iff S T).1 hwe⟩)
  rw [om_eq_sum_lattice hW hS hT he hf (fun u hu hh => hh.elim (hv.2 e he u hu)
    (hv.2 _ (GlobalTheory.SplitScalar.isSplitIdem_conj he) u hu)) hg hh hx hy hR hRu hle, r1,
    model_sum hTm fun u hu => isHalf_mono hae (hR u hu).2,
    sum_halfInd he.1 hc hae (GlobalTheory.SplitScalar.idem_smul_mem he.1) (suppAt_inv hg) (suppAt_inv hh) hR hRu hle]

end GlobalTheory.SplitLinear

end
