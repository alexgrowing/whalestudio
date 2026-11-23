import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ThetaAtEqSumHeisOfFourierSum
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussGLZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIdempotentComponentOfGroupElement

noncomputable section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SumHecke

open GlobalTheory.SplitScalar GlobalTheory.SplitHecke
open scoped ComplexOrder

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

def IsoIdem (e : AE D) : Prop := e * e = e ∧ e * cA D e = 0 ∧ infPart D e = 0

theorem IsoIdem.conj_of {e : AE D} (he : GlobalTheory.PlaceModelSum.IsOrthSum e) (hec : e * cA D e = 0) : IsoIdem e :=
  ⟨he.idem, hec, he.infPart_eq⟩

theorem infPart_cA (a : AE D) (h : infPart D a = 0) : infPart D (cA D a) = 0 := by
  have h1 := realIdem_mul_of_fin h
  have h2 : realIdem D * cA D a = 0 := by
    rw [← cA_realIdem, ← RingHom.map_mul, h1, RingHom.map_zero]
  have h3 := congrArg (infPart D) h2
  rwa [RingHom.map_mul, infPart_realIdem, one_mul, RingHom.map_zero] at h3

theorem IsoIdem.conj {e : AE D} (he : IsoIdem e) : IsoIdem (cA D e) :=
  ⟨by rw [← RingHom.map_mul, he.1], by rw [GlobalTheory.DualPairCheck.cA_cA, mul_comm, he.2.1], infPart_cA e he.2.2⟩

theorem half_fin_iso {m n : ℕ} {e : AE D} (he : IsoIdem e) {u : Mx D m n} (hu : IsHalf e u) :
    u.map (infPart D) = 0 := by
  ext i j
  show infPart D (u i j) = 0
  rw [← hu i j, RingHom.map_mul, he.2.2, zero_mul]

def FormLaw (ψ : AddChar (AF D.host.F) ℂ) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (e : AE D)
    (g : GA D S) (h : GA D T) (z : Circle) : Prop :=
  ∃ r : ℝ, 0 < r ∧ ∀ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ,
    (∀ u : WO S T, IsHalf (cA D e) u → ∀ f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T u f) = ℓ f) →
      ∀ f, IsThetaFunO ψ S T f → ℓ (om (g, h) f) = (r : ℂ) * (z : ℂ) * ℓ f

theorem half_orth_iso {e : AE D} (he : IsoIdem e) {x y : WO S T} (hx : IsHalf e x) (hy : IsHalf e y) :
    symplO S T x y = 0 :=
  symplO_eq_zero S T (by rw [mul_comm, he.2.1]) hx hy

theorem heisL_add_half_iso {e : AE D} (he : IsoIdem e) {x y : WO S T} (hx : IsHalf e x) (hy : IsHalf e y) :
    heisL ψ S T (x + y) = heisL ψ S T x * heisL ψ S T y :=
  LinearMap.ext fun f => heisO_add_of_orth ψ S T (half_orth_iso he hx hy) f

theorem heisL_commute_half_iso {e : AE D} (he : IsoIdem e) {x y : WO S T} (hx : IsHalf e x) (hy : IsHalf e y) :
    Commute (heisL ψ S T x) (heisL ψ S T y) := by
  rw [Commute, SemiconjBy, ← heisL_add_half_iso he hx hy, ← heisL_add_half_iso he hy hx, add_comm]

theorem exists_dual_half_iso {Λ : AddSubgroup (WO S T)} {e : AE D} (he : IsoIdem e)
    (hd : ∀ u : WO S T, u.map (infPart D) = 0 → (u ∈ Λ ↔ ∀ u' ∈ Λ, ψ (symplO S T u u') = 1))
    (hst : ∀ u ∈ Λ, cA D e • u ∈ Λ) {y : WO S T} (hy : IsHalf e y) (hyΛ : y ∉ Λ) :
    ∃ l ∈ Λ, IsHalf (cA D e) l ∧ ψ (symplO S T l y) ≠ 1 := by
  rw [hd y (half_fin_iso he hy)] at hyΛ
  push Not at hyΛ
  obtain ⟨u, hu, h⟩ := hyΛ
  refine ⟨cA D e • u, hst u hu, isHalf_smul he.conj.1 u, psi_skew_ne ?_⟩
  rwa [← symplO_smul, (isHalf_iff _ _).1 hy]

theorem sum_reps_invariant_iso {Λ Λ' : AddSubgroup (WO S T)} {e : AE D} (he : IsoIdem e) {R : Finset (WO S T)}
    (hR : ∀ u ∈ R, u ∈ Λ' ∧ IsHalf e u) (hR' : ∀ u ∈ Λ', IsHalf e u → ∃! v, v ∈ R ∧ u - v ∈ Λ)
    {G : WO S T → ℂ} (hG : ∀ d ∈ Λ, d ∈ Λ' → IsHalf e d → heisO ψ S T d G = G) {a : WO S T} (ha : a ∈ Λ')
    (hae : IsHalf e a) :
    heisO ψ S T a (∑ u ∈ R, heisO ψ S T u G) = ∑ u ∈ R, heisO ψ S T u G := by
  have ex : ∀ u ∈ R, ∃! v, v ∈ R ∧ a + u - v ∈ Λ := fun u hu =>
    hR' _ (add_mem ha (hR u hu).1) (isHalf_add hae (hR u hu).2)
  choose σ hσ hσu using ex
  rw [heisO_sum]
  have hinj : ∀ u₁ h₁ u₂ h₂, σ u₁ h₁ = σ u₂ h₂ → u₁ = u₂ := by
    intro u₁ h₁ u₂ h₂ h
    refine (hR' u₁ (hR u₁ h₁).1 (hR u₁ h₁).2).unique ⟨h₁, by rw [sub_self]; exact zero_mem _⟩ ⟨h₂, ?_⟩
    have := sub_mem (hσ u₁ h₁).2 (hσ u₂ h₂).2
    rwa [h, sub_sub_sub_cancel_right, add_sub_add_left_eq_sub] at this
  refine Finset.sum_bij σ (fun u hu => (hσ u hu).1) hinj
    (fun v hv => ?_) fun u hu => ?_
  · obtain ⟨u, hu, h⟩ := Finset.surj_on_of_inj_on_of_card_le σ (fun u hu => (hσ u hu).1)
      (fun u₁ u₂ h₁ h₂ => hinj u₁ h₁ u₂ h₂) le_rfl v hv
    exact ⟨u, hu, h.symm⟩
  · have hv := hR _ (hσ u hu).1
    have hd : IsHalf e (a + u - σ u hu) := isHalf_sub (isHalf_add hae (hR u hu).2) hv.2
    rw [← heisO_add_of_orth ψ S T (half_orth_iso he hae (hR u hu).2)]
    conv_rhs => rw [← hG _ (hσ u hu).2 (sub_mem (add_mem ha (hR u hu).1) hv.1) hd]
    rw [← heisO_add_of_orth ψ S T (half_orth_iso he hv.2 hd), add_sub_cancel]

theorem exists_count_form_iso {Λ : AddSubgroup (WO S T)} {e : AE D} (he : IsoIdem e)
    (hd : ∀ y, IsHalf e y → y ∉ Λ → ∃ l ∈ Λ, IsHalf (cA D e) l ∧ ψ (symplO S T l y) ≠ 1)
    {f : WO S T → ℂ} (hf0 : f ≠ 0) (hf1 : ∀ u ∈ Λ, IsHalf e u → heisO ψ S T u f = f)
    (hf2 : ∀ u ∈ Λ, IsHalf (cA D e) u → heisO ψ S T u f = f) :
    ∃ κ : (WO S T → ℂ) →ₗ[ℂ] ℂ, κ f = 1 ∧ ∀ y, IsHalf e y → 0 ≤ κ (heisO ψ S T y f) := by
  have he' := he.conj
  have h : f ∉ Submodule.span ℂ {x | ∃ y, IsHalf e y ∧ y ∉ Λ ∧ x = heisO ψ S T y f} := by
    refine notMem_span_of_commute
      {g | ∃ l ∈ Λ, ∃ z : ℂ, IsHalf (cA D e) l ∧ z ≠ 1 ∧ g = heisL ψ S T l - z • 1} ?_ _ ?_ f ?_
    · rintro _ ⟨l, -, z, hl, -, rfl⟩ _ ⟨l', -, z', hl', -, rfl⟩
      exact ((heisL_commute_half_iso he' hl hl').sub_right ((Commute.one_right _).smul_right _)).sub_left
        ((Commute.one_left _).smul_left _)
    · rintro _ ⟨y, hy, hyΛ, rfl⟩
      obtain ⟨l, hl, hl', hne⟩ := hd y hy hyΛ
      refine ⟨_, ⟨l, hl, _, hl', hne, rfl⟩, ?_⟩
      rw [LinearMap.sub_apply, heisL_apply, heisO_comm, hf2 l hl hl']
      exact sub_self _
    · have : ∀ B ∈ Submonoid.closure
          {g | ∃ l ∈ Λ, ∃ z : ℂ, IsHalf (cA D e) l ∧ z ≠ 1 ∧ g = heisL ψ S T l - z • 1},
          ∃ c : ℂ, c ≠ 0 ∧ B f = c • f := by
        intro B hB
        induction hB using Submonoid.closure_induction with
        | mem b hb =>
          obtain ⟨l, hl, z, hl', hz, rfl⟩ := hb
          refine ⟨1 - z, sub_ne_zero.2 hz.symm, ?_⟩
          rw [LinearMap.sub_apply, heisL_apply, hf2 l hl hl', sub_smul, one_smul]
          rfl
        | one => exact ⟨1, one_ne_zero, (one_smul _ _).symm⟩
        | mul x y _ _ hx hy =>
          obtain ⟨c, hc, hx⟩ := hx
          obtain ⟨d, hd, hy⟩ := hy
          exact ⟨d * c, mul_ne_zero hd hc, by rw [Module.End.mul_apply, hy, map_smul, hx, smul_smul]⟩
      intro B hB
      obtain ⟨c, hc, h⟩ := this B hB
      rw [h]
      exact smul_ne_zero hc hf0
  obtain ⟨κ, hκ, hκ'⟩ := Submodule.exists_dual_map_eq_bot_of_notMem h inferInstance
  refine ⟨(κ f)⁻¹ • κ, by rw [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hκ], fun y hy => ?_⟩
  by_cases hyΛ : y ∈ Λ
  · rw [hf1 y hyΛ hy, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hκ]
    exact zero_le_one
  · have : κ (heisO ψ S T y f) = 0 := by
      rw [← Submodule.mem_bot ℂ, ← hκ']
      exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨y, hy, hyΛ, rfl⟩)
    rw [LinearMap.smul_apply, this, smul_zero]

theorem exists_invariant_form_iso {Λ : AddSubgroup (WO S T)} {e : AE D} (he : IsoIdem e)
    (hd : ∀ y, IsHalf e y → y ∉ Λ → ∃ l ∈ Λ, IsHalf (cA D e) l ∧ ψ (symplO S T l y) ≠ 1)
    {f : WO S T → ℂ} (hf0 : f ≠ 0) (hf1 : ∀ u ∈ Λ, IsHalf e u → heisO ψ S T u f = f)
    (hf2 : ∀ u ∈ Λ, IsHalf (cA D e) u → heisO ψ S T u f = f) :
    ∃ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ, ℓ f ≠ 0 ∧
      ∀ y, IsHalf e y → ∀ φ, IsThetaFunO ψ S T φ → ℓ (heisO ψ S T y φ) = ℓ φ := by
  obtain ⟨κ, hκ1, hκ⟩ := exists_count_form_iso he hd hf0 hf1 hf2
  have h : f ∉ Submodule.span ℂ
      {x | ∃ y φ, IsHalf e y ∧ IsThetaFunO ψ S T φ ∧ x = heisO ψ S T y φ - φ} := by
    refine notMem_span_of_commute
      {g | ∃ (y : WO S T) (N : ℕ), IsHalf e y ∧ g = ∑ k ∈ Finset.range (N + 1), heisL ψ S T (k • y)} ?_ _ ?_ f ?_
    · rintro _ ⟨y, N, hy, rfl⟩ _ ⟨y', N', hy', rfl⟩
      exact Commute.sum_left _ _ _ fun k _ => Commute.sum_right _ _ _ fun k' _ =>
        heisL_commute_half_iso he (isHalf_nsmul hy k) (isHalf_nsmul hy' k')
    · rintro _ ⟨y, φ, hy, hφ, rfl⟩
      obtain ⟨U, hU, hUφ⟩ := hφ.level
      obtain ⟨N, hN, hNU⟩ := exists_nsmul_mem U hU (half_fin_iso he hy)
      obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
      refine ⟨_, ⟨y, N, hy, rfl⟩, ?_⟩
      have e1 : ∀ k : ℕ, heisL ψ S T (k • y) (heisO ψ S T y φ - φ) =
          heisO ψ S T ((k + 1) • y) φ - heisO ψ S T (k • y) φ := by
        intro k
        rw [map_sub, succ_nsmul, heisO_add_of_orth ψ S T (half_orth_iso he (isHalf_nsmul hy k) hy)]
        rfl
      rw [LinearMap.sum_apply, Finset.sum_congr rfl fun k _ => e1 k,
        Finset.sum_range_sub (fun k => heisO ψ S T (k • y) φ), zero_smul, heisO_zero,
        hUφ _ hNU (half_fin_iso he (isHalf_nsmul hy _)), sub_self]
    · have : ∀ B ∈ Submonoid.closure
          {g | ∃ (y : WO S T) (N : ℕ), IsHalf e y ∧ g = ∑ k ∈ Finset.range (N + 1), heisL ψ S T (k • y)},
          (∀ y, IsHalf e y → 0 ≤ κ (B (heisO ψ S T y f))) ∧ 0 < κ (B f) := by
        intro B hB
        induction hB using Submonoid.closure_induction_right with
        | one => exact ⟨hκ, by rw [Module.End.one_apply, hκ1]; exact zero_lt_one⟩
        | mul_right B _ g hg ih =>
          obtain ⟨y', N, hy', rfl⟩ := hg
          refine ⟨fun y hy => ?_, ?_⟩
          · rw [Module.End.mul_apply, LinearMap.sum_apply, map_sum, map_sum]
            refine Finset.sum_nonneg fun k _ => ?_
            rw [heisL_apply, ← heisO_add_of_orth ψ S T (half_orth_iso he (isHalf_nsmul hy' k) hy)]
            exact ih.1 _ (isHalf_add (isHalf_nsmul hy' k) hy)
          · rw [Module.End.mul_apply, LinearMap.sum_apply, map_sum, map_sum]
            refine Finset.sum_pos' (fun k _ => ih.1 _ (isHalf_nsmul hy' k)) ⟨0, Finset.mem_range.2 N.succ_pos, ?_⟩
            rw [heisL_apply, zero_smul, heisO_zero]
            exact ih.2
      intro B hB h0
      have := (this B hB).2
      rw [h0, map_zero] at this
      exact lt_irrefl _ this
  obtain ⟨ℓ, hℓ, hℓ'⟩ := Submodule.exists_dual_map_eq_bot_of_notMem h inferInstance
  refine ⟨ℓ, hℓ, fun y hy φ hφ => ?_⟩
  rw [← sub_eq_zero, ← map_sub, ← Submodule.mem_bot ℂ, ← hℓ']
  exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨y, φ, hy, hφ, rfl⟩)

theorem om_eq_smul_sum_iso {χS χT : (AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (hW : IsWeilDatumO ψ S T χS χT om) {e : AE D} (he : IsoIdem e) {Λ : AddSubgroup (WO S T)}
    (hdd : ∀ u ∈ Λ, ∀ u' ∈ Λ, ψ (symplO S T u u') = 1)
    (hd : ∀ y, IsHalf e y → y ∉ Λ → ∃ l ∈ Λ, IsHalf (cA D e) l ∧ ψ (symplO S T l y) ≠ 1)
    (hd' : ∀ y, IsHalf (cA D e) y → y ∉ Λ → ∃ l ∈ Λ, IsHalf e l ∧ ψ (symplO S T l y) ≠ 1)
    {g : GA D S} {h : GA D T} {z : Circle} (hz : FormLaw ψ om e g h z) {R : Finset (WO S T)} (hR : ∀ u ∈ R, actO S T g⁻¹ h⁻¹ u ∈ Λ ∧ IsHalf e u)
    (hRu : ∀ w, actO S T g⁻¹ h⁻¹ w ∈ Λ → IsHalf e w → ∃! v, v ∈ R ∧ w - v ∈ Λ)
    (hle : ∀ w ∈ Λ, IsHalf e w → actO S T g⁻¹ h⁻¹ w ∈ Λ) :
    ∃ r : ℝ, 0 < r ∧ ∀ f, IsThetaFunO ψ S T f → (∀ u ∈ Λ, IsHalf e u → heisO ψ S T u f = f) →
      (∀ u ∈ Λ, IsHalf (cA D e) u → heisO ψ S T u f = f) →
      om (g, h) f = ((r : ℂ) * (z : ℂ)) • ∑ u ∈ R, heisO ψ S T u f := by
  have he' := he.conj
  have hψ := hW.std.1
  obtain ⟨r, hr, hrℓ⟩ := hz
  refine ⟨r, hr, fun f hf hf1 hf2 => ?_⟩
  obtain ⟨Λ', hΛ'⟩ : ∃ Λ' : AddSubgroup (WO S T), ∀ w, w ∈ Λ' ↔ actO S T g⁻¹ h⁻¹ w ∈ Λ :=
    ⟨Λ.comap (actAdd S T g⁻¹ h⁻¹), fun _ => Iff.rfl⟩
  have hdd' : ∀ u ∈ Λ', ∀ u' ∈ Λ', ψ (symplO S T u u') = 1 := fun u hu u' hu' => by
    rw [← symplO_actO S T g⁻¹ h⁻¹]
    exact hdd _ ((hΛ' _).1 hu) _ ((hΛ' _).1 hu')
  have hG : ∀ w ∈ Λ', IsHalf e w ∨ IsHalf (cA D e) w → heisO ψ S T w (om (g, h) f) = om (g, h) f := by
    intro w hw hwh
    have h1 := hW.om_heis g h (actO S T g⁻¹ h⁻¹ w) f hf
    rw [GlobalTheory.AdelicLatMove.actO_actO_inv] at h1
    rw [← h1]
    rcases hwh with hwh | hwh
    · rw [hf1 _ ((hΛ' _).1 hw) (isHalf_actO _ _ hwh)]
    · rw [hf2 _ ((hΛ' _).1 hw) (isHalf_actO _ _ hwh)]
  have hF1 : ∀ w ∈ Λ', IsHalf e w → heisO ψ S T w (∑ u ∈ R, heisO ψ S T u f) = ∑ u ∈ R, heisO ψ S T u f :=
    fun w hw hwh => sum_reps_invariant_iso (Λ := Λ) (Λ' := Λ') he (fun u hu => ⟨(hΛ' _).2 (hR u hu).1, (hR u hu).2⟩)
      (fun u hu => hRu u ((hΛ' _).1 hu)) (fun d hd _ => hf1 d hd) hw hwh
  have hF2 : ∀ w ∈ Λ', IsHalf (cA D e) w →
      heisO ψ S T w (∑ u ∈ R, heisO ψ S T u f) = ∑ u ∈ R, heisO ψ S T u f := by
    intro w hw hwh
    have hwΛ : w ∈ Λ := by
      by_contra hn
      obtain ⟨l, hl, hlh, hne⟩ := hd' w hwh hn
      exact hne (hdd' _ ((hΛ' _).2 (hle l hl hlh)) _ hw)
    rw [heisO_sum]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [heisO_comm, hdd' w hw u ((hΛ' _).2 (hR u hu).1), one_smul, hf2 w hwΛ hwh]
  rw [← sub_eq_zero]
  by_contra hne
  obtain ⟨ℓ, hℓ0, hℓ⟩ := exists_invariant_form_iso (Λ := Λ') (ψ := ψ) he' (fun w hwh hw => by
      obtain ⟨l, hl, hlh, hne⟩ := hd' _ (isHalf_actO g⁻¹ h⁻¹ hwh) fun hh => hw ((hΛ' _).2 hh)
      refine ⟨actO S T g h l, (hΛ' _).2 (by rwa [actO_inv_actO]), ?_, ?_⟩
      · rw [GlobalTheory.DualPairCheck.cA_cA]
        exact isHalf_actO _ _ hlh
      · rwa [← symplO_actO S T g⁻¹ h⁻¹, actO_inv_actO]) hne
    (fun w hw hwh => by
      rw [← heisL_apply, map_sub, map_smul, heisL_apply, heisL_apply, hG w hw (Or.inr hwh), hF2 w hw hwh])
    (fun w hw hwh => by
      rw [GlobalTheory.DualPairCheck.cA_cA] at hwh
      rw [← heisL_apply, map_sub, map_smul, heisL_apply, heisL_apply, hG w hw (Or.inl hwh), hF1 w hw hwh])
  apply hℓ0
  have hval := hrℓ ℓ (fun u hu φ hφ => hℓ u hu φ hφ) f hf
  have h0 : actO S T g⁻¹ h⁻¹ 0 ∈ Λ := (hΛ' _).1 (zero_mem _)
  obtain ⟨v₀, ⟨hv₀, hv₀Λ⟩, hv₀u⟩ := hRu 0 h0 (isHalf_zero e)
  have hv₀' : v₀ ∈ Λ := by rwa [zero_sub, neg_mem_iff] at hv₀Λ
  have hsum : ℓ (∑ u ∈ R, heisO ψ S T u f) = ℓ f := by
    rw [map_sum, Finset.sum_eq_single_of_mem v₀ hv₀, hf1 v₀ hv₀' (hR _ hv₀).2]
    intro u hu hne
    have huΛ : u ∉ Λ := fun huΛ => hne (hv₀u u ⟨hu, by rwa [zero_sub, neg_mem_iff]⟩)
    obtain ⟨l, hl, hlh, hlne⟩ := hd u (hR u hu).2 huΛ
    have hth : IsThetaFunO ψ S T (heisO ψ S T u f) := by
      have := GlobalTheory.FinTranslate.isTheta_sum_heisO_fin D ψ S T hψ f hf Unit {()} (fun _ => u) (fun _ => 1)
        fun _ _ => half_fin_iso he (hR u hu).2
      rwa [Finset.sum_singleton, one_smul] at this
    have h2 := hℓ l hlh _ hth
    rw [heisO_comm, hf2 l hl hlh, map_smul, smul_eq_mul] at h2
    have h3 : (ψ (symplO S T l u) - 1) * ℓ (heisO ψ S T u f) = 0 := by rw [sub_mul, h2, one_mul, sub_self]
    exact (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 hlne)
  rw [map_sub, map_smul, hval, hsum, smul_eq_mul, sub_self]

theorem om_eq_sum_iso {χS χT : (AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (hW : IsWeilDatumO ψ S T χS χT om)
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {e : AE D} (he : IsoIdem e) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (hfix : ∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True), IsHalf e u ∨ IsHalf (cA D e) u → heisO ψ S T u f = f)
    {g : GA D S} {h : GA D T} {z : Circle} (hz : FormLaw ψ om e g h z) {R : Finset (WO S T)}
    (hR : ∀ u ∈ R, actO S T g⁻¹ h⁻¹ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) ∧ IsHalf e u)
    (hRu : ∀ w, actO S T g⁻¹ h⁻¹ w ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) → IsHalf e w →
      ∃! v, v ∈ R ∧ w - v ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True))
    (hle : ∀ w ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True), IsHalf e w →
      actO S T g⁻¹ h⁻¹ w ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) :
    om (g, h) f = ((z : ℂ) * ((Real.sqrt (R.card : ℝ) : ℝ) : ℂ)⁻¹) • ∑ u ∈ R, heisO ψ S T u f := by
  by_cases hf0 : f = 0
  · subst hf0
    have : ∀ u, heisO ψ S T u 0 = 0 := fun u => (heisL ψ S T u).map_zero
    simp only [map_zero, this, Finset.sum_const_zero, smul_zero]
  have he' := he.conj
  have hψ := hW.std.1
  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hW.std hS hT).1
  have hst := @idem_smul_mem D S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) _ he.1
  have hstc := @idem_smul_mem D S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) _ he'.1
  have hfin := @latO_fin D S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
  generalize latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) = Λ at *
  have hd : ∀ y, IsHalf e y → y ∉ Λ → ∃ l ∈ Λ, IsHalf (cA D e) l ∧ ψ (symplO S T l y) ≠ 1 :=
    fun y hy hn => exists_dual_half_iso he hdual hstc hy hn
  have hd' : ∀ y, IsHalf (cA D e) y → y ∉ Λ → ∃ l ∈ Λ, IsHalf e l ∧ ψ (symplO S T l y) ≠ 1 := fun y hy hn => by
    have := exists_dual_half_iso he' hdual (by rw [GlobalTheory.DualPairCheck.cA_cA]; exact hst) hy hn
    rwa [GlobalTheory.DualPairCheck.cA_cA] at this
  obtain ⟨r, hr, hom⟩ := om_eq_smul_sum_iso hW he (fun u hu => (hdual u (hfin hu)).1 hu) hd hd' hz hR hRu hle
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  obtain ⟨⟨μ, 𝓕, hμ⟩, c, hc⟩ := GlobalTheory.exists_normalise_meanSquare_of_cocompact (WO S T) (ratL T S) K hK hKc f hf.cont hf0
    (by
      rintro _ ⟨γ, rfl⟩ w
      exact (congrArg norm (hf.quasi γ w)).trans (by rw [norm_mul, hψ.2.1, one_mul]))
  have hn : nrm2 μ 𝓕 (c • f) = 1 := hc μ 𝓕 hμ.1 hμ.2.1 hμ.2.2
  have hcf := GlobalTheory.WeilVacMove.isTheta_smul c hf
  have hfix' : ∀ u ∈ Λ, IsHalf e u ∨ IsHalf (cA D e) u → heisO ψ S T u (c • f) = c • f := fun u hu hh => by
    rw [heisO_smul, hfix u hu hh]
  have h1 := hom _ hcf (fun u hu hh => hfix' u hu (Or.inl hh)) fun u hu hh => hfix' u hu (Or.inr hh)
  have h2 : nrm2 μ 𝓕 (om (g, h) (c • f)) = 1 := by
    rw [← hn, nrm2, nrm2, integral_normSq_eq _ (hW.om_pres _ _ hcf).cont.measurable,
      integral_normSq_eq _ hcf.cont.measurable, hW.om_unit μ 𝓕 hμ.1 hμ.2.1 _ _ hcf]
  have h3 := GlobalTheory.HeisOrtho.thetaNormSq_sum_heisenbergTranslates_distinctChars D ψ S T hψ μ 𝓕 hμ _ hcf hn _ R (fun u => u)
    (fun _ => (z : ℂ)) (fun _ _ => Circle.norm_coe _) (fun u hu u' hu' hne => by
      have hn : u - u' ∉ Λ := fun hm => hne ((hRu u (hR u hu).1 (hR u hu).2).unique
        ⟨hu, by rw [sub_self]; exact zero_mem _⟩ ⟨hu', hm⟩)
      obtain ⟨l, hl, hlh, hlne⟩ := hd _ (isHalf_sub (hR u hu).2 (hR u' hu').2) hn
      exact ⟨l, 1, norm_one, by rw [hfix' l hl (Or.inr hlh), one_smul], psi_skew_ne hlne⟩)
  rw [h1, mul_smul, pairNorm_smul, Finset.smul_sum, h3] at h2
  have h4 : r = (Real.sqrt (R.card : ℝ))⁻¹ := by
    rw [← Real.sqrt_inv, ← eq_inv_of_mul_eq_one_left h2, Real.sqrt_sq hr.le]
  rw [hom f hf (fun u hu hh => hfix u hu (Or.inl hh)) (fun u hu hh => hfix u hu (Or.inr hh)), h4, mul_comm,
    Complex.ofReal_inv]

theorem cut_exists (V : HSp D) (g : GA D V) (ε : AE D) (hεε : ε * ε = ε) (hε : cA D ε = ε) :
    ∃ k : GA D V, mt V k = ε • mt V g + (1 - ε) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := by
  set M := mt V g with hM
  have hinv : M * ((matHom V g)⁻¹).1 = 1 := (matHom V g).mul_inv
  have hinv' : ((matHom V g)⁻¹).1 * M = 1 := (matHom V g).inv_mul
  let K : GL (Fin V.rank) (AE D) := ⟨ε • M + (1 - ε) • 1, ε • ((matHom V g)⁻¹).1 + (1 - ε) • 1,
    GlobalTheory.GfCut.idem_mul ε hεε _ _ hinv, GlobalTheory.GfCut.idem_mul ε hεε _ _ hinv'⟩
  have hgU : Formalism.UG.cT (cA D) M * V.gram.map (incA D) * M = V.gram.map (incA D) :=
    (show HR (AF D.host.F) D.sp.cm.sig V.gram from g).2
  have hKU : K ∈ HR (AF D.host.F) D.sp.cm.sig V.gram :=
    GlobalTheory.GfCut.idem_unitary (cA D) ε hε hεε _ M hgU
  exact ⟨(⟨K, hKU⟩ : HR (AF D.host.F) D.sp.cm.sig V.gram), rfl⟩

theorem cut_mul {R : Type} [CommRing R] {n : ℕ} (e f : R) (hef : e * f = 0) (M : Matrix (Fin n) (Fin n) R) :
    (e • M + (1 - e) • (1 : Matrix (Fin n) (Fin n) R)) * (f • M + (1 - f) • 1) = (e + f) • M + (1 - (e + f)) • 1 := by
  have h1 : e * (1 - f) = e := by rw [mul_sub, mul_one, hef, sub_zero]
  have h2 : (1 - e) * f = f := by rw [sub_mul, one_mul, hef, sub_zero]
  have h3 : (1 - e) * (1 - f) = 1 - (e + f) := by linear_combination hef
  simp only [add_mul, mul_add, smul_mul_smul_comm, Matrix.mul_one, Matrix.one_mul, hef, h1, h2, h3, zero_smul, zero_add]
  rw [add_smul]; abel

theorem idem_det {R : Type} [CommRing R] {n : ℕ} {a ε : R} (ha : a * a = a) (haε : a * ε = a)
    (M : Matrix (Fin n) (Fin n) R) : a * (ε • M + (1 - ε) • (1 : Matrix (Fin n) (Fin n) R)).det = a * M.det := by
  have h0 : a * a ^ Fintype.card (Fin n) = a := by
    rw [← pow_succ']
    exact IsIdempotentElem.pow_succ_eq _ ha
  have h1 : a • (ε • M + (1 - ε) • (1 : Matrix (Fin n) (Fin n) R)) = a • M := by
    rw [smul_add, smul_smul, smul_smul, mul_sub, haε, mul_one, sub_self, zero_smul, add_zero]
  rw [← h0, mul_assoc, mul_assoc, ← Matrix.det_smul, ← Matrix.det_smul, h1]

theorem cut_supp {R : Type} [CommRing R] {n : ℕ} {ε : R} (hε : ε * ε = ε) (M : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    ε * ((ε • M + (1 - ε) • (1 : Matrix (Fin n) (Fin n) R)) - 1) i j =
      ((ε • M + (1 - ε) • (1 : Matrix (Fin n) (Fin n) R)) - 1) i j := by
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  linear_combination (M i j - (1 : Matrix (Fin n) (Fin n) R) i j) * hε

theorem det_parts {R : Type} [CommRing R] {a b d d₁ d₂ x x₁ x₂ : R} (hab : a * b = 0)
    (h : x = (a + b) * d + (1 - (a + b))) (h₁ : x₁ = a * d₁ + (1 - a)) (h₂ : x₂ = b * d₂ + (1 - b))
    (k₁ : a * d₁ = a * d) (k₂ : b * d₂ = b * d) : x = x₁ * x₂ := by
  rw [h, h₁, h₂, k₁, k₂]
  linear_combination (-(d - 1) ^ 2) * hab

theorem exists_detAt {a : AE D} (ha : a * a = a) (V : HSp D) (g : GA D V) : ∃ x, IsDetAt a V g x := by
  have h : (mt V g).det * (mt V g⁻¹).det = 1 := by
    rw [← Matrix.det_mul, show mt V g * mt V g⁻¹ = 1 from (matHom V g).mul_inv, Matrix.det_one]
  have h2 : (a * (mt V g).det + (1 - a)) * (a * (mt V g⁻¹).det + (1 - a)) = 1 := by
    linear_combination ((mt V g).det * (mt V g⁻¹).det - (mt V g).det - (mt V g⁻¹).det + 1) * ha + a * h
  exact ⟨⟨_, _, h2, by rw [mul_comm, h2]⟩, rfl⟩

def SplitLaw (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (e : AE D) : Prop :=
  ∀ g x, SuppAt e S g → IsDetAt e S g x → FormLaw ψ om e g 1 (splitFacO χS χT x 1)

variable {χS χT : (AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

theorem splitLaw_split (hW : IsWeilDatumO ψ S T χS χT om) {e : AE D} (he : IsSplitIdem D e) :
    SplitLaw ψ χS χT om e := fun g x hg hx =>
  hW.om_split e he g 1 hg (fun i j => by
    rw [show mt T 1 = 1 from rfl, sub_self, Matrix.zero_apply, mul_zero]) x 1 hx (by
    show (1 : AE D) = _
    rw [show mt T 1 = 1 from rfl, Matrix.det_one]; ring)

theorem splitLaw_zero : SplitLaw ψ χS χT om (0 : AE D) := by
  intro g x hg hx
  have h1 : g = 1 := by
    refine Subtype.ext (Units.ext ?_)
    show mt S g = 1
    rw [← sub_eq_zero]
    ext i j
    rw [← hg i j, RingHom.map_zero, add_zero, zero_mul, Matrix.zero_apply]
  have h2 : x = 1 := Units.ext (by rw [show (x : AE D) = _ from hx, zero_mul, zero_add, sub_zero, Units.val_one])
  subst h1 h2
  refine ⟨1, one_pos, fun ℓ _ f _ => ?_⟩
  rw [show ((1 : GA D S), (1 : GA D T)) = 1 from rfl, map_one, splitFacO, map_one, map_one, inv_one, mul_one]
  simp

theorem isHalf_add_left {m n : ℕ} {a b : AE D} (hab : a * b = 0) {u : Mx D m n} (hu : IsHalf a u) :
    IsHalf (a + b) u := fun i j => by
  rw [add_mul, hu i j, ← hu i j, ← mul_assoc, mul_comm b, hab, zero_mul, add_zero]

set_option maxHeartbeats 1600000 in
theorem splitLaw_add (hW : IsWeilDatumO ψ S T χS χT om) {a b : AE D} (ha : a * a = a) (hb : b * b = b)
    (hac : a * cA D a = 0) (hbc : b * cA D b = 0) (hab : a * b = 0) (habc : a * cA D b = 0)
    (la : SplitLaw ψ χS χT om a) (lb : SplitLaw ψ χS χT om b) : SplitLaw ψ χS χT om (a + b) := by
  intro g x hg hx
  have cc := @GlobalTheory.DualPairCheck.cA_cA D
  have ha' : cA D a * cA D a = cA D a := by rw [← RingHom.map_mul, ha]
  have hb' : cA D b * cA D b = cA D b := by rw [← RingHom.map_mul, hb]
  have hab' : cA D a * cA D b = 0 := by rw [← RingHom.map_mul, hab, RingHom.map_zero]
  have hcab : cA D a * b = 0 := by
    have := congrArg (cA D) habc
    rwa [RingHom.map_mul, cc, RingHom.map_zero] at this
  have ea : (a + cA D a) * (a + cA D a) = a + cA D a := by linear_combination ha + ha' + 2 * hac
  have eb : (b + cA D b) * (b + cA D b) = b + cA D b := by linear_combination hb + hb' + 2 * hbc
  have eab : (a + cA D a) * (b + cA D b) = 0 := by linear_combination hab + hab' + habc + hcab
  obtain ⟨g₁, hg₁⟩ := cut_exists S g _ ea (by rw [RingHom.map_add, cc, add_comm])
  obtain ⟨g₂, hg₂⟩ := cut_exists S g _ eb (by rw [RingHom.map_add, cc, add_comm])
  have hgg : g = g₁ * g₂ := by
    refine Subtype.ext (Units.ext ?_)
    show mt S g = mt S g₁ * mt S g₂
    rw [hg₁, hg₂, cut_mul _ _ eab]
    ext i j
    have := hg i j
    rw [RingHom.map_add, Matrix.sub_apply] at this
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    linear_combination -this
  obtain ⟨x₁, hx₁⟩ := exists_detAt ha S g₁
  obtain ⟨x₂, hx₂⟩ := exists_detAt hb S g₂
  obtain ⟨r₁, hr₁, l₁⟩ := la g₁ x₁ (fun i j => by rw [hg₁]; exact cut_supp ea _ i j) hx₁
  obtain ⟨r₂, hr₂, l₂⟩ := lb g₂ x₂ (fun i j => by rw [hg₂]; exact cut_supp eb _ i j) hx₂
  have hxx : x = x₁ * x₂ := by
    refine Units.ext (det_parts hab hx hx₁ hx₂ ?_ ?_)
    · rw [hg₁]
      exact idem_det ha (by rw [mul_add, ha, hac, add_zero]) _
    · rw [hg₂]
      exact idem_det hb (by rw [mul_add, hb, hbc, add_zero]) _
  refine ⟨r₁ * r₂, mul_pos hr₁ hr₂, fun ℓ hℓ f hf => ?_⟩
  rw [RingHom.map_add] at hℓ
  have e1 : om (g, 1) f = om (g₁, 1) (om (g₂, 1) f) := by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, ← hgg]
  rw [e1, l₁ ℓ (fun u hu => hℓ u (isHalf_add_left hab' hu)) _ (hW.om_pres _ _ hf),
    l₂ ℓ (fun u hu => hℓ u (by rw [add_comm]; exact isHalf_add_left (by rw [mul_comm, hab']) hu)) _ hf, hxx]
  simp only [splitFacO, map_mul, map_one, mul_one, mul_inv, Circle.coe_mul, Complex.ofReal_mul]
  ring

theorem splitLaw_sum (hW : IsWeilDatumO ψ S T χS χT om) {e : AE D} (he : GlobalTheory.PlaceModelSum.IsOrthSum e)
    (hec : e * cA D e = 0) : SplitLaw ψ χS χT om e := by
  classical
  obtain ⟨ι, P, es, h1, h2, rfl⟩ := he
  induction P using Finset.induction_on with
  | empty => exact splitLaw_zero
  | insert i P hi ih =>
    have h1' : ∀ j ∈ P, IsSplitIdem D (es j) := fun j hj => h1 j (Finset.mem_insert_of_mem hj)
    have h2' : ∀ j ∈ P, ∀ k ∈ P, k ≠ j → es j * es k = 0 := fun j hj k hk =>
      h2 j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk)
    have hi' := h1 i (Finset.mem_insert_self i P)
    have hb : (∑ j ∈ P, es j) * ∑ j ∈ P, es j = ∑ j ∈ P, es j :=
      GlobalTheory.PlaceModelSum.IsOrthSum.idem ⟨ι, P, es, h1', h2', rfl⟩
    have hab : es i * ∑ j ∈ P, es j = 0 := by
      rw [Finset.mul_sum]
      exact Finset.sum_eq_zero fun j hj => h2 i (Finset.mem_insert_self i P) j (Finset.mem_insert_of_mem hj)
        fun h => hi (h ▸ hj)
    rw [Finset.sum_insert hi] at hec ⊢
    generalize (∑ j ∈ P, es j) = b at *
    have hb' : cA D b * cA D b = cA D b := by rw [← RingHom.map_mul, hb]
    have hab' : cA D (es i) * cA D b = 0 := by rw [← RingHom.map_mul, hab, RingHom.map_zero]
    rw [RingHom.map_add] at hec
    have hbc : b * cA D b = 0 := by
      have : b * cA D b = (b * (es i + b)) * (cA D b * (cA D (es i) + cA D b)) := by
        rw [mul_add, mul_add, mul_comm b (es i), hab, hb, mul_comm (cA D b) (cA D (es i)), hab', hb', zero_add, zero_add]
      rw [this, mul_mul_mul_comm, hec, mul_zero]
    have habc : es i * cA D b = 0 := by
      have : es i * cA D b = (es i * (es i + b)) * (cA D b * (cA D (es i) + cA D b)) := by
        rw [mul_add, mul_add, hab, hi'.1, mul_comm (cA D b) (cA D (es i)), hab', hb', zero_add, add_zero]
      rw [this, mul_mul_mul_comm, hec, mul_zero]
    exact splitLaw_add hW hi'.1 hb hi'.2.1 hbc hab habc (splitLaw_split hW hi') (ih h1' h2' hbc)

end GlobalTheory.SumHecke
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

theorem GlobalTheory.SumHecke.om_eq_sum_idemSum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e Q → ∀ (g : GA D S) (x : (AE D)ˣ), SuppAt e S g → IsDetAt (cA D e) S g x → ∀ (R : Finset (WO S T)), (∀ u ∈ R, actO S T g⁻¹ 1 u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) ∧ IsHalf (cA D e) u) → (∀ w, actO S T g⁻¹ 1 w ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) → IsHalf (cA D e) w → ∃! v, v ∈ R ∧ w - v ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) → (∀ w ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True), IsHalf (cA D e) w → actO S T g⁻¹ 1 w ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) → ∀ f, IsThetaFunO ψ S T f → (∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True), IsHalf e u ∨ IsHalf (cA D e) u → heisO ψ S T u f = f) → om (g, 1) f = ((splitFacO χS χT x 1 : ℂ) * ((Real.sqrt (R.card : ℝ) : ℝ) : ℂ)⁻¹) • ∑ u ∈ R, heisO ψ S T u f := by
  intro D ψ S T χS χT om hW ΛS ΛT hS hT Q e he g x hg hx R hR hRu hle f hf hfix
  have cc := @GlobalTheory.DualPairCheck.cA_cA D
  have ho := (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).conj
  have hec : cA D e * cA D (cA D e) = 0 := by rw [cc, mul_comm, he.2]
  have hz := GlobalTheory.SumHecke.splitLaw_sum hW ho hec g x (fun i j => by rw [cc, add_comm]; exact hg i j) hx
  refine GlobalTheory.SumHecke.om_eq_sum_iso hW hS hT (GlobalTheory.SumHecke.IsoIdem.conj_of ho hec) hf
    (fun u hu h => hfix u hu (by rw [cc] at h; exact h.symm)) hz ?_ ?_ ?_ <;> rw [inv_one] <;> assumption

end

end
