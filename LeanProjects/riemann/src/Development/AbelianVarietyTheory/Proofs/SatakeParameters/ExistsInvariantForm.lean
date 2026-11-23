import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmVacuumEqSplitFacSmulSum
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsNormaliseMeanSquareOfCocompact
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitHecke

open GlobalTheory.SplitScalar
open scoped ComplexOrder

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem hO_trace (S T : HSp D) (x y : WO S T) :
    hO S T x y = Matrix.trace ((S.gram⁻¹).map (incA D) * (Formalism.UG.cT (cA D) (y : Matrix (Fin T.rank) (Fin S.rank) (AE D))) *
      T.gram.map (incA D) * (x : Matrix (Fin T.rank) (Fin S.rank) (AE D))) := by
  unfold hO
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]

theorem trace_inv {A : Type} [CommRing A] (σ : A →+* A) {a b : ℕ} (G G' k : Matrix (Fin a) (Fin a) A)
    (H m : Matrix (Fin b) (Fin b) A) (x y : Matrix (Fin b) (Fin a) A) (h1 : G' * G = 1)
    (hk : Formalism.UG.cT σ k * G * k = G) (hm : Formalism.UG.cT σ m * H * m = H) :
    Matrix.trace (G' * Formalism.UG.cT σ (m * y * k) * H * (m * x * k)) = Matrix.trace (G' * Formalism.UG.cT σ y * H * x) := by
  have h2 : G * G' = 1 := mul_eq_one_comm.1 h1
  have h3 : (G' * Formalism.UG.cT σ k * G) * k = 1 := by
    calc _ = G' * (Formalism.UG.cT σ k * G * k) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hk, h1]
  have h4 : k * (G' * Formalism.UG.cT σ k * G) = 1 := mul_eq_one_comm.1 h3
  have h5 : k * G' * Formalism.UG.cT σ k = G' := by
    have := congrArg (· * G') h4
    simp only [Matrix.mul_assoc, h2, Matrix.mul_one, Matrix.one_mul] at this
    simpa only [Matrix.mul_assoc] using this
  rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul, ← Matrix.mul_assoc _ _ k, Matrix.trace_mul_comm _ k]
  congr 1
  calc _ = (k * G' * Formalism.UG.cT σ k) * Formalism.UG.cT σ y * (Formalism.UG.cT σ m * H * m) * x := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [h5, hm]

theorem symplO_actO (S T : HSp D) (g : GA D S) (h : GA D T) (x y : WO S T) :
    symplO S T (actO S T g h x) (actO S T g h y) = symplO S T x y := by
  unfold symplO
  by_cases hS : IsUnit S.gram.det
  · congr 2
    rw [hO_trace, hO_trace]
    have hk : Formalism.UG.cT (cA D) (mt S g⁻¹) * S.gram.map (incA D) * mt S g⁻¹ = S.gram.map (incA D) :=
      (show HR (AF D.host.F) D.sp.cm.sig S.gram from g⁻¹).2
    have hm : Formalism.UG.cT (cA D) (mt T h) * T.gram.map (incA D) * mt T h = T.gram.map (incA D) :=
      (show HR (AF D.host.F) D.sp.cm.sig T.gram from h).2
    have h1 : (S.gram⁻¹).map (incA D) * S.gram.map (incA D) = 1 := by
      rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hS, Matrix.map_one _ (map_zero _) (map_one _)]
    exact trace_inv (cA D) _ _ _ _ _ x y h1 hk hm
  · simp only [hO, Matrix.nonsing_inv_apply_not_isUnit _ hS, Matrix.zero_apply, map_zero, zero_mul,
      Finset.sum_const_zero]

def actAdd (S T : HSp D) (g : GA D S) (h : GA D T) : WO S T →+ WO S T :=
  AddMonoidHom.mk' (actO S T g h) fun x y => by simp only [actO, Matrix.mul_add, Matrix.add_mul]

theorem isHalf_actO {e : AE D} (g : GA D S) (h : GA D T) {u : WO S T} (hu : IsHalf e u) :
    IsHalf e (actO S T g h u) := by
  rw [isHalf_iff] at *
  unfold actO
  rw [← Matrix.smul_mul, ← Matrix.mul_smul, hu]

theorem actO_inv_actO (g : GA D S) (h : GA D T) (u : WO S T) : actO S T g⁻¹ h⁻¹ (actO S T g h u) = u := by
  have := GlobalTheory.AdelicLatMove.actO_actO_inv S T g⁻¹ h⁻¹ u
  rwa [inv_inv, inv_inv] at this

theorem exists_count_form' {Λ : AddSubgroup (WO S T)} {e : AE D} (he : IsSplitIdem D e)
    (hd : ∀ y, IsHalf e y → y ∉ Λ → ∃ l ∈ Λ, IsHalf (cA D e) l ∧ ψ (symplO S T l y) ≠ 1)
    {f : WO S T → ℂ} (hf0 : f ≠ 0) (hf1 : ∀ u ∈ Λ, IsHalf e u → heisO ψ S T u f = f)
    (hf2 : ∀ u ∈ Λ, IsHalf (cA D e) u → heisO ψ S T u f = f) :
    ∃ κ : (WO S T → ℂ) →ₗ[ℂ] ℂ, κ f = 1 ∧ ∀ y, IsHalf e y → 0 ≤ κ (heisO ψ S T y f) := by
  have he' := isSplitIdem_conj he
  have h : f ∉ Submodule.span ℂ {x | ∃ y, IsHalf e y ∧ y ∉ Λ ∧ x = heisO ψ S T y f} := by
    refine notMem_span_of_commute
      {g | ∃ l ∈ Λ, ∃ z : ℂ, IsHalf (cA D e) l ∧ z ≠ 1 ∧ g = heisL ψ S T l - z • 1} ?_ _ ?_ f ?_
    · rintro _ ⟨l, -, z, hl, -, rfl⟩ _ ⟨l', -, z', hl', -, rfl⟩
      exact ((heisL_commute_half he' hl hl').sub_right ((Commute.one_right _).smul_right _)).sub_left
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

theorem exists_invariant_form' {Λ : AddSubgroup (WO S T)} {e : AE D} (he : IsSplitIdem D e)
    (hd : ∀ y, IsHalf e y → y ∉ Λ → ∃ l ∈ Λ, IsHalf (cA D e) l ∧ ψ (symplO S T l y) ≠ 1)
    {f : WO S T → ℂ} (hf0 : f ≠ 0) (hf1 : ∀ u ∈ Λ, IsHalf e u → heisO ψ S T u f = f)
    (hf2 : ∀ u ∈ Λ, IsHalf (cA D e) u → heisO ψ S T u f = f) :
    ∃ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ, ℓ f ≠ 0 ∧
      ∀ y, IsHalf e y → ∀ φ, IsThetaFunO ψ S T φ → ℓ (heisO ψ S T y φ) = ℓ φ := by
  obtain ⟨κ, hκ1, hκ⟩ := exists_count_form' he hd hf0 hf1 hf2
  have h : f ∉ Submodule.span ℂ
      {x | ∃ y φ, IsHalf e y ∧ IsThetaFunO ψ S T φ ∧ x = heisO ψ S T y φ - φ} := by
    refine notMem_span_of_commute
      {g | ∃ (y : WO S T) (N : ℕ), IsHalf e y ∧ g = ∑ k ∈ Finset.range (N + 1), heisL ψ S T (k • y)} ?_ _ ?_ f ?_
    · rintro _ ⟨y, N, hy, rfl⟩ _ ⟨y', N', hy', rfl⟩
      exact Commute.sum_left _ _ _ fun k _ => Commute.sum_right _ _ _ fun k' _ =>
        heisL_commute_half he (isHalf_nsmul hy k) (isHalf_nsmul hy' k')
    · rintro _ ⟨y, φ, hy, hφ, rfl⟩
      obtain ⟨U, hU, hUφ⟩ := hφ.level
      obtain ⟨N, hN, hNU⟩ := exists_nsmul_mem U hU (half_fin he hy)
      obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
      refine ⟨_, ⟨y, N, hy, rfl⟩, ?_⟩
      have e1 : ∀ k : ℕ, heisL ψ S T (k • y) (heisO ψ S T y φ - φ) =
          heisO ψ S T ((k + 1) • y) φ - heisO ψ S T (k • y) φ := by
        intro k
        rw [map_sub, succ_nsmul, heisO_add_of_orth ψ S T (half_orth he (isHalf_nsmul hy k) hy)]
        rfl
      rw [LinearMap.sum_apply, Finset.sum_congr rfl fun k _ => e1 k,
        Finset.sum_range_sub (fun k => heisO ψ S T (k • y) φ), zero_smul, heisO_zero,
        hUφ _ hNU (half_fin he (isHalf_nsmul hy _)), sub_self]
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
            rw [heisL_apply, ← heisO_add_of_orth ψ S T (half_orth he (isHalf_nsmul hy' k) hy)]
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

theorem om_eq_smul_sum {χS χT : (AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (hW : IsWeilDatumO ψ S T χS χT om) {e : AE D} (he : IsSplitIdem D e) {Λ : AddSubgroup (WO S T)}
    (hdd : ∀ u ∈ Λ, ∀ u' ∈ Λ, ψ (symplO S T u u') = 1)
    (hd : ∀ y, IsHalf e y → y ∉ Λ → ∃ l ∈ Λ, IsHalf (cA D e) l ∧ ψ (symplO S T l y) ≠ 1)
    (hd' : ∀ y, IsHalf (cA D e) y → y ∉ Λ → ∃ l ∈ Λ, IsHalf e l ∧ ψ (symplO S T l y) ≠ 1)
    {g : GA D S} {h : GA D T} (hg : SuppAt e S g) (hh : SuppAt e T h) {x y : (AE D)ˣ} (hx : IsDetAt e S g x)
    (hy : IsDetAt e T h y) {R : Finset (WO S T)} (hR : ∀ u ∈ R, actO S T g⁻¹ h⁻¹ u ∈ Λ ∧ IsHalf e u)
    (hRu : ∀ w, actO S T g⁻¹ h⁻¹ w ∈ Λ → IsHalf e w → ∃! v, v ∈ R ∧ w - v ∈ Λ)
    (hle : ∀ w ∈ Λ, IsHalf e w → actO S T g⁻¹ h⁻¹ w ∈ Λ) :
    ∃ r : ℝ, 0 < r ∧ ∀ f, IsThetaFunO ψ S T f → (∀ u ∈ Λ, IsHalf e u → heisO ψ S T u f = f) →
      (∀ u ∈ Λ, IsHalf (cA D e) u → heisO ψ S T u f = f) →
      om (g, h) f = ((r : ℂ) * (splitFacO χS χT x y : ℂ)) • ∑ u ∈ R, heisO ψ S T u f := by
  have he' := isSplitIdem_conj he
  have hψ := hW.std.1
  obtain ⟨r, hr, hrℓ⟩ := hW.om_split e he g h hg hh x y hx hy
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
    fun w hw hwh => sum_reps_invariant (Λ := Λ) (Λ' := Λ') he (fun u hu => ⟨(hΛ' _).2 (hR u hu).1, (hR u hu).2⟩)
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
  obtain ⟨ℓ, hℓ0, hℓ⟩ := exists_invariant_form' (Λ := Λ') (ψ := ψ) he' (fun w hwh hw => by
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
        fun _ _ => half_fin he (hR u hu).2
      rwa [Finset.sum_singleton, one_smul] at this
    have h2 := hℓ l hlh _ hth
    rw [heisO_comm, hf2 l hl hlh, map_smul, smul_eq_mul] at h2
    have h3 : (ψ (symplO S T l u) - 1) * ℓ (heisO ψ S T u f) = 0 := by rw [sub_mul, h2, one_mul, sub_self]
    exact (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 hlne)
  rw [map_sub, map_smul, hval, hsum, smul_eq_mul, sub_self]

theorem integral_normSq_eq {X : Type} [MeasurableSpace X] (ν : Measure X) {f : X → ℂ} (hf : Measurable f) :
    ∫ w, ‖f w‖ ^ 2 ∂ν = (∫⁻ w, ‖f w‖ₑ ^ 2 ∂ν).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun w => by positivity)
    (hf.norm.pow_const 2).aestronglyMeasurable]
  congr 2
  funext w
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]

theorem om_eq_sum {χS χT : (AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (hW : IsWeilDatumO ψ S T χS χT om) {e : AE D} (he : IsSplitIdem D e) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (hfix : ∀ u ∈ latO S T (L0c D S) (L0c D T) (fun _ => True), IsHalf e u ∨ IsHalf (cA D e) u → heisO ψ S T u f = f)
    {g : GA D S} {h : GA D T} (hg : SuppAt e S g) (hh : SuppAt e T h) {x y : (AE D)ˣ} (hx : IsDetAt e S g x)
    (hy : IsDetAt e T h y) {R : Finset (WO S T)}
    (hR : ∀ u ∈ R, actO S T g⁻¹ h⁻¹ u ∈ latO S T (L0c D S) (L0c D T) (fun _ => True) ∧ IsHalf e u)
    (hRu : ∀ w, actO S T g⁻¹ h⁻¹ w ∈ latO S T (L0c D S) (L0c D T) (fun _ => True) → IsHalf e w →
      ∃! v, v ∈ R ∧ w - v ∈ latO S T (L0c D S) (L0c D T) (fun _ => True))
    (hle : ∀ w ∈ latO S T (L0c D S) (L0c D T) (fun _ => True), IsHalf e w →
      actO S T g⁻¹ h⁻¹ w ∈ latO S T (L0c D S) (L0c D T) (fun _ => True)) :
    om (g, h) f = ((splitFacO χS χT x y : ℂ) * ((Real.sqrt (R.card : ℝ) : ℝ) : ℂ)⁻¹) • ∑ u ∈ R, heisO ψ S T u f := by
  by_cases hf0 : f = 0
  · subst hf0
    have : ∀ u, heisO ψ S T u 0 = 0 := fun u => (heisL ψ S T u).map_zero
    simp only [map_zero, this, Finset.sum_const_zero, smul_zero]
  have he' := isSplitIdem_conj he
  have hψ := hW.std.1
  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hW.std (GlobalTheory.PlaceModel.isSelfDualC_latFrame S)
    (GlobalTheory.PlaceModel.isSelfDualC_latFrame T)).1
  rw [GlobalTheory.PlaceModel.coe_latFrame, GlobalTheory.PlaceModel.coe_latFrame] at hdual
  have hst := @idem_smul_mem D S T (L0c D S) (L0c D T) _ he.1
  have hstc := @idem_smul_mem D S T (L0c D S) (L0c D T) _ he'.1
  have hfin := @latO_fin D S T (L0c D S) (L0c D T)
  generalize latO S T (L0c D S) (L0c D T) (fun _ => True) = Λ at *
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
    rw [heisO_smul, hfix u hu hh]
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

end GlobalTheory.SplitHecke

end
