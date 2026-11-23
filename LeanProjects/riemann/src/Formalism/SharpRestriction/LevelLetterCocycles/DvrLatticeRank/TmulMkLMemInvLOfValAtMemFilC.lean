import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ExpansionLowCoeffsIntegral
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.PiNSOfPi
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelFPfB

noncomputable section

namespace Formalism.MainNotions.N.Ln34.LevelExpansions

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.N.Ln34 Formalism.MainNotions.N.Ln34.DescentValuation TensorProduct
open Formalism.MainNotions.N.Ln34.UnivLinkPf PowerSeries

theorem ser_van {LL : Type} [Field LL] (e e₁ P G A : PowerSeries LL) (u x₀ : LL) (h N : ℕ)
    (he : e = X * e₁) (he₁ : constantCoeff e₁ ≠ 0) (hP : constantCoeff P ≠ 0) (hu : u ≠ 0)
    (hrel : rescale u (e ^ h) * P * G = e ^ h * rescale u A - rescale u (e ^ h) * A)
    (hA : ∀ i < N, coeff i A = x₀ * coeff i (e ^ h)) :
    ∀ i < N, coeff i G = 0 := by
  set D := A - C x₀ * e ^ h with hD
  have hXD : X ^ N ∣ D := by
    rw [X_pow_dvd_iff]
    intro i hi
    rw [hD, map_sub, coeff_C_mul, hA i hi, sub_self]
  obtain ⟨D₁, hD₁⟩ := hXD
  have hA' : A = C x₀ * e ^ h + X ^ N * D₁ := by rw [← hD₁, hD]; ring
  have hR : rescale u (e ^ h) = X ^ h * (C (u ^ h) * (rescale u e₁) ^ h) := by
    rw [map_pow, he, map_mul, rescale_X, mul_pow, mul_pow]; simp only [map_pow]; ring
  have hRC : rescale u (C x₀) = C x₀ := by
    ext k
    rw [coeff_rescale, coeff_C]
    split_ifs with hk
    · subst hk; simp
    · simp
  have hresc : rescale u A = C x₀ * rescale u (e ^ h) + X ^ N * (C (u ^ N) * rescale u D₁) := by
    rw [hA', map_add, map_mul, map_mul, hRC, map_pow (rescale u) X N, rescale_X, mul_pow]
    simp only [map_pow]; ring
  have key : X ^ h * (C (u ^ h) * (rescale u e₁) ^ h * P * G) =
      X ^ h * (X ^ N * (e₁ ^ h * C (u ^ N) * rescale u D₁ - C (u ^ h) * (rescale u e₁) ^ h * D₁)) := by
    have h1 := hrel
    rw [hresc, hA', hR, he] at h1
    rw [mul_pow] at h1
    linear_combination h1
  have hX : (X : PowerSeries LL) ^ h ≠ 0 := pow_ne_zero _ X_ne_zero
  have key2 := mul_left_cancel₀ hX key
  have hV : IsUnit (C (u ^ h) * (rescale u e₁) ^ h * P) := by
    rw [isUnit_iff_constantCoeff]
    simp only [map_mul, map_pow, constantCoeff_C]
    have : constantCoeff (rescale u e₁) = constantCoeff e₁ := by
      rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale, pow_zero, one_mul,
        coeff_zero_eq_constantCoeff_apply]
    rw [this]
    exact (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hu) (pow_ne_zero _ he₁)) hP).isUnit
  have hdvd : X ^ N ∣ C (u ^ h) * (rescale u e₁) ^ h * P * G := ⟨_, key2⟩
  exact X_pow_dvd_iff.1 ((hV.dvd_mul_left).1 hdvd)

section Core

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem letE_mem (c : ZMod n) : (letE c : LetA O n) ∈ W.AΔ :=
  fun δ _ => Formalism.MainNotions.LiftingTheory.wmap_γA_letE W δ c

theorem algE_smul (o : O) (a : LetA O n) :
    algebraMap (LetA O n) W.EE (o • a) = o • algebraMap (LetA O n) W.EE a := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply]

theorem lev_smul (c : ZMod n) (ζ : LL) (o : O) (a : LetA O n) (i : ℕ) :
    coeff i (W.lev c ζ (o • a)) = algebraMap O LL o * coeff i (W.lev c ζ a) := by
  rw [Algebra.smul_def, map_mul, lev_alg, coeff_C_mul]

theorem expS_nat (T : LocLat G Qp LL O) (c : ZMod n) (ζ : LL) {m : ℕ} (a : Fin m → LetA O n)
    (y : Fin m → W.DD T) (i : ℕ) :
    expS W T c ζ a y i = ∑ j, coeff i (W.lev c ζ (a j)) • valAt W T c ζ (y j) := by
  unfold expS serC
  simp

theorem tmul_mem_LamLA (T : LocLat G Qp LL O) (π' Eπ : LetA O n) (h' : ℕ) (c : ZMod n) {f : W.EE}
    {a : LetA O n} (ha : a ∈ W.AΔ) (hea : (letE c : LetA O n) * a = a)
    (hΛ : algebraMap (LetA O n) W.EE (Eπ ^ h') * f = algebraMap (LetA O n) W.EE a) (z : LcQ W T π' c) :
    f ⊗ₜ z ∈ LamLA W T π' Eπ h' c ⊤ := by
  rw [ModelFPf.mem_LamLA, ModelFPf.smulLA_tmul, hΛ]
  exact ⟨⟨a, ha⟩ ⊗ₜ ⟨z, Submodule.mem_top⟩, by rw [ModelFPf.toLA_tmul, hea]⟩

theorem memNL0 (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (π' Eπ : LetA O n)
    (h' : ℕ) (c : ZMod n) {f : W.EE} {a : LetA O n} (ha : a ∈ W.AΔ) (hea : (letE c : LetA O n) * a = a)
    (hΛ : algebraMap (LetA O n) W.EE (Eπ ^ h') * f = algebraMap (LetA O n) W.EE a)
    (x : W.DD T) (hx : x ∈ NcS W T (c - 1))
    (H : ∀ τ ζ, Pt c ζ τ → ∃ m : ℕ, (∀ i < m, coeff i (W.lev c ζ a) = 0) ∧
      valAt W T c ζ x ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ ((h' : ℤ) - m)) :
    f ⊗ₜ mkL W T π' c x hx ∈ NL W T Pt π' Eπ h' c := by
  apply Submodule.subset_span
  refine ⟨1, fun _ => ⟨a, ha⟩, fun _ => x, ⟨fun _ => hx, ?_⟩, ?_⟩
  · rw [Fin.sum_univ_one, ModelFPf.smulLA_tmul, hΛ, hea]
  · intro τ ζ hpt i
    obtain ⟨m, h1, h2⟩ := H τ ζ hpt
    show (∑ j : Fin 1, serC (W.lev c ζ a) (valAt W T c ζ x) i) ∈ _
    rw [Fin.sum_univ_one]
    unfold serC
    split_ifs with hi
    · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hi
      simp only [Int.toNat_natCast]
      by_cases hlt : k < m
      · rw [h1 k hlt, zero_smul]
        exact Submodule.zero_mem _
      · exact Submodule.smul_mem _ _ (u3upPf_FilC_anti T τ (by omega) h2)
    · exact Submodule.zero_mem _

theorem tmul_mkL_mem_InvL_of_valAt_mem_filC (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop)
    (π' Eπ : LetA O n) (h' S : ℕ) (up : (K →ₐ[Qp] LL) → Bool) (b : (K →ₐ[Qp] LL) → ℕ) (c : ZMod n)
    (hπu : IsUnit (algebraMap (LetA O n) W.EE π')) (hEu : IsUnit (algebraMap (LetA O n) W.EE Eπ))
    (hP : ∀ τ ζ, Pt c ζ τ → constantCoeff (W.lev c ζ π') ≠ 0)
    (hE : ∀ τ ζ, Pt c ζ τ → ∃ e₁ : PowerSeries LL, W.lev c ζ Eπ = X * e₁ ∧ constantCoeff e₁ ≠ 0)
    (hΓ : ∀ τ ζ, Pt c ζ τ → ∃ u : LL, u ≠ 0 ∧
      ∀ a, W.lev c ζ (W.γA W.gamK a) = rescale u (W.lev c ζ a))
    (f : W.EE) (hf : IsCoord W Pt π' Eπ h' S up b c f) :
    ∃ g : ↥W.AΔ, (∀ τ ζ, Pt c ζ τ → up τ = true → ∀ i < h' - b τ, coeff i (W.lev c ζ g) = 0) ∧
      (∀ τ ζ, Pt c ζ τ → up τ = false → ∀ i < h' + b τ + S, coeff i (W.lev c ζ g) = 0) ∧
      ∀ (T : LocLat G Qp LL O) (x : W.DD T) (hx : x ∈ NcS W T (c - 1)),
        (∀ τ ζ, Pt c ζ τ → ∃ m : ℕ, (∀ i < m, coeff i (W.lev c ζ g) = 0) ∧
          valAt W T c ζ x ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ ((h' : ℤ) - m)) →
        f ⊗ₜ mkL W T π' c x hx ∈ InvL W T Pt π' Eπ h' c ⊤ := by
  obtain ⟨a, ha, hea, hΛ, hup, hdn, g, hg, hγ⟩ := hf
  have hΛu : IsUnit (algebraMap (LetA O n) W.EE (Eπ ^ h')) := by rw [map_pow]; exact hEu.pow _
  have hef : algebraMap (LetA O n) W.EE (letE c) * f = f := by
    apply hΛu.mul_left_cancel
    rw [← mul_assoc, mul_comm (algebraMap (LetA O n) W.EE (Eπ ^ h')), mul_assoc, hΛ, ← map_mul, hea]
  have hγe : W.γE W.gamK (algebraMap (LetA O n) W.EE (letE c)) = algebraMap (LetA O n) W.EE (letE c) := by
    rw [show W.γE W.gamK (algebraMap (LetA O n) W.EE (letE c)) =
      algebraMap (LetA O n) W.EE (W.γA W.gamK (letE c)) from W.γE_ext _ _, Formalism.MainNotions.LiftingTheory.wmap_γA_letE]
  have hegf : algebraMap (LetA O n) W.EE (letE c) * (W.γE W.gamK f - f) = W.γE W.gamK f - f := by
    rw [mul_sub, hef]
    congr 1
    conv_rhs => rw [← hef]
    rw [map_mul, hγe]
  have heg : (letE c : LetA O n) * g = g := by
    apply W.EE_inj
    apply hπu.mul_left_cancel
    calc algebraMap (LetA O n) W.EE π' * algebraMap (LetA O n) W.EE (letE c * g)
        = algebraMap (LetA O n) W.EE (letE c) * algebraMap (LetA O n) W.EE (π' * g) := by
          rw [map_mul, map_mul]; ring
      _ = algebraMap (LetA O n) W.EE (letE c) * (algebraMap (LetA O n) W.EE (Eπ ^ h') * (W.γE W.gamK f - f)) := by
          rw [hγ]
      _ = algebraMap (LetA O n) W.EE (Eπ ^ h') * (algebraMap (LetA O n) W.EE (letE c) * (W.γE W.gamK f - f)) := by
          ring
      _ = algebraMap (LetA O n) W.EE π' * algebraMap (LetA O n) W.EE g := by rw [hegf, hγ, map_mul]
  have hA : W.γA W.gamK (Eπ ^ h') * (π' * g) = Eπ ^ h' * W.γA W.gamK a - W.γA W.gamK (Eπ ^ h') * a := by
    apply W.EE_inj
    have h1 : algebraMap (LetA O n) W.EE (W.γA W.gamK a) =
        W.γE W.gamK (algebraMap (LetA O n) W.EE (Eπ ^ h')) * W.γE W.gamK f := by
      rw [← map_mul, hΛ]; exact (W.γE_ext _ _).symm
    have h2 : algebraMap (LetA O n) W.EE (W.γA W.gamK (Eπ ^ h')) =
        W.γE W.gamK (algebraMap (LetA O n) W.EE (Eπ ^ h')) := (W.γE_ext _ _).symm
    have hγ' : algebraMap (LetA O n) W.EE π' * algebraMap (LetA O n) W.EE g =
        algebraMap (LetA O n) W.EE (Eπ ^ h') * (W.γE W.gamK f - f) := by rw [← map_mul, hγ]
    simp only [map_mul, map_sub]
    rw [h1, h2, hγ', ← hΛ]
    ring
  have hG0 : ∀ τ ζ, Pt c ζ τ → ∀ (x₀ : LL) (N : ℕ),
      (∀ i < N, coeff i (W.lev c ζ a) = x₀ * coeff i (W.lev c ζ (Eπ ^ h'))) →
      ∀ k < N, coeff k (W.lev c ζ g) = 0 := by
    intro τ ζ hpt x₀ N hx₀
    obtain ⟨e₁, he, he₁⟩ := hE τ ζ hpt
    obtain ⟨u, hu, hu2⟩ := hΓ τ ζ hpt
    have hl := congrArg (W.lev c ζ) hA
    simp only [map_mul, map_sub] at hl
    rw [hu2, hu2, map_pow] at hl
    refine ser_van (W.lev c ζ Eπ) e₁ (W.lev c ζ π') (W.lev c ζ g) (W.lev c ζ a) u x₀ h' N
      he he₁ (hP τ ζ hpt) hu (by linear_combination hl) (fun i hi => ?_)
    rw [hx₀ i hi, map_pow]
  refine ⟨⟨g, hg⟩, fun τ ζ hpt hu => hG0 τ ζ hpt 0 _ fun i hi => ?_, fun τ ζ hpt hd => ?_,
    fun T x hx H => Submodule.mem_inf.2 ⟨tmul_mem_LamLA W T π' Eπ h' c ha hea hΛ _, ?_⟩⟩
  · rw [hup τ ζ hpt hu i (by omega), zero_mul]
  · obtain ⟨x₀, hx₀⟩ := hdn τ ζ hpt hd
    exact hG0 τ ζ hpt x₀ _ hx₀
  · rw [Submodule.mem_comap]
    rw [LinearMap.sub_apply, ModelFPf.γLA_tmul, LinearMap.id_apply, ← TensorProduct.sub_tmul]
    refine Submodule.mem_map.2 ⟨((↑hπu.unit⁻¹ : W.EE) * (W.γE W.gamK f - f)) ⊗ₜ mkL W T π' c x hx,
      memNL0 W T Pt π' Eπ h' c hg heg ?_ x hx H, ?_⟩
    · rw [mul_left_comm, hγ, map_mul, ← mul_assoc, hπu.val_inv_mul, one_mul]
    · rw [ModelFPf.smulLA_tmul, pow_one, ← mul_assoc, hπu.mul_val_inv, one_mul]

variable {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop} {π' Eπ : LetA O n} {h' M σ : ℕ} {c : ZMod n}
    {α : FrA W π' Eπ h' M c} {β : FrB W π' Eπ h' M c}

theorem lifts_mono {y y' : ℕ} (h : y ≤ y') {z : W.DD T₂} (H : LiftsBy W F π' Eπ h' y c z) :
    LiftsBy W F π' Eπ h' y' c z := by
  obtain ⟨h1, w, hw, h2⟩ := H
  refine ⟨h1, ((PD.p : ℕ) : O) ^ (y' - y) • w, Submodule.smul_mem _ _ hw, ?_⟩
  rw [LinearMap.map_smul_of_tower, show y' = (y' - y) + y by omega, pow_add, mul_smul,
    Nat.add_sub_cancel, ← smul_sub]
  exact Submodule.smul_mem _ _ h2

variable (hfr : IsFrame W Pt π' Eπ h' M σ c α β) (hc1 : IsCrys PD T₁.ρ) (hc2 : IsCrys PD T₂.ρ)
    (hj1 : ∀ τ, JumpsInV PD T₁.ρ τ (Set.Icc (-(h' : ℤ)) h'))
    (hj2 : ∀ τ, JumpsInV PD T₂.ρ τ (Set.Icc (-(h' : ℤ)) h'))
    (hMF1 : ModelF W T₁ Pt π' Eπ h' M c α β) (hMF2 : ModelF W T₂ Pt π' Eπ h' M c α β) (hM : 1 ≤ M)

include hfr hc1 hc2 hj1 hj2 hMF1 hMF2 hM in

theorem core (f : W.EE) (x : W.DD T₂) (hx : x ∈ NcS W T₂ (c - 1)) (x₁ : W.DD T₁)
    (hx₁ : x₁ ∈ NcS W T₁ (c - 1)) (ρ : ℕ)
    (hdiff : W.map F x₁ - ((PD.p : ℕ) : O) ^ ρ • x ∈ PiNS W T₂ π' 1)
    (hI1 : f ⊗ₜ mkL W T₁ π' c x₁ hx₁ ∈ InvL W T₁ Pt π' Eπ h' c ⊤)
    (hI2 : f ⊗ₜ mkL W T₂ π' c x hx ∈ InvL W T₂ Pt π' Eπ h' c ⊤)
    (h1 : f ⊗ₜ mkL W T₂ π' c x hx ∈ LamLA W T₂ π' Eπ h' c ⊤) (y : W.DD T₂) (hy : y ∈ LamPS W T₂ Eπ h' c)
    (hα : α T₂ ⟨_, h1⟩ = mkP W T₂ π' Eπ h' M c y hy) : LiftsBy W F π' Eπ h' ρ c y := by
  have hyI : y ∈ InvS W T₂ π' Eπ h' 1 c := hMF2.2.2.2.1 _ h1 y hy hα hI2
  have hL1 : f ⊗ₜ mkL W T₁ π' c x₁ hx₁ ∈ LamLA W T₁ π' Eπ h' c ⊤ := (Submodule.mem_inf.1 hI1).1
  obtain ⟨w₁, hw₁⟩ := Submodule.Quotient.mk_surjective _ (α T₁ ⟨_, hL1⟩)
  have hw₁I : (w₁ : W.DD T₁) ∈ InvS W T₁ π' Eπ h' 1 c := hMF1.2.2.2.1 _ hL1 w₁ w₁.2 hw₁.symm hI1
  have hmx : W.map F x₁ ∈ NcS W T₂ (c - 1) := u3downPf_map_NcS W F hc1 hc2 (c - 1) hx₁
  have heq : mkL W T₂ π' c (W.map F x₁) hmx = ((PD.p : ℕ) : O) ^ ρ • mkL W T₂ π' c x hx :=
    u3downPf_mkL_eq W T₂ π' c hx hmx _ hdiff
  have hL2 : f ⊗ₜ mkL W T₂ π' c (W.map F x₁) hmx ∈ LamLA W T₂ π' Eπ h' c ⊤ := by
    rw [heq, TensorProduct.tmul_smul]
    exact Submodule.smul_mem _ _ h1
  have hy₂ : W.map F (w₁ : W.DD T₁) ∈ LamPS W T₂ Eπ h' c := univLinkPf_map_LamPS W F hc1 hc2 Eπ h' c w₁.2
  have hnat := (hfr.2 T₁ T₂ F hc1 hc2 hj1 hj2).1 _ hL1 _ hL2 _ w₁.2 hy₂
    ⟨1, fun _ => f, fun _ => x₁, fun _ => hx₁, fun _ => hmx, by simp, by simp⟩ hw₁.symm
  have hsub : (⟨_, hL2⟩ : ↥(LamLA W T₂ π' Eπ h' c ⊤)) = ((PD.p : ℕ) : O) ^ ρ • ⟨_, h1⟩ :=
    Subtype.ext (by simp [heq, TensorProduct.tmul_smul])
  rw [hsub, map_smul, hα] at hnat
  have hJ : Submodule.Quotient.mk (((PD.p : ℕ) : O) ^ ρ • (⟨y, hy⟩ : ↥(LamPS W T₂ Eπ h' c)) - ⟨_, hy₂⟩) =
      (0 : QLamP W T₂ π' Eπ h' M c) := by
    rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul, sub_eq_zero]
    exact hnat
  have hP := univLinkPf_PiNS_anti W T₂ π' hM (univLinkPf_JP W T₂ hMF2 hM _ hJ)
  refine ⟨hyI, w₁, hw₁I, ?_⟩
  simpa using hP

include hMF2 hM in

theorem combine (ρ y : ℕ) (o : O) (X XK XN : ↥(LamLA W T₂ π' Eπ h' c ⊤))
    (hX : ((PD.p : ℕ) : O) ^ y • X = o • XK + XN)
    (hK : ∀ z hz, α T₂ XK = mkP W T₂ π' Eπ h' M c z hz → LiftsBy W F π' Eπ h' ρ c z)
    (hN : ∀ z hz, α T₂ XN = mkP W T₂ π' Eπ h' M c z hz → LiftsBy W F π' Eπ h' ρ c z)
    (z : W.DD T₂) (hz : z ∈ LamPS W T₂ Eπ h' c) (hα : α T₂ X = mkP W T₂ π' Eπ h' M c z hz)
    (hzI : z ∈ InvS W T₂ π' Eπ h' 1 c) : LiftsBy W F π' Eπ h' (ρ + y) c z := by
  obtain ⟨zK, hzK⟩ := Submodule.Quotient.mk_surjective _ (α T₂ XK)
  obtain ⟨zN, hzN⟩ := Submodule.Quotient.mk_surjective _ (α T₂ XN)
  obtain ⟨-, wK, hwK, hK'⟩ := hK zK zK.2 hzK.symm
  obtain ⟨-, wN, hwN, hN'⟩ := hN zN zN.2 hzN.symm
  have h1 := congrArg (α T₂) hX
  rw [map_smul, map_add, map_smul, hα, ← hzK, ← hzN] at h1
  have hJ : Submodule.Quotient.mk (((PD.p : ℕ) : O) ^ y • (⟨z, hz⟩ : ↥(LamPS W T₂ Eπ h' c)) -
      (o • zK + zN)) = (0 : QLamP W T₂ π' Eπ h' M c) := by
    rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul, Submodule.Quotient.mk_add,
      Submodule.Quotient.mk_smul, sub_eq_zero]
    exact h1
  have hP : ((PD.p : ℕ) : O) ^ y • z - (o • (zK : W.DD T₂) + zN) ∈ PiNS W T₂ π' 1 :=
    univLinkPf_PiNS_anti W T₂ π' hM (univLinkPf_JP W T₂ hMF2 hM _ hJ)
  refine ⟨hzI, o • wK + wN, Submodule.add_mem _ (Submodule.smul_mem _ _ hwK) hwN, ?_⟩
  have h2 := Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.smul_mem _ (((PD.p : ℕ) : O) ^ ρ) hP) (Submodule.smul_mem _ o hK')) hN'
  convert h2 using 1
  rw [map_add, LinearMap.map_smul_of_tower, pow_add]
  module

theorem NL_rep (T : LocLat G Qp LL O) {x : LA W T π' c} (hx : x ∈ NL W T Pt π' Eπ h' c) :
    x ∈ NLset W T Pt π' Eπ h' c := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact hx
  | zero =>
    refine ⟨0, Fin.elim0, Fin.elim0, ⟨fun j => j.elim0, by simp⟩, fun τ ζ _ i => ?_⟩
    simp [expS]
  | add x y _ _ hx hy =>
    obtain ⟨m, a, u, ⟨hu, hx1⟩, hx2⟩ := hx
    obtain ⟨m', a', u', ⟨hu', hy1⟩, hy2⟩ := hy
    let U : Fin (m + m') → ↥(NcS W T (c - 1)) :=
      Fin.append (fun j => ⟨u j, hu j⟩) (fun j => ⟨u' j, hu' j⟩)
    refine ⟨m + m', Fin.append a a', fun j => U j, ⟨fun j => (U j).2, ?_⟩, fun τ ζ hpt i => ?_⟩
    · rw [map_add, hx1, hy1, Fin.sum_univ_add]
      simp only [U, Fin.append_left, Fin.append_right]
    · have := Submodule.add_mem _ (hx2 τ ζ hpt i) (hy2 τ ζ hpt i)
      unfold expS at this ⊢
      rw [Fin.sum_univ_add]
      simpa only [U, Fin.append_left, Fin.append_right] using this
  | smul o x _ hx =>
    obtain ⟨m, a, u, ⟨hu, hx1⟩, hx2⟩ := hx
    refine ⟨m, fun j => o • a j, u, ⟨hu, ?_⟩, fun τ ζ hpt i => ?_⟩
    · rw [map_smul, hx1, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [TensorProduct.smul_tmul', Subalgebra.coe_smul, mul_smul_comm, algE_smul]
    · have := Submodule.smul_mem _ (algebraMap O LL o) (hx2 τ ζ hpt i)
      convert this using 1
      unfold expS serC
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs
      · beta_reduce
        rw [Subalgebra.coe_smul, lev_smul, smul_smul]
      · rw [smul_zero]

include hfr hc1 hc2 hj1 hj2 hMF1 hMF2 in

theorem compare {ρ : ℕ} (hW : WKill W F ρ) (hNL : NinLam W T₁ Eπ h') (V₂ : ValH W T₂ Pt π' c)
    (hEu : IsUnit (algebraMap (LetA O n) W.EE Eπ)) (hh : 1 ≤ h')
    (hE : ∀ τ ζ, Pt c ζ τ → ∃ e₁ : PowerSeries LL, W.lev c ζ Eπ = X * e₁ ∧ constantCoeff e₁ ≠ 0)
    {f₀ : W.EE} {a₀ : LetA O n} (hea : (letE c : LetA O n) * a₀ = a₀)
    (hΛ : algebraMap (LetA O n) W.EE (Eπ ^ h') * f₀ = algebraMap (LetA O n) W.EE a₀)
    (x : W.DD T₂) (hx : x ∈ NcS W T₂ (c - 1)) (hN : f₀ ⊗ₜ mkL W T₂ π' c x hx ∈ NL W T₂ Pt π' Eπ h' c) :
    ∃ (m : ℕ) (a : Fin m → ↥W.AΔ) (y : Fin m → W.DD T₁), (∀ j, y j ∈ NcS W T₁ (c - 1)) ∧
      (∀ τ ζ, Pt c ζ τ → Gd (Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T₁ τ) h' (fun j => evA W c ζ (a j))
        (fun j => valAt W T₁ c ζ (y j))) ∧
      ∀ τ ζ, Pt c ζ τ → ∀ i ≤ h', ∑ j, coeff i (evA W c ζ (a j)) • valAt W T₂ c ζ (W.map F (y j)) =
        coeff i (C ((PD.p : LL) ^ (ρ + 2 * σ)) * W.lev c ζ a₀) • valAt W T₂ c ζ x := by
  have hx₀ := ModelFPf.NL_le_LamLA W T₂ π' Eπ h' c Pt hN
  obtain ⟨n₂, hn₂, hn₂N, hα⟩ := hMF2.1 _ hx₀ hN
  obtain ⟨n₁, hn₁, hF⟩ := hW c n₂ hn₂N
  obtain ⟨ν, hν, hνN, hβ⟩ := hMF1.2.1 n₁ (hNL c hn₁) hn₁
  obtain ⟨m, a, y, ⟨hy, hrep⟩, hfil⟩ := NL_rep W T₁ hνN
  have hΛu : IsUnit (algebraMap (LetA O n) W.EE (Eπ ^ h')) := by rw [map_pow]; exact hEu.pow _
  have hy2 : ∀ j, W.map F (y j) ∈ NcS W T₂ (c - 1) := fun j => u3downPf_map_NcS W F hc1 hc2 _ (hy j)
  set e : Fin m → W.EE := fun j =>
    (↑hΛu.unit⁻¹ : W.EE) * algebraMap (LetA O n) W.EE ((letE c : LetA O n) * a j) with he
  have hΛe : ∀ (T : LocLat G Qp LL O) (z : Fin m → LcQ W T π' c),
      smulLA W T π' c (Eπ ^ h') (∑ j, e j ⊗ₜ z j) =
        ∑ j, algebraMap (LetA O n) W.EE ((letE c : LetA O n) * a j) ⊗ₜ z j := by
    intro T z
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ModelFPf.smulLA_tmul, he, ← mul_assoc, hΛu.mul_val_inv, one_mul]
  have hinjΛ : Function.Injective (smulLA W T₁ π' c (Eπ ^ h')) := by
    have hl : ∀ z, TensorProduct.map (LinearMap.mulLeft O (↑hΛu.unit⁻¹ : W.EE)) LinearMap.id
        (smulLA W T₁ π' c (Eπ ^ h') z) = z := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul u w =>
        rw [ModelFPf.smulLA_tmul, TensorProduct.map_tmul, LinearMap.mulLeft_apply, LinearMap.id_apply,
          ← mul_assoc, hΛu.val_inv_mul, one_mul]
      | add u w hu hw => simp only [map_add, hu, hw]
    exact Function.LeftInverse.injective hl
  have hν1 : ν = ∑ j, e j ⊗ₜ mkL W T₁ π' c (y j) (hy j) := hinjΛ (by rw [hrep, hΛe])
  have hν₂ : ∑ j, e j ⊗ₜ mkL W T₂ π' c (W.map F (y j)) (hy2 j) ∈ LamLA W T₂ π' Eπ h' c ⊤ := by
    rw [ModelFPf.mem_LamLA, hΛe]
    exact ModelFPf.rep_mem W T₂ π' c _ (fun j => (a j).2) _ hy2
  have hy₂ : W.map F n₁ ∈ LamPS W T₂ Eπ h' c := univLinkPf_map_LamPS W F hc1 hc2 Eπ h' c (hNL c hn₁)
  have hβ₂ := (hfr.2 T₁ T₂ F hc1 hc2 hj1 hj2).2 n₁ (hNL c hn₁) hy₂ ν hν _ hν₂
    ⟨m, e, y, hy, hy2, hν1, rfl⟩ hβ
  have hβα := (hfr.1 T₂ hc2 hj2).2.2.1 _ hx₀ n₂ hn₂ hα
  have hsub : (⟨_, hy₂⟩ : ↥(LamPS W T₂ Eπ h' c)) = ((PD.p : ℕ) : O) ^ ρ • ⟨n₂, hn₂⟩ := Subtype.ext hF
  rw [hsub, map_smul, hβα] at hβ₂
  unfold mkLA at hβ₂
  rw [← Submodule.Quotient.mk_smul, eq_comm, Submodule.Quotient.eq, Submodule.mem_comap] at hβ₂
  obtain ⟨u, hu, hue⟩ := Submodule.mem_map.1 hβ₂
  obtain ⟨m', b, z, hz, rfl⟩ := ModelFPf.range_rep W T₂ π' c u hu
  have hue' := congrArg (smulLA W T₂ π' c (Eπ ^ h')) hue
  simp only [Submodule.subtype_apply, Submodule.coe_sub, Submodule.coe_smul] at hue'
  rw [map_sub, hΛe, ModelFPf.smulLA_smulLA, ModelFPf.smulLA_rep, map_smul, map_smul,
    ModelFPf.smulLA_tmul, hΛ] at hue'
  refine ⟨m, a, y, hy, fun τ ζ hpt i => ?_, fun τ ζ hpt i hi => ?_⟩
  · have := hfil τ ζ hpt i
    rw [expS_nat] at this
    exact this
  · let Zs : Fin (m' + 1) → ↥(NcS W T₂ (c - 1)) := Fin.cons ⟨x, hx⟩ fun k => ⟨z k, hz k⟩
    let Bs : Fin (m' + 1) → LetA O n := Fin.cons (algebraMap O (LetA O n) (((PD.p : ℕ) : O) ^ (ρ + 2 * σ)) * a₀)
      fun k => Eπ ^ h' * (π' ^ M * Eπ ^ (3 * h')) * b k
    have hwd := V₂.wd τ ζ hpt (fun j => (a j : LetA O n)) (fun j => W.map F (y j)) hy2 Bs
      (fun k => Zs k) (fun k => (Zs k).2) (by
        rw [Fin.sum_univ_succ]
        simp only [Zs, Bs, Fin.cons_zero, Fin.cons_succ]
        rw [hue', mul_left_comm, hea, map_mul, ← IsScalarTower.algebraMap_apply, ← Algebra.smul_def,
          ← TensorProduct.smul_tmul', smul_smul, ← pow_add]
        abel)
    have h1 := congrFun hwd (i : ℤ)
    rw [expS_nat, expS_nat, Fin.sum_univ_succ] at h1
    simp only [Zs, Bs, Fin.cons_zero, Fin.cons_succ] at h1
    obtain ⟨e₁, he₁, -⟩ := hE τ ζ hpt
    rw [Finset.sum_eq_zero (s := Finset.univ) (f := fun k : Fin m' => coeff i
      (W.lev c ζ (Eπ ^ h' * (π' ^ M * Eπ ^ (3 * h')) * b k)) • valAt W T₂ c ζ (z k)) fun k _ => by
        rw [show Eπ ^ h' * (π' ^ M * Eπ ^ (3 * h')) * b k = Eπ ^ (3 * h') * (Eπ ^ h' * π' ^ M * b k) by ring,
          map_mul, map_pow, van_of_dvd he₁ _ i (by omega), zero_smul], add_zero, map_mul, lev_alg, map_pow,
      map_natCast] at h1
    exact h1

end Core

end Formalism.MainNotions.N.Ln34.LevelExpansions

end
