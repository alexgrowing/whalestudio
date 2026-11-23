import Formalism.SharpRestriction.LevelLetterCocycles.UpPositionHypothesis
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.UnivLinkPfA
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.U3upPfFilCAnti
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfPt

noncomputable section

namespace Formalism.MainNotions.N.Ln34.DescentValuation

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct
open Formalism.MainNotions.N.Ln34 Formalism.MainNotions.N.Ln34.UnivLinkPf

section Series

open PowerSeries

theorem u3downPf_series {LL : Type} [Field LL] (e e₁ P G A : PowerSeries LL) (u x₀ : LL) (h m : ℕ)
    (he : e = X * e₁) (he₁ : constantCoeff e₁ ≠ 0) (hP : constantCoeff P ≠ 0) (hu : u ≠ 0)
    (hrel : rescale u (e ^ h) * P * G = e ^ h * rescale u A - rescale u (e ^ h) * A)
    (hA : ∀ i < h + m, coeff i A = x₀ * coeff i (e ^ h)) :
    ∀ i < h + m, coeff i G = 0 := by
  set D := A - C x₀ * e ^ h with hD
  have hXD : X ^ (h + m) ∣ D := by
    rw [X_pow_dvd_iff]
    intro i hi
    rw [hD, map_sub, coeff_C_mul, hA i hi, sub_self]
  obtain ⟨D₁, hD₁⟩ := hXD
  have hA' : A = C x₀ * e ^ h + X ^ (h + m) * D₁ := by rw [← hD₁, hD]; ring
  have hR : rescale u (e ^ h) = X ^ h * (C (u ^ h) * (rescale u e₁) ^ h) := by
    rw [map_pow, he, map_mul, rescale_X, mul_pow, mul_pow]; simp only [map_pow]; ring
  have hRC : rescale u (C x₀) = C x₀ := by
    ext k
    rw [coeff_rescale, coeff_C]
    split_ifs with hk
    · subst hk; simp
    · simp
  have hresc : rescale u A = C x₀ * rescale u (e ^ h) + X ^ (h + m) * (C (u ^ (h + m)) * rescale u D₁) := by
    rw [hA', map_add, map_mul, map_mul, hRC, map_pow (rescale u) X (h + m), rescale_X, mul_pow]
    simp only [map_pow]; ring
  have key : X ^ h * (C (u ^ h) * (rescale u e₁) ^ h * P * G) =
      X ^ h * (X ^ (h + m) * (e₁ ^ h * C (u ^ (h + m)) * rescale u D₁ - C (u ^ h) * (rescale u e₁) ^ h * D₁)) := by
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
      rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale, pow_zero, one_mul, coeff_zero_eq_constantCoeff_apply]
    rw [this]
    exact (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hu) (pow_ne_zero _ he₁)) hP).isUnit
  have hdvd : X ^ (h + m) ∣ C (u ^ h) * (rescale u e₁) ^ h * P * G := ⟨_, key2⟩
  have hG : X ^ (h + m) ∣ G := (hV.dvd_mul_left).1 hdvd
  exact (X_pow_dvd_iff.1 hG)

end Series

section Fil

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem u3downPf_fildR_const (T : LocLat G Qp LL O) (τ : K →ₐ[Qp] LL) (m : ℤ)
    (hj : ∀ a, IsJumpV PD T.ρ τ a → m ≤ a) : ∀ a ≤ m, FildR PD T.ρ τ a = FildR PD T.ρ τ m := by
  have key : ∀ d : ℕ, FildR PD T.ρ τ (m - d) = FildR PD T.ρ τ m := by
    intro d
    induction d with
    | zero => simp
    | succ d ih =>
      have hn : ¬ IsJumpV PD T.ρ τ (m - ((d + 1 : ℕ) : ℤ)) := fun hJ => by have := hj _ hJ; omega
      have hn' : FildR PD T.ρ τ (m - ((d + 1 : ℕ) : ℤ) + 1) = FildR PD T.ρ τ (m - ((d + 1 : ℕ) : ℤ)) := by
        by_contra hc; exact hn hc
      rw [← hn', show m - ((d + 1 : ℕ) : ℤ) + 1 = m - (d : ℤ) by push_cast; ring, ih]
  intro a ha
  have := key (m - a).toNat
  rwa [show m - ((m - a).toNat : ℤ) = a by omega] at this

theorem u3downPf_filC_low (T : LocLat G Qp LL O) (τ : K →ₐ[Qp] LL) (m : ℤ)
    (hj : ∀ a, IsJumpV PD T.ρ τ a → m ≤ a) {a k : ℤ} (ha : a ≤ m) {z : T.V ⊗[Qp] BdR}
    (hz : z ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ k) : z ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ a := by
  have hc : Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ a = Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ m := by
    unfold Formalism.MainNotions.DeltaInvariantLattices.FilC
    rw [u3downPf_fildR_const T τ m hj a ha]
  rw [hc]
  rcases le_total k m with hkm | hkm
  · have hk : Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ k = Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ m := by
      unfold Formalism.MainNotions.DeltaInvariantLattices.FilC
      rw [u3downPf_fildR_const T τ m hj k hkm]
    rwa [← hk]
  · exact u3upPf_FilC_anti T τ hkm hz

end Fil

section LemC

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem u3downPf_lemC (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop)
    (π' Eπ : LetA O n) (h' S : ℕ) (up : (K →ₐ[Qp] LL) → Bool) (b : (K →ₐ[Qp] LL) → ℕ) (c : ZMod n)
    (hπu : IsUnit (algebraMap (LetA O n) W.EE π')) (hEu : IsUnit (algebraMap (LetA O n) W.EE Eπ))
    (hdown : ∀ τ ζ, Pt c ζ τ → up τ = false)
    (hP : ∀ τ ζ, Pt c ζ τ → PowerSeries.constantCoeff (W.lev c ζ π') ≠ 0)
    (hE : ∀ τ ζ, Pt c ζ τ → ∃ e₁ : PowerSeries LL, W.lev c ζ Eπ = PowerSeries.X * e₁ ∧
      PowerSeries.constantCoeff e₁ ≠ 0)
    (hΓ : ∀ τ ζ, Pt c ζ τ → ∃ u : LL, u ≠ 0 ∧
      ∀ a, W.lev c ζ (W.γA W.gamK a) = PowerSeries.rescale u (W.lev c ζ a))
    (hval : ∀ x ∈ NcS W T (c - 1), ∀ τ ζ, Pt c ζ τ →
      ∃ k : ℤ, valAt W T c ζ x ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ k)
    (hjump : ∀ τ ζ, Pt c ζ τ → ∀ a, IsJumpV PD T.ρ τ a → -((b τ : ℤ) + S) ≤ a)
    (x : W.DD T) (hx : x ∈ NcS W T (c - 1)) (f : W.EE) (hf : IsCoord W Pt π' Eπ h' S up b c f) :
    f ⊗ₜ mkL W T π' c x hx ∈ InvL W T Pt π' Eπ h' c ⊤ := by
  obtain ⟨a, ha, hea, hΛ, -, hdn, g, hg, hγ⟩ := hf
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
  have hG0 : ∀ τ ζ, Pt c ζ τ → ∀ k < h' + (b τ + S), PowerSeries.coeff k (W.lev c ζ g) = 0 := by
    intro τ ζ hpt
    obtain ⟨e₁, he, he₁⟩ := hE τ ζ hpt
    obtain ⟨u, hu, hu2⟩ := hΓ τ ζ hpt
    obtain ⟨x₀, hx₀⟩ := hdn τ ζ hpt (hdown τ ζ hpt)
    have hl := congrArg (W.lev c ζ) hA
    simp only [map_mul, map_sub] at hl
    rw [hu2, hu2, map_pow] at hl
    refine u3downPf_series (W.lev c ζ Eπ) e₁ (W.lev c ζ π') (W.lev c ζ g) (W.lev c ζ a) u x₀ h' (b τ + S)
      he he₁ (hP τ ζ hpt) hu (by linear_combination hl) (fun i hi => ?_)
    rw [hx₀ i (by omega), map_pow]
  refine Submodule.mem_inf.2 ⟨?_, ?_⟩
  · unfold LamLA
    rw [Submodule.mem_comap, LinearMap.mem_range]
    refine ⟨⟨a, ha⟩ ⊗ₜ ⟨mkL W T π' c x hx, Submodule.mem_top⟩, ?_⟩
    simp only [toLA, smulLA, TensorProduct.map_tmul, LinearMap.comp_apply, LinearMap.mulLeft_apply,
      LinearMap.id_apply, Submodule.subtype_apply]
    rw [hΛ]
    congr 1
    show algebraMap (LetA O n) W.EE ((letE c : LetA O n) * a) = _
    rw [hea]
  · rw [Submodule.mem_comap]
    have hsub : (γLA W T π' c - LinearMap.id : LA W T π' c →ₗ[O] LA W T π' c) (f ⊗ₜ mkL W T π' c x hx) =
        (W.γE W.gamK f - f) ⊗ₜ mkL W T π' c x hx := by
      simp [γLA, TensorProduct.sub_tmul]
    rw [hsub]
    unfold piNL
    rw [Submodule.mem_map]
    refine ⟨((↑hπu.unit⁻¹ : W.EE) * (W.γE W.gamK f - f)) ⊗ₜ mkL W T π' c x hx, ?_, ?_⟩
    · apply Submodule.subset_span
      refine ⟨1, fun _ => ⟨g, hg⟩, fun _ => x, ⟨fun _ => hx, ?_⟩, ?_⟩
      · rw [Fin.sum_univ_one]
        show TensorProduct.map (LinearMap.mulLeft O (algebraMap (LetA O n) W.EE (Eπ ^ h'))) LinearMap.id
            (((↑hπu.unit⁻¹ : W.EE) * (W.γE W.gamK f - f)) ⊗ₜ mkL W T π' c x hx) =
          algebraMap (LetA O n) W.EE ((letE c : LetA O n) * g) ⊗ₜ mkL W T π' c x hx
        rw [TensorProduct.map_tmul, LinearMap.mulLeft_apply, LinearMap.id_apply, heg, mul_left_comm, hγ,
          map_mul, ← mul_assoc, hπu.val_inv_mul, one_mul]
      · intro τ ζ hpt i
        show (∑ j : Fin 1, serC (W.lev c ζ g) (valAt W T c ζ x) i) ∈ _
        rw [Fin.sum_univ_one]
        unfold serC
        split_ifs with hi
        · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hi
          simp only [Int.toNat_natCast]
          by_cases hk : k < h' + (b τ + S)
          · rw [hG0 τ ζ hpt k hk, zero_smul]
            exact Submodule.zero_mem _
          · apply Submodule.smul_mem
            obtain ⟨k₀, hk₀⟩ := hval x hx τ ζ hpt
            exact u3downPf_filC_low T τ _ (hjump τ ζ hpt) (by omega) hk₀
        · exact Submodule.zero_mem _
    · show TensorProduct.map (LinearMap.mulLeft O (algebraMap (LetA O n) W.EE (π' ^ 1))) LinearMap.id
          (((↑hπu.unit⁻¹ : W.EE) * (W.γE W.gamK f - f)) ⊗ₜ mkL W T π' c x hx) = _
      rw [TensorProduct.map_tmul, LinearMap.mulLeft_apply, LinearMap.id_apply, pow_one, ← mul_assoc,
        hπu.mul_val_inv, one_mul]

end LemC

section Pts

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem u3downPf_cc_unit (c : ZMod n) (ζ : LL) (w : (LetA O n)ˣ) :
    PowerSeries.constantCoeff (W.lev c ζ (w : LetA O n)) ≠ 0 := by
  intro h
  have h1 := congrArg (fun z => PowerSeries.constantCoeff (W.lev c ζ z)) w.mul_inv
  simp only [map_mul, map_one, h, zero_mul] at h1
  exact zero_ne_one h1

theorem u3downPf_cc_π (c : ZMod n) (ζ : LL) (hζ : IsPrimitiveRoot ζ PD.p) :
    PowerSeries.constantCoeff (W.lev c ζ letπ) ≠ 0 := by
  obtain ⟨E, hE0, -, hE⟩ := W.lev_π c ζ ⟨1, by simpa using hζ⟩
  have hζ1 : ζ ≠ 1 := hζ.ne_one PD.hp.one_lt
  have := congrArg PowerSeries.constantCoeff hE
  rw [map_add, map_one, map_mul, PowerSeries.constantCoeff_C, hE0, mul_one] at this
  intro h0
  rw [h0, add_zero] at this
  exact hζ1 this.symm

theorem u3downPf_cc_π' (c : ZMod n) (ζ : LL) (hζ : IsPrimitiveRoot ζ PD.p) (π' : LetA O n) (s' : ℕ)
    (w : (LetA O n)ˣ) (hw : π' = (w : LetA O n) * letπ ^ s') :
    PowerSeries.constantCoeff (W.lev c ζ π') ≠ 0 := by
  rw [hw, map_mul, map_pow, map_mul, map_pow]
  exact mul_ne_zero (u3downPf_cc_unit W c ζ w) (pow_ne_zero _ (u3downPf_cc_π W c ζ hζ))

theorem u3downPf_lev_E (c : ZMod n) (ζ : LL) (hζ : IsPrimitiveRoot ζ PD.p) (Eπ : LetA O n)
    (w : (LetA O n)ˣ) (hw : W.q = (w : LetA O n) * Eπ) :
    ∃ e₁ : PowerSeries LL, W.lev c ζ Eπ = PowerSeries.X * e₁ ∧ PowerSeries.constantCoeff e₁ ≠ 0 := by
  obtain ⟨u, hu, hu0⟩ := framepf_lev_q_simple W c ζ hζ
  have hE : Eπ = ((w⁻¹ : (LetA O n)ˣ) : LetA O n) * W.q := by
    rw [hw, ← mul_assoc, Units.inv_mul, one_mul]
  refine ⟨W.lev c ζ ((w⁻¹ : (LetA O n)ˣ) : LetA O n) * u, ?_, ?_⟩
  · rw [hE, map_mul, hu]; ring
  · rw [map_mul]
    exact mul_ne_zero (u3downPf_cc_unit W c ζ w⁻¹) hu0

theorem u3downPf_valAt_fil (T : LocLat G Qp LL O) (c : ZMod n) (ζ : LL) (τ : K →ₐ[Qp] LL)
    (h4 : ∀ (x' : ↥(W.N T)) (k : ℤ), W.levN T c ζ ((letE c : LetA O n) • x') k ∈
      Formalism.MainNotions.DeltaInvariantLattices.ιDi W T c ⊓ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (-k))
    (x : W.DD T) (hx : x ∈ NcS W T (c - 1)) :
    ∃ k : ℤ, valAt W T c ζ x ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ k := by
  have key : ∀ (m : ℕ) (hm : W.Q ^ m • W.φD T x ∈ W.N T) (r : LL),
      ∃ k : ℤ, r • W.levN T c ζ ⟨_, hm⟩ (m : ℤ) ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ k := by
    intro m hm r
    refine ⟨-(m : ℤ), Submodule.smul_mem _ _ ?_⟩
    have hmem := h4 ⟨_, hm⟩ m
    have heq : ((letE c : LetA O n) • (⟨_, hm⟩ : ↥(W.N T))) = ⟨_, hm⟩ := Subtype.ext (by
      show (letE c : LetA O n) • (W.Q ^ m • W.φD T x) = W.Q ^ m • W.φD T x
      rw [smul_comm, ← φD_letE, ((mem_NcS W T (c - 1) x).1 hx).2.2])
    rw [heq] at hmem
    exact (Submodule.mem_inf.1 hmem).2
  unfold valAt
  split_ifs with h
  · exact key _ _ _
  · exact ⟨0, Submodule.zero_mem _⟩

end Pts
end Formalism.MainNotions.N.Ln34.DescentValuation
