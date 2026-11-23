import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BlockSplitAll
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsobaricDiscreteSelfDualStrongMultiplicityOne
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlockCharIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowLeSpan

noncomputable section

namespace GlobalTheory.XiOver

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

section Coeff

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc)

theorem norm_iota_le_one (b : N.O i) : ‖iotaOQ N A i b‖ ≤ 1 := by
  obtain ⟨C, hC⟩ := GlobalTheory.CoeffEmbedding.exists_norm_le N A i
  by_contra h
  rw [not_le] at h
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C h
  have := hC (b ^ n)
  rw [map_pow, norm_pow] at this
  linarith

theorem norm_iota_lt_one {c : N.O i} (hc : c ∈ IsLocalRing.maximalIdeal (N.O i)) :
    ‖iotaOQ N A i c‖ < 1 := by
  obtain ⟨e, he⟩ := GlobalTheory.CoeffEmbedding.exists_pow_le_span N A i
  have h1 : c ^ e ∈ Ideal.span {((N.l i : ℕ) : N.O i)} := he (Ideal.pow_mem_pow hc e)
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.1 h1
  have hl : ‖iotaOQ N A i ((N.l i : ℕ) : N.O i)‖ < 1 := by
    rw [map_natCast, ← map_natCast (algebraMap ℚ_[N.l i] (Qbar (N.l i))), norm_algebraMap']
    exact Padic.norm_p_lt_one
  by_contra h
  rw [not_lt] at h
  have h2 := one_le_pow₀ h (n := e)
  rw [← norm_pow, ← map_pow, hb, map_mul, norm_mul] at h2
  exact absurd ((mul_le_of_le_one_right (norm_nonneg _) (norm_iota_le_one N A i b)).trans_lt hl) (not_lt.2 h2)

theorem isUnit_of_norm {c : N.O i} (hc : ‖iotaOQ N A i c‖ = 1) : IsUnit c := by
  by_contra hu
  have := norm_iota_lt_one N A i (c := c) ((IsLocalRing.mem_maximalIdeal c).2 hu)
  linarith

theorem norm_iota_unit {c : N.O i} (hc : IsUnit c) : ‖iotaOQ N A i c‖ = 1 := by
  obtain ⟨u, rfl⟩ := hc
  have h1 := norm_iota_le_one N A i (u : N.O i)
  have h2 := norm_iota_le_one N A i ((u⁻¹ : (N.O i)ˣ) : N.O i)
  have h3 : ‖iotaOQ N A i (u : N.O i)‖ * ‖iotaOQ N A i ((u⁻¹ : (N.O i)ˣ) : N.O i)‖ = 1 := by
    rw [← norm_mul, ← map_mul, Units.mul_inv, map_one, norm_one]
  nlinarith [norm_nonneg (iotaOQ N A i (u : N.O i)), norm_nonneg (iotaOQ N A i ((u⁻¹ : (N.O i)ˣ) : N.O i))]

theorem iota_inj : Function.Injective (iotaOQ N A i) :=
  (A.iotaQ i).injective.comp (IsFractionRing.injective (N.O i) (FractionRing (N.O i)))

theorem iota_smul (z : ℤ_[N.l i]) (y : N.O i) :
    iotaOQ N A i (z • y) = algebraMap ℚ_[N.l i] (Qbar (N.l i)) (z : ℚ_[N.l i]) * iotaOQ N A i y := by
  rw [Algebra.smul_def, map_mul]
  congr 1
  exact A.iotaQ_alg i z

theorem isClosed_range_iota : IsClosed (Set.range (iotaOQ N A i)) := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ_[N.l i]) (M := N.O i)
  let f : (s → ℤ_[N.l i]) → Qbar (N.l i) := fun c =>
    ∑ y : s, algebraMap ℚ_[N.l i] (Qbar (N.l i)) (c y : ℚ_[N.l i]) * iotaOQ N A i y
  have hf : Continuous f := by
    refine continuous_finset_sum _ fun y _ => ?_
    exact ((continuous_algebraMap ℚ_[N.l i] (Qbar (N.l i))).comp
      ((continuous_subtype_val : Continuous fun x : ℤ_[N.l i] => (x : ℚ_[N.l i])).comp
        (continuous_apply y))).mul continuous_const
  have hr : Set.range (iotaOQ N A i) = Set.range f := by
    ext x
    constructor
    · rintro ⟨b, rfl⟩
      have hb : b ∈ Submodule.span ℤ_[N.l i] (s : Set (N.O i)) := hs ▸ Submodule.mem_top
      obtain ⟨c, -, rfl⟩ := Submodule.mem_span_finset.1 hb
      refine ⟨fun y => c y, ?_⟩
      rw [map_sum]
      simp only [f, iota_smul]
      exact Finset.sum_coe_sort s (fun y => algebraMap ℚ_[N.l i] (Qbar (N.l i)) (c y : ℚ_[N.l i]) * iotaOQ N A i y)
    · rintro ⟨c, rfl⟩
      refine ⟨∑ y : s, c y • (y : N.O i), ?_⟩
      rw [map_sum]
      simp only [f, iota_smul]
  rw [hr]
  exact (isCompact_range hf).isClosed

theorem mem_range_of_norm {x : FractionRing (N.O i)} (hx : ‖A.iotaQ i x‖ = 1) :
    A.iotaQ i x ∈ Set.range (iotaOQ N A i) := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  rcases ValuationRing.isInteger_or_isInteger (N.O i) x with ⟨c, hc⟩ | ⟨c, hc⟩
  · exact ⟨c, by rw [← hc]; rfl⟩
  · have h1 : ‖iotaOQ N A i c‖ = 1 := by
      show ‖A.iotaQ i (algebraMap _ _ c)‖ = 1
      rw [hc, map_inv₀, norm_inv, hx, inv_one]
    obtain ⟨u, rfl⟩ := isUnit_of_norm N A i h1
    refine ⟨((u⁻¹ : (N.O i)ˣ) : N.O i), ?_⟩
    show A.iotaQ i (algebraMap _ _ _) = _
    congr 1
    have h2 : algebraMap (N.O i) (FractionRing (N.O i)) (u : N.O i) * algebraMap (N.O i) (FractionRing (N.O i)) ((u⁻¹ : (N.O i)ˣ) : N.O i) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    rw [hc] at h2
    field_simp at h2
    exact h2

theorem norm_eq_one_of_compact {Γ k : Type} [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ] [NormedField k]
    (d : Γ →* k) (hd : Continuous d) (g : Γ) : ‖d g‖ = 1 := by
  obtain ⟨C, hC⟩ := (isCompact_range (continuous_norm.comp hd)).bddAbove
  have hle : ∀ g, ‖d g‖ ≤ 1 := by
    intro g
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C hlt
    have : ‖d (g ^ n)‖ ≤ C := hC ⟨g ^ n, rfl⟩
    rw [map_pow, norm_pow] at this
    linarith
  have h1 : ‖d g‖ * ‖d g⁻¹‖ = 1 := by rw [← norm_mul, ← map_mul, mul_inv_cancel, map_one, norm_one]
  have := hle g; have := hle g⁻¹; have := norm_nonneg (d g); have := norm_nonneg (d g⁻¹)
  nlinarith

theorem mem_pow_of_norm_lt (k : ℕ) : ∃ δ : ℝ, 0 < δ ∧ ∀ y : N.O i, ‖iotaOQ N A i y‖ < δ →
    y ∈ IsLocalRing.maximalIdeal (N.O i) ^ k := by
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible (N.O i)
  have hp0 : iotaOQ N A i p ≠ 0 := by
    intro h
    have : p = 0 := iota_inj N A i (by simpa using h)
    exact hp.ne_zero this
  refine ⟨‖iotaOQ N A i p‖ ^ k, pow_pos (norm_pos_iff.2 hp0) k, fun y hy => ?_⟩
  rcases eq_or_ne y 0 with rfl | hy0
  · exact zero_mem _
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy0 hp
  rw [map_mul, norm_mul, norm_iota_unit N A i u.isUnit, one_mul, map_pow, norm_pow] at hy
  have hlt : ‖iotaOQ N A i p‖ < 1 := norm_iota_lt_one N A i (by
    rw [hp.maximalIdeal_eq]; exact Ideal.mem_span_singleton_self p)
  have hkn : k ≤ n := by
    by_contra h
    rw [not_le] at h
    exact absurd hy (not_lt.2 (pow_le_pow_of_le_one (norm_nonneg _) hlt.le h.le))
  rw [hp.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact (pow_dvd_pow p hkn).mul_left _

theorem exists_integral_char (d : G H.E N.Om →* Qbar (N.l i)) (hd : Continuous d) (S : Set (G H.E N.Om))
    (hS : closure S = Set.univ) (hv : ∀ σ ∈ S, d σ ∈ Set.range (A.iotaQ i)) :
    ∃ ξ : G H.E N.Om →* (N.O i)ˣ, Continuous (fun g => ((ξ g : (N.O i)ˣ) : N.O i)) ∧
      ∀ g, iotaOQ N A i ((ξ g : (N.O i)ˣ) : N.O i) = d g := by
  have : IsGalois H.E N.Om := {}
  have hn := norm_eq_one_of_compact d hd
  have hinj := iota_inj N A i
  have hall : ∀ g, d g ∈ Set.range (iotaOQ N A i) := by
    have hsub : closure S ⊆ d ⁻¹' Set.range (iotaOQ N A i) :=
      closure_minimal (fun σ hσ => by
        obtain ⟨x, hx⟩ := hv σ hσ
        have := mem_range_of_norm N A i (x := x) (by rw [hx]; exact hn σ)
        rw [hx] at this
        exact this) ((isClosed_range_iota N A i).preimage hd)
    intro g
    exact hsub (hS ▸ Set.mem_univ g)
  choose u hu using hall
  let ξ0 : G H.E N.Om →* N.O i :=
    { toFun := u
      map_one' := hinj (by rw [hu, map_one, map_one])
      map_mul' := fun a b => hinj (by rw [hu, map_mul, map_mul, hu, hu]) }
  refine ⟨ξ0.toHomUnits, ?_, fun g => ?_⟩
  · have hval : (fun g => ((ξ0.toHomUnits g : (N.O i)ˣ) : N.O i)) = u := funext fun g => rfl
    rw [hval, continuous_iff_continuousAt]
    intro g
    rw [ContinuousAt, ← tendsto_sub_nhds_zero_iff,
      (N.O_adic i).hasBasis_nhds_zero.tendsto_right_iff]
    intro k _
    obtain ⟨δ, hδ, hk⟩ := mem_pow_of_norm_lt N A i k
    have hcd : ∀ᶠ x in nhds g, ‖d x - d g‖ < δ := by
      have := (hd.tendsto g)
      exact (Metric.tendsto_nhds.1 this δ hδ).mono fun x hx => by simpa [dist_eq_norm] using hx
    filter_upwards [hcd] with x hx
    apply hk
    rw [map_sub, hu, hu]
    exact hx
  · exact hu g

end Coeff

section Main

open Formalism.L2.Host

theorem inf_int (D : D7) (hA : Formalism.MainNotions.SumRepresentations.At.TieAut D.nd D.naut) (τ : D.host.E →+* ℂ) (z : ℂ)
    (hz : z ∈ D.naut.infG D.naut.etaTinv τ) : ∃ k : ℤ, z + ((-(D.R.t : ℝ) / 2 : ℝ) : ℂ) = (k : ℂ) := by
  obtain ⟨v, hv⟩ := D.R.t_odd
  have hs : ((-(D.R.t : ℝ) / 2 : ℝ) : ℂ) = -(v : ℂ) - 1 / 2 := by
    rw [hv]
    push_cast
    ring
  obtain ⟨h1, h3⟩ := hA.2.1 τ
  rw [h3] at hz
  rcases h1 with h1 | h1
  · rw [h1] at hz
    simp only [Multiset.map_singleton, Multiset.mem_singleton] at hz
    subst hz
    exact ⟨-(v : ℤ) - 1, by rw [hs]; push_cast; ring⟩
  · rw [h1] at hz
    simp only [Multiset.map_singleton, Multiset.mem_singleton] at hz
    subst hz
    exact ⟨-(v : ℤ), by rw [hs]; push_cast; ring⟩

theorem frob_value (D : D7) (C : CharFrame D) (nch : NChoice D) (Tp : TupTied D C nch)
    (T : NCharTied D C nch Tp) (V : ValLL0 D C) (w : PlE D.host) :
    ∃ x : D.what₂.LL, D.naut.frobEig (D.naut.lpTw (D.naut.locG D.naut.etaTinv w) (-(D.R.t : ℝ) / 2)) =
      {D.what₂.embLL x} := by
  obtain ⟨v, hv⟩ := D.R.t_odd
  have hu := (D.naut.etaTinv_def w).1
  have hU := (T.unr_iff _ w).1 hu
  have hf := T.frob _ w hU
  rw [T.etaTinv] at hf hU
  have hE : C.eta.UnrAt w := by simpa using hU.inv
  obtain ⟨y, hy⟩ := V.eta w hE
  have hq : ((normV w : ℕ) : ℂ) ≠ 0 := by
    have := w.asIdeal.finiteQuotientOfFreeOfNeBot w.ne_bot
    exact Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hn : (Ideal.absNorm w.asIdeal : ℕ) = normV w := rfl
  have hy' : D.what₂.embLL (y : D.what₂.LL) =
      ((C.eta.val w : ℂˣ) : ℂ) * ((normV w : ℕ) : ℂ) ^ (-(((1 / 2 : ℝ)) : ℂ)) := by
    have e : D.what₂.embLL (y : D.what₂.LL) = C.eta.valTw (1 / 2) w := hy
    rw [e, HChar.valTw, hn]
  refine ⟨(y : D.what₂.LL) * (((normV w : ℕ) : D.what₂.LL)⁻¹) ^ v, ?_⟩
  rw [D.naut.frobEig_tw _ _ hu, hf, Multiset.map_singleton, HChar.val_inv, inv_inv]
  congr 1
  rw [map_mul, map_pow, map_inv₀, map_natCast, hy', mul_assoc]
  congr 1
  have e1 : (((-(D.R.t : ℝ) / 2 : ℝ)) : ℂ) = -(((1 / 2 : ℝ)) : ℂ) + -(v : ℂ) := by
    rw [hv]
    push_cast
    ring
  rw [e1, Complex.cpow_add _ _ hq, Complex.cpow_neg _ (v : ℂ), Complex.cpow_natCast, inv_pow]

end Main

theorem main : ∀ (D : D7) (C : Formalism.L2.Host.CharFrame D) (nch : NChoice D) (Tp : Formalism.L2.Host.TupTied D C nch), Formalism.L2.Host.NCharTied D C nch Tp → Formalism.L2.Host.ValLL0 D C → Formalism.MainNotions.SumRepresentations.tie0 D → Formalism.MainNotions.SumRepresentations.adm2 D → Formalism.MainNotions.SumRepresentations.adm5 D → XiOverO D.nd D.naut := by
  intro D C nch Tp T V ht h2 h5 i
  have hA : Formalism.MainNotions.SumRepresentations.At.TieAut D.nd D.naut := ht.2.1
  obtain ⟨ρ, hρ, hwd, -⟩ := (h2 i).2.2 D.naut.etaTinv (-(D.R.t : ℝ) / 2) (inf_int D hA)
  have hun : ∀ w, w ∉ placesOver D.host.E (D.nd.l i) → D.naut.unr (D.naut.wdOf i ρ w) := fun w hw => by
    rw [hwd w hw]
    exact (D.naut.unr_tw _ _).2 (D.naut.etaTinv_def w).1
  have hfrob : ∀ w, w ∉ placesOver D.host.E (D.nd.l i) → ∀ (B : ValuationSubring D.nd.Om) (σ : G D.host.E D.nd.Om),
      IsPlaceOver (F := D.host.E) B w → IsFrob (F := D.host.E) B (normV w) σ →
      D.naut.frobEig (D.naut.lpTw (D.naut.locG D.naut.etaTinv w) (-(D.R.t : ℝ) / 2)) =
        {D.naut.iotaQC i (((ρ σ : GL (Fin 1) (Qbar (D.nd.l i))) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))) 0 0)} := by
    intro w hw B σ hB hσ
    have e := D.naut.wdOf_frob i ρ w hw hρ (hun w hw) B σ hB hσ
    obtain ⟨a, ha⟩ := Multiset.card_eq_one.1
      ((D.naut.frobEig_card _ (hun w hw)).trans (D.naut.wdOf_dim i ρ w))
    rw [ha, charpoly_fin_one] at e
    simp only [Multiset.map_singleton, Multiset.prod_singleton, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_C] at e
    have e2 := C_injective (sub_right_injective e)
    rw [← hwd w hw, ha]
    exact congrArg _ e2.symm
  let d : G D.host.E D.nd.Om →* Qbar (D.nd.l i) :=
    (Units.coeHom _).comp (Matrix.GeneralLinearGroup.det.comp ρ)
  have hde : ∀ g, d g = ((ρ g : GL (Fin 1) (Qbar (D.nd.l i))) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))) 0 0 :=
    fun g => Matrix.det_fin_one _
  have hd : Continuous d := by
    have : (d : G D.host.E D.nd.Om → Qbar (D.nd.l i)) = fun g =>
        ((ρ g : GL (Fin 1) (Qbar (D.nd.l i))) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))) 0 0 := funext hde
    rw [this]
    exact (continuous_apply_apply 0 0).comp hρ
  have hfin : (placesOver D.host.E (D.nd.l i)).Finite :=
    GlobalTheory.SplitRead.finite_placesOver _ (Fact.out : (D.nd.l i).Prime).ne_zero
  have hS := h5.2.2.1 _ hfin
  obtain ⟨ξ, hξc, hξ⟩ := exists_integral_char D.nd D.naut i d hd _ hS (by
    rintro σ ⟨w, hw, -, B, hB, hσ⟩
    obtain ⟨x, hx⟩ := frob_value D C nch Tp T V w
    have e := hfrob w hw B σ hB hσ
    rw [hx, Multiset.singleton_inj, ← D.naut.iota_LL i x, ← hde] at e
    exact ⟨_, (D.naut.iotaQC i).injective e⟩)
  refine ⟨ξ, hξc, fun w hw => ⟨fun σ hσ => ?_, fun B σ hB hσ => ?_⟩⟩
  · have h1 := (D.naut.wdOf_unr i ρ w hw hρ).1 (hun w hw) σ hσ
    apply Units.ext
    apply iota_inj D.nd D.naut i
    rw [hξ, hde, h1]
    simp
  · rw [hfrob w hw B σ hB hσ, ← hde, ← hξ]
    rfl

end GlobalTheory.XiOver
