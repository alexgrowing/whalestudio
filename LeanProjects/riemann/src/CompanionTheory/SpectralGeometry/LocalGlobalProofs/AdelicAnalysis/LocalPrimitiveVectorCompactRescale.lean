import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.PrimV

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

def UniP (K : Type*) [CommRing K] [TopologicalSpace K] (M : ℕ) : Prop :=
  ∃ Ω : Set (Fin M → K), IsCompact Ω ∧ ∀ y : Fin M → K, (∃ z : Fin M → K, z ⬝ᵥ y = 1) →
    ∃ (a : Kˣ) (z : Fin M → K), (a : K) • y ∈ Ω ∧ z ∈ Ω ∧ z ⬝ᵥ ((a : K) • y) = 1

theorem primitiveCompact_of_multiplicative {K : Type*} [CommRing K] [Nontrivial K] [TopologicalSpace K] (M : ℕ) (ν : K → ℝ)
    (h0 : ν 0 = 0) (h1 : ν 1 = 1) (hm : ∀ x y, ν (x * y) = ν x * ν y) (hn : ∀ x, 0 ≤ ν x)
    (hu : ∀ x, x ≠ 0 → IsUnit x ∧ 0 < ν x) (hc : IsCompact {x | ν x ≤ 1}) : UniP K M := by
  refine ⟨Set.pi Set.univ fun _ => {x | ν x ≤ 1}, isCompact_univ_pi fun _ => hc, ?_⟩
  rintro y ⟨z, hz⟩
  have hex : ∃ j, y j ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hy0 : y = 0 := funext hcon
    rw [hy0, dotProduct_zero] at hz
    exact zero_ne_one hz
  obtain ⟨j, hj⟩ := hex
  haveI : Nonempty (Fin M) := ⟨j⟩
  obtain ⟨i, hi⟩ := Finite.exists_max (fun k => ν (y k))
  have hyi : y i ≠ 0 := by
    intro h
    have h2 := hi j
    simp only [h, h0] at h2
    exact absurd (hu _ hj).2 (not_lt.2 h2)
  obtain ⟨w, hw⟩ := (hu _ hyi).1
  have hwi : ((w⁻¹ : Kˣ) : K) * y i = 1 := by rw [← hw]; exact Units.inv_mul w
  have hνw : ν ((w⁻¹ : Kˣ) : K) * ν (y i) = 1 := by rw [← hm, hwi, h1]
  refine ⟨w⁻¹, Pi.single i 1, ?_, ?_, ?_⟩
  · intro k _
    show ν ((((w⁻¹ : Kˣ) : K) • y) k) ≤ 1
    rw [Pi.smul_apply, smul_eq_mul, hm, ← hνw]
    exact mul_le_mul_of_nonneg_left (hi k) (hn _)
  · intro k _
    show ν ((Pi.single i (1 : K) : Fin M → K) k) ≤ 1
    by_cases hk : k = i
    · subst hk; simp [h1]
    · simp [Pi.single_eq_of_ne hk, h0]
  · simp [hwi]

theorem primitiveCompact_prod {A B : Type*} [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B] {M : ℕ}
    (hA : UniP A M) (hB : UniP B M) : UniP (A × B) M := by
  obtain ⟨ΩA, cA, pA⟩ := hA
  obtain ⟨ΩB, cB, pB⟩ := hB
  let f : (Fin M → A) × (Fin M → B) → (Fin M → A × B) := fun p i => (p.1 i, p.2 i)
  have hf : Continuous f := continuous_pi fun i =>
    ((continuous_apply i).comp continuous_fst).prodMk ((continuous_apply i).comp continuous_snd)
  refine ⟨f '' (ΩA ×ˢ ΩB), (cA.prod cB).image hf, ?_⟩
  rintro y ⟨z, hz⟩
  have h1 : (fun i => (z i).1) ⬝ᵥ (fun i => (y i).1) = 1 := by
    have := congrArg Prod.fst hz
    simpa [dotProduct, Prod.fst_sum] using this
  have h2 : (fun i => (z i).2) ⬝ᵥ (fun i => (y i).2) = 1 := by
    have := congrArg Prod.snd hz
    simpa [dotProduct, Prod.snd_sum] using this
  obtain ⟨a, za, m1, m2, m3⟩ := pA _ ⟨_, h1⟩
  obtain ⟨b, zb, n1, n2, n3⟩ := pB _ ⟨_, h2⟩
  have hab : ((MulEquiv.prodUnits.symm (a, b) : (A × B)ˣ) : A × B) = ((a : A), (b : B)) := rfl
  refine ⟨MulEquiv.prodUnits.symm (a, b), fun i => (za i, zb i),
    ⟨(_, _), ⟨m1, n1⟩, ?_⟩, ⟨(za, zb), ⟨m2, n2⟩, rfl⟩, ?_⟩
  · ext i <;> simp [f, hab]
  · refine Prod.ext ?_ ?_
    · simpa [dotProduct, Prod.fst_sum, hab] using m3
    · simpa [dotProduct, Prod.snd_sum, hab] using n3

theorem primitiveCompact_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B] {M : ℕ}
    (e : A ≃+* B) (hc : Continuous e.symm) (h : UniP B M) : UniP A M := by
  obtain ⟨Ω, c, p⟩ := h
  refine ⟨(fun w i => e.symm (w i)) '' Ω,
    c.image (continuous_pi fun i => hc.comp (continuous_apply i)), ?_⟩
  rintro y ⟨z, hz⟩
  have h1 : (fun i => e (z i)) ⬝ᵥ (fun i => e (y i)) = 1 := by
    have := congrArg e hz
    simpa [dotProduct, map_sum, map_mul] using this
  obtain ⟨a, w, m1, m2, m3⟩ := p _ ⟨_, h1⟩
  refine ⟨Units.map (e.symm : B →* A) a, fun i => e.symm (w i), ⟨_, m1, ?_⟩, ⟨w, m2, rfl⟩, ?_⟩
  · ext i; simp
  · apply e.injective
    simpa [dotProduct, map_sum, map_mul] using m3

section Quad

variable {L K : Type*} [Field L] [CommRing K] [Algebra L K]

def gg (d : K) (p : L × L) : K := p.1 • (1 : K) + p.2 • d

theorem gg_mul {d : K} {D : L} (hd : d * d = algebraMap L K D) (p q : L × L) :
    gg d p * gg d q = gg d (p.1 * q.1 + D * (p.2 * q.2), p.1 * q.2 + p.2 * q.1) := by
  simp only [gg, Algebra.smul_def, map_add, map_mul, mul_one]
  linear_combination (algebraMap L K p.2 * algebraMap L K q.2) * hd

variable (bs : Module.Basis (Fin 2) L K)

def rr (x : K) : L × L := (bs.repr x 0, bs.repr x 1)

theorem gg_rr (h0 : bs 0 = 1) (x : K) : gg (bs 1) (rr bs x) = x := by
  have := bs.sum_repr x
  rw [Fin.sum_univ_two, h0] at this
  exact this

theorem rr_gg (h0 : bs 0 = 1) (p : L × L) : rr bs (gg (bs 1) p) = p := by
  refine Prod.ext ?_ ?_ <;> simp [rr, gg, ← h0]

theorem rr_mul (h0 : bs 0 = 1) {D : L} (hd : bs 1 * bs 1 = algebraMap L K D) (x y : K) :
    rr bs (x * y) = ((rr bs x).1 * (rr bs y).1 + D * ((rr bs x).2 * (rr bs y).2),
      (rr bs x).1 * (rr bs y).2 + (rr bs x).2 * (rr bs y).1) := by
  conv_lhs => rw [← gg_rr bs h0 x, ← gg_rr bs h0 y, gg_mul hd, rr_gg bs h0]

theorem rr_zero : rr bs (0 : K) = 0 := by simp [rr]

theorem rr_one (h0 : bs 0 = 1) : rr bs (1 : K) = (1, 0) := by
  rw [← h0]; simp [rr]

theorem rr_add (x y : K) : rr bs (x + y) = rr bs x + rr bs y := by simp [rr]

theorem nontrivial_of_basis (h0 : bs 0 = 1) : Nontrivial K := by
  refine ⟨⟨0, 1, fun h => ?_⟩⟩
  have := rr_one bs h0
  rw [← h, rr_zero] at this
  simpa using congrArg Prod.fst this

end Quad

section Norm

variable {L K : Type*} [NormedField L] [ProperSpace L]

def Nf (D : L) (p : L × L) : L := p.1 ^ 2 - D * p.2 ^ 2

theorem Nf_mul (D : L) (p q : L × L) :
    Nf D (p.1 * q.1 + D * (p.2 * q.2), p.1 * q.2 + p.2 * q.1) = Nf D p * Nf D q := by
  simp only [Nf]; ring

theorem Nf_ne {D : L} (hD : ∀ s, s * s ≠ D) {p : L × L} (hp : p ≠ 0) : Nf D p ≠ 0 := by
  intro h
  simp only [Nf] at h
  by_cases hc : p.2 = 0
  · apply hp
    refine Prod.ext ?_ hc
    rw [hc] at h
    simpa using h
  · apply hD (p.1 / p.2)
    field_simp
    linear_combination h

theorem compact_Nf {D : L} (hD : ∀ s, s * s ≠ D) : IsCompact {p : L × L | ‖Nf D p‖ ≤ 1} := by
  have hcont : Continuous fun p : L × L => ‖Nf D p‖ := by
    unfold Nf; fun_prop
  have hs : IsCompact (Metric.sphere (0 : L × L) 1) := isCompact_sphere _ _
  have hne : (Metric.sphere (0 : L × L) 1).Nonempty := ⟨(1, 0), by simp [Prod.norm_def]⟩
  obtain ⟨q0, hq0, hmin⟩ := hs.exists_isMinOn hne hcont.continuousOn
  have hq00 : q0 ≠ 0 := by
    rintro rfl
    simp at hq0
  have hm : 0 < ‖Nf D q0‖ := norm_pos_iff.2 (Nf_ne hD hq00)
  refine Metric.isCompact_of_isClosed_isBounded (isClosed_le hcont continuous_const) ?_
  refine (Metric.isBounded_closedBall (x := (0 : L × L)) (r := 1 + 1 / ‖Nf D q0‖)).subset ?_
  intro p hp
  rw [mem_closedBall_zero_iff]
  by_cases hp0 : p = 0
  · subst hp0
    simp only [norm_zero]
    positivity
  obtain ⟨w, hw⟩ : ∃ w : L, ‖w‖ = ‖p‖ := by
    rw [Prod.norm_def]
    rcases max_choice ‖p.1‖ ‖p.2‖ with h | h
    · exact ⟨p.1, h.symm⟩
    · exact ⟨p.2, h.symm⟩
  have hpn : 0 < ‖p‖ := norm_pos_iff.2 hp0
  have hw0 : w ≠ 0 := by
    rintro rfl
    simp at hw
    exact hp0 (norm_eq_zero.1 hw.symm)
  have hq : w⁻¹ • p ∈ Metric.sphere (0 : L × L) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, hw]
    field_simp
  have h1 : ‖Nf D q0‖ ≤ ‖Nf D (w⁻¹ • p)‖ := hmin hq
  have h2 : Nf D p = w ^ 2 * Nf D (w⁻¹ • p) := by
    simp only [Nf, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
  have h3 : ‖p‖ ^ 2 * ‖Nf D q0‖ ≤ 1 := by
    have h4 : ‖Nf D p‖ ≤ 1 := hp
    rw [h2, norm_mul, norm_pow, hw] at h4
    exact (mul_le_mul_of_nonneg_left h1 (by positivity)).trans h4
  have h5 : ‖p‖ ^ 2 ≤ 1 / ‖Nf D q0‖ := by
    rw [le_div_iff₀ hm]; exact h3
  have h6 : 0 < 1 / ‖Nf D q0‖ := by positivity
  by_cases h7 : ‖p‖ ≤ 1
  · linarith
  · push_neg at h7
    nlinarith

variable [CommRing K] [Algebra L K] [TopologicalSpace K] (bs : Module.Basis (Fin 2) L K)

theorem primitiveCompact_nonsplit (h0 : bs 0 = 1) {D : L} (hd : bs 1 * bs 1 = algebraMap L K D)
    (hD : ∀ s, s * s ≠ D) (hg : Continuous (gg (bs 1) : L × L → K)) (M : ℕ) : UniP K M := by
  haveI := nontrivial_of_basis bs h0
  refine primitiveCompact_of_multiplicative M (fun x => ‖Nf D (rr bs x)‖) ?_ ?_ ?_ (fun _ => norm_nonneg _) ?_ ?_
  · simp [rr_zero, Nf]
  · simp [rr_one bs h0, Nf]
  · intro x y
    simp only [rr_mul bs h0 hd, Nf_mul, norm_mul]
  · intro x hx
    show IsUnit x ∧ 0 < ‖Nf D (rr bs x)‖
    have hxg := gg_rr bs h0 x
    have hp : rr bs x ≠ 0 := by
      intro h
      apply hx
      rw [← hxg, h]
      simp [gg]
    have hn := Nf_ne hD hp
    generalize rr bs x = p at hxg hp hn ⊢
    refine ⟨isUnit_iff_exists_inv.2 ⟨gg (bs 1) (p.1 / Nf D p, -p.2 / Nf D p), ?_⟩, norm_pos_iff.2 hn⟩
    rw [← hxg, gg_mul hd]
    have e1 : p.1 * (p.1 / Nf D p) + D * (p.2 * (-p.2 / Nf D p)) = 1 := by
      field_simp
      simp only [Nf]
      ring
    have e2 : p.1 * (-p.2 / Nf D p) + p.2 * (p.1 / Nf D p) = 0 := by
      field_simp
      ring
    simp only [e1, e2]
    simp [gg]
  · have : {x : K | ‖Nf D (rr bs x)‖ ≤ 1} = gg (bs 1) '' {p : L × L | ‖Nf D p‖ ≤ 1} := by
      ext x
      constructor
      · intro hx
        exact ⟨rr bs x, hx, gg_rr bs h0 x⟩
      · rintro ⟨p, hp, rfl⟩
        show ‖Nf D (rr bs (gg (bs 1) p))‖ ≤ 1
        rw [rr_gg bs h0]
        exact hp
    rw [this]
    exact (compact_Nf hD).image hg

theorem primitiveCompact_normedField (M : ℕ) : UniP L M := by
  refine primitiveCompact_of_multiplicative M (fun x => ‖x‖) norm_zero norm_one norm_mul (fun _ => norm_nonneg _)
    (fun x hx => ⟨isUnit_iff_ne_zero.2 hx, norm_pos_iff.2 hx⟩) ?_
  have : {x : L | ‖x‖ ≤ 1} = Metric.closedBall 0 1 := by
    ext x; simp
  rw [this]
  exact isCompact_closedBall _ _

theorem primitiveCompact_split (h0 : bs 0 = 1) {D : L} (hd : bs 1 * bs 1 = algebraMap L K D) {s : L} (hs : s ≠ 0)
    (hD : s * s = D) (h2 : (2 : L) ≠ 0) (hg : Continuous (gg (bs 1) : L × L → K)) (M : ℕ) : UniP K M := by
  let e : K ≃+* L × L :=
    { toFun := fun x => ((rr bs x).1 + s * (rr bs x).2, (rr bs x).1 - s * (rr bs x).2)
      invFun := fun w => gg (bs 1) ((w.1 + w.2) / 2, (w.1 - w.2) / (2 * s))
      left_inv := fun x => by
        have e1 : ((rr bs x).1 + s * (rr bs x).2 + ((rr bs x).1 - s * (rr bs x).2)) / 2 = (rr bs x).1 := by
          field_simp
          ring
        have e2 : ((rr bs x).1 + s * (rr bs x).2 - ((rr bs x).1 - s * (rr bs x).2)) / (2 * s) = (rr bs x).2 := by
          field_simp
          ring
        simp only [e1, e2]
        exact gg_rr bs h0 x
      right_inv := fun w => by
        simp only [rr_gg bs h0]
        refine Prod.ext ?_ ?_
        · simp only
          field_simp
          ring
        · simp only
          field_simp
          ring
      map_mul' := fun x y => by
        simp only [rr_mul bs h0 hd, ← hD]
        refine Prod.ext ?_ ?_
        · simp only [Prod.fst_mul]
          ring
        · simp only [Prod.snd_mul]
          ring
      map_add' := fun x y => by
        simp only [rr_add]
        refine Prod.ext ?_ ?_
        · simp only [Prod.fst_add, Prod.snd_add]
          ring
        · simp only [Prod.fst_add, Prod.snd_add]
          ring }
  refine primitiveCompact_of_ringEquiv e ?_ (primitiveCompact_prod (primitiveCompact_normedField M) (primitiveCompact_normedField M))
  show Continuous fun w : L × L => gg (bs 1) ((w.1 + w.2) / 2, (w.1 - w.2) / (2 * s))
  exact hg.comp (by fun_prop)

end Norm

section Delta

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

theorem basis_of_not_mem (h2 : Module.finrank F E = 2) {d : E} (hd : d ∉ (algebraMap F E).range) :
    ∃ b : Module.Basis (Fin 2) F E, b 0 = 1 ∧ b 1 = d := by
  have hli : LinearIndependent F ![(1 : E), d] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have ht : t = 0 := by
      by_contra ht
      apply hd
      refine ⟨-(s / t), ?_⟩
      have hht : algebraMap F E t ≠ 0 := by simpa using ht
      simp only [Algebra.smul_def, mul_one] at hst
      have h3 : algebraMap F E t * (algebraMap F E s / algebraMap F E t) = algebraMap F E s := by
        field_simp
      apply mul_left_cancel₀ hht
      rw [map_neg, map_div₀, mul_neg, h3]
      linear_combination -hst
    subst ht
    simpa using hst
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hli (by simp [h2]), ?_, ?_⟩ <;> simp

theorem exists_delta [CharZero F] (h2 : Module.finrank F E = 2) :
    ∃ (b : Module.Basis (Fin 2) F E) (Δ : F), b 0 = 1 ∧ b 1 * b 1 = algebraMap F E Δ ∧ Δ ≠ 0 := by
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  obtain ⟨x, hx⟩ : ∃ x : E, x ∉ (algebraMap F E).range := by
    by_contra hcon
    push_neg at hcon
    have : (⊥ : Subalgebra F E) = ⊤ := by
      ext y
      simpa [Algebra.mem_bot] using hcon y
    have h1 := Subalgebra.bot_eq_top_iff_finrank_eq_one.1 this
    omega
  obtain ⟨b0, h00, h01⟩ := basis_of_not_mem h2 hx
  have hxx : x * x = algebraMap F E (b0.repr (x * x) 0) + algebraMap F E (b0.repr (x * x) 1) * x := by
    have := b0.sum_repr (x * x)
    rw [Fin.sum_univ_two, h00, h01] at this
    simp only [Algebra.smul_def, mul_one] at this
    exact this.symm
  set q := b0.repr (x * x) 0
  set p := b0.repr (x * x) 1
  have hδ : x - algebraMap F E (p / 2) ∉ (algebraMap F E).range := by
    rintro ⟨c, hc⟩
    apply hx
    refine ⟨c + p / 2, ?_⟩
    rw [map_add, hc]
    ring
  obtain ⟨b, hb0, hb1⟩ := basis_of_not_mem h2 hδ
  have h2F : algebraMap F E 2 = 2 := map_ofNat _ 2
  have hsq : b 1 * b 1 = algebraMap F E (q + p / 2 * (p / 2)) := by
    have hp2 : algebraMap F E p = 2 * algebraMap F E (p / 2) := by
      rw [← h2F, ← map_mul]
      congr 1
      ring
    rw [hb1, map_add, map_mul]
    linear_combination hxx + x * hp2
  refine ⟨b, q + p / 2 * (p / 2), hb0, hsq, fun h0 => ?_⟩
  rw [h0, map_zero, hb1] at hsq
  have : x - algebraMap F E (p / 2) = 0 := mul_self_eq_zero.1 hsq
  exact hδ ⟨0, by rw [this, map_zero]⟩

end Delta

theorem exists_compact_unimodular_vectors_mod_units : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (v : HeightOneSpectrum (𝓞 F)), ∃ Ω : Set (Fin 1 → Fin M → Fv F v ⊗[F] E), IsCompact Ω ∧ ∀ y : Fin 1 → Fin M → Fv F v ⊗[F] E, (∃ z : Fin M → Fv F v ⊗[F] E, z ⬝ᵥ y 0 = 1) → ∃ (a : (Fv F v ⊗[F] E)ˣ) (z : Fin 1 → Fin M → Fv F v ⊗[F] E), (a : Fv F v ⊗[F] E) • y ∈ Ω ∧ z ∈ Ω ∧ z 0 ⬝ᵥ ((a : Fv F v ⊗[F] E) • y) 0 = 1 := by
  intro F E _ _ _ _ _ σ hσ M v
  obtain ⟨b, Δ, hb0, hb1, hΔ⟩ := exists_delta (F := F) (E := E) hσ.2.2.1
  haveI hprop : ProperSpace (Fv F v) := Formalism.BasicNotions.Examples₂.LocF.proper v
  haveI hmt : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := TopK.isModTop (F := F) (E := E) (Fv F v)
  haveI : ContinuousAdd (Fv F v ⊗[F] E) := IsModuleTopology.toContinuousAdd (Fv F v) _
  haveI : ContinuousSMul (Fv F v) (Fv F v ⊗[F] E) := IsModuleTopology.toContinuousSMul (Fv F v) _
  let bs : Module.Basis (Fin 2) (Fv F v) (Fv F v ⊗[F] E) := Algebra.TensorProduct.basis (Fv F v) b
  have h0 : bs 0 = 1 := by
    simp [bs, Algebra.TensorProduct.basis_apply, hb0, Algebra.TensorProduct.one_def]
  have hd : bs 1 * bs 1 = algebraMap (Fv F v) (Fv F v ⊗[F] E) (algebraMap F (Fv F v) Δ) := by
    simp only [bs, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul, hb1, mul_one,
      Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_eq_smul_one Δ, TensorProduct.smul_tmul,
      Algebra.algebraMap_self, RingHom.id_apply]
  have hg : Continuous (gg (bs 1) : Fv F v × Fv F v → Fv F v ⊗[F] E) := by
    unfold gg
    have c1 : Continuous fun p : Fv F v × Fv F v => p.1 • (1 : Fv F v ⊗[F] E) := by
      fun_prop
    have c2 : Continuous fun p : Fv F v × Fv F v => p.2 • bs 1 := by
      fun_prop
    exact c1.add c2
  have hU : UniP (Fv F v ⊗[F] E) M := by
    by_cases hsq : ∃ s, s * s = algebraMap F (Fv F v) Δ
    · obtain ⟨s, hs⟩ := hsq
      have hD0 : algebraMap F (Fv F v) Δ ≠ 0 := by simpa using hΔ
      have hs0 : s ≠ 0 := by
        rintro rfl
        exact hD0 (by rw [← hs, mul_zero])
      exact primitiveCompact_split bs h0 hd hs0 hs two_ne_zero hg M
    · push_neg at hsq
      exact primitiveCompact_nonsplit bs h0 hd hsq hg M
  obtain ⟨Ω, hc, hp⟩ := hU
  have hcw : Continuous (fun (w : Fin M → Fv F v ⊗[F] E) (_ : Fin 1) => w) :=
    continuous_pi fun _ => continuous_id
  refine ⟨(fun w _ => w) '' Ω, hc.image hcw, ?_⟩
  rintro y ⟨z, hz⟩
  obtain ⟨a, w, m1, m2, m3⟩ := hp (y 0) ⟨z, hz⟩
  refine ⟨a, fun _ => w, ⟨_, m1, ?_⟩, ⟨w, m2, rfl⟩, m3⟩
  funext i
  rw [Subsingleton.elim i 0]
  rfl

end GlobalTheory.CompanionTheory.SW.PrimV
