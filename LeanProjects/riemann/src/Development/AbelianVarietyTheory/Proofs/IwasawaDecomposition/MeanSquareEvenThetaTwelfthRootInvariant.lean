import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Retie
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EisGEqZeroOfInfinite
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ExistsPowPrincipalFractionalIdeal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaNormUnimodularLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemInvMulDifferent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPeriodPairBaseLat

noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.Mem.Per GlobalTheory.Glob

namespace GlobalTheory.Mem.TruePeriods

theorem area_map_unit (Λ : AddSubgroup ℂ) {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    area (Λ.map (AddMonoidHom.mulLeft ζ)) = area Λ := by
  have e : ∀ x y : ℂ, (starRingEnd ℂ) (ζ * x) * (ζ * y) = (starRingEnd ℂ) x * y := fun x y => by
    have : (starRingEnd ℂ) ζ * ζ = 1 := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hζ]; simp
    rw [map_mul]; linear_combination ((starRingEnd ℂ) x * y) * this
  unfold area
  congr 1
  ext a
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨ha, _, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨ha, x, hx, y, hy, congrArg (fun z : ℂ => |z.im|) (e x y)⟩
  · rintro ⟨ha, x, hx, y, hy, rfl⟩
    exact ⟨ha, ζ * x, ⟨x, hx, rfl⟩, ζ * y, ⟨y, hy, rfl⟩, congrArg (fun z : ℂ => |z.im|) (e x y).symm⟩

theorem isLat_of_discr_one {Λ : AddSubgroup ℂ} (h : TaylorLogMetric.discr Λ = 1) : GlobalTheory.ThetaConj.IsLat Λ := by
  obtain ⟨L, hL⟩ := GlobalTheory.LatticeInvariants.exists_periodPair_of_discr_ne_zero (Λ := Λ) (by rw [h]; exact one_ne_zero)
  refine ⟨L.ω₁, L.ω₂, L.indep, ?_⟩
  ext z
  rw [hL, AddSubgroup.mem_closure_pair, PeriodPair.mem_lattice]
  simp only [zsmul_eq_mul]

theorem exists_root_of_jLat_eq {Λ Λ' : AddSubgroup ℂ} (h : TaylorLogMetric.discr Λ = 1) (h' : TaylorLogMetric.discr Λ' = 1)
    (hj : jLat Λ = jLat Λ') : ∃ ζ : ℂ, ζ ^ 12 = 1 ∧ Λ' = Λ.map (AddMonoidHom.mulLeft ζ) := by
  have h2 : g2 Λ ^ 3 = g2 Λ' ^ 3 := by
    unfold jLat at hj
    rw [h, h'] at hj
    linear_combination hj / 1728
  have h3 : g3 Λ ^ 2 = g3 Λ' ^ 2 := by
    unfold TaylorLogMetric.discr at h h'
    linear_combination (h' - h + h2) / 27
  obtain ⟨u, hu, hu2⟩ : ∃ u : ℂ, u ^ 3 = 1 ∧ g2 Λ = u * g2 Λ' := by
    by_cases h0 : g2 Λ' = 0
    · refine ⟨1, one_pow _, ?_⟩
      rw [h0] at h2 ⊢
      simpa using h2
    · exact ⟨g2 Λ / g2 Λ', by rw [div_pow, h2, div_self (pow_ne_zero _ h0)], by field_simp⟩
  obtain ⟨ζ, h4, h6⟩ : ∃ ζ : ℂ, ζ ^ 4 = u ∧ g3 Λ = ζ ^ 6 * g3 Λ' := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h3 with e | e
    · exact ⟨u, by linear_combination u * hu, by rw [e]; linear_combination (-(u ^ 3 + 1) * g3 Λ') * hu⟩
    · have i4 : Complex.I ^ 4 = 1 := Complex.I_pow_four
      have i6 : Complex.I ^ 6 = -1 := by
        rw [show (6 : ℕ) = 4 + 2 from rfl, pow_add, i4, Complex.I_sq, one_mul]
      refine ⟨u * Complex.I, ?_, ?_⟩
      · rw [mul_pow, i4]; linear_combination u * hu
      · rw [mul_pow, i6, e]; linear_combination ((u ^ 3 + 1) * g3 Λ') * hu
  have h12 : ζ ^ 12 = 1 := by rw [show ζ ^ 12 = (ζ ^ 4) ^ 3 by ring, h4, hu]
  have h0 : ζ ≠ 0 := by rintro rfl; simp at h12
  refine ⟨ζ, h12, ?_⟩
  obtain ⟨L, hL⟩ := (isLat_of_discr_one h').exists_periodPair
  refine ((GlobalTheory.LatticeInvariants.invariants_dictionary L Λ' hL).2.2.2.2.2.1 _ ?_ ?_).symm
  · rw [← h4] at hu2
    unfold g2 at hu2 ⊢
    rw [Model.eisG_map _ _ h0]
    field_simp
    linear_combination hu2 / 60
  · unfold g3 at h6 ⊢
    rw [Model.eisG_map _ _ h0]
    field_simp
    linear_combination h6 / 140

theorem norm_eq_one_of_pow {ζ : ℂ} (h : ζ ^ 12 = 1) : ‖ζ‖ = 1 := by
  have := congrArg norm h
  rw [norm_pow, norm_one] at this
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 this

theorem meanSquare_evenTheta_twelfthRoot_invariant {Λ : AddSubgroup ℂ} (h : TaylorLogMetric.discr Λ = 1) {ζ : ℂ} (hζ : ζ ^ 12 = 1) (t : ℂ) :
    nrm1Sq (Λ.map (AddMonoidHom.mulLeft ζ)) (GL3Theta.th0 (Λ.map (AddMonoidHom.mulLeft ζ)) (ζ * t)) =
      nrm1Sq Λ (GL3Theta.th0 Λ t) := by
  have h0 : ζ ≠ 0 := by rintro rfl; simp at hζ
  have hn := norm_eq_one_of_pow hζ
  have h' : TaylorLogMetric.discr (Λ.map (AddMonoidHom.mulLeft ζ)) = 1 := by rw [Model.discr_map _ _ h0, hζ, h]; simp
  have ha := area_map_unit Λ hn
  have hc : ζ * (starRingEnd ℂ) ζ = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]; simp
  have hU : U1 (Λ.map (AddMonoidHom.mulLeft ζ)) (ζ * t) (sgStar (Λ.map (AddMonoidHom.mulLeft ζ))) 0 =
      ζ * U1 Λ t (sgStar Λ) 0 := by
    unfold U1
    rw [zero_add, zero_add, (GlobalTheory.OddTheta.sgStar_laws Λ (isLat_of_discr_one h)).2.2.2.2 ζ h0, ha, mul_assoc,
      show (Real.pi : ℂ) * (ζ * t) * (starRingEnd ℂ) (ζ * t) = (Real.pi : ℂ) * t * (starRingEnd ℂ) t by
        rw [map_mul]; linear_combination ((Real.pi : ℂ) * t * (starRingEnd ℂ) t) * hc]
    simp
  obtain ⟨a1, a2⟩ := GlobalTheory.OddThetaNorm.odd_theta_norm_sigma_star Λ (isLat_of_discr_one h) h
  obtain ⟨b1, b2⟩ := GlobalTheory.OddThetaNorm.odd_theta_norm_sigma_star _ (isLat_of_discr_one h') h'
  by_cases hz : U1 Λ t (sgStar Λ) 0 = 0
  · unfold GL3Theta.th0
    rw [hU, hz]
    simp [nrm1Sq]
  · rw [a2 t hz, b2 _ (by rw [hU]; exact mul_ne_zero h0 hz), hU, norm_mul, hn, one_mul]
    congr 1
    rw [ha, ← a1] at b1
    refine (pow_left_inj₀ ?_ ?_ two_ne_zero).1 b1 <;>
      (rw [← normSq1_eq_nrm1Sq]; exact normSq1_nonneg _ _)

variable {D : D7} {δ : ℂ} {M : IntermediateField ℚ ℂ}

theorem isCurveIdeal_ccK (D : D7) : IsCurveIdeal D D.host.ccK :=
  ⟨D.host.ccK_ne_bot, Nat.Coprime.mul_right (D.host.ccK_coprime 2 (by simp)) (D.host.ccK_coprime _ (by simp))⟩

theorem exists_discriminantTwelfthRoot_of_ideal (D : D7) : ∃ δ, IsDiscriminantTwelfthRootOfIdealLattice D D.host.ccK δ :=
  IsAlgClosed.exists_pow_nat_eq _ (by norm_num)

theorem lamOf_one (D : D7) : lamOf D D.host.ccK 1 = baseLat D.host := by
  unfold lamOf baseLat
  simp only [one_mul]

theorem lamOf_eq_map (D : D7) (δ : ℂ) :
    lamOf D D.host.ccK δ = (baseLat D.host).map (AddMonoidHom.mulLeft δ) := by
  unfold lamOf baseLat
  rw [AddMonoidHom.map_closure]
  congr 1
  ext w
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨_, ⟨c, hc, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    exact ⟨c, hc, rfl⟩

theorem discr_baseLat_ne_zero (D : D7) : TaylorLogMetric.discr (baseLat D.host) ≠ 0 := by
  obtain ⟨L, hL⟩ := GlobalTheory.Mem.Per.ConjCM.exists_periodPair_baseLat D.host
  exact (GlobalTheory.LatticeInvariants.invariants_dictionary L _ hL).2.2.1

theorem delta_ne_zero (h : IsDiscriminantTwelfthRootOfIdealLattice D D.host.ccK δ) : δ ≠ 0 := by
  rintro rfl
  apply discr_baseLat_ne_zero D
  rw [← lamOf_one, ← h]; simp

theorem discr_lamOf (h : IsDiscriminantTwelfthRootOfIdealLattice D D.host.ccK δ) : TaylorLogMetric.discr (lamOf D D.host.ccK δ) = 1 := by
  rw [lamOf_eq_map, Model.discr_map _ _ (delta_ne_zero h), ← lamOf_one, ← h,
    inv_mul_cancel₀ (pow_ne_zero _ (delta_ne_zero h))]

theorem jLat_lamOf (h : IsDiscriminantTwelfthRootOfIdealLattice D D.host.ccK δ) : jLat (lamOf D D.host.ccK δ) = jLat (baseLat D.host) := by
  rw [lamOf_eq_map, Model.jLat_map _ _ (delta_ne_zero h)]

theorem lamConj_spec {Λ : AddSubgroup ℂ} (h : TaylorLogMetric.discr Λ = 1) (h2 : g2 Λ ∈ M) (h3 : g3 Λ ∈ M) (ρ : M →ₐ[ℚ] ℂ) :
    g2 (lamConj M ρ Λ) = ρ ⟨_, h2⟩ ∧ g3 (lamConj M ρ Λ) = ρ ⟨_, h3⟩ ∧ TaylorLogMetric.discr (lamConj M ρ Λ) = 1 := by
  have h1 : ρ ⟨_, h2⟩ ^ 3 - 27 * ρ ⟨_, h3⟩ ^ 2 = 1 := by
    have : (⟨_, h2⟩ : M) ^ 3 - 27 * (⟨_, h3⟩ : M) ^ 2 = 1 := Subtype.ext h
    have e := congrArg ρ this
    rwa [map_sub, map_mul, map_pow, map_pow, map_ofNat, map_one] at e
  obtain ⟨L, e2, e3⟩ := GlobalTheory.LatticeInvariants.exists_periodPair_of_invariants (a := ρ ⟨_, h2⟩) (b := ρ ⟨_, h3⟩)
    (by rw [h1]; exact one_ne_zero)
  have hd := GlobalTheory.LatticeInvariants.invariants_dictionary L L.lattice.toAddSubgroup (fun _ => Iff.rfl)
  have l2 : liftM M (g2 Λ) = ⟨_, h2⟩ := dif_pos h2
  have l3 : liftM M (g3 Λ) = ⟨_, h3⟩ := dif_pos h3
  have hs := Classical.epsilon_spec (p := fun Λ' : AddSubgroup ℂ =>
    g2 Λ' = ρ (liftM M (g2 Λ)) ∧ g3 Λ' = ρ (liftM M (g3 Λ)))
    ⟨L.lattice.toAddSubgroup, by rw [hd.1, e2, l2], by rw [hd.2.1, e3, l3]⟩
  have a2 : g2 (lamConj M ρ Λ) = ρ ⟨_, h2⟩ := hs.1.trans (by rw [l2])
  have a3 : g3 (lamConj M ρ Λ) = ρ ⟨_, h3⟩ := hs.2.trans (by rw [l3])
  exact ⟨a2, a3, by rw [TaylorLogMetric.discr, a2, a3, h1]⟩

def into (D : D7) (M : IntermediateField ℚ ℂ) (hL : ∀ x, D.what₂.embLL x ∈ M) : D.what₂.LL →+* M :=
  D.what₂.embLL.codRestrict M hL

theorem conjLat_eq (hF : FieldOK D.host D.what₂.embLL D.embE) (h : IsDiscriminantTwelfthRootOfIdealLattice D D.host.ccK δ)
    (hL : ∀ x, D.what₂.embLL x ∈ M) (hM : DataIn D (tor0 D D.host.ccK δ) M) (ρ : M →ₐ[ℚ] ℂ)
    (s : D.what₂.LL →+* ℂ) (hs : ∀ x, s x = ρ (into D M hL x)) :
    ∃ ζ : ℂ, ζ ^ 12 = 1 ∧ conjLat D.host D.what₂.embLL s =
      (lamConj M ρ (lamOf D D.host.ccK δ)).map (AddMonoidHom.mulLeft ζ) := by
  obtain ⟨c1, a, ha, ha'⟩ := Model.conjLat_spec D.host hF s
  obtain ⟨a2, -, a1⟩ := lamConj_spec (discr_lamOf h) hM.2.1 hM.2.2 ρ
  refine exists_root_of_jLat_eq a1 c1 ?_
  have : into D M hL a = 1728 * (⟨_, hM.2.1⟩ : M) ^ 3 := by
    apply Subtype.ext
    change D.what₂.embLL a = 1728 * g2 (lamOf D D.host.ccK δ) ^ 3
    rw [ha, ← jLat_lamOf h, jLat, discr_lamOf h, div_one]
  rw [← ha', hs, this, jLat, a1, a2, div_one, map_mul, map_pow, map_ofNat]
  rfl

theorem data_of_fieldOK (hF : FieldOK D.host D.what₂.embLL D.embE) (h : IsDiscriminantTwelfthRootOfIdealLattice D D.host.ccK δ)
    (hL : ∀ x, D.what₂.embLL x ∈ M) :
    (∀ τ x, embT D τ x ∈ M) ∧ g2 (lamOf D D.host.ccK δ) ^ 3 ∈ M ∧ g3 (lamOf D D.host.ccK δ) ^ 2 ∈ M := by
  obtain ⟨a, ha⟩ := hF.1
  have h1 := discr_lamOf h
  have h2 : g2 (lamOf D D.host.ccK δ) ^ 3 = D.what₂.embLL (a / 1728) := by
    rw [map_div₀, ha, ← jLat_lamOf h, jLat, h1, map_ofNat]; ring
  refine ⟨fun τ x => ?_, h2 ▸ hL _, ?_⟩
  · have := hL (D.embE (D.host.sigmaOf (D.eTau τ).1 x))
    rwa [← RingHom.comp_apply, D.embE_φ₀] at this
  · have : g3 (lamOf D D.host.ccK δ) ^ 2 = D.what₂.embLL ((a / 1728 - 1) / 27) := by
      rw [map_div₀, map_sub, ← h2, map_one, map_ofNat]
      unfold TaylorLogMetric.discr at h1
      linear_combination -h1 / 27
    exact this ▸ hL _

theorem span_gen [NumberField M] (hF : FieldOK D.host D.what₂.embLL D.embE) (hL : ∀ x, D.what₂.embLL x ∈ M)
    (τ : D.what₂.Tau) :
    Submodule.span (𝓞 M) {into D M hL (gen D.host D.embE (D.eTau τ).1)} = ellT D M τ := by
  rw [GlobalTheory.Mem.EigenLine.ellT_eq_ellLat D M ((into D M hL).comp D.embE) (fun x => by rw [← D.embE_φ₀]; rfl) τ]
  have hg := Model.gen_spec D.host hF (D.eTau τ).1
  have key : ∀ (S : Set D.what₂.LL) (N : Submodule (𝓞 M) M), (∀ y ∈ S, into D M hL y ∈ N) →
      ∀ y ∈ Submodule.span (𝓞 D.what₂.LL) S, into D M hL y ∈ N := by
    intro S N hS y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact hS y hy
    | zero => rw [map_zero]; exact N.zero_mem
    | add x y _ _ hx hy => rw [map_add]; exact N.add_mem hx hy
    | smul r y _ hy =>
      have := N.smul_mem (RingOfIntegers.mapRingHom (into D M hL) r) hy
      rw [Algebra.smul_def, map_mul]
      exact this
  apply le_antisymm
  · rw [Submodule.span_singleton_le_iff_mem]
    refine key _ _ ?_ _ (hg.le (Submodule.mem_span_singleton_self _))
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact Submodule.subset_span ⟨a, ha, b, hb, rfl⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨a, ha, b, hb, rfl⟩
    refine key {gen D.host D.embE (D.eTau τ).1} _ ?_ _ (hg.ge (Submodule.subset_span ⟨a, ha, b, hb, rfl⟩))
    rintro _ rfl
    exact Submodule.mem_span_singleton_self _

theorem om_eq (hF : FieldOK D.host D.what₂.embLL D.embE) (h : IsDiscriminantTwelfthRootOfIdealLattice D D.host.ccK δ)
    (hL : ∀ x, D.what₂.embLL x ∈ M) (hM : DataIn D (tor0 D D.host.ccK δ) M) (ρ : M →ₐ[ℚ] ℂ)
    (s : D.what₂.LL →+* ℂ) (hs : ∀ x, s x = ρ (into D M hL x)) (τ : D.what₂.Tau) :
    (retie D).gx.Om τ s = Real.exp (-logMet M (lamOf D D.host.ccK δ) ρ
      (into D M hL (gen D.host D.embE (D.eTau τ).1))) := by
  obtain ⟨ζ, hζ, e⟩ := conjLat_eq hF h hL hM ρ s hs
  have h0 := (retie D).gx.Om_pos τ s
  have h1 : (retie D).gx.Om τ s = _ := Model.om_eq D.host hF D.eTau τ s
  rw [e, area_map_unit _ (norm_eq_one_of_pow hζ), hs] at h1
  rw [logMet, ← Real.log_inv, inv_div, ← h1, Real.exp_log h0]

theorem thOne_sq (hF : FieldOK D.host D.what₂.embLL D.embE) (h : IsDiscriminantTwelfthRootOfIdealLattice D D.host.ccK δ)
    (hL : ∀ x, D.what₂.embLL x ∈ M) (hM : DataIn D (tor0 D D.host.ccK δ) M) (ρ : M →ₐ[ℚ] ℂ)
    (s : D.what₂.LL →+* ℂ) (hs : ∀ x, s x = ρ (into D M hL x)) (t : ℂ)
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamConj M ρ (lamOf D D.host.ccK δ)) t) :
    (retie D).gx.thOne s ^ 2 = GL3Theta.normSq1 (lamConj M ρ (lamOf D D.host.ccK δ))
      (GL3Theta.th0 (lamConj M ρ (lamOf D D.host.ccK δ)) t) := by
  obtain ⟨ζ, hζ, e⟩ := conjLat_eq hF h hL hM ρ s hs
  have hc : Crv D D.host.ccK δ := ⟨isCurveIdeal_ccK D, h⟩
  have h0 : ζ ≠ 0 := by rintro rfl; simp at hζ
  have hd := (lamConj_spec (discr_lamOf h) hM.2.1 hM.2.2 ρ).2.2
  have hm : ∀ c z : ℂ, c * (ζ * z) ∈ conjLat D.host D.what₂.embLL s ↔
      c * z ∈ lamConj M ρ (lamOf D D.host.ccK δ) := fun c z => by
    rw [e, mul_left_comm]
    constructor
    · rintro ⟨y, hy, hy'⟩
      exact mul_left_cancel₀ h0 hy' ▸ hy
    · exact fun hz => ⟨_, hz, rfl⟩
  have hT : ∀ z, IsHalfPt D.host.d (conjLat D.host D.what₂.embLL s) (ζ * z) ↔
      GL3Theta.IsTwoTorsionPointUnkilled D (lamConj M ρ (lamOf D D.host.ccK δ)) z := fun z => by
    unfold IsHalfPt GL3Theta.IsTwoTorsionPointUnkilled
    rw [hm, hm, hm]
  have hε := Classical.epsilon_spec (p := IsHalfPt D.host.d (conjLat D.host D.what₂.embLL s)) ⟨_, (hT t).2 ht⟩
  have hv : thAt D.host D.what₂.embLL s = Real.sqrt (GL3Theta.normSq1 (lamConj M ρ (lamOf D D.host.ccK δ))
      (GL3Theta.th0 (lamConj M ρ (lamOf D D.host.ccK δ)) t)) := by
    unfold thAt
    generalize Classical.epsilon (IsHalfPt D.host.d (conjLat D.host D.what₂.embLL s)) = u at hε
    obtain ⟨v, rfl⟩ : ∃ v, u = ζ * v := ⟨ζ⁻¹ * u, by field_simp⟩
    rw [e, meanSquare_evenTheta_twelfthRoot_invariant hd hζ, normSq1_eq_nrm1Sq, thetaZero_eq_of_isThetaZero hc hM ρ ((hT v).1 hε) ht]
  have hp := normSq_thetaZero_pos hc hM ρ ht
  change posOr1 (thAt D.host D.what₂.embLL s) ^ 2 = _
  rw [posOr1, hv, if_pos (Real.sqrt_pos.2 hp), Real.sq_sqrt hp.le]

theorem perTie_retie (hF : FieldOK D.host D.what₂.embLL D.embE) (h : IsDiscriminantTwelfthRootOfIdealLattice D D.host.ccK δ)
    (h2 : g2 (lamOf D D.host.ccK δ) ∈ coefM D) (h3 : g3 (lamOf D D.host.ccK δ) ∈ coefM D) :
    PerTie (retie D) D.host.ccK δ := by
  have hL : ∀ x, D.what₂.embLL x ∈ coefM D := fun x => ⟨x, rfl⟩
  have hM : DataIn D (tor0 D D.host.ccK δ) (coefM D) := ⟨(data_of_fieldOK hF h hL).1, h2, h3⟩
  have hs : ∀ (s : D.what₂.LL →+* ℂ) x, s x = rhoOf D.what₂.embLL s (into D (coefM D) hL x) := fun s x =>
    (rhoOf_imEquiv D.what₂.embLL s x).symm
  exact ⟨⟨isCurveIdeal_ccK D, h⟩, hM,
    fun τ => ⟨_, span_gen hF hL τ, fun s => om_eq hF h hL hM _ s (hs s) τ⟩,
    fun s t ht => thOne_sq hF h hL hM _ s (hs s) t ht⟩

theorem exists_field (hF : FieldOK D.host D.what₂.embLL D.embE) (h : IsDiscriminantTwelfthRootOfIdealLattice D D.host.ccK δ) :
    ∃ (M : IntermediateField ℚ ℂ) (_ : NumberField M), (∀ x, D.what₂.embLL x ∈ M) ∧
      DataIn D (tor0 D D.host.ccK δ) M := by
  have hL : ∀ x, D.what₂.embLL x ∈ coefM D := fun x => ⟨x, rfl⟩
  obtain ⟨-, h2, h3⟩ := data_of_fieldOK hF h hL
  have hi : ∀ x ∈ coefM D, IsIntegral ℚ x := fun x hx =>
    (IsIntegral.of_finite ℚ (⟨x, hx⟩ : coefM D)).map (coefM D).val
  let S : Set ℂ := {g2 (lamOf D D.host.ccK δ), g3 (lamOf D D.host.ccK δ)}
  have hS : FiniteDimensional ℚ (IntermediateField.adjoin ℚ S) := by
    refine IntermediateField.finiteDimensional_adjoin ?_
    rintro _ (rfl | rfl)
    · exact (hi _ h2).of_pow (by norm_num)
    · exact (hi _ h3).of_pow (by norm_num)
  have hL' : ∀ x, D.what₂.embLL x ∈ coefM D ⊔ IntermediateField.adjoin ℚ S := fun x => le_sup_left (a := coefM D) (hL x)
  refine ⟨coefM D ⊔ IntermediateField.adjoin ℚ S, ⟨⟩, hL', (data_of_fieldOK hF h hL').1, ?_, ?_⟩
  · exact le_sup_right (a := coefM D) (IntermediateField.subset_adjoin ℚ S (by simp [S, tor0]))
  · exact le_sup_right (a := coefM D) (IntermediateField.subset_adjoin ℚ S (by simp [S, tor0]))

theorem retie_periods : ∀ D : D7, FieldOK D.host D.what₂.embLL D.embE →
    (∃ δ, IsDiscriminantTwelfthRootOfIdealLattice D D.host.ccK δ) ∧ ∀ δ, IsDiscriminantTwelfthRootOfIdealLattice D D.host.ccK δ →
      (∃ (M : IntermediateField ℚ ℂ) (_ : NumberField M), (∀ x, D.what₂.embLL x ∈ M) ∧
        DataIn D (tor0 D D.host.ccK δ) M) ∧
      ∀ (M : IntermediateField ℚ ℂ) [NumberField M] (hL : ∀ x, D.what₂.embLL x ∈ M),
        DataIn D (tor0 D D.host.ccK δ) M →
        ∃ c : D.what₂.Tau → D.what₂.LL, (∀ τ, Submodule.span (𝓞 M) {into D M hL (c τ)} = ellT D M τ) ∧
          ∀ ρ : M →ₐ[ℚ] ℂ,
            (∀ τ, (retie D).gx.Om τ ((ρ : M →+* ℂ).comp (into D M hL)) =
              Real.exp (-logMet M (lamOf D D.host.ccK δ) ρ (into D M hL (c τ)))) ∧
            ∀ t, GL3Theta.IsTwoTorsionPointUnkilled D (lamConj M ρ (lamOf D D.host.ccK δ)) t →
              (retie D).gx.thOne ((ρ : M →+* ℂ).comp (into D M hL)) ^ 2 =
                GL3Theta.normSq1 (lamConj M ρ (lamOf D D.host.ccK δ))
                  (GL3Theta.th0 (lamConj M ρ (lamOf D D.host.ccK δ)) t) :=
  fun D hF => ⟨exists_discriminantTwelfthRoot_of_ideal D, fun _ h => ⟨exists_field hF h, fun _ _ hL hM =>
    ⟨_, span_gen hF hL, fun ρ => ⟨om_eq hF h hL hM ρ _ fun _ => rfl, thOne_sq hF h hL hM ρ _ fun _ => rfl⟩⟩⟩⟩

end GlobalTheory.Mem.TruePeriods
