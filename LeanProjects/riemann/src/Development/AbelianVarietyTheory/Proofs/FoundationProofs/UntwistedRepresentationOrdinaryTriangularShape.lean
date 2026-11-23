import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsZetaTW
import Development.AbelianVarietyTheory.Definitions.Foundations.ThNSpec
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ZetaUr
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFixingMulFrobAt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.KatoTwCont
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.LocalFieldAutomorphisms.ValuationIntCastLtOneIff

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.CyclotomicQExpansion
open Polynomial
open scoped Matrix MatrixGroups Pointwise

namespace GlobalTheory.RhoAdm

theorem unifCont : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {E : Type} [NormedField E]
    (f : (Ω ≃ₐ[ℚ] Ω) → E), Continuous f → ∀ δ : ℝ, 0 < δ → ∃ E0 : Finset Ω, ∀ s s' : Ω ≃ₐ[ℚ] Ω,
      (∀ x ∈ E0, s' x = x) → ‖f (s * s') - f s‖ < δ := by
  intro Ω _ _ _ E _ f hf δ hδ
  classical
  haveI : CompactSpace (Ω ≃ₐ[ℚ] Ω) := inferInstance
  have key : ∀ x : Ω ≃ₐ[ℚ] Ω, ∃ V ∈ nhds (1 : Ω ≃ₐ[ℚ] Ω), ∀ a ∈ V, ∀ b ∈ V, ‖f (x * a * b) - f x‖ < δ / 2 := by
    intro x
    have hc : Continuous fun p : (Ω ≃ₐ[ℚ] Ω) × (Ω ≃ₐ[ℚ] Ω) => f (x * p.1 * p.2) :=
      hf.comp ((continuous_const.mul continuous_fst).mul continuous_snd)
    have ht := hc.tendsto (1, 1)
    simp only [mul_one] at ht
    have hev := (Metric.tendsto_nhds.1 ht) (δ / 2) (by linarith)
    rw [nhds_prod_eq] at hev
    obtain ⟨V, hV, hV'⟩ :=
      (Filter.eventually_prod_self_iff (r := fun a b => dist (f (x * a * b)) (f x) < δ / 2)).1 hev
    exact ⟨V, hV, fun a ha b hb => by simpa [dist_eq_norm] using hV' a ha b hb⟩
  choose V hV1 hV using key
  obtain ⟨U, hU1, hU⟩ : ∃ U ∈ nhds (1 : Ω ≃ₐ[ℚ] Ω), ∀ s, ∀ u ∈ U, ‖f (s * u) - f s‖ < δ := by
    obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
      (fun x => (fun y => x⁻¹ * y) ⁻¹' interior (V x))
      (fun x => isOpen_interior.preimage (continuous_mul_left x⁻¹))
      (fun y _ => Set.mem_iUnion.2 ⟨y, by
        show y⁻¹ * y ∈ interior (V y)
        rw [inv_mul_cancel]
        exact mem_interior_iff_mem_nhds.2 (hV1 y)⟩)
    refine ⟨⋂ x ∈ t, V x, (Filter.biInter_finset_mem t).2 fun x _ => hV1 x, fun s u hu => ?_⟩
    obtain ⟨x, hxt, hsx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ s))
    have ha : x⁻¹ * s ∈ V x := interior_subset hsx
    have hux : u ∈ V x := Set.mem_iInter₂.1 hu x hxt
    have h1 := hV x (x⁻¹ * s) ha u hux
    have h2 := hV x (x⁻¹ * s) ha 1 (mem_of_mem_nhds (hV1 x))
    simp only [mul_inv_cancel_left, mul_one] at h1 h2
    calc ‖f (s * u) - f s‖ = ‖(f (s * u) - f x) - (f s - f x)‖ := by congr 1; abel
      _ ≤ ‖f (s * u) - f x‖ + ‖f s - f x‖ := norm_sub_le _ _
      _ < δ / 2 + δ / 2 := add_lt_add h1 h2
      _ = δ := by ring
  obtain ⟨L, hL, hLU⟩ := (krullTopology_mem_nhds_one_iff ℚ Ω U).1 hU1
  let b := Module.finBasis ℚ L
  refine ⟨Finset.univ.image (fun i => (b i : Ω)), fun s s' hs' => hU s s' (hLU ?_)⟩
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  suffices h : ∀ y : L, s' y = y from fun x hx => h ⟨x, hx⟩
  intro y
  have hy := b.mem_span y
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨i, rfl⟩ := hz
    exact hs' _ (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩)
  | zero => simp
  | add y z _ _ hy hz => simp [hy, hz]
  | smul c y _ hy => simp [hy]

theorem normV_ratPrime {q : ℕ} (hq : q.Prime) (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : ((q : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) : normV v = q := by
  have h1 : normV v = Ideal.absNorm v.asIdeal := by
    unfold normV
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have h2 : Ideal.absNorm v.asIdeal ∣ Ideal.absNorm (Ideal.span {((q : ℕ) : 𝓞 ℚ)}) :=
    Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).mpr hv)
  have h3 : Ideal.absNorm (Ideal.span {((q : ℕ) : 𝓞 ℚ)}) = q := by
    rw [Ideal.absNorm_span_singleton]
    have h4 : ((q : ℕ) : 𝓞 ℚ) = algebraMap ℤ (𝓞 ℚ) (q : ℤ) := by simp
    rw [h4, Algebra.norm_algebraMap, RingOfIntegers.rank, Module.finrank_self]
    simp
  rw [h3] at h2
  rcases (Nat.dvd_prime hq).mp h2 with h | h
  · exact absurd (Ideal.absNorm_eq_one_iff.mp h) v.isPrime.ne_top
  · rw [h1, h]

theorem frobPlace : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] (q : ℕ), q.Prime → ∀ s : Ω ≃ₐ[ℚ] Ω, FrobAt q s →
    ∃ (w : HeightOneSpectrum (𝓞 ℚ)) (A : ValuationSubring Ω), normV w = q ∧ IsPlaceOver A w ∧
      IsFrob (F := ℚ) A (normV w) s := by
  intro Ω _ _ q hq s hs
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  obtain ⟨V, hqV, hV⟩ := hs
  have hval : V.valuation (q : Ω) < 1 := (ValuationSubring.mem_nonunits_iff V).1 hqV
  have hover : IsPlaceOver V (ReciprocityTheory.Neutral.Cmp.ratPrime q) := fun x => by
    have h := ReciprocityTheory.Neutral.Cmp.lies_over_ratPrime V hval x
    rw [eq_ratCast] at h
    rw [eq_ratCast]
    exact h
  have hmem : ((q : ℕ) : 𝓞 ℚ) ∈ (ReciprocityTheory.Neutral.Cmp.ratPrime q).asIdeal := (hover _).1 (by simpa using hval)
  have hn : normV (ReciprocityTheory.Neutral.Cmp.ratPrime q) = q := normV_ratPrime hq _ hmem
  refine ⟨_, V, hn, hover, ?_⟩
  show s ∈ V.decompositionSubgroup ℚ ∧ ∀ x, V.valuation x ≤ 1 → V.valuation (s x - x ^ normV _) < 1
  rw [hn]
  have key : ∀ y : Ω, s y ∈ V → y ∈ V := by
    intro y hy
    by_contra hyV
    have hy0 : y ≠ 0 := fun h => hyV (h ▸ V.zero_mem)
    have hlt : 1 < V.valuation y := by
      rw [← not_le, V.valuation_le_one_iff]; exact hyV
    have hinv : V.valuation y⁻¹ < 1 := by rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hlt
    have hinvV : y⁻¹ ∈ V := (V.valuation_le_one_iff _).1 hinv.le
    have h1 := (hV y⁻¹ hinvV).2
    have h2 : V.valuation (y⁻¹ ^ q) < 1 := by
      rw [map_pow]; exact pow_lt_one₀ zero_le' hinv hq.ne_zero
    have h3 : V.valuation (s y⁻¹) < 1 := by
      have := Valuation.map_add_lt V.valuation h1 h2
      rwa [sub_add_cancel] at this
    have h4 : V.valuation (s y) ≤ 1 := (V.valuation_le_one_iff _).2 hy
    rw [map_inv₀ s] at h3
    have h5 : V.valuation (s y * (s y)⁻¹) < 1 := by
      rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' h4) h3
    rw [mul_inv_cancel₀ ((map_ne_zero s).2 hy0), map_one] at h5
    exact lt_irrefl _ h5
  refine ⟨MulAction.mem_stabilizer_iff.2 ?_, fun x hx => (hV x ((V.valuation_le_one_iff x).1 hx)).2⟩
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
  constructor
  · intro h
    have := (hV _ h).1
    rwa [AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply] at this
  · intro h
    apply key
    rwa [AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]

theorem killsMu_inv {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {χ : G ℚ Ω →* (Qbar l)ˣ}
    (h : KillsMu l χ) : KillsMu l χ⁻¹ := by
  intro s hs
  simp [h s hs]

variable {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω]

theorem unTw_eq (e : ℕ) (W : R2 Ω l) (χ : G ℚ Ω →* (Qbar l)ˣ) :
    unTw W e χ = tw W (cycBar ℚ Ω l ^ (e : ℤ) * χ⁻¹) := by
  rw [zpow_natCast]; rfl

theorem untw_val (e : ℕ) (W : R2 Ω l) (χ : G ℚ Ω →* (Qbar l)ˣ) (s : G ℚ Ω) :
    (unTw W e χ s : Matrix (Fin 2) (Fin 2) (Qbar l)) = ((cycBar ℚ Ω l ^ (e : ℤ) * χ⁻¹) s : Qbar l) • mat W s := by
  rw [unTw_eq]; exact tw_val _ _ _

theorem untw_val' (e : ℕ) (W : R2 Ω l) (χ : G ℚ Ω →* (Qbar l)ˣ) (s : G ℚ Ω) :
    (unTw W e χ s : Matrix (Fin 2) (Fin 2) (Qbar l)) = (eps l s ^ e * (χ s : Qbar l)⁻¹) • mat W s := by
  rw [untw_val]; simp

theorem untw_det (e : ℕ) (W : R2 Ω l) (χ : G ℚ Ω →* (Qbar l)ˣ) (s : G ℚ Ω) :
    (unTw W e χ s : Matrix (Fin 2) (Fin 2) (Qbar l)).det =
      eps l s ^ (2 * e) * (((χ s : Qbar l)⁻¹) ^ 2 * (dt W s : Qbar l)) := by
  have hdet : ((dt W s : (Qbar l)ˣ) : Qbar l) = (mat W s).det := by
    simp [dt, mat, Matrix.GeneralLinearGroup.val_det_apply]
  rw [untw_val', Matrix.det_smul, Fintype.card_fin, hdet]
  ring

theorem untw_irr (e : ℕ) (W : R2 Ω l) (χ : G ℚ Ω →* (Qbar l)ˣ) (hirr : IsIrr (W.comp (H0g W).subtype)) :
    ∀ V : Submodule (Qbar l) (Fin 2 → Qbar l),
      (∀ s v, v ∈ V → (unTw W e χ s : Matrix (Fin 2) (Fin 2) (Qbar l)) *ᵥ v ∈ V) → V = ⊥ ∨ V = ⊤ := by
  intro V hV
  refine hirr.2.2 V le_top fun s v hv => ?_
  have h := V.smul_mem ((((cycBar ℚ Ω l ^ (e : ℤ) * χ⁻¹) (s : G ℚ Ω) : (Qbar l)ˣ)⁻¹ : (Qbar l)ˣ) : Qbar l) (hV s v hv)
  rw [untw_val, Matrix.smul_mulVec, smul_smul, Units.inv_mul, one_smul] at h
  exact h

theorem att_inv_eq (e : ℕ) (W : R2 Ω l) (χ : G ℚ Ω →* (Qbar l)ˣ) (s : G ℚ Ω) :
    (tw W (cycBar ℚ Ω l ^ (-(e : ℤ)) * (dt W)⁻¹ * χ) s⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)) =
      (unTw W e χ s : Matrix (Fin 2) (Fin 2) (Qbar l)).adjugate := by
  have hu : (cycBar ℚ Ω l ^ (-(e : ℤ)) * (dt W)⁻¹ * χ) s⁻¹ = (cycBar ℚ Ω l ^ (e : ℤ) * χ⁻¹) s * dt W s := by
    simp only [map_inv, MonoidHom.mul_apply, MonoidHom.inv_apply, zpow_neg, MonoidHom.zpow_apply]
    simp [mul_comm, mul_left_comm, mul_assoc]
  have hdet : ((dt W s : (Qbar l)ˣ) : Qbar l) = (mat W s).det := by
    simp [dt, mat, Matrix.GeneralLinearGroup.val_det_apply]
  have hne : (mat W s).det ≠ 0 := hdet ▸ Units.ne_zero _
  rw [tw_val, untw_val, hu, Units.val_mul, hdet, map_inv, Matrix.coe_units_inv, Matrix.adjugate_smul,
    Fintype.card_fin]
  change _ • (mat W s)⁻¹ = _
  rw [Matrix.inv_def, Ring.inverse_eq_inv', smul_smul, mul_assoc, mul_inv_cancel₀ hne, mul_one, pow_one]

theorem coeff_quad (a b : ℂ) :
    (X ^ 2 - C a * X + C b : ℂ[X]).coeff 1 = -a ∧ (X ^ 2 - C a * X + C b : ℂ[X]).coeff 0 = b := by
  constructor <;> simp [coeff_X, coeff_C, coeff_X_pow]

theorem frob_trace_det (ι : Qbar l ≃+* ℂ) (e : ℕ) (W : R2 Ω l) (g : Newform (2 * e + 1)) (χ : G ℚ Ω →* (Qbar l)ˣ)
    (hatt : g.Att ι (tw W (cycBar ℚ Ω l ^ (-(e : ℤ)) * (dt W)⁻¹ * χ))) :
    ∃ S0 : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S0 → ∀ s : Ω ≃ₐ[ℚ] Ω, FrobAt q s →
      Matrix.trace (unTw W e χ s : Matrix (Fin 2) (Fin 2) (Qbar l)) = ι.symm (g.a q) ∧
      Matrix.det (unTw W e χ s : Matrix (Fin 2) (Fin 2) (Qbar l)) =
        (q : Qbar l) ^ (2 * e) * ι.symm (g.χ (q : ZMod g.M)) := by
  classical
  have hB := Filter.eventually_cofinite.1 hatt.2
  refine ⟨hB.toFinset.image normV, fun q hq hqS s hs => ?_⟩
  obtain ⟨w, A, hn, hA, hF⟩ := frobPlace q hq s hs
  have hw : w ∉ hB.toFinset := fun h => hqS (Finset.mem_image.2 ⟨w, h, hn⟩)
  have hgood := of_not_not fun h => hw (hB.mem_toFinset.2 h)
  have hcp := (hgood A hA).2 s hF
  rw [hn, att_inv_eq] at hcp
  set M := (unTw W e χ s : Matrix (Fin 2) (Fin 2) (Qbar l))
  have htr : M.adjugate.trace = M.trace := by
    simp [Matrix.trace_fin_two, Matrix.adjugate_fin_two, add_comm]
  have hdt : M.adjugate.det = M.det := by
    rw [Matrix.det_adjugate, Fintype.card_fin]; simp
  have h1 : (Polynomial.map ι.toRingHom M.adjugate.charpoly).coeff 1 = (g.heckePoly q).coeff 1 := by rw [hcp]
  have h0 : (Polynomial.map ι.toRingHom M.adjugate.charpoly).coeff 0 = (g.heckePoly q).coeff 0 := by rw [hcp]
  rw [Polynomial.coeff_map, Newform.heckePoly, (coeff_quad _ _).1] at h1
  rw [Polynomial.coeff_map, Newform.heckePoly, (coeff_quad _ _).2] at h0
  have et := Matrix.trace_eq_neg_charpoly_coeff M.adjugate
  have ed := Matrix.det_eq_sign_charpoly_coeff M.adjugate
  simp only [Fintype.card_fin, Nat.reduceSub] at et ed
  constructor
  · rw [← htr, et]
    apply ι.injective
    simp only [map_neg, RingEquiv.apply_symm_apply]
    simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe] at h1
    rw [h1, neg_neg]
  · rw [← hdt, ed]
    apply ι.injective
    simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe] at h0
    simp only [map_mul, map_pow, map_neg, map_one, RingEquiv.apply_symm_apply, map_natCast, h0, neg_one_sq, one_mul]
    rw [show 2 * e + 1 - 1 = 2 * e by omega, mul_comm]

theorem untw_cont [IsAlgClosure ℚ Ω] (e : ℕ) (W : R2 Ω l) (χ : G ℚ Ω →* (Qbar l)ˣ) (hW : Continuous W)
    (hχ : KillsMu l χ) : Continuous (unTw W e χ) := by
  rw [unTw_eq]
  exact UpperTheory.V.X.Kato.twCont l Ω 2 W hW l (Fact.out : l.Prime).one_lt.le χ⁻¹ (killsMu_inv hχ) e

theorem root_eq {p M n : ℕ} (hp : p.Prime) (hM : ¬ p ∣ M) (V : ValuationSubring Ω) (hV : V.valuation (p : Ω) < 1)
    (s : G ℚ Ω) (hs : ∀ x, V.valuation x ≤ 1 → V.valuation (s x - x ^ n) < 1) {ζ : Ω} (hζ : ζ ^ M = 1) :
    s ζ = ζ ^ n := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hM0 : M ≠ 0 := fun h => hM (h ▸ dvd_zero p)
  have hN : ¬ V.valuation (M : Ω) < 1 := fun h => by
    have := (ReciprocityTheory.Neutral.Cmp.valuation_intCast_lt_one_iff V hV (M : ℤ)).1 (by simpa using h)
    exact hM (Int.natCast_dvd_natCast.1 this)
  refine eq_of_pow_eq_one V hN ?_ ?_ (hs ζ (valuation_eq_one_of_pow_eq_one V hM0 hζ).le)
  · rw [← map_pow, hζ, map_one]
  · rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]

theorem eps_frobAt [IsAlgClosure ℚ Ω] {q : ℕ} (hq : q.Prime) (hql : q ≠ l) {s : G ℚ Ω} (hs : FrobAt q s) :
    eps l s = (q : Qbar l) := by
  obtain ⟨w, B, hn, hB, hF⟩ := frobPlace q hq s hs
  have hl : ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := fun h => hql (hn.symm.trans (normV_ratPrime Fact.out w h))
  have h := cycZ_of_isFrob hl hB hF
  have e1 : eps l s = algebraMap ℚ_[l] (Qbar l) (((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) := rfl
  rw [e1, h, hn]
  simp

theorem det_mul_eq_one_on_inertia [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (W : R2 Ω l) (g : Newform (2 * e + 1))
    (χ : G ℚ Ω →* (Qbar l)ˣ) (hW : Continuous W) (hχ : KillsMu l χ)
    (hatt : g.Att ι (tw W (cycBar ℚ Ω l ^ (-(e : ℤ)) * (dt W)⁻¹ * χ))) (hM : ¬ l ∣ g.M)
    {A : ValuationSubring Ω} (hA : OverL l A) {s : G ℚ Ω} (hs : s ∈ Ine (F := ℚ) A) :
    ((χ s : Qbar l)⁻¹) ^ 2 * (dt W s : Qbar l) = 1 := by
  classical
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : NeZero g.M := ⟨g.pos.ne'⟩
  haveI : NeZero ((g.M : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr g.pos.ne'⟩
  set η : G ℚ Ω → Qbar l := fun t => ((χ t : Qbar l)⁻¹) ^ 2 * (dt W t : Qbar l) with hη
  have hc : Continuous η := by
    have h := (Units.continuous_val.comp (untw_cont 0 W χ hW hχ)).matrix_det
    refine h.congr fun t => ?_
    simp only [Function.comp_apply, untw_det, hη, mul_zero, pow_zero, one_mul]
  show η s = 1
  by_contra hne
  obtain ⟨E0, hE0⟩ := unifCont η hc ‖1 - η s‖ (norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hne)))
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω g.M
  obtain ⟨S0, hS0⟩ := frob_trace_det ι e W g χ hatt
  obtain ⟨s', q, hs', hq, hqS, hF⟩ := exists_fixing_mul_frobAt s (insert ζ E0) (insert l (S0 ∪ g.M.primeFactors))
  simp only [Finset.mem_insert, Finset.mem_union, not_or, Nat.mem_primeFactors] at hqS
  obtain ⟨hql, hqS0, hqM⟩ := hqS
  have hqM' : ¬ q ∣ g.M := fun h => hqM ⟨hq, h, g.pos.ne'⟩
  have hlA : A.valuation (l : Ω) < 1 := by
    obtain ⟨v, hv, hlv⟩ := hA
    simpa using (hv _).2 hlv
  have h1 : s ζ = ζ := by
    simpa using root_eq (n := 1) Fact.out hM A hlA s (fun x hx => by simpa using hs.2 x hx) hζ.pow_eq_one
  have h2 : (s * s') ζ = ζ ^ q := by
    obtain ⟨V, hqV, hV⟩ := hF
    exact root_eq hq hqM' V ((ValuationSubring.mem_nonunits_iff V).1 hqV) (s * s')
      (fun x hx => (hV x ((V.valuation_le_one_iff x).1 hx)).2) hζ.pow_eq_one
  rw [AlgEquiv.mul_apply, hs' ζ (Finset.mem_insert_self _ _), h1] at h2
  have hq1 : (q : ZMod g.M) = 1 := by
    obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by have := hq.pos; omega⟩
    have hζ0 : ζ ≠ 0 := hζ.ne_zero g.pos.ne'
    have hk : ζ ^ k = 1 := by
      apply mul_right_cancel₀ hζ0
      rw [← pow_succ, ← h2, one_mul]
    have := (ZMod.natCast_eq_zero_iff k g.M).2 ((hζ.pow_eq_one_iff_dvd k).1 hk)
    push_cast
    rw [this, zero_add]
  have hd := (hS0 q hq hqS0 (s * s') hF).2
  rw [untw_det, eps_frobAt hq hql hF, hq1, map_one, map_one] at hd
  have hq0 : (q : Qbar l) ^ (2 * e) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hq.ne_zero)
  have h3 : η (s * s') = 1 := mul_left_cancel₀ hq0 hd
  have h4 := hE0 s s' fun x hx => hs' x (Finset.mem_insert_of_mem hx)
  rw [h3] at h4
  exact lt_irrefl _ h4

theorem rho_ordinary_shape : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (S : Finset Pl)
    (A : ValuationSubring Ω) (W : R2 Ω l) (g : Newform (2 * e + 1)) (ψ : ZMod l → Qbar l),
  Nf e S A W → SrcUr ι e A W g →
  (∃ χ : G ℚ Ω →* (Qbar l)ˣ, KillsMu l χ ∧
    (∀ s ∈ Ine (F := ℚ) A, mat W s 1 1 * (cycBar ℚ Ω l s : Qbar l) ^ (e : ℤ) * ((dt W s : Qbar l)⁻¹ * (χ s : Qbar l)) = 1) ∧
    ∀ s : G ℚ Ω, (χ s : Qbar l) = ψ ((((cycMod (F := ℚ) (Ω := Ω) l 1 s : ZMod (l ^ 1))).val : ℕ) : ZMod l)) →
  ∃ ρ : (Ω ≃ₐ[ℚ] Ω) →* GL (Fin 2) (Qbar l),
    (∀ s, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) = rhoK W e ψ s) ∧ Continuous ρ ∧
    (∀ s ∈ Dec (F := ℚ) A, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) 1 0 = 0) ∧
    (∀ s ∈ Ine (F := ℚ) A, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) 1 1 = 1) ∧
    ∃ F : Finset Ω, ∀ s ∈ Ine (F := ℚ) A, (∀ y ∈ F, s y = y) →
      (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) 0 0 = ((cycZ ℚ Ω l s : ℤ_[l]) : Qbar l) ^ (2 * e) := by
  intro l _ Ω _ _ _ ι e S A W g ψ hN hU hψ
  obtain ⟨χ, hχ, hin, hχψ⟩ := hψ
  obtain ⟨hM, -, χ', hχ', hatt, hin'⟩ := hU
  have hkey : ∀ s ∈ Ine (F := ℚ) A, ((χ s : Qbar l)⁻¹) ^ 2 * (dt W s : Qbar l) = 1 := by
    intro s hs
    have h := det_mul_eq_one_on_inertia ι e W g χ' hN.cont hχ' hatt hM hN.atL hs
    have h1 := hin s hs
    have h2 := hin' s hs
    have h0 : mat W s 1 1 * (cycBar ℚ Ω l s : Qbar l) ^ (e : ℤ) ≠ 0 := left_ne_zero_of_mul_eq_one h1
    have h3 := mul_left_cancel₀ h0 (h1.trans h2.symm)
    have h4 := mul_left_cancel₀ (inv_ne_zero (Units.ne_zero (dt W s))) h3
    rwa [h4]
  have h10 : ∀ s ∈ Dec (F := ℚ) A, (unTw W e χ s : Matrix (Fin 2) (Fin 2) (Qbar l)) 1 0 = 0 := by
    intro s hs
    rw [untw_val', Matrix.smul_apply, hN.upper s hs, smul_zero]
  have h11 : ∀ s ∈ Ine (F := ℚ) A, (unTw W e χ s : Matrix (Fin 2) (Fin 2) (Qbar l)) 1 1 = 1 := by
    intro s hs
    have h1 := hin s hs
    have h2 := hkey s hs
    have hx : (χ s : Qbar l) ≠ 0 := Units.ne_zero _
    have hd : (dt W s : Qbar l) ≠ 0 := Units.ne_zero _
    rw [zpow_natCast] at h1
    rw [untw_val', Matrix.smul_apply, smul_eq_mul]
    calc eps l s ^ e * (χ s : Qbar l)⁻¹ * mat W s 1 1
        = (mat W s 1 1 * (cycBar ℚ Ω l s : Qbar l) ^ e * ((dt W s : Qbar l)⁻¹ * (χ s : Qbar l))) *
          (((χ s : Qbar l)⁻¹) ^ 2 * (dt W s : Qbar l)) := by
          simp only [eps]
          field_simp
      _ = 1 := by rw [h1, h2, one_mul]
  refine ⟨unTw W e χ, fun s => ?_, untw_cont e W χ hN.cont hχ, h10, h11, ∅, fun s hs _ => ?_⟩
  · rw [untw_val', rhoK, thK, ← hχψ s, mul_inv, inv_inv]
  · have hd := untw_det e W χ s
    rw [Matrix.det_fin_two, h11 s hs, h10 s (Ine_le_Dec A hs), hkey s hs, mul_one, mul_zero, sub_zero, mul_one] at hd
    exact hd

end GlobalTheory.RhoAdm

end
