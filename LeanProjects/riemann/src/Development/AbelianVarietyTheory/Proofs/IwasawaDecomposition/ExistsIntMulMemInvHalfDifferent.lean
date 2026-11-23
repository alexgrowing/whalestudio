import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIntegralHalf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyIsoKGStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsComplexLinearExtensionOfTraceIsometryStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMatrixBasisLatticeUpToDenominatorNotMemStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryMulIntegralAtSplitPrimeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SelfDualLatticeStandardAtRationalPrimeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrimeOverSplitNotMemConjStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComapSingleSpanAlgebraMapNumberFieldStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteExtensionCapitulationComplexStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCurveLatticeStatement

noncomputable section

namespace GlobalTheory.Mem.Col2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Matrix
open scoped BigOperators

namespace AmbEx

theorem form_mulVec {K n : Type} [Field K] [Fintype n] [DecidableEq n] (σ : K →+* K) (u : Matrix n n K)
    (hu : (u.map σ)ᵀ * u = 1) (x y : n → K) : ∑ i, (u *ᵥ x) i * σ ((u *ᵥ y) i) = ∑ i, x i * σ (y i) := by
  have h1 : ∀ i, σ ((u *ᵥ y) i) = (u.map σ *ᵥ fun j => σ (y j)) i := fun i => RingHom.map_mulVec σ u y i
  simp only [h1]
  change (u *ᵥ x) ⬝ᵥ (u.map σ *ᵥ fun j => σ (y j)) = x ⬝ᵥ fun j => σ (y j)
  rw [dotProduct_comm, dotProduct_mulVec, vecMul_mulVec, hu, vecMul_one, dotProduct_comm]

theorem exists_move : ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* K) (n : Type) [Fintype n] [DecidableEq n] (p : ℕ) (𝔭 : HeightOneSpectrum (𝓞 K)) (α β : 𝓞 K) (L : Submodule (𝓞 K) (n → K)), (∀ x, σ (σ x) = x) → (∀ x : 𝓞 K, ∃ m : ℤ, (x : K) * σ x = m) → p.Prime → (p : 𝓞 K) ∈ 𝔭.asIdeal → α ∈ 𝔭.asIdeal → β ∉ 𝔭.asIdeal → (β : K) = σ α → L.FG → Submodule.span K (L : Set (n → K)) = ⊤ → (∀ x, x ∈ L ↔ ∀ y ∈ L, ∑ i, x i * σ (y i) ∈ (algebraMap (𝓞 K) K).range) → ∃ u : (n → K) ≃ₗ[K] (n → K), (∀ x y, ∑ i, u x i * σ (u y i) = ∑ i, x i * σ (y i)) ∧ ∃ s : ℕ, Nat.Coprime s p ∧ (∀ x ∈ L, ∀ i, (s : K) * u x i ∈ (algebraMap (𝓞 K) K).range) ∧ ∀ v : n → K, (∀ i, v i ∈ (algebraMap (𝓞 K) K).range) → (s : K) • u.symm v ∈ L := by
  intro K _ _ σ n _ _ p 𝔭 α β L hσ hN hp hp𝔭 hα hβ hαβ hfg hsp hsd
  obtain ⟨g, hg, t, ht, hL, hc⟩ := GlobalTheory.T.exists_matrix_basis_lattice_up_to_denominator_notMem K n L 𝔭 hfg hsp
  obtain ⟨u, hu, t', ht', h1, h2⟩ := GlobalTheory.T.exists_unitary_mul_integral_at_split_prime K σ n 𝔭 α β hσ hα hβ hαβ g hg
  have hud : IsUnit u.det := Matrix.isUnit_det_of_left_inverse hu
  let e : (n → K) ≃ₗ[K] (n → K) := (Matrix.toLinearEquiv' u (Matrix.invertibleOfIsUnitDet u hud)).symm
  have hes : ∀ v, e.symm v = u *ᵥ v := fun v => rfl
  have he : ∀ x, e x = u⁻¹ *ᵥ x := fun x => by
    apply e.symm.injective
    rw [e.symm_apply_apply, hes, mulVec_mulVec, mul_nonsing_inv _ hud, one_mulVec]
  have hform : ∀ x y, ∑ i, e x i * σ (e y i) = ∑ i, x i * σ (y i) := fun x y => by
    rw [← form_mulVec σ u hu (e x) (e y), ← hes, ← hes, e.symm_apply_apply, e.symm_apply_apply]
  let L' : Submodule (𝓞 K) (n → K) := L.comap (e.symm.toLinearMap.restrictScalars (𝓞 K))
  have hm : ∀ v, v ∈ L' ↔ e.symm v ∈ L := fun v => Iff.rfl
  have htt : t * t' ∉ 𝔭.asIdeal := fun h => (𝔭.isPrime.mem_or_mem h).elim ht ht'
  obtain ⟨s, hs, ha, hb⟩ := GlobalTheory.T.selfDual_lattice_standard_at_rational_prime K σ n p 𝔭 α β L' (t * t') hσ hN hp hp𝔭 hα hβ hαβ
    (fun x => by
      rw [hm, hsd]
      constructor
      · intro h y hy
        have := h _ ((hm y).1 hy)
        rwa [← hform, e.apply_symm_apply, e.apply_symm_apply] at this
      · intro h y hy
        have := h (e y) (by rw [hm, e.symm_apply_apply]; exact hy)
        rwa [← hform, e.apply_symm_apply]) htt
    (fun x hx i => by
      have hx' := hL _ ((hm x).1 hx)
      have : x = (u⁻¹ * g) *ᵥ (g⁻¹ *ᵥ e.symm x) := by
        rw [mulVec_mulVec, Matrix.mul_assoc, mul_nonsing_inv _ hg, Matrix.mul_one, ← he, e.apply_symm_apply]
      have e2 : ((t * t' : 𝓞 K) : K) * x i = ∑ j, ((t' : K) * (u⁻¹ * g) i j) * ((t : K) * (g⁻¹ *ᵥ e.symm x) j) := by
        conv_lhs => rw [this]
        simp only [mulVec, dotProduct, Finset.mul_sum]
        push_cast
        exact Finset.sum_congr rfl fun j _ => by simp only [← Finset.mul_sum]; ring
      rw [e2]
      exact sum_mem fun j _ => mul_mem (h2 i j) (hx' j))
    (fun j => by
      rw [hm, hes]
      choose c hc' using fun k => h1 k j
      have e2 : u *ᵥ (Pi.single j ((t * t' : 𝓞 K) : K)) = ∑ k, c k • ((t : K) • fun i => g i k) := by
        have : u = g * (g⁻¹ * u) := by rw [← Matrix.mul_assoc, mul_nonsing_inv _ hg, Matrix.one_mul]
        funext i
        have h3 : (u *ᵥ (Pi.single j ((t * t' : 𝓞 K) : K))) i = u i j * ((t : K) * t') := by
          simp [mulVec_single]
        have h4 : u i j = ∑ k, g i k * (g⁻¹ * u) k j := by
          conv_lhs => rw [this]
          exact Matrix.mul_apply
        rw [h3, h4, Finset.sum_apply, Finset.sum_mul]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Pi.smul_apply, Pi.smul_apply, Algebra.smul_def, hc', smul_eq_mul]
        ring
      rw [e2]
      exact sum_mem fun k _ => L.smul_mem _ (hc k))
  refine ⟨e, hform, s, hs, fun x hx i => ha _ (by rw [hm, e.symm_apply_apply]; exact hx) i, fun v hv => ?_⟩
  have := (hm _).1 (hb v hv)
  rwa [map_smul] at this

theorem exists_gen_pow {K : Type} [Field K] [NumberField K] (𝔭 : HeightOneSpectrum (𝓞 K)) :
    ∃ π : 𝓞 K, 𝔭.asIdeal ^ classNumber K = Ideal.span {π} := by
  have hI0 : 𝔭.asIdeal ∈ nonZeroDivisors (Ideal (𝓞 K)) := mem_nonZeroDivisors_of_ne_zero 𝔭.ne_bot
  have hp : (𝔭.asIdeal ^ classNumber K).IsPrincipal := by
    rw [← ClassGroup.mk0_eq_one_iff (pow_mem hI0 _)]
    have : (⟨𝔭.asIdeal ^ classNumber K, pow_mem hI0 _⟩ : nonZeroDivisors (Ideal (𝓞 K))) = ⟨𝔭.asIdeal, hI0⟩ ^ classNumber K := rfl
    rw [this, map_pow, classNumber]
    exact pow_card_eq_one
  exact ⟨_, (Ideal.span_singleton_generator _).symm⟩

variable {R : Ranks} (H : Host R)

theorem nonempty_isoK : Nonempty (Th.IsoK H (Tau R)) :=
  GlobalTheory.T.nonempty_isoKG_of_trace_positive H.K H.E (H.conj : H.E →+* H.E) (HostK.conjK H) (Tau R) (HostK.card_tau H) (fun _ => rfl)
    (UnusedSlot33.HK.conj_conj H) (HostK.trace_conj H) (HostK.trace_pos H)

theorem exists_int_mul_mem_invHalfDifferent (x : H.E) : ∃ N : ℤ, N ≠ 0 ∧ (N : H.E) * x ∈ H.AA0 := by
  obtain ⟨a, ha, ha0⟩ : ∃ a ∈ H.AA0, a ≠ 0 := by
    by_contra h
    push Not at h
    refine one_ne_zero (h 1 ((factMMUnimodular R H 1).2 fun y hy => ?_))
    rw [h y hy, map_zero, mul_zero, map_zero]
    exact zero_mem _
  obtain ⟨N, hN, hi⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ H.E).2
    (Algebra.IsAlgebraic.isAlgebraic (x / a))).exists_integral_multiple
  refine ⟨N, hN, ?_⟩
  have h := (H.AA0 : Submodule (𝓞 H.E) H.E).smul_mem (⟨N • (x / a), hi⟩ : 𝓞 H.E) ha
  have e : (⟨N • (x / a), hi⟩ : 𝓞 H.E) • a = (N : H.E) * x := by
    change (N • (x / a)) * a = _
    rw [zsmul_eq_mul]
    field_simp
  rw [← e]
  exact h

def lat4 : Submodule (𝓞 H.K) (Fin 4 → H.E) :=
  Submodule.pi Set.univ fun _ => (H.AA0 : Submodule (𝓞 H.E) H.E).restrictScalars (𝓞 H.K)

theorem mem_fourCopiesInvHalfDifferent_iff (x : Fin 4 → H.E) : x ∈ lat4 H ↔ ∀ a, x a ∈ H.AA0 :=
  ⟨fun h a => h a trivial, fun h a _ => h a⟩

theorem fourCopiesInvHalfDifferent_fg : (lat4 H).FG := by
  refine Submodule.fg_pi fun _ => ?_
  have h1 : Module.Finite (𝓞 H.E) (H.AA0 : Submodule (𝓞 H.E) H.E) :=
    Module.Finite.iff_fg.2 (FractionalIdeal.fg_of_isNoetherianRing le_rfl H.AA0)
  have h2 : Module.Finite (𝓞 H.K) (H.AA0 : Submodule (𝓞 H.E) H.E) := Module.Finite.trans (𝓞 H.E) _
  exact Module.Finite.iff_fg.1 h2

theorem fourCopiesInvHalfDifferent_selfDual (x : Fin 4 → H.E) : x ∈ lat4 H ↔ ∀ y ∈ lat4 H,
    ∑ a, Algebra.trace H.K H.E (x a * H.conj (y a)) ∈ (algebraMap (𝓞 H.K) H.K).range := by
  rw [mem_fourCopiesInvHalfDifferent_iff]
  constructor
  · intro h y hy
    exact sum_mem fun a _ => (factMMUnimodular R H _).1 (h a) _ ((mem_fourCopiesInvHalfDifferent_iff H y).1 hy a)
  · intro h a
    refine (factMMUnimodular R H _).2 fun y hy => ?_
    have := h (Pi.single a y) ((mem_fourCopiesInvHalfDifferent_iff H _).2 fun b => by
      by_cases e : b = a
      · subst e
        rwa [Pi.single_eq_same]
      · rw [Pi.single_eq_of_ne e]
        exact (H.AA0 : Submodule (𝓞 H.E) H.E).zero_mem)
    rwa [Finset.sum_eq_single a (fun b _ e => by rw [Pi.single_eq_of_ne e, map_zero, mul_zero, map_zero]) (by simp),
      Pi.single_eq_same] at this

theorem exists_atP (p : ℕ) (hp : p.Prime) (hs : Th.SplitK H p) : ∃ γ : Th.IsoK H (Tau R), Th.AtP γ p := by
  classical
  obtain ⟨γ⟩ := nonempty_isoK H
  obtain ⟨𝔭, α, β, hp𝔭, hα, hβ, hαβ⟩ := GlobalTheory.T.exists_prime_over_split_not_mem_conj R H p hp hs
  have hiso : ∀ x y, ∑ w, γ.g x w * HostK.conjK H (γ.g y w) = ∑ a, Algebra.trace H.K H.E (x a * H.conj (y a)) := fun x y => by
    apply (algebraMap H.K H.E).injective
    rw [← γ.isom, map_sum]
    exact Finset.sum_congr rfl fun w _ => map_mul _ _ _
  let L : Submodule (𝓞 H.K) (Fin 4 × Tau R → H.K) := (lat4 H).map (γ.g.toLinearMap.restrictScalars (𝓞 H.K))
  have hm : ∀ x, γ.g x ∈ L ↔ x ∈ lat4 H := fun x =>
    ⟨fun ⟨y, hy, e⟩ => (γ.g.injective e : y = x) ▸ hy, fun h => ⟨x, h, rfl⟩⟩
  obtain ⟨u, hu, s, hsp, h1, h2⟩ := exists_move H.K (HostK.conjK H) (Fin 4 × Tau R) p 𝔭 α β L (HostK.conjK_conjK H)
    (HostK.exists_norm_int H) hp hp𝔭 hα hβ hαβ ((fourCopiesInvHalfDifferent_fg H).map _)
    (by
      rw [eq_top_iff]
      rintro v -
      obtain ⟨x, rfl⟩ := γ.g.surjective v
      choose N hN hx using fun a => exists_int_mul_mem_invHalfDifferent H (x a)
      have h0 : ((∏ a, N a : ℤ) : H.K) ≠ 0 := Int.cast_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun a _ => hN a)
      rw [← Submodule.smul_mem_iff _ h0, ← γ.g.map_smul]
      refine Submodule.subset_span ((hm _).2 ((mem_fourCopiesInvHalfDifferent_iff H _).2 fun a => ?_))
      have := (H.AA0 : Submodule (𝓞 H.E) H.E).smul_of_tower_mem (∏ b ∈ Finset.univ.erase a, N b) (hx a)
      rw [Pi.smul_apply, Algebra.smul_def, map_intCast, ← Finset.prod_erase_mul _ _ (Finset.mem_univ a), Int.cast_mul, mul_assoc,
        ← zsmul_eq_mul]
      exact this)
    (fun v => by
      obtain ⟨x, rfl⟩ := γ.g.surjective v
      rw [hm, fourCopiesInvHalfDifferent_selfDual]
      constructor
      · rintro h _ ⟨y, hy, rfl⟩
        exact (hiso x y).symm ▸ h y hy
      · intro h y hy
        exact hiso x y ▸ h _ ((hm y).2 hy))
  refine ⟨⟨γ.g.trans u, fun x y => ?_⟩, fun x hx => ⟨s, hsp, h1 _ ((hm x).2 ((mem_fourCopiesInvHalfDifferent_iff H x).2 hx))⟩, fun v hv => ⟨s, hsp, fun a => ?_⟩⟩
  · rw [← hiso, ← hu, map_sum]
    exact Finset.sum_congr rfl fun w _ => (map_mul (algebraMap H.K H.E) (u (γ.g x) w) (HostK.conjK H (u (γ.g y) w))).symm
  · have h3 := h2 v hv
    rw [← γ.g.apply_symm_apply (u.symm v), ← γ.g.map_smul, hm, mem_fourCopiesInvHalfDifferent_iff] at h3
    have h4 := h3 a
    rwa [Pi.smul_apply, Algebra.smul_def, map_natCast] at h4

def conjVec : Set (Tau R → H.E) := {v | ∃ a ∈ H.AA0, v = fun τ : Tau R => H.sigmaOf (τ : R.GG) a}

def ellE (τ : Tau R) : Submodule (𝓞 H.E) H.E :=
  letI : DecidableEq (Tau R) := fun a b => Classical.propDecidable (a = b)
  (Submodule.span (𝓞 H.E) (conjVec H)).comap (LinearMap.single (𝓞 H.E) (fun _ : Tau R => H.E) τ)

theorem ellE_fg (τ : Tau R) : (ellE H τ).FG := by
  letI : DecidableEq (Tau R) := fun a b => Classical.propDecidable (a = b)
  obtain ⟨d, hd, hA⟩ := H.AA0.isFractional
  have hd0 : (d : H.E) ≠ 0 := by exact_mod_cast nonZeroDivisors.ne_zero hd
  let g := H.sigmaOf (τ : R.GG)
  have hg0 : g d ≠ 0 := (map_ne_zero g).2 hd0
  have hle : ellE H τ ≤ Submodule.span (𝓞 H.E) {(g d)⁻¹} := by
    intro s hs
    have h1 : Submodule.span (𝓞 H.E) (conjVec H) ≤
        (Submodule.span (𝓞 H.E) {(g d)⁻¹}).comap (LinearMap.proj (R := 𝓞 H.E) (φ := fun _ : Tau R => H.E) τ) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨a, ha, rfl⟩
      obtain ⟨b, hb⟩ := hA a ha
      refine Submodule.mem_span_singleton.2 ⟨⟨g b, b.isIntegral_coe.map (g : H.E →+* H.E).toIntAlgHom⟩, ?_⟩
      change g (algebraMap _ _ b) * (g d)⁻¹ = g a
      rw [hb, Algebra.smul_def, map_mul]
      change g d * g a * (g d)⁻¹ = g a
      field_simp
    have h2 := h1 hs
    simpa using h2
  exact Submodule.FG.of_le (Submodule.fg_span_singleton _) hle

theorem exists_dgen : ∃ cD, Th.IsDgen H (embT H) cD := by
  obtain ⟨M, hM, hφ, hs⟩ := GlobalTheory.T.exists_finite_extension_capitulation_complex H.E H.φ₀ (Tau R) (ellE H) (ellE_fg H)
  choose s hs using hs
  haveI : NumberField M := ⟨⟩
  letI : Algebra H.E M := (H.φ₀.codRestrict M hφ).toAlgebra
  have hal : ∀ x : H.E, ((algebraMap H.E M x : M) : ℂ) = H.φ₀ x := fun _ => rfl
  refine ⟨fun τ => s τ, M, inferInstance, fun τ x => hφ _, fun τ => ⟨s τ, rfl, ?_⟩⟩
  have hl : ∀ x : H.E, TaylorLogMetric.liftM M (H.φ₀ x) = algebraMap H.E M x := fun x => dif_pos (hφ x)
  have h1 : Th.mmM H (embT H) M =
      Submodule.span (𝓞 M) ((fun (v : Tau R → H.E) (i : Tau R) => algebraMap H.E M (v i)) '' conjVec H) := by
    unfold Th.mmM
    congr 1
    ext v
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨_, ⟨a, ha, rfl⟩, funext fun τ => (hl _).symm⟩
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨a, ha, funext fun τ => (hl _).symm⟩
  have h2 := @GlobalTheory.T.comap_single_span_algebraMap_numberField H.E M _ _ _ _ _ (Tau R) _ (fun a b => Classical.propDecidable (a = b)) (conjVec H) τ
  rw [← hs τ]
  unfold Th.ellT
  rw [h1]
  refine h2.trans ?_
  congr 1
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, e⟩
    exact ⟨x, hx, Subtype.ext e.symm⟩

theorem nonempty_kapIn (γ₀ : Th.IsoK H (Tau R)) : Nonempty (Th.KapIn γ₀) := by
  classical
  have h2 : Th.SplitK H 2 := Or.inl rfl
  have hpp : ∀ p : ℕ, ∃ 𝔭 : HeightOneSpectrum (𝓞 H.K), p.Prime → Th.SplitK H p → (p : 𝓞 H.K) ∈ 𝔭.asIdeal := fun p => by
    by_cases h : p.Prime ∧ Th.SplitK H p
    · obtain ⟨𝔭, -, -, h1, -⟩ := GlobalTheory.T.exists_prime_over_split_not_mem_conj R H p h.1 h.2
      exact ⟨𝔭, fun _ _ => h1⟩
    · obtain ⟨𝔭, -⟩ := GlobalTheory.T.exists_prime_over_split_not_mem_conj R H 2 Nat.prime_two h2
      exact ⟨𝔭, fun a b => absurd ⟨a, b⟩ h⟩
  have hga : ∀ p : ℕ, ∃ γ : Th.IsoK H (Tau R), p.Prime → Th.SplitK H p → Th.AtP γ p := fun p => by
    by_cases h : p.Prime ∧ Th.SplitK H p
    · obtain ⟨γ, h1⟩ := exists_atP H p h.1 h.2
      exact ⟨γ, fun _ _ => h1⟩
    · exact ⟨γ₀, fun a b => absurd ⟨a, b⟩ h⟩
  choose pp hpp using hpp
  choose ga hga using hga
  choose pi hpi using fun p => exists_gen_pow (pp p)
  choose rt hrt using fun p => IsAlgClosed.exists_pow_nat_eq
    (H.φ₀ (((pi p : 𝓞 H.K) : H.K) : H.E) / H.φ₀ (H.conj (((pi p : 𝓞 H.K) : H.K) : H.E)))
    (n := 2 * classNumber H.K) (Nat.mul_pos two_pos (classNumber_pos H.K))
  exact ⟨⟨pp, hpp, pi, fun p _ _ => hpi p, ga, hga, rt, fun p _ _ => hrt p⟩⟩

end AmbEx

theorem exists_ambIn_ok {R : Ranks} (H : Host R) : ∃ J : AmbIn H, J.Ok := by
  obtain ⟨δ, L, ω₀, hδ, hL, ht⟩ := GlobalTheory.T.exists_periodPair_lattice_eq_lamOf R H
  obtain ⟨γ₀⟩ := AmbEx.nonempty_isoK H
  obtain ⟨gC, hgC⟩ := GlobalTheory.T.exists_complexLinear_extension_of_traceIsometry' H.K H.E H.conj (Tau R) H.φ₀ (embT H) (HostK.emb_conj H _) (fun _ => HostK.emb_conj H _)
    (HostK.embT_K H) (HostK.sum_embT H) γ₀
  obtain ⟨kc⟩ := AmbEx.nonempty_kapIn H γ₀
  obtain ⟨cD, hc⟩ := AmbEx.exists_dgen H
  exact ⟨⟨δ, ⟨L, hL, ω₀, ht, γ₀, gC, hgC, kc⟩, cD⟩, hδ, hc⟩

end GlobalTheory.Mem.Col2

end
