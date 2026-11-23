import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.MatchIndOf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHcharPrescribedTrivial
import GroundTheory.GlobalFields.SemilocalAlgebras.LocalDegree

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.L2.Host Formalism.ConjugateSelfDual GroundTheory.Global.SemiLocal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.DelEps.Twist
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace UpperTheory.V.Z.Gam

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem exists_retr : ∃ r : kˣ →* kˣ, (∀ x : kˣ, valuation k (x : k) = 1 → r x = x) ∧
    ∀ H : Subgroup kˣ, IsOpen (H : Set kˣ) → IsOpen (H.comap r : Set kˣ) ∧ Finite (kˣ ⧸ H.comap r) := by
  obtain ⟨p, -, hp⟩ := exists_unit_pow k 1
  let r : kˣ →* kˣ :=
    { toFun := fun x => x * p ^ (-ord k x)
      map_one' := by rw [ord_eq_zero (by simp)]; simp
      map_mul' := fun x y => by rw [ord_mul, neg_add, zpow_add, mul_mul_mul_comm] }
  have hr : ∀ x : kˣ, valuation k (x : k) = 1 → r x = x := fun x hx => by
    change x * p ^ (-ord k x) = x
    rw [ord_eq_zero hx]; simp
  have hrp : r p = 1 := by
    change p * p ^ (-ord k p) = 1
    rw [hp]; simp
  refine ⟨r, hr, fun H hH => ?_⟩
  have ho : IsOpen (H.comap r : Set kˣ) :=
    Subgroup.isOpen_mono (H₁ := H ⊓ filtSub k 0) (fun x hx => by rw [Subgroup.mem_comap, hr x hx.2.1]; exact hx.1)
      (hH.inter (isOpen_filtSub k 0))
  refine ⟨ho, ?_⟩
  haveI : DiscreteTopology (kˣ ⧸ H.comap r) := QuotientGroup.discreteTopology ho
  have hf := ((GroundTheory.LocalField.isCompact_unitFiltrationUnits (K := k) 0).image
    (QuotientGroup.continuous_mk (N := H.comap r))).finite_of_discrete
  refine Set.finite_univ_iff.1 (hf.subset ?_)
  intro g _
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
  refine ⟨g * p ^ (-ord k g), ?_, ?_⟩
  · rw [SetLike.mem_coe, GroundTheory.LocalField.mem_unitFiltrationUnits_zero_iff, ← ord_eq_zero_iff, ord_mul, ord_zpow, hp]
    simp
  · rw [eq_comm, QuotientGroup.eq, inv_mul_cancel_left, Subgroup.mem_comap, map_zpow, hrp, one_zpow]
    exact one_mem _

private theorem exists_fin (θ : kˣ →* ℂˣ) (hθ : IsSmoothChar θ) :
    ∃ χ : kˣ →* ℂˣ, IsSmoothChar χ ∧ (∃ N : ℕ, 0 < N ∧ χ ^ N = 1) ∧ IsUnram (χ * θ⁻¹) := by
  obtain ⟨r, hr, hH⟩ := exists_retr (k := k)
  obtain ⟨ho, hf⟩ := hH θ.ker hθ
  refine ⟨θ.comp r, ho, ⟨Nat.card (kˣ ⧸ θ.ker.comap r), Nat.card_pos, MonoidHom.ext fun x => ?_⟩, fun x hx => ?_⟩
  · rw [MonoidHom.pow_apply, ← map_pow]
    exact Subgroup.pow_index_mem (θ.ker.comap r) x
  · rw [MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.comp_apply, hr x hx, mul_inv_cancel]

private theorem exists_sep (y : kˣ) (hy : valuation k (y : k) = 1) (h1 : y ≠ 1) :
    ∃ χ : kˣ →* ℂˣ, IsSmoothChar χ ∧ (∃ N : ℕ, 0 < N ∧ χ ^ N = 1) ∧ χ y ≠ 1 := by
  obtain ⟨r, hr, hH⟩ := exists_retr (k := k)
  have h0 : valuation k ((y : k) - 1) ≠ 0 := by
    rw [Valuation.ne_zero_iff, sub_ne_zero]
    exact fun h => h1 (Units.ext h)
  obtain ⟨a, ha⟩ : ∃ a : ℕ, uniformizer k ^ a < valuation k ((y : k) - 1) :=
    exists_pow_lt₀ uniformizer_lt_one (Units.mk0 _ h0)
  obtain ⟨ho, hf⟩ := hH _ (isOpen_filtSub k a)
  set H := (filtSub k a).comap r
  have hyH : (QuotientGroup.mk y : kˣ ⧸ H) ≠ 1 := by
    rw [Ne, QuotientGroup.eq_one_iff, Subgroup.mem_comap, hr y hy]
    exact fun h => absurd h.2 (not_le.2 ha)
  obtain ⟨θ, hθ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity (kˣ ⧸ H) ℂ hyH
  refine ⟨θ.comp (QuotientGroup.mk' H), Subgroup.isOpen_mono (fun z hz => ?_) ho,
    ⟨Nat.card (kˣ ⧸ H), Nat.card_pos, MonoidHom.ext fun z => ?_⟩, hθ⟩
  · rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff z).2 hz, map_one]
  · rw [MonoidHom.pow_apply, MonoidHom.comp_apply, ← map_pow, pow_card_eq_one', map_one, MonoidHom.one_apply]

private theorem exists_avoid (x : kˣ) (hx : valuation k (x : k) = 1) (hi : ∀ n : ℕ, 0 < n → x ^ n ≠ 1)
    (F : Finset (ℕ × ℂˣ)) (hF : ∀ p ∈ F, 0 < p.1) :
    ∃ χ : kˣ →* ℂˣ, IsSmoothChar χ ∧ (∃ N : ℕ, 0 < N ∧ χ ^ N = 1) ∧ ∀ p ∈ F, p.2 * χ x ^ p.1 ≠ 1 := by
  have hM : 0 < ∏ p ∈ F, p.1 * max (orderOf p.2) 1 :=
    Finset.prod_pos fun p hp => Nat.mul_pos (hF p hp) (by omega)
  obtain ⟨χ, h1, ⟨N, hN, h2⟩, h3⟩ := exists_sep _ (by rw [Units.val_pow_eq_pow_val, map_pow, hx, one_pow]) (hi _ hM)
  refine ⟨χ, h1, ⟨N, hN, h2⟩, fun p hp h => h3 ?_⟩
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun p : ℕ × ℂˣ => p.1 * max (orderOf p.2) 1) hp
  have hN1 : χ x ^ N = 1 := by rw [← MonoidHom.pow_apply, h2, MonoidHom.one_apply]
  have e : χ x ^ p.1 = p.2⁻¹ := eq_inv_of_mul_eq_one_right h
  have hfin : IsOfFinOrder p.2 := by
    rw [← isOfFinOrder_inv_iff, ← e]
    exact (isOfFinOrder_iff_pow_eq_one.2 ⟨N, hN, hN1⟩).pow
  have hpos := hfin.orderOf_pos
  rw [hc, map_pow, max_eq_left (by omega), pow_mul, pow_mul, e, inv_pow, pow_orderOf_eq_one, inv_one, one_pow]

end Loc

private theorem val_one_iff {K : Type} [Field K] [NumberField K] (u : HeightOneSpectrum (𝓞 K)) (x : u.adicCompletion K) :
    valuation (u.adicCompletion K) x = 1 ↔ Valued.v x = 1 := by
  haveI : (Valued.v : Valuation (u.adicCompletion K) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (valuation (u.adicCompletion K)) Valued.v).eq_one_iff_eq_one

private theorem exists_at {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (u : HeightOneSpectrum (𝓞 K)) (bad : Finset ((u.adicCompletion K)ˣ →* ℂˣ))
    (bad' : ∀ w : HeightOneSpectrum (𝓞 L), Finset ((w.adicCompletion L)ˣ →* ℂˣ)) :
    ∃ χ : (u.adicCompletion K)ˣ →* ℂˣ, IsSmoothChar χ ∧ (∃ N : ℕ, 0 < N ∧ χ ^ N = 1) ∧
      (∀ ξ ∈ bad, ¬ IsUnram (ξ * χ)) ∧ ∀ w : PlacesOver L u, ∀ ζ ∈ bad' w.1, ¬ IsUnram (ζ * χ.comp (nm w)) := by
  haveI : CharZero (u.adicCompletion K) := charZero_of_injective_ringHom (algebraMap K (u.adicCompletion K)).injective
  obtain ⟨m, hm, hmu⟩ : ∃ m : ℕ, 0 < m ∧ ((m : ℕ) : 𝓞 K) ∈ u.asIdeal :=
    ⟨_, (GlobalTheory.LocalData.resChar_prime u).pos, GlobalTheory.LocalData.resChar_mem u⟩
  have hv : Valued.v (((1 + m : ℕ) : u.adicCompletion K)) = 1 := by
    have := (valued_algebraMap_int_lt_one_iff u _).2 hmu
    rw [map_natCast] at this
    rw [Nat.cast_add, Nat.cast_one]
    exact Valuation.map_one_add_of_lt _ this
  let x : (u.adicCompletion K)ˣ := Units.mk0 ((1 + m : ℕ) : u.adicCompletion K) (Nat.cast_ne_zero.2 (by omega))
  let ι : ∀ w : PlacesOver L u, (w.1.adicCompletion L)ˣ := fun w =>
    Units.map (algebraMap (u.adicCompletion K) (w.1.adicCompletion L) : u.adicCompletion K →* w.1.adicCompletion L) x
  let d : PlacesOver L u → ℕ := fun w => Module.finrank (u.adicCompletion K) (w.1.adicCompletion L)
  have hd : ∀ w, 0 < d w := fun w =>
    lt_of_lt_of_le (Nat.mul_pos (Ideal.ramificationIdx_pos _ _) (Ideal.inertiaDeg_pos _ _))
      (ramificationIdx_mul_inertiaDeg_le_finrank u w.1)
  have hι : ∀ w, valuation _ (ι w : w.1.adicCompletion L) = 1 := fun w => by
    rw [val_one_iff]
    change Valued.v (completionMap u w.1 ((1 + m : ℕ) : u.adicCompletion K)) = 1
    rw [valued_completionMap, hv, one_pow]
  have hn : ∀ w, nm w (ι w) = x ^ d w := fun w => Units.ext (Algebra.norm_algebraMap _)
  have hx : valuation _ (x : u.adicCompletion K) = 1 := (val_one_iff u _).2 hv
  obtain ⟨χ, h1, h2, h3⟩ := exists_avoid x hx
    (fun n hn h => by
      have h' : ((1 + m : ℕ) : u.adicCompletion K) ^ n = 1 := congrArg Units.val h
      have h'' : (1 + m) ^ n = 1 := by exact_mod_cast h'
      exact absurd h'' (Nat.one_lt_pow hn.ne' (by omega)).ne')
    (bad.image (fun ξ => (1, ξ x)) ∪ Finset.univ.biUnion fun w : PlacesOver L u => (bad' w.1).image fun ζ => (d w, ζ (ι w)))
    (fun p hp => by
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_biUnion] at hp
      rcases hp with ⟨_, -, rfl⟩ | ⟨w, -, _, -, rfl⟩
      · exact one_pos
      · exact hd w)
  refine ⟨χ, h1, h2, fun ξ hξ h => h3 (1, ξ x) (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hξ)) ?_,
    fun w ζ hζ h => h3 (d w, ζ (ι w)) (Finset.mem_union_right _
      (Finset.mem_biUnion.2 ⟨w, Finset.mem_univ _, Finset.mem_image_of_mem _ hζ⟩)) ?_⟩
  · simpa using h x hx
  · have := h (ι w) (hι w)
    rwa [MonoidHom.mul_apply, MonoidHom.comp_apply, hn, map_pow] at this

theorem globTw : GlobTw := by
  intro K L _ _ _ _ _ v θ hθ S bad bad'
  obtain ⟨θ', a1, a2, a3⟩ := exists_fin θ hθ
  choose c c1 c2 c3 using fun u : HeightOneSpectrum (𝓞 K) => exists_at u (bad u) bad'
  obtain ⟨η, -, -, h⟩ := exists_hchar_prescribed K (insert v S) (Function.update c v θ')
    (fun w _ => by
      by_cases e : w = v
      · subst e; rwa [Function.update_self]
      · rw [Function.update_of_ne e]; exact c1 w)
    (fun w _ => by
      by_cases e : w = v
      · subst e; rwa [Function.update_self]
      · rw [Function.update_of_ne e]; exact c2 w)
  refine ⟨η, by rwa [h v (Finset.mem_insert_self _ _), Function.update_self], fun u hu e => ?_⟩
  rw [h u (Finset.mem_insert_of_mem hu), Function.update_of_ne e]
  exact c3 u

end UpperTheory.V.Z.Gam
