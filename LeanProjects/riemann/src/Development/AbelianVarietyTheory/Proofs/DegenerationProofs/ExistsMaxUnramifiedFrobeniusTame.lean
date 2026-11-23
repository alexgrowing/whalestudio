import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFiniteEtaleLocalSurjectiveOfIsSeparable
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteAlgebrasOverHenselianAndComplete
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CompositumFiniteNormalIsPGroup
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KummerTwistRelationAndFixedField
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsArithFrobeniusAbsGalois
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GaloisOfPrimePowerDegree

namespace GlobalTheory.SS.MaxUnr
open IsLocalRing Polynomial

theorem pow_pow_mul_eq {M : Type*} [Monoid M] {q f : ℕ} {x : M} (h : x ^ q ^ f = x) (g : ℕ) :
    x ^ q ^ (f * g) = x := by
  induction g with
  | zero => simp
  | succ g ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, h]

def Teich (q : ℕ) (S : Type*) [Monoid S] : Set S := {t | ∃ f, 1 ≤ f ∧ t ^ q ^ f = t}

section
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

theorem one_lt_card [Finite (ResidueField V)] : 1 < Nat.card (ResidueField V) :=
  Finite.one_lt_card

theorem isIntegral_of_teich {q : ℕ} (hq : 1 < q) {S : Type*} [CommRing S] [Algebra V S] {t : S}
    (ht : t ∈ Teich q S) : IsIntegral V t := by
  obtain ⟨f, hf, h⟩ := ht
  refine ⟨X ^ q ^ f - X, monic_X_pow_sub ?_, by simp [h]⟩
  refine lt_of_le_of_lt degree_X_le ?_
  exact_mod_cast Nat.one_lt_pow (by omega) hq

theorem isLocalRing_of_isIntegral [IsAdicComplete (maximalIdeal V) V] (S : Type*) [CommRing S]
    [IsDomain S] [Algebra V S] [Algebra.IsIntegral V S] : IsLocalRing S := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  have : Module.Finite V (Algebra.adjoin V {a}) :=
    Algebra.finite_adjoin_simple_of_isIntegral (Algebra.IsIntegral.isIntegral a)
  have := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isLocalRing_finite_domain (R := V) (Algebra.adjoin V {a})
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self
    (⟨a, Algebra.self_mem_adjoin_singleton V a⟩ : Algebra.adjoin V {a}) with h | h
  · exact Or.inl (h.map (Algebra.adjoin V {a}).val)
  · exact Or.inr (by simpa using h.map (Algebra.adjoin V {a}).val)

theorem isLocalHom_of_injective {S S' : Type*} [CommRing S] [CommRing S'] [Algebra V S] [Algebra V S']
    [Algebra.IsIntegral V S'] (g : S →ₐ[V] S') (hg : Function.Injective g) :
    IsLocalHom g.toRingHom := by
  refine RingHom.IsIntegral.isLocalHom (fun x => ?_) hg
  let := g.toRingHom.toAlgebra
  have : IsScalarTower V S S' := .of_algebraMap_eq fun v => (g.commutes v).symm
  exact (Algebra.IsIntegral.isIntegral (R := V) x).tower_top (A := S)

theorem exists_prime [Finite (ResidueField V)] : ∃ p n : ℕ, p.Prime ∧ (p : V) ∈ maximalIdeal V ∧
    Nat.card (ResidueField V) = p ^ n := by
  have := Fintype.ofFinite (ResidueField V)
  obtain ⟨p, hp, n, hp', h⟩ := FiniteField.card' (ResidueField V)
  refine ⟨p, n, hp', ?_, by rw [Nat.card_eq_fintype_card, h]⟩
  rw [← residue_eq_zero_iff, map_natCast, CharP.cast_eq_zero]

theorem pow_card_sub_mem [Finite (ResidueField V)] (v : V) :
    v ^ Nat.card (ResidueField V) - v ∈ maximalIdeal V := by
  have := Fintype.ofFinite (ResidueField V)
  rw [← residue_eq_zero_iff, map_sub, map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card, sub_self]

theorem teich_of_mem_adjoin [Finite (ResidueField V)] {Q : Type*} [CommRing Q] [Algebra V Q]
    (h0 : ∀ v ∈ maximalIdeal V, algebraMap V Q v = 0) {x : Q}
    (hx : x ∈ Algebra.adjoin V (Teich (Nat.card (ResidueField V)) Q)) :
    x ∈ Teich (Nat.card (ResidueField V)) Q := by
  rcases subsingleton_or_nontrivial Q with _ | _
  · exact ⟨1, le_rfl, Subsingleton.elim _ _⟩
  obtain ⟨p, n, hp, hpm, hq⟩ := exists_prime (V := V)
  have := Fact.mk hp
  have : CharP Q p := (CharP.charP_iff_prime_eq_zero hp).2 (by simpa using h0 _ hpm)
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact hx
  | algebraMap v =>
    refine ⟨1, le_rfl, ?_⟩
    have := h0 _ (pow_card_sub_mem v)
    rw [map_sub, map_pow, sub_eq_zero] at this
    rw [pow_one, this]
  | add x y _ _ hx hy =>
    obtain ⟨f, hf, hx⟩ := hx
    obtain ⟨g, hg, hy⟩ := hy
    refine ⟨f * g, Nat.mul_pos hf hg, ?_⟩
    have h1 := pow_pow_mul_eq hx g
    have h2 := pow_pow_mul_eq hy f
    rw [mul_comm] at h2
    rw [hq, ← pow_mul] at h1 h2 ⊢
    rw [add_pow_char_pow, h1, h2]
  | mul x y _ _ hx hy =>
    obtain ⟨f, hf, hx⟩ := hx
    obtain ⟨g, hg, hy⟩ := hy
    refine ⟨f * g, Nat.mul_pos hf hg, ?_⟩
    have h2 := pow_pow_mul_eq hy f
    rw [mul_comm] at h2
    rw [mul_pow, pow_pow_mul_eq hx g, h2]

theorem isIntegral_of_gen [Finite (ResidueField V)] {S : Type*} [CommRing S] [Algebra V S]
    (hS : Algebra.adjoin V (Teich (Nat.card (ResidueField V)) S) = ⊤) : Algebra.IsIntegral V S := by
  refine ⟨fun x => ?_⟩
  have : Algebra.adjoin V (Teich (Nat.card (ResidueField V)) S) ≤ integralClosure V S :=
    Algebra.adjoin_le fun t ht => isIntegral_of_teich one_lt_card ht
  exact this (hS ▸ Algebra.mem_top)

theorem teich_quot_of_gen [Finite (ResidueField V)] {S : Type*} [CommRing S] [Algebra V S]
    (hS : Algebra.adjoin V (Teich (Nat.card (ResidueField V)) S) = ⊤) (I : Ideal S)
    (hI : (maximalIdeal V).map (algebraMap V S) ≤ I) (x : S ⧸ I) :
    x ∈ Teich (Nat.card (ResidueField V)) (S ⧸ I) := by
  refine teich_of_mem_adjoin (fun v hv => ?_) ?_
  · exact Ideal.Quotient.eq_zero_iff_mem.2 (hI (Ideal.mem_map_of_mem _ hv))
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hx : x ∈ Algebra.adjoin V (Teich (Nat.card (ResidueField V)) S) := hS ▸ Algebra.mem_top
  have h2 := Subalgebra.mem_map.2 ⟨x, hx, (rfl : Ideal.Quotient.mkₐ V I x = _)⟩
  rw [AlgHom.map_adjoin] at h2
  refine Algebra.adjoin_mono ?_ h2
  rintro _ ⟨t, ⟨f, hf, ht⟩, rfl⟩
  exact ⟨f, hf, by rw [← map_pow, ht]⟩

theorem maximalIdeal_of_gen [Finite (ResidueField V)] {S : Type*} [CommRing S] [Algebra V S]
    [IsLocalRing S] [IsLocalHom (algebraMap V S)]
    (hS : Algebra.adjoin V (Teich (Nat.card (ResidueField V)) S) = ⊤) :
    (maximalIdeal V).map (algebraMap V S) = maximalIdeal S := by
  refine le_antisymm (Ideal.map_le_iff_le_comap.2 fun v hv => map_nonunit _ v hv) fun x hx => ?_
  obtain ⟨f, hf, h⟩ := teich_quot_of_gen hS _ le_rfl (Ideal.Quotient.mk _ x)
  rw [← map_pow, Ideal.Quotient.eq] at h
  obtain ⟨N, hN⟩ : ∃ N, Nat.card (ResidueField V) ^ f = N + 2 :=
    Nat.exists_eq_add_of_le' (Nat.one_lt_pow (by omega) one_lt_card)
  have hu : IsUnit (1 - x ^ (N + 1)) :=
    isUnit_one_sub_self_of_mem_nonunits _ (Ideal.pow_mem_of_mem (maximalIdeal S) hx _ (by omega))
  rw [← Ideal.unit_mul_mem_iff_mem _ hu]
  have e : (1 - x ^ (N + 1)) * x = -(x ^ (N + 2) - x) := by ring
  rw [e, ← hN]
  exact neg_mem h

theorem gen_adjoin {q : ℕ} {S : Type*} [CommRing S] [Algebra V S] {T : Set S} (hT : T ⊆ Teich q S) :
    Algebra.adjoin V (Teich q (Algebra.adjoin V T)) = ⊤ := by
  rw [eq_top_iff, ← Algebra.adjoin_adjoin_coe_preimage (R := V) (s := T)]
  refine Algebra.adjoin_mono fun t ht => ?_
  obtain ⟨f, hf, h⟩ := hT ht
  exact ⟨f, hf, Subtype.ext h⟩

theorem dvr_of_gen [Finite (ResidueField V)] {S : Type*} [CommRing S] [IsDomain S] [Algebra V S]
    [FaithfulSMul V S] [IsLocalRing S] [Module.Finite V S]
    (hS : Algebra.adjoin V (Teich (Nat.card (ResidueField V)) S) = ⊤) :
    IsDiscreteValuationRing S := by
  have : IsLocalHom (algebraMap V S) :=
    isLocalHom_of_injective (Algebra.ofId V S) (FaithfulSMul.algebraMap_injective V S)
  have : IsNoetherianRing S := IsNoetherianRing.of_finite V S
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hm := maximalIdeal_of_gen hS
  rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton] at hm
  have hnf : ¬ IsField S := by
    rw [isField_iff_maximalIdeal_eq, ← hm, Ideal.span_singleton_eq_bot, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective V S)]
    exact hπ.ne_zero
  exact ((IsDiscreteValuationRing.TFAE S hnf).out 0 4).2 (show (maximalIdeal S).IsPrincipal from ⟨⟨_, hm.symm⟩⟩)
end

section
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  [IsAdicComplete (maximalIdeal V) V] [Finite (ResidueField V)]

omit [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [Finite (ResidueField V)] in
theorem exists_level {q : ℕ} {S : Type*} [CommRing S] [Algebra V S] {x : S}
    (hx : x ∈ Algebra.adjoin V (Teich q S)) :
    ∃ f, 1 ≤ f ∧ ∀ g, x ∈ Algebra.adjoin V {t : S | t ^ q ^ (f * g) = t} := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨f, hf, h⟩ := hx
    exact ⟨f, hf, fun g => Algebra.subset_adjoin (pow_pow_mul_eq h g)⟩
  | algebraMap v => exact ⟨1, le_rfl, fun g => Subalgebra.algebraMap_mem _ v⟩
  | add x y _ _ hx hy =>
    obtain ⟨f, hf, hx⟩ := hx
    obtain ⟨g, hg, hy⟩ := hy
    refine ⟨f * g, Nat.mul_pos hf hg, fun k => add_mem ?_ ?_⟩
    · rw [mul_assoc]; exact hx _
    · rw [mul_comm f g, mul_assoc]; exact hy _
  | mul x y _ _ hx hy =>
    obtain ⟨f, hf, hx⟩ := hx
    obtain ⟨g, hg, hy⟩ := hy
    refine ⟨f * g, Nat.mul_pos hf hg, fun k => mul_mem ?_ ?_⟩
    · rw [mul_assoc]; exact hx _
    · rw [mul_comm f g, mul_assoc]; exact hy _

theorem exists_stage {S : Type} [CommRing S] [IsDomain S] [Algebra V S] [FaithfulSMul V S]
    (hS : Algebra.adjoin V (Teich (Nat.card (ResidueField V)) S) = ⊤) (s : Finset S) :
    ∃ (W : Subalgebra V S) (_ : IsDiscreteValuationRing W), (↑s : Set S) ⊆ W ∧
      IsAdicComplete (maximalIdeal W) W ∧ Module.Finite V W ∧ IsLocalHom W.val.toRingHom ∧
      (maximalIdeal V).map (algebraMap V W) = maximalIdeal W ∧
      ∃ f, 1 ≤ f ∧ W = Algebra.adjoin V {t : S | t ^ Nat.card (ResidueField V) ^ f = t} := by
  classical
  set q := Nat.card (ResidueField V) with hq
  have hI := isIntegral_of_gen hS
  choose F hF hF' using fun x : S => exists_level (V := V) (q := q) (x := x) (hS ▸ Algebra.mem_top)
  have hf : 1 ≤ ∏ x ∈ s, F x := Finset.one_le_prod' fun x _ => hF x
  set f := ∏ x ∈ s, F x with hfdef
  have hT : {t : S | t ^ q ^ f = t} ⊆ Teich q S := fun t ht => ⟨f, hf, ht⟩
  have hfin : {t : S | t ^ q ^ f = t}.Finite := by
    have hm : (X ^ q ^ f - X : S[X]).Monic := by
      refine monic_X_pow_sub (lt_of_le_of_lt degree_X_le ?_)
      exact_mod_cast Nat.one_lt_pow (by omega) (one_lt_card (V := V))
    refine (X ^ q ^ f - X : S[X]).roots.finite_toSet.subset fun t ht => ?_
    have ht' : t ^ q ^ f = t := ht
    simp [mem_roots hm.ne_zero, ht']
  set W := Algebra.adjoin V {t : S | t ^ q ^ f = t} with hW
  have hWfin : Module.Finite V W :=
    Algebra.finite_adjoin_of_finite_of_isIntegral hfin fun x _ => Algebra.IsIntegral.isIntegral x
  have hloc : IsLocalRing W := isLocalRing_of_isIntegral (V := V) W
  have hg : Algebra.adjoin V (Teich q W) = ⊤ := gen_adjoin hT
  have hfa : FaithfulSMul V W := (faithfulSMul_iff_algebraMap_injective V W).2 fun a b h =>
    FaithfulSMul.algebraMap_injective V S (congrArg Subtype.val h)
  have : IsLocalHom (algebraMap V W) :=
    isLocalHom_of_injective (Algebra.ofId V W) (FaithfulSMul.algebraMap_injective V W)
  have hm := maximalIdeal_of_gen hg
  have hc := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isAdicComplete_finite_algebra (R := V) W
  rw [hm] at hc
  refine ⟨W, dvr_of_gen hg, fun x hx => ?_, hc, hWfin,
    isLocalHom_of_injective W.val Subtype.val_injective, hm, f, hf, rfl⟩
  obtain ⟨g, hg⟩ : F x ∣ f := Finset.dvd_prod_of_mem F hx
  rw [hW, hg]
  exact hF' x g

theorem irreducible_of_gen {S : Type} [CommRing S] [IsDomain S] [Algebra V S] [FaithfulSMul V S]
    (hS : Algebra.adjoin V (Teich (Nat.card (ResidueField V)) S) = ⊤) {π : V} (hπ : Irreducible π) :
    Irreducible (algebraMap V S π) := by
  have hI := isIntegral_of_gen hS
  have hloc : IsLocalRing S := isLocalRing_of_isIntegral (V := V) S
  have : IsLocalHom (algebraMap V S) :=
    isLocalHom_of_injective (Algebra.ofId V S) (FaithfulSMul.algebraMap_injective V S)
  have hm := maximalIdeal_of_gen hS
  rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton] at hm
  have h0 : algebraMap V S π ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective V S)]
    exact hπ.ne_zero
  refine Prime.irreducible ((Ideal.span_singleton_prime h0).1 ?_)
  rw [hm]; infer_instance

theorem dvr_of_gen' {S : Type} [CommRing S] [IsDomain S] [Algebra V S] [FaithfulSMul V S]
    (hS : Algebra.adjoin V (Teich (Nat.card (ResidueField V)) S) = ⊤) :
    IsDiscreteValuationRing S := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible V
  refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨_, irreducible_of_gen hS hπ, fun {x} hx => ?_⟩
  obtain ⟨W, _, hs, -, -, -, hm, -⟩ := exists_stage hS {x}
  have hxW : x ∈ W := hs (by simp)
  rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton] at hm
  have hi : Irreducible (algebraMap V W π) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 hm.symm
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible (x := (⟨x, hxW⟩ : W))
    (fun h => hx (congrArg Subtype.val h)) hi
  exact ⟨n, by simpa using (hn.map W.val).symm⟩

theorem henselian_of_gen {S : Type} [CommRing S] [IsDomain S] [Algebra V S] [FaithfulSMul V S]
    (hS : Algebra.adjoin V (Teich (Nat.card (ResidueField V)) S) = ⊤) :
    HenselianLocalRing S := by
  classical
  have hI := isIntegral_of_gen hS
  have hloc : IsLocalRing S := isLocalRing_of_isIntegral (V := V) S
  refine ⟨fun P hP a h1 h2 => ?_⟩
  obtain ⟨W, _, hs, hc, -, hl, -⟩ := exists_stage hS (insert a P.coeffs)
  have haW : a ∈ W := hs (by simp)
  have hH := GlobalTheory.henselianLocalRing_of_isAdicComplete W
  have hlift : P ∈ lifts W.val.toRingHom := by
    rw [lifts_iff_coeff_lifts]
    intro n
    by_cases h : P.coeff n = 0
    · exact ⟨0, by simp [h]⟩
    · exact ⟨⟨P.coeff n, hs (by simp [coeff_mem_coeffs h])⟩, rfl⟩
  obtain ⟨P', rfl, -, hP'⟩ := lifts_and_natDegree_eq_and_monic hlift hP
  have e : ∀ Q : W[X], (Q.map W.val.toRingHom).eval a = W.val.toRingHom (Q.eval ⟨a, haW⟩) := fun Q =>
    eval_map_apply (p := Q) W.val.toRingHom ⟨a, haW⟩
  rw [derivative_map, e] at h2
  rw [e] at h1
  obtain ⟨b, hb, hb'⟩ := HenselianLocalRing.is_henselian P' hP' ⟨a, haW⟩
    (fun h => h1 (h.map _)) (isUnit_of_map_unit _ _ h2)
  exact ⟨b, hb.map (f := W.val.toRingHom), map_nonunit W.val.toRingHom _ hb'⟩
end

section
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Finite (ResidueField V)]

theorem teich_inj {S : Type*} [CommRing S] [IsLocalRing S] [Algebra V S] [IsLocalHom (algebraMap V S)]
    {t u : S} (ht : t ∈ Teich (Nat.card (ResidueField V)) S)
    (hu : u ∈ Teich (Nat.card (ResidueField V)) S) (h : t - u ∈ maximalIdeal S) : t = u := by
  obtain ⟨f, hf, ht⟩ := ht
  obtain ⟨g, hg, hu⟩ := hu
  have h1 := pow_pow_mul_eq ht g
  have h2 := pow_pow_mul_eq hu f
  rw [mul_comm] at h2
  obtain ⟨p, n, hp, hpm, hq⟩ := exists_prime (V := V)
  have hN : ((Nat.card (ResidueField V) ^ (f * g) : ℕ) : ResidueField S) = 0 := by
    have hp0 : (p : ResidueField S) = 0 := by
      have : residue S (algebraMap V S p) = 0 := (residue_eq_zero_iff _).2 (map_nonunit _ _ hpm)
      simpa using this
    have hn : n ≠ 0 := by
      rintro rfl
      have := one_lt_card (V := V)
      simp [hq] at this
    have := Nat.mul_pos hf hg
    rw [hq, ← pow_mul, Nat.cast_pow, hp0, zero_pow (by positivity)]
  generalize Nat.card (ResidueField V) ^ (f * g) = N at h1 h2 hN
  have h3 := geom_sum₂_mul t u N
  rw [h1, h2] at h3
  have h4 : (∑ i ∈ Finset.range N, t ^ i * u ^ (N - 1 - i)) ∈ maximalIdeal S := by
    have h5 : residue S t = residue S u := by
      rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]; exact h
    rw [← residue_eq_zero_iff, map_sum]
    simp only [map_mul, map_pow, h5]
    rw [geom_sum₂_self, hN, zero_mul]
  have h6 := isUnit_one_sub_self_of_mem_nonunits _ h4
  rw [← sub_eq_zero, ← h6.mul_right_eq_zero, sub_mul, h3, one_mul, sub_self]

theorem residue_teich {S : Type*} [CommRing S] [IsLocalRing S] [Algebra V S]
    [IsLocalHom (algebraMap V S)] [Algebra.IsIntegral V S] (a : S) :
    ∃ f, 1 ≤ f ∧ a ^ Nat.card (ResidueField V) ^ f - a ∈ maximalIdeal S := by
  have hc : IsIntegral (ResidueField V) (residue S a) := by
    have : IsIntegral V (residue S a) :=
      (Algebra.IsIntegral.isIntegral (R := V) a).map (IsScalarTower.toAlgHom V S (ResidueField S))
    exact this.tower_top
  let F := IntermediateField.adjoin (ResidueField V) {residue S a}
  have : FiniteDimensional (ResidueField V) F := IntermediateField.adjoin.finiteDimensional hc
  have : Finite F := Module.finite_of_finite (ResidueField V)
  have := Fintype.ofFinite F
  refine ⟨Module.finrank (ResidueField V) F, Module.finrank_pos, ?_⟩
  have h := FiniteField.pow_card (⟨_, IntermediateField.mem_adjoin_simple_self _ _⟩ : F)
  rw [← Nat.card_eq_fintype_card, Module.natCard_eq_pow_finrank (K := ResidueField V)] at h
  rw [← residue_eq_zero_iff, map_sub, map_pow, sub_eq_zero]
  exact congrArg Subtype.val h

variable {Ω : Type} [Field Ω] [IsAlgClosed Ω] [Algebra V Ω] [FaithfulSMul V Ω]

omit [IsDomain V] [IsDiscreteValuationRing V] [Finite (ResidueField V)] [IsAlgClosed Ω] in
theorem faithful_sub (R : Subalgebra V Ω) : FaithfulSMul V R :=
  (faithfulSMul_iff_algebraMap_injective V R).2 fun _ _ h =>
    FaithfulSMul.algebraMap_injective V Ω (congrArg Subtype.val h)

theorem exists_teich [IsLocalRing (integralClosure V Ω)] (a : integralClosure V Ω) :
    ∃ t ∈ Teich (Nat.card (ResidueField V)) (integralClosure V Ω),
      a - t ∈ maximalIdeal (integralClosure V Ω) := by
  have := faithful_sub (integralClosure V Ω)
  have : IsLocalHom (algebraMap V (integralClosure V Ω)) :=
    isLocalHom_of_injective (Algebra.ofId V _) (FaithfulSMul.algebraMap_injective V _)
  obtain ⟨f, hf, h⟩ := residue_teich (V := V) a
  set q := Nat.card (ResidueField V) with hq
  have hm : (X ^ q ^ f - X : (integralClosure V Ω)[X]).Monic := by
    refine monic_X_pow_sub (lt_of_le_of_lt degree_X_le ?_)
    exact_mod_cast Nat.one_lt_pow (by omega) (one_lt_card (V := V))
  have hs : (X ^ q ^ f - X : (integralClosure V Ω)[X]).Splits := by
    refine Polynomial.Splits.of_splits_map_of_injective (i := (integralClosure V Ω).val.toRingHom)
      Subtype.val_injective (IsAlgClosed.splits _) fun b hb => ?_
    have hb' := isRoot_of_mem_roots hb
    have : b ∈ Teich q Ω := ⟨f, hf, by simpa [sub_eq_zero] using hb'⟩
    exact ⟨⟨b, isIntegral_of_teich one_lt_card this⟩, rfl⟩
  have h1 : (X ^ q ^ f - X : (integralClosure V Ω)[X]).eval a ∈ maximalIdeal (integralClosure V Ω) := by
    simpa using h
  rw [hs.eval_eq_prod_roots_of_monic hm] at h1
  obtain ⟨c, hc, hcm⟩ := (Ideal.IsPrime.multiset_prod_mem_iff_exists_mem inferInstance _).1 h1
  obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.1 hc
  exact ⟨t, ⟨f, hf, by simpa [sub_eq_zero] using isRoot_of_mem_roots ht⟩, hcm⟩

theorem isAlgClosed_residue [IsLocalRing (integralClosure V Ω)]
    [IsLocalRing (Algebra.adjoin V (Teich (Nat.card (ResidueField V)) Ω))] :
    IsAlgClosed (ResidueField (Algebra.adjoin V (Teich (Nat.card (ResidueField V)) Ω))) := by
  set R := Algebra.adjoin V (Teich (Nat.card (ResidueField V)) Ω) with hR
  have hRI : Algebra.IsIntegral V R := isIntegral_of_gen (gen_adjoin subset_rfl)
  have hle : R ≤ integralClosure V Ω := Algebra.adjoin_le fun t ht => isIntegral_of_teich one_lt_card ht
  refine IsAlgClosed.of_exists_root _ fun p hp hi => ?_
  obtain ⟨P, hP, hd, hPm⟩ := lifts_and_natDegree_eq_and_monic (f := residue R)
    (p := p) (map_surjective _ residue_surjective _) hp
  have hdeg : P.degree ≠ 0 := by
    have := hi.natDegree_pos
    exact (natDegree_pos_iff_degree_pos.1 (by omega)).ne'
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_aeval_eq_zero_of_injective Ω (R := R) Subtype.val_injective P hdeg
  have hαi : IsIntegral V α := isIntegral_trans (A := R) α ⟨P, hPm, hα⟩
  obtain ⟨t, ⟨f, hf, ht⟩, hαt⟩ := exists_teich (⟨α, hαi⟩ : integralClosure V Ω)
  let t' : R := ⟨t, Algebra.subset_adjoin ⟨f, hf, congrArg Subtype.val ht⟩⟩
  let ι : R →+* integralClosure V Ω := (Subalgebra.inclusion hle).toRingHom
  refine ⟨residue R t', ?_⟩
  rw [← hP, eval_map_apply, residue_eq_zero_iff]
  have h0 : (P.map ι).eval ⟨α, hαi⟩ = 0 := by
    apply Subtype.val_injective
    have := eval_map_apply (p := P.map ι) (integralClosure V Ω).val.toRingHom ⟨α, hαi⟩
    refine this.symm.trans ?_
    rw [Polynomial.map_map, eval_map]
    exact hα
  have h1 := Ideal.mem_of_dvd _ (sub_dvd_eval_sub _ _ (P.map ι)) hαt
  rw [h0, zero_sub, neg_mem_iff, show t = ι t' from rfl, eval_map_apply] at h1
  exact fun hu => h1 (hu.map ι)
end

theorem exists_fractionField {V : Type} (K : Type) {Ω : Type} (R : Type) [CommRing V] [IsDomain V] [Field K] [Algebra V K] [IsFractionRing V K]
    [Field Ω] [Algebra K Ω] [Algebra V Ω] [IsScalarTower V K Ω] [CommRing R] [IsDomain R] [Algebra V R]
    [Algebra R Ω] [IsScalarTower V R Ω] [FaithfulSMul V R] [FaithfulSMul R Ω] :
    ∃ (F : Type) (_ : Field F) (_ : Algebra R F) (_ : IsFractionRing R F) (_ : Algebra F Ω)
      (_ : Algebra K F), IsScalarTower R F Ω ∧ IsScalarTower K F Ω := by
  let F := FractionRing R
  let _ : Algebra F Ω := FractionRing.liftAlgebra R Ω
  have : IsScalarTower R F Ω := FractionRing.isScalarTower_liftAlgebra R Ω
  have hinj : Function.Injective ((algebraMap R F).comp (algebraMap V R)) :=
    (IsFractionRing.injective R F).comp (FaithfulSMul.algebraMap_injective V R)
  let _ : Algebra K F := (IsFractionRing.lift hinj).toAlgebra
  refine ⟨F, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, this, ?_⟩
  refine .of_algebraMap_eq' (IsFractionRing.ringHom_ext (A := V) fun v => ?_)
  have e : algebraMap K F (algebraMap V K v) = algebraMap R F (algebraMap V R v) :=
    IsFractionRing.lift_algebraMap hinj v
  rw [RingHom.comp_apply, e, ← IsScalarTower.algebraMap_apply R F Ω,
    ← IsScalarTower.algebraMap_apply V K Ω, ← IsScalarTower.algebraMap_apply V R Ω]

open GlobalTheory.SS in
theorem main_of (hT : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [CharZero K] [Algebra R K], SH R K → ∀ (π : R), Irreducible π → ∀ (l : ℕ), l.Prime → IsUnit (l : R) → ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω], (∀ L : IntermediateField K Ω, FiniteDimensional K L → Normal K L → IsPGroup l (L ≃ₐ[K] L) → ∃ (m : ℕ) (ρ : Ω), ρ ^ l ^ m = algebraMap K Ω (algebraMap R K π) ∧ L ≤ IntermediateField.adjoin K {ρ}) ∧ (∀ (m : ℕ) (ζ : Ω), ζ ^ l ^ m = 1 → ζ ∈ Set.range (algebraMap K Ω)) ∧ ∃ σ : Ω ≃ₐ[K] Ω, ∀ (m : ℕ) (ρ : Ω), ρ ^ l ^ m = algebraMap K Ω (algebraMap R K π) → ∃ ζ, IsPrimitiveRoot ζ (l ^ m) ∧ σ ρ = ζ * ρ) (hA : ∀ (K K' Ω : Type) [Field K] [Field K'] [Field Ω] [Algebra K K'] [Algebra K' Ω] [Algebra K Ω] [IsScalarTower K K' Ω] (l : ℕ) (L : IntermediateField K Ω), FiniteDimensional K L → Normal K L → IsPGroup l (L ≃ₐ[K] L) → FiniteDimensional K' (IntermediateField.adjoin K' (L : Set Ω)) ∧ Normal K' (IntermediateField.adjoin K' (L : Set Ω)) ∧ IsPGroup l (IntermediateField.adjoin K' (L : Set Ω) ≃ₐ[K'] IntermediateField.adjoin K' (L : Set Ω))) (hB : ∀ (F Ω : Type) [Field F] [CharZero F] [Field Ω] [Algebra F Ω] (n q : ℕ) (ρ ζ : Ω) (c : F) (σ : Ω ≃ₐ[F] Ω) (φ : Ω →+* Ω), 0 < n → ρ ^ n = algebraMap F Ω c → φ (algebraMap F Ω c) = algebraMap F Ω c → (∀ a : F, φ (algebraMap F Ω a) ∈ Set.range (algebraMap F Ω)) → (∀ ξ : Ω, ξ ^ n = 1 → ξ ∈ Set.range (algebraMap F Ω)) → IsPrimitiveRoot ζ n → σ ρ = ζ * ρ → φ ζ = ζ ^ q → ∀ x ∈ IntermediateField.adjoin F ({ρ} : Set Ω), φ (σ x) = (σ ^ q) (φ x) ∧ (σ x = x → x ∈ Set.range (algebraMap F Ω))) (hC : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K], Finite (IsLocalRing.ResidueField V) → ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] [Algebra V Ω] [IsScalarTower V K Ω] [IsLocalRing (integralClosure V Ω)], ∃ φ : Ω ≃ₐ[K] Ω, ∀ x : integralClosure V Ω, ∃ y : integralClosure V Ω, (y : Ω) = φ x ∧ y - x ^ Nat.card (IsLocalRing.ResidueField V) ∈ IsLocalRing.maximalIdeal (integralClosure V Ω)) :
    ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K], Finite (IsLocalRing.ResidueField V) → ∀ (l : ℕ), l.Prime → IsUnit (l : V) → ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] [Algebra V Ω] [IsScalarTower V K Ω] (q : ℕ), q = Nat.card (IsLocalRing.ResidueField V) → ∃ (R : Subalgebra V Ω) (_ : IsLocalRing R) (σ φ : Ω ≃ₐ[K] Ω), SH R (FractionRing R) ∧ IsLocalHom (algebraMap V R) ∧ (∀ c : IsLocalRing.ResidueField R, ∃ m, 1 ≤ m ∧ c ^ (q ^ m) = c) ∧ (∀ s : Finset R, ∃ (W : Subalgebra V R) (_ : IsDiscreteValuationRing W), (↑s : Set R) ⊆ W ∧ IsAdicComplete (IsLocalRing.maximalIdeal W) W ∧ Module.Finite V W ∧ IsLocalHom W.val.toRingHom ∧ ∃ f, 1 ≤ f ∧ ∀ x ∈ W, (φ ^ f) ((x : R) : Ω) = x) ∧ (∀ x ∈ R, σ x = x) ∧ (∀ x : R, ∃ y : R, (y : Ω) = φ x ∧ y - x ^ q ∈ IsLocalRing.maximalIdeal R) ∧ (∀ (m : ℕ) (ζ : Ω), ζ ^ l ^ m = 1 → σ ζ = ζ ∧ φ ζ = ζ ^ q) ∧ ∀ L : IntermediateField K Ω, FiniteDimensional K L → Normal K L → IsPGroup l (L ≃ₐ[K] L) → ∀ x ∈ L, φ (σ x) = (σ ^ q) (φ x) ∧ (σ x = x → ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ x * b = a) := by
  intro V K _ _ _ _ _ _ _ _ hfin l hl hlu Ω _ _ _ _ _ q hq
  subst hq
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have : FaithfulSMul V Ω := (faithfulSMul_iff_algebraMap_injective V Ω).2 (by
    rw [IsScalarTower.algebraMap_eq V K Ω]
    exact (algebraMap K Ω).injective.comp (IsFractionRing.injective V K))
  have hAloc : IsLocalRing (integralClosure V Ω) := isLocalRing_of_isIntegral (V := V) _
  obtain ⟨φ, hφ⟩ := hC V K hfin Ω
  set q := Nat.card (ResidueField V) with hq
  have hres := @isAlgClosed_residue V _ _ _ _ Ω _ _ _ _ _
  rw [← hq] at hres
  set R := Algebra.adjoin V (Teich q Ω) with hR
  have hg : Algebra.adjoin V (Teich q R) = ⊤ := gen_adjoin subset_rfl
  have hRI : Algebra.IsIntegral V R := isIntegral_of_gen hg
  have hle : R ≤ integralClosure V Ω := Algebra.adjoin_le fun t ht => isIntegral_of_teich one_lt_card ht
  have := faithful_sub R
  have := faithful_sub (integralClosure V Ω)
  have hRloc : IsLocalRing R := isLocalRing_of_isIntegral (V := V) _
  have hVR : IsLocalHom (algebraMap V R) :=
    isLocalHom_of_injective (Algebra.ofId V _) (FaithfulSMul.algebraMap_injective V _)
  have hVA : IsLocalHom (algebraMap V (integralClosure V Ω)) :=
    isLocalHom_of_injective (Algebra.ofId V _) (FaithfulSMul.algebraMap_injective V _)
  have hSH : SH R (FractionRing R) := ⟨dvr_of_gen' hg, henselian_of_gen hg, hres, inferInstance⟩
  have hφV : ∀ v : V, φ (algebraMap V Ω v) = algebraMap V Ω v := fun v => by
    rw [IsScalarTower.algebraMap_apply V K Ω, AlgEquiv.commutes]
  have hφT : ∀ t ∈ Teich q Ω, φ t = t ^ q := by
    rintro t ⟨f, hf, ht⟩
    obtain ⟨y, hy, hy'⟩ := hφ ⟨t, isIntegral_of_teich one_lt_card ⟨f, hf, ht⟩⟩
    have := teich_inj (V := V) ⟨f, hf, Subtype.ext (by
        rw [Subalgebra.coe_pow, hy, ← map_pow]; exact congrArg φ ht)⟩
      ⟨f, hf, Subtype.ext (by
        rw [Subalgebra.coe_pow, Subalgebra.coe_pow, ← pow_mul, mul_comm, pow_mul]
        exact congrArg (· ^ q) ht)⟩ hy'
    exact hy.symm.trans (congrArg Subtype.val this)
  have hTq : ∀ t ∈ Teich q Ω, ∀ n, t ^ n ∈ Teich q Ω := by
    rintro t ⟨f, hf, ht⟩ n
    exact ⟨f, hf, by rw [← pow_mul, mul_comm, pow_mul, ht]⟩
  have hφR : ∀ x ∈ R, φ x ∈ R := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx => rw [hφT x hx]; exact Algebra.subset_adjoin (hTq x hx q)
    | algebraMap v => rw [hφV]; exact Subalgebra.algebraMap_mem _ v
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  have hφn : ∀ t ∈ Teich q Ω, ∀ n, (φ ^ n) t = t ^ q ^ n := by
    intro t ht n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', AlgEquiv.mul_apply, ih, hφT _ (hTq t ht _), ← pow_mul, pow_succ]
  have hζ : ∀ (m : ℕ) (ζ : Ω), ζ ^ l ^ m = 1 → ζ ∈ Teich q Ω := by
    intro m ζ h
    obtain ⟨p, n, hp, hpm, hqp⟩ := exists_prime (V := V)
    have hne : p ≠ l := by
      rintro rfl
      exact hpm hlu
    have hco : Nat.Coprime q (l ^ m) := by
      rw [hq, hqp]
      exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hp hl).2 hne)
    refine ⟨(l ^ m).totient, Nat.totient_pos.2 (pow_pos hl.pos m), ?_⟩
    have h1 := Nat.ModEq.pow_totient hco
    rw [pow_eq_pow_of_modEq h1 h, pow_one]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨F, _, _, hF, _, _, _, _⟩ := exists_fractionField (V := V) (Ω := Ω) K R
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  have : IsAlgClosure F Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := K) F⟩
  obtain ⟨hT1, hT2, σ, hσ⟩ := hT R F ⟨hSH.1, hSH.2.1, hSH.2.2.1, hF⟩ _ (irreducible_of_gen hg hπ) l hl
    (by simpa using hlu.map (algebraMap V R)) Ω
  have hRF : ∀ x : R, algebraMap F Ω (algebraMap R F x) = x := fun x =>
    (IsScalarTower.algebraMap_apply R F Ω x).symm
  have hσR : ∀ x ∈ R, σ x = x := fun x hx => by
    have := σ.commutes (algebraMap R F ⟨x, hx⟩)
    rwa [hRF] at this
  refine ⟨R, hRloc, σ.restrictScalars K, φ, hSH, hVR, fun c => ?_, fun s => ?_, hσR, fun x => ?_,
    fun m ζ h => ⟨hσR ζ (Algebra.subset_adjoin (hζ m ζ h)), hφT ζ (hζ m ζ h)⟩, ?_⟩
  · exact teich_quot_of_gen hg (maximalIdeal R) (maximalIdeal_of_gen hg).le c
  · obtain ⟨W, hW, h1, h2, h3, h4, -, f, hf, hWf⟩ := exists_stage hg s
    refine ⟨W, hW, h1, h2, h3, h4, f, hf, fun x hx => ?_⟩
    rw [hWf] at hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      have hx' : (x : Ω) ^ q ^ f = x := congrArg Subtype.val hx
      rw [hφn x ⟨f, hf, hx'⟩, hx']
    | algebraMap v =>
      show (φ ^ f) (algebraMap V Ω v) = algebraMap V Ω v
      rw [IsScalarTower.algebraMap_apply V K Ω, AlgEquiv.commutes]
    | add x y _ _ hx hy => rw [Subalgebra.coe_add, map_add, hx, hy]
    | mul x y _ _ hx hy => rw [Subalgebra.coe_mul, map_mul, hx, hy]
  · refine ⟨⟨φ x, hφR x x.2⟩, rfl, fun hu => ?_⟩
    obtain ⟨y, hy, hy'⟩ := hφ ⟨x, hle x.2⟩
    refine hy' ?_
    convert hu.map (Subalgebra.inclusion hle) using 1
    apply Subtype.ext
    simp [hy]
  · intro L h1 h2 h3 x hx
    obtain ⟨a1, a2, a3⟩ := hA K F Ω l L h1 h2 h3
    obtain ⟨m, ρ, hρ, hL⟩ := hT1 _ a1 a2 a3
    obtain ⟨ζ, hζp, hσρ⟩ := hσ m ρ hρ
    have hfrac : ∀ a : F, ∃ u v : R, v ≠ 0 ∧ algebraMap F Ω a = (u : Ω) / v := fun a => by
      obtain ⟨u, v, hv, rfl⟩ := IsFractionRing.div_surjective (A := R) a
      exact ⟨u, v, nonZeroDivisors.ne_zero hv, by rw [map_div₀, hRF, hRF]⟩
    obtain ⟨b1, b2⟩ := hB F Ω (l ^ m) q ρ ζ _ σ (φ : Ω →+* Ω) (pow_pos hl.pos m) hρ
      (by rw [hRF]; exact hφV π)
      (fun a => by
        obtain ⟨u, v, -, h⟩ := hfrac a
        refine ⟨algebraMap R F ⟨φ u, hφR u u.2⟩ / algebraMap R F ⟨φ v, hφR v v.2⟩, ?_⟩
        rw [h, map_div₀, map_div₀, hRF, hRF]; rfl)
      (hT2 m) hζp hσρ (hφT ζ (hζ m ζ hζp.pow_eq_one)) x
      (hL (IntermediateField.subset_adjoin F _ hx))
    refine ⟨b1.trans ?_, fun h => ?_⟩
    · have : ∀ (n : ℕ) (y : Ω), (σ ^ n) y = (σ.restrictScalars K ^ n) y := fun n => by
        induction n with
        | zero => intro y; rfl
        | succ n ih => intro y; rw [pow_succ, pow_succ, AlgEquiv.mul_apply, AlgEquiv.mul_apply, ih]; rfl
      exact this _ _
    · obtain ⟨a, rfl⟩ := b2 h
      obtain ⟨u, v, hv, h⟩ := hfrac a
      have hv' : (v : Ω) ≠ 0 := fun e => hv (Subtype.ext e)
      exact ⟨u, u.2, v, v.2, hv', by rw [h, div_mul_cancel₀ _ hv']⟩

end GlobalTheory.SS.MaxUnr

open GlobalTheory.SS in

theorem GlobalTheory.SS.exists_maxUnramified_frobenius_tame : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K], Finite (IsLocalRing.ResidueField V) → ∀ (l : ℕ), l.Prime → IsUnit (l : V) → ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] [Algebra V Ω] [IsScalarTower V K Ω] (q : ℕ), q = Nat.card (IsLocalRing.ResidueField V) → ∃ (R : Subalgebra V Ω) (_ : IsLocalRing R) (σ φ : Ω ≃ₐ[K] Ω), SH R (FractionRing R) ∧ IsLocalHom (algebraMap V R) ∧ (∀ c : IsLocalRing.ResidueField R, ∃ m, 1 ≤ m ∧ c ^ (q ^ m) = c) ∧ (∀ s : Finset R, ∃ (W : Subalgebra V R) (_ : IsDiscreteValuationRing W), (↑s : Set R) ⊆ W ∧ IsAdicComplete (IsLocalRing.maximalIdeal W) W ∧ Module.Finite V W ∧ IsLocalHom W.val.toRingHom ∧ ∃ f, 1 ≤ f ∧ ∀ x ∈ W, (φ ^ f) ((x : R) : Ω) = x) ∧ (∀ x ∈ R, σ x = x) ∧ (∀ x : R, ∃ y : R, (y : Ω) = φ x ∧ y - x ^ q ∈ IsLocalRing.maximalIdeal R) ∧ (∀ (m : ℕ) (ζ : Ω), ζ ^ l ^ m = 1 → σ ζ = ζ ∧ φ ζ = ζ ^ q) ∧ ∀ L : IntermediateField K Ω, FiniteDimensional K L → Normal K L → IsPGroup l (L ≃ₐ[K] L) → ∀ x ∈ L, φ (σ x) = (σ ^ q) (φ x) ∧ (σ x = x → ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ x * b = a) :=
  GlobalTheory.SS.MaxUnr.main_of GlobalTheory.TameKummer.galois_of_prime_power_degree GlobalTheory.compositum_finite_normal_isPGroup
    GlobalTheory.kummer_twist_relation_and_fixed_field GlobalTheory.exists_arithFrobenius_absGalois
