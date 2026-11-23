import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.IdealValuations.LocDefY
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsRootCongruence

open KStar.TotallyRealRoots

namespace KStar.IdealValuations

variable {l : ℕ} [Fact l.Prime]

private noncomputable def lrO (l : ℕ) [Fact l.Prime] : ValuationSubring (PadicAlgCl l) :=
  (Valued.v : Valuation (PadicAlgCl l) NNReal).valuationSubring

private theorem lr_mem (x : PadicAlgCl l) : x ∈ lrO l ↔ ‖x‖ ≤ 1 := by
  rw [lrO, Valuation.mem_valuationSubring_iff, ← NNReal.coe_le_coe, PadicAlgCl.valuation_coe]
  rfl

private theorem lr_max (x : lrO l) :
    x ∈ IsLocalRing.maximalIdeal (lrO l) ↔ ‖(x : PadicAlgCl l)‖ < 1 := by
  unfold lrO at x ⊢
  rw [Valuation.mem_maximalIdeal_iff, ← NNReal.coe_lt_coe, PadicAlgCl.valuation_coe]
  rfl

private theorem lr_res (x y : lrO l) :
    IsLocalRing.residue (lrO l) x = IsLocalRing.residue (lrO l) y ↔
      ‖(x : PadicAlgCl l) - y‖ < 1 := by
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, lr_max]
  rfl

private theorem lr_char : CharP (IsLocalRing.ResidueField (lrO l)) l := by
  refine (CharP.charP_iff_prime_eq_zero Fact.out).mpr ?_
  rw [← map_natCast (IsLocalRing.residue (lrO l)), IsLocalRing.residue_eq_zero_iff, lr_max]
  have h := PadicAlgCl.norm_extends l (l : ℚ_[l])
  have h2 : ((l : lrO l) : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by
    simp
  rw [h2]
  exact h.trans_lt Padic.norm_p_lt_one

private theorem lr_aut (g : Gal(PadicAlgCl l/ℚ_[l])) (x : PadicAlgCl l) : ‖g x‖ = ‖x‖ :=
  (spectralNorm_eq_of_equiv g x).symm

private theorem lr_norm_root {m : ℕ} {ζ : PadicAlgCl l} (hm : ¬ l ∣ m) (h : ζ ^ m = 1) :
    ‖ζ‖ = 1 := by
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero _)
  have h1 : ‖ζ‖ ^ m = 1 := by rw [← norm_pow, h, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm0).mp h1

private theorem lr_field_pow {k : Type*} [Field k] [CharP k l] (φ : k →+* k) {m : ℕ}
    (hm : ¬ l ∣ m) : ∃ j : ℕ, ∀ a : k, a ^ m = 1 → φ a = a ^ l ^ j := by
  have hl : l.Prime := Fact.out
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero _)
  have hf : m.totient ≠ 0 := (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hm0)).ne'
  let F : Subfield k := RingHom.eqLocusField (iterateFrobenius k l m.totient) (RingHom.id k)
  have hF : ∀ a, a ∈ F ↔ a ^ l ^ m.totient = a := fun a => Iff.rfl
  have : Finite F := by
    classical
    have hne := FiniteField.X_pow_card_pow_sub_X_ne_zero k hf hl.one_lt
    refine Set.Finite.subset (s := (((Polynomial.X ^ l ^ m.totient - Polynomial.X :
      Polynomial k).roots.toFinset : Finset k) : Set k)) (Finset.finite_toSet _) ?_
    intro a ha
    have ha' := (hF a).mp ha
    simp only [Finset.mem_coe, Multiset.mem_toFinset]
    rw [Polynomial.mem_roots hne]
    simp [ha']
  let ψ : F →+* F := φ.restrict F F fun a ha => by
    rw [hF] at ha ⊢
    rw [← map_pow, ha]
  let : Algebra (ZMod l) F := ZMod.algebra _ _
  let ψ' : F →ₐ[ZMod l] F :=
    { ψ with commutes' := fun r => RingHom.congr_fun (RingHom.ext_zmod (ψ.comp (algebraMap _ _))
        (algebraMap (ZMod l) F)) r }
  let e : F ≃ₐ[ZMod l] F :=
    AlgEquiv.ofBijective ψ' (Finite.injective_iff_bijective.mp ψ.injective)
  obtain ⟨j, hj⟩ := FiniteField.exists_forall_apply_eq_pow (ZMod l) l F e
  refine ⟨j, fun a ha => ?_⟩
  have haF : a ∈ F := by
    rw [hF]
    have h1 : l ^ m.totient ≡ 1 [MOD m] :=
      Nat.ModEq.pow_totient ((Nat.Prime.coprime_iff_not_dvd hl).mpr hm)
    obtain ⟨c, hc⟩ := (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hl.pos)).mp h1.symm
    have h2 : l ^ m.totient = m * c + 1 := by
      have := Nat.one_le_pow m.totient _ hl.pos
      omega
    rw [h2, pow_succ, pow_mul, ha, one_pow, one_mul]
  have h := congrArg Subtype.val (hj ⟨a, haF⟩)
  rw [Nat.card_zmod] at h
  exact h

private theorem lr_int_pow {k : Type*} [Field k] [CharP k l] [Algebra (ZMod l) k] {a : k}
    (ha : IsIntegral (ZMod l) a) (h0 : a ≠ 0) : ∃ m : ℕ, ¬ l ∣ m ∧ a ^ m = 1 := by
  have hl : l.Prime := Fact.out
  let F := IntermediateField.adjoin (ZMod l) {a}
  have : FiniteDimensional (ZMod l) F := IntermediateField.adjoin.finiteDimensional ha
  have : Finite F := Module.finite_of_finite (ZMod l)
  let : Fintype F := Fintype.ofFinite F
  have : CharP F l := charP_of_injective_algebraMap (algebraMap (ZMod l) F).injective l
  obtain ⟨n, -, hn⟩ := FiniteField.card F l
  let b : F := ⟨a, IntermediateField.mem_adjoin_simple_self _ _⟩
  have hb : b ≠ 0 := fun h => h0 (congrArg Subtype.val h)
  refine ⟨Fintype.card F - 1, fun h => ?_,
    congrArg Subtype.val (FiniteField.pow_card_sub_one_eq_one b hb)⟩
  have h1 : l ∣ Fintype.card F := hn ▸ dvd_pow_self l n.ne_zero
  have h2 := (Nat.dvd_sub_iff_right Fintype.card_pos h1).mp h
  exact hl.one_lt.ne' (Nat.dvd_one.mp h2)

theorem norm_aut_and_roots :
    (∀ (g : Gal(PadicAlgCl l/ℚ_[l])) (x : PadicAlgCl l), ‖g x‖ = ‖x‖) ∧
      ∀ (m : ℕ) (ζ ζ' : PadicAlgCl l), ¬ l ∣ m → ζ ^ m = 1 → ζ' ^ m = 1 → ‖ζ - ζ'‖ < 1 →
        ζ = ζ' := by
  refine ⟨lr_aut, fun m ζ ζ' hm h h' hlt => ?_⟩
  by_contra hne
  have := lr_char (l := l)
  let a : lrO l := ⟨ζ, (lr_mem _).mpr (lr_norm_root hm h).le⟩
  let b : lrO l := ⟨ζ', (lr_mem _).mpr (lr_norm_root hm h').le⟩
  have hab : a - b ≠ 0 := fun hh => hne (congrArg Subtype.val (sub_eq_zero.mp hh))
  have ha : a ^ m = 1 := Subtype.ext h
  have hb : b ^ m = 1 := Subtype.ext h'
  have h1 := geom_sum₂_mul a b m
  rw [ha, hb, sub_self, mul_eq_zero_iff_right hab] at h1
  have h2 := congrArg (IsLocalRing.residue (lrO l)) h1
  have h3 := (lr_res a b).mpr hlt
  simp only [map_sum, map_mul, map_pow, map_zero, h3] at h2
  rw [geom_sum₂_self, mul_eq_zero] at h2
  rcases h2 with h2 | h2
  · exact hm ((CharP.cast_eq_zero_iff _ l m).mp h2)
  · have h4 := (lr_res b 0).mp (by rw [map_zero]; exact eq_zero_of_pow_eq_zero h2)
    simp only [b, ZeroMemClass.coe_zero, sub_zero, lr_norm_root hm h', lt_irrefl] at h4

theorem exists_pow_of_aut (g : Gal(PadicAlgCl l/ℚ_[l])) {m : ℕ} (hm : ¬ l ∣ m) :
    ∃ j : ℕ, ∀ ζ : PadicAlgCl l, ζ ^ m = 1 → g ζ = ζ ^ l ^ j := by
  have := lr_char (l := l)
  let gO : lrO l →+* lrO l := (g : PadicAlgCl l →+* PadicAlgCl l).restrict (lrO l) (lrO l)
    fun x hx => (lr_mem _).mpr ((lr_aut g x).trans_le ((lr_mem _).mp hx))
  have : IsLocalHom gO := ⟨fun x hx => by
    rw [← IsLocalRing.notMem_maximalIdeal, lr_max] at hx ⊢
    rw [← lr_aut g]
    exact hx⟩
  obtain ⟨j, hj⟩ := lr_field_pow (IsLocalRing.ResidueField.map gO) hm
  refine ⟨j, fun ζ h => ?_⟩
  let a : lrO l := ⟨ζ, (lr_mem _).mpr (lr_norm_root hm h).le⟩
  have ha : a ^ m = 1 := Subtype.ext h
  have h1 := hj (IsLocalRing.residue _ a) (by rw [← map_pow, ha, map_one])
  rw [IsLocalRing.ResidueField.map_residue, ← map_pow, lr_res] at h1
  refine norm_aut_and_roots.2 m _ _ hm (by rw [← map_pow, h, map_one]) ?_ h1
  rw [← pow_mul, mul_comm, pow_mul, h, one_pow]

theorem exists_root_congr {x : PadicAlgCl l} (hx : ‖x‖ = 1) :
    ∃ (m : ℕ) (ζ : PadicAlgCl l), ¬ l ∣ m ∧ ζ ^ m = 1 ∧ ‖x - ζ‖ < 1 :=
  _root_.UpperTheory.Reformulated.B.ExistsRootCongruence.exists_root_congr hx

theorem mem_locInertia_iff (g : Gal(PadicAlgCl l/ℚ_[l])) :
    g ∈ locInertia l ↔ IsResTrivial l g := by
  constructor
  · intro hg x hx
    rcases hx.lt_or_eq with hx | hx
    · rw [sub_eq_add_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
      · rwa [lr_aut]
      · rwa [norm_neg]
    · obtain ⟨m, ζ, hm, h, hlt⟩ := exists_root_congr hx
      have h1 : g x - x = g (x - ζ) + -(x - ζ) := by
        rw [map_sub, hg m ζ hm h]; ring
      rw [h1]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
      · rwa [lr_aut]
      · rwa [norm_neg]
  · intro hg m ζ hm h
    exact norm_aut_and_roots.2 m _ _ hm (by rw [← map_pow, h, map_one]) h
      (hg ζ (lr_norm_root hm h).le)

end KStar.IdealValuations
