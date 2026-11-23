import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderContainsCharacters

open GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT

noncomputable section

namespace PositivityTheory.HtPt.Twpair

section Ind

variable {R : Type} [CommRing R] {T : Type} [CommGroup T]

theorem translate_mem {A : Subalgebra R (T → R)} (hA : IsHopfOrder A) {f : T → R} (hf : f ∈ A) (t : T) :
    (fun h => f (t * h)) ∈ A := by
  have key : ∀ g ∈ prodSpan A, (fun h => g (t, h)) ∈ A := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem x h =>
      obtain ⟨a, -, b, hb, rfl⟩ := h
      exact A.smul_mem hb (a t)
    | zero => exact A.zero_mem
    | add x y _ _ hx hy => exact A.add_mem hx hy
    | smul r x _ hx => exact A.smul_mem hx r
  exact key _ (hA.comul f hf)

omit [CommGroup T] in

theorem mul_mem_prodSpan {A : Subalgebra R (T → R)} {a b : T → R} (ha : a ∈ A) (hb : b ∈ A)
    {g : T × T → R} (hg : g ∈ prodSpan A) : (fun z => a z.1 * b z.2 * g z) ∈ prodSpan A := by
  induction hg using Submodule.span_induction with
  | mem x h =>
    obtain ⟨a', ha', b', hb', rfl⟩ := h
    refine Submodule.subset_span ⟨a * a', A.mul_mem ha ha', b * b', A.mul_mem hb hb', ?_⟩
    funext z
    simp only [Pi.mul_apply]
    ring
  | zero =>
    have := (prodSpan A).zero_mem
    convert this using 1
    funext z
    simp
  | add x y _ _ hx hy =>
    have := (prodSpan A).add_mem hx hy
    convert this using 1
    funext z
    simp [mul_add]
  | smul r x _ hx =>
    have := (prodSpan A).smul_mem r hx
    convert this using 1
    funext z
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

open Classical in

def extZero (H : Subgroup T) (t : T) (a : H → R) : T → R :=
  fun x => if h : t⁻¹ * x ∈ H then a ⟨_, h⟩ else 0

open Classical in

def extZero₂ (H : Subgroup T) (t s : T) (g : H × H → R) : T × T → R :=
  fun z => if h : t⁻¹ * z.1 ∈ H ∧ s⁻¹ * z.2 ∈ H then g (⟨_, h.1⟩, ⟨_, h.2⟩) else 0

theorem extZero_mem {H : Subgroup T} {A : Subalgebra R (H → R)} (hA : IsHopfOrder A) (t : T) {a : H → R}
    (ha : a ∈ A) : extZero H t a ∈ indOrder H.subtype A := by
  intro u
  by_cases hu : t⁻¹ * u ∈ H
  · have := translate_mem hA ha ⟨_, hu⟩
    convert this using 1
    funext h
    have h1 : t⁻¹ * (u * H.subtype h) ∈ H := by
      rw [← mul_assoc]; exact H.mul_mem hu h.2
    simp only [extZero]
    rw [dif_pos h1]
    congr 1
    exact Subtype.ext (mul_assoc _ _ _).symm
  · have : (fun h : H => extZero H t a (u * H.subtype h)) = 0 := by
      funext h
      have h1 : ¬ t⁻¹ * (u * H.subtype h) ∈ H := by
        rw [← mul_assoc]
        exact fun h1 => hu ((H.mul_mem_cancel_right h.2).1 h1)
      simp only [extZero]
      rw [dif_neg h1]
      rfl
    rw [this]
    exact A.zero_mem

theorem extZero₂_mem {H : Subgroup T} {A : Subalgebra R (H → R)} (hA : IsHopfOrder A) (t s : T)
    {g : H × H → R} (hg : g ∈ prodSpan A) : extZero₂ H t s g ∈ prodSpan (indOrder H.subtype A) := by
  induction hg using Submodule.span_induction with
  | mem x h =>
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    refine Submodule.subset_span ⟨_, extZero_mem hA t ha, _, extZero_mem hA s hb, ?_⟩
    funext z
    by_cases h1 : t⁻¹ * z.1 ∈ H <;> by_cases h2 : s⁻¹ * z.2 ∈ H <;> simp [extZero, extZero₂, h1, h2]
  | zero =>
    have : extZero₂ H t s (0 : H × H → R) = 0 := by
      funext z
      simp [extZero₂]
    rw [this]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    have := Submodule.add_mem _ hx hy
    convert this using 1
    funext z
    simp only [extZero₂, Pi.add_apply]
    split_ifs <;> simp
  | smul r x _ hx =>
    have := Submodule.smul_mem _ r hx
    convert this using 1
    funext z
    simp only [extZero₂, Pi.smul_apply]
    split_ifs <;> simp

theorem pair_ind : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (H : Subgroup T) (A : Subalgebra R (H → R)) (β : T →* T →* Rˣ), IsHopfOrder A → (fun z : H × H => ((β z.1 z.2 : Rˣ) : R)) ∈ prodSpan A → (fun z : T × T => ((β z.1 z.2 : Rˣ) : R)) ∈ prodSpan (indOrder H.subtype A) := by
  intro R _ _ _ T _ _ H A β hA hβ
  classical
  have := Fintype.ofFinite (T ⧸ H)
  have h1 : ∀ t s : T, (fun w : H × H => ((β (t * w.1) (s * w.2) : Rˣ) : R)) ∈ prodSpan A := by
    intro t s
    have ha := char_mem_hopfOrder R H A hA ((β.flip s).comp H.subtype)
    have hb := char_mem_hopfOrder R H A hA ((β t).comp H.subtype)
    have := Submodule.smul_mem _ ((β t s : Rˣ) : R) (mul_mem_prodSpan ha hb hβ)
    convert this using 1
    funext w
    simp
    ring
  have key : ∀ (c : T ⧸ H) (x : T), c.out⁻¹ * x ∈ H ↔ c = (x : T ⧸ H) := by
    intro c x
    rw [← QuotientGroup.eq, QuotientGroup.out_eq']
  have e : (fun z : T × T => ((β z.1 z.2 : Rˣ) : R)) = ∑ c : (T ⧸ H) × (T ⧸ H),
      extZero₂ H c.1.out c.2.out (fun w : H × H => ((β (c.1.out * w.1) (c.2.out * w.2) : Rˣ) : R)) := by
    funext z
    rw [Finset.sum_apply, Finset.sum_eq_single ((z.1 : T ⧸ H), (z.2 : T ⧸ H))]
    · simp only [extZero₂]
      rw [dif_pos ⟨(key _ _).2 rfl, (key _ _).2 rfl⟩]
      simp only [mul_inv_cancel_left]
    · intro c _ hc
      simp only [extZero₂]
      rw [dif_neg]
      rintro ⟨a, b⟩
      exact hc (Prod.ext ((key _ _).1 a) ((key _ _).1 b))
    · simp
  rw [e]
  exact Submodule.sum_mem _ fun c _ => extZero₂_mem hA _ _ (h1 _ _)

end Ind

section Val

variable {C : Type} [Field C] {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C]

theorem mem_maximalIdeal_iff [IsLocalRing O] (hv : v.Integers O) (x : O) :
    x ∈ IsLocalRing.maximalIdeal O ↔ v (algebraMap O C x) < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hv.isUnit_iff_valuation_eq_one]
  exact ⟨fun h => lt_of_le_of_ne (hv.map_le_one x) h, fun h => h.ne⟩

theorem prime_eq_bot_or_maximal [IsLocalRing O] (hv : v.Integers O) (P : Ideal O) [hP : P.IsPrime] :
    P = ⊥ ∨ P = IsLocalRing.maximalIdeal O := by
  by_cases h : P = ⊥
  · exact Or.inl h
  right
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  refine le_antisymm (IsLocalRing.le_maximalIdeal hP.ne_top) fun y hy => ?_
  rw [mem_maximalIdeal_iff hv] at hy
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (hv.valuation_pos_iff_ne_zero.2 hx0) hy
  have : x ∣ y ^ n := hv.dvd_of_le (by rw [map_pow, map_pow]; exact hn.le)
  exact hP.mem_of_pow_mem n (Ideal.mem_of_dvd P this hx)

theorem henselian [IsAlgClosed C] [IsLocalRing O] (hv : v.Integers O) : HenselianLocalRing O where
  is_henselian f hf a₀ h₀ _ := by
    rw [mem_maximalIdeal_iff hv] at h₀
    have hm : (f.map (algebraMap O C)).Monic := hf.map _
    have e := (IsAlgClosed.splits (f.map (algebraMap O C))).eval_eq_prod_roots_of_monic hm (algebraMap O C a₀)
    rw [Polynomial.eval_map_algebraMap, Polynomial.aeval_algebraMap_apply, Polynomial.coe_aeval_eq_eval] at e
    have : ∃ r ∈ (f.map (algebraMap O C)).roots, v (algebraMap O C a₀ - r) < 1 := by
      by_contra hne
      push Not at hne
      rw [e, map_multiset_prod] at h₀
      refine absurd h₀ (not_lt.2 (Multiset.one_le_prod_of_one_le fun x hx => ?_))
      simp only [Multiset.map_map, Multiset.mem_map] at hx
      obtain ⟨r, hr, rfl⟩ := hx
      exact hne r hr
    obtain ⟨r, hr, hlt⟩ := this
    have hr1 : v r ≤ 1 := by
      have : r = algebraMap O C a₀ - (algebraMap O C a₀ - r) := by ring
      rw [this]
      exact v.map_sub_le (hv.map_le_one _) hlt.le
    obtain ⟨a, rfl⟩ := hv.exists_of_le_one hr1
    refine ⟨a, ?_, ?_⟩
    · have := (Polynomial.mem_roots hm.ne_zero).1 hr
      exact (Polynomial.isRoot_map_iff hv.hom_inj).1 this
    · rw [mem_maximalIdeal_iff hv, map_sub, Valuation.map_sub_swap]
      exact hlt

end Val

section Lev

variable {La : Type} [AddCommGroup La]

theorem lev_surjective (p n : ℕ) : Function.Surjective (lev p n : La → LevGrp La p n) := fun t => by
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ t.toAdd
  exact ⟨a, congrArg Multiplicative.ofAdd ha⟩

theorem finite_levGrp [Module.Finite ℤ La] {p : ℕ} (hp : p ≠ 0) (n : ℕ) : Finite (LevGrp La p n) := by
  have : Finite (La ⧸ LinearMap.range ((p ^ n) • (LinearMap.id : La →ₗ[ℤ] La))) := by
    refine Module.finite_of_fg_torsion _ fun x => ?_
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    refine ⟨⟨((p ^ n : ℕ) : ℤ), mem_nonZeroDivisors_of_ne_zero (by positivity)⟩, ?_⟩
    change Submodule.Quotient.mk (((p ^ n : ℕ) : ℤ) • a) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact ⟨a, by simp only [LinearMap.smul_apply, LinearMap.id_apply, natCast_zsmul]⟩
  infer_instance

theorem exists_bichar {O : Type} [CommRing O] (p n : ℕ) (B : La →ₗ[ℤ] La →ₗ[ℤ] ℤ) (ζ : Oˣ) (hζ : ζ ^ p ^ n = 1) :
    ∃ β : LevGrp La p n →* LevGrp La p n →* Oˣ, ∀ a b, β (lev p n a) (lev p n b) = ζ ^ B a b := by
  let N := LinearMap.range ((p ^ n) • (LinearMap.id : La →ₗ[ℤ] La))
  let z : ℤ →ₗ[ℤ] Additive Oˣ := LinearMap.toSpanSingleton ℤ _ (Additive.ofMul ζ)
  have hz : ∀ k : ℤ, z ((p ^ n) • k) = 0 := by
    intro k
    rw [map_nsmul, LinearMap.toSpanSingleton_apply, smul_comm, ← ofMul_pow, hζ]
    simp
  let B' : La →ₗ[ℤ] La →ₗ[ℤ] Additive Oˣ := B.compr₂ z
  let B'' : (La ⧸ N) →ₗ[ℤ] (La ⧸ N) →ₗ[ℤ] Additive Oˣ := B'.liftQ₂ N N
    (by
      rintro _ ⟨a, rfl⟩
      rw [LinearMap.mem_ker]
      ext b
      simp only [B', LinearMap.smul_apply, LinearMap.id_apply, LinearMap.compr₂_apply, map_nsmul,
        LinearMap.zero_apply]
      rw [← map_nsmul, hz])
    (by
      rintro _ ⟨a, rfl⟩
      rw [LinearMap.mem_ker]
      ext b
      simp only [B', LinearMap.smul_apply, LinearMap.id_apply, LinearMap.compr₂_apply, map_nsmul,
        LinearMap.zero_apply, LinearMap.flip_apply]
      rw [← map_nsmul, hz])
  refine ⟨{ toFun := fun x => { toFun := fun y => (B'' x.toAdd y.toAdd).toMul
                                map_one' := by simp
                                map_mul' := by simp }
            map_one' := by ext; simp
            map_mul' := by intros; ext; simp }, fun a b => ?_⟩
  change (z (B a b)).toMul = _
  rw [LinearMap.toSpanSingleton_apply, ← ofMul_zpow]
  rfl

end Lev

end PositivityTheory.HtPt.Twpair
