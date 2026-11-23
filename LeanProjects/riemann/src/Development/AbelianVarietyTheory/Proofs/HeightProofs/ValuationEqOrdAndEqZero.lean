import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.LocRingPf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj
open scoped TensorProduct

namespace GlobalTheory.OrdVal

variable {O A : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing A] [Algebra O A]

omit [IsDomain O] [IsDiscreteValuationRing O] in

theorem nonneg_of_isIntegral (u : AddValuation A (WithTop ℤ))
    (hu : ∀ r : O, 0 ≤ u (algebraMap O A r)) {x : A} (hx : IsIntegral O x) : 0 ≤ u x := by
  let v : Valuation A (Multiplicative (WithTop ℤ)ᵒᵈ) := u
  let f : O →+* v.integer := (algebraMap O A).codRestrict v.integer (fun r => hu r)
  have h1 : IsIntegral v.integer x := by
    obtain ⟨p, hp, hz⟩ := hx
    refine ⟨p.map f, hp.map f, ?_⟩
    rw [Polynomial.eval₂_map]
    exact hz
  exact (Valuation.integer.integers v).mem_of_integral h1

def centre (u : AddValuation A (WithTop ℤ)) (hu : ∀ a : ↥(As O A), 0 ≤ u (a : A)) :
    Ideal ↥(As O A) where
  carrier := {a | 0 < u (a : A)}
  zero_mem' := by simp
  add_mem' := fun {a b} ha hb => by
    have := u.map_add (a : A) b
    exact lt_of_lt_of_le (lt_min ha hb) this
  smul_mem' := fun c a ha => by
    change 0 < u ((c : A) * a)
    rw [u.map_mul]
    exact lt_of_lt_of_le ha (le_add_of_nonneg_left (hu c))

theorem centre_isPrime (u : AddValuation A (WithTop ℤ)) (hu : ∀ a : ↥(As O A), 0 ≤ u (a : A)) :
    (centre u hu).IsPrime := by
  refine ⟨fun h => ?_, fun {a b} h => ?_⟩
  · have : (1 : ↥(As O A)) ∈ centre u hu := h ▸ Submodule.mem_top
    change 0 < u (1 : A) at this
    simp at this
  · change 0 < u ((a : A) * b) at h
    by_contra hn
    rw [not_or] at hn
    have ha : u (a : A) = 0 := le_antisymm (not_lt.1 hn.1) (hu a)
    have hb : u (b : A) = 0 := le_antisymm (not_lt.1 hn.2) (hu b)
    rw [u.map_mul, ha, hb] at h
    simp at h

theorem centre_isMaximal (u : AddValuation A (WithTop ℤ)) (hu : ∀ a : ↥(As O A), 0 ≤ u (a : A))
    {ϖ : O} (hϖ : Irreducible ϖ) (hpos : 0 < u (algebraMap O A ϖ)) :
    (centre u hu).IsMaximal := by
  haveI := centre_isPrime u hu
  refine Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := O) _ ?_
  have hle : IsLocalRing.maximalIdeal O ≤ (centre u hu).comap (algebraMap O ↥(As O A)) := by
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_le_iff_mem]
    exact hpos
  have := (IsLocalRing.maximalIdeal.isMaximal O).eq_of_le (Ideal.IsPrime.ne_top inferInstance) hle
  rw [← this]
  infer_instance

theorem le_of_vL_le (u : AddValuation A (WithTop ℤ)) (hu : ∀ a : ↥(As O A), 0 ≤ u (a : A))
    (ζ : Pts O A) [IsDVRAt ζ] (hζ : ∀ a : ↥(As O A), a ∉ ζ.asIdeal → u (a : A) = 0)
    {a b : ↥(As O A)} (hab : vL ζ a ≤ vL ζ b) : u (a : A) ≤ u (b : A) := by
  rw [vL_eq_addVal, vL_eq_addVal, IsDiscreteValuationRing.addVal_le_iff_dvd] at hab
  obtain ⟨z, hz⟩ := hab
  obtain ⟨⟨x, s⟩, hs⟩ := IsLocalization.surj ζ.asIdeal.primeCompl z
  have h1 : algebraMap _ (Loc ζ) (b * s) = algebraMap _ (Loc ζ) (a * x) := by
    simp only at hs
    rw [map_mul, map_mul, hz, mul_assoc, hs]
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists ζ.asIdeal.primeCompl (Loc ζ)).1 h1
  have h2 : ((c : ↥(As O A)) : A) * ((b : A) * ((s : ↥(As O A)) : A))
      = ((c : ↥(As O A)) : A) * ((a : A) * (x : A)) := congrArg Subtype.val hc
  have h3 := congrArg u h2
  rw [u.map_mul, u.map_mul, u.map_mul, u.map_mul, hζ _ c.2, hζ _ s.2, zero_add, zero_add,
    add_zero] at h3
  rw [h3]
  exact le_add_of_nonneg_right (hu x)

theorem exists_vL_eq_one (ζ : Pts O A) [IsDVRAt ζ] : ∃ a : ↥(As O A), vL ζ a = 1 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (Loc ζ)
  obtain ⟨⟨x, s⟩, hs⟩ := IsLocalization.surj ζ.asIdeal.primeCompl π
  refine ⟨x, ?_⟩
  have h0 := (vL_eq_zero_iff ζ s).2 s.2
  rw [vL_eq_addVal] at h0
  simp only at hs
  rw [vL_eq_addVal, ← hs, IsDiscreteValuationRing.addVal_mul, h0,
    IsDiscreteValuationRing.addVal_uniformizer hπ, add_zero]

theorem exists_ord_eq [∀ ζ : Pts O A, IsDVRAt ζ] {ϖ : O} (h : IsUnif A ϖ)
    (u : AddValuation A (WithTop ℤ)) (hO : ∀ r : O, 0 ≤ u (algebraMap O A r))
    (hpos : 0 < u (algebraMap O A ϖ)) (hone : ∃ a, u a = 1) :
    ∃ ζ : Pts O A, ∀ a : A, Formalism.MainNotions.Gaps.EtaleWeightGaps.ord ϖ ζ a = u a := by
  have hu : ∀ a : ↥(As O A), 0 ≤ u (a : A) := fun a => nonneg_of_isIntegral u hO a.2
  let ζ : Pts O A := ⟨centre u hu, centre_isMaximal u hu h.irreducible hpos⟩
  have hζ : ∀ a : ↥(As O A), a ∉ ζ.asIdeal → u (a : A) = 0 :=
    fun a ha => le_antisymm (not_lt.1 ha) (hu a)
  obtain ⟨a₀, ha₀⟩ := exists_vL_eq_one ζ
  have hfin : ∀ (b : ↥(As O A)) (m : ℕ), vL ζ b = m → u (b : A) = m • u (a₀ : A) := by
    intro b m hb
    have e : vL ζ (a₀ ^ m) = vL ζ b := by rw [vL_pow, ha₀, hb]; simp
    have := le_antisymm (le_of_vL_le u hu ζ hζ e.ge) (le_of_vL_le u hu ζ hζ e.le)
    rw [this, SubmonoidClass.coe_pow, u.map_pow]
  have htop : ∀ b : ↥(As O A), vL ζ b = ⊤ → u (b : A) = ⊤ := by
    intro b hb
    have := le_of_vL_le u hu ζ hζ (a := 0) (b := b) (by rw [hb]; exact le_top)
    simpa using this
  have hϖ : u (algebraMap O A ϖ) = ep ϖ ζ • u (a₀ : A) :=
    hfin (algebraMap O ↥(As O A) ϖ) _ (coe_ep ζ h).symm
  have hϖfin : u (algebraMap O A ϖ) ≠ ⊤ := by
    obtain ⟨y, hy⟩ := h.isUnit.exists_right_inv
    intro ht
    have := congrArg u hy
    rw [u.map_mul, ht, u.map_one] at this
    simp at this
  have ha₀fin : u (a₀ : A) ≠ ⊤ := by
    intro ht
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (ep_pos ζ h).ne'
    rw [hϖ, ht, hk, succ_nsmul] at hϖfin
    simp at hϖfin
  obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.1 ha₀fin
  have hq0 : 0 ≤ q := by
    have := hu a₀
    rw [← hq] at this
    exact_mod_cast this
  have key : ∀ x : A, (Formalism.MainNotions.Gaps.EtaleWeightGaps.ord ϖ ζ x = ⊤ ∧ u x = ⊤) ∨
      ∃ k : ℤ, Formalism.MainNotions.Gaps.EtaleWeightGaps.ord ϖ ζ x = (k : WithTop ℤ) ∧ u x = ((k * q : ℤ) : WithTop ℤ) := by
    intro x
    obtain ⟨n, hn⟩ := h.denom x
    have e1 : u (ϖ ^ n • x) = ((n * (ep ϖ ζ * q) : ℤ) : WithTop ℤ) + u x := by
      rw [Algebra.smul_def, map_pow, u.map_mul, u.map_pow, hϖ, ← hq, ← WithTop.coe_nsmul,
        ← WithTop.coe_nsmul, nsmul_eq_mul, nsmul_eq_mul]
    rw [ord_eq ζ h hn, ordAt]
    cases hv : vL ζ ⟨ϖ ^ n • x, hn⟩ with
    | top =>
      left
      refine ⟨by simp, ?_⟩
      have := htop _ hv
      change u (ϖ ^ n • x) = ⊤ at this
      rw [e1, WithTop.add_eq_top] at this
      exact this.resolve_left WithTop.coe_ne_top
    | coe m =>
      right
      refine ⟨m + -(n * ep ϖ ζ), by rw [ENat.map_natCast, ← WithTop.coe_add], ?_⟩
      have := hfin _ m hv
      change u (ϖ ^ n • x) = _ at this
      rw [e1, ← hq, ← WithTop.coe_nsmul, nsmul_eq_mul] at this
      have hx : u x ≠ ⊤ := by
        intro ht
        rw [ht, add_top] at this
        exact WithTop.top_ne_coe this
      obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 hx
      rw [← ht, ← WithTop.coe_add, WithTop.coe_inj] at this
      rw [← ht, WithTop.coe_inj]
      linarith
  have hq1 : q = 1 := by
    obtain ⟨a, ha⟩ := hone
    rcases key a with ⟨_, h2⟩ | ⟨k, _, h2⟩
    · rw [ha] at h2
      exact absurd h2 WithTop.one_ne_top
    · rw [ha, ← WithTop.coe_one, WithTop.coe_inj] at h2
      exact Int.eq_one_of_mul_eq_one_left hq0 h2.symm
  refine ⟨ζ, fun a => ?_⟩
  rcases key a with ⟨h1, h2⟩ | ⟨k, h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, hq1, mul_one]

theorem eq_zero_of_ord_eq_top [∀ ζ : Pts O A, IsDVRAt ζ] {ϖ : O} (h : IsUnif A ϖ) (a : A)
    (ha : ∀ ζ : Pts O A, Formalism.MainNotions.Gaps.EtaleWeightGaps.ord ϖ ζ a = ⊤) : a = 0 := by
  obtain ⟨n, hn⟩ := h.denom a
  have key : (⟨ϖ ^ n • a, hn⟩ : ↥(As O A)) ∈ (⊥ : Ideal ↥(As O A)) := by
    have h0 : ∀ ζ : Pts O A, algebraMap ↥(As O A) (Loc ζ) ⟨ϖ ^ n • a, hn⟩ ∈
        Ideal.map (algebraMap ↥(As O A) (Loc ζ)) ⊥ := by
      intro ζ
      have h1 := ha ζ
      rw [ord_eq ζ h hn, ordAt, WithTop.add_eq_top] at h1
      have h2 : vL ζ ⟨ϖ ^ n • a, hn⟩ = ⊤ := by
        simpa using h1.resolve_right WithTop.coe_ne_top
      rw [(vL_eq_top_iff ζ _).1 h2]
      exact Submodule.zero_mem _
    exact Ideal.mem_of_localization_maximal (fun P hP => h0 ⟨P, hP⟩)
  have h2 : ϖ ^ n • a = 0 := congrArg Subtype.val (Ideal.mem_bot.1 key)
  rw [Algebra.smul_def, map_pow] at h2
  exact ((h.isUnit.pow n).mul_right_eq_zero).1 h2

theorem valuation_eq_ord_and_eq_zero :
    ∀ (O A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing A] [Algebra O A] [∀ ζ : Pts O A, IsDVRAt ζ] (ϖ : O), IsUnif A ϖ → (∀ u : AddValuation A (WithTop ℤ), (∀ r : O, 0 ≤ u (algebraMap O A r)) → 0 < u (algebraMap O A ϖ) → (∃ a, u a = 1) → ∃ ζ : Pts O A, ∀ a : A, Formalism.MainNotions.Gaps.EtaleWeightGaps.ord ϖ ζ a = u a) ∧ ∀ a : A, (∀ ζ : Pts O A, Formalism.MainNotions.Gaps.EtaleWeightGaps.ord ϖ ζ a = ⊤) → a = 0 :=
  fun _ _ _ _ _ _ _ _ _ h => ⟨exists_ord_eq h, eq_zero_of_ord_eq_top h⟩

end GlobalTheory.OrdVal
