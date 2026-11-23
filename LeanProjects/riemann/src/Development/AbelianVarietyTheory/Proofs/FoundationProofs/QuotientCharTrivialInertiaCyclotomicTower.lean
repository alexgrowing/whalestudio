import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotZeroChi
import Development.AbelianVarietyTheory.Definitions.Foundations.ZetaSysUOfHalves
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ZetaUr
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries

noncomputable section

namespace GlobalTheory.QuotInertia

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem fix_mu [IsAlgClosure ℚ Ω] (s : G ℚ Ω) (hs : cycBar ℚ Ω l s = 1) (ζ : Ω) (hζ : ζ ^ l = 1) :
    s ζ = ζ := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hinj : Function.Injective ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom) :=
    (algebraMap ℚ_[l] (Qbar l)).injective.comp (fun a b h => Subtype.ext h)
  have hz : cycZ ℚ Ω l s = 1 := by
    apply Units.map_injective (f := ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom).toMonoidHom) hinj
    rw [map_one]
    exact hs
  have hz' : cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) = 1 := hz
  have h := cyclotomicCharacter.spec l (n := 1) (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) ζ (by rw [pow_one]; exact hζ)
  change s ζ = _ at h
  rw [h, hz', Units.val_one, map_one, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by rw [pow_one]; exact (Fact.out : l.Prime).one_lt), pow_one]

theorem fix_sqrt_unit (hl : l ≠ 2) {A : ValuationSubring Ω} (hA : OverL l A) {s : G ℚ Ω}
    (hs : s ∈ Ine (F := ℚ) A) (N : ℤ) (hN : ¬ (l : ℤ) ∣ N) (β : Ω) (hβ : β ^ 2 = N) : s β = β := by
  have hsq : (s β) ^ 2 = β ^ 2 := by rw [← map_pow, hβ, map_intCast]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · exact h
  exfalso
  obtain ⟨-, hI⟩ := hs
  have hβ1 : A.valuation β ≤ 1 := by
    by_contra hc
    push_neg at hc
    have h1 : 1 < A.valuation β ^ 2 := one_lt_pow₀ hc two_ne_zero
    rw [← map_pow, hβ] at h1
    have : A.valuation (N : Ω) ≤ 1 := (A.valuation_le_one_iff _).2 (intCast_mem A N)
    exact absurd h1 (not_lt.2 this)
  have h2 := hI β hβ1
  rw [h] at h2
  have h3 : A.valuation (((4 * N : ℤ) : Ω)) < 1 := by
    have e : ((4 * N : ℤ) : Ω) = (-β - β) ^ 2 := by push_cast; rw [← hβ]; ring
    rw [e, map_pow]
    exact pow_lt_one₀ zero_le' h2 two_ne_zero
  obtain ⟨v, hv, hlv⟩ := hA
  have h4 : ((4 * N : ℤ) : 𝓞 ℚ) ∈ v.asIdeal := by
    rw [← hv]
    convert h3 using 2
    simp only [map_intCast, Int.cast_mul, Int.cast_ofNat, map_mul, map_ofNat, algebraMap.coe_mul, map_ratCast]
  have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
  have hcop : IsCoprime (l : ℤ) (4 * N) := by
    rw [hp.irreducible.coprime_iff_not_dvd]
    intro hd
    rcases hp.dvd_or_dvd hd with h5 | h5
    · have h6 : l ∣ 4 := by exact_mod_cast h5
      have h7 : l ∣ 2 := (Fact.out : l.Prime).dvd_of_dvd_pow (n := 2) (by norm_num; exact h6)
      exact hl ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h7)
    · exact hN h5
  obtain ⟨a, b, hab⟩ := hcop.map (Int.castRingHom (𝓞 ℚ))
  have hl' : (Int.castRingHom (𝓞 ℚ)) (l : ℤ) ∈ v.asIdeal := by simpa using hlv
  have h1 : (1 : 𝓞 ℚ) ∈ v.asIdeal := by
    rw [← hab]
    exact add_mem (Ideal.mul_mem_left _ _ hl') (Ideal.mul_mem_left _ _ (by simpa using h4))
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)

theorem gauss_fix [IsAlgClosure ℚ Ω] (hl : l ≠ 2) (s : G ℚ Ω) (hs : ∀ ζ : Ω, ζ ^ l = 1 → s ζ = ζ) :
    ∃ (Gs : Ω) (c : ℤ), c ^ 2 = 1 ∧ Gs ^ 2 = ((c * l : ℤ) : Ω) ∧ s Gs = Gs := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω l
  have hF : ringChar (ZMod l) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hl
  set ψ : AddChar (ZMod l) Ω := AddChar.zmodChar l hζ.pow_eq_one with hψdef
  have hψ : ψ.IsPrimitive := AddChar.zmodChar_primitive_of_primitive_root l hζ
  set χ : MulChar (ZMod l) Ω := (quadraticChar (ZMod l)).ringHomComp (Int.castRingHom Ω) with hχdef
  have hχ1 : χ ≠ 1 :=
    (MulChar.ringHomComp_ne_one_iff (Int.cast_injective (α := Ω))).2 (quadraticChar_ne_one hF)
  have hχ2 : χ.IsQuadratic := (quadraticChar_isQuadratic (ZMod l)).comp _
  have hχa : ∀ x, χ x = ((quadraticChar (ZMod l) x : ℤ) : Ω) := fun x => rfl
  refine ⟨gaussSum χ ψ, quadraticChar (ZMod l) (-1), quadraticChar_sq_one (neg_ne_zero.2 one_ne_zero), ?_, ?_⟩
  · rw [gaussSum_sq hχ1 hχ2 hψ, hχa, ZMod.card]
    push_cast
    rfl
  · rw [gaussSum, map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [map_mul, hχa, map_intCast, hψdef, AddChar.zmodChar_apply, map_pow, hs ζ hζ.pow_eq_one]

theorem fix_sqrt_int [IsAlgClosure ℚ Ω] (hl : l ≠ 2) {A : ValuationSubring Ω} (hA : OverL l A) {s : G ℚ Ω}
    (hs : s ∈ Ine (F := ℚ) A) (hmu : ∀ ζ : Ω, ζ ^ l = 1 → s ζ = ζ) :
    ∀ (N : ℤ) (α : Ω), α ^ 2 = N → s α = α := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  intro N
  induction hn : N.natAbs using Nat.strong_induction_on generalizing N with
  | _ n ih =>
  intro α hα
  by_cases h0 : N = 0
  · subst h0
    have : α = 0 := pow_eq_zero_iff two_ne_zero |>.1 (by simpa using hα)
    rw [this, map_zero]
  by_cases hd : (l : ℤ) ∣ N
  · obtain ⟨N1, rfl⟩ := hd
    obtain ⟨Gs, c, hc, hG, hsG⟩ := gauss_fix hl s hmu
    have hc0 : (c : Ω) ≠ 0 := by
      rintro h
      have : c = 0 := by exact_mod_cast h
      rw [this] at hc
      norm_num at hc
    have hl0 : (l : Ω) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
    have hG0 : Gs ≠ 0 := by
      rintro h
      rw [h] at hG
      push_cast at hG
      exact mul_ne_zero hc0 hl0 (by rw [← hG]; ring)
    have hc' : (c : Ω) ^ 2 = 1 := by exact_mod_cast hc
    have hβ : (α / Gs) ^ 2 = ((c * N1 : ℤ) : Ω) := by
      rw [div_pow, hα, hG]
      push_cast
      rw [div_eq_iff (mul_ne_zero hc0 hl0)]
      linear_combination (-(l : Ω) * N1) * hc'
    have hcabs : c.natAbs = 1 := by
      have h1 : (c ^ 2).natAbs = 1 := by rw [hc]; rfl
      rw [Int.natAbs_pow] at h1
      exact (pow_eq_one_iff.1 h1).resolve_right two_ne_zero
    have hN1 : N1 ≠ 0 := by rintro rfl; exact h0 (mul_zero _)
    have hlt : (c * N1).natAbs < n := by
      rw [← hn, Int.natAbs_mul, Int.natAbs_mul, hcabs, one_mul, Int.natAbs_natCast]
      have := Int.natAbs_pos.2 hN1
      have := (Fact.out : l.Prime).one_lt
      nlinarith
    have h1 := ih _ hlt (c * N1) rfl (α / Gs) hβ
    have e : α = α / Gs * Gs := (div_mul_cancel₀ α hG0).symm
    rw [e, map_mul, h1, hsG]
  · exact fix_sqrt_unit hl hA hs N hd α hα

theorem fix_sqrt_rat [IsAlgClosure ℚ Ω] (hl : l ≠ 2) {A : ValuationSubring Ω} (hA : OverL l A) {s : G ℚ Ω}
    (hs : s ∈ Ine (F := ℚ) A) (hmu : ∀ ζ : Ω, ζ ^ l = 1 → s ζ = ζ) (α : Ω) (q : ℚ)
    (hα : α ^ 2 = algebraMap ℚ Ω q) : s α = α := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hden : (q.den : Ω) ≠ 0 := Nat.cast_ne_zero.2 q.den_nz
  have hq : algebraMap ℚ Ω q * (q.den : Ω) = (q.num : Ω) := by
    rw [← map_natCast (algebraMap ℚ Ω), ← map_mul, Rat.mul_den_eq_num, map_intCast]
  have h := fix_sqrt_int hl hA hs hmu (q.num * q.den) (α * q.den) (by
    rw [mul_pow, hα]
    push_cast
    rw [← hq]
    ring)
  rw [map_mul, map_natCast] at h
  exact mul_right_cancel₀ hden h

theorem dt_eq_one [IsAlgClosure ℚ Ω] {W : R2 Ω l} (hcont : Continuous W) (hdet2 : dt W ^ 2 = 1) (s : G ℚ Ω)
    (hfix : ∀ (α : Ω) (q : ℚ), α ^ 2 = algebraMap ℚ Ω q → s α = α) : dt W s = 1 := by
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hval : ∀ g, ((dt W g : (Qbar l)ˣ) : Qbar l) = ((W g : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)).det :=
    fun g => Matrix.GeneralLinearGroup.val_det_apply _
  have hc : Continuous fun g : G ℚ Ω => ((dt W g : (Qbar l)ˣ) : Qbar l) := by
    simp only [hval]
    exact (Units.continuous_val.comp hcont).matrix_det
  have hcl : IsClosed ((dt W).ker : Set (G ℚ Ω)) := by
    have : ((dt W).ker : Set (G ℚ Ω)) = (fun g : G ℚ Ω => ((dt W g : (Qbar l)ˣ) : Qbar l)) ⁻¹' {1} := by
      ext g
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun h => by rw [h, Units.val_one], fun h => Units.ext (by rw [h, Units.val_one])⟩
    rw [this]
    exact isClosed_singleton.preimage hc
  let Hc : ClosedSubgroup (G ℚ Ω) := ⟨(dt W).ker, hcl⟩
  have hpm : ∀ g, dt W g = 1 ∨ dt W g = -1 := by
    intro g
    have h2 : (dt W g) ^ 2 = 1 := by
      have := congrArg (fun f => f g) hdet2
      simpa using this
    have hv : ((dt W g : (Qbar l)ˣ) : Qbar l) * ((dt W g : (Qbar l)ˣ) : Qbar l) = 1 := by
      rw [← Units.val_mul, ← pow_two, h2, Units.val_one]
    rcases mul_self_eq_one_iff.1 hv with h | h
    · exact Or.inl (Units.ext (by rw [h, Units.val_one]))
    · exact Or.inr (Units.ext (by rw [h, Units.val_neg, Units.val_one]))
  have hsub : s ∈ (IntermediateField.fixedField (Hc : Subgroup (G ℚ Ω))).fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    rw [IntermediateField.mem_fixedField_iff] at hx
    have hsame : ∀ g1 g2 : G ℚ Ω, dt W g1 = dt W g2 → g1 x = g2 x := by
      intro g1 g2 h
      have hm : g2⁻¹ * g1 ∈ (Hc : Subgroup (G ℚ Ω)) := by
        show g2⁻¹ * g1 ∈ (dt W).ker
        rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
      have h1 := hx _ hm
      calc g1 x = g2 ((g2⁻¹ * g1) x) := by
            rw [AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]
        _ = g2 x := by rw [h1]
    rcases hpm s with h1 | h1
    · exact hx s (show s ∈ (dt W).ker from h1)
    have hs2 : (s * s) x = x := by
      rw [hsame (s * s) 1 (by rw [map_mul, h1, map_one]; simp)]
      rfl
    have hsα : s (x - s x) = -(x - s x) := by
      rw [map_sub, ← AlgEquiv.mul_apply, hs2]
      ring
    have hgα : ∀ g : G ℚ Ω, (g (x - s x)) ^ 2 = (x - s x) ^ 2 := by
      intro g
      rw [map_sub, ← AlgEquiv.mul_apply]
      rcases hpm g with h2 | h2
      · rw [hsame g 1 (by rw [h2, map_one]), hsame (g * s) s (by rw [map_mul, h2, one_mul])]
        rfl
      · rw [hsame g s (by rw [h2, h1]), hsame (g * s) 1 (by rw [map_mul, h2, h1, map_one]; simp)]
        show (s x - x) ^ 2 = (x - s x) ^ 2
        ring
    obtain ⟨q, hq⟩ : ∃ q : ℚ, (x - s x) ^ 2 = algebraMap ℚ Ω q := by
      have hmem : (x - s x) ^ 2 ∈ IntermediateField.fixedField (⊥ : IntermediateField ℚ Ω).fixingSubgroup := by
        rw [IntermediateField.mem_fixedField_iff]
        intro f _
        rw [map_pow]
        exact hgα f
      rw [InfiniteGalois.fixedField_fixingSubgroup, IntermediateField.mem_bot] at hmem
      obtain ⟨q, hq⟩ := hmem
      exact ⟨q, hq.symm⟩
    have h3 := hfix _ q hq
    rw [hsα] at h3
    have h4 : (2 : Ω) * (x - s x) = 0 := by linear_combination -h3
    have h5 := (mul_eq_zero.1 h4).resolve_left two_ne_zero
    exact (sub_eq_zero.1 h5).symm
  rw [InfiniteGalois.fixingSubgroup_fixedField Hc] at hsub
  exact hsub

end GlobalTheory.QuotInertia

open GlobalTheory.QuotInertia in

theorem GlobalTheory.quot_eq_one_of_cycBar_eq_one : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (ι : Qbar l ≃+* ℂ) (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l) (g : Newform (2 * e + 1)),
    Nf e S A W → SrcUr ι e A W g → ∀ s ∈ Ine (F := ℚ) A, cycBar ℚ Ω l s = 1 → mat W s 1 1 = 1 := by
  intro l _ Ω _ _ _ ι e S A W g hNf hSrc s hs hc
  obtain ⟨-, -, χ, hχ, -, hI⟩ := hSrc
  have hmu := fix_mu s hc
  have hχs : χ s = 1 := hχ s hmu
  have hdt := dt_eq_one hNf.cont hNf.det2 s (fun α q hq => fix_sqrt_rat hNf.l_odd hNf.atL hs hmu α q hq)
  have h := hI s hs
  rw [hc, hχs, hdt] at h
  simpa using h

end
