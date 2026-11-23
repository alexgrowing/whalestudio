import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.ChainRows
import Development.AutomorphicSpectrum.Definitions.NonGaloisLines.TopLine
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.OrthogonalFreeOfPerfectAltZmod
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatCardAddMonoidHomZmodLe
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual

namespace GlobalTheory.CompanionTheory.LocDual.GenChar

theorem exists_addHom_zmod_ne_zero {N : ℕ} [NeZero N] {A : Type} [AddCommGroup A]
    (hA : ∀ a : A, N • a = 0) {q : A} (hq : q ≠ 0) : ∃ f : A →+ ZMod N, f q ≠ 0 := by
  obtain ⟨c, hc⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero hq
  let c' : A →+ AddCircle (1 : ℚ) := c
  have hc' : c' q ≠ 0 := hc
  have hN : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  let g : ℤ →+ AddCircle (1 : ℚ) :=
    (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ))).comp
      ((AddMonoidHom.mulRight ((N : ℚ)⁻¹)).comp (Int.castAddHom ℚ))
  have hg : ∀ z : ℤ, g z = QuotientAddGroup.mk ((z : ℚ) * (N : ℚ)⁻¹) := fun z => rfl
  have hgN : g N = 0 := by
    rw [hg, Int.cast_natCast, mul_inv_cancel₀ hN]
    exact (QuotientAddGroup.eq_zero_iff _).2 (AddSubgroup.mem_zmultiples _)
  let ι : ZMod N →+ AddCircle (1 : ℚ) := ZMod.lift N ⟨g, hgN⟩
  have hι : ∀ z : ℤ, ι z = g z := fun z => ZMod.lift_coe N ⟨g, hgN⟩ z
  have hinj : Function.Injective ι := by
    refine (injective_iff_map_eq_zero ι).2 fun m hm => ?_
    obtain ⟨z, rfl⟩ := ZMod.intCast_surjective m
    rw [hι, hg] at hm
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 ((QuotientAddGroup.eq_zero_iff _).1 hm)
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    refine ⟨k, ?_⟩
    rw [zsmul_eq_mul, mul_one] at hk
    have h2 : (z : ℚ) = (N : ℚ) * k := by
      field_simp at hk
      linarith
    exact_mod_cast h2
  have hmem : ∀ a : A, c' a ∈ ι.range := by
    intro a
    obtain ⟨r, hr⟩ := QuotientAddGroup.mk_surjective (c' a)
    have h1 : N • c' a = 0 := by rw [← map_nsmul, hA, map_zero]
    have h0 : (N • r : ℚ) ∈ AddSubgroup.zmultiples (1 : ℚ) := by
      rw [← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.mk_nsmul, hr]
      exact h1
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 h0
    refine AddMonoidHom.mem_range.2 ⟨(k : ZMod N), ?_⟩
    rw [hι, hg, ← hr]
    congr 1
    rw [zsmul_eq_mul, mul_one, nsmul_eq_mul] at hk
    rw [hk]
    field_simp
  refine ⟨(AddMonoidHom.ofInjective hinj).symm.toAddMonoidHom.comp
    (AddMonoidHom.codRestrict c' ι.range hmem), ?_⟩
  intro h0
  apply hc'
  have h1 : AddMonoidHom.codRestrict c' ι.range hmem q = 0 := by
    have h3 := congrArg (AddMonoidHom.ofInjective hinj) h0
    simpa using h3
  have h2 := congrArg Subtype.val h1
  simpa using h2

theorem exists_mul_eq_socle {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {ϖ : O} (hϖ : Irreducible ϖ) (s : ℕ) {x : O ⧸ Ideal.span {ϖ ^ (s + 1)}} (hx : x ≠ 0) :
    ∃ o, o * x = Ideal.Quotient.mk (Ideal.span {ϖ ^ (s + 1)}) (ϖ ^ s) := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hy : y ≠ 0 := by
    rintro rfl
    exact hx (map_zero _)
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hϖ
  have hn : n ≤ s := by
    by_contra hlt
    apply hx
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, hu]
    exact Dvd.dvd.mul_left (pow_dvd_pow ϖ (Nat.succ_le_of_lt (not_le.1 hlt))) _
  refine ⟨Ideal.Quotient.mk _ (↑u⁻¹ * ϖ ^ (s - n)), ?_⟩
  rw [← map_mul, hu]
  congr 1
  calc ↑u⁻¹ * ϖ ^ (s - n) * (↑u * ϖ ^ n) = (↑u⁻¹ * ↑u) * (ϖ ^ (s - n) * ϖ ^ n) := by ring
    _ = ϖ ^ s := by rw [Units.inv_mul, one_mul, ← pow_add, Nat.sub_add_cancel hn]

theorem socle_ne_zero {O : Type} [CommRing O] [IsDomain O] {ϖ : O} (hϖ : Irreducible ϖ) (s : ℕ) :
    Ideal.Quotient.mk (Ideal.span {ϖ ^ (s + 1)}) (ϖ ^ s) ≠ 0 := by
  rw [Ne, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton,
    pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit]
  omega

theorem exists_generating_character : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (r N : ℕ), 0 < N → Finite (O ⧸ Ideal.span {ϖ ^ r}) → ((N : O) ∈ Ideal.span {ϖ ^ r}) → ∃ ψ₀ : (O ⧸ Ideal.span {ϖ ^ r}) →+ ZMod N, (∀ x, (∀ o, ψ₀ (o * x) = 0) → x = 0) ∧ ∀ ψ : (O ⧸ Ideal.span {ϖ ^ r}) →+ ZMod N, ∃ o, ∀ x, ψ x = ψ₀ (o * x) := by
  intro O _ _ _ ϖ hϖ r N hN hfin hNmem
  haveI : NeZero N := ⟨by omega⟩
  have htors : ∀ a : O ⧸ Ideal.span {ϖ ^ r}, N • a = 0 := by
    intro a
    have hN0 : ((N : O ⧸ Ideal.span {ϖ ^ r})) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {ϖ ^ r}))]
      exact Ideal.Quotient.eq_zero_iff_mem.2 hNmem
    rw [nsmul_eq_mul, hN0, zero_mul]
  have key : ∃ ψ₀ : (O ⧸ Ideal.span {ϖ ^ r}) →+ ZMod N,
      ∀ x, (∀ o, ψ₀ (o * x) = 0) → x = 0 := by
    cases r with
    | zero =>
      refine ⟨0, fun x _ => ?_⟩
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [Ideal.Quotient.eq_zero_iff_mem, pow_zero, Ideal.span_singleton_one]
      exact Submodule.mem_top
    | succ s =>
      obtain ⟨ψ₀, hψ₀⟩ := exists_addHom_zmod_ne_zero htors (socle_ne_zero hϖ s)
      refine ⟨ψ₀, fun x hx => ?_⟩
      by_contra hne
      obtain ⟨o, ho⟩ := exists_mul_eq_socle hϖ s hne
      have h5 := hx o
      rw [ho] at h5
      exact hψ₀ h5
  obtain ⟨ψ₀, hψ₀⟩ := key
  refine ⟨ψ₀, hψ₀, ?_⟩
  let Φ : (O ⧸ Ideal.span {ϖ ^ r}) → ((O ⧸ Ideal.span {ϖ ^ r}) →+ ZMod N) :=
    fun o => ψ₀.comp (AddMonoidHom.mulLeft o)
  have hinj : Function.Injective Φ := by
    intro a b hab
    have h0 : ∀ x, ψ₀ ((a - b) * x) = 0 := by
      intro x
      have h6 : ψ₀ (a * x) = ψ₀ (b * x) := DFunLike.congr_fun hab x
      rw [sub_mul, map_sub, h6, sub_self]
    have h7 : a - b = 0 := hψ₀ (a - b) (fun o => by rw [mul_comm]; exact h0 o)
    exact sub_eq_zero.1 h7
  haveI : Finite ((O ⧸ Ideal.span {ϖ ^ r}) →+ ZMod N) :=
    Finite.of_injective (fun f : (O ⧸ Ideal.span {ϖ ^ r}) →+ ZMod N =>
      (f : (O ⧸ Ideal.span {ϖ ^ r}) → ZMod N)) DFunLike.coe_injective
  have hbij := hinj.bijective_of_nat_card_le (GlobalTheory.natCard_addMonoidHom_zmod_le N _)
  intro ψ
  obtain ⟨o, ho⟩ := hbij.2 ψ
  exact ⟨o, fun x => by rw [← ho]; rfl⟩

end GlobalTheory.CompanionTheory.LocDual.GenChar
