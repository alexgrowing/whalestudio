import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardKilledByIdealModIntEqAbsNormPowStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.HTTorsCount

theorem absNorm_pos_coprime {K : Type} [Field K] [NumberField K] (p : ℕ) [hp : Fact p.Prime]
    (𝔟 : Ideal (𝓞 K)) (h : 𝔟 ⊔ Ideal.span {(p : 𝓞 K)} = ⊤) :
    0 < Ideal.absNorm 𝔟 ∧ (Ideal.absNorm 𝔟).Coprime p := by
  obtain ⟨β, hβ, z, hz, hsum⟩ := Submodule.mem_sup.1 (h ▸ Submodule.mem_top (x := (1 : 𝓞 K)))
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hz
  have hpos : 0 < Ideal.absNorm 𝔟 := by
    rw [Nat.pos_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
    rintro rfl
    rw [Submodule.mem_bot] at hβ
    subst hβ
    rw [zero_add, _root_.mul_comm] at hsum
    have hu : IsUnit (p : 𝓞 K) := isUnit_iff_exists_inv.2 ⟨y, hsum⟩
    have e : (p : 𝓞 K) = algebraMap ℤ (𝓞 K) (p : ℤ) := by simp
    have hn := hu.map (Algebra.norm ℤ (S := 𝓞 K))
    rw [e, Algebra.norm_algebraMap, Int.isUnit_iff_natAbs_eq, Int.natAbs_pow, Int.natAbs_natCast] at hn
    rcases Nat.pow_eq_one.1 hn with h1 | h1
    · exact hp.out.one_lt.ne' h1
    · exact (Module.finrank_pos (R := ℤ) (M := 𝓞 K)).ne' h1
  refine ⟨hpos, ?_⟩
  refine (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp.out).2 fun hd => ?_))
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hd hpos
  have : Finite (𝓞 K ⧸ 𝔟) := Nat.finite_of_card_ne_zero hpos.ne'
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' p hd
  have hpx : (p : 𝓞 K ⧸ 𝔟) * x = 0 := by rw [← nsmul_eq_mul, ← hx, addOrderOf_nsmul_eq_zero]
  have h1 : Ideal.Quotient.mk 𝔟 y * (p : 𝓞 K ⧸ 𝔟) = 1 := by
    have := congrArg (Ideal.Quotient.mk 𝔟) hsum
    rwa [map_add, Ideal.Quotient.eq_zero_iff_mem.2 hβ, zero_add, map_mul, map_natCast, map_one] at this
  have hx0 : x = 0 := by
    calc x = (Ideal.Quotient.mk 𝔟 y * (p : 𝓞 K ⧸ 𝔟)) * x := by rw [h1, _root_.one_mul]
      _ = 0 := by rw [_root_.mul_assoc, hpx, mul_zero]
  rw [hx0, addOrderOf_zero] at hx
  exact hp.out.one_lt.ne hx

theorem card_killedBy_eq_absNorm_pow : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : GlobalTheory.UPel.HT.Obj b N s) (𝔟 : Ideal (𝓞 D.F)), 𝔟 ⊔ Ideal.span {(p : 𝓞 D.F)} = ⊤ → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S), Nat.card {y : Over.mk t ⟶ o.A // GlobalTheory.IwLevel.KilledBy (GlobalTheory.IwLevel.htAct o) (𝔟.map (algebraMap (𝓞 D.F) D.O)) y} = Ideal.absNorm 𝔟 ^ (D.m * D.n) := by
  intro p _ D R _ b N S s o 𝔟 h𝔟 k _ _ t
  obtain ⟨hcpos, hcop⟩ := absNorm_pos_coprime p 𝔟 h𝔟
  obtain ⟨β, hβ⟩ : ∃ β : R →+* k, spMap β = t ≫ s := ⟨(Spec.preimage (t ≫ s)).hom, Spec.map_preimage _⟩
  obtain ⟨I, -⟩ := o.geom k t β hβ.symm
  letI : Module (𝓞 D.F) D.La := Module.compHom D.La (algebraMap (𝓞 D.F) D.O)
  have hsmul : ∀ (a : 𝓞 D.F) (x : D.La), a • x = (algebraMap (𝓞 D.F) D.O a) • x := fun _ _ => rfl
  have hcnt := GlobalTheory.T.card_killed_by_ideal_mod_int_eq_absNorm_pow D.F D.La D.freeLa D.finLa (D.m * D.n) D.rankLa 𝔟 (Ideal.absNorm 𝔟) hcpos
    (Ideal.absNorm_mem 𝔟)
  rw [← hcnt]
  set c := Ideal.absNorm 𝔟 with hc
  set P : Submodule (𝓞 D.F) D.La := Ideal.span {(c : 𝓞 D.F)} • (⊤ : Submodule (𝓞 D.F) D.La) with hP
  have hmemP : ∀ x, x ∈ P ↔ ∃ y, x = c • y := by
    intro x
    rw [hP, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨y, -, rfl⟩
      exact ⟨y, by rw [hsmul, map_natCast, Nat.cast_smul_eq_nsmul]⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, Submodule.mem_top, by rw [hsmul, map_natCast, Nat.cast_smul_eq_nsmul]⟩
  let g : D.La → (Over.mk t ⟶ o.A) := I.ev c
  have hker : ∀ x, g x = 1 ↔ x ∈ P := fun x => by rw [hmemP]; exact I.ker c hcpos hcop x
  have hsub : ∀ x y, g (x - y) = g x * (g y)⁻¹ := fun x y =>
    eq_mul_inv_of_mul_eq (by rw [← I.add, sub_add_cancel])
  have hlin : ∀ (a : 𝓞 D.F) x, g (a • x) = g x ≫ o.act.act (algebraMap (𝓞 D.F) D.O a) := fun a x => by
    rw [hsmul]; exact I.lin c _ x
  have hmap : 𝔟.map (algebraMap (𝓞 D.F) D.O) = Ideal.span (algebraMap (𝓞 D.F) D.O '' 𝔟) := rfl
  let f : D.La ⧸ P → (Over.mk t ⟶ o.A) := fun z => Quotient.liftOn' z g (fun x y hxy => by
    have h1 : g (x - y) = 1 := (hker _).2 ((Submodule.quotientRel_def P).1 hxy)
    rw [hsub] at h1
    exact mul_inv_eq_one.1 h1)
  have hf : ∀ x, f (Submodule.Quotient.mk x) = g x := fun _ => rfl
  have hkill : ∀ x, (∀ a ∈ 𝔟, a • (Submodule.Quotient.mk x : D.La ⧸ P) = 0) ↔
      GlobalTheory.IwLevel.KilledBy (GlobalTheory.IwLevel.htAct o) (𝔟.map (algebraMap (𝓞 D.F) D.O)) (g x) := by
    intro x
    rw [hmap, GlobalTheory.IwLevel.killedBy_span]
    constructor
    · rintro h _ ⟨a, ha, rfl⟩
      rw [GlobalTheory.IwLevel.htAct_act, ← hlin, hker, ← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
      exact h a ha
    · intro h a ha
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, ← hker, hlin]
      have := h _ ⟨a, ha, rfl⟩
      rwa [GlobalTheory.IwLevel.htAct_act] at this
  have hpow : ∀ (q : Over.mk t ⟶ o.A) (n : ℕ), q ≫ o.act.act (n : D.O) = q ^ n := by
    intro q n
    have h0 : o.act.act 0 = 1 := by
      have := o.act.add 0 0
      rw [add_zero] at this
      exact left_eq_mul.1 this
    induction n with
    | zero => rw [Nat.cast_zero, h0, pow_zero, MonObj.comp_one]
    | succ n ih => rw [Nat.cast_succ, o.act.add, o.act.one, MonObj.comp_mul, ih, Category.comp_id, pow_succ]
  let F : {z : D.La ⧸ P // ∀ a ∈ 𝔟, a • z = 0} →
      {y : Over.mk t ⟶ o.A // GlobalTheory.IwLevel.KilledBy (GlobalTheory.IwLevel.htAct o) (𝔟.map (algebraMap (𝓞 D.F) D.O)) y} :=
    fun z => ⟨f z.1, by
      obtain ⟨z, hz⟩ := z
      induction z using Submodule.Quotient.induction_on with
      | H x => exact (hkill x).1 hz⟩
  refine (Nat.card_eq_of_bijective F ⟨?_, ?_⟩).symm
  · rintro ⟨z₁, h₁⟩ ⟨z₂, h₂⟩ h
    have h' : f z₁ = f z₂ := congrArg Subtype.val h
    induction z₁ using Submodule.Quotient.induction_on with
    | H x =>
    induction z₂ using Submodule.Quotient.induction_on with
    | H y =>
    rw [hf, hf] at h'
    apply Subtype.ext
    change Submodule.Quotient.mk x = Submodule.Quotient.mk y
    rw [Submodule.Quotient.eq, ← hker, hsub, h', mul_inv_cancel]
  · rintro ⟨q, hq⟩
    have hq1 : q ^ c = 1 := by
      rw [← hpow, ← map_natCast (algebraMap (𝓞 D.F) D.O)]
      have := hq _ (Ideal.mem_map_of_mem (algebraMap (𝓞 D.F) D.O) (Ideal.absNorm_mem 𝔟))
      rwa [GlobalTheory.IwLevel.htAct_act] at this
    obtain ⟨x, hx⟩ := (I.onto c hcpos hcop q).1 hq1
    refine ⟨⟨Submodule.Quotient.mk x, (hkill x).2 (by change GlobalTheory.IwLevel.KilledBy _ _ (I.ev c x); rw [hx]; exact hq)⟩, Subtype.ext ?_⟩
    exact hx

end GlobalTheory.HTTorsCount
