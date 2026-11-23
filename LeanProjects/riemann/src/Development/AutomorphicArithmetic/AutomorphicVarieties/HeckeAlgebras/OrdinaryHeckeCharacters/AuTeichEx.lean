import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.Classical
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.DecompU
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PartU
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DvrFacts
import Mathlib.RingTheory.Teichmuller

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

private theorem card_residueField_sub_one_eq_neg_one {O : Type} [CommRing O] [IsLocalRing O] [Fintype (ResidueField O)] :
    ((Fintype.card (ResidueField O) - 1 : ℕ) : ResidueField O) = -1 := by
  have h1 : 1 ≤ Fintype.card (ResidueField O) := Fintype.card_pos
  rw [Nat.cast_sub h1, FiniteField.cast_card_eq_zero]
  simp

private theorem teichmuller_eq_of_residue_eq {O : Type} [CommRing O] [IsLocalRing O] [Fintype (ResidueField O)] (a b : O)
    (ha : a ^ (Fintype.card (ResidueField O) - 1) = 1) (hb : b ^ (Fintype.card (ResidueField O) - 1) = 1)
    (hab : residue O a = residue O b) : a = b := by
  obtain ⟨N, hN⟩ : ∃ N, N = Fintype.card (ResidueField O) - 1 := ⟨_, rfl⟩
  rw [← hN] at ha hb
  have hN0 : N ≠ 0 := by
    have := Fintype.one_lt_card (α := ResidueField O)
    omega
  have hra : residue O a ≠ 0 := by
    intro h0
    have h := congrArg (residue O) ha
    rw [map_pow, h0, map_one, zero_pow hN0] at h
    exact zero_ne_one h
  have key := geom_sum₂_mul a b N
  rw [ha, hb, sub_self] at key
  have hu : IsUnit (∑ i ∈ Finset.range N, a ^ i * b ^ (N - 1 - i)) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_sum]
    simp only [map_mul, map_pow, ← hab]
    have hterm : ∀ i ∈ Finset.range N,
        residue O a ^ i * residue O a ^ (N - 1 - i) = residue O a ^ (N - 1) := by
      intro i hi
      rw [← pow_add]
      congr 1
      have := Finset.mem_range.mp hi
      omega
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul, hN, card_residueField_sub_one_eq_neg_one]
    exact mul_ne_zero (neg_ne_zero.mpr one_ne_zero) (pow_ne_zero _ hra)
  exact sub_eq_zero.mp ((hu.mul_right_eq_zero).mp key)

private theorem exists_teichmuller_lift' {O : Type} [CommRing O] [IsLocalRing O] [IsAdicComplete (maximalIdeal O) O]
    [Fintype (ResidueField O)] (u : ResidueField O) (hu : u ≠ 0) :
    ∃ a : O, a ^ (Fintype.card (ResidueField O) - 1) = 1 ∧ residue O a = u := by
  obtain ⟨N, hN⟩ : ∃ N, N = Fintype.card (ResidueField O) - 1 := ⟨_, rfl⟩
  rw [← hN]
  have hN0 : N ≠ 0 := by
    have := Fintype.one_lt_card (α := ResidueField O)
    omega
  obtain ⟨a₀, rfl⟩ := IsLocalRing.residue_surjective u
  haveI := IsAdicComplete.henselianRing O (maximalIdeal O)
  have h1 : eval a₀ (X ^ N - C 1) ∈ maximalIdeal O := by
    rw [← IsLocalRing.residue_eq_zero_iff]
    simp only [eval_sub, eval_pow, eval_X, eval_C, eval_one, map_sub, map_pow, map_one]
    rw [hN, FiniteField.pow_card_sub_one_eq_one _ hu, sub_self]
  have h2 : IsUnit (Ideal.Quotient.mk (maximalIdeal O) (eval a₀ (derivative (X ^ N - C 1)))) := by
    change IsUnit (residue O _)
    rw [isUnit_iff_ne_zero]
    simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, eval_mul, eval_C, eval_pow, eval_X,
      eval_natCast, map_mul, map_pow, map_natCast]
    rw [hN, card_residueField_sub_one_eq_neg_one]
    exact mul_ne_zero (neg_ne_zero.mpr one_ne_zero) (pow_ne_zero _ hu)
  obtain ⟨a, hroot, hmem⟩ := HenselianRing.is_henselian (I := maximalIdeal O) (X ^ N - C 1)
    (monic_X_pow_sub_C 1 hN0) a₀ h1 h2
  refine ⟨a, ?_, ?_⟩
  · have h : eval a (X ^ N - C 1) = 0 := hroot
    simp only [eval_sub, eval_pow, eval_X, eval_C, eval_one] at h
    exact sub_eq_zero.mp h
  · exact Ideal.Quotient.eq.mpr hmem

private theorem au_teich_ex (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] [CharP (ResidueField O) l] :
    ∃ τ : ResidueField O →* O, ∀ x, residue O (τ x) = x := by
  letI := Fintype.ofFinite (ResidueField O)
  classical
  have ex := fun (x : ResidueField O) (hx : x ≠ 0) => exists_teichmuller_lift' (O := O) x hx
  let f : ResidueField O → O := fun x => if hx : x = 0 then 0 else Classical.choose (ex x hx)
  have hf : ∀ x, x ≠ 0 → f x ^ (Fintype.card (ResidueField O) - 1) = 1 ∧ residue O (f x) = x := by
    intro x hx
    simp only [f, dif_neg hx]
    exact Classical.choose_spec (ex x hx)
  have hf0 : f 0 = 0 := by simp [f]
  have hres : ∀ x, residue O (f x) = x := by
    intro x
    by_cases hx : x = 0
    · rw [hx, hf0, map_zero]
    · exact (hf x hx).2
  refine ⟨{ toFun := f, map_one' := ?_, map_mul' := ?_ }, hres⟩
  · apply teichmuller_eq_of_residue_eq
    · exact (hf 1 one_ne_zero).1
    · exact one_pow _
    · rw [(hf 1 one_ne_zero).2, map_one]
  · intro x y
    by_cases hx : x = 0
    · simp [hx, hf0]
    by_cases hy : y = 0
    · simp [hy, hf0]
    apply teichmuller_eq_of_residue_eq
    · exact (hf _ (mul_ne_zero hx hy)).1
    · rw [mul_pow, (hf x hx).1, (hf y hy).1, one_mul]
    · rw [(hf _ (mul_ne_zero hx hy)).2, map_mul, (hf x hx).2, (hf y hy).2]

private theorem au_isTeich {l : ℕ} [hl : Fact l.Prime] {F : W.GFrame l} (c : Coef l) {n : ℕ} (r : Resid F c.O n) :
    ∃ t, r.IsTeich t := by
  haveI := c.dvr
  haveI := c.fin
  obtain ⟨hc, hfin, hlm, -⟩ := abelian₂.dvr_finite l c.O
  haveI := hc
  haveI := hfin
  haveI : CharP (ResidueField c.O) l := by
    rw [CharP.charP_iff_prime_eq_zero hl.out]
    have := (IsLocalRing.residue_eq_zero_iff _).mpr hlm
    simpa using this
  obtain ⟨τ, hτ⟩ := au_teich_ex l c.O
  refine ⟨fun i => (Units.map τ).comp (r.chib i), fun i g => ⟨?_, ?_⟩⟩
  · simp [hτ]
  · rw [MonoidHom.comp_apply, ← map_pow]
    have hp : (r.chib i g) ^ (Nat.card (ResidueField c.O) - 1) = 1 := by
      letI := Fintype.ofFinite (ResidueField c.O)
      ext
      rw [Units.val_pow_eq_pow_val, Units.val_one, Nat.card_eq_fintype_card]
      exact FiniteField.pow_card_sub_one_eq_one _ (r.chib i g).ne_zero
    rw [hp, map_one]

private theorem au_open {G O : Type} [Group G] [TopologicalSpace G] [CommRing O] {m : ℕ} (f : O →+* ℂ) (hf : Function.Injective f)
    (τ : G →* GL (Fin m) O) (h : IsOpen (((Matrix.GeneralLinearGroup.map f).comp τ).ker : Set G)) : IsOpen (τ.ker : Set G) := by
  have hinj : Function.Injective (Matrix.GeneralLinearGroup.map f : GL (Fin m) O →* GL (Fin m) ℂ) := by
    intro A B hAB
    ext i j
    have h := congrArg (fun M : GL (Fin m) ℂ => (M : Matrix (Fin m) (Fin m) ℂ) i j) hAB
    simp at h
    exact hf h
  have hk : ((Matrix.GeneralLinearGroup.map f).comp τ).ker = τ.ker := by
    ext g
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply]
    constructor
    · intro h
      exact hinj (by rw [h, map_one])
    · intro h
      rw [h, map_one]
  rwa [hk] at h

theorem UpperTheory.V.Hi.autU :
    Af.HypothesesH → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ), ∀ (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O), TypeFor r ι τ₀ →
    (hset Q τ₀).Aut ι (PU r ι) := by
  intro hP l _ L Ω _ _ _ _ _ _ s n hn V Q c r ι m τ₀ hτ lam _ d ξ hξ F hF hK hI
  obtain ⟨e, he⟩ := hξ
  obtain ⟨t, ht⟩ := au_isTeich c r
  have hop : IsOpen (τ₀.ker : Set (KT n (wt s))) :=
    au_open _ (ι.injective.comp Subtype.val_injective) τ₀ (hτ t ht).1
  have h1 := decompU l L Ω s n hn V Q c m τ₀ ι hop lam d e ξ he F hF hK hI
  refine SetLike.le_def.1 (iSup_le fun σ => ?_) h1
  by_cases h0 : YOf Q ι τ₀ e ξ σ.1 = ⊥
  · rw [h0]; exact bot_le
  · obtain ⟨Y, hY, hPU, -⟩ := partU hP l L Ω s n hn V Q c r ι m τ₀ hτ lam d e ξ he σ.1 σ.2 h0
    rw [← hY]
    exact le_iSup (fun Y : {Y : (hset Q τ₀).Part ι lam ξ // PU r ι lam Y.r} => Y.1.Y) ⟨Y, hPU⟩
