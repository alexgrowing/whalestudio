import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SimultaneousEigenvectors.SimEig
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.CoefFieldEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.Thorne
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.CocycleCoefficients.PetAdj
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.CocycleCoefficients.PetHerm
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.HeckeEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.FinDim

noncomputable section SlopeTestRemainingChoices

open CongruenceSubgroup UpperHalfPlane UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Lit
open scoped MatrixGroups ModularForm ComplexConjugate

namespace UpperTheory.V.Lit.KT.EigenformSpan

private theorem one_mem_per (N : ℕ) :
    (1 : ℝ) ∈ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (Gamma1 N)).strictPeriods := by
  rw [strictPeriods_Gamma1]; exact AddSubgroup.mem_zmultiples 1

private theorem coef_smul {N : ℕ} {k : ℤ} (c : ℂ) (f : CuspForm (Gamma1 N) k) (n : ℕ) :
    coef (c • f : CuspForm (Gamma1 N) k) n = c * coef f n := by
  unfold coef
  rw [show ((c • f : CuspForm (Gamma1 N) k) : ℍ → ℂ) = c • (f : ℍ → ℂ) from rfl,
    ModularForm.qExpansion_smul one_pos (one_mem_per N) c f]
  simp

private theorem coef_add {N : ℕ} {k : ℤ} (f g : CuspForm (Gamma1 N) k) (n : ℕ) :
    coef (f + g : CuspForm (Gamma1 N) k) n = coef f n + coef g n := by
  unfold coef
  rw [← map_add]
  congr 1
  exact ModularForm.qExpansion_add one_pos (one_mem_per N) f g

private def fT {K : Type} [Field K] (p : ℕ) (e : K) : Module.End K (ℕ → K) where
  toFun c n := c (p * n) + e * (if p ∣ n then c (n / p) else 0)
  map_add' c d := by
    funext n
    by_cases h : p ∣ n <;> simp [h] <;> ring
  map_smul' a c := by
    funext n
    by_cases h : p ∣ n <;> simp [h] <;> ring

private theorem fT_apply {K : Type} [Field K] (p : ℕ) (e : K) (c : ℕ → K) (n : ℕ) :
    fT p e c n = c (p * n) + e * (if p ∣ n then c (n / p) else 0) := rfl

private theorem fT_comm {K : Type} [Field K] {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (e e' : K)
    (c : ℕ → K) : fT p e (fT q e' c) = fT q e' (fT p e c) := by
  have hc : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 hpq
  funext n
  simp only [fT_apply]
  have h1 : q ∣ p * n ↔ q ∣ n := hc.symm.dvd_mul_left
  have h2 : p ∣ q * n ↔ p ∣ n := hc.dvd_mul_left
  by_cases a : p ∣ n <;> by_cases b : q ∣ n
  · obtain ⟨m, rfl⟩ : p * q ∣ n := hc.mul_dvd_of_dvd_of_dvd a b
    have e1 : p * q * m / p = q * m := by rw [mul_assoc, Nat.mul_div_cancel_left _ hp.pos]
    have e2 : p * q * m / q = p * m := by rw [mul_comm p q, mul_assoc, Nat.mul_div_cancel_left _ hq.pos]
    simp only [h1, h2, a, b, if_true, e1, e2, dvd_mul_right, Nat.mul_div_cancel_left _ hp.pos,
      Nat.mul_div_cancel_left _ hq.pos, Nat.mul_div_assoc _ a, Nat.mul_div_assoc _ b, mul_left_comm q p]
    ring
  · have b' : ¬ q ∣ n / p := fun h => b (h.trans (Nat.div_dvd_of_dvd a))
    simp only [h1, h2, a, b, b', if_true, if_false, Nat.mul_div_assoc _ a, mul_left_comm q p]
    ring
  · have a' : ¬ p ∣ n / q := fun h => a (h.trans (Nat.div_dvd_of_dvd b))
    simp only [h1, h2, a, b, a', if_true, if_false, Nat.mul_div_assoc _ b, mul_left_comm q p]
    ring
  · simp only [h1, h2, a, b, if_false, mul_left_comm q p]
    ring

private def chSub (N k : ℕ) (χ : DirichletCharacter ℂ N) : Submodule ℂ (CuspForm (Gamma1 N) (k : ℤ)) where
  carrier := {g | HasChar k χ g}
  add_mem' := by
    intro f g hf hg γ hγ
    rw [show ((f + g : CuspForm (Gamma1 N) (k : ℤ)) : ℍ → ℂ) = (f : ℍ → ℂ) + g from rfl, SlashAction.add_slash,
      hf γ hγ, hg γ hγ, smul_add]
  zero_mem' := by
    intro γ _
    rw [show ((0 : CuspForm (Gamma1 N) (k : ℤ)) : ℍ → ℂ) = 0 from rfl, SlashAction.zero_slash, smul_zero]
  smul_mem' := by
    intro c f hf γ hγ
    rw [show ((c • f : CuspForm (Gamma1 N) (k : ℤ)) : ℍ → ℂ) = c • (f : ℍ → ℂ) from rfl, ModularForm.SL_smul_slash,
      hf γ hγ, smul_comm]

section
open Module
variable {K M : Type} [Field K] [IsAlgClosed K] [AddCommGroup M] [Module K M] [FiniteDimensional K M]

end

private theorem span_eig {M J : Type} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (T : J → Module.End ℂ M)
    (hc : ∀ i j, T i * T j = T j * T i) (B : M → M →ₗ[ℂ] ℂ) (hB : ∀ x y, B y x = conj (B x y))
    (h0 : ∀ x, B x x = 0 → x = 0) (c : J → ℂ) (hadj : ∀ j x y, B x (T j y) = c j * B (T j x) y) :
    Submodule.span ℂ {v : M | ∀ j, ∃ a : ℂ, T j v = a • v} = ⊤ := by
  set S : Set M := {v : M | ∀ j, ∃ a : ℂ, T j v = a • v} with hS
  by_contra hne
  have hlt : Module.finrank ℂ (Submodule.span ℂ S) < Module.finrank ℂ M := Submodule.finrank_lt hne
  let b := Module.finBasis ℂ (Submodule.span ℂ S)
  let L : M →ₗ[ℂ] (Fin (Module.finrank ℂ (Submodule.span ℂ S)) → ℂ) := LinearMap.pi fun i => B (b i).1
  have hker : LinearMap.ker L ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by simpa using hlt)
  obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 hker
  have hyS : ∀ v ∈ S, B v y = 0 := by
    intro v hv
    have h1 : (B y).comp (Submodule.span ℂ S).subtype = 0 := b.ext fun i => by
      have : B (b i).1 y = 0 := congrFun (LinearMap.mem_ker.1 hy) i
      change B y (b i).1 = 0
      rw [hB, this, map_zero]
    have h2 : B y v = 0 := LinearMap.congr_fun h1 ⟨v, Submodule.subset_span hv⟩
    rw [hB, h2, map_zero]
  let U : Submodule ℂ M := ⨅ v : S, LinearMap.ker (B v.1)
  have hU : ∀ x, x ∈ U ↔ ∀ v ∈ S, B v x = 0 := fun x => by
    simp only [U, Submodule.mem_iInf, LinearMap.mem_ker, Subtype.forall]
  obtain ⟨w, hw, hw0, hwe⟩ := UpperTheory.V.LinAlg.simEig T hc _ U rfl ((Submodule.ne_bot_iff U).2 ⟨y, (hU y).2 hyS, hy0⟩) (by
    intro j x hx
    rw [hU] at hx ⊢
    intro v hv
    obtain ⟨a, ha⟩ := hv j
    have h3 : B x v = 0 := by rw [hB, hx v hv, map_zero]
    rw [hadj, ha, hB, map_smul, h3, smul_zero, map_zero, mul_zero])
  exact hw0 (h0 w ((hU w).1 hw w hwe))

private def Phi (N : ℕ) (k : ℤ) : CuspForm (Gamma1 N) k →ₗ[ℂ] (ℕ → ℂ) where
  toFun g n := if n = 0 then 0 else coef g n
  map_add' f g := by
    funext n
    by_cases h : n = 0 <;> simp only [h, if_true, if_false, coef_add, Pi.add_apply, add_zero]
  map_smul' a f := by
    funext n
    by_cases h : n = 0 <;> simp only [h, if_true, if_false, coef_smul, Pi.smul_apply, smul_eq_mul, mul_zero]
    rfl

private theorem Phi_apply (N : ℕ) (k : ℤ) (g : CuspForm (Gamma1 N) k) (n : ℕ) :
    Phi N k g n = if n = 0 then 0 else coef g n := rfl

private theorem fT_Phi (N : ℕ) (k : ℤ) (g : CuspForm (Gamma1 N) k)
    {p : ℕ} (hp : p.Prime) (e : ℂ) {n : ℕ} (hn : 1 ≤ n) :
    fT p e (Phi N k g) n = coef g (p * n) + e * (if p ∣ n then coef g (n / p) else 0) := by
  have h1 : p * n ≠ 0 := mul_ne_zero hp.ne_zero (by omega)
  rw [fT_apply, Phi_apply, if_neg h1]
  by_cases h : p ∣ n
  · have : n / p ≠ 0 := (Nat.div_pos (Nat.le_of_dvd hn h) hp.pos).ne'
    rw [if_pos h, if_pos h, Phi_apply, if_neg this]
  · rw [if_neg h, if_neg h]

private theorem eig_iff (N k : ℕ) (χ : DirichletCharacter ℂ N) (g : CuspForm (Gamma1 N) (k : ℤ)) {p : ℕ} (hp : p.Prime) (c : ℂ) :
    fT p (χ (p : ZMod N) * (p : ℂ) ^ (k - 1)) (Phi N k g) = c • Phi N k g ↔ IsEigAt k χ g p c := by
  constructor
  · intro h n hn
    have := congrFun h n
    rwa [fT_Phi N k g hp _ hn, Pi.smul_apply, Phi_apply, if_neg (show ¬ n = 0 by omega), smul_eq_mul] at this
  · intro h
    funext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [fT_apply, Phi_apply]
    · rw [fT_Phi N k g hp _ hn, Pi.smul_apply, Phi_apply, if_neg hn.ne', smul_eq_mul]
      exact h n hn

private theorem main (M N k : ℕ) (hN : 0 < N) (hNM : N ∣ M) (hk : 1 ≤ k) (χ : DirichletCharacter ℂ N)
    (g : CuspForm (Gamma1 N) (k : ℤ)) (hg : HasChar k χ g) :
    g ∈ Submodule.span ℂ {h : CuspForm (Gamma1 N) (k : ℤ) | HasChar k χ h ∧
      ∃ b : ℕ → ℂ, ∀ p : ℕ, p.Prime → ¬ p ∣ M → IsEigAt k χ h p (b p)} := by
  classical
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI := (finDim N k).1
  have hinj : Function.Injective (Phi N k) := (injective_iff_map_eq_zero _).2 fun f h0 =>
    (finDim N k).2 f fun n hn => by
      have := congrFun h0 n
      rwa [Phi_apply, if_neg (by omega)] at this
  let J := {p : ℕ // p.Prime ∧ ¬ p ∣ M}
  let e : J → ℂ := fun p => χ ((p.1 : ℕ) : ZMod N) * ((p.1 : ℕ) : ℂ) ^ (k - 1)
  have hex := fun (p : J) (f : chSub N k χ) => heckeEx N k hk χ f.1 f.2 p.1 p.2.1
  choose t ht1 ht2 using hex
  have ht : ∀ (p : J) (f : chSub N k χ), Phi N k (t p f) = fT p.1 (e p) (Phi N k f.1) := by
    intro p f
    funext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [fT_apply, Phi_apply]
    · rw [fT_Phi N k f.1 p.2.1 _ hn, Phi_apply, if_neg hn.ne', ht2 p f n hn]
  let T : J → Module.End ℂ (chSub N k χ) := fun p =>
    { toFun := fun f => ⟨t p f, ht1 p f⟩
      map_add' := fun f f' => Subtype.ext (hinj (by
        simp only [Submodule.coe_add, map_add, ht]))
      map_smul' := fun a f => Subtype.ext (hinj (by
        simp only [Submodule.coe_smul, map_smul, ht, RingHom.id_apply])) }
  have hT : ∀ p (f : chSub N k χ), (T p f).1 = t p f := fun _ _ => rfl
  have hc : ∀ p q, T p * T q = T q * T p := by
    intro p q
    by_cases hpq : p = q
    · rw [hpq]
    · ext1 v
      refine Subtype.ext (hinj ?_)
      simp only [Module.End.mul_apply, hT, ht]
      exact fT_comm p.2.1 q.2.1 (fun h => hpq (Subtype.ext h)) _ _ _
  obtain ⟨hadd, hsmul, hherm, hdef⟩ := petHerm N k hN
  let B : chSub N k χ → chSub N k χ →ₗ[ℂ] ℂ := fun f =>
    { toFun := fun f' => pet N k f.1 f'.1
      map_add' := fun x y => hadd f.1 x.1 y.1
      map_smul' := fun a x => hsmul a f.1 x.1 }
  have htop := span_eig T hc B (fun x y => hherm x.1 y.1) (fun x hx => Subtype.ext (hdef x.1 hx))
    (fun p => χ (p.1 : ZMod N)) (fun p x y => petAdj N k hN hk χ p.1 p.2.1 (fun h => p.2.2 (h.trans hNM))
      x.1 y.1 (t p x) (t p y) x.2 y.2 (ht2 p x) (ht2 p y))
  have hmem : (⟨g, hg⟩ : chSub N k χ) ∈ Submodule.span ℂ {v : chSub N k χ | ∀ j, ∃ a : ℂ, T j v = a • v} := by
    rw [htop]; trivial
  have h2 := Submodule.mem_map_of_mem (f := (chSub N k χ).subtype) hmem
  rw [Submodule.map_span] at h2
  refine Submodule.span_mono ?_ h2
  rintro _ ⟨v, hv, rfl⟩
  choose a ha using hv
  refine ⟨v.2, fun p => if h : p.Prime ∧ ¬ p ∣ M then a ⟨p, h⟩ else 0, fun p hp hpM => ?_⟩
  simp only [dif_pos (And.intro hp hpM)]
  refine (eig_iff N k χ v.1 hp _).1 ?_
  have h3 := congrArg (fun x : chSub N k χ => Phi N k x.1) (ha ⟨p, hp, hpM⟩)
  simp only [hT, ht, Submodule.coe_smul, map_smul] at h3
  exact h3

end UpperTheory.V.Lit.KT.EigenformSpan

end SlopeTestRemainingChoices

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.GalOfCusp GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published.Kato UpperTheory.V.Lit CongruenceSubgroup
open scoped Matrix MatrixGroups ModularForm ComplexConjugate

theorem UpperTheory.V.Lit.KT.eigSpan :
    ∀ (M M' k : ℕ), 0 < M → M' ∣ M → 1 ≤ k → ∀ (χ' : DirichletCharacter ℂ M') (g : CuspForm (Gamma1 M') (k : ℤ)), HasChar k χ' g →
    g ∈ Submodule.span ℂ {h : CuspForm (Gamma1 M') (k : ℤ) | HasChar k χ' h ∧ ∃ b : ℕ → ℂ, ∀ p : ℕ, p.Prime → ¬ p ∣ M → IsEigAt k χ' h p (b p)} :=
  fun M M' k hM hd hk χ' g hg =>
    UpperTheory.V.Lit.KT.EigenformSpan.main M M' k (Nat.pos_of_dvd_of_pos hd hM) hd hk χ' g hg
