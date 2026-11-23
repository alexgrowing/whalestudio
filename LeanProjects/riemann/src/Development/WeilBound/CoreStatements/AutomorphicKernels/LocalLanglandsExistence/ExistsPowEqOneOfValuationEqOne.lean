import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalLanglandsExistence.KernelCond
import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalLanglandsExistence.KernelCondGlob
import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalLanglandsExistence.HasExponentMulOfIsUnram
import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalLanglandsExistence.LaurentMonomialEqOneOfCircle
import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalLanglandsExistence.KernelCondTwCircleOfRootsOfUnity

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Pf1.LocalLanglands.HeckeKernelConditions

namespace RootOfUnityValuation

section Roots

def IsRoot (z : ℂˣ) : Prop := ∃ n : ℕ, 0 < n ∧ z ^ n = 1

def IsCls (d : ℤ) (a : ℂˣ) (μ : ℂ) : Prop := ∃ q : ℕ, 0 < q ∧ μ ^ q = ((a ^ ((q : ℤ) * d) : ℂˣ) : ℂ)

theorem isRoot_of_zpow {g : ℂˣ} {k : ℤ} (hk : k ≠ 0) (h : g ^ k = 1) : IsRoot g := by
  refine ⟨k.natAbs, Int.natAbs_pos.2 hk, ?_⟩
  rcases Int.natAbs_eq k with e | e
  · rw [e, zpow_natCast] at h; exact h
  · rw [e, zpow_neg, zpow_natCast, inv_eq_one] at h; exact h

theorem IsRoot.mul {a b : ℂˣ} (ha : IsRoot a) (hb : IsRoot b) : IsRoot (a * b) := by
  obtain ⟨m, hm, h1⟩ := ha
  obtain ⟨n, hn, h2⟩ := hb
  have e1 : a ^ (m * n) = 1 := by rw [pow_mul, h1, one_pow]
  have e2 : b ^ (m * n) = 1 := by rw [Nat.mul_comm m n, pow_mul, h2, one_pow]
  exact ⟨m * n, Nat.mul_pos hm hn, by rw [mul_pow, e1, e2, one_mul]⟩

theorem IsRoot.inv {a : ℂˣ} (ha : IsRoot a) : IsRoot a⁻¹ := by
  obtain ⟨m, hm, h1⟩ := ha
  exact ⟨m, hm, by rw [inv_pow, h1, inv_one]⟩

theorem IsRoot.pow {a : ℂˣ} (ha : IsRoot a) (f : ℕ) : IsRoot (a ^ f) := by
  obtain ⟨m, hm, h1⟩ := ha
  exact ⟨m, hm, by rw [← pow_mul, Nat.mul_comm, pow_mul, h1, one_pow]⟩

theorem IsCls.root {d : ℤ} {a b : ℂˣ} {μ : ℂ} (hd : d ≠ 0) (ha : IsCls d a μ) (hb : IsCls d b μ) :
    IsRoot (a * b⁻¹) := by
  obtain ⟨q, hq, h1⟩ := ha
  obtain ⟨p, hp, h2⟩ := hb
  have e1 : μ ^ (q * p) = ((a ^ (((q * p : ℕ) : ℤ) * d) : ℂˣ) : ℂ) := by
    rw [pow_mul, h1, ← Units.val_pow_eq_pow_val, ← zpow_natCast, ← zpow_mul,
      show ((q * p : ℕ) : ℤ) * d = (q : ℤ) * d * (p : ℤ) by push_cast; ring]
  have e2 : μ ^ (q * p) = ((b ^ (((q * p : ℕ) : ℤ) * d) : ℂˣ) : ℂ) := by
    rw [Nat.mul_comm q p, pow_mul, h2, ← Units.val_pow_eq_pow_val, ← zpow_natCast, ← zpow_mul,
      show ((p * q : ℕ) : ℤ) * d = (p : ℤ) * d * (q : ℤ) by push_cast; ring]
  have hk : ((q * p : ℕ) : ℤ) * d ≠ 0 :=
    mul_ne_zero (by exact_mod_cast (Nat.mul_pos hq hp).ne') hd
  refine isRoot_of_zpow hk ?_
  rw [mul_zpow, inv_zpow, mul_inv_eq_one]
  exact Units.ext (e1.symm.trans e2)

theorem IsCls.of_root {d : ℤ} {a b : ℂˣ} {μ : ℂ} (ha : IsCls d a μ) (hab : IsRoot (a * b⁻¹)) : IsCls d b μ := by
  obtain ⟨q, hq, h1⟩ := ha
  obtain ⟨n, hn, h2⟩ := hab
  have hab' : a ^ n = b ^ n := by rw [mul_pow, inv_pow, mul_inv_eq_one] at h2; exact h2
  refine ⟨q * n, Nat.mul_pos hq hn, ?_⟩
  rw [pow_mul, h1, ← Units.val_pow_eq_pow_val, ← zpow_natCast, ← zpow_mul,
    show (q : ℤ) * d * (n : ℤ) = (n : ℤ) * ((q : ℤ) * d) by ring, zpow_mul, zpow_natCast, hab', ← zpow_natCast,
    ← zpow_mul, show ((q * n : ℕ) : ℤ) * d = (n : ℤ) * ((q : ℤ) * d) by push_cast; ring]

theorem isOfFinOrder_unrChar (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {α : ℂˣ} (hα : IsRoot α) : IsOfFinOrder (GlobalTheory.SmGL.unrChar k α) := by
  obtain ⟨n, hn, h1⟩ := hα
  refine isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, MonoidHom.ext fun y => ?_⟩
  rw [MonoidHom.pow_apply, GlobalTheory.SmGL.unrChar_apply, MonoidHom.one_apply, ← zpow_natCast, ← zpow_mul, mul_comm,
    zpow_mul, zpow_natCast, h1, one_zpow]

end Roots

section Eig

open GlobalTheory.WeilRestrict Polynomial

variable {Ω : Type} [Field Ω] {A : ValuationSubring Ω}
  {K L : Type} [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω]
  [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω]
  {v : HeightOneSpectrum (𝓞 K)} {v' : HeightOneSpectrum (𝓞 L)}

theorem exists_deg_resWeil_pos (h : IsPlaceOver A v) (h' : IsPlaceOver A v') :
    ∃ f : ℕ, (∀ σ : Weil h', deg (resWeil h h' σ) = f * deg σ) ∧ 0 < f := by
  obtain ⟨f, hf⟩ := normV_eq_pow_of_isPlaceOver h h'
  refine ⟨f, fun σ => ?_, ?_⟩
  · obtain ⟨a, b, hab⟩ := (mem_Weil h').1 σ.2
    have h1 := deg_eq hab
    rw [hf] at hab
    have h2 := actsAs_resG (K := K) hab
    have h3 := deg_eq (σ := resWeil h h' σ) h2
    rw [h3, h1]
    push_cast
    ring
  · rcases Nat.eq_zero_or_pos f with rfl | hpos
    · have h1 := one_lt_normV v'
      rw [hf, pow_zero] at h1
      exact absurd h1 (lt_irrefl 1)
    · exact hpos

theorem eig_isCls (h : IsPlaceOver A v) (h' : IsPlaceOver A v') {a : Weil h' →* (v'.adicCompletion L)ˣ}
    (χ φ : (v'.adicCompletion L)ˣ →* ℂˣ) (hφ : IsOfFinOrder φ) (z : ℂˣ)
    (hdec : ∀ (σ' : Weil h') (σ : Weil h), (∀ w : Ω, (σ : G K Ω) w = (σ' : G L Ω) w) →
      χ (a σ') = φ (a σ') * GlobalTheory.WeilDeligne.unrChar h z σ)
    (hs : IsSmooth (χ.comp a)) {y : WD h} (hy : Induces (WD.lpOfChar h' (χ.comp a) hs) y) (σ : Weil h) :
    ∀ μ ∈ y.eig σ, IsCls (deg σ) z μ := by
  obtain ⟨N, hN, hN'⟩ := eig_pow_of_induces h h' _ _ hy σ
  obtain ⟨M, hM, hφM⟩ := hφ.exists_pow_eq_one
  intro μ hμ
  obtain ⟨τ, hτd, hτ⟩ := hN' μ hμ
  rw [MonoidHom.comp_apply, hdec τ (resWeil h h' τ) (fun w => resWeil_apply h h' τ w),
    GlobalTheory.WeilDeligne.unrChar_apply, hτd] at hτ
  have e1 : ((φ (a τ)) ^ M : ℂˣ) = 1 := by rw [← MonoidHom.pow_apply, hφM]; rfl
  refine ⟨N * M, Nat.mul_pos hN hM, ?_⟩
  rw [pow_mul, hτ, ← Units.val_pow_eq_pow_val, mul_pow, e1, one_mul, ← zpow_natCast, ← zpow_mul,
    show ((N * M : ℕ) : ℤ) * deg σ = (N : ℤ) * deg σ * (M : ℤ) by push_cast; ring]

end Eig

section Partial

open Polynomial

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem charPol_rel_partial {r : ℕ} (c : Fin r → ℤ) (x x₀ x' : Fin r → WD h) (σ : Weil h) (p : ℂ → Prop)
    (T : Fin r → Prop) (hxT : ∀ i, T i → ∀ μ ∈ (x i).eig σ, p μ) (hxN : ∀ i, ¬ T i → ∀ μ ∈ (x i).eig σ, ¬ p μ)
    (hx₀ : ∀ i, ∀ μ ∈ (x₀ i).eig σ, ¬ p μ) (s : ℂ)
    (hx'T : ∀ i, T i → (x' i).eig σ = ((x i).eig σ).map (· * s))
    (hx'N : ∀ i, ¬ T i → (x' i).eig σ = (x i).eig σ)
    (H : ∏ i, (x i).charPol σ ^ (c i).toNat * (x₀ i).charPol σ ^ (-c i).toNat =
      ∏ i, (x₀ i).charPol σ ^ (c i).toNat * (x i).charPol σ ^ (-c i).toNat) :
    ∏ i, (x' i).charPol σ ^ (c i).toNat * (x₀ i).charPol σ ^ (-c i).toNat =
      ∏ i, (x₀ i).charPol σ ^ (c i).toNat * (x' i).charPol σ ^ (-c i).toNat := by
  classical
  rw [prod_charPol_eq, prod_charPol_eq] at H ⊢
  have H' := congrArg Polynomial.roots H
  rw [roots_multiset_prod_X_sub_C, roots_multiset_prod_X_sub_C] at H'
  set Mp : Fin r → Multiset ℂ := fun i => ((x i).eig σ).filter (fun μ => p μ) with hMp
  set Mn : Fin r → Multiset ℂ := fun i => ((x i).eig σ).filter (fun μ => ¬ p μ) with hMn
  have hsplit : ∀ i, (x' i).eig σ = (Mp i).map (· * s) + Mn i := by
    intro i
    by_cases hT : T i
    · rw [hx'T i hT, hMp, hMn]
      simp only
      rw [Multiset.filter_eq_self.2 (hxT i hT),
        Multiset.filter_eq_nil.2 (fun μ hμ => not_not.2 (hxT i hT μ hμ)), add_zero]
    · rw [hx'N i hT, hMp, hMn]
      simp only
      rw [Multiset.filter_eq_nil.2 (hxN i hT), Multiset.filter_eq_self.2 (hxN i hT), Multiset.map_zero, zero_add]
  have hf1 : ∀ i, ((x₀ i).eig σ).filter (fun μ => p μ) = 0 := fun i => Multiset.filter_eq_nil.2 (hx₀ i)
  have hg1 : ∀ i, ((x₀ i).eig σ).filter (fun μ => ¬ p μ) = (x₀ i).eig σ := fun i =>
    Multiset.filter_eq_self.2 (hx₀ i)
  have E1 := congrArg (Multiset.filter fun μ : ℂ => p μ) H'
  have E2 := congrArg (Multiset.filter fun μ : ℂ => ¬ p μ) H'
  simp only [filter_finsetSum, Multiset.filter_add, Multiset.filter_nsmul, hf1, hg1, smul_zero, add_zero,
    zero_add] at E1 E2
  have E3 := congrArg (Multiset.map (· * s)) E1
  simp only [map_finsetSum, Multiset.map_nsmul] at E3
  congr 2
  simp only [hsplit, nsmul_add, Finset.sum_add_distrib]
  have E1' : ∑ i, (c i).toNat • (Mp i).map (· * s) = ∑ i, (-c i).toNat • (Mp i).map (· * s) := E3
  have E2' : ∑ i, (c i).toNat • Mn i + ∑ i, (-c i).toNat • (x₀ i).eig σ =
      ∑ i, (c i).toNat • (x₀ i).eig σ + ∑ i, (-c i).toNat • Mn i := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]; exact E2
  rw [E1', add_assoc, E2']
  abel

end Partial

section Decomp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end Decomp

section Main

open GlobalTheory.WeilRestrict

variable {Ω : Type} [Field Ω] {A : ValuationSubring Ω}

open scoped Classical in

theorem main {K : Type} [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] {v : HeightOneSpectrum (𝓞 K)}
    {h : IsPlaceOver A v} {ψ : AddChar (v.adicCompletion K) Circle} (H : KernelCondTw h ψ {1})
    {r : ℕ} {L : Fin r → Type} [∀ i, Field (L i)] [∀ i, NumberField (L i)] [∀ i, Algebra (L i) Ω]
    [∀ i, IsAlgClosure (L i) Ω] [∀ i, Algebra K (L i)] [∀ i, IsScalarTower K (L i) Ω]
    {v' : ∀ i, HeightOneSpectrum (𝓞 (L i))} {h' : ∀ i, IsPlaceOver A (v' i)} (hloc : ∀ i, IsLocalExt (L i) h)
    {ψ' : ∀ i, AddChar ((v' i).adicCompletion (L i)) Circle} (hψc : ∀ i, Continuous (ψ' i))
    (hψtr : ∀ i (z : L i), ψ' i (algebraMap (L i) _ z) = ψ (algebraMap K _ (Algebra.trace K (L i) z)))
    {a : ∀ i, Weil (h' i) →* ((v' i).adicCompletion (L i))ˣ} (ha : ∀ i, IsLocalArtin (h' i) (a i))
    (c : Fin r → ℤ) {x₀ : Fin r → WD h}
    (hx₀ : ∀ i, Induces (WD.lpOfChar (h' i) ((1 : ((v' i).adicCompletion (L i))ˣ →* ℂˣ).comp (a i))
      ((ha i).smooth (isSmoothChar_of_isUnram fun _ _ => rfl))) (x₀ i))
    {t : ℝ} {e₀ : Fin r → ℂ} (ht : 0 < t) (he₀ : ∀ i, IsTateMeas (ψ' i) t 1 (e₀ i)) (n : ℕ) :
    ∀ (χ : ∀ i, ((v' i).adicCompletion (L i))ˣ →* ℂˣ) (hχ : ∀ i, IsSmoothChar (χ i))
      (x : Fin r → WD h) (z : Fin r → ℂˣ) (φ : ∀ i, ((v' i).adicCompletion (L i))ˣ →* ℂˣ),
      (∀ i, IsOfFinOrder (φ i)) →
      (∀ i (σ' : Weil (h' i)) (σ : Weil h), (∀ w : Ω, (σ : G K Ω) w = (σ' : G (L i) Ω) w) →
        χ i (a i σ') = φ i (a i σ') * GlobalTheory.WeilDeligne.unrChar h (z i) σ) →
      (Finset.univ.filter fun i => ¬ IsRoot (z i)).card ≤ n →
      (∀ i, Induces (WD.lpOfChar (h' i) ((χ i).comp (a i)) ((ha i).smooth (hχ i))) (x i)) →
      (∀ σ, ∏ i, (x i).charPol σ ^ (c i).toNat * (x₀ i).charPol σ ^ (-c i).toNat =
        ∏ i, (x₀ i).charPol σ ^ (c i).toNat * (x i).charPol σ ^ (-c i).toNat) →
      ∀ (e : Fin r → ℂ), (∀ i, IsTateMeas (ψ' i) t (χ i) (e i)) → ∏ i, (e i / e₀ i) ^ (c i) = 1 := by
  classical
  choose f hf hfpos using fun i => exists_deg_resWeil_pos h (h' i)
  induction n with
  | zero =>
    intro χ hχ x z φ hφ hdec hcard hx hrel e he
    have hroot : ∀ i, IsRoot (z i) := fun i => by
      by_contra hni
      have hmem : i ∈ Finset.univ.filter fun i => ¬ IsRoot (z i) :=
        Finset.mem_filter.2 ⟨Finset.mem_univ _, hni⟩
      have := Finset.card_pos.2 ⟨i, hmem⟩
      omega
    refine H r L v' h' hloc ψ' hψc hψtr a ha χ hχ c x x₀ ⟨1, Set.mem_singleton _,
      fun i => φ i * GlobalTheory.SmGL.unrChar _ (z i ^ f i)⁻¹,
      fun i => (hφ i).mul (isOfFinOrder_unrChar _ ((hroot i).pow (f i)).inv), fun i σ' σ hσ => ?_⟩
      hx hx₀ hrel t e e₀ ht he he₀
    have hd : deg σ = f i * deg σ' := by rw [eq_resWeil_of_agree h (h' i) hσ, hf]
    rw [hdec i σ' σ hσ, MonoidHom.mul_apply, GlobalTheory.SmGL.unrChar_apply, (ha i).ord_eq, GlobalTheory.WeilDeligne.unrChar_apply,
      GlobalTheory.WeilDeligne.unrChar_apply, one_zpow, mul_one, hd, inv_zpow', neg_neg,
      ← zpow_natCast (z i), ← zpow_mul]
  | succ n ih =>
    intro χ hχ x z φ hφ hdec hcard hx hrel e he
    by_cases hle : (Finset.univ.filter fun i => ¬ IsRoot (z i)).card ≤ n
    · exact ih χ hχ x z φ hφ hdec hle hx hrel e he
    obtain ⟨i0, hi0⟩ : ∃ i0, ¬ IsRoot (z i0) := by
      by_contra hne
      push Not at hne
      apply hle
      rw [Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun i _ => not_not.2 (hne i))]
      exact Nat.zero_le _
    obtain ⟨Z, hZ⟩ : ∃ Z : ℂˣ, Z = z i0 := ⟨_, rfl⟩
    have hZroot : ¬ IsRoot Z := hZ ▸ hi0
    have hT0 : IsRoot (z i0 * Z⁻¹) := ⟨1, one_pos, by rw [hZ, mul_inv_cancel, pow_one]⟩
    obtain ⟨δ, hδ⟩ : ∃ δ : Fin r → ℤ, ∀ i, δ i = if IsRoot (z i * Z⁻¹) then 1 else 0 := ⟨_, fun _ => rfl⟩
    have hδT : ∀ i, IsRoot (z i * Z⁻¹) → δ i = 1 := fun i hi => by rw [hδ, if_pos hi]
    have hδN : ∀ i, ¬ IsRoot (z i * Z⁻¹) → δ i = 0 := fun i hi => by rw [hδ, if_neg hi]
    have hce : ∀ i, ∃ (cc : ((v' i).adicCompletion (L i))ˣ) (m : ℕ), HasConductor (ψ' i) cc ∧ HasExponent (χ i) m :=
      fun i => by obtain ⟨cc, m, R, h1, h2, -⟩ := he i; exact ⟨cc, m, h1, h2⟩
    choose cc nn hcc hnn using hce
    obtain ⟨m, hm⟩ : ∃ m : Fin r → ℤ, ∀ i, m i = (nn i : ℤ) - ord _ (cc i) := ⟨_, fun _ => rfl⟩
    obtain ⟨P, hP⟩ : ∃ P : ℂ, P = ∏ i, (e i / e₀ i) ^ (c i) := ⟨_, rfl⟩
    obtain ⟨k, hk⟩ : ∃ k : ℤ, k = ∑ i, δ i * f i * m i * c i := ⟨_, rfl⟩
    have key : ∀ w : ℂ, (∃ q : ℕ, 0 < q ∧ w ^ q = 1) → (P * (Z : ℂ) ^ k) * w ^ (-k) = 1 := by
      intro w hw
      have hw0 : w ≠ 0 := by
        rintro rfl
        obtain ⟨q, hq, hq1⟩ := hw
        rw [zero_pow hq.ne'] at hq1
        exact zero_ne_one hq1
      obtain ⟨W, hW⟩ : ∃ W : ℂˣ, (W : ℂ) = w := ⟨Units.mk0 w hw0, rfl⟩
      have hWroot : IsRoot W := by
        obtain ⟨q, hq, hq1⟩ := hw
        exact ⟨q, hq, Units.ext (by rw [Units.val_pow_eq_pow_val, hW, hq1, Units.val_one])⟩
      obtain ⟨u, hu⟩ : ∃ u : ℂˣ, u = W * Z⁻¹ := ⟨_, rfl⟩
      have hχ' : ∀ i, IsSmoothChar (χ i * GlobalTheory.SmGL.unrChar _ ((u ^ δ i) ^ f i)⁻¹) := fun i =>
        (hχ i).mul (isSmoothChar_of_isUnram (isUnram_unrChar _ _))
      have hres : ∀ i (σ' : Weil (h' i)), GlobalTheory.WeilDeligne.unrChar (h' i) ((u ^ δ i) ^ f i) σ' =
          GlobalTheory.WeilDeligne.unrChar h (u ^ δ i) (resWeil h (h' i) σ') := by
        intro i σ'
        rw [GlobalTheory.WeilDeligne.unrChar_apply, GlobalTheory.WeilDeligne.unrChar_apply, hf, ← zpow_natCast, ← zpow_mul]
      have hind : ∀ i, Induces (WD.lpOfChar (h' i) ((χ i * GlobalTheory.SmGL.unrChar _ ((u ^ δ i) ^ f i)⁻¹).comp (a i))
          ((ha i).smooth (hχ' i)))
          ((x i).lpTwist (GlobalTheory.WeilDeligne.unrChar h (u ^ δ i)) (isSmooth_unrChar h (u ^ δ i))) := by
        intro i
        have h1 := induces_lpTwist h (h' i) (hx i) _ (isSmooth_unrChar h (u ^ δ i)) _
          (isSmooth_unrChar (h' i) ((u ^ δ i) ^ f i)) (hres i)
        rwa [lpTwist_lpOfChar_unr (ha i) (hχ i)] at h1
      have hdec' : ∀ i (σ' : Weil (h' i)) (σ : Weil h), (∀ w : Ω, (σ : G K Ω) w = (σ' : G (L i) Ω) w) →
          (χ i * GlobalTheory.SmGL.unrChar _ ((u ^ δ i) ^ f i)⁻¹ : ((v' i).adicCompletion (L i))ˣ →* ℂˣ) (a i σ') =
            φ i (a i σ') * GlobalTheory.WeilDeligne.unrChar h (z i * u ^ δ i) σ := by
        intro i σ' σ hσ
        have hd : deg σ = f i * deg σ' := by rw [eq_resWeil_of_agree h (h' i) hσ, hf]
        rw [MonoidHom.mul_apply, hdec i σ' σ hσ, GlobalTheory.SmGL.unrChar_apply, (ha i).ord_eq,
          GlobalTheory.WeilDeligne.unrChar_apply, GlobalTheory.WeilDeligne.unrChar_apply, hd, inv_zpow', neg_neg,
          ← zpow_natCast (u ^ δ i), ← zpow_mul, mul_zpow, mul_assoc]
      have hcard' : (Finset.univ.filter fun i => ¬ IsRoot (z i * u ^ δ i)).card ≤ n := by
        have hsub : (Finset.univ.filter fun i => ¬ IsRoot (z i * u ^ δ i)) ⊆
            (Finset.univ.filter fun i => ¬ IsRoot (z i)).erase i0 := by
          intro i hi
          rw [Finset.mem_filter] at hi
          have hN : ¬ IsRoot (z i * Z⁻¹) := by
            intro hT
            apply hi.2
            have e1 : z i * u ^ δ i = (z i * Z⁻¹) * W := by
              rw [hδT i hT, zpow_one, hu, mul_assoc, mul_comm Z⁻¹ W]
            rw [e1]
            exact hT.mul hWroot
          rw [Finset.mem_erase, Finset.mem_filter]
          refine ⟨fun hii => hN (by rw [hii]; exact hT0), Finset.mem_univ _, ?_⟩
          have h2 := hi.2
          rwa [hδN i hN, zpow_zero, mul_one] at h2
        have h1 := Finset.card_le_card hsub
        have hmem : i0 ∈ (Finset.univ.filter fun i => ¬ IsRoot (z i)) := Finset.mem_filter.2 ⟨Finset.mem_univ _, hi0⟩
        rw [Finset.card_erase_of_mem hmem] at h1
        omega
      have hrel' : ∀ σ, ∏ i, ((x i).lpTwist (GlobalTheory.WeilDeligne.unrChar h (u ^ δ i))
            (isSmooth_unrChar h (u ^ δ i))).charPol σ ^ (c i).toNat * (x₀ i).charPol σ ^ (-c i).toNat =
          ∏ i, (x₀ i).charPol σ ^ (c i).toNat * ((x i).lpTwist (GlobalTheory.WeilDeligne.unrChar h (u ^ δ i))
            (isSmooth_unrChar h (u ^ δ i))).charPol σ ^ (-c i).toNat := by
        intro σ
        by_cases hd : deg σ = 0
        · have h1 : ∀ i, GlobalTheory.WeilDeligne.unrChar h (u ^ δ i) σ = 1 := fun i => by
            rw [GlobalTheory.WeilDeligne.unrChar_apply, hd, zpow_zero]
          simp only [charPol_lpTwist_of_eq_one _ _ _ (h1 _)]
          exact hrel σ
        · refine charPol_rel_partial c x x₀ _ σ (IsCls (deg σ) Z) (fun i => IsRoot (z i * Z⁻¹)) ?_ ?_ ?_
            ((GlobalTheory.WeilDeligne.unrChar h u σ : ℂˣ) : ℂ) ?_ ?_ (hrel σ)
          · intro i hT μ hμ
            exact (eig_isCls h (h' i) (χ i) (φ i) (hφ i) (z i) (hdec i) _ (hx i) σ μ hμ).of_root hT
          · intro i hT μ hμ hZμ
            exact hT ((eig_isCls h (h' i) (χ i) (φ i) (hφ i) (z i) (hdec i) _ (hx i) σ μ hμ).root hd hZμ)
          · intro i μ hμ hZμ
            have h1 : IsCls (deg σ) 1 μ := eig_isCls h (h' i) 1 1 (isOfFinOrder_iff_pow_eq_one.2 ⟨1, one_pos, one_pow 1⟩) 1
              (fun _ _ _ => by simp [GlobalTheory.WeilDeligne.unrChar_apply]) _ (hx₀ i) σ μ hμ
            have h2 := (h1.root hd hZμ).inv
            rw [one_mul, inv_inv] at h2
            exact hZroot h2
          · intro i hT
            rw [eig_lpTwist, hδT i hT, zpow_one]
          · intro i hT
            rw [eig_lpTwist, hδN i hT, zpow_zero, GlobalTheory.WeilDeligne.unrChar_apply, one_zpow, Units.val_one]
            simp
      have he' : ∀ i, IsTateMeas (ψ' i) t (χ i * GlobalTheory.SmGL.unrChar _ ((u ^ δ i) ^ f i)⁻¹)
          (((((u ^ δ i) ^ f i)⁻¹ ^ m i : ℂˣ) : ℂ) * e i) := fun i => by
        have h1 := isTateMeas_mul_unrChar ((u ^ δ i) ^ f i)⁻¹ (hcc i) (hnn i) (he i)
        rwa [← hm i] at h1
      have hT := ih (fun i => χ i * GlobalTheory.SmGL.unrChar _ ((u ^ δ i) ^ f i)⁻¹) hχ'
        (fun i => (x i).lpTwist (GlobalTheory.WeilDeligne.unrChar h (u ^ δ i)) (isSmooth_unrChar h (u ^ δ i)))
        (fun i => z i * u ^ δ i) φ hφ hdec' hcard' hind hrel'
        (fun i => (((((u ^ δ i) ^ f i)⁻¹ ^ m i : ℂˣ) : ℂ) * e i)) he'
      have e2 : ∀ i, (((((u ^ δ i) ^ f i)⁻¹ ^ m i : ℂˣ) : ℂ) * e i / e₀ i) ^ c i =
          ((((u ^ δ i) ^ f i)⁻¹ ^ (m i * c i) : ℂˣ) : ℂ) * (e i / e₀ i) ^ c i := by
        intro i
        rw [mul_div_assoc, mul_zpow, zpow_mul, Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val,
          Units.val_zpow_eq_zpow_val]
      have zs : ∀ (s : Finset (Fin r)) (g : Fin r → ℤ), ∏ i ∈ s, u ^ g i = u ^ ∑ i ∈ s, g i := by
        intro s g
        induction s using Finset.induction_on with
        | empty => simp
        | insert j s hj ih' => rw [Finset.prod_insert hj, Finset.sum_insert hj, ih', zpow_add]
      have e5 : ∀ i, ((u ^ δ i) ^ f i)⁻¹ ^ (m i * c i) = u ^ (-(δ i * f i * m i * c i)) := by
        intro i
        rw [← zpow_natCast (u ^ δ i), ← zpow_mul, ← zpow_neg, ← zpow_mul,
          show -(δ i * (f i : ℤ)) * (m i * c i) = -(δ i * f i * m i * c i) by ring]
      have e3 : ∏ i, ((u ^ δ i) ^ f i)⁻¹ ^ (m i * c i) = u ^ (-k) := by
        rw [Finset.prod_congr rfl fun i _ => e5 i, zs, Finset.sum_neg_distrib, hk]
      have e4 : u ^ (-k) = Z ^ k * W ^ (-k) := by
        rw [hu, mul_zpow, inv_zpow', neg_neg, mul_comm]
      simp only [e2] at hT
      rw [Finset.prod_mul_distrib, ← hP, ← Units.coe_prod, e3, e4] at hT
      rw [← hT, Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, hW]
      ring
    have h1 := key 1 ⟨1, one_pos, one_pow 1⟩
    rw [one_zpow, mul_one] at h1
    have hk0 : k = 0 := by
      set q : ℕ := k.natAbs + 1 with hq
      have hprim := Complex.isPrimitiveRoot_exp q (by omega)
      have h2 := key _ ⟨q, by omega, hprim.pow_eq_one⟩
      rw [h1, one_mul, zpow_neg, inv_eq_one, hprim.zpow_eq_one_iff_dvd] at h2
      exact Int.eq_zero_of_dvd_of_natAbs_lt_natAbs h2 (by rw [Int.natAbs_natCast]; omega)
    rw [hk0, zpow_zero, mul_one] at h1
    rw [← hP]
    exact h1

end Main

end RootOfUnityValuation

section Top

open RootOfUnityValuation GlobalTheory.WeilRestrict

variable {Ω : Type} [Field Ω] {A : ValuationSubring Ω}

end Top

end PositivityTheory.Pf1.LocalLanglands.HeckeKernelConditions

end
