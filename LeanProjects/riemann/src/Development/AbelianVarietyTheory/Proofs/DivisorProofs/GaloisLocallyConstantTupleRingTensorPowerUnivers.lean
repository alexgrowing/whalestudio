import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdSubConjEqZero

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

open GlobalTheory.EtC.GalSec

private theorem prim_lemma (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsSeparable K Ω]
    (E : IntermediateField K Ω) [FiniteDimensional K E] :
    ∃ θ : Ω, IntermediateField.adjoin K {θ} = E := by
  have : Algebra.IsSeparable K E := Algebra.isSeparable_tower_bot_of_isSeparable K E Ω
  obtain ⟨α, hα⟩ := Field.exists_primitive_element K E
  refine ⟨(α : Ω), ?_⟩
  simpa only [IntermediateField.lift_adjoin_simple, IntermediateField.lift_top] using
    congr_arg IntermediateField.lift hα

theorem GlobalTheory.EtC.GalSec.Tens.lem_ref : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (θ₁ θ₂ : Ω), ∃ θ : Ω, θ₁ ∈ IntermediateField.adjoin K {θ} ∧ θ₂ ∈ IntermediateField.adjoin K {θ} := by
  intro K Ω _ _ _ _ θ₁ θ₂
  have h1 : IsIntegral K θ₁ := (Algebra.IsSeparable.isSeparable K θ₁).isIntegral
  have h2 : IsIntegral K θ₂ := (Algebra.IsSeparable.isSeparable K θ₂).isIntegral
  have : FiniteDimensional K (IntermediateField.adjoin K {θ₁, θ₂}) :=
    IntermediateField.finiteDimensional_adjoin_pair h1 h2
  obtain ⟨θ, hθ⟩ := prim_lemma K Ω (IntermediateField.adjoin K {θ₁, θ₂})
  refine ⟨θ, ?_, ?_⟩ <;> rw [hθ]
  · exact IntermediateField.subset_adjoin K _ (Set.mem_insert _ _)
  · exact IntermediateField.subset_adjoin K _ (Set.mem_insert_of_mem _ rfl)

private theorem algEquiv_eq_on_adjoin_of_eq_generator (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
    (σ τ : Ω ≃ₐ[K] Ω) (θ x : Ω) (hx : x ∈ IntermediateField.adjoin K {θ}) (h : σ θ = τ θ) :
    σ x = τ x := by
  rw [← IntermediateField.mem_toSubalgebra,
    IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (Algebra.IsAlgebraic.isAlgebraic θ)] at hx
  have hle : Algebra.adjoin K {θ} ≤ AlgHom.equalizer (σ : Ω →ₐ[K] Ω) (τ : Ω →ₐ[K] Ω) :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr h)
  exact hle hx

theorem GlobalTheory.EtC.GalSec.Tens.lem_mono : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (k : ℕ) (θ θ' : Ω) (φ : GlobalTheory.EtC.GalSec.LCRing K Ω k), θ ∈ IntermediateField.adjoin K {θ'} → GlobalTheory.EtC.GalSec.Tens.DependsOn K Ω k θ φ → GlobalTheory.EtC.GalSec.Tens.DependsOn K Ω k θ' φ := by
  intro K Ω _ _ _ _ k θ θ' φ hθ hφ g g' h
  exact hφ g g' fun i => algEquiv_eq_on_adjoin_of_eq_generator K Ω (g i) (g' i) θ' θ hθ (h i)

theorem GlobalTheory.EtC.GalSec.Tens.lem_dep : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (k : ℕ) (φ : GlobalTheory.EtC.GalSec.LCRing K Ω k), ∃ θ : Ω, GlobalTheory.EtC.GalSec.Tens.DependsOn K Ω k θ φ := by
  intro K Ω _ _ _ _ k φ
  classical
  have hinv : ∃ V ∈ nhds (1 : Fin k → (Ω ≃ₐ[K] Ω)), ∀ g v, v ∈ V → φ (g * v) = φ g := by
    have hfin : (Set.range φ).Finite := φ.range_finite
    have hV : ∀ a, ∃ V ∈ nhds (1 : Fin k → (Ω ≃ₐ[K] Ω)), ∀ x v, φ x = a → v ∈ V → φ (x * v) = a := by
      intro a
      have hc := φ.isLocallyConstant.isClopen_fiber a
      obtain ⟨V, hV1, hV2⟩ := compact_open_separated_mul_right hc.isClosed.isCompact hc.isOpen subset_rfl
      exact ⟨V, hV1, fun x v hx hv => hV2 (Set.mul_mem_mul hx hv)⟩
    choose V hV1 hV2 using hV
    refine ⟨⋂ a ∈ Set.range φ, V a, (Filter.biInter_mem hfin).mpr fun a _ => hV1 a, ?_⟩
    intro g v hv
    have hv' : v ∈ V (φ g) := Set.mem_iInter₂.mp hv (φ g) ⟨g, rfl⟩
    exact hV2 (φ g) g v rfl hv'
  obtain ⟨V, hV, hφV⟩ := hinv
  rw [nhds_pi, Filter.mem_pi'] at hV
  obtain ⟨I, t, ht, hIt⟩ := hV
  have hW : (⋂ i, t i) ∈ nhds (1 : Ω ≃ₐ[K] Ω) := Filter.iInter_mem.mpr fun i => by simpa using ht i
  obtain ⟨E, hE, hEW⟩ := (krullTopology_mem_nhds_one_iff K Ω _).mp hW
  obtain ⟨θ, hθ⟩ := prim_lemma K Ω E
  refine ⟨θ, fun g g' h => ?_⟩
  have hu : ∀ i, (g i)⁻¹ * g' i ∈ ⋂ i, t i := by
    intro i
    refine hEW ((IntermediateField.mem_fixingSubgroup_iff E _).mpr fun x hx => ?_)
    rw [← hθ] at hx
    have hx' := algEquiv_eq_on_adjoin_of_eq_generator K Ω (g' i) (g i) θ x hx (h i).symm
    rw [AlgEquiv.mul_apply, hx', AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
  have hmem : (fun i => (g i)⁻¹ * g' i) ∈ V := hIt fun i _ => Set.mem_iInter.mp (hu i) i
  have hg : g * (fun i => (g i)⁻¹ * g' i) = g' := by
    funext i; simp only [Pi.mul_apply, mul_inv_cancel_left]
  have := hφV g _ hmem
  rw [hg] at this
  exact this.symm
private theorem exists_unitary_diagonal_of_isHermitian {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    {B : Type} [CommRing B] (g₀ σ' : Ω →+* B)
    (h : σ'.comp (algebraMap K Ω) = g₀.comp (algebraMap K Ω)) (θ : Ω) :
    CompleteOrthogonalIdempotents (Tens.idem (K := K) g₀ θ (σ' θ)) ∧
      (∀ s : Tens.conj K Ω θ, σ' θ * Tens.idem (K := K) g₀ θ (σ' θ) s = g₀ s * Tens.idem (K := K) g₀ θ (σ' θ) s) ∧
      σ' θ = ∑ s : Tens.conj K Ω θ, g₀ s * Tens.idem (K := K) g₀ θ (σ' θ) s :=
  Tens.idem_spec (K := K) g₀ θ (σ' θ) (Tens.prod_sub_conj_eq_zero (K := K) g₀ σ' h θ)

private theorem sum_pi_prod_eq_prod_sum {ι κ R : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [CommSemiring R]
    (f : ι → κ → R) : ∑ t : ι → κ, ∏ i, f i (t i) = ∏ i, ∑ s, f i s := by
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

private theorem sum_prod_tens_idem {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    {B : Type} [CommRing B] {k : ℕ} (g₀ : Ω →+* B) (gs : Fin k → (Ω →+* B))
    (hgs : ∀ i, (gs i).comp (algebraMap K Ω) = g₀.comp (algebraMap K Ω)) (θ : Ω) :
    ∑ t : Fin k → Tens.conj K Ω θ, ∏ i, Tens.idem (K := K) g₀ θ (gs i θ) (t i) = 1 := by
  rw [sum_pi_prod_eq_prod_sum]
  exact Finset.prod_eq_one fun i _ => (exists_unitary_diagonal_of_isHermitian g₀ (gs i) (hgs i) θ).1.complete

private theorem prod_tens_idem_mul {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    {B : Type} [CommRing B] {k : ℕ} (g₀ : Ω →+* B) (gs : Fin k → (Ω →+* B))
    (hgs : ∀ i, (gs i).comp (algebraMap K Ω) = g₀.comp (algebraMap K Ω)) (θ : Ω)
    [DecidableEq (Tens.conj K Ω θ)] (t s : Fin k → Tens.conj K Ω θ) :
    (∏ i, Tens.idem (K := K) g₀ θ (gs i θ) (t i)) * (∏ i, Tens.idem (K := K) g₀ θ (gs i θ) (s i)) =
      if t = s then ∏ i, Tens.idem (K := K) g₀ θ (gs i θ) (t i) else 0 := by
  rw [← Finset.prod_mul_distrib]
  by_cases hts : t = s
  · subst hts
    rw [if_pos rfl]
    exact Finset.prod_congr rfl fun i _ => ((exists_unitary_diagonal_of_isHermitian g₀ (gs i) (hgs i) θ).1.idem (t i)).eq
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp hts
    rw [if_neg hts]
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    rw [(exists_unitary_diagonal_of_isHermitian g₀ (gs i) (hgs i) θ).1.toOrthogonalIdempotents.mul_eq (t i) (s i), if_neg hi]

theorem GlobalTheory.EtC.GalSec.Tens.lem_hom : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (B : Type) [CommRing B] (k : ℕ) (g₀ : Ω →+* B) (gs : Fin k → (Ω →+* B)), (∀ i, (gs i).comp (algebraMap K Ω) = g₀.comp (algebraMap K Ω)) → ∀ θ : Ω, ∃ v : GlobalTheory.EtC.GalSec.LCRing K Ω k →+* B, ∀ φ, v φ = GlobalTheory.EtC.GalSec.Tens.lev g₀ gs θ φ := by
  intro K Ω _ _ _ _ B _ k g₀ gs hgs θ
  classical
  refine ⟨{ toFun := fun φ => Tens.lev g₀ gs θ φ, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, fun φ => rfl⟩
  · simp only [Tens.lev, LocallyConstant.coe_one, Pi.one_apply, map_one, one_mul]
    exact sum_prod_tens_idem g₀ gs hgs θ
  · intro φ ψ
    simp only [Tens.lev, LocallyConstant.coe_mul, Pi.mul_apply, map_mul]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_congr rfl fun s _ => by rw [mul_mul_mul_comm, prod_tens_idem_mul g₀ gs hgs θ]]
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  · simp [Tens.lev]
  · intro φ ψ
    simp only [Tens.lev, LocallyConstant.coe_add, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
private theorem polynomial_eval_eq_sum_eval_mul_idempotent {ι B : Type} [Fintype ι] [CommRing B] (e : ι → B) (he : ∑ i, e i = 1)
    (c : ι → B) (b : B) (hb : ∀ i, b * e i = c i * e i) (q : Polynomial B) :
    q.eval b = ∑ i, q.eval (c i) * e i := by
  have key : ∀ i, q.eval b * e i = q.eval (c i) * e i := by
    intro i
    refine Polynomial.induction_on' q (fun p r hp hr => ?_) (fun n a => ?_)
    · simp only [Polynomial.eval_add, add_mul, hp, hr]
    · have hpow : ∀ m : ℕ, b ^ m * e i = c i ^ m * e i := by
        intro m
        induction m with
        | zero => simp
        | succ m ih =>
          calc b ^ (m + 1) * e i = b ^ m * (b * e i) := by ring
            _ = b ^ m * (c i * e i) := by rw [hb i]
            _ = c i * (b ^ m * e i) := by ring
            _ = c i * (c i ^ m * e i) := by rw [ih]
            _ = c i ^ (m + 1) * e i := by ring
      simp only [Polynomial.eval_monomial]
      rw [mul_assoc, hpow n, ← mul_assoc]
  calc q.eval b = q.eval b * ∑ i, e i := by rw [he, mul_one]
    _ = ∑ i, q.eval (c i) * e i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => key i

private theorem mul_prod_eval_sub_eq_eval_C_mul_prod {ι B : Type} [CommRing B] (S : Finset ι) (a : B) (c : ι → B)
    (P : Polynomial B) (y : B) :
    a * ∏ j ∈ S, (P.eval y - c j) =
      (Polynomial.C a * ∏ j ∈ S, (P - Polynomial.C (c j))).eval y := by
  simp [Polynomial.eval_prod]

private theorem tens_idem_self {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {B : Type} [CommRing B]
    (g₀ : Ω →+* B) (θ r : Ω) (hr : r ∈ Tens.conj K Ω θ) :
    Tens.idem (K := K) g₀ θ (g₀ r) ⟨r, hr⟩ = 1 := by
  classical
  unfold Tens.idem
  simp only [← map_sub, ← map_prod, ← map_mul]
  rw [inv_mul_cancel₀, map_one]
  refine Finset.prod_ne_zero_iff.mpr fun j hj => sub_ne_zero.mpr fun e => ?_
  exact Finset.ne_of_mem_erase hj (Subtype.ext e.symm)

private theorem tens_idem_of_ne {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {B : Type} [CommRing B]
    (g₀ : Ω →+* B) (θ r : Ω) (hr : r ∈ Tens.conj K Ω θ) (s : Tens.conj K Ω θ)
    (h : (⟨r, hr⟩ : Tens.conj K Ω θ) ≠ s) :
    Tens.idem (K := K) g₀ θ (g₀ r) s = 0 := by
  classical
  unfold Tens.idem
  refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (i := ⟨r, hr⟩) ?_ (sub_self _))
  exact Finset.mem_erase.mpr ⟨h, Finset.mem_univ _⟩

theorem GlobalTheory.EtC.GalSec.Tens.lem_indep : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (B : Type) [CommRing B] (k : ℕ) (g₀ : Ω →+* B) (gs : Fin k → (Ω →+* B)), (∀ i, (gs i).comp (algebraMap K Ω) = g₀.comp (algebraMap K Ω)) → ∀ (θ θ' : Ω) (φ : GlobalTheory.EtC.GalSec.LCRing K Ω k), θ ∈ IntermediateField.adjoin K {θ'} → GlobalTheory.EtC.GalSec.Tens.DependsOn K Ω k θ φ → GlobalTheory.EtC.GalSec.Tens.lev g₀ gs θ φ = GlobalTheory.EtC.GalSec.Tens.lev g₀ gs θ' φ := by
  intro K Ω _ _ _ _ B _ k g₀ gs hgs θ θ' φ hθ hφ
  classical
  have hθ' : θ ∈ Algebra.adjoin K {θ'} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (Algebra.IsAlgebraic.isAlgebraic θ')]
    exact hθ
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hθ'
  obtain ⟨p, hp⟩ := hθ'
  replace hp : Polynomial.aeval θ' p = θ := hp
  have hπ : ∀ s' : Tens.conj K Ω θ', Polynomial.aeval (s' : Ω) p ∈ Tens.conj K Ω θ := by
    intro s'
    obtain ⟨σ, hσ⟩ := (Tens.mem_conj_iff θ' s').mp s'.2
    have e1 : Polynomial.aeval (σ θ') p = σ (Polynomial.aeval θ' p) :=
      Polynomial.aeval_algHom_apply (σ : Ω →ₐ[K] Ω) θ' p
    rw [← hσ, e1, hp]
    exact Tens.apply_mem_conj θ σ
  have hrel : ∀ (i : Fin k) (s : Tens.conj K Ω θ), Tens.idem (K := K) g₀ θ (gs i θ) s =
      ∑ s' : Tens.conj K Ω θ', if (⟨Polynomial.aeval (s' : Ω) p, hπ s'⟩ : Tens.conj K Ω θ) = s then
        Tens.idem (K := K) g₀ θ' (gs i θ') s' else 0 := by
    intro i s
    obtain ⟨hco, hmul, -⟩ := exists_unitary_diagonal_of_isHermitian g₀ (gs i) (hgs i) θ'
    have hb : gs i θ = (p.map (g₀.comp (algebraMap K Ω))).eval (gs i θ') := by
      rw [← hp, Polynomial.aeval_def, Polynomial.hom_eval₂, hgs i, Polynomial.eval_map]
    have hs' : ∀ s' : Tens.conj K Ω θ', (p.map (g₀.comp (algebraMap K Ω))).eval (g₀ s') =
        g₀ (Polynomial.aeval (s' : Ω) p) := by
      intro s'
      rw [Polynomial.aeval_def, Polynomial.hom_eval₂, Polynomial.eval_map]
    obtain ⟨Q, hQ⟩ : ∃ Q : Polynomial B, ∀ y, Tens.idem (K := K) g₀ θ
        ((p.map (g₀.comp (algebraMap K Ω))).eval y) s = Q.eval y := by
      unfold Tens.idem
      exact ⟨_, fun y => mul_prod_eval_sub_eq_eval_C_mul_prod _ _ (fun j : Tens.conj K Ω θ => g₀ (j : Ω)) _ y⟩
    rw [hb, hQ, polynomial_eval_eq_sum_eval_mul_idempotent _ hco.complete (fun s' => g₀ s') _ (fun s' => hmul s')]
    refine Finset.sum_congr rfl fun s' _ => ?_
    rw [← hQ, hs']
    split_ifs with h
    · subst h
      rw [tens_idem_self g₀ θ _ (hπ s'), one_mul]
    · rw [tens_idem_of_ne g₀ θ _ (hπ s') s h, zero_mul]
  have hsum : ∀ t : Fin k → Tens.conj K Ω θ, ∏ i, Tens.idem (K := K) g₀ θ (gs i θ) (t i) =
      ∑ t' : Fin k → Tens.conj K Ω θ', if (fun i => (⟨Polynomial.aeval (t' i : Ω) p, hπ (t' i)⟩ :
        Tens.conj K Ω θ)) = t then ∏ i, Tens.idem (K := K) g₀ θ' (gs i θ') (t' i) else 0 := by
    intro t
    rw [Finset.prod_congr rfl fun i _ => hrel i (t i), ← sum_pi_prod_eq_prod_sum]
    refine Finset.sum_congr rfl fun t' _ => ?_
    simp only [Finset.prod_ite_zero, funext_iff, Finset.mem_univ, true_implies]
  have key : ∀ t' : Fin k → Tens.conj K Ω θ',
      φ (Tens.pick K Ω k θ (fun i => Polynomial.aeval (t' i : Ω) p)) =
        φ (Tens.pick K Ω k θ' (fun i => (t' i : Ω))) := by
    intro t'
    apply hφ
    intro i
    rw [Tens.pick_spec (K := K) k θ _ (fun j => hπ (t' j)) i, ← hp]
    have e2 := Polynomial.aeval_algHom_apply
      ((Tens.pick K Ω k θ' (fun j => (t' j : Ω)) i : Ω ≃ₐ[K] Ω) : Ω →ₐ[K] Ω) θ' p
    have e3 : (Tens.pick K Ω k θ' (fun j => (t' j : Ω)) i) θ' = t' i :=
      Tens.pick_spec (K := K) k θ' _ (fun j => (t' j).2) i
    rw [show ((Tens.pick K Ω k θ' (fun j => (t' j : Ω)) i : Ω ≃ₐ[K] Ω) : Ω →ₐ[K] Ω) θ' = t' i from e3] at e2
    exact e2
  unfold Tens.lev
  simp only [hsum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t' _ => ?_
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, key]
theorem GlobalTheory.EtC.GalSec.Tens.lem_legs : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (B : Type) [CommRing B] (k : ℕ) (g₀ : Ω →+* B) (gs : Fin k → (Ω →+* B)), (∀ i, (gs i).comp (algebraMap K Ω) = g₀.comp (algebraMap K Ω)) → (∀ (θ a : Ω), GlobalTheory.EtC.GalSec.Tens.lev g₀ gs θ (GlobalTheory.EtC.GalSec.legHom K Ω k 0 a) = g₀ a) ∧ ∀ (i : Fin k) (a : Ω), GlobalTheory.EtC.GalSec.Tens.lev g₀ gs a (GlobalTheory.EtC.GalSec.legHom K Ω k i.succ a) = gs i a := by
  intro K Ω _ _ _ _ B _ k g₀ gs hgs
  classical
  refine ⟨fun θ a => ?_, fun i a => ?_⟩
  · have h0 : legHom K Ω k 0 a = LocallyConstant.const _ a := rfl
    simp only [Tens.lev, h0, LocallyConstant.coe_const, Function.const_apply]
    rw [← Finset.mul_sum, sum_prod_tens_idem g₀ gs hgs θ, mul_one]
  · have h1 : legHom K Ω k i.succ a = coord K Ω k i a := by simp [legHom]
    have hp : ∀ t : Fin k → Tens.conj K Ω a, (Tens.pick K Ω k a (fun j => (t j : Ω)) i) a = t i :=
      fun t => Tens.pick_spec (K := K) k a _ (fun j => (t j).2) i
    simp only [Tens.lev, h1, coord_apply, hp]
    have hfac : ∀ t : Fin k → Tens.conj K Ω a,
        g₀ (t i : Ω) * ∏ j, Tens.idem (K := K) g₀ a (gs j a) (t j) =
          ∏ j, (if j = i then g₀ (t j : Ω) else 1) * Tens.idem (K := K) g₀ a (gs j a) (t j) := by
      intro t
      rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ i, if_pos (Finset.mem_univ _)]
    rw [Finset.sum_congr rfl fun t _ => hfac t,
      sum_pi_prod_eq_prod_sum (fun (j : Fin k) (s : Tens.conj K Ω a) => (if j = i then g₀ (s : Ω) else 1) * Tens.idem (K := K) g₀ a (gs j a) s)]
    rw [Finset.prod_eq_single i]
    · simp only [if_true]
      exact (exists_unitary_diagonal_of_isHermitian g₀ (gs i) (hgs i) a).2.2.symm
    · intro j _ hj
      simp only [if_neg hj, one_mul]
      exact (exists_unitary_diagonal_of_isHermitian g₀ (gs j) (hgs j) a).1.complete
    · intro h; exact absurd (Finset.mem_univ i) h
private theorem map_tens_idem {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {B C : Type} [CommRing B]
    [CommRing C] (f : B →+* C) (g₀ : Ω →+* B) (θ : Ω) (b : B) (s : Tens.conj K Ω θ) :
    f (Tens.idem (K := K) g₀ θ b s) = Tens.idem (K := K) (f.comp g₀) θ (f b) s := by
  unfold Tens.idem
  simp only [map_mul, map_prod, map_sub, RingHom.comp_apply]

private theorem map_tens_lev {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {B C : Type} [CommRing B]
    [CommRing C] (f : B →+* C) (g₀ : Ω →+* B) {k : ℕ} (gs : Fin k → (Ω →+* B)) (θ : Ω)
    (φ : LCRing K Ω k) :
    f (Tens.lev g₀ gs θ φ) = Tens.lev (f.comp g₀) (fun i => f.comp (gs i)) θ φ := by
  unfold Tens.lev
  simp only [map_sum, map_mul, map_prod, map_tens_idem, RingHom.comp_apply]

private theorem tens_lev_legHom_eq_of_dependsOn {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (k : ℕ)
    (θ : Ω) (φ : LCRing K Ω k) (hφ : Tens.DependsOn K Ω k θ φ) :
    Tens.lev (legHom K Ω k 0) (fun i => legHom K Ω k i.succ) θ φ = φ := by
  classical
  ext g
  change LocallyConstant.evalRingHom g (Tens.lev (legHom K Ω k 0) (fun i => legHom K Ω k i.succ) θ φ) = φ g
  rw [map_tens_lev]
  have h0 : (LocallyConstant.evalRingHom g).comp (legHom K Ω k 0) = RingHom.id Ω := by
    ext a; simp [legHom]
  have h1 : ∀ i, ((LocallyConstant.evalRingHom g).comp (legHom K Ω k i.succ)) θ = g i θ := by
    intro i; simp [legHom, coord_apply]
  have hmem : ∀ i, g i θ ∈ Tens.conj K Ω θ := fun i => Tens.apply_mem_conj θ (g i)
  unfold Tens.lev
  simp only [h0, h1, RingHom.id_apply]
  rw [Finset.sum_eq_single (fun i => (⟨g i θ, hmem i⟩ : Tens.conj K Ω θ))]
  · dsimp only
    rw [Finset.prod_eq_one (fun i _ => by
      have := tens_idem_self (K := K) (RingHom.id Ω) θ (g i θ) (hmem i)
      rwa [RingHom.id_apply] at this), mul_one]
    exact hφ _ _ (fun i => Tens.pick_spec (K := K) k θ _ (fun j => hmem j) i)
  · intro t _ ht
    obtain ⟨i, hi⟩ := Function.ne_iff.mp ht
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by
      have := tens_idem_of_ne (K := K) (RingHom.id Ω) θ (g i θ) (hmem i) (t i) (Ne.symm hi)
      rwa [RingHom.id_apply] at this), mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem GlobalTheory.EtC.GalSec.Tens.lem_uniq : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (k : ℕ) (B : Type) [CommRing B] (u u' : GlobalTheory.EtC.GalSec.LCRing K Ω k →+* B), (∀ φ : GlobalTheory.EtC.GalSec.LCRing K Ω k, ∃ θ : Ω, GlobalTheory.EtC.GalSec.Tens.DependsOn K Ω k θ φ) → (∀ i, u.comp (GlobalTheory.EtC.GalSec.legHom K Ω k i) = u'.comp (GlobalTheory.EtC.GalSec.legHom K Ω k i)) → u = u' := by
  intro K Ω _ _ _ _ k B _ u u' hdep hleg
  ext φ
  obtain ⟨θ, hθ⟩ := hdep φ
  rw [← tens_lev_legHom_eq_of_dependsOn k θ φ hθ, map_tens_lev, map_tens_lev]
  simp only [hleg]

namespace GlobalTheory.EtC.GalSec.Tens

theorem lcRing_universal : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (k : ℕ) (B : Type) [CommRing B] (g : Fin (k + 1) → (Ω →+* B)) (c : K →+* B), (∀ i, (g i).comp (algebraMap K Ω) = c) → ∃! u : GlobalTheory.EtC.GalSec.LCRing K Ω k →+* B, u.comp (GlobalTheory.EtC.GalSec.baseHom K Ω k) = c ∧ ∀ i, u.comp (GlobalTheory.EtC.GalSec.legHom K Ω k i) = g i := by
  intro K Ω _ _ _ _ k B _ g c hg
  classical
  set g₀ := g 0 with hg₀
  set gs : Fin k → (Ω →+* B) := fun i => g i.succ with hgsd
  have hgs : ∀ i, (gs i).comp (algebraMap K Ω) = g₀.comp (algebraMap K Ω) :=
    fun i => (hg i.succ).trans (hg 0).symm
  choose θf hθf using fun φ : LCRing K Ω k => lem_dep K Ω k φ
  have hwd : ∀ (φ : LCRing K Ω k) (θ : Ω), DependsOn K Ω k θ φ →
      lev g₀ gs θ φ = lev g₀ gs (θf φ) φ := by
    intro φ θ hθ
    obtain ⟨η, h1, h2⟩ := lem_ref K Ω θ (θf φ)
    rw [lem_indep K Ω B k g₀ gs hgs θ η φ h1 hθ, lem_indep K Ω B k g₀ gs hgs (θf φ) η φ h2 (hθf φ)]
  have hcommon : ∀ φ ψ : LCRing K Ω k, ∃ η, DependsOn K Ω k η φ ∧ DependsOn K Ω k η ψ := by
    intro φ ψ
    obtain ⟨η, h1, h2⟩ := lem_ref K Ω (θf φ) (θf ψ)
    exact ⟨η, lem_mono K Ω k _ η φ h1 (hθf φ), lem_mono K Ω k _ η ψ h2 (hθf ψ)⟩
  have hdmul : ∀ η (φ ψ : LCRing K Ω k), DependsOn K Ω k η φ → DependsOn K Ω k η ψ →
      DependsOn K Ω k η (φ * ψ) := by
    intro η φ ψ h1 h2 x x' h
    simp only [LocallyConstant.coe_mul, Pi.mul_apply, h1 x x' h, h2 x x' h]
  have hdadd : ∀ η (φ ψ : LCRing K Ω k), DependsOn K Ω k η φ → DependsOn K Ω k η ψ →
      DependsOn K Ω k η (φ + ψ) := by
    intro η φ ψ h1 h2 x x' h
    simp only [LocallyConstant.coe_add, Pi.add_apply, h1 x x' h, h2 x x' h]
  obtain ⟨u, hu⟩ : ∃ u : LCRing K Ω k →+* B, ∀ φ, u φ = lev g₀ gs (θf φ) φ := by
    refine ⟨{ toFun := fun φ => lev g₀ gs (θf φ) φ, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, fun _ => rfl⟩
    · obtain ⟨v, hv⟩ := lem_hom K Ω B k g₀ gs hgs (θf 1)
      show lev g₀ gs (θf 1) 1 = 1
      rw [← hv, map_one]
    · intro φ ψ
      obtain ⟨η, h1, h2⟩ := hcommon φ ψ
      obtain ⟨v, hv⟩ := lem_hom K Ω B k g₀ gs hgs η
      show lev g₀ gs (θf (φ * ψ)) (φ * ψ) = lev g₀ gs (θf φ) φ * lev g₀ gs (θf ψ) ψ
      rw [← hwd _ η (hdmul η φ ψ h1 h2), ← hwd φ η h1, ← hwd ψ η h2, ← hv, ← hv, ← hv, map_mul]
    · obtain ⟨v, hv⟩ := lem_hom K Ω B k g₀ gs hgs (θf 0)
      show lev g₀ gs (θf 0) 0 = 0
      rw [← hv, map_zero]
    · intro φ ψ
      obtain ⟨η, h1, h2⟩ := hcommon φ ψ
      obtain ⟨v, hv⟩ := lem_hom K Ω B k g₀ gs hgs η
      show lev g₀ gs (θf (φ + ψ)) (φ + ψ) = lev g₀ gs (θf φ) φ + lev g₀ gs (θf ψ) ψ
      rw [← hwd _ η (hdadd η φ ψ h1 h2), ← hwd φ η h1, ← hwd ψ η h2, ← hv, ← hv, ← hv, map_add]
  have hlegs : ∀ i, u.comp (legHom K Ω k i) = g i := by
    intro i
    cases i using Fin.cases with
    | zero =>
      ext x
      rw [RingHom.comp_apply, hu, (lem_legs K Ω B k g₀ gs hgs).1]
    | succ j =>
      ext x
      have hdep : DependsOn K Ω k x (legHom K Ω k j.succ x) := by
        intro y y' h
        simp only [legHom, Fin.cases_succ, coord_apply]
        exact h j
      rw [RingHom.comp_apply, hu, ← hwd _ x hdep, (lem_legs K Ω B k g₀ gs hgs).2 j x]
  have hbase : u.comp (baseHom K Ω k) = c := by
    ext a
    have e : baseHom K Ω k a = legHom K Ω k 0 (algebraMap K Ω a) := rfl
    rw [RingHom.comp_apply, e, ← RingHom.comp_apply, hlegs 0]
    exact RingHom.congr_fun (hg 0) a
  exact ⟨u, ⟨hbase, hlegs⟩, fun u' hu' => lem_uniq K Ω k B u' u (fun φ => lem_dep K Ω k φ)
    fun i => (hu'.2 i).trans (hlegs i).symm⟩

end GlobalTheory.EtC.GalSec.Tens
