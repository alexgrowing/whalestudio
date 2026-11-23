import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDualWeylWeightProjector
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.HighWtEmb

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HighWtEmb.NabInter

variable {k : Type} [Field k]

def mr {σ A B : Type} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] (L : A →ₗ[k] B)
    (F : MvPolynomial σ A) : MvPolynomial σ B :=
  ∑ m ∈ F.support, monomial m (L (coeff m F))

section
variable {σ A B : Type} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] (L : A →ₗ[k] B)

theorem coeff_mr (F : MvPolynomial σ A) (m : σ →₀ ℕ) : coeff m (mr L F) = L (coeff m F) := by
  classical
  simp only [mr, coeff_sum, coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [MvPolynomial.notMem_support_iff.mp h, map_zero]

theorem mr_add (F G : MvPolynomial σ A) : mr L (F + G) = mr L F + mr L G := by
  ext m; simp [coeff_mr]

theorem mr_smul (c : k) (F : MvPolynomial σ A) : mr L (c • F) = c • mr L F := by
  ext m; simp [coeff_mr, coeff_smul]

theorem mr_monomial (m : σ →₀ ℕ) (a : A) : mr L (monomial m a) = monomial m (L a) := by
  classical
  ext n; simp only [coeff_mr, coeff_monomial]; split_ifs <;> simp

theorem mr_C (a : A) : mr L (C a : MvPolynomial σ A) = C (L a) := mr_monomial L 0 a

theorem mr_map_mul (q : MvPolynomial σ k) (F : MvPolynomial σ A) :
    mr L (map (algebraMap k A) q * F) = map (algebraMap k B) q * mr L F := by
  classical
  ext n
  simp only [coeff_mr, coeff_mul, coeff_map, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Algebra.smul_def (coeff x.1 q) (coeff x.2 F), LinearMap.map_smul, Algebra.smul_def]
end

theorem mr_C_mul_map {σ A : Type} [CommRing A] [Algebra k A] (L : A →ₗ[k] k) (c : A) (h : MvPolynomial σ k) :
    mr L (C c * map (algebraMap k A) h) = L c • h := by
  ext n
  simp only [coeff_mr, coeff_C_mul, coeff_map, coeff_smul, smul_eq_mul]
  rw [← Algebra.commutes, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul, mul_comm]

theorem commAlgEquiv_monomial_one {S₁ S₂ : Type} (m' : S₁ →₀ ℕ) :
    commAlgEquiv k S₁ S₂ (monomial m' 1) = C (monomial m' 1) := by
  rw [monomial_eq, monomial_eq, C_1, C_1, one_mul, one_mul]
  simp only [Finsupp.prod, map_prod, map_pow, commAlgEquiv_X]

theorem coeff_coeff_commAlgEquiv {S₁ S₂ : Type} (F : MvPolynomial S₁ (MvPolynomial S₂ k)) (β : S₂ →₀ ℕ) (m : S₁ →₀ ℕ) :
    coeff m (coeff β (commAlgEquiv k S₁ S₂ F)) = coeff β (coeff m F) := by
  classical
  induction F using MvPolynomial.induction_on' with
  | monomial m' a =>
    have : (monomial m' a : MvPolynomial S₁ (MvPolynomial S₂ k)) = C a * monomial m' 1 := by
      rw [C_mul_monomial, mul_one]
    rw [this, map_mul, commAlgEquiv_C, commAlgEquiv_monomial_one, mul_comm, coeff_C_mul, coeff_map,
      ← this, coeff_monomial]
    rw [mul_comm, C_mul_monomial, mul_one, coeff_monomial]
    split_ifs <;> simp
  | add p q hp hq => simp [hp, hq]

end GlobalTheory.HighWtEmb.NabInter

namespace GlobalTheory.HighWtEmb.NabInter
variable {k : Type} [Field k]

theorem mr_aeval {σ τ' A : Type} [CommRing A] [Algebra k A] (L : A →ₗ[k] k) (g : σ → MvPolynomial τ' k)
    (F : MvPolynomial σ A) :
    mr L (aeval (fun v => map (algebraMap k A) (g v)) F) = aeval g (mr L F) := by
  induction F using MvPolynomial.induction_on' with
  | monomial u a =>
    have h1 : aeval (fun v => map (algebraMap k A) (g v)) (monomial u (1 : A)) =
        map (algebraMap k A) (aeval g (monomial u (1 : k))) := by
      simp only [aeval_monomial, Finsupp.prod, map_prod, map_pow, map_one, one_mul, map_mul, map_X]
    have h2 : (monomial u a : MvPolynomial σ A) = C a * monomial u 1 := by rw [C_mul_monomial, mul_one]
    rw [h2, map_mul, aeval_C, h1, algebraMap_eq, mr_C_mul_map, ← h2, mr_monomial,
      show (monomial u (L a) : MvPolynomial σ k) = L a • monomial u 1 by rw [smul_monomial, smul_eq_mul, mul_one],
      map_smul]
  | add p q hp hq => rw [map_add, mr_add, hp, hq, mr_add, map_add]

theorem colAddGen_eq_aeval (A : Type) [CommRing A] [Algebra k A] {r n : ℕ} (l j : Fin n) :
    colAddGen A (r := r) l j = aeval (fun v => map (algebraMap k A)
      ((if v.2 = j then X (some v) + X none * X (some (v.1, l)) else X (some v) :
        MvPolynomial (Option (Fin r × Fin n)) k))) := by
  unfold colAddGen
  congr 1
  funext v
  split_ifs <;> simp

theorem rename_some_eq_aeval (A : Type) [CommRing A] [Algebra k A] {r n : ℕ} :
    (rename (R := A) (some : Fin r × Fin n → Option (Fin r × Fin n))) =
      aeval (fun v => map (algebraMap k A) (X (some v) : MvPolynomial (Option (Fin r × Fin n)) k)) := by
  apply MvPolynomial.algHom_ext
  intro v
  simp

theorem dualWeyl_mr {A : Type} [CommRing A] [Algebra k A] (L : A →ₗ[k] k) (r n : ℕ) (ν : Fin n → ℕ)
    (F : MvPolynomial (Fin r × Fin n) A) (hF : F ∈ dualWeyl A r n ν) : mr L F ∈ dualWeyl k r n ν := by
  simp only [dualWeyl, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    AlgHom.toLinearMap_apply, sub_eq_zero, mem_weightedHomogeneousSubmodule] at hF ⊢
  obtain ⟨h1, h2⟩ := hF
  refine ⟨?_, fun l j hlj => ?_⟩
  · intro d hd
    apply h1
    intro h0
    apply hd
    rw [coeff_mr, h0, map_zero]
  · have := congrArg (mr L) (h2 l j hlj)
    rw [colAddGen_eq_aeval (k := k), rename_some_eq_aeval (k := k), mr_aeval, mr_aeval] at this
    rw [colAddGen_eq_aeval (k := k), rename_some_eq_aeval (k := k)]
    simpa [Algebra.algebraMap_self, map_id] using this

end GlobalTheory.HighWtEmb.NabInter

namespace GlobalTheory.HighWtEmb.NabInter
variable {k : Type} [Field k]

theorem exists_proj {M : Type} [AddCommGroup M] [Module k M] (D : Submodule k M) :
    ∃ π : M →ₗ[k] M, (∀ f, π f ∈ D) ∧ ∀ f ∈ D, π f = f := by
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl D
  refine ⟨D.subtype ∘ₗ Submodule.projectionOnto D q hq, fun f => by simp, fun f hf => ?_⟩
  have := Submodule.projectionOnto_apply_left hq ⟨f, hf⟩
  simpa using congrArg Subtype.val this

def mrL {σ A B : Type} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] (L : A →ₗ[k] B) :
    MvPolynomial σ A →ₗ[k] MvPolynomial σ B where
  toFun := mr L
  map_add' := mr_add L
  map_smul' c F := by rw [mr_smul, RingHom.id_apply]

section
variable (N : ℕ) {ι : Type} [DecidableEq ι]

def splitEquiv (τ : ι) : BVar N ι ≃ OVar N τ ⊕ (Fin N × Fin N) where
  toFun p := if h : p.1 = τ then Sum.inr p.2 else Sum.inl ⟨p, h⟩
  invFun := Sum.elim Subtype.val (fun v => (τ, v))
  left_inv p := by
    obtain ⟨a, v⟩ := p
    by_cases h : a = τ
    · subst h; simp
    · simp [h]
  right_inv x := by
    rcases x with ⟨p, hp⟩ | v
    · simp [hp]
    · simp

def Ψ (τ : ι) :
    MvPolynomial (BVar N ι) k ≃ₐ[k] MvPolynomial (OVar N τ) (MvPolynomial (Fin N × Fin N) k) :=
  (renameEquiv k (splitEquiv N τ)).trans (sumAlgEquiv k _ _)

theorem Ψ_X_self (τ : ι) (v : Fin N × Fin N) : Ψ (k := k) N τ (X (τ, v)) = C (X v) := by
  simp [Ψ, splitEquiv]

theorem Ψ_X_ne (τ : ι) (p : BVar N ι) (h : p.1 ≠ τ) : Ψ (k := k) N τ (X p) = X ⟨p, h⟩ := by
  simp [Ψ, splitEquiv, h]

theorem Ψ_rename_self (τ : ι) (f : MvPolynomial (Fin N × Fin N) k) :
    Ψ N τ (rename (fun v : Fin N × Fin N => ((τ, v) : BVar N ι)) f) = C f := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    have := (Ψ (k := k) N τ).commutes a
    simpa [MvPolynomial.algebraMap_apply] using this
  | add p q hp hq => simp [hp, hq]
  | mul_X p v ih => simp [ih, Ψ_X_self]

theorem Ψ_rename_ne (τ σ : ι) (h : σ ≠ τ) (f : MvPolynomial (Fin N × Fin N) k) :
    Ψ N τ (rename (fun v : Fin N × Fin N => ((σ, v) : BVar N ι)) f) =
      map (algebraMap k (MvPolynomial (Fin N × Fin N) k))
        (rename (fun v : Fin N × Fin N => (⟨(σ, v), h⟩ : OVar N τ)) f) := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    have := (Ψ (k := k) N τ).commutes a
    simpa [MvPolynomial.algebraMap_apply] using this
  | add p q hp hq => simp [hp, hq]
  | mul_X p v ih => simp [ih, Ψ_X_ne N τ (σ, v) h]

theorem Ψ_eq_toBlock (τ : ι) (P : MvPolynomial (BVar N ι) k) :
    Ψ N τ P = commAlgEquiv k (Fin N × Fin N) (OVar N τ) (toBlock k N τ P) := by
  have : (Ψ (k := k) N τ).toAlgHom = (commAlgEquiv k (Fin N × Fin N) (OVar N τ)).toAlgHom.comp (toBlock k N τ) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, v⟩
    by_cases h : a = τ
    · subst h; simp [toBlock, Ψ_X_self]
    · simp [toBlock, h, Ψ_X_ne N τ (a, v) h]
  exact congrArg (fun φ : MvPolynomial (BVar N ι) k →ₐ[k] _ => φ P) this

end

end GlobalTheory.HighWtEmb.NabInter

namespace GlobalTheory.HighWtEmb.NabInter
variable {k : Type} [Field k]

section
variable (N : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι]

def E (τ : ι) (π : MvPolynomial (Fin N × Fin N) k →ₗ[k] MvPolynomial (Fin N × Fin N) k) :
    MvPolynomial (BVar N ι) k →ₗ[k] MvPolynomial (BVar N ι) k :=
  (Ψ N τ).symm.toLinearMap ∘ₗ mrL π ∘ₗ (Ψ N τ).toLinearMap

def gen (D : ι → Submodule k (MvPolynomial (Fin N × Fin N) k)) (T : Finset ι) :
    Set (MvPolynomial (BVar N ι) k) :=
  {Q | ∃ f : ι → MvPolynomial (Fin N × Fin N) k, (∀ σ ∈ T, f σ ∈ D σ) ∧
    Q = ∏ σ, rename (fun v : Fin N × Fin N => ((σ, v) : BVar N ι)) (f σ)}

theorem E_gen (D : ι → Submodule k (MvPolynomial (Fin N × Fin N) k)) (T : Finset ι) (τ : ι)
    (π : MvPolynomial (Fin N × Fin N) k →ₗ[k] MvPolynomial (Fin N × Fin N) k) (hπ : ∀ f, π f ∈ D τ)
    (Q : MvPolynomial (BVar N ι) k) (hQ : Q ∈ gen N D T) : E N τ π Q ∈ gen N D (insert τ T) := by
  obtain ⟨f, hf, rfl⟩ := hQ
  set A := ∏ σ ∈ Finset.univ.erase τ, rename (fun v : Fin N × Fin N => ((σ, v) : BVar N ι)) (f σ) with hAdef
  have hsplit : ∏ σ, rename (fun v : Fin N × Fin N => ((σ, v) : BVar N ι)) (f σ) =
      A * rename (fun v : Fin N × Fin N => ((τ, v) : BVar N ι)) (f τ) :=
    (Finset.prod_erase_mul _ _ (Finset.mem_univ τ)).symm
  have hA : ∃ q, Ψ N τ A = map (algebraMap k (MvPolynomial (Fin N × Fin N) k)) q := by
    refine Finset.prod_induction _ (fun x => ∃ q, Ψ N τ x = map (algebraMap k (MvPolynomial (Fin N × Fin N) k)) q)
      (fun a b ⟨qa, ha⟩ ⟨qb, hb⟩ => ⟨qa * qb, by rw [map_mul, ha, hb, map_mul]⟩) ⟨1, by simp⟩ ?_
    intro σ hσ
    exact ⟨_, Ψ_rename_ne N τ σ (Finset.ne_of_mem_erase hσ) (f σ)⟩
  obtain ⟨q, hq⟩ := hA
  refine ⟨Function.update f τ (π (f τ)), ?_, ?_⟩
  · intro σ hσ
    by_cases h : σ = τ
    · subst h; simp [hπ]
    · rw [Function.update_of_ne h]
      exact hf σ (by simpa [h] using hσ)
  · have hA' : ∏ σ ∈ Finset.univ.erase τ,
        rename (fun v : Fin N × Fin N => ((σ, v) : BVar N ι)) (Function.update f τ (π (f τ)) σ) = A := by
      refine Finset.prod_congr rfl fun σ hσ => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hσ)]
    have hR : ∏ σ, rename (fun v : Fin N × Fin N => ((σ, v) : BVar N ι)) (Function.update f τ (π (f τ)) σ) =
        A * rename (fun v : Fin N × Fin N => ((τ, v) : BVar N ι)) (π (f τ)) := by
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ τ), Function.update_self, hA']
    rw [hR, hsplit]
    show (Ψ N τ).symm (mr π (Ψ N τ (A * rename (fun v : Fin N × Fin N => ((τ, v) : BVar N ι)) (f τ)))) =
      A * rename (fun v : Fin N × Fin N => ((τ, v) : BVar N ι)) (π (f τ))
    rw [map_mul, hq, Ψ_rename_self, mr_map_mul, mr_C, ← Ψ_rename_self N τ, ← hq, ← map_mul,
      AlgEquiv.symm_apply_apply]

theorem span_gen_empty (D : ι → Submodule k (MvPolynomial (Fin N × Fin N) k)) (P : MvPolynomial (BVar N ι) k) :
    P ∈ Submodule.span k (gen N D ∅) := by
  have hmulX : ∀ v : BVar N ι, ∀ Q ∈ Submodule.span k (gen N D ∅), Q * X v ∈ Submodule.span k (gen N D ∅) := by
    intro v Q hQ
    induction hQ using Submodule.span_induction with
    | mem Q hQ =>
      obtain ⟨f, -, rfl⟩ := hQ
      refine Submodule.subset_span ⟨fun σ => f σ * (if σ = v.1 then X v.2 else 1), by simp, ?_⟩
      simp only [map_mul, Finset.prod_mul_distrib]
      congr 1
      simp only [apply_ite, rename_X, map_one]
      rw [Finset.prod_ite_eq']
      simp
    | zero => simp
    | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
    | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx
  induction P using MvPolynomial.induction_on with
  | C a =>
    have h1 : (1 : MvPolynomial (BVar N ι) k) ∈ gen N D ∅ := ⟨fun _ => 1, by simp, by simp⟩
    rw [show (C a : MvPolynomial (BVar N ι) k) = a • 1 by rw [smul_eq_C_mul, mul_one]]
    exact Submodule.smul_mem _ a (Submodule.subset_span h1)
  | add p q hp hq => exact add_mem hp hq
  | mul_X p v ih => exact hmulX v p ih

theorem mem_span_gen_univ (D : ι → Submodule k (MvPolynomial (Fin N × Fin N) k)) (P : MvPolynomial (BVar N ι) k)
    (h : ∀ τ β, coeff β (Ψ N τ P) ∈ D τ) : P ∈ Submodule.span k (gen N D Finset.univ) := by
  choose π hπ1 hπ2 using fun τ => exists_proj (D τ)
  have key : ∀ T : Finset ι, P ∈ Submodule.span k (gen N D T) := by
    intro T
    induction T using Finset.induction_on with
    | empty => exact span_gen_empty N D P
    | insert τ T hτ ih =>
      have hfix : E N τ (π τ) P = P := by
        show (Ψ N τ).symm (mr (π τ) (Ψ N τ P)) = P
        have : mr (π τ) (Ψ N τ P) = Ψ N τ P := by
          ext β
          rw [coeff_mr, hπ2 τ _ (h τ β)]
        rw [this, AlgEquiv.symm_apply_apply]
      rw [← hfix]
      have hle : Submodule.span k (gen N D T) ≤ (Submodule.span k (gen N D (insert τ T))).comap (E N τ (π τ)) :=
        Submodule.span_le.mpr fun Q hQ => Submodule.subset_span (E_gen N D T τ (π τ) (hπ1 τ) Q hQ)
      exact hle ih
  exact key Finset.univ

end

end GlobalTheory.HighWtEmb.NabInter

namespace GlobalTheory.HighWtEmb

open NabInter in

theorem mem_nabK_of_toBlock : ∀ (k : Type) [Field k] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (ν : ι → Fin N → ℕ) (P : MvPolynomial (BVar N ι) k),
    (∀ τ, toBlock k N τ P ∈ dualWeyl (MvPolynomial (OVar N τ) k) N N (ν τ)) → P ∈ nabK k N ν := by
  intro k _ N ι _ _ ν P hP
  have h : ∀ τ β, coeff β (Ψ N τ P) ∈ dualWeyl k N N (ν τ) := by
    intro τ β
    have := dualWeyl_mr (lcoeff k β) N N (ν τ) _ (hP τ)
    convert this using 1
    ext m
    rw [Ψ_eq_toBlock, coeff_mr, lcoeff_apply, coeff_coeff_commAlgEquiv]
  have := mem_span_gen_univ N (fun τ => dualWeyl k N N (ν τ)) P h
  refine Submodule.span_mono ?_ this
  rintro Q ⟨f, hf, rfl⟩
  exact ⟨f, fun τ => hf τ (Finset.mem_univ τ), rfl⟩

end GlobalTheory.HighWtEmb

end
