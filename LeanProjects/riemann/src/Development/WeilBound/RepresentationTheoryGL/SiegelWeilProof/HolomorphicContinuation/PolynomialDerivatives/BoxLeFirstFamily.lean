import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.SymKEqZeroOfOm

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC

namespace CoreD

variable {m n : ℕ} {ε : Fin m → Bool}

theorem opMono_add (t : (Fin m × Fin n × Bool) ⊕ (Fin m × Fin n × Bool) →₀ ℕ) (f g : PX m n) :
    opMono t (f + g) = opMono t f + opMono t g := by
  simp [opMono, map_add, mul_add]

theorem opMono_smul (t : (Fin m × Fin n × Bool) ⊕ (Fin m × Fin n × Bool) →₀ ℕ) (r : ℂ) (f : PX m n) :
    opMono t (r • f) = r • opMono t f := by
  simp [opMono, map_smul, mul_smul_comm]

def opL (s : Sym m n) : Module.End ℂ (PX m n) where
  toFun := op s
  map_add' f g := by simp [op, opMono_add, smul_add, Finset.sum_add_distrib]
  map_smul' r f := by simp [op, opMono_smul, Finset.smul_sum, smul_comm r]

@[simp] theorem opL_apply (s : Sym m n) (f : PX m n) : opL s f = op s f := rfl

theorem op_eq (s : Sym m n) (T : Finset _) (h : s.support ⊆ T) (f : PX m n) :
    op s f = ∑ t ∈ T, s.coeff t • opMono t f := by
  unfold op
  refine Finset.sum_subset h fun t _ ht => ?_
  rw [mem_support_iff, not_not] at ht
  rw [ht, zero_smul]

theorem op_add_sym (s₁ s₂ : Sym m n) (f : PX m n) : op (s₁ + s₂) f = op s₁ f + op s₂ f := by
  classical
  rw [op_eq (s₁ + s₂) (s₁.support ∪ s₂.support) support_add, op_eq s₁ (s₁.support ∪ s₂.support)
    Finset.subset_union_left, op_eq s₂ (s₁.support ∪ s₂.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun t _ => by rw [coeff_add, add_smul]

theorem op_smul_sym (s : Sym m n) (r : ℂ) (f : PX m n) : op (r • s) f = r • op s f := by
  classical
  rw [op_eq (r • s) s.support support_smul, op, Finset.smul_sum]
  exact Finset.sum_congr rfl fun t _ => by rw [coeff_smul, smul_eq_mul, mul_smul]

theorem op_sum_sym {ι : Type*} (F : Finset ι) (g : ι → Sym m n) (f : PX m n) :
    op (∑ i ∈ F, g i) f = ∑ i ∈ F, op (g i) f := by
  classical
  induction F using Finset.induction_on with
  | empty => simp [op]
  | insert a F ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, op_add_sym, ih]

theorem box_le_first_family (R : Set (Fin m → ℕ)) : box (n := n) ε R ≤ F1 ε := by
  refine Submodule.span_le.2 fun p ⟨s, hs, _, hp⟩ => ?_
  subst hp
  change monomial s 1 ∈ MvPolynomial.supported ℂ {k | inF1 ε k}
  rw [MvPolynomial.mem_supported, vars_monomial one_ne_zero]
  exact fun k hk => hs k hk

def Ad {V : Submodule ℂ (PX m n)} (K : Module.End ℂ (PX m n)) (KV : Module.End ℂ V) :
    Module.End ℂ (V →ₗ[ℂ] PX m n) where
  toFun h := K ∘ₗ h - h ∘ₗ KV
  map_add' h₁ h₂ := LinearMap.ext fun f => by simp; abel
  map_smul' r h := LinearMap.ext fun f => by simp [smul_sub]

section main

variable (R : Set (Fin m → ℕ)) (hV : ∀ (i j : Fin n), ∀ f ∈ box ε R, KopL ε i j f ∈ box ε R)

def KV (i j : Fin n) : Module.End ℂ (box (n := n) ε R) := (KopL ε i j).restrict (hV i j)

def OmH : Module.End ℂ (box (n := n) ε R →ₗ[ℂ] PX m n) :=
  ∑ ij : Fin n × Fin n, Ad (KopL ε ij.1 ij.2) (KV R hV ij.1 ij.2) * Ad (KopL ε ij.2 ij.1) (KV R hV ij.2 ij.1)

def rr (N : ℕ) : S (n := n) ε N →ₗ[ℂ] (box (n := n) ε R →ₗ[ℂ] PX m n) where
  toFun x := opL x.1 ∘ₗ (box ε R).subtype
  map_add' x y := LinearMap.ext fun f => op_add_sym x.1 y.1 f.1
  map_smul' r x := LinearMap.ext fun f => op_smul_sym x.1 r f.1

variable (hS : SymKComm)
include hS

theorem rr_Om (N : ℕ) (x : S (n := n) ε N) : rr R N (OmS ε N x) = OmH R hV (rr R N x) := by
  refine LinearMap.ext fun f => ?_
  have hf : f.1 ∈ F1 ε := box_le_first_family R f.2
  have hF1 : ∀ (i j : Fin n) (g : box (n := n) ε R), (KopL ε i j g.1) ∈ F1 ε := fun i j g => box_le_first_family R (hV i j g.1 g.2)
  simp only [rr, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply, Submodule.coe_subtype, OmH,
    LinearMap.sum_apply, Module.End.mul_apply, opL]
  change op (Om ε x.1) f.1 = _
  rw [Om_apply, op_sum_sym]
  refine Finset.sum_congr rfl fun ij _ => ?_
  have hx : SymbolInFirstFamily ε x.1 := symbol_first_family_of_mem x.2
  have hx' : SymbolInFirstFamily ε (symK ε ij.2 ij.1 x.1) := symbol_first_family_of_mem (symK_mem _ _ x.2)
  rw [hS m n ε ij.1 ij.2 _ hx' f.1 hf, hS m n ε ij.2 ij.1 _ hx f.1 hf,
    hS m n ε ij.2 ij.1 _ hx _ (hF1 ij.1 ij.2 f)]
  rfl

theorem rr_aeval (N : ℕ) (q : Polynomial ℂ) (x : S (n := n) ε N) :
    rr R N (Polynomial.aeval (OmS ε N) q x) = Polynomial.aeval (OmH R hV) q (rr R N x) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq]
  | monomial k a =>
    simp only [Polynomial.aeval_monomial, Module.End.mul_apply, LinearMap.map_smul_of_tower,
      Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply, map_smul]
    congr 1
    induction k generalizing x with
    | zero => simp
    | succ k ih => rw [pow_succ, Module.End.mul_apply, ih, rr_Om R hV hS, pow_succ, Module.End.mul_apply]

end main

theorem aeval_ker {V : Type*} [AddCommGroup V] [Module ℂ V] (T : Module.End ℂ V) (v : V) (h : T v = 0)
    (q : Polynomial ℂ) : Polynomial.aeval T q v = q.eval 0 • v := by
  conv_lhs => rw [← Polynomial.divX_mul_X_add q]
  rw [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C, LinearMap.add_apply, Module.End.mul_apply, h,
    map_zero, zero_add, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply,
    Polynomial.coeff_zero_eq_eval_zero]

end CoreD

open CoreD in

theorem equivLift_of (hFFT : PositivityTheory.Rg.Sw.FFT) (_hSF : SemiFam) (hD : Dens) (hS : SymKComm) (hI : InvOp)
    (hF : FormFacts) : EquivLift := by
  intro m n ε c hc R t ht htk
  obtain ⟨-, -, -, hF4, hF5⟩ := hF m n ε c hc
  have hadj : ∀ (i j : Fin n) (s u : Sym m n), psi (symK ε i j s) u = psi s (symK ε j i u) := fun i j s u => by
    have := (hF5 i j s u).2
    simpa [psi] using this
  have hV : ∀ (i j : Fin n), ∀ f ∈ box ε (R : Set (Fin m → ℕ)), KopL ε i j f ∈ box ε (R : Set (Fin m → ℕ)) :=
    fun i j f hf => hF4 i j _ f hf
  obtain ⟨s, hs1, hs2⟩ := hD m n ε R t (fun f hf => box_le_first_family _ (ht f hf))
  set N := s.totalDegree
  let x : S (n := n) ε N := ⟨s, mem_S_of hs1⟩
  obtain ⟨q, hq0, hq⟩ := exists_q hadj N
  set y := Polynomial.aeval (OmS ε N) q x with hy
  have ht' : OmH (R : Set (Fin m → ℕ)) hV (t ∘ₗ (box ε (R : Set (Fin m → ℕ))).subtype) = 0 := by
    rw [OmH, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun ij _ => ?_
    have h0 : Ad (KopL ε ij.2 ij.1) (KV (R : Set (Fin m → ℕ)) hV ij.2 ij.1) (t ∘ₗ (box ε (R : Set (Fin m → ℕ))).subtype) = 0 := by
      refine LinearMap.ext fun f => ?_
      simp [Ad, KV, LinearMap.restrict_apply, htk ij.2 ij.1 f.1 f.2]
    rw [Module.End.mul_apply, h0, map_zero]
  have hrx : rr (R : Set (Fin m → ℕ)) N x = t ∘ₗ (box ε (R : Set (Fin m → ℕ))).subtype := by
    refine LinearMap.ext fun f => ?_
    exact hs2 f.1 f.2
  have hry : rr (R : Set (Fin m → ℕ)) N y = t ∘ₗ (box ε (R : Set (Fin m → ℕ))).subtype := by
    rw [hy, rr_aeval _ hV hS, hrx, aeval_ker _ _ ht', hq0, one_smul]
  have hy0 : Om ε y.1 = 0 := congrArg Subtype.val (hq x)
  have hsym : ∀ i j, symK ε i j y.1 = 0 := symK_eq_zero_of_Om hadj _ hy0
  obtain ⟨w, hw, hwf⟩ := hI hFFT m n ε c hc y.1 (symbol_first_family_of_mem y.2) hsym
  refine ⟨w, hw, fun f hf => ?_⟩
  have h1 : op y.1 f = t f := LinearMap.congr_fun hry ⟨f, hf⟩
  rw [← h1, hwf f (box_le_first_family _ hf)]

end PositivityTheory.Rg.Sw.LC
