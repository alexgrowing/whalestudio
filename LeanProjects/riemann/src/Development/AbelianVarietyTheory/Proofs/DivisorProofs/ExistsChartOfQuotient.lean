import Mathlib
open scoped TensorProduct

namespace GlobalTheory.HilbChart

variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {N r : ℕ}
  (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N)

noncomputable def sc (a m b : Fin N) : A := e.repr (e a * e m) b

variable {S : Type} [CommRing S] [Algebra A S]

noncomputable def coord (c : Fin N → Fin r → S) : S ⊗[A] B →ₗ[S] (Fin r → S) :=
  (Algebra.TensorProduct.basis S e).constr S c

noncomputable def ell (c : Fin N → Fin r → S) (m : Fin N) : S ⊗[A] B :=
  (1 : S) ⊗ₜ[A] e m - ∑ k, c m k • ((1 : S) ⊗ₜ[A] e (σ k))

noncomputable def chartIdeal (c : Fin N → Fin r → S) : Ideal (S ⊗[A] B) :=
  Ideal.span (Set.range (ell e σ c))

noncomputable def mulDefect (c : Fin N → Fin r → S) (a m : Fin N) (k : Fin r) : S :=
  ∑ b, algebraMap A S (sc e a m b) * c b k -
    ∑ k', c m k' * ∑ b, algebraMap A S (sc e a (σ k') b) * c b k

def IsChart (c : Fin N → Fin r → S) : Prop :=
  (∀ k k', c (σ k) k' = Pi.single (M := fun _ => S) k 1 k') ∧ ∀ a m k, mulDefect e σ c a m k = 0

end GlobalTheory.HilbChart

namespace GlobalTheory.HilbChart
variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {N r : ℕ}
  (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) {S : Type} [CommRing S] [Algebra A S]

theorem coord_one_tmul_basis (c : Fin N → Fin r → S) (m : Fin N) :
    coord e c ((1:S) ⊗ₜ e m) = c m := by
  rw [← Algebra.TensorProduct.basis_apply]; exact Module.Basis.constr_basis _ _ _ _

theorem sum_smul_single (v : Fin r → S) : ∑ k, v k • (Pi.single k (1:S) : Fin r → S) = v := by
  funext j; simp [Finset.sum_apply, Pi.single_apply]

theorem coord_apply (c : Fin N → Fin r → S) (y : S ⊗[A] B) :
    coord e c y = ∑ m, (Algebra.TensorProduct.basis S e).repr y m • c m := by
  rw [coord, Module.Basis.constr_apply, Finsupp.sum_fintype]; simp

theorem coord_one_tmul (c : Fin N → Fin r → S) (x : B) :
    coord e c ((1:S) ⊗ₜ x) = ∑ b, e.repr x b • c b := by
  conv_lhs => rw [← e.sum_repr x]
  simp only [TensorProduct.tmul_sum, map_sum, TensorProduct.tmul_smul]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [LinearMap.map_smul_of_tower, coord_one_tmul_basis]

theorem decomp (c : Fin N → Fin r → S) (y : S ⊗[A] B) :
    y = ∑ m, (Algebra.TensorProduct.basis S e).repr y m • ell e σ c m +
      ∑ k, coord e c y k • ((1:S) ⊗ₜ[A] e (σ k)) := by
  set bS := Algebra.TensorProduct.basis S e
  rw [coord_apply]
  simp only [ell, smul_sub, Finset.sum_sub_distrib, Finset.smul_sum, smul_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, Finset.sum_smul]
  rw [Finset.sum_comm (γ := Fin r)]
  have : ∑ m, bS.repr y m • ((1:S) ⊗ₜ[A] e m) = y := by
    conv_rhs => rw [← bS.sum_repr y]
    simp [bS]
  rw [this]; abel

theorem coord_sigma {c : Fin N → Fin r → S} (hc : ∀ k k', c (σ k) k' = Pi.single (M := fun _ => S) k 1 k')
    (k : Fin r) : c (σ k) = Pi.single k 1 := funext (hc k)

theorem coord_ell {c : Fin N → Fin r → S} (hc : ∀ k k', c (σ k) k' = Pi.single (M := fun _ => S) k 1 k')
    (m : Fin N) : coord e c (ell e σ c m) = 0 := by
  simp only [ell, map_sub, map_sum, map_smul, coord_one_tmul_basis, coord_sigma σ hc, sum_smul_single, sub_self]

theorem coord_mul_ell (c : Fin N → Fin r → S) (a m : Fin N) (k : Fin r) :
    coord e c (((1:S) ⊗ₜ[A] e a) * ell e σ c m) k = mulDefect e σ c a m k := by
  simp only [ell, mul_sub, Finset.mul_sum, mul_smul_comm, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
    map_sub, map_sum, map_smul, coord_one_tmul]
  simp only [mulDefect, sc, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp only [Algebra.smul_def, Finset.mul_sum]

theorem coord_mul_eq_zero {c : Fin N → Fin r → S} (hc : IsChart e σ c) (z y : S ⊗[A] B)
    (hy : coord e c y = 0) : coord e c (z * y) = 0 := by
  set bS := Algebra.TensorProduct.basis S e
  have hy' : y = ∑ m, bS.repr y m • ell e σ c m := by
    have := decomp e σ c y; rw [hy] at this; simpa using this
  rw [← bS.sum_repr z, hy']
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm, map_sum, map_smul]
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun m _ => ?_
  have : coord e c (bS m * ell e σ c a) = 0 := by
    funext k; rw [Algebra.TensorProduct.basis_apply, coord_mul_ell]; exact hc.2 m a k
  rw [this, smul_zero]

theorem mem_chartIdeal_iff {c : Fin N → Fin r → S} (hc : IsChart e σ c) (y : S ⊗[A] B) :
    y ∈ chartIdeal e σ c ↔ coord e c y = 0 := by
  constructor
  · intro hy
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨m, rfl⟩; exact coord_ell e σ hc.1 m
    · simp
    · intro u v _ _ hu hv; rw [map_add, hu, hv, add_zero]
    · intro z u _ hu; exact coord_mul_eq_zero e σ hc z u hu
  · intro hy
    rw [decomp e σ c y, hy]
    simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero]
    refine Ideal.sum_mem _ fun m _ => ?_
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨m, rfl⟩)

theorem mk_smul (J : Ideal (S ⊗[A] B)) (s : S) (y : S ⊗[A] B) :
    Ideal.Quotient.mk J (s • y) = s • Ideal.Quotient.mk J y := rfl

theorem sum_smul_tmul_sigma (c : Fin N → Fin r → S) (v : Fin r → S) (hc : ∀ k, c (σ k) = Pi.single k 1) :
    coord e c (∑ k, v k • ((1:S) ⊗ₜ[A] e (σ k))) = v := by
  simp only [map_sum, map_smul, coord_one_tmul_basis, hc, sum_smul_single]

theorem quotient_basis {c : Fin N → Fin r → S} (hc : IsChart e σ c) :
    LinearIndependent S (fun k => Ideal.Quotient.mk (chartIdeal e σ c) ((1 : S) ⊗ₜ[A] e (σ k))) ∧
    Submodule.span S (Set.range (fun k => Ideal.Quotient.mk (chartIdeal e σ c) ((1 : S) ⊗ₜ[A] e (σ k)))) = ⊤ := by
  constructor
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    simp only [← mk_smul, ← map_sum, Ideal.Quotient.eq_zero_iff_mem, mem_chartIdeal_iff e σ hc] at hg
    rw [sum_smul_tmul_sigma e σ c g (coord_sigma σ hc.1)] at hg
    intro k; rw [hg]; rfl
  · rw [Submodule.eq_top_iff']
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [decomp e σ c y, map_add, map_sum, map_sum]
    have h0 : ∀ m, Ideal.Quotient.mk (chartIdeal e σ c)
        ((Algebra.TensorProduct.basis S e).repr y m • ell e σ c m) = 0 := fun m => by
      rw [Ideal.Quotient.eq_zero_iff_mem, Algebra.smul_def]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨m, rfl⟩)
    simp only [h0, Finset.sum_const_zero, zero_add]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [mk_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

variable {S' : Type} [CommRing S'] [Algebra A S']

theorem map_ell (φ : S →ₐ[A] S') (c : Fin N → Fin r → S) (m : Fin N) :
    Algebra.TensorProduct.map φ (AlgHom.id A B) (ell e σ c m) = ell e σ (fun m k => φ (c m k)) m := by
  simp [ell, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem map_chartIdeal (φ : S →ₐ[A] S') (c : Fin N → Fin r → S) :
    (chartIdeal e σ c).map (Algebra.TensorProduct.map φ (AlgHom.id A B)) =
      chartIdeal e σ (fun m k => φ (c m k)) := by
  rw [chartIdeal, chartIdeal, Ideal.map_span, ← Set.range_comp]
  have : (⇑(Algebra.TensorProduct.map φ (AlgHom.id A B)) ∘ ell e σ c) =
      ell e σ (fun m k => φ (c m k)) := funext (map_ell e σ φ c)
  rw [this]

theorem IsChart.map {c : Fin N → Fin r → S} (hc : IsChart e σ c) (φ : S →ₐ[A] S') :
    IsChart e σ (fun m k => φ (c m k)) := by
  refine ⟨fun k k' => ?_, fun a m k => ?_⟩
  · show φ (c (σ k) k') = _
    rw [hc.1]; by_cases h : k' = k <;> simp [Pi.single_apply, h]
  · have : mulDefect e σ (fun m k => φ (c m k)) a m k = φ (mulDefect e σ c a m k) := by
      simp [mulDefect, map_sub, map_sum, map_mul, AlgHom.commutes]
    rw [this, hc.2, map_zero]

theorem eq_of_chartIdeal_le {c d : Fin N → Fin r → S} (hc : IsChart e σ c)
    (h : chartIdeal e σ d ≤ chartIdeal e σ c) : c = d := by
  funext m
  have h1 := (mem_chartIdeal_iff e σ hc _).1 (h (Ideal.subset_span ⟨m, rfl⟩))
  simp only [ell, map_sub, map_sum, map_smul, coord_one_tmul_basis, coord_sigma σ hc.1,
    sum_smul_single] at h1
  exact sub_eq_zero.1 h1

theorem exists_chart_of_quotient (J : Ideal (S ⊗[A] B))
    (hli : LinearIndependent S (fun k => Ideal.Quotient.mk J ((1 : S) ⊗ₜ[A] e (σ k))))
    (hsp : Submodule.span S (Set.range (fun k => Ideal.Quotient.mk J ((1 : S) ⊗ₜ[A] e (σ k)))) = ⊤) :
    ∃ c : Fin N → Fin r → S, IsChart e σ c ∧ chartIdeal e σ c = J := by
  let bq := Module.Basis.mk hli hsp.ge
  let c : Fin N → Fin r → S := fun m k => bq.repr (Ideal.Quotient.mk J ((1:S) ⊗ₜ[A] e m)) k
  have hbq : ∀ k, bq k = Ideal.Quotient.mk J ((1 : S) ⊗ₜ[A] e (σ k)) := fun k => Module.Basis.mk_apply _ _ _
  have ha : ∀ k k', c (σ k) k' = Pi.single (M := fun _ => S) k 1 k' := by
    intro k k'
    simp only [c, ← hbq, Module.Basis.repr_self, Finsupp.single_apply, Pi.single_apply]
    by_cases h : k = k'
    · subst h; simp
    · simp [h, Ne.symm h]
  have hell : ∀ m, Ideal.Quotient.mk J (ell e σ c m) = 0 := by
    intro m
    simp only [ell, map_sub, map_sum, mk_smul, ← hbq]
    rw [sub_eq_zero]
    exact (bq.sum_repr _).symm
  have hq : ∀ y, Ideal.Quotient.mk J y = ∑ k, coord e c y k • bq k := by
    intro y
    conv_lhs => rw [decomp e σ c y]
    simp only [map_add, map_sum, mk_smul, hell, smul_zero, Finset.sum_const_zero, zero_add, hbq]
  have hmem : ∀ y, y ∈ J ↔ coord e c y = 0 := by
    intro y
    rw [← Ideal.Quotient.eq_zero_iff_mem, hq y]
    constructor
    · intro h
      exact funext ((Fintype.linearIndependent_iff.1 bq.linearIndependent) _ h)
    · intro h; simp [h]
  have hc : IsChart e σ c := by
    refine ⟨ha, fun a m k => ?_⟩
    rw [← coord_mul_ell]
    have : ell e σ c m ∈ J := (hmem _).2 (coord_ell e σ ha m)
    rw [(hmem _).1 (J.mul_mem_left _ this)]; rfl
  refine ⟨c, hc, ?_⟩
  ext y
  rw [mem_chartIdeal_iff e σ hc, hmem]

theorem mulDefect_map (φ : S →ₐ[A] S') (c : Fin N → Fin r → S) (a m : Fin N) (k : Fin r) :
    mulDefect e σ (fun m k => φ (c m k)) a m k = φ (mulDefect e σ c a m k) := by
  simp [mulDefect, map_sub, map_sum, map_mul, AlgHom.commutes]

noncomputable def rels : (Fin r × Fin r) ⊕ (Fin N × Fin N × Fin r) → MvPolynomial (Fin N × Fin r) A
  | .inl p => MvPolynomial.X (σ p.1, p.2) - MvPolynomial.C (Pi.single (M := fun _ => A) p.1 1 p.2)
  | .inr p => mulDefect e σ (fun m k => (MvPolynomial.X (m, k) : MvPolynomial (Fin N × Fin r) A)) p.1 p.2.1 p.2.2

theorem isChart_iff_aeval (c : Fin N → Fin r → S) :
    IsChart e σ c ↔ ∀ i, MvPolynomial.aeval (fun p : Fin N × Fin r => c p.1 p.2) (rels e σ i) = 0 := by
  have hd : ∀ a m k, MvPolynomial.aeval (fun p : Fin N × Fin r => c p.1 p.2)
      (mulDefect e σ (fun m k => (MvPolynomial.X (m, k) : MvPolynomial (Fin N × Fin r) A)) a m k) =
      mulDefect e σ c a m k := by
    intro a m k
    rw [← mulDefect_map]; simp
  have hs : ∀ k k' : Fin r, algebraMap A S (Pi.single (M := fun _ => A) k 1 k') =
      Pi.single (M := fun _ => S) k 1 k' := by
    intro k k'; by_cases h : k' = k <;> simp [Pi.single_apply, h]
  constructor
  · rintro ⟨ha, hb⟩ (⟨k, k'⟩ | ⟨a, m, k⟩)
    · simp [rels, ha, hs]
    · simp only [rels]; rw [hd, hb]
  · intro h
    refine ⟨fun k k' => ?_, fun a m k => ?_⟩
    · have := h (.inl (k, k'))
      simp only [rels, map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_C, hs] at this
      exact sub_eq_zero.1 this
    · have := h (.inr (a, m, k))
      simp only [rels] at this; rwa [hd] at this

noncomputable def relIdeal : Ideal (MvPolynomial (Fin N × Fin r) A) := Ideal.span (Set.range (rels e σ))

abbrev ChartRing := MvPolynomial (Fin N × Fin r) A ⧸ relIdeal e σ

noncomputable def univChart : Fin N → Fin r → ChartRing e σ :=
  fun m k => Ideal.Quotient.mk (relIdeal e σ) (MvPolynomial.X (m, k))

theorem isChart_univChart : IsChart e σ (univChart e σ) := by
  rw [isChart_iff_aeval]
  intro i
  have : MvPolynomial.aeval (fun p : Fin N × Fin r => univChart e σ p.1 p.2) =
      Ideal.Quotient.mkₐ A (relIdeal e σ) := by
    apply MvPolynomial.algHom_ext; intro p; simp [univChart]
  rw [this, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span ⟨i, rfl⟩

end GlobalTheory.HilbChart

open GlobalTheory.HilbChart in
theorem GlobalTheory.hilbChart_representable : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (N r : ℕ) (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N), ∃ (C : Type) (_ : CommRing C) (_ : Algebra A C) (J : Ideal (C ⊗[A] B)), Algebra.FinitePresentation A C ∧ LinearIndependent C (fun k => Ideal.Quotient.mk J ((1 : C) ⊗ₜ[A] e (σ k))) ∧ Submodule.span C (Set.range (fun k => Ideal.Quotient.mk J ((1 : C) ⊗ₜ[A] e (σ k)))) = ⊤ ∧ ∀ (A' : Type) [CommRing A'] [Algebra A A'] (J' : Ideal (A' ⊗[A] B)), LinearIndependent A' (fun k => Ideal.Quotient.mk J' ((1 : A') ⊗ₜ[A] e (σ k))) → Submodule.span A' (Set.range (fun k => Ideal.Quotient.mk J' ((1 : A') ⊗ₜ[A] e (σ k)))) = ⊤ → ∃! φ : C →ₐ[A] A', J' = J.map (Algebra.TensorProduct.map φ (AlgHom.id A B)) := by
  intro A B _ _ _ N r e σ
  have hC := isChart_univChart e σ
  refine ⟨ChartRing e σ, inferInstance, inferInstance, chartIdeal e σ (univChart e σ), ?_,
    (quotient_basis e σ hC).1, (quotient_basis e σ hC).2, ?_⟩
  · exact Algebra.FinitePresentation.quotient (Submodule.fg_span (Set.finite_range _))
  · intro A' _ _ J' hli hsp
    obtain ⟨c, hc, hJ⟩ := exists_chart_of_quotient e σ J' hli hsp
    let ψ : MvPolynomial (Fin N × Fin r) A →ₐ[A] A' := MvPolynomial.aeval (fun p => c p.1 p.2)
    have hψ : ∀ a ∈ relIdeal e σ, ψ a = 0 := by
      intro a ha
      have hle : relIdeal e σ ≤ RingHom.ker ψ := by
        rw [relIdeal, Ideal.span_le]
        rintro _ ⟨i, rfl⟩
        exact (isChart_iff_aeval e σ c).1 hc i
      exact hle ha
    let φ : ChartRing e σ →ₐ[A] A' := Ideal.Quotient.liftₐ _ ψ hψ
    have hφ : (fun m k => φ (univChart e σ m k)) = c := by
      funext m k
      change ψ (MvPolynomial.X (m, k)) = c m k
      simp [ψ]
    refine ⟨φ, ?_, ?_⟩
    · show J' = _
      rw [map_chartIdeal, hφ, hJ]
    · intro φ' hφ'
      rw [map_chartIdeal, ← hJ] at hφ'
      have h1 : c = fun m k => φ' (univChart e σ m k) := eq_of_chartIdeal_le e σ hc hφ'.ge
      apply Ideal.Quotient.algHom_ext
      apply MvPolynomial.algHom_ext
      intro p
      have h2 := congrFun (congrFun (h1.symm.trans hφ.symm) p.1) p.2
      simpa [univChart] using h2
