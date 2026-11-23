import Mathlib

open TensorProduct

namespace GlobalTheory.EtaleSub

section Fixed

variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (φ : R →+* R) (Φ : M →+ M)

def fixIn (U : Submodule R M) : Set M := {x | x ∈ U ∧ Φ x = x}

theorem exists_sub_of_mem_span (hΦ : ∀ r x, Φ (r • x) = φ r • Φ x) (hs : ∀ y, ∃ b, φ b - b = y)
    (U : Submodule R M) (y : M) (hy : y ∈ Submodule.span R (fixIn Φ U)) :
    ∃ z ∈ U, Φ z - z = y := by
  obtain ⟨n, c, g, rfl⟩ := Submodule.mem_span_set'.1 hy
  choose b hb using fun i => hs (c i)
  refine ⟨∑ i, b i • (g i : M), U.sum_mem fun i _ => U.smul_mem _ (g i).2.1, ?_⟩
  rw [map_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hΦ, (g i).2.2, ← sub_smul, hb]

theorem le_span_step (hΦ : ∀ r x, Φ (r • x) = φ r • Φ x) (hs : ∀ y, ∃ b, φ b - b = y)
    (hI : ∀ I : Ideal R, (∀ x ∈ I, φ x ∈ I) → I ≤ Ideal.span {x | x ∈ I ∧ φ x = x})
    (U : Submodule R M) (hU : ∀ x ∈ U, Φ x ∈ U) (f : M →ₗ[R] R) (hf : ∀ x, f (Φ x) = φ (f x))
    (h0 : U ⊓ LinearMap.ker f ≤ Submodule.span R (fixIn Φ (U ⊓ LinearMap.ker f))) :
    U ≤ Submodule.span R (fixIn Φ U) := by
  have h1 : U ⊓ LinearMap.ker f ≤ Submodule.span R (fixIn Φ U) :=
    h0.trans (Submodule.span_mono fun x hx => ⟨hx.1.1, hx.2⟩)
  have h2 : U.map f ≤ (Submodule.span R (fixIn Φ U)).map f := by
    refine (hI (U.map f) ?_).trans ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨Φ x, hU x hx, hf x⟩
    · rw [Ideal.span_le]
      rintro _ ⟨⟨u, hu, rfl⟩, hfix⟩
      have hmem : Φ u - u ∈ U ⊓ LinearMap.ker f :=
        ⟨U.sub_mem (hU u hu) hu, by
          change f (Φ u - u) = 0
          rw [map_sub, hf, hfix, sub_self]⟩
      obtain ⟨z, hz, hz'⟩ := exists_sub_of_mem_span φ Φ hΦ hs _ _ (h0 hmem)
      refine ⟨u - z, Submodule.subset_span ⟨U.sub_mem hu hz.1, ?_⟩, ?_⟩
      · rw [map_sub]
        exact sub_eq_sub_iff_sub_eq_sub.2 hz'.symm
      · have : f z = 0 := hz.2
        rw [map_sub, this, sub_zero]
  intro x hx
  obtain ⟨s, hs', hsx⟩ := h2 ⟨x, hx, rfl⟩
  have hsU : s ∈ U := (Submodule.span_le.2 fun y hy => hy.1 : Submodule.span R (fixIn Φ U) ≤ U) hs'
  have : x - s ∈ U ⊓ LinearMap.ker f := ⟨U.sub_mem hx hsU, by
    change f (x - s) = 0
    rw [map_sub, hsx, sub_self]⟩
  simpa using Submodule.add_mem _ (h1 this) hs'

theorem le_span_fixIn (hΦ : ∀ r x, Φ (r • x) = φ r • Φ x) (hs : ∀ y, ∃ b, φ b - b = y)
    (hI : ∀ I : Ideal R, (∀ x ∈ I, φ x ∈ I) → I ≤ Ideal.span {x | x ∈ I ∧ φ x = x})
    {ι : Type} [Finite ι] (f : ι → M →ₗ[R] R) (hf : ∀ i x, f i (Φ x) = φ (f i x))
    (hinj : ∀ x, (∀ i, f i x = 0) → x = 0)
    (U : Submodule R M) (hU : ∀ x ∈ U, Φ x ∈ U) : U ≤ Submodule.span R (fixIn Φ U) := by
  classical
  haveI := Fintype.ofFinite ι
  have key : ∀ s : Finset ι, ∀ U : Submodule R M, (∀ x ∈ U, Φ x ∈ U) →
      (∀ x ∈ U, ∀ i ∉ s, f i x = 0) → U ≤ Submodule.span R (fixIn Φ U) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro U _ h x hx
      rw [hinj x fun i => h x hx i (by simp)]
      exact Submodule.zero_mem _
    | insert a s _ ih =>
      intro U hU h
      refine le_span_step φ Φ hΦ hs hI U hU (f a) (hf a) (ih _ ?_ ?_)
      · intro x hx
        refine ⟨hU x hx.1, ?_⟩
        have : f a x = 0 := hx.2
        change f a (Φ x) = 0
        rw [hf, this, map_zero]
      · intro x hx i hi
        by_cases hia : i = a
        · subst hia; exact hx.2
        · exact h x hx.1 i (by simp [hia, hi])
  exact key Finset.univ U hU fun _ _ i hi => absurd (Finset.mem_univ i) hi

end Fixed

theorem tensor_le_span {A R T : Type} [CommRing A] [CommRing R] [Algebra A R] [AddCommGroup T]
    [Module A T] [Module.Free A T] [Module.Finite A T] (φ : R →ₐ[A] R)
    (hs : ∀ y, ∃ b, φ b - b = y)
    (hI : ∀ I : Ideal R, (∀ x ∈ I, φ x ∈ I) → I ≤ Ideal.span {x | x ∈ I ∧ φ x = x})
    (U : Submodule R (R ⊗[A] T))
    (hU : ∀ x ∈ U, TensorProduct.map φ.toLinearMap LinearMap.id x ∈ U) :
    U ≤ Submodule.span R {x | x ∈ U ∧ TensorProduct.map φ.toLinearMap LinearMap.id x = x} := by
  let b := Module.Free.chooseBasis A T
  refine le_span_fixIn φ.toRingHom
    (TensorProduct.map φ.toLinearMap (LinearMap.id : T →ₗ[A] T)).toAddMonoidHom ?_ hs hI
    (fun i => (b.baseChange R).coord i) ?_ ?_ U hU
  · intro r x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a t => simp [TensorProduct.smul_tmul']
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  · intro i x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a t => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  · intro x hx
    exact (b.baseChange R).ext_elem fun i => by simpa using hx i

theorem ideal_le_span {A W O : Type} [CommRing A] [CommRing W] [Algebra A W] [CommRing O]
    [Algebra A O] [Module.Free A O] [Module.Finite A O] (φ : W →ₐ[A] W)
    (hs : ∀ y, ∃ b, φ b - b = y)
    (hI : ∀ I : Ideal W, (∀ x ∈ I, φ x ∈ I) → I ≤ Ideal.span {x | x ∈ I ∧ φ x = x})
    (I : Ideal (O ⊗[A] W)) (hU : ∀ x ∈ I, Algebra.TensorProduct.map (AlgHom.id O O) φ x ∈ I) :
    I ≤ Ideal.span {x | x ∈ I ∧ Algebra.TensorProduct.map (AlgHom.id O O) φ x = x} := by
  let e := Algebra.TensorProduct.comm A W O
  have hc : ∀ b : W ⊗[A] O, e (TensorProduct.map φ.toLinearMap LinearMap.id b) =
      Algebra.TensorProduct.map (AlgHom.id O O) φ (e b) := by
    intro b
    induction b using TensorProduct.induction_on with
    | zero => simp
    | tmul a w => simp [e]
    | add x y hx hy => simp only [map_add, hx, hy]
  let U : Submodule W (W ⊗[A] O) := (I.comap e.toRingEquiv.toRingHom).restrictScalars W
  have hUm : ∀ x, x ∈ U ↔ e x ∈ I := fun x => Iff.rfl
  have h := tensor_le_span φ hs hI U fun x hx => by
    rw [hUm, hc]; exact hU _ hx
  intro x hx
  obtain ⟨y, rfl⟩ := e.surjective x
  have hy := h ((hUm y).2 hx)
  clear hx
  induction hy using Submodule.span_induction with
  | mem z hz => exact Ideal.subset_span ⟨hz.1, by rw [← hc, hz.2]⟩
  | zero => simp
  | add z w _ _ hz hw => rw [map_add]; exact Ideal.add_mem _ hz hw
  | smul a z _ hz => rw [Algebra.smul_def, map_mul]; exact Ideal.mul_mem_left _ _ hz

theorem flat_of_letters {E M ι : Type} [CommRing E] [AddCommGroup M] [Module E M] [Fintype ι]
    (e : ι → E) (he : ∑ i, e i = 1) (hid : ∀ i, e i * e i = e i) (ϖ : E)
    (hS : ∀ i x, e i * x = 0 ∨ ∃ (k : ℕ) (u : E), IsUnit u ∧ e i * x = e i * ϖ ^ k * u)
    (hM : ∀ m : M, ϖ • m = 0 → m = 0) : Module.Flat E M := by
  classical
  have hMk : ∀ (k : ℕ) (m : M), ϖ ^ k • m = 0 → m = 0 := by
    intro k
    induction k with
    | zero => intro m h; simpa using h
    | succ k ih => intro m h; rw [pow_succ, mul_smul] at h; exact hM _ (ih _ h)
  rw [Module.Flat.iff_lift_lsmul_comp_subtype_injective]
  intro I _
  rw [injective_iff_map_eq_zero]
  intro t ht
  have key : ∀ i, e i • t = 0 := by
    intro i
    by_cases h : ∃ k : ℕ, e i * ϖ ^ k ∈ I
    · let d : I := ⟨e i * ϖ ^ Nat.find h, Nat.find_spec h⟩
      have h1 : ∀ s : I ⊗[E] M, ∃ m : M, e i • s = d ⊗ₜ m := by
        intro s
        induction s using TensorProduct.induction_on with
        | zero => exact ⟨0, by simp⟩
        | tmul a m =>
          rw [TensorProduct.smul_tmul']
          rcases hS i a with h0 | ⟨k, u, hu, hk⟩
          · have : e i • a = 0 := Subtype.ext h0
            exact ⟨0, by rw [this]; simp⟩
          · have hk' : e i * ϖ ^ k ∈ I := by
              rw [← Ideal.mul_unit_mem_iff_mem I hu, ← hk]
              exact I.mul_mem_left _ a.2
            obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.find_min' h hk')
            have : e i • a = (ϖ ^ j * u) • d := Subtype.ext (by
              change e i * a = ϖ ^ j * u * (e i * ϖ ^ Nat.find h)
              rw [hk]; ring)
            exact ⟨(ϖ ^ j * u) • m, by rw [this, TensorProduct.smul_tmul]⟩
        | add x y hx hy =>
          obtain ⟨m, hm⟩ := hx
          obtain ⟨m', hm'⟩ := hy
          exact ⟨m + m', by rw [smul_add, hm, hm', TensorProduct.tmul_add]⟩
      obtain ⟨m, hm⟩ := h1 t
      have h2 : (d : E) • m = 0 := by
        have := congrArg (TensorProduct.lift ((LinearMap.lsmul E M).comp I.subtype)) hm
        rw [map_smul, ht, smul_zero] at this
        simpa using this.symm
      have h3 : e i • m = 0 := hMk (Nat.find h) _ (by rw [← mul_smul, mul_comm]; exact h2)
      have h4 : d = e i • d := Subtype.ext (by
        change e i * ϖ ^ Nat.find h = e i * (e i * ϖ ^ Nat.find h)
        rw [← mul_assoc, hid])
      rw [hm, h4, TensorProduct.smul_tmul, h3, TensorProduct.tmul_zero]
    · clear ht
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul a m =>
        rw [TensorProduct.smul_tmul']
        rcases hS i a with h0 | ⟨k, u, hu, hk⟩
        · have : e i • a = 0 := Subtype.ext h0
          rw [this]; simp
        · refine absurd ⟨k, ?_⟩ h
          rw [← Ideal.mul_unit_mem_iff_mem I hu, ← hk]
          exact I.mul_mem_left _ a.2
      | add x y hx hy => rw [smul_add, hx, hy, add_zero]
  rw [← one_smul E t, ← he, Finset.sum_smul]
  exact Finset.sum_eq_zero fun i _ => key i

theorem mem_of_mem_span_image {E R D M : Type} [CommRing E] [CommRing R] [Algebra E R]
    [Module.FaithfullyFlat E R] [AddCommGroup D]
    [Module E D] [AddCommGroup M] [Module R M] [Module.Free E D] [Module.Finite E D]
    (j : D →+ M) (hj : ∀ e x, j (e • x) = algebraMap E R e • j x)
    (hrank : Nontrivial R → Module.finrank E D = Module.finrank R M)
    (hspan : Submodule.span R (Set.range j) = ⊤)
    (N : Submodule E D) (x : D) (hx : j x ∈ Submodule.span R (j '' (N : Set D))) : x ∈ N := by
  classical
  rcases subsingleton_or_nontrivial E with hE | hE
  · haveI := Module.subsingleton E D
    rw [Subsingleton.elim x 0]; exact N.zero_mem
  haveI : Nontrivial R := (FaithfulSMul.algebraMap_injective E R).nontrivial
  let b := Module.Free.chooseBasis E D
  have hsp : ⊤ ≤ Submodule.span R (Set.range fun i => j (b i)) := by
    rw [← hspan, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    rw [← b.sum_repr x, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [hj]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let c := basisOfTopLeSpanOfCardEqFinrank (fun i => j (b i)) hsp
    (by rw [← hrank inferInstance, Module.finrank_eq_card_chooseBasisIndex])
  have hc : ∀ i, c i = j (b i) := fun i => by simp [c]
  let F : M →ₗ[R] R ⊗[E] (D ⧸ N) := c.constr R fun i => (1 : R) ⊗ₜ N.mkQ (b i)
  have hF : ∀ x, F (j x) = (1 : R) ⊗ₜ N.mkQ x := by
    intro x
    rw [← b.sum_repr x]
    simp only [map_sum, hj, map_smul, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hc, Module.Basis.constr_basis, algebraMap_smul, TensorProduct.tmul_smul]
  have hker : Submodule.span R (j '' (N : Set D)) ≤ LinearMap.ker F := by
    rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    change F (j y) = 0
    rw [hF, show N.mkQ y = 0 from (Submodule.Quotient.mk_eq_zero _).2 hy, TensorProduct.tmul_zero]
  have h1 : (1 : R) ⊗ₜ[E] N.mkQ x = 0 := (hF x).symm.trans (hker hx)
  exact (Submodule.Quotient.mk_eq_zero _).1
    ((Module.FaithfullyFlat.one_tmul_eq_zero_iff E (D ⧸ N) _).1 h1)

end GlobalTheory.EtaleSub
