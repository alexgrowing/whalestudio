import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LieLatticeData
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.PolarisedFlagStatement
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MemFlagSubIff

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Num.PtDx

open GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.GR ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up

variable {o C : Type} [CommRing o] [Field C] [Algebra o C] (RC : Subalgebra o C)
  {F : Type} [Field F] {n : ℕ}

theorem mem_flagSub_iff (i : ℕ) (x : Fin n → F) :
    x ∈ flagSub (Pi.basisFun F (Fin n)) i ↔ ∀ j : Fin n, i ≤ (j : ℕ) → x j = 0 :=
  _root_.UpperTheory.Reformulated.B.Qi34.mem_flagSub_iff i x

theorem mem_stdLat {ι : Type} (f : ι → C) : f ∈ stdLat RC ι ↔ ∀ x, f x ∈ RC := by
  simp [stdLat, AddSubgroup.mem_pi]

theorem mem_pInt (p : ℕ) (y : C) :
    y ∈ pInt (C := C) RC p ↔ ∃ r : RC, y = (r : C) * (p : C) := by
  unfold pInt
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨r, rfl⟩
  · rintro ⟨r, rfl⟩
    exact ⟨r, rfl⟩

theorem mem_vanSub (i : ℕ) (f : (Fin n → F) → C) :
    f ∈ vanSub C F n i ↔ ∀ x : Fin n → F, (∀ j : Fin n, i ≤ (j : ℕ) → x j = 0) → f x = 0 := by
  simp [vanSub, Submodule.mem_pi]

theorem mem_annSub (i : ℕ) (l : Fin n → C) :
    l ∈ annSub C n i ↔ ∀ j : Fin n, (j : ℕ) < i → l j = 0 := by
  simp [annSub, Submodule.mem_pi]

theorem linMap_apply (χ : F → C) (l : Fin n → C) (x : Fin n → F) :
    linMap n χ l x = ∑ j, l j * χ (x j) := by
  simp [linMap, Fintype.linearCombination_apply]

variable {Sg : Type} {r s : Sg → ℕ}

theorem mem_first_lattice_iff (D : LieLatticeData C F n Sg r s) (p : ℕ) (f : (Fin n → F) → C) :
    f ∈ D.l1 RC p ↔ ∃ m ∈ D.M, ∀ x, f x - m x ∈ pInt (C := C) RC p := by
  unfold LieLatticeData.l1
  rw [AddSubgroup.mem_sup]
  constructor
  · rintro ⟨m, hm, z, hz, rfl⟩
    obtain ⟨h, hh, rfl⟩ := hz
    refine ⟨m, hm, fun x => ?_⟩
    rw [mem_pInt]
    refine ⟨⟨h x, (mem_stdLat RC h).1 hh x⟩, ?_⟩
    simp [mul_comm]
  · rintro ⟨m, hm, h⟩
    choose t ht using fun x => (mem_pInt RC p _).1 (h x)
    refine ⟨m, hm, _, ⟨fun x => (t x : C), (mem_stdLat RC _).2 fun x => (t x).2, rfl⟩, ?_⟩
    funext x
    have := ht x
    simp only [Pi.add_apply, DistribMulAction.toAddMonoidHom_apply, Pi.smul_apply, smul_eq_mul]
    rw [mul_comm, ← this]; ring

theorem mem_xId (D : LieLatticeData C F n Sg r s) (χ : F → C) (i : Fin n) (c : C) :
    c ∈ D.xId χ i ↔ ∃ g ∈ D.M, ∀ x : Fin n → F, (∀ j : Fin n, (i : ℕ) + 1 ≤ (j : ℕ) → x j = 0) →
      g x = c * χ (x i) := by
  unfold LieLatticeData.xId
  rw [AddSubgroup.mem_comap]
  simp only [LinearMap.toAddMonoidHom_coe, LinearMap.toSpanSingleton_apply]
  rw [AddSubgroup.mem_sup]
  constructor
  · rintro ⟨g, hg, z, hz, e⟩
    refine ⟨g, hg, fun x hx => ?_⟩
    have h0 := (mem_vanSub _ z).1 hz x hx
    have := congrFun e x
    simpa [h0] using this
  · rintro ⟨g, hg, h⟩
    refine ⟨g, hg, (c • fun x => χ (x i)) - g, ?_, by abel⟩
    refine (mem_vanSub _ _).2 fun x hx => ?_
    simp [h x hx]

theorem mem_dId (D : LieLatticeData C F n Sg r s) (p : ℕ) (χ : F → C) (i : Fin n) (c : C) :
    c ∈ D.dId RC p χ i ↔ ∃ l : Fin n → C,
      (∃ m ∈ D.M, ∀ x, (∑ j, l j * χ (x j)) - m x ∈ pInt (C := C) RC p) ∧
      (∀ j : Fin n, (j : ℕ) < (i : ℕ) → l j = 0) ∧ l i = c := by
  unfold LieLatticeData.dId LieLatticeData.af
  constructor
  · rintro ⟨l, ⟨h1, h2⟩, rfl⟩
    refine ⟨l, ?_, (mem_annSub _ _).1 h2, rfl⟩
    obtain ⟨m, hm, h⟩ := (mem_first_lattice_iff RC D p _).1 h1
    exact ⟨m, hm, fun x => by simpa [linMap_apply] using h x⟩
  · rintro ⟨l, ⟨m, hm, h⟩, h2, rfl⟩
    refine ⟨l, ⟨?_, (mem_annSub _ _).2 h2⟩, rfl⟩
    exact (mem_first_lattice_iff RC D p _).2 ⟨m, hm, fun x => by simpa [linMap_apply] using h x⟩

theorem fund_pow (p : ℕ) [hp : Fact p.Prime] (σ : MulChar F RC) (hσ : IsFund p σ) (k : ℕ) :
    IsFund p (σ ^ p ^ k) := by
  intro a b
  have hq : p ^ k ≠ 0 := pow_ne_zero _ hp.out.ne_zero
  rw [MulChar.pow_apply' _ hq, MulChar.pow_apply' _ hq, MulChar.pow_apply' _ hq]
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 (hσ a b)
  have e : σ (a + b) = (σ a + σ b) + (p : RC) * t := by rw [mul_comm, ht]; ring
  obtain ⟨r1, h1⟩ := exists_add_pow_prime_pow_eq hp.out (σ a + σ b) ((p : RC) * t) k
  obtain ⟨r2, h2⟩ := exists_add_pow_prime_pow_eq hp.out (σ a) (σ b) k
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hq
  rw [e, h1, h2]
  refine Ideal.mem_span_singleton'.2
    ⟨((p : RC) * t) ^ m * t + (σ a + σ b) * ((p : RC) * t) * r1 + σ a * σ b * r2, ?_⟩
  rw [hm, pow_succ ((p : RC) * t) m]
  ring

theorem step_coord (i : Fin n) (a : F) (k : Fin n → F)
    (hk : k ∈ flagSub (Pi.basisFun F (Fin n)) (i : ℕ)) :
    (∀ j : Fin n, (i : ℕ) + 1 ≤ (j : ℕ) → (a • Pi.basisFun F (Fin n) i + k) j = 0) ∧
      (a • Pi.basisFun F (Fin n) i + k) i = a := by
  have hk' := (mem_flagSub_iff i k).1 hk
  constructor
  · intro j hj
    have hne : j ≠ i := by rintro rfl; omega
    simp [Pi.single_apply, hne, hk' j (by omega)]
  · simp [hk' i le_rfl]

theorem step_decomp (i : Fin n) (x : Fin n → F)
    (hx : ∀ j : Fin n, (i : ℕ) + 1 ≤ (j : ℕ) → x j = 0) :
    ∃ k ∈ flagSub (Pi.basisFun F (Fin n)) (i : ℕ), x = x i • Pi.basisFun F (Fin n) i + k := by
  refine ⟨Function.update x i 0, (mem_flagSub_iff _ _).2 fun j hj => ?_, ?_⟩
  · by_cases h : j = i
    · subst h; simp
    · have h' : (i : ℕ) ≠ j := fun e => h (Fin.ext e.symm)
      rw [Function.update_of_ne h]
      exact hx j (by omega)
  · funext j
    by_cases h : j = i
    · subst h; simp
    · simp [Pi.single_apply, h]

theorem pInt_le_RC (p : ℕ) {y : C} (hy : y ∈ pInt (C := C) RC p) : y ∈ RC := by
  obtain ⟨r, rfl⟩ := (mem_pInt RC p y).1 hy
  exact RC.mul_mem r.2 (natCast_mem RC p)

theorem xId_iff (D : LieLatticeData C F n Sg r s) (M : Submodule RC ((Fin n → F) → C))
    (hM : M.toAddSubgroup = D.M) (hint : D.M ≤ stdLat RC _) (ψ : MulChar F RC) (χ : F → C)
    (hχ : ∀ a, χ a = ((ψ a : RC) : C)) (i : Fin n) (c : C) :
    c ∈ D.xId χ i ↔ ∃ c' ∈ xIdeal (stepOrderRes M (flagSub (Pi.basisFun F (Fin n)) (i : ℕ))
      (Pi.basisFun F (Fin n) i)) ψ, (c' : C) = c := by
  have hχ1 : χ 1 = 1 := by simp [hχ]
  rw [mem_xId]
  constructor
  · rintro ⟨g, hg, h⟩
    have hgM : g ∈ M := by
      have : g ∈ M.toAddSubgroup := hM ▸ hg
      exact this
    have hc := step_coord i (1 : F) 0 (Submodule.zero_mem _)
    have hgi := h _ hc.1
    rw [hc.2, hχ1, mul_one] at hgi
    have hcR : c ∈ RC := hgi ▸ (mem_stdLat RC g).1 (hint hg) _
    refine ⟨⟨c, hcR⟩, ?_, rfl⟩
    refine ⟨g, hgM, fun a k hk => ?_⟩
    have hc' := step_coord i a k hk
    rw [h _ hc'.1, hc'.2, hχ a]
    simp [Algebra.smul_def]
  · rintro ⟨c', ⟨g, hgM, h⟩, rfl⟩
    refine ⟨g, (hM ▸ hgM : g ∈ D.M), fun x hx => ?_⟩
    obtain ⟨k, hk, e⟩ := step_decomp i x hx
    conv_lhs => rw [e]
    rw [h _ k hk, hχ]
    simp [Algebra.smul_def]

section dId

variable [DecidableEq F]

theorem dId_forward (D : LieLatticeData C F n Sg r s) (M : Submodule RC ((Fin n → F) → C))
    (hM : M.toAddSubgroup = D.M) (hint : D.M ≤ stdLat RC _) (p : ℕ) (ψ : MulChar F RC)
    (hψ : IsFund p ψ) (χ : F → C) (hχ : ∀ a, χ a = ((ψ a : RC) : C)) (i : Fin n) (c : C)
    (hc : c ∈ D.dId RC p χ i) :
    ∃ c' ∈ idealD p M (flagSub (Pi.basisFun F (Fin n)) (i : ℕ)) (Pi.basisFun F (Fin n) i) ψ,
      (c' : C) = c := by
  obtain ⟨l, ⟨m, hm, hd⟩, h0, rfl⟩ := (mem_dId RC D p χ i c).1 hc
  have hχ0 : χ 0 = 0 := by simp [hχ, MulChar.map_zero]
  have hχ1 : χ 1 = 1 := by simp [hχ]
  have hχm : ∀ a b, χ (a * b) = χ a * χ b := fun a b => by simp [hχ]
  have hχadd : ∀ a b, χ (a + b) - χ a - χ b ∈ pInt (C := C) RC p := by
    intro a b
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 (hψ a b)
    refine (mem_pInt RC p _).2 ⟨t, ?_⟩
    have := congrArg (fun y : RC => (y : C)) ht
    simp only [hχ]
    simpa using this.symm
  have hmM : m ∈ M := by
    have : m ∈ M.toAddSubgroup := hM ▸ hm
    exact this
  set S : (Fin n → F) → C := fun x => ∑ j, l j * χ (x j) with hS
  have hSe : ∀ j, S (Pi.basisFun F (Fin n) j) = l j := by
    intro j
    simp only [hS, Pi.basisFun_apply]
    rw [Finset.sum_eq_single j]
    · simp [hχ1]
    · intro b _ hb
      simp [Pi.single_apply, hb, hχ0]
    · simp
  have hl : ∀ j, l j ∈ RC := by
    intro j
    have h1 := pInt_le_RC RC p (hd (Pi.basisFun F (Fin n) j))
    have h2 := (mem_stdLat RC m).1 (hint hm) (Pi.basisFun F (Fin n) j)
    have h3 := RC.add_mem h1 h2
    rw [sub_add_cancel] at h3
    have h4 : S (Pi.basisFun F (Fin n) j) ∈ RC := h3
    rwa [hSe] at h4
  have hSadd : ∀ x y, S (x + y) - S x - S y ∈ pInt (C := C) RC p := by
    intro x y
    have e : S (x + y) - S x - S y =
        ∑ j, (⟨l j, hl j⟩ : RC) • (χ (x j + y j) - χ (x j) - χ (y j)) := by
      simp only [hS, Pi.add_apply, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Algebra.smul_def]
      change _ = l j * _
      ring
    rw [e]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hχadd _ _)
  have hSsmul : ∀ (a : F) x, S (a • x) = χ a * S x := by
    intro a x
    simp only [hS, Pi.smul_apply, smul_eq_mul, hχm, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hSK : ∀ k ∈ flagSub (Pi.basisFun F (Fin n)) (i : ℕ), S k = 0 := by
    intro k hk
    have hk' := (mem_flagSub_iff _ k).1 hk
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : (j : ℕ) < (i : ℕ)
    · simp [h0 j hj]
    · simp [hk' j (not_lt.mp hj), hχ0]
  have hneg : ∀ x, m x - S x ∈ pInt (C := C) RC p := fun x => by
    have := Submodule.neg_mem _ (hd x)
    simpa using this
  refine ⟨⟨l i, hl i⟩, ⟨m, ⟨hmM, fun x y => ?_⟩, fun a x => ?_, fun k hk => ?_, ?_⟩, rfl⟩
  · have h := Submodule.add_mem _
      (Submodule.sub_mem _ (hneg (x + y)) (Submodule.add_mem _ (hneg x) (hneg y))) (hSadd x y)
    show m (x + y) - m x - m y ∈ pInt (C := C) RC p
    convert h using 1
    ring
  · have h := Submodule.sub_mem _ (hneg (a • x)) (Submodule.smul_mem _ (ψ a) (hneg x))
    convert h using 1
    have e : algebraMap RC C (ψ a) = χ a := (hχ a).symm
    rw [hSsmul, Algebra.smul_def (ψ a) (m x - S x), e]
    ring
  · have := hneg k
    rwa [hSK k hk, sub_zero] at this
  · have := hneg (Pi.basisFun F (Fin n) i)
    rwa [hSe] at this

theorem dId_backward (D : LieLatticeData C F n Sg r s) (M : Submodule RC ((Fin n → F) → C))
    (hM : M.toAddSubgroup = D.M) (p : ℕ) (ψ : MulChar F RC) (χ : F → C)
    (hχ : ∀ a, χ a = ((ψ a : RC) : C)) (i : Fin n) (c' : RC)
    (hc : c' ∈ idealD p M (flagSub (Pi.basisFun F (Fin n)) (i : ℕ)) (Pi.basisFun F (Fin n) i) ψ) :
    (c' : C) ∈ D.dId RC p χ i := by
  obtain ⟨g, ⟨hgM, hadd⟩, h1, h2, h3⟩ := hc
  have hadd' : ∀ x y, g (x + y) - g x - g y ∈ pInt (C := C) RC p := hadd
  have hg0 : g 0 ∈ pInt (C := C) RC p := by
    have := Submodule.neg_mem _ (hadd' 0 0)
    simpa using this
  have hsum : ∀ (t : Finset (Fin n)) (y : Fin n → Fin n → F),
      (∑ j ∈ t, g (y j)) - g (∑ j ∈ t, y j) ∈ pInt (C := C) RC p := by
    intro t y
    induction t using Finset.induction_on with
    | empty =>
      have := Submodule.neg_mem _ hg0
      simpa using this
    | insert a t ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      have := Submodule.sub_mem _ ih (hadd' (y a) (∑ j ∈ t, y j))
      convert this using 1
      ring
  let l : Fin n → C := fun j => if j < i then 0 else if j = i then (c' : C) else
    g (Pi.basisFun F (Fin n) j)
  have hle : ∀ j, l j - g (Pi.basisFun F (Fin n) j) ∈ pInt (C := C) RC p := by
    intro j
    by_cases hj : j < i
    · have hK : Pi.basisFun F (Fin n) j ∈ flagSub (Pi.basisFun F (Fin n)) (i : ℕ) :=
        Submodule.subset_span ⟨j, hj, rfl⟩
      have := Submodule.neg_mem _ (h2 _ hK)
      simpa [l, hj] using this
    · by_cases hji : j = i
      · subst hji
        have := Submodule.neg_mem _ h3
        simpa [l] using this
      · simp [l, hj, hji]
  have hterm : ∀ (x : Fin n → F) j,
      l j * χ (x j) - g (x j • Pi.basisFun F (Fin n) j) ∈ pInt (C := C) RC p := by
    intro x j
    have h := Submodule.sub_mem _ (Submodule.smul_mem _ (ψ (x j)) (hle j)) (h1 (x j) (Pi.basisFun F (Fin n) j))
    convert h using 1
    simp only [Algebra.smul_def, hχ]
    have : algebraMap RC C (ψ (x j)) = (ψ (x j) : C) := rfl
    rw [this]
    ring
  refine (mem_dId RC D p χ i _).2 ⟨l, ⟨g, (hM ▸ hgM : g ∈ D.M), fun x => ?_⟩, fun j hj => ?_, ?_⟩
  · have hx : ∑ j, x j • Pi.basisFun F (Fin n) j = x := by
      simpa using (Pi.basisFun F (Fin n)).sum_repr x
    have h := Submodule.add_mem _ (Submodule.sum_mem _ fun j (_ : j ∈ Finset.univ) => hterm x j)
      (hsum Finset.univ fun j => x j • Pi.basisFun F (Fin n) j)
    convert h using 1
    rw [hx, Finset.sum_sub_distrib]
    ring
  · have hj' : j < i := hj
    simp [l, hj']
  · simp [l]

end dId

end GlobalTheory.CompanionTheory.Ar.Num.PtDx

open GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.GR ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up in

theorem GlobalTheory.CompanionTheory.Ar.Num.PtDx.main : ∀ {o C : Type} [CommRing o] [Field C] [Algebra o C] [IsAlgClosed C] [CharZero C] (RC : Subalgebra o C) (v : Valuation C NNReal), (∀ c, c ∈ RC ↔ v c ≤ 1) → ∀ (p : ℕ) [Fact p.Prime], v (p : C) < 1 → ∀ {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F p] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData C F n Sg r s) (w : C) (χ : Sg → F → C) (φ : Equiv.Perm Sg), D.Base RC p w → ∀ AA : HopfOrder (C := C) RC (Fin n → F), AA.carrier.toAddSubgroup = D.M → FStable F AA.carrier → ∀ (σ : MulChar F RC), IsFund p σ → FlagConcl v p AA.carrier (Pi.basisFun F (Fin n)) σ → ∀ e : Sg → ℕ, (∀ τ a, χ τ a = ((σ ^ p ^ e τ) a : RC)) → (∀ τ, σ ^ p ^ e (φ τ) = σ ^ p ^ (e τ + 1)) → (∀ τ, (∀ g ∈ sqIdeal (augIdeal AA.carrier), (g, 0) ∈ D.Th τ) ∧ (∀ (a : F) g m, (g, m) ∈ D.Th τ → ((fun x => g (a • x)), χ τ a • m) ∈ D.Th τ) ∧ ∀ g ∈ eig AA.carrier (σ ^ p ^ e τ), (g, 0) ∈ D.Th τ → g ∈ sqIdeal (augIdeal AA.carrier)) → ∀ τ i, D.dId RC p (χ τ) i = D.xId (χ τ) i := by
  intro o C _ _ _ _ _ RC v _ p _ _ F _ _ _ _ n Sg r s D w χ φ hB AA hM _ σ hσ hF e hχ _ _ τ i
  obtain ⟨c, δ, h, -, -⟩ := hF
  obtain ⟨-, -, hX, hD, -, -⟩ := h i (e τ)
  have hint := hB.M_le
  ext y
  constructor
  · intro hy
    obtain ⟨c', hc', rfl⟩ := PtDx.dId_forward RC D AA.carrier hM hint p _
      (PtDx.fund_pow RC p σ hσ (e τ)) (χ τ) (hχ τ) i y hy
    rw [hD, ← hX] at hc'
    exact (PtDx.xId_iff RC D AA.carrier hM hint _ (χ τ) (hχ τ) i _).2 ⟨c', hc', rfl⟩
  · intro hy
    obtain ⟨c', hc', rfl⟩ := (PtDx.xId_iff RC D AA.carrier hM hint _ (χ τ) (hχ τ) i y).1 hy
    rw [hX, ← hD] at hc'
    exact PtDx.dId_backward RC D AA.carrier hM p _ (χ τ) (hχ τ) i c' hc'
