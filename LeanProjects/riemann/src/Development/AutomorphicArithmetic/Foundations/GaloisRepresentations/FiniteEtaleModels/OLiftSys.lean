import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.LiftUnit
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.Bezout
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.LiftOfEq

set_option autoImplicit false

noncomputable section

open NumberField

namespace UpperTheory.Gal.FiniteEtaleModels.O

section Congruences

variable {M : Type} [AddCommGroup M]

private theorem cg_mk {n : ℕ} {x y : M} (z : M) (h : x = y + n • z) : Cg n x y := Exists.intro z h

private theorem cg_refl (n : ℕ) (x : M) : Cg n x x := cg_mk 0 (by simp)

private theorem cg_symm {n : ℕ} {x y : M} (h : Cg n x y) : Cg n y x := by
  obtain ⟨z, hz⟩ := h
  exact ⟨-z, by rw [hz]; simp⟩

private theorem cg_trans {n : ℕ} {x y w : M} (h : Cg n x y) (k : Cg n y w) : Cg n x w := by
  obtain ⟨z, hz⟩ := h
  obtain ⟨z', hz'⟩ := k
  exact ⟨z' + z, by rw [hz, hz', smul_add]; abel⟩

private theorem cg_hom {n : ℕ} (f : M →+ M) {x y : M} (h : Cg n x y) : Cg n (f x) (f y) := by
  obtain ⟨z, hz⟩ := h
  exact ⟨f z, by rw [hz, map_add, map_nsmul]⟩

private theorem cg_smul {O : Type} [Ring O] [Module O M] {n : ℕ} (c : O) {x y : M} (h : Cg n x y) :
    Cg n (c • x) (c • y) := by
  obtain ⟨z, hz⟩ := h
  exact ⟨c • z, by rw [hz, smul_add, smul_comm c n z]⟩

private theorem cg_of_dvd {a b : ℕ} (h : a ∣ b) {x y : M} (k : Cg b x y) : Cg a x y := by
  obtain ⟨d, hd⟩ := h
  obtain ⟨z, hz⟩ := k
  exact ⟨d • z, by rw [hz, hd, mul_smul]⟩

private theorem bezout {a b : ℕ} (hc : a.Coprime b) : (a : ℤ) * Nat.gcdA a b + b * Nat.gcdB a b = 1 := by
  have h := Nat.gcd_eq_gcd_ab a b
  rw [Nat.Coprime.gcd_eq_one hc] at h
  push_cast at h
  exact h.symm

private theorem cg_mul {a b : ℕ} (hc : a.Coprime b) {x y : M} (h₁ : Cg a x y) (h₂ : Cg b x y) :
    Cg (a * b) x y := by
  obtain ⟨z₁, h1⟩ := h₁
  obtain ⟨z₂, h2⟩ := h₂
  refine ⟨Nat.gcdA a b • z₂ + Nat.gcdB a b • z₁, ?_⟩
  have e1 : (a : ℤ) • z₁ = x - y := by rw [h1, natCast_zsmul]; abel
  have e2 : (b : ℤ) • z₂ = x - y := by rw [h2, natCast_zsmul]; abel
  rw [← natCast_zsmul]
  push_cast
  have key : ((a : ℤ) * b) • (Nat.gcdA a b • z₂ + Nat.gcdB a b • z₁) =
      ((a : ℤ) * Nat.gcdA a b) • ((b : ℤ) • z₂) + ((b : ℤ) * Nat.gcdB a b) • ((a : ℤ) • z₁) := by
    module
  rw [key, e1, e2, ← add_smul, bezout hc, one_smul]
  abel

private theorem crt_elt {a b : ℕ} (hc : a.Coprime b) (x₁ x₂ : M) :
    Cg a (((b : ℤ) * Nat.gcdB a b) • x₁ + ((a : ℤ) * Nat.gcdA a b) • x₂) x₁ ∧
      Cg b (((b : ℤ) * Nat.gcdB a b) • x₁ + ((a : ℤ) * Nat.gcdA a b) • x₂) x₂ := by
  have hb := bezout hc
  have h' : (b : ℤ) * Nat.gcdB a b = 1 - a * Nat.gcdA a b := by linarith
  refine ⟨⟨Nat.gcdA a b • (x₂ - x₁), ?_⟩, ⟨Nat.gcdB a b • (x₁ - x₂), ?_⟩⟩
  · rw [← natCast_zsmul, h']
    module
  · have h'' : (a : ℤ) * Nat.gcdA a b = 1 - b * Nat.gcdB a b := by linarith
    rw [← natCast_zsmul, h'']
    module

private theorem exists_mix {a b : ℕ} (hc : a.Coprime b) (f : M →+ M) :
    ∃ k : M →+ M, ∀ x, Cg a (k x) (f x) ∧ Cg b (k x) x := by
  let k : M →+ M :=
    { toFun := fun x => ((b : ℤ) * Nat.gcdB a b) • f x + ((a : ℤ) * Nat.gcdA a b) • x
      map_zero' := by simp
      map_add' := by
        intro x y
        simp only [map_add, smul_add]
        abel }
  exact ⟨k, fun x => crt_elt hc (f x) x⟩

private theorem cg_bil {n : ℕ} (B : LinearMap.BilinForm ℤ M) {x x' y y' : M} (hx : Cg n x x')
    (hy : Cg n y y') : (n : ℤ) ∣ B x y - B x' y' := by
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨v, rfl⟩ := hy
  refine ⟨B x' v + B u y' + n * B u v, ?_⟩
  simp [nsmul_eq_mul]
  ring

end Congruences

private theorem cop_pow {q n : ℕ} (hq : q.Prime) (hn : n ≠ 0) :
    (q ^ n.factorization q).Coprime (n / q ^ n.factorization q) :=
  Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hq hn)

private theorem prod_eq (q n : ℕ) : q ^ n.factorization q * (n / q ^ n.factorization q) = n :=
  Nat.ordProj_mul_ordCompl_eq_self n q

private theorem cg_split {M : Type} [AddCommGroup M] {q n : ℕ} (hq : q.Prime) (hn : n ≠ 0) {x y : M}
    (h₁ : Cg (q ^ n.factorization q) x y) (h₂ : Cg (n / q ^ n.factorization q) x y) : Cg n x y := by
  have h := cg_mul (cop_pow hq hn) h₁ h₂
  rwa [prod_eq] at h

private theorem sys_of {O M : Type} [Ring O] [AddCommGroup M] [Module O M] (B : LinearMap.BilinForm ℤ M)
    {q : ℕ} (hq : q.Prime) (G : ℕ → M →+ M)
    (hlin : ∀ e (c : O) x, Cg (q ^ e) (G e (c • x)) (c • G e x))
    (hiso : ∀ e x y, ((q ^ e : ℕ) : ℤ) ∣ B (G e x) (G e y) - B x y)
    (htow : ∀ e x, Cg (q ^ e) (G (e + 1) x) (G e x))
    (hinj : ∀ e x, Cg (q ^ e) (G e x) 0 → Cg (q ^ e) x 0)
    (honto : ∀ e x, ∃ y, Cg (q ^ e) (G e y) x) :
    ∃ g : ℕ → M →+ M,
      (∀ n, 0 < n → ∀ (c : O) x, ∃ z, g n (c • x) = c • g n x + n • z) ∧ (∀ n, 0 < n → ∀ x, ∃ y z, g n y = x + n • z) ∧
      (∀ n, 0 < n → ∀ x z, g n x = n • z → ∃ v, x = n • v) ∧ (∀ n : ℕ, 0 < n → ∀ x y, (n : ℤ) ∣ B (g n x) (g n y) - B x y) ∧
      (∀ n m, 0 < n → 0 < m → ∀ x, ∃ z, g (n * m) x = g n x + n • z) ∧
      (∀ n, 0 < n → ∀ x, Cg (q ^ n.factorization q) (g n x) (G (n.factorization q) x)) ∧
      (∀ n, 0 < n → ∀ x, Cg (n / q ^ n.factorization q) (g n x) x) := by
  have hmix : ∀ n : ℕ, ∃ k : M →+ M, n ≠ 0 → ∀ x, Cg (q ^ n.factorization q) (k x) (G (n.factorization q) x) ∧
      Cg (n / q ^ n.factorization q) (k x) x := by
    intro n
    by_cases hn : n = 0
    · exact ⟨0, fun h => absurd hn h⟩
    · obtain ⟨k, hk⟩ := exists_mix (cop_pow hq hn) (G (n.factorization q))
      exact ⟨k, fun _ => hk⟩
  choose g hg using hmix
  have htow' : ∀ e j x, Cg (q ^ e) (G (e + j) x) (G e x) := by
    intro e j
    induction j with
    | zero => intro x; exact cg_refl _ _
    | succ j ih =>
      intro x
      have h1 : Cg (q ^ e) (G (e + j + 1) x) (G (e + j) x) :=
        cg_of_dvd (pow_dvd_pow q (Nat.le_add_right e j)) (htow (e + j) x)
      exact cg_trans h1 (ih x)
  have hdiv : ∀ n, n ≠ 0 → ∀ D : ℤ, ((q ^ n.factorization q : ℕ) : ℤ) ∣ D →
      ((n / q ^ n.factorization q : ℕ) : ℤ) ∣ D → (n : ℤ) ∣ D := by
    intro n hn D h1 h2
    have hc := Nat.isCoprime_iff_coprime.mpr (cop_pow hq hn)
    have h := hc.mul_dvd h1 h2
    rwa [← Nat.cast_mul, prod_eq] at h
  refine ⟨g, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n hn c x
    have hn0 : n ≠ 0 := hn.ne'
    exact cg_split hq hn0
      (cg_trans (hg n hn0 (c • x)).1 (cg_trans (hlin _ c x) (cg_smul c (cg_symm (hg n hn0 x).1))))
      (cg_trans (hg n hn0 (c • x)).2 (cg_smul c (cg_symm (hg n hn0 x).2)))
  · intro n hn x
    have hn0 : n ≠ 0 := hn.ne'
    obtain ⟨y₁, hy₁⟩ := honto (n.factorization q) x
    obtain ⟨hw1, hw2⟩ := crt_elt (cop_pow hq hn0) y₁ x
    have key : ∀ w : M, Cg (q ^ n.factorization q) w y₁ → Cg (n / q ^ n.factorization q) w x →
        Cg n (g n w) x := fun w h1 h2 =>
      cg_split hq hn0 (cg_trans (hg n hn0 w).1 (cg_trans (cg_hom _ h1) hy₁))
        (cg_trans (hg n hn0 w).2 h2)
    exact ⟨_, key _ hw1 hw2⟩
  · intro n hn x z hz
    have hn0 : n ≠ 0 := hn.ne'
    have h0 : Cg n (g n x) 0 := ⟨z, by rw [hz, zero_add]⟩
    have ha : Cg (q ^ n.factorization q) (g n x) 0 := cg_of_dvd (Nat.ordProj_dvd n q) h0
    have hb : Cg (n / q ^ n.factorization q) (g n x) 0 :=
      cg_of_dvd (Nat.div_dvd_of_dvd (Nat.ordProj_dvd n q)) h0
    have h1 : Cg (q ^ n.factorization q) x 0 := hinj _ x (cg_trans (cg_symm (hg n hn0 x).1) ha)
    have h2 : Cg (n / q ^ n.factorization q) x 0 := cg_trans (cg_symm (hg n hn0 x).2) hb
    obtain ⟨v, hv⟩ := cg_split hq hn0 h1 h2
    exact ⟨v, by rw [hv, zero_add]⟩
  · intro n hn x y
    have hn0 : n ≠ 0 := hn.ne'
    apply hdiv n hn0
    · have h1 := cg_bil B (hg n hn0 x).1 (hg n hn0 y).1
      have h2 := hiso (n.factorization q) x y
      rw [show B (g n x) (g n y) - B x y = (B (g n x) (g n y) - B (G (n.factorization q) x)
        (G (n.factorization q) y)) + (B (G (n.factorization q) x) (G (n.factorization q) y) - B x y) by ring]
      exact dvd_add h1 h2
    · exact cg_bil B (hg n hn0 x).2 (hg n hn0 y).2
  · intro n m hn hm x
    have hn0 : n ≠ 0 := hn.ne'
    have hnm0 : n * m ≠ 0 := (Nat.mul_pos hn hm).ne'
    have hle : n.factorization q ≤ (n * m).factorization q :=
      (Nat.factorization_le_iff_dvd hn0 hnm0).mpr (dvd_mul_right n m) q
    have ha : Cg (q ^ n.factorization q) (g (n * m) x) (g n x) := by
      have e1 := cg_of_dvd (pow_dvd_pow q hle) (hg (n * m) hnm0 x).1
      obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hle
      have e2 : Cg (q ^ n.factorization q) (G ((n * m).factorization q) x) (G (n.factorization q) x) := by
        rw [hj]
        exact htow' _ j x
      exact cg_trans e1 (cg_trans e2 (cg_symm (hg n hn0 x).1))
    have hb : Cg (n / q ^ n.factorization q) (g (n * m) x) (g n x) := by
      have e1 := (hg (n * m) hnm0 x).2
      rw [Nat.ordCompl_mul] at e1
      exact cg_trans (cg_of_dvd (dvd_mul_right _ _) e1) (cg_symm (hg n hn0 x).2)
    exact cg_split hq hn0 ha hb
  · intro n hn x
    exact (hg n hn.ne' x).1
  · intro n hn x
    exact (hg n hn.ne' x).2

private theorem pow_mem_of {A : Type} [CommRing A] (I : Ideal A) {q a c f : ℕ} (hc : c.Coprime q)
    (hn : ((q ^ a * c : ℕ) : A) ∈ I) (hf : (q : A) ^ f ∈ I) : (q : A) ^ a ∈ I := by
  have hcop : c.Coprime (q ^ f) := Nat.Coprime.pow_right f hc
  have hz := bezout hcop
  have hA : (c : A) * (Nat.gcdA c (q ^ f) : A) + (q : A) ^ f * (Nat.gcdB c (q ^ f) : A) = 1 := by
    have h := congrArg (Int.cast : ℤ → A) hz
    push_cast at h
    exact h
  push_cast at hn
  have e : (q : A) ^ a = ((q : A) ^ a * c) * (Nat.gcdA c (q ^ f) : A) +
      (q : A) ^ f * ((q : A) ^ a * (Nat.gcdB c (q ^ f) : A)) := by
    linear_combination (-(q : A) ^ a) * hA
  rw [e]
  exact I.add_mem (I.mul_mem_right _ hn) (I.mul_mem_right _ hf)

end UpperTheory.Gal.FiniteEtaleModels.O

open UpperTheory.Gal.FiniteEtaleModels.O GlobalTheory.UPel.HT.EtLev GlobalTheory.UPel.HT NumberField in
theorem UpperTheory.Gal.FiniteEtaleModels.O.liftSys :
    UpperTheory.Gal.FiniteEtaleModels.LiftSys := by
  intro q _ D hm r hr 𝔞 N₀ hpow hcop g₀
  have hq : q.Prime := Fact.out
  obtain ⟨G, hG⟩ := qSys q D hm r hr 𝔞 hpow g₀
  obtain ⟨g, h1, h2, h3, h4, h5, h6, h7⟩ := sys_of (O := D.O) D.EF hq G (fun e => (hG e).1)
    (fun e => (hG e).2.1) (fun e => (hG e).2.2.1)
    (fun e x => ((adj q D e).2.2 (G e) (hG e).2.1).1 x) (fun e x => ((adj q D e).2.2 (G e) (hG e).2.1).2 x)
  refine ⟨g, h1, h2, h3, h4, h5, ?_, ?_⟩
  · have hnd : ¬ q ∣ N₀ := (Nat.Prime.coprime_iff_not_dvd hq).mp hcop.symm
    have hN : N₀ ≠ 0 := fun h => hnd (h ▸ dvd_zero q)
    have hv : N₀.factorization q = 0 := Nat.factorization_eq_zero_of_not_dvd hnd
    intro x
    have h := h7 N₀ (Nat.pos_of_ne_zero hN) x
    rw [hv, pow_zero, Nat.div_one] at h
    exact h
  · intro n hn hmem x
    have hn0 : n ≠ 0 := hn.ne'
    obtain ⟨f, hf⟩ := hpow
    have hqf : (q : 𝓞 D.F) ^ f ∈ 𝔞 := hf (Ideal.pow_mem_pow (GlobalTheory.UPel.HT.ES.p_mem_uIdeal D r) f)
    have hn' : ((q ^ n.factorization q * (n / q ^ n.factorization q) : ℕ) : 𝓞 D.F) ∈ 𝔞 := by
      rw [prod_eq]
      exact hmem
    have hqa : (q : 𝓞 D.F) ^ n.factorization q ∈ 𝔞 :=
      pow_mem_of 𝔞 (Nat.coprime_ordCompl hq hn0).symm hn' hqf
    rw [← (hG (n.factorization q)).2.2.2 hqa x]
    obtain ⟨z, hz⟩ := h6 n hn x
    have hzero : (wSub D 𝔞 1).mkQ (q ^ n.factorization q • z) = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, ← Nat.cast_smul_eq_nsmul D.O]
      apply Submodule.subset_span
      refine ⟨((q ^ n.factorization q : ℕ) : 𝓞 D.F), ?_, z, ?_⟩
      · rw [pow_one]
        exact_mod_cast hqa
      · rw [map_natCast]
    rw [hz, map_add, hzero, add_zero]
