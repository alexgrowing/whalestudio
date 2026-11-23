import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubPairRight
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsHomLocBijectiveGrSum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFinsetSum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmulEqZeroOfMem
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

theorem exists_grSum_semilift {ι : Type} {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R')
    {A : ℤ → Type} [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)]
    {x : ι → ∀ n, A n →ₗ[R] A (n + 1)} (hx : OperatorsCommute x)
    {N : Type} [AddCommGroup N] [Module (MvPolynomial ι R') N] (φ : ∀ n, A n →+ N)
    (hr : ∀ n (r : R) (a : A n),
      φ n (r • a) = (MvPolynomial.C (f r) : MvPolynomial ι R') • φ n a)
    (hX : ∀ i n (a : A n),
      φ (n + 1) (x i n a) = (MvPolynomial.X i : MvPolynomial ι R') • φ n a) :
    ∃ Φ : GrSum hx →+ N, (∀ n a, Φ (GrSum.of hx n a) = φ n a) ∧
      ∀ (q : MvPolynomial ι R) (u : GrSum hx), Φ (q • u) = (MvPolynomial.map f q) • Φ u := by
  letI : Module R N := Module.compHom N ((MvPolynomial.C : R' →+* MvPolynomial ι R').comp f)
  letI : Module (MvPolynomial ι R) N :=
    Module.compHom N (MvPolynomial.map f : MvPolynomial ι R →+* MvPolynomial ι R')
  haveI : IsScalarTower R (MvPolynomial ι R) N := ⟨fun r q m => by
    change (MvPolynomial.map f (r • q)) • m =
      (MvPolynomial.C (f r) : MvPolynomial ι R') • (MvPolynomial.map f q) • m
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, mul_smul]⟩
  let ψ : ∀ n, A n →ₗ[R] N := fun n =>
    { toFun := φ n, map_add' := map_add _, map_smul' := fun r a => hr n r a }
  have hψ : ∀ i n a, ψ (n + 1) (x i n a) = (MvPolynomial.X i : MvPolynomial ι R) • ψ n a := by
    intro i n a
    change φ (n + 1) (x i n a) = (MvPolynomial.map f (MvPolynomial.X i)) • φ n a
    rw [MvPolynomial.map_X]
    exact hX i n a
  refine ⟨(GrSum.lift hx ψ hψ).toAddMonoidHom, fun n a => GrSum.lift_of hx ψ hψ n a,
    fun q u => ?_⟩
  exact (GrSum.lift hx ψ hψ).map_smul q u

section Tower

variable {ι : Type} [LinearOrder ι] {R : Type} [CommRing R] {g : ℕ} {ρ : Fin g → R}
  {T : ℕ → ℤ → Finset ι → Type} [∀ e t S, AddCommGroup (T e t S)] [∀ e t S, Module R (T e t S)]
  {res : ∀ e t (S S' : Finset ι), S ⊆ S' → T e t S →ₗ[R] T e t S'}
  {p : ∀ e t S, T (e + 1) t S →ₗ[R] T e t S}
  {mm : ι → ∀ e t S, T e t S →ₗ[R] T e (t + 1) S}

theorem smul_mem_Ks (H : TowerAx ρ res p mm) {e : ℕ} {t : ℤ} {S : Finset ι} (hS : S.Nonempty)
    {r : R} (hr : r ∈ Ideal.span (Set.range ρ) ^ (e + 1)) (y : T (e + 1) t S) :
    r • y ∈ Ks p e t S := by
  rw [mem_Ks hS, map_smul]
  exact H.smul_eq_zero_of_mem hS (m := e + 1) (n := 0) (by omega) hr (by simp)

variable (hc : ∀ e S, OperatorsCommute (ι := ι) (R := R) (A := fun t => T e t S)
  fun j t => mm j e t S)

theorem exists_mulMap (H : TowerAx ρ res p mm) {e : ℕ} {r : R}
    (hr : r ∈ Ideal.span (Set.range ρ) ^ (e + 1)) {S : Finset ι} (hS : S.Nonempty) :
    ∃ Φ : GrSum (hc (e + 1) S) →+ H.Tot hc S,
      (∀ t y, Φ (GrSum.of (hc (e + 1) S) t y) =
        (H.ops hc S).of e t ⟨r • y, smul_mem_Ks H hS hr y⟩) ∧
      ∀ (q : MvPolynomial ι R) (u : GrSum (hc (e + 1) S)),
        Φ (q • u) = (MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial (Fin g) R) q) • Φ u := by
  let μ : ∀ t, T (e + 1) t S →+ Ks p e t S := fun t =>
    { toFun := fun y => ⟨r • y, smul_mem_Ks H hS hr y⟩
      map_zero' := Subtype.ext (smul_zero r)
      map_add' := fun a b => Subtype.ext (smul_add r a b) }
  obtain ⟨Φ, h1, h2⟩ := exists_grSum_semilift (MvPolynomial.C : R →+* MvPolynomial (Fin g) R)
    (hc (e + 1) S) (N := H.Tot hc S) (fun t => ((H.ops hc S).of e t).comp (μ t))
    (fun t c a => by
      simp only [AddMonoidHom.comp_apply]
      rw [BiOps.C_C_smul_of]
      congr 1
      exact Subtype.ext (smul_comm r c a))
    (fun j t a => by
      simp only [AddMonoidHom.comp_apply]
      rw [BiOps.X_smul_of]
      congr 1
      apply Subtype.ext
      change r • mm j (e + 1) t S a = mm j (e + 1) t S (r • a)
      rw [map_smul])
  exact ⟨Φ, h1, h2⟩

def unitIdeal (H : TowerAx ρ res p mm) (one : ∀ e (i : ι), T e 0 {i}) (i : ι)
    (Q : Submodule (MvPolynomial ι (MvPolynomial (Fin g) R)) (H.Tot hc {i})) (e : ℕ) : Ideal R where
  carrier := {r | ∃ h : r • one (e + 1) i ∈ Ks p e 0 {i},
    (H.ops hc {i}).of e 0 ⟨r • one (e + 1) i, h⟩ ∈ Q}
  add_mem' := by
    rintro a b ⟨ha, ma⟩ ⟨hb, mb⟩
    have h : (a + b) • one (e + 1) i ∈ Ks p e 0 {i} := by
      rw [add_smul]
      exact add_mem ha hb
    refine ⟨h, ?_⟩
    have e1 : (⟨(a + b) • one (e + 1) i, h⟩ : Ks p e 0 {i}) =
        ⟨a • one (e + 1) i, ha⟩ + ⟨b • one (e + 1) i, hb⟩ := Subtype.ext (add_smul a b _)
    rw [e1, map_add]
    exact add_mem ma mb
  zero_mem' := by
    have h : (0 : R) • one (e + 1) i ∈ Ks p e 0 {i} := by
      rw [zero_smul]
      exact zero_mem _
    refine ⟨h, ?_⟩
    have e1 : (⟨(0 : R) • one (e + 1) i, h⟩ : Ks p e 0 {i}) = 0 := Subtype.ext (zero_smul R _)
    rw [e1, map_zero]
    exact zero_mem _
  smul_mem' := by
    rintro c a ⟨ha, ma⟩
    have h : (c • a) • one (e + 1) i ∈ Ks p e 0 {i} := by
      rw [smul_assoc]
      exact Submodule.smul_mem _ c ha
    refine ⟨h, ?_⟩
    have e1 : (⟨(c • a) • one (e + 1) i, h⟩ : Ks p e 0 {i}) =
        c • ⟨a • one (e + 1) i, ha⟩ := Subtype.ext (smul_assoc c a _)
    rw [e1, ← BiOps.C_C_smul_of]
    exact Q.smul_mem _ ma

theorem pow_le_unitIdeal (H : TowerAx ρ res p mm) (one : ∀ e (i : ι), T e 0 {i})
    (hone : ∀ e i, p e 0 {i} (one (e + 1) i) = one e i) (i : ι)
    (Q : Submodule (MvPolynomial ι (MvPolynomial (Fin g) R)) (H.Tot hc {i}))
    (hQ : ∀ l, (H.ops hc {i}).of 0 0 ⟨ρ l • one (0 + 1) i,
      smul_mem_Ks H (Finset.singleton_nonempty i) (by simpa using rho_mem l) _⟩ ∈ Q) (e : ℕ) :
    Ideal.span (Set.range ρ) ^ (e + 1) ≤ unitIdeal hc H one i Q e := by
  have hS : ({i} : Finset ι).Nonempty := Finset.singleton_nonempty i
  induction e with
  | zero =>
    rw [zero_add, pow_one, Ideal.span_le]
    rintro _ ⟨l, rfl⟩
    exact ⟨_, hQ l⟩
  | succ e ih =>
    rw [pow_succ, Ideal.mul_le]
    intro u hu v hv
    obtain ⟨h, hm⟩ := ih hu
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨l, rfl⟩ := hv
      have hmem : u * ρ l ∈ Ideal.span (Set.range ρ) ^ (e + 1 + 1) := by
        rw [pow_succ]
        exact Ideal.mul_mem_mul hu (rho_mem l)
      have h' := smul_mem_Ks H hS hmem (one (e + 1 + 1) i)
      refine ⟨h', ?_⟩
      have hb : p (e + 1) 0 {i} (u • one (e + 1 + 1) i) =
          ((⟨u • one (e + 1) i, h⟩ : Ks p e 0 {i}) : T (e + 1) 0 {i}) := by
        rw [map_smul, hone]
      have e1 : (⟨(u * ρ l) • one (e + 1 + 1) i, h'⟩ : Ks p (e + 1) 0 {i}) =
          (H.ops hc {i}).y l e 0 ⟨u • one (e + 1) i, h⟩ := by
        apply Subtype.ext
        change (u * ρ l) • one (e + 1 + 1) i = (H.yK l e 0 {i} ⟨u • one (e + 1) i, h⟩ : _)
        rw [H.coe_yK l hS _ _ hb, smul_smul, mul_comm]
      rw [e1, ← BiOps.C_X_smul_of]
      exact Q.smul_mem _ hm
    | zero => simpa using zero_mem (unitIdeal hc H one i Q (e + 1))
    | add a b _ _ ha hb =>
      rw [mul_add]
      exact add_mem ha hb
    | smul c a _ ha =>
      rw [smul_eq_mul, mul_left_comm]
      exact Ideal.mul_mem_left _ c ha

theorem pow_smul_add_mem {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (Q : Submodule A M)
    (x : A) {a b : M} (ha : ∃ k : ℕ, x ^ k • a ∈ Q) (hb : ∃ k : ℕ, x ^ k • b ∈ Q) :
    ∃ k : ℕ, x ^ k • (a + b) ∈ Q := by
  obtain ⟨k, hk⟩ := ha
  obtain ⟨k', hk'⟩ := hb
  refine ⟨k + k', ?_⟩
  rw [smul_add]
  refine add_mem ?_ ?_
  · rw [add_comm, pow_add, mul_smul]
    exact Q.smul_mem _ hk
  · rw [pow_add, mul_smul]
    exact Q.smul_mem _ hk'

theorem exists_pow_smul_mem (H : TowerAx ρ res p mm) (one : ∀ e (i : ι), T e 0 {i}) (i : ι)
    (hform : ∀ e t (a : T e t {i}), ∃ (k : ℕ) (q : MvPolynomial ι R) (t' : ℤ) (w : T e t' {i}),
      w ∈ Ideal.span (Set.range ρ) • (⊤ : Submodule R (T e t' {i})) ∧
      (MvPolynomial.X i : MvPolynomial ι R) ^ k • GrSum.of (hc e {i}) t a =
        q • GrSum.of (hc e {i}) 0 (one e i) + GrSum.of (hc e {i}) t' w)
    (Q : Submodule (MvPolynomial ι (MvPolynomial (Fin g) R)) (H.Tot hc {i}))
    (hQ : ∀ e r (hr : r ∈ Ideal.span (Set.range ρ) ^ (e + 1)),
      (H.ops hc {i}).of e 0 ⟨r • one (e + 1) i,
        smul_mem_Ks H (Finset.singleton_nonempty i) hr _⟩ ∈ Q)
    (m : H.Tot hc {i}) :
    ∃ k : ℕ, (MvPolynomial.X i : MvPolynomial ι (MvPolynomial (Fin g) R)) ^ k • m ∈ Q := by
  have hS : ({i} : Finset ι).Nonempty := Finset.singleton_nonempty i
  have hker : ∀ (e : ℕ) (t : ℤ) (x : T (e + 1) t {i}), x ∈ Ks p e t {i} ↔
      x ∈ Ideal.span (Set.range ρ) ^ (e + 1) • (⊤ : Submodule R (T (e + 1) t {i})) := by
    intro e t x
    rw [← H.ker_eq e t {i} hS, mem_Ks hS, LinearMap.mem_ker]
  induction m using (H.ops hc {i}).induction with
  | h0 => exact ⟨0, by simp⟩
  | hadd a b ha hb => exact pow_smul_add_mem Q _ ha hb
  | hof e t a =>
    obtain ⟨x, hx⟩ := a
    have hx' := (hker e t x).1 hx
    suffices hs : ∀ x ∈ Ideal.span (Set.range ρ) ^ (e + 1) • (⊤ : Submodule R (T (e + 1) t {i})),
        ∀ h : x ∈ Ks p e t {i}, ∃ k : ℕ,
          (MvPolynomial.X i : MvPolynomial ι (MvPolynomial (Fin g) R)) ^ k •
            (H.ops hc {i}).of e t ⟨x, h⟩ ∈ Q from hs x hx' hx
    intro x hx
    induction hx using Submodule.smul_induction_on' with
    | smul r hr y _ =>
      intro h
      obtain ⟨k, q, t', w, hw, e1⟩ := hform (e + 1) t y
      obtain ⟨Φ, hΦ1, hΦ2⟩ := exists_mulMap hc H hr hS
      have e2 := congrArg Φ e1
      rw [hΦ2, map_add, hΦ2, hΦ1, hΦ1, hΦ1, map_pow, MvPolynomial.map_X] at e2
      have hz : r • w = 0 := H.smul_eq_zero_of_mem (e := e + 1) hS (m := e + 1) (n := 1) rfl hr
        (by simpa using hw)
      have e3 : (⟨r • w, smul_mem_Ks H hS hr w⟩ : Ks p e t' {i}) = 0 := Subtype.ext hz
      rw [e3, map_zero, add_zero] at e2
      refine ⟨k, ?_⟩
      rw [show (⟨r • y, h⟩ : Ks p e t {i}) = ⟨r • y, smul_mem_Ks H hS hr y⟩ from rfl, e2]
      exact Q.smul_mem _ (hQ e r hr)
    | add a ha b hb iha ihb =>
      intro h
      have e1 : (⟨a + b, h⟩ : Ks p e t {i}) =
          ⟨a, (hker e t a).2 ha⟩ + ⟨b, (hker e t b).2 hb⟩ := rfl
      rw [e1, map_add]
      exact pow_smul_add_mem Q _ (iha _) (ihb _)

end Tower

theorem tot_singleton_finite_up_to_X :
    ∀ (ι : Type) [LinearOrder ι] (R : Type) [CommRing R] (g : ℕ) (ρ : Fin g → R) (T : ℕ → ℤ → Finset ι → Type) [∀ e t S, AddCommGroup (T e t S)] [∀ e t S, Module R (T e t S)] (res : ∀ e t (S S' : Finset ι), S ⊆ S' → T e t S →ₗ[R] T e t S') (p : ∀ e t S, T (e + 1) t S →ₗ[R] T e t S) (mm : ι → ∀ e t S, T e t S →ₗ[R] T e (t + 1) S) (hc : ∀ e S, OperatorsCommute (ι := ι) (R := R) (A := fun t => T e t S) fun j t => mm j e t S) (H : TowerAx ρ res p mm) (one : ∀ e (i : ι), T e 0 {i}), (∀ e i, p e 0 {i} (one (e + 1) i) = one e i) → (∀ e i t (a : T e t {i}), ∃ (k : ℕ) (q : MvPolynomial ι R) (t' : ℤ) (w : T e t' {i}), w ∈ Ideal.span (Set.range ρ) • (⊤ : Submodule R (T e t' {i})) ∧ (MvPolynomial.X i : MvPolynomial ι R) ^ k • GrSum.of (hc e {i}) t a = q • GrSum.of (hc e {i}) 0 (one e i) + GrSum.of (hc e {i}) t' w) → ∀ i : ι, ∃ s : Finset (H.Tot hc {i}), ∀ m : H.Tot hc {i}, ∃ k : ℕ, (MvPolynomial.X i : MvPolynomial ι (MvPolynomial (Fin g) R)) ^ k • m ∈ Submodule.span (MvPolynomial ι (MvPolynomial (Fin g) R)) (s : Set (H.Tot hc {i})) := by
  intro ι _ R _ g ρ T _ _ res p mm hc H one hone hform i
  classical
  have hS : ({i} : Finset ι).Nonempty := Finset.singleton_nonempty i
  let f : Fin g → H.Tot hc {i} := fun l => (H.ops hc {i}).of 0 0 ⟨ρ l • one (0 + 1) i,
    smul_mem_Ks H hS (by simpa using rho_mem l) _⟩
  refine ⟨Finset.univ.image f, fun m => ?_⟩
  set Q := Submodule.span (MvPolynomial ι (MvPolynomial (Fin g) R))
    ((Finset.univ.image f : Finset (H.Tot hc {i})) : Set (H.Tot hc {i})) with hQdef
  have hf : ∀ l, f l ∈ Q := fun l => Submodule.subset_span (by simp)
  refine exists_pow_smul_mem hc H one i (hform · i) Q (fun e r hr => ?_) m
  obtain ⟨_, h⟩ := pow_le_unitIdeal hc H one hone i Q hf e hr
  exact h

end GlobalTheory.CompanionTheory.FormalAlg.Lift
