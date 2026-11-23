import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrismaticDieudonnePerfdIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrPowEqPrime

set_option autoImplicit false

noncomputable section

open CategoryTheory WittVector
open scoped TensorProduct Pointwise ChangeOfRings

namespace GlobalTheory.RingChain

open GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.Published GlobalTheory.PerfdLat

section Defs

variable {A : Type} [CommRing A]

abbrev Qt {X : Type} [AddCommGroup X] [Module A X] (P N : Submodule A X) : Type := P ⧸ N.comap P.subtype

variable (A) in

def IsFrobLin (p q : ℕ) {M N : Type} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] (ψ : M →+ N) : Prop :=
  ∀ f : A →+* A ⧸ Ideal.span {(p : A)}, (∀ a, f a = Ideal.Quotient.mk _ (a ^ q)) →
    ∃ e : (ModuleCat.extendScalars f).obj (ModuleCat.of A M) ≃+ N,
      ∀ (a : A) (x : M), e ((Ideal.Quotient.mk _ a : A ⧸ Ideal.span {(p : A)}) ⊗ₜ[A, f] x) = a • ψ x

abbrev baseOf (π : A) (h : ℕ) : Submodule A (Fin h → A) := π • ⊤

structure RChain (p : ℕ) (A : Type) [CommRing A] (h o : ℕ) (π : A) (γ : ℕ → A) (Lie Om : Type) [AddCommGroup Lie]
    [Module A Lie] [AddCommGroup Om] [Module A Om] where

  L : ℕ → Submodule A (Fin h → A)
  finite : ∀ n, Module.Finite A (L n)
  projective : ∀ n, Module.Projective A (L n)
  base_le : ∀ n, baseOf π h ≤ L n
  succ_le : ∀ n, L (n + 1) ≤ L n
  kill : ∀ n < o, γ 0 • L (n + 1) ≤ baseOf π h
  gam : ∀ n < o, γ n • L n ≤ L (n + 1)
  lfree : ∀ n < o, Module.Projective (A ⧸ Ideal.span {γ n}) ((A ⧸ Ideal.span {γ n}) ⊗[A] Qt (L n) (L (n + 1)))

  j : Lie →ₗ[A] Qt (L 0) (baseOf π h)

  ρ : Om →ₗ[A] Qt (L 0) (baseOf π h) ⧸ LinearMap.range j
  ρ_surj : Function.Surjective ρ

  ψ : ∀ n, Qt (L (n + 1)) (baseOf π h) →+ Qt (L n) (baseOf π h)
  ψ_lin : ∀ n < o, IsFrobLin A p p (ψ n)

  κ : ∀ n, Qt (L n) (L (n + 1)) →+ Lie ⧸ (p : A) • (⊤ : Submodule A Lie)
  κ_lin : ∀ n < o, IsFrobLin A p (p ^ (n + 1)) (κ n)

variable {A' : Type} [CommRing A']

def mv (φ : A →+* A') {h : ℕ} (M : Matrix (Fin h) (Fin h) ℤ) (x : Fin h → A) : Fin h → A' :=
  (M.map (Int.cast : ℤ → A')).mulVec fun i => φ (x i)

variable {p h o : ℕ} {π : A} {γ : ℕ → A} {Lie Om : Type} [AddCommGroup Lie] [Module A Lie] [AddCommGroup Om] [Module A Om]
  {π' : A'} {γ' : ℕ → A'} {Lie' Om' : Type} [AddCommGroup Lie'] [Module A' Lie'] [AddCommGroup Om'] [Module A' Om']

structure RChain.Map (C : RChain p A h o π γ Lie Om) (C' : RChain p A' h o π' γ' Lie' Om') (φ : A →+* A')
    (M : Matrix (Fin h) (Fin h) ℤ) (l : Lie → Lie') (m : Om → Om') : Prop where
  mem : ∀ n, ∀ x ∈ C.L n, mv φ M x ∈ C'.L n
  j : ∀ (y : Lie) (x : C.L 0) (x' : C'.L 0), x'.1 = mv φ M x.1 → C.j y = Submodule.Quotient.mk x →
    C'.j (l y) = Submodule.Quotient.mk x'
  ρ : ∀ (w : Om) (x : C.L 0) (x' : C'.L 0), x'.1 = mv φ M x.1 →
    C.ρ w = Submodule.Quotient.mk (Submodule.Quotient.mk x) →
      C'.ρ (m w) = Submodule.Quotient.mk (Submodule.Quotient.mk x')
  ψ : ∀ n < o, ∀ (x : C.L (n + 1)) (x' : C'.L (n + 1)) (y : C.L n) (y' : C'.L n), x'.1 = mv φ M x.1 → y'.1 = mv φ M y.1 →
    C.ψ n (Submodule.Quotient.mk x) = Submodule.Quotient.mk y → C'.ψ n (Submodule.Quotient.mk x') = Submodule.Quotient.mk y'
  κ : ∀ n < o, ∀ (x : C.L n) (x' : C'.L n) (y : Lie), x'.1 = mv φ M x.1 →
    C.κ n (Submodule.Quotient.mk x) = Submodule.Quotient.mk y →
      C'.κ n (Submodule.Quotient.mk x') = Submodule.Quotient.mk (l y)

theorem mv_id (x : Fin h → A) : mv (RingHom.id A) 1 x = x := by
  rw [mv, Matrix.map_one _ Int.cast_zero Int.cast_one, Matrix.one_mulVec]; rfl

theorem RChain.Map.refl (C : RChain p A h o π γ Lie Om) : C.Map C (RingHom.id A) 1 id id where
  mem n x hx := by rwa [mv_id]
  j y x x' e k := by rw [mv_id] at e; rw [Subtype.ext e]; exact k
  ρ y x x' e k := by rw [mv_id] at e; rw [Subtype.ext e]; exact k
  ψ n _ x x' y y' e e' k := by rw [mv_id] at e e'; rw [Subtype.ext e, Subtype.ext e']; exact k
  κ n _ x x' y e k := by rw [mv_id] at e; rw [Subtype.ext e]; exact k

def RChain.kerJ (C : RChain p A h o π γ Lie Om) {R : Type} [CommRing R] (φ : A →+* R) {r : ℕ} (y : Fin r → Lie) :
    Set (Fin r → R) :=
  {c | ∃ x : Fin r → C.L 0, (∀ l, C.j (y l) = Submodule.Quotient.mk (x l)) ∧
    ∑ l, c l • piMap φ _ (x l).1 ∈ baseOf (φ π) h}

def RChain.kerR (C : RChain p A h o π γ Lie Om) {R : Type} [CommRing R] (φ : A →+* R) {r : ℕ} (w : Fin r → Om) :
    Set (Fin r → R) :=
  {c | ∃ x : Fin r → C.L 0, (∀ l, C.ρ (w l) = Submodule.Quotient.mk (Submodule.Quotient.mk (x l))) ∧
    ∑ l, c l • piMap φ _ (x l).1 ∈ Submodule.span R
      {z | ∃ x₀ : C.L 0, Submodule.Quotient.mk x₀ ∈ LinearMap.range C.j ∧ z = piMap φ _ x₀.1}}

variable (A') in

def ModIso [Algebra A A'] (a : A) : Prop :=
  (∀ r : A', ∃ x : A, algebraMap A A' a ∣ r - algebraMap A A' x) ∧ ∀ x : A, algebraMap A A' a ∣ algebraMap A A' x → a ∣ x

end Defs

namespace Examples₂

variable {A : Type} [CommRing A]

theorem exists_isFrobLin (p q : ℕ) {M N : Type} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] (a d : A)
    (hd : Associated (a ^ q) d) (eM : M ≃ₗ[A] A ⧸ Ideal.span {a}) (eN : (A ⧸ Ideal.span {d}) ≃ₗ[A] N) (hp : d ∣ (p : A)) :
    ∃ ψ : M →+ N, IsFrobLin A p q ψ := by
  by_cases hf : ∃ f : A →+* A ⧸ Ideal.span {(p : A)}, ∀ a, f a = Ideal.Quotient.mk _ (a ^ q)
  swap
  · exact ⟨0, fun f h => absurd ⟨f, h⟩ hf⟩
  obtain ⟨f, hf⟩ := hf
  let g : (A ⧸ Ideal.span {(p : A)}) →+* A ⧸ Ideal.span {d} :=
    Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.2 hp)
  have hg : ∀ r, g (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ r := fun _ => rfl
  let F : (A ⧸ Ideal.span {a}) →+* A ⧸ Ideal.span {d} := Ideal.Quotient.lift _ (g.comp f) fun x hx => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.1 hx
    rw [RingHom.comp_apply, hf, hg, Ideal.Quotient.eq_zero_iff_mem, mul_pow, Ideal.mem_span_singleton]
    exact hd.symm.dvd.mul_right _
  have hF : ∀ r, F (Ideal.Quotient.mk _ r) = g (f r) := fun _ => rfl
  refine ⟨eN.toLinearMap.toAddMonoidHom.comp (F.toAddMonoidHom.comp eM.toLinearMap.toAddMonoidHom), fun f' hf' => ?_⟩
  obtain rfl : f' = f := RingHom.ext fun a => (hf' a).trans (hf a).symm
  let X : ModuleCat A := (ModuleCat.restrictScalars f').obj (ModuleCat.of _ (A ⧸ Ideal.span {(p : A)}))
  let k : A → X := fun r => (Ideal.Quotient.mk _ r : A ⧸ Ideal.span {(p : A)})
  have hs : ∀ r s : A, r • k s = k (r ^ q * s) := fun r s => by
    change f' r * Ideal.Quotient.mk _ s = Ideal.Quotient.mk _ _
    rw [hf, map_mul]
  let g' : X →+ A ⧸ Ideal.span {d} := g.toAddMonoidHom
  let u : X ⊗[A] M →+ A ⧸ Ideal.span {d} := TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun b => (AddMonoidHom.mulLeft (g' b)).comp (F.toAddMonoidHom.comp eM.toLinearMap.toAddMonoidHom))
      fun b b' => AddMonoidHom.ext fun x => by simp [add_mul])
    fun r b x => by
      obtain ⟨s, rfl⟩ : ∃ s, k s = b := Ideal.Quotient.mk_surjective (I := Ideal.span {(p : A)}) b
      rw [hs]
      change g (Ideal.Quotient.mk _ _) * F (eM x) = g (Ideal.Quotient.mk _ _) * F (eM (r • x))
      rw [map_smul, Algebra.smul_def, map_mul, map_mul, map_mul, Ideal.Quotient.algebraMap_eq, hF, hf]
      ring
  have hu : ∀ b x, u (k b ⊗ₜ x) = Ideal.Quotient.mk _ b * F (eM x) := fun _ _ => rfl
  have gen : ∀ t : X ⊗[A] M, ∃ r : A, t = k r ⊗ₜ eM.symm 1 := fun t => by
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, (TensorProduct.zero_tmul _ _).symm⟩
    | add s t hs ht =>
      obtain ⟨r, rfl⟩ := hs
      obtain ⟨r', rfl⟩ := ht
      exact ⟨r + r', (TensorProduct.add_tmul _ _ _).symm⟩
    | tmul b x =>
      obtain ⟨s, hs'⟩ := Ideal.Quotient.mk_surjective (eM x)
      obtain ⟨r, rfl⟩ : ∃ s, k s = b := Ideal.Quotient.mk_surjective (I := Ideal.span {(p : A)}) b
      have hx : x = s • eM.symm 1 := by
        rw [← map_smul, LinearEquiv.eq_symm_apply, ← hs', Algebra.smul_def, mul_one]; rfl
      exact ⟨s ^ q * r, by rw [hx, ← TensorProduct.smul_tmul, hs]⟩
  have bij : Function.Bijective u := by
    refine ⟨(injective_iff_map_eq_zero _).2 fun t ht => ?_, fun y => ?_⟩
    · obtain ⟨r, rfl⟩ := gen t
      rw [hu, LinearEquiv.apply_symm_apply, map_one, mul_one, Ideal.Quotient.eq_zero_iff_mem,
        Ideal.mem_span_singleton] at ht
      obtain ⟨c, rfl⟩ := hd.dvd.trans ht
      have h0 : a • eM.symm 1 = 0 := by
        rw [← map_smul, Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq,
          Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self a), map_zero]
      rw [← hs, TensorProduct.smul_tmul, h0, TensorProduct.tmul_zero]
    · obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
      exact ⟨k r ⊗ₜ eM.symm 1, by rw [hu, LinearEquiv.apply_symm_apply, map_one, mul_one]⟩
  refine ⟨(AddEquiv.ofBijective u bij).trans eN.toAddEquiv, fun r x => ?_⟩
  change eN (g (Ideal.Quotient.mk _ r) * F (eM x)) = r • eN (F (eM x))
  rw [← map_smul, Algebra.smul_def]
  rfl

abbrev line (u : A) : Submodule A (Fin 1 → A) := baseOf u 1

theorem mem_line (u : A) (x : Fin 1 → A) : x ∈ line u ↔ u ∣ x 0 := by
  rw [Submodule.mem_smul_pointwise_iff_exists]
  exact ⟨fun ⟨y, _, h⟩ => ⟨y 0, (congrFun h 0).symm⟩, fun ⟨c, h⟩ => ⟨fun _ => c, trivial, funext fun i => by
    rw [Subsingleton.elim i 0, h]; rfl⟩⟩

def lineEquiv [IsDomain A] {u : A} (hu : u ≠ 0) : A ≃ₗ[A] line u :=
  LinearEquiv.ofBijective (LinearMap.toSpanSingleton A _ ⟨fun _ => u, (mem_line _ _).2 dvd_rfl⟩)
    ⟨fun r s h => mul_right_cancel₀ hu (by simpa using congrFun (congrArg Subtype.val h) 0), fun x => by
      obtain ⟨c, hc⟩ := (mem_line _ _).1 x.2
      exact ⟨c, Subtype.ext (funext fun i => by rw [Subsingleton.elim i 0, hc, mul_comm]; rfl)⟩⟩

def qtEquiv [IsDomain A] {u : A} (hu : u ≠ 0) (d v : A) (h : v = u * d) :
    (A ⧸ Ideal.span {d}) ≃ₗ[A] Qt (line u) (line v) :=
  Submodule.Quotient.equiv _ _ (lineEquiv hu) (by
    rw [Submodule.map_equiv_eq_comap_symm]
    ext x
    obtain ⟨r, rfl⟩ := (lineEquiv hu).surjective x
    rw [Submodule.mem_comap, Submodule.mem_comap, mem_line, h]
    change (lineEquiv hu).symm (lineEquiv hu r) ∈ Ideal.span {d} ↔ u * d ∣ r * u
    rw [LinearEquiv.symm_apply_apply, Ideal.mem_span_singleton, mul_comm r, mul_dvd_mul_iff_left hu])

theorem projective_tensor {M : Type} [AddCommGroup M] [Module A M] (d : A) (e : (A ⧸ Ideal.span {d}) ≃ₗ[A] M) :
    Module.Projective (A ⧸ Ideal.span {d}) ((A ⧸ Ideal.span {d}) ⊗[A] M) := by
  refine Module.Projective.of_equiv ((LinearEquiv.ofBijective (LinearMap.toSpanSingleton (A ⧸ Ideal.span {d})
    ((A ⧸ Ideal.span {d}) ⊗[A] (A ⧸ Ideal.span {d})) (1 ⊗ₜ 1)) ⟨fun r s h => ?_, fun t => ?_⟩).trans
      (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl _ _) e))
  · simpa [TensorProduct.smul_tmul'] using congrArg (Algebra.TensorProduct.lmul' A) h
  · induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | add s t hs ht => exact hs.elim fun a ha => ht.elim fun b hb => ⟨a + b, by rw [map_add, ha, hb]⟩
    | tmul b x =>
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
      refine ⟨s • b, ?_⟩
      rw [LinearMap.toSpanSingleton_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one, TensorProduct.smul_tmul,
        Algebra.smul_def, mul_one]
      rfl

theorem exists_rChain [IsDomain A] (p : ℕ) [Fact p.Prime] (o : ℕ) (ϖ : A) (h0 : ϖ ≠ 0)
    (hu : Associated (ϖ ^ (p ^ (o + 1) * (p - 1))) (p : A)) :
    ∃ C : RChain p A 1 o (ϖ ^ p ^ (o + 1)) (fun n => ϖ ^ (p ^ (o - n) * (p - 1))) A PUnit,
      ∀ n, C.L n = line (ϖ ^ (p ^ (o + 1) - p ^ (o + 1 - n))) := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hn : ∀ k, ϖ ^ k ≠ 0 := fun k => pow_ne_zero _ h0
  have hle : ∀ n, p ^ (o + 1 - n) ≤ p ^ (o + 1) := fun n => Nat.pow_le_pow_right (by omega) (by omega)
  have ln : ∀ {a b : ℕ}, a ≤ b → line (ϖ ^ b) ≤ line (ϖ ^ a) := fun h x hx =>
    (mem_line _ _).2 ((pow_dvd_pow ϖ h).trans ((mem_line _ _).1 hx))
  have sm : ∀ {a b c : ℕ}, c ≤ a + b → ϖ ^ a • line (ϖ ^ b) ≤ line (ϖ ^ c) := fun h x hx => by
    obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
    exact (mem_line _ _).2 ((pow_dvd_pow ϖ h).trans (by
      rw [pow_add]; exact mul_dvd_mul_left _ ((mem_line _ _).1 hy)))
  have st : ∀ n < o, p ^ (o + 1 - n) = p ^ (o - n) * (p - 1) + p ^ (o + 1 - (n + 1)) := fun n h => by
    rw [show o + 1 - (n + 1) = o - n by omega, show o + 1 - n = o - n + 1 by omega, pow_succ]
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    simp [mul_add]
  have eQ : ∀ n, (A ⧸ Ideal.span {ϖ ^ p ^ (o + 1 - n)}) ≃ₗ[A]
      Qt (line (ϖ ^ (p ^ (o + 1) - p ^ (o + 1 - n)))) (baseOf (ϖ ^ p ^ (o + 1)) 1) := fun n =>
    qtEquiv (hn _) _ _ (by rw [← pow_add, Nat.sub_add_cancel (hle n)])
  have eL : ∀ n < o, (A ⧸ Ideal.span {ϖ ^ (p ^ (o - n) * (p - 1))}) ≃ₗ[A]
      Qt (line (ϖ ^ (p ^ (o + 1) - p ^ (o + 1 - n)))) (line (ϖ ^ (p ^ (o + 1) - p ^ (o + 1 - (n + 1))))) := fun n h =>
    qtEquiv (hn _) _ _ (by
      rw [← pow_add]; congr 1; have := st n h; have := hle n; omega)
  have eP : (A ⧸ Ideal.span {(p : A)}) ≃ₗ[A] A ⧸ (p : A) • (⊤ : Submodule A A) := Submodule.quotEquivOfEq _ _ (by
    ext x
    rw [Submodule.mem_smul_pointwise_iff_exists, Ideal.mem_span_singleton]
    exact ⟨fun ⟨c, h⟩ => ⟨c, trivial, h.symm⟩, fun ⟨c, _, h⟩ => ⟨c, h.symm⟩⟩)
  have hψ : ∀ n, ∃ ψ : Qt (line (ϖ ^ (p ^ (o + 1) - p ^ (o + 1 - (n + 1))))) (baseOf (ϖ ^ p ^ (o + 1)) 1) →+
      Qt (line (ϖ ^ (p ^ (o + 1) - p ^ (o + 1 - n)))) (baseOf (ϖ ^ p ^ (o + 1)) 1), n < o → IsFrobLin A p p ψ := fun n => by
    by_cases h : n < o
    · refine (exists_isFrobLin p p _ _ (Associated.of_eq ?_) (eQ (n + 1)).symm (eQ n)
        ((pow_dvd_pow ϖ ((hle n).trans (Nat.le_mul_of_pos_right _ (by omega)))).trans hu.dvd)).imp fun _ k _ => k
      rw [← pow_mul, ← pow_succ]; congr 2; omega
    · exact ⟨0, fun h' => absurd h' h⟩
  have hκ : ∀ n, ∃ κ : Qt (line (ϖ ^ (p ^ (o + 1) - p ^ (o + 1 - n)))) (line (ϖ ^ (p ^ (o + 1) - p ^ (o + 1 - (n + 1))))) →+
      A ⧸ (p : A) • (⊤ : Submodule A A), n < o → IsFrobLin A p (p ^ (n + 1)) κ := fun n => by
    by_cases h : n < o
    · refine (exists_isFrobLin p _ _ _ ?_ (eL n h).symm eP dvd_rfl).imp fun _ k _ => k
      rw [← pow_mul, mul_right_comm, ← pow_add, show o - n + (n + 1) = o + 1 by omega]
      exact hu
    · exact ⟨0, fun h' => absurd h' h⟩
  choose ψ hψ using hψ
  choose κ hκ using hκ
  let j : A →ₗ[A] Qt (line (ϖ ^ (p ^ (o + 1) - p ^ (o + 1 - 0)))) (baseOf (ϖ ^ p ^ (o + 1)) 1) :=
    (eQ 0).toLinearMap ∘ₗ Submodule.mkQ _
  have hj : LinearMap.range j = ⊤ := LinearMap.range_eq_top.2 ((eQ 0).surjective.comp (Submodule.mkQ_surjective _))
  refine ⟨{
      L := fun n => line (ϖ ^ (p ^ (o + 1) - p ^ (o + 1 - n)))
      finite := fun n => Module.Finite.equiv (lineEquiv (hn _))
      projective := fun n => Module.Projective.of_equiv (lineEquiv (hn _))
      base_le := fun n => ln (Nat.sub_le _ _)
      succ_le := fun n => ln (Nat.sub_le_sub_left (Nat.pow_le_pow_right (by omega) (by omega)) _)
      kill := fun n h => sm ?_
      gam := fun n h => sm ?_
      lfree := fun n h => projective_tensor _ (eL n h)
      j := j
      ρ := 0
      ρ_surj := fun x => ⟨0, by
        haveI := Submodule.Quotient.subsingleton_iff.2 hj
        exact Subsingleton.elim _ _⟩
      ψ := ψ, ψ_lin := hψ, κ := κ, κ_lin := hκ }, fun _ => rfl⟩
  · have h1 : p ^ (o + 1 - (n + 1)) ≤ p ^ (o - 0) * (p - 1) :=
      (Nat.pow_le_pow_right (by omega) (by omega)).trans (Nat.le_mul_of_pos_right _ (by omega))
    omega
  · have := st n h; have := hle n; omega

theorem exists_ring_rChain (p : ℕ) [Fact p.Prime] (o : ℕ) : ∃ (A : Type) (_ : CommRing A) (π : A) (γ : ℕ → A)
    (C : RChain p A 1 o π γ A PUnit), (∀ n < o, C.L (n + 1) ≠ C.L n) ∧ C.L o ≠ baseOf π 1 := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hpos : 0 < p ^ (o + 1) * (p - 1) := Nat.mul_pos (pow_pos (by omega) _) (by omega)
  obtain ⟨O, _, _, _, _, _, ϖ, h⟩ := GlobalTheory.RootDVR.exists_dvr_pow_eq_prime p (p ^ (o + 1) * (p - 1)) hpos
  have h0 : ϖ ≠ 0 := by
    rintro rfl
    rw [zero_pow hpos.ne', eq_comm] at h
    exact GlobalTheory.Vert.natCast_ne_zero O p h
  have hnu : ¬ IsUnit ϖ := fun k => (IsLocalRing.mem_maximalIdeal _).1 (GlobalTheory.Vert.natCast_mem_maximalIdeal O p) (h ▸ k.pow _)
  obtain ⟨C, hC⟩ := exists_rChain p o ϖ h0 (Associated.of_eq h)
  have key : ∀ a b : ℕ, line (ϖ ^ a) = line (ϖ ^ b) → a ≤ b := fun a b e =>
    (pow_dvd_pow_iff h0 hnu).1 ((mem_line _ _).1 (e ▸ (mem_line (ϖ ^ b) fun _ => ϖ ^ b).2 dvd_rfl))
  have hle : ∀ n, p ^ (o + 1 - n) ≤ p ^ (o + 1) := fun n => Nat.pow_le_pow_right (by omega) (by omega)
  refine ⟨O, _, _, _, C, fun n hn e => ?_, fun e => ?_⟩
  · rw [hC, hC] at e
    have h1 := key _ _ e
    have h2 : p ^ (o + 1 - (n + 1)) < p ^ (o + 1 - n) := Nat.pow_lt_pow_right (by omega) (by omega)
    have := hle n
    omega
  · rw [hC] at e
    have h1 := key _ _ e.symm
    have h2 : 0 < p ^ (o + 1 - o) := pow_pos (by omega) _
    have := hle o
    omega

end Examples₂

section Group

variable {p : ℕ} [Fact p.Prime] (D : PrismData p) {S : CycPerfd p} {G : PDivGroup p S.R} (c : ConstTate (eps S) G)
  {A : Type} [CommRing A] [Algebra A S.R] {h o : ℕ} (e : G.height = h) {π : A} {γ : ℕ → A} {Lie Om : Type}
  [AddCommGroup Lie] [Module A Lie] [AddCommGroup Om] [Module A Om]

def toR (x : Fin h → A) : Fin G.height → S.R := fun i => algebraMap A S.R (x (Fin.cast e i))

structure IsOf (iL : Lie → G.Lie) (iO : Om → G.dual.omega) (C : RChain p A h o π γ Lie Om) : Prop where
  pi_eq : algebraMap A S.R π = zeta S.ε 1 - 1
  mem : ∀ n x, x ∈ C.L n ↔ toR e x ∈ H D c n
  j : ∀ (y : Lie) (x : C.L 0), C.j y = Submodule.Quotient.mk x ↔ toR e x.1 - c.alDual (iL y) ∈ base S G.height
  ρ : ∀ (w : Om) (x : C.L 0), C.ρ w = Submodule.Quotient.mk (Submodule.Quotient.mk x) ↔
    ∃ x₀ ∈ H D c 0, (zeta S.ε 1 - 1) • iO w = c.al x₀ ∧ toR e x.1 - x₀ ∈ base S G.height ⊔ LinearMap.range c.alDual
  ψ : ∀ n < o, ∀ (x : C.L (n + 1)) (y : C.L n), C.ψ n (Submodule.Quotient.mk x) = Submodule.Quotient.mk y ↔
    ∃ k ∈ K D c (n + 2), (zeta S.ε 1 - 1) • piMap (fontaineTheta S.R p) _ k = (zeta S.ε (n + 2) - 1) • toR e x.1 ∧
      ∃ y₀, (zeta S.ε 1 - 1) • piMap (fontaineTheta S.R p) _ (piMap frobenius _ k) = (zeta S.ε (n + 1) - 1) • y₀ ∧
        toR e y.1 - y₀ ∈ base S G.height
  κ : ∀ n < o, ∀ (x : C.L n) (y : Lie), C.κ n (Submodule.Quotient.mk x) = Submodule.Quotient.mk y ↔
    ∃ m : D.Cov G, (zeta S.ε 1 - 1) • piMap (fontaineTheta S.R p) _ (fun j => (phiInv p S.R)^[n + 1] (coord D c m j)) =
      (zeta S.ε (n + 1) - 1) • toR e x.1 ∧ ∃ y₀ : G.Lie, c.alDual y₀ = b D c m ∧
        iL y - y₀ ∈ (p : S.R) • (⊤ : Submodule S.R G.Lie)

end Group

def ExistsSt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : PrismData p) (S : CycPerfd p) (G : PDivGroup p S.R) (c : ConstTate (eps S) G)
    (A : Type) [CommRing A] [IsDomain A] [CharZero A] [Algebra A S.R]
    (ec : AdicCompletion (Ideal.span {(p : A)}) A ≃+* S.R), (∀ a, ec (algebraMap A _ a) = algebraMap A S.R a) →
    ∀ (h o : ℕ) (e : G.height = h) (π : A) (γ : ℕ → A), π ∣ (p : A) → (∀ n ≤ o, γ n ∣ (p : A)) →
      algebraMap A S.R π = zeta S.ε 1 - 1 → (∀ n ≤ o, algebraMap A S.R (γ n) = fontaineTheta S.R p (xiN S (n + 1))) →
      ∀ (Lie Om : Type) [AddCommGroup Lie] [Module A Lie] [AddCommGroup Om] [Module A Om] [Module.Finite A Lie]
        [Module.Projective A Lie] [Module.Finite A Om] [Module.Projective A Om]
        (eL : S.R ⊗[A] Lie ≃ₗ[S.R] G.Lie) (eO : S.R ⊗[A] Om ≃ₗ[S.R] G.dual.omega),
        ∃ C : RChain p A h o π γ Lie Om, IsOf D c e (fun y => eL (1 ⊗ₜ y)) (fun w => eO (1 ⊗ₜ w)) C

def MapSt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : PrismData p) (S S' : CycPerfd p) [Algebra S.R S'.R] (G : PDivGroup p S.R)
    (G' : PDivGroup p S'.R) (c : ConstTate (eps S) G) (c' : ConstTate (eps S') G') (A A' : Type) [CommRing A] [CommRing A']
    [Algebra A S.R] [Algebra A' S'.R] (φ : A →+* A') (h o : ℕ) (e : G.height = h) (e' : G'.height = h) (π : A) (π' : A')
    (γ : ℕ → A) (γ' : ℕ → A') (Lie Om Lie' Om' : Type) [AddCommGroup Lie] [Module A Lie] [AddCommGroup Om] [Module A Om]
    [AddCommGroup Lie'] [Module A' Lie'] [AddCommGroup Om'] [Module A' Om'] (iL : Lie → G.Lie) (iO : Om → G.dual.omega)
    (iL' : Lie' → G'.Lie) (iO' : Om' → G'.dual.omega) (C : RChain p A h o π γ Lie Om) (C' : RChain p A' h o π' γ' Lie' Om')
    (f : G.baseChange S'.R ⟶ G') (M : Matrix (Fin h) (Fin h) ℤ) (l : Lie → Lie') (m : Om → Om'),
    IsOf D c e iL iO C → IsOf D c' e' iL' iO' C' →
    (∀ a, algebraMap S.R S'.R (algebraMap A S.R a) = algebraMap A' S'.R (φ a)) →
    (∀ n, zeta S'.ε n = algebraMap S.R S'.R (zeta S.ε n)) →
    (∀ j : Fin h, tateMap _ _ S'.R (dualHom _ G' f) (c'.t' (Fin.cast e'.symm j)) =
      ∑ i : Fin h, M j i • bcChar S'.R (c.t' (Fin.cast e.symm i))) →
    (∀ (y : Lie) (j : Fin h), c'.alDual (iL' (l y)) (Fin.cast e'.symm j) =
      mv (algebraMap S.R S'.R) M (fun i => c.alDual (iL y) (Fin.cast e.symm i)) j) →
    (∀ (w : Om) (x : Fin G.height → S.R), (zeta S.ε 1 - 1) • iO w = c.al x → (zeta S'.ε 1 - 1) • iO' (m w) =
      c'.al fun j => mv (algebraMap S.R S'.R) M (fun i => x (Fin.cast e.symm i)) (Fin.cast e' j)) →
    C.Map C' φ M l m ∧ (IsIso f → M = 1 → φ π = π' → ModIso S.R π → ModIso S'.R π' →
      ∀ n, C'.L n = Submodule.span A' (piMap φ (Fin h) '' (C.L n : Set (Fin h → A))))

end GlobalTheory.RingChain

end
