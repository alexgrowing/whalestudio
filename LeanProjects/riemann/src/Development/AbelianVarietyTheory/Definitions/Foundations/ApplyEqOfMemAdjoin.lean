import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EeProd

noncomputable section

open scoped MatrixGroups

namespace GlobalTheory.Glue

open GlobalTheory.KZ GlobalTheory.K5

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def zt (ε : Ω →+* ℂ) (l n : ℕ) : Ω := eOm ε (1 / (l : ℚ) ^ n)

def Stab (A : ValuationSubring Ω) (s : Ω ≃ₐ[ℚ] Ω) : Prop := ∀ x, s x ∈ A ↔ x ∈ A

def InZl (ε : Ω →+* ℂ) (l n : ℕ) (F : Ω) : Prop := ∃ D : ℕ, ¬ l ∣ D ∧ (D : Ω) * F ∈ Subring.closure {zt ε l n}

open Classical in

def IsNT (ε : Ω →+* ℂ) (l n m : ℕ) [NeZero l] (F F' : Ω) : Prop :=
  ∃ τ : (ZMod (l ^ n))ˣ → (Ω ≃ₐ[ℚ] Ω), (∀ a, τ a (zt ε l n) = zt ε l n ^ (a : ZMod (l ^ n)).val) ∧
    (l : Ω) ^ (n - m) * F' = ∑ a ∈ Finset.univ.filter (fun a : (ZMod (l ^ n))ˣ => (a : ZMod (l ^ n)).val ≡ 1 [MOD l ^ m]), τ a F

def KT (X : GlobalTheory.KZ.Tower Ω ε) (L : ℕ) : Subfield X.K :=
  RingHom.eqLocusField (X.sl (ofSL (ModularGroup.T ^ L))).toRingEquiv.toRingHom (RingHom.id X.K)

variable {p : ℕ} [Fact p.Prime] {Ωl : Type} [Field Ωl] [Algebra (O0 p) Ωl]

structure IsCusp (ε : Ω →+* ℂ) (A : ValuationSubring Ω) (T : GlobalTheory.K5.Tower p Ωl) (j : Ω →+* Ωl) : Prop where
  int : ∀ x, x ∈ A ↔ IsInt p (j x)
  alg : ∀ x, IsAlgZp p (j x)
  root : ∀ n, j (zt ε p n) = T.ζ n
  dense : ∀ (k : ℕ) (e : Ωl), IsInt p e → IsAlgZp p e → ∃ a ∈ A, Cong p k e (j a)
  down : ∀ g : Gal p Ωl, ∃ s : Ω ≃ₐ[ℚ] Ω, Stab A s ∧ ∀ x, g (j x) = j (s x)
  up : ∀ (n : ℕ) (s : Ω ≃ₐ[ℚ] Ω), Stab A s → ∃ g : Gal p Ωl, g (T.qq n) = T.qq n ∧ ∀ x, g (j x) = j (s x)

structure IsIo (X : GlobalTheory.KZ.Tower Ω ε) (A : ValuationSubring Ω) (T : GlobalTheory.K5.Tower p Ωl) (j : Ω →+* Ωl) (n : ℕ)
    (ψ : O0 p →+* Ωl) (io : KT X (p ^ n) →+* Ωl) : Prop where
  ev : ∀ (y : KT X (p ^ n)) (S : Finset Ω),
    (∀ r, (X.exp y).coeff r ∈ A ∧ (X.exp y).coeff r ∈ IntermediateField.adjoin ℚ (S : Set Ω)) →
    ∃ x', Ev ψ (fun r : ℤ => j ((X.exp y).coeff ((r : ℚ) / (p : ℚ) ^ n))) (io y) x'
  gal : ∀ (g : Gal p Ωl) (s : Ω ≃ₐ[ℚ] Ω), g (T.qq n) = T.qq n → (∀ x, g (j x) = j (s x)) →
    ∀ y y' : KT X (p ^ n), (y' : X.K) = X.gal s y → g (io y) = io y'

def IsNTr (ε : Ω →+* ℂ) (l n m : ℕ) [NeZero l] (F F' : Ω) : Prop :=
  1 ≤ m ∧ m ≤ n ∧ F ∈ IntermediateField.adjoin ℚ {zt ε l n} ∧ IsNT ε l n m F F'

theorem InZl.mem_adjoin {l n : ℕ} {F : Ω} (h : InZl ε l n F) : F ∈ IntermediateField.adjoin ℚ {zt ε l n} := by
  haveI : CharZero Ω := algebraRat.charZero Ω
  obtain ⟨D, hD, hF⟩ := h
  have hD0 : (D : Ω) ≠ 0 := by
    rintro h0
    exact hD (by rw [Nat.cast_eq_zero.1 h0]; exact dvd_zero _)
  have h1 : (D : Ω) * F ∈ IntermediateField.adjoin ℚ {zt ε l n} :=
    (Subring.closure_le (t := (IntermediateField.adjoin ℚ {zt ε l n}).toSubring)).2
      (IntermediateField.subset_adjoin ℚ _) hF
  have h2 := mul_mem (inv_mem (natCast_mem (IntermediateField.adjoin ℚ {zt ε l n}) D)) h1
  rwa [inv_mul_cancel_left₀ hD0] at h2

theorem IsNTr.iff_isNT {l n m : ℕ} [NeZero l] {F F' : Ω} (hm : 1 ≤ m) (hmn : m ≤ n) (hF : InZl ε l n F) :
    IsNTr ε l n m F F' ↔ IsNT ε l n m F F' :=
  ⟨fun h => h.2.2.2, fun h => ⟨hm, hmn, hF.mem_adjoin, h⟩⟩

theorem IsNTr.apply_eq_of_mem_adjoin {z F : Ω} (hF : F ∈ IntermediateField.adjoin ℚ {z}) {s t : Ω ≃ₐ[ℚ] Ω} (h : s z = t z) :
    s F = t F := by
  induction hF using IntermediateField.adjoin_induction with
  | mem x hx => rw [Set.mem_singleton_iff.1 hx, h]
  | algebraMap r => rw [AlgEquiv.commutes, AlgEquiv.commutes]
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
  | inv x _ hx => rw [map_inv₀, map_inv₀, hx]
  | mul x y _ _ hx hy => rw [map_mul, map_mul, hx, hy]

theorem IsNTr.unique {l n m : ℕ} [NeZero l] {F F' F'' : Ω} (h : IsNTr ε l n m F F') (h' : IsNTr ε l n m F F'') : F' = F'' := by
  haveI : CharZero Ω := algebraRat.charZero Ω
  obtain ⟨-, -, hF, τ, hτ, e⟩ := h
  obtain ⟨-, -, -, τ', hτ', e'⟩ := h'
  refine mul_left_cancel₀ (pow_ne_zero (n - m) (Nat.cast_ne_zero.2 (NeZero.ne l))) (e.trans (Eq.trans ?_ e'.symm))
  exact Finset.sum_congr rfl fun a _ => IsNTr.apply_eq_of_mem_adjoin hF ((hτ a).trans (hτ' a).symm)

theorem IsNTr.add {l n m : ℕ} [NeZero l] {F F' G G' : Ω} (h : IsNTr ε l n m F F') (h' : IsNTr ε l n m G G') :
    IsNTr ε l n m (F + G) (F' + G') := by
  obtain ⟨h1, h2, hF, τ, hτ, e⟩ := h
  obtain ⟨-, -, hG, τ', hτ', e'⟩ := h'
  refine ⟨h1, h2, add_mem hF hG, τ, hτ, ?_⟩
  rw [mul_add, e, e', ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => by
    rw [map_add, IsNTr.apply_eq_of_mem_adjoin hG ((hτ a).trans (hτ' a).symm)]

example (l : ℕ) [NeZero l] (F F' : Ω) : ¬ IsNTr ε l 0 1 F F' ∧ ¬ IsNTr ε l 0 0 F F' ∧ ¬ IsNTr ε l 3 0 F F' :=
  ⟨fun h => by have := h.2.1; omega, fun h => by have := h.1; omega, fun h => by have := h.1; omega⟩

theorem KT.mem_def (X : GlobalTheory.KZ.Tower Ω ε) (L : ℕ) (f : X.K) : f ∈ KT X L ↔ X.sl (ofSL (ModularGroup.T ^ L)) f = f := Iff.rfl

example (X : GlobalTheory.KZ.Tower Ω ε) (L : ℕ) (c : Ω) : X.jK ∈ KT X L ∧ algebraMap Ω X.K c ∈ KT X L :=
  ⟨X.j_inv _, (X.sl _).commutes c⟩

structure IsPlaceIn (ε : Ω →+* ℂ) (A : ValuationSubring Ω) (T : GlobalTheory.K5.Tower p Ωl) (j : Ω →+* Ωl) : Prop where
  int : ∀ x, x ∈ A ↔ IsInt p (j x)
  alg : ∀ x, IsAlgZp p (j x)
  root : ∀ n, j (zt ε p n) = T.ζ n

theorem IsCusp.isPlaceIn {A : ValuationSubring Ω} {T : GlobalTheory.K5.Tower p Ωl} {j : Ω →+* Ωl} (h : IsCusp ε A T j) :
    IsPlaceIn ε A T j := ⟨h.int, h.alg, h.root⟩

theorem IsPlaceIn.unique {A A' : ValuationSubring Ω} {T T' : GlobalTheory.K5.Tower p Ωl} {j : Ω →+* Ωl} (h : IsPlaceIn ε A T j)
    (h' : IsPlaceIn ε A' T' j) : A = A' :=
  ValuationSubring.ext _ _ fun x => (h.int x).trans (h'.int x).symm

theorem IsPlaceIn.mem_nonunits (hc : IsClo p Ωl) {A : ValuationSubring Ω} {T : GlobalTheory.K5.Tower p Ωl} {j : Ω →+* Ωl}
    (h : IsPlaceIn ε A T j) : ((p : ℕ) : Ω) ∈ A.nonunits := by
  haveI := Basic.charZero_of_isClo hc
  rw [ValuationSubring.mem_nonunits_iff_or]
  refine Or.inr fun hA => Basic.not_cong_one_zero hc 1 one_ne_zero ⟨_, (h.int _).1 hA, ?_⟩
  have hp0 : (p : Ωl) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  rw [map_inv₀, map_natCast, pow_one, mul_inv_cancel₀ hp0, sub_zero]

theorem IsPlaceIn.stab {A : ValuationSubring Ω} {T : GlobalTheory.K5.Tower p Ωl} {j : Ω →+* Ωl} (h : IsPlaceIn ε A T j)
    {g : Gal p Ωl} {s : Ω ≃ₐ[ℚ] Ω} (hs : ∀ x, g (j x) = j (s x)) : Stab A s := fun x => by
  rw [h.int, h.int, ← hs]
  exact ⟨fun hx => by simpa using Basic.isInt_gal g.symm hx, Basic.isInt_gal g⟩

structure IsExpIn (X : GlobalTheory.KZ.Tower Ω ε) (A : ValuationSubring Ω) (T : GlobalTheory.K5.Tower p Ωl) (j : Ω →+* Ωl) (n : ℕ)
    (ψ : O0 p →+* Ωl) (io : KT X (p ^ n) →+* Ωl) : Prop where
  place : IsPlaceIn ε A T j
  rebase₂ : IsReb T n ψ
  ev : ∀ (y : KT X (p ^ n)) (S : Finset Ω),
    (∀ r, (X.exp y).coeff r ∈ A ∧ (X.exp y).coeff r ∈ IntermediateField.adjoin ℚ (S : Set Ω)) →
    ∃ x', Ev ψ (fun r : ℤ => j ((X.exp y).coeff ((r : ℚ) / (p : ℚ) ^ n))) (io y) x'

def GalTr (X : GlobalTheory.KZ.Tower Ω ε) (T : GlobalTheory.K5.Tower p Ωl) (j : Ω →+* Ωl) (n : ℕ) (io : KT X (p ^ n) →+* Ωl) : Prop :=
  ∀ (g : Gal p Ωl) (s : Ω ≃ₐ[ℚ] Ω) (b : ℕ), g (T.qq n) = T.ζ n ^ b * T.qq n → (∀ x, g (j x) = j (s x)) →
    ∀ y y' : KT X (p ^ n), (y' : X.K) = X.sl (ofSL (ModularGroup.T ^ b)) (X.gal s y) → g (io y) = io y'

section

variable {X : GlobalTheory.KZ.Tower Ω ε} {A : ValuationSubring Ω} {T : GlobalTheory.K5.Tower p Ωl} {j : Ω →+* Ωl} {n : ℕ} {ψ : O0 p →+* Ωl}
  {io : KT X (p ^ n) →+* Ωl}

theorem IsIo.isExpIn (h : IsIo X A T j n ψ io) (hj : IsPlaceIn ε A T j) (hψ : IsReb T n ψ) : IsExpIn X A T j n ψ io :=
  ⟨hj, hψ, h.ev⟩

theorem IsExpIn.isIo (h : IsExpIn X A T j n ψ io) (hg : GalTr X T j n io) : IsIo X A T j n ψ io :=
  ⟨h.ev, fun g s hq hs y y' hy => hg g s 0 (by rw [pow_zero, one_mul, hq]) hs y y' (by rw [pow_zero, map_one, X.sl_one, hy])⟩

theorem IsExpIn.par (h : IsExpIn X A T j n ψ io) : ψ (qO p) = T.qq n := h.rebase₂.par

theorem GalTr.coeff_sl_gal (X : GlobalTheory.KZ.Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) (b : ℕ) (y : X.K) (r : ℚ) :
    (X.exp (X.sl (ofSL (ModularGroup.T ^ b)) (X.gal s y))).coeff r = eOm ε (r * b) * s ((X.exp y).coeff r) := by
  have he : ∀ i k, ent (ofSL (ModularGroup.T ^ b)) i k = ((!![1, (b : ℤ); 0, 1] i k : ℤ) : ℚ) := fun i k => by
    rw [← ModularGroup.coe_T_zpow, zpow_natCast]; rfl
  have h := X.exp_upper (ofSL (ModularGroup.T ^ b)) (by rw [he]; simp) (X.gal s y) r
  rw [he, he, he, X.gal_exp] at h
  simpa using h

end

end GlobalTheory.Glue
