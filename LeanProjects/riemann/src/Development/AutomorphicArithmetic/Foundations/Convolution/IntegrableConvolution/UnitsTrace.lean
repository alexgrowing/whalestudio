import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TrDefs

noncomputable section

namespace UpperTheory.ConvolutionTheory.L1

section Units

variable {W : Type} [AddCommGroup W] [Module ℂ W] {m d : ℕ}

private abbrev Mt (d : ℕ) := Matrix (Fin d) (Fin d) ℂ

private abbrev uu {d : ℕ} (p q : Fin d) : Mt d := Matrix.single p q 1

private theorem uu_same (a b c : Fin d) : uu a b * uu b c = uu a c := by
  simp [uu, Matrix.single_mul_single_same]

private theorem uu_ne {a b b' c : Fin d} (h : b ≠ b') : uu a b * uu b' c = 0 := by
  simp [uu, Matrix.single_mul_single_of_ne _ _ _ _ h]

private theorem uu_sum : ∑ a : Fin d, uu a a = 1 := by
  ext i j
  by_cases h : i = j
  · subst h; simp [uu, Matrix.single_apply, Matrix.sum_apply]
  · simp [uu, Matrix.single_apply, Matrix.sum_apply, h, Matrix.one_apply]

private theorem uu_sandwich (a : Fin d) (b : Mt d) : uu a a * b * uu a a = b a a • uu a a := by
  ext i j
  simp only [uu, Matrix.single_apply, Matrix.mul_apply, Matrix.smul_apply]
  rcases eq_or_ne a i with rfl | h1 <;> rcases eq_or_ne a j with rfl | h2 <;> simp [*]

private def RR (r : Fin (m + 1) → (Mt d →ₐ[ℂ] Module.End ℂ W))
    (hc : ∀ i j, i ≠ j → ∀ a b, Commute (r i a) (r j b)) :
    (Fin (m + 1) → Mt d) →* Module.End ℂ W :=
  MonoidHom.noncommPiCoprod (fun i => MonoidHomClass.toMonoidHom (r i))
    (show Pairwise (fun i j => ∀ x y, Commute (MonoidHomClass.toMonoidHom (r i) x)
      (MonoidHomClass.toMonoidHom (r j) y)) from fun i j h x y => hc i j h x y)

variable (r : Fin (m + 1) → (Mt d →ₐ[ℂ] Module.End ℂ W))
    (hc : ∀ i j, i ≠ j → ∀ a b, Commute (r i a) (r j b))

private theorem RR_single (i : Fin (m + 1)) (x : Mt d) : RR r hc (Pi.mulSingle i x) = r i x := by
  exact (MonoidHom.noncommPiCoprod_mulSingle (N := fun _ => Mt d)
    (fun i => MonoidHomClass.toMonoidHom (r i)) i x).trans rfl

private theorem RR_update (a : Fin (m + 1) → Mt d) (i : Fin (m + 1)) (x : Mt d) :
    RR r hc (Function.update a i x) = r i x * RR r hc (Function.update a i 1) := by
  rw [← RR_single r hc i x, ← map_mul]
  congr 1
  funext j
  by_cases h : j = i
  · subst h; simp
  · simp [h]

private theorem RR_mem (Q : Submonoid (Module.End ℂ W)) (a : Fin (m + 1) → Mt d)
    (h : ∀ i, r i (a i) ∈ Q) : RR r hc a ∈ Q := by
  unfold RR
  simp only [MonoidHom.noncommPiCoprod, MonoidHom.coe_mk, OneHom.coe_mk]
  exact Submonoid.noncommProd_mem _ _ _ _ (fun i _ => h i)

private def RM : MultilinearMap ℂ (fun _ : Fin (m + 1) => Mt d) (Module.End ℂ W) where
  toFun := RR r hc
  map_update_add' := by
    intro inst a i x y
    obtain rfl : inst = instDecidableEqFin (m + 1) := Subsingleton.elim _ _
    rw [RR_update r hc a i (x + y), RR_update r hc a i x, RR_update r hc a i y, map_add, add_mul]
  map_update_smul' := by
    intro inst a i c x
    obtain rfl : inst = instDecidableEqFin (m + 1) := Subsingleton.elim _ _
    rw [RR_update r hc a i (c • x), RR_update r hc a i x, map_smul, smul_mul_assoc]

private theorem RM_apply (a : Fin (m + 1) → Mt d) : RM r hc a = RR r hc a := rfl

private theorem RR_shift (Ue : Module.End ℂ W)
    (hU : ∀ i a, Ue * r (i + 1) a = r i a * Ue) (a : Fin (m + 1) → Mt d) :
    Ue * RR r hc a = RR r hc (fun i => a (i + 1)) * Ue := by
  have key : ∀ s : Finset (Fin (m + 1)),
      Ue * RR r hc (fun i => if i ∈ s then a i else 1) =
        RR r hc (fun i => if i + 1 ∈ s then a (i + 1) else 1) * Ue := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have h1 : (fun i : Fin (m + 1) => if i ∈ (∅ : Finset (Fin (m + 1))) then a i else 1) = 1 := by
        funext i; simp
      have h2 : (fun i : Fin (m + 1) => if i + 1 ∈ (∅ : Finset (Fin (m + 1))) then a (i + 1) else 1) = 1 := by
        funext i; simp
      rw [h1, h2]; simp
    | insert i s hi ih =>
      have h1 : (fun j => if j ∈ insert i s then a j else 1) =
          Pi.mulSingle i (a i) * fun j => if j ∈ s then a j else 1 := by
        funext j
        by_cases h : j = i
        · subst h; simp [hi]
        · simp [h, Finset.mem_insert]
      have h2 : (fun j => if j + 1 ∈ insert i s then a (j + 1) else 1) =
          Pi.mulSingle (i - 1) (a i) * fun j => if j + 1 ∈ s then a (j + 1) else 1 := by
        funext j
        by_cases h : j = i - 1
        · subst h; simp [hi]
        · have h' : j + 1 ≠ i := fun e => h (eq_sub_of_add_eq e)
          simp [h, h', Finset.mem_insert]
      have h3 := hU (i - 1) (a i)
      rw [sub_add_cancel] at h3
      rw [h1, h2, map_mul, map_mul, RR_single, RR_single, ← mul_assoc, h3, mul_assoc, ih, mul_assoc]
  simpa using key Finset.univ

private def FF (p : Fin (m + 1) → Fin d) : Module.End ℂ W := RR r hc (fun i => uu (p i) (p i))

private theorem FF_sum : ∑ p : Fin (m + 1) → Fin d, FF r hc p = 1 := by
  have h := (RM r hc).map_sum (fun (_ : Fin (m + 1)) (a : Fin d) => uu a a)
  simp only [uu_sum, RM_apply] at h
  have h1 : (fun _ : Fin (m + 1) => (1 : Mt d)) = 1 := rfl
  rw [h1, map_one] at h
  exact h.symm

private theorem FF_idem (p : Fin (m + 1) → Fin d) : FF r hc p * FF r hc p = FF r hc p := by
  unfold FF
  rw [← map_mul]
  congr 1
  funext i
  simp [uu_same]

private theorem FF_right (p : Fin (m + 1) → Fin d) (j : Fin (m + 1)) :
    FF r hc p * r j (uu (p j) (p j)) = FF r hc p := by
  unfold FF
  rw [← RR_single r hc j, ← map_mul]
  congr 1
  funext i
  by_cases h : i = j
  · subst h; simp [uu_same]
  · simp [h]

private theorem FF_left (p : Fin (m + 1) → Fin d) (j : Fin (m + 1)) :
    r j (uu (p j) (p j)) * FF r hc p = FF r hc p := by
  unfold FF
  rw [← RR_single r hc j, ← map_mul]
  congr 1
  funext i
  by_cases h : i = j
  · subst h; simp [uu_same]
  · simp [h]

open Fin.NatCast Fin.CommRing in
private theorem const_of {α : Type} (i₀ : Fin (m + 1)) (p : Fin (m + 1) → α)
    (h : ∀ j, j ≠ i₀ → p j = p (j + 1)) (i : Fin (m + 1)) : p i = p i₀ := by
  have key : ∀ k : ℕ, k ≤ m → p (i₀ + 1 + (k : Fin (m + 1))) = p (i₀ + 1) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro hk
      have hne : i₀ + 1 + (k : Fin (m + 1)) ≠ i₀ := by
        intro e
        have h0 : ((k + 1 : ℕ) : Fin (m + 1)) = 0 := by
          have : i₀ + ((k + 1 : ℕ) : Fin (m + 1)) = i₀ + 0 := by
            push_cast
            rw [add_zero]
            calc i₀ + ((k : Fin (m + 1)) + 1) = i₀ + 1 + (k : Fin (m + 1)) := by ring
              _ = i₀ := e
          exact add_left_cancel this
        rw [Fin.natCast_eq_zero] at h0
        have := Nat.le_of_dvd (by omega) h0
        omega
      rw [← ih (by omega), h _ hne]
      congr 1
      push_cast
      ring
  have h1 := key ((i - i₀ - 1 : Fin (m + 1)).val) (by have := (i - i₀ - 1 : Fin (m + 1)).isLt; omega)
  have h2 := key m le_rfl
  have e1 : i₀ + 1 + (((i - i₀ - 1 : Fin (m + 1)).val : ℕ) : Fin (m + 1)) = i := by
    rw [Fin.cast_val_eq_self]
    ring
  have e2 : i₀ + 1 + (m : Fin (m + 1)) = i₀ := by
    have : ((m + 1 : ℕ) : Fin (m + 1)) = 0 := Fin.natCast_self _
    push_cast at this
    calc i₀ + 1 + (m : Fin (m + 1)) = i₀ + ((m : Fin (m + 1)) + 1) := by ring
      _ = i₀ := by rw [this, add_zero]
  rw [e1] at h1
  rw [e2] at h2
  rw [h1, h2]

private theorem tr_nonconst [FiniteDimensional ℂ W] (Ue : Module.End ℂ W)
    (hU : ∀ i a, Ue * r (i + 1) a = r i a * Ue) (S : Module.End ℂ W) (j : Fin (m + 1))
    (hS : ∀ a, Commute S (r j a)) (p : Fin (m + 1) → Fin d) (hne : p j ≠ p (j + 1)) :
    LinearMap.trace ℂ W (FF r hc p * (S * Ue)) = 0 := by
  set q : Fin (m + 1) → Fin d := fun i => p (i + 1) with hq
  have hUF : Ue * FF r hc p = FF r hc q * Ue := RR_shift r hc Ue hU _
  have hz : FF r hc p * S * FF r hc q = 0 := by
    have h1 : FF r hc p * S * FF r hc q =
        FF r hc p * (r j (uu (p j) (p j)) * S * r j (uu (q j) (q j))) * FF r hc q := by
      calc FF r hc p * S * FF r hc q
          = (FF r hc p * r j (uu (p j) (p j))) * S * (r j (uu (q j) (q j)) * FF r hc q) := by
            rw [FF_right, FF_left]
        _ = _ := by simp only [mul_assoc]
    have h2 : r j (uu (p j) (p j)) * S * r j (uu (q j) (q j)) = 0 := by
      rw [← (hS _).eq, mul_assoc, ← map_mul, uu_ne hne, map_zero, mul_zero]
    rw [h1, h2, mul_zero, zero_mul]
  calc LinearMap.trace ℂ W (FF r hc p * (S * Ue))
      = LinearMap.trace ℂ W (FF r hc p * (FF r hc p * (S * Ue))) := by
        rw [← mul_assoc (FF r hc p) (FF r hc p), FF_idem]
    _ = LinearMap.trace ℂ W (FF r hc p * (S * Ue) * FF r hc p) := by
        rw [LinearMap.trace_mul_comm]
    _ = LinearMap.trace ℂ W (FF r hc p * S * (Ue * FF r hc p)) := by
        simp only [mul_assoc]
    _ = 0 := by
        rw [hUF, ← mul_assoc, hz, zero_mul, map_zero]

private theorem tr_fib [FiniteDimensional ℂ W] (i₀ : Fin (m + 1)) (S : Module.End ℂ W)
    (hS : ∀ j, j ≠ i₀ → ∀ a, Commute S (r j a)) (p : Fin (m + 1) → Fin d) :
    LinearMap.trace ℂ W (FF r hc p * S) =
      LinearMap.trace ℂ W (FF r hc (fun _ => p i₀) * S) := by
  set X := RR r hc (fun j => if j = i₀ then 1 else uu (p i₀) (p j)) with hX
  set Y := RR r hc (fun j => if j = i₀ then 1 else uu (p j) (p i₀)) with hY
  have h1 : X * FF r hc p * Y = FF r hc (fun _ => p i₀) := by
    unfold FF
    rw [hX, hY, ← map_mul, ← map_mul]
    congr 1
    funext j
    by_cases h : j = i₀
    · subst h; simp
    · simp [h, uu_same]
  have h2 : FF r hc p * (Y * X) = FF r hc p := by
    unfold FF
    rw [hX, hY, ← map_mul, ← map_mul]
    congr 1
    funext j
    by_cases h : j = i₀
    · subst h; simp
    · simp only [Pi.mul_apply, h, if_false]
      rw [uu_same, uu_same]
  have h3 : Commute S X := by
    have : X ∈ Submonoid.centralizer ({S} : Set (Module.End ℂ W)) := by
      refine RR_mem r hc _ _ (fun j => ?_)
      rw [Submonoid.mem_centralizer_iff]
      rintro g rfl
      by_cases h : j = i₀
      · simp [h]
      · simpa [h] using (hS j h _).eq
    exact (Submonoid.mem_centralizer_iff.1 this S rfl)
  calc LinearMap.trace ℂ W (FF r hc p * S)
      = LinearMap.trace ℂ W (FF r hc p * (Y * X) * S) := by rw [h2]
    _ = LinearMap.trace ℂ W (FF r hc p * Y * S * X) := by
        rw [mul_assoc (FF r hc p * Y) S X, h3.eq]; simp only [mul_assoc]
    _ = LinearMap.trace ℂ W (X * (FF r hc p * Y * S)) := by rw [LinearMap.trace_mul_comm]
    _ = LinearMap.trace ℂ W (FF r hc (fun _ => p i₀) * S) := by
        rw [← h1]; simp only [mul_assoc]

private theorem sum_fib {β : Type} [AddCommMonoid β] (i₀ : Fin (m + 1)) (g : Fin d → β) :
    ∑ p : Fin (m + 1) → Fin d, g (p i₀) = (d ^ m) • ∑ a, g a := by
  rw [← Fintype.sum_equiv (Fin.insertNthEquiv (fun _ => Fin d) i₀) (fun x => g x.1)
    (fun p => g (p i₀)) (fun x => by simp)]
  rw [Fintype.sum_prod_type]
  simp [Finset.smul_sum]

private theorem FF_conj (p : Fin (m + 1) → Fin d) (o : Fin d) :
    FF r hc p = RR r hc (fun i => uu (p i) o) * FF r hc (fun _ => o) * RR r hc (fun i => uu o (p i)) := by
  unfold FF
  rw [← map_mul, ← map_mul]
  congr 1
  funext i
  simp [uu_same]

private theorem exists_scalar [FiniteDimensional ℂ W] [Nontrivial W] (o : Fin d)
    (hirr : ∀ P : Submodule ℂ W, (∀ i a, ∀ w ∈ P, r i a w ∈ P) → P = ⊥ ∨ P = ⊤)
    (U : W ≃ₗ[ℂ] W)
    (hU : ∀ i a, ((U : W →ₗ[ℂ] W) : Module.End ℂ W) * r (i + 1) a = r i a * (U : W →ₗ[ℂ] W)) :
    ∃ μ : ℂ, μ ≠ 0 ∧ ((U : W →ₗ[ℂ] W) : Module.End ℂ W) * FF r hc (fun _ => o) =
      μ • FF r hc (fun _ => o) := by
  set f : Module.End ℂ W := FF r hc (fun _ => o) with hf
  set Ue : Module.End ℂ W := (U : W →ₗ[ℂ] W) with hUe
  have hf0 : f ≠ 0 := by
    intro h0
    have h1 : (1 : Module.End ℂ W) = 0 := by
      rw [← FF_sum r hc]
      refine Finset.sum_eq_zero (fun p _ => ?_)
      rw [FF_conj r hc p o, ← hf, h0]
      simp
    exact one_ne_zero h1
  have hidem : f * f = f := FF_idem r hc _
  have hcomm : Ue * f = f * Ue := RR_shift r hc Ue hU _
  have hinv : ∀ x ∈ LinearMap.range f, Ue x ∈ LinearMap.range f := by
    rintro _ ⟨y, rfl⟩
    refine ⟨Ue y, ?_⟩
    exact (LinearMap.congr_fun hcomm y).symm
  haveI : Nontrivial (LinearMap.range f) :=
    (Submodule.nontrivial_iff_ne_bot).2 (fun h => hf0 (LinearMap.range_eq_bot.1 h))
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (Ue.restrict hinv)
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hv1 : Ue (v : W) = μ • (v : W) := by
    have := congrArg Subtype.val hv.apply_eq_smul
    simpa using this
  have hw0 : (v : W) ≠ 0 := by
    have := hv.2
    simpa using this
  have hfw : f (v : W) = v := by
    obtain ⟨y, hy⟩ := v.2
    rw [← hy]
    exact LinearMap.congr_fun hidem y
  set w : W := (v : W) with hw
  let P : Submodule ℂ W := Submodule.span ℂ (Set.range fun b : Fin (m + 1) → Mt d => RR r hc b w)
  have hP : P = ⊤ := by
    have hinvP : ∀ i a, ∀ x ∈ P, r i a x ∈ P := by
      intro i a x hx
      induction hx using Submodule.span_induction with
      | mem x h =>
        obtain ⟨b, rfl⟩ := h
        exact Submodule.subset_span ⟨Pi.mulSingle i a * b, by
          change RR r hc (Pi.mulSingle i a * b) w = r i a (RR r hc b w)
          rw [map_mul, RR_single]
          rfl⟩
      | zero => simp
      | add x y _ _ hx hy => rw [map_add]; exact P.add_mem hx hy
      | smul c x _ hx => rw [map_smul]; exact P.smul_mem c hx
    rcases hirr P hinvP with h | h
    · exfalso
      have hwP : w ∈ P := Submodule.subset_span ⟨1, by simp⟩
      rw [h] at hwP
      exact hw0 (by simpa using hwP)
    · exact h
  have hall : ∀ x, Ue (f x) = μ • f x := by
    have hle : P ≤ LinearMap.ker (Ue * f - μ • f) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨b, rfl⟩
      have h1 : f * RR r hc b * f = (∏ i, b i o o) • f := by
        have h := (RM r hc).map_smul_univ (fun i => b i o o) (fun _ => uu o o)
        simp only [RM_apply] at h
        rw [hf]
        unfold FF
        rw [← h, ← map_mul, ← map_mul]
        congr 1
        funext i
        exact uu_sandwich o (b i)
      have h2 : f (RR r hc b w) = (∏ i, b i o o) • w := by
        have h := LinearMap.congr_fun h1 w
        simpa [Module.End.mul_apply, hfw] using h
      simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.mul_apply,
        LinearMap.smul_apply, h2, map_smul, hv1]
      rw [smul_comm, sub_self]
    intro x
    have hx : x ∈ P := hP ▸ Submodule.mem_top
    have h := hle hx
    simpa [sub_eq_zero, Module.End.mul_apply] using h
  refine ⟨μ, ?_, LinearMap.ext hall⟩
  rintro rfl
  rw [zero_smul] at hv1
  exact hw0 (U.injective (by simpa [hUe] using hv1))

include hc in
private theorem core [FiniteDimensional ℂ W] [Nontrivial W] (o : Fin d)
    (hirr : ∀ P : Submodule ℂ W, (∀ i a, ∀ w ∈ P, r i a w ∈ P) → P = ⊥ ∨ P = ⊤)
    (U : W ≃ₗ[ℂ] W) (hU : ∀ i a w, U (r (i + 1) a w) = r i a (U w)) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ (i₀ : Fin (m + 1)) (S : Module.End ℂ W),
      (∀ j, j ≠ i₀ → ∀ a, Commute S (r j a)) →
      LinearMap.trace ℂ W (S ∘ₗ (U : W →ₗ[ℂ] W)) = c * LinearMap.trace ℂ W S := by
  set Ue : Module.End ℂ W := (U : W →ₗ[ℂ] W) with hUe
  have hU' : ∀ i a, Ue * r (i + 1) a = r i a * Ue := fun i a => LinearMap.ext (fun w => hU i a w)
  obtain ⟨μ, hμ0, hμ⟩ := exists_scalar r hc o hirr U hU'
  have hd : (d : ℂ) ≠ 0 := by
    have := o.pos
    exact_mod_cast this.ne'
  have hF : ∀ a : Fin d, Ue * FF r hc (fun _ => a) = μ • FF r hc (fun _ => a) := by
    intro a
    have h2 : Ue * RR r hc (fun _ => uu a o) = RR r hc (fun _ => uu a o) * Ue :=
      RR_shift r hc Ue hU' _
    rw [FF_conj r hc (fun _ => a) o, ← mul_assoc, ← mul_assoc, h2, mul_assoc _ Ue, hμ]
    simp only [mul_smul_comm, smul_mul_assoc]
  refine ⟨μ / (d : ℂ) ^ m, div_ne_zero hμ0 (pow_ne_zero _ hd), fun i₀ S hS => ?_⟩
  have hone : ∀ T : Module.End ℂ W, LinearMap.trace ℂ W T =
      ∑ p : Fin (m + 1) → Fin d, LinearMap.trace ℂ W (FF r hc p * T) := by
    intro T
    rw [← map_sum, ← Finset.sum_mul, FF_sum, one_mul]
  have h1 : LinearMap.trace ℂ W (S * Ue) =
      ∑ a : Fin d, LinearMap.trace ℂ W (FF r hc (fun _ => a) * (S * Ue)) := by
    rw [hone (S * Ue)]
    have hinj : Function.Injective (fun (a : Fin d) (_ : Fin (m + 1)) => a) :=
      fun a b h => congrFun h 0
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image fun (a : Fin d) (_ : Fin (m + 1)) => a)),
      Finset.sum_image (fun a _ b _ h => hinj h)]
    intro p _ hp
    by_contra hne
    apply hp
    have hcst : ∀ j, j ≠ i₀ → p j = p (j + 1) := by
      intro j hj
      by_contra hpj
      exact hne (tr_nonconst r hc Ue hU' S j (hS j hj) p hpj)
    refine Finset.mem_image.2 ⟨p i₀, Finset.mem_univ _, ?_⟩
    funext i
    exact (const_of i₀ p hcst i).symm
  have h2 : LinearMap.trace ℂ W S =
      (d : ℂ) ^ m * ∑ a : Fin d, LinearMap.trace ℂ W (FF r hc (fun _ => a) * S) := by
    rw [hone S, Finset.sum_congr rfl (fun p _ => tr_fib r hc i₀ S hS p),
      sum_fib i₀ (fun a => LinearMap.trace ℂ W (FF r hc (fun _ => a) * S))]
    simp [nsmul_eq_mul]
  have h3 : ∀ a : Fin d, LinearMap.trace ℂ W (FF r hc (fun _ => a) * (S * Ue)) =
      μ * LinearMap.trace ℂ W (FF r hc (fun _ => a) * S) := by
    intro a
    calc LinearMap.trace ℂ W (FF r hc (fun _ => a) * (S * Ue))
        = LinearMap.trace ℂ W (FF r hc (fun _ => a) * S * Ue) := by rw [mul_assoc]
      _ = LinearMap.trace ℂ W (Ue * (FF r hc (fun _ => a) * S)) := LinearMap.trace_mul_comm _ _ _
      _ = LinearMap.trace ℂ W (Ue * FF r hc (fun _ => a) * S) := by rw [mul_assoc]
      _ = _ := by rw [hF, smul_mul_assoc, map_smul, smul_eq_mul]
  change LinearMap.trace ℂ W (S * Ue) = _
  rw [h1, h2, Finset.sum_congr rfl (fun a _ => h3 a), ← Finset.mul_sum]
  field_simp

end Units

end UpperTheory.ConvolutionTheory.L1

theorem UpperTheory.ConvolutionTheory.L1.unitsTrace :
    UpperTheory.ConvolutionTheory.L1.UnitsTrace := by
  intro W _ _ _ m d r hc hirr U hU
  rcases subsingleton_or_nontrivial W with hW | hW
  · refine ⟨1, one_ne_zero, fun i₀ S _ => ?_⟩
    have h0 : S = 0 := LinearMap.ext (fun x => Subsingleton.elim _ _)
    have h1 : S ∘ₗ (U : W →ₗ[ℂ] W) = 0 := LinearMap.ext (fun x => Subsingleton.elim _ _)
    rw [h1, h0]
    simp
  · have hd : 0 < d := by
      rcases Nat.eq_zero_or_pos d with rfl | h
      · exfalso
        have h1 : (1 : Module.End ℂ W) = 0 := by
          have e1 := map_one (r 0)
          have e2 := map_zero (r 0)
          rw [Subsingleton.elim (1 : Matrix (Fin 0) (Fin 0) ℂ) 0] at e1
          rw [← e1, e2]
        exact one_ne_zero h1
      · exact h
    exact core r hc ⟨0, hd⟩ hirr U hU
