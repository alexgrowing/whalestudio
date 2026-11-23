import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.ActUVariableEqPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHeckePairIwC

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem lt_imp_mul_prod_le_of_b_le_one_le_a_mul_le {G : Type} [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] {n : ℕ}
    (a b : Fin n → G) (hb1 : ∀ l, b l ≤ 1) (hba : ∀ l, b l ≤ a l) (hab : ∀ l, a l * b l ≤ 1) :
    ∀ i j : Fin n, i < j → a i * ∏ l, b l ≤ a j := by
  classical
  intro i j hij
  have hne : j ≠ i := ne_of_gt hij
  have hsplit : ∏ l, b l = b i * (b j * ∏ l ∈ (Finset.univ.erase i).erase j, b l) := by
    rw [Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ j⟩),
      Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  calc a i * ∏ l, b l = (a i * b i) * (b j * ∏ l ∈ (Finset.univ.erase i).erase j, b l) := by
        rw [hsplit, mul_assoc]
    _ ≤ 1 * (b j * 1) := mul_le_mul' (hab i) (mul_le_mul' le_rfl (Finset.prod_le_one' (fun l _ => hb1 l)))
    _ ≤ a j := by rw [one_mul, mul_one]; exact hba j

private theorem le_imp_mul_pow_sub_le_of_c_le_one_mul_le {G : Type} [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] {n : ℕ}
    (a : Fin n → G) (c : G) (hc1 : c ≤ 1) (hc : ∀ i j : Fin n, i < j → a i * c ≤ a j) (i j : Fin n)
    (hij : i ≤ j) : a i * c ^ (n - (i : ℕ)) ≤ a j * c ^ (n - (j : ℕ)) := by
  rcases lt_or_eq_of_le hij with h | h
  · obtain ⟨d, hd⟩ : ∃ d, n - (i : ℕ) = (n - (j : ℕ)) + d + 1 :=
      ⟨(j : ℕ) - i - 1, by have := j.isLt; have := Fin.lt_iff_val_lt_val.mp h; omega⟩
    calc a i * c ^ (n - (i : ℕ)) = (a i * c) * c ^ d * c ^ (n - (j : ℕ)) := by
          rw [hd, pow_add, pow_add, pow_one]; ac_rfl
      _ ≤ a j * 1 * c ^ (n - (j : ℕ)) := mul_le_mul' (mul_le_mul' (hc i j h) (pow_le_one' hc1 d)) le_rfl
      _ = a j * c ^ (n - (j : ℕ)) := by rw [mul_one]
  · rw [h]

private theorem thetaMap_split {k : Type} [Field k] [ValuativeRel k] {n : ℕ} (t : Fin n → kˣ) :
    ∃ c : kˣ, ∀ s : Fin n → kˣ, (s = 1 ∨ s = t) → ∀ i j : Fin n, i ≤ j →
      valuation k ((s i * c ^ (n - i) : kˣ) : k) ≤ valuation k ((s j * c ^ (n - j) : kˣ) : k) := by
  classical
  let φ : kˣ →* (ValueGroupWithZero k)ˣ := Units.map (valuation k).toMonoidWithZeroHom.toMonoidHom
  have hφ : ∀ u : kˣ, valuation k (u : k) = ((φ u : (ValueGroupWithZero k)ˣ) : ValueGroupWithZero k) :=
    fun u => rfl
  let w : Fin n → kˣ := fun l => if φ (t l) ≤ 1 then t l else (t l)⁻¹
  have hw1 : ∀ l, φ (w l) ≤ 1 := fun l => by
    simp only [w]
    split_ifs with h
    · exact h
    · rw [map_inv]; exact inv_le_one'.mpr (le_of_lt (not_le.mp h))
  have hwa : ∀ l, φ (w l) ≤ φ (t l) := fun l => by
    simp only [w]
    split_ifs with h
    · exact le_rfl
    · rw [map_inv]
      exact (inv_le_one'.mpr (le_of_lt (not_le.mp h))).trans (le_of_lt (not_le.mp h))
  have hwab : ∀ l, φ (t l) * φ (w l) ≤ 1 := fun l => by
    simp only [w]
    split_ifs with h
    · exact mul_le_one' h h
    · rw [map_inv, mul_inv_cancel]
  refine ⟨∏ l, w l, ?_⟩
  have hC : φ (∏ l, w l) = ∏ l, φ (w l) := map_prod φ _ _
  have hc1 : ∏ l, φ (w l) ≤ 1 := Finset.prod_le_one' (fun l _ => hw1 l)
  intro s hs i j hij
  rw [hφ, hφ, Units.val_le_val, map_mul, map_mul, map_pow, map_pow, hC]
  rcases hs with h | h
  · rw [h]
    simpa using le_imp_mul_pow_sub_le_of_c_le_one_mul_le (fun _ => (1 : (ValueGroupWithZero k)ˣ)) _ hc1
      (fun _ _ _ => by rw [one_mul]; exact hc1) i j hij
  · rw [h]
    exact le_imp_mul_pow_sub_le_of_c_le_one_mul_le (fun l => φ (t l)) _ hc1
      (lt_imp_mul_prod_le_of_b_le_one_le_a_mul_le (fun l => φ (t l)) (fun l => φ (w l)) hw1 hwa hwab) i j hij

private theorem thetaMap_dc {A M A' M' G : Type} [CommRing A] [AddCommGroup M] [Module A M] [CommRing A'] [AddCommGroup M']
    [Module A' M'] [Group G] (ρ : Representation A G M) (ρ' : Representation A' G M') (K K' : Subgroup G) (x : G)
    (hx : FinOrb K K' x) (f : M →+ M') (hf : ∀ g m, f (ρ g m) = ρ' g (f m)) (m : M) :
    dc ρ' K K' x (f m) = f (dc ρ K K' x m) := by
  haveI := hx.fintype
  simp only [dc, finsum_eq_sum_of_fintype, LinearMap.sum_apply, map_sum, hf]

private theorem thetaMap_ext {A N A' N' T : Type} [CommRing A] [AddCommGroup N] [Module A N] [CommRing A'] [AddCommGroup N']
    [Module A' N'] [Group T] (θ : T →* (Module.End A N)ˣ) (θ' : T →* (Module.End A' N')ˣ) (g : N → N') (t b : T)
    (hb : ∀ m, (θ' b).val (g m) = g ((θ b).val m)) (ha : ∀ m, (θ' (b * t)).val (g m) = g ((θ (b * t)).val m)) (m : N) :
    (θ' t).val (g m) = g ((θ t).val m) := by
  have key : ∀ y, ((θ' b)⁻¹).val ((θ' b).val y) = y := fun y => by
    rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one, Module.End.one_apply]
  have h1 := ha m
  simp only [map_mul, Units.val_mul, Module.End.mul_apply] at h1
  rw [← hb] at h1
  rw [← key ((θ' t).val (g m)), h1, key]

theorem UpperTheory.V.Pa.Lev.thetaMap :
    ∀ (L : Type) [Field L] [NumberField L] (n q : ℕ) (w : Fin q → Plc L) (A M A' M' : Type) [CommRing A] [AddCommGroup M] [Module A M] [CommRing A'] [AddCommGroup M'] [Module A' M'] (ρ : Representation A (GV n w) M) (ρ' : Representation A' (GV n w) M') (C : ∀ j, Subgroup 𝓀[(w j).adicCompletion L]ˣ) (Θ) (Θ'), IsThetaQ ρ C Θ → IsThetaQ ρ' C Θ' → ∀ f : M →+ M', (∀ g m, f (ρ g m) = ρ' g (f m)) → ∀ j t (m : fixd ρ (UC n w C)) (m' : fixd ρ' (UC n w C)), (m' : M') = f m → ((Θ' j t).val m').val = f ((Θ j t).val m).val := by
  intro L _ _ n q w A M A' M' _ _ _ _ _ _ ρ ρ' C Θ Θ' hΘ hΘ' f hf j t m m' hm
  let g : fixd ρ (UC n w C) → fixd ρ' (UC n w C) := fun x =>
    ⟨f x, show ∀ u ∈ UC n w C, ρ' u (f x) = f x from fun u hu => by
      rw [← hf]
      exact congrArg f ((show ∀ u ∈ UC n w C, ρ u x = x from x.2) u hu)⟩
  have hdom : ∀ s, Dom s → ∀ x, (Θ' j s).val (g x) = g ((Θ j s).val x) := by
    intro s hs x
    apply Subtype.ext
    rw [hΘ'.1 j s hs (g x)]
    change _ = f (((Θ j s).val x : M))
    rw [hΘ.1 j s hs x]
    exact thetaMap_dc _ _ _ _ _ ((heckePairIwC _ n (C j)).1 _) f (fun g' y => hf _ y) x
  obtain ⟨c, hc⟩ := thetaMap_split t
  let b : Fin n → (HeightOneSpectrum.adicCompletion L (w j))ˣ := fun i => c ^ (n - (i : ℕ))
  have hb : Dom b := fun i i' h => by simpa [b] using hc 1 (Or.inl rfl) i i' h
  have hbt : Dom (b * t) := fun i i' h => by
    have := hc t (Or.inr rfl) i i' h
    simpa [b, Pi.mul_apply, mul_comm] using this
  have key := thetaMap_ext (Θ j) (Θ' j) g t b (hdom b hb) (hdom (b * t) hbt) m
  have hm' : m' = g m := Subtype.ext hm
  rw [hm', key]
