import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsUniqueUnramifiedCocycleFrobeniusValue
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FrobDense
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IqBasic
import Mathlib.RingTheory.Nilpotent.Exp

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module Topology UpperTheory.V.Loc UpperTheory.V.U3

namespace UpperTheory.V.Loc.TorusExponentialLift

open IsNilpotent

private theorem nil_add {B : Type} [CommRing B] {a b : B} (ha : IsNilpotent a) (hb : IsNilpotent b) :
    IsNilpotent (a + b) := (Commute.all a b).isNilpotent_add ha hb

private theorem exists_exp_eq_one_add_add_sq_mul_of_nilpotent {B : Type} [CommRing B] [Algebra ℚ B] (n : B) (K : ℕ) (hK : n ^ K = 0) :
    ∃ w : B, exp n = 1 + n + n ^ 2 * w := by
  have hK' : n ^ (K + 2) = 0 := by rw [pow_add, hK, zero_mul]
  refine ⟨∑ i ∈ Finset.range K, (((i + 2).factorial : ℕ) : ℚ)⁻¹ • n ^ i, ?_⟩
  rw [exp_eq_sum hK', Finset.sum_range_succ', Finset.sum_range_succ', Finset.mul_sum]
  have e : ∀ i : ℕ, (((i + 1 + 1).factorial : ℕ) : ℚ)⁻¹ • n ^ (i + 1 + 1) =
      n ^ 2 * ((((i + 2).factorial : ℕ) : ℚ)⁻¹ • n ^ i) := by
    intro i
    rw [mul_smul_comm, ← pow_add, add_comm 2 i]
  simp only [e, zero_add, Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, inv_one, one_smul,
    pow_zero, pow_one]
  abel

private theorem exp_onto {B : Type} [CommRing B] [Algebra ℚ B] :
    ∀ (k : ℕ) (n : B), n ^ (k + 1) = 0 → ∃ x : B, IsNilpotent x ∧ exp x = 1 + n := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro n hn
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [zero_add, pow_one] at hn
      exact ⟨0, IsNilpotent.zero, by rw [exp_zero, hn, add_zero]⟩
    · obtain ⟨w, hw⟩ := exists_exp_eq_one_add_add_sq_mul_of_nilpotent n (k + 1) hn
      have hnil : IsNilpotent n := ⟨k + 1, hn⟩
      have hu := exp_mul_exp_neg_self hnil
      have h1 : exp n * (1 + n ^ 2 * (-(exp (-n)) * w)) = 1 + n := by
        linear_combination hw - n ^ 2 * w * hu
      have hm : (n ^ 2 * (-(exp (-n)) * w)) ^ (k / 2 + 1) = 0 := by
        rw [mul_pow, ← pow_mul, pow_eq_zero_of_le (by omega : k + 1 ≤ 2 * (k / 2 + 1)) hn, zero_mul]
      obtain ⟨y, hy, hey⟩ := ih (k / 2) (by omega) _ hm
      refine ⟨n + y, nil_add hnil hy, ?_⟩
      rw [exp_add_of_commute (Commute.all n y) hnil hy, hey]
      exact h1

private theorem cont_exp {l : ℕ} [Fact l.Prime] {B : Type} [CommRing B] [Algebra ℚ B] [Algebra ℚ_[l] B]
    [TopologicalSpace B] [IsTopologicalRing B] [ContinuousSMul ℚ_[l] B] {X : Type} [TopologicalSpace X]
    {f : X → ℚ_[l]} (hf : Continuous f) {a : B} (ha : IsNilpotent a) : Continuous fun g => exp (f g • a) := by
  obtain ⟨K, hK⟩ := ha
  have e : ∀ g, exp (f g • a) = ∑ i ∈ Finset.range K,
      algebraMap ℚ B ((i.factorial : ℚ)⁻¹) * ((f g) ^ i • a ^ i) := by
    intro g
    rw [exp_eq_sum (k := K) (by rw [smul_pow, hK, smul_zero])]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, smul_pow]
  simp only [e]
  refine continuous_finset_sum _ fun i _ => ?_
  exact continuous_const.mul ((hf.pow i).smul continuous_const)

private theorem continuous_exp_nilpotent_pair {l : ℕ} [Fact l.Prime] {B : Type} [CommRing B] [Algebra ℚ B] [Algebra ℚ_[l] B]
    [TopologicalSpace B] [IsTopologicalRing B] [ContinuousSMul ℚ_[l] B] {X : Type} [TopologicalSpace X]
    {f f' : X → ℚ_[l]} (hf : Continuous f) (hf' : Continuous f') {a b : B} (ha : IsNilpotent a)
    (hb : IsNilpotent b) : Continuous fun g => exp (f g • a + f' g • b) := by
  have hna : ∀ g, IsNilpotent (f g • a) := by
    intro g
    obtain ⟨K, hK⟩ := ha
    exact ⟨K, by rw [smul_pow, hK, smul_zero]⟩
  have hnb : ∀ g, IsNilpotent (f' g • b) := by
    intro g
    obtain ⟨K, hK⟩ := hb
    exact ⟨K, by rw [smul_pow, hK, smul_zero]⟩
  simp only [fun g => exp_add_of_commute (Commute.all (f g • a) (f' g • b)) (hna g) (hnb g)]
  exact (cont_exp hf ha).mul (cont_exp hf' hb)

private theorem t2Space_of_finite_dim_padic_module {l : ℕ} [Fact l.Prime] (V : Type) [AddCommGroup V] [Module ℚ_[l] V]
    [Module.Finite ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] : T2Space V := by
  let b := Module.Free.chooseBasis ℚ_[l] V
  let e : V →ₗ[ℚ_[l]] (Module.Free.ChooseBasisIndex ℚ_[l] V → ℚ_[l]) := b.equivFun.toLinearMap
  have hc : Continuous e := IsModuleTopology.continuous_of_linearMap e
  exact T2Space.of_injective_continuous b.equivFun.injective hc

private theorem tor_inv_apply_eq_ite_rev {G : Type} [Group G] {η : G →* ℤˣ} {B : Type} [CommRing B] (T : Tor η B)
    (a : G) (i : Fin 3) : T.t a⁻¹ i = if η a = 1 then (T.t a i)⁻¹ else T.t a i.rev := by
  have h := T.mul a a⁻¹
  split_ifs with ha
  · have h1 := h i
    rw [mul_inv_cancel, T.t_one, if_pos ha] at h1
    exact eq_inv_of_mul_eq_one_right h1.symm
  · have h1 := h i.rev
    rw [mul_inv_cancel, T.t_one, if_neg ha, Fin.rev_rev] at h1
    exact (mul_inv_eq_one.mp h1.symm).symm

private theorem tor_ext {l : ℕ} [Fact l.Prime] {η : GQ l →* ℤˣ} {B B' : Type} [CommRing B] [CommRing B']
    [TopologicalSpace B'] [T2Space B'] (p : B →* B') (T : Tor η B) (T' : Tor η B')
    (hT : ∀ i, Continuous fun g => p (T.t g i : B)) (hT' : ∀ i, Continuous fun g => (T'.t g i : B'))
    {σ : GQ l} (hσ : IsFrob σ) (hI : ∀ g ∈ Iq l, ∀ i, p (T.t g i : B) = T'.t g i)
    (hs : ∀ i, p (T.t σ i : B) = T'.t σ i) (g : GQ l) : ∀ i, p (T.t g i : B) = T'.t g i := by
  let S : Subgroup (GQ l) :=
    { carrier := {g | ∀ i, Units.map p (T.t g i) = T'.t g i}
      one_mem' := by
        intro i
        simp only [T.t_one, T'.t_one, map_one]
      mul_mem' := by
        intro a b ha hb i
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [T.mul, T'.mul, map_mul, ha]
        split_ifs
        · rw [hb]
        · rw [map_inv, hb]
      inv_mem' := by
        intro a ha i
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [tor_inv_apply_eq_ite_rev T, tor_inv_apply_eq_ite_rev T']
        split_ifs
        · rw [map_inv, ha]
        · rw [ha] }
  have key : ∀ g i, p (T.t g i : B) = T'.t g i ↔ Units.map p (T.t g i) = T'.t g i := by
    intro g i
    rw [Units.ext_iff, Units.coe_map]
  have hS : IsClosed (S : Set (GQ l)) := by
    have e : (S : Set (GQ l)) = ⋂ i, {g | p (T.t g i : B) = T'.t g i} := by
      ext g
      simp only [Set.mem_iInter, Set.mem_setOf_eq, key]
      exact Iff.rfl
    rw [e]
    exact isClosed_iInter fun i => isClosed_eq (hT i) (hT' i)
  have hle : Iq l ⊔ Subgroup.zpowers σ ≤ S := by
    rw [sup_le_iff, Subgroup.zpowers_le]
    exact ⟨fun g hg i => (key g i).1 (hI g hg i), fun i => (key σ i).1 (hs i)⟩
  have htop := Subgroup.topologicalClosure_minimal _ hle hS
  rw [frobDense σ hσ] at htop
  intro i
  exact (key g i).2 (htop (Subgroup.mem_top g) i)

private theorem scal_cocycle {l : ℕ} [Fact l.Prime] {η : GQ l →* ℤˣ} (hI : ∀ g ∈ Iq l, η g = 1)
    (hlc : IsLocallyConstant η) {σ : GQ l} (hσ : IsFrob σ) :
    ∃ c : GQ l → ℚ_[l], Continuous c ∧ (∀ g h, c (g * h) = c g + ((η g : ℤ) : ℚ_[l]) * c h) ∧
      (∀ g ∈ Iq l, c g = 0) ∧ c σ = 1 := by
  let χ : GQ l →* ℚ_[l]ˣ := (Units.map (Int.castRingHom ℚ_[l]).toMonoidHom).comp η
  have hχ : ∀ g, (χ g : ℚ_[l]) = ((η g : ℤ) : ℚ_[l]) := by
    intro g
    simp [χ]
  have hcont : Continuous fun g => (χ g : ℚ_[l]) := by
    simp only [hχ]
    exact (hlc.comp fun u : ℤˣ => ((u : ℤ) : ℚ_[l])).continuous
  have hI' : ∀ g ∈ Iq l, chRep χ g = 1 := by
    intro g hg
    apply LinearMap.ext
    intro v
    rw [chRep_apply, hχ, hI g hg]
    simp
  obtain ⟨c, ⟨hcZ, hcI, hcσ⟩, -⟩ :=
    existsUnique_unramified_cocycle_frobenius_value (v := l) (l := l) (chRep χ) (contAction_chRep hcont) hI' σ hσ (1 : ℚ_[l])
  rw [ReciprocityTheory.Gal.mem_Z1_iff_cocycle] at hcZ
  refine ⟨c, hcZ.1, fun g h => ?_, hcI, hcσ⟩
  rw [hcZ.2 g h, chRep_apply, hχ]

private theorem weight_rev_eq_neg (i : Fin 3) : wt1 i.rev = -wt1 i := by
  fin_cases i <;> rfl

end UpperTheory.V.Loc.TorusExponentialLift

open UpperTheory.V.Loc.TorusExponentialLift IsNilpotent in
theorem UpperTheory.exists_torus_lift_to_nilpotent_thickening :
    ∀ {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {η : GQ l →* ℤˣ} {Ψ : GQ l →* Eˣ} {H : Subgroup (GQ l)} {e : ℕ} (hD : TriDat η Ψ H e) {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) {B' : Type} [CommRing B'] [Algebra ℚ_[l] B'] [Module.Finite ℚ_[l] B'] [TopologicalSpace B'] [IsModuleTopology ℚ_[l] B'] [IsTopologicalRing B'] [Algebra ℤ_[l] B'] [IsScalarTower ℤ_[l] ℚ_[l] B'] [Algebra E B'] [IsScalarTower ℚ_[l] E B'] (π' : B' →ₐ[E] E) (hπ' : ∀ a, π' a = 0 → IsNilpotent a) (p : B →ₐ[E] B'), Function.Surjective p → π'.comp p = π → ∀ T' : Tor η B', T'.Good π' Ψ → ∃ T : Tor η B, T.Good π Ψ ∧ ∀ g i, p (T.t g i : B) = (T'.t g i : B') := by
  intro l _ E _ _ _ _ _ η Ψ H e hD B _ _ _ _ _ _ _ _ _ _ π hπ B' _ _ _ _ _ _ _ _ _ _ π' hπ' p hp hpπ T' hT'
  letI : Algebra ℚ B := ((algebraMap ℚ_[l] B).comp (algebraMap ℚ ℚ_[l])).toAlgebra
  letI : Algebra ℚ B' := ((algebraMap ℚ_[l] B').comp (algebraMap ℚ ℚ_[l])).toAlgebra
  haveI : T2Space B' := t2Space_of_finite_dim_padic_module (l := l) B'
  obtain ⟨σ, hσ⟩ := (iqBasic l).2.2.2.1
  obtain ⟨c, hc, hcm, hcI, hcσ⟩ := scal_cocycle hD.ηI hD.ηlc hσ
  obtain ⟨d, hd, hdm, hdI, hdσ⟩ :=
    scal_cocycle (η := 1) (fun _ _ => rfl) (IsLocallyConstant.const (1 : ℤˣ)) hσ
  have hdm' : ∀ g h, d (g * h) = d g + d h := by
    intro g h
    rw [hdm]
    simp
  have hEnil : ∀ z : E, IsNilpotent z → z = 0 := fun z hz => hz.eq_zero
  have hn' : ∀ i, IsNilpotent ((T'.t σ i : B') * algebraMap E B' ↑((Ψ σ ^ wt1 i)⁻¹) - 1) := by
    intro i
    apply hπ'
    rw [map_sub, map_mul, AlgHom.commutes, hT'.red, map_one, Algebra.algebraMap_self, RingHom.id_apply,
      Units.mul_inv, sub_self]
  have hy : ∀ i, ∃ y : B', IsNilpotent y ∧
      exp y = (T'.t σ i : B') * algebraMap E B' ↑((Ψ σ ^ wt1 i)⁻¹) := by
    intro i
    obtain ⟨k, hk⟩ := hn' i
    obtain ⟨y, hy1, hy2⟩ := exp_onto k _ (pow_eq_zero_of_le (Nat.le_succ k) hk)
    exact ⟨y, hy1, by rw [hy2, add_sub_cancel]⟩
  choose y hyn hye using hy
  choose x hx using fun i => hp (y i)
  have hxn : ∀ i, IsNilpotent (x i) := by
    intro i
    apply hπ
    rw [← hpπ, AlgHom.comp_apply, hx]
    exact hEnil _ ((hyn i).map π')
  let s : Fin 3 → B := fun i => (2⁻¹ : ℚ_[l]) • (x i + x i.rev)
  let u : Fin 3 → B := fun i => (2⁻¹ : ℚ_[l]) • (x i - x i.rev)
  have hs : ∀ i, s i.rev = s i := by
    intro i
    simp only [s, Fin.rev_rev, add_comm]
  have hu : ∀ i, u i.rev = -u i := by
    intro i
    simp only [u, Fin.rev_rev, ← smul_neg, neg_sub]
  have hsu : ∀ i, s i + u i = x i := by
    intro i
    simp only [s, u]
    rw [← smul_add, show x i + x i.rev + (x i - x i.rev) = (2 : ℚ_[l]) • x i by rw [two_smul]; abel,
      smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]
  have hsn : ∀ i, IsNilpotent (s i) := fun i => by
    obtain ⟨k, hk⟩ := nil_add (hxn i) (hxn i.rev)
    exact ⟨k, by simp only [s]; rw [smul_pow, hk, smul_zero]⟩
  have hun : ∀ i, IsNilpotent (u i) := fun i => by
    obtain ⟨k, hk⟩ := nil_add (hxn i) (hxn i.rev).neg
    exact ⟨k, by simp only [u]; rw [sub_eq_add_neg, smul_pow, hk, smul_zero]⟩
  let a : GQ l → Fin 3 → B := fun g i => c g • s i + d g • u i
  have ha : ∀ g h i, a (g * h) i = a g i + if η g = 1 then a h i else -a h i.rev := by
    intro g h i
    rcases Int.units_eq_one_or (η g) with h1 | h1
    · simp only [a, hcm, hdm', h1, if_pos, Units.val_one, Int.cast_one, one_mul, add_smul]
      abel
    · rw [if_neg (by rw [h1]; decide)]
      simp only [a, hcm, hdm', h1, hs, hu, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one,
        neg_one_mul, add_smul, neg_smul, smul_neg]
      abel
  have han : ∀ g i, IsNilpotent (a g i) := by
    intro g i
    refine nil_add ?_ ?_
    · obtain ⟨k, hk⟩ := hsn i
      exact ⟨k, by rw [smul_pow, hk, smul_zero]⟩
    · obtain ⟨k, hk⟩ := hun i
      exact ⟨k, by rw [smul_pow, hk, smul_zero]⟩
  have hLc : Continuous fun b : B' => algebraMap E B (π' b) := by
    let L : B' →ₗ[ℚ_[l]] B := ((Algebra.linearMap E B).comp π'.toLinearMap).restrictScalars ℚ_[l]
    exact IsModuleTopology.continuous_of_linearMap L
  have hpc : Continuous fun b : B => p b := by
    let L : B →ₗ[ℚ_[l]] B' := p.toLinearMap.restrictScalars ℚ_[l]
    exact IsModuleTopology.continuous_of_linearMap L
  let EU : GQ l → Fin 3 → Bˣ := fun g i => Units.map (algebraMap E B : E →* B) (Ψ g ^ wt1 i)
  let XU : GQ l → Fin 3 → Bˣ := fun g i => (isUnit_exp (han g i)).unit
  have hEU : ∀ g i, (EU g i : B) = algebraMap E B ↑(Ψ g ^ wt1 i) := fun g i => rfl
  have hXU : ∀ g i, (XU g i : B) = exp (a g i) := fun g i => rfl
  have hE1 : ∀ g h i, EU (g * h) i = EU g i * EU h i := by
    intro g h i
    simp only [EU, map_mul, mul_zpow]
  have hE2 : ∀ h i, EU h i.rev = (EU h i)⁻¹ := by
    intro h i
    simp only [EU, weight_rev_eq_neg, zpow_neg, map_inv]
  have hX1 : ∀ g h i, η g = 1 → XU (g * h) i = XU g i * XU h i := by
    intro g h i h1
    apply Units.ext
    rw [Units.val_mul, hXU, hXU, hXU, ha, if_pos h1,
      exp_add_of_commute (Commute.all _ _) (han g i) (han h i)]
  have hX2 : ∀ g h i, ¬ η g = 1 → (XU (g * h) i : B) * XU h i.rev = XU g i := by
    intro g h i h1
    rw [hXU, hXU, hXU, ha, if_neg h1,
      ← exp_add_of_commute (Commute.all _ _) (nil_add (han g i) (han h i.rev).neg) (han h i.rev),
      neg_add_cancel_right]
  let T : Tor η B := ⟨fun g i => EU g i * XU g i, by
    intro g h i
    split_ifs with h1
    · rw [hE1, hX1 g h i h1]
      exact mul_mul_mul_comm _ _ _ _
    · rw [eq_mul_inv_iff_mul_eq, hE1, hE2]
      apply Units.ext
      have hP := Units.mul_inv (EU h i)
      have hQ := hX2 g h i h1
      simp only [Units.val_mul] at hP ⊢
      linear_combination ((EU g i : B) * ((XU (g * h) i : B) * XU h i.rev)) * hP + (EU g i : B) * hQ⟩
  have hT : ∀ g i, (T.t g i : B) = algebraMap E B ↑(Ψ g ^ wt1 i) * exp (a g i) := fun g i => rfl
  obtain ⟨hT'c, hT'ci, hT'ine, hT'red⟩ := hT'
  have hUred : ∀ g i, Units.map (π' : B' →+* E).toMonoidHom (T'.t g i) = Ψ g ^ wt1 i := by
    intro g i
    apply Units.ext
    rw [Units.coe_map]
    exact hT'red g i
  have hPE : ∀ w : Eˣ, algebraMap E B (w : E) * algebraMap E B ↑w⁻¹ = 1 := by
    intro w
    rw [← map_mul, Units.mul_inv, map_one]
  have hPE' : ∀ w : Eˣ, algebraMap E B' (w : E) * algebraMap E B' ↑w⁻¹ = 1 := by
    intro w
    rw [← map_mul, Units.mul_inv, map_one]
  have hTinv : ∀ g i, ((T.t g i)⁻¹ : Bˣ) = algebraMap E B (π' ↑((T'.t g i)⁻¹)) * exp (-a g i) := by
    intro g i
    have e1 : π' ↑((T'.t g i)⁻¹) = ↑((Ψ g ^ wt1 i)⁻¹) := by
      rw [← hUred g i, ← map_inv, Units.coe_map]
      rfl
    apply Units.inv_eq_of_mul_eq_one_right
    rw [hT, e1]
    linear_combination (exp (a g i) * exp (-a g i)) * hPE (Ψ g ^ wt1 i) + exp_mul_exp_neg_self (han g i)
  have hπexp : ∀ g i, π (exp (a g i)) = 1 := by
    intro g i
    have h0 := hEnil _ ((isNilpotent_exp_sub_one (han g i)).map π)
    rw [map_sub, map_one, sub_eq_zero] at h0
    exact h0
  have hG : T.Good π Ψ := by
    refine ⟨fun i => ?_, fun i => ?_, fun g hg i => ?_, fun g i => ?_⟩
    · have e1 : (fun g => (T.t g i : B)) =
          fun g => algebraMap E B (π' (T'.t g i)) * exp (c g • s i + d g • u i) := by
        funext g
        rw [hT, hT'red]
      rw [e1]
      exact (hLc.comp (hT'c i)).mul (continuous_exp_nilpotent_pair hc hd (hsn i) (hun i))
    · have e1 : (fun g => ((T.t g i)⁻¹ : Bˣ) : GQ l → B) =
          fun g => algebraMap E B (π' ↑((T'.t g i)⁻¹)) * exp ((-c g) • s i + (-d g) • u i) := by
        funext g
        rw [hTinv]
        simp only [a, neg_smul, neg_add]
      rw [e1]
      exact (hLc.comp (hT'ci i)).mul (continuous_exp_nilpotent_pair hc.neg hd.neg (hsn i) (hun i))
    · rw [hT]
      simp only [a, hcI g hg, hdI g hg, zero_smul, add_zero, exp_zero, mul_one]
    · rw [hT, map_mul, hπexp, mul_one, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]
  refine ⟨T, hG, fun g i => ?_⟩
  have hI' : ∀ g ∈ Iq l, ∀ i, p.toRingHom.toMonoidHom (T.t g i : B) = T'.t g i := by
    intro g hg i
    show p (T.t g i : B) = T'.t g i
    rw [hT]
    simp only [a, hcI g hg, hdI g hg, zero_smul, add_zero, exp_zero, mul_one]
    rw [AlgHom.commutes, hT'ine g hg i]
  have hs' : ∀ i, p.toRingHom.toMonoidHom (T.t σ i : B) = T'.t σ i := by
    intro i
    show p (T.t σ i : B) = T'.t σ i
    have e1 : a σ i = x i := by
      simp only [a, hcσ, hdσ, one_smul, hsu]
    rw [hT, e1, map_mul, AlgHom.commutes, map_exp (hxn i) p, hx, hye]
    linear_combination (T'.t σ i : B') * hPE' (Ψ σ ^ wt1 i)
  exact tor_ext p.toRingHom.toMonoidHom T T' (fun i => hpc.comp (hG.cont i)) hT'c hσ hI' hs' g i
