import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.PrimesEffectiveChebotarev
import Formalism.SharpRestriction.LevelLetterCocycles.StatementFamilies.ArithmeticCylinders
import Formalism.PadicSubsetSums.StableGradedCounts.FixedByAutomorphismInField
import Formalism.PadicSubsetSums.StableGradedCounts.IRRGoodDualStable

noncomputable section

namespace Formalism.MainNotions.N.PlaceLabelTeichmuller

section BoundedBy'

open Formalism.BasicNotions Formalism.MainNotions

section Len

variable {R : Type} [CommRing R]

end Len

section Drop

variable {O K V X : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    [FiniteDimensional K V] [DecidableEq X]
    (T : Subalgebra O (X → O)) (act : T →ₐ[O] (V →ₗ[K] V))

omit [IsPrincipalIdealRing O] [DecidableEq X] in

theorem exists_sep (hsep : ∀ x y : X, x ≠ y → ∃ t : T, (t : X → O) x ≠ (t : X → O) y) (π : X)
    (S : Finset X) (hπ : π ∉ S) :
    ∃ s : T, (∀ y ∈ S, (s : X → O) y = 0) ∧ (s : X → O) π ≠ 0 := by
  classical
  have hne : ∀ y : {y // y ∈ S}, (y : X) ≠ π := fun y h => hπ (h ▸ y.2)
  choose t ht using fun y : {y // y ∈ S} => hsep y π (hne y)
  have key : ∀ (u : T) (c : O) (x : X), ((u - algebraMap O T c : T) : X → O) x = (u : X → O) x - c :=
    fun u c x => by first | rfl | simp
  refine ⟨∏ y : {y // y ∈ S}, (t y - algebraMap O T ((t y : X → O) y)), ?_, ?_⟩
  · intro y hy
    rw [SubmonoidClass.coe_finset_prod, Finset.prod_apply]
    refine Finset.prod_eq_zero (Finset.mem_univ ⟨y, hy⟩) ?_
    simp only [key]
    exact sub_self _
  · rw [SubmonoidClass.coe_finset_prod, Finset.prod_apply]
    refine Finset.prod_ne_zero_iff.mpr (fun y _ => ?_)
    simp only [key]
    exact sub_ne_zero.mpr (Ne.symm (ht y))

omit [IsDomain O] [IsPrincipalIdealRing O] [IsFractionRing O K] [FiniteDimensional K V] [DecidableEq X] in
theorem act_comm (s t : T) (x : V) : act s (act t x) = act t (act s x) := by
  have h : act s * act t = act t * act s := by rw [← map_mul, ← map_mul, mul_comm]
  exact LinearMap.congr_fun h x

end Drop

end BoundedBy'

section Tensor

variable {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)] [∀ i, Finite (G i)]

def tens (a : ∀ i, MonoidAlgebra ℂ (G i)) : MonoidAlgebra ℂ (∀ i, G i) :=
  MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm fun g => ∏ i, (a i).coeff (g i))

theorem tens_coeff (a : ∀ i, MonoidAlgebra ℂ (G i)) (g : ∀ i, G i) :
    (tens a).coeff g = ∏ i, (a i).coeff (g i) := rfl

theorem conv_coeff {H : Type} [Group H] [Fintype H] (x y : MonoidAlgebra ℂ H) (g : H) :
    (x * y).coeff g = ∑ h, x.coeff h * y.coeff (h⁻¹ * g) := by
  classical
  rw [MonoidAlgebra.coeff_mul, Finsupp.sum_fintype]
  · refine Finset.sum_congr rfl (fun h _ => ?_)
    rw [Finsupp.sum_fintype]
    · rw [Finset.sum_eq_single (h⁻¹ * g)]
      · simp
      · intro b _ hb
        rw [if_neg]
        intro hh
        apply hb
        rw [← hh]
        simp
      · intro hb
        exact absurd (Finset.mem_univ _) hb
    · intro i
      simp
  · intro i
    simp

theorem tens_mul (a b : ∀ i, MonoidAlgebra ℂ (G i)) :
    tens a * tens b = tens (fun i => a i * b i) := by
  classical
  letI : ∀ i, Fintype (G i) := fun i => Fintype.ofFinite _
  apply MonoidAlgebra.ext
  ext g
  simp only [conv_coeff, tens_coeff]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  rw [Finset.prod_mul_distrib]
  rfl

theorem central_of_coeff {H : Type} [Group H] (x : MonoidAlgebra ℂ H)
    (h : ∀ g k, x.coeff (k * g⁻¹) = x.coeff (g⁻¹ * k)) (a : MonoidAlgebra ℂ H) : x * a = a * x := by
  classical
  apply MonoidAlgebra.ext
  ext k
  have L : ∀ (m : H) (c : ℂ),
      (x.coeff.sum fun m₁ r₁ => if m₁ * m = k then r₁ * c else 0) = x.coeff (k * m⁻¹) * c := by
    intro m c
    have e1 : (fun (m₁ : H) (r₁ : ℂ) => if m₁ * m = k then r₁ * c else 0) =
        fun m₁ r₁ => (if m₁ = k * m⁻¹ then r₁ else 0) * c := by
      funext m₁ r₁
      simp only [← eq_mul_inv_iff_mul_eq]
      split_ifs <;> simp
    rw [e1, ← Finsupp.sum_mul, Finsupp.sum_ite_self_eq']
  have R : ∀ (m : H) (c : ℂ),
      (x.coeff.sum fun m₂ r₂ => if m * m₂ = k then c * r₂ else 0) = c * x.coeff (m⁻¹ * k) := by
    intro m c
    have e1 : (fun (m₂ : H) (r₂ : ℂ) => if m * m₂ = k then c * r₂ else 0) =
        fun m₂ r₂ => c * (if m₂ = m⁻¹ * k then r₂ else 0) := by
      funext m₂ r₂
      simp only [← eq_inv_mul_iff_mul_eq]
      split_ifs <;> simp
    rw [e1, ← Finsupp.mul_sum, Finsupp.sum_ite_self_eq']
  rw [MonoidAlgebra.coeff_mul, MonoidAlgebra.coeff_mul, Finsupp.sum_comm]
  refine Finsupp.sum_congr (fun m _ => ?_)
  rw [L, R, h m k, mul_comm]

theorem coeff_of_central {H : Type} [Group H] (x : MonoidAlgebra ℂ H)
    (h : ∀ a : MonoidAlgebra ℂ H, x * a = a * x) (g k : H) : x.coeff (k * g⁻¹) = x.coeff (g⁻¹ * k) := by
  classical
  have hr : ∀ y : MonoidAlgebra ℂ H,
      (y * MonoidAlgebra.ofCoeff (Finsupp.single g 1)).coeff k = y.coeff (k * g⁻¹) := by
    intro y
    rw [MonoidAlgebra.coeff_mul, MonoidAlgebra.coeff_ofCoeff]
    simp only [Finsupp.sum_single_index, mul_zero, ite_self, mul_one]
    simp only [← eq_mul_inv_iff_mul_eq]
    exact Finsupp.sum_ite_self_eq' _ _
  have hl : ∀ y : MonoidAlgebra ℂ H,
      (MonoidAlgebra.ofCoeff (Finsupp.single g 1) * y).coeff k = y.coeff (g⁻¹ * k) := by
    intro y
    rw [MonoidAlgebra.coeff_mul, MonoidAlgebra.coeff_ofCoeff]
    rw [Finsupp.sum_single_index (by simp)]
    simp only [one_mul]
    simp only [← eq_inv_mul_iff_mul_eq]
    exact Finsupp.sum_ite_self_eq' _ _
  have e := congrArg (fun y => y.coeff k) (h (MonoidAlgebra.ofCoeff (Finsupp.single g 1)))
  rw [hr, hl] at e
  exact e

theorem tens_central (a : ∀ i, MonoidAlgebra ℂ (G i)) (h : ∀ i x, a i * x = x * a i)
    (x : MonoidAlgebra ℂ (∀ i, G i)) : tens a * x = x * tens a := by
  refine central_of_coeff _ (fun g k => ?_) x
  rw [tens_coeff, tens_coeff]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  simpa only [Pi.mul_apply, Pi.inv_apply] using coeff_of_central (a i) (h i) (g i) (k i)

theorem tens_one : tens (fun i => (1 : MonoidAlgebra ℂ (G i))) = 1 := by
  classical
  apply MonoidAlgebra.ext
  ext g
  rw [tens_coeff]
  have h1 : ∀ (j : ι) (x : G j), (1 : MonoidAlgebra ℂ (G j)).coeff x = if (1 : G j) = x then 1 else 0 := by
    intro j x
    rw [show (1 : MonoidAlgebra ℂ (G j)).coeff = Finsupp.single 1 1 by
      first
      | rfl
      | exact SkewMonoidAlgebra.ofCoeff_eq_one.mp rfl
      | exact MonoidAlgebra.ofCoeff_eq_one.mp rfl, Finsupp.single_apply]
  have h2 : (1 : MonoidAlgebra ℂ (∀ i, G i)).coeff g = if (1 : ∀ i, G i) = g then 1 else 0 := by
    rw [show (1 : MonoidAlgebra ℂ (∀ i, G i)).coeff = Finsupp.single 1 1 by
      first
      | rfl
      | exact SkewMonoidAlgebra.ofCoeff_eq_one.mp rfl
      | exact MonoidAlgebra.ofCoeff_eq_one.mp rfl, Finsupp.single_apply]
  simp only [h1, h2]
  by_cases hg : g = 1
  · subst hg
    simp
  · rw [if_neg (Ne.symm hg)]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hg
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg (Ne.symm hi))

theorem sum_tens {P : ι → Type} [∀ i, Fintype (P i)] [DecidableEq ι]
    (E : ∀ i, P i → MonoidAlgebra ℂ (G i)) :
    ∑ p : ∀ i, P i, tens (fun i => E i (p i)) = tens (fun i => ∑ q, E i q) := by
  classical
  apply MonoidAlgebra.ext
  ext g
  have hs : ∀ {M κ : Type} (s : Finset κ) (f : κ → MonoidAlgebra ℂ M) (x : M),
      (∑ j ∈ s, f j).coeff x = ∑ j ∈ s, (f j).coeff x :=
    fun {M κ} s f x => map_sum (AddMonoidHom.mk' (fun y : MonoidAlgebra ℂ M => y.coeff x)
      (fun y z => by first | rfl | simp)) f s
  simp only [hs, tens_coeff]
  rw [Fintype.prod_sum]

variable [DecidableEq ι]

def plc (i : ι) (a : MonoidAlgebra ℂ (G i)) : MonoidAlgebra ℂ (∀ i, G i) :=
  tens (Function.update (fun _ => 1) i a)

theorem tens_mul_plc (a : ∀ i, MonoidAlgebra ℂ (G i)) (i : ι) (b : MonoidAlgebra ℂ (G i)) :
    tens a * plc i b = tens (Function.update a i (a i * b)) := by
  unfold plc
  rw [tens_mul]
  congr 1
  funext j
  by_cases hj : j = i
  · subst hj
    simp
  · simp [Function.update_apply, hj]

theorem plc_central (i : ι) (a : MonoidAlgebra ℂ (G i)) (h : ∀ x, a * x = x * a)
    (x : MonoidAlgebra ℂ (∀ i, G i)) : plc i a * x = x * plc i a := by
  unfold plc
  refine tens_central _ (fun j y => ?_) x
  by_cases hj : j = i
  · subst hj
    simpa using h y
  · simp [Function.update_apply, hj]

theorem mapDomain_mulSingle (i : ι) (a : MonoidAlgebra ℂ (G i)) :
    MonoidAlgebra.ofCoeff (Finsupp.mapDomain (fun h => Pi.mulSingle (M := G) i h) a.coeff) = plc i a := by
  classical
  apply MonoidAlgebra.ext
  ext g
  rw [MonoidAlgebra.coeff_ofCoeff]
  unfold plc
  rw [tens_coeff]
  have h1 : ∀ (j : ι) (x : G j), (1 : MonoidAlgebra ℂ (G j)).coeff x = if (1 : G j) = x then 1 else 0 := by
    intro j x
    rw [show (1 : MonoidAlgebra ℂ (G j)).coeff = Finsupp.single 1 1 by
      first
      | rfl
      | exact SkewMonoidAlgebra.ofCoeff_eq_one.mp rfl
      | exact MonoidAlgebra.ofCoeff_eq_one.mp rfl, Finsupp.single_apply]
  have hinj : Function.Injective (fun h : G i => Pi.mulSingle (M := G) i h) := Pi.mulSingle_injective i
  by_cases hg : ∀ j, j ≠ i → g j = 1
  · have hgeq : g = Pi.mulSingle (M := G) i (g i) := by
      funext j
      by_cases hj : j = i
      · subst hj
        simp
      · rw [Pi.mulSingle_eq_of_ne hj, hg j hj]
    rw [hgeq, Finsupp.mapDomain_apply hinj, Fintype.prod_eq_single i]
    · simp
    · intro j hj
      rw [Pi.mulSingle_eq_of_ne hj]
      first | rw [Function.update_of_ne hj] | rw [Function.update_noteq hj]
      rw [h1, if_pos rfl]
  · push_neg at hg
    obtain ⟨j, hj, hgj⟩ := hg
    rw [Finsupp.mapDomain_notin_range]
    · symm
      refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
      first | rw [Function.update_of_ne hj] | rw [Function.update_noteq hj]
      rw [h1]
      exact if_neg (Ne.symm hgj)
    · rintro ⟨h, rfl⟩
      exact hgj (Pi.mulSingle_eq_of_ne hj h)

end Tensor

section Good

variable {ι : Type} [Fintype ι] [DecidableEq ι] {G : ι → Type} [∀ i, Group (G i)] [∀ i, Finite (G i)]
  {P : ι → Type} [∀ i, Fintype (P i)]

open Classical in

def eGood (E : ∀ i, P i → MonoidAlgebra ℂ (G i)) (good : (∀ i, P i) → Prop) :
    MonoidAlgebra ℂ (∀ i, G i) :=
  ∑ p : ∀ i, P i, if good p then tens (fun i => E i (p i)) else 0

variable (E : ∀ i, P i → MonoidAlgebra ℂ (G i)) (good : (∀ i, P i) → Prop)

theorem eGood_central (hcen : ∀ i p a, E i p * a = a * E i p) (x : MonoidAlgebra ℂ (∀ i, G i)) :
    eGood E good * x = x * eGood E good := by
  unfold eGood
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  split_ifs
  · exact tens_central _ (fun i y => hcen i (p i) y) x
  · simp

variable {W : Type} [AddCommGroup W] [Module ℂ W]

open Classical in

def onC {A : Type} [Ring A] [Algebra ℂ A] (Φ : Subalgebra.center ℂ A →ₐ[ℂ] Module.End ℂ W) (z : A) :
    Module.End ℂ W :=
  if h : z ∈ Subalgebra.center ℂ A then Φ ⟨z, h⟩ else 0

theorem onC_eGood (hid : ∀ i p, E i p * E i p = E i p) (hcen : ∀ i p a, E i p * a = a * E i p)
    (hsum : ∀ i, ∑ p, E i p = 1)
    (Φ : Subalgebra.center ℂ (MonoidAlgebra ℂ (∀ i, G i)) →ₐ[ℂ] Module.End ℂ W) (F : W) (lab : ∀ i, P i)
    (h : ∀ i p, p ≠ lab i → onC Φ (plc i (E i p)) F = 0) :
    (good lab → onC Φ (eGood E good) F = F) ∧ (¬ good lab → onC Φ (eGood E good) F = 0) := by
  classical
  have cen : ∀ p : (∀ i, P i),
      tens (fun i => E i (p i)) ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (∀ i, G i)) := by
    intro p
    rw [Subalgebra.mem_center_iff]
    intro y
    exact (tens_central _ (fun i x => hcen i (p i) x) y).symm
  have hz : ∀ w : W, onC Φ (0 : MonoidAlgebra ℂ (∀ i, G i)) w = 0 := by
    intro w
    unfold onC
    rw [dif_pos (Subalgebra.zero_mem _)]
    exact LinearMap.congr_fun (map_zero Φ) w
  have onC_mul : ∀ x y : MonoidAlgebra ℂ (∀ i, G i), x ∈ Subalgebra.center ℂ _ →
      y ∈ Subalgebra.center ℂ _ → ∀ w : W, onC Φ (x * y) w = onC Φ x (onC Φ y w) := by
    intro x y hx hy w
    unfold onC
    rw [dif_pos (Subalgebra.mul_mem _ hx hy), dif_pos hx, dif_pos hy, ← Module.End.mul_apply, ← map_mul]
    rfl
  have onC_sum : ∀ (s : Finset (∀ i, P i)) (f : (∀ i, P i) → MonoidAlgebra ℂ (∀ i, G i)),
      (∀ p, f p ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (∀ i, G i))) → ∀ w : W,
        onC Φ (∑ p ∈ s, f p) w = ∑ p ∈ s, onC Φ (f p) w := by
    intro s f hf w
    refine Finset.induction_on s ?_ ?_
    · simp only [Finset.sum_empty]
      exact hz w
    · intro a s ha ih
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
      have h1 := hf a
      have h2 : ∑ p ∈ s, f p ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (∀ i, G i)) :=
        sum_mem (fun p _ => hf p)
      unfold onC
      rw [dif_pos (add_mem h1 h2), dif_pos h1, dif_pos h2, ← LinearMap.add_apply, ← map_add]
      rfl
  have hone : ∑ p : (∀ i, P i), tens (fun i => E i (p i)) = 1 := by
    rw [sum_tens]
    simp only [hsum]
    exact tens_one
  have hzero : ∀ p : (∀ i, P i), p ≠ lab → onC Φ (tens (fun i => E i (p i))) F = 0 := by
    intro p hp
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hp
    have hfix : tens (fun j => E j (p j)) = tens (fun j => E j (p j)) * plc i (E i (p i)) := by
      rw [tens_mul_plc]
      simp only [hid]
      congr 1
      funext j
      by_cases hj : j = i <;> simp [Function.update_apply, hj]
    have hcp : plc i (E i (p i)) ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (∀ i, G i)) := by
      rw [Subalgebra.mem_center_iff]
      intro y
      exact (plc_central i _ (hcen i (p i)) y).symm
    rw [hfix, onC_mul _ _ (hfix ▸ cen p) hcp, h i (p i) hi, map_zero]
  have hlab : onC Φ (tens (fun i => E i (lab i))) F = F := by
    have h1 : onC Φ (∑ p : (∀ i, P i), tens (fun i => E i (p i))) F = F := by
      rw [hone]
      unfold onC
      rw [dif_pos (Subalgebra.one_mem _)]
      exact LinearMap.congr_fun (map_one Φ) F
    rw [onC_sum Finset.univ (fun p => tens (fun i => E i (p i))) cen F, Finset.sum_eq_single lab] at h1
    · exact h1
    · intro p _ hp
      exact hzero p hp
    · intro hl
      exact absurd (Finset.mem_univ _) hl
  have hmain : onC Φ (eGood E good) F = if good lab then F else 0 := by
    have hs := onC_sum Finset.univ (fun p => if good p then tens (fun i => E i (p i)) else 0)
      (fun p => by
        split_ifs
        · exact cen p
        · exact Subalgebra.zero_mem _) F
    unfold eGood
    rw [hs, Finset.sum_eq_single lab]
    · split_ifs <;> simp [hlab, hz]
    · intro p _ hp
      split_ifs <;> simp [hzero p hp, hz]
    · intro hl
      exact absurd (Finset.mem_univ _) hl
  constructor
  · intro hg
    rw [hmain, if_pos hg]
  · intro hg
    rw [hmain, if_neg hg]

end Good

section Record

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Polynomial

variable (D : D7)

local instance factG (k : Fin 2) : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩

local instance neZeroG (k : Fin 2) : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩

def ESer (kv : Σ k : Fin 2, D.nd.PlG k) (p : Fin D.R.r → ZMod (D.host.g kv.1)) :
    MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :=
  D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf p)

def goodVec (p : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fin D.R.r → ZMod (D.host.g kv.1)) : Prop :=
  D.ntypes.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (p ⟨k, v⟩))

private theorem monicOf_coeff_lemma {K : Type} [Field K] {N : ℕ} (a : Fin N → K) (i : Fin N) :
    (Formalism.CyclotomicNorms.monicOf a).coeff i = a i := by
  unfold Formalism.CyclotomicNorms.monicOf
  rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, if_neg (Nat.ne_of_lt i.isLt), zero_add,
    Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [if_neg]
    exact fun h => hj (Fin.ext h).symm
  · simp

theorem monicOf_inj {K : Type} [Field K] {N : ℕ} (a b : Fin N → K)
    (h : Formalism.CyclotomicNorms.monicOf a = Formalism.CyclotomicNorms.monicOf b) : a = b := by
  funext i
  rw [← monicOf_coeff_lemma a i, ← monicOf_coeff_lemma b i, h]

theorem ESer_idem (kv) (p) : ESer D kv p * ESer D kv p = ESer D kv p := by
  unfold ESer
  exact D.ntypes.eSer_idem _ _

theorem ESer_central (kv) (p) (a) : ESer D kv p * a = a * ESer D kv p := by
  unfold ESer
  exact D.ntypes.eSer_central _ _ _

theorem ESer_sum (kv : Σ k : Fin 2, D.nd.PlG k) : ∑ p, ESer D kv p = 1 := by
  classical
  obtain ⟨S, hS, hsum⟩ := D.ntypes.eSer_sum kv.1
  rw [← hsum]
  have himg : ∑ p, ESer D kv p =
      ∑ f ∈ Finset.univ.image (fun p : Fin D.R.r → ZMod (D.host.g kv.1) => Formalism.CyclotomicNorms.monicOf p),
        D.ntypes.eSer kv.1 f := by
    rw [Finset.sum_image fun a _ b _ h => monicOf_inj a b h]
    rfl
  rw [himg]
  symm
  refine Finset.sum_subset (fun f hf => ?_) fun f _ hf => ?_
  · obtain ⟨hm, hd, -⟩ := (hS f).1 hf
    exact Finset.mem_image.2 ⟨_, Finset.mem_univ _, Formalism.CyclotomicNorms.Sqf.monicOf_coeffs f hm hd⟩
  · exact D.ntypes.eSer_zero _ _ fun hh => hf ((hS f).2 hh)

variable [DecidableEq (Σ k : Fin 2, D.nd.PlG k)]

private theorem coeff_sum_lemma_3 {M ι : Type} (s : Finset ι) (f : ι → MonoidAlgebra ℂ M) (g : M) :
    (∑ i ∈ s, f i).coeff g = ∑ i ∈ s, (f i).coeff g :=
  map_sum (AddMonoidHom.mk' (fun x : MonoidAlgebra ℂ M => x.coeff g) (fun x y => by first | rfl | simp)) f s

theorem e0_eq : D.ntypes.e0 = eGood (ESer D) (goodVec D) := by
  classical
  apply MonoidAlgebra.ext
  ext g
  have h1 : D.ntypes.e0.coeff g = ∑ᶠ p : (∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fin D.R.r → ZMod (D.host.g kv.1)),
      if goodVec D p then ∏ kv, (ESer D kv (p kv)).coeff (g kv) else 0 := by
    first
    | rfl
    | (unfold Formalism.BasicNotions.NTypes.e0; rfl)
  rw [h1, finsum_eq_sum_of_fintype]
  unfold eGood
  rw [coeff_sum_lemma_3]
  refine Finset.sum_congr (by first | rfl | (congr 1; exact Subsingleton.elim _ _) | convert rfl) (fun p _ => ?_)
  split_ifs <;> rfl

open Classical in

theorem typeIdempotent_coeff_across_layers (g : G0g D.nd) :
    D.ntypes.e0.coeff g = ∑ p : (∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fin D.R.r → ZMod (D.host.g kv.1)),
      if goodVec D p then ∏ kv, (ESer D kv (p kv)).coeff (g kv) else 0 := by
  rw [e0_eq D]
  unfold eGood
  rw [coeff_sum_lemma_3]
  refine Finset.sum_congr (by first | rfl | (congr 1; exact Subsingleton.elim _ _) | convert rfl) (fun p _ => ?_)
  split_ifs <;> rfl

theorem atPlace_eq (k : Fin 2) (v : D.nd.PlG k) (a : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k)))) :
    ArithmeticCylinders.atPlace D k v a =
      plc (G := fun kv : (Σ k : Fin 2, D.nd.PlG k) => GL (Fin D.R.r) (ZMod (D.host.g kv.1))) ⟨k, v⟩ a := by
  unfold Formalism.MainNotions.ArithmeticCylinders.atPlace
  convert mapDomain_mulSingle
    (G := fun kv : (Σ k : Fin 2, D.nd.PlG k) => GL (Fin D.R.r) (ZMod (D.host.g kv.1))) ⟨k, v⟩ a
    <;> first | rfl | exact Subsingleton.elim _ _

end Record

section Record2

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Polynomial

variable (D : D7)

local instance factG' (k : Fin 2) : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩

local instance neZeroG' (k : Fin 2) : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩

theorem goodElement_mem_center_groupAlgebra (a : MonoidAlgebra ℂ (G0g D.nd)) : D.ntypes.e0 * a = a * D.ntypes.e0 := by
  classical
  rw [e0_eq D]
  exact eGood_central _ _ (ESer_central D) a

def labVec (σ' : D.ntypes.Par) (kv : Σ k : Fin 2, D.nd.PlG k) : Fin D.R.r → ZMod (D.host.g kv.1) :=
  fun i => (D.ntypes.labPar kv.1 σ' kv.2).coeff i

theorem monicOf_labVec (σ' : D.ntypes.Par) (kv : Σ k : Fin 2, D.nd.PlG k) :
    Formalism.CyclotomicNorms.monicOf (labVec D σ' kv) = D.ntypes.labPar kv.1 σ' kv.2 :=
  Formalism.CyclotomicNorms.Sqf.monicOf_coeffs _ (D.ntypes.labPar_monic _ _ _).1 (D.ntypes.labPar_monic _ _ _).2

theorem goodVec_labVec (σ' : D.ntypes.Par) : goodVec D (labVec D σ') ↔ D.ntypes.goodPar σ' := by
  unfold goodVec
  have e : (fun k v => Formalism.CyclotomicNorms.monicOf (labVec D σ' ⟨k, v⟩)) = (fun k v => D.ntypes.labPar k σ' v) :=
    funext fun k => funext fun v => monicOf_labVec D σ' ⟨k, v⟩
  exact Iff.of_eq (congrArg D.ntypes.goodTuple e)

theorem idempotent_action_on_forms {W : Type} [AddCommGroup W] [Module ℂ W]
    (Φ : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)) →ₐ[ℂ] Module.End ℂ W) (σ' : D.ntypes.Par) (F : W)
    (h : ∀ (k : Fin 2) (v : D.nd.PlG k) (f : (ZMod (D.host.g k))[X]),
      onC Φ (ArithmeticCylinders.atPlace D k v (D.ntypes.eSer k f)) F ≠ 0 → f = D.ntypes.labPar k σ' v) :
    (D.ntypes.goodPar σ' → onC Φ D.ntypes.e0 F = F) ∧ (¬ D.ntypes.goodPar σ' → onC Φ D.ntypes.e0 F = 0) := by
  classical
  have key := onC_eGood (ESer D) (goodVec D) (ESer_idem D) (ESer_central D) (ESer_sum D) Φ F
    (labVec D σ') ?_
  · rw [e0_eq D]
    rw [goodVec_labVec] at key
    exact key
  · rintro ⟨k, v⟩ p hp
    by_contra hne
    apply hp
    have h' := h k v (Formalism.CyclotomicNorms.monicOf p) (by rwa [atPlace_eq])
    apply monicOf_inj
    rw [h', monicOf_labVec]

end Record2

section ClauseA

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Polynomial

theorem pp_arith (l n : ℕ) (hl : l.Prime) (hn : 0 < n) :
    l ^ n.factorization l * (((l ^ n.factorization l : ℕ) : ZMod (n / l ^ n.factorization l))⁻¹).val ≡
      (ordProj[l] n) ^ Nat.totient (ordCompl[l] n) [MOD n] := by
  set P := l ^ n.factorization l with hP
  set Q := n / P with hQdef
  have hPQ : P * Q = n := Nat.ordProj_mul_ordCompl_eq_self n l
  have hQpos : 0 < Q := by
    rcases Nat.eq_zero_or_pos Q with h | h
    · rw [h, mul_zero] at hPQ
      omega
    · exact h
  have hcop : Nat.Coprime P Q := (Nat.coprime_ordCompl hl hn.ne').pow_left _
  haveI : NeZero Q := ⟨hQpos.ne'⟩
  have htot : 0 < Nat.totient Q := by
    first
    | exact Nat.totient_pos.mpr hQpos
    | exact Nat.totient_pos hQpos
  rw [← hPQ]
  refine (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨?_, ?_⟩
  · have h1 : P ∣ P * ((P : ZMod Q)⁻¹).val := dvd_mul_right _ _
    have h2 : P ∣ P ^ Nat.totient Q := dvd_pow_self P htot.ne'
    exact (Nat.modEq_zero_iff_dvd.mpr h1).trans (Nat.modEq_zero_iff_dvd.mpr h2).symm
  · have h1 : P * ((P : ZMod Q)⁻¹).val ≡ 1 [MOD Q] := by
      first
      | rw [← ZMod.natCast_eq_natCast_iff]
      | rw [← ZMod.eq_iff_modEq_nat]
      rw [Nat.cast_mul, ZMod.natCast_zmod_val, Nat.cast_one]
      exact ZMod.coe_mul_inv_eq_one P hcop
    exact h1.trans (Nat.ModEq.pow_totient hcop).symm

theorem pp_eq {M : Type*} [Monoid M] (l : ℕ) (hl : l.Prime) (x : M) (hx : IsOfFinOrder x) :
    Formalism.CyclotomicNorms.primeToPart l x = Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.primeToPart l x := by
  have h := pp_arith l (orderOf x) hl hx.orderOf_pos
  unfold Formalism.CyclotomicNorms.primeToPart Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.primeToPart
  exact (pow_mod_orderOf x _).symm.trans ((congrArg (x ^ ·) h).trans (pow_mod_orderOf x _))

section GoodTr

variable {g : ℕ} [Fact g.Prime]

theorem mem_rootSet_iff (f : (ZMod g)[X]) (x : Formalism.CyclotomicNorms.Fbar g) :
    x ∈ f.rootSet (Formalism.CyclotomicNorms.Fbar g) ↔ x ∈ Formalism.CyclotomicNorms.rootsBar f := by
  unfold Formalism.CyclotomicNorms.rootsBar
  simp [Polynomial.mem_rootSet, Polynomial.aroots_def]

theorem root_ne_zero {f : (ZMod g)[X]} (h0 : f.coeff 0 ≠ 0) {x : Formalism.CyclotomicNorms.Fbar g}
    (hx : x ∈ Formalism.CyclotomicNorms.rootsBar f) : x ≠ 0 := by
  intro hx0
  subst hx0
  unfold Formalism.CyclotomicNorms.rootsBar at hx
  have hne : f.map (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)) ≠ 0 := by
    intro h
    rw [h] at hx
    simp at hx
  have hr := (Polynomial.mem_roots hne).mp hx
  rw [Polynomial.IsRoot.def, ← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map] at hr
  exact h0 ((map_eq_zero_iff _ (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)).injective).mp hr)

def bigM (g N : ℕ) : ℕ := ∏ d ∈ Finset.Icc 1 N, (g ^ d - 1)

omit [Fact g.Prime] in
theorem bigM_pos (hg : 2 ≤ g) (N : ℕ) : 0 < bigM g N := by
  unfold bigM
  apply Finset.prod_pos
  intro d hd
  have h1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
  have h2 : 1 < g ^ d := by
    first
    | exact Nat.one_lt_pow (by omega) (by omega)
    | exact Nat.one_lt_pow _ _ (by omega) (by omega)
    | exact one_lt_pow₀ (by omega) (by omega)
  first
  | exact Nat.sub_pos_of_lt h2
  | omega

theorem root_pow {N : ℕ} {f : (ZMod g)[X]} (h0 : f.coeff 0 ≠ 0) (hd : f.natDegree = N)
    {x : Formalism.CyclotomicNorms.Fbar g} (hx : x ∈ Formalism.CyclotomicNorms.rootsBar f) : x ^ bigM g N = 1 := by
  classical
  have hx0 : x ≠ 0 := root_ne_zero h0 hx
  have hf0 : f ≠ 0 := fun h => h0 (by rw [h, Polynomial.coeff_zero])
  have hroot : Polynomial.aeval x f = 0 := ((Polynomial.mem_rootSet).mp ((mem_rootSet_iff f x).mpr hx)).2
  have hint : IsIntegral (ZMod g) x := (show IsAlgebraic (ZMod g) x from ⟨f, hf0, hroot⟩).isIntegral
  have hd1 : 1 ≤ (minpoly (ZMod g) x).natDegree := minpoly.natDegree_pos hint
  have hdN : (minpoly (ZMod g) x).natDegree ≤ N := by
    rw [← hd]
    exact Polynomial.natDegree_le_of_dvd (minpoly.dvd _ _ hroot) hf0
  haveI : FiniteDimensional (ZMod g) (IntermediateField.adjoin (ZMod g) ({x} : Set (Formalism.CyclotomicNorms.Fbar g))) :=
    IntermediateField.adjoin.finiteDimensional hint
  haveI : Finite (IntermediateField.adjoin (ZMod g) ({x} : Set (Formalism.CyclotomicNorms.Fbar g))) :=
    Module.finite_of_finite (ZMod g)
  letI : Fintype (IntermediateField.adjoin (ZMod g) ({x} : Set (Formalism.CyclotomicNorms.Fbar g))) := Fintype.ofFinite _
  have hcard : Fintype.card (IntermediateField.adjoin (ZMod g) ({x} : Set (Formalism.CyclotomicNorms.Fbar g))) =
      g ^ (minpoly (ZMod g) x).natDegree := by
    first
    | rw [Module.card_eq_pow_finrank (K := ZMod g), ZMod.card, IntermediateField.adjoin.finrank hint]
    | rw [card_eq_pow_finrank (K := ZMod g), ZMod.card, IntermediateField.adjoin.finrank hint]
  have hy : (⟨x, IntermediateField.mem_adjoin_simple_self (ZMod g) x⟩ :
      IntermediateField.adjoin (ZMod g) ({x} : Set (Formalism.CyclotomicNorms.Fbar g))) ≠ 0 := by
    intro h
    apply hx0
    exact congrArg Subtype.val h
  have hp := FiniteField.pow_card_sub_one_eq_one _ hy
  rw [hcard] at hp
  have hxp : x ^ (g ^ (minpoly (ZMod g) x).natDegree - 1) = 1 := by
    have := congrArg (fun z : IntermediateField.adjoin (ZMod g) ({x} : Set (Formalism.CyclotomicNorms.Fbar g)) =>
      (z : Formalism.CyclotomicNorms.Fbar g)) hp
    simpa using this
  have hdvd : g ^ (minpoly (ZMod g) x).natDegree - 1 ∣ bigM g N :=
    Finset.dvd_prod_of_mem (fun d => g ^ d - 1) (Finset.mem_Icc.mpr ⟨hd1, hdN⟩)
  obtain ⟨c, hc⟩ := hdvd
  rw [hc, pow_mul, hxp, one_pow]

theorem root_finOrd {N : ℕ} {f : (ZMod g)[X]} (h0 : f.coeff 0 ≠ 0) (hd : f.natDegree = N)
    {x : Formalism.CyclotomicNorms.Fbar g} (hx : x ∈ Formalism.CyclotomicNorms.rootsBar f) : IsOfFinOrder x :=
  isOfFinOrder_iff_pow_eq_one.mpr ⟨bigM g N, bigM_pos (Fact.out : g.Prime).two_le N, root_pow h0 hd hx⟩

theorem BB_iff (N l : ℕ) : l ∈ Formalism.CyclotomicNorms.BB N g ↔ l ∈ Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.BB g N := by
  constructor
  · intro h
    exact Finset.mem_coe.mp (CuspidalLatticeIdempotents.algBB_sub g N (Fact.out : g.Prime).two_le h)
  · intro h
    rcases (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.mem_BB_iff g N l).mp h with h | ⟨-, hp, d, hd, hlt⟩
    · exact Or.inl h
    · exact Or.inr ⟨d, (Finset.mem_Icc.mp hd).1, (Finset.mem_Icc.mp hd).2, hp, hlt⟩

theorem good_of {PP J : Type} (N : ℕ) (f : PP → (ZMod g)[X]) (χ : PP → J → (ZMod g)ˣ)
    (h : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.GoodAt (ZMod g) (Formalism.CyclotomicNorms.Fbar g) N f χ) :
    Formalism.CyclotomicNorms.IsGood N g f χ ∧ Formalism.CyclotomicNorms.IsGood N g f (fun v j => (χ v j)⁻¹) := by
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := h
  have hfo : ∀ v, ∀ x ∈ Formalism.CyclotomicNorms.rootsBar (f v), IsOfFinOrder x := fun v x hx =>
    root_finOrd (a0 v).2.2 (a0 v).2.1 hx
  have c2 : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ Formalism.CyclotomicNorms.BB N g → ∀ v, ∀ x ∈ Formalism.CyclotomicNorms.rootsBar (f v),
      ∀ y ∈ Formalism.CyclotomicNorms.rootsBar (f v), Formalism.CyclotomicNorms.primeToPart ℓ x = Formalism.CyclotomicNorms.primeToPart ℓ y → x = y := by
    intro l hl hBB v x hx y hy hxy
    rw [pp_eq l hl x (hfo v x hx), pp_eq l hl y (hfo v y hy)] at hxy
    refine a2 l hl ?_ v ((mem_rootSet_iff _ _).mpr hx) ((mem_rootSet_iff _ _).mpr hy) hxy
    rw [ZMod.card]
    exact fun h => hBB ((BB_iff N l).mpr h)
  have c3 := fun (l : ℕ) (hl : l.Prime) (hne : l ≠ g) v j x (hx : x ∈ Formalism.CyclotomicNorms.rootsBar (f v)) =>
    a3 l hl (by rw [ZMod.card]; exact hne) v j x ((mem_rootSet_iff _ _).mpr hx)
  refine ⟨⟨a0, a1, c2, ?_, a4, a5⟩, ⟨a0, a1, c2, ?_, a4, a5⟩⟩
  · intro l hl hne v j x hx
    rw [pp_eq l hl x (hfo v x hx), pp_eq l hl _ (Formalism.MainNotions.AdmissibleThreePrime.isOfFinOrder_alg (χ v j))]
    exact (c3 l hl hne v j x hx).1
  · intro l hl hne v j x hx
    rw [pp_eq l hl x (hfo v x hx), pp_eq l hl _ (Formalism.MainNotions.AdmissibleThreePrime.isOfFinOrder_alg (χ v j)⁻¹)]
    exact (c3 l hl hne v j x hx).2

end GoodTr

theorem exists_exp (τ : ℂ ≃+* ℂ) (n : ℕ) (hn : 0 < n) :
    ∃ a : ℕ, a.Coprime n ∧ ∀ z : ℂ, z ^ n = 1 → τ z = z ^ a := by
  haveI : NeZero n := ⟨hn.ne'⟩
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ n := ⟨_, Complex.isPrimitiveRoot_exp n hn.ne'⟩
  have hτζ : IsPrimitiveRoot (τ ζ) n := by
    first
    | exact hζ.map_of_injective τ.injective
    | exact hζ.map_of_injective (f := τ) τ.injective
    | exact hζ.map_of_injective (f := (τ : ℂ →+* ℂ)) τ.injective
  have hpow : ∀ ξ : ℂ, ξ ^ n = 1 → ∃ i : ℕ, ζ ^ i = ξ := by
    intro ξ hξ
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hξ
    exact ⟨i, hi⟩
  obtain ⟨a, ha⟩ := hpow (τ ζ) hτζ.pow_eq_one
  have hcop : a.Coprime n := by
    have h' : IsPrimitiveRoot (ζ ^ a) n := by rw [ha]; exact hτζ
    first
    | exact (hζ.pow_iff_coprime hn a).mp h'
    | exact (hζ.pow_iff_coprime hn.ne' a).mp h'
  refine ⟨a, hcop, fun z hz => ?_⟩
  obtain ⟨k, rfl⟩ := hpow z hz
  rw [map_pow, ← ha]
  first
  | ring
  | rw [← pow_mul, ← pow_mul, mul_comm]

end ClauseA

section DualAmb

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Polynomial

section Poly

variable {g : ℕ} [Fact g.Prime]

end Poly

variable (D : D7)

local instance factGd (k : Fin 2) : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩

local instance neZeroGd (k : Fin 2) : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩

def dualT (σ' : D.ntypes.Par) (k : Fin 2) (v : D.nd.PlG k) : (ZMod (D.host.g k))[X] :=
  ArithmeticCylinders.dualLab D k (D.ntypes.labPar k σ' v)

def dualVec (σ' : D.ntypes.Par) (kv : Σ k : Fin 2, D.nd.PlG k) : Fin D.R.r → ZMod (D.host.g kv.1) :=
  fun i => (dualT D σ' kv.1 kv.2).coeff i

end DualAmb

section RecordA

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Polynomial

variable (D : D7)

local instance factG'' (k : Fin 2) : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩

local instance neZeroG'' (k : Fin 2) : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩

theorem teich_zero (k : Fin 2) : D.ntypes.teichC k 0 = 0 := by
  classical
  by_contra h
  have h1 : ∀ x, D.ntypes.teichC k x = 1 := by
    intro x
    have h2 : D.ntypes.teichC k 0 * D.ntypes.teichC k x = D.ntypes.teichC k 0 := by
      rw [← map_mul, zero_mul]
    exact mul_left_cancel₀ h (by rw [h2, mul_one])
  obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset (Formalism.CyclotomicNorms.Fbar (D.host.g k)))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy
  exact hy.2 (D.ntypes.teichC_inj k y 1 hy.1 one_ne_zero (by rw [h1 y, h1 1]))

theorem teich_ne_zero (k : Fin 2) (x : Formalism.CyclotomicNorms.Fbar (D.host.g k)) (hx : x ≠ 0) :
    D.ntypes.teichC k x ≠ 0 := by
  intro h
  have h1 : D.ntypes.teichC k x * D.ntypes.teichC k x⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hx, map_one]
  rw [h, zero_mul] at h1
  exact zero_ne_one h1

theorem teich_inj (k : Fin 2) : Function.Injective (D.ntypes.teichC k) := by
  intro x y hxy
  by_cases hx : x = 0
  · by_cases hy : y = 0
    · rw [hx, hy]
    · rw [hx, teich_zero] at hxy
      exact absurd hxy.symm (teich_ne_zero D k y hy)
  · by_cases hy : y = 0
    · rw [hy, teich_zero] at hxy
      exact absurd hxy (teich_ne_zero D k x hx)
    · exact D.ntypes.teichC_inj k x y hx hy hxy

def ActsBy (τ : ℂ ≃+* ℂ) (k : Fin 2) (a : ℕ) : Prop :=
  ∀ z : ℂ, z ^ bigM (D.host.g k) D.R.r = 1 → τ z = z ^ a

variable {D}

variable (D)

def actVec (τ : ℂ ≃+* ℂ) (p : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fin D.R.r → ZMod (D.host.g kv.1)) :
    ∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fin D.R.r → ZMod (D.host.g kv.1) :=
  fun kv i => (ArithmeticCylinders.labAct D τ kv.1 (Formalism.CyclotomicNorms.monicOf (p kv))).coeff i

variable {D}

variable (D)

end RecordA

end Formalism.MainNotions.N.PlaceLabelTeichmuller
