import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistAlg
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StInterNumAdditive
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StInterNumEventual
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StInterSumTopVanish
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.InterSumEventuallyEqInterNum
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

section Monoid

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

abbrev twistMonoid : CommMonoid (SubSystem S x Ω) where
  mul F Q := F.twist Q
  one := twistSys S x 0
  mul_assoc F P Q := SubSystem.twist_assoc F P Q
  one_mul F := twistSys_zero_twist F
  mul_one F := SubSystem.twist_twistSys_zero F
  mul_comm F Q := SubSystem.twist_comm F Q

attribute [local instance] twistMonoid

theorem foldl_twist_eq_mul {n : ℕ} (L : Fin n → SubSystem S x Ω) (l : List (Fin n)) (F : SubSystem S x Ω) :
    l.foldl (fun F i => F.twist (L i)) F = F * (l.map L).prod := by
  induction l generalizing F with
  | nil => exact (mul_one F).symm
  | cons a l ih =>
    rw [List.foldl_cons, ih, List.map_cons, List.prod_cons, ← mul_assoc]
    rfl

theorem prod_map_filter {α M : Type*} [CommMonoid M] (p : α → Bool) (f : α → M) (l : List α) :
    ((l.filter p).map f).prod = (l.map fun a => if p a then f a else 1).prod := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h : p a
    · simp [h, ih]
    · simp [h, ih]

theorem tensorSub_eq_prod {n : ℕ} (L : Fin n → SubSystem S x Ω) (T : Finset (Fin n)) :
    tensorSub L T = ∏ j ∈ T, L j := by
  unfold tensorSub
  rw [foldl_twist_eq_mul]
  change 1 * _ = _
  rw [one_mul, prod_map_filter, ← Fin.prod_univ_def, ← Finset.prod_filter]
  congr 1
  ext j
  simp

end Monoid

section MixDiff

theorem powerset_map_emb {α β : Type*} (e : α ↪ β) (s : Finset α) :
    (s.map e).powerset = s.powerset.map (Finset.mapEmbedding e).toEmbedding := by
  ext T
  simp only [Finset.mem_powerset, Finset.mem_map, Finset.subset_map_iff, RelEmbedding.coe_toEmbedding,
    Finset.mapEmbedding_apply]
  constructor
  · rintro ⟨u, hu, rfl⟩; exact ⟨u, hu, rfl⟩
  · rintro ⟨u, hu, rfl⟩; exact ⟨u, hu, rfl⟩

variable {G : Type*} [CommMonoid G]

def mixDiff (f : G → ℤ) {n : ℕ} (L : Fin n → G) : ℤ :=
  ∑ T : Finset (Fin n), (-1) ^ (n - T.card) * f (∏ j ∈ T, L j)

theorem mixDiff_snoc (f : G → ℤ) {m : ℕ} (L : Fin m → G) (X : G) :
    mixDiff f (Fin.snoc (α := fun _ => G) L X) = mixDiff (fun g => f (X * g)) L - mixDiff f L := by
  classical
  unfold mixDiff
  rw [← Finset.powerset_univ, ← Finset.powerset_univ, Fin.univ_castSuccEmb, Finset.cons_eq_insert,
    Finset.sum_powerset_insert (by simp), powerset_map_emb, Finset.sum_map, Finset.sum_map,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun U _ => ?_
  have hU : U.card ≤ m := by simpa using U.card_le_univ
  have hlast : Fin.last m ∉ U.map Fin.castSuccEmb := by simp [Fin.castSucc_ne_last]
  have hp : ∏ j ∈ U.map Fin.castSuccEmb, Fin.snoc (α := fun _ => G) L X j = ∏ j ∈ U, L j := by
    rw [Finset.prod_map]
    simp
  simp only [RelEmbedding.coe_toEmbedding, Finset.mapEmbedding_apply, Finset.card_insert_of_notMem hlast,
    Finset.card_map, Finset.prod_insert hlast, hp, Fin.snoc_last]
  rw [show m + 1 - U.card = m - U.card + 1 by omega, show m + 1 - (U.card + 1) = m - U.card by omega, pow_succ]
  ring

theorem mixDiff_snoc_mul (f : G → ℤ) {m : ℕ} (L : Fin m → G) (X Y : G) :
    mixDiff f (Fin.snoc (α := fun _ => G) L (X * Y)) =
      mixDiff f (Fin.snoc (α := fun _ => G) L X) + mixDiff f (Fin.snoc (α := fun _ => G) L Y) +
        mixDiff f (Fin.snoc (α := fun _ => G) (Fin.snoc (α := fun _ => G) L X) Y) := by
  simp only [mixDiff_snoc]
  have h : mixDiff (fun g => f (Y * (X * g))) L = mixDiff (fun g => f (X * Y * g)) L := by
    congr 1
    funext g
    rw [mul_left_comm, mul_assoc]
  simp only [h]
  ring

end MixDiff

section Main

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

attribute [local instance] twistMonoid

theorem interSum_eq_mixDiff (pp : Ideal (Poly S N)) {n : ℕ} (L : Fin n → SubSystem S x Ω) (c : ℕ) :
    interSum pp L c = mixDiff (fun F => restrLen pp (F.twist (twistSys S x (c : ℤ)))) L := by
  unfold interSum mixDiff
  simp only [tensorSub_eq_prod]

end Main

attribute [local instance] twistMonoid

theorem InterNumAdditive.proof (hE : InterNumEventual.Statement.{u, w})
    (hZ : InterSumTopVanish.Statement.{u, w}) : InterNumAdditive.Statement.{u, w} := by
  intro k _ Ω _ _ N x n pp L i L' L'' hW
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := i.pos; omega⟩
  set σ := Equiv.swap i (Fin.last m) with hσ
  set L₀ : Fin m → LineBundle k x := fun j => L (σ (Fin.castSucc j)) with hL₀

  have hfam : ∀ B : LineBundle k x, Function.update (fun j => (L j).toSubSystem) i B.toSubSystem =
      fun j => (Function.update L i B j).toSubSystem := fun B => by
    funext j
    exact (Function.apply_update (fun _ B => B.toSubSystem) L i B j).symm

  have hmove : ∀ (Y : SubSystem k x Ω) (c : ℕ),
      interSum pp (Function.update (fun j => (L j).toSubSystem) i Y) c =
        interSum pp (Fin.snoc (α := fun _ => SubSystem k x Ω) (fun j => (L₀ j).toSubSystem) Y) c := by
    intro Y c
    rw [← interSum_comp_perm pp _ σ c]
    congr 1
    funext j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp [hσ]
    · have hne : σ (Fin.castSucc j) ≠ i := by
        rw [hσ, Ne, Equiv.swap_apply_eq_iff, Equiv.swap_apply_left]
        exact Fin.castSucc_ne_last j
      simp [Function.update_of_ne hne, hL₀]

  have hev : ∀ B : LineBundle k x, ∀ᶠ c : ℕ in atTop,
      interSum pp (Function.update (fun j => (L j).toSubSystem) i B.toSubSystem) c =
        interNum pp (Function.update (fun j => (L j).toSubSystem) i B.toSubSystem) := fun B => by
    obtain ⟨a, ha⟩ := hE k Ω N x (m + 1) pp (Function.update L i B) hW
    rw [hfam B]
    exact interSum_eventually_eq_interNum pp _ ha
  have hz := hZ k Ω N x (m + 1) pp
    (Fin.snoc (α := fun _ => LineBundle k x) (Fin.snoc (α := fun _ => LineBundle k x) L₀ L') L'') hW
  obtain ⟨c, h1, h2, h3, h4⟩ :=
    ((hev (L'.tensorProd L'')).and ((hev L').and ((hev L'').and hz))).exists
  have hs : (fun j => (Fin.snoc (α := fun _ => LineBundle k x)
      (Fin.snoc (α := fun _ => LineBundle k x) L₀ L') L'' j).toSubSystem) =
      Fin.snoc (α := fun _ => SubSystem k x Ω) (Fin.snoc (α := fun _ => SubSystem k x Ω)
        (fun j => (L₀ j).toSubSystem) L'.toSubSystem) L''.toSubSystem := by
    have e1 := Fin.comp_snoc (fun B : LineBundle k x => B.toSubSystem)
      (Fin.snoc (α := fun _ => LineBundle k x) L₀ L') L''
    have e2 := Fin.comp_snoc (fun B : LineBundle k x => B.toSubSystem) L₀ L'
    simp only [Function.comp_def] at e1 e2
    rw [e1, e2]
  have key := mixDiff_snoc_mul (fun F => restrLen pp (F.twist (twistSys k x (c : ℤ))))
    (fun j => (L₀ j).toSubSystem) L'.toSubSystem L''.toSubSystem
  rw [← interSum_eq_mixDiff, ← interSum_eq_mixDiff, ← interSum_eq_mixDiff, ← interSum_eq_mixDiff, ← hs, h4,
    add_zero, ← hmove, ← hmove, ← hmove] at key
  have e : (L'.tensorProd L'').toSubSystem = L'.toSubSystem.twist L''.toSubSystem := rfl
  rw [e] at h1
  rw [← h1, ← h2, ← h3]
  exact key

end

end GroundTheory.Heights₂.Heights.Kleiman
