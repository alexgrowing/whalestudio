import Mathlib
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CapelliDeterminantBlockProduct
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds

open Finset CompanionTheory.D.DSIC

noncomputable section

namespace GlobalTheory.CompanionTheory.DSICFRel

def bil {ι A : Type} [Fintype ι] [Ring A] [Algebra ℂ A] (c a : ι → A) (m : ι → ι → ℂ) : A :=
  ∑ i, ∑ j, m i j • (c i * a j)

theorem pair_comm {ι A : Type} [DecidableEq ι] [Ring A] (c a : ι → A)
    (haa : ∀ i j, a i * a j + a j * a i = 0) (hcc : ∀ i j, c i * c j + c j * c i = 0)
    (hac : ∀ i j, a i * c j + c j * a i = if i = j then 1 else 0) (i j k l : ι) :
    (c i * a j) * (c k * a l) - (c k * a l) * (c i * a j) =
      (if j = k then c i * a l else 0) - (if l = i then c k * a j else 0) := by
  have h1 : a j * c k = (if j = k then 1 else 0) - c k * a j := eq_sub_of_add_eq (hac j k)
  have h2 : a l * c i = (if l = i then 1 else 0) - c i * a l := eq_sub_of_add_eq (hac l i)
  have h3 : c k * c i = - (c i * c k) := eq_neg_of_add_eq_zero_left (hcc k i)
  have h4 : a l * a j = - (a j * a l) := eq_neg_of_add_eq_zero_left (haa l j)
  have e1 : (c i * a j) * (c k * a l) = (if j = k then c i * a l else 0) - (c i * c k) * (a j * a l) := by
    rw [mul_assoc, ← mul_assoc (a j), h1]
    split_ifs <;> noncomm_ring
  have e2 : (c k * a l) * (c i * a j) = (if l = i then c k * a j else 0) - (c k * c i) * (a l * a j) := by
    rw [mul_assoc, ← mul_assoc (a l), h2]
    split_ifs <;> noncomm_ring
  rw [e1, e2, h3, h4]
  noncomm_ring

theorem bil_comm {ι A : Type} [Fintype ι] [DecidableEq ι] [Ring A] [Algebra ℂ A] (c a : ι → A)
    (haa : ∀ i j, a i * a j + a j * a i = 0) (hcc : ∀ i j, c i * c j + c j * c i = 0)
    (hac : ∀ i j, a i * c j + c j * a i = if i = j then 1 else 0) (m m' : ι → ι → ℂ) :
    bil c a m * bil c a m' - bil c a m' * bil c a m =
      bil c a (fun i l => ∑ k, m i k * m' k l - ∑ k, m' i k * m k l) := by
  have e1 : bil c a m * bil c a m' =
      ∑ i, ∑ j, ∑ k, ∑ l, (m i j * m' k l) • ((c i * a j) * (c k * a l)) := by
    unfold bil
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_mul_smul_comm]
  have e2 : bil c a m' * bil c a m =
      ∑ i, ∑ j, ∑ k, ∑ l, (m i j * m' k l) • ((c k * a l) * (c i * a j)) := by
    unfold bil
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_mul_smul_comm, mul_comm (m' k l)]
  have e3 : ∑ i, ∑ j, ∑ k, ∑ l, (m i j * m' k l) • (if j = k then c i * a l else 0) =
      ∑ i, ∑ l, (∑ k, m i k * m' k l) • (c i * a l) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Finset.sum_smul]
    rw [Finset.sum_comm (f := fun l k => (m i k * m' k l) • (c i * a l))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    simp
  have e4 : ∑ i, ∑ j, ∑ k, ∑ l, (m i j * m' k l) • (if l = i then c k * a j else 0) =
      ∑ i, ∑ l, (∑ k, m' i k * m k l) • (c i * a l) := by
    have : ∀ i j k, ∑ l, (m i j * m' k l) • (if l = i then c k * a j else 0) =
        (m' k i * m i j) • (c k * a j) := by
      intro i j k
      simp [mul_comm]
    simp only [this, Finset.sum_smul]
    calc ∑ i, ∑ j, ∑ k, (m' k i * m i j) • (c k * a j)
        = ∑ j, ∑ i, ∑ k, (m' k i * m i j) • (c k * a j) := Finset.sum_comm
      _ = ∑ j, ∑ k, ∑ i, (m' k i * m i j) • (c k * a j) :=
          Finset.sum_congr rfl fun j _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [e1, e2]
  simp only [← Finset.sum_sub_distrib, ← smul_sub, pair_comm c a haa hcc hac]
  simp only [smul_sub, Finset.sum_sub_distrib, e3, e4, bil, sub_smul]

variable {n : ℕ}

def dl (x y : Fin n) : ℂ := if x = y then 1 else 0

theorem dl_comm (x y : Fin n) : dl x y = dl y x := by
  simp only [dl, eq_comm]

def mm (c d : Fin n) (x y : Fin n × Fin n) : ℂ :=
  dl x.1 c * dl y.1 d * dl x.2 y.2 - dl x.2 d * dl y.2 c * dl x.1 y.1

theorem gop_eq (ε : Fin n → Bool) (V : Type) [AddCommGroup V] [Module ℂ V] (c d : Fin n) :
    (Gop ε c d : Module.End ℂ (Ch ε V)) = bil cre ann (fun i j : NC ε => mm c d i.1 j.1) := by
  unfold Gop bil
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 1
  simp only [mm, dl, ite_and, mul_ite, mul_one, mul_zero]
  split_ifs <;> simp_all

theorem sum_pt (ε : Fin n → Bool) (x y : Fin n) (hx : ε x = true) (hy : ε y = false)
    (f : Fin n × Fin n → ℂ) : ∑ k : NC ε, dl k.1.1 x * dl k.1.2 y * f k.1 = f (x, y) := by
  rw [Finset.sum_eq_single (⟨(x, y), hx, hy⟩ : NC ε)]
  · simp [dl]
  · rintro ⟨⟨u, v⟩, h⟩ _ hne
    by_cases h1 : u = x
    · by_cases h2 : v = y
      · subst h1 h2; exact absurd rfl hne
      · simp [dl, h2]
    · simp [dl, h1]
  · simp

theorem sum_mm (ε : Fin n → Bool) (a b : Fin n) (hab : ε a = ε b) (i : NC ε) (f : Fin n × Fin n → ℂ) :
    ∑ k : NC ε, mm a b i.1 k.1 * f k.1 = dl i.1.1 a * f (b, i.1.2) - dl i.1.2 b * f (i.1.1, a) := by
  have e : ∀ k : NC ε, mm a b i.1 k.1 * f k.1 =
      dl i.1.1 a * (dl k.1.1 b * dl k.1.2 i.1.2 * f k.1) - dl i.1.2 b * (dl k.1.1 i.1.1 * dl k.1.2 a * f k.1) := by
    intro k
    rw [mm, dl_comm i.1.2 k.1.2, dl_comm i.1.1 k.1.1]; ring
  simp only [e, Finset.sum_sub_distrib, ← Finset.mul_sum]
  congr 1
  · by_cases h : i.1.1 = a
    · rw [sum_pt ε b i.1.2 (by rw [← hab, ← h]; exact i.2.1) i.2.2]
    · simp [dl, h]
  · by_cases h : i.1.2 = b
    · rw [sum_pt ε i.1.1 a i.2.1 (by rw [hab, ← h]; exact i.2.2)]
    · simp [dl, h]

theorem gop_rel (h : CAR) (ε : Fin n → Bool) (V : Type) [AddCommGroup V] [Module ℂ V] :
    KRel ε (Gop ε : Fin n → Fin n → Module.End ℂ (Ch ε V)) := by
  intro a b c d hab hcd
  have hr : ∀ (x y : Fin n) (T : Module.End ℂ (Ch ε V)), (if x = y then T else 0) = dl x y • T := by
    intro x y T; unfold dl; split_ifs <;> simp
  simp only [gop_eq, hr]
  rw [bil_comm cre ann (fun i j => (h n ε V i j).1) (fun i j => (h n ε V i j).2.1)
    (fun i j => by convert (h n ε V i j).2.2)]
  simp only [bil, Finset.smul_sum, ← Finset.sum_sub_distrib, smul_smul, ← sub_smul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 1
  rw [Finset.sum_sub_distrib, sum_mm ε a b hab i (fun k => mm c d k j.1), sum_mm ε c d hcd i (fun k => mm a b k j.1)]
  simp only [mm]
  rw [dl_comm b j.1.1, dl_comm d j.1.1, dl_comm a j.1.2, dl_comm c j.1.2, dl_comm a d, dl_comm c b]
  ring

section

variable {ε : Fin n → Bool} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem lift_gop (T : Module.End ℂ V) (c d : Fin n) :
    Commute (lift ε T : Module.End ℂ (Ch ε V)) (Gop ε c d) := by
  have ha : ∀ i : NC ε, Commute (lift ε T : Module.End ℂ (Ch ε V)) (ann i) := by
    intro i
    refine LinearMap.ext fun x => funext fun A => ?_
    by_cases h : i ∈ A <;> simp [ann, h]
  have hc : ∀ i : NC ε, Commute (lift ε T : Module.End ℂ (Ch ε V)) (cre i) := by
    intro i
    refine LinearMap.ext fun x => funext fun A => ?_
    by_cases h : i ∈ A <;> simp [cre, h]
  unfold Gop
  exact Commute.sum_right _ _ _ fun i _ => Commute.sum_right _ _ _ fun j _ =>
    ((hc i).mul_right (ha j)).smul_right _

theorem lift_rel (E : Fin n → Fin n → Module.End ℂ V) (hE : KRel ε E) :
    KRel ε (fun c d => (lift ε (E c d) : Module.End ℂ (Ch ε V))) := by
  intro a b c d hab hcd
  refine LinearMap.ext fun x => funext fun A => ?_
  have := LinearMap.congr_fun (hE a b c d hab hcd) (x A)
  split_ifs at this ⊢ <;> simpa using this

end

theorem add_rel {A : Type} [Ring A] (ε : Fin n → Bool) (L G : Fin n → Fin n → A) (hL : KRel ε L) (hG : KRel ε G)
    (hc : ∀ a b c d, Commute (L a b) (G c d)) : KRel ε (fun c d => L c d + G c d) := by
  intro a b c d hab hcd
  have h1 := hL a b c d hab hcd
  have h2 := hG a b c d hab hcd
  have h3 := (hc a b c d).eq
  have h4 := (hc c d a b).eq
  have : (L a b + G a b) * (L c d + G c d) - (L c d + G c d) * (L a b + G a b) =
      (L a b * L c d - L c d * L a b) + (G a b * G c d - G c d * G a b) := by
    simp only [mul_add, add_mul, h3, h4]; abel
  simp only []
  rw [this, h1, h2]
  split_ifs <;> abel

theorem neg_rel {A : Type} [Ring A] (ε : Fin n → Bool) (G : Fin n → Fin n → A) (hG : KRel ε G) :
    KRel ε (fun c d => -G d c) := by
  intro a b c d hab hcd
  have h := hG b a d c hab.symm hcd.symm
  simp only [neg_mul_neg]
  rw [h]
  simp only [eq_comm (a := a) (b := d), eq_comm (a := c) (b := b)]
  split_ifs <;> abel

theorem frel_of_car (h : CAR) : FRel := by
  intro n ε V _ _ E hE
  refine ⟨add_rel ε _ _ (lift_rel E hE) (gop_rel h ε V) fun a b c d => lift_gop _ c d, ?_⟩
  have := add_rel ε _ _ (lift_rel E hE) (neg_rel ε _ (gop_rel h ε V)) fun a b c d => (lift_gop _ d c).neg_right
  simp only [← sub_eq_add_neg] at this
  exact this

theorem car_imp_frel : CompanionTheory.D.DSIC.CAR → CompanionTheory.D.DSIC.FRel := frel_of_car

end GlobalTheory.CompanionTheory.DSICFRel
