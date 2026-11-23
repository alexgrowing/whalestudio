import Mathlib

noncomputable section

namespace PositivityTheory.KB.SimplicialChains

abbrev HC (X : Type) (n : ℕ) : Type := (Fin n → X) →₀ ℝ

def hbd (X : Type) (n : ℕ) : HC X (n + 1) →ₗ[ℝ] HC X n :=
  Finsupp.linearCombination ℝ fun t : Fin (n + 1) → X =>
    ∑ j : Fin (n + 1), ((-1 : ℝ) ^ (j : ℕ)) • Finsupp.single (t ∘ j.succAbove) (1 : ℝ)

def cone {X : Type} (a : X) (n : ℕ) : HC X n →ₗ[ℝ] HC X (n + 1) :=
  Finsupp.lmapDomain ℝ ℝ fun t : Fin n → X => (Fin.cons a t : Fin (n + 1) → X)

def chMap {X Y : Type} (f : X → Y) (n : ℕ) : HC X n →ₗ[ℝ] HC Y n :=
  Finsupp.lmapDomain ℝ ℝ fun t : Fin n → X => f ∘ t

theorem eq_of_single {α M : Type} [AddCommGroup M] [Module ℝ M] (φ ψ : (α →₀ ℝ) →ₗ[ℝ] M)
    (h : ∀ t, φ (Finsupp.single t 1) = ψ (Finsupp.single t 1)) (c : α →₀ ℝ) : φ c = ψ c := by
  have : φ = ψ := Finsupp.lhom_ext' fun t => LinearMap.ext_ring (by simpa using h t)
  rw [this]

section Tuples

variable {X Y Z : Type}

theorem hbd_single (n : ℕ) (t : Fin (n + 1) → X) :
    hbd X n (Finsupp.single t 1) =
      ∑ j : Fin (n + 1), ((-1 : ℝ) ^ (j : ℕ)) • Finsupp.single (t ∘ j.succAbove) (1 : ℝ) := by
  rw [hbd, Finsupp.linearCombination_single, one_smul]

theorem cone_single (a : X) (n : ℕ) (t : Fin n → X) (c : ℝ) :
    cone a n (Finsupp.single t c) = Finsupp.single (Fin.cons a t : Fin (n + 1) → X) c := by
  simp [cone]

theorem chMap_single (f : X → Y) (n : ℕ) (t : Fin n → X) (c : ℝ) :
    chMap f n (Finsupp.single t c) = Finsupp.single (f ∘ t) c := by
  simp [chMap]

theorem hbd_chMap (f : X → Y) (n : ℕ) (c : HC X (n + 1)) :
    hbd Y n (chMap f (n + 1) c) = chMap f n (hbd X n c) := by
  refine eq_of_single (hbd Y n ∘ₗ chMap f (n + 1)) (chMap f n ∘ₗ hbd X n) (fun t => ?_) c
  simp only [LinearMap.comp_apply, chMap_single, hbd_single, map_sum, map_smul]
  rfl

theorem chMap_chMap (f : X → Y) (g : Y → Z) (n : ℕ) (c : HC X n) :
    chMap g n (chMap f n c) = chMap (g ∘ f) n c := by
  refine eq_of_single (chMap g n ∘ₗ chMap f n) (chMap (g ∘ f) n) (fun t => ?_) c
  simp only [LinearMap.comp_apply, chMap_single]
  rfl

theorem chMap_cone (f : X → Y) (a : X) (n : ℕ) (c : HC X n) :
    chMap f (n + 1) (cone a n c) = cone (f a) n (chMap f n c) := by
  refine eq_of_single (chMap f (n + 1) ∘ₗ cone a n) (cone (f a) n ∘ₗ chMap f n) (fun t => ?_) c
  simp only [LinearMap.comp_apply, chMap_single, cone_single, Fin.comp_cons]

theorem hbd_cone_zero (a : X) (c : HC X 0) : hbd X 0 (cone a 0 c) = c := by
  refine eq_of_single (hbd X 0 ∘ₗ cone a 0) LinearMap.id (fun t => ?_) c
  simp only [LinearMap.comp_apply, cone_single, hbd_single, LinearMap.id_apply]
  rw [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.val_zero, pow_zero, one_smul]
  congr 1

theorem hbd_cone_succ (a : X) (n : ℕ) (c : HC X (n + 1)) :
    hbd X (n + 1) (cone a (n + 1) c) = c - cone a n (hbd X n c) := by
  refine eq_of_single (hbd X (n + 1) ∘ₗ cone a (n + 1)) (LinearMap.id - cone a n ∘ₗ hbd X n)
    (fun t => ?_) c
  simp only [LinearMap.comp_apply, cone_single, hbd_single, LinearMap.id_apply,
    LinearMap.sub_apply, map_sum, map_smul]
  rw [Fin.sum_univ_succ, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  · simp only [Fin.val_zero, pow_zero, one_smul]
    congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    have : (Fin.cons a t : Fin (n + 2) → X) ∘ (Fin.succ j).succAbove
        = (Fin.cons a (t ∘ j.succAbove) : Fin (n + 1) → X) := by
      funext k
      refine Fin.cases ?_ (fun k => ?_) k <;> simp
    rw [this, Fin.val_succ, pow_succ]
    simp

theorem hbd_hbd (n : ℕ) (c : HC X (n + 2)) : hbd X n (hbd X (n + 1) c) = 0 := by
  induction n with
  | zero =>
    refine eq_of_single (hbd X 0 ∘ₗ hbd X 1) 0 (fun t => ?_) c
    rw [← Fin.cons_self_tail t, ← cone_single]
    simp only [LinearMap.comp_apply, hbd_cone_succ, map_sub, hbd_cone_zero, sub_self,
      LinearMap.zero_apply]
  | succ n ih =>
    refine eq_of_single (hbd X (n + 1) ∘ₗ hbd X (n + 2)) 0 (fun t => ?_) c
    rw [← Fin.cons_self_tail t, ← cone_single]
    simp only [LinearMap.comp_apply, hbd_cone_succ, map_sub, ih, map_zero, sub_zero, sub_self,
      LinearMap.zero_apply]

end Tuples

section Group

variable {G : Type} [Group G]

def rho (a : G) (n : ℕ) : HC G n →ₗ[ℝ] HC G n := chMap (· * a) n

def hD (a : G) : ∀ n, HC G n →ₗ[ℝ] HC G (n + 1)
  | 0 => 0
  | n + 1 => Finsupp.linearCombination ℝ fun t : Fin (n + 1) → G =>
      cone (t 0) (n + 1) (Finsupp.single t 1 - rho a (n + 1) (Finsupp.single t 1)
        - hD a n (hbd G n (Finsupp.single t 1)))

theorem hD_single (a : G) (n : ℕ) (t : Fin (n + 1) → G) :
    hD a (n + 1) (Finsupp.single t 1) =
      cone (t 0) (n + 1) (Finsupp.single t 1 - rho a (n + 1) (Finsupp.single t 1)
        - hD a n (hbd G n (Finsupp.single t 1))) := by
  rw [hD, Finsupp.linearCombination_single, one_smul]

theorem rho_zero (a : G) (c : HC G 0) : rho a 0 c = c := by
  refine eq_of_single (rho a 0) LinearMap.id (fun t => ?_) c
  simp only [rho, chMap_single, LinearMap.id_apply]
  congr 1
  funext i
  exact i.elim0

theorem hbd_rho (a : G) (n : ℕ) (c : HC G (n + 1)) :
    hbd G n (rho a (n + 1) c) = rho a n (hbd G n c) := hbd_chMap _ n c

theorem hD_step (a : G) (n : ℕ)
    (h : ∀ c : HC G (n + 1), hbd G n (hD a n (hbd G n c)) = hbd G n c - rho a n (hbd G n c))
    (c : HC G (n + 1)) :
    hbd G (n + 1) (hD a (n + 1) c) + hD a n (hbd G n c) = c - rho a (n + 1) c := by
  refine eq_of_single (hbd G (n + 1) ∘ₗ hD a (n + 1) + hD a n ∘ₗ hbd G n)
    (LinearMap.id - rho a (n + 1)) (fun t => ?_) c
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply]
  rw [hD_single, hbd_cone_succ, map_sub (hbd G n), map_sub (hbd G n), h, hbd_rho, sub_self, map_zero]
  abel

theorem hD_spec (a : G) (n : ℕ) (c : HC G (n + 1)) :
    hbd G (n + 1) (hD a (n + 1) c) + hD a n (hbd G n c) = c - rho a (n + 1) c := by
  induction n with
  | zero =>
    refine hD_step a 0 (fun c => ?_) c
    rw [rho_zero, sub_self, hD, LinearMap.zero_apply, map_zero]
  | succ n ih =>
    refine hD_step a (n + 1) (fun c => ?_) c
    have := ih (hbd G (n + 1) c)
    rwa [hbd_hbd, map_zero, add_zero] at this

theorem chMap_rho (g a : G) (n : ℕ) (c : HC G n) :
    chMap (g * ·) n (rho a n c) = rho a n (chMap (g * ·) n c) := by
  have : ((fun x : G => g * x) ∘ fun x => x * a) = ((fun x => x * a) ∘ fun x => g * x) := by
    funext x
    simp [mul_assoc]
  simp only [rho, chMap_chMap, this]

theorem hD_left (g a : G) (n : ℕ) (c : HC G n) :
    hD a n (chMap (g * ·) n c) = chMap (g * ·) (n + 1) (hD a n c) := by
  induction n with
  | zero => simp [hD]
  | succ n ih =>
    refine eq_of_single (hD a (n + 1) ∘ₗ chMap (g * ·) (n + 1))
      (chMap (g * ·) (n + 2) ∘ₗ hD a (n + 1)) (fun t => ?_) c
    simp only [LinearMap.comp_apply]
    rw [chMap_single, hD_single, hD_single, chMap_cone]
    simp only [map_sub]
    rw [← ih, ← hbd_chMap, chMap_rho, chMap_single]
    rfl

def rat {n : ℕ} (x : Fin (n + 1) → G) : Fin n → G := fun i => (x i.castSucc)⁻¹ * x i.succ

def ph (n : ℕ) : HC G (n + 1) →ₗ[ℝ] HC G n := Finsupp.lmapDomain ℝ ℝ rat

def ps (n : ℕ) : HC G n →ₗ[ℝ] HC G (n + 1) := Finsupp.lmapDomain ℝ ℝ Fin.partialProd

def ibd (G : Type) [Group G] (m : ℕ) : HC G (m + 1) →ₗ[ℝ] HC G m :=
  Finsupp.linearCombination ℝ fun g =>
    Finsupp.single (fun i => g i.succ) 1 +
      ∑ j : Fin (m + 1), ((-1 : ℝ) ^ ((j : ℕ) + 1)) • Finsupp.single (Fin.contractNth j (· * ·) g) 1

def icmap {H : Type} [Group H] (f : G →* H) (m : ℕ) : HC G m →ₗ[ℝ] HC H m :=
  Finsupp.lmapDomain ℝ ℝ fun g i => f (g i)

theorem ph_single (n : ℕ) (x : Fin (n + 1) → G) (r : ℝ) :
    ph n (Finsupp.single x r) = Finsupp.single (rat x) r := by
  simp [ph]

theorem ps_single (n : ℕ) (x : Fin n → G) (r : ℝ) :
    ps n (Finsupp.single x r) = Finsupp.single (Fin.partialProd x) r := by
  simp [ps]

theorem icmap_single {H : Type} [Group H] (f : G →* H) (m : ℕ) (x : Fin m → G) (r : ℝ) :
    icmap f m (Finsupp.single x r) = Finsupp.single (fun i => f (x i)) r := by
  simp [icmap]

theorem ibd_single (m : ℕ) (g : Fin (m + 1) → G) :
    ibd G m (Finsupp.single g 1) = Finsupp.single (fun i => g i.succ) 1 +
      ∑ j : Fin (m + 1), ((-1 : ℝ) ^ ((j : ℕ) + 1)) • Finsupp.single (Fin.contractNth j (· * ·) g) 1 := by
  rw [ibd, Finsupp.linearCombination_single, one_smul]

theorem rat_partialProd {n : ℕ} (g : Fin n → G) : rat (Fin.partialProd g) = g := by
  funext i
  simp [rat, Fin.partialProd_succ]

theorem partialProd_rat {n : ℕ} (x : Fin (n + 1) → G) :
    Fin.partialProd (rat x) = fun k => (x 0)⁻¹ * x k := by
  funext k
  induction k using Fin.induction with
  | zero => simp
  | succ k ih => rw [Fin.partialProd_succ, ih, rat, mul_assoc, mul_inv_cancel_left]

theorem ph_ps (n : ℕ) (z : HC G n) : ph n (ps n z) = z := by
  refine eq_of_single (ph n ∘ₗ ps n) LinearMap.id (fun t => ?_) z
  simp only [LinearMap.comp_apply, ps_single, ph_single, rat_partialProd, LinearMap.id_apply]

theorem ph_chMap_left (g : G) (n : ℕ) (c : HC G (n + 1)) :
    ph n (chMap (g * ·) (n + 1) c) = ph n c := by
  refine eq_of_single (ph n ∘ₗ chMap (g * ·) (n + 1)) (ph n) (fun t => ?_) c
  simp only [LinearMap.comp_apply, chMap_single, ph_single]
  congr 1
  funext i
  simp [rat, mul_assoc]

theorem ph_rho (a : G) (n : ℕ) (c : HC G (n + 1)) :
    ph n (rho a (n + 1) c) = icmap (MulAut.conj a⁻¹).toMonoidHom n (ph n c) := by
  refine eq_of_single (ph n ∘ₗ rho a (n + 1)) (icmap (MulAut.conj a⁻¹).toMonoidHom n ∘ₗ ph n)
    (fun t => ?_) c
  simp only [LinearMap.comp_apply, rho, chMap_single, ph_single, icmap_single]
  congr 1
  funext i
  simp [rat, mul_assoc]

theorem ps_ph_single (n : ℕ) (x : Fin (n + 1) → G) :
    ps n (ph n (Finsupp.single x 1)) = chMap ((x 0)⁻¹ * ·) (n + 1) (Finsupp.single x 1) := by
  rw [ph_single, ps_single, partialProd_rat, chMap_single]
  rfl

theorem rat_succAbove_zero {m : ℕ} (x : Fin (m + 2) → G) :
    rat (x ∘ (0 : Fin (m + 2)).succAbove) = fun i => rat x i.succ := by
  funext i
  simp only [rat, Function.comp_apply, Fin.succAbove_zero, Fin.succ_castSucc]

theorem rat_succAbove_succ {m : ℕ} (x : Fin (m + 2) → G) (j : Fin (m + 1)) :
    rat (x ∘ j.succ.succAbove) = Fin.contractNth j (· * ·) (rat x) := by
  funext i
  simp only [Function.comp_apply, rat, Fin.contractNth]
  by_cases h1 : (i : ℕ) < j
  · rw [if_pos h1, Fin.succAbove_of_castSucc_lt _ _ (by simp [Fin.lt_def] <;> omega),
      Fin.succAbove_of_castSucc_lt _ _ (by simp [Fin.lt_def] <;> omega)]
    simp only [Fin.succ_castSucc]
  · by_cases h2 : (i : ℕ) = j
    · rw [if_neg h1, if_pos h2, Fin.succAbove_of_castSucc_lt _ _ (by simp [Fin.lt_def] <;> omega),
        Fin.succAbove_of_le_castSucc _ _ (by simp [Fin.le_def] <;> omega)]
      simp only [Fin.succ_castSucc, mul_assoc, mul_inv_cancel_left]
    · rw [if_neg h1, if_neg h2, Fin.succAbove_of_le_castSucc _ _ (by simp [Fin.le_def] <;> omega),
        Fin.succAbove_of_le_castSucc _ _ (by simp [Fin.le_def] <;> omega)]
      simp only [Fin.succ_castSucc]

theorem ibd_ph (m : ℕ) (c : HC G (m + 2)) : ibd G m (ph (m + 1) c) = ph m (hbd G (m + 1) c) := by
  refine eq_of_single (ibd G m ∘ₗ ph (m + 1)) (ph m ∘ₗ hbd G (m + 1)) (fun x => ?_) c
  simp only [LinearMap.comp_apply, ph_single, ibd_single, hbd_single, map_sum, map_smul]
  conv_rhs => rw [Fin.sum_univ_succ]
  congr 1
  · rw [rat_succAbove_zero]
    simp
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [rat_succAbove_succ, Fin.val_succ]

def hI (a : G) (m : ℕ) : HC G m →ₗ[ℝ] HC G (m + 1) := ph (m + 1) ∘ₗ hD a (m + 1) ∘ₗ ps m

theorem ph_hD (a : G) (m : ℕ) (c : HC G (m + 1)) : ph (m + 1) (hD a (m + 1) c) = hI a m (ph m c) := by
  refine eq_of_single (ph (m + 1) ∘ₗ hD a (m + 1)) (hI a m ∘ₗ ph m) (fun x => ?_) c
  simp only [LinearMap.comp_apply, hI]
  rw [ps_ph_single, hD_left, ph_chMap_left]

theorem homotopy (a : G) (m : ℕ) (z : HC G (m + 1)) :
    ibd G (m + 1) (hI a (m + 1) z) + hI a m (ibd G m z) =
      z - icmap (MulAut.conj a⁻¹).toMonoidHom (m + 1) z := by
  have hz : z = ph (m + 1) (ps (m + 1) z) := (ph_ps _ z).symm
  rw [hz, ← ph_hD, ibd_ph, ibd_ph, ← ph_hD, ← map_add, hD_spec, map_sub, ph_rho]

theorem ibd_ibd (m : ℕ) (z : HC G (m + 2)) : ibd G m (ibd G (m + 1) z) = 0 := by
  rw [← ph_ps _ z, ibd_ph, ibd_ph, hbd_hbd, map_zero]

theorem ibd_icmap {H : Type} [Group H] (f : G →* H) (m : ℕ) (z : HC G (m + 1)) :
    ibd H m (icmap f (m + 1) z) = icmap f m (ibd G m z) := by
  refine eq_of_single (ibd H m ∘ₗ icmap f (m + 1)) (icmap f m ∘ₗ ibd G m) (fun x => ?_) z
  simp only [LinearMap.comp_apply, icmap_single, ibd_single, map_add, map_sum, map_smul]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 2
  funext i
  simp only [Fin.contractNth]
  split_ifs <;> simp

theorem icmap_comp {H K : Type} [Group H] [Group K] (f : G →* H) (g : H →* K) (m : ℕ) (z : HC G m) :
    icmap (g.comp f) m z = icmap g m (icmap f m z) := by
  refine eq_of_single (icmap (g.comp f) m) (icmap g m ∘ₗ icmap f m) (fun x => ?_) z
  simp only [LinearMap.comp_apply, icmap_single, MonoidHom.comp_apply]

theorem conj_bd (g : G) (m : ℕ) (z : HC G (m + 1)) (hz : ibd G m z = 0) :
    icmap (MulAut.conj g).toMonoidHom (m + 1) z - z ∈ LinearMap.range (ibd G (m + 1)) := by
  refine ⟨-hI g⁻¹ (m + 1) z, ?_⟩
  have h := homotopy g⁻¹ m z
  rw [hz, map_zero, add_zero, inv_inv] at h
  rw [map_neg, h, neg_sub]

end Group

end PositivityTheory.KB.SimplicialChains
