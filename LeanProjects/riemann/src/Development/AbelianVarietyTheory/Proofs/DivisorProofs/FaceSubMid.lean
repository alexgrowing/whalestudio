import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroChains

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.EtC.CupSpec

variable {R : Type} [CommRing R]

section Faces
variable {E : Spc} {U : Scheme.{0}}

theorem along_along {N p r : ℕ} (x : Sx E N U) (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N)
    (b : SimplexCategory.mk r ⟶ SimplexCategory.mk p) : (x.along a).along b = x.along (b ≫ a) := by
  unfold Sx.along
  rw [op_comp, E.map_comp]
  rfl

theorem δ_val {n : ℕ} (i : Fin (n + 2)) (v : Fin (n + 1)) :
    (((SimplexCategory.δ i).toOrderHom v : Fin (n + 2)) : ℕ) = if (v : ℕ) < i then (v : ℕ) else v + 1 := by
  change ((i.succAbove v : Fin (n + 2)) : ℕ) = _
  unfold Fin.succAbove
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd h1 h2
  · exact absurd h2 h1
  · rfl

theorem hom_ext_val {a b : ℕ} (f g : SimplexCategory.mk a ⟶ SimplexCategory.mk b)
    (h : ∀ v : Fin (a + 1), ((f.toOrderHom v : Fin (b + 1)) : ℕ) = (g.toOrderHom v : Fin (b + 1))) : f = g :=
  SimplexCategory.Hom.ext _ _ (OrderHom.ext _ _ (funext fun v => Fin.ext (h v)))

theorem sub_δ_val {N j l : ℕ} (h : j + l ≤ N) (i : Fin (N + 2)) (v : Fin (l + 1)) :
    (((SimplexCategory.subinterval j l h ≫ SimplexCategory.δ i).toOrderHom v : Fin (N + 2)) : ℕ) =
      if (v : ℕ) + j < i then (v : ℕ) + j else v + j + 1 :=
  δ_val i ((SimplexCategory.subinterval j l h).toOrderHom v)

theorem δ_sub_val {N j l : ℕ} (h : j + (l + 1) ≤ N) (i : Fin (l + 2)) (v : Fin (l + 1)) :
    (((SimplexCategory.δ i ≫ SimplexCategory.subinterval j (l + 1) h).toOrderHom v : Fin (N + 1)) : ℕ) =
      (if (v : ℕ) < i then (v : ℕ) else v + 1) + j :=
  congrArg (· + j) (δ_val i v)

theorem sub_val {N j l : ℕ} (h : j + l ≤ N) (v : Fin (l + 1)) :
    (((SimplexCategory.subinterval j l h).toOrderHom v : Fin (N + 1)) : ℕ) = v + j := rfl

section
variable {N : ℕ} (x : Sx E (N + 1) U) (i : Fin (N + 2)) (j l : ℕ) (h : j + l ≤ N)

theorem face_sub_le (hi : (i : ℕ) ≤ j) : (x.face i).sub j l h = x.sub (j + 1) l (by omega) := by
  refine (along_along x _ _).trans (congrArg x.along (hom_ext_val _ _ fun v => ?_))
  rw [sub_δ_val, sub_val]
  split_ifs <;> omega

theorem face_sub_gt (hi : j + l < (i : ℕ)) : (x.face i).sub j l h = x.sub j l (by omega) := by
  refine (along_along x _ _).trans (congrArg x.along (hom_ext_val _ _ fun v => ?_))
  rw [sub_δ_val, sub_val]
  split_ifs <;> omega

theorem face_sub_mid (i' : Fin (l + 2)) (hi : (i : ℕ) = j + i') :
    (x.face i).sub j l h = (x.sub j (l + 1) (by omega)).face i' := by
  refine (along_along x _ _).trans ((congrArg x.along (hom_ext_val _ _ fun v => ?_)).trans (along_along x _ _).symm)
  rw [sub_δ_val, δ_sub_val]
  split_ifs <;> omega

end

theorem telescope {N : ℕ} (x : Sx E (N + 1) U) {A : Type*} [AddCommGroup A] {p r : ℕ} (hN : p + r = N) (φ : Sx E p U → Sx E r U → A) :
    ∑ i : Fin (N + 2), (-1 : ℤ) ^ (i : ℕ) • φ ((x.face i).sub 0 p (by omega)) ((x.face i).sub p r (by omega)) =
      ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • φ ((x.sub 0 (p + 1) (by omega)).face i) (x.sub (p + 1) r (by omega)) +
      (-1 : ℤ) ^ p • ∑ j : Fin (r + 2), (-1 : ℤ) ^ (j : ℕ) •
        φ (x.sub 0 p (by omega)) ((x.sub p (r + 1) (by omega)).face j) := by
  have e1 : (x.sub 0 (p + 1) (by omega)).face (Fin.last (p + 1)) = x.sub 0 p (by omega) :=
    (face_sub_mid x ⟨p + 1, by omega⟩ 0 p (by omega) (Fin.last _) (by simp)).symm.trans
      (face_sub_gt x _ 0 p _ (by simp))
  have e2 : (x.sub p (r + 1) (by omega)).face 0 = x.sub (p + 1) r (by omega) :=
    (face_sub_mid x ⟨p, by omega⟩ p r (by omega) 0 (by simp)).symm.trans (face_sub_le x _ p r _ (by simp))
  rw [← Fin.sum_congr' _ (show (p + 1) + (r + 1) = N + 2 by omega), Fin.sum_univ_add,
    Fin.sum_univ_castSucc (n := p + 1), Fin.sum_univ_succ (n := r + 1), e1, e2, smul_add, Finset.smul_sum]
  have c : (-1 : ℤ) ^ ((Fin.last (p + 1) : Fin (p + 2)) : ℕ) • φ (x.sub 0 p (by omega)) (x.sub (p + 1) r (by omega)) +
      (-1 : ℤ) ^ p • (-1 : ℤ) ^ ((0 : Fin (r + 2)) : ℕ) • φ (x.sub 0 p (by omega)) (x.sub (p + 1) r (by omega)) = 0 := by
    simp [pow_succ]
  have key : ∀ a b c d e f : A, c + d = 0 → a = e → b = f → a + b = e + c + (d + f) := by
    rintro a b c d _ _ h rfl rfl
    rw [add_assoc, ← add_assoc c, h, zero_add]
  refine key _ _ _ _ _ _ c (Finset.sum_congr rfl fun i _ => ?_) (Finset.sum_congr rfl fun j _ => ?_)
  · rw [face_sub_mid x _ 0 p _ i.castSucc (by simp), face_sub_le x _ p r _ (by simpa using Nat.lt_succ_iff.1 i.2)]
    rfl
  · rw [face_sub_mid x _ p r _ j.succ (by simp; omega), face_sub_gt x _ 0 p _ (by simp; omega), smul_smul, ← pow_add]
    congr 2
    simp; omega

end Faces

def sg (j : ℤ) : ℤ := (j.negOnePow : ℤˣ)

theorem sg_add (a b : ℤ) : sg (a + b) = sg a * sg b := by simp [sg, Int.negOnePow_add]
theorem sg_neg (a : ℤ) : sg (-a) = sg a := by simp [sg]
theorem sg_one : sg 1 = -1 := by simp [sg]
theorem sg_sq (a : ℤ) : sg a * sg a = 1 := by rw [sg, ← Units.val_mul, Int.units_mul_self, Units.val_one]
theorem sg_nat (p : ℕ) : (-1 : ℤ) ^ p = sg p := by simp [sg, Int.coe_negOnePow_natCast]
theorem sg_smul {A : Type*} [AddCommGroup A] (j : ℤ) (a : A) : j.negOnePow • a = sg j • a := rfl

section Leibniz
variable {E : Spc} {U : Scheme.{0}}

def cl {N : ℕ} (x : Sx E N U) (j l : ℕ) : Sx E l U :=
  if h : j + l ≤ N then x.sub j l h else x.along (SimplexCategory.const _ _ 0)

theorem cl_eq {N : ℕ} (x : Sx E N U) (j l : ℕ) (h : j + l ≤ N) : cl x j l = x.sub j l h := dif_pos h

def bdL {A : Type*} [AddCommGroup A] (φ : ∀ p r : ℕ, Sx E p U → Sx E r U → A) : ∀ p r : ℕ, Sx E p U → Sx E r U → A
  | 0, _, _, _ => 0
  | p + 1, r, y, z => ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • φ p r (y.face i) z

def bdR {A : Type*} [AddCommGroup A] (φ : ∀ p r : ℕ, Sx E p U → Sx E r U → A) : ∀ p r : ℕ, Sx E p U → Sx E r U → A
  | _, 0, _, _ => 0
  | p, r + 1, y, z => ∑ i : Fin (r + 2), (-1 : ℤ) ^ (i : ℕ) • φ p r y (z.face i)

variable {I J K : Cx R} (μ : Pair I J K) {n m : ℤ}

def pv (a : Cochain ((chains R).obj E) I n) (b : Cochain ((chains R).obj E) J m) (w : ℤ) (p r : ℕ) (y : Sx E p U)
    (z : Sx E r U) : Sec (K.X w) U :=
  if h : (-(p : ℤ) + n) + (-(r : ℤ) + m) = w then μ.mul U _ _ w h (ev a p _ rfl U y) (ev b r _ rfl U z) else 0

theorem pv_eq (a : Cochain ((chains R).obj E) I n) (b : Cochain ((chains R).obj E) J m) (w : ℤ) (p r : ℕ) (y : Sx E p U)
    (z : Sx E r U) (s t : ℤ) (hs : -(p : ℤ) + n = s) (ht : -(r : ℤ) + m = t) (h : s + t = w) :
    pv μ a b w p r y z = μ.mul U s t w h (ev a p s hs U y) (ev b r t ht U z) := by
  subst hs ht
  exact dif_pos h

theorem ev_aw {k : ℤ} {hk : n + m = k} {a : Cochain ((chains R).obj E) I n} {b : Cochain ((chains R).obj E) J m}
    {c : Cochain ((chains R).obj E) K k} (hc : μ.IsAW hk a b c) (N : ℕ) (w : ℤ) (h : -(N : ℤ) + k = w) (x : Sx E N U) :
    ev c N w h U x = ∑ q ∈ Finset.HasAntidiagonal.antidiagonal N, sg (m * q.1) • pv μ a b w q.1 q.2 (cl x 0 q.1) (cl x q.1 q.2) := by
  rw [hc N w h U x, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [pv_eq μ a b w _ _ _ _ _ _ rfl rfl (by omega), cl_eq x 0 p (by omega), cl_eq x p (N - p) (by omega)]
  rfl

theorem pv_δ_left {n₁ : ℤ} (hn : n + 1 = n₁) (a : Cochain ((chains R).obj E) I n) (b : Cochain ((chains R).obj E) J m)
    (w : ℤ) (p r : ℕ) (y : Sx E p U) (z : Sx E r U) (s s' t : ℤ) (hs : -(p : ℤ) + n = s) (hs' : s + 1 = s')
    (ht : -(r : ℤ) + m = t) (h : s' + t = w) :
    μ.mul U s' t w h (Sec.map (I.d s s') (ev a p s hs U y)) (ev b r t ht U z) =
      pv μ (δ n n₁ a) b w p r y z - sg n₁ • bdL (pv μ a b w) p r y z := by
  rw [pv_eq μ _ b w p r y z s' t (by omega) ht h]
  cases p with
  | zero => rw [ev_δ_zero hn a U s s' hs, bdL, smul_zero, sub_zero]
  | succ p =>
    rw [ev_δ_succ hn a U p s s' hs, bdL, map_add, LinearMap.add_apply, sg_smul, map_zsmul, LinearMap.smul_apply, map_sum,
      LinearMap.sum_apply, eq_sub_iff_add_eq]
    refine congrArg₂ (· + ·) rfl (congrArg _ (Finset.sum_congr rfl fun i _ => ?_))
    rw [map_zsmul, LinearMap.smul_apply, pv_eq μ a b w p r _ z s' t (by omega) ht h]

theorem pv_δ_right {m₁ : ℤ} (hm : m + 1 = m₁) (a : Cochain ((chains R).obj E) I n) (b : Cochain ((chains R).obj E) J m)
    (w : ℤ) (p r : ℕ) (y : Sx E p U) (z : Sx E r U) (s t t' : ℤ) (hs : -(p : ℤ) + n = s)
    (ht : -(r : ℤ) + m = t) (ht' : t + 1 = t') (h : s + t' = w) :
    μ.mul U s t' w h (ev a p s hs U y) (Sec.map (J.d t t') (ev b r t ht U z)) =
      pv μ a (δ m m₁ b) w p r y z - sg m₁ • bdR (pv μ a b w) p r y z := by
  rw [pv_eq μ a _ w p r y z s t' hs (by omega) h]
  cases r with
  | zero => rw [ev_δ_zero hm b U t t' ht, bdR, smul_zero, sub_zero]
  | succ r =>
    rw [ev_δ_succ hm b U r t t' ht, bdR, map_add, sg_smul, map_zsmul, map_sum, eq_sub_iff_add_eq]
    refine congrArg₂ (· + ·) rfl (congrArg _ (Finset.sum_congr rfl fun i _ => ?_))
    rw [map_zsmul, pv_eq μ a b w p r y _ s t' hs (by omega) h]

theorem d_pv {n₁ m₁ : ℤ} (hn : n + 1 = n₁) (hm : m + 1 = m₁) (a : Cochain ((chains R).obj E) I n)
    (b : Cochain ((chains R).obj E) J m) (w w' : ℤ) (hw : w + 1 = w') (p r : ℕ) (y : Sx E p U) (z : Sx E r U)
    (h : (-(p : ℤ) + n) + (-(r : ℤ) + m) = w) :
    Sec.map (K.d w w') (pv μ a b w p r y z) =
      (pv μ (δ n n₁ a) b w' p r y z - sg n₁ • bdL (pv μ a b w') p r y z) +
        sg (-(p : ℤ) + n) • (pv μ a (δ m m₁ b) w' p r y z - sg m₁ • bdR (pv μ a b w') p r y z) := by
  subst hw
  rw [pv_eq μ a b w p r y z _ _ rfl rfl h, μ.leibniz, pv_δ_left μ hn a b _ p r y z _ _ _ rfl rfl rfl,
    pv_δ_right μ hm a b _ p r y z _ _ _ rfl rfl rfl, sg_smul]

def rem (a : Cochain ((chains R).obj E) I n) (b : Cochain ((chains R).obj E) J m) (w : ℤ) {N : ℕ} (x : Sx E N U) :
    Sec (K.X w) U :=
  ∑ q ∈ Finset.HasAntidiagonal.antidiagonal N, sg (m * q.1 + m) • bdL (pv μ a b w) q.1 q.2 (cl x 0 q.1) (cl x q.1 q.2) +
    ∑ q ∈ Finset.HasAntidiagonal.antidiagonal N, sg (m * q.1 + q.1) • bdR (pv μ a b w) q.1 q.2 (cl x 0 q.1) (cl x q.1 q.2)

theorem rem_zero (a : Cochain ((chains R).obj E) I n) (b : Cochain ((chains R).obj E) J m) (w : ℤ) (x : Sx E 0 U) :
    rem μ a b w x = 0 := by
  simp [rem, bdL, bdR]

theorem rem_succ {k : ℤ} {hk : n + m = k} {a : Cochain ((chains R).obj E) I n} {b : Cochain ((chains R).obj E) J m}
    {c : Cochain ((chains R).obj E) K k} (hc : μ.IsAW hk a b c) (N : ℕ) (w : ℤ) (h : -(N : ℤ) + k = w)
    (x : Sx E (N + 1) U) :
    rem μ a b w x = ∑ i : Fin (N + 2), (-1 : ℤ) ^ (i : ℕ) • ev c N w h U (x.face i) := by
  simp only [ev_aw μ hc, Finset.smul_sum]
  rw [Finset.sum_comm, rem, Finset.Nat.sum_antidiagonal_succ, Finset.Nat.sum_antidiagonal_succ']
  simp only [bdL, bdR, smul_zero, zero_add]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  rintro ⟨p, r⟩ hq
  have hN : p + r = N := by simpa using hq
  have e1 : sg (m * ((p + 1 : ℕ) : ℤ) + m) = sg (m * p) := by
    rw [show m * ((p + 1 : ℕ) : ℤ) + m = m * p + (m + m) by push_cast; ring, sg_add, sg_add, sg_sq, mul_one]
  have h1 : ∀ i : Fin (N + 2), cl (x.face i) 0 p = (x.face i).sub 0 p (by omega) := fun i => cl_eq _ _ _ _
  have h2 : ∀ i : Fin (N + 2), cl (x.face i) p r = (x.face i).sub p r (by omega) := fun i => cl_eq _ _ _ _
  dsimp only
  simp only [h1, h2, smul_comm _ (sg (m * p))]
  rw [← Finset.smul_sum, telescope x hN, e1, sg_add, mul_smul, ← smul_add, sg_nat p,
    cl_eq x 0 (p + 1) (by omega), cl_eq x (p + 1) r (by omega), cl_eq x 0 p (by omega), cl_eq x p (r + 1) (by omega)]

theorem d_ev_aw {k n₁ m₁ k₁ : ℤ} {hk : n + m = k} (hn : n + 1 = n₁) (hm : m + 1 = m₁) (hk₁ : k + 1 = k₁)
    {a : Cochain ((chains R).obj E) I n} {b : Cochain ((chains R).obj E) J m} {c : Cochain ((chains R).obj E) K k}
    {c₁ c₂ : Cochain ((chains R).obj E) K k₁} {e₁ : n₁ + m = k₁} {e₂ : n + m₁ = k₁} (hc : μ.IsAW hk a b c)
    (h₁ : μ.IsAW e₁ (δ n n₁ a) b c₁) (h₂ : μ.IsAW e₂ a (δ m m₁ b) c₂) (N : ℕ) (w w' : ℤ) (h : -(N : ℤ) + k = w)
    (h' : -(N : ℤ) + k₁ = w') (x : Sx E N U) :
    Sec.map (K.d w w') (ev c N w h U x) + sg k₁ • rem μ a b w' x = ev c₁ N w' h' U x + sg n • ev c₂ N w' h' U x := by
  rw [ev_aw μ hc, ev_aw μ h₁, ev_aw μ h₂, rem, Sec.map, map_sum, smul_add, Finset.smul_sum, Finset.smul_sum, Finset.smul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  rintro ⟨p, r⟩ hq
  have hN : p + r = N := by simpa using hq
  dsimp only
  have hd := d_pv μ hn hm a b w w' (by omega) p r (cl x 0 p) (cl x p r) (by omega)
  rw [Sec.map] at hd
  rw [map_zsmul, hd]
  clear hd
  subst hn hm hk hk₁
  have e : sg ((m + 1) * p) = sg (m * p) * sg p := by rw [add_mul, one_mul, sg_add]
  rw [e]
  simp only [sg_add, sg_neg, sg_one]
  have q1 := sg_sq m
  have q2 := sg_sq n
  have q3 := sg_sq p
  generalize sg m = α at *
  generalize sg n = β at *
  generalize sg p = γ at *
  generalize sg (m * p) = ε at *
  match_scalars
  · ring
  · linear_combination (-(β * ε)) * q1
  · ring
  · ring

theorem aw_leibniz {k n₁ m₁ k₁ : ℤ} {hk : n + m = k} (hn : n + 1 = n₁) (hm : m + 1 = m₁) (hk₁ : k + 1 = k₁)
    {a : Cochain ((chains R).obj E) I n} {b : Cochain ((chains R).obj E) J m} {c : Cochain ((chains R).obj E) K k}
    {c₁ c₂ : Cochain ((chains R).obj E) K k₁} {e₁ : n₁ + m = k₁} {e₂ : n + m₁ = k₁} (hc : μ.IsAW hk a b c)
    (h₁ : μ.IsAW e₁ (δ n n₁ a) b c₁) (h₂ : μ.IsAW e₂ a (δ m m₁ b) c₂) : δ k k₁ c = c₁ + n.negOnePow • c₂ := by
  refine ev_ext _ _ fun N w' h' U x => ?_
  rw [ev_add, sg_smul, ev_zsmul, ← d_ev_aw μ hn hm hk₁ hc h₁ h₂ N _ w' rfl h' x]
  cases N with
  | zero => rw [ev_δ_zero hk₁ c U _ w' rfl, rem_zero, smul_zero, add_zero]
  | succ N => rw [ev_δ_succ hk₁ c U N _ w' rfl, rem_succ μ hc N w' (by omega), sg_smul]

end Leibniz

end GlobalTheory.EtC.CupSpec

end
