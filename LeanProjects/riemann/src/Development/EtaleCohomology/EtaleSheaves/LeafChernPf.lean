import Development.EtaleCohomology.EtaleSheaves.InstCommRingR

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.D2.ChernPf

theorem cast_rfl {q : ℕ} {E : Spc} {n i : ℤ} (x : Ht q E n i) (h1 : n = n) (h2 : i = i) : x.cast h1 h2 = x := rfl

theorem cast_cast {q : ℕ} {E : Spc} {n i n' i' n'' i'' : ℤ} (x : Ht q E n i) (h1 : n = n') (h2 : i = i')
    (h3 : n' = n'') (h4 : i' = i'') : (x.cast h1 h2).cast h3 h4 = x.cast (h1.trans h3) (h2.trans h4) := by
  subst h1 h2 h3 h4; rfl

theorem term {q : ℕ} (P : Collected q) {E F : Spc} (f : F ⟶ E) (h : Inv q E) (h' : Inv q F) (y : Ht q F 2 1)
    {n' i' : ℤ} (u : Ht q E n' i') (k m N : ℕ) (hN : k + m = N) (hn : n' = 2 * (k : ℤ)) (hi : i' = k)
    (h1 : n' + 2 * (m : ℤ) = 2 * (N : ℤ)) (h2 : i' + (m : ℤ) = N) :
    P.ι h' N ((cup q (pull _ f _ _ u) (cpow q y m)).cast h1 h2) =
      P.map f h' h (P.ι h k (u.cast hn hi)) * P.ι h' m (cpow q y m) := by
  subst hN hn hi
  rw [cast_rfl, P.map_ι]
  exact P.ι_mul h' k m _ _

variable {q : ℕ} {E : Spc} {N : ℕ}

def Phi (V : E ⟶ ofCat (glCat N)) (a : ∀ j : Fin N, Ht q E (2 * (N : ℤ) - 2 * ((j : ℕ) : ℤ)) ((N : ℤ) - ((j : ℕ) : ℤ))) :
    Ht q (PB V) (2 * (N : ℤ)) N :=
  ∑ j : Fin N, ((cup q (pull _ (pullback.fst V (PGL.pr N)) _ _ (a j))
      (cpow q (c1 q (pullback.snd V (PGL.pr N) ≫ PGL.line N)) j)).cast (by ring) (by ring) : Ht q _ (2 * (N : ℤ)) N)

def ac (c : ∀ j : ℕ, Ht q E (2 * j) j) : ∀ j : Fin N, Ht q E (2 * (N : ℤ) - 2 * ((j : ℕ) : ℤ)) ((N : ℤ) - ((j : ℕ) : ℤ)) :=
  fun j => (c (N - j)).cast (by have := j.isLt; omega) (by have := j.isLt; omega)

theorem phi_ι (P : Collected q) (h : Inv q E) (V : E ⟶ ofCat (glCat N))
    (a : ∀ j : Fin N, Ht q E (2 * (N : ℤ) - 2 * ((j : ℕ) : ℤ)) ((N : ℤ) - ((j : ℕ) : ℤ))) :
    P.ι (inv_of (PB.pr V) h) N (Phi V a) = ∑ j : Fin N, P.map (PB.pr V) (inv_of (PB.pr V) h) h
      (P.ι h (N - j) ((a j).cast (by have := j.isLt; omega) (by have := j.isLt; omega))) *
      P.deg1 (inv_of (PB.pr V) h) (c1 q (PB.line V)) ^ (j : ℕ) := by
  unfold Phi
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [term P (PB.pr V) h (inv_of (PB.pr V) h) _ (a j) (N - j) j N (by have := j.isLt; omega)
    (by have := j.isLt; omega) (by have := j.isLt; omega), P.ι_cpow]

end LateralTheory.E.D2.ChernPf

namespace LateralTheory.E.D2.ChernPf
variable {q : ℕ} {E : Spc} {N : ℕ}

theorem cast_inj {n i n' i' : ℤ} {x y : Ht q E n i} (h1 : n = n') (h2 : i = i') (e : x.cast h1 h2 = y.cast h1 h2) : x = y := by
  subst h1 h2; exact e

theorem cast_idx {n i : Fin N → ℤ} (a : ∀ j, Ht q E (n j) (i j)) (j j' : Fin N) (e : j = j')
    (h1 : n j = n j') (h2 : i j = i j') : (a j).cast h1 h2 = a j' := by
  subst e; rfl

theorem sum_eq (P : Collected q) (h : Inv q E) (V : E ⟶ ofCat (glCat N)) (c : ∀ j : ℕ, Ht q E (2 * j) j)
    (h0 : P.ι h 0 (c 0) = 1) :
    ∑ j ∈ Finset.range (N + 1), P.map (PB.pr V) (inv_of (PB.pr V) h) h (P.ι h j (c j)) *
      P.deg1 (inv_of (PB.pr V) h) (c1 q (PB.line V)) ^ (N - j) =
      P.deg1 (inv_of (PB.pr V) h) (c1 q (PB.line V)) ^ N + P.ι (inv_of (PB.pr V) h) N (Phi V (ac c)) := by
  have key : ∀ g : ℕ → P.R (PB V) (inv_of (PB.pr V) h),
      ∑ j ∈ Finset.range (N + 1), g j = ∑ j ∈ Finset.range N, g (N - j) + g 0 := by
    intro g
    rw [← Finset.sum_range_reflect, Finset.sum_range_succ]
    simp
  rw [key, phi_ι P h V, h0, map_one, one_mul, Nat.sub_zero, add_comm, Finset.sum_range]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Nat.sub_sub_self j.isLt.le]
  dsimp only [ac]
  rw [ChernPf.cast_cast, cast_rfl]

def mkc (a : ∀ j : Fin N, Ht q E (2 * (N : ℤ) - 2 * ((j : ℕ) : ℤ)) ((N : ℤ) - ((j : ℕ) : ℤ))) : ∀ j : ℕ, Ht q E (2 * j) j :=
  fun j => if h0 : j = 0 then (one q E).cast (by simp [h0]) (by simp [h0])
    else if hj : j ≤ N then (a ⟨N - j, by omega⟩).cast (by simp; omega) (by simp; omega) else 0

end LateralTheory.E.D2.ChernPf

namespace LateralTheory.E.D2
open ChernPf

theorem LeafChern_of : LeafChern := by
  intro hD1 q _ P E h N V
  have hB : Function.Bijective (Phi (q := q) V) := hD1 q V h (2 * (N : ℤ)) N
  have hι : ∀ {F : Spc} (h : Inv q F) k, Function.Injective (P.ι h k) := fun h k a b e => by
    simpa [P.π_ι] using congrArg (P.π h k) e
  have char : ∀ c, P.ι h 0 (c 0) = 1 → (IsChern P h V c ↔
      (∀ j, N < j → c j = 0) ∧ Phi V (ac c) = -cpow q (c1 q (PB.line V)) N) := by
    intro c h0
    unfold IsChern
    rw [sum_eq P h V c h0, ← P.ι_cpow, ← map_add, map_eq_zero_iff _ (hι _ _), add_eq_zero_iff_neg_eq, eq_comm]
    simp only [h0, true_and]
    exact and_congr_right fun _ => eq_comm
  have uniq : ∀ c c', IsChern P h V c → IsChern P h V c' → c = c' := by
    intro c c' hc hc'
    have hA : ac c = ac c' := hB.1 (((char c hc.1).1 hc).2.trans ((char c' hc'.1).1 hc').2.symm)
    funext j
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · exact hι h 0 (hc.1.trans hc'.1.symm)
    by_cases hjN : N < j
    · rw [hc.2.1 j hjN, hc'.2.1 j hjN]
    have := cast_inj _ _ (congrFun hA ⟨N - j, by omega⟩)
    have e : N - ((⟨N - j, by omega⟩ : Fin N) : ℕ) = j := by simp; omega
    rw [e] at this
    exact this
  obtain ⟨a, ha⟩ := hB.2 (-cpow q (c1 q (PB.line V)) N)
  have hc0 : P.ι h 0 (mkc a 0) = 1 := by
    dsimp only [mkc]
    rw [dif_pos rfl]
    exact P.ι_one h
  have hac : ac (mkc a) = a := by
    funext j
    dsimp only [ac, mkc]
    rw [dif_neg (by omega), dif_pos (by omega), ChernPf.cast_cast]
    exact cast_idx a _ _ (Fin.ext (by simp; omega)) _ _
  have hC : IsChern P h V (mkc a) := (char _ hc0).2 ⟨fun j hj => by
    dsimp only [mkc]
    rw [dif_neg (by omega), dif_neg (by omega)], by rw [hac]; exact ha⟩
  exact ⟨mkc a, hC, fun c' hc' => uniq _ _ hc' hC⟩

end LateralTheory.E.D2
