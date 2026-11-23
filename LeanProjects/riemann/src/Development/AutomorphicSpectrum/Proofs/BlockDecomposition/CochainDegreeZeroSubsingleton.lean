import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Polynomial CrystallineSemistableComparison CrystallineSemistableComparison.CH
universe w w' v u v' u' v'' u''

open GlobalTheory.CatH (face toLast)

namespace GlobalTheory.CompanionTheory.NatCoh

abbrev Mn : Type := SingleObj (Multiplicative ℕ)

abbrev Ch (n : ℕ) : Type := ComposableArrows Mn n

def val {x y : Mn} (h : x ⟶ y) : ℕ := Multiplicative.toAdd (show Multiplicative ℕ from h)

theorem val_comp {x y z : Mn} (f : x ⟶ y) (g : y ⟶ z) : val (f ≫ g) = val f + val g := by
  change Multiplicative.toAdd ((show Multiplicative ℕ from g) * (show Multiplicative ℕ from f)) = _
  rw [toAdd_mul, add_comm]; rfl

theorem val_id (x : Mn) : val (𝟙 x) = 0 := rfl

def natF : ℕ ⥤ Mn where
  obj _ := SingleObj.star _
  map {i j} _ := (Multiplicative.ofAdd (j - i) : Multiplicative ℕ)
  map_id i := by
    change Multiplicative.ofAdd (i - i) = 1
    simp
  map_comp {i j k} f g := by
    have h1 := leOfHom f
    have h2 := leOfHom g
    change Multiplicative.ofAdd (k - i) = Multiplicative.ofAdd (k - j) * Multiplicative.ofAdd (j - i)
    rw [← ofAdd_add]
    congr 1
    omega

def ch {n : ℕ} (c : Fin (n + 1) → ℕ) (hc : Monotone c) : Ch n := hc.functor ⋙ natF

theorem val_ch {n : ℕ} (c : Fin (n + 1) → ℕ) (hc : Monotone c) {i j : Fin (n + 1)} (φ : i ⟶ j) :
    val ((ch c hc).map φ) = c j - c i := rfl

theorem chain_ext {n : ℕ} {s t : Ch n} (h : ∀ (i j : Fin (n + 1)) (φ : i ⟶ j), val (s.map φ) = val (t.map φ)) : s = t := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) fun i j φ => ?_
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
  exact (Multiplicative.toAdd).injective (h i j φ)

theorem ch_congr {n : ℕ} {c c' : Fin (n + 1) → ℕ} (hc : Monotone c) (hc' : Monotone c') (h : c = c') : ch c hc = ch c' hc' := by
  subst h; rfl

def ht {n : ℕ} (s : Ch n) (i : Fin (n + 1)) : ℕ := val (s.map (homOfLE (Fin.zero_le i)))

theorem ht_add {n : ℕ} (s : Ch n) {i j : Fin (n + 1)} (h : i ≤ j) :
    ht s j = ht s i + val (s.map (homOfLE h)) := by
  unfold ht
  rw [← val_comp, ← s.map_comp]
  rfl

theorem ht_mono {n : ℕ} (s : Ch n) : Monotone (ht s) := fun i j h => by
  rw [ht_add s h]; omega

theorem ch_ht {n : ℕ} (s : Ch n) : s = ch (ht s) (ht_mono s) := by
  refine chain_ext fun i j φ => ?_
  have h := leOfHom φ
  rw [val_ch, ht_add s h]
  have : φ = homOfLE h := Subsingleton.elim _ _
  rw [this]; omega

theorem exists_ch {n : ℕ} (s : Ch n) : ∃ c hc, s = ch c hc := ⟨_, _, ch_ht s⟩

theorem face_ch {n : ℕ} (j : Fin (n + 2)) (c : Fin (n + 2) → ℕ) (hc : Monotone c) :
    face j (ch c hc) = ch (c ∘ j.succAbove) (hc.comp (Fin.strictMono_succAbove j).monotone) := rfl

def sn {n : ℕ} (c : Fin (n + 1) → ℕ) (t : ℕ) : Fin (n + 2) → ℕ := Fin.snoc (α := fun _ => ℕ) c t

@[simp] theorem sn_castSucc {n : ℕ} (c : Fin (n + 1) → ℕ) (t : ℕ) (i : Fin (n + 1)) : sn c t i.castSucc = c i := by
  simp [sn]

@[simp] theorem sn_last {n : ℕ} (c : Fin (n + 1) → ℕ) (t : ℕ) : sn c t (Fin.last _) = t := by
  simp [sn]

theorem sn_mono {n : ℕ} {c : Fin (n + 1) → ℕ} (hc : Monotone c) {t : ℕ} (h : c (Fin.last n) ≤ t) : Monotone (sn c t) := by
  intro i j hij
  induction j using Fin.lastCases with
  | last =>
    induction i using Fin.lastCases with
    | last => exact le_rfl
    | cast i => rw [sn_castSucc, sn_last]; exact (hc (Fin.le_last i)).trans h
  | cast j =>
    induction i using Fin.lastCases with
    | last =>
      exfalso
      have : (Fin.last _ : Fin (n + 2)).1 ≤ j.castSucc.1 := hij
      simp at this
      have := j.2
      omega
    | cast i =>
      rw [sn_castSucc, sn_castSucc]
      exact hc (by simpa using hij)

def E {n : ℕ} (b : ℕ) (s : Ch n) : Ch (n + 1) :=
  ch (sn (ht s) (ht s (Fin.last n) + b)) (sn_mono (ht_mono s) (Nat.le_add_right _ _))

theorem E_ch {n : ℕ} (b : ℕ) (c : Fin (n + 1) → ℕ) (hc : Monotone c) :
    E b (ch c hc) = ch (sn c (c (Fin.last n) + b)) (sn_mono hc (Nat.le_add_right _ _)) := by
  refine chain_ext fun i j φ => ?_
  have hij := leOfHom φ
  have key : ∀ x, ht (ch c hc) x = c x - c 0 := fun x => rfl
  have h0 : ∀ x, c 0 ≤ c x := fun x => hc (Fin.zero_le x)
  unfold E
  rw [val_ch, val_ch]
  induction j using Fin.lastCases with
  | last =>
    induction i using Fin.lastCases with
    | last => simp
    | cast i =>
      simp only [sn_castSucc, sn_last, key]
      have := h0 i
      have := h0 (Fin.last n)
      have := hc (Fin.le_last i)
      omega
  | cast j =>
    induction i using Fin.lastCases with
    | last =>
      exfalso
      have : (Fin.last _ : Fin (n + 2)).1 ≤ j.castSucc.1 := hij
      simp at this
      have := j.2
      omega
    | cast i =>
      simp only [sn_castSucc, key]
      have := h0 i
      have := h0 j
      have := hc (show i ≤ j by simpa using hij)
      omega

def len {n : ℕ} (s : Ch (n + 1)) : ℕ := val (toLast (Fin.last (n + 1)) s)

theorem ini_E {n : ℕ} (b : ℕ) (x : Ch n) : face (Fin.last (n + 1)) (E b x) = x := by
  obtain ⟨c, hc, rfl⟩ := exists_ch x
  rw [E_ch, face_ch]
  refine ch_congr _ _ (funext fun i => ?_)
  simp

theorem face_E {p : ℕ} (i : Fin (p + 1)) (b : ℕ) (y : Ch (p + 1)) :
    face i.castSucc.castSucc (E b y) = E b (face i.castSucc y) := by
  obtain ⟨c, hc, rfl⟩ := exists_ch y
  rw [E_ch, face_ch, face_ch, E_ch]
  refine ch_congr _ _ (funext fun x => ?_)
  have hl : ∀ {m : ℕ} (a : Fin (m + 1)), a.castSucc.succAbove (Fin.last m) = Fin.last (m + 1) := fun a => by
    have := a.2
    ext; simp [Fin.succAbove, Fin.lt_def]
    rw [if_neg (by omega)]; simp
  induction x using Fin.lastCases with
  | last => simp [hl]
  | cast x =>
    have : i.castSucc.castSucc.succAbove x.castSucc = (i.castSucc.succAbove x).castSucc := by
      ext; simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc]; split_ifs <;> simp
    simp [this, hl]

theorem face_EE {p : ℕ} (a b : ℕ) (m : Ch p) :
    face (Fin.last (p + 1)).castSucc (E b (E a m)) = E (a + b) m := by
  obtain ⟨c, hc, rfl⟩ := exists_ch m
  rw [E_ch, E_ch, face_ch, E_ch]
  refine ch_congr _ _ (funext fun x => ?_)
  induction x using Fin.lastCases with
  | last =>
    have : (Fin.last (p + 1)).castSucc.succAbove (Fin.last (p + 1)) = Fin.last (p + 2) := by
      ext; simp [Fin.succAbove, Fin.lt_def]
    simp [this, add_assoc]
  | cast x =>
    have : (Fin.last (p + 1)).castSucc.succAbove x.castSucc = x.castSucc.castSucc := by
      have := x.2
      ext; simp [Fin.succAbove, Fin.lt_def]
      rw [if_pos (by omega)]; simp
    simp [this]

theorem len_E {n : ℕ} (a : ℕ) (m : Ch n) : len (E a m) = a := by
  obtain ⟨c, hc, rfl⟩ := exists_ch m
  rw [E_ch]
  unfold len toLast
  rw [val_ch]
  simp

theorem E_surj {n : ℕ} (s : Ch (n + 1)) : E (len s) (face (Fin.last (n + 1)) s) = s := by
  obtain ⟨c, hc, rfl⟩ := exists_ch s
  have hl : len (ch c hc) = c (Fin.last _) - c (Fin.last n).castSucc := by
    unfold len toLast
    rw [val_ch]
    simp
  rw [hl, face_ch, E_ch]
  refine ch_congr _ _ (funext fun x => ?_)
  induction x using Fin.lastCases with
  | last =>
    have := hc (Fin.le_last (Fin.last n).castSucc)
    simp
    omega
  | cast x => simp

section Alg

variable {R : Type} [CommRing R] (N : Mn ⥤ ModuleCat.{w} R)

abbrev Vv : Type w := N.obj (SingleObj.star _)

def gp (k : ℕ) : Vv N →ₗ[R] Vv N :=
  (N.map (X := SingleObj.star _) (Y := SingleObj.star _) (Multiplicative.ofAdd k)).hom

theorem map_eq_gp {x y : Mn} (h : x ⟶ y) (v : Vv N) : (N.map h).hom v = gp N (val h) v := rfl

theorem gp_zero (v : Vv N) : gp N 0 v = v := by
  have : (N.map (X := SingleObj.star _) (Y := SingleObj.star _) (𝟙 _)).hom v = v := by
    rw [N.map_id]; rfl
  exact this

theorem gp_add (a b : ℕ) (v : Vv N) : gp N (a + b) v = gp N b (gp N a v) := by
  have : (N.map (X := SingleObj.star _) (Y := SingleObj.star _)
      ((show SingleObj.star (Multiplicative ℕ) ⟶ SingleObj.star _ from Multiplicative.ofAdd a) ≫
        (show SingleObj.star (Multiplicative ℕ) ⟶ SingleObj.star _ from Multiplicative.ofAdd b))).hom v =
      gp N b (gp N a v) := by
    rw [N.map_comp]; rfl
  rw [← this, map_eq_gp, val_comp]
  rfl

def dp {n : ℕ} (φ : Ch n → Vv N) (s : Ch (n + 1)) : Vv N :=
  ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) • φ (face i.castSucc s)

theorem d_eq {n : ℕ} (f : Ch n → Vv N) (s : Ch (n + 1)) :
    (d N n (f : Cn N n) s : Vv N) = dp N f s + (-1 : ℤ) ^ (n + 1) • gp N (len s) (f (face (Fin.last (n + 1)) s)) := by
  change ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (N.map (toLast i s)).hom (f (face i s)) = _
  rw [Fin.sum_univ_castSucc]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    have h : val (toLast i.castSucc s) = 0 := by
      have hl : i.castSucc.succAbove (Fin.last n) = Fin.last (n + 1) := by
        have := i.2
        ext; simp [Fin.succAbove, Fin.lt_def]
        rw [if_neg (by omega)]; simp
      have key : ∀ (x : Fin (n + 2)) (hx : x ≤ Fin.last (n + 1)), x = Fin.last (n + 1) → val (s.map (homOfLE hx)) = 0 := by
        intro x hx e
        subst e
        have : homOfLE hx = 𝟙 _ := Subsingleton.elim _ _
        rw [this, s.map_id]; rfl
      exact key _ _ hl
    rw [map_eq_gp, h, gp_zero]
    simp

theorem dp_add {n : ℕ} (φ ψ : Ch n → Vv N) (s : Ch (n + 1)) :
    dp N (fun x => φ x + ψ x) s = dp N φ s + dp N ψ s := by
  simp [dp, smul_add, Finset.sum_add_distrib]

theorem dp_zsmul {n : ℕ} (e : ℤ) (φ : Ch n → Vv N) (s : Ch (n + 1)) :
    dp N (fun x => e • φ x) s = e • dp N φ s := by
  simp only [dp, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _

theorem dp_map {n : ℕ} (g : Vv N →ₗ[R] Vv N) (φ : Ch n → Vv N) (s : Ch (n + 1)) :
    dp N (fun x => g (φ x)) s = g (dp N φ s) := by
  simp [dp, map_sum, map_zsmul]

theorem dp_zero {n : ℕ} (s : Ch (n + 1)) : dp N (fun _ : Ch n => 0) s = 0 := by
  simp [dp]

noncomputable def Pp (φ : ℕ → Vv N) : ℕ → Vv N
  | 0 => 0
  | a + 1 => gp N 1 (Pp φ a) + φ a

theorem dp_EE {p : ℕ} (φ : Ch (p + 1) → Vv N) (a b : ℕ) (m : Ch p) :
    dp N φ (E b (E a m)) = dp N (fun x => φ (E b x)) (E a m) + (-1 : ℤ) ^ (p + 1) • φ (E (a + b) m) := by
  unfold dp
  rw [Fin.sum_univ_castSucc]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [face_E]; simp
  · rw [face_EE]; simp

theorem d_EE {p : ℕ} (f : Ch (p + 1) → Vv N) (a b : ℕ) (m : Ch p) :
    (d N (p + 1) (f : Cn N (p + 1)) (E b (E a m)) : Vv N) =
      dp N (fun x => f (E b x)) (E a m) + (-1 : ℤ) ^ (p + 1) • f (E (a + b) m) +
        (-1 : ℤ) ^ (p + 2) • gp N b (f (E a m)) := by
  have h' := d_eq N f (E b (E a m))
  rwa [len_E, ini_E, dp_EE] at h'

theorem rel {p : ℕ} (f : Ch (p + 1) → Vv N) (hf : d N (p + 1) (f : Cn N (p + 1)) = 0) (a b : ℕ) (m : Ch p) :
    dp N (fun x => f (E b x)) (E a m) + (-1 : ℤ) ^ (p + 1) • f (E (a + b) m) +
      (-1 : ℤ) ^ (p + 2) • gp N b (f (E a m)) = 0 :=
  (d_EE N f a b m).symm.trans (congrFun hf (E b (E a m)))

theorem cocycle_zero {p : ℕ} (e : Ch (p + 2) → Vv N) (he : d N (p + 2) (e : Cn N (p + 2)) = 0)
    (h0 : ∀ k, e (E 0 k) = 0) (h1 : ∀ k, e (E 1 k) = 0) (s : Ch (p + 2)) : e s = 0 := by
  have key : ∀ (b : ℕ) (k : Ch (p + 1)), e (E b k) = 0 := by
    intro b k
    induction b with
    | zero => exact h0 k
    | succ b ih =>
      have h := rel N e he b 1 k
      have hz : (fun x => e (E 1 x)) = fun _ => 0 := funext h1
      rw [hz, dp_zero, ih, map_zero, smul_zero, add_zero, zero_add] at h
      have h2 := congrArg (fun v => (-1 : ℤ) ^ (p + 2) • v) h
      simpa [smul_smul, ← mul_pow, ← pow_add] using h2
  rw [← E_surj s]
  exact key _ _

theorem exact_hi {p : ℕ} (f : Ch (p + 2) → Vv N) (hf : d N (p + 2) (f : Cn N (p + 2)) = 0) :
    ∃ z : Ch (p + 1) → Vv N, ∀ t : Ch (p + 2), (d N (p + 1) (z : Cn N (p + 1)) t : Vv N) = f t := by
  set w : Ch p → Vv N := fun m => f (E 0 (E 0 m)) with hw
  set u : Ch (p + 1) → Vv N := fun x => f (E 1 x) with hu
  set v : Ch (p + 1) → Vv N := fun x => f (E 0 x) with hv
  let z : Ch (p + 1) → Vv N := fun s =>
    (-1 : ℤ) ^ (p + 1) • Pp N (fun i => u (E i (face (Fin.last (p + 1)) s))) (len s) +
      (-1 : ℤ) ^ p • gp N (len s) (w (face (Fin.last (p + 1)) s))
  have hz : ∀ a m, z (E a m) = (-1 : ℤ) ^ (p + 1) • Pp N (fun i => u (E i m)) a + (-1 : ℤ) ^ p • gp N a (w m) := by
    intro a m
    simp only [z, len_E, ini_E]
  have hz0 : (fun x => z (E 0 x)) = fun x => (-1 : ℤ) ^ p • w x := by
    funext x
    rw [hz]
    simp [Pp, gp_zero]
  have hz1 : (fun x => z (E 1 x)) = fun x => (-1 : ℤ) ^ (p + 1) • u (E 0 x) + (-1 : ℤ) ^ p • gp N 1 (w x) := by
    funext x
    rw [hz]
    simp [Pp]
  have hR0 : ∀ a m, dp N w (E a m) + (-1 : ℤ) ^ (p + 1) • f (E 0 (E a m)) = 0 := by
    intro a m
    have h := rel N f hf 0 0 (E a m)
    have h2 := dp_EE N v a 0 m
    simp only [Nat.add_zero, gp_zero] at h h2
    rw [pow_succ (-1 : ℤ) (p + 2), mul_neg_one, neg_smul, add_neg_cancel_right] at h
    exact h2.symm.trans h
  have hs0 : ∀ a m, (d N (p + 1) (z : Cn N (p + 1)) (E 0 (E a m)) : Vv N) = v (E a m) := by
    intro a m
    have h := hR0 a m
    change dp N w (E a m) + (-1 : ℤ) ^ (p + 1) • v (E a m) = 0 at h
    rw [d_EE, hz0, dp_zsmul]
    simp only [Nat.add_zero, gp_zero]
    rcases neg_one_pow_eq_or ℤ p with hp | hp <;> simp only [pow_succ, hp] at h ⊢
    · linear_combination (norm := module) h
    · linear_combination (norm := module) (-1 : ℤ) • h
  have hs1 : ∀ a m, (d N (p + 1) (z : Cn N (p + 1)) (E 1 (E a m)) : Vv N) = u (E a m) := by
    intro a m
    have hd : dp N (fun x => z (E 1 x)) (E a m) = (-1 : ℤ) ^ (p + 1) • dp N (fun x => u (E 0 x)) (E a m) +
        (-1 : ℤ) ^ p • gp N 1 (dp N w (E a m)) := by
      rw [hz1, dp_add, dp_zsmul, dp_zsmul, dp_map]
    have h0 : dp N w (E a m) + (-1 : ℤ) ^ (p + 1) • v (E a m) = 0 := hR0 a m
    have hG : gp N 1 (dp N w (E a m)) + (-1 : ℤ) ^ (p + 1) • gp N 1 (v (E a m)) = 0 := by
      have := congrArg (gp N 1) h0
      simpa only [map_add, map_zsmul, map_zero] using this
    have h1 : dp N u (E 0 (E a m)) + (-1 : ℤ) ^ (p + 2) • u (E a m) + (-1 : ℤ) ^ (p + 3) • gp N 1 (v (E a m)) = 0 :=
      rel N f hf 0 1 (E a m)
    have hB : dp N u (E 0 (E a m)) = dp N (fun x => u (E 0 x)) (E a m) + (-1 : ℤ) ^ (p + 1) • u (E a m) :=
      dp_EE N u a 0 m
    have hP : Pp N (fun i => u (E i m)) (a + 1) = gp N 1 (Pp N (fun i => u (E i m)) a) + u (E a m) := rfl
    rw [d_EE, hd, hz (a + 1) m, hz a m, hP, gp_add N a 1 (w m)]
    simp only [map_add, map_zsmul]
    rcases neg_one_pow_eq_or ℤ p with hp | hp <;> simp only [pow_succ, hp] at hG h1 hB ⊢
    · linear_combination (norm := module) hB - h1 + hG
    · linear_combination (norm := module) h1 - hB - hG
  refine ⟨z, fun t => ?_⟩
  let Dz : Ch (p + 2) → Vv N := d N (p + 1) (z : Cn N (p + 1))
  let e : Ch (p + 2) → Vv N := fun t => f t - Dz t
  have he : d N (p + 2) (e : Cn N (p + 2)) = 0 := by
    let fC : Cn N (p + 2) := f
    have : (e : Cn N (p + 2)) = fC - d N (p + 1) (z : Cn N (p + 1)) := rfl
    rw [this, map_sub]
    have hf' : d N (p + 2) fC = 0 := hf
    rw [hf', d_d, sub_zero]
  have h0 : ∀ k, e (E 0 k) = 0 := by
    intro k
    rw [← E_surj k]
    have : Dz (E 0 (E (len k) (face (Fin.last (p + 1)) k))) = f (E 0 (E (len k) (face (Fin.last (p + 1)) k))) := hs0 _ _
    exact sub_eq_zero.2 this.symm
  have h1 : ∀ k, e (E 1 k) = 0 := by
    intro k
    rw [← E_surj k]
    have : Dz (E 1 (E (len k) (face (Fin.last (p + 1)) k))) = f (E 1 (E (len k) (face (Fin.last (p + 1)) k))) := hs1 _ _
    exact sub_eq_zero.2 this.symm
  have h2 : f t - Dz t = 0 := cocycle_zero N e he h0 h1 t
  exact (sub_eq_zero.1 h2).symm

def m0 : Ch 0 := ch (fun _ => 0) monotone_const

theorem cochain_degree_zero_subsingleton (m m' : Ch 0) : m = m' := by
  refine chain_ext fun i j φ => ?_
  obtain rfl : i = j := Fin.ext (by have := i.2; have := j.2; omega)
  have : φ = 𝟙 _ := Subsingleton.elim _ _
  rw [this, m.map_id, m'.map_id]
  rfl

theorem dp0 (φ : Ch 0 → Vv N) (t : Ch 1) : dp N φ t = φ m0 := by
  change ∑ i : Fin 1, (-1 : ℤ) ^ (i : ℕ) • φ (face i.castSucc t) = φ m0
  rw [Fin.sum_univ_one, cochain_degree_zero_subsingleton (face _ t) m0]
  simp

theorem exact_one (σ : R) (hS : SurjUpTo σ (gp N 1 - LinearMap.id)) (y : Ch 1 → Vv N)
    (hy : d N 1 (y : Cn N 1) = 0) :
    ∃ x : Ch 0 → Vv N, ∀ t : Ch 1, (d N 0 (x : Cn N 0) t : Vv N) = σ • y t := by
  have hr : ∀ a b, y (E b m0) - y (E (a + b) m0) + gp N b (y (E a m0)) = 0 := by
    intro a b
    have h := rel N (p := 0) y hy a b m0
    rw [dp0] at h
    simpa [sub_eq_add_neg] using h
  have y0 : y (E 0 m0) = 0 := by simpa [gp_zero] using hr 0 0
  obtain ⟨x, hx⟩ := hS (y (E 1 m0))
  have hx' : gp N 1 x - x = σ • y (E 1 m0) := by simpa using hx
  have key : ∀ a, gp N a x - x = σ • y (E a m0) := by
    intro a
    induction a with
    | zero => rw [gp_zero, sub_self, y0, smul_zero]
    | succ a ih =>
      have h := hr a 1
      have e1 : y (E (a + 1) m0) = y (E 1 m0) + gp N 1 (y (E a m0)) := by
        linear_combination (norm := module) (-1 : ℤ) • h
      rw [e1, smul_add, ← map_smul, ← ih, gp_add, map_sub, ← hx']
      abel
  refine ⟨fun _ => -x, fun t => ?_⟩
  have e2 : E (len t) m0 = t := by
    have := E_surj t
    rwa [cochain_degree_zero_subsingleton (face _ t) m0] at this
  have h3 := key (len t)
  rw [e2] at h3
  rw [d_eq, dp0, ← h3]
  simp
  abel

end Alg

theorem resUpTo_of_acyc : ∀ {R : Type} [CommRing R] {M : Type w} [AddCommGroup M] [Module R M] (N : SingleObj (Multiplicative ℕ) ⥤ ModuleCat.{w} R) (a : M →ₗ[R] N.obj (SingleObj.star _)) (s : R), (∀ x, (N.map (X := SingleObj.star _) (Y := SingleObj.star _) (Multiplicative.ofAdd 1)).hom (a x) = a x) → InjUpTo s a → ExactUpTo s a ((N.map (X := SingleObj.star _) (Y := SingleObj.star _) (Multiplicative.ofAdd 1)).hom - LinearMap.id) → SurjUpTo s ((N.map (X := SingleObj.star _) (Y := SingleObj.star _) (Multiplicative.ofAdd 1)).hom - LinearMap.id) → (cx N).ResUpTo s (aug N fun _ => a) := by
  intro R _ M _ _ N a s hfix hinj hex hsurj
  have hg : ∀ k x, gp N k (a x) = a x := by
    intro k x
    induction k with
    | zero => exact gp_zero N _
    | succ k ih => rw [gp_add, ih]; exact hfix x
  refine ⟨fun x => ?_, fun x hx => ?_, fun y hy => ?_, fun n y hy => ?_⟩
  · funext t
    have h := d_eq N (n := 0) (fun _ => a x) t
    refine h.trans ?_
    rw [dp0, hg]
    simp
    rfl
  · exact hinj x (congrFun hx m0)
  · let y' : Ch 0 → Vv N := y
    have h1 : (d N 0 y (E 1 m0) : Vv N) = 0 := congrFun hy (E 1 m0)
    have h2 := d_eq N (n := 0) y' (E 1 m0)
    rw [dp0, len_E, ini_E] at h2
    have h3 : gp N 1 (y' m0) - y' m0 = 0 := by
      have h4 := h2.symm.trans h1
      have h5 : y' m0 - gp N 1 (y' m0) = 0 := by simpa [sub_eq_add_neg] using h4
      rw [← neg_sub, h5, neg_zero]
    obtain ⟨x, hx⟩ := hex (y' m0) (by rw [LinearMap.sub_apply]; exact h3)
    refine ⟨x, funext fun t => ?_⟩
    rw [cochain_degree_zero_subsingleton t m0]
    exact hx
  · cases n with
    | zero =>
      obtain ⟨x, hx⟩ := exact_one N s hsurj y hy
      exact ⟨x, funext hx⟩
    | succ p =>
      obtain ⟨z, hz⟩ := exact_hi N y hy
      refine ⟨s • (z : Cn N (p + 1)), ?_⟩
      change d N (p + 1) (s • (z : Cn N (p + 1))) = _
      rw [map_smul]
      exact congrArg (s • ·) (funext hz)

end GlobalTheory.CompanionTheory.NatCoh
