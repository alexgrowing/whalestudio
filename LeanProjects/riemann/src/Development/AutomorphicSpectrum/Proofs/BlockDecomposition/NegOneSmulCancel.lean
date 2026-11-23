import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.CechDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.TotPairing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DvMemOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeZigzagCompat

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeZig

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (A : C ⥤ CommAlgCat.{0} R)

abbrev Ch (U : ObjectProperty C) (q : ℕ) : Type 1 := CH.Cn (CH.modF (U.ι ⋙ A)) q

def rM {U V : ObjectProperty C} (h : V ≤ U) :
    CH.Mor (CH.modF (U.ι ⋙ A)) (CH.modF (V.ι ⋙ A)) (RingHom.id R) where
  G := ObjectProperty.ιOfLE h
  τ _ := LinearMap.id
  nat _ _ := rfl

variable {A}

theorem d_resB {U V : ObjectProperty C} (h : V ≤ U) {k : ℕ} (x : Ch A U k) :
    CH.d _ k (resB A h x) = resB A h (CH.d _ k x) := (rM A h).d_pullC k x

theorem resB_resB {U V T : ObjectProperty C} (h : V ≤ U) (h' : T ≤ V) (h'' : T ≤ U) {k : ℕ} (x : Ch A U k) :
    resB A h' (resB A h x) = resB A h'' x := rfl

theorem resB_sub {U V : ObjectProperty C} (h : V ≤ U) {k : ℕ} (x y : Ch A U k) :
    resB A h (x - y) = resB A h x - resB A h y := map_sub ((rM A h).pullC k) x y

def Lm (a : IdF A) (U : ObjectProperty C) (q : ℕ) : Submodule R (Ch A U q) where
  carrier := {x | ∀ σ, x σ ∈ a.S _}
  add_mem' hx hy σ := (a.S _).add_mem (hx σ) (hy σ)
  zero_mem' σ := (a.S _).zero_mem
  smul_mem' r x hx σ := by
    change r • x σ ∈ a.S _
    exact Submodule.smul_of_tower_mem (a.S _) r (hx σ)

theorem Lm_d {a : IdF A} {U : ObjectProperty C} {q : ℕ} {x : Ch A U q} (hx : x ∈ Lm a U q) :
    CH.d _ q x ∈ Lm a U (q + 1) := by
  intro σ
  change ∑ i : Fin (q + 2), (-1 : ℤ) ^ (i : ℕ) • _ ∈ a.S _
  refine (a.S _).sum_mem fun i _ => ?_
  exact Submodule.smul_of_tower_mem (a.S _) _ (a.map_mem _ (hx _))

theorem Lm_res {a : IdF A} {U V : ObjectProperty C} (h : V ≤ U) {q : ℕ} {x : Ch A U q} (hx : x ∈ Lm a U q) :
    resB A h x ∈ Lm a V q := fun σ => hx (σ ⋙ ObjectProperty.ιOfLE h)

theorem Lm_le {a b : IdF A} (hab : ∀ T, a.S T ≤ b.S T) {U : ObjectProperty C} {q : ℕ} {x : Ch A U q}
    (hx : x ∈ Lm a U q) : x ∈ Lm b U q := fun σ => hab _ (hx σ)

theorem Lm_cup {a b c : IdF A} (habc : ∀ (T : C) (x y : A.obj T), x ∈ a.S T → y ∈ b.S T → x * y ∈ c.S T)
    {U : ObjectProperty C} {p q n : ℕ} (e : p + q = n) {x : Ch A U p} {y : Ch A U q}
    (hx : x ∈ Lm a U p) (hy : y ∈ Lm b U q) : (CH.mulP (U.ι ⋙ A)).cupC e x y ∈ Lm c U n := by
  intro σ
  exact habc _ _ _ (a.map_mem _ (hx ((CH.front_mono e).functor ⋙ σ))) (b.map_mem _ (hy ((CH.back_mono e).functor ⋙ σ)))

variable {N : ℕ} (W : Fin N → ObjectProperty C)

def fc {p : ℕ} (k : Fin (p + 2)) (i : Idx (p + 2) N) : Idx (p + 1) N :=
  ⟨i.1 ∘ k.succAbove, i.2.comp (Fin.strictMono_succAbove k)⟩

theorem cap_le {p : ℕ} (k : Fin (p + 2)) (i : Idx (p + 2) N) : capT W i.1 ≤ capT W (fc k i).1 :=
  fun _ h _ => h _

theorem x_congr {ι : Type} {f : ι → ObjectProperty C} {V : ObjectProperty C} {q : ℕ} (x : ∀ i, Ch A (f i) q)
    {i i' : ι} (e : i = i') (h : V ≤ f i) (h' : V ≤ f i') : resB A h (x i) = resB A h' (x i') := by
  subst e; rfl

variable (A)

def cosK : CosCx.{1} R where
  K p :=
    { X := fun q => ∀ i : Idx (p + 1) N, Ch A (capT W i.1) q
      d := fun q => LinearMap.pi fun i => (CH.d _ q).comp (LinearMap.proj i)
      dd := fun q x => funext fun i => CH.d_d _ q (x i) }
  δ p k := ⟨fun q => LinearMap.pi fun i => ((rM A (cap_le W k i)).pullC q).comp (LinearMap.proj (fc k i)),
    fun q x => funext fun i => (rM A (cap_le W k i)).d_pullC q (x (fc k i))⟩
  rel p j t q x := by
    funext i
    have e : fc (t.predAbove j) (fc (j.succAbove t) i) = fc t (fc j i) :=
      Subtype.ext (funext fun k => congrArg i.1 (Fin.succAbove_succAbove_succAbove_predAbove j t k))
    exact x_congr (f := fun i : Idx (p + 1) N => capT W i.1) x e (fun _ h _ => h _) (fun _ h _ => h _)

abbrev KK : DCx.{1} R := (cosK A W).dcx

variable {A W}

theorem dv_apply {p q : ℕ} (x : (KK A W).X p q) (i : Idx (p + 1) N) : (KK A W).dv p q x i = CH.d _ q (x i) := rfl

theorem dh_apply {p q : ℕ} (x : (KK A W).X p q) (i : Idx (p + 2) N) :
    (KK A W).dh p q x i = ∑ k : Fin (p + 2), (-1 : ℤ) ^ (k : ℕ) • resB A (cap_le W k i) (x (fc k i)) := by
  refine (congrFun (Cos.d_apply ((cosK A W).cos q) p x) i).trans ?_
  rw [Finset.sum_apply]
  rfl

def dfil (Fil : ℤ → IdF A) (hanti : ∀ {r r' : ℤ}, r ≤ r' → ∀ T, (Fil r').S T ≤ (Fil r).S T) :
    GlobalTheory.CompanionTheory.ConeCech.DFil (KK A W) where
  L r p q := Submodule.pi Set.univ fun i : Idx (p + 1) N => Lm (Fil r) (capT W i.1) q
  mem_h r p q x hx i _ := by
    rw [dh_apply]
    refine Submodule.sum_mem _ fun k _ => ?_
    exact Submodule.smul_of_tower_mem _ _ (Lm_res _ (hx _ trivial))
  mem_v r p q x hx i _ := Lm_d (hx i trivial)
  anti h p q x hx i _ := Lm_le (hanti h) (hx i trivial)

end GlobalTheory.CompanionTheory.ConeZig

namespace GlobalTheory.CompanionTheory.ConeZig

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R}

def bm {U V : ObjectProperty C} (h : V ≤ U) (l : Ch A V 1) (q : ℕ) : Ch A U q →ₗ[R] Ch A V (q + 1) :=
  ((CH.mulP (V.ι ⋙ A)).cupC (rfl : q + 1 = q + 1)).flip l ∘ₗ (rM A h).pullC q

theorem bm_apply {U V : ObjectProperty C} (h : V ≤ U) (l : Ch A V 1) {q : ℕ} (x : Ch A U q) :
    bm h l q x = (CH.mulP (V.ι ⋙ A)).cupC rfl (resB A h x) l := rfl

theorem res_bm {U V T : ObjectProperty C} (h : V ≤ U) (h' : T ≤ V) (h'' : T ≤ U) (l : Ch A V 1) {q : ℕ} (x : Ch A U q) :
    resB A h' (bm h l q x) = bm h'' (resB A h' l) q x := rfl

theorem bm_add {U V : ObjectProperty C} (h : V ≤ U) (l l' : Ch A V 1) {q : ℕ} (x : Ch A U q) :
    bm h (l + l') q x = bm h l q x + bm h l' q x := by
  simp only [bm_apply, map_add]

theorem bm_congr {ι : Type} {f : ι → ObjectProperty C} {V : ObjectProperty C} {q : ℕ} (x : ∀ i, Ch A (f i) q)
    {i i' : ι} (e : i = i') (h : V ≤ f i) (h' : V ≤ f i') (l : Ch A V 1) : bm h l q (x i) = bm h' l q (x i') := by
  subst e; rfl

variable {N : ℕ} {W : Fin N → ObjectProperty C} (b : ∀ α, Ch A (W α) 1)

theorem capT_at {m : ℕ} (i : Idx m N) (a : Fin m) : capT W i.1 ≤ W (i.1 a) := fun _ h => h a

def LL {m : ℕ} (i : Idx m N) (a c : Fin m) : Ch A (capT W i.1) 1 :=
  resB A (capT_at i a) (b (i.1 a)) - resB A (capT_at i c) (b (i.1 c))

theorem LL_add {m : ℕ} (i : Idx m N) (a c e : Fin m) : LL b i a c = LL b i a e + LL b i e c := by
  simp only [LL]; abel

theorem res_LL {m m' : ℕ} (i : Idx m N) (i' : Idx m' N) (h : capT W i.1 ≤ capT W i'.1) (a' c' : Fin m') (a c : Fin m)
    (ha : i'.1 a' = i.1 a) (hc : i'.1 c' = i.1 c) : resB A h (LL b i' a' c') = LL b i a c := by
  rw [LL, LL, resB_sub, resB_resB _ _ (h.trans (capT_at i' a')), resB_resB _ _ (h.trans (capT_at i' c'))]
  exact congrArg₂ (· - ·) (x_congr b ha _ _) (x_congr b hc _ _)

def BB (p q : ℕ) : (KK A W).X p q →ₗ[R] (KK A W).X (p + 1) (q + 1) :=
  LinearMap.pi fun i : Idx (p + 2) N => bm (cap_le W (Fin.last (p + 1)) i)
    (LL b i (Fin.last p).castSucc (Fin.last (p + 1))) q ∘ₗ LinearMap.proj (fc (Fin.last (p + 1)) i)

theorem BB_apply {p q : ℕ} (x : (KK A W).X p q) (i : Idx (p + 2) N) :
    BB b p q x i = bm (cap_le W (Fin.last (p + 1)) i) (LL b i (Fin.last p).castSucc (Fin.last (p + 1))) q
      (x (fc (Fin.last (p + 1)) i)) := rfl

theorem neg_one_smul_cancel {M : Type*} [AddCommGroup M] (s : ℤ) (X Y : M) :
    (s * -1) • X + (s * -1) • Y + (s * -1 * -1) • X = (s * -1) • Y := by
  have e : (s * -1 * -1) • X = - ((s * -1) • X) := by rw [mul_neg_one, mul_neg_one, neg_neg, neg_smul, neg_neg]
  rw [e]; abel

theorem BB_dh (p q : ℕ) (x : (KK A W).X p q) :
    (KK A W).dh (p + 1) (q + 1) (BB b p q x) = BB b (p + 1) q ((KK A W).dh p q x) := by
  funext i
  rw [dh_apply, BB_apply, dh_apply, map_sum]
  have hS : ∀ k : Fin (p + 2), bm (cap_le W (Fin.last (p + 2)) i)
      (LL b i (Fin.last (p + 1)).castSucc (Fin.last (p + 2))) q
      ((-1 : ℤ) ^ (k : ℕ) • resB A (cap_le W k (fc (Fin.last (p + 2)) i)) (x (fc k (fc (Fin.last (p + 2)) i)))) =
      (-1 : ℤ) ^ (k : ℕ) • bm (fun _ h _ => h _) (LL b i (Fin.last (p + 1)).castSucc (Fin.last (p + 2))) q
        (x (fc k (fc (Fin.last (p + 2)) i))) := fun k => by rw [map_zsmul]; rfl
  have h1 : ∀ j : Fin (p + 1), resB A (cap_le W j.castSucc.castSucc i) (BB b p q x (fc j.castSucc.castSucc i)) =
      bm (fun _ h _ => h _) (LL b i (Fin.last (p + 1)).castSucc (Fin.last (p + 2))) q
        (x (fc j.castSucc (fc (Fin.last (p + 2)) i))) := by
    intro j
    have e : fc (Fin.last (p + 1)) (fc j.castSucc.castSucc i) = fc j.castSucc (fc (Fin.last (p + 2)) i) := by
      refine Subtype.ext (funext fun t => congrArg i.1 ?_)
      have := j.2
      have := t.2
      apply Fin.ext
      simp only [Function.comp, CrystallineSemistableComparison.Auxff.sa_val, Fin.val_castSucc, Fin.val_last]
      split_ifs <;> omega
    have ha : (fc j.castSucc.castSucc i).1 (Fin.last p).castSucc = i.1 (Fin.last (p + 1)).castSucc := by
      refine congrArg i.1 ?_
      have := j.2
      apply Fin.ext
      simp only [CrystallineSemistableComparison.Auxff.sa_val, Fin.val_castSucc, Fin.val_last]
      split_ifs <;> omega
    have hc : (fc j.castSucc.castSucc i).1 (Fin.last (p + 1)) = i.1 (Fin.last (p + 2)) := by
      refine congrArg i.1 ?_
      have := j.2
      apply Fin.ext
      simp only [CrystallineSemistableComparison.Auxff.sa_val, Fin.val_castSucc, Fin.val_last]
      split_ifs <;> omega
    rw [BB_apply, res_bm _ _ (fun _ h _ => h _), res_LL b i _ _ _ _ _ _ ha hc]
    exact bm_congr (f := fun i : Idx (p + 1) N => capT W i.1) x e _ _ _
  have h2 : resB A (cap_le W (Fin.last (p + 1)).castSucc i) (BB b p q x (fc (Fin.last (p + 1)).castSucc i)) =
      bm (fun _ h _ => h _) (LL b i (Fin.last p).castSucc.castSucc (Fin.last (p + 2))) q
        (x (fc (Fin.last (p + 1)) (fc (Fin.last (p + 2)) i))) := by
    have e : fc (Fin.last (p + 1)) (fc (Fin.last (p + 1)).castSucc i) = fc (Fin.last (p + 1)) (fc (Fin.last (p + 2)) i) := by
      refine Subtype.ext (funext fun t => congrArg i.1 ?_)
      have := t.2
      apply Fin.ext
      simp only [Function.comp, CrystallineSemistableComparison.Auxff.sa_val, Fin.val_castSucc, Fin.val_last]
      split_ifs <;> omega
    have ha : (fc (Fin.last (p + 1)).castSucc i).1 (Fin.last p).castSucc = i.1 (Fin.last p).castSucc.castSucc := by
      refine congrArg i.1 ?_
      apply Fin.ext
      simp only [CrystallineSemistableComparison.Auxff.sa_val, Fin.val_castSucc, Fin.val_last]
      split_ifs <;> omega
    have hc : (fc (Fin.last (p + 1)).castSucc i).1 (Fin.last (p + 1)) = i.1 (Fin.last (p + 2)) := by
      refine congrArg i.1 ?_
      apply Fin.ext
      simp only [CrystallineSemistableComparison.Auxff.sa_val, Fin.val_castSucc, Fin.val_last]
      split_ifs <;> omega
    rw [BB_apply, res_bm _ _ (fun _ h _ => h _), res_LL b i _ _ _ _ _ _ ha hc]
    exact bm_congr (f := fun i : Idx (p + 1) N => capT W i.1) x e _ _ _
  have h3 : resB A (cap_le W (Fin.last (p + 2)) i) (BB b p q x (fc (Fin.last (p + 2)) i)) =
      bm (fun _ h _ => h _) (LL b i (Fin.last p).castSucc.castSucc (Fin.last (p + 1)).castSucc) q
        (x (fc (Fin.last (p + 1)) (fc (Fin.last (p + 2)) i))) := by
    have ha : (fc (Fin.last (p + 2)) i).1 (Fin.last p).castSucc = i.1 (Fin.last p).castSucc.castSucc := by
      refine congrArg i.1 ?_
      apply Fin.ext
      simp only [CrystallineSemistableComparison.Auxff.sa_val, Fin.val_castSucc, Fin.val_last]
      split_ifs <;> omega
    have hc : (fc (Fin.last (p + 2)) i).1 (Fin.last (p + 1)) = i.1 (Fin.last (p + 1)).castSucc := by
      refine congrArg i.1 ?_
      apply Fin.ext
      simp only [CrystallineSemistableComparison.Auxff.sa_val, Fin.val_castSucc, Fin.val_last]
      split_ifs <;> omega
    rw [BB_apply, res_bm _ _ (fun _ h _ => h _), res_LL b i _ _ _ _ _ _ ha hc]
  simp only [hS]
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc (n := p + 1)]
  refine (add_assoc _ _ _).trans (congrArg₂ (· + ·) (Finset.sum_congr rfl fun j _ => ?_) ?_)
  · rw [h1]; rfl
  · rw [h2, h3, LL_add b i (Fin.last p).castSucc.castSucc (Fin.last (p + 2)) (Fin.last (p + 1)).castSucc, bm_add]
    simp only [Fin.val_castSucc, Fin.val_last, smul_add, pow_succ]
    exact neg_one_smul_cancel _ _ _

variable {V : ObjectProperty C} (hWV : ∀ α, W α ≤ V) (z : Ch A V 2)

theorem d_LL (hb : ∀ α, resB A (hWV α) z = CH.d _ 1 (b α)) {m : ℕ} (i : Idx m N) (a c : Fin m) :
    CH.d _ 1 (LL b i a c) = 0 := by
  rw [LL, map_sub, d_resB, d_resB, ← hb, ← hb]
  exact sub_self _

theorem BB_dv (hb : ∀ α, resB A (hWV α) z = CH.d _ 1 (b α)) (p q : ℕ) (x : (KK A W).X p q) :
    (KK A W).dv (p + 1) (q + 1) (BB b p q x) = BB b p (q + 1) ((KK A W).dv p q x) := by
  funext i
  rw [dv_apply, BB_apply, BB_apply, bm_apply, bm_apply, CrystallineSemistableComparison.P.leibniz, d_LL b hWV z hb, map_zero, smul_zero, add_zero,
    d_resB]
  rfl

theorem capV (hW : ∀ α, W α ≤ V) {p : ℕ} (i : Idx (p + 1) N) : capT W i.1 ≤ V := (capT_at i 0).trans (hW _)

def aa (k : ℕ) : (KK A W).X 0 (2 * k) := fun i => resB A (capV hWV i) (cupPowC (V.ι ⋙ A) z k)

def gg (k : ℕ) : (KK A W).X 0 (2 * k + 1) := fun i =>
  (CH.mulP _).cupC rfl (resB A (capV hWV i) (cupPowC (V.ι ⋙ A) z k)) (resB A (capT_at i 0) (b (i.1 0)))

def PP (k : ℕ) : (KK A W).X k k :=
  Nat.rec (motive := fun k => (KK A W).X k k) (aa hWV z 0) (fun k y => (-1 : ℤ) ^ k • BB b k k y) k

theorem cupPow_d (A' : (V.FullSubcategory) ⥤ CommAlgCat.{0} R) (z : CH.Cn (CH.modF A') 2) (hz : CH.d _ 2 z = 0) (k : ℕ) :
    CH.d _ (2 * k) (cupPowC A' z k) = 0 := by
  induction k with
  | zero =>
    funext s
    change ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (A'.map (GlobalTheory.CatH.toLast i s)).hom 1 = (0 : A'.obj _)
    rw [Fin.sum_univ_two, map_one, map_one]
    simp
  | succ k ih =>
    change CH.d _ _ ((CH.mulP A').cupC _ (cupPowC A' z k) z) = 0
    rw [CrystallineSemistableComparison.P.leibniz, ih, hz]
    simp

theorem gg_dv (hz : CH.d _ 2 z = 0) (hb : ∀ α, resB A (hWV α) z = CH.d _ 1 (b α)) (k : ℕ) :
    (KK A W).dv 0 (2 * k + 1) (gg b hWV z k) = aa hWV z (k + 1) := by
  funext i
  rw [dv_apply]
  change CH.d _ _ ((CH.mulP _).cupC _ _ _) = _
  rw [CrystallineSemistableComparison.P.leibniz, d_resB, cupPow_d _ z hz, d_resB, ← hb]
  have e : ((-1 : ℤ) ^ (2 * k)) = 1 := by rw [pow_mul]; simp
  rw [e, one_smul]
  have h0 : resB A (capV hWV i) (0 : Ch A V (2 * k + 1)) = 0 := map_zero ((rM A (capV hWV i)).pullC _)
  rw [h0, map_zero, LinearMap.zero_apply]
  exact zero_add _

theorem gg_dh (k : ℕ) : (KK A W).dh 0 (2 * k + 1) (gg b hWV z k) = - BB b 0 (2 * k) (aa hWV z k) := by
  funext i
  rw [dh_apply, Fin.sum_univ_two]
  have h0 : resB A (cap_le W 0 i) (gg b hWV z k (fc 0 i)) = (CH.mulP _).cupC rfl (resB A (capV hWV i) (cupPowC (V.ι ⋙ A) z k))
      (resB A (capT_at i 1) (b (i.1 1))) := by
    have e : (fc 0 i).1 0 = i.1 1 := rfl
    have e' := x_congr b e (V := capT W i.1) (fun _ h => h _) (capT_at i 1)
    exact congrArg ((CH.mulP _).cupC rfl (resB A (capV hWV i) (cupPowC (V.ι ⋙ A) z k))) e'
  have h1 : resB A (cap_le W 1 i) (gg b hWV z k (fc 1 i)) = (CH.mulP _).cupC rfl (resB A (capV hWV i) (cupPowC (V.ι ⋙ A) z k))
      (resB A (capT_at i 0) (b (i.1 0))) := by
    have e : (fc 1 i).1 0 = i.1 0 := rfl
    have e' := x_congr b e (V := capT W i.1) (fun _ h => h _) (capT_at i 0)
    exact congrArg ((CH.mulP _).cupC rfl (resB A (capV hWV i) (cupPowC (V.ι ⋙ A) z k))) e'
  have hL : LL b i (Fin.last 0).castSucc (Fin.last 1) = resB A (capT_at i 0) (b (i.1 0)) - resB A (capT_at i 1) (b (i.1 1)) := rfl
  rw [h0, h1, Pi.neg_apply, BB_apply, hL, bm_apply]
  have hy : resB A (cap_le W (Fin.last 1) i) (aa hWV z k (fc (Fin.last 1) i)) = resB A (capV hWV i) (cupPowC (V.ι ⋙ A) z k) := rfl
  rw [hy, map_sub]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul]
  abel

end GlobalTheory.CompanionTheory.ConeZig
