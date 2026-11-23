import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DpZeroRight
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb
open GlobalTheory.CatH (face toLast)

noncomputable section
namespace GlobalTheory.CompanionTheory.CocProd

theorem tele {B : Type*} [CommRing B] (P : ℕ → B) (m : ℕ) :
    P 0 + ∑ i ∈ Finset.range m, (-1 : B) ^ (i + 1) * (P (i + 1) + P i) = (-1) ^ m * P m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ← add_assoc, ih]
    ring

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {d : ℕ}
  (E : Frame Φ d) (σ : ∀ T : C, E.D ⟶ T)

theorem a_comp (i : Fin d) {T T' T'' : C} (φ : T ⟶ T') (ψ : T' ⟶ T'') :
    E.a σ i (φ ≫ ψ) = (Φ.A.map ψ).hom (E.a σ i φ) + E.a σ i ψ := by
  unfold Frame.a
  rw [E.add i (σ T ≫ φ ≫ ψ) (σ T' ≫ ψ) (σ T''), ← Category.assoc, E.nat]

def ga (i : Fin d) {n : ℕ} (s : ComposableArrows C n) (p q : Fin (n + 1)) (h : p ≤ q) :
    Φ.A.obj (s.obj (Fin.last n)) :=
  (Φ.A.map (s.map (homOfLE (Fin.le_last q)))).hom (E.a σ i (s.map (homOfLE h)))

theorem ga_add (i : Fin d) {n : ℕ} (s : ComposableArrows C n) (p q r : Fin (n + 1)) (h : p ≤ q) (h' : q ≤ r) :
    ga E σ i s p r (h.trans h') = ga E σ i s p q h + ga E σ i s q r h' := by
  unfold ga
  have e : s.map (homOfLE (h.trans h')) = s.map (homOfLE h) ≫ s.map (homOfLE h') := by
    rw [← s.map_comp]; rfl
  have e2 : s.map (homOfLE (Fin.le_last q)) = s.map (homOfLE h') ≫ s.map (homOfLE (Fin.le_last r)) := by
    rw [← s.map_comp]; rfl
  rw [e, a_comp, map_add, e2, Functor.map_comp]
  rfl

theorem ga_mem {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil) (i : Fin d) {n : ℕ} (s : ComposableArrows C n)
    (p q : Fin (n + 1)) (h : p ≤ q) : ga E σ i s p q h ∈ (Fil ((1 : ℕ) : ℤ)).S _ := by
  have : E.a σ i (s.map (homOfLE h)) ∈ (Fil 1).S _ := by
    rw [hF.one]; exact E.mem i _ _
  exact (Fil _).map_mem _ (by simpa using this)

theorem prod_mem {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil) {T : C} {j : ℕ} (f : Fin j → Φ.A.obj T)
    (hf : ∀ k, f k ∈ (Fil ((1 : ℕ) : ℤ)).S T) {q : ℕ} {x : Φ.A.obj T} (hx : x ∈ (Fil (q : ℤ)).S T) :
    (∏ k, f k) * x ∈ (Fil ((j + q : ℕ) : ℤ)).S T := by
  induction j with
  | zero =>
    simpa using hx
  | succ j ih =>
    rw [Fin.prod_univ_succ, mul_assoc]
    have := hF.mul 1 (j + q) T (hf 0) (ih (fun k => f k.succ) (fun k => hf k.succ))
    have e : 1 + (j + q) = j + 1 + q := by omega
    rwa [e] at this

theorem map_map {X Y Z : C} (g : X ⟶ Y) (f : Y ⟶ Z) (y : Φ.A.obj X) :
    (Φ.A.map f).hom ((Φ.A.map g).hom y) = (Φ.A.map (g ≫ f)).hom y := by
  simp

theorem face_form {j : ℕ} (I : Fin j → Fin d) (x : Φ.A.obj E.D) (s : ComposableArrows C (j + 1)) (i : Fin (j + 2)) :
    (Φ.A.map (toLast i s)).hom (E.form σ I x (face i s)) =
      (∏ k : Fin j, ga E σ (I k) s (i.succAbove k.castSucc) (i.succAbove k.succ)
        ((Fin.strictMono_succAbove i).monotone (Fin.castSucc_lt_succ (i := k)).le)) *
      (Φ.A.map (toLast i s)).hom ((Φ.A.map (σ _)).hom x) := by
  unfold Frame.form
  rw [map_mul, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  unfold ga
  rw [map_map]
  have e : (face i s).map (homOfLE (Fin.le_last k.succ)) ≫ toLast i s =
      s.map (homOfLE (Fin.le_last (i.succAbove k.succ))) := by
    change s.map _ ≫ s.map _ = _
    rw [← s.map_comp]; rfl
  rw [e]
  rfl

theorem sa_val {n : ℕ} (i : Fin (n + 1)) (m : Fin n) :
    ((i.succAbove m : Fin (n + 1)) : ℕ) = if (m : ℕ) < i then (m : ℕ) else m + 1 := by
  unfold Fin.succAbove
  split_ifs <;> simp_all [Fin.lt_def]

local macro "fa" : tactic =>
  `(tactic| (simp only [sa_val, Fin.val_castSucc, Fin.val_succ, Fin.val_last]; split_ifs <;> omega))

theorem ga_congr (i : Fin d) {n : ℕ} (s : ComposableArrows C n) {p q p' q' : Fin (n + 1)} (h : p ≤ q) (h' : p' ≤ q')
    (hp : (p : ℕ) = p') (hq : (q : ℕ) = q') : ga E σ i s p q h = ga E σ i s p' q' h' := by
  obtain rfl := Fin.ext hp
  obtain rfl := Fin.ext hq
  rfl

theorem sec_last {n : ℕ} (s : ComposableArrows C n) (p : Fin (n + 1)) (hp : p = Fin.last n) :
    σ (s.obj p) ≫ s.map (homOfLE (Fin.le_last p)) = σ (s.obj (Fin.last n)) := by
  subst hp
  have : (homOfLE (Fin.le_last (Fin.last n)) : Fin.last n ⟶ Fin.last n) = 𝟙 _ := Subsingleton.elim _ _
  rw [this, s.map_id, Category.comp_id]

theorem d_form_mem {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil) (hc : E.GrConst Fil) (j q : ℕ)
    (I : Fin j → Fin d) (x : Φ.A.obj E.D) (hx : x ∈ (Fil q).S E.D) (s : ComposableArrows C (j + 1)) :
    ∑ i : Fin (j + 2), (-1 : ℤ) ^ (i : ℕ) • (Φ.A.map (toLast i s)).hom (E.form σ I x (face i s)) ∈
      (Fil (((j : ℤ) + q) + 1)).S _ := by
  classical
  set u : Fin j → Φ.A.obj (s.obj (Fin.last (j + 1))) := fun k =>
    ga E σ (I k) s k.castSucc.castSucc k.succ.castSucc (by rw [Fin.le_def]; simp) with hu
  set v : Fin j → Φ.A.obj (s.obj (Fin.last (j + 1))) := fun k =>
    ga E σ (I k) s k.succ.castSucc k.succ.succ (by rw [Fin.le_def]; simp) with hv
  set P : ℕ → Φ.A.obj (s.obj (Fin.last (j + 1))) := fun n => ∏ k : Fin j, if (k : ℕ) < n then u k else v k with hP
  set T : Fin (j + 2) → Φ.A.obj (s.obj (Fin.last (j + 1))) := fun i =>
    ∏ k : Fin j, ga E σ (I k) s (i.succAbove k.castSucc) (i.succAbove k.succ)
        ((Fin.strictMono_succAbove i).monotone (Fin.castSucc_lt_succ (i := k)).le) with hT
  set W : Fin (j + 2) → Φ.A.obj (s.obj (Fin.last (j + 1))) := fun i =>
    (Φ.A.map (toLast i s)).hom ((Φ.A.map (σ _)).hom x) with hW
  set Y := (Φ.A.map (σ (s.obj (Fin.last (j + 1))))).hom x with hY
  have hT0 : T 0 = P 0 := by
    refine Finset.prod_congr rfl fun k _ => ?_
    simp only [Nat.not_lt_zero, if_false]
    refine ga_congr E σ _ s _ _ ?_ ?_ <;> simp
  have hTl : T (Fin.last (j + 1)) = P j := by
    refine Finset.prod_congr rfl fun k _ => ?_
    simp only [k.2, if_true]
    refine ga_congr E σ _ s _ _ ?_ ?_ <;> simp
  have hTi : ∀ i : Fin j, T i.succ.castSucc = P (i + 1) + P i := by
    intro i
    have hPa : P (i + 1) = u i * ∏ k ∈ Finset.univ.erase i, (if (k : ℕ) < i + 1 then u k else v k) := by
      have := Finset.mul_prod_erase Finset.univ (fun k : Fin j => if (k : ℕ) < i + 1 then u k else v k) (Finset.mem_univ i)
      simp only [Nat.lt_add_one, if_true] at this
      exact this.symm
    have hPb : P i = v i * ∏ k ∈ Finset.univ.erase i, (if (k : ℕ) < i then u k else v k) := by
      have := Finset.mul_prod_erase Finset.univ (fun k : Fin j => if (k : ℕ) < i then u k else v k) (Finset.mem_univ i)
      simp only [lt_irrefl, if_false] at this
      exact this.symm
    have hTa : T i.succ.castSucc = (u i + v i) * ∏ k ∈ Finset.univ.erase i, (if (k : ℕ) < i then u k else v k) := by
      have := Finset.mul_prod_erase Finset.univ (fun k : Fin j => ga E σ (I k) s (i.succ.castSucc.succAbove k.castSucc)
        (i.succ.castSucc.succAbove k.succ) ((Fin.strictMono_succAbove _).monotone (Fin.castSucc_lt_succ (i := k)).le)) (Finset.mem_univ i)
      refine this.symm.trans ?_
      congr 1
      · rw [hu, hv]
        dsimp only
        rw [← ga_add]
        refine ga_congr E σ _ s _ _ ?_ ?_ <;> fa
      · refine Finset.prod_congr rfl fun k hk => ?_
        have hki : (k : ℕ) ≠ i := fun h => Finset.ne_of_mem_erase hk (Fin.ext h)
        split_ifs with h
        · refine ga_congr E σ _ s _ _ ?_ ?_ <;> fa
        · refine ga_congr E σ _ s _ _ ?_ ?_ <;> fa
    have hE : ∏ k ∈ Finset.univ.erase i, (if (k : ℕ) < i + 1 then u k else v k) =
        ∏ k ∈ Finset.univ.erase i, (if (k : ℕ) < i then u k else v k) := by
      refine Finset.prod_congr rfl fun k hk => ?_
      have hki : (k : ℕ) ≠ i := fun h => Finset.ne_of_mem_erase hk (Fin.ext h)
      have : (k : ℕ) < i + 1 ↔ (k : ℕ) < i := by omega
      simp only [this]
    rw [hTa, hPa, hPb, hE]
    ring
  have hWY : ∀ i : Fin (j + 2), i ≠ Fin.last (j + 1) → W i = Y := by
    intro i hi
    have hi' : i.succAbove (Fin.last j) = Fin.last (j + 1) := by
      have h1 : (i : ℕ) ≠ j + 1 := fun h => hi (Fin.ext h)
      have h2 := i.2
      apply Fin.ext
      rw [sa_val]
      simp only [Fin.val_last]
      split_ifs <;> omega
    calc W i = (Φ.A.map (σ _ ≫ toLast i s)).hom x := map_map _ _ _
      _ = Y := by rw [show σ _ ≫ toLast i s = σ (s.obj (Fin.last (j + 1))) from sec_last E σ s _ hi']
  have hYW : Y - W (Fin.last (j + 1)) ∈ (Fil ((q : ℤ) + 1)).S _ := by
    have h := hc q (σ (s.obj (Fin.last (j + 1)))) (σ _ ≫ toLast (Fin.last (j + 1)) s) hx
    rwa [show W (Fin.last (j + 1)) = (Φ.A.map (σ _ ≫ toLast (Fin.last (j + 1)) s)).hom x from map_map _ _ _]
  have hsum : ∑ i : Fin (j + 2), (-1 : ℤ) ^ (i : ℕ) • (Φ.A.map (toLast i s)).hom (E.form σ I x (face i s)) =
      (-1) ^ j * (P j * (Y - W (Fin.last (j + 1)))) := by
    have hterm : ∀ i : Fin (j + 2), (-1 : ℤ) ^ (i : ℕ) • (Φ.A.map (toLast i s)).hom (E.form σ I x (face i s)) =
        (-1) ^ (i : ℕ) * (T i * W i) := by
      intro i
      rw [face_form, zsmul_eq_mul]
      push_cast
      rfl
    rw [Finset.sum_congr rfl fun i _ => hterm i, Fin.sum_univ_castSucc, Fin.sum_univ_succ]
    have h0 : T (Fin.castSucc 0) = P 0 := hT0
    have hne0 : Fin.castSucc (0 : Fin (j + 1)) ≠ Fin.last (j + 1) := (Fin.castSucc_lt_last _).ne
    have hint : ∑ i : Fin j, (-1) ^ ((i.succ.castSucc : Fin (j + 2)) : ℕ) * (T i.succ.castSucc * W i.succ.castSucc) =
        (∑ m ∈ Finset.range j, (-1) ^ (m + 1) * (P (m + 1) + P m)) * Y := by
      rw [Finset.sum_mul, ← Fin.sum_univ_eq_sum_range (fun m => (-1) ^ (m + 1) * (P (m + 1) + P m) * Y) j]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hTi, hWY _ (Fin.castSucc_lt_last _).ne]
      simp only [Fin.val_castSucc, Fin.val_succ]
      ring
    rw [hint, h0, hWY _ hne0, hTl]
    simp only [Fin.val_castSucc, Fin.val_zero, Fin.val_last, pow_zero]
    linear_combination Y * tele P j
  rw [hsum]
  refine Ideal.mul_mem_left _ _ ?_
  have h := prod_mem hF (fun k : Fin j => if (k : ℕ) < j then u k else v k)
    (fun k => by
      split_ifs
      · exact ga_mem E σ hF _ s _ _ _
      · exact ga_mem E σ hF _ s _ _ _)
    (q := q + 1) (x := Y - W (Fin.last (j + 1))) (by push_cast; exact hYW)
  have e : ((j + (q + 1) : ℕ) : ℤ) = (j : ℤ) + q + 1 := by push_cast; ring
  rwa [e] at h

theorem rep_form {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil)
    {d : ℕ} (E : Frame Φ d) (σ : ∀ T : C, E.D ⟶ T) (hc : E.GrConst Fil) (j q : ℕ) (r : ℤ) (hr : r = j + q)
    (I : Fin j → Fin d) (x : Φ.A.obj E.D) (hx : x ∈ (Fil q).S E.D) :
    ∃ c, Rep (Fil r) (Fil (r + 1)) (E.form σ I x) c := by
  subst hr
  have hmem : ∀ s : ComposableArrows C j, E.form σ I x s ∈ (Fil ((j : ℤ) + q)).S _ := by
    intro s
    have h := prod_mem hF _ (fun k => ga_mem E σ hF (I k) s k.castSucc k.succ (Fin.castSucc_lt_succ (i := k)).le)
      ((Fil q).map_mem (σ _) hx)
    rw [Nat.cast_add] at h
    exact h
  let f : CH.Cn (sq (Fil ((j : ℤ) + q)) (Fil ((j : ℤ) + q + 1))) j := fun s => sqMk _ _ (E.form σ I x s) (hmem s)
  have hd : CH.d _ j f = 0 := by
    funext s
    apply Subtype.ext
    have h := Ideal.Quotient.eq_zero_iff_mem.2 (d_form_mem E σ hF hc j q I x hx s)
    rw [map_sum] at h
    refine Eq.trans ?_ h
    change Subtype.val (∑ i : Fin (j + 2), (-1 : ℤ) ^ (i : ℕ) • ((sq (Fil ((j : ℤ) + q)) (Fil ((j : ℤ) + q + 1))).map (toLast i s)).hom (f (face i s)) :
      sqM (Fil ((j : ℤ) + q)) (Fil ((j : ℤ) + q + 1)) _) = _
    rw [AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul]
    rfl
  exact ⟨_, f, hd, rfl, fun s => rfl⟩

end GlobalTheory.CompanionTheory.CocProd
