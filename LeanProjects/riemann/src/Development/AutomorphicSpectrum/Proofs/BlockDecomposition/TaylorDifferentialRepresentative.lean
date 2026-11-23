import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.LocDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepUnique
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)

noncomputable section
namespace GlobalTheory.CompanionTheory.ConeLocal

open GlobalTheory.CompanionTheory.CocProd in

theorem d_eq_of_rep {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R} {a b : IdF A} {n : ℕ}
    (f g : CH.Cn (CH.modF A) n) {c : CH.H (sq a b) n}
    (hf : CrystallineSemistableComparison.Pb.Rep a b (fun u => f u) c) (hg : CrystallineSemistableComparison.Pb.Rep a b (fun u => g u) c) :
    ∃ e : CH.Cn (CH.modF A) n, (∀ s, e s ∈ b.S _) ∧ CH.d _ n f = CH.d _ n g + CH.d _ n e := by
  obtain ⟨f', hf', rfl, hv⟩ := hf
  obtain ⟨g', hg', hc, hv'⟩ := hg
  have hB : f' - g' ∈ (CH.cx (sq a b)).B n := by
    have := (Submodule.Quotient.eq _).1 hc
    exact this
  cases n with
  | zero =>
    have h0 : f' - g' = 0 := hB
    refine ⟨f - g, fun s => ?_, ?_⟩
    · have e1 : (show sqM a b _ from f' s) = (show sqM a b _ from g' s) := congrFun (sub_eq_zero.1 h0) s
      have e2 := (hv s).symm.trans ((congrArg Subtype.val e1).trans (hv' s))
      have e3 : ∀ x y : A.obj (s.obj (Fin.last 0)), Ideal.Quotient.mk (b.S _) x = Ideal.Quotient.mk (b.S _) y → x - y ∈ b.S _ :=
        fun x y h => Ideal.Quotient.eq.1 h
      exact e3 _ _ e2
    · rw [map_sub]; abel
  | succ m =>
    obtain ⟨h', hh⟩ := hB
    have hl : ∀ s, ∃ t ∈ a.S _, Ideal.Quotient.mk (b.S _) t = (show sqM a b _ from h' s).1 := fun s =>
      (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 (show sqM a b _ from h' s).2
    choose l hl1 hl2 using hl
    let l' : CH.Cn (CH.modF A) m := fun s => l s
    refine ⟨f - g - CH.d _ m l', fun s => ?_, ?_⟩
    · have e0 := d_val h' (fun s => l s) (fun s => (hl2 s).symm) s
      have e1 : (show sqM a b _ from CH.d (sq a b) m h' s) =
          (show sqM a b _ from f' s) - (show sqM a b _ from g' s) := congrFun hh s
      rw [e1] at e0
      have e3 : ∀ x y z : A.obj (s.obj (Fin.last (m + 1))), Ideal.Quotient.mk (b.S _) x - Ideal.Quotient.mk (b.S _) y =
          Ideal.Quotient.mk (b.S _) z → x - y - z ∈ b.S _ := fun x y z h => by
        rw [← map_sub] at h
        exact Ideal.Quotient.eq.1 h
      refine e3 _ _ _ ?_
      rw [← hv, ← hv']
      exact e0
    · rw [map_sub, map_sub, CH.d_d]; abel

section Form
open GlobalTheory.CompanionTheory.CocProd
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {d : ℕ}
  (E : Frame Φ d) (σ : ∀ T : C, E.D ⟶ T)

local macro "fa" : tactic =>
  `(tactic| (simp only [sa_val, Fin.val_castSucc, Fin.val_succ, Fin.val_last]; split_ifs <;> omega))

def headP {j : ℕ} (I : Fin j → Fin d) (s : ComposableArrows C (j + 1)) : Φ.A.obj (s.obj (Fin.last (j + 1))) :=
  ∏ k : Fin j, ga E σ (I k) s k.castSucc.castSucc k.succ.castSucc (by rw [Fin.le_def]; simp)

theorem alt_sum_form {j : ℕ} (I : Fin j → Fin d) (x : Φ.A.obj E.D) (s : ComposableArrows C (j + 1)) :
    ∑ i : Fin (j + 2), (-1 : ℤ) ^ (i : ℕ) • (Φ.A.map (toLast i s)).hom (E.form σ I x (face i s)) =
      (-1) ^ j * (headP E σ I s * ((Φ.A.map (σ (s.obj (Fin.last (j + 1))))).hom x -
        (Φ.A.map (σ _ ≫ toLast (Fin.last (j + 1)) s)).hom x)) := by
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
  have hPj : headP E σ I s = P j := by
    refine Finset.prod_congr rfl fun k _ => ?_
    simp only [k.2, if_true]
    rfl
  have hWl : (Φ.A.map (σ _ ≫ toLast (Fin.last (j + 1)) s)).hom x = W (Fin.last (j + 1)) := (map_map _ _ _).symm
  rw [hWl, hPj]
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

theorem form_snoc {j : ℕ} (I : Fin j → Fin d) (k : Fin d) (z : Φ.A.obj E.D) (s : ComposableArrows C (j + 1)) :
    E.form σ (Fin.snoc (α := fun _ => Fin d) I k) z s =
      headP E σ I s * (ga E σ k s ((Fin.last (j + 1)).succAbove (Fin.last j)) (Fin.last (j + 1)) (Fin.le_last _) *
        (Φ.A.map (σ (s.obj (Fin.last (j + 1))))).hom z) := by
  unfold Frame.form headP
  rw [Fin.prod_univ_castSucc, mul_assoc]
  congr 1
  · refine Finset.prod_congr rfl fun m _ => ?_
    rw [Fin.snoc_castSucc (α := fun _ => Fin d)]
    exact ga_congr E σ _ s _ _ (by simp) (by simp)
  · congr 1
    rw [Fin.snoc_last (α := fun _ => Fin d)]
    refine ga_congr E σ _ s (Fin.castSucc_lt_succ (i := Fin.last j)).le _ ?_ ?_
    · simp [sa_val]
    · simp

theorem ga_last {j : ℕ} (k : Fin d) (s : ComposableArrows C (j + 1)) (q : Fin (j + 2)) (h : q ≤ Fin.last (j + 1)) :
    ga E σ k s q (Fin.last (j + 1)) h = E.τ k (σ (s.obj q) ≫ s.map (homOfLE h)) (σ (s.obj (Fin.last (j + 1)))) := by
  unfold ga
  have : (homOfLE (Fin.le_last (Fin.last (j + 1))) : Fin.last (j + 1) ⟶ Fin.last (j + 1)) = 𝟙 _ := Subsingleton.elim _ _
  rw [this, s.map_id]
  simp
  rfl

theorem form_neg_pow {j : ℕ} (I : Fin j → Fin d) (x : Φ.A.obj E.D) (m : ℕ) (s : ComposableArrows C j) :
    E.form σ I ((-1) ^ m * x) s = (-1) ^ m * E.form σ I x s := by
  unfold Frame.form
  rw [map_mul, map_pow, map_neg, map_one]
  ring

end Form

section Conn
open GlobalTheory.CompanionTheory.CocProd
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {d : ℕ}

theorem d_form {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil) (E : Frame Φ d) (σ : ∀ T : C, E.D ⟶ T) (hc : E.GrConst Fil)
    {p : Fin d → Φ.A.obj E.D → Φ.A.obj E.D} (hT : Taylor Fil E p) {j : ℕ} (I : Fin j → Fin d) (x : Φ.A.obj E.D)
    (s : ComposableArrows C (j + 1)) :
    ∑ i : Fin (j + 2), (-1 : ℤ) ^ (i : ℕ) • (Φ.A.map (toLast i s)).hom (E.form σ I x (face i s)) -
      (-1) ^ j * ∑ k : Fin d, E.form σ (Fin.snoc (α := fun _ => Fin d) I k) (p k x) s ∈ (Fil ((j : ℤ) + 1 + 1)).S _ := by
  set q := (Fin.last (j + 1)).succAbove (Fin.last j) with hq
  set T := s.obj (Fin.last (j + 1)) with hTdef
  set v : E.D ⟶ T := σ (s.obj q) ≫ s.map (homOfLE (Fin.le_last q)) with hv
  have hvl : (σ _ ≫ toLast (Fin.last (j + 1)) s) = v := rfl
  set g : Fin d → Φ.A.obj T := fun k => ga E σ k s q (Fin.last (j + 1)) (Fin.le_last _) with hg
  have hgτ : ∀ k, g k = E.τ k v (σ T) := fun k => ga_last E σ k s q (Fin.le_last _)
  have hg1 : ∀ k, g k ∈ (Fil ((1 : ℕ) : ℤ)).S T := fun k => ga_mem E σ hF k s q _ _
  have hdiff : ∀ k, g k * ((Φ.A.map v).hom (p k x) - (Φ.A.map (σ T)).hom (p k x)) ∈ (Fil ((2 : ℕ) : ℤ)).S T := by
    intro k
    have h0 : p k x ∈ (Fil ((0 : ℕ) : ℤ)).S E.D := by
      rw [hF.top _ (by norm_num)]; trivial
    have h1 := hc 0 v (σ T) h0
    have e1 : (((0 : ℕ) : ℤ) + 1) = ((1 : ℕ) : ℤ) := by norm_num
    rw [e1] at h1
    exact hF.mul 1 1 T (hg1 k) h1
  have hin : (Φ.A.map (σ T)).hom x - (Φ.A.map v).hom x - ∑ k, g k * (Φ.A.map (σ T)).hom (p k x) ∈ (Fil ((2 : ℕ) : ℤ)).S T := by
    have tay := hT T (σ T) v x
    have e2 : (2 : ℤ) = ((2 : ℕ) : ℤ) := by norm_num
    rw [e2] at tay
    have e3 : (Φ.A.map (σ T)).hom x - (Φ.A.map v).hom x - ∑ k, g k * (Φ.A.map (σ T)).hom (p k x) =
        ((Φ.A.map (σ T)).hom x - (Φ.A.map v).hom x - ∑ k, E.τ k v (σ T) * (Φ.A.map v).hom (p k x)) +
          ∑ k, g k * ((Φ.A.map v).hom (p k x) - (Φ.A.map (σ T)).hom (p k x)) := by
      simp only [hgτ, mul_sub, Finset.sum_sub_distrib]
      ring
    rw [e3]
    exact Ideal.add_mem _ tay (Ideal.sum_mem _ fun k _ => hdiff k)
  have hfin := prod_mem hF (fun k : Fin j => ga E σ (I k) s k.castSucc.castSucc k.succ.castSucc (by rw [Fin.le_def]; simp))
    (fun k => ga_mem E σ hF _ s _ _ _) hin
  have e4 : ((j + 2 : ℕ) : ℤ) = (j : ℤ) + 1 + 1 := by push_cast; ring
  rw [e4] at hfin
  have e5 : ∑ i : Fin (j + 2), (-1 : ℤ) ^ (i : ℕ) • (Φ.A.map (toLast i s)).hom (E.form σ I x (face i s)) -
      (-1) ^ j * ∑ k : Fin d, E.form σ (Fin.snoc (α := fun _ => Fin d) I k) (p k x) s =
      (-1) ^ j * (headP E σ I s * ((Φ.A.map (σ T)).hom x - (Φ.A.map v).hom x - ∑ k, g k * (Φ.A.map (σ T)).hom (p k x))) := by
    rw [alt_sum_form, hvl]
    simp only [form_snoc, ← Finset.mul_sum]
    ring
  rw [e5]
  exact Ideal.mul_mem_left _ _ hfin

theorem connecting_form {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A} {d : ℕ} (hF : IsFil Φ Fil) (E : Frame Φ d) (σ : ∀ T : C, E.D ⟶ T) (hc : E.GrConst Fil)
    (p : Fin d → Φ.A.obj E.D → Φ.A.obj E.D) (hT : Taylor Fil E p) (n : ℕ) (f : CH.Cn (CH.modF Φ.A) n) (y : Idx n d → Φ.A.obj E.D) (c : CH.H (gr Fil (n : ℤ)) n)
      (x : CH.H (gr Fil ((n : ℤ) + 1)) (n + 1))
      (hf : CrystallineSemistableComparison.Pb.Rep (Fil (n : ℤ)) (Fil ((n : ℤ) + 1)) (fun u => f u) c)
      (hg : CrystallineSemistableComparison.Pb.Rep (Fil (n : ℤ)) (Fil ((n : ℤ) + 1)) (fun u => ∑ I : Idx n d, E.form σ I.1 (y I) u) c)
      (hx : CrystallineSemistableComparison.Pb.Rep (Fil ((n : ℤ) + 1)) (Fil ((n : ℤ) + 1 + 1)) (fun u => CH.d _ n f u) x) :
      CrystallineSemistableComparison.Pb.Rep (Fil ((n : ℤ) + 1)) (Fil ((n : ℤ) + 1 + 1))
        (fun u => ∑ a : Idx n d × Fin d, E.form σ (Fin.snoc (α := fun _ => Fin d) a.1.1 a.2) ((-1) ^ n * p a.2 (y a.1)) u) x := by
  let g : CH.Cn (CH.modF Φ.A) n := fun u => (∑ I : Idx n d, E.form σ I.1 (y I) u : Φ.A.obj (u.obj (Fin.last n)))
  obtain ⟨e, he, hde⟩ := d_eq_of_rep f g hf hg
  have h0 : CrystallineSemistableComparison.Pb.Rep (Fil ((n : ℤ) + 1)) (Fil ((n : ℤ) + 1 + 1)) (fun u => CH.d _ n (-e) u) 0 :=
    rep_d (-e) fun s => (Fil ((n : ℤ) + 1)).S _ |>.neg_mem (he s)
  have h1 := rep_add hx h0
  rw [add_zero] at h1
  refine rep_congr h1 fun s => ?_
  have e1 : CH.d _ n f s + CH.d _ n (-e) s = CH.d _ n g s := by
    rw [hde, map_neg]
    simp
  have e2 : ∀ (a b : Φ.A.obj (s.obj (Fin.last (n + 1)))), (CH.d _ n f s + CH.d _ n (-e) s : (CH.modF Φ.A).obj _) = a →
     a - b ∈ (Fil ((n : ℤ) + 1 + 1)).S _ → (show Φ.A.obj _ from CH.d _ n f s) + (show Φ.A.obj _ from CH.d _ n (-e) s) - b ∈ (Fil ((n : ℤ) + 1 + 1)).S _ := by
    intro a b h h'
    rw [← h] at h'
    exact h'
  refine e2 (∑ I : Idx n d, ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (Φ.A.map (toLast i s)).hom (E.form σ I.1 (y I) (face i s))) _ ?_ ?_
  · rw [e1]
    change ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (Φ.A.map (toLast i s)).hom (∑ I : Idx n d, E.form σ I.1 (y I) (face i s)) = _
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum, Finset.smul_sum]
  · rw [Fintype.sum_prod_type, ← Finset.sum_sub_distrib]
    refine Ideal.sum_mem _ fun I _ => ?_
    have := d_form hF E σ hc hT I.1 (y I) s
    simpa only [form_neg_pow, Finset.mul_sum] using this

end Conn

end GlobalTheory.CompanionTheory.ConeLocal
