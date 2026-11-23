import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ExistsEigv
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SphStarU

noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.U.UU

open PositivityTheory.Rg.BcB.F.Eig

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem pu_hz {w : Pl E} (K : Subgroup (UL n w)) : IsHecke K (0 : UL n w → ℂ) :=
  ⟨HasCompactSupport.zero, fun _ _ _ => ⟨rfl, rfl⟩⟩

theorem pu_lev {S : Set (Pl E)} {B : Finset (Pl E)} {K' : ∀ w : Pl E, Subgroup (UL n w)} (hB : LevelOff S B K')
    (w : Pl E) (hw : w ∉ B) : IsLevel (MonoidHom.id _) (KL n w) (KL n w) := by
  have h := hB.2.1.1 w
  rw [hB.2.2 w hw] at h
  exact h

theorem uAdjOfU : DiagAlg → LocAlg → SphOne → CompUnit → SphStarU → UAdj := by
  intro hD hL h1 hC hS E _ _ _ hE n S lam K' F B g R hB x hx
  rcases x with c | ⟨w0, h⟩
  · refine ⟨trivial, ?_⟩
    unfold UMod.op
    rw [(hD _ _ R.blk _ 0 0).2.2.2]
    rfl
  · obtain ⟨hw, hwB, hh⟩ := hx
    have hlev := pu_lev hB w0 hwB
    refine ⟨⟨hw, hwB, (hL E n w0 (SmIrr.triv _) (KL n w0) hlev h h hh hh).2.2.2.1⟩, ?_⟩
    unfold UMod.op
    rw [(hD _ _ R.blk _ 0 0).2.2.2]
    congr 1
    funext i
    exact (hS E hE n w0 (F.σ i w0) (hC E n (F.π i) (F.comp i).1 w0 _ ((F.comp i).2.2.2 w0 hw).1)
      (sph_line h1 hE F hB i w0 hw hwB) h h hh hh).2.1

section Word

variable {S : Set (Pl E)} {lam : InfinitePlace E → DomWeight n} {K' : ∀ w : Pl E, Subgroup (UL n w)}
  {F : UFam S lam K'} {B : Finset (Pl E)}

theorem pu_sph_inl (c : ℂ) (l : List (UGen E n)) (w : Pl E) : UGen.sph (Sum.inl c :: l) w = UGen.sph l w := rfl

theorem pu_sph_inr (w0 : Pl E) (h : UL n w0 → ℂ) (l : List (UGen E n)) (w : Pl E) :
    UGen.sph (Sum.inr ⟨w0, h⟩ :: l) w = if hw : w0 = w then lconv (hw ▸ h) (UGen.sph l w) else UGen.sph l w := rfl

theorem pu_sph_self (w0 : Pl E) (h : UL n w0 → ℂ) (l : List (UGen E n)) :
    UGen.sph (Sum.inr ⟨w0, h⟩ :: l) w0 = lconv h (UGen.sph l w0) := by
  rw [pu_sph_inr, dif_pos rfl]

theorem pu_sph_ne (w0 : Pl E) (h : UL n w0 → ℂ) (l : List (UGen E n)) (w : Pl E) (hw : w0 ≠ w) :
    UGen.sph (Sum.inr ⟨w0, h⟩ :: l) w = UGen.sph l w := by
  rw [pu_sph_inr, dif_neg hw]

def pu_pls (l : List (UGen E n)) : Finset (Pl E) :=
  (l.filterMap fun x => Sum.elim (fun _ => none) (fun y : Σ w : Pl E, UL n w → ℂ => some y.1) x).toFinset

theorem pu_sph_off (l : List (UGen E n)) (w : Pl E) (hw : w ∉ pu_pls l) :
    UGen.sph l w = (KL n w : Set (UL n w)).indicator 1 := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    have hw' : w ∉ pu_pls l := fun h => hw (by
      unfold pu_pls at h ⊢
      rw [List.mem_toFinset, List.mem_filterMap] at h ⊢
      obtain ⟨a, ha, hb⟩ := h
      exact ⟨a, List.mem_cons_of_mem _ ha, hb⟩)
    rcases x with c | ⟨w0, h⟩
    · rw [pu_sph_inl, ih hw']
    · have hne : w0 ≠ w := by
        rintro rfl
        apply hw
        unfold pu_pls
        rw [List.mem_toFinset, List.mem_filterMap]
        exact ⟨_, List.mem_cons_self, rfl⟩
      rw [pu_sph_ne _ _ _ _ hne, ih hw']

theorem pu_sph_hecke (hL : LocAlg) (hB : LevelOff S B K') (l : List (UGen E n)) (hl : ∀ x ∈ l, x.Ok S B)
    (w : Pl E) (hw : w ∉ B) : IsHecke (KL n w) (UGen.sph l w) := by
  have hlev := pu_lev hB w hw
  induction l with
  | nil =>
    have h := (hL E n w (SmIrr.triv _) (KL n w) hlev 0 0 (pu_hz _) (pu_hz _)).2.2.2.2.2.2.1
    rw [Subgroup.relIndex_self, Nat.cast_one] at h
    exact h
  | cons x l ih =>
    have ih' := ih fun y hy => hl y (List.mem_cons_of_mem _ hy)
    rcases x with c | ⟨w0, h⟩
    · rw [pu_sph_inl]; exact ih'
    · by_cases hw0 : w0 = w
      · subst hw0
        have hh : IsHecke (KL n w0) h := (hl _ List.mem_cons_self).2.2
        rw [pu_sph_self]
        exact (hL E n w0 (SmIrr.triv _) (KL n w0) hlev h _ hh ih').2.2.1
      · rw [pu_sph_ne _ _ _ _ hw0]; exact ih'

theorem pu_lpow (hL : LocAlg) (w : Pl E) (K : Subgroup (UL n w)) (hlev : IsLevel (MonoidHom.id _) (KL n w) K)
    (g : UL n w → ℂ) (hg : IsHecke K g) (σ : SmIrr (UL n w)) (k : ℕ) :
    IsHecke K (lpow K g k) ∧ locOp σ K (lpow K g k) = locOp σ K g ^ k := by
  induction k with
  | zero =>
    have h := hL E n w σ K hlev g g hg hg
    exact ⟨h.2.2.2.2.2.2.1, by rw [pow_zero]; exact h.2.2.2.2.2.2.2⟩
  | succ k ih =>
    have h := hL E n w σ K hlev g _ hg ih.1
    refine ⟨h.2.2.1, ?_⟩
    show locOp σ K (lconv g (lpow K g k)) = _
    rw [h.2.2.2.2.1, ih.2, pow_succ']

end Word

section Word2

variable {S : Set (Pl E)} {lam : InfinitePlace E → DomWeight n} {K' : ∀ w : Pl E, Subgroup (UL n w)}
  {F : UFam S lam K'} {B : Finset (Pl E)}

theorem pu_tw (h1 : SphOne) (hC : CompUnit) (hS : SphStarU) (hE : GlobalTheory.BCT.Unr E) (hB : LevelOff S B K') (i : F.ι)
    (w : Pl E) (hw : w ∈ S) (hwB : w ∉ B) (h₁ h₂ : UL n w → ℂ) (hh₁ : IsHecke (KL n w) h₁) (hh₂ : IsHecke (KL n w) h₂) :
    twTr (F.σ i w).ρ (KL n w) (KL n w) (lconv h₁ h₂) LinearMap.id =
      twTr (F.σ i w).ρ (KL n w) (KL n w) h₁ LinearMap.id * twTr (F.σ i w).ρ (KL n w) (KL n w) h₂ LinearMap.id ∧
    twTr (F.σ i w).ρ (KL n w) (KL n w) ((KL n w : Set (UL n w)).indicator 1) LinearMap.id = 1 := by
  have h := hS E hE n w (F.σ i w) (hC E n (F.π i) (F.comp i).1 w _ ((F.comp i).2.2.2 w hw).1)
    (sph_line h1 hE F hB i w hw hwB) h₁ h₂ hh₁ hh₂
  exact ⟨h.1, h.2.2⟩

theorem pu_supp (h1 : SphOne) (hC : CompUnit) (hS : SphStarU) (hE : GlobalTheory.BCT.Unr E) (hB : LevelOff S B K') (i : F.ι)
    (l : List (UGen E n)) :
    (S \ ↑B ∩ Function.mulSupport fun w => twTr (F.σ i w).ρ (KL n w) (KL n w) (UGen.sph l w) LinearMap.id).Finite := by
  refine (pu_pls l).finite_toSet.subset fun w hw => ?_
  obtain ⟨⟨hwS, hwB⟩, hne⟩ := hw
  by_contra hp
  apply hne
  show twTr (F.σ i w).ρ (KL n w) (KL n w) (UGen.sph l w) LinearMap.id = 1
  rw [pu_sph_off l w hp]
  exact (pu_tw h1 hC hS hE hB i w hwS hwB 0 0 (pu_hz _) (pu_hz _)).2

theorem pu_prod (hL : LocAlg) (h1 : SphOne) (hC : CompUnit) (hS : SphStarU) (hE : GlobalTheory.BCT.Unr E) (hB : LevelOff S B K')
    (i : F.ι) (l : List (UGen E n)) (hl : ∀ x ∈ l, x.Ok S B) :
    (l.map fun x => x.p F i).prod =
      UGen.sc l * ∏ᶠ w ∈ S \ ↑B, twTr (F.σ i w).ρ (KL n w) (KL n w) (UGen.sph l w) LinearMap.id := by
  induction l with
  | nil =>
    have h : ∏ᶠ w ∈ S \ ↑B, twTr (F.σ i w).ρ (KL n w) (KL n w) (UGen.sph ([] : List (UGen E n)) w) LinearMap.id = 1 :=
      (finprod_mem_congr (g := fun _ => (1 : ℂ)) rfl fun w hw =>
        (pu_tw h1 hC hS hE hB i w hw.1 hw.2 0 0 (pu_hz _) (pu_hz _)).2).trans (finprod_mem_one _)
    rw [h, mul_one]
    rfl
  | cons x l ih =>
    have ih' := ih fun y hy => hl y (List.mem_cons_of_mem _ hy)
    rcases x with c | ⟨w0, h⟩
    · rw [List.map_cons, List.prod_cons, ih']
      show c * (UGen.sc l * _) = (c * UGen.sc l) * ∏ᶠ w ∈ S \ ↑B, twTr (F.σ i w).ρ (KL n w) (KL n w) (UGen.sph l w) LinearMap.id
      rw [mul_assoc]
    · obtain ⟨hw0, hw0B, hh⟩ := hl _ List.mem_cons_self
      set t0 := twTr (F.σ i w0).ρ (KL n w0) (KL n w0) h LinearMap.id with ht0
      have hP : ∏ᶠ w ∈ S \ ↑B, twTr (F.σ i w).ρ (KL n w) (KL n w) (UGen.sph (Sum.inr ⟨w0, h⟩ :: l) w) LinearMap.id =
          t0 * ∏ᶠ w ∈ S \ ↑B, twTr (F.σ i w).ρ (KL n w) (KL n w) (UGen.sph l w) LinearMap.id := by
        rw [finprod_mem_congr (g := fun w => (if w = w0 then t0 else 1) *
          twTr (F.σ i w).ρ (KL n w) (KL n w) (UGen.sph l w) LinearMap.id) rfl ?_]
        · rw [finprod_mem_mul_distrib' ?_ (pu_supp h1 hC hS hE hB i l)]
          · congr 1
            rw [finprod_eq_single _ w0 (fun x hx => by simp [hx])]
            simp [show w0 ∈ S \ ↑B from ⟨hw0, hw0B⟩]
          · refine (Set.finite_singleton w0).subset fun w hw => ?_
            by_contra hne
            exact hw.2 (if_neg hne)
        · intro w hw
          rcases eq_or_ne w w0 with rfl | hne
          · rw [if_pos rfl, pu_sph_self]
            exact (pu_tw h1 hC hS hE hB i w hw.1 hw.2 h _ hh (pu_sph_hecke hL hB l (fun y hy => hl y
              (List.mem_cons_of_mem _ hy)) w hw.2)).1
          · rw [if_neg hne, one_mul, pu_sph_ne _ _ _ _ (Ne.symm hne)]
      rw [List.map_cons, List.prod_cons, ih']
      show t0 * (UGen.sc l * _) = (1 * UGen.sc l) * _
      rw [hP, one_mul, mul_left_comm]

theorem pu_opprod (hD : DiagAlg) {g : ∀ w : Pl E, UL n w → ℂ} (R : UMod F B g) (l : List (UGen E n)) :
    (l.map R.op).prod = diagOp R.blk (fun i => (l.map fun x => x.p F i).prod) := by
  induction l with
  | nil =>
    simp only [List.map_nil, List.prod_nil]
    rw [(hD F.ι R.d R.blk 1 1 1).2.2.1, one_smul]
  | cons x l ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [ih]
    unfold UMod.op
    rw [← (hD F.ι R.d R.blk _ _ 0).1]
    rfl

end Word2

theorem uWordOfU : DiagAlg → LocAlg → SphOne → CompUnit → SphStarU → UWord := by
  intro hD hL h1 hC hS E _ _ _ hE n S lam K' F B g R hB hg k l hl
  have hT : IsTest (KL n) K' (fam B K' g k l) := by
    refine ⟨fun w => ?_, ?_⟩
    · by_cases hw : w ∈ B
      · rw [fam, if_pos hw]
        exact (pu_lpow hL w (K' w) (hB.2.1.1 w) (g w) (hg w hw) (SmIrr.triv _) k).1
      · rw [fam, if_neg hw, hB.2.2 w hw]
        exact pu_sph_hecke hL hB l hl w hw
    · rw [Filter.eventually_cofinite]
      refine (B ∪ pu_pls l).finite_toSet.subset fun w hw => ?_
      by_contra hc
      simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, not_or] at hc
      exact hw (by rw [fam, if_neg hc.1, pu_sph_off l w hc.2])
  refine ⟨hT, fun hreg => ?_⟩
  have hloc : ∀ i, ∀ w ∈ B, locOp (F.σ i w) (K' w) (fam B K' g k l w) = locOp (F.σ i w) (K' w) (g w) ^ k :=
    fun i w hw => by
      rw [fam, if_pos hw]
      exact (pu_lpow hL w (K' w) (hB.2.1.1 w) (g w) (hg w hw) (F.σ i w) k).2
  have e1 := R.tr k _ hT hloc
  rw [F.tf _ hT hreg] at e1
  have e2 : (fun i => (l.map fun x => x.p F i).prod) = (fun _ => UGen.sc l) * fun i =>
      ∏ᶠ w ∈ S \ ↑B, twTr (F.σ i w).ρ (KL n w) (KL n w) (fam B K' g k l w) LinearMap.id := by
    funext i
    rw [Pi.mul_apply, pu_prod hL h1 hC hS hE hB i l hl]
    congr 1
    exact finprod_mem_congr rfl fun w hw => by rw [fam, if_neg (show w ∉ B from hw.2)]
  rw [pu_opprod hD R l, e2, (hD F.ι R.d R.blk (fun _ => UGen.sc l) _ 0).1, (hD F.ι R.d R.blk 0 0 (UGen.sc l)).2.2.1,
    smul_mul_assoc, one_mul, mul_smul_comm, ContinuousLinearMap.toLinearMap_smul, map_smul, smul_eq_mul, e1]

end PositivityTheory.Rg.BcB.F.U.UU

end
