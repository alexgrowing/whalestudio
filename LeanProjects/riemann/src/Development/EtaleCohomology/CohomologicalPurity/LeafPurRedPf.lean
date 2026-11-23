import Development.EtaleCohomology.CohomologicalPurity.LeafPurPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity

namespace PurRedPf

open PurPf

theorem inv_red (q r : ℕ) {E E' : Spc} (f : E ⟶ E') (n i : ℤ)
    (hq : Function.Bijective (pull (ZMod q) f (tw q i) n)) (hr : Function.Bijective (pull (ZMod r) f (tw r i) n))
    (y : Ht q E n i) :
    (AddEquiv.ofBijective _ hr).symm (red q r E n i y) = red q r E' n i ((AddEquiv.ofBijective _ hq).symm y) := by
  apply hr.1
  rw [AddEquiv.ofBijective_apply_symm_apply]
  rw [GlobalTheory.EtC.pull_red]
  congr 1
  exact ((AddEquiv.ofBijective _ hq).apply_symm_apply y).symm

def redS (q r : ℕ) (P : Arrow Spc) (n i : ℤ) (x : Hs q P n i) : Hs r P n i :=
  ⟨red q r _ n i x.1, by
    change pull _ (dbl.inr P) (tw r i) n (red q r _ n i x.1) = 0
    have hx : pull _ (dbl.inr P) (tw q i) n x.1 = 0 := x.2
    rw [GlobalTheory.EtC.pull_red, hx, map_zero]⟩

theorem redS_coe (q r : ℕ) (P : Arrow Spc) (n i : ℤ) (x : Hs q P n i) : (redS q r P n i x).1 = red q r _ n i x.1 := rfl

theorem Hs.pullS_red (q r : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P) (n i : ℤ) (x : Hs q P n i) :
    Hs.pull r φ n i (redS q r P n i x) = redS q r P' n i (Hs.pull q φ n i x) := by
  apply Subtype.ext
  change pull _ (dbl.map φ) (tw r i) n (red q r _ n i x.1) = red q r _ n i (pull _ (dbl.map φ) (tw q i) n x.1)
  rw [GlobalTheory.EtC.pull_red]

theorem Hs.inv_red (q r : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P) (n i : ℤ)
    (hq : Function.Bijective (Hs.pull q φ n i)) (hr : Function.Bijective (Hs.pull r φ n i)) (y : Hs q P' n i) :
    (AddEquiv.ofBijective _ hr).symm (redS q r P' n i y) = redS q r P n i ((AddEquiv.ofBijective _ hq).symm y) := by
  apply hr.1
  rw [AddEquiv.ofBijective_apply_symm_apply, Hs.pullS_red]
  congr 1
  exact ((AddEquiv.ofBijective _ hq).apply_symm_apply y).symm

theorem Hs.act_red (hA : A11) (q r : ℕ) [NeZero q] (hrq : r ∣ q) {P : Arrow Spc} {n m i j : ℤ}
    (a : Ht q P.right n i) (b : Hs q P m j) :
    Hs.act r (red q r _ n i a) (redS q r P m j b) = redS q r P _ _ (Hs.act q a b) := by
  apply Subtype.ext
  have hc : cup r (pull _ (dbl.fold P) (tw r i) n (red q r _ n i a)) (red q r _ m j b.1) =
      red q r _ _ _ (cup q (pull _ (dbl.fold P) (tw q i) n a) b.1) := by
    rw [(hA q r hrq (dbl P)).1, GlobalTheory.EtC.pull_red]
  simp only [Hs.act, Hs.proj, redS_coe]
  rw [hc, map_sub, GlobalTheory.EtC.pull_red, GlobalTheory.EtC.pull_red]

theorem fcl_isCl (hH : Hyp) (hCl : LeafCl) (d : ℕ) : IsCl d (fcl d) := by
  unfold fcl
  exact pick_spec (hCl hH d)

theorem purT_eq {d : ℕ} (T : ∀ P : SP d, Tube P) (q : ℕ) [NeZero q] (P : SP d) (hq : IsUnit (q : Γ(P.X, ⊤)))
    (n i : ℤ) (a : Ht q (sch.obj P.Z) n i) :
    purT T q P n i a = (AddEquiv.ofBijective _ (((T P).ok q hq).2.2.1 (n + 2 * d) (i + d))).symm
      (Hs.act q (P := abv P.U (T P).π) ((AddEquiv.ofBijective _ (((T P).ok q hq).1 i n)).symm
        (pull _ (pullback.snd (T P).π (sch.map P.ι)) (tw q i) n a))
        (Hs.pull q (abvMap P.U (T P).π) _ _ (fcl d q P))) := by
  unfold purT
  rw [dif_pos ⟨NeZero.ne q, hq⟩]
  rfl

theorem act_fcl (hH : Hyp) (hCl : LeafCl) {d : ℕ} (T : ∀ P : SP d, Tube P) (q : ℕ) [NeZero q] (P : SP d)
    (hq : IsUnit (q : Γ(P.X, ⊤))) (r : ℕ) (hrq : r ∣ q) (n i : ℤ) (x : Ht q (T P).E n i) :
    Hs.act r (P := abv P.U (T P).π) (red q r (T P).E n i x) (Hs.pull r (abvMap P.U (T P).π) _ _ (fcl d r P)) =
      redS q r _ _ _ (Hs.act q (P := abv P.U (T P).π) x (Hs.pull q (abvMap P.U (T P).π) _ _ (fcl d q P))) := by
  have hfr : fcl d r P = redS q r _ _ _ (fcl d q P) := Subtype.ext (((fcl_isCl hH hCl d) q).2.2 r hrq P hq)
  rw [hfr, Hs.pullS_red]
  exact Hs.act_red hH.2.2.2.2.2.2.2.1 q r hrq _ _

end PurRedPf

open PurPf PurRedPf

theorem LeafPurRed_of : EtalePurityReduction := by
  intro hH hCl d T q _ P hq r hrq n i a
  have hq0 : q ≠ 0 := NeZero.ne q
  have hr0 : r ≠ 0 := by rintro rfl; exact hq0 (zero_dvd_iff.mp hrq)
  have : NeZero r := ⟨hr0⟩
  have hru : IsUnit (r : Γ(P.X, ⊤)) := isUnit_of_dvd_unit (Nat.cast_dvd_cast hrq) hq
  rw [purT_eq T r P hru, purT_eq T q P hq, GlobalTheory.EtC.pull_red, inv_red q r _ n i (((T P).ok q hq).1 i n) (((T P).ok r hru).1 i n), act_fcl hH hCl T q P hq r hrq, Hs.inv_red q r _ _ _, redS_coe]

end LateralTheory.CohomologicalPurity
