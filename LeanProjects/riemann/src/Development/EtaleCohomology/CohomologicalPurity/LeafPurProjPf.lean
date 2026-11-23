import Development.EtaleCohomology.CohomologicalPurity.LeafPurPf
import Development.EtaleCohomology.CohomologicalPurity.LeafActNatPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity

namespace PurProjPf

open PurPf

def HsCast {q : ℕ} {P : Arrow Spc} {N N' I I' : ℤ} (hN : N = N') (hI : I = I') (x : Hs q P N I) : Hs q P N' I' := by
  subst hN; subst hI; exact x

theorem HsCast_val {q : ℕ} {P : Arrow Spc} {N N' I I' : ℤ} (hN : N = N') (hI : I = I') (x : Hs q P N I) :
    (HsCast hN hI x).1 = Ht.cast hN hI x.1 := by
  subst hN; subst hI; rfl

theorem HsCast_pull {q : ℕ} {P' P : Arrow Spc} (φ : P' ⟶ P) {N N' I I' : ℤ} (hN : N = N') (hI : I = I')
    (x : Hs q P N I) : Hs.pull q φ N' I' (HsCast hN hI x) = HsCast hN hI (Hs.pull q φ N I x) := by
  subst hN; subst hI; rfl

theorem HsCast_fgt {q : ℕ} {P : Arrow Spc} {N N' I I' : ℤ} (hN : N = N') (hI : I = I') (x : Hs q P N I) :
    Hs.fgt q P N' I' (HsCast hN hI x) = Ht.cast hN hI (Hs.fgt q P N I x) := by
  subst hN; subst hI; rfl

theorem act_val (hA : DivisorNaturality) (q : ℕ) [NeZero q] {P : Arrow Spc} {n m i j : ℤ} (a : Ht q P.right n i)
    (b : Hs q P m j) : (Hs.act q a b).1 = cup q (pull _ (dbl.fold P) _ n a) b.1 := by
  have hb : pull _ (dbl.inr P) (tw q j) m b.1 = 0 := b.2
  change cup q (pull _ (dbl.fold P) _ n a) b.1 -
    pull _ (dbl.fold P) _ _ (pull _ (dbl.inr P) _ _ (cup q (pull _ (dbl.fold P) _ n a) b.1)) = _
  rw [(hA q).1, hb]
  simp only [map_zero, sub_zero]

theorem act_cup (hA : DivisorNaturality) (hR : DivisorRingCompatibility) (q : ℕ) [NeZero q] {P : Arrow Spc} {n m k i j l : ℤ}
    (x : Ht q P.right n i) (y : Ht q P.right m j) (c : Hs q P k l) :
    Hs.act q (cup q x y) c = HsCast (by ring) (by ring) (Hs.act q x (Hs.act q y c)) := by
  apply Subtype.ext
  rw [HsCast_val, act_val hA, act_val hA, act_val hA, (hA q).1, (hR q _).2.1]

theorem fgt_act (hA : DivisorNaturality) (q : ℕ) [NeZero q] {P : Arrow Spc} {n m i j : ℤ} (a : Ht q P.right n i)
    (s : Hs q P m j) : Hs.fgt q P _ _ (Hs.act q a s) = cup q a (Hs.fgt q P m j s) := by
  change pull _ (dbl.inl P) _ _ (Hs.act q a s).1 = cup q a (pull _ (dbl.inl P) _ _ s.1)
  rw [act_val hA, (hA q).1, ← pull_comp, show dbl.inl P ≫ dbl.fold P = 𝟙 _ from pushout.inl_desc _ _ _, pull_id]

theorem purT_char {d : ℕ} (T : ∀ P : SP d, Tube P) (q : ℕ) [NeZero q] (P : SP d) (hq : IsUnit (q : Γ(P.X, ⊤)))
    (n i : ℤ) (x : Ht q (sch.obj P.Z) n i) : ∃ e : Ht q (T P).E n i,
      pull _ (pullback.fst (T P).π (sch.map P.ι)) _ _ e = pull _ (pullback.snd (T P).π (sch.map P.ι)) _ _ x ∧
      Hs.pull q (abvMap P.U (T P).π) _ _ (purT T q P n i x) =
        Hs.act q (P := abv P.U (T P).π) e (Hs.pull q (abvMap P.U (T P).π) _ _ (fcl d q P)) := by
  classical
  have h : q ≠ 0 ∧ IsUnit (q : Γ(P.X, ⊤)) := ⟨NeZero.ne q, hq⟩
  refine ⟨(AddEquiv.ofBijective _ (((T P).ok q hq).1 i n)).symm
    (pull _ (pullback.snd (T P).π (sch.map P.ι)) (tw q i) n x), ?_, ?_⟩
  · exact AddEquiv.ofBijective_apply_symm_apply _ (((T P).ok q hq).1 i n)
  · unfold purT
    rw [dif_pos h]
    exact AddEquiv.ofBijective_apply_symm_apply _ (((T P).ok q hq).2.2.1 (n + 2 * d) (i + d))

end PurProjPf

open PurPf PurProjPf

theorem LeafPurProj_of : EtalePurityProjection := by
  intro hH d T q _ P hq n m i j a b
  have hA : DivisorNaturality := hH.2.2.2.2.1
  have hR : DivisorRingCompatibility := hH.2.2.2.2.2.1
  obtain ⟨eb, heb1, heb2⟩ := purT_char T q P hq m j b
  obtain ⟨ex, hex1, hex2⟩ := purT_char T q P hq (n + m) (i + j) (cup q (pull _ (sch.map P.ι) _ _ a) b)
  have hex : ex = cup q (pull (ZMod q) (T P).π (tw q i) n a) eb := by
    apply (((T P).ok q hq).1 (i + j) (n + m)).1
    rw [hex1, (hA q).1, (hA q).1, heb1, ← pull_comp, ← pull_comp, pullback.condition]
  have hN : n + (m + 2 * (d : ℤ)) = n + m + 2 * d := by ring
  have hI : i + (j + (d : ℤ)) = i + j + d := by ring
  have key : purT T q P (n + m) (i + j) (cup q (pull _ (sch.map P.ι) _ _ a) b) =
      HsCast hN hI (Hs.act q (P := opn P.U) (n := n) (i := i) a (purT T q P m j b)) := by
    apply (((T P).ok q hq).2.2.1 (n + m + 2 * d) (i + j + d)).1
    rw [hex2, hex, HsCast_pull]
    refine (act_cup hA hR q (P := abv P.U (T P).π) (pull (ZMod q) (T P).π (tw q i) n a) eb
      (Hs.pull q (abvMap P.U (T P).π) (2 * d) d (fcl d q P))).trans ?_
    rw [TubeCut.LeafActNat_of hA q _ _ (abvMap P.U (T P).π) n (m + 2 * d) i (j + d) a (purT T q P m j b), heb2]
    rfl
  rw [key, HsCast_fgt]
  exact congrArg (Ht.cast hN hI) (fgt_act hA q (P := opn P.U) a (purT T q P m j b))

end LateralTheory.CohomologicalPurity
