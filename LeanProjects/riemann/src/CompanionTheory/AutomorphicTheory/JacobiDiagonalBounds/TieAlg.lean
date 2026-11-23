import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameOfAdmissibleWord

namespace Formalism.FourierDecayAlt.P.NormalFormRelations

open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr

noncomputable section

structure SRel (A A' : Type) [Ring A] [StarRing A] [Algebra ℂ A] [Ring A'] [StarRing A'] [Algebra ℂ A'] where
  r : A → A' → Prop
  zero : r 0 0
  one : r 1 1
  add : ∀ {a a' b b'}, r a a' → r b b' → r (a + b) (a' + b')
  mul : ∀ {a a' b b'}, r a a' → r b b' → r (a * b) (a' * b')
  smul : ∀ (c : ℂ) {a a'}, r a a' → r (c • a) (c • a')
  star : ∀ {a a'}, r a a' → r (star a) (star a')

namespace SRel

variable {A A' : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Ring A'] [StarRing A'] [Algebra ℂ A'] (R : SRel A A')

def InvClosed : Prop :=
  ∀ a a' b b', R.r a a' → a * b = 1 → b * a = 1 → a' * b' = 1 → b' * a' = 1 → R.r b b'

variable {R}

theorem neg {a a'} (h : R.r a a') : R.r (-a) (-a') := by
  have := R.smul (-1) h
  rwa [neg_one_smul, neg_one_smul] at this

theorem sub {a a' b b'} (h : R.r a a') (h' : R.r b b') : R.r (a - b) (a' - b') := by
  rw [sub_eq_add_neg, sub_eq_add_neg]; exact R.add h (neg h')

theorem sum {ι : Type} (s : Finset ι) {f : ι → A} {f' : ι → A'} (h : ∀ i ∈ s, R.r (f i) (f' i)) :
    R.r (∑ i ∈ s, f i) (∑ i ∈ s, f' i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using R.zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact R.add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem pow {a a'} (h : R.r a a') (n : ℕ) : R.r (a ^ n) (a' ^ n) := by
  induction n with
  | zero => simpa using R.one
  | succ n ih => rw [pow_succ, pow_succ]; exact R.mul ih h

theorem algMap (c : ℂ) : R.r (algebraMap ℂ A c) (algebraMap ℂ A' c) := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]; exact R.smul c R.one

theorem ite (p : Prop) [Decidable p] {a a' b b'} (h : R.r a a') (h' : R.r b b') :
    R.r (if p then a else b) (if p then a' else b') := by
  split_ifs; exacts [h, h']

theorem listProd {ι : Type} (l : List ι) {f : ι → A} {f' : ι → A'} (h : ∀ i ∈ l, R.r (f i) (f' i)) :
    R.r (l.map f).prod (l.map f').prod := by
  induction l with
  | nil => simpa using R.one
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons]
    exact R.mul (h a List.mem_cons_self) (ih fun i hi => h i (List.mem_cons_of_mem _ hi))

variable (R)

def mat (n : Type) [Fintype n] [DecidableEq n] : SRel (Matrix n n A) (Matrix n n A') where
  r M M' := ∀ i j, R.r (M i j) (M' i j)
  zero _ _ := R.zero
  one i j := by rw [Matrix.one_apply, Matrix.one_apply]; exact ite _ R.one R.zero
  add h h' i j := R.add (h i j) (h' i j)
  mul h h' i j := by
    rw [Matrix.mul_apply, Matrix.mul_apply]; exact sum _ fun k _ => R.mul (h i k) (h' k j)
  smul c _ _ h i j := R.smul c (h i j)
  star h i j := by rw [Matrix.star_apply, Matrix.star_apply]; exact R.star (h j i)

variable {R}

theorem m2 {a b c d : A} {a' b' c' d' : A'} (ha : R.r a a') (hb : R.r b b') (hc : R.r c c') (hd : R.r d d') :
    (R.mat (Fin 2)).r !![a, b; c, d] !![a', b'; c', d'] := by
  intro i j
  fin_cases i <;> fin_cases j <;> simpa

variable {S : Type} [Fintype S] [DecidableEq S]

theorem eU (a : S) (i j : Fin 2) : (R.mat (Ix S)).r (Wd.eU a i j) (Wd.eU a i j) := fun x y => by
  simp only [Wd.eU, Matrix.of_apply]; exact ite _ R.one R.zero

theorem io {x : A} {x' : A'} (h : R.r x x') : (R.mat (Ix S)).r (Wd.io x) (Wd.io x') := fun i j => by
  simp only [Wd.io, Matrix.scalar_apply, Matrix.diagonal_apply]; exact ite _ h R.zero

theorem ins (a : S) {M : M2 (SlopeTestRemainingChoices S A)} {M' : M2 (SlopeTestRemainingChoices S A')} (h : ((R.mat (Ix S)).mat (Fin 2)).r M M') :
    (R.mat (Ix S)).r (Wd.ins a M) (Wd.ins a M') :=
  sum _ fun i _ => sum _ fun j _ => (R.mat (Ix S)).mul (eU a i j) (h i j)

theorem lift0 {M : M2 A} {M' : M2 A'} (h : (R.mat (Fin 2)).r M M') :
    ((R.mat (Ix S)).mat (Fin 2)).r (Wd.lift0 M) (Wd.lift0 M') := fun i j => io (h i j)

theorem Rh0 (a : S) (D : ℂ) : ((R.mat (Ix S)).mat (Fin 2)).r (Wd.Rh0 a D) (Wd.Rh0 a D) :=
  SRel.smul _ _ (sub (SRel.smul _ _ (SRel.one _)) fun i j => eU a j i)

theorem Rht0 (a : S) (D : ℂ) : ((R.mat (Ix S)).mat (Fin 2)).r (Wd.Rht0 a D) (Wd.Rht0 a D) :=
  SRel.smul _ _ (sub (SRel.smul _ _ (SRel.one _)) fun i j => eU a i j)

def Site (σ : Wd.Site A) (σ' : Wd.Site A') : Prop := R.r σ.p σ'.p ∧ R.r σ.c σ'.c ∧ R.r σ.ci σ'.ci

theorem Ts {σ : Wd.Site A} {σ' : Wd.Site A'} (h : R.Site σ σ') (Y : ℂ) :
    (R.mat (Fin 2)).r (Wd.Ts σ Y) (Wd.Ts σ' Y) :=
  m2 (R.add (algMap Y) h.1) (neg h.2.1) h.2.2 R.zero

theorem vlet {σ : Wd.Site A} {σ' : Wd.Site A'} (h : R.Site σ σ') (l : Letter ℂ S) :
    (R.mat (Ix S)).r (Wd.vlet σ l) (Wd.vlet σ' l) := by
  refine ins _ (lift0 ?_)
  split_ifs
  · exact Ts h _
  · exact fun i j => R.star (Ts h _ i j)

theorem bT {σ : Wd.Site A} {σ' : Wd.Site A'} (h : R.Site σ σ') (w : List (Letter ℂ S)) :
    (R.mat (Ix S)).r (Wd.bT σ w) (Wd.bT σ' w) := by
  induction w with
  | nil => exact SRel.one _
  | cons l w ih => exact SRel.mul _ (vlet h l) ih

end SRel

section frames

variable {A A' : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Ring A'] [StarRing A'] [Algebra ℂ A']
  [StarModule ℂ A'] {S : Type} [Fintype S] [DecidableEq S] {r : ℕ}

structure FnRel (R : SRel A A') (L : LevelData A r) (L' : LevelData A' r) : Prop where
  ζ : R.r L.ζ L'.ζ
  ζi : R.r L.ζi L'.ζi
  ζb : R.r L.ζb L'.ζb
  ζbi : R.r L.ζbi L'.ζbi
  GG : R.r L.GG L'.GG
  GGi : R.r L.GGi L'.GGi

structure FrRel (R : SRel A A') (I : Set ℂ) (f : FrameData S A) (f' : FrameData S A') : Prop where
  inv : f.inv = f'.inv
  sub : f.inv ⊆ I
  q : f.q = f'.q
  N : f.N = f'.N
  TT : ∀ Y, star Y = Y → ((R.mat (Ix S)).mat (Fin 2)).r (f.TT Y) (f'.TT Y)
  F : (R.mat (Ix S)).r f.F f'.F
  Fi : (R.mat (Ix S)).r f.Fi f'.Fi
  x : ∀ Y, star Y = Y → (R.mat (Ix S)).r (f.x Y) (f'.x Y)
  xi : ∀ Y, star Y = Y → Y ∈ I → (R.mat (Ix S)).r (f.xi Y) (f'.xi Y)
  c : (R.mat (Ix S)).r f.c f'.c
  ci : (R.mat (Ix S)).r f.ci f'.ci

omit [StarModule ℂ A] in

theorem l_eq {L : LevelData A r} {f : FrameData S A} (hf : IsFrame L f) {Y : ℂ} (hY : Y ∈ f.inv)
    (hY1 : Y + 1 ∈ f.inv) : f.l L Y = f.xi Y * io L.GGi * (f.F * f.TT Y 1 0) * f.Fi := by
  have hG : (io L.GGi : SlopeTestRemainingChoices S A) * io L.GG = 1 := by
    rw [io, io, ← map_mul, L.GGi_GG, map_one]
  rw [hf.frame_l Y hY hY1]
  calc f.l L Y = (f.xi Y * ((io L.GGi * io L.GG) * f.x Y)) * f.l L Y * (f.F * f.Fi) := by
        rw [hG, one_mul, (hf.x_xi Y hY).2, hf.F_Fi, one_mul, mul_one]
    _ = _ := by simp only [mul_assoc]

omit [StarModule ℂ A] [StarModule ℂ A'] in
theorem l_rel {R : SRel A A'} {I : Set ℂ} {L : LevelData A r} {L' : LevelData A' r} (hL : FnRel R L L')
    {f : FrameData S A} {f' : FrameData S A'} (h : FrRel R I f f') (hf : IsFrame L f) (hf' : IsFrame L' f')
    {Y : ℂ} (hr : star Y = Y) (hY : Y ∈ f.inv) (hY1 : Y + 1 ∈ f.inv) : (R.mat (Ix S)).r (f.l L Y) (f'.l L' Y) := by
  rw [l_eq hf hY hY1, l_eq hf' (h.inv ▸ hY) (h.inv ▸ hY1)]
  exact SRel.mul _ (SRel.mul _ (SRel.mul _ (h.xi Y hr (h.sub hY)) (SRel.io hL.GGi))
    (SRel.mul _ h.F (h.TT Y hr 1 0))) h.Fi

omit [StarModule ℂ A] [StarModule ℂ A'] in
theorem d_rel {R : SRel A A'} {I : Set ℂ} {L : LevelData A r} {L' : LevelData A' r} (hL : FnRel R L L')
    {f : FrameData S A} {f' : FrameData S A'} (h : FrRel R I f f') : (R.mat (Ix S)).r (f.d L) (f'.d L') := by
  unfold FrameData.d
  rw [h.N]
  exact SRel.mul _ (SRel.pow (SRel.io (R.mul (R.mul hL.ζ hL.ζb) hL.GGi)) _) h.c

omit [StarModule ℂ A] [StarModule ℂ A'] in
theorem di_rel {R : SRel A A'} {I : Set ℂ} {L : LevelData A r} {L' : LevelData A' r} (hL : FnRel R L L')
    {f : FrameData S A} {f' : FrameData S A'} (h : FrRel R I f f') : (R.mat (Ix S)).r (f.di L) (f'.di L') := by
  unfold FrameData.di
  rw [h.N]
  exact SRel.mul _ h.ci (SRel.pow (SRel.io (R.mul (R.mul hL.GG hL.ζi) hL.ζbi)) _)

theorem star_add_one {Y : ℂ} (h : star Y = Y) : star (Y + 1) = Y + 1 := by rw [star_add, h, star_one]

theorem star_sub_one {Y : ℂ} (h : star Y = Y) : star (Y - 1) = Y - 1 := by rw [star_sub, h, star_one]

omit [StarModule ℂ A] [StarModule ℂ A'] in
theorem plus_rel {R : SRel A A'} {I : Set ℂ} {L : LevelData A r} {L' : LevelData A' r} (hL : FnRel R L L')
    {f : FrameData S A} {f' : FrameData S A'} (h : FrRel R I f f') (hf : IsFrame L f) (hf' : IsFrame L' f')
    (a : S) {Y : ℂ} (hr : star Y = Y) (hY : Y ∈ f.inv) (hY1 : Y + 1 ∈ f.inv) :
    FrRel R I (f.plus L a Y) (f'.plus L' a Y) := by
  have hl := l_rel hL h hf hf' hr hY hY1
  have z := (R.mat (Ix S)).zero
  have o := (R.mat (Ix S)).one
  refine ⟨?_, fun _ hy => h.sub hy.1, ?_, ?_, fun y hy => ?_, ?_, ?_, fun y hy => ?_, fun y hy hI => ?_, ?_, ?_⟩
  · simp only [FrameData.plus, h.inv]
  · simp only [FrameData.plus, h.q]
  · simp only [FrameData.plus, h.N]
  · exact SRel.mul _ (h.TT y hy) (SRel.Rh0 a _)
  · exact SRel.mul _ (SRel.ins a (SRel.mul _ (SRel.m2 (SRel.io hL.ζi) z z (SRel.io hL.ζbi))
      (SRel.m2 o z (SRel.mul _ (SRel.io hL.GG) hl) (SRel.io hL.GG)))) h.F
  · exact SRel.mul _ h.Fi (SRel.ins a (SRel.mul _ (SRel.m2 o z (SRel.neg hl) (SRel.io hL.GGi))
      (SRel.m2 (SRel.io hL.ζ) z z (SRel.io hL.ζb))))
  · exact SRel.mul _ (h.x y hy) (SRel.ins a (SRel.m2 (SRel.smul _ _ o) z z o))
  · exact SRel.mul _ (h.xi y hy hI) (SRel.ins a (SRel.m2 (SRel.smul _ _ o) z z o))
  · show (R.mat (Ix S)).r (f.c * ins a !![f.q Y • f.xi (Y + 1), 0; 0, f.x Y])
      (f'.c * ins a !![f'.q Y • f'.xi (Y + 1), 0; 0, f'.x Y])
    rw [← h.q]
    exact SRel.mul _ h.c (SRel.ins a (SRel.m2 (SRel.smul _ _ (h.xi _ (star_add_one hr) (h.sub hY1))) z z (h.x Y hr)))
  · show (R.mat (Ix S)).r (f.ci * ins a !![(f.q Y)⁻¹ • f.x (Y + 1), 0; 0, f.xi Y])
      (f'.ci * ins a !![(f'.q Y)⁻¹ • f'.x (Y + 1), 0; 0, f'.xi Y])
    rw [← h.q]
    exact SRel.mul _ h.ci (SRel.ins a (SRel.m2 (SRel.smul _ _ (h.x _ (star_add_one hr))) z z (h.xi Y hr (h.sub hY))))

omit [StarModule ℂ A] [StarModule ℂ A'] in
theorem minus_rel {R : SRel A A'} {I : Set ℂ} {L : LevelData A r} {L' : LevelData A' r} (hL : FnRel R L L')
    {f : FrameData S A} {f' : FrameData S A'} (h : FrRel R I f f') (hf : IsFrame L f) (hf' : IsFrame L' f')
    (a : S) {Y : ℂ} (hr : star Y = Y) (hY : Y ∈ f.inv) (hY1 : Y - 1 ∈ f.inv) :
    FrRel R I (f.minus L a Y) (f'.minus L' a Y) := by
  have hl := l_rel hL h hf hf' (star_sub_one hr) hY1 (by rwa [sub_add_cancel])
  have hm : (R.mat (Ix S)).r (f.m L Y) (f'.m L' Y) :=
    SRel.mul _ (SRel.mul _ (di_rel hL h) (SRel.star _ hl)) (d_rel hL h)
  have z := (R.mat (Ix S)).zero
  have o := (R.mat (Ix S)).one
  refine ⟨?_, fun _ hy => h.sub hy.1, ?_, ?_, fun y hy => ?_, ?_, ?_, fun y hy => ?_, fun y hy hI => ?_, ?_, ?_⟩
  · simp only [FrameData.minus, h.inv]
  · simp only [FrameData.minus, h.q]
  · simp only [FrameData.minus, h.N]
  · exact SRel.mul _ (SRel.Rht0 a _) (h.TT y hy)
  · exact SRel.mul _ (SRel.ins a (SRel.mul _ (SRel.m2 (SRel.io hL.ζbi) z z (SRel.io hL.ζi))
      (SRel.m2 o z (SRel.mul _ (SRel.io hL.GG) hm) (SRel.io hL.GG)))) h.F
  · exact SRel.mul _ h.Fi (SRel.ins a (SRel.mul _ (SRel.m2 o z (SRel.neg hm) (SRel.io hL.GGi))
      (SRel.m2 (SRel.io hL.ζb) z z (SRel.io hL.ζ))))
  · exact SRel.mul _ (h.x y hy) (SRel.ins a (SRel.m2 (SRel.smul _ _ o) z z o))
  · exact SRel.mul _ (h.xi y hy hI) (SRel.ins a (SRel.m2 (SRel.smul _ _ o) z z o))
  · show (R.mat (Ix S)).r (f.c * ins a !![f.q (Y - 1) • f.xi (Y - 1), 0; 0, f.x Y])
      (f'.c * ins a !![f'.q (Y - 1) • f'.xi (Y - 1), 0; 0, f'.x Y])
    rw [← h.q]
    exact SRel.mul _ h.c (SRel.ins a (SRel.m2 (SRel.smul _ _ (h.xi _ (star_sub_one hr) (h.sub hY1))) z z (h.x Y hr)))
  · show (R.mat (Ix S)).r (f.ci * ins a !![(f.q (Y - 1))⁻¹ • f.x (Y - 1), 0; 0, f.xi Y])
      (f'.ci * ins a !![(f'.q (Y - 1))⁻¹ • f'.x (Y - 1), 0; 0, f'.xi Y])
    rw [← h.q]
    exact SRel.mul _ h.ci (SRel.ins a (SRel.m2 (SRel.smul _ _ (h.x _ (star_sub_one hr))) z z (h.xi Y hr (h.sub hY))))

omit [StarModule ℂ A] [StarModule ℂ A'] in
theorem start_rel {R : SRel A A'} (hR : R.InvClosed) {L : LevelData A r} {L' : LevelData A' r} (hL : FnRel R L L')
    {st : Start A} {st' : Start A'} (hs : IsLevelStart L st) (hs' : IsLevelStart L' st') (hq : st.q = st'.q)
    (hi : st.inv = st'.inv) (hQ : ∀ Y, star Y = Y → (R.mat (Fin 2)).r (st.QQ Y) (st'.QQ Y)) :
    FrRel R st.inv (st.frame : FrameData S A) (st'.frame : FrameData S A') := by
  have hx : ∀ Y, star Y = Y → R.r (st.x Y) (st'.x Y) := fun Y hY => by
    have e : st.x Y = L.GGi * st.QQ Y 1 1 := by rw [hs.tau, ← mul_assoc, L.GGi_GG, one_mul]
    have e' : st'.x Y = L'.GGi * st'.QQ Y 1 1 := by rw [hs'.tau, ← mul_assoc, L'.GGi_GG, one_mul]
    rw [e, e']; exact R.mul hL.GGi (hQ Y hY 1 1)
  have o := (R.mat (Ix S)).one
  exact ⟨hi, subset_rfl, hq, rfl, fun Y hY => SRel.lift0 (hQ Y hY), o, o, fun Y hY => SRel.io (hx Y hY),
    fun Y hY hI => SRel.io (hR _ _ _ _ (hx Y hY) (hs.x_xi Y hI).1 (hs.x_xi Y hI).2 (hs'.x_xi Y (hi ▸ hI)).1
      (hs'.x_xi Y (hi ▸ hI)).2), o, o⟩

theorem ofWord_rel {R : SRel A A'} (hR : R.InvClosed) {L : LevelData A r} {L' : LevelData A' r} (hL : FnRel R L L')
    (hSL : IsStarLevel L) (hSL' : IsStarLevel L')
    {st : Start A} {st' : Start A'} (hs : IsLevelStart L st) (hs' : IsLevelStart L' st') (hq : st.q = st'.q)
    (hi : st.inv = st'.inv) (hQ : ∀ Y, star Y = Y → (R.mat (Fin 2)).r (st.QQ Y) (st'.QQ Y))
    (w : List (Letter ℂ S)) (hw : AdmRec L st w) :
    AdmRec L' st' w ∧ FrRel R st.inv (ofWord L st w) (ofWord L' st' w) := by
  induction w with
  | nil => exact ⟨trivial, start_rel hR hL hs hs' hq hi hQ⟩
  | cons l w ih =>
    obtain ⟨h0, hsl, hre, hY, hY1, hq'⟩ := hw
    obtain ⟨h0', h⟩ := ih h0
    have hf := frame_of_recursive_word A S r L st w hSL hs h0
    have hf' := frame_of_recursive_word A' S r L' st' w hSL' hs' h0'
    refine ⟨⟨h0', hsl, hre, h.inv ▸ hY, h.inv ▸ hY1, by rw [← h.inv, ← h.q]; exact hq'⟩, ?_⟩
    by_cases hp : l.plus = true
    · simp only [ofWord, hp, if_true]
      exact plus_rel hL h hf hf' _ hre hY hY1
    · simp only [ofWord, hp] at hq' ⊢
      exact minus_rel hL h hf hf' _ hre hY hq'.1

end frames

end

end Formalism.FourierDecayAlt.P.NormalFormRelations
