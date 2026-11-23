import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SqMap
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeneratorRatioUnitExistsStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.AdTr

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.Flat.FrGauge
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)
  {k : Type} [Field k] (x : Sp k ⟶ X)

abbrev sqU : Over.mk ((GF t x ⊗ GF t x).hom ≫ x) ⟶ t.G ⊗ t.G :=
  lift (sqPr t x (fst _ _)) (sqPr t x (snd _ _))

theorem sqPt_left_fst (a : t.G ⊗ t.G ⟶ t.G) :
    (sqPt t x a).left ≫ pullback.fst t.G.hom x = sqMap t x ≫ a.left :=
  pullback.lift_fst _ _ _

theorem fib_ext {T : Over (Sp k)} {a b : T ⟶ GF t x}
    (h : a.left ≫ pullback.fst t.G.hom x = b.left ≫ pullback.fst t.G.hom x) : a = b := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext h
  exact (Over.w a).trans (Over.w b).symm

theorem sqPt_psum {n : ℕ} (xs : Fin n → (t.G ⊗ t.G ⟶ t.G)) (I : Finset (Fin n)) :
    sqPt t x (psum t.G xs I) = psum (GF t x) (fun i => sqPt t x (xs i)) I := by
  apply fib_ext
  rw [sqPt_left_fst]
  refine Eq.symm (psum_push (isGrpPullback_pullback t.G x) _ xs (sqU t x) (fun i => ?_) I)
  apply Over.OverMorphism.ext
  exact sqPt_left_fst t x (xs i)

theorem sqPt_fst : sqPt t x (fst t.G t.G) = fst (GF t x) (GF t x) := by
  apply fib_ext
  rw [sqPt_left_fst]
  show (sqU t x ≫ fst t.G t.G).left = _
  rw [lift_fst]
  rfl

theorem sqPt_snd : sqPt t x (snd t.G t.G) = snd (GF t x) (GF t x) := by
  apply fib_ext
  rw [sqPt_left_fst]
  show (sqU t x ≫ snd t.G t.G).left = _
  rw [lift_snd]
  rfl

theorem sqPt_comp (b : t.G ⊗ t.G ⟶ t.G) (c : t.G ⟶ t.G) :
    sqPt t x (b ≫ c) = sqPt t x b ≫ (Over.pullback x).map c := by
  apply fib_ext
  rw [sqPt_left_fst, Over.comp_left, Over.comp_left, Category.assoc]
  have A : ((Over.pullback x).map c).left ≫ pullback.fst t.G.hom x = pullback.fst t.G.hom x ≫ c.left :=
    pullback.lift_fst _ _ _
  rw [A, ← Category.assoc (Over.Hom.left (sqPt t x b)), sqPt_left_fst]
  simp only [Category.assoc]

theorem psum_comp_hom {S : Scheme.{0}} {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
    (q : A ⟶ B) [IsMonHom q] {T : Over S} {n : ℕ} (ys : Fin n → (T ⟶ A)) (I : Finset (Fin n)) :
    psum A ys I ≫ q = psum B (fun i => ys i ≫ q) I :=
  psum_hom (MonoidHom.mk' (· ≫ q) fun a b => MonObj.mul_comp a b q) ys I

theorem comp_psum {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B]
    {T T' : Over S} (U : T' ⟶ T) {n : ℕ} (ys : Fin n → (T ⟶ B)) (I : Finset (Fin n)) :
    U ≫ psum B ys I = psum B (fun i => U ≫ ys i) I :=
  psum_hom (preHom U) ys I

section Quot

variable {t x} (Q : AbQuot t x)

abbrev qL : GF t x ⊗ GF t x ⟶ Q.tB.G ⊗ Q.tB.G :=
  lift (fst (GF t x) (GF t x) ≫ Q.q) (snd (GF t x) (GF t x) ≫ Q.q)

theorem sqPt_psum_q {n : ℕ} (xs : Fin n → (t.G ⊗ t.G ⟶ t.G)) (ys : Fin n → (Q.tB.G ⊗ Q.tB.G ⟶ Q.tB.G))
    (h : ∀ i, sqPt t x (xs i) ≫ Q.q = qL Q ≫ ys i) (I : Finset (Fin n)) :
    (sqPt t x (psum t.G xs I)).left ≫ Q.q.left = qq Q ≫ (psum Q.tB.G ys I).left := by
  haveI := Q.q_hom
  have e : sqPt t x (psum t.G xs I) ≫ Q.q = qL Q ≫ psum Q.tB.G ys I := by
    rw [sqPt_psum, psum_comp_hom, comp_psum]
    exact congrArg (fun z => psum Q.tB.G z I) (funext h)
  exact congrArg (fun z => z.left) e

theorem sqPt_fst_q : sqPt t x (fst t.G t.G) ≫ Q.q = qL Q ≫ fst Q.tB.G Q.tB.G := by
  rw [sqPt_fst, lift_fst]

theorem sqPt_snd_q : sqPt t x (snd t.G t.G) ≫ Q.q = qL Q ≫ snd Q.tB.G Q.tB.G := by
  rw [sqPt_snd, lift_snd]

theorem sqPt_act_q {b : t.G ⊗ t.G ⟶ t.G} {b' : Q.tB.G ⊗ Q.tB.G ⟶ Q.tB.G}
    (h : sqPt t x b ≫ Q.q = qL Q ≫ b') (a : 𝓞 E) :
    sqPt t x (b ≫ t.act.act a) ≫ Q.q = qL Q ≫ b' ≫ Q.tB.act.act a := by
  rw [sqPt_comp, Category.assoc, Q.act_q, ← Category.assoc, h, Category.assoc]

end Quot

theorem adF_fst (a : 𝓞 E) (i : ULift (Finset (Fin 2)) ⊕ ULift (Finset (Fin 2))) :
    adF t x a i ≫ pullback.fst t.G.hom x = sqMap t x ≫ Sum.elim (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)])
      (cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G]) i := by
  rcases i with I | I
  · exact sqPt_left_fst t x _
  · exact sqPt_left_fst t x _

theorem adF_q {t : SAB H X} {x : Sp k ⟶ X} (Q : AbQuot t x) (a : 𝓞 E) (i : ULift (Finset (Fin 2)) ⊕ ULift (Finset (Fin 2))) :
    adF t x a i ≫ Q.q.left = qq Q ≫ Sum.elim (cφG Q.tB ![fst Q.tB.G Q.tB.G, snd Q.tB.G Q.tB.G ≫ Q.tB.act.act (H.bar a)])
      (cφG Q.tB ![fst Q.tB.G Q.tB.G ≫ Q.tB.act.act a, snd Q.tB.G Q.tB.G]) i := by
  rcases i with I | I
  · refine sqPt_psum_q Q _ _ (fun i => ?_) I.down
    fin_cases i
    · exact sqPt_fst_q Q
    · exact sqPt_act_q Q (sqPt_snd_q Q) _
  · refine sqPt_psum_q Q _ _ (fun i => ?_) I.down
    fin_cases i
    · exact sqPt_act_q Q (sqPt_fst_q Q) _
    · exact sqPt_snd_q Q

theorem adjunction_ratio : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X) (Q : AbQuot t x) (d d' : ℕ) (g : GermAt t x d) (gB : GermAt Q.tB (𝟙 (Sp k)) d'), ∀ (w : LB.Iso (t.PP.L.pull (pullback.fst t.G.hom x)) (Q.tB.PP.L.pull Q.q.left)), w.IsGen → ∀ (a : 𝓞 E) (wL : AdTy t a) (wB : AdTy Q.tB a), wL.IsGen → wB.IsGen → ∃ u : Γ((GF t x ⊗ GF t x).left, ⊤)ˣ, Tr w (adF t x a) (fun i => sqMap t x ≫ Sum.elim (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)]) (cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G]) i) (fun i => qq Q ≫ Sum.elim (cφG Q.tB ![fst Q.tB.G Q.tB.G, snd Q.tB.G Q.tB.G ≫ Q.tB.act.act (H.bar a)]) (cφG Q.tB ![fst Q.tB.G Q.tB.G ≫ Q.tB.act.act a, snd Q.tB.G Q.tB.G]) i) (Sum.elim (cε 2) fun I => -cε 2 I) (LB.pullGen t.PP.L _ _ wL (sqMap t x)) (LB.pullGen Q.tB.PP.L _ _ wB (qq Q)) u := by
  intro E _ _ _ H _ _ X t k _ _ p _ _ x Q d d' g gB w hw a wL wB hL hB
  exact GlobalTheory.T.generator_ratio_unit_exists t.G.left Q.tB.G.left (GF t x).left t.PP.L Q.tB.PP.L (pullback.fst t.G.hom x) Q.q.left
    t.PP.isLB Q.tB.PP.isLB w hw _ _ (adF t x a) _ _ _ _ _ (adF_fst t x a) (adF_q Q a)
    (LB.isGen_pullGen _ _ _ _ hL _) (LB.isGen_pullGen _ _ _ _ hB _)

end GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.AdTr
