import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTorsionPairRepresentativeStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTorsionHomImageStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct

namespace GlobalTheory.FlatTors.TorsMapExists

open ReciprocityTheory.ChartRestriction.G.DVR

theorem isPull_trans {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {T T' T'' : Over (Sp R)}
    {a : T'.left ⟶ T.left} {b : T''.left ⟶ T'.left} {g : GtPt D T} {g' : GtPt D T'} {g'' : GtPt D T''}
    (h : GtPt.IsPull a g g') (h' : GtPt.IsPull b g' g'') : GtPt.IsPull (b ≫ a) g g'' := by
  refine ⟨by rw [h'.1, h.1, Category.assoc], fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩
  rw [val_corr hJ (h'.2 χ), val_pull hJ, val_corr hJ (h.2 χ), val_pull hJ, val_pull hJ, Category.assoc]

theorem isPullF_trans {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {T T' : Over (Sp R)}
    {F : Type} [Field F] [Algebra (FractionRing R) F]
    {a : T'.left ⟶ T.left} {b : Sp F ⟶ T'.left} {g : GtPt D T} {g' : GtPt D T'} {g'' : GtPtF D F}
    (h : GtPt.IsPull a g g') (h' : GtPt.IsPullF F b g' g'') : GtPt.IsPullF F (b ≫ a) g g'' :=
  isPull_trans (T'' := TF (R := R) F) (g'' := ⟨g''.b, g''.s, g''.isGen, g''.s_zero, g''.mult⟩) h h'

theorem pair_trans {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {W : (Sp R).Opens} {ψW : PsiOn D W} {k : ℕ}
    {T T' T'' : Over W.toScheme} {a : T' ⟶ T} {b : T'' ⟶ T'} {p : QkPtW D W ψW k T} {p' : QkPtW D W ψW k T'}
    {p'' : QkPtW D W ψW k T''} (h : QkPtW.IsPull a p p') (h' : QkPtW.IsPull b p' p'') :
    QkPtW.IsPull (b ≫ a) p p'' := by
  have h₁ : p''.y = p.y := Eq.trans h'.1 h.1
  have h₂ := isPull_trans (T := overW W T) (T' := overW W T') (T'' := overW W T'') (a := a.left) (b := b.left)
    (g := p.g) (g' := p'.g) (g'' := p''.g) h.2 h'.2
  exact ⟨h₁, h₂⟩

theorem pairF_trans {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {W : (Sp R).Opens} {ψW : PsiOn D W} {k : ℕ}
    {F : Type} [Field F] [Algebra (FractionRing R) F]
    {T T' : Over W.toScheme} {a : T' ⟶ T} {x : Sp F ⟶ T'.left} {p : QkPtW D W ψW k T} {p' : QkPtW D W ψW k T'}
    {q : QkPt D F k} (h : QkPtW.IsPull a p p') (h' : QkPtW.IsPullF F x p' q) :
    QkPtW.IsPullF F (x ≫ a.left) p q := by
  have h₁ : q.y = p.y := Eq.trans h'.1 h.1
  have h₂ := isPullF_trans (T := overW W T) (T' := overW W T') (a := a.left) (b := x)
    (g := p.g) (g' := p'.g) (g'' := q.g) h.2 h'.2
  exact ⟨h₁, h₂⟩

theorem exists_isTorsMap :
    AllFlat fun {E} _ _ _ {H} {R} _ _ _ {t} P {W} ψW k => ∃ f, IsTorsMap P ψW k f := by
  intro E _ _ _ H R _ _ _ _ hR t P W hW hp ψW k hk
  choose N p₀ hN using GlobalTheory.T.exists_torsion_pair_representative E H R hR t P W hW hp ψW k hk
  choose v hv hvF using fun y => GlobalTheory.T.exists_torsion_hom_image E H R hR t P W hW hp ψW k hk y (N y) (p₀ y) (hN y)
  choose c hc hu using fun y => (hN y).2.2.2
  have key : ∀ y T (p : QkPtW P.D.toPre W ψW k T) (hy : p.y = y),
      (Over.map W.ι).map (c p.y T p rfl) ≫ v p.y = (Over.map W.ι).map (c y T p hy) ≫ v y := by
    intro y T p hy
    subst hy
    rfl
  refine ⟨fun T p => (Over.map W.ι).map (c p.y T p rfl) ≫ v p.y, fun T p => ?_, fun T T' h p p' hh => ?_,
    fun F _ _ _ T x hx p q hq => ?_⟩
  · rw [← MonObj.comp_pow, hv, MonObj.comp_one]
  · have := hu p.y T' p' hh.1 (h ≫ c p.y T p rfl) (pair_trans (hc p.y T p rfl) hh)
    refine (key p.y T' p' hh.1).trans ?_
    rw [← this, Functor.map_comp, Category.assoc]
  · have e : (c p.y T p rfl).left ≫ (overW W (N p.y)).hom = (overW W T).hom :=
      Over.w ((Over.map W.ι).map (c p.y T p rfl))
    have hx' : OverGen F (overW W (N p.y)) (x ≫ (c p.y T p rfl).left) :=
      (Category.assoc _ _ _).trans ((congrArg (x ≫ ·) e).trans hx)
    have := hvF p.y F (x ≫ (c p.y T p rfl).left) hx' q (pairF_trans (hc p.y T p rfl) hq)
    rw [Category.assoc] at this
    exact this

end GlobalTheory.FlatTors.TorsMapExists
