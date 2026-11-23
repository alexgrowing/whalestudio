import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsToricRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullFib
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.LabTrans

open GlobalTheory.ArcPull GlobalTheory.TorusExt GlobalTheory.ArcExt ReciprocityTheory.ChartRestriction.G.DVR

section Ext

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F F' F'' : Type} [Field F] [Algebra (FractionRing R) F]
  [Field F'] [Algebra (FractionRing R) F'] [Field F''] [Algebra (FractionRing R) F''] {k : ℕ}

theorem qkExt_trans {f : F →+* F'} {g : F' →+* F''} {p : QkPt D F k} {q : QkPt D F' k} {r : QkPt D F'' k}
    (h₁ : QkExt f p q) (h₂ : QkExt g q r) : QkExt (g.comp f) p r := by
  have hs : spMap (g.comp f) = spMap g ≫ spMap f := Geo.Tor.spMap_comp _ _
  refine ⟨h₂.1.trans h₁.1, by rw [h₂.2.1, h₁.2.1, hs, Category.assoc], fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩
  refine ((val_corr hJ (h₂.2.2 χ) _).trans ((val_pull hJ _ _ _).trans ((val_corr hJ (h₁.2.2 χ) _).trans
    (val_pull hJ _ _ _)))).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
  exact congrArg (fun s => val (p.g.s χ) s y J) ((Category.assoc _ _ _).trans (congrArg (𝟙 _ ≫ ·) hs.symm))

theorem qkExt_inj (hB : D.TauBimult) (f : F →ₐ[FractionRing R] F') {p q : QkPt D F k} {r : QkPt D F' k}
    (h₁ : QkExt f.toRingHom p r) (h₂ : QkExt f.toRingHom q r) : p = q := by
  have e := ((qkExt_iff hB _ f.comp_algebraMap _ _).1 h₁).symm.trans ((qkExt_iff hB _ f.comp_algebraMap _ _).1 h₂)
  exact qk_ext (congrArg QkPt.y e :) (gtExt_injective _ f.comp_algebraMap (congrArg QkPt.g e))

theorem exists_ext (hB : D.TauBimult) (f : F →ₐ[FractionRing R] F') (p : QkPt D F k) : ∃ r, QkExt f.toRingHom p r :=
  ⟨_, (qkExt_iff hB _ f.comp_algebraMap _ _).2 rfl⟩

theorem ext_unique (hB : D.TauBimult) (f : F →ₐ[FractionRing R] F') {p : QkPt D F k} {r r' : QkPt D F' k}
    (h₁ : QkExt f.toRingHom p r) (h₂ : QkExt f.toRingHom p r') : r = r' :=
  ((qkExt_iff hB _ f.comp_algebraMap _ _).1 h₁).trans ((qkExt_iff hB _ f.comp_algebraMap _ _).1 h₂).symm

theorem exists_of_ext [CharZero R] [IsAlgClosed F] [IsAlgClosed F'] (hB : D.TauBimult) (f : F →ₐ[FractionRing R] F')
    (hk : 1 ≤ k) (r : QkPt D F' k) : ∃ p : QkPt D F k, QkExt f.toRingHom p r := by
  have : CharZero F := (RingHom.charZero_iff (algebraMap (FractionRing R) F).injective).1 inferInstance
  obtain ⟨p, hp⟩ := exists_qkExt f.toRingHom f.comp_algebraMap hB GlobalTheory.firstFiveLaws.1 (Nat.cast_ne_zero.2 (by omega)) r
  exact ⟨p, (qkExt_iff hB _ f.comp_algebraMap _ _).2 hp.symm⟩

end Ext

theorem exists_lift_pt {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {ga : FractionRing R →+* FractionRing R'}
    {A : Over (Sp (FractionRing R))} {A' : Over (Sp (FractionRing R'))} {a : A'.left ⟶ A.left}
    (h : IsPullback a A'.hom A.hom (spMap ga)) {F F' : Type} [Field F] [Field F'] [Algebra (FractionRing R) F]
    [Algebra (FractionRing R') F'] (f : F →+* F') (hf : f.comp (algebraMap (FractionRing R) F) = (algebraMap _ F').comp ga)
    (x : TFK (R := R) F ⟶ A) : ∃ x' : TFK (R := R') F' ⟶ A', x'.left ≫ a = spMap f ≫ x.left := by
  have w : (spMap f ≫ x.left) ≫ A.hom = jFK (R := R') F' ≫ spMap ga := by
    rw [Category.assoc, Over.w x]
    exact (Geo.Tor.spMap_comp _ _).symm.trans ((congrArg spMap hf).trans (Geo.Tor.spMap_comp _ _))
  exact ⟨Over.homMk (h.lift _ _ w) (h.lift_snd _ _ w), h.lift_fst _ _ w⟩

theorem eq_fracMap {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'}
    (hφ : Function.Injective φ) {ga : FractionRing R →+* FractionRing R'}
    (h : ∀ r, ga (algebraMap R _ r) = algebraMap R' _ (φ r)) : ga = fracMap hφ :=
  IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => (h r).trans (fracMap_algebraMap hφ r).symm)

theorem exists_fib_cancel {S S' S₀ S₁ : Scheme.{0}} {A : PolAV S} {A' : PolAV S'} {A₀ : PolAV S₀} {A₁ : PolAV S₁}
    {f : S' ⟶ S} {f₀ : S₀ ⟶ S} {g : S₁ ⟶ S₀} {g' : S₁ ⟶ S'} (sq : g' ≫ f = g ≫ f₀)
    {a : A'.A.left ⟶ A.A.left} {a₀ : A₀.A.left ⟶ A.A.left} {b : A₁.A.left ⟶ A₀.A.left}
    (ha : IsGrpPullback A'.A A.A f a) (la : LBIso A'.L (A.L.pull a))
    (ha₀ : IsGrpPullback A₀.A A.A f₀ a₀) (la₀ : LBIso A₀.L (A.L.pull a₀))
    (hb : IsGrpPullback A₁.A A₀.A g b) (lb : LBIso A₁.L (A₀.L.pull b)) :
    ∃ a₁ : A₁.A.left ⟶ A'.A.left, a₁ ≫ a = b ≫ a₀ ∧ IsGrpPullback A₁.A A'.A g' a₁ ∧ LBIso A₁.L (A'.L.pull a₁) := by
  have n := (hb.comp ha₀).congr sq.symm rfl
  have w : (b ≫ a₀) ≫ A.A.hom = (A₁.A.hom ≫ g') ≫ f := n.1.w.trans (Category.assoc _ _ _).symm
  have e := ha.1.lift_fst _ _ w
  refine ⟨ha.1.lift _ _ w, e, IsGrpPullback.cancel ha (n.congr rfl e.symm) (ha.1.lift_snd _ _ w), ?_⟩
  have l₁ : LBIso (A₀.L.pull b) (A.L.pull (b ≫ a₀)) :=
    la₀.chartPull (Geo.Tor.chartPullPull A₀.L _ _ rfl)
      (chartPullSame A.L (fun _ : PUnit => b ≫ a₀) (fun _ => a₀) _ b fun _ => rfl)
  have l₂ : LBIso (A'.L.pull (ha.1.lift _ _ w)) (A.L.pull (b ≫ a₀)) :=
    la.chartPull (Geo.Tor.chartPullPull A'.L _ _ rfl)
      (chartPullSame A.L (fun _ : PUnit => b ≫ a₀) (fun _ => a) _ _ fun _ => e.symm)
  exact LBIso.trans A₁.isLB (pull_isLB A.isLB _) (pull_isLB A'.isLB _)
    (LBIso.trans A₁.isLB (pull_isLB A₀.isLB _) (pull_isLB A.isLB _) lb l₁) l₂.symm

theorem nonempty_lift (K F : Type) [Field K] [Field F] [IsAlgClosed F] [Algebra K F] :
    Nonempty (AlgebraicClosure K →ₐ[K] F) := ⟨IsAlgClosed.lift⟩

end GlobalTheory.LabTrans

namespace GlobalTheory.Mum

open GlobalTheory.LabTrans GlobalTheory.ArcPull GlobalTheory.TorusExt

end GlobalTheory.Mum
