import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.SymmetricAdjointUnits
import Formalism.LocalToGlobal.ProjectiveLattices.IsThRule

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.PrimitiveGermFrames

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.JetChartLaws GlobalTheory.IndefiniteRowSideFullHecke.RigidAdjointFrameLaws

variable {X₀ : Scheme.{0}} {S : Type} [CommRing S]

section Group

variable (G : Over X₀) [GrpObj G] [IsCommMonObj G]

def primφ (α : G ⟶ G) : ULift.{0} (Finset (Fin 2)) ⊕ PUnit → (G.left ⟶ G.left) :=
  Sum.elim (lamφ G ![𝟙 G, α]) fun _ => 𝟙 G.left

def primε : ULift.{0} (Finset (Fin 2)) ⊕ PUnit → ℤ := Sum.elim lamε fun _ => -1

def primGen (L : LB G.left) (α : G ⟶ G) (w : LB.Iso L (cubeLB G ![𝟙 G, α] L)) :
    LB.Gen (LB.LinComb L (primφ G α) primε) where
  s := fun j => res
    (le_inf (fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inl k))
      (fun _ hy => Set.mem_iInter.1 hy (Sum.inr PUnit.unit)) :
      LB.wchart L (primφ G α) j ≤
        LB.wchart L (lamφ G ![𝟙 G, α]) (j ∘ Sum.inl) ⊓ L.U (j (Sum.inr PUnit.unit)))
    (w.s (j ∘ Sum.inl, j (Sum.inr PUnit.unit)))

def IsRigPrim (L : RigLB G) (α : G ⟶ G) (w : LB.Iso L.L (cubeLB G ![𝟙 G, α] L.L)) : Prop :=
  w.IsGen ∧
  LB.Gen.Corr L.L _ _ _ _
    (LB.mulGen L.L _ _ _ _ (LB.pullGen L.L _ _ (primGen G L.L α w) (eSec G)) L.rig) (LB.oneGen L.L)

variable (x : Sp S ⟶ X₀) {d : ℕ}

omit [GrpObj G] [IsCommMonObj G] in

abbrev FrameL (L : LB G.left) (j : JetPts G x d) : Type :=
  ∀ m : ℕ, LB.Gen (LB.LinComb L (Y := (algO x (Jet S (Fin 1 × Fin d) m)).left) (K := Fin 1)
    (fun _ => (jPt G x j 1 m 0).left) (fun _ => 1))

variable {G x}

def IsFrameLVia {L : LB G.left} {α : G ⟶ G} (w : LB.Iso L (cubeLB G ![𝟙 G, α] L)) {j : JetPts G x d}
    (e : FrameFam G x L j) (A : Germ.Pt S 1 d) (eL : FrameL G x L j) : Prop :=
  IsFrame e ∧ EndIs G x j α A ∧
  ∀ m, (eL m).IsGen ∧
    LB.Gen.Corr L _ _ _ _
      (LB.mulGen L _ _ _ _ (LB.pullGen L _ _ (primGen G L α w) (jPt G x j 1 m 0).left) (eL m))
      (frAt e (n := 1) m (Germ.pt S d 0) (Germ.comp1 A (Germ.pt S d 0)))

end Group

def toBase (x : Sp S ⟶ X₀) (B : Type) [CommRing B] [Algebra S B] : algO x B ⟶ Over.mk x :=
  Over.homMk (spMap (algebraMap S B)) rfl

def funOn {B : Type} [CommRing B] (b : B) : Γ(Sp B, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b

section Germ

variable {G : Over X₀} [GrpObj G] {x : Sp S ⟶ X₀} {d : ℕ}

def IsGermIn {L : LB G.left} {j : JetPts G x d} (eL : FrameL G x L j) (k : ℤ)
    (F : LB.Sec (Out.LPow G L k (Over.mk x))) (f : Germ.PS S 1 d) : Prop :=
  ∀ m, ∃ F' : LB.Sec (Out.LPow G L k (algO x (Jet S (Fin 1 × Fin d) m))),
    Out.IsPullSec G L k (toBase x (Jet S (Fin 1 × Fin d) m) ▷ G) (whiskerRight_snd _ _) F F' ∧
    Out.IsValueAt G L k F' (jPt G x j 1 m 0) (Out.powFrame G L (jPt G x j 1 m 0) (eL m) k)
      (funOn (psJet m f))

end Germ

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

abbrev PrimIso (t : SAB H X₀) : Type :=
  LB.Iso t.PP.L (cubeLB t.G ![𝟙 t.G, t.act.act H.w0] t.PP.L)

def IsPrim (t : SAB H X₀) (w : PrimIso t) : Prop := IsRigPrim t.G t.PP (t.act.act H.w0) w

def IsFrameL (t : SAB H X₀) (x : Sp S ⟶ X₀) {d : ℕ} (j : JetPts t.G x d) (e : FrameFam t.G x t.PP.L j)
    (W : Germ.Pt S 1 d) (eL : FrameL t.G x t.PP.L j) : Prop :=
  IsFormalParam t.G x j ∧ ∃ w : PrimIso t, IsPrim t w ∧ IsFrameLVia w e W eL

def IsGerm (t : SAB H X₀) (x : Sp S ⟶ X₀) {d : ℕ} (j : JetPts t.G x d) (e : FrameFam t.G x t.PP.L j)
    (W : Germ.Pt S 1 d) (k : ℤ) (F : LB.Sec (Out.LPow t.G t.PP.L k (Over.mk x))) (f : Germ.PS S 1 d) : Prop :=
  ∃ eL : FrameL t.G x t.PP.L j, IsFrameL t x j e W eL ∧ IsGermIn eL k F f

def IsGermOf [StarRing (𝓞 E)] (t : SAB H X₀) (x : Sp S ⟶ X₀) {d : ℕ} (j : JetPts t.G x d)
    (e : FrameFam t.G x t.PP.L j) (B : Germ.FB S d (𝓞 E)) (k : ℤ)
    (F : LB.Sec (Out.LPow t.G t.PP.L k (Over.mk x))) (f : Germ.PS S 1 d) : Prop :=
  Realises t x j e B ∧ IsGerm t x j e (B.A.act H.w0) k F f

def PrimSt (t : SAB H X₀) : Prop :=
  (∃ w, IsPrim t w) ∧ (IsProper t.G.hom → ∀ w w', IsPrim t w → IsPrim t w' → w = w')

def FrameLSt (t : SAB H X₀) (x : Sp S ⟶ X₀) (d : ℕ) : Prop :=
  ∀ (w : PrimIso t) (j : JetPts t.G x d) (e : FrameFam t.G x t.PP.L j) (W : Germ.Pt S 1 d),
    IsPrim t w → IsFormalParam t.G x j → IsFrame e → EndIs t.G x j (t.act.act H.w0) W →
      ∃! eL : FrameL t.G x t.PP.L j, IsFrameLVia w e W eL

def GermSt (t : SAB H X₀) (x : Sp S ⟶ X₀) (d : ℕ) : Prop :=
  ∀ (j : JetPts t.G x d) (e : FrameFam t.G x t.PP.L j) (W : Germ.Pt S 1 d) (eL : FrameL t.G x t.PP.L j),
    IsFrameL t x j e W eL → ∀ (k : ℤ) (F : LB.Sec (Out.LPow t.G t.PP.L k (Over.mk x))),
      ∃! f : Germ.PS S 1 d, IsGermIn eL k F f

theorem sum_primε : ∑ k, primε k = -1 := by
  decide

end GlobalTheory.IndefiniteRowSideFullHecke.PrimitiveGermFrames
