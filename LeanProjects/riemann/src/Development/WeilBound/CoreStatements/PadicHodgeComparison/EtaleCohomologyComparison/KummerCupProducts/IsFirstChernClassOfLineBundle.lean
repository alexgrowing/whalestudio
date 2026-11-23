import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HarishChandraFormulaStatement
import GroundTheory.PAdicHodge.ACrisLog
import GroundTheory.PAdicHodge.UntiltFrobeniusEquivSymmEpsilonNeOne
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GalOCOkToOC
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.IsKumCoc

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison.E

open CH GlobalTheory.EtC

variable {l : ℕ} [Fact l.Prime]

def IsLog (A : PAlg l) (n : ℕ) (w : A.W) (y : A.Acr n) : Prop :=
  ∃ g : ℕ → A.Acr0, (∀ k, (g k).1 = dpw k (w - 1)) ∧
    y = ∑ k ∈ Finset.range (l * n), (-1) ^ k * (k.factorial : A.Acr n) * A.mkAcr n (g (k + 1))

section Line
variable {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* OC l}
  {C : Type 1} [Category.{0} C] (G : C ⥤ El (PX q κ)) (D : LineData X)

structure Lift where
  p : ∀ T : C, Spec (CommRingCat.of (G.obj T).1.obj.U) ⟶ D.Y
  hp : ∀ T : C, p T ≫ D.f = (G.obj T).2.1
  w : ∀ {T T' : C}, (T ⟶ T') → ((G.obj T').1.obj.A)ˣ
  hw : ∀ {T T' : C} (φ : T ⟶ T')
    (h : (Spec.map (CommRingCat.ofHom (PAlg.mapU (G.map φ).1.hom)) ≫ p T) ≫ D.f = p T' ≫ D.f),
    (G.obj T').1.obj.sharp (w φ) = (Scheme.ΓSpecIso (CommRingCat.of (G.obj T').1.obj.U)).hom.hom
      (D.u (Spec.map (CommRingCat.ofHom (PAlg.mapU (G.map φ).1.hom)) ≫ p T) (p T') h)

variable {G D}

def Lift.r (Λ : Lift G D) (s : ComposableArrows C 2) : ((G.obj (s.obj (Fin.last 2))).1.obj.A)ˣ :=
  Units.map (PAlg.Hom.f (G.map (s.map' 1 2)).1.hom).toMonoidHom (Λ.w (s.map' 0 1)) * Λ.w (s.map' 1 2) * (Λ.w (s.map' 0 2))⁻¹

def acrVal {P : PAlg l ⥤ Type} (G : C ⥤ El P) (n : ℕ) (T : C) (x : (G ⋙ modF (AcrEl P n)).obj T) : (G.obj T).1.obj.Acr n := x

def tei (A : PAlg l) (u : (A.A)ˣ) : A.W := WittVector.teichmuller l u.val

def Lift.IsCoc (Λ : Lift G D) (n : ℕ) (z : Cn (G ⋙ modF (AcrEl (PX q κ) n)) 2) : Prop :=
  ∀ s : ComposableArrows C 2, IsLog (G.obj (s.obj (Fin.last 2))).1.obj n (tei (G.obj (s.obj (Fin.last 2))).1.obj (Λ.r s))
    (acrVal G n (s.obj (Fin.last 2)) (z s))

variable (q κ D) in

def IsFirstChernClassOfLineBundle (y : ∀ n, MH (PX q κ) n 2) : Prop :=
  ∀ (C : Type 1) [Category.{0} C] (G : C ⥤ El (PX q κ)) (Λ : Lift G D) (n : ℕ),
    ∃ (z : Cn (G ⋙ modF (AcrEl (PX q κ) n)) 2) (hz : d _ 2 z = 0), Λ.IsCoc n z ∧
      (cx _).cls z hz = (Mor.restrict (modF (AcrEl (PX q κ) n)) G).pull 2 (y n)

end Line

variable (l) in

structure RIn : Prop where
  splitUg : ∀ A : PAlg l, A.IsTest → Splits (Spec (CommRingCat.of A.Ug))
  splitU : ∀ A : PAlg l, A.IsTest → Splits (Spec (CommRingCat.of A.U))
  tf : ∀ A : PAlg l, (l : A.U) ∈ nonZeroDivisors A.U
  idem : ∀ A : PAlg l, A.IsTest → ∀ e : A.Ug, IsIdempotentElem e →
    ∃! e₀ : A.A, IsIdempotentElem e₀ ∧ algebraMap A.U A.Ug (A.sharp e₀) = e
  sharp : ∀ A : PAlg l, A.IsTest → ∀ u : (A.U)ˣ, ∃ w : (A.A)ˣ, A.sharp w = u

variable {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

abbrev gb (M : Model l K) : Scheme.{0} := GlobalTheory.Et.geom (PadicAlgCl l) M.q

variable (l K) in

abbrev EtFam : Type 1 := ∀ (M : Model l K) (n j : ℕ), Ht (l ^ n) (sch.obj (gb M)) j 0 →+ M.MH n j

namespace EtFam
variable (e : EtFam l K)

def Red : Prop := ∀ (M : Model l K) (n j : ℕ) (x : Ht (l ^ (n + 1)) (sch.obj (gb M)) j 0),
  (MSys M.P j).r n (e M (n + 1) j x) = e M n j (GlobalTheory.EtC.red (l ^ (n + 1)) (l ^ n) _ j 0 x)

def Equi : Prop := ∀ (M : Model l K) (n j : ℕ) (σ : Gal(PadicAlgCl l/K)) (x : Ht (l ^ n) (sch.obj (gb M)) j 0),
  e M n j (pull _ (sch.map (GlobalTheory.Et.galMap (PadicAlgCl l) M.q σ)) _ j x) = M.galMH σ n j (e M n j x)

def Phi : Prop := ∀ (M : Model l K) (n j : ℕ) (x : Ht (l ^ n) (sch.obj (gb M)) j 0), M.phiMH n j (e M n j x) = e M n j x

def Natu : Prop := ∀ (M N : Model l K) (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (n j : ℕ) (x : Ht (l ^ n) (sch.obj (gb N)) j 0),
  e M n j (pull _ (sch.map (GlobalTheory.Et.geomMap (PadicAlgCl l) M.q (Model.genMap u hu) (Model.genMap_q u hu))) _ j x) =
    Model.pullMH u hu n j (e N n j x)

def Cup : Prop := ∀ (M : Model l K) (n i j : ℕ) (x : Ht (l ^ n) (sch.obj (gb M)) i 0) (y : Ht (l ^ n) (sch.obj (gb M)) j 0),
  e M n (i + j) ((GlobalTheory.EtC.cup (l ^ n) x y).cast (by push_cast; rfl) (add_zero 0)) =
    (mulP (AcrEl M.P n)).cup rfl (e M n i x) (e M n j y)

def One : Prop := ∀ M : Model l K, ∃ v : Hl l (sch.obj (gb M)) (0 : ℕ) 0, ∀ n, e M n 0 (v.1 n) = oneH (AcrEl M.P n)

def tMul (M : Model l K) (v : Hl l (sch.obj (gb M)) (2 : ℕ) 0) (n : ℕ) : M.MH n 2 :=
  (ACris.periodT (untilt_epsilon (p := l)) : Acris l) • e M n 2 (v.1 n)

def C1 : Prop := ∀ (M : Model l K) (D : LineData M.X), ∃ v : Hl l (sch.obj (gb M)) (2 : ℕ) 0,
  IsFirstChernClassOfLineBundle M.p (okToOC l K) D (e.tMul M v)

structure Good : Prop where
  red : e.Red
  equi : e.Equi
  phi : e.Phi
  nat : e.Natu
  cup : e.Cup
  one : e.One
  c1 : e.C1

end EtFam

variable (l K) in

def EtMap : Prop := ∃ e : EtFam l K, e.Good

def LiftEx : Prop := ∀ (l : ℕ) [Fact l.Prime], RIn l → ∀ (O : Type) [CommRing O] (X : Scheme.{0}) (q : X ⟶ Spec (CommRingCat.of O))
  (κ : O →+* OC l) (C : Type 1) [Category.{0} C] (G : C ⥤ El (PX q κ)) (D : LineData X),
  (∀ p : ∀ T : C, Spec (CommRingCat.of (G.obj T).1.obj.U) ⟶ D.Y, (∀ T, p T ≫ D.f = (G.obj T).2.1) → ∃ Λ : Lift G D, Λ.p = p) ∧
  (Etale D.f → Nonempty (Lift G D))

def FirstChernUniqueEtale : Prop := ∀ (l : ℕ) [Fact l.Prime], RIn l → ∀ (O : Type) [CommRing O] (X : Scheme.{0}) (q : X ⟶ Spec (CommRingCat.of O))
  (κ : O →+* OC l) (D : LineData X), Etale D.f → ∀ y y', IsFirstChernClassOfLineBundle q κ D y → IsFirstChernClassOfLineBundle q κ D y' → y = y'

def EtaleComparisonMapExists : Prop := EtIn → ∀ (l : ℕ) [Fact l.Prime], RIn l → ∀ K : IntermediateField ℚ_[l] (PadicAlgCl l), EtMap l K

end CrystallineSemistableComparison.E
