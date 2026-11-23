import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.ExampleSatisfiesConditionsAtFive
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.ONLeaves
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.ONPage
import Formalism.LocalToGlobal.Divisibility.Numbers
import Formalism.LocalToGlobal.Columns.AdelicLemmas
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas

open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.IndefR.Obj

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.IndefR.Links Formalism.IndefR.Arith

noncomputable instance kPFintype {E : Type} [Field E] [NumberField E] (PP : Pl E) : Fintype (kP PP) :=
  Fintype.ofFinite _

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem r_pos (D : D7) : D.R.r - 1 + 1 = D.R.r := by
  have h := D.R.m_add_three_le_k
  unfold Ranks.r
  omega

abbrev OnP (R : RealDat D A Ks) : Type := ∀ v : R.Pg, ↥(mirabSub (kP v.1) (D.R.r - 1))

def glCast (D : D7) (k : Type) [CommRing k] : GL (Fin (D.R.r - 1 + 1)) k →* GL (Fin D.R.r) k :=
  Units.map (Matrix.reindexAlgEquiv k k (finCongr (r_pos D))).toAlgHom.toRingHom.toMonoidHom

def mirabolicInclusion (R : RealDat D A Ks) : OnP R →* G0 R.Pg D.R.r :=
  MonoidHom.pi fun v => (glCast D (kP v.1)).comp ((mirabSub (kP v.1) (D.R.r - 1)).subtype.comp (Pi.evalMonoidHom _ v))

def incl (R : RealDat D A Ks) : OnP R →* G := R.eG.symm.toMonoidHom.comp (mirabolicInclusion R)

def psiVal (F : Face D A) (g : G) (h : g ∈ (F.lvl false).P) : D.what₂.LL :=
  ((((F.lvl false).ψ ⟨g, h⟩)⁻¹ : D.what₂.LLˣ) : D.what₂.LL)

open Classical in

def psiOn (R : RealDat D A Ks) (F : Face D A) (u : OnP R) : 𝓞 D.what₂.LL :=
  if h : incl R u ∈ (F.lvl false).P then
    (if hi : IsIntegral ℤ (psiVal F (incl R u) h) then ⟨psiVal F (incl R u) h, hi⟩ else 0)
  else 0

def algSpan (R : RealDat D A Ks) (i : Fin D.R.m) (S : Set (R.HW i (sg0 D A)).H) :
    Submodule (𝓞 D.what₂.LL) (Fin (R.nW i) → D.what₂.LL) :=
  Submodule.span (𝓞 D.what₂.LL) {x | (R.FW i).j (sg0 D A) x ∈ S}

def remOf {n : ℕ} (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (Ms Th : Submodule (𝓞 D.what₂.LL) (Fin n → D.what₂.LL)) (E : ℕ) :
    ℝ :=
  max 0 (sSup (Set.range fun W : Submodule D.what₂.LL (Fin n → D.what₂.LL) =>
    (lix v (cut W Ms) (cut W Th) : ℝ) - (E : ℝ) * (finrank D.what₂.LL W : ℝ)))

structure OnIn (R : RealDat D A Ks) where

  run : Bool → HeightOneSpectrum (𝓞 D.what₂.LL) → ∀ i : Fin D.R.m, Set (R.HW i (sg0 D A)).H

  serN : HeightOneSpectrum (𝓞 D.what₂.LL) → ∀ i : Fin D.R.m, Set (R.HW i (sg0 D A)).H

  serK : HeightOneSpectrum (𝓞 D.what₂.LL) → ∀ i : Fin D.R.m, Set (R.HW i (sg0 D A)).H

  ser0 : HeightOneSpectrum (𝓞 D.what₂.LL) → ∀ i : Fin D.R.m, Set (R.HW i (sg0 D A)).H

  serJ : HeightOneSpectrum (𝓞 D.what₂.LL) → ∀ i : Fin D.R.m, Set (R.HW i (sg0 D A)).H

  serX : HeightOneSpectrum (𝓞 D.what₂.LL) → ∀ i : Fin D.R.m, Set (R.HW i (sg0 D A)).H

  σ : HeightOneSpectrum (𝓞 D.what₂.LL) → Fin D.R.m → D.what₂.LL

  E : HeightOneSpectrum (𝓞 D.what₂.LL) → Fin D.R.m → ℕ

  ε0 : HeightOneSpectrum (𝓞 D.what₂.LL) → Fin D.R.m → ℝ

  nnK : Fin D.R.m → D.what₂.LL

  Jp : Fin D.R.m → ℕ → ℝ

  Sc : ℝ

  eta : ℝ

  T : ℕ

  DF : ℝ

  eps : ℝ

  th : ℕ → ℝ

  ad : ℕ → ℝ

def OnIn.withNum {R : RealDat D A Ks} (I : OnIn R) (N : NumDatum) : OnIn R :=
  { I with eps := N.sc.eps, Sc := N.Sc, eta := N.eta }

abbrev Sb (R : RealDat D A Ks) (F : Face D A) := (R.toCx F).data F.cr false

def eOn (R : RealDat D A Ks) (j : Fin D.R.m) : (Fin (R.nW j) → D.what₂.LL) →ₗ[D.what₂.LL] (Fin (R.nW j) → D.what₂.LL) :=
  (R.FW j).eOp fun g => (idemOf A.X).coeff g

def MsOf (R : RealDat D A Ks) (j : Fin D.R.m) : Submodule (𝓞 D.what₂.LL) (Fin (R.nW j) → D.what₂.LL) :=
  Submodule.span (𝓞 D.what₂.LL) ((R.FW j).MK : Set (Fin (R.nW j) → D.what₂.LL))

abbrev xAt (F : Face D A) (R : RealDat D A Ks) : ℝ := (F.fc (R.toCx F).zs).Z.x

def onMk (R : RealDat D A Ks) (F : Face D A) {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} (S : IndefData Df)
    (eJ : Bs.J ≃ Fin D.R.m) (φ : ∀ j, (Fin (S.dW j) → D.what₂.LL) →ₗ[D.what₂.LL] (Fin (R.nW (eJ j)) → D.what₂.LL)) (x : ℝ)
    (c : OnConst) (I : OnIn R) : OnObj S (OnP R) c where
  nZ j := R.nW (eJ j)
  ρ j := (R.FW (eJ j)).ρ.comp (incl R)
  U := Subgroup.pi Set.univ fun v => uniSub (kP v.1) (D.R.r - 1)
  ψ := psiOn R F
  V₀ j := LinearMap.range (eOn R (eJ j))
  e j := eOn R (eJ j)
  Ms j := MsOf R (eJ j)
  φ := φ
  Th1 v j := algSpan R (eJ j) (I.run (decide (plc v = D.host.pde)) v (eJ j))
  Th v j := algSpan R (eJ j) (I.serN v (eJ j))
  ThK v j := algSpan R (eJ j) (I.serK v (eJ j))
  Th0 v j := algSpan R (eJ j) (I.ser0 v (eJ j))
  ThJ v j := algSpan R (eJ j) (I.serJ v (eJ j))
  X₃ v j := (algSpan R (eJ j) (I.serX v (eJ j))).map ((eOn R (eJ j)).restrictScalars (𝓞 D.what₂.LL))
  σ v j := I.σ v (eJ j)
  a v j := Classical.epsilon fun a : D.what₂.LL => a ≠ 0 ∧ vw v a = (I.E v (eJ j) : ℤ)
  E v j := I.E v (eJ j)
  r1 v j := if plc v = D.host.pde then 0 else
    remOf v (MsOf R (eJ j)) (algSpan R (eJ j) (I.run false v (eJ j))) (I.E v (eJ j))
  r2 v j := if plc v = D.host.pde then
    remOf v (MsOf R (eJ j)) (algSpan R (eJ j) (I.run true v (eJ j))) (I.E v (eJ j)) else 0
  pde := D.host.pde
  ε0 v j := I.ε0 v (eJ j)
  nX v j := Df.dZ j (S.μ v)
  θ' v j := φ j ∘ₗ (S.θ j (S.μ v)).mulVecLin
  eX _ _ := LinearMap.id
  pr _ _ := LinearMap.id
  Mt v j := Df.Tl j (S.μ v)
  nnK j := I.nnK (eJ j)
  Jp j := I.Jp (eJ j)
  k := D.R.k
  m := D.R.m
  f := D.R.f
  bp := x * Real.exp (x ^ I.eps) / Real.exp (x ^ (I.eps / 3))
  Sc := I.Sc
  eta := I.eta
  T := (I.T : ℝ)
  DF := I.DF
  X2 := x * Real.exp (x ^ I.eps) / (x * Real.exp (x ^ I.eps) / Real.exp (x ^ (I.eps / 3)) / (x * ((D.R.f : ℝ) / 2)))
  x := x
  eps := I.eps
  vd := Real.logb 2 D.host.QS
  rr := D.R.r
  de2 := 1
  Nc := (D.host.T2.card : ℝ) / ((D.R.f : ℝ) / 2) * (D.R.k : ℝ) * Real.exp (x ^ I.eps) * x ^ (2 * I.eps) / ((D.R.f : ℝ) / 2)
  wt _ := 2 * (D.R.f : ℝ) * Real.exp (x ^ I.eps)
  th := I.th
  ad := I.ad
  T2 := D.host.T2.card
  g1 := D.host.g 0
  g2 := D.host.g 1
  q1 := D.host.q
  sm := D.host.small
  dd := D.host.d

def onObjOf (R : RealDat D A Ks) (F : Face D A) (c : OnConst) (I : OnIn R) : OnObj (Sb R F) (OnP R) c :=
  onMk R F (Sb R F) (Equiv.refl _) (fun j => Fintype.linearCombination D.what₂.LL (R.bL F false j)) (xAt F R) c I

variable (R : RealDat D A Ks) (F : Face D A) (c : OnConst) (I : OnIn R)

theorem tieU_rfl : TieU (onObjOf R F c I) (fun v => uniSub (kP v.1) (D.R.r - 1)) := rfl

theorem tieLevelNum : TieLevelNum (onObjOf R F c I) (D.R.r - 1) D.R.f := by
  refine ⟨rfl, ?_⟩
  show (D.R.r : ℝ) = ((D.R.r - 1 : ℕ) : ℝ) + 1
  rw [← Nat.cast_add_one, r_pos]

theorem proj_range (j : Fin D.R.m) : LinearMap.range ((onObjOf R F c I).e j) = (onObjOf R F c I).V₀ j := rfl

theorem pageTies_rfl : OnPage.SecondRatioDefinition (onObjOf R F c I) ∧
    OnPage.TieBp (onObjOf R F c I) ∧ OnPage.TieNc (onObjOf R F c I) := ⟨rfl, rfl, rfl⟩

def TieUnit : Prop := (F.fc (R.toCx F).zs).Z.E1u = (onObjOf R F c I).E1u

structure OnLeaves (N : IndefNum A.fam.base) : Prop where
  mackey : LeafMackey (onObjOf R F c I)
  sup : LeafSup (onObjOf R F c I)
  proj : LeafProj (onObjOf R F c I)
  coord : TieCoord (onObjOf R F c I)
  span : LeafSpan (onObjOf R F c I)
  lemmaS : LeafLemmaS (onObjOf R F c I)
  t0 : LatticeIndexBoundAtPairs (onObjOf R F c I)
  data : LeafData (onObjOf R F c I)
  rankJ : LeafRankJ (onObjOf R F c I)
  identity : LeafIdentity (onObjOf R F c I)
  tw2 : LeafTW2 (onObjOf R F c I)
  tw1 : LeafTW1 (onObjOf R F c I)
  shareI : LeafShareI (onObjOf R F c I)
  indexU : LeafIndexU (onObjOf R F c I)
  badShare : LeafBadShare (onObjOf R F c I)
  unip : LeafUnip (onObjOf R F c I)
  depthGood : LeafDepthGood N (onObjOf R F c I)
  depthRam : LeafDepthRam N (onObjOf R F c I)
  depth2 : LeafDepth2 N (onObjOf R F c I)
  depthLevel : LeafDepthLevel N (onObjOf R F c I)
  page : LeafPage (onObjOf R F c I)
  sizes : LeafSizes (onObjOf R F c I)
  X : LeafX (onObjOf R F c I)
  bad : LeafBad (onObjOf R F c I)
  jSum : LeafJSum (onObjOf R F c I)
  jExp : LeafJExp N (onObjOf R F c I)

theorem onto_of_leaves (C CH : ℝ) (hRk : RankRows (Sb R F)) (hL : OnLeaves R F c I (R.num F C CH)) (hCE : c.CE ≤ C)
    (hE : TieUnit R F c I) (tErr : TieErr (onObjOf R F c I)) : R.LOnto F C CH :=
  on_of_leaves (R.num F C CH) (onObjOf R F c I) C hRk hL.mackey hL.sup hL.proj hL.coord hL.span hL.lemmaS hL.t0 hL.data
    hL.rankJ hL.identity hL.tw2 hL.tw1 hL.shareI hL.indexU hL.badShare hL.unip hL.depthGood hL.depthRam hL.depth2
    hL.depthLevel hL.page hL.sizes hL.X hL.bad hL.jSum hL.jExp hCE (fun _ => by show C * _ = C * _; rw [hE]) tErr

end Formalism.IndefR.Obj
