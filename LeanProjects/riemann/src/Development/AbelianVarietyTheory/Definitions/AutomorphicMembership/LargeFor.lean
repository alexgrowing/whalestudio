import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PeriodComparisonProvisional
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GeometrySectionsEqRiemannRoch
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocStOfLoc
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GeoTiedPGraft
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VarietyWithModels
import Formalism.LocalToGlobal.LatticeGeometry.GeoTiedP

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.TrueGeo GlobalTheory.LocM GlobalTheory.ShFam.Pad

namespace GlobalTheory.ShFam

abbrev JC (D : D7) : Type := ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)

def JC.Pinned {D : D7} (jC : JC D) : Prop := ∀ (p : ℕ) [Fact p.Prime] (la : PlL D p), JcPin D p la (jC p la)

abbrev KitT {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} (s : FinalTheorems S κ) (L : CmList A) (jC : JC D) : Type 1 :=
  Kit s L (cxSt D.what₂.LL) jC ngTrue

abbrev KitClass (D : D7) : Type 1 :=
  ∀ (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (L : CmList A) (jC : JC D),
    KitT s L jC → (s.Comp → D.what₂.Tau → ℝ) → Prop

variable {D : D7}

def KitClass.Ex (Q : KitClass D) : Prop :=
  ∀ A N j S κ s L jC, jC.Pinned → ∃ k d, Q A N j S κ s L jC k d

def KitClass.Loc (Q : KitClass D) : Prop :=
  ∀ A N j S κ s L jC k d, jC.Pinned → Q A N j S κ s L jC k d →
    ∃ (F : StFam S κ) (cts : Ats S κ), cts.Over jC ∧ LocSt.ofPkg k.pad = locStOf F cts

structure FamOver (Q : KitClass D) (T : Top D) (h : LawsP T) (c : ℕ) : Type 1 where
  F : SrcFam (ambOf T.Q h.pins.1)
  t : ParTie T.Q h.pins.1 F
  exp : F.κs.l.A = 15 ^ c
  L : CmList (ambOf T.Q h.pins.1)
  jC : JC D
  pin : jC.Pinned
  k : Kits F L (cxSt D.what₂.LL) jC ngTrue
  d : ∀ N j hN hj κ, (F.src N j hN hj κ).Comp → D.what₂.Tau → ℝ
  mem : ∀ N j hN hj κ, Q _ N j _ κ (F.src N j hN hj κ) L jC (k N j hN hj κ) (d N j hN hj κ)
  hg : F.κg.primes = Finset.univ.image D.host.g
  P : FormsOver (cutSt _) (resSt _) k
  forms : FormsAre h t (cutSt _) (resSt _) k P
  prov : ∃ (I : Type) (dat : I → Dat D (Lv (ambOf T.Q h.pins.1))) (hI : ∀ i, (dat i).Indef) (iW : ℕ → I),
    (∀ w : Dat D (Lv (ambOf T.Q h.pins.1)), w.Indef → ∃ i, (dat i).N = w.N ∧ (dat i).j = w.j ∧ (dat i).κ = w.κ) ∧
    (∀ j, 1 ≤ j → j < D.R.m → dat (iW j) = datW D F.κg j) ∧
    T.G.P = indefiniteDataFamily (shimOf (cutSt _) (resSt _) k) I dat hI ∧ ∀ j, 1 ≤ j → j < D.R.m → HEq (T.G.dat j) (iW j)

namespace FamOver

variable {Q : KitClass D} {T : Top D} {h : LawsP T} {c : ℕ} (Φ : FamOver Q T h c)

def fam : ShimFam D (geoTrue D.what₂.LL) (Lv (ambOf T.Q h.pins.1)) := famOf (cutSt _) (resSt _) Φ.k Φ.hg Φ.P

def dH (j : ℕ) : (Φ.fam.Uw j).Comp → D.what₂.Tau → ℝ :=
  Φ.d _ _ (datW D Φ.F.κg j).two_le (datW D Φ.F.κg j).j_le (datW D Φ.F.κg j).κ

theorem locTie : LocTie h Φ.k := by
  obtain ⟨I, dat, hI, iW, -, h1, h2, h3⟩ := Φ.prov
  exact LocTie.localTie_of_provisional (cutSt _) (resSt _) h1 h2 h3

def Reads (X₀ : DivX D)
    (iM : ∀ j (a : (Φ.fam.Uw j).Comp), (X₀.MjH j).V →ₗ[D.what₂.LL] (geoTrue D.what₂.LL).Fn ((Φ.fam.Uw j).alg.Yv a)) : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → (∀ x, (∀ a, iM j a x = 0) → x = 0) ∧
    ∃ (w : WeightFamilies.Wt D j) (s : Submodule Φ.P.KO (Φ.P.Cusp j w)) (φ : s →ₛₗ[Φ.P.sig0] D.what₂.Mj j),
      w.n = D.R.nV ∧ Formalism.L2.Geo.wtOf w = DV.kapW D j ∧ Submodule.span ℂ (Set.range φ) = ⊤ ∧
      (D.what₂.MjLat j).carrier ⊆ Set.range φ ∧
      (∀ x : s, (x : Φ.P.Cusp j w) ∈ Φ.P.Mlat j w ↔ φ x ∈ (D.what₂.MjLat j).carrier) ∧
      (∃ vol : ℝ, ∀ x : s, ‖φ x‖ = Real.sqrt (vol * dimKap D j) * Φ.P.l2NormAlt j w Φ.P.sig0 x) ∧
      ∀ (f : s) x, X₀.jM j x = φ f → ∀ a, iM j a x = Φ.P.cmp j w a f

end FamOver

def IsGeoOf (Q : KitClass D) (J : Core D) (c : ℕ) (X : DivX D) : Prop :=
  ∃ (T : Top D) (h : LawsP T) (Φ : FamOver Q T h c) (X₀ : DivX D) (iM : _) (hiM : _), T.toCore = J ∧
    X = GlobalTheory.VarietyModelRecord.record X₀ Φ.fam iM hiM Φ.dH ∧ Φ.Reads X₀ iM ∧ X.vdd = fun p _ => vDiff D.host.E p

def SameSurf (X Y : DivX D) : Prop :=
  X.Surf = Y.Surf ∧ HEq X.surfCh2 Y.surfCh2 ∧ HEq X.surfDegOm Y.surfDegOm ∧ X.SurfFp = Y.SurfFp ∧ HEq X.surfFpCh2 Y.surfFpCh2

def LargeFor (Q : Par D) (h : Q.PinHost) (c : ℕ) : Prop :=
  IsLargeFor (ambOf Q h) (D.host.g 0 * D.host.g 1) ∧ IsLargeFor (ambOf Q h) (Nat.lcm (D.host.g 0 * D.host.g 1) (15 ^ c))

end GlobalTheory.ShFam
