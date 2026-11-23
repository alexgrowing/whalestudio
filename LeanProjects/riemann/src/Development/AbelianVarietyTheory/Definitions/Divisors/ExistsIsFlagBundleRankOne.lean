import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ArInt GlobalTheory.VB

namespace GlobalTheory.CovTest

def IsFlagBundle {B Y : Scheme.{0}} (π : Y ⟶ B) {ι : Type} (E : ι → B.Modules) (n : ι → ℕ)
    (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (n a)) : Prop :=
  ∀ (T : Scheme.{0}) (g : T ⟶ B) (fl' : ∀ a, Vert.Flag ((Scheme.Modules.pullback g).obj (E a)) (n a)),
    ∃! g' : T ⟶ Y, ∃ w : g' ≫ π = g, ∀ a i, ∃ e : (Scheme.Modules.pullback g').obj ((fl a).F i) ≅ (fl' a).F i,
      e.hom ≫ (fl' a).ι i = (Scheme.Modules.pullback g').map ((fl a).ι i) ≫
        (Scheme.Modules.pullbackComp g' π).hom.app (E a) ≫ (Scheme.Modules.pullbackCongr w).hom.app (E a)

theorem isFlagBundle_empty (B : Scheme.{0}) (E : Empty → B.Modules) (n : Empty → ℕ)
    (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback (𝟙 B)).obj (E a)) (n a)) : IsFlagBundle (𝟙 B) E n fl :=
  fun _ g _ => ⟨g, ⟨Category.comp_id g, fun a => a.elim⟩, fun _ ⟨w, _⟩ => (Category.comp_id _).symm.trans w⟩

theorem isFlagBundle_rank_one (B : Scheme.{0}) {ι : Type} (E : ι → B.Modules)
    (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback (𝟙 B)).obj (E a)) 1) : IsFlagBundle (𝟙 B) E (fun _ => 1) fl := by
  intro T g fl'
  refine ⟨g, ⟨Category.comp_id g, fun a i => ?_⟩, fun _ ⟨w, _⟩ => (Category.comp_id _).symm.trans w⟩
  induction i using Fin.lastCases with
  | last =>
    have := (fl a).isIso_last
    have := (fl' a).isIso_last
    exact ⟨asIso ((Scheme.Modules.pullback g).map ((fl a).ι (Fin.last 1)) ≫
        (Scheme.Modules.pullbackComp g (𝟙 B)).hom.app (E a) ≫
          (Scheme.Modules.pullbackCongr (Category.comp_id g)).hom.app (E a)) ≪≫ (asIso ((fl' a).ι (Fin.last 1))).symm,
      by simp⟩
  | cast i =>
    obtain rfl : i = 0 := Subsingleton.elim _ _
    have z : Limits.IsZero ((Scheme.Modules.pullback g).obj ((fl a).F (0 : Fin 1).castSucc)) :=
      isVB_zero_iff.1 (((fl a).isVB _).pullback g)
    exact ⟨z.iso (isVB_zero_iff.1 ((fl' a).isVB _)), z.eq_of_src _ _⟩

theorem exists_isFlagBundle_rank_one (B : Scheme.{0}) {ι : Type} (E : ι → B.Modules) (hE : ∀ a, IsVB (E a) 1) :
    ∃ fl, IsFlagBundle (𝟙 B) E (fun _ => 1) fl :=
  ⟨fun a => .ofRankOne ((hE a).pullback _), isFlagBundle_rank_one B E _⟩

def Homog (G : ℕ → ℤ → ℤ → MvPolynomial (Fin 3) ℝ) : Prop := ∀ D a b, (G D a b).IsHomogeneous D

def Swap2 (G : ℕ → ℤ → ℤ → MvPolynomial (Fin 3) ℝ) : Prop :=
  ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ),
    IsArithVar q d → IsArithVar p (d + 1) → ∀ (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2), IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) →
    ∀ (A : HermLB q) (Φ Ψ : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] ℝ),
      IsArFun ![VMetric.grLB fl 0 (H.pull π w), VMetric.grLB fl 1 (H.pull π w), A.pull π w] (d + 1) Φ →
      IsGeoFun ![VMetric.grLB fl 0 (H.pull π w), VMetric.grLB fl 1 (H.pull π w), A.pull π w] (d + 1) Ψ →
      ∀ a b : ℤ, Φ (lin ![(a : ℝ), b, 1] ^ (d + 2)) + Φ (lin ![(b : ℝ), a, 1] ^ (d + 2)) = Ψ (G (d + 1) a b)

open Classical in

def swapPol {κ : Type} [Fintype κ] (G : ℕ → ℤ → ℤ → MvPolynomial (Fin 3) ℝ) (D : ℕ) (x y : κ) (n : κ → ℤ) :
    MvPolynomial κ ℝ :=
  aeval ![X x, X y, lin fun z => if z = x ∨ z = y then 0 else (n z : ℝ)] (G D (n x) (n y))

open Classical in

def SwapFl (G : ℕ → ℤ → ℤ → MvPolynomial (Fin 3) ℝ) : Prop :=
  ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d D : ℕ),
    IsArithVar q d → IsArithVar p D → ∀ (π : Y ⟶ B) (w : π ≫ q = p) (ι : Type) [Fintype ι] (E : ι → B.Modules) (r : ι → ℕ)
    (h : ∀ a, VMetric q (E a) (r a)) (H : ∀ a, (h a).IsCInf)
    (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), IsFlagBundle π E r fl →
    ∀ (Φ Ψ : MvPolynomial (Σ a, Fin (r a)) ℝ →ₗ[ℝ] ℝ),
      IsArFun (fun z : Σ a, Fin (r a) => VMetric.grLB (fl z.1) z.2 ((H z.1).pull π w)) D Φ →
      IsGeoFun (fun z : Σ a, Fin (r a) => VMetric.grLB (fl z.1) z.2 ((H z.1).pull π w)) D Ψ →
      ∀ (a : ι) (i i' : Fin (r a)), (i' : ℕ) = i + 1 → ∀ n : (Σ a, Fin (r a)) → ℤ,
        Φ (lin (fun z => (n z : ℝ)) ^ (D + 1)) +
            Φ (lin (fun z => (n (Equiv.swap (⟨a, i⟩ : Σ a, Fin (r a)) ⟨a, i'⟩ z) : ℝ)) ^ (D + 1)) =
          Ψ (swapPol G D ⟨a, i⟩ ⟨a, i'⟩ n)

def Ch2Const (r : ℝ) : Prop :=
  ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [IsIntegral X], IsArithVar p 1 →
    ∀ P : PPAS X, P.IsCh2Omega p (r / 2 * (P.degOmega p : ℝ))

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.ShFam.Pad

section One

variable {D : D7} (Y : ShimX D.what₂.Tau)

open Classical in

def SwapEq (G : ℕ → ℤ → ℤ → MvPolynomial (Fin 3) ℝ) (Φ Ψ : Pol D.what₂.Tau Y.N → ℝ) : Prop :=
  ∀ (τ : D.what₂.Tau) (a b : Fin Y.N), (b : ℕ) = a + 1 → (b : ℕ) ≠ Y.j → ∀ n : D.what₂.Tau × Fin Y.N → ℤ,
    Φ (lin (fun z => (n z : ℝ)) ^ (dimFl D.what₂.Tau Y.N + 1)) +
        Φ (lin (fun z => (n (swapAt τ a b z) : ℝ)) ^ (dimFl D.what₂.Tau Y.N + 1)) =
      Ψ (swapPol G (dimFl D.what₂.Tau Y.N) (τ, a) (τ, b) n)

def PrimeLocalCondition : Prop := ∀ (Sx : Finset ℕ) (R : ℝ), 2 ≤ R → ∀ p : ℕ, p.Prime →
  ∀ Q : MvPolynomial (Rt D.what₂.Tau Y.N) ℝ, Q.IsHomogeneous (dimFl D.what₂.Tau Y.N - 1) →
    Y.arMix Sx R p ((X (Sum.inr (false, 2)) - X (Sum.inr (true, 2))) * tagDR D.what₂.Tau _ Q) =
      -(Real.log p * ((p : ℝ) / ((p : ℝ) ^ 2 - 1)) * Y.chern (chLieA D _ Y.j 1 * Q))

def PrimeLocalSplitCondition : Prop := ∀ (Sx : Finset ℕ) (R : ℝ), 2 ≤ R → ∀ p : ℕ, p.Prime →
  ∀ Q : MvPolynomial (Rt D.what₂.Tau Y.N) ℝ,
    Y.arMix Sx R p (X (Sum.inr (true, 2)) * (tagDR D.what₂.Tau _ Q - tagHT D.what₂.Tau _ Q)) = 0

def sieg (T : Finset ℕ) (R : ℝ) : ℝ :=
  Y.arMix T R 1 (X (Sum.inr (false, 2)) * tagDR D.what₂.Tau _ (curveCl D.what₂.Tau Y.N Y.j))

def SiegRead : Prop := ∀ (T : Finset ℕ) (R : ℝ) (p : ℕ), p.Prime → p ∉ T → (∀ q ∈ T, q.Prime) →
  sieg Y T R = Y.arMix T R p (X (Sum.inr (false, 2)) * tagDR D.what₂.Tau _ (curveCl D.what₂.Tau Y.N Y.j)) ∧
  sieg Y (insert p T) R = Y.arMix T R p (X (Sum.inr (true, 2)) * tagHT D.what₂.Tau _ (curveCl D.what₂.Tau Y.N Y.j))

def LatAt : Prop := ∀ B : ℝ, 2 ≤ B → ∀ R : ℝ, 2 ≤ R → Y.arDeg (setB Y B) R (testF Y) = sieg Y (setB Y B) R

def bcFl : ℝ := (1 / (Y.j : ℝ) - 1 / ((Y.N : ℝ) - Y.j)) * testI Y

theorem bcFl_eq : bcFl Y =
    -(((Y.j : ℝ) - 1) / Y.j) * testI Y + -(((Y.N : ℝ) - Y.j - 1) / ((Y.N : ℝ) - Y.j)) * -testI Y := by
  have h₁ : (Y.j : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.one_le_iff_ne_zero.1 Y.j_pos)
  have h₂ : (Y.N : ℝ) - Y.j ≠ 0 := (sub_pos.2 (Nat.cast_lt.2 Y.j_lt)).ne'
  rw [bcFl]
  field_simp
  ring

theorem bcFl_of_eq_two_mul (h : Y.N = 2 * Y.j) : bcFl Y = 0 := by
  rw [bcFl, show (Y.N : ℝ) - Y.j = Y.j by rw [h]; push_cast; ring, sub_self, zero_mul]

example (h : Y.N = 3) (h' : Y.j = 1) : bcFl Y = testI Y / 2 := by
  rw [bcFl, show (Y.N : ℝ) = 3 by rw [h]; norm_num, show (Y.j : ℝ) = 1 by rw [h']; norm_num]
  ring

def HhTest (hh : Fn Y) : Prop := hh (testF Y) = bcFl Y - testI Y

def DRAt (r : ℝ) : Prop := Tendsto (sieg Y ∅) atTop (𝓝 (Y.vol * bcFl Y - 2 * r * Y.vol * testI Y))

theorem HhTest.vol_mul {hh : Fn Y} (h : HhTest Y hh) (r s : ℝ) :
    Y.vol * bcFl Y - 2 * r * Y.vol * testI Y + s * (2 * Y.vol * testI Y) =
      Y.vol * (hh (testF Y) - 2 * testI Y * (r - 1 / 2 - s)) := by
  rw [h]
  ring

end One

def rkB (ι : Type) (N j : ℕ) (a : ι × Bool) : ℕ := cond a.2 j (N - j)

structure BunModel {D : D7} (O : Setup D) (P : Finset ℕ) (R : ℝ) (c : O.s.Comp) : Type 1 where

  V : Cover (O.var c)

  B : Scheme.{0}
  [int : IsIntegral B]

  q : B ⟶ Sp (𝓞 D.what₂.LL)
  ar : IsArithVar q (dimGr D.what₂.Tau O.N O.j)

  π : V.X ⟶ B
  w : π ≫ q = V.p

  E : D.what₂.Tau × Bool → B.Modules

  h : ∀ a, VMetric q (E a) (rkB D.what₂.Tau O.N O.j a)
  H : ∀ a, (h a).IsCInf

  fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (rkB D.what₂.Tau O.N O.j a)
  univ : IsFlagBundle π E (rkB D.what₂.Tau O.N O.j) fl
  ind : ∀ (a : D.what₂.Tau × Bool) (i : Fin (rkB D.what₂.Tau O.N O.j a)),
    V.Induces (adlOf (O.Φ.C c) (O.met.hm c)
      (rootSym O.S.Dw (ArIn.ind P) (some R) (DV.tauEmb D a.1) (cond a.2 0 O.j + i))) (VMetric.grLB (fl a) i ((H a).pull π w)) 1

def BunSt : Prop := ∀ (D : D7) (O : Setup D), O.Core → ∀ B : ℝ, 2 ≤ B → ∀ R : ℝ, 2 ≤ R → ∀ c,
  Nonempty (BunModel O (setB O.Y B) R c)

end GlobalTheory.CovTest

end
