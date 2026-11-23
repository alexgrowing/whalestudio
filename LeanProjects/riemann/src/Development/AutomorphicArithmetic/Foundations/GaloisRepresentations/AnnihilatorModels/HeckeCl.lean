import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.LocFacts

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV CrystallineSemistableComparison UpperTheory.Ru.crystallineComparison UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen)

namespace UpperTheory.Gal.crystallineComparison.Br

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {L : Type} [Field L] {H : HTower K} {θ : H.Γ → L}

def mdl (C : Cover H θ (OK l K)) : Model l K := ⟨C.Y, C.p⟩

def inTot (M : Model l K) (j : ℕ) : M.V j →ₗ[ℚ_[l]] Htot l M.spc :=
  DirectSum.lof ℚ_[l] ℤ (fun n : ℤ => HQ l M.spc n 0) (j : ℤ)

def piTot (C : Cover H θ (OK l K)) : Htot l (mdl C).spc →ₗ[ℚ_[l]] Htot l (sch.obj (H.geomZ (PadicAlgCl l))) :=
  (etG l K (PadicAlgCl l)).pull (piK C) (piK_snd C)

def GenFEt : Prop := ∀ (l : ℕ) (O k : Type) [CommRing O] [Field k] [Algebra O k], (l : k) ≠ 0 → ∀ {Y : Scheme.{0}} (p : Y ⟶ sp O)
  (T : Corr l Y), FEt (bcMap (gen O k) T.p (rfl : T.p ≫ p = _)) T.d

def TrTot : Prop := ∀ (l : ℕ) [Fact l.Prime] {B Z Y : Scheme.{0}} (p : Z ⟶ B) (q : Y ⟶ B) (s : Y ⟶ Z)
  (tr : ∀ n : ℤ, HQ l (sch.obj Y) n 0 →ₗ[ℚ_[l]] HQ l (sch.obj Z) n 0), (∀ n, (etn l B n 0).IsTr p q s (tr n)) →
  (et l B).IsTr p q s (DirectSum.lmap tr)

def TrBc : Prop := ∀ {B B' : Scheme.{0}} {R : Type} [Field R] (T : Th.{1} B R) (g : B ⟶ B') {Z Y : Scheme.{0}} (p : Z ⟶ B') (q : Y ⟶ B')
  (s : Y ⟶ Z) [IsFinite s] [Etale s] (hs : s ≫ p = q) (tr), T.IsTr (pullback.snd p g) (pullback.snd q g) (bcMap g s hs) tr → (T.bc g).IsTr p q s tr

def TrPush : Prop := ∀ (l : ℕ) [Fact l.Prime] {B Z Y : Scheme.{0}} (p : Z ⟶ B) (q : Y ⟶ B) (s : Y ⟶ Z), s ≫ p = q → ∀ (n : ℤ)
  (tr : HQ l (sch.obj Y) n 0 →ₗ[ℚ_[l]] HQ l (sch.obj Z) n 0), (etn l B n 0).IsTr p q s tr → LateralTheory.EtaleTrace.IsPush l s n tr

def HeckeCl : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (L : Type) [Field L] (H : HTower K)
  (θ : H.Γ → L) (C : Cover H θ (OK l K)) (T : Corr l C.Y) (hr : T.r ≫ C.p = T.p ≫ C.p) (γ : H.Γ) (m d : ℕ), FEt (H.s γ) d →
  C.Lies γ T.p T.r m → ∃ A : ∀ j : ℕ, (mdl C).V j →ₗ[ℚ_[l]] (mdl C).V j, ∀ j, IsHk (mdl C) T hr j (A j) ∧
    ∀ v, hop l H (PadicAlgCl l) γ (piTot C (inTot (mdl C) j v)) = (m : ℚ_[l]) • piTot C (inTot (mdl C) j (A j v))

end UpperTheory.Gal.crystallineComparison.Br
