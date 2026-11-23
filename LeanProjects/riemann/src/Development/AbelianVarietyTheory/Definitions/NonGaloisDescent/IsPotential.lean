import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ElementDenominator
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIterateDerivative
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal

def IsEps {l : ℕ} [Fact l.Prime] (ε : OCb l) : Prop := ε.untilt = 1 ∧ ∃ δ : OCb l, δ ^ l = ε ∧ δ.untilt ≠ 1

def muOf {l : ℕ} [Fact l.Prime] (x : OCb l) : Ainf l := WittVector.teichmuller l x - 1

section General

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e)
  {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  {G : Type} [Group G] [TopologicalSpace G]

variable (l O) in

def toB : OA l O →ₐ[O] OB l O := (toOB l O).comp (toOCr l O)

variable {t ϖ} in

def IsCrisCmp {P : PhiMod O K l e a ι} {T : LocLat G ℚ_[l] K O} (I : Ident t ϖ P T)
    (jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T) : Prop :=
  ∀ (c : ι → OA l O) (z : TW (OA l O) T), I.j (inclL t ϖ P c) = TWincl (inclO l O) T z →
    jB (fun i => toB l O (c i)) = TWincl (toB l O) T z

def IsCrisVal (P : PhiMod O K l e a ι) {T : LocLat G ℚ_[l] K O}
    (jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T) (w : ι → OW l O) (b : TW (OB l O) T) : Prop :=
  ∃ (m : OA l O) (c : ι → OA l O), IsUnit (toB l O m) ∧ inclO l O m • w = inclL t ϖ P c ∧
    toB l O m • b = jB fun i => toB l O (c i)

abbrev actB (s : G →* GQ l) (T : LocLat G ℚ_[l] K O) (g : G) : TW (OB l O) T →ₗ[O] TW (OB l O) T :=
  TWact (galOB O (s g)) T g

def IsCobOf (s : G →* GQ l) (T : LocLat G ℚ_[l] K O) (b : TW (OB l O) T) (c : G → T.V) : Prop :=
  ∀ (g : G) (n : ℕ) (x : ↥T.L.T), (x : T.V) = (l : K) ^ n • c g →
    (1 : OB l O) ⊗ₜ[O] x = (l : O) ^ n • (actB s T g b - b)

variable [TameDescentExponentData K l e a]

variable (K) in

def Covers (h : GQ l) (γ : TameGal K l e a) : Prop :=
  ∀ f f' : ZMod a → A O K, (∀ τ, (f' τ : K⟦X⟧) = ringAct γ (fun σ => (f σ : K⟦X⟧)) τ) →
    galOA O h (ϖ.iTot t K f) = ϖ.iTot t K f'

variable {t ϖ} in

def IsGalDesc (s : G →* GQ l) {P : PhiMod O K l e a ι} {T : LocLat G ℚ_[l] K O} (I : Ident t ϖ P T)
    (Δ : Descent P) : Prop :=
  ∀ (g : G) (γ : TameGal K l e a), Covers K t ϖ (s g) γ → ∀ v v' : ME P, v'.1 = Δ.act γ v.1 →
    I.act (s g) g (toW t ϖ P v) = toW t ϖ P v'

def IsHoriz (s : G →* GQ l) (P : PhiMod O K l e a ι) {T : LocLat G ℚ_[l] K O}
    (jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T) : Prop :=
  ∀ g : G, s g ∈ GK (ϖ.field a) → ∀ (d : P.D) (h : P.xi d ∈ P.MMl),
    actB s T g (jB (toBcris t ϖ P ⟨P.xi d, h⟩)) = jB (toBcris t ϖ P ⟨P.xi d, h⟩)

structure GalDat (s : G →* GQ l) {η H : ℕ} (D : BKDat O K l e a ι η H) (T : LocLat G ℚ_[l] K O) where

  I : Ident t ϖ D.toPhiMod T

  jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T
  cmp : IsCrisCmp I jB
  desc : IsGalDesc s I D.desc
  stable : ∀ g : G, ∀ v ∈ LA t ϖ D.toPhiMod, I.act (s g) g v ∈ LA t ϖ D.toPhiMod
  horiz : IsHoriz t ϖ s D.toPhiMod jB

namespace GalDat

variable {t ϖ} {s : G →* GQ l} {η H : ℕ} {D : BKDat O K l e a ι η H} {T : LocLat G ℚ_[l] K O}
  (R : GalDat t ϖ s D T)

def IsPotential (y : Vec K a ι) (b : TW (OB l O) T) : Prop :=
  ∃ (hy : y ∈ ME D.toPhiMod) (m₀ : ι → OW l O) (σ : D.MMl) (b₀ : TW (OB l O) T),
    phiW t ϖ D.toPhiMod m₀ - m₀ = toW t ϖ D.toPhiMod ⟨y, hy⟩ ∧ σ.1 ∈ D.desc.inv ∧ D.conn σ.1 = D.zeta y ∧
    IsCrisVal t ϖ D.toPhiMod R.jB (phiW t ϖ D.toPhiMod m₀) b₀ ∧ b = R.jB (toBcris t ϖ D.toPhiMod σ) - b₀

def ClassOf (y : Vec K a ι) (c : G → T.V) : Prop := ∃ b, R.IsPotential y b ∧ IsCobOf s T b c

end GalDat

end General

section Ql

variable {l : ℕ} [hl : Fact l.Prime]

variable (l) in

abbrev Gl : Type := ↥(GK (Formalism.MainNotions.ElementDenominator.qlExt l))

variable (l) in

abbrev sQ : Gl l →* GQ l := (GK (Formalism.MainNotions.ElementDenominator.qlExt l)).subtype

abbrev QLat (LL : FinExt l) : Type 1 := LocLat (Gl l) ℚ_[l] ↥LL.1 ↥(OL LL)

def inclG (F : FinExt l) : ↥(GK F) →* Gl l :=
  Subgroup.inclusion (GK_le (K := Formalism.MainNotions.ElementDenominator.qlExt l) (K' := F) bot_le)

def resF {LL : FinExt l} (T : QLat LL) (F : FinExt l) : LocLat ↥(GK F) ℚ_[l] ↥LL.1 ↥(OL LL) :=
  resLoc T (inclG F) (continuous_subtype_val.subtype_mk _)

variable {e : ℕ} (a : ℕ) [NeZero a] (ϖ : PiSys l e) (Pl : LocPrime l) {LL : FinExt l}

def TameType (T : QLat LL) (Sig : Finset (ZMod e)) : Prop :=
  ∀ g ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l), ∀ w : ↥LL.1, (w : Om l) * ϖ.seq 0 = (g : GQ l) (ϖ.seq 0) →
    ∀ x ∈ Dcris (Pl.PD (ϖ.field a)) (resF T (ϖ.field a)).ρ,
      Polynomial.aeval (actVB (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g : Module.End ↥LL.1 (T.V ⊗[ℚ_[l]] Pl.R.B))
        (∏ c ∈ Sig, (Polynomial.X - Polynomial.C (w ^ c.val))) x = 0

structure IsGood (T : QLat LL) (Sig : Finset (ZMod e)) (U : Finset ℤ) : Prop where
  crys : IsCrys (Pl.PD (ϖ.field a)) (resF T (ϖ.field a)).ρ
  type : TameType a ϖ Pl T Sig
  jumps : ∀ τ, JumpsInV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ τ (U : Set ℤ)

variable [NeZero e] [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a]

structure Pack (η H : ℕ) (T : QLat LL) where

  n : ℕ

  D : BKDat ↥(OL LL) ↥LL.1 l e a (Fin n) η H

  R : GalDat (thetaW a LL) ϖ (sQ l) D T
  isBK : IsBK (T := resF T (ϖ.field a)) (R.I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _))

end Ql

end GlobalTheory.BKGal
