import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains

noncomputable section

namespace Formalism.MainNotions.HerrCohomologyExtensions

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

section Ties

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

def UnitGen (e : W.DD W.one) (e₀ : W.one.V) : Prop :=
  e ∈ W.N W.one ∧ W.N W.one = Submodule.span (LetA O n) {e} ∧
    Submodule.span W.EE {e} = (⊤ : Submodule W.EE (W.DD W.one)) ∧
    W.φD W.one e = e ∧ (∀ g, W.γD W.one g e = e) ∧ W.one.L.T = Submodule.span O {e₀}

def clsK (T : LocLat G Qp LL O) (κ : G → T.V) (hκ : κ ∈ latticeCocycles T.L) : LatticeCohomology T.L :=
  Submodule.Quotient.mk (⟨κ, hκ⟩ : ↥(latticeCocycles T.L))

def IsCocOf {T Tp : LocLat G Qp LL O} (ι : LatHom T.L Tp.L) (π : LatHom Tp.L W.one.L)
    (e₀ : W.one.V) (κ : G → T.V) : Prop :=
  IsSESLat (Qp := Qp) ι π ∧ ∃ t ∈ Tp.L.T, π.f t = e₀ ∧ ∀ g, ι.f (κ g) = Tp.ρ g t - t

def ExtKs (e : W.DD W.one) (e₀ : W.one.V) : Prop :=
  ∀ (T Tp : LocLat G Qp LL O) (ι : LatHom T.L Tp.L) (π : LatHom Tp.L W.one.L)
    (κ : G → T.V) (hκ : κ ∈ latticeCocycles T.L), IsCocOf W ι π e₀ κ →
    ∀ (x : W.DD Tp) (c : O), W.map π x = c • e →
    ∀ w : ↥(W.divisibleCocycles T), W.map ι (w : W.DD T × W.DD T).1 = W.φD Tp x - x →
      W.map ι (w : W.DD T × W.DD T).2 = W.γ Tp x - x →
      W.cl T w = c • Formalism.MainNotions.DeltaInvariantLattices.res W.GKs T (clsK T κ hκ)

def ExtK (e : W.DD W.one) (e₀ : W.one.V) : Prop :=
  W.s = 1 → PD.p ≠ 2 →
  ∀ (T Tp : LocLat G Qp LL O) (ι : LatHom T.L Tp.L) (π : LatHom Tp.L W.one.L)
    (κ : G → T.V) (hκ : κ ∈ latticeCocycles T.L), IsCocOf W ι π e₀ κ →
    ∀ (x : W.DD Tp) (c : O), W.map π x = c • e → (∀ δ ∈ W.DelF, W.γD Tp δ x = x) →
    ∀ w : ↥(W.wachCocyclesDelta T), W.map ι (w : W.DD T × W.DD T).1 = W.φD Tp x - x →
      W.map ι (w : W.DD T × W.DD T).2 = W.γD Tp W.gamK x - x →
      W.clK T w = c • clsK T κ hκ

def CrystallineExtensionImage (e : W.DD W.one) (e₀ : W.one.V) : Prop :=
  ∀ (T Tp : LocLat G Qp LL O) (ι : LatHom T.L Tp.L) (π : LatHom Tp.L W.one.L) (M h : ZMod n → ℕ)
    (κ : G → T.V) (hκ : κ ∈ latticeCocycles T.L), IsCocOf W ι π e₀ κ →
    IsCrys PD T.ρ → IsCrys PD Tp.ρ → Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T M h →
    ∀ c : O, (∃ x ∈ W.N Tp, W.map π x = c • e) →
      ∃ (y z : W.DD T) (hw : (y, z) ∈ W.divisibleCocycles T),
        y ∈ Formalism.MainNotions.DeltaInvariantLattices.invN W T (W.Q ^ Formalism.MainNotions.DeltaInvariantLattices.mx M) ∧ z ∈ Formalism.MainNotions.DeltaInvariantLattices.aN W T W.X ∧
        W.cl T ⟨(y, z), hw⟩ = c • Formalism.MainNotions.DeltaInvariantLattices.res W.GKs T (clsK T κ hκ)

def HerrExt : Prop :=
  ∃ (e : W.DD W.one) (e₀ : W.one.V), UnitGen W e e₀ ∧ ExtKs W e e₀ ∧ ExtK W e e₀

theorem invariant_cocycle_le_gamma_cocycle (h1 : W.s = 1) (h2 : PD.p ≠ 2) (T : LocLat G Qp LL O) : W.wachCocyclesDelta T ≤ W.divisibleCocycles T := by
  intro w hw
  have hg : W.gamK = W.gam := W.gamK_eq_one h1 h2
  unfold LocWach.wachCocyclesDelta herrZ1Δ at hw
  rw [hg] at hw
  exact hw.1

def ClKRes : Prop :=
  ∀ (h1 : W.s = 1) (h2 : PD.p ≠ 2) (T : LocLat G Qp LL O) (w : ↥(W.wachCocyclesDelta T)),
    Formalism.MainNotions.DeltaInvariantLattices.res W.GKs T (W.clK T w) = W.cl T ⟨(w : W.DD T × W.DD T), invariant_cocycle_le_gamma_cocycle W h1 h2 T w.2⟩

end Ties

def TheoremCConstantsRange (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (R : ℕ → Prop) (k₁ k₂ k₃ k₄ k₅ C : ℝ) : Prop :=
  Formalism.MainNotions.RamifiedCoefficientChains.TheoremCConstantsRange D HW F R k₁ k₂ k₃ k₄ k₅ C

def aux₃ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C : ℝ) : Prop := Formalism.MainNotions.RamifiedCoefficientChains.aux₃ D HW F C

def Conclusion2 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C : ℝ) : Prop := Formalism.MainNotions.RamifiedCoefficientChains.Conclusion2 D HW F C

def adm1 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop := Formalism.MainNotions.RamifiedCoefficientChains.adm1 D HW F Cm

def adm2 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.RamifiedCoefficientChains.adm2 D HW F

def adm3 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.RamifiedCoefficientChains.adm3 D HW F

def ArchimedeanSignatureMatching (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.RamifiedCoefficientChains.ArchimedeanSignatureMatching D HW F

def adm5 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.RamifiedCoefficientChains.adm5 D HW F

def adm6 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.RamifiedCoefficientChains.adm6 D HW F

def adm7 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C : ℝ) : Prop := Formalism.MainNotions.RamifiedCoefficientChains.adm7 D HW F C

def adm8 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.RamifiedCoefficientChains.adm8 D HW F

def adm9 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.RamifiedCoefficientChains.adm9 D HW F

def adm10 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (CA CB CK : ℝ) : Prop := Formalism.MainNotions.RamifiedCoefficientChains.adm10 D HW F CA CB CK

def adm11 (D : D7) : Prop := Formalism.MainNotions.RamifiedCoefficientChains.adm11 D

def adm12 (D : D7) : Prop := Formalism.MainNotions.RamifiedCoefficientChains.adm12 D

def adm13 (D : D7) : Prop := Formalism.MainNotions.RamifiedCoefficientChains.adm13 D

def adm14 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.RamifiedCoefficientChains.adm14 D HW F

def adm15 (D : D7) : Prop := Formalism.MainNotions.RamifiedCoefficientChains.adm15 D

def adm16 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    HerrExt ((HW l).W K s LL h)

def adm17 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    ClKRes ((HW l).W K s LL h)

def adm18 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    ((HW l).W K s LL h).ClNat ∧ Formalism.MainNotions.DeltaInvariantLattices.ClKNatG ((HW l).W K s LL h)

def admitted (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CR CA CB CK : ℝ) : Prop :=
  adm1 D HW F Cm ∧ adm2 D HW F ∧ adm3 D HW F ∧ ArchimedeanSignatureMatching D HW F ∧ adm5 D HW F ∧ adm6 D HW F ∧ adm7 D HW F CR ∧ adm8 D HW F ∧ adm9 D HW F ∧
    adm10 D HW F CA CB CK ∧ adm11 D ∧ adm12 D ∧ adm13 D ∧ adm14 D HW F ∧ adm15 D ∧ adm16 D HW F ∧ adm17 D HW F ∧
    adm18 D HW F

def Stmt (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (C CR CA CB CK : ℝ) : Prop := admitted D HW F Cm CR CA CB CK → aux₃ D HW F C

end Formalism.MainNotions.HerrCohomologyExtensions
