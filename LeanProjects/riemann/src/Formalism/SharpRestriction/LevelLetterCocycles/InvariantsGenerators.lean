import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ClassMapInjectiveBijectiveNorms
import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
import Formalism.SharpRestriction.LevelLetterCocycles.ExtensionClauses

noncomputable section

namespace Formalism.MainNotions.InvariantsGenerators

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.tableLineDegreeTwo

section Core

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def H0FixedPoints (W : LocWach PD LL O v n) : Prop :=
  ∀ T : LocLat G Qp LL O, Nonempty (↥(invariantLattice T) ≃ₗ[O] ↥(fixDD W T))

def FontCore (W : LocWach PD LL O v n) : Prop :=
  (∀ (T T' : LocLat G Qp LL O) (f : W.DD T →ₗ[W.EE] W.DD T'),
    (∀ x, f (W.φD T x) = W.φD T' (f x)) → (∀ g x, f (W.γD T g x) = W.γD T' g (f x)) →
      ∃! F : LatHom T.L T'.L, ∀ x, W.map F x = f x) ∧
  (∀ (T₀ T₁ T₂ : LocLat G Qp LL O) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L), IsSESLat (Qp := Qp) (O := O) ι π →
    Function.Injective (W.map ι) ∧ Function.Surjective (W.map π) ∧
      ∀ x, W.map π x = 0 ↔ ∃ y, W.map ι y = x) ∧
  (∃ ψ : W.EE →ₗ[O] W.EE, (∀ a x, ψ (W.φE a * x) = a * ψ x) ∧
    (∀ g x, ψ (W.γE g x) = W.γE g (ψ x)) ∧
    (∀ j < PD.p, ∀ a, ψ (algebraMap (LetA O n) W.EE (1 + letπ) ^ j * W.φE a) = if j = 0 then a else 0) ∧
    ∀ x, ∃ c : Fin PD.p → W.EE, x = ∑ j : Fin PD.p, algebraMap (LetA O n) W.EE (1 + letπ) ^ (j : ℕ) * W.φE (c j)) ∧
  ∀ T : LocLat G Qp LL O, ∃ ψ : W.DD T →ₗ[O] W.DD T, (∀ x, ψ (W.φD T x) = x) ∧
    (∀ (a : W.EE) x, ψ (W.φE a • x) = a • ψ x) ∧ ∀ g x, ψ (W.γD T g x) = W.γD T g (ψ x)

theorem herrLat_iff (W : LocWach PD LL O v n) : HerrLat W ↔
    (∀ T : LocLat G Qp LL O, Function.Surjective (W.clK T) ∧
      ∀ p, W.clK T p = 0 ↔ ∃ m : W.DD T, (∀ δ ∈ W.DelF, W.γD T δ m = m) ∧
        (p : W.DD T × W.DD T) = (W.φD T m - m, W.γD T W.gamK m - m)) ∧
    W.ClKNat ∧ H0FixedPoints W ∧ FontCore W := Iff.rfl

end Core

def H0InvariantsUnramified (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : CaseA K LL), H0FixedPoints ((HW l).W K 1 LL hA.2.2)

def FieldOfNormsSequence (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.HerrComplexNaturality.FN D HW F

def H0InvariantsTheorem (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := FieldOfNormsSequence D HW F → H0InvariantsUnramified D HW F

def LitFont (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : CaseA K LL), FontCore ((HW l).W K 1 LL hA.2.2)

def HerrLatticeDescription (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.tableLineDegreeTwo.adm16 D HW F

def HerrLatticeHypotheses (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.LocalSituation.ClassMapInjectiveBijectiveNorms D HW F ∧ H0InvariantsUnramified D HW F ∧ LitFont D HW F

def HerrLatticeTheorem (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := HerrLatticeHypotheses D HW F → HerrLatticeDescription D HW F

theorem herr_lattice_of_fon (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : HerrLatticeTheorem D HW F := by
  rintro ⟨h, h0, hF⟩ l _ K LL hA
  have h1 := (h l K 1 LL hA.2.2).1 (fun h2 => absurd (((D.loc l).PD_p K).symm.trans h2) hA.2.1)
  refine (herrLat_iff _).2 ⟨fun T => ⟨(h1 T).1, (h1 T).2.1⟩, ?_, h0 l K LL hA, hF l K LL hA⟩
  intro T T' f pr pr' hp
  exact ((h1 T).2.2 T' f pr pr' hp).symm

def LitSub (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : CaseA K LL), HerrSub ((HW l).W K 1 LL hA.2.2)

def HerrExtensionEtale (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : CaseA K LL),
    Formalism.MainNotions.tableLineDegreeTwo.HerrExt ((HW l).W K 1 LL hA.2.2) ((F l).E K 1 LL hA.2.2).tie

def AdmExtT (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.HerrComplexNaturality.FN D HW F ∧ Formalism.MainNotions.LocalSituation.ClassMapInjectiveBijectiveNorms D HW F

def HerrExtensionEtaleTheorem (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := AdmExtT D HW F → HerrExtensionEtale D HW F

def HerrLatticeFurtherConditions (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.tableLineDegreeTwo.adm17 D HW F

theorem herr_lattice_rest_iff (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : HerrLatticeFurtherConditions D HW F ↔ LitSub D HW F ∧ HerrExtensionEtale D HW F :=
  ⟨fun H => ⟨fun l _ K LL hA => (H l K LL hA).1, fun l _ K LL hA => (H l K LL hA).2⟩,
    fun H l _ K LL hA => ⟨H.1 l K LL hA, H.2 l K LL hA⟩⟩

def SenOperatorLetter (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.tableLineDegreeTwo.adm21 D HW F

def SenOperatorTheorem (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop :=
  Formalism.MainNotions.UnusedSlot35.AdmDss D HW F Cm → SenOperatorLetter D HW F

end Formalism.MainNotions.InvariantsGenerators
