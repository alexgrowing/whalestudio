import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Formalism.SharpRestriction.LevelLetterCocycles.LocalizationQuotientSeparatedDvd

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup
open scoped TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

theorem filV_sep {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (z : V ⊗[Qp] BdR) (hz : ∀ a : ℤ, z ∈ FilV PD (LL := LL) (V := V) a) : z = 0 := by
  classical
  let bV := Module.Free.chooseBasis Qp V
  let E := TensorProduct.equivFinsuppOfBasisLeft (N := BdR) bV
  have hco : ∀ (a : ℤ) (w : V ⊗[Qp] BdR), w ∈ FilV PD (LL := LL) (V := V) a →
      ∀ j, E w j ∈ PD.Fil a := by
    intro a w hw
    obtain ⟨y, rfl⟩ := hw
    induction y using TensorProduct.induction_on with
    | zero => intro j; simp
    | tmul x f =>
      intro j
      simp only [TensorProduct.AlgebraTensorModule.map_tmul, LinearMap.id_apply,
        Submodule.coe_subtype, E, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul,
        Finsupp.mapRange_apply]
      exact ((PD.Fil a).restrictScalars Qp).smul_mem _ f.2
    | add x y hx hy =>
      intro j
      rw [map_add, map_add, Finsupp.add_apply]
      exact (PD.Fil a).add_mem (hx j) (hy j)
  have h0 : E z = 0 := by
    ext j
    exact PD.Fil_sep _ fun a => hco a z (hz a) j
  simpa using congrArg E.symm h0

theorem filS_top (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (A : ArcP n)
    (T : LocLat G Qp LL O) (hW : Win W A T) (a : ZMod n) (s : ℕ) (u : ℤ)
    (hu : ∀ x ∈ (A.ty (a - (s : ZMod n))).win A.G₀ A.S A.η, x < u) :
    FilS W T a s u = ⊥ := by
  classical
  rw [eq_bot_iff]
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨hxF, hxL⟩ := Submodule.mem_inf.mp hx
  suffices hx0 : x = 0 by simp [hx0]
  set i : ZMod n := a - (s : ZMod n) with hi
  obtain ⟨hbij, -, -⟩ := hcase
  let e : K₀ ≃ₐ[Qp] K := AlgEquiv.ofBijective (IsScalarTower.toAlgHom Qp K₀ K) hbij
  let τ : K →ₐ[Qp] LL := (W.emb i).comp e.symm.toAlgHom
  have hez : ∀ z : K₀, e z = algebraMap K₀ K z := fun z => rfl
  have hover : ∀ z : K₀, τ (algebraMap K₀ K z) = W.emb i z := by
    intro z
    have : e.symm (algebraMap K₀ K z) = z := by
      rw [← hez, AlgEquiv.symm_apply_apply]
    show W.emb i (e.symm (algebraMap K₀ K z)) = W.emb i z
    rw [this]
  have hOver : Formalism.MainNotions.LiftingTheory.Over W τ i := by
    ext z
    exact hover z
  have hJ := hW.2 i τ hOver
  have hE : ιV PD (LL := LL) (V := T.V) x ∈ DdRE PD T.ρ τ :=
    Formalism.MainNotions.UnusedSlot80.LevR.ιDi_le W T i τ hover hbij.2 ⟨x, hxL, rfl⟩
  have hV : ιV PD (LL := LL) (V := T.V) x ∈ FilV PD (LL := LL) (V := T.V) u :=
    (Submodule.mem_inf.mp hxF).2
  have hall : ∀ k : ℕ, ιV PD (LL := LL) (V := T.V) x ∈ FildR PD T.ρ τ (u + k) := by
    intro k
    induction k with
    | zero =>
      rw [Nat.cast_zero, add_zero]
      exact Submodule.mem_inf.mpr ⟨hE, hV⟩
    | succ k ih =>
      have heq : FildR PD T.ρ τ (u + k + 1) = FildR PD T.ρ τ (u + k) := by
        by_contra h
        have := hu _ (hJ (u + k) h)
        omega
      rw [Nat.cast_succ, ← add_assoc, heq]
      exact ih
  have hallV : ∀ b : ℤ, ιV PD (LL := LL) (V := T.V) x ∈ FilV PD (LL := LL) (V := T.V) b := by
    intro b
    by_cases h : b ≤ u
    · exact Formalism.MainNotions.UnusedSlot80.LevR.filV_anti h hV
    · have hk := (Submodule.mem_inf.mp (hall (b - u).toNat)).2
      have : u + ((b - u).toNat : ℤ) = b := by omega
      rwa [this] at hk
  have h0 := filV_sep _ hallV
  exact Formalism.MainNotions.UnusedSlot80.LevR.ιV_inj (h0.trans (map_zero _).symm)

end Formalism.MainNotions.N.FrobeniusPowerSeries
