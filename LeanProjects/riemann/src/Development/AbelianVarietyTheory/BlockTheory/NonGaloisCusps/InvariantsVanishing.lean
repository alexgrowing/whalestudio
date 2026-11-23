import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import ReciprocityTheory.BasicDefinitions.AdRep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.AdmLoc
open ReciprocityTheory.Def (H2)

section Concl

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {n r : ℕ} (emb : ZMod n → (K₀ →ₐ[Qp] LL))
    (D : TopData n r) (Γ : GalData G Qp LL O)

abbrev resK : Type := O ⧸ Ideal.span {Γ.lam}

abbrev resRep : Representation O G (TensorProduct O ↥Γ.T₀.L.T (resK Γ)) := twCoef Γ.W₀ Γ.χ₁ (resK Γ)

abbrev HH : Type := H1tw Γ.T₀.L Γ.χ₁

abbrev Hf : Submodule O (HH Γ) := latticeFiniteCohomology PD (twLattice Γ.T₀.L Γ.χ₁⁻¹)

def Concl [NeZero n] : Prop :=
  (resRep Γ).invariants = ⊥ ∧
  Subsingleton (H2 (resRep Γ) ⊤) ∧
  (Module.Free O (HH Γ) ∧ Module.Finite O (HH Γ) ∧ Module.finrank O (HH Γ) = r * n) ∧
  ((∃ C : Submodule O (HH Γ), IsCompl (Hf PD Γ) C) ∧ Module.finrank O ↥(Hf PD Γ) = D.dsum) ∧
  ∀ (X : Type) [AddCommGroup X] [Module O X] [Finite X],
    TensIso Γ.T₀.L Γ.χ₁ X ∧
      adm PD emb Γ D.t D.Ut Γ.W₀ X = (finiteSelmer PD Γ.T₀.L Γ.χ₁ X : Set _)

theorem invariants_eq_bot_iff :
    (resRep Γ).invariants = ⊥ ↔ ∀ x, (∀ g, resRep Γ g x = x) → x = 0 := by
  rw [Submodule.eq_bot_iff]
  exact Iff.rfl

example (x : resK Γ) : Γ.lam ^ 1 • x = 0 := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [pow_one]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))

end Concl

def ErrorExponentStatement {l : ℕ} [Fact l.Prime] (P : LocPrime l) : Prop :=
  ∀ (K LL : FinExt l) (n r : ℕ) [NeZero n] (emb : ZMod n → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1))
    (D : TopData n r) (Γ : GalData ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)),
    Standing P K LL emb Γ.lam → IsTopGal (P.PD K) emb D Γ →
    D.T1 l → D.T2 l → D.T3 l → Concl (P.PD K) emb D Γ

def Stmt : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ErrorExponentStatement P

theorem letters_ne_zero {l : ℕ} [Fact l.Prime] {P : LocPrime l} {K LL : FinExt l} {n : ℕ}
    {emb : ZMod n → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1)} {lam : ↥(OL LL)} (h : Standing P K LL emb lam) : n ≠ 0 := by
  have := K.2
  rw [h.2.2.1]
  exact Module.finrank_pos.ne'

example : exData.dsum = 2 := by decide

end GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing
