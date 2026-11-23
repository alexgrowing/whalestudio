import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioParts
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceFrameLatticeOfMovedLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InLatticeStabilizerAtPlacesIffPlaceSetProd
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.Fam ValuativeRel IsLocalRing
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitInt

variable {D : D7}

theorem mem_latV_iff_at (S : HSp D) (N : Lat S) {P : Pl D → Prop} {v : Pl D} (hv : P v)
    (y : Fin S.rank → AE D) (hy : ∀ i, y i ∈ idAt D (· = v)) :
    y ∈ latV S N P ↔ y ∈ latV S N (· = v) := by
  constructor
  · intro h
    have h2 := GlobalTheory.FinPlLoc.smul_latV v (GlobalTheory.FinPlLoc.idem_mem_intAt (D := D) (· = v)) h
    have e : GlobalTheory.FinPlLoc.idem D (· = v) • y = y := by
      funext i
      rw [Pi.smul_apply, smul_eq_mul]
      exact (GlobalTheory.FinPlLoc.mem_idAt_iff _ _).1 (hy i)
    rwa [e] at h2
  · intro h
    exact GlobalTheory.FinPl.KSplit.latV_mono S N (fun w hw => by subst hw; exact hv) h

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mul_sec (q : SplitPt D k) (a : AE D) (b : k) : a * q.sec b = q.sec (q.pr a * b) := by
  have h := q.sec_pr (a * q.sec b)
  have h2 := q.sec_pr (q.sec b)
  rw [q.pr_sec] at h2
  rw [RingHom.map_mul, q.pr_sec] at h
  rw [h, mul_left_comm, ← h2]

theorem mulVec_sec (q : SplitPt D k) {n : ℕ} (M : Matrix (Fin n) (Fin n) (AE D)) (b : Fin n → k) :
    (M *ᵥ fun i => q.sec (b i)) = fun i => q.sec ((M.map q.pr *ᵥ b) i) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
  rw [map_sum q.sec]
  exact Finset.sum_congr rfl fun j _ => mul_sec q _ _

theorem mem_KO_of_keeps {Y : Type} [Fintype Y] [DecidableEq Y] (x : GL Y k)
    (h : ∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ ∀ i, (x.val *ᵥ y) i ∈ 𝒪[k]) : x ∈ GlobalTheory.SplitWeil.KO k Y := by
  have h1 : ∀ j i : Y, (Pi.single j (1 : k) : Y → k) i ∈ 𝒪[k] := by
    intro j i
    by_cases hij : i = j
    · subst hij; rw [Pi.single_eq_same]; exact one_mem _
    · rw [Pi.single_eq_of_ne hij]; exact zero_mem _
  have hc : ∀ (A : Matrix Y Y k) (i j : Y), (A *ᵥ (Pi.single j (1 : k) : Y → k)) i = A i j := by
    intro A i j
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hA : ∀ i j, x.val i j ∈ 𝒪[k] := fun i j => by
    rw [← hc x.val i j]; exact (h _).1 (h1 j) i
  have hB : ∀ i j, (x⁻¹).val i j ∈ 𝒪[k] := fun i j => by
    rw [← hc (x⁻¹).val i j]
    refine (h _).2 ?_ i
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    exact h1 j
  have hinj : Function.Injective ((algebraMap 𝒪[k] k).mapMatrix : Matrix Y Y 𝒪[k] → Matrix Y Y k) :=
    fun a b hab => Matrix.ext fun i j => Subtype.ext (congrFun (congrFun hab i) j)
  let A : Matrix Y Y 𝒪[k] := Matrix.of fun i j => ⟨x.val i j, hA i j⟩
  let B : Matrix Y Y 𝒪[k] := Matrix.of fun i j => ⟨(x⁻¹).val i j, hB i j⟩
  have eA : (algebraMap 𝒪[k] k).mapMatrix A = x.val := rfl
  have eB : (algebraMap 𝒪[k] k).mapMatrix B = (x⁻¹).val := rfl
  refine ⟨⟨A, B, hinj ?_, hinj ?_⟩, Units.ext eA⟩
  · rw [RingHom.map_mul, RingHom.map_one, eA, eB, Units.mul_inv]
  · rw [RingHom.map_mul, RingHom.map_one, eA, eB, Units.inv_mul]

end

theorem mem_KO_of_moves : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k) (S : HSp D) {Y : Type} [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k S.rank Y) (N : Lat S) (P : Pl D → Prop), P q.v → IntIn q S F N → ∀ g : GA D S, Moves S g N N P → ∀ x : GL Y k, (mt S g).map q.pr = F.β * x.val * F.γ → x ∈ GlobalTheory.SplitWeil.KO k Y := by
  intro D k _ _ _ _ q S Y _ _ F N P hP hI g hM x hx
  refine mem_KO_of_keeps x fun y => ?_
  have hs : ∀ (b : Fin S.rank → k) i, (fun i => q.sec (b i)) i ∈ idAt D (· = q.v) := fun b i => q.sec_mem_idAt _
  have e : (Formalism.L2.Theta.mt S g).map q.pr *ᵥ (F.β *ᵥ y) = F.β *ᵥ (x.val *ᵥ y) := by
    rw [hx, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, F.γβ, Matrix.mul_one]
  rw [hI y, hI (x.val *ᵥ y), ← mem_latV_iff_at S N hP _ (hs _), ← mem_latV_iff_at S N hP _ (hs _),
    hM _ (fun i => GlobalTheory.FinPl.KSplit.idAt_mono (fun w hw => by subst hw; exact hP) (hs _ i)), mulVec_sec, e]

end GlobalTheory.SplitInt

end
