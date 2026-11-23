import Formalism.LocalRingCardinality.SpanPowerMembership.NZLevB
import Formalism.LocalToGlobal.GroupLattices.FockModels.Cartan
import Formalism.LocalToGlobal.GroupLattices.FockModels.WeylDim
import Formalism.LocalToGlobal.GroupLattices.FockModels.SpanTopOf
import Formalism.SharpRestriction.GrowthBounds.DataG

open MvPolynomial

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.G.Model

section Weyl

variable {O Kf : Type} [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf] [CharZero Kf]

theorem Dl0_le (m : ℕ) (lam : Fin (m + 1) → ℤ) (Λ : Submodule O (Fin (m + 1) → Kf)) (hΛ : IsLattice O Λ) :
    Dl0 O m lam Λ ≤ (dualWeyl Kf (m + 1) (m + 1) (nuOf lam)).restrictScalars O := by
  unfold Dl0
  split_ifs with hanti
  · obtain ⟨g, hg, rfl⟩ := hΛ
    refine (iInf_le _ g).trans ((iInf_le _ ⟨hg, rfl⟩).trans ?_)
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨w0, hw0, hw0x⟩ := hx
    have hnu : Antitone (nuOf lam) := toNat_antitone lam hanti
    have h1 : (mapAlgHom (Algebra.ofId O Kf)).toLinearMap w0 ∈ dualWeyl Kf (m + 1) (m + 1) (nuOf lam) :=
      dualWeylMap O Kf (algebraMap O Kf) _ _ _ w0 (weylLeDual O _ _ le_rfl _ hnu hw0)
    have h2 : x = rowAct Kf g⁻¹ (rowAct Kf g x) := by
      rw [rowAct_inv_left Kf _ _ g hg]
    have h3 : x ∈ dualWeyl Kf (m + 1) (m + 1) (nuOf lam) := by
      rw [h2]
      refine dualWeylRowStable Kf _ _ _ g⁻¹ _ ?_
      have : rowAct Kf g x = (mapAlgHom (Algebra.ofId O Kf)).toLinearMap w0 := hw0x.symm
      rw [this]; exact h1
    exact (dualWeyl Kf (m + 1) (m + 1) (nuOf lam)).smul_mem _ h3
  · exact bot_le

end Weyl

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  [CharZero Kf] (P : Places p O Kf)

abbrev nuV (v : Fin P.nV) (s : Fin (P.n' v)) : Fin (P.m + 1) → ℕ := nuOf (lamAt (P.lam0 v) s)

theorem nuV_anti (v : Fin P.nV) (s : Fin (P.n' v)) : Antitone (nuV P v s) :=
  toNat_antitone _ (lamAt_antitone' _ (P.dom v) s)

abbrev IdxV (v : Fin P.nV) (s : Fin (P.n' v)) : Type := ↥(ssIdx (P.m + 1) (P.m + 1) (nuV P v s))

instance (v : Fin P.nV) (s : Fin (P.n' v)) : Finite (IdxV P v s) := (sSIdxFinite _ _ _).to_subtype

def bV (v : Fin P.nV) (s : Fin (P.n' v)) : IdxV P v s → MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) Kf :=
  (sSBasis Kf (P.m + 1) (P.m + 1) (nuV P v s)).choose

theorem bV_spec (v : Fin P.nV) (s : Fin (P.n' v)) :
    IsWeightBasis Kf (P.m + 1) (P.m + 1) (nuV P v s) (bV P v s) (fun i => rowWt i.1) :=
  (sSBasis Kf (P.m + 1) (P.m + 1) (nuV P v s)).choose_spec.1

def prodF (F : ∀ v, Fin (P.n' v) → MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) Kf) : P.Xsp :=
  ∏ v, P.vEmb v (∏ s, blockEmb Kf s (F v s))

def BI (I : ∀ v s, IdxV P v s) : P.Xsp := prodF P fun v s => bV P v s (I v s)

def EV : P.Xsp := prodF P fun v s => hw Kf le_rfl (nuV P v s)

theorem htupW_le (L : P.Tup) (hL : ∀ v (s : Fin (P.n' v)), IsLattice O (extO O (P.ι v) (P.σ v) s.val (L v))) :
    P.HtupW L ≤ (Submodule.span Kf (Set.range (BI P))).restrictScalars O := by
  classical
  let Tv : ∀ v, Submodule Kf (MvPolynomial (Fin (P.n' v) × (Fin (P.m + 1) × Fin (P.m + 1))) Kf) := fun v =>
    Submodule.span Kf {X | ∃ I : ∀ s, IdxV P v s, X = ∏ s, blockEmb Kf s (bV P v s (I s))}
  have hv : ∀ v, HtenW O (P.lam0 v) (fun s => extO O (P.ι v) (P.σ v) s.val (L v)) ≤ (Tv v).restrictScalars O := by
    intro v
    unfold HtenW tensorLat
    rw [Submodule.span_le]
    rintro _ ⟨F, hF, rfl⟩
    refine prod_mem_of_span (R := Kf) (fun s => (blockEmb Kf s).toLinearMap) (fun s => Set.range (bV P v s)) (Tv v)
      (fun f hf => ?_) F (fun s => ?_)
    · choose I hI using hf
      exact Submodule.subset_span ⟨I, by simp only [AlgHom.toLinearMap_apply, hI]⟩
    · rw [(bV_spec P v s).2.1]
      exact Dl0_le _ _ _ (hL v s) (hF s)
  unfold Places.HtupW Places.tenV
  rw [Submodule.span_le]
  rintro _ ⟨F, hF, rfl⟩
  refine prod_mem_of_span (R := Kf) (fun v => (P.vEmb v).toLinearMap)
    (fun v => {X | ∃ I : ∀ s, IdxV P v s, X = ∏ s, blockEmb Kf s (bV P v s (I s))}) _ (fun f hf => ?_) F
    (fun v => hv v (hF v))
  choose I hI using hf
  exact Submodule.subset_span ⟨fun v s => I v s, by simp only [AlgHom.toLinearMap_apply, hI]; rfl⟩

end Formalism.BasicNotions.Examples₂.NZ
