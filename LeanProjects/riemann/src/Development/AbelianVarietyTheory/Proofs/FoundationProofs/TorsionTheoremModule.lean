import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SelmerWindowSums
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankCyclotomicExtAndCyclotomicCharSurjective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InclWFrobIter
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DeRhamJumpDescentStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisUniformizerRingStableStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIntegersFiniteExtensionOpenStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AbsoluteGaloisMemFixingSubgroupMaxUnramified

noncomputable section

namespace GlobalTheory.TorsionBoundCompare

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified

section Hyp

open Formalism.MainNotions.LocalSituation

variable {l : ℕ} [Fact l.Prime] (LT : LocTheory) (HW : HWOf LT) (AI : LocAinf l (LT l)) {K : FinExt l}
  {s : ℕ} {LL : FinExt l} (h : Good K s LL)

theorem actVB_res (Y : Lat K LL) (g : ↥(GK K)) (g' : ↥(GK (levelField K s))) (hg : (g : GQ l) = g') :
    actVB ((LT l).PD K) Y.ρ g = actVB ((LT l).PD (levelField K s)) (resKs h Y) g' := by
  have h2 : Y.ρ g = resKs h Y g' := congrArg Y.ρ (Subtype.ext hg)
  have h3 : (((LT l).PD K).actB g).toAlgHom.toLinearMap.restrictScalars ℚ_[l] =
      (((LT l).PD (levelField K s)).actB g').toAlgHom.toLinearMap.restrictScalars ℚ_[l] :=
    LinearMap.ext fun b => (((LT l).PD_actB K g b).trans (by rw [hg])).trans
      ((LT l).PD_actB (levelField K s) g' b).symm
  unfold actVB
  rw [h2, h3]

theorem iInf_eq_of {α β γ : Type} [CompleteLattice γ] (f : α → γ) (g : β → γ)
    (h1 : ∀ a, ∃ b, f a = g b) (h2 : ∀ b, ∃ a, f a = g b) : ⨅ a, f a = ⨅ b, g b :=
  le_antisymm (le_iInf fun b => by obtain ⟨a, ha⟩ := h2 b; exact ha ▸ iInf_le f a)
    (le_iInf fun a => by obtain ⟨b, hb⟩ := h1 a; exact hb ▸ iInf_le g b)

theorem finrank_congr {R M : Type} [Field R] [AddCommGroup M] [Module R M] {X X' : Submodule R M}
    (e : X = X') : Module.finrank R ↥X = Module.finrank R ↥X' := by rw [e]

theorem fixed_eq (Y : Lat K LL) : (⨅ g : ((HW l).W K s LL h).GKs,
      LinearMap.ker (actVB ((LT l).PD K) Y.ρ (g : ↥(GK K)) - LinearMap.id)) =
      Dcris ((LT l).PD (levelField K s)) (resKs h Y) := by
  refine iInf_eq_of _ _ (fun g => ?_) fun g' => ?_
  · have hg : (g.1.1 : GQ l) ∈ GK (levelField K s) := (mem_GKs ((HW l).W_s K s LL h) g.1).mp g.2
    exact ⟨⟨g.1.1, hg⟩,
      congrArg (fun T => LinearMap.ker (T - LinearMap.id)) (actVB_res LT h Y g.1 ⟨g.1.1, hg⟩ rfl)⟩
  · exact ⟨⟨⟨g'.1, GK_le (K := K) (K' := levelField K s) h.2.2.1 g'.2⟩,
      (mem_GKs ((HW l).W_s K s LL h) _).mpr g'.2⟩,
      congrArg (fun T => LinearMap.ker (T - LinearMap.id)) (actVB_res LT h Y _ _ rfl)⟩

theorem crys_iff (Y : Lat K LL) :
    IsCrysOn (sit LT HW l AI K s LL h) (sit LT HW l AI K s LL h).W.GKs Y ↔
      IsCrys ((LT l).PD (levelField K s)) (resKs h Y) := by
  have h1 := finrank_congr (fixed_eq LT HW h Y)
  have h2 := congrArg (· * Module.finrank ↥LL.1 Y.V) (finrank_maxUnramified_levelFieldFiniteExtension K s h.1).symm
  exact iff_of_eq (congrArg₂ Eq h1 h2)

end Hyp

section Final

open Formalism.MainNotions.LocalSituation

variable {l : ℕ} [Fact l.Prime]

def lineLat {K LL : FinExt l} {ψ : ↥(GK K) →* (↥LL.1)ˣ} (L : Lattice (O := ↥(OL LL)) (charRep ψ))
    (hψ : Continuous fun g => ((ψ g : (↥LL.1)ˣ) : ↥LL.1)) : Lat K LL where
  V := ↥LL.1
  modO := Algebra.toModule
  towO := inferInstance
  ρ := charRep ψ
  cont := fun _ => hψ.mul continuous_const
  L := L

variable (LT : LocTheory) (HW : HWOf LT) (AI : LocAinf l (LT l)) {K : FinExt l}
  {s : ℕ} {LL : FinExt l} (h : Good K s LL)

def TorsionBoundUnder {P : LocPrime l} {K LL : FinExt l} {s : ℕ} (h : Good K s LL)
    (Hyp : Lat K LL → ℕ → ℕ → Prop) (e : ℕ) : Prop :=
  ∀ (Y Yt : Lat K LL) (ι : LatHom Y.L Yt.L) (π : LatHom Yt.L (unitLat K LL)),
    IsSESLat (Qp := ℚ_[l]) ι π →
    IsCrys (P.PD (levelField K s)) (resKs h Yt) →
  ∀ M₀ h₀ : ℕ, Hyp Y M₀ h₀ →
  ∀ U : Finset ℤ, (∀ u, u ∈ U ↔ IsJump P h Y u) →
  ∀ x ∈ Yt.L.T, π.f x = 1 →
  ∀ c : ↥(GK K) → ↥Y.L.T, (∀ g, ι.f (c g : Y.V) = Yt.ρ g x - x) →
    PushInHf (P.PD K) (tateLat P K LL e) l (cTor K s (M₀ + h₀) U e) Y c

variable (D : Formalism.BasicNotions.D7) (H : HWOf D.loc) (F : FonOf D.loc D.locA H)

def TorsionTheoremModule : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (e : ℕ),
    TorsionBoundUnder (P := D.loc l) h
        (HypW (sit D.loc H l (D.locA l) K s LL h) ((F l).E K s LL h).tie) e ∧
      FiniteClasses (D.loc l) K LL e ∧ LengthBound (D.loc l) K LL e

end Final

end GlobalTheory.TorsionBoundCompare
