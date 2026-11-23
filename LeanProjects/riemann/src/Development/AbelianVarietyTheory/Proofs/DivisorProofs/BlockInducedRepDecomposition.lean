import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSkewSignature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripSizesSum
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ColumnEval

open GlobalTheory.SmGL GlobalTheory.PRep

section Group

variable {β : Type} [DecidableEq β]

theorem update_mul_left {G : β → Type} [∀ j, Monoid (G j)] (y : ∀ j, G j) (j₀ : β) (p x : G j₀) :
    Function.update y j₀ (p * x) = Pi.mulSingle j₀ p * Function.update y j₀ x := by
  funext j
  by_cases hj : j = j₀
  · subst hj; simp
  · simp [Function.update_of_ne hj, Pi.mulSingle_eq_of_ne hj]

theorem update_mul_right {G : β → Type} [∀ j, Monoid (G j)] (y : ∀ j, G j) (j₀ : β) (x h : G j₀) :
    Function.update y j₀ (x * h) = Function.update y j₀ x * Pi.mulSingle j₀ h := by
  funext j
  by_cases hj : j = j₀
  · subst hj; simp
  · simp [Function.update_of_ne hj, Pi.mulSingle_eq_of_ne hj]

end Group

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {α β : Type} [Fintype α] [LinearOrder α] [Fintype β] [LinearOrder β] [DecidableEq β]
    {m' : β → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)]
    {c : β → α → Type} [∀ j i, Fintype (c j i)] [∀ j i, DecidableEq (c j i)]

theorem mulSingle_mem_relParab (g : ∀ j, (Σ i, c j i) ≃ m' j) (j₀ : β) (p : parab k (g j₀)) :
    (Pi.mulSingle j₀ (p : GL (m' j₀) k) : Levi k m') ∈ relParab k g := by
  intro j _
  by_cases hj : j = j₀
  · subst hj; simpa using p.2
  · rw [Pi.mulSingle_eq_of_ne hj]; exact (parab k (g j)).one_mem

theorem relProj_mulSingle (g : ∀ j, (Σ i, c j i) ≃ m' j) (j₀ : β) (p : parab k (g j₀)) :
    relProj k g ⟨Pi.mulSingle j₀ (p : GL (m' j₀) k), mulSingle_mem_relParab g j₀ p⟩ =
      Pi.mulSingle j₀ (leviProj k (g j₀) p) := by
  funext j
  simp only [relProj, MonoidHom.coe_mk, OneHom.coe_mk]
  by_cases hj : j = j₀
  · subst hj
    rw [Pi.mulSingle_eq_same (M := fun j => Levi k (c j)) j (leviProj k (g j) p)]
    congr 1
    exact Subtype.ext (Pi.mulSingle_eq_same _ _)
  · rw [Pi.mulSingle_eq_of_ne (M := fun j => Levi k (c j)) hj (leviProj k (g j₀) p)]
    convert map_one (leviProj k (g j))
    first
      | exact Pi.mulSingle_eq_of_ne (M := fun j => GL (m' j) k) hj (p : GL (m' j₀) k)
      | simp [Pi.mulSingle, Function.update, hj]

theorem relDeltaHalf_mulSingle (j₀ : β) (L : Levi k (c j₀)) :
    relDeltaHalf k c (Pi.mulSingle j₀ L) = deltaHalf k (c j₀) L := by
  rw [relDeltaHalf_apply, Finset.prod_eq_single j₀]
  · rw [Pi.mulSingle_eq_same]
  · intro j _ hj; rw [Pi.mulSingle_eq_of_ne hj, map_one]
  · intro h; exact absurd (Finset.mem_univ _) h

variable {W : Type} [AddCommGroup W] [Module ℂ W]

def evalFun (g : ∀ j, (Σ i, c j i) ≃ m' j) (τ : Representation ℂ (∀ j, Levi k (c j)) W) (j₀ : β)
    (y : ∀ j, GL (m' j) k) (l : Module.Dual ℂ W)
    (F : smoothPart (ind (relParab k g) ((twist τ (relDeltaHalf k c)).comp (relProj k g)))) :
    GL (m' j₀) k → ℂ :=
  fun x => l (F.1.1 (Function.update y j₀ x))

theorem evalFun_mem (g : ∀ j, (Σ i, c j i) ≃ m' j) (τ : Representation ℂ (∀ j, Levi k (c j)) W)
    (ψ : (∀ j, Levi k (c j)) →* ℂˣ) (hτ : ∀ z w, τ z w = (ψ z : ℂ) • w) (j₀ : β)
    (y : ∀ j, GL (m' j) k) (l : Module.Dual ℂ W)
    (F : smoothPart (ind (relParab k g) ((twist τ (relDeltaHalf k c)).comp (relProj k g)))) :
    evalFun g τ j₀ y l F ∈ indSpace (parab k (g j₀))
      ((twist (ofChar (ψ.comp (MonoidHom.mulSingle (fun j => Levi k (c j)) j₀)))
        (deltaHalf k (c j₀))).comp (leviProj k (g j₀))) := by
  intro p x
  have h1 : F.1.1 (Pi.mulSingle j₀ (p : GL (m' j₀) k) * Function.update y j₀ x) = _ :=
    F.1.2 ⟨_, mulSingle_mem_relParab g j₀ p⟩ (Function.update y j₀ x)
  simp only [evalFun]
  rw [update_mul_left, h1]
  simp only [MonoidHom.comp_apply, twist_apply, hτ, relProj_mulSingle, relDeltaHalf_mulSingle,
    ofChar_apply, map_smul, smul_eq_mul, MonoidHom.mulSingle_apply]

theorem evalFun_smooth (g : ∀ j, (Σ i, c j i) ≃ m' j)
    (τ : Representation ℂ (∀ j, Levi k (c j)) W)
    (ψ : (∀ j, Levi k (c j)) →* ℂˣ) (hτ : ∀ z w, τ z w = (ψ z : ℂ) • w) (j₀ : β)
    (y : ∀ j, GL (m' j) k) (l : Module.Dual ℂ W)
    (F : smoothPart (ind (relParab k g) ((twist τ (relDeltaHalf k c)).comp (relProj k g)))) :
    (⟨evalFun g τ j₀ y l F, evalFun_mem g τ ψ hτ j₀ y l F⟩ :
      indSpace (parab k (g j₀))
        ((twist (ofChar (ψ.comp (MonoidHom.mulSingle (fun j => Levi k (c j)) j₀)))
          (deltaHalf k (c j₀))).comp (leviProj k (g j₀)))) ∈
      smoothPart (ind (parab k (g j₀))
        ((twist (ofChar (ψ.comp (MonoidHom.mulSingle (fun j => Levi k (c j)) j₀)))
          (deltaHalf k (c j₀))).comp (leviProj k (g j₀)))) := by
  apply mem_smoothPart_of_nhds
  have hF : IsOpen {G : Levi k m' | ind (relParab k g) ((twist τ (relDeltaHalf k c)).comp (relProj k g)) G F.1 = F.1} := F.2
  have hc : Continuous (fun x : GL (m' j₀) k => (Pi.mulSingle j₀ x : Levi k m')) := by
    first
      | fun_prop
      | exact continuous_mulSingle (f := fun j => GL (m' j) k) j₀
      | exact (continuous_pi fun j => by
          by_cases hj : j = j₀
          · subst hj; simp only [Pi.mulSingle_eq_same]; exact continuous_id'
          · simpa [Pi.mulSingle_eq_of_ne hj] using continuous_const)
  refine Filter.mem_of_superset ((hF.preimage hc).mem_nhds (by simp)) ?_
  intro h hh
  simp only [Set.mem_preimage, Set.mem_setOf_eq] at hh ⊢
  apply Subtype.ext
  funext x
  have := congrFun (congrArg Subtype.val hh) (Function.update y j₀ x)
  show l (F.1.1 (Function.update y j₀ (x * h))) = l (F.1.1 (Function.update y j₀ x))
  rw [update_mul_right]
  exact congrArg l this

def evalMap (g : ∀ j, (Σ i, c j i) ≃ m' j) (τ : Representation ℂ (∀ j, Levi k (c j)) W)
    (ψ : (∀ j, Levi k (c j)) →* ℂˣ) (hτ : ∀ z w, τ z w = (ψ z : ℂ) • w) (j₀ : β)
    (y : ∀ j, GL (m' j) k) (l : Module.Dual ℂ W) :
    smoothPart (ind (relParab k g) ((twist τ (relDeltaHalf k c)).comp (relProj k g))) →ₗ[ℂ]
      IndSp (g j₀) (ofChar (ψ.comp (MonoidHom.mulSingle (fun j => Levi k (c j)) j₀))) where
  toFun F := ⟨⟨evalFun g τ j₀ y l F, evalFun_mem g τ ψ hτ j₀ y l F⟩, evalFun_smooth g τ ψ hτ j₀ y l F⟩
  map_add' F G := by
    apply Subtype.ext; apply Subtype.ext; funext x
    exact map_add l _ _
  map_smul' a F := by
    apply Subtype.ext; apply Subtype.ext; funext x
    exact map_smul l a _

theorem exists_evalMap (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {α β : Type} [Fintype α] [LinearOrder α] [Fintype β] [LinearOrder β] [DecidableEq β]
    {m' : β → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)]
    {c : β → α → Type} [∀ j i, Fintype (c j i)] [∀ j i, DecidableEq (c j i)]
    (g : ∀ j, (Σ i, c j i) ≃ m' j) {W : Type} [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ (∀ j, GlobalTheory.SmGL.Levi k (c j)) W) (ψ : (∀ j, GlobalTheory.SmGL.Levi k (c j)) →* ℂˣ) :
    (∀ z w, τ z w = (ψ z : ℂ) • w) → ∀ (j₀ : β) (ν : GlobalTheory.SmGL.Levi k m' →* ℂˣ)
    (y : ∀ j, GL (m' j) k) (l : Module.Dual ℂ W),
    ∃ E : Representation.IntertwiningMap ((GlobalTheory.SmGL.twist (GlobalTheory.SmGL.relInd g τ) ν).comp (MonoidHom.mulSingle (fun j => GL (m' j) k) j₀)) (GlobalTheory.SmGL.twist (GlobalTheory.SmGL.parInd (g j₀)
        (GlobalTheory.SmGL.ofChar (ψ.comp (MonoidHom.mulSingle (fun j => GlobalTheory.SmGL.Levi k (c j)) j₀))))
        (ν.comp (MonoidHom.mulSingle (fun j => GL (m' j) k) j₀))),
      ∀ F x, (E F).1.1 x = l (F.1.1 (Function.update y j₀ x)) := by
  intro hτ j₀ ν y l
  refine ⟨{ toLinearMap := evalMap g τ ψ hτ j₀ y l, isIntertwining' := fun h => ?_ }, fun F x => rfl⟩
  refine LinearMap.ext fun F => ?_
  apply Subtype.ext; apply Subtype.ext; funext x
  show l ((ν (Pi.mulSingle j₀ h) : ℂ) • F.1.1 (Function.update y j₀ x * Pi.mulSingle j₀ h)) =
    (ν (Pi.mulSingle j₀ h) : ℂ) * l (F.1.1 (Function.update y j₀ (x * h)))
  rw [update_mul_right, map_smul, smul_eq_mul]

end GlobalTheory.ColumnEval
