import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsDataDualGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLevelCharacterAtConjugateSplitPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InductionContragredient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleAdmissible
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionTensorProductHasFiniteLength
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchurAdmissibleAlt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CuspLaws
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalCompactFixedVectorsPiTensorSmooStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.JHMult
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.ContraProd

section General

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

end General

end GlobalTheory.ContraProd

noncomputable section

namespace GlobalTheory.ContraProd

section Fixed

theorem finiteDimensional_fixed_piTensor {α : Type} [Finite α] {Γ X : α → Type} [∀ a, Group (Γ a)]
    [∀ a, TopologicalSpace (Γ a)] [∀ a, IsTopologicalGroup (Γ a)] [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a)) (hρ : ∀ a, IsSmooth (ρ a))
    (K : ∀ a, Subgroup (Γ a)) (hK : ∀ a, IsCompact (K a : Set (Γ a)))
    (hf : ∀ a, FiniteDimensional ℂ (fixed (ρ a) (K a))) :
    FiniteDimensional ℂ (fixed (piTensor ρ) (Subgroup.pi Set.univ K)) :=
  GlobalTheory.T.finiteDimensional_compact_fixed_vectors_piTensor_smooth ρ hρ K hK hf

end Fixed

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_compactOpen_GL (n : Type) [Fintype n] [DecidableEq n] (U : Set (GL n k)) (hU : U ∈ nhds 1) :
    ∃ K : Subgroup (GL n k), IsOpen (K : Set (GL n k)) ∧ IsCompact (K : Set (GL n k)) ∧ (K : Set (GL n k)) ⊆ U := by
  obtain ⟨J, h1, h2, h3, -⟩ := exists_open_normalised_subgroup_subset k n U hU
  exact ⟨J, h1, GlobalTheory.SplitFlip.isCompact_KO.of_isClosed_subset (J.isClosed_of_isOpen h1) h3, h2⟩

theorem exists_pi_compactOpen {α : Type} [Finite α] (m : α → Type) [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
    (U : Set (Levi k m)) (hU : U ∈ nhds (1 : Levi k m)) :
    ∃ K : ∀ a, Subgroup (GL (m a) k), (∀ a, IsOpen (K a : Set (GL (m a) k))) ∧
      (∀ a, IsCompact (K a : Set (GL (m a) k))) ∧ ((Subgroup.pi Set.univ K : Subgroup (Levi k m)) : Set (Levi k m)) ⊆ U := by
  rw [nhds_pi, Filter.mem_pi] at hU
  obtain ⟨I, -, t, ht, hts⟩ := hU
  choose K hKo hKc hKt using fun a => exists_compactOpen_GL (k := k) (m a) (t a) (ht a)
  refine ⟨K, hKo, hKc, ?_⟩
  rw [Subgroup.coe_pi]
  exact fun g hg => hts fun a _ => hKt a (hg a (Set.mem_univ a))

theorem isAdmissible_piTensor {α : Type} [Finite α] (m : α → Type) [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
    {X : α → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    (ρ : ∀ a, Representation ℂ (GL (m a) k) (X a)) (hρ : ∀ a, IsAdmissible (ρ a)) :
    IsAdmissible (piTensor ρ : Representation ℂ (Levi k m) _) := by
  refine ⟨isSmooth_piTensor fun a => (hρ a).1, fun K hKo hKc => ?_⟩
  obtain ⟨K', hKo', hKc', hK'⟩ := exists_pi_compactOpen m (K : Set (Levi k m)) (hKo.mem_nhds K.one_mem)
  haveI := finiteDimensional_fixed_piTensor ρ (fun a => (hρ a).1) K' hKc'
    fun a => (hρ a).2 (K' a) (hKo' a) (hKc' a)
  exact Submodule.finiteDimensional_of_le (S₁ := fixed (piTensor ρ : Representation ℂ (Levi k m) _) K)
    (S₂ := fixed (piTensor ρ) (Subgroup.pi Set.univ K'))
    (fun v hv => GlobalTheory.ContraRefl.mem_fix.2 fun h hh => GlobalTheory.ContraRefl.mem_fix.1 hv h (hK' hh))

end GlobalTheory.ContraProd

noncomputable section

namespace GlobalTheory.ContraProd

section Pairing

variable {α : Type} [Fintype α] {Γ X : α → Type} [∀ a, Group (Γ a)] [∀ a, TopologicalSpace (Γ a)]
  [∀ a, IsTopologicalGroup (Γ a)] [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
  (ρ : ∀ a, Representation ℂ (Γ a) (X a))

def pairLin : (⨂[ℂ] a, smoothPart (ρ a).dual) →ₗ[ℂ] Module.Dual ℂ (⨂[ℂ] a, X a) :=
  PiTensorProduct.dualDistrib ∘ₗ PiTensorProduct.map (fun a => (smoothPart (ρ a).dual).subtype)

theorem pairLin_tprod (l : ∀ a, smoothPart (ρ a).dual) (v : ∀ a, X a) :
    pairLin ρ (PiTensorProduct.tprod ℂ l) (PiTensorProduct.tprod ℂ v) =
      ∏ a, (l a : Module.Dual ℂ (X a)) (v a) := by
  simp [pairLin, PiTensorProduct.map_tprod, PiTensorProduct.dualDistrib_apply]

theorem pairLin_equivariant (g : ∀ a, Γ a) (t : ⨂[ℂ] a, smoothPart (ρ a).dual) :
    pairLin ρ (piTensor (fun a => contra (ρ a)) g t) = (piTensor ρ).dual g (pairLin ρ t) := by
  induction t using PiTensorProduct.induction_on with
  | smul_tprod c l =>
    rw [map_smul, map_smul, map_smul, map_smul]
    congr 1
    refine PiTensorProduct.ext (MultilinearMap.ext fun v => ?_)
    simp only [LinearMap.compMultilinearMap_apply, piTensor_tprod, pairLin_tprod, Representation.dual_apply,
      Module.Dual.transpose_apply, LinearMap.comp_apply, contra_apply, Pi.inv_apply]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

theorem pairLin_mem (t : ⨂[ℂ] a, smoothPart (ρ a).dual) : pairLin ρ t ∈ smoothPart (piTensor ρ).dual := by
  induction t using PiTensorProduct.induction_on with
  | smul_tprod c l =>
    rw [map_smul]
    refine Submodule.smul_mem _ _ (mem_smoothPart_of_nhds ?_)
    refine Filter.mem_of_superset (set_pi_mem_nhds Set.finite_univ fun a _ =>
      (isSmooth_contra (ρ a) (l a)).mem_nhds (by simp)) fun g hg => ?_
    show (piTensor ρ).dual g (pairLin ρ (PiTensorProduct.tprod ℂ l)) = pairLin ρ (PiTensorProduct.tprod ℂ l)
    rw [← pairLin_equivariant, piTensor_tprod]
    congr 2
    funext a
    exact hg a (Set.mem_univ a)
  | add x y hx hy => rw [map_add]; exact add_mem hx hy

def pairMap : (piTensor fun a => contra (ρ a)).IntertwiningMap (contra (piTensor ρ)) where
  toLinearMap := (pairLin ρ).codRestrict _ (pairLin_mem ρ)
  isIntertwining' g := LinearMap.ext fun t => Subtype.ext (pairLin_equivariant ρ g t)

end Pairing

end GlobalTheory.ContraProd

noncomputable section

namespace GlobalTheory.ContraProd

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end GlobalTheory.ContraProd
