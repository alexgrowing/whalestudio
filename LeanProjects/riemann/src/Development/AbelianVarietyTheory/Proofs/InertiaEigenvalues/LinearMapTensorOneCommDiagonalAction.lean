import Mathlib
import Formalism.WeaklyAdmissibleFiltrations.CrystallineStableLifts.DPotCrisStableAndExistsPotentiallyCrystallineDat
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsCrystallineJumpsOfIsIsoMatrixGaloisRepresentat
open Formalism.WeaklyAdmissibleFiltrations Module TensorProduct

noncomputable section

namespace GlobalTheory.HTW.Rec

section PotTransport

variable {G : Type} [Group G] {Qp K₀ K K₀' K' : Type} [Field Qp] [Field K₀] [Field K]
    [Field K₀'] [Field K']
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    [Algebra Qp K₀'] [Algebra Qp K'] [Algebra K₀' K'] [IsScalarTower Qp K₀' K']
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra K₀' B] [IsScalarTower Qp K₀' B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    [Algebra K₀' BdR] [Algebra K' BdR] [IsScalarTower Qp K' BdR]
    [IsScalarTower K₀' K' BdR] [IsScalarTower Qp K₀' BdR]
    (PC : PotCrysData G Qp K₀ K K₀' K' B BdR) {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']

theorem linearMap_tensorOne_comm_diagonalAction {H : Type} [Group H] {K₁ K₂ : Type} [Field K₁] [Field K₂]
    [Algebra Qp K₁] [Algebra Qp K₂] [Algebra K₁ K₂] [IsScalarTower Qp K₁ K₂]
    [Algebra K₁ B] [IsScalarTower Qp K₁ B]
    [Algebra K₁ BdR] [Algebra K₂ BdR] [IsScalarTower Qp K₂ BdR]
    [IsScalarTower K₁ K₂ BdR] [IsScalarTower Qp K₁ BdR]
    (PD : PeriodData H Qp K₁ K₂ B BdR) {σ : Representation LL H V} {σ' : Representation LL H V'}
    (f : V →ₗ[LL] V') (hf : ∀ g v, f (σ g v) = σ' g (f v)) (g : H) (x : V ⊗[Qp] B) :
    SumJumps.ext1 Qp B f (actVB PD σ g x) = actVB PD σ' g (SumJumps.ext1 Qp B f x) := by
  unfold actVB
  rw [SumJumps.ext1_comm f (σ g) (σ' g) (hf g)]

theorem eq_map_of_equiv_tensor (e : V ≃ₗ[LL] V')
    (S : Submodule LL (V ⊗[Qp] B)) (S' : Submodule LL (V' ⊗[Qp] B))
    (a : ∀ x ∈ S, SumJumps.ext1 Qp B e.toLinearMap x ∈ S')
    (b : ∀ x ∈ S', SumJumps.ext1 Qp B e.symm.toLinearMap x ∈ S) :
    S = S'.map (SumJumps.ext1 Qp B e.symm.toLinearMap) := by
  apply le_antisymm
  · intro x hx
    refine ⟨_, a x hx, ?_⟩
    rw [SumJumps.ext1_comp_ext1]
    convert SumJumps.ext1_id (LL := LL) x
    ext v; simp
  · rintro _ ⟨y, hy, rfl⟩
    exact b y hy

variable {ρ : Representation LL G V} {ρ' : Representation LL G V'}

theorem dpcris_map (f : V →ₗ[LL] V') (hf : ∀ g v, f (ρ g v) = ρ' g (f v)) :
    ∀ x ∈ PC.Dpcris ρ, SumJumps.ext1 Qp B f x ∈ PC.Dpcris ρ' :=
  SumJumps.dcris_map PC.PD' (ρ := PC.resH ρ) (ρ' := PC.resH ρ') f (fun h v => hf (h : G) v)

theorem eig_map (f : V →ₗ[LL] V') (hf : ∀ g v, f (ρ g v) = ρ' g (f v)) (I : Subgroup G)
    (a : I →* LLˣ) : ∀ x ∈ PC.Eig ρ I a, SumJumps.ext1 Qp B f x ∈ PC.Eig ρ' I a := by
  intro x hx
  simp only [PotCrysData.Eig, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hx ⊢
  refine ⟨dpcris_map PC f hf x hx.1, fun g => ?_⟩
  rw [← linearMap_tensorOne_comm_diagonalAction PC.PD f hf, hx.2 g, map_smul]

theorem potCrys_inertiaThrough_of_equiv (e : V ≃ₗ[LL] V') (he : ∀ g v, e (ρ g v) = ρ' g (e v)) :
    (PC.IsPotCrys ρ' → PC.IsPotCrys ρ) ∧
      ∀ S : Finset (PC.Iner →* LLˣ), PC.InertiaThrough ρ' S → PC.InertiaThrough ρ S := by
  have he' : ∀ g v, e.symm.toLinearMap (ρ' g v) = ρ g (e.symm.toLinearMap v) :=
    symm_equivariant e he
  refine ⟨fun h => isCrys_of_equiv PC.PD' (ρ := PC.resH ρ) (ρ' := PC.resH ρ') e (fun h v => he (h : G) v) h, fun S hS => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hS
  refine ⟨h1, h2, ?_⟩
  have hD : PC.Dpcris ρ = (PC.Dpcris ρ').map (SumJumps.ext1 Qp B e.symm.toLinearMap) :=
    eq_map_of_equiv_tensor e _ _ (dpcris_map PC e.toLinearMap he)
      (dpcris_map PC e.symm.toLinearMap he')
  have hE : ∀ a, PC.Eig ρ PC.Iner a =
      (PC.Eig ρ' PC.Iner a).map (SumJumps.ext1 Qp B e.symm.toLinearMap) := fun a =>
    eq_map_of_equiv_tensor e _ _ (eig_map PC e.toLinearMap he _ a)
      (eig_map PC e.symm.toLinearMap he' _ a)
  rw [hD, h3, Submodule.map_iSup]
  congr 1; ext a
  rw [Submodule.map_iSup, hE]

end PotTransport

end GlobalTheory.HTW.Rec

theorem GlobalTheory.HTW.Rec.potCrysData_transport : ∀ {G : Type} [Group G] {Qp K₀ K K₀' K' : Type} [Field Qp] [Field K₀] [Field K] [Field K₀'] [Field K']
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    [Algebra Qp K₀'] [Algebra Qp K'] [Algebra K₀' K'] [IsScalarTower Qp K₀' K']
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra K₀' B] [IsScalarTower Qp K₀' B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    [Algebra K₀' BdR] [Algebra K' BdR] [IsScalarTower Qp K' BdR]
    [IsScalarTower K₀' K' BdR] [IsScalarTower Qp K₀' BdR]
    (PC : PotCrysData G Qp K₀ K K₀' K' B BdR) {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    (ρ : Representation LL G V) (ρ' : Representation LL G V') (e : V ≃ₗ[LL] V'),
    (∀ g v, e (ρ g v) = ρ' g (e v)) →
    (PC.IsPotCrys ρ' → PC.IsPotCrys ρ) ∧ ∀ S : Finset (PC.Iner →* LLˣ), PC.InertiaThrough ρ' S → PC.InertiaThrough ρ S :=
  by
  intros
  exact GlobalTheory.HTW.Rec.potCrys_inertiaThrough_of_equiv _ ‹_› ‹_›
