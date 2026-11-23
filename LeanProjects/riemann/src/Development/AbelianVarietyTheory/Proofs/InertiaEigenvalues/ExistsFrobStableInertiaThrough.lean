import Mathlib
import Formalism.WeaklyAdmissibleFiltrations.CrystallineStableLifts.DPotCrisStableAndExistsPotentiallyCrystallineDat
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsCrystallineJumpsOfIsIsoMatrixGaloisRepresentat
open Formalism.WeaklyAdmissibleFiltrations Module TensorProduct

noncomputable section

namespace GlobalTheory

section InertialCharacters

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
    (PC : PotCrysData G Qp K₀ K K₀' K' B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem inertialEig_mem_iff (ρ : Representation LL G V) (I : Subgroup G) (a : I →* LLˣ)
    (w : V ⊗[Qp] B) :
    w ∈ PC.Eig ρ I a ↔ w ∈ PC.Dpcris ρ ∧ ∀ g : I, actVB PC.PD ρ (g : G) w = ((a g : LLˣ) : LL) • w := by
  simp [PotCrysData.Eig, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]

theorem actVB_one_apply (ρ : Representation LL G V) (x : V ⊗[Qp] B) :
    actVB PC.PD ρ 1 x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem inertialEig_inf_iSup_eq_bot (ρ : Representation LL G V) (I : Subgroup G) (b : I →* LLˣ)
    (T : Finset (I →* LLˣ)) (hb : b ∉ T) :
    PC.Eig ρ I b ⊓ (⨆ a ∈ T, PC.Eig ρ I a) = ⊥ := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert a0 T' ha0 ih =>
    have hba0 : b ≠ a0 := fun h => hb (h ▸ Finset.mem_insert_self _ _)
    have hbT : b ∉ T' := fun h => hb (Finset.mem_insert_of_mem h)
    have ih' := ih hbT
    obtain ⟨g, hg⟩ : ∃ g : I, b g ≠ a0 g := by
      by_contra h
      push_neg at h
      exact hba0 (MonoidHom.ext h)
    have hne : ((b g : LLˣ) : LL) - ((a0 g : LLˣ) : LL) ≠ 0 := by
      intro h
      exact hg (Units.ext (sub_eq_zero.mp h))
    set f : V ⊗[Qp] B →ₗ[LL] V ⊗[Qp] B :=
      actVB PC.PD ρ (g : G) - ((a0 g : LLˣ) : LL) • LinearMap.id with hf
    have hfE : ∀ (a : I →* LLˣ) w, w ∈ PC.Eig ρ I a →
        f w = (((a g : LLˣ) : LL) - ((a0 g : LLˣ) : LL)) • w := by
      intro a w hw
      rw [inertialEig_mem_iff] at hw
      simp [hf, hw.2 g, sub_smul]
    have hmapT : ∀ z ∈ (⨆ a ∈ T', PC.Eig ρ I a), f z ∈ (⨆ a ∈ T', PC.Eig ρ I a) := by
      intro z hz
      have : (⨆ a ∈ T', PC.Eig ρ I a) ≤ (⨆ a ∈ T', PC.Eig ρ I a).comap f := by
        refine iSup₂_le fun a ha w hw => ?_
        rw [Submodule.mem_comap, hfE a w hw]
        exact Submodule.smul_mem _ _ ((le_iSup₂ (f := fun a (_ : a ∈ T') => PC.Eig ρ I a) a ha) hw)
      exact this hz
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_inf] at hx
    obtain ⟨hxb, hxs⟩ := hx
    rw [Finset.iSup_insert, Submodule.mem_sup] at hxs
    obtain ⟨y, hy, z, hz, rfl⟩ := hxs
    have hfx : f (y + z) = (((b g : LLˣ) : LL) - ((a0 g : LLˣ) : LL)) • (y + z) := hfE b _ hxb
    have hfy : f y = 0 := by rw [hfE a0 y hy, sub_self, zero_smul]
    have hmem : (((b g : LLˣ) : LL) - ((a0 g : LLˣ) : LL)) • (y + z) ∈
        PC.Eig ρ I b ⊓ (⨆ a ∈ T', PC.Eig ρ I a) := by
      refine ⟨Submodule.smul_mem _ _ hxb, ?_⟩
      rw [← hfx, map_add, hfy, zero_add]
      exact hmapT z hz
    rw [ih'] at hmem
    rw [Submodule.mem_bot] at hmem ⊢
    exact (smul_eq_zero.mp hmem).resolve_left hne

theorem conj_mem_Iner (F : G) (g : G) (hg : g ∈ PC.Iner) : F⁻¹ * g * F ∈ PC.Iner := by
  intro c
  obtain ⟨c', hc'⟩ := PC.stableK₀' F c
  have hg' := hg c'
  have hFinv : PC.PD.actB F⁻¹ (algebraMap K₀' B c') = algebraMap K₀' B c := by
    rw [← hc', ← AlgEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one, AlgEquiv.one_apply]
  rw [map_mul, map_mul, AlgEquiv.mul_apply, AlgEquiv.mul_apply, hc', hg', hFinv]

def inerConj (F : G) : PC.Iner →* PC.Iner where
  toFun g := ⟨F⁻¹ * (g : G) * F, conj_mem_Iner PC F g g.2⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp [mul_assoc]

theorem exists_frobStable_inertiaThrough {ι : Type} (ρ : ι → Representation LL G V) (F : G)
    (S : Finset (PC.Iner →* LLˣ)) (h1 : 1 ∈ S) (hS : ∀ x, PC.InertiaThrough (ρ x) S) :
    ∃ Sig : Finset (PC.Iner →* LLˣ), Sig ⊆ S ∧ 1 ∈ Sig ∧ FrobStable PC.Iner F Sig ∧
      ∀ x, PC.InertiaThrough (ρ x) Sig := by
  classical
  let Sig : Finset (PC.Iner →* LLˣ) :=
    insert 1 (S.filter (fun a => ∃ x, PC.Eig (ρ x) PC.Iner a ≠ ⊥))
  have hSigS : Sig ⊆ S := by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact h1
    · exact (Finset.mem_filter.mp ha).1
  refine ⟨Sig, hSigS, Finset.mem_insert_self _ _, ?_, ?_⟩
  · intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact ⟨1, Finset.mem_insert_self _ _, fun g h _ => by simp⟩
    obtain ⟨haS, x, hx⟩ := Finset.mem_filter.mp ha
    let b : PC.Iner →* LLˣ := a.comp (inerConj PC F)
    refine ⟨b, ?_, ?_⟩
    · obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hx
      rw [inertialEig_mem_iff] at hv
      set u := actVB PC.PD (ρ x) F v with hu
      have huD : u ∈ PC.Dpcris (ρ x) := pc_Dpcris_stable PC (ρ x) F hv.1
      have hu0 : u ≠ 0 := by
        intro h
        apply hv0
        have : actVB PC.PD (ρ x) F⁻¹ u = v := by
          rw [hu, ← pc_actVB_mul, inv_mul_cancel, actVB_one_apply]
        rw [← this, h, map_zero]
      have huE : u ∈ PC.Eig (ρ x) PC.Iner b := by
        rw [inertialEig_mem_iff]
        refine ⟨huD, fun g => ?_⟩
        have e : (g : G) * F = F * (F⁻¹ * (g : G) * F) := by group
        have hc := hv.2 (inerConj PC F g)
        rw [hu, ← pc_actVB_mul, e, pc_actVB_mul]
        change actVB PC.PD (ρ x) F (actVB PC.PD (ρ x) ((inerConj PC F g : PC.Iner) : G) v) = _
        rw [hc, map_smul]
        rfl
      have hbS : b ∈ S := by
        by_contra hbS
        have hbot := inertialEig_inf_iSup_eq_bot PC (ρ x) PC.Iner b S hbS
        apply hu0
        have : u ∈ PC.Eig (ρ x) PC.Iner b ⊓ (⨆ a ∈ S, PC.Eig (ρ x) PC.Iner a) := by
          refine ⟨huE, ?_⟩
          rw [← (hS x).2.2]
          exact huD
        rw [hbot] at this
        exact (Submodule.mem_bot LL).mp this
      apply Finset.mem_insert_of_mem
      refine Finset.mem_filter.mpr ⟨hbS, x, ?_⟩
      intro h
      apply hu0
      have := huE
      rw [h] at this
      exact (Submodule.mem_bot LL).mp this
    · intro g h hh
      change a (inerConj PC F g) = a h
      congr 1
      ext
      exact hh.symm
  · intro x
    refine ⟨?_, ?_, ?_⟩
    · intro a ha g hg
      rcases Finset.mem_insert.mp ha with rfl | ha
      · rfl
      · exact (hS x).1 a (Finset.mem_filter.mp ha).1 g hg
    · intro a ha
      rcases Finset.mem_insert.mp ha with rfl | ha
      · simp
      · exact (hS x).2.1 a (Finset.mem_filter.mp ha).1
    · apply le_antisymm
      · rw [(hS x).2.2]
        refine iSup₂_le fun a ha => ?_
        by_cases h0 : PC.Eig (ρ x) PC.Iner a = ⊥
        · rw [h0]; exact bot_le
        · have haSig : a ∈ Sig := Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨ha, x, h0⟩)
          exact le_iSup₂ (f := fun a (_ : a ∈ Sig) => PC.Eig (ρ x) PC.Iner a) a haSig
      · exact iSup₂_le fun a _ => inf_le_left

end InertialCharacters

theorem frobStable_inertial_subset : ∀ {G : Type} [Group G] {Qp K₀ K K₀' K' : Type} [Field Qp] [Field K₀] [Field K] [Field K₀'] [Field K']
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
    {ι : Type} (ρ : ι → Representation LL G V) (F : G) (S : Finset (PC.Iner →* LLˣ)),
    1 ∈ S → (∀ x, PC.InertiaThrough (ρ x) S) →
    ∃ Sig : Finset (PC.Iner →* LLˣ), Sig ⊆ S ∧ 1 ∈ Sig ∧ FrobStable PC.Iner F Sig ∧
      ∀ x, PC.InertiaThrough (ρ x) Sig := by
  intros
  apply exists_frobStable_inertiaThrough <;> assumption

end GlobalTheory
