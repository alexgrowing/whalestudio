import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GaugeUnfold
import Formalism.LocalToGlobal.GlobalTheory.GL5.Statement
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SelfDualUnramifiedPlaces
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemStabLocStdLatticeIffHtFinEqOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

namespace GlobalTheory.CompletedSelfDual

open GlobalTheory.AdelicU GlobalTheory.AdelicU.SelfDual GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces

theorem mem_maxOrder_iff_mem_intLoc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (z : Fv F v ⊗[F] E) :
    z ∈ maxOrder F E v ↔ z ∈ intLoc F E v := by
  constructor
  · intro hz
    rw [mem_intLoc_iff_absFin_le_one, absFin_le_iff]
    intro τ
    obtain ⟨p, hp, hpz⟩ := (mem_maxOrder F E v z).1 hz
    let f : v.adicCompletionIntegers F →+* (valBar F v).integer :=
      ((algebraMap (Fv F v) (FvBar F v)).comp (v.adicCompletionIntegers F).subtype).codRestrict _ fun a => by
        change absBar F v (algebraMap (Fv F v) (FvBar F v) a) ≤ 1
        rw [absBar_algebraMap]
        exact_mod_cast Valued.toNormedField.norm_le_one_iff.2 a.2
    refine (Valuation.integer.integers (valBar F v)).mem_of_integral (x := finEmb F v τ z)
      ⟨p.map f, hp.map _, ?_⟩
    have := congrArg (finEmb F v τ : Fv F v ⊗[F] E →+* FvBar F v) hpz
    rw [Polynomial.hom_eval₂, map_zero] at this
    rw [Polynomial.eval₂_map, ← this]
    congr 1
    ext a
    exact ((finEmb F v τ).commutes (a : Fv F v)).symm
  · refine intLoc_induction (p := fun z => z ∈ maxOrder F E v) (fun a ha x => ?_) (zero_mem _)
      (fun _ _ => add_mem) (fun _ => neg_mem)
    have h1 : (1 : Fv F v) ⊗ₜ[F] (x : E) ∈ maxOrder F E v := by
      letI := (intToEv F E v).toAlgebra
      exact (RingOfIntegers.isIntegral_coe x).map_of_comp_eq (algebraMap ℤ _) (inclR (F := F) (E := E) (Fv F v))
        (RingHom.ext_int _ _)
    have h2 : a ⊗ₜ[F] (1 : E) ∈ maxOrder F E v :=
      RingHom.isIntegralElem_map (intToEv F E v) (x := ⟨a, ha⟩)
    simpa using mul_mem h2 h1

theorem exists_isSelfDualLattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)), IsHermND σ J → Submodule.IsLattice E L → (∀ y : Fin n → E, y ∈ L ↔ ∀ x ∈ L, hE σ J x y ∈ (algebraMap (𝓞 E) E).range) → ∀ v : HeightOneSpectrum (𝓞 F), ∃ Lv : Submodule (GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.maxOrder F E v) (Fin n → Fv F v ⊗[F] E), GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.IsSelfDualLattice σ J v Lv ∧ ∀ y, y ∈ Lv ↔ y ∈ GlobalTheory.AdelicU.latLoc F L v := by
  intro F E _ _ _ _ _ σ n J L hJ hL hsd v
  classical
  let Lv : Submodule (maxOrder F E v) (Fin n → Fv F v ⊗[F] E) :=
    { carrier := latLoc F L v
      zero_mem' := zero_mem _
      add_mem' := fun h h' => add_mem h h'
      smul_mem' := fun c _ hy =>
        (latLoc F L v).smul_mem ⟨c.1, (mem_maxOrder_iff_mem_intLoc v _).1 c.2⟩ hy }
  have hmem : ∀ y, y ∈ Lv ↔ y ∈ latLoc F L v := fun _ => Iff.rfl
  obtain ⟨k, S, Φ, h1, hS, hΦ⟩ := exists_frame L hL
  have h2 := map_mul_eq_one (F := F) (Fv F v) h1
  have hcol : ∀ j, (fun i => S.map (inclR (F := F) (Fv F v)) i j) ∈ Lv := fun j =>
    tmul_mem_latLoc (one_mem _) (hS j)
  refine ⟨Lv, ⟨?_, ?_, fun y => ?_⟩, hmem⟩
  · refine ⟨Finset.univ.image fun j i => S.map (inclR (F := F) (Fv F v)) i j, le_antisymm ?_ fun y hy => ?_⟩
    · rw [Submodule.span_le]
      intro y hy
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hy
      exact hcol j
    · rw [eq_sum_col h2 y]
      refine sum_mem fun j _ => ?_
      exact Submodule.smul_mem _ (⟨_, (mem_maxOrder_iff_mem_intLoc v _).2
        ((mem_latLoc_iff_of_frame h1 hS hΦ v y).1 hy j)⟩ : maxOrder F E v)
        (Submodule.subset_span (Finset.mem_image.2 ⟨j, Finset.mem_univ j, rfl⟩))
  · refine eq_top_iff.2 fun y _ => ?_
    rw [eq_sum_col h2 y]
    exact sum_mem fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span (hcol j))
  · have h3 : latLoc F L v = dualLoc σ J L v := (forall_isSelfDualAt_iff hJ.2 hL).2 hsd v
    simp only [mem_maxOrder_iff_mem_intLoc]
    rw [hmem, h3]
    exact Iff.rfl

end GlobalTheory.CompletedSelfDual
