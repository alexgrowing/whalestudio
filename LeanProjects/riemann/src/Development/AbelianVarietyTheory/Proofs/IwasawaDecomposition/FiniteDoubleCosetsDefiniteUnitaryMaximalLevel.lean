import Mathlib
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteClassSetHermitianUnitaryOpenLevel
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSet

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.DefiniteClassFinite

variable (L : Type) [Field L] [NumberField L] [IsCMField L]

noncomputable abbrev sig : L →ₐ[maximalRealSubfield L] L :=
  ((IsCMField.complexConj L : L ≃ₐ[maximalRealSubfield L] L) : L →ₐ[maximalRealSubfield L] L)

noncomputable def swapAd : ReciprocityTheory.Aut.AL L ≃ₐ[maximalRealSubfield L]
    TensorProduct (maximalRealSubfield L) (Af (maximalRealSubfield L)) L :=
  Algebra.TensorProduct.comm _ _ _

theorem flip_symm_tmul (a : L) (b : Af (maximalRealSubfield L)) : (swapAd L).symm (b ⊗ₜ a) = a ⊗ₜ b := rfl

theorem flip_conj (x : ReciprocityTheory.Aut.AL L) :
    swapAd L (ReciprocityTheory.Aut.conjAL L x) = sigR (Af (maximalRealSubfield L)) (sig L) (swapAd L x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

end GlobalTheory.DefiniteClassFinite

namespace GlobalTheory.DefiniteClassFinite
variable (L : Type) [Field L] [NumberField L] [IsCMField L]

noncomputable def flipGL (n : ℕ) : GL (Fin n) (ReciprocityTheory.Aut.AL L) ≃*
    GL (Fin n) (TensorProduct (maximalRealSubfield L) (Af (maximalRealSubfield L)) L) :=
  Units.mapEquiv (swapAd L).toRingEquiv.mapMatrix.toMulEquiv

theorem JR_one (n : ℕ) : JR (F := ↥(maximalRealSubfield L)) (Af (maximalRealSubfield L)) (1 : Matrix (Fin n) (Fin n) L) = 1 := by
  unfold JR
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem mem_GA_iff {n : ℕ} (g : GL (Fin n) (ReciprocityTheory.Aut.AL L)) :
    g ∈ ReciprocityTheory.Aut.GA L n ↔
      flipGL L n g ∈ HR (Af (maximalRealSubfield L)) (sig L) (1 : Matrix (Fin n) (Fin n) L) := by
  set M : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L) := (g : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L))
  have hc : Formalism.UG.cT (sigR (Af (maximalRealSubfield L)) (sig L)) (M.map (swapAd L)) =
      (ReciprocityTheory.Aut.conjT (ReciprocityTheory.Aut.conjAL L) M).map (swapAd L) := by
    ext i j; simp [Formalism.UG.cT, ReciprocityTheory.Aut.conjT, flip_conj]
  change M * ReciprocityTheory.Aut.conjT (ReciprocityTheory.Aut.conjAL L) M = 1 ↔
    Formalism.UG.cT (sigR (Af (maximalRealSubfield L)) (sig L)) (M.map (swapAd L)) *
      JR (F := ↥(maximalRealSubfield L)) (Af (maximalRealSubfield L)) (1 : Matrix (Fin n) (Fin n) L) * M.map (swapAd L) =
      JR (F := ↥(maximalRealSubfield L)) (Af (maximalRealSubfield L)) (1 : Matrix (Fin n) (Fin n) L)
  rw [hc, JR_one, mul_one]
  have key : ∀ X Y : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L),
      X.map (swapAd L) * Y.map (swapAd L) = (X * Y).map (swapAd L) := fun X Y =>
    (map_mul (swapAd L).toRingEquiv.mapMatrix X Y).symm
  rw [key, mul_eq_one_comm]
  constructor
  · intro h; rw [h]; exact Matrix.map_one _ (map_zero _) (map_one _)
  · intro h
    apply (swapAd L).toRingEquiv.mapMatrix.injective
    rw [map_one]; exact h

end GlobalTheory.DefiniteClassFinite

namespace GlobalTheory.DefiniteClassFinite
variable (L : Type) [Field L] [NumberField L] [IsCMField L]

abbrev Jn (n : ℕ) : Matrix (Fin n) (Fin n) L := 1

abbrev Hf (n : ℕ) := HA (Af (maximalRealSubfield L)) (sig L) (Jn L n)

noncomputable def back (n : ℕ) : Hf L n →* Formalism.AUTREP.GAf L n where
  toFun h := ⟨(flipGL L n).symm (HA.mat _ _ _ h), by
    rw [mem_GA_iff, MulEquiv.apply_symm_apply]; exact h.2⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (flipGL L n).symm
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul (flipGL L n).symm (HA.mat _ _ _ x) (HA.mat _ _ _ y)

noncomputable def fwd (n : ℕ) (g : Formalism.AUTREP.GAf L n) : Hf L n :=
  ⟨flipGL L n g.1, (mem_GA_iff L g.1).1 g.2⟩

theorem back_fwd (n : ℕ) (g : Formalism.AUTREP.GAf L n) : back L n (fwd L n g) = g := by
  apply Subtype.ext
  exact MulEquiv.symm_apply_apply (flipGL L n) g.1

theorem back_smul (n : ℕ) (γ : HFinIn (Af (maximalRealSubfield L)) (sig L) (Jn L n)) (h : Hf L n) :
    back L n (γ • h) = back L n γ.1 * back L n h := by
  apply Subtype.ext
  exact map_mul (flipGL L n).symm (γ.1.1) (HA.mat _ _ _ h)

theorem back_mem_GQ (n : ℕ) (γ : HFinIn (Af (maximalRealSubfield L)) (sig L) (Jn L n)) :
    back L n γ.1 ∈ ReciprocityTheory.Aut.GQ L n := by
  obtain ⟨γ0, hγ0, e⟩ := γ.2
  rw [ReciprocityTheory.Aut.GQ, Subgroup.mem_subgroupOf]
  refine ⟨γ0, ?_, ?_⟩
  · change (γ0 : Matrix (Fin n) (Fin n) L) * ReciprocityTheory.Aut.conjT _ (γ0 : Matrix (Fin n) (Fin n) L) = 1
    have h0 : Formalism.UG.cT (sig L : L →+* L) (γ0 : Matrix (Fin n) (Fin n) L) * 1 * (γ0 : Matrix (Fin n) (Fin n) L) = 1 := hγ0
    rw [mul_one] at h0
    rw [mul_eq_one_comm]
    exact h0
  · apply Units.ext
    have e' : Units.val (γ.1.1 : GL (Fin n) _) =
        Units.val (Formalism.UG.bc (inclR (F := ↥(maximalRealSubfield L)) (E := L) (Af (maximalRealSubfield L))) γ0) := by
      rw [e]; rfl
    change ((γ0 : Matrix (Fin n) (Fin n) L)).map Algebra.TensorProduct.includeLeftRingHom =
      ((γ.1.1 : GL (Fin n) _) : Matrix (Fin n) (Fin n) _).map (swapAd L).symm
    rw [e']
    ext i j
    rfl

end GlobalTheory.DefiniteClassFinite

namespace GlobalTheory.DefiniteClassFinite
variable (L : Type) [Field L] [NumberField L] [IsCMField L]

def intSet : Set (TensorProduct (maximalRealSubfield L) (Af (maximalRealSubfield L)) L) :=
  (swapAd L).symm ⁻¹' (ReciprocityTheory.Aut.ALint L : Set (ReciprocityTheory.Aut.AL L))

theorem isOpen_intSet : IsOpen (intSet L) := by
  classical
  let b0 := Module.finBasisOfFinrankEq (maximalRealSubfield L) L
    (Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield L) L)
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := L) (Finset.univ.image b0)
  let b := b0.unitsSMul (fun _ => Units.mk0 ((y : maximalRealSubfield L)) (by exact_mod_cast hy0))
  have hb : ∀ i, IsIntegral ℤ (b i) := by
    intro i
    rw [Module.Basis.unitsSMul_apply]
    have := hy _ (Finset.mem_image_of_mem b0 (Finset.mem_univ i))
    simpa [Units.smul_def, Int.cast_smul_eq_zsmul] using this
  let B := Algebra.TensorProduct.basis (Af (maximalRealSubfield L)) b
  haveI : IsModuleTopology (Af (maximalRealSubfield L))
      (TensorProduct (maximalRealSubfield L) (Af (maximalRealSubfield L)) L) := ⟨rfl⟩
  have hc : Continuous B.equivFun := IsModuleTopology.continuous_of_linearMap B.equivFun.toLinearMap
  let H : AddSubgroup (Fin 2 → Af (maximalRealSubfield L)) :=
    (ReciprocityTheory.Aut.ALint L).toAddSubgroup.comap
      ((swapAd L).symm.toRingEquiv.toAddMonoidHom.comp B.equivFun.symm.toLinearMap.toAddMonoidHom)
  have hW := GlobalTheory.AdLat.OpenLat.isOpen_integral (maximalRealSubfield L)
  have hV : (Set.univ.pi fun _ : Fin 2 => {a : Af (maximalRealSubfield L) |
      ∀ v, a v ∈ HeightOneSpectrum.adicCompletionIntegers (maximalRealSubfield L) v}) ⊆ H := by
    intro c hc'
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_setOf_eq] at hc'
    change (swapAd L).symm (B.equivFun.symm c) ∈ ReciprocityTheory.Aut.ALint L
    rw [Module.Basis.equivFun_symm_apply, map_sum]
    refine Subring.sum_mem _ fun i _ => ?_
    rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one, flip_symm_tmul]
    have : b i ⊗ₜ[maximalRealSubfield L] c i =
        (b i ⊗ₜ[maximalRealSubfield L] (1 : Af (maximalRealSubfield L))) * (1 ⊗ₜ c i) := by
      simp [Algebra.TensorProduct.tmul_mul_tmul]
    rw [this]
    exact Subring.mul_mem _ (Subring.subset_closure (Or.inl ⟨⟨b i, hb i⟩, rfl⟩))
      (Subring.subset_closure (Or.inr ⟨c i, hc' i, rfl⟩))
  have hHo : IsOpen (H : Set (Fin 2 → Af (maximalRealSubfield L))) := by
    apply AddSubgroup.isOpen_of_mem_nhds H (g := 0)
    apply Filter.mem_of_superset _ hV
    apply (isOpen_set_pi Set.finite_univ fun _ _ => hW).mem_nhds
    intro i _ v
    simp
  have : intSet L = B.equivFun ⁻¹' H := by
    ext x
    simp [intSet, H]
  rw [this]
  exact hHo.preimage hc

end GlobalTheory.DefiniteClassFinite

namespace GlobalTheory.DefiniteClassFinite
variable (L : Type) [Field L] [NumberField L] [IsCMField L]

noncomputable def Kmax (n : ℕ) : Subgroup (Hf L n) := (ReciprocityTheory.Aut.Umax L n).comap (back L n)

theorem isOpen_Kmax (n : ℕ) : IsOpen (Kmax L n : Set (Hf L n)) := by
  refine ⟨{x : GL (Fin n) (TensorProduct (maximalRealSubfield L) (Af (maximalRealSubfield L)) L) |
    ∀ i j, (x : Matrix (Fin n) (Fin n) _) i j ∈ intSet L}, ?_, ?_⟩
  · have : {x : GL (Fin n) (TensorProduct (maximalRealSubfield L) (Af (maximalRealSubfield L)) L) |
        ∀ i j, (x : Matrix (Fin n) (Fin n) _) i j ∈ intSet L} =
        ⋂ i, ⋂ j, (fun x : GL (Fin n) (TensorProduct (maximalRealSubfield L) (Af (maximalRealSubfield L)) L) =>
          (x : Matrix (Fin n) (Fin n) _) i j) ⁻¹' intSet L := by
      ext x; simp
    rw [this]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (isOpen_intSet L).preimage ((Units.continuous_val (M := Matrix (Fin n) (Fin n)
        (TensorProduct (maximalRealSubfield L) (Af (maximalRealSubfield L)) L))).matrix_elem i j)
  · ext h
    rfl

theorem herm_one (n : ℕ) : IsHermND (sig L) (Jn L n) := by
  refine ⟨fun i j => ?_, by simp⟩
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply, h, Ne.symm h]

theorem exists_finset_double_cosets_Umax (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) :
    ∃ T : Finset (Formalism.AUTREP.GAf L n), ∀ g : Formalism.AUTREP.GAf L n,
      ∃ (γ : ReciprocityTheory.Aut.GQ L n) (t : Formalism.AUTREP.GAf L n) (u : Formalism.AUTREP.GAf L n),
        t ∈ T ∧ u ∈ ReciprocityTheory.Aut.Umax L n ∧ g = (γ : Formalism.AUTREP.GAf L n) * t * u := by
  classical
  obtain ⟨S, hS⟩ := GlobalTheory.Mem.ClassFinite.exists_finset_classes _ L (sig L)
    (GlobalTheory.AdelicU.isCMExt_of_isCMField L) n (Jn L n) (herm_one L n) (Kmax L n) (isOpen_Kmax L n)
  refine ⟨S.image (back L n), fun g => ?_⟩
  obtain ⟨γ, s, hs, k, hk, e⟩ := hS (fwd L n g)
  refine ⟨⟨back L n γ.1, back_mem_GQ L n γ⟩, back L n s, back L n k,
    Finset.mem_image_of_mem _ hs, hk, ?_⟩
  have := congrArg (back L n) e
  rw [back_fwd, back_smul, map_mul, ← mul_assoc] at this
  exact this

end GlobalTheory.DefiniteClassFinite
