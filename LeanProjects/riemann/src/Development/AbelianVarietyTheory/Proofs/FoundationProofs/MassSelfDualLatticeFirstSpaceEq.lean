import Mathlib
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ClassesDoubleCosets
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SelfDualLatticeIndex
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SplittingProjection
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ColumnStabiliser
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DoubleCosetCount
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GenusMassStdOfLandherrHasse
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CosetGroupEquiv
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TotallyDefiniteMass
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StabilizerGroupMap
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EqOneOfMembership

noncomputable section

namespace GlobalTheory.ColClassNumber

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Formalism.MainNotions.StandardLattice
open GlobalTheory.IndefiniteRowSideFullHecke

theorem card_eq_index_mul_mass {G : Type} [Group G] (Γ U K : Subgroup G) (m : ℝ) (hUK : U ≤ K)
    (hidx : U.relIndex K ≠ 0) (hm : ClassesDoubleCosets.CosetMass Γ K m)
    (hfree : ∀ x γ : G, γ ∈ Γ → x⁻¹ * γ * x ∈ U → γ = 1) :
    (Nat.card (ClassSet Γ U) : ℝ) = (U.relIndex K : ℝ) * m := by
  obtain ⟨hfin, hst, hsum⟩ := hm
  letI : Fintype (ClassSet Γ K) := Fintype.ofFinite _
  have e : ∀ y : G, StabiliserCardinality.stab Γ K y ≃ stabAt Γ K y := fun y =>
    { toFun := fun γ => ⟨⟨γ.1, ((StabiliserCardinality.mem_stab Γ K y _).1 γ.2).1⟩, ((StabiliserCardinality.mem_stab Γ K y _).1 γ.2).2⟩
      invFun := fun γ => ⟨γ.1.1, (StabiliserCardinality.mem_stab Γ K y _).2 ⟨γ.1.2, γ.2⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hs : ∀ c : ClassSet Γ K, DoubleCoset.mk Γ K (Quotient.out c) = c := fun c => Quotient.out_eq' c
  have h := (GlobalTheory.Proof.DoubleCosetCountGlobalInterpolation.doubleCosetCount G Γ U K hUK ⟨hidx⟩
    (fun y => have := hst y; Finite.of_equiv _ (e y).symm)
    (fun x => (Subgroup.eq_bot_iff_forall _).2 fun γ hγ =>
      hfree x γ ((StabiliserCardinality.mem_stab Γ U x γ).1 hγ).1 ((StabiliserCardinality.mem_stab Γ U x γ).1 hγ).2)
    _ hs).2
  have h' := congrArg (fun q : ℚ => (q : ℝ)) h
  push_cast at h'
  rw [h', ← hsum _ hs]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [one_div, Nat.card_congr (e _)]

section Lattice

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
  [Algebra F E] (sp : Spaces R F E)

theorem exists_lattice (N : Submodule (𝓞 E) (Fin R.k → E)) (hfin : Module.Finite (𝓞 E) N)
    (hspan : Submodule.span E (N : Set (Fin R.k → E)) = ⊤)
    (hdual : dualSet (sp.cm.sig : E →+* E) sp.gram0 N = (N : Set (Fin R.k → E))) :
    ∃ M : Submodule (𝓞 E) (sp.X 0).V, Submodule.IsLattice E M ∧
      Formalism.HermitianLatticesTheory.IsUnimodular (sp.X 0).hT M ∧ sp.crdLat0 M = N := by
  let e : (sp.X 0).V ≃ₗ[𝓞 E] (Fin R.k → E) := sp.crd0.restrictScalars (𝓞 E)
  have hmem : ∀ x, x ∈ N.map (e.symm : (Fin R.k → E) →ₗ[𝓞 E] (sp.X 0).V) ↔ sp.crd0 x ∈ N := fun x => by
    rw [Submodule.mem_map_equiv]; rfl
  refine ⟨N.map (e.symm : (Fin R.k → E) →ₗ[𝓞 E] (sp.X 0).V), ⟨?_, ?_⟩, ?_, ?_⟩
  · exact (Module.Finite.iff_fg.1 hfin).map _
  · have : ((N.map (e.symm : (Fin R.k → E) →ₗ[𝓞 E] (sp.X 0).V) : Submodule (𝓞 E) _) : Set (sp.X 0).V) =
        (sp.crd0.symm : (Fin R.k → E) →ₗ[E] (sp.X 0).V) '' (N : Set _) := rfl
    rw [this, Submodule.span_image, hspan, Submodule.map_top, LinearEquiv.range]
  · ext x
    rw [hmem, ← SetLike.mem_coe (p := N), ← hdual]
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
      LinearMap.restrictScalars_apply, Submodule.mem_one, hmem, sp.hermitianForm_base_coordinates, dualSet, Set.mem_setOf_eq,
      RingHom.mem_range]
    constructor
    · intro h y hy
      have := h (sp.crd0.symm y) (by simpa using hy)
      simpa using this
    · intro h y hy
      exact h _ hy
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hmem x).1 hx
    · intro hy
      exact ⟨sp.crd0.symm y, (hmem _).2 (by simpa using hy), by simp⟩

end Lattice

theorem idx_pos (D : D7) : 0 < idxPi D (D.host.g 0) (D.host.g 1) := by
  have h : ∀ g k : ℕ, g.Prime → 0 < idxColLoc g k := by
    intro g k hg
    haveI : NeZero g := ⟨hg.ne_zero⟩
    haveI : Nonempty {A : GL (Fin k) (ZMod g) // IsUnitri (A : Matrix (Fin k) (Fin k) (ZMod g))} :=
      ⟨⟨1, fun i j h => by simp [h.ne'], fun i => by simp⟩⟩
    exact div_pos (Nat.cast_pos.2 Nat.card_pos) (Nat.cast_pos.2 Nat.card_pos)
  exact mul_pos (pow_pos (h _ _ (D.host.g_prime 0)) _) (pow_pos (h _ _ (D.host.g_prime 1)) _)

theorem mass_selfDualLattice_firstSpace_eq (D : D7) : letI := D.host.cmStar
    ∀ M : Submodule (𝓞 D.host.E) (D.sp.X 0).V, Submodule.IsLattice D.host.E M →
      Formalism.HermitianLatticesTheory.IsUnimodular (D.sp.X 0).hT M → Formalism.HermitianLatticesTheory.mass (D.sp.X 0).hT M = massI D D.R.k := by
  letI := D.host.cmStar
  intro M hM hu
  rw [← D.sp.rank0]
  exact GlobalTheory.genusMassStd D { D.sp.X 0 with L0 := M, standardTuple_isLattice := hM, baseLattice_isUnimodular := hu } (D.sp.X_sig 0)
    (baseSpace_posDef _ _ D.sp)

theorem classNumber (hover : SplittingProjection.SelfDualOverBase) (hindex : SelfDualLatticeIndex.StabiliserLevelIndexFormula)
    (hcos : ClassesDoubleCosets.ClassesAsDoubleCosets) (hstab : ColumnStabiliser.ColStabTrivial)
    (D : D7) (Lv : LevelData D) : ClassNumberFormula₂ D Lv := by
  letI := D.host.cmStar
  intro hg hs u hT
  obtain ⟨-, N, ⟨hfin, hspan, hdual, -⟩, -, -, hUK⟩ := hover D Lv u hT
  obtain ⟨M, hM, hu, rfl⟩ := exists_lattice D.sp N hfin hspan hdual
  have hidx := hindex D Lv u hs hT _ ⟨hfin, hspan, hdual.symm⟩ hUK
  have hm := hcos.2 D Lv u M hM hu
  rw [mass_selfDualLattice_firstSpace_eq D M hM hu] at hm
  have hrel := Subgroup.relIndex_subgroupOf (H := SelfDualLatticeIndex.levelU D Lv u)
    (SelfDualLatticeIndex.stabHat_le D (D.sp.crdLat0 M))
  have hne : (SelfDualLatticeIndex.levelU D Lv u).relIndex (SelfDualLatticeIndex.stabHat D (D.sp.crdLat0 M)) ≠ 0 := by
    intro h0
    rw [h0, Nat.cast_zero] at hidx
    exact (mul_pos (idx_pos D) (SelfDualLatticeIndex.factorT_pos D u)).ne hidx
  have h := card_eq_index_mul_mass _ ((Lv u).U.subgroupOf _) _ _ (Subgroup.comap_mono hUK)
    (hrel.trans_ne hne) hm (by
      intro x γ hγ hx
      have h1 := ColumnStabiliser.map_colStab D Lv u x
      rw [hstab D Lv u hg hs x, Subgroup.map_bot] at h1
      have h2 : γ.1 ∈ (⊥ : Subgroup _) := by
        rw [h1]
        exact ⟨hγ, ⟨_, hx, by simp [mul_assoc]⟩⟩
      exact Subtype.ext (Subgroup.mem_bot.1 h2))
  rw [Nat.card_eq_of_bijective _ (Lv u).y_bij]
  refine h.trans ?_
  rw [mul_assoc (massI D D.R.k), mul_comm (massI D D.R.k)]
  exact congrArg (· * massI D D.R.k) ((congrArg (fun n : ℕ => (n : ℝ)) hrel).trans hidx)

theorem classNumber_of_index (hover : SplittingProjection.SelfDualOverBase) (hindex : SelfDualLatticeIndex.StabiliserLevelIndexFormula)
    (D : D7) (Lv : LevelData D) : ClassNumberFormula₂ D Lv :=
  classNumber hover hindex (GlobalTheory.Proof.CosetGroupEquiv.massAsCosetSum_iff.1 GlobalTheory.Proof.TotallyDefiniteMass.massAsCosetSum)
    (GlobalTheory.Proof.StabilizerGroupMap.columnStabilisersTrivial_iff.1 GlobalTheory.Proof.EqOneOfMembership.columnStabilisersTrivial) D Lv

end GlobalTheory.ColClassNumber

end
