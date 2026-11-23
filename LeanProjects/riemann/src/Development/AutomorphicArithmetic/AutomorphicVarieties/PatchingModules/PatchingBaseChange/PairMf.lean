import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FinDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.AlgebraMapEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FinE
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.GammaOneGammaZeroHomogeneousCocyclesFinite
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

theorem UpperTheory.V.Pa.BC.pair_mf :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [IsLocalRing O] [Finite (ResidueField O)] [CharP (ResidueField O) l] [Algebra ℤ_[l] O] (n : ℕ) (r : Resid F O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B), PhiCond F.G₀ l → Finite (ResidueField B) ∧ (∃ (χ : Fin n → F.G₀ →* (ResidueField B)ˣ) (h : ℕ), u.D.map (residue B) = GDet.ofChars χ ∧ UpperTheory.V.CA.MultFree χ h) ∧ ∀ Z : Set (MonoidAlgebra B F.G₀), ∃ s : Finset F.G₀, ∀ y : MonoidAlgebra B F.G₀, ∃ c : F.G₀ → B, y - ∑ g ∈ s, MonoidAlgebra.single g (c g) ∈ u.D.chBar Z := by
  intro l _ F O _ _ _ _ _ n r B _ _ _ u hPhi
  haveI : CompactSpace F.G₀ :=
    isCompact_iff_compactSpace.mp (Subgroup.isClosed_of_isOpen _ F.η_open).isCompact
  let e : ResidueField O ≃+* ResidueField B :=
    RingEquiv.ofBijective (ResidueField.map (algebraMap O B)) (resMap_bijective O B)
  haveI hfin : Finite (ResidueField B) := Finite.of_equiv _ e.toEquiv
  haveI : CharP (ResidueField B) l :=
    charP_of_injective_ringHom (f := (e : ResidueField O →+* ResidueField B)) e.injective l
  have hE : Function.Injective (Units.map (e : ResidueField O →* ResidueField B)) :=
    Units.map_injective (f := (e : ResidueField O →* ResidueField B)) e.injective
  let χ : Fin n → F.G₀ →* (ResidueField B)ˣ :=
    fun i => (Units.map (e : ResidueField O →* ResidueField B)).comp (r.chib i)
  have hker : ∀ i, (χ i).ker = (r.chib i).ker := by
    intro i
    ext g
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    show Units.map (e : ResidueField O →* ResidueField B) (r.chib i g) = 1 ↔ r.chib i g = 1
    rw [← map_one (Units.map (e : ResidueField O →* ResidueField B)), hE.eq_iff]
  have hopen : ∀ i, IsOpen ((χ i).ker : Set F.G₀) := fun i => by
    rw [hker]
    exact r.chib_open i
  have hinj : Function.Injective χ := by
    intro i j hij
    exact r.chib_inj (MonoidHom.ext fun g => hE (DFunLike.congr_fun hij g))
  have hres : (residue B) = (e : ResidueField O →+* ResidueField B).comp (res O B : B →+* ResidueField O) :=
    RingHom.ext fun b => (e.apply_symm_apply (residue B b)).symm
  obtain ⟨-, hcomp, -, -⟩ := UpperTheory.V.CA.d_gmap u.D
  obtain ⟨-, -, -, hrep⟩ := UpperTheory.V.CA.d_gmap (GDet.ofRep (diagRep r.chib))
  have hmap : u.D.map (residue B) = GDet.ofChars χ := by
    rw [hres, ← hcomp, u.red]
    show (GDet.ofRep (diagRep r.chib)).map _ = GDet.ofRep (GDet.diagRep χ)
    rw [hrep]
    congr 1
    ext g i j
    simp [diagRep, GDet.diagRep, χ, Matrix.diagonal_apply]
    split_ifs <;> simp
  obtain ⟨h, hmf⟩ := UpperTheory.V.CA.exists_multFree_of_phiCond_of_injective_chars l χ hPhi hopen hinj
  refine ⟨hfin, ⟨χ, h, hmap, hmf⟩, fun Z => ?_⟩
  obtain ⟨⟨s, -, hs⟩, -, -⟩ := UpperTheory.V.CA.finE u.D χ u.cont hmap hmf Z
  refine ⟨s, fun y => ?_⟩
  have hy : u.D.toQuot Z y ∈ Submodule.span B
      ((fun g ↦ (u.D.toQuot Z) (MonoidAlgebra.single g 1)) '' (s : Set F.G₀)) := by
    rw [hs]
    exact Submodule.mem_top
  obtain ⟨c, hc, hcy⟩ := (Finsupp.mem_span_image_iff_linearCombination B).mp hy
  rw [Finsupp.linearCombination_apply_of_mem_supported B hc] at hcy
  refine ⟨c, ?_⟩
  have hz : u.D.toQuot Z (y - ∑ g ∈ s, MonoidAlgebra.single g (c g)) = 0 := by
    rw [map_sub, map_sum, ← hcy, sub_eq_zero]
    refine Finset.sum_congr rfl (fun g _ => ?_)
    rw [← map_smul, MonoidAlgebra.smul_single', mul_one]
  rw [TwoSidedIdeal.mem_iff]
  exact (u.D.chBar Z).ringCon.eq.mp hz
