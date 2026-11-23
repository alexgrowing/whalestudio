import Mathlib
import GroundTheory.GlobalFields.IdeleGroups.SIdeleGroups.Places
import GroundTheory.GlobalFields.IdeleGroups.LocalHerbrand
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleCohomology.IsDiscreteRepCoindStabRep
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleCohomology.ExistsSIdelesCohomologyEqZero
import GroundTheory.ProfiniteCohomology.InflationRestriction.Coinduced
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits IsDedekindDomain NumberField GroundTheory.Global GroundTheory.Global.IdeleGroup
  GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange

open scoped Pointwise

section PiUnits

variable {G X : Type} [Group G] {U : X → Type} [∀ x, CommGroup (U x)]
  [MulDistribMulAction G (∀ x, U x)]

noncomputable def piUnitsRep : Representation ℤ G (∀ x, Additive (U x)) where
  toFun g := AddMonoidHom.toIntLinearMap
    { toFun := fun y x => Additive.ofMul ((g • fun x => (y x).toMul) x)
      map_zero' := funext fun x => congrArg (fun f : ∀ x, U x => Additive.ofMul (f x)) (smul_one g)
      map_add' := fun y z => funext fun x =>
        congrArg (fun f : ∀ x, U x => Additive.ofMul (f x))
          (smul_mul' g (fun x => (y x).toMul) (fun x => (z x).toMul)) }
  map_one' := LinearMap.ext fun y => funext fun x =>
    congrArg (fun f : ∀ x, U x => Additive.ofMul (f x)) (one_smul G fun x => (y x).toMul)
  map_mul' g h := LinearMap.ext fun y => funext fun x =>
    congrArg (fun f : ∀ x, U x => Additive.ofMul (f x)) (mul_smul g h fun x => (y x).toMul)

theorem piUnitsRep_apply (g : G) (y : ∀ x, Additive (U x)) (x : X) :
    piUnitsRep g y x = Additive.ofMul ((g • fun x => (y x).toMul) x) :=
  rfl

end PiUnits

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K))

section Representation

variable (L) in

noncomputable abbrev finiteUnitsAboveRep :
    Representation ℤ Gal(L/K) (∀ w : PlacesOver L v, Additive (w.1.adicCompletion L)ˣ) :=
  piUnitsRep

theorem finiteUnitsAbove_smul_apply_of_eq (σ : Gal(L/K))
    (y : (w : PlacesOver L v) → (w.1.adicCompletion L)ˣ) (w w' : PlacesOver L v)
    (h : w' = σ • w) :
    (((σ • y) w' : (w'.1.adicCompletion L)ˣ) : w'.1.adicCompletion L) =
      galEquiv v σ w.1 w'.1 (by rw [h]; rfl) (y w) := by
  subst h
  exact finiteUnitsAbove_smul_apply v σ y w

theorem permutesFactors_finiteUnitsAboveRep : PermutesFactors (finiteUnitsAboveRep L v) := by
  intro σ f w hf
  apply Additive.toMul.injective
  apply Units.ext
  change (((σ • fun x => (f x).toMul) (σ • w) : ((σ • w).1.adicCompletion L)ˣ) :
    (σ • w).1.adicCompletion L) = 1
  rw [finiteUnitsAbove_smul_apply, hf]
  exact map_one _

noncomputable def finiteProjAboveRep : ideleRep K L ⟶ Rep.of (finiteUnitsAboveRep L v) :=
  Rep.ofHom ⟨AddMonoidHom.toIntLinearMap
    { toFun := fun x w => Additive.ofMul (finiteProjAbove v x.toMul w)
      map_zero' := by
        funext w
        change Additive.ofMul (finiteProjAbove v 1 w) = 0
        rw [map_one]
        rfl
      map_add' := fun x y => by
        funext w
        change Additive.ofMul (finiteProjAbove v (x.toMul * y.toMul) w) = _
        rw [map_mul]
        rfl },
    fun σ => LinearMap.ext fun x => by
      funext w
      change Additive.ofMul (finiteProjAbove v (σ • x.toMul) w) = _
      rw [finiteProjAbove_smul]
      rfl⟩

@[simp]
theorem finiteProjAboveRep_hom_apply (x : ideleRep K L) (w : PlacesOver L v) :
    (finiteProjAboveRep v).hom x w = Additive.ofMul (finiteProjAbove v x.toMul w) :=
  rfl

noncomputable def finiteEmbedAboveRep : Rep.of (finiteUnitsAboveRep L v) ⟶ ideleRep K L :=
  Rep.ofHom ⟨AddMonoidHom.toIntLinearMap
    { toFun := fun y => Additive.ofMul (finiteEmbedAbove v fun w => (y w).toMul)
      map_zero' := by
        change Additive.ofMul (finiteEmbedAbove v 1) = 0
        rw [map_one]
        rfl
      map_add' := fun y z => by
        change Additive.ofMul (finiteEmbedAbove v ((fun w => (y w).toMul) * fun w => (z w).toMul)) = _
        rw [map_mul]
        rfl },
    fun σ => LinearMap.ext fun y => by
      change Additive.ofMul (finiteEmbedAbove v (σ • fun w => (y w).toMul)) = _
      rw [finiteEmbedAbove_smul]
      rfl⟩

@[simp]
theorem finiteEmbedAboveRep_hom_apply (y : ∀ w : PlacesOver L v, Additive (w.1.adicCompletion L)ˣ) :
    (finiteEmbedAboveRep v).hom y = Additive.ofMul (finiteEmbedAbove v fun w => (y w).toMul) :=
  rfl

theorem finiteEmbedAboveRep_comp_finiteProjAboveRep :
    finiteEmbedAboveRep (L := L) v ≫ finiteProjAboveRep (L := L) v = 𝟙 _ := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro y
  funext w
  change Additive.ofMul (finiteProjAbove v (finiteEmbedAbove v fun w => (y w).toMul) w) = y w
  rw [finiteProjAbove_finiteEmbedAbove]
  rfl

theorem finiteEmbedAboveRep_comp_finiteProjAboveRep_of_ne {v v' : HeightOneSpectrum (𝓞 K)}
    (h : v' ≠ v) : finiteEmbedAboveRep (L := L) v ≫ finiteProjAboveRep (L := L) v' = 0 := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro y
  funext w
  change Additive.ofMul (finiteProjAbove v' (finiteEmbedAbove v fun w => (y w).toMul) w) = 0
  rw [finiteProjAbove_finiteEmbedAbove_of_ne h]
  rfl

end Representation

section Decomposition

variable (w : PlacesOver L v)

omit [NumberField K] [NumberField L] in

theorem mem_stabilizer_iff_smul_eq (σ : Gal(L/K)) :
    σ ∈ MulAction.stabilizer Gal(L/K) w.1.asIdeal ↔ σ • w = w := by
  rw [MulAction.mem_stabilizer_iff, Subtype.ext_iff, coe_smul_placesOver,
    HeightOneSpectrum.ext_iff, smul_asIdeal]

omit [NumberField K] in

theorem galHom_eq_decomposition (σ : MulAction.stabilizer Gal(L/K) w.1.asIdeal)
    (h : w.1 = (σ : Gal(L/K)) • w.1) (x : w.1.adicCompletion L) :
    galHom (σ : Gal(L/K)) w.1 w.1 h x = σ • x := by
  rw [decomposition_smul_def]
  exact congrFun (congrArg DFunLike.coe (ringHom_ext_adicCompletion w.1 (continuous_galHom _ _ _ h)
    (continuous_adicCompletionRingHomOf _ _) fun y => by
      rw [galHom_algebraMap, adicCompletionRingHomOf_algebraMap])) x

theorem stabRep_finiteUnitsAboveRep (σ : MulAction.stabilizer Gal(L/K) w.1.asIdeal)
    (a : Additive (w.1.adicCompletion L)ˣ) :
    stabRep (finiteUnitsAboveRep L v) (permutesFactors_finiteUnitsAboveRep v) w
        (MulAction.stabilizer Gal(L/K) w.1.asIdeal) (mem_stabilizer_iff_smul_eq v w) σ a =
      Representation.ofMulDistribMulAction (MulAction.stabilizer Gal(L/K) w.1.asIdeal)
        (w.1.adicCompletion L)ˣ σ a := by
  classical
  rw [stabRep_apply]
  apply Additive.toMul.injective
  apply Units.ext
  have hw : w = (σ : Gal(L/K)) • w := ((mem_stabilizer_iff_smul_eq v w σ).1 σ.2).symm
  simp only [piUnitsRep_apply, toMul_ofMul]
  rw [finiteUnitsAbove_smul_apply_of_eq v (σ : Gal(L/K)) _ w w hw, galEquiv_apply,
    galHom_eq_decomposition]
  simp only [Pi.single_eq_same]
  rfl

noncomputable def stabRepFiniteIso :
    Rep.of (stabRep (finiteUnitsAboveRep L v) (permutesFactors_finiteUnitsAboveRep v) w
        (MulAction.stabilizer Gal(L/K) w.1.asIdeal) (mem_stabilizer_iff_smul_eq v w)) ≅
      Rep.ofMulDistribMulAction (MulAction.stabilizer Gal(L/K) w.1.asIdeal)
        (w.1.adicCompletion L)ˣ :=
  Rep.mkIso (Representation.Equiv.mk (LinearEquiv.refl ℤ _) fun σ =>
    LinearMap.ext fun a => stabRep_finiteUnitsAboveRep v w σ a)

variable [IsGalois K L]

noncomputable def finiteShapiroIso (n : ℕ) :
    cohomology (Rep.of (finiteUnitsAboveRep L v)) n ≅
      cohomology (Rep.ofMulDistribMulAction (MulAction.stabilizer Gal(L/K) w.1.asIdeal)
        (w.1.adicCompletion L)ˣ) n :=
  orbitShapiroIso (permutesFactors_finiteUnitsAboveRep v)
      ⟨MulAction.stabilizer Gal(L/K) w.1.asIdeal, isOpen_discrete _⟩
      (mem_stabilizer_iff_smul_eq v w) n ≪≫
    cohomologyIsoOfIso (stabRepFiniteIso v w) n

end Decomposition

end GroundTheory.ProfCoh
