import Mathlib
import GroundTheory.ProfiniteCohomology.ShapiroDefs
import GroundTheory.ProfiniteCohomology.CoinducedModules.CohomologyCoindCokernelIsoHom
import GroundTheory.ProfiniteCohomology.CohomologyFunctoriality.QuotientToInvariantsFunctorPreservesZeroMorphism
import GroundTheory.ProfiniteCohomology.CohomologyFunctoriality.Naturality
import GroundTheory.ProfiniteCohomology.InflationRestriction.Coinduced
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits Topology

universe u

variable {k G : Type u} [CommRing k] [Group G]

section Exact

variable (U : Subgroup G)

noncomputable abbrev coindShortComplexOf (X : ShortComplex (Rep.{u} k U)) : ShortComplex (Rep.{u} k G) :=
  ShortComplex.mk (Rep.coindMap U.subtype X.f) (Rep.coindMap U.subtype X.g) (by
    ext F x
    exact congrArg (fun φ => φ.hom (F.1 x)) X.zero)

theorem shortExact_coindShortComplexOf {X : ShortComplex (Rep.{u} k U)} (hX : X.ShortExact) :
    (coindShortComplexOf U X).ShortExact := by
  have hf : Function.Injective X.f.hom := (Rep.mono_iff_injective _).1 hX.mono_f
  have hexact := hX.exact.map (forget₂ (Rep.{u} k U) (ModuleCat.{u} k))
  rw [ShortComplex.moduleCat_exact_iff] at hexact
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · rw [← ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep.{u} k G) (ModuleCat.{u} k)),
      ShortComplex.moduleCat_exact_iff]
    intro F₀ hF₀
    let F : Rep.coind U.subtype X.X₂ := F₀
    have hF : ∀ x, X.g.hom (F.1 x) = 0 := fun x =>
      congrArg (fun φ : Rep.coind U.subtype X.X₃ => φ.1 x) hF₀
    have hy : ∀ x, ∃ y, X.f.hom y = F.1 x := fun x => hexact (F.1 x) (hF x)
    choose y hy using hy
    refine ⟨(⟨y, fun u x => hf ?_⟩ : Rep.coind U.subtype X.X₁), Subtype.ext (funext hy)⟩
    rw [hy, F.2 u x, ← hy x]
    exact (Rep.hom_comm_apply X.f u (y x)).symm
  · refine (Rep.mono_iff_injective _).2 fun a b h => Subtype.ext (funext fun x => hf ?_)
    exact congrArg (fun φ : Rep.coind U.subtype X.X₂ => φ.1 x) h
  · have := hX.epi_g
    exact (Rep.coindFunctor k U.subtype).map_epi X.g

noncomputable def coindEvalOneShortComplex (X : ShortComplex (Rep.{u} k U)) :
    (coindShortComplexOf U X).map (Rep.resFunctor U.subtype) ⟶ X where
  τ₁ := coindEvalOne U X.X₁
  τ₂ := coindEvalOne U X.X₂
  τ₃ := coindEvalOne U X.X₃
  comm₁₂ := by
    ext f
    rfl
  comm₂₃ := by
    ext f
    rfl

end Exact

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (U : OpenSubgroup G)

section Naturality

@[reassoc]
theorem shapiroMap_naturality {B B' : Rep.{u} k (U : Subgroup G)} [IsDiscreteRep B]
    [IsDiscreteRep B'] (g : B ⟶ B') (n : ℕ) :
    cohomologyMap (Rep.coindMap (U : Subgroup G).subtype g) n ≫ shapiroMap U B' n =
      shapiroMap U B n ≫ cohomologyMap g n := by
  rw [← cohomologyMapAlong_id_eq_cohomologyMap, ← cohomologyMapAlong_id_eq_cohomologyMap,
    shapiroMap, shapiroMap, ← cohomologyMapAlong_comp, ← cohomologyMapAlong_comp]
  rfl

end Naturality

instance isDiscreteRep_coind_res (A : Rep.{u} k G) [IsDiscreteRep A] :
    IsDiscreteRep (Rep.coind (U : Subgroup G).subtype (Rep.res (U : Subgroup G).subtype A)) :=
  isDiscreteRep_coind U _

section Acyclic

variable (X : Type u) [AddCommGroup X] [Module k X]

instance isDiscreteRep_coind_discreteCoind :
    IsDiscreteRep (Rep.coind (U : Subgroup G).subtype (discreteCoind k (U : Subgroup G) X)) :=
  isDiscreteRep_coind U _

noncomputable def coindDiscreteCoindIso :
    Rep.coind (U : Subgroup G).subtype (discreteCoind k (U : Subgroup G) X) ≅
      discreteCoind k G X where
  hom := Rep.ofHom ⟨
    { toFun := fun F => ⟨fun x => (F.1 x) 1,
        (isLocallyConstant_coind U (discreteCoind k (U : Subgroup G) X) F).comp
          fun ψ : LocallyConstant (U : Subgroup G) X => ψ 1⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }, fun g => by
        ext F x
        rfl⟩
  inv := Rep.ofHom ⟨
    { toFun := fun φ => ⟨fun x => ⟨fun v => φ ((v : G) * x),
          φ.isLocallyConstant.comp_continuous (continuous_subtype_val.mul continuous_const)⟩,
        fun u x => by
          ext v
          simp [mul_assoc]⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }, fun g => by
        ext φ x v
        change φ ((v : G) * x * g) = φ ((v : G) * (x * g))
        rw [mul_assoc]⟩
  hom_inv_id := by
    ext F x v
    change (F.1 ((v : G) * x)) 1 = F.1 x v
    rw [show (v : G) * x = (U : Subgroup G).subtype v * x from rfl, F.2 v x]
    simp
  inv_hom_id := by
    ext φ x
    change φ (((1 : (U : Subgroup G)) : G) * x) = φ x
    simp

theorem isZero_cohomology_coind_discreteCoind (n : ℕ) :
    IsZero (cohomology (Rep.coind.{u} (U : Subgroup G).subtype
      (discreteCoind k (U : Subgroup G) X)) (n + 1)) :=
  (isZero_cohomology_discreteCoind k G X n).of_iso
    (cohomologyIsoOfIso (coindDiscreteCoindIso U X) (n + 1))

end Acyclic

section DegreeZero

variable (B : Rep.{u} k (U : Subgroup G)) [IsDiscreteRep B]

omit [IsTopologicalGroup G] [CompactSpace G] [IsDiscreteRep B] in

theorem coind_invariant_apply (f : (Rep.coind (U : Subgroup G).subtype B).ρ.invariants) (x : G) :
    f.1.1 x = f.1.1 1 := by
  have h : f.1.1 (1 * x) = f.1.1 1 :=
    congrArg (fun φ : Rep.coind (U : Subgroup G).subtype B => φ.1 1) (f.2 x)
  rwa [one_mul] at h

noncomputable def coindInvariantsEval :
    (Rep.coind (U : Subgroup G).subtype B).ρ.invariants →ₗ[k] B.ρ.invariants where
  toFun f := ⟨f.1.1 1, fun u => by
    have h := f.1.2 u 1
    simp only [Subgroup.subtype_apply, mul_one] at h
    rw [← h, coind_invariant_apply]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [IsTopologicalGroup G] [CompactSpace G] [IsDiscreteRep B] in
theorem coindInvariantsEval_bijective : Function.Bijective (coindInvariantsEval U B) := by
  refine ⟨fun f f' h => ?_, fun b => ?_⟩
  · apply Subtype.ext
    apply Subtype.ext
    funext x
    rw [coind_invariant_apply, coind_invariant_apply U B f']
    exact congrArg Subtype.val h
  · refine ⟨⟨⟨fun _ => b.1, fun u _ => (b.2 u).symm⟩, fun g => rfl⟩, rfl⟩

private theorem cocyclesIso₀_hom_comp_f {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    (A : Rep.{u} k Γ) [IsDiscreteRep A] :
    (cocyclesIso₀ A).hom ≫ ModuleCat.ofHom (invariantsToCochains₀ A) =
      (cochainsComplex A).iCycles 0 := by
  dsimp only [cocyclesIso₀, KernelFork.mapIsoOfIsLimit]
  exact (KernelFork.mapOfIsLimit_ι _ _ _).trans (Category.comp_id _)

theorem isIso_shapiroMap_zero : IsIso (shapiroMap U B 0) := by
  set ψ := cochainsMapAlong (A := Rep.coind (U : Subgroup G).subtype B) (B := B)
    (U : Subgroup G).subtype (continuous_subgroup_subtype _) (coindEvalOne (U : Subgroup G) B)
  have hψ : HomologicalComplex.cyclesMap ψ 0 = (cocyclesIso₀ _).hom ≫
      ModuleCat.ofHom (coindInvariantsEval U B) ≫ (cocyclesIso₀ B).inv := by
    have hK := cocyclesIso₀_hom_comp_f (Rep.coind (U : Subgroup G).subtype B)
    have hL := cocyclesIso₀_hom_comp_f B
    have hinj : Function.Injective ((cochainsComplex B).iCycles 0).hom :=
      (ModuleCat.mono_iff_injective _).1 inferInstance
    refine ModuleCat.hom_ext (LinearMap.ext fun z => hinj ?_)
    have e1 := congrArg (fun f => f.hom z) (HomologicalComplex.cyclesMap_i ψ 0)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e1
    rw [e1, ← hL, ← hK]
    set w := (cocyclesIso₀ (Rep.coind (U : Subgroup G).subtype B)).hom.hom z
    have e2 : (cocyclesIso₀ B).hom.hom ((cocyclesIso₀ B).inv.hom (coindInvariantsEval U B w)) =
        coindInvariantsEval U B w := by
      simp
    change (ψ.f 0).hom (invariantsToCochains₀ _ w) =
      invariantsToCochains₀ B ((cocyclesIso₀ B).hom.hom
        ((cocyclesIso₀ B).inv.hom (coindInvariantsEval U B w)))
    rw [e2]
    apply Subtype.ext
    funext x
    rfl
  haveI : IsIso (ModuleCat.ofHom (coindInvariantsEval U B)) :=
    (LinearEquiv.ofBijective _ (coindInvariantsEval_bijective U B)).toModuleIso.isIso_hom
  haveI : IsIso (HomologicalComplex.cyclesMap ψ 0) := by
    rw [hψ]
    infer_instance
  have h := CochainComplex.isoHomologyπ₀_inv_naturality ψ
  have h' : HomologicalComplex.homologyMap ψ 0 = (cochainsComplex _).isoHomologyπ₀.inv ≫
      HomologicalComplex.cyclesMap ψ 0 ≫ (cochainsComplex B).isoHomologyπ₀.hom := by
    rw [← Category.assoc, ← h, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change IsIso (HomologicalComplex.homologyMap ψ 0)
  rw [h']
  infer_instance

end DegreeZero

section Shapiro

theorem isIso_shapiroMap (n : ℕ) :
    ∀ (B : Rep.{u} k (U : Subgroup G)) [IsDiscreteRep B], IsIso (shapiroMap U B n) := by
  induction n with
  | zero => intro B _; exact isIso_shapiroMap_zero U B
  | succ n ih =>
    intro B _
    let X := coindShortComplex B
    have hX : X.ShortExact := coindShortComplex_shortExact B
    have hY : (coindShortComplexOf (U : Subgroup G) X).ShortExact :=
      shortExact_coindShortComplexOf _ hX
    have i1 : IsDiscreteRep X.X₁ := isDiscreteRep_coindShortComplex_X₁ B
    have i2 : IsDiscreteRep X.X₂ := isDiscreteRep_coindShortComplex_X₂ B
    have i3 : IsDiscreteRep X.X₃ := isDiscreteRep_coindShortComplex_X₃ B
    have j1 : IsDiscreteRep (coindShortComplexOf (U : Subgroup G) X).X₁ := isDiscreteRep_coind U X.X₁
    have j2 : IsDiscreteRep (coindShortComplexOf (U : Subgroup G) X).X₂ := isDiscreteRep_coind U X.X₂
    have j3 : IsDiscreteRep (coindShortComplexOf (U : Subgroup G) X).X₃ := isDiscreteRep_coind U X.X₃
    have hcomm : δ hY n (n + 1) rfl ≫ shapiroMap U X.X₁ (n + 1) =
        shapiroMap U X.X₃ n ≫ δ hX n (n + 1) rfl :=
      δ_comp_cohomologyMapAlong (U : Subgroup G).subtype (continuous_subgroup_subtype _)
        (coindEvalOneShortComplex (U : Subgroup G) X) hY hX n (n + 1) rfl

    have hδU : Epi (δ hX n (n + 1) rfl) :=
      (cohomology_exact₁ hX n (n + 1) rfl).epi_f
        ((isZero_cohomology_discreteCoind k (U : Subgroup G) B n).eq_of_tgt _ _)
    have hδG : Epi (δ hY n (n + 1) rfl) :=
      (cohomology_exact₁ hY n (n + 1) rfl).epi_f
        ((isZero_cohomology_coind_discreteCoind U B n).eq_of_tgt _ _)
    have e3 : IsIso (shapiroMap U X.X₃ n) := ih X.X₃
    have e2 : IsIso (shapiroMap U X.X₂ n) := ih X.X₂
    have hepi : Epi (shapiroMap U X.X₁ (n + 1)) := by
      have : Epi (δ hY n (n + 1) rfl ≫ shapiroMap U X.X₁ (n + 1)) := by
        rw [hcomm]
        exact @epi_comp _ _ _ _ _ (shapiroMap U X.X₃ n) (@IsIso.epi_of_iso _ _ _ _ _ e3)
          (δ hX n (n + 1) rfl) hδU
      exact epi_of_epi (δ hY n (n + 1) rfl) _
    have hmono : Mono (shapiroMap U X.X₁ (n + 1)) := by
      rw [ModuleCat.mono_iff_injective, injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨y, rfl⟩ := (ModuleCat.epi_iff_surjective _).1 hδG x
      have h1 : (δ hX n (n + 1) rfl).hom ((shapiroMap U X.X₃ n).hom y) = 0 := by
        have := congrArg (fun f => f.hom y) hcomm
        simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
        rw [← this, hx]
      obtain ⟨z, hz⟩ := (ShortComplex.moduleCat_exact_iff _).1
        (cohomology_exact₃ hX n (n + 1) rfl) _ h1
      obtain ⟨z', rfl⟩ := (ModuleCat.epi_iff_surjective _).1
        (@IsIso.epi_of_iso _ _ _ _ (shapiroMap U X.X₂ n) e2) z
      have h2 : (shapiroMap U X.X₃ n).hom
          ((cohomologyMap (coindShortComplexOf (U : Subgroup G) X).g n).hom z') =
          (shapiroMap U X.X₃ n).hom y := by
        have := congrArg (fun f => f.hom z') (shapiroMap_naturality U X.g n)
        simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
        exact this.trans hz
      have hinj := (ModuleCat.mono_iff_injective _).1
        (@IsIso.mono_of_iso _ _ _ _ (shapiroMap U X.X₃ n) e3)
      rw [← hinj h2]
      have := congrArg (fun f => f.hom z') (comp_δ hY n (n + 1) rfl)
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
        LinearMap.zero_apply] at this
      exact this
    show IsIso (shapiroMap U X.X₁ (n + 1))
    exact @isIso_of_mono_of_epi _ _ _ _ _ _ hmono hepi

instance isIso_shapiroMap' (B : Rep.{u} k (U : Subgroup G)) [IsDiscreteRep B] (n : ℕ) :
    IsIso (shapiroMap U B n) :=
  isIso_shapiroMap U n B

noncomputable def shapiroIso (B : Rep.{u} k (U : Subgroup G)) [IsDiscreteRep B] (n : ℕ) :
    cohomology (Rep.coind (U : Subgroup G).subtype B) n ≅ cohomology B n :=
  asIso (shapiroMap U B n)

@[simp]
theorem shapiroIso_hom (B : Rep.{u} k (U : Subgroup G)) [IsDiscreteRep B] (n : ℕ) :
    (shapiroIso U B n).hom = shapiroMap U B n :=
  rfl

end Shapiro

section Corestriction

variable (A : Rep.{u} k G) [IsDiscreteRep A]

theorem cohomologyRes_eq_coindUnit_shapiroMap (n : ℕ) :
    cohomologyRes A (U : Subgroup G) n =
      cohomologyMap (coindUnit (U : Subgroup G) A) n ≫
        shapiroMap U (Rep.res (U : Subgroup G).subtype A) n := by
  rw [← cohomologyMapAlong_id_eq_cohomologyMap, shapiroMap, ← cohomologyMapAlong_comp]
  erw [coindUnit_comp_coindEvalOne]
  rfl

omit [CompactSpace G] in
private theorem cohomologyMap_nsmul {B : Rep.{u} k G} [IsDiscreteRep B] (f : A ⟶ B) (m n : ℕ) :
    cohomologyMap (m • f) n = m • cohomologyMap f n := by
  have h : cochainsMap (m • f) = m • cochainsMap f := by
    induction m with
    | zero =>
      rw [zero_smul, zero_smul]
      exact cochainsMap_zero
    | succ m ih =>
      rw [succ_nsmul, succ_nsmul, ← ih]
      ext i c : 3
      rfl
  rw [cohomologyMap, h]
  exact (HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.up ℕ) n).map_nsmul

noncomputable def cohomologyCores (n : ℕ) :
    cohomology (Rep.res (U : Subgroup G).subtype A) n ⟶ cohomology A n :=
  inv (shapiroMap U (Rep.res (U : Subgroup G).subtype A) n) ≫
    cohomologyMap (coindTrace (U : Subgroup G) A) n

theorem cohomologyRes_comp_cohomologyCores (n : ℕ) :
    cohomologyRes A (U : Subgroup G) n ≫ cohomologyCores U A n = (U : Subgroup G).index • 𝟙 _ := by
  rw [cohomologyRes_eq_coindUnit_shapiroMap, cohomologyCores, Category.assoc, IsIso.hom_inv_id_assoc,
    ← cohomologyMap_comp, coindUnit_comp_coindTrace, cohomologyMap_nsmul, cohomologyMap_id]

end Corestriction

end GroundTheory.ProfCoh
