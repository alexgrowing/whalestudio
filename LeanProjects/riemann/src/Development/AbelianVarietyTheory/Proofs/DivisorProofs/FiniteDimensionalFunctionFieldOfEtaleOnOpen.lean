import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldMapCompConstFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NadelVanishingCanonicalAddBoundary
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.FunctionFieldEtale

theorem finiteDimensional_fractionRing_of_etale {R S K L : Type} [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S] [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
    [Algebra S L] [IsFractionRing S L] (φ : R →+* S) (hφ : φ.Etale) (ψ : K →+* L)
    (h : ∀ r, ψ (algebraMap R K r) = algebraMap S L (φ r)) :
    letI := ψ.toAlgebra; FiniteDimensional K L := by
  letI : Algebra K L := ψ.toAlgebra
  letI : Algebra R S := φ.toAlgebra
  haveI : Algebra.Etale R S := hφ
  letI : Algebra R L := (ψ.comp (algebraMap R K)).toAlgebra
  haveI : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower R S L := IsScalarTower.of_algebraMap_eq (fun r => h r)
  haveI : Module.Finite K (K ⊗[R] S) := Algebra.FormallyUnramified.finite_of_free K (K ⊗[R] S)
  let g : K ⊗[R] S →ₐ[K] L := Algebra.TensorProduct.lift (Algebra.ofId K L)
    (IsScalarTower.toAlgHom R S L) (fun _ _ => Commute.all _ _)
  haveI : Module.Finite K g.range :=
    Module.Finite.of_surjective g.rangeRestrict.toLinearMap g.rangeRestrict_surjective
  have hS : ∀ s : S, algebraMap S L s ∈ g.range := fun s => ⟨1 ⊗ₜ s, by simp [g]⟩
  have hinv : ∀ x ∈ g.range, x⁻¹ ∈ g.range := fun x hx =>
    Subalgebra.inv_mem_of_algebraic (A := g.range) (x := ⟨x, hx⟩)
      ((Algebra.IsAlgebraic.isAlgebraic (R := K) (⟨x, hx⟩ : g.range)).algHom g.range.val)
  have hsurj : Function.Surjective g := by
    intro y
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := S) y
    rw [div_eq_mul_inv]
    exact Subalgebra.mul_mem _ (hS a) (hinv _ (hS b))
  exact Module.Finite.of_surjective g.toLinearMap hsurj

theorem finiteDimensional_functionField_of_etale_on_open : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W]
    (f : M ⟶ W) [IsDominant f] (U : M.Opens), Etale (U.ι ≫ f) → (U : Set M).Nonempty →
    letI := (functionFieldMap f).toAlgebra; FiniteDimensional W.functionField M.functionField := by
  intro M W _ _ f _ U hf hU
  have hξU : genericPoint M ∈ U :=
    ((genericPoint_spec M).mem_open_set_iff U.isOpen).mpr (by simpa using hU)
  obtain ⟨V, hV, hfξV, -⟩ := exists_isAffineOpen_mem_and_subset (x := f (genericPoint M))
    (U := ⊤) trivial
  let x : U := ⟨genericPoint M, hξU⟩
  have hx : x ∈ (U.ι ≫ f) ⁻¹ᵁ V := hfξV
  obtain ⟨V', hV', hxV', hV'sub⟩ := exists_isAffineOpen_mem_and_subset hx
  have hle : V' ≤ (U.ι ≫ f) ⁻¹ᵁ V := fun _ h => hV'sub h
  let U' : M.Opens := U.ι ''ᵁ V'
  have hU' : IsAffineOpen U' := hV'.image_of_isOpenImmersion U.ι
  have hξU' : genericPoint M ∈ U' := ⟨x, hxV', rfl⟩
  have e' : U' ≤ f ⁻¹ᵁ V := by
    rintro _ ⟨y, hy, rfl⟩
    exact hV'sub hy
  haveI : Nonempty V := ⟨⟨_, hfξV⟩⟩
  haveI : Nonempty U' := ⟨⟨_, hξU'⟩⟩
  have het0 := HasRingHomProperty.appLE (P := @Etale) (f := U.ι ≫ f) hf ⟨V, hV⟩ ⟨V', hV'⟩ hle
  have key : (U.ι ≫ f).appLE V V' hle = f.appLE V U' e' := by
    rw [Scheme.Hom.comp_appLE]
    erw [Scheme.Opens.ι_appLE]
    rfl
  have het : (f.appLE V U' e').hom.Etale := by
    rw [← key]; exact het0
  haveI := functionField_isFractionRing_of_isAffineOpen W V hV
  haveI := functionField_isFractionRing_of_isAffineOpen M U' hU'
  refine finiteDimensional_fractionRing_of_etale (f.appLE V U' e').hom het (functionFieldMap f) ?_
  intro r
  have := functionFieldMap_algebraMap f (genericPoint M) (W.presheaf.germ V _ hfξV r)
  rw [Scheme.algebraMap_germ_eq_germToFunctionField] at this
  rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra]
  refine this.trans ?_
  rw [Scheme.Hom.germ_stalkMap_apply]
  haveI : Nonempty (f ⁻¹ᵁ V) := ⟨⟨_, hfξV⟩⟩
  erw [Scheme.algebraMap_germ_eq_germToFunctionField]
  show M.presheaf.germ _ _ _ (f.app V r) =
    M.presheaf.germ U' _ hξU' (M.presheaf.map (homOfLE e').op (f.app V r))
  rw [TopCat.Presheaf.germ_res_apply]

end GlobalTheory.FunctionFieldEtale
