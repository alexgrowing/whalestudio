import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuliLawsCoefficientFieldChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralRuleRuleBaseChangeCoeffFieldIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCoverComplexModelsComponentsIsometriesDegre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeepLevelCoverPrincipalLevelLawsGalois
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecZEqZeroOfGenVal
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RuleBaseChangeSectionValuesSemilinear
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPins
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueFieldBaseChangePullbackStatement

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

noncomputable section
namespace GlobalTheory.CompBC
open AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct

theorem fib_irr : ∀ (K K' : Type) [Field K] [Field K'] [Algebra K K'] (X X' : AlgebraicGeometry.Scheme.{0}) (g : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of K)) (p : X' ⟶ X) (g' : X' ⟶ AlgebraicGeometry.Spec (CommRingCat.of K')), CategoryTheory.IsPullback p g' g (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap K K'))) → ∀ x : X, (letI : Algebra K (X.residueField x) := (AlgebraicGeometry.Spec.preimage (X.fromSpecResidueField x ≫ g)).hom.toAlgebra; IsDomain (TensorProduct K (X.residueField x) K')) → IsPreirreducible ((⇑p) ⁻¹' {x}) := GlobalTheory.T.residue_field_base_change_pullback

theorem surj_open : ∀ (K K' : Type) [Field K] [Field K'] [Algebra K K'] [Module.Finite K K'] (X X' : Scheme.{0})
    (g : X ⟶ Spec (CommRingCat.of K)) (p : X' ⟶ X) (g' : X' ⟶ Spec (CommRingCat.of K')),
    IsPullback p g' g (Spec.map (CommRingCat.ofHom (algebraMap K K'))) → Function.Surjective p ∧ IsOpenMap p := by
  intro K K' _ _ _ _ X X' g p g' hP
  have hfl : Flat (Spec.map (CommRingCat.ofHom (algebraMap K K'))) :=
    (HasRingHomProperty.Spec_iff (P := @Flat)).2 (RingHom.flat_algebraMap_iff.2 inferInstance)
  have hfp : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap K K'))) := by
    have : Algebra.FinitePresentation K K' := Algebra.FinitePresentation.of_finiteType.1 inferInstance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).2
      (RingHom.finitePresentation_algebraMap.2 inferInstance)
  have hsu : Surjective (Spec.map (CommRingCat.ofHom (algebraMap K K'))) := by
    refine ⟨fun x => ?_⟩
    have y : PrimeSpectrum K' := ⟨⊥, Ideal.isPrime_bot⟩
    exact ⟨y, Subsingleton.elim (α := PrimeSpectrum K) _ _⟩
  have h1 : UniversallyOpen p := MorphismProperty.of_isPullback hP.flip (UniversallyOpen.of_flat _)
  have h2 : Surjective p := MorphismProperty.of_isPullback hP.flip hsu
  exact ⟨h2.surj, p.isOpenMap⟩

theorem exists_compEquiv {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) (hc : Continuous f)
    (hs : Function.Surjective f) (hi : ∀ Z ∈ irreducibleComponents Y, IsIrreducible (f ⁻¹' Z)) :
    ∃ e : irreducibleComponents Y ≃ irreducibleComponents X, ∀ Z, (e Z : Set X) = f ⁻¹' Z := by
  have mem : ∀ Z ∈ irreducibleComponents Y, f ⁻¹' Z ∈ irreducibleComponents X := by
    intro Z hZ
    refine ⟨hi Z hZ, fun W hW hsub => ?_⟩
    have h1 : IsIrreducible (closure (f '' W)) := (hW.image f hc.continuousOn).closure
    have h2 : Z ⊆ closure (f '' W) := fun z hz => by
      obtain ⟨x, rfl⟩ := hs z
      exact subset_closure ⟨x, hsub hz, rfl⟩
    have h3 : closure (f '' W) ⊆ Z := hZ.2 h1 h2
    intro x hx
    exact h3 (subset_closure ⟨x, hx, rfl⟩)
  refine ⟨Equiv.ofBijective (fun Z => ⟨f ⁻¹' Z, mem Z Z.2⟩) ⟨fun Z Z' h => ?_, fun W => ?_⟩, fun Z => rfl⟩
  · apply Subtype.ext
    have := congrArg (fun s : irreducibleComponents X => f '' (s : Set X)) h
    simpa [Set.image_preimage_eq _ hs] using this
  · obtain ⟨Z, hZ, hWZ⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible (f '' W) (W.2.1.image f hc.continuousOn)
    refine ⟨⟨Z, hZ⟩, Subtype.ext ?_⟩
    show f ⁻¹' Z = W
    exact (W.2.2 (hi Z hZ) (Set.image_subset_iff.1 hWZ)).antisymm (Set.image_subset_iff.1 hWZ)

theorem isDomain_tensor_alg {K Ω K' : Type} [Field K] [CharZero K] [Field Ω] [Field K'] [Algebra K Ω] [Algebra K K']
    [Algebra.IsAlgebraic K K'] (h : ∀ a : Ω, IsAlgebraic K a → a ∈ (algebraMap K Ω).range) :
    IsDomain (Ω ⊗[K] K') := by
  let N := algebraicClosure K (AlgebraicClosure Ω)
  haveI : IsDomain (N ⊗[K] Ω) := (GlobalTheory.GeomConn.linearDisjoint_algebraicClosure h).isDomain
  haveI : IsAlgClosed N := IsAlgClosure.isAlgClosed K
  let j : K' →ₐ[K] N := IsAlgClosed.lift
  let φ := Algebra.TensorProduct.map j (AlgHom.id K Ω)
  have hφ : Function.Injective φ :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := Ω) j.toLinearMap j.injective
  haveI : IsDomain (K' ⊗[K] Ω) := Function.Injective.isDomain φ.toRingHom hφ
  exact (Algebra.TensorProduct.comm K Ω K').toMulEquiv.isDomain

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c c' : Coeff l}

theorem spMap_incF (hle : c.F ≤ c'.F) :
    spMap (incF c c' hle) ≫ spMap (IntermediateField.inclusion c.le).toRingHom =
      spMap (IntermediateField.inclusion c'.le).toRingHom := by
  rw [← Spec.map_comp]; rfl

variable (Xo) in

def pF (hle : c.F ≤ c'.F) : Xo.XF c' ⟶ Xo.XF c :=
  pullback.map _ _ _ _ (𝟙 _) (spMap (incF c c' hle)) (𝟙 _) (by simp) (by rw [Category.comp_id, spMap_incF])

theorem ptF_res (hle : c.F ≤ c'.F) {S : Type} [CommRing S] [Algebra c.F S] [Algebra c'.F S]
    (h : AlgOver c c' hle S) (y : FrPt Xo c' S) : ptF y ≫ pF Xo hle = ptF (y.res hle h) := by
  apply pullback.hom_ext
  · erw [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, Category.comp_id, pullback.lift_fst]; rfl
  · erw [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, pullback.lift_snd]
    rw [← Spec.map_comp]; congr 1; ext a; exact h a

theorem ptF_frMap {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] {φ : S →ₐ[c.F] T}
    {y : FrPt Xo c S} {z : FrPt Xo c T} (h : FrMap φ y z) : ptF z = spMap φ.toRingHom ≫ ptF y := by
  apply pullback.hom_ext
  · erw [Category.assoc, pullback.lift_fst, pullback.lift_fst, h.1]
  · erw [Category.assoc, pullback.lift_snd, pullback.lift_snd]
    rw [← Spec.map_comp]; congr 1; ext a; exact (φ.commutes a).symm

theorem isPullback_pF (hle : c.F ≤ c'.F) :
    IsPullback (pF Xo hle) (pullback.snd Xo.s (spMap (IntermediateField.inclusion c'.le).toRingHom))
      (strK (Xo := Xo) (c := c)) (spMap (incF c c' hle)) := by
  refine IsPullback.of_right ?_ (by erw [pullback.lift_snd]) (IsPullback.of_hasPullback _ _)
  have e1 : pF Xo hle ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) =
      pullback.fst Xo.s (spMap (IntermediateField.inclusion c'.le).toRingHom) := by erw [pullback.lift_fst, Category.comp_id]
  rw [e1, spMap_incF]
  exact IsPullback.of_hasPullback _ _

theorem kap_closed (hac : FnAlgClosed Xo c) (Z : Comp Xo c) (a : kap Z) (ha : IsAlgebraic c.F a) :
    a ∈ (algebraMap c.F (kap Z)).range := by
  have h1 : IsAlgebraic c.F (algebraMap (kap Z) (Om Z) a) := ha.algebraMap
  obtain ⟨b, hb⟩ := hac Z _ h1
  refine ⟨b, (algebraMap (kap Z) (Om Z)).injective ?_⟩
  rw [← hb, IsScalarTower.algebraMap_apply c.F (kap Z) (Om Z)]

theorem finite_incF (hle : c.F ≤ c'.F) :
    letI : Algebra c.F c'.F := (incF c c' hle).toAlgebra
    Module.Finite c.F c'.F := by
  letI : Algebra c.F c'.F := (incF c c' hle).toAlgebra
  haveI : IsScalarTower ℚ c.F c'.F := ⟨fun a b x => by
    show (incF c c' hle) ((a • b : c.F)) * x = a • ((incF c c' hle b) * x)
    rw [map_rat_smul, smul_mul_assoc]⟩
  haveI := c'.fin
  exact Module.Finite.of_restrictScalars_finite ℚ c.F c'.F

theorem preimage_irr (hle : c.F ≤ c'.F) (hac : FnAlgClosed Xo c) (Z : Comp Xo c) :
    IsIrreducible (pF Xo hle ⁻¹' (Z : Set (Xo.XF c))) := by
  letI : Algebra c.F c'.F := (incF c c' hle).toAlgebra
  haveI : Module.Finite c.F c'.F := finite_incF hle
  have hP : IsPullback (pF Xo hle) (pullback.snd Xo.s (spMap (IntermediateField.inclusion c'.le).toRingHom))
      (strK (Xo := Xo) (c := c)) (Spec.map (CommRingCat.ofHom (algebraMap c.F c'.F))) := isPullback_pF hle
  obtain ⟨hs, ho⟩ := surj_open c.F c'.F _ _ _ _ _ hP
  have hZ : (Z : Set (Xo.XF c)) = closure {genPt Z} := by
    rw [genPt, IsIrreducible.genericPoint_closure_eq, (isClosed_of_mem_irreducibleComponents _ Z.2).closure_eq]
  have hdom : IsDomain (kap Z ⊗[c.F] c'.F) := isDomain_tensor_alg (kap_closed hac Z)
  have hpre := fib_irr c.F c'.F _ _ _ _ _ hP (genPt Z) hdom
  rw [hZ, ho.preimage_closure_eq_closure_preimage (pF Xo hle).continuous]
  refine IsIrreducible.closure ⟨?_, hpre⟩
  obtain ⟨x, hx⟩ := hs (genPt Z)
  exact ⟨x, hx⟩

theorem comp_equiv (hle : c.F ≤ c'.F) (hac : FnAlgClosed Xo c) :
    ∃ eC : Comp Xo c ≃ Comp Xo c', ∀ Z, ((eC Z : Set (Xo.XF c'))) = pF Xo hle ⁻¹' (Z : Set (Xo.XF c)) := by
  letI : Algebra c.F c'.F := (incF c c' hle).toAlgebra
  have hs : Function.Surjective (pF Xo hle) := by
    haveI : Module.Finite c.F c'.F := finite_incF hle
    exact (surj_open c.F c'.F _ _ _ _ _ (isPullback_pF hle)).1
  exact exists_compEquiv _ (pF Xo hle).continuous hs fun Z hZ => preimage_irr hle hac ⟨Z, hZ⟩

set_option synthInstance.maxHeartbeats 400000 in

theorem comp_bc_genVal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c c' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (hle : c.F ≤ c'.F), FnAlgClosed Xo c → ∃ eC : Comp Xo c ≃ Comp Xo c', ∀ (Z : Comp Xo c) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, (GlobalTheory.CompHt.genVal (eC Z) (GlobalTheory.FieldBC.rulBC hle f) = 0 ↔ GlobalTheory.CompHt.genVal Z f = 0) := by
  intro E _ _ _ H Dw l Xo c c' hle hac
  obtain ⟨eC, heC⟩ := comp_equiv hle hac
  refine ⟨eC, fun Z a n f hf => ?_⟩
  have hf' : f ∈ secZ Xo c (fun i => (ex Dw a n i : ℤ)) := by rw [secZ_nat]; exact hf
  have hBC := (GlobalTheory.FieldBC.rulBC_sec_val_linear E H Dw l Xo c c' hle).1 a n f hf
  have hg' : GlobalTheory.FieldBC.rulBC hle f ∈ secZ Xo c' (fun i => (ex Dw a n i : ℤ)) := by rw [secZ_nat]; exact hBC.1
  rw [genVal_eq_zero_iff E H Dw l Xo c' (eC Z) _ _ hg']
  constructor
  · intro h0
    have hG : GenFrEx Xo c := (Reg.genFrEx_and_genFromTest E H Dw l Xo c).1
    rw [genVal_apply hG]
    let y := genFr hG Z
    let L := AlgebraicClosure (Om Z)
    letI : Algebra c.F c'.F := (incF c c' hle).toAlgebra
    haveI : Module.Finite c.F c'.F := finite_incF hle
    let j : c'.F →ₐ[c.F] L := IsAlgClosed.lift
    letI : Algebra c'.F L := j.toRingHom.toAlgebra
    have hAO : AlgOver c c' hle L := fun a => j.commutes a
    let φ : Om Z →ₐ[c.F] L := IsScalarTower.toAlgHom c.F (Om Z) L
    obtain ⟨z, hz⟩ := GlobalTheory.FlagTan.exists_frMap φ y
    have h1 := h0 L (z.ext hle hAO) (fun s => by
      show ptF (z.ext hle hAO) s ∈ ((eC Z : Comp Xo c') : Set (Xo.XF c'))
      rw [heC Z]
      show (ptF (z.ext hle hAO) ≫ pF Xo hle) s ∈ (Z : Set (Xo.XF c))
      rw [ptF_res hle hAO, FrPt.res_ext, ptF_frMap hz]
      exact liesOn_genFr hG Z _)
    rw [hBC.2 L hAO, FrPt.res_ext, GlobalTheory.FlagTan.evR_frMap hf.1 hz] at h1
    exact φ.toRingHom.injective (a₁ := evC hG Z f) (a₂ := 0) (by rw [map_zero]; exact h1)
  · intro h0 S _ _ y hy
    letI := GlobalTheory.FieldBC.resAlg hle S
    rw [hBC.2 S (fun _ => rfl) y]
    refine (genVal_eq_zero_iff E H Dw l Xo c Z _ f hf').1 h0 S (y.res hle (fun _ => rfl)) (fun s => ?_)
    rw [← ptF_res hle (fun _ => rfl) y]
    have := hy s
    rw [heC Z] at this
    exact this

end GlobalTheory.CompBC
