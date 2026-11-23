import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Edge1
import Development.AbelianVarietyTheory.Definitions.Divisors.IsGaloisCover
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OmegaPullOmegaTraceOfSecTraceOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffCoverSpec
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 KaehlerDifferential
open scoped TensorProduct

namespace UpperTheory

private theorem reduced_of_etale_proj (R S : Type) [CommRing R] [CommRing S] [Algebra R S] [IsReduced R]
    [Algebra.Etale R S] [Module.Projective R S] : IsReduced S := by
  refine ⟨fun s hs => ?_⟩
  by_contra hne
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual R S, φ s ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne ((Module.forall_dual_apply_eq_zero_iff R s).1 h)
  have hnil : φ s ∉ nilradical R := by
    rw [nilradical_eq_zero]; simpa using hφ
  rw [nilradical_eq_sInf, Ideal.mem_sInf] at hnil
  push_neg at hnil
  obtain ⟨p, hp, hsp⟩ := hnil
  haveI : p.IsPrime := hp
  let κ := p.ResidueField
  haveI : IsReduced (κ ⊗[R] S) := Algebra.FormallyUnramified.isReduced_of_field κ (κ ⊗[R] S)
  have h0 : (1 : κ) ⊗ₜ[R] s = 0 := by
    have : IsNilpotent ((Algebra.TensorProduct.includeRight : S →ₐ[R] κ ⊗[R] S) s) := hs.map _
    simpa using this.eq_zero
  have h1 := congrArg ((TensorProduct.rid R κ).toLinearMap ∘ₗ LinearMap.lTensor κ φ) h0
  simp at h1
  rw [Algebra.smul_def, mul_one] at h1
  exact hsp (Ideal.algebraMap_residueField_eq_zero.1 h1)

private theorem reduced_quot (B B' : Type) [CommRing B] [CommRing B'] [Algebra B B'] [Algebra.Etale B B']
    [Module.Projective B B'] (I : Ideal B) [IsReduced (B ⧸ I)] : IsReduced (B' ⧸ I.map (algebraMap B B')) := by
  haveI : IsReduced ((B ⧸ I) ⊗[B] B') := reduced_of_etale_proj (B ⧸ I) ((B ⧸ I) ⊗[B] B')
  have e := Algebra.TensorProduct.quotIdealMapEquivTensorQuot B' I
  haveI : IsReduced (B' ⊗[B] (B ⧸ I)) := isReduced_of_injective (Algebra.TensorProduct.comm B B' (B ⧸ I)).toRingEquiv (Algebra.TensorProduct.comm B B' (B ⧸ I)).injective
  exact isReduced_of_injective e.toRingEquiv e.injective

private theorem transfer {A A' B B' ι : Type} [CommRing A] [CommRing A'] [CommRing B] [CommRing B'] [Algebra A A']
    [Algebra.Etale A A'] [Module.Projective A A'] (eA : A ≃+* B) (eA' : A' ≃+* B') (t : ι → B) (t' : ι → B')
    (ht : ∀ j, eA' (algebraMap A A' (eA.symm (t j))) = t' j) (hr : IsReduced (B ⧸ Ideal.span (Set.range t))) :
    IsReduced (B' ⧸ Ideal.span (Set.range t')) := by
  let J : Ideal A := Ideal.span (Set.range fun j => eA.symm (t j))
  have hJ : Ideal.span (Set.range t) = J.map (eA : A →+* B) := by
    simp only [J, Ideal.map_span, ← Set.range_comp]
    congr 2
    ext j
    simp
  have eq1 : (A ⧸ J) ≃+* (B ⧸ Ideal.span (Set.range t)) := Ideal.quotientEquiv J _ eA hJ
  haveI : IsReduced (A ⧸ J) := isReduced_of_injective eq1 eq1.injective
  haveI := reduced_quot A A' J
  have hJ' : Ideal.span (Set.range t') = (J.map (algebraMap A A')).map (eA' : A' →+* B') := by
    simp only [J, Ideal.map_span, ← Set.range_comp]
    congr 2
    ext j
    simp [ht]
  have eq2 := Ideal.quotientEquiv (J.map (algebraMap A A')) _ eA' hJ'
  exact isReduced_of_injective eq2.symm eq2.symm.injective

private theorem cover_ring {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    [Algebra k X.functionField] {ι : Type} [DecidableEq ι] {U : ι → X.Opens}
    {B : Finset ι → Subalgebra k X.functionField} (h : IsAffCover p U B) (i : ι) :
    IsAffineOpen (U i) ∧ ∃ hg : genericPoint X ∈ U i, ∀ y, y ∈ B {i} ↔
      ∃ f : Γ(X, U i), (X.presheaf.germ (U i) (genericPoint X) hg).hom f = y := by
  have key : ∀ (V : X.Opens) (_ : V = ({i} : Finset ι).inf U), IsAffineOpen V ∧
      ∃ hg : genericPoint X ∈ V, ∀ y, y ∈ B {i} ↔
        ∃ f : Γ(X, V), (X.presheaf.germ V (genericPoint X) hg).hom f = y := by
    rintro V rfl
    exact ⟨h.affine _ (Finset.singleton_nonempty i), h.ne _, h.ring _ (Finset.singleton_nonempty i)⟩
  exact key (U i) Finset.inf_singleton.symm

private noncomputable def chartEquiv {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] [Algebra k X.functionField]
    (V : X.Opens) (hg : genericPoint X ∈ V) (B : Subalgebra k X.functionField)
    (h : ∀ y, y ∈ B ↔ ∃ f : Γ(X, V), (X.presheaf.germ V (genericPoint X) hg).hom f = y) : Γ(X, V) ≃+* B :=
  RingEquiv.ofBijective
    (((X.presheaf.germ V (genericPoint X) hg).hom).codRestrict B fun f => (h _).2 ⟨f, rfl⟩)
    (by
      refine ⟨fun a b e => ?_, fun y => ?_⟩
      · haveI : Nonempty V := ⟨⟨_, hg⟩⟩
        exact germ_injective_of_isIntegral X _ hg (congrArg Subtype.val e)
      · obtain ⟨f, hf⟩ := (h y.1).1 y.2
        exact ⟨f, Subtype.ext hf⟩)

end UpperTheory

theorem UpperTheory.Cb.finite_etale_function_field_germ_compat_of_smooth :
    ∀ (d : ℕ) (Z Y : Scheme.{0}) [IsIntegral Z] [IsIntegral Y] (s : Z ⟶ Sp ℂ) (s' : Y ⟶ Sp ℂ) [SmoothOfRelativeDimension d s] [SmoothOfRelativeDimension d s'] (c1 : Y ⟶ Z), c1 ≫ s = s' → IsFinite c1 → Etale c1 → ∀ [inst : Algebra ℂ Z.functionField] [inst' : Algebra ℂ Y.functionField], inst = ffAlg s → inst' = ffAlg s' → ∀ [Algebra Z.functionField Y.functionField] [IsScalarTower ℂ Z.functionField Y.functionField], (∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Y ∈ c1 ⁻¹ᵁ V) (g : Γ(Z, V)), algebraMap Z.functionField Y.functionField ((Z.presheaf.germ V (genericPoint Z) hV).hom g) = (Y.presheaf.germ (c1 ⁻¹ᵁ V) (genericPoint Y) hV').hom (c1.app V g)) → ∀ (F : Type) [Field F] [Algebra ℂ F] [Algebra F Z.functionField] [IsScalarTower ℂ F Z.functionField] [Algebra F Y.functionField] [IsScalarTower F Z.functionField Y.functionField] [IsScalarTower ℂ F Y.functionField] (x : Fin (d + 1) → F) (U : Fin (d + 1) → Z.Opens), IsFinCover ℂ Z.functionField x → IsAffCover s U (rB ℂ Z.functionField x) → IsAffCover s' (fun i => c1 ⁻¹ᵁ U i) (rB ℂ Y.functionField x) → IsReduced ((rB ℂ Z.functionField x {0}) ⧸ (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem ℂ Z.functionField x j⟩ : rB ℂ Z.functionField x {0})))) → IsReduced ((rB ℂ Y.functionField x {0}) ⧸ (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem ℂ Y.functionField x j⟩ : rB ℂ Y.functionField x {0})))) := by
  intro d Z Y _ _ s s' _ _ c1 hc hfin het inst inst' _ _ _ _ hcomp F _ _ _ _ _ _ _ x U _ hZ hY hred
  obtain ⟨hW, hg, hring⟩ := cover_ring hZ 0
  obtain ⟨-, hg', hring'⟩ := cover_ring hY 0
  letI : Algebra Γ(Z, U 0) Γ(Y, c1 ⁻¹ᵁ U 0) := (c1.app (U 0)).hom.toAlgebra
  haveI : Module.Finite Γ(Z, U 0) Γ(Y, c1 ⁻¹ᵁ U 0) := sec_finite (s := s) (s' := s') (f := c1) hW
  haveI : Algebra.Etale Γ(Z, U 0) Γ(Y, c1 ⁻¹ᵁ U 0) := sec_etale (s := s) (s' := s') (f := c1) hW
  haveI := projective_of_etale Γ(Z, U 0) Γ(Y, c1 ⁻¹ᵁ U 0)
  let eZ := chartEquiv (U 0) hg _ hring
  let eY := chartEquiv (c1 ⁻¹ᵁ U 0) hg' _ hring'
  refine transfer eZ eY _ _ (fun j => ?_) hred
  apply Subtype.ext
  obtain ⟨f, hf⟩ := eZ.surjective ⟨_, tco_mem ℂ Z.functionField x j⟩
  rw [← hf, RingEquiv.symm_apply_apply]
  have h1 : (Z.presheaf.germ (U 0) (genericPoint Z) hg).hom f = algebraMap F Z.functionField (x j.succ / x 0) :=
    congrArg Subtype.val hf
  have h2 := hcomp (U 0) hg hg' f
  rw [h1, ← IsScalarTower.algebraMap_apply] at h2
  exact h2.symm
