import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SmoothFlatAlgebraFiniteCoverDecompStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSchemeModelOfAffineSmoothChartStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCoverModelIrreducibleSpecialFibreStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GlobalTheory.SS.WeakNeronEx
open GlobalTheory.AbLaw ReciprocityTheory.ChartRestriction.G.Out

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp _ _).symm

theorem sp_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (e : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective e)

theorem away_of_irreducible (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (K : Type) [Field K] [Algebra V K] [IsFractionRing V K]
    {π : V} (hπ : Irreducible π) : IsLocalization.Away π K := by
  refine (IsLocalization.iff_of_le_of_exists_dvd (M := Submonoid.powers π) (S := K)
    (nonZeroDivisors V) (powers_le_nonZeroDivisors_of_noZeroDivisors hπ.ne_zero) ?_).mpr
    inferInstance
  intro a ha
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible
    (nonZeroDivisors.ne_zero ha) hπ
  exact ⟨π ^ n, ⟨n, rfl⟩, hn.dvd⟩

section Ev
variable {X : Scheme.{0}} {L : Type} [Field L] (a : Sp L ⟶ X)

def ev (W : X.Opens) (h : ⊤ ≤ a ⁻¹ᵁ W) : Γ(X, W) →+* L :=
  (Scheme.ΓSpecIso (CommRingCat.of L)).hom.hom.comp (a.appLE W ⊤ h).hom

theorem ev_rs {W W' : X.Opens} (e : W' ≤ W) (h : ⊤ ≤ a ⁻¹ᵁ W) (h' : ⊤ ≤ a ⁻¹ᵁ W') (f : Γ(X, W)) :
    ev a W' h' (rs X e f) = ev a W h f := by
  have := congrArg (fun q => q.hom f) (Scheme.Hom.map_appLE a h' (homOfLE e).op)
  exact congrArg (Scheme.ΓSpecIso (CommRingCat.of L)).hom.hom this

theorem ev_ne_zero {W : X.Opens} (h : ⊤ ≤ a ⁻¹ᵁ W) (f : Γ(X, W)) :
    ev a W h f ≠ 0 ↔ ⊤ ≤ a ⁻¹ᵁ X.basicOpen f := by
  have e := Scheme.basicOpen_appLE a ⊤ W h f
  rw [top_inf_eq] at e
  rw [← e, ← isUnit_iff_ne_zero]
  constructor
  · intro hu
    have : IsUnit ((a.appLE W ⊤ h).hom f) := by
      have := hu.map (Scheme.ΓSpecIso (CommRingCat.of L)).inv.hom
      simpa [ev] using this
    exact (Scheme.basicOpen_of_isUnit _ this).ge
  · intro hu
    have : IsUnit ((a.appLE W ⊤ h).hom f) :=
      RingedSpace.isUnit_of_isUnit_germ (Sp L).toRingedSpace ⊤ _ fun x hx =>
        (Scheme.mem_basicOpen _ _ x hx).1 (hu hx)
    exact this.map (Scheme.ΓSpecIso (CommRingCat.of L)).hom.hom

theorem spMap_ev {W : X.Opens} (hW : IsAffineOpen W) (h : ⊤ ≤ a ⁻¹ᵁ W) :
    spMap (ev a W h) ≫ hW.fromSpec = a := by
  have e := IsAffineOpen.SpecMap_appLE_fromSpec a hW (isAffineOpen_top _) h
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at e
  have : spMap (ev a W h) = Spec.map (Scheme.ΓSpecIso (CommRingCat.of L)).hom ≫ Spec.map (a.appLE W ⊤ h) :=
    Spec.map_comp (a.appLE W ⊤ h) _
  rw [this, Category.assoc, e, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
    Category.id_comp]
end Ev

theorem fromSpec_hom {X : Scheme.{0}} {K : Type} [CommRing K] (f : X ⟶ Sp K) {W : X.Opens} (hW : IsAffineOpen W) :
    hW.fromSpec ≫ f = spMap (cst f W) := by
  have e := IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top _) hW (le_top : W ≤ f ⁻¹ᵁ ⊤)
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp] at e
  rw [← e]
  rfl

theorem exists_min {V L : Type} [CommRing V] [IsDomain V] [ValuationRing V] [Field L] [Algebra V L]
    [IsFractionRing V L] {I : Type} [Finite I] [Nonempty I] (c : I → L) :
    ∃ i, ∀ j, ∃ t : V, c j = algebraMap V L t * c i := by
  obtain ⟨i, hi⟩ := Finite.exists_max (fun j => ValuationRing.valuation V L (c j))
  refine ⟨i, fun j => ?_⟩
  by_cases h0 : c i = 0
  · have := hi j
    simp only [h0, map_zero, le_zero_iff, Valuation.zero_iff] at this
    exact ⟨0, by simp [this]⟩
  · have : c j / c i ∈ (ValuationRing.valuation V L).integer := by
      rw [Valuation.mem_integer_iff, map_div₀]
      exact div_le_one_of_le₀ (hi j) zero_le'
    obtain ⟨t, ht⟩ := (ValuationRing.mem_integer_iff V L _).1 this
    exact ⟨t, by rw [ht, div_mul_cancel₀ _ h0]⟩

theorem exists_chart {X : Scheme.{0}} {H : LB X} {m : ℕ} (s : Fin (m + 1) → LB.Sec H)
    (hc : ⨆ i, nonzeroLocus (s i) = ⊤) (r : ∀ i, Fin (m + 1) → Γ(X, nonzeroLocus (s i)))
    (hr : ∀ i j k, rs X (inf_le_right : nonzeroLocus (s i) ⊓ H.U k ≤ H.U k) ((s j).f k) =
        rs X (inf_le_left : nonzeroLocus (s i) ⊓ H.U k ≤ nonzeroLocus (s i)) (r i j) *
          rs X (inf_le_right : nonzeroLocus (s i) ⊓ H.U k ≤ H.U k) ((s i).f k))
    {V L : Type} [CommRing V] [IsDomain V] [ValuationRing V] [Field L] [Algebra V L]
    [IsFractionRing V L] (a : Sp L ⟶ X) :
    ∃ (i : Fin (m + 1)) (h : ⊤ ≤ a ⁻¹ᵁ nonzeroLocus (s i)), ∀ j, ev a _ h (r i j) ∈ (algebraMap V L).range := by
  have hpt : ∀ W : X.Opens, a (IsLocalRing.closedPoint L) ∈ W → ⊤ ≤ a ⁻¹ᵁ W := fun W hW y _ => by
    have : y = IsLocalRing.closedPoint L := Subsingleton.elim (α := PrimeSpectrum L) _ _
    subst this
    exact hW
  have hx : a (IsLocalRing.closedPoint L) ∈ ⨆ i, nonzeroLocus (s i) := by rw [hc]; trivial
  obtain ⟨i₀, h₀⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 h₀
  have hU : ⊤ ≤ a ⁻¹ᵁ H.U k := hpt _ (X.basicOpen_le _ hk)
  have hne : ev a _ hU ((s i₀).f k) ≠ 0 := (ev_ne_zero a hU _).2 (hpt _ hk)
  obtain ⟨i, hi⟩ := exists_min (V := V) (fun j => ev a _ hU ((s j).f k))
  have hne' : ev a _ hU ((s i).f k) ≠ 0 := by
    intro h
    obtain ⟨t, ht⟩ := hi i₀
    exact hne (by simpa [h] using ht)
  have hD : ⊤ ≤ a ⁻¹ᵁ nonzeroLocus (s i) :=
    hpt _ (TopologicalSpace.Opens.mem_iSup.2 ⟨k, (ev_ne_zero a hU _).1 hne' (x := IsLocalRing.closedPoint L) trivial⟩)
  have hI : ⊤ ≤ a ⁻¹ᵁ (nonzeroLocus (s i) ⊓ H.U k) := fun y hy => ⟨hD hy, hU hy⟩
  refine ⟨i, hD, fun j => ?_⟩
  obtain ⟨t, ht⟩ := hi j
  have e := congrArg (ev a _ hI) (hr i j k)
  rw [map_mul, ev_rs a _ hU, ev_rs a _ hU, ev_rs a _ hD, ht] at e
  exact ⟨t, mul_right_cancel₀ hne' e⟩

section Alg
variable (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
  {D : Type} [CommRing D] [Algebra K D] [Algebra R D] [IsScalarTower R K D]

include K in

theorem flat_sub (B : Subalgebra R D) : Module.Flat R B := by
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, Submodule.eq_bot_iff]
  rintro x ⟨c, hc⟩
  have hu : IsUnit (algebraMap R D c) := by
    rw [IsScalarTower.algebraMap_apply R K D]
    exact (IsLocalization.map_units K c).map _
  have : algebraMap R D c * (x : D) = 0 := by
    rw [← Algebra.smul_def]
    exact congrArg Subtype.val hc
  exact Subtype.ext (hu.mul_right_eq_zero.1 this)

def gen (B : Subalgebra R D) : TensorProduct R K B →ₐ[K] D :=
  Algebra.TensorProduct.lift (Algebra.ofId K D) B.val (fun _ _ => Commute.all _ _)

omit [IsDomain R] [IsDiscreteValuationRing R] in

theorem gen_injective (B : Subalgebra R D) : Function.Injective (gen R K B) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  letI : Algebra B (TensorProduct R K B) := Algebra.TensorProduct.rightAlgebra
  have hl : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors R)) (TensorProduct R K B) :=
    IsLocalization.tensorRight K (nonZeroDivisors R)
  obtain ⟨⟨b, c⟩, e⟩ := IsLocalization.surj (Algebra.algebraMapSubmonoid B (nonZeroDivisors R)) x
  have e' := congrArg (gen R K B) e
  rw [map_mul, hx, zero_mul] at e'
  have hb : b = 0 := by
    apply Subtype.ext
    have : gen R K B (algebraMap B _ b) = (b : D) := by
      show gen R K B (1 ⊗ₜ b) = _
      simp [gen]
    rw [← this, ← e']; rfl
  rw [hb, map_zero] at e
  exact (IsLocalization.map_units (TensorProduct R K B) c).mul_left_eq_zero.1 e

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in

theorem gen_surjective {I : Type} (r : I → D)
    (h : Function.Surjective (MvPolynomial.eval₂Hom (algebraMap K D) r)) :
    Function.Surjective (gen R K (Algebra.adjoin R (Set.range r))) := by
  intro d
  obtain ⟨p, rfl⟩ := h d
  refine ⟨MvPolynomial.aeval (fun i => (1 : K) ⊗ₜ (⟨r i, Algebra.subset_adjoin ⟨i, rfl⟩⟩ :
    Algebra.adjoin R (Set.range r))) p, ?_⟩
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  simp [gen, MvPolynomial.aeval_def]

theorem smooth_away {π : R} (hπ : Irreducible π) (B : Type) [CommRing B] [Algebra R B]
    [Algebra.Smooth K (TensorProduct R K B)] : Algebra.Smooth R (Localization.Away (algebraMap R B π)) := by
  have := away_of_irreducible R K hπ
  have h₁ : Algebra.Smooth R K := Algebra.Smooth.of_isLocalization_Away π
  have h₂ : Algebra.Smooth R (TensorProduct R K B) := Algebra.Smooth.comp R K _
  letI : Algebra B (TensorProduct R K B) := Algebra.TensorProduct.rightAlgebra
  have hl : IsLocalization (Algebra.algebraMapSubmonoid B (Submonoid.powers π)) (TensorProduct R K B) :=
    IsLocalization.tensorRight K (Submonoid.powers π)
  rw [Algebra.algebraMapSubmonoid_powers] at hl
  haveI : IsScalarTower R B (TensorProduct R K B) := Algebra.TensorProduct.right_isScalarTower
  exact Algebra.Smooth.of_equiv ((IsLocalization.algEquiv (Submonoid.powers (algebraMap R B π))
    (TensorProduct R K B) (Localization.Away (algebraMap R B π))).restrictScalars R)
end Alg

theorem exists_affine (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] {X : Scheme.{0}} (f : X ⟶ Sp K) (hf : IsProjBy f) :
    ∃ (m : ℕ) (B : Fin m → Type) (_ : ∀ i, CommRing (B i)) (_ : ∀ i, Algebra R (B i))
      (u : ∀ i, Sp (TensorProduct R K (B i)) ⟶ X),
      (∀ i, Algebra.FiniteType R (B i) ∧ Module.Flat R (B i) ∧ IsOpenImmersion (u i) ∧
        u i ≫ f = spMap (algebraMap K _)) ∧
      ∀ (V L : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra R V] [Field L] [Algebra V L]
        [IsFractionRing V L] (a : Sp L ⟶ X),
        a ≫ f ≫ spMap (algebraMap R K) = spMap ((algebraMap V L).comp (algebraMap R V)) →
        ∃ (i : Fin m) (b : B i →ₐ[R] V) (ψ : TensorProduct R K (B i) →+* L), spMap ψ ≫ u i = a ∧
          ∀ x, ψ (1 ⊗ₜ x) = algebraMap V L (b x) := by
  obtain ⟨H, -, m, s, hc, hs⟩ := hf
  choose haff r hr hsurj using hs
  letI : ∀ i, Algebra K Γ(X, nonzeroLocus (s i)) := fun i => (cst f _).toAlgebra
  letI : ∀ i, Algebra R Γ(X, nonzeroLocus (s i)) := fun i => ((cst f _).comp (algebraMap R K)).toAlgebra
  haveI : ∀ i, IsScalarTower R K Γ(X, nonzeroLocus (s i)) := fun i => IsScalarTower.of_algebraMap_eq fun _ => rfl
  let e : ∀ i, TensorProduct R K (Algebra.adjoin R (Set.range (r i))) ≃ₐ[K] Γ(X, nonzeroLocus (s i)) := fun i =>
    AlgEquiv.ofBijective (gen R K _) ⟨gen_injective R K _, gen_surjective R K _ (hsurj i)⟩
  refine ⟨m + 1, fun i => Algebra.adjoin R (Set.range (r i)), inferInstance, inferInstance,
    fun i => spMap (e i).symm.toAlgHom.toRingHom ≫ (haff i).fromSpec, fun i => ⟨?_, flat_sub R K _, ?_, ?_⟩, ?_⟩
  · exact Algebra.FiniteType.adjoin_of_finite (Set.finite_range _)
  · haveI : IsIso (spMap (e i).symm.toAlgHom.toRingHom) :=
      inferInstanceAs (IsIso (Spec.map (e i).symm.toRingEquiv.toCommRingCatIso.hom))
    infer_instance
  · rw [Category.assoc, fromSpec_hom, sp_comp]
    exact congrArg spMap ((e i).symm.toAlgHom.comp_algebraMap)
  · intro V L _ _ _ _ _ _ _ a ha
    obtain ⟨i, h, hi⟩ := exists_chart s hc r hr (V := V) a
    have h₁ := spMap_ev a (haff i) h
    have h₂ : (ev a _ h).comp (algebraMap R _) = (algebraMap V L).comp (algebraMap R V) := by
      apply sp_inj
      have h₀ : a ≫ f = spMap ((ev a _ h).comp (cst f _)) := by
        rw [← sp_comp, ← fromSpec_hom f (haff i), reassoc_of% h₁]
      rw [← ha, reassoc_of% h₀, sp_comp]
      rfl
    letI : Algebra R L := ((algebraMap V L).comp (algebraMap R V)).toAlgebra
    haveI : IsScalarTower R V L := IsScalarTower.of_algebraMap_eq fun _ => rfl
    let φ : Γ(X, nonzeroLocus (s i)) →ₐ[R] L := ⟨ev a _ h, fun c => congrArg (fun q => q c) h₂⟩
    have hle : Algebra.adjoin R (Set.range (r i)) ≤ (IsScalarTower.toAlgHom R V L).range.comap φ := by
      rw [Algebra.adjoin_le_iff]
      rintro _ ⟨j, rfl⟩
      exact hi j
    let κ := AlgEquiv.ofInjective (IsScalarTower.toAlgHom R V L) (IsFractionRing.injective V L)
    refine ⟨i, κ.symm.toAlgHom.comp ((φ.comp (Subalgebra.val _)).codRestrict _ fun x => hle x.2),
      (ev a _ h).comp (e i).toAlgHom.toRingHom, ?_, fun x => ?_⟩
    · rw [← Category.assoc, sp_comp]
      refine Eq.trans ?_ h₁
      congr 2
      ext y
      simp
    · have h₃ : ∀ y, algebraMap V L (κ.symm y) = y := fun y =>
        congrArg Subtype.val (κ.apply_symm_apply y)
      refine Eq.trans ?_ (h₃ _).symm
      have h₄ : gen R K (Algebra.adjoin R (Set.range (r i))) (1 ⊗ₜ x) = x.1 := by simp [gen]
      exact congrArg (ev a _ h) h₄

theorem range_subset {V : Type} [CommRing V] [IsLocalRing V] {Y Z : Scheme.{0}} (b : Sp V ⟶ Y) (g : Z ⟶ Y)
    [IsOpenImmersion g] (h : b (IsLocalRing.closedPoint V) ∈ Set.range g) : Set.range b ⊆ Set.range g := by
  rintro _ ⟨y, rfl⟩
  exact ((IsLocalRing.specializes_closedPoint y).map b.continuous).mem_open g.isOpenEmbedding.isOpen_range h

theorem exists_weakNeron : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K], PerfectField (IsLocalRing.ResidueField R) → ∀ (A : Over (Sp K)), Smooth A.hom → IsProper A.hom → GlobalTheory.AbLaw.IsProjBy A.hom → ∃ (n : ℕ) (M : Fin n → Model R A), (∀ i, (M i).Irr) ∧ WeakNeron M := by
  intro R K _ _ _ _ _ _ hperf A hsm hpr hproj
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨m, B, _, _, u, hB, hpt⟩ := exists_affine R K A.hom hproj
  have hs : ∀ i, Algebra.Smooth R (Localization.Away (algebraMap R (B i) π)) := fun i => by
    obtain ⟨-, -, h₃, h₄⟩ := hB i
    have h₅ : Smooth (spMap (algebraMap K (TensorProduct R K (B i)))) := by rw [← h₄]; infer_instance
    rw [HasRingHomProperty.Spec_iff (P := @Smooth)] at h₅
    haveI := RingHom.smooth_algebraMap.mp h₅
    exact smooth_away R K hπ (B i)
  have h₁ := fun i => by
    haveI := (hB i).1
    haveI := (hB i).2.1
    exact GlobalTheory.T.smooth_flat_algebra_finite_cover_decomp R K π hπ hperf (B i) (hs i)
  choose n C instR instA φ hC hlift using h₁
  have h₂ := fun i k => GlobalTheory.T.exists_scheme_model_of_affine_smooth_chart R K A hsm inferInstance inferInstance (C i k) (hC i k).1
    (spMap (Algebra.TensorProduct.map (AlgHom.id K K) (φ i k)).toRingHom ≫ u i)
    (by haveI := (hC i k).2; haveI := (hB i).2.2.1; infer_instance)
    (by
      rw [Category.assoc, (hB i).2.2.2, sp_comp]
      exact congrArg spMap (AlgHom.comp_algebraMap (Algebra.TensorProduct.map (AlgHom.id K K) (φ i k))))
  choose M g hg₁ hg₂ hg₃ hg₄ using h₂
  choose p N q hN hcov using fun i k => GlobalTheory.T.exists_cover_model_irreducible_specialFibre R K A (M i k)
  let e := Fintype.equivFin (Σ (i : Fin m) (k : Fin (n i)), Fin (p i k))
  refine ⟨_, fun t => N (e.symm t).1 (e.symm t).2.1 (e.symm t).2.2, fun t => (hN _ _ _).1, ?_⟩
  intro V L _ _ _ _ _ _ _ hmax a ha
  suffices h : ∃ i k l, ∃ b : Sp V ⟶ (N i k l).Y.left, b ≫ (N i k l).Y.hom = spMap (algebraMap R V) ∧
      spMap (algebraMap V L) ≫ b = a ≫ (N i k l).j by
    obtain ⟨i, k, l, h⟩ := h
    refine ⟨e ⟨i, k, l⟩, ?_⟩
    beta_reduce
    rw [e.symm_apply_apply]
    exact h
  have hunr : Unr π V := by
    refine ⟨inferInstance, inferInstance, ?_⟩
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer, ← hmax, hπ.maximalIdeal_eq, Ideal.map_span,
      Set.image_singleton]
  obtain ⟨i, b, ψ, hψ, hb⟩ := hpt V L a ha
  obtain ⟨k, c, hc⟩ := hlift i V b hunr
  have hb₀ : (spMap c.toRingHom ≫ g i k) ≫ (M i k).Y.hom = spMap (algebraMap R V) := by
    rw [Category.assoc, hg₂, sp_comp]
    exact congrArg spMap (AlgHom.comp_algebraMap c)
  have hgen : spMap (algebraMap V L) ≫ spMap c.toRingHom ≫ g i k = a ≫ (M i k).j := by
    letI : Algebra R L := ((algebraMap V L).comp (algebraMap R V)).toAlgebra
    haveI : IsScalarTower R V L := IsScalarTower.of_algebraMap_eq fun _ => rfl
    let ψ₀ : TensorProduct R K (B i) →ₐ[R] L := ⟨ψ, fun x => by
      have := hb (algebraMap R _ x)
      rw [AlgHom.commutes] at this
      refine Eq.trans (congrArg ψ ?_) this
      exact ((Algebra.TensorProduct.includeRight : B i →ₐ[R] TensorProduct R K (B i)).commutes x).symm⟩
    let ψ' : TensorProduct R K (C i k) →ₐ[R] L := Algebra.TensorProduct.lift
      (ψ₀.comp Algebra.TensorProduct.includeLeft) ((IsScalarTower.toAlgHom R V L).comp c) fun _ _ => Commute.all _ _
    have e₁ : ψ'.toRingHom.comp (Algebra.TensorProduct.map (AlgHom.id K K) (φ i k)).toRingHom = ψ := by
      refine RingHom.ext fun x => ?_
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul x y =>
        have h₅ : c (φ i k y) = b y := congrArg (fun q => q y) hc
        show ψ' (x ⊗ₜ φ i k y) = _
        rw [Algebra.TensorProduct.lift_tmul]
        show ψ (x ⊗ₜ 1) * algebraMap V L (c (φ i k y)) = _
        rw [h₅, ← hb, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, _root_.one_mul]
    have e₂ : ψ'.toRingHom.comp (Algebra.TensorProduct.includeRight : C i k →ₐ[R] TensorProduct R K (C i k)).toRingHom =
        (algebraMap V L).comp c.toRingHom := by
      refine RingHom.ext fun x => ?_
      show ψ' (1 ⊗ₜ x) = _
      rw [Algebra.TensorProduct.lift_tmul, map_one, _root_.one_mul]
      rfl
    rw [← Category.assoc, sp_comp, ← e₂, ← sp_comp, Category.assoc, hg₃, ← Category.assoc, ← Category.assoc,
      sp_comp, e₁, hψ]
  have hsp : (spMap c.toRingHom ≫ g i k) (IsLocalRing.closedPoint V) ∈ (M i k).sp := by
    show (M i k).Y.hom ((spMap c.toRingHom ≫ g i k) _) = _
    rw [← Scheme.Hom.comp_apply, hb₀]
    haveI : IsLocalHom (algebraMap R V) := by
      apply ((IsLocalRing.local_hom_TFAE (algebraMap R V)).out 0 2).2
      exact hmax.le
    exact IsLocalRing.comap_closedPoint (algebraMap R V)
  obtain ⟨l, hl⟩ := hcov i k _ hsp
  obtain ⟨-, hq, hj⟩ := hN i k l
  have hfac := IsOpenImmersion.lift_fac (q i k l).left _ (range_subset _ _ hl)
  refine ⟨i, k, l, IsOpenImmersion.lift (q i k l).left _ (range_subset _ _ hl), ?_, ?_⟩
  · rw [← Over.w (q i k l), ← Category.assoc, hfac, hb₀]
  · rw [← cancel_mono (q i k l).left, Category.assoc, hfac, Category.assoc, hj, hgen]

end GlobalTheory.SS.WeakNeronEx
end
