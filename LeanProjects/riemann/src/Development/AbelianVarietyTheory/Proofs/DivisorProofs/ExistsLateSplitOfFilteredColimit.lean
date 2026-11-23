import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZModTorsorIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyFiniteBaseChangeFilteredColimitStatement
open CategoryTheory Limits TensorProduct

noncomputable section
namespace GlobalTheory.SplitColim

variable {J : Type} [SmallCategory J] [IsFiltered J] {F : J ⥤ CommRingCat.{0}} {c : Cocone F}

theorem eventually_map_eq_zero (hc : IsColimit c) {k : J} (x : F.obj k)
    (hx : (c.ι.app k).hom x = 0) :
    ∃ (k₀ : J) (f₀ : k ⟶ k₀), ∀ (k' : J) (f : k₀ ⟶ k'), (F.map (f₀ ≫ f)).hom x = 0 := by
  have hc' := isColimitOfPreserves (forget _) hc
  have h0 : (c.ι.app k).hom x = (c.ι.app k).hom 0 := by rw [hx, map_zero]
  obtain ⟨k₀, f₀, e⟩ := (Types.FilteredColimit.isColimit_eq_iff' hc' x 0).1 (by exact h0)
  refine ⟨k₀, f₀, fun k' f => ?_⟩
  have e' : (F.map f₀).hom x = 0 := by simpa using e
  rw [Functor.map_comp, CommRingCat.hom_comp, RingHom.comp_apply, e', map_zero]

theorem eventually_map_eq_zero_finite (hc : IsColimit c) {k : J} {κ : Type} [Fintype κ]
    (x : κ → F.obj k) (hx : ∀ i, (c.ι.app k).hom (x i) = 0) :
    ∃ (k₀ : J) (f₀ : k ⟶ k₀), ∀ (k' : J) (f : k₀ ⟶ k') (i : κ), (F.map (f₀ ≫ f)).hom (x i) = 0 := by
  classical
  suffices H : ∀ S : Finset κ, ∃ (k₀ : J) (f₀ : k ⟶ k₀), ∀ (k' : J) (f : k₀ ⟶ k'),
      ∀ i ∈ S, (F.map (f₀ ≫ f)).hom (x i) = 0 by
    obtain ⟨k₀, f₀, h⟩ := H Finset.univ
    exact ⟨k₀, f₀, fun k' f i => h k' f i (Finset.mem_univ i)⟩
  intro S
  induction S using Finset.induction_on with
  | empty => exact ⟨k, 𝟙 k, fun _ _ i hi => absurd hi (Finset.notMem_empty i)⟩
  | insert a S _ ih =>
    obtain ⟨k₀, f₀, h⟩ := GlobalTheory.TorsorColim.eventually_and
      (fun k' (g : k ⟶ k') => (F.map g).hom (x a) = 0)
      (fun k' (g : k ⟶ k') => ∀ i ∈ S, (F.map g).hom (x i) = 0)
      (eventually_map_eq_zero hc (x a) (hx a)) ih
    refine ⟨k₀, f₀, fun k' f i hi => ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact (h k' f).1
    · exact (h k' f).2 i hi

theorem exists_stage_rep (hc : IsColimit c) (k₁ : J) {ι : Type} [Finite ι] (t : ι → c.pt) :
    ∃ (K : J) (h : k₁ ⟶ K) (u : ι → F.obj K), ∀ i, (c.ι.app K).hom (u i) = t i := by
  classical
  have hc' := isColimitOfPreserves (forget _) hc
  choose jx x hx using fun i : ι => Types.jointly_surjective_of_isColimit hc' (t i)
  haveI := Fintype.ofFinite ι
  obtain ⟨K, hK⟩ := IsFiltered.sup_objs_exists (insert k₁ (Finset.univ.image jx))
  obtain ⟨h⟩ := hK (Finset.mem_insert_self k₁ _)
  have hm : ∀ i, Nonempty (jx i ⟶ K) := fun i =>
    hK (Finset.mem_insert_of_mem (Finset.mem_image_of_mem jx (Finset.mem_univ i)))
  refine ⟨K, h, fun i => (F.map (hm i).some).hom (x i), fun i => ?_⟩
  have h1 := hx i
  have h2 := congr(($(c.w (hm i).some)).hom (x i))
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h2
  rw [h2]
  exact h1

end GlobalTheory.SplitColim

namespace GlobalTheory.SplitColim

variable {J : Type} [SmallCategory J] [IsFiltered J] {F : J ⥤ CommRingCat.{0}} {c : Cocone F}

theorem exists_late_solution (hc : IsColimit c) (k₁ : J) {ι κ : Type} [Finite ι] [Fintype κ]
    (P : κ → MvPolynomial ι (F.obj k₁)) (t : ι → c.pt)
    (ht : ∀ i, MvPolynomial.eval₂ (c.ι.app k₁).hom t (P i) = 0) :
    ∃ (k₀ : J) (f₀ : k₁ ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k), ∃ u : ι → F.obj k,
      ∀ i, MvPolynomial.eval₂ (F.map (f₀ ≫ f)).hom u (P i) = 0 := by
  obtain ⟨K, h, u, hu⟩ := exists_stage_rep hc k₁ t
  have hx : ∀ i, (c.ι.app K).hom (MvPolynomial.eval₂ (F.map h).hom u (P i)) = 0 := by
    intro i
    rw [MvPolynomial.eval₂_comp_left]
    have e1 : (c.ι.app K).hom.comp (F.map h).hom = (c.ι.app k₁).hom := by
      rw [← CommRingCat.hom_comp, c.w h]
    have e2 : ⇑(c.ι.app K).hom ∘ u = t := funext hu
    rw [e1, e2]; exact ht i
  obtain ⟨k₀, f₀, h0⟩ := eventually_map_eq_zero_finite hc _ hx
  refine ⟨k₀, h ≫ f₀, fun k f => ⟨fun a => (F.map (f₀ ≫ f)).hom (u a), fun i => ?_⟩⟩
  have := h0 k f i
  rw [MvPolynomial.eval₂_comp_left, ← CommRingCat.hom_comp, ← Functor.map_comp] at this
  rw [Category.assoc]
  exact this

theorem exists_late_linear (hc : IsColimit c) (k₁ : J) (M : Type) [AddCommGroup M]
    [Module (F.obj k₁) M] [Module.FinitePresentation (F.obj k₁) M] (m : M) :
    letI : Algebra (F.obj k₁) c.pt := (c.ι.app k₁).hom.toAlgebra
    ∀ σ : M →ₗ[F.obj k₁] c.pt, σ m = 1 →
    ∃ (k₀ : J) (f₀ : k₁ ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k),
      letI : Algebra (F.obj k₁) (F.obj k) := (F.map (f₀ ≫ f)).hom.toAlgebra
      ∃ σk : M →ₗ[F.obj k₁] F.obj k, σk m = 1 := by
  letI : Algebra (F.obj k₁) c.pt := (c.ι.app k₁).hom.toAlgebra
  intro σ hσ
  classical
  obtain ⟨s, hs, K, hK⟩ := Module.FinitePresentation.out (R := F.obj k₁) (M := M)
  set π := Finsupp.linearCombination (F.obj k₁) (Subtype.val : s → M) with hπdef
  have hπ : Function.Surjective π := by
    rw [← LinearMap.range_eq_top, hπdef, Finsupp.range_linearCombination, Subtype.range_coe_subtype]
    simpa using hs
  obtain ⟨e, he⟩ := hπ m
  have hπapp : ∀ {T : Type} [AddCommGroup T] [Module (F.obj k₁) T] (g : M →ₗ[F.obj k₁] T)
      (v : s →₀ F.obj k₁), g (π v) = ∑ x, v x • g x := by
    intro T _ _ g v
    rw [hπdef, Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (fun i => by simp), map_sum]
    simp
  let lin : (s →₀ F.obj k₁) → MvPolynomial s (F.obj k₁) :=
    fun v => ∑ x, MvPolynomial.C (v x) * MvPolynomial.X x
  have evlin : ∀ {T : Type} [CommRing T] (φ : F.obj k₁ →+* T) (u : s → T) (v : s →₀ F.obj k₁),
      MvPolynomial.eval₂ φ u (lin v) = ∑ x, φ (v x) * u x := by
    intro T _ φ u v; simp [lin, MvPolynomial.eval₂_sum]
  let P : Option K → MvPolynomial s (F.obj k₁) := fun o => o.elim (lin e - 1) (fun v => lin v.1)
  have hKker : ∀ v ∈ K, π v = 0 := fun v hv => by
    have : v ∈ Submodule.span (F.obj k₁) (K : Set (s →₀ F.obj k₁)) := Submodule.subset_span hv
    rw [hK] at this
    exact this
  obtain ⟨k₀, f₀, hsol⟩ := exists_late_solution hc k₁ P (fun x => σ x) (by
    intro o
    cases o with
    | none =>
      change MvPolynomial.eval₂ _ _ (lin e - 1) = 0
      rw [MvPolynomial.eval₂_sub, MvPolynomial.eval₂_one, evlin, sub_eq_zero, ← hσ, ← he, hπapp σ e]
      rfl
    | some v =>
      change MvPolynomial.eval₂ _ _ (lin v.1) = 0
      rw [evlin]
      have := hπapp σ v.1
      rw [hKker v.1 v.2, map_zero] at this
      rw [this]
      rfl)
  refine ⟨k₀, f₀, fun k f => ?_⟩
  letI : Algebra (F.obj k₁) (F.obj k) := (F.map (f₀ ≫ f)).hom.toAlgebra
  obtain ⟨u, hu⟩ := hsol k f
  let φ := Finsupp.linearCombination (F.obj k₁) u
  have hφ : ∀ v : s →₀ F.obj k₁, φ v = MvPolynomial.eval₂ (F.map (f₀ ≫ f)).hom u (lin v) := by
    intro v
    rw [evlin, Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    · rfl
    · intro i; simp
  have hle : LinearMap.ker π ≤ LinearMap.ker φ := by
    rw [← hK, Submodule.span_le]
    intro v hv
    simp only [SetLike.mem_coe, LinearMap.mem_ker]
    rw [hφ]
    exact hu (some ⟨v, hv⟩)
  refine ⟨((LinearMap.ker π).liftQ φ hle).comp
    (π.quotKerEquivOfSurjective hπ).symm.toLinearMap, ?_⟩
  have hq : (π.quotKerEquivOfSurjective hπ).symm m = Submodule.Quotient.mk e := by
    rw [LinearEquiv.symm_apply_eq, LinearMap.quotKerEquivOfSurjective_apply_mk, he]
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, hq, Submodule.liftQ_apply, hφ]
  have := hu none
  change MvPolynomial.eval₂ _ _ (lin e - 1) = 0 at this
  rw [MvPolynomial.eval₂_sub, MvPolynomial.eval₂_one, sub_eq_zero] at this
  exact this

end GlobalTheory.SplitColim

namespace GlobalTheory.SplitColim

theorem exists_late_split_of_isColimit :
    ∀ (J : Type) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{0}) (c : Cocone F),
    IsColimit c → ∀ (j : J) (A : Type) [CommRing A] [Algebra (F.obj j) A]
    [Algebra.FinitePresentation (F.obj j) A],
    (letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra;
      Module.Finite c.pt (c.pt ⊗[F.obj j] A) ∧
        ∃ τ : (c.pt ⊗[F.obj j] A) →ₗ[c.pt] c.pt, τ 1 = 1) →
    ∃ (k₀ : J) (f₀ : j ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k),
      letI : Algebra (F.obj j) (F.obj k) := (F.map (f₀ ≫ f)).hom.toAlgebra;
      ∃ τ : (F.obj k ⊗[F.obj j] A) →ₗ[F.obj k] F.obj k, τ 1 = 1 := by
  intro J _ _ F c hc j A _ _ _ h
  letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra
  obtain ⟨hfin, τ, hτ⟩ := h
  obtain ⟨k₁, f₁, hk₁⟩ := GlobalTheory.T.eventually_finite_baseChange_filtered_colimit J F c hc j A hfin
  have hfin₁ := hk₁ k₁ (𝟙 k₁)
  rw [Category.comp_id] at hfin₁
  letI : Algebra (F.obj j) (F.obj k₁) := (F.map f₁).hom.toAlgebra
  letI : Algebra (F.obj k₁) c.pt := (c.ι.app k₁).hom.toAlgebra
  haveI : IsScalarTower (F.obj j) (F.obj k₁) c.pt := IsScalarTower.of_algebraMap_eq (fun x => by
    change (c.ι.app j).hom x = (c.ι.app k₁).hom ((F.map f₁).hom x)
    rw [← c.w f₁]; rfl)
  haveI : Module.Finite (F.obj k₁) (F.obj k₁ ⊗[F.obj j] A) := hfin₁
  haveI : Module.FinitePresentation (F.obj k₁) (F.obj k₁ ⊗[F.obj j] A) :=
    (Module.FinitePresentation.iff_finitePresentation_of_finite _ _).2 inferInstance
  let g : A →ₗ[F.obj j] c.pt :=
    (τ.restrictScalars (F.obj j)).comp (TensorProduct.mk (F.obj j) c.pt A 1)
  let σ : (F.obj k₁ ⊗[F.obj j] A) →ₗ[F.obj k₁] c.pt := LinearMap.liftBaseChange (F.obj k₁) g
  have hσ : σ 1 = 1 := by
    rw [Algebra.TensorProduct.one_def, LinearMap.liftBaseChange_tmul, one_smul]
    change τ (1 ⊗ₜ 1) = 1
    rw [← Algebra.TensorProduct.one_def]; exact hτ
  obtain ⟨k₀, f₀, hk₀⟩ := exists_late_linear hc k₁ _ (1 : F.obj k₁ ⊗[F.obj j] A) σ hσ
  refine ⟨k₀, f₁ ≫ f₀, fun k f => ?_⟩
  letI : Algebra (F.obj j) (F.obj k) := (F.map ((f₁ ≫ f₀) ≫ f)).hom.toAlgebra
  letI : Algebra (F.obj k₁) (F.obj k) := (F.map (f₀ ≫ f)).hom.toAlgebra
  haveI : IsScalarTower (F.obj j) (F.obj k₁) (F.obj k) := IsScalarTower.of_algebraMap_eq (fun x => by
    change (F.map ((f₁ ≫ f₀) ≫ f)).hom x = (F.map (f₀ ≫ f)).hom ((F.map f₁).hom x)
    rw [Category.assoc, Functor.map_comp, CommRingCat.hom_comp, RingHom.comp_apply])
  obtain ⟨σk, hσk⟩ := hk₀ k f
  refine ⟨LinearMap.liftBaseChange (F.obj k)
    ((σk.restrictScalars (F.obj j)).comp (TensorProduct.mk (F.obj j) (F.obj k₁) A 1)), ?_⟩
  rw [Algebra.TensorProduct.one_def, LinearMap.liftBaseChange_tmul, one_smul]
  change σk (1 ⊗ₜ 1) = 1
  rw [← Algebra.TensorProduct.one_def]; exact hσk

end GlobalTheory.SplitColim
