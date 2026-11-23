import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EllPullExistsOAct
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LieMultIffFinrank

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF.LieType

theorem repr_eq_zero {k O V J : Type} [Field k] [CommRing O] [AddCommGroup V] [Module k V] [Module O V]
    [SMulCommClass O k V] (b : Module.Basis J k V) (χ : J → (O →+* k)) (hb : ∀ i a, a • b i = χ i a • b i)
    (ψ : O →+* k) (w : V) (hw : ∀ a : O, a • w = ψ a • w) (j : J) (hj : χ j ≠ ψ) : b.repr w j = 0 := by
  obtain ⟨a, ha⟩ : ∃ a, χ j a ≠ ψ a := by
    by_contra h
    push Not at h
    exact hj (RingHom.ext h)
  have e : (b.coord j).comp (DistribSMul.toLinearMap k V a) = χ j a • b.coord j := b.ext fun i => by
    by_cases h : i = j
    · subst h
      simp [hb]
    · simp [hb, Finsupp.single_eq_of_ne' h]
  have e' := LinearMap.congr_fun e w
  simp only [LinearMap.comp_apply, DistribSMul.toLinearMap_apply, hw, map_smul, LinearMap.smul_apply, smul_eq_mul,
    Module.Basis.coord_apply] at e'
  exact (mul_eq_mul_right_iff.1 e').resolve_left ha.symm

theorem lieMult_of_eigenbasis {k O : Type} [Field k] [CommRing O] {G : Over (Sp k)} [GrpObj G] [IsCommMonObj G]
    (a : OAct O G) {n : ℕ} {v : Fin n → (epsR k ⟶ G)} (hv : IsLieBasis v) (χ : Fin n → (O →+* k))
    (hχ : Function.Injective χ) (h : ∀ x i, IsLieComb (Pi.single i (χ i x)) v (v i ≫ a.act x)) :
    (∀ i, LieMult a (𝟙 _) (χ i) 1) ∧ ∀ ψ, (∀ i, χ i ≠ ψ) → LieMult a (𝟙 _) ψ 0 := by
  let b := Serre.Lie.basis a hv
  have hb : ∀ i x, x • b i = χ i x • b i := fun i x => by
    have h1 := h x i
    obtain e : v = fun i => (b i).hom := funext fun i => (Serre.Lie.hom_basis hv i).symm
    rw [e, Serre.Lie.isLieComb_iff] at h1
    refine (Serre.Lie.ext h1 : x • b i = _).trans ?_
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj]) (by simp), Pi.single_eq_same]
  refine ⟨fun i => ?_, fun ψ hψ => ?_⟩
  · have e : Serre.Lie.eig a (χ i) = Submodule.span k {b i} := by
      refine le_antisymm (fun w hw => ?_) ((Submodule.span_singleton_le_iff_mem _ _).2 (hb i))
      rw [← b.sum_repr w, Finset.sum_eq_single i (fun j _ hj => by
        rw [repr_eq_zero b χ hb (χ i) w hw j (hχ.ne hj), zero_smul]) (by simp)]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    rw [Serre.Lie.lieMult_id_iff, e]
    exact ⟨Module.finBasisOfFinrankEq _ _ (finrank_span_singleton (b.ne_zero i))⟩
  · have e : Serre.Lie.eig a ψ = ⊥ := by
      refine eq_bot_iff.2 fun w hw => ?_
      rw [Submodule.mem_bot, ← b.sum_repr w]
      exact Finset.sum_eq_zero fun j _ => by rw [repr_eq_zero b χ hb ψ w hw j (hψ j), zero_smul]
    rw [Serre.Lie.lieMult_id_iff, e]
    exact ⟨Module.Basis.empty _⟩

theorem exists_label {E K k : Type} [Field E] [NumberField E] [Field K] [CharZero K] [Field k] [IsAlgClosed k]
    (j : K →+* k) (lab : (E →+* ℂ) → (E →+* K)) (hl : Function.Injective lab) (τ : 𝓞 E →+* k) :
    ∃ t, τ = j.comp ((lab t).comp (algebraMap (𝓞 E) E)) := by
  have : CharZero k := j.charZero_iff j.injective |>.1 inferInstance
  have hτ : Function.Injective τ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_
    rw [RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
    exact RingHom.injective_int _
  have hi : Function.Injective fun t => j.comp (lab t) := fun t t' e =>
    hl (RingHom.ext fun x => j.injective (RingHom.congr_fun e x))
  have hs := ((Fintype.bijective_iff_injective_and_card _).2
    ⟨hi, (Embeddings.card E ℂ).trans (Embeddings.card E k).symm⟩).2
  obtain ⟨t, ht⟩ := hs (IsFractionRing.lift hτ : E →+* k)
  refine ⟨t, RingHom.ext fun a => ?_⟩
  exact ((RingHom.congr_fun ht _).trans (IsFractionRing.lift_algebraMap hτ a)).symm

theorem hasType_of_isLieType : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] (H : Host E) (K : Type) [Field K] [NumberField K] (A : Out.PolAV (Sp (𝓞 K))) (x : KeyIn K) (φ : x.P.A.left ⟶ A.A.left) (hf : IsPolFibre (algebraMap (𝓞 K) K) A x.P φ) (oa : A.OAct (𝓞 E)) (act : OAct (𝓞 E) A.A) (S : Set (E →+* ℂ)) (τ : Fin x.P.g ≃ S) (lab : (E →+* ℂ) → (E →+* K)) (ρ : 𝓞 K), act.act = oa.act → Function.Injective lab → (∀ t, t ∈ S ↔ lab t (H.rt : E) = (ρ : K)) → IsLieType A oa x φ τ lab → HasType H act ρ 1 0 := by
  intro E _ _ _ _ H K _ _ A x φ hf oa act S τ lab ρ hact hl hS hT k _ _ β hβ σ
  obtain ⟨act', e⟩ := ellPull_exists_oAct hf.2.1 act
  have := x.P.isAb.comm
  have := x.P.smoothDim
  have : Smooth x.P.A.hom := SmoothOfRelativeDimension.smooth x.P.g _
  let res : (E →+* ℂ) → (𝓞 E →+* K) := fun t => (lab t).comp (algebraMap (𝓞 E) E)
  have hres : Function.Injective res := fun t t' h => hl (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) h)
  obtain ⟨h1, h0⟩ := lieMult_of_eigenbasis act' x.basis (fun i => res (τ i))
    (hres.comp (Subtype.val_injective.comp τ.injective)) fun a i => by
      obtain ⟨w, hw, ew⟩ := hT a i
      obtain rfl : w = x.v i ≫ act'.act a := by
        refine Over.OverMorphism.ext (hf.2.1.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
        rw [← ew, Over.comp_left, Category.assoc, e, hact]
      exact hw
  let j : K →+* k := IsFractionRing.lift hβ
  have hj : ∀ a : 𝓞 K, j a = β a := IsFractionRing.lift_algebraMap hβ
  obtain ⟨t, rfl⟩ := exists_label j lab hl σ
  have key : ∀ n, LieMult act' (𝟙 _) (res t) n → LieMult act (spMap β) (j.comp (res t)) n := fun n h => by
    rw [← LieExt.lieMult_extend_iff j, LiePull.lieMult_pull _ _ _ _ _ _ _ act act' hf.2.1 e,
      spMap_comp_spMap] at h
    convert h using 2
    exact (RingHom.ext hj).symm
  have ht : t ∈ S ↔ j.comp (res t) H.rt = β ρ := by
    rw [hS, ← hj]
    exact j.injective.eq_iff.symm
  refine ⟨fun h => key _ ?_, fun h => key _ (h0 _ fun i hi => h (ht.1 ?_))⟩
  · simpa using h1 (τ.symm ⟨t, ht.2 h⟩)
  · rw [← hres hi]
    exact (τ i).2

end GlobalTheory.LamF.LieType
