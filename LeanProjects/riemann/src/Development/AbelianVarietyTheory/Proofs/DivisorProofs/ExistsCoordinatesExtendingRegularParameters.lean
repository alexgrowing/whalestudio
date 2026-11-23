import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotangentImagesLinearIndependent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBaseFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanOneTmulEqTop
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

open scoped TensorProduct

namespace GlobalTheory.CoordExt

theorem formallySmooth_of_charZero (F K : Type) [Field F] [CharZero F] [Field K] [Algebra F K] :
    Algebra.FormallySmooth F K := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis F K
  haveI := hs.isAlgebraic_field
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  haveI : CharZero (IntermediateField.adjoin F (Set.range ((↑) : s → K))) :=
    charZero_of_injective_algebraMap (algebraMap F _).injective
  haveI : Algebra.IsSeparable (IntermediateField.adjoin F (Set.range ((↑) : s → K))) K :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable hs.1

theorem span_D_algebraMap_eq_top (F A R : Type) [Field F] [CommRing A] [CommRing R]
    [Algebra F A] [Algebra A R] [Algebra F R] [IsScalarTower F A R] (P : Ideal A) [P.IsPrime]
    [IsLocalization.AtPrime R P] :
    Submodule.span R (Set.range fun y : A => KaehlerDifferential.D F R (algebraMap A R y)) = ⊤ := by
  set S := Submodule.span R (Set.range fun y : A => KaehlerDifferential.D F R (algebraMap A R y))
  rw [eq_top_iff, ← KaehlerDifferential.span_range_derivation, Submodule.span_le]
  rintro _ ⟨r, rfl⟩
  obtain ⟨⟨y, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl r
  have hu : IsUnit (algebraMap A R s) := IsLocalization.map_units R s
  obtain ⟨v, hv⟩ := hu.exists_left_inv
  have key : algebraMap A R s • KaehlerDifferential.D F R (IsLocalization.mk' R y s) =
      KaehlerDifferential.D F R (algebraMap A R y) -
        IsLocalization.mk' R y s • KaehlerDifferential.D F R (algebraMap A R s) := by
    rw [eq_sub_iff_add_eq, add_comm, ← Derivation.leibniz, IsLocalization.mk'_spec]
  have hmem : algebraMap A R s • KaehlerDifferential.D F R (IsLocalization.mk' R y s) ∈ S := by
    rw [key]
    exact sub_mem (Submodule.subset_span ⟨y, rfl⟩)
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, rfl⟩))
  have : KaehlerDifferential.D F R (IsLocalization.mk' R y s) =
      v • (algebraMap A R s • KaehlerDifferential.D F R (IsLocalization.mk' R y s)) := by
    rw [smul_smul, hv, one_smul]
  change _ ∈ S
  rw [this]
  exact Submodule.smul_mem _ _ hmem

theorem span_tmul_eq_top {R M : Type} [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
    {ι : Type} (f : ι → M) (hf : Submodule.span R (Set.range f) = ⊤) :
    Submodule.span (IsLocalRing.ResidueField R)
      (Set.range fun i => (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] f i) = ⊤ := by
  first
  | exact @_root_.GlobalTheory.TensorUnitSpanTop.main
  | exact _root_.GlobalTheory.TensorUnitSpanTop.main
  | (apply _root_.GlobalTheory.TensorUnitSpanTop.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.TensorUnitSpanTop.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TensorUnitSpanTop.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TensorUnitSpanTop.main ..)

end GlobalTheory.CoordExt

open GlobalTheory.CoordExt in

theorem GlobalTheory.exists_coords_extending_regularParams : ∀ (F A R : Type) [Field F] [CharZero F] [CommRing A] [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsRegularLocalRing R] [Algebra F A] [Algebra A R] [Algebra F R] [IsScalarTower F A R] (P : Ideal A) [P.IsPrime] [IsLocalization.AtPrime R P] (n : ℕ) [Module.Free R Ω[R⁄F]] [Module.Finite R Ω[R⁄F]], Module.finrank R Ω[R⁄F] = n → ∀ (m : ℕ) (a : Fin m → A), ReciprocityTheory.AnForm.R.FinalTheorems.Rsp R m (fun i => algebraMap A R (a i)) → ∃ (x : Fin n → A) (e : Fin m ↪ Fin n), (∀ j, x (e j) = a j) ∧ ∃ bs : Module.Basis (Fin n) R Ω[R⁄F], ∀ i, bs i = KaehlerDifferential.D F R (algebraMap A R (x i)) := by
  classical
  intro F A R _ _ _ _ _ _ _ _ _ _ _ P _ _ n _ _ hn m a hrsp
  haveI : Algebra.FormallySmooth F (IsLocalRing.ResidueField R) := formallySmooth_of_charZero F _
  set r : Fin m → R := fun i => algebraMap A R (a i) with hr_def
  have hr : ∀ i, r i ∈ IsLocalRing.maximalIdeal R := fun i => hrsp.1 ▸ Ideal.subset_span ⟨i, rfl⟩

  have hcot : LinearIndependent (IsLocalRing.ResidueField R) (fun i =>
      ((IsLocalRing.maximalIdeal R).toCotangent ⟨r i, hr i⟩ : IsLocalRing.CotangentSpace R)) := by
    have hfr : Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) = m := by
      have := (IsRegularLocalRing.iff_finrank_cotangentSpace R).1 inferInstance
      rw [← hrsp.2] at this
      exact_mod_cast this
    refine linearIndependent_of_top_le_span_of_card_eq_finrank ?_ (by simp [hfr])
    have hsp : Submodule.span R (Set.range fun i => (⟨r i, hr i⟩ : IsLocalRing.maximalIdeal R)) = ⊤ := by
      apply Submodule.map_injective_of_injective (IsLocalRing.maximalIdeal R).injective_subtype
      rw [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp]
      exact hrsp.1
    rw [← IsLocalRing.CotangentSpace.span_image_eq_top_iff] at hsp
    rw [← Set.range_comp] at hsp
    exact hsp.ge
  have hw := GlobalTheory.AdaptedFrame.linearIndependent_tmul_D (k := F) r hr hcot
  let φ : A → IsLocalRing.ResidueField R ⊗[R] Ω[R⁄F] :=
    fun y => (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] KaehlerDifferential.D F R (algebraMap A R y)
  have hw' : LinearIndependent (IsLocalRing.ResidueField R) (φ ∘ a) := hw
  have ha : Function.Injective a := fun i j h => hw'.injective (by simp only [Function.comp_apply, h])
  have hli : LinearIndepOn (IsLocalRing.ResidueField R) φ (Set.range a) :=
    (linearIndepOn_range_iff ha φ).2 hw'
  obtain ⟨b, -, hab, hbsp, hbli⟩ := exists_linearIndepOn_extension hli (Set.subset_univ _)
  have hVsp : Submodule.span (IsLocalRing.ResidueField R) (Set.range φ) = ⊤ :=
    span_tmul_eq_top _ (span_D_algebraMap_eq_top F A R P)
  have hbtop : ⊤ ≤ Submodule.span (IsLocalRing.ResidueField R) (Set.range fun y : b => φ y) := by
    rw [← Set.image_eq_range, ← hVsp, ← Set.image_univ]
    exact Submodule.span_le.2 hbsp
  let bV := Module.Basis.mk hbli hbtop
  haveI : Finite b := Module.Finite.finite_basis bV
  letI : Fintype b := Fintype.ofFinite b
  have hcard : Fintype.card b = n := by
    rw [← Module.finrank_eq_card_basis bV, Module.finrank_baseChange, hn]
  let σ := Fintype.equivFinOfCardEq hcard
  let e0 : Fin m ↪ b := ⟨fun j => ⟨a j, hab ⟨j, rfl⟩⟩, fun i j h => ha (congrArg Subtype.val h)⟩
  refine ⟨fun i => ((σ.symm i : b) : A), e0.trans σ.toEmbedding, fun j => by
    simp only [Function.Embedding.trans_apply, Equiv.coe_toEmbedding, Equiv.symm_apply_apply]
    rfl, ?_⟩
  let ω : Fin n → Ω[R⁄F] := fun i => KaehlerDifferential.D F R (algebraMap A R (σ.symm i : b))
  have hb' : ∀ i, (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] ω i = bV.reindex σ i := by
    intro i
    rw [Module.Basis.reindex_apply]
    exact (Module.Basis.mk_apply hbli hbtop _).symm
  have hspan := IsLocalRing.span_eq_top_of_tmul_eq_basis ω (bV.reindex σ) hb'
  have hli2 : LinearIndependent R ω :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hspan.ge (by simp [hn])
  exact ⟨Module.Basis.mk hli2 hspan.ge, fun i => by rw [Module.Basis.mk_apply]⟩
