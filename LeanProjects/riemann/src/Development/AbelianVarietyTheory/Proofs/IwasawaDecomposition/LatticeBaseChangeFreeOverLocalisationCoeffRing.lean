import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.WeightFamilies

noncomputable section
namespace GlobalTheory.FreeDedekindQuotient

variable {A O : Type} [CommRing A] [CommRing O] {ι : Type} [Fintype ι] [DecidableEq ι]

def bcEnd (s : A →+* O) (e : (ι → A) →ₗ[A] (ι → A)) : (ι → O) →ₗ[O] (ι → O) where
  toFun y := ∑ k, y k • (fun i => s (e (Pi.single k 1) i))
  map_add' y z := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c y := by simp [mul_smul, Finset.smul_sum]

theorem bcEnd_comp (s : A →+* O) (e : (ι → A) →ₗ[A] (ι → A)) (r : ι → A) :
    bcEnd s e (s ∘ r) = s ∘ e r := by
  have hr : r = ∑ k, r k • (Pi.single k 1 : ι → A) := by
    ext i; simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hr]
  ext i
  simp [bcEnd, Finset.sum_apply, map_sum]

theorem free_quot [IsDomain O] [IsPrincipalIdealRing O] (s : A →+* O) (N : Submodule A (ι → A))
    (e : (ι → A) →ₗ[A] (ι → A)) (he1 : ∀ x, e x ∈ N) (he2 : ∀ x ∈ N, e x = x) :
    Module.Free O ((ι → O) ⧸ Submodule.span O ((fun r => s ∘ r) '' (N : Set (ι → A)))) := by
  set P := Submodule.span O ((fun r => s ∘ r) '' (N : Set (ι → A))) with hPdef
  have hfix : P ≤ LinearMap.ker (bcEnd s e - LinearMap.id) := by
    rw [Submodule.span_le]
    rintro _ ⟨r, hr, rfl⟩
    simp [bcEnd_comp, he2 r hr]
  have hrange : ∀ y, bcEnd s e y ∈ P := by
    intro y
    refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact ⟨e (Pi.single k 1), he1 _, rfl⟩
  haveI : Module.IsTorsionFree O ((ι → O) ⧸ P) := Module.IsTorsionFree.of_smul_eq_zero fun c q h => by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective P q
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h
    by_cases hc : c = 0
    · exact Or.inl hc
    right
    rw [Submodule.Quotient.mk_eq_zero]
    have h1 := hfix h
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, map_smul] at h1
    have h2 : c • (bcEnd s e x - x) = 0 := h1
    rcases smul_eq_zero.1 h2 with h3 | h3
    · exact absurd h3 hc
    · rw [← sub_eq_zero.1 h3]; exact hrange x
  exact Module.free_of_finite_type_torsion_free'

end GlobalTheory.FreeDedekindQuotient

noncomputable section
namespace GlobalTheory.FreeDedekindQuotient
open Formalism.BasicNotions NumberField

theorem exists_proj {A : Type} [CommRing A] [IsDedekindDomain A] {ι : Type} [Fintype ι]
    (N : Submodule A (ι → A)) (htf : ∀ a : A, a ≠ 0 → ∀ x, a • x ∈ N → x ∈ N) :
    ∃ e : (ι → A) →ₗ[A] (ι → A), (∀ x, e x ∈ N) ∧ ∀ x ∈ N, e x = x := by
  have htor : Submodule.torsion A ((ι → A) ⧸ N) = ⊥ := by
    rw [eq_bot_iff]
    intro q hq
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff q).1 hq
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective N q
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at ha
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
    exact htf a (nonZeroDivisors.coe_ne_zero a) x ha
  haveI : Module.Flat A ((ι → A) ⧸ N) := IsDedekindDomain.flat_iff_torsion_eq_bot.2 htor
  haveI := Module.finitePresentation_of_finite A ((ι → A) ⧸ N)
  haveI : Module.Projective A ((ι → A) ⧸ N) := Module.Flat.projective_of_finitePresentation
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property N.mkQ LinearMap.id (Submodule.mkQ_surjective N)
  refine ⟨LinearMap.id - σ ∘ₗ N.mkQ, fun x => ?_, fun x hx => ?_⟩
  · rw [← Submodule.Quotient.mk_eq_zero]
    have := congrArg (fun f => f (N.mkQ x)) hσ
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, Submodule.Quotient.mk_sub]
    rw [← Submodule.mkQ_apply N (σ (N.mkQ x)), this, Submodule.mkQ_apply, sub_self]
  · have h0 : N.mkQ x = 0 := by simpa using hx
    simp [h0]

theorem dedekind_of_concrete (D : D7) (h : Function.Injective D.what₂.OtoLL ∧
    ∃ F : Subfield D.what₂.LL, ∀ x, x ∈ D.what₂.OtoLL.range ↔ x ∈ F ∧ IsIntegral ℤ x) :
    IsDedekindDomain D.what₂.O := by
  obtain ⟨hinj, F, hF⟩ := h
  have hc : Formalism.MainNotions.DIV.Inh.OsConcrete D := by
    refine ⟨hinj, F.toIntermediateField (fun x => by
      rw [eq_ratCast (algebraMap ℚ D.what₂.LL) x]; exact SubfieldClass.ratCast_mem F x), ?_⟩
    ext x
    have := hF x
    rw [RingHom.mem_range] at this
    exact this
  obtain ⟨K, _, _, ⟨e⟩⟩ := Formalism.MainNotions.DIV.Inh.OsRingOfIntegers_of_concrete D hc
  exact { e.symm.toMulEquiv.isDomain _, isNoetherianRing_of_ringEquiv _ e, Ring.DimensionLEOne.of_ringEquiv e.symm,
      IsIntegrallyClosed.of_equiv e with }

end GlobalTheory.FreeDedekindQuotient

noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

namespace GlobalTheory.BjFree

theorem latRel_torsionFree (D : D7) (hinj : Function.Injective D.what₂.OtoLL) (j : ℕ) (a : D.what₂.O) (ha : a ≠ 0)
    (x : (D.what₂.MjLat j).gen → D.what₂.O) (hx : a • x ∈ Formalism.L2.latRelSub (D.what₂.MjLat j)) :
    x ∈ Formalism.L2.latRelSub (D.what₂.MjLat j) := by
  simp only [Formalism.L2.mem_latRelSub, Formalism.L2.latRel, Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul, map_mul,
    mul_smul] at hx ⊢
  rw [← Finset.smul_sum] at hx
  have hne : (D.what₂.embLL.comp D.what₂.OtoLL) a ≠ 0 := by
    rw [RingHom.comp_apply]
    exact (_root_.map_ne_zero _).2 ((map_ne_zero_iff _ hinj).2 ha)
  exact (smul_eq_zero.1 hx).resolve_left hne

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem bjC_free : ∀ (D : D7) (B : LocBase0 D.host D.what₂) (hI : OsInt B), (Function.Injective D.what₂.OtoLL ∧ ∃ F : Subfield D.what₂.LL, ∀ x, x ∈ D.what₂.OtoLL.range ↔ x ∈ F ∧ IsIntegral ℤ x) → ∀ i, Module.Free (OOf B i) (BjC B hI i) := by
  intro D B hI hO i
  classical
  haveI := GlobalTheory.FreeDedekindQuotient.dedekind_of_concrete D hO
  obtain ⟨e, he1, he2⟩ := GlobalTheory.FreeDedekindQuotient.exists_proj (Formalism.L2.latRelSub (D.what₂.MjLat (jOf B i)))
    (fun a ha x hx => latRel_torsionFree D hO.1 _ a ha x hx)
  haveI : IsPrincipalIdealRing (OOf B i) := inferInstance
  have hF := GlobalTheory.FreeDedekindQuotient.free_quot (sOfC B hI i) _ e he1 he2
  exact hF

end GlobalTheory.BjFree
