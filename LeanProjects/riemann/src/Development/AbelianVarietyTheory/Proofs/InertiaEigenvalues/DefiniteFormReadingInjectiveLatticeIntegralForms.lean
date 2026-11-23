import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockOfApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmT4OfRootsInField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaSeriesIntegralFormsEqSpanDedekindCoefRingStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentComplexOfSubfieldCoeffLatticeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

noncomputable section

namespace GlobalTheory.PlaceExp

section Alg

variable {R K E V A : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] [Field E] [Algebra R E]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V] [AddCommGroup A] [Module ℂ A]

theorem span_one_tmul (hE : Function.Injective (algebraMap R E)) {I : Type} (v : I → V)
    (hv : Submodule.span K (Set.range v) = ⊤) :
    Submodule.span E (Set.range fun i => ((1 : E) ⊗ₜ[R] v i : E ⊗[R] V)) = ⊤ := by
  have key : ∀ f : V, ((1 : E) ⊗ₜ[R] f : E ⊗[R] V) ∈
      Submodule.span E (Set.range fun i => ((1 : E) ⊗ₜ[R] v i : E ⊗[R] V)) := fun f => by
    have hf : f ∈ Submodule.span K (Set.range v) := hv ▸ Submodule.mem_top
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact Submodule.subset_span ⟨i, rfl⟩
    | zero => rw [TensorProduct.tmul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [TensorProduct.tmul_add]; exact add_mem hx hy
    | smul a x _ hx =>
      obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := R) a
      have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
      have hqK : algebraMap R K q ≠ 0 := by simpa using hq0
      have hqE : algebraMap R E q ≠ 0 := fun h => hq0 (hE (h.trans (map_zero _).symm))
      rw [← Submodule.smul_mem_iff _ hqE, algebraMap_smul, ← TensorProduct.tmul_smul, ← algebraMap_smul K q, smul_smul,
        mul_div_cancel₀ _ hqK, algebraMap_smul, TensorProduct.tmul_smul, ← algebraMap_smul E p]
      exact Submodule.smul_mem _ _ hx
  refine Submodule.eq_top_iff'.2 fun y => ?_
  induction y using TensorProduct.induction_on with
  | zero => exact zero_mem _
  | add x y hx hy => exact add_mem hx hy
  | tmul a f =>
    have : (a ⊗ₜ[R] f : E ⊗[R] V) = a • ((1 : E) ⊗ₜ[R] f) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ (key f)

theorem injective_of_indep {W : Type} [AddCommGroup W] [Module E W] {ε : E →+* ℂ} (φ : W →ₛₗ[ε] A) {I : Type} (u : I → W)
    (hu : Submodule.span E (Set.range u) = ⊤) (hi : LinearIndependent ℂ fun i => φ (u i)) : Function.Injective φ := by
  refine (injective_iff_map_eq_zero φ).2 fun y hy => ?_
  have hy' : y ∈ Submodule.span E (Set.range u) := hu ▸ Submodule.mem_top
  obtain ⟨l, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hy'
  rw [Finsupp.sum, map_sum] at hy
  simp only [map_smulₛₗ] at hy
  have h := linearIndependent_iff'.1 hi _ _ hy
  refine Finset.sum_eq_zero fun i hi' => ?_
  have : l i = 0 := ε.injective ((h i hi').trans (map_zero _).symm)
  simp only [this, zero_smul]

theorem indep_fieldRange {e : K →+* ℂ} (g : V →ₛₗ[e] A) (hg : Function.Injective g) {I : Type} {v : I → V}
    (hv : LinearIndependent K v) : LinearIndependent e.fieldRange fun i => g (v i) := by
  refine linearIndependent_iff'.2 fun t c h i hi => ?_
  choose d hd using fun i => RingHom.mem_fieldRange.1 (c i).2
  have h1 : g (∑ i ∈ t, d i • v i) = 0 := by
    rw [map_sum, ← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smulₛₗ, hd]
    rfl
  have h2 := linearIndependent_iff'.1 hv _ _ (hg (h1.trans (map_zero _).symm)) i hi
  exact Subtype.ext ((hd i).symm.trans (by rw [h2, map_zero]; rfl))

end Alg

theorem rdE_injective_lattice : ∀ (D : D7) (c : NChoice D) (w : D.what₂.places.Pl) (ρ : Setup D.ntw) (hρ : ρ.Good) (j : Fin D.R.m) (rd : Rd ρ D.nexp (c.twI w) j (c.sd w)) (T : CellTie hρ D.nexp rd) (ε : KE c w →+* ℂ) (hε : Extends ρ ε), TwOK (c.twI w) (c.k' w) (c.Q w) (chr c w) → (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange) →
  Function.Injective (rdE T hε) ∧ ∀ F : Amb D j, F ∈ (ρ.B (c.twI w) j (c.sd w)).mtLat (embLL0 D) (labLL0 D) (ringOf ε) (twVia ρ ε) ↔ ∃ y ∈ latT c w (j.1 + 1), rdE T hε y = F := by
  intro D c w ρ hρ j rd T ε hε hok hr
  refine ⟨?_, ?_⟩
  · obtain ⟨s, hs, hspan, hli⟩ := exists_linearIndependent (FractionRing (D.ntw.Ok (c.twI w) (c.k' w)))
      (D.nexp.MtLat (c.twI w) (j.1 + 1) (c.sd w) (c.k' w) (c.Q w) (chr c w) :
        Set (D.nexp.MtV (c.twI w) (j.1 + 1) (c.sd w) (c.k' w) (c.Q w) (chr c w)))
    rw [D.nexp.MtLat_span] at hspan
    have hE : Function.Injective (algebraMap (D.ntw.Ok (c.twI w) (c.k' w)) (KE c w)) := fun a b h =>
      ρ.eOk_injective (c.twI w) (c.sd w) (c.k' w) (by rw [← hε.apply, ← hε.apply, h])
    refine injective_of_indep (rdE T hε) _ (span_one_tmul (K := FractionRing (D.ntw.Ok (c.twI w) (c.k' w))) hE
      (Subtype.val : s → _) (by rw [Subtype.range_coe]; exact hspan)) ?_
    have h1 := indep_fieldRange _ (T.rdV_inj _ _ _ hok) hli
    have h2 := GlobalTheory.T.linearIndependent_complex_of_subfield_coeffLattice D _ _ _ (hρ.base (c.twI w) j (c.sd w)) _ _ _ _ (hρ.isCoefRing_k (c.twI w) (c.sd w) (c.k' w))
      (ρ.ek (c.twI w) (c.sd w) (c.k' w)).fieldRange (by rintro _ ⟨x, rfl⟩; exact ⟨_, rfl⟩) _ _
      (fun a h => ((Base.mem_mtLat _ _ _ _).1 ((T.rdV_mem hok).1 (hs a.2))).2 h) h1
    simpa only [rdE_tmul, map_one, one_smul] using h2
  · obtain ⟨hg, hadm, -⟩ := GlobalTheory.TwistGood.tw_good D _ _ ρ hρ (c.twI w) j (c.sd w) _ _ _ hok
    have hle : (ρ.eOk (c.twI w) (c.sd w) (c.k' w)).range ≤ ringOf ε := by
      rintro _ ⟨x, rfl⟩
      refine ⟨algebraMap _ _ x, ?_⟩
      rw [← hε.apply, IsScalarTower.algebraMap_apply (D.ntw.Ok (c.twI w) (c.k' w)) (c.Oe w) (KE c w)]
      rfl
    have hbc := GlobalTheory.T.thetaSeriesIntegralForms_eq_span_dedekindCoefRing D _ _ _ (hρ.base (c.twI w) j (c.sd w)) _ hg hadm _ _ _ _ _
      (ρ.eOk_injective (c.twI w) (c.sd w) (c.k' w)) (hρ.isCoefRing_k (c.twI w) (c.sd w) (c.k' w))
      (levLam_mem_eOk hr T hok) _ hle
    have hsm : ∀ (a : c.Oe w) (y : Tgt c w (j.1 + 1)), rdE T hε (a • y) = ε (algebraMap _ _ a) • rdE T hε y := fun a y => by
      rw [← algebraMap_smul (KE c w) a y, map_smulₛₗ]
    intro F
    rw [hε.twVia_eq, hbc]
    constructor
    · intro hF
      induction hF using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨f, hf, rfl⟩ := (T.mtLat_iff _ _ _ hok x).1 hx
        refine ⟨_, Submodule.subset_span ⟨f, hf, rfl⟩, ?_⟩
        rw [TensorProduct.mk_apply, rdE_tmul, map_one, one_smul]
      | zero => exact ⟨0, zero_mem _, map_zero _⟩
      | add x y _ _ hx hy =>
        obtain ⟨x', hx, rfl⟩ := hx
        obtain ⟨y', hy, rfl⟩ := hy
        exact ⟨x' + y', add_mem hx hy, map_add _ _ _⟩
      | smul a x _ hx =>
        obtain ⟨x', hx, rfl⟩ := hx
        obtain ⟨_, a, rfl⟩ := a
        exact ⟨a • x', Submodule.smul_mem _ _ hx, hsm a x'⟩
    · rintro ⟨y, hy, rfl⟩
      induction hy using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨f, hf, rfl⟩ := hx
        rw [TensorProduct.mk_apply, rdE_tmul, map_one, one_smul]
        exact Submodule.subset_span ((T.rdV_mem hok).1 hf)
      | zero => rw [map_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
      | smul a x _ hx =>
        rw [hsm]
        exact Submodule.smul_mem _ (⟨ε (algebraMap _ _ a), a, rfl⟩ : ringOf ε) hx

end GlobalTheory.PlaceExp

end
