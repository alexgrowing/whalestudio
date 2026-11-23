import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProdRecSatakeLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CongOpen

section Lemmas

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem kappa_one_tmul (F : FinIso L n) (a : AFplus L) :
    F.κ (1 ⊗ₜ a) = GlobalTheory.AdeleBaseChange.adMap (maximalRealSubfield L) L a := by
  refine FiniteAdeleRing.ext _ fun w ↦ ?_
  obtain ⟨i, hi, hia⟩ := F.right w (w.under (𝓞 (maximalRealSubfield L))) rfl
  rw [hia, GlobalTheory.DefU.ClassFin.adMap_eq_complMap rfl]
  refine congrFun ((HeightOneSpectrum.denseRange_algebraMap (maximalRealSubfield L)
    (w.under (𝓞 (maximalRealSubfield L)))).equalizer hi
    (GlobalTheory.LFun.InertChart.continuous_complMap rfl) (funext fun k ↦ ?_)) _
  change i (algebraMap _ _ k) = GlobalTheory.LFun.complMap rfl (algebraMap _ _ k)
  rw [GlobalTheory.LFun.complMap_algebraMap]
  have h1 : (algebraMap (maximalRealSubfield L) (AFplus L) k) (w.under (𝓞 (maximalRealSubfield L))) =
      algebraMap _ (HeightOneSpectrum.adicCompletion (maximalRealSubfield L) (w.under (𝓞 (maximalRealSubfield L)))) k := rfl
  rw [← h1, ← hia, Algebra.algebraMap_eq_smul_one (A := AFplus L) k, TensorProduct.tmul_smul,
    TensorProduct.smul_tmul', ← Algebra.algebraMap_eq_smul_one, F.left]
  rfl

theorem kappa_tmul (F : FinIso L n) (x : L) (a : AFplus L) :
    F.κ (x ⊗ₜ a) = algebraMap L _ x * GlobalTheory.AdeleBaseChange.adMap (maximalRealSubfield L) L a := by
  rw [← kappa_one_tmul, ← F.left, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem mem_ALint_of_kappa (F : FinIso L n) {y : AL L} (hy : F.κ y ∈ Formalism.UG.intAd L) :
    y ∈ ALint L := by
  have h := GlobalTheory.AdeleBaseChange.mem_int_of_map (F := maximalRealSubfield L) (E := L)
    (ι := F.κ.toRingHom) (fun x a ↦ kappa_tmul F x a) hy
  refine (Subring.closure_le.2 ?_) h
  rintro _ (⟨x, rfl⟩ | ⟨a, rfl⟩)
  · obtain ⟨r, hr⟩ := x.2
    exact Subring.subset_closure (Or.inl ⟨r, by show (x : L) ⊗ₜ _ = _; rw [← hr]⟩)
  · exact Subring.subset_closure (Or.inr ⟨a.1, a.2, rfl⟩)

end Lemmas

theorem exists_open_cong : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (N : ℕ),
    0 < N → ∃ O : Set (finU L n), IsOpen O ∧ (1 : finU L n) ∈ O ∧
      ∀ k ∈ O, ∀ x : GAf L n, F.j x = (k : UA L n) → NG.Cong L n N x := by
  intro L _ _ _ n F N hN
  set c : Af L := algebraMap L (Af L) (N : L)⁻¹ with hc
  let S : Set (Af L) := {z | z * c ∈ Formalism.UG.intAd L}
  have hI : IsOpen ((Formalism.UG.intAd L : Subring (Af L)) : Set (Af L)) :=
    RestrictedProduct.isOpen_forall_mem (fun v ↦ Valued.isOpen_valuationSubring _)
  have hS : IsOpen S := hI.preimage (continuous_id.mul continuous_const)
  let f : Fin n → Fin n → finU L n → Af L := fun s t k ↦
    pFin L ((((k : UA L n) : GlobalTheory.CuspRep.GA L n) : Matrix (Fin n) (Fin n) (Ad L)) s t) -
      pFin L ((1 : Matrix (Fin n) (Fin n) (Ad L)) s t)
  have hm : Continuous (fun k : finU L n ↦ (((k : UA L n) : GlobalTheory.CuspRep.GA L n) : Matrix (Fin n) (Fin n) (Ad L))) :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hp : Continuous (pFin L) := continuous_snd
  have hf : ∀ s t, Continuous (f s t) := fun s t ↦
    (hp.comp (hm.matrix_elem s t)).sub continuous_const
  refine ⟨{k | ∀ s t, f s t k ∈ S}, ?_, ?_, ?_⟩
  · have e : {k | ∀ s t, f s t k ∈ S} = ⋂ s, ⋂ t, (f s t) ⁻¹' S := by ext; simp
    rw [e]
    exact isOpen_iInter_of_finite fun s ↦ isOpen_iInter_of_finite fun t ↦ hS.preimage (hf s t)
  · intro s t
    have e : f s t 1 = 0 := by simp [f]
    show f s t 1 * c ∈ Formalism.UG.intAd L
    rw [e, zero_mul]
    exact zero_mem _
  · intro k hk x hx
    have hloc : ∀ s t, F.κ (((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) s t) =
        pFin L ((((k : UA L n) : GlobalTheory.CuspRep.GA L n) : Matrix (Fin n) (Fin n) (Ad L)) s t) := by
      intro s t
      refine FiniteAdeleRing.ext _ fun w ↦ ?_
      rw [← F.loc x w s t, hx]
      rfl
    have hone : ∀ s t, F.κ ((1 : Matrix (Fin n) (Fin n) (AL L)) s t) =
        pFin L ((1 : Matrix (Fin n) (Fin n) (Ad L)) s t) := by
      intro s t
      by_cases h : s = t <;> simp [Matrix.one_apply, h]
    have key : ∀ s t, ∃ y ∈ ALint L, ((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) s t -
        (1 : Matrix (Fin n) (Fin n) (AL L)) s t = (N : AL L) * y := by
      intro s t
      have h1 : f s t k * c ∈ Formalism.UG.intAd L := hk s t
      have hz : F.κ (((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) s t -
          (1 : Matrix (Fin n) (Fin n) (AL L)) s t) = f s t k := by
        simp only [f, map_sub, hloc, hone]
      refine ⟨F.κ.symm (f s t k * c), mem_ALint_of_kappa F (by rw [RingEquiv.apply_symm_apply]; exact h1), ?_⟩
      apply F.κ.injective
      rw [hz, map_mul, RingEquiv.apply_symm_apply, map_natCast, mul_comm (f s t k), ← mul_assoc, hc,
        ← map_natCast (algebraMap L (Af L)), ← map_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hN.ne'),
        map_one, one_mul]
    have hU : ∀ s t, ((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) s t ∈ ALint L := by
      intro s t
      obtain ⟨y, hy, e⟩ := key s t
      rw [sub_eq_iff_eq_add] at e
      rw [e]
      refine add_mem (mul_mem (natCast_mem _ N) hy) ?_
      by_cases h : s = t
      · simp [Matrix.one_apply, h, one_mem]
      · simp [Matrix.one_apply, h, zero_mem]
    exact ⟨hU, key⟩

end GlobalTheory.CongOpen
