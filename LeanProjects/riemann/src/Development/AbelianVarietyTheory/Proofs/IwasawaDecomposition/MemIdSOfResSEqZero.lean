import Mathlib
import Formalism.LocalToGlobal.Columns.RecLevelLoc
import Formalism.LocalToGlobal.HermitianForms.PsiZeroNontrivialCharacter
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AfsplitB

open NumberField IsDedekindDomain Formalism.UG
open scoped TensorProduct

namespace GlobalTheory.SplitResidue

open Formalism.L2.DIV HeightOneSpectrum

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem mem_maximalIdeal_iff (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletionIntegers F) :
    x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) ↔
      Valued.v (x : v.adicCompletion F) < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact Valuation.Integer.not_isUnit_iff_valuation_lt_one (x := (x : Valued.integer (v.adicCompletion F)))

theorem integral_image (v : HeightOneSpectrum (𝓞 F))
    (φ : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F) (b : 𝓞 E) :
    φ ((algebraMap (𝓞 E) E b) ⊗ₜ[F] (1 : v.adicCompletion F)) ∈ v.adicCompletionIntegers F := by
  have h0 : IsIntegral ℤ b := Algebra.IsIntegral.isIntegral b
  let ψ : 𝓞 E →+* v.adicCompletion F :=
    φ.comp ((inclE (F := F) (v.adicCompletion F)).comp (algebraMap (𝓞 E) E))
  have h1 : IsIntegral (v.adicCompletionIntegers F) (ψ b) :=
    IsIntegral.map_of_comp_eq (Int.castRingHom _) ψ (RingHom.ext_int _ _) h0
  exact (adicCompletionIntegers.integers F v).mem_of_integral h1

theorem comp_mem (v : HeightOneSpectrum (𝓞 F))
    (φ : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F)
    (hφ : ∀ a : v.adicCompletion F, φ ((1 : E) ⊗ₜ[F] a) = a) (s : Formalism.L2.Herm.intAf F E) :
    φ (prV (E := E) v s.1) ∈ v.adicCompletionIntegers F := by
  have hle : Formalism.L2.Herm.intAf F E ≤
      Subring.comap (φ.comp (prV (E := E) v)) (v.adicCompletionIntegers F).toSubring := by
    refine Subring.closure_le.2 ?_
    rintro x (⟨b, rfl⟩ | ⟨y, rfl⟩)
    · obtain ⟨b0, hb0⟩ := b.2
      show φ (prV (E := E) v ((b : E) ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F))) ∈ v.adicCompletionIntegers F
      rw [Formalism.UG.P.afsplit_prV_tmul, ← hb0]
      exact integral_image v φ b0
    · show φ (prV (E := E) v ((1 : E) ⊗ₜ[F] (y : Formalism.L2.Herm.Af F))) ∈ v.adicCompletionIntegers F
      rw [Formalism.UG.P.afsplit_prV_tmul, hφ]
      exact y.2 v
  exact hle s.2

theorem mem_idS_of_resS_eq_zero (w : HeightOneSpectrum (𝓞 E)) {t : Formalism.L2.Herm.intAf F E}
    (h : resS F w t = 0) : t ∈ idS F w.asIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  unfold resS at h
  rw [RingHom.comp_apply] at h
  exact (map_eq_zero_iff _ (RingEquiv.injective _)).1 h

theorem exists_residue_equiv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    (φ : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F) (p : 𝓞 E),
    (∀ a : v.adicCompletion F, φ ((1 : E) ⊗ₜ[F] a) = a) →
    Valued.v (φ (inclE (F := F) (v.adicCompletion F) (p : E))) < 1 →
    (∀ P : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) = v → p ∈ P.asIdeal → P = w) →
    ∃ (ρ : Formalism.L2.Herm.intAf F E →+* v.adicCompletionIntegers F)
      (e : (𝓞 E ⧸ w.asIdeal) ≃+* Formalism.L2.Forms.kv F v),
      (∀ s, ((ρ s : v.adicCompletionIntegers F) : v.adicCompletion F) = φ (prV (E := E) v s.1)) ∧
      ∀ s, IsLocalRing.residue _ (ρ s) = e (Formalism.L2.DIV.resS F w s) := by
  intro F E _ _ _ _ _ v w φ p hφ hp hw
  let ρ : Formalism.L2.Herm.intAf F E →+* v.adicCompletionIntegers F :=
    (φ.comp ((prV (E := E) v).comp (Formalism.L2.Herm.intAf F E).subtype)).codRestrict
      (v.adicCompletionIntegers F) (fun s => comp_mem v φ hφ s)
  have hρ : ∀ s, ((ρ s : v.adicCompletionIntegers F) : v.adicCompletion F) = φ (prV (E := E) v s.1) :=
    fun _ => rfl
  let r : Formalism.L2.Herm.intAf F E →+* Formalism.L2.Forms.kv F v := (IsLocalRing.residue _).comp ρ
  let g : 𝓞 E →+* Formalism.L2.Forms.kv F v := r.comp (oToS F E)
  have hg0 : ∀ b : 𝓞 E, Valued.v (φ (inclE (F := F) (v.adicCompletion F) (b : E))) < 1 → g b = 0 := by
    intro b hb
    show IsLocalRing.residue _ (ρ (oToS F E b)) = 0
    rw [IsLocalRing.residue_eq_zero_iff, mem_maximalIdeal_iff, hρ]
    exact hb
  have hv : ∀ x ∈ v.asIdeal, g (algebraMap (𝓞 F) (𝓞 E) x) = 0 := by
    intro x hx
    refine hg0 _ ?_
    have e1 : ((algebraMap (𝓞 F) (𝓞 E) x : 𝓞 E) : E) = algebraMap F E (algebraMap (𝓞 F) F x) := by
      show algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) x) = _
      rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    have e2 : inclE (F := F) (v.adicCompletion F) (algebraMap F E (algebraMap (𝓞 F) F x)) =
        (1 : E) ⊗ₜ[F] (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F x)) := by
      show (algebraMap F E (algebraMap (𝓞 F) F x)) ⊗ₜ[F] (1 : v.adicCompletion F) = _
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one]
    rw [e1, e2, hφ]
    refine lt_of_eq_of_lt (valuedAdicCompletion_eq_valuation' v _) ?_
    exact (valuation_lt_one_iff_mem v x).2 hx
  have hne : RingHom.ker g ≠ ⊥ := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
    intro hb
    have h1 : algebraMap (𝓞 F) (𝓞 E) x ∈ RingHom.ker g := hv x hx
    rw [hb, Ideal.mem_bot] at h1
    exact hx0 (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E) (h1.trans (map_zero _).symm))
  let P : HeightOneSpectrum (𝓞 E) := ⟨RingHom.ker g, RingHom.ker_isPrime g, hne⟩
  have hunder : P.under (𝓞 F) = v := by
    refine HeightOneSpectrum.ext (v.isMaximal.eq_of_le (P.under (𝓞 F)).isPrime.ne_top ?_).symm
    intro x hx
    exact hv x hx
  have hk : RingHom.ker g = w.asIdeal := congrArg HeightOneSpectrum.asIdeal (hw P hunder (hg0 p hp))
  have hz : idS F w.asIdeal ≤ RingHom.ker r := by
    refine Ideal.map_le_iff_le_comap.2 fun a ha => ?_
    rw [← hk] at ha
    exact ha
  have hfac : ∀ s (b : 𝓞 E), resS F w s = Ideal.Quotient.mk w.asIdeal b → r s = g b := by
    intro s b h
    have h0 : resS F w (s - oToS F E b) = 0 := by rw [map_sub, resS_oToS, h, sub_self]
    have h1 : r (s - oToS F E b) = 0 := hz (mem_idS_of_resS_eq_zero w h0)
    rw [map_sub] at h1
    exact sub_eq_zero.1 h1
  have hs : Function.Surjective g := by
    intro κ
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective κ
    let s : Formalism.L2.Herm.intAf F E := ⟨(1 : E) ⊗ₜ[F] Formalism.UG.P.afsplitI v (a : v.adicCompletion F),
      Subring.subset_closure (Or.inr ⟨⟨_, Formalism.UG.P.afsplitI_mem_intAd v _ a.2⟩, rfl⟩)⟩
    have hρs : ρ s = a := Subtype.ext (by
      rw [hρ]
      show φ (prV (E := E) v ((1 : E) ⊗ₜ[F] Formalism.UG.P.afsplitI v (a : v.adicCompletion F))) = _
      rw [Formalism.UG.P.afsplit_prV_tmul, Formalism.UG.P.afsplitI_self, hφ])
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (resS F w s)
    refine ⟨b, (hfac s b hb.symm).symm.trans ?_⟩
    show IsLocalRing.residue _ (ρ s) = _
    rw [hρs]
  refine ⟨ρ, (Ideal.quotEquivOfEq hk.symm).trans (RingHom.quotientKerEquivOfSurjective hs), hρ, ?_⟩
  intro s
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (resS F w s)
  rw [← hb]
  exact hfac s b hb.symm

end GlobalTheory.SplitResidue
