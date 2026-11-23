import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt

noncomputable section

namespace GlobalTheory.LFun

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU
open Formalism.L2.Host (IsUnifAt atFin)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)}

namespace InertValue

theorem single_ne' {K : Type} [Field K] [NumberField K] {P Q : HeightOneSpectrum (𝓞 K)} (h : Q ≠ P)
    (u : (P.adicCompletion K)ˣ) : (GlobalTheory.CMVal.single P u : FiniteAdeleRing (𝓞 K) K) Q = 1 := by
  classical
  exact Pi.mulSingle_eq_of_ne h _

theorem exists_isUnifAt (hw : IsInertAt F E v w) (h : w.under (𝓞 F) = v) :
    ∃ a : (Fv F v)ˣ, IsUnifAt w (Units.map (complMap h).toMonoidHom a) := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have hπ0 : π ≠ 0 := by
    rintro rfl
    simp at hπ
    exact WithZero.exp_ne_zero hπ.symm
  refine ⟨Units.mk0 (algebraMap F (Fv F v) π) ((map_ne_zero _).2 hπ0), ?_⟩
  have hw' : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = w.asIdeal := hw
  have : w.asIdeal.LiesOver v.asIdeal := ⟨by subst h; rfl⟩
  have he : v.asIdeal.ramificationIdx' w.asIdeal = 1 := by
    apply Ideal.ramificationIdx'_spec
    · rw [pow_one, hw']
    · exact InertChart.not_map_le_sq hw
  show Valued.v (complMap h (algebraMap F (Fv F v) π)) = WithZero.exp (-1)
  rw [complMap_algebraMap]
  have hvw : Valued.v (algebraMap E (w.adicCompletion E) (algebraMap F E π)) = w.valuation E (algebraMap F E π) := by
    exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := w) (algebraMap F E π)
  rw [hvw, ← HeightOneSpectrum.valuation_liesOver E v w, he, pow_one, hπ]

theorem locIdele_complMap (hw : IsInertAt F E v w) (h : w.under (𝓞 F) = v) (a : (Fv F v)ˣ) :
    locIdele F w (Units.map (complMap h).toMonoidHom a) =
      ideleMap F E (GlobalTheory.CMVal.finIdele F (GlobalTheory.CMVal.single v a)) := by
  subst h
  have key : (finAdEquiv F E).symm ((GlobalTheory.CMVal.single w (Units.map (complMap rfl).toMonoidHom a) :
      (FiniteAdeleRing (𝓞 E) E)ˣ) : FiniteAdeleRing (𝓞 E) E) =
      ((GlobalTheory.CMVal.single (w.under (𝓞 F)) a : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (1 : E) := by
    rw [RingEquiv.symm_apply_eq]
    refine FiniteAdeleRing.ext (h := fun u => ?_)
    rw [finAdEquiv_apply (rfl : u.under (𝓞 F) = _)]
    simp only [Algebra.TensorProduct.map_tmul, toCompl_tmul, map_one, mul_one]
    classical
    have same : ∀ (K : Type) [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K)) (z : (P.adicCompletion K)ˣ),
        ((GlobalTheory.CMVal.single P z : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) P = z :=
      fun K _ _ P z => Pi.mulSingle_eq_same (M := fun R : HeightOneSpectrum (𝓞 K) => R.adicCompletion K) P
        (z : P.adicCompletion K)
    by_cases hu : u = w
    · subst hu
      rw [same]
      exact congrArg (complMap (rfl : u.under (𝓞 F) = _)) (same F _ a).symm
    · have hne : u.under (𝓞 F) ≠ w.under (𝓞 F) := fun h' => hu ((InertChart.under_eq_iff hw u).1 h')
      rw [single_ne' hu]
      have e2 : ((GlobalTheory.CMVal.single (w.under (𝓞 F)) a : (FiniteAdeleRing (𝓞 F) F)ˣ) :
          FiniteAdeleRing (𝓞 F) F) (u.under (𝓞 F)) = 1 := single_ne' hne a
      exact ((congrArg (complMap (rfl : u.under (𝓞 F) = _)) e2).trans (map_one _)).symm
  apply Units.ext
  show 1 - extZero F E 1 + extZero F E ((finAdEquiv F E).symm ((GlobalTheory.CMVal.single w
      (Units.map (complMap rfl).toMonoidHom a) : (FiniteAdeleRing (𝓞 E) E)ˣ) : FiniteAdeleRing (𝓞 E) E)) =
    algebraMap (AF F) (AF F ⊗[F] E) ((MonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))
      ((GlobalTheory.CMVal.single (w.under (𝓞 F)) a : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F))
  rw [key]
  generalize ((GlobalTheory.CMVal.single (w.under (𝓞 F)) a : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) = s
  have h2 : extZero F E 1 = (@id (AF F) (LinearMap.inr F (Ainf F) (Af F) 1)) ⊗ₜ[F] (1 : E) :=
    GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU_tmul _ _ 1 1
  have h3 : extZero F E (s ⊗ₜ[F] (1 : E)) = (@id (AF F) (LinearMap.inr F (Ainf F) (Af F) s)) ⊗ₜ[F] (1 : E) :=
    GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU_tmul _ _ s 1
  have h4 : algebraMap (AF F) (AF F ⊗[F] E) (MonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F) s) =
      (@id (AF F) (MonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F) s)) ⊗ₜ[F] (1 : E) := rfl
  have hX : (1 : AF F) - (@id (AF F) (LinearMap.inr F (Ainf F) (Af F) 1)) +
      (@id (AF F) (LinearMap.inr F (Ainf F) (Af F) s)) =
      (@id (AF F) (MonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F) s)) := by
    refine Prod.ext ?_ ?_
    · show (1 : Ainf F) - 0 + 0 = 1
      simp
    · show (1 : Af F) - 1 + s = s
      simp
  rw [h2, h3, h4, ← hX, TensorProduct.add_tmul, TensorProduct.sub_tmul]
  rfl

theorem eta_sq (h2 : Module.finrank F E = 2) {η : (AF F)ˣ →* Circle} (hη : IsEta F E η) (a : (AF F)ˣ) :
    η a ^ 2 = 1 := by
  have hn := hη.2.2.1 (ideleMap F E a)
  have hnorm : Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F) (ideleMap F E a) = a ^ 2 := by
    apply Units.ext
    show Algebra.norm (AF F) (algebraMap (AF F) (AF F ⊗[F] E) (a : AF F)) = ((a ^ 2 : (AF F)ˣ) : AF F)
    rw [Units.val_pow_eq_pow_val,
      Algebra.norm_algebraMap_of_basis (Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)), Fintype.card_fin, h2]
  rw [hnorm, map_pow] at hn
  exact hn

end InertValue

open InertValue in

theorem val_sq_eq_one_of_isInertAt (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (μ : (TensorProduct F (AF F) E)ˣ →* Circle) (b : ℕ) (hμ : ResEta F E μ b)
    (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (hw : IsInertAt F E v w) (hu : UnrAt μ w) :
    val μ w ^ 2 = 1 := by
  obtain ⟨⟨η, hη⟩, hres⟩ := hμ
  have h2 : Module.finrank F E = 2 := hσ.2.2.1
  have hw' : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = w.asIdeal := hw
  have hv : w.under (𝓞 F) = v := by
    ext1
    symm
    refine v.isMaximal.eq_of_le (w.under (𝓞 F)).isPrime.ne_top ?_
    exact Ideal.map_le_iff_le_comap.1 hw'.le
  obtain ⟨a, ha⟩ := exists_isUnifAt hw hv
  rw [← UnrAt.locChar_eq_val hu ha]
  simp only [locChar, MonoidHom.comp_apply]
  rw [locIdele_complMap hw hv a, hres η hη, ← map_pow, ← pow_mul, mul_comm, pow_mul, eta_sq h2 hη, one_pow,
    map_one]

end GlobalTheory.LFun

end
