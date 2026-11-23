import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesLocallyCompactSecondCountable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GramNear
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitHermOfDet
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SiegelND.Coef

section Abstract

variable {Y X : Type*} [MeasurableSpace Y] [MeasurableSpace X]

theorem fubini_unimod {dy : Measure Y} {dx : Measure X} [SFinite dy] [SFinite dx] {f : Y → ℂ} {g : X → ℂ}
    (hf : Integrable f dy) (hg : Integrable g dx) {u : Y → X → ℂ}
    (hu : AEStronglyMeasurable (Function.uncurry u) (dy.prod dx)) (hn : ∀ y x, ‖u y x‖ = 1) :
    ∫ y, f y * ∫ x, g x * u y x ∂dx ∂dy = ∫ x, g x * ∫ y, f y * u y x ∂dy ∂dx := by
  have h0 : Integrable (fun z : Y × X => f z.1 * g z.2) (dy.prod dx) := hf.mul_prod hg
  have hint : Integrable (Function.uncurry fun y x => f y * (g x * u y x)) (dy.prod dx) := by
    refine h0.mono ?_ (Filter.Eventually.of_forall fun z => ?_)
    · refine (h0.aestronglyMeasurable.mul hu).congr (Filter.Eventually.of_forall fun z => ?_)
      simp only [Function.uncurry, Pi.mul_apply, mul_assoc]
    · simp only [Function.uncurry, norm_mul, hn, mul_one, le_refl]
  have hL : ∀ y, f y * ∫ x, g x * u y x ∂dx = ∫ x, f y * (g x * u y x) ∂dx := fun y =>
    (integral_const_mul _ _).symm
  have hR : ∀ x, g x * ∫ y, f y * u y x ∂dy = ∫ y, f y * (g x * u y x) ∂dy := fun x => by
    rw [← integral_const_mul]
    congr 1
    funext y
    ring
  simp_rw [hL, hR]
  exact integral_integral_swap hint

end Abstract

section Pair

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem pairHerm_sub (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {n : ℕ} (S A B : HermR R σ n) :
    pairHerm R σ n S (A - B) = pairHerm R σ n S A - pairHerm R σ n S B := by
  simp only [pairHerm, AddSubgroup.coe_sub, Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib, map_sub]

theorem half_trace_mul_eq_pairHerm (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {n : ℕ} (S G : HermR R σ n) :
    algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E)
      (Matrix.trace ((S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * (G : Matrix (Fin n) (Fin n) (R ⊗[F] E)))) =
    pairHerm R σ n S G := by
  simp only [pairHerm, Matrix.trace, Matrix.diag, Matrix.mul_apply]

theorem half_trace_mul_eq_pairHerm' (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {n : ℕ} (S G : HermR R σ n) :
    algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E)
      (Matrix.trace ((G : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)))) =
    pairHerm R σ n S G := by
  rw [Matrix.trace_mul_comm]
  exact half_trace_mul_eq_pairHerm R σ S G

theorem continuous_pairHerm (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
    [Module.Finite F E] (σ : E →ₐ[F] E) (n : ℕ) :
    Continuous fun z : HermR R σ n × HermR R σ n => pairHerm R σ n z.1 z.2 := by
  haveI : IsTopologicalRing (R ⊗[F] E) := GlobalTheory.CompanionTheory.SW.TopK.isTopRing R
  unfold pairHerm
  refine continuous_const.mul ((GlobalTheory.CompanionTheory.SW.TopK.continuous_trace R).comp ?_)
  refine continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun b _ => ?_
  exact ((continuous_subtype_val.comp continuous_fst).matrix_elem a b).mul
    ((continuous_subtype_val.comp continuous_snd).matrix_elem b a)

end Pair

section Cm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem continuous_pairHerm_gramH_sub (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
    {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) {M n : ℕ} {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J)
    (hg : Continuous (gramR R σ J : (Fin n → Fin M → R ⊗[F] E) → _)) (c : HermR R σ n) :
    Continuous fun z : HermR R σ n × (Fin n → Fin M → R ⊗[F] E) =>
      pairHerm R σ n z.1 (gramH hCM hJ R z.2 - c) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have hp := continuous_pairHerm (F := F) (E := E) R σ n
  have hgH : Continuous fun x : Fin n → Fin M → R ⊗[F] E => gramH hCM hJ R x :=
    Continuous.subtype_mk hg _
  have m1 : Continuous fun z : HermR R σ n × (Fin n → Fin M → R ⊗[F] E) =>
      ((z.1, gramH hCM hJ R z.2) : HermR R σ n × HermR R σ n) :=
    Continuous.prodMk continuous_fst (hgH.comp continuous_snd)
  have m2 : Continuous fun z : HermR R σ n × (Fin n → Fin M → R ⊗[F] E) =>
      ((z.1, c) : HermR R σ n × HermR R σ n) :=
    Continuous.prodMk continuous_fst continuous_const
  have h1 : Continuous fun z : HermR R σ n × (Fin n → Fin M → R ⊗[F] E) =>
      pairHerm R σ n z.1 (gramH hCM hJ R z.2) := by
    have h := hp.comp m1
    exact h
  have h2 : Continuous fun z : HermR R σ n × (Fin n → Fin M → R ⊗[F] E) => pairHerm R σ n z.1 c := by
    have h := hp.comp m2
    exact h
  have := h1.sub h2
  refine this.congr fun z => ?_
  exact (pairHerm_sub R σ z.1 _ c).symm

end Cm

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem chiT_eq (σ : E →ₐ[F] E) {n : ℕ} (ψ : AddChar (AF F) ℂ) (T : Matrix (Fin n) (Fin n) E)
    (hT : ∀ a c, σ (T c a) = T a c) (y : HermR (AF F) σ n) :
    chiT σ ψ T y = ψ (-pairHerm (AF F) σ n y (hermOf (AF F) σ T hT)) := by
  rw [← half_trace_mul_eq_pairHerm' (AF F) σ y (hermOf (AF F) σ T hT)]
  rfl

theorem psi_mul_chiT {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) {M n : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (hJ : IsHermND σ J) (ψ : AddChar (AF F) ℂ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a c, σ (T c a) = T a c)
    (y : HermR (AF F) σ n) (x : Fin n → Fin M → AF F ⊗[F] E) :
    ψ (algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
      (Matrix.trace ((y : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * gramR (AF F) σ J x))) * chiT σ ψ T y =
    ψ (pairHerm (AF F) σ n y (gramH hCM hJ (AF F) x - hermOf (AF F) σ T hT)) := by
  have h2 : algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
      (Matrix.trace ((y : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * gramR (AF F) σ J x)) =
      pairHerm (AF F) σ n y (gramH hCM hJ (AF F) x) :=
    half_trace_mul_eq_pairHerm (AF F) σ y (gramH hCM hJ (AF F) x)
  rw [h2, chiT_eq σ ψ T hT, ← AddChar.map_add_eq_mul, pairHerm_sub, sub_eq_add_neg]

theorem starN_mul_chiT {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) {M n : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (hJ : IsHermND σ J) (ψ : AddChar (AF F) ℂ) (dx : Measure (Fin n → Fin M → AF F ⊗[F] E))
    (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a c, σ (T c a) = T a c)
    (y : HermR (AF F) σ n) :
    GlobalTheory.CompanionTheory.SiegelND.starN σ J ψ dx Φ y * chiT σ ψ T y =
      ∫ x, Φ x * ψ (pairHerm (AF F) σ n y (gramH hCM hJ (AF F) x - hermOf (AF F) σ T hT)) ∂dx := by
  rw [GlobalTheory.CompanionTheory.SiegelND.starN, ← integral_mul_const]
  congr 1
  funext x
  rw [mul_assoc, psi_mul_chiT hCM hJ ψ T hT]

end Adelic

end GlobalTheory.CompanionTheory.SiegelND.Coef

namespace GlobalTheory.CompanionTheory.SiegelND.Coef

theorem fubini_starN_fouH : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ) (hCM : IsCMExt F E σ), ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ (dx : Measure (Fin n → Fin M → AF F ⊗[F] E)) (db : Measure (HermR (AF F) σ n)), SFinite dx → SFinite db → ∀ Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ, Integrable Φ dx → ∀ τ : HermR (AF F) σ n → ℂ, Integrable (GlobalTheory.CompanionTheory.SiegelND.Coef.fouH σ ψ db τ) db → (∀ z, ∫ y, GlobalTheory.CompanionTheory.SiegelND.Coef.fouH σ ψ db τ y * ψ (pairHerm (AF F) σ n y z) ∂db = τ (-z)) → ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a c, σ (T c a) = T a c), Continuous (GlobalTheory.CompanionTheory.SiegelND.Coef.chiT σ ψ T) ∧ ∫ y, GlobalTheory.CompanionTheory.SiegelND.Coef.fouH σ ψ db τ y * (GlobalTheory.CompanionTheory.SiegelND.starN σ J ψ dx Φ y * GlobalTheory.CompanionTheory.SiegelND.Coef.chiT σ ψ T y) ∂db = ∫ x, Φ x * τ (hermOf (AF F) σ T hT - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ (AF F) x) ∂dx := by
  intro F E _ _ _ _ _ σ M J hJ n hCM ψ hψ dx db _ _ Φ hΦ τ hTh hinv T hT
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  obtain ⟨_, _, _, _, -, -, -, hB, -, hg⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (AF F)
  have := hB n M
  have : BorelSpace (AF F) := ⟨rfl⟩
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨hψc, hψn, -⟩ := hψ
  have hpc := continuous_pairHerm_gramH_sub (AF F) hCM hJ (hg n M J) (hermOf (AF F) σ T hT)
  refine ⟨?_, ?_⟩
  · have hp := continuous_pairHerm (F := F) (E := E) (AF F) σ n
    have m : Continuous fun y : HermR (AF F) σ n =>
        ((y, hermOf (AF F) σ T hT) : HermR (AF F) σ n × HermR (AF F) σ n) :=
      Continuous.prodMk continuous_id continuous_const
    have h1 := (hp.comp m).neg
    have h2 := hψc.comp h1
    have : GlobalTheory.CompanionTheory.SiegelND.Coef.chiT σ ψ T =
        fun y => ψ (-pairHerm (AF F) σ n y (hermOf (AF F) σ T hT)) := funext (chiT_eq σ ψ T hT)
    rw [this]
    exact h2
  · have hmeas : AEStronglyMeasurable (Function.uncurry fun (y : HermR (AF F) σ n)
        (x : Fin n → Fin M → AF F ⊗[F] E) =>
        ψ (pairHerm (AF F) σ n y (gramH hCM hJ (AF F) x - hermOf (AF F) σ T hT))) (db.prod dx) :=
      (hψc.comp hpc).aestronglyMeasurable
    have key := fubini_unimod hTh hΦ hmeas (fun y x => hψn _)
    have hL : ∀ y, fouH σ ψ db τ y * (GlobalTheory.CompanionTheory.SiegelND.starN σ J ψ dx Φ y * chiT σ ψ T y) =
        fouH σ ψ db τ y * ∫ x, Φ x *
          ψ (pairHerm (AF F) σ n y (gramH hCM hJ (AF F) x - hermOf (AF F) σ T hT)) ∂dx := fun y => by
      rw [starN_mul_chiT hCM hJ ψ dx Φ T hT y]
    have hR : ∀ x, ∫ y, fouH σ ψ db τ y *
        ψ (pairHerm (AF F) σ n y (gramH hCM hJ (AF F) x - hermOf (AF F) σ T hT)) ∂db =
        τ (hermOf (AF F) σ T hT - gramH hCM hJ (AF F) x) := fun x => by
      rw [hinv, neg_sub]
    simp_rw [hL]
    rw [key]
    simp_rw [hR]

end GlobalTheory.CompanionTheory.SiegelND.Coef
