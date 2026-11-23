import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalFinite
import GroundTheory.GlobalFields.AnalyticClassNumber.HeckeContinued
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ContinuousIdeleCircle
import GroundTheory.GlobalFields.TateThesis.EulerFactorsArch
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousInfIdele
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCMTypeOfEmbeddingsCardEqFinrank
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps GlobalTheory.CompanionTheory.HeckeBridge GroundTheory.Global GroundTheory.LocalField GroundTheory.Global.IdeleGroup
open GroundTheory.Automorphic.GodementSection (localChar)
open Formalism.L2.Host (unif atFin unif_spec)

noncomputable section

namespace GlobalTheory.CompanionTheory.HeckeArch

open InfinitePlace.Completion

variable {E : Type} [Field E] [NumberField E]

theorem infiniteEmbedding_eq (w : InfinitePlace E) (a : (w.Completion)ˣ) :
    (infiniteEmbedding w a : IdeleGroup E) = ReciprocityTheory.Neutral.Bridge.HCFR.infIdele E w a := by
  classical
  refine Units.ext (Prod.ext ?_ rfl)
  show Pi.mulSingle w (a : w.Completion) = Pi.mulSingle w (a : w.Completion)
  congr!

theorem component_on_field (χ : HChar E) (hu : IsUnitary χ) {I : Type} [Fintype I] {φ : I → E →+* ℂ}
    (hφ : Function.Bijective fun i => InfinitePlace.mk (φ i)) (n : I → ℤ)
    (hn : Formalism.L2.Host.HChar.HasInf χ φ n) (i : I) (k : Eˣ) :
    (((toHecke χ hu).infiniteComponent (InfinitePlace.mk (φ i)) (Formalism.L2.Host.atInf _ k) : Circle) : ℂ) =
      (φ i (k : E) / ((‖φ i (k : E)‖ : ℝ) : ℂ)) ^ n i := by
  have h := (GlobalTheory.InfTypeLocal.infType_iff_local E I φ hφ χ.1 χ.2.1 n).1 hn i k
  rw [HeckeCharacter.infiniteComponent_apply, coe_toIdele, infiniteEmbedding_eq]
  exact h

theorem denseRange_atInf_place (w : InfinitePlace E) : DenseRange (Formalism.L2.Host.atInf w) :=
  ((Function.surjective_eval w).denseRange.comp (GlobalTheory.InfTypeLocal.denseRange_atInf E)
    (continuous_apply w) : DenseRange _)

theorem component_eq (χ : HChar E) (hu : IsUnitary χ) {I : Type} [Fintype I] {φ : I → E →+* ℂ}
    (hφ : Function.Bijective fun i => InfinitePlace.mk (φ i)) (n : I → ℤ)
    (hn : Formalism.L2.Host.HChar.HasInf χ φ n) (i : I)
    (e : (InfinitePlace.mk (φ i)).Completion →+* ℂ) (hec : Continuous e)
    (he : ∀ k : E, e (algebraMap E _ k) = φ i k) (a : ((InfinitePlace.mk (φ i)).Completion)ˣ) :
    (((toHecke χ hu).infiniteComponent (InfinitePlace.mk (φ i)) a : Circle) : ℂ) =
      (e a / ((‖e a‖ : ℝ) : ℂ)) ^ n i := by
  have h1 : Continuous fun u : ((InfinitePlace.mk (φ i)).Completion)ˣ => e u :=
    hec.comp Units.continuous_val
  have h2 : ∀ u : ((InfinitePlace.mk (φ i)).Completion)ˣ, e u ≠ 0 := fun u =>
    (map_ne_zero _).2 u.ne_zero
  have h3 : ∀ u : ((InfinitePlace.mk (φ i)).Completion)ˣ, ((‖e u‖ : ℝ) : ℂ) ≠ 0 := fun u => by
    exact_mod_cast norm_ne_zero_iff.2 (h2 u)
  have key : (fun u : ((InfinitePlace.mk (φ i)).Completion)ˣ =>
      (((toHecke χ hu).infiniteComponent (InfinitePlace.mk (φ i)) u : Circle) : ℂ)) =
      fun u : ((InfinitePlace.mk (φ i)).Completion)ˣ => (e u / ((‖e u‖ : ℝ) : ℂ)) ^ n i := by
    refine (denseRange_atInf_place _).equalizer ?_ ?_ ?_
    · exact continuous_subtype_val.comp (map_continuous _)
    · exact (h1.div (Complex.continuous_ofReal.comp h1.norm) h3).zpow₀ _
        fun u => Or.inl (div_ne_zero (h2 u) (h3 u))
    · funext k
      show _ = (e (algebraMap E _ (k : E)) / ((‖e (algebraMap E _ (k : E))‖ : ℝ) : ℂ)) ^ n i
      rw [he]
      exact component_on_field χ hu hφ n hn i k
  exact congrFun key a

theorem conj_div_norm {z : ℂ} (hz : z ≠ 0) :
    (starRingEnd ℂ) z / ((‖z‖ : ℝ) : ℂ) = (z / ((‖z‖ : ℝ) : ℂ))⁻¹ := by
  have h0 : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hz
  rw [inv_div, div_eq_div_iff h0 hz, Complex.conj_mul']
  ring

theorem params (χ : HChar E) (hu : IsUnitary χ) {I : Type} [Fintype I] {φ : I → E →+* ℂ}
    (hφ : Function.Bijective fun i => InfinitePlace.mk (φ i)) (n : I → ℤ)
    (hn : Formalism.L2.Host.HChar.HasInf χ φ n) (i : I) (hc : (InfinitePlace.mk (φ i)).IsComplex) :
    (toHecke χ hu).infiniteTau (InfinitePlace.mk (φ i)) = 0 ∧
      ((toHecke χ hu).infiniteWeight (InfinitePlace.mk (φ i))).natAbs = (n i).natAbs := by
  set w := InfinitePlace.mk (φ i) with hw
  set T := toHecke χ hu with hT
  have hnr : ¬ w.IsReal := InfinitePlace.not_isReal_iff_isComplex.2 hc
  set e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hc with he
  have hec : Continuous e.symm := (isometryEquivComplexOfIsComplex hc).symm.continuous
  set ψ : ℂˣ →ₜ* Circle := (T.infiniteComponent w).comp (unitsContinuousHom e.symm hec) with hψ
  obtain ⟨p, -, huniq⟩ := existsUnique_complexUnits_circle ψ
  have hι : ∀ z : ℂˣ, extensionEmbedding w ((unitsContinuousHom e.symm hec z : (w.Completion)ˣ) : w.Completion) = z :=
    fun z => e.apply_symm_apply (z : ℂ)
  have hnorm : ∀ z : ℂˣ, ‖((unitsContinuousHom e.symm hec z : (w.Completion)ˣ) : w.Completion)‖ = ‖(z : ℂ)‖ := fun z => by
    rw [← hι z]
    exact ((isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) _).symm
  have h1 : ∀ z : ℂˣ, (ψ z : ℂ) = ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ^ (T.infiniteWeight w, 2 * T.infiniteTau w).1 *
      ((‖(z : ℂ)‖ : ℝ) : ℂ) ^ ((((T.infiniteWeight w, 2 * T.infiniteTau w).2 : ℝ) : ℂ) * Complex.I) := fun z => by
    have hpos : 0 < ‖(z : ℂ)‖ := norm_pos_iff.2 z.ne_zero
    show ((T.infiniteComponent w (unitsContinuousHom e.symm hec z) : Circle) : ℂ) = _
    rw [HeckeCharacter.infiniteComponent_eq, hι, hnorm, InfinitePlace.mult, if_neg hnr,
      ofReal_pow_cpow hpos]
    congr 2
    push_cast
    ring
  have h2 : ∃ s : ℤ, s.natAbs = (n i).natAbs ∧ ∀ z : ℂˣ, (ψ z : ℂ) = ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ^ (s, (0 : ℝ)).1 *
      ((‖(z : ℂ)‖ : ℝ) : ℂ) ^ ((((s, (0 : ℝ)).2 : ℝ) : ℂ) * Complex.I) := by
    have h0 : ∀ k : E, extensionEmbedding w (algebraMap E _ k) = w.embedding k := fun k =>
      extensionEmbedding_coe w (WithAbs.toAbs _ k)
    have hcont := (isometry_extensionEmbedding w).continuous
    rcases InfinitePlace.embedding_mk_eq (φ i) with h | h
    · refine ⟨n i, rfl, fun z => ?_⟩
      have := component_eq χ hu hφ n hn i (extensionEmbedding w) hcont
        (fun k => by rw [h0, hw, h]) (unitsContinuousHom e.symm hec z)
      show ((T.infiniteComponent w (unitsContinuousHom e.symm hec z) : Circle) : ℂ) = _
      rw [this, hι]
      simp
    · refine ⟨-n i, by simp, fun z => ?_⟩
      have := component_eq χ hu hφ n hn i ((starRingEnd ℂ).comp (extensionEmbedding w))
        (Complex.continuous_conj.comp hcont)
        (fun k => by
          rw [RingHom.comp_apply, h0, hw, h]
          simp) (unitsContinuousHom e.symm hec z)
      show ((T.infiniteComponent w (unitsContinuousHom e.symm hec z) : Circle) : ℂ) = _
      rw [this, RingHom.comp_apply, hι, Complex.norm_conj, conj_div_norm z.ne_zero, inv_zpow, ← zpow_neg]
      simp
  obtain ⟨s, hs, h2⟩ := h2
  have e1 := huniq _ h1
  have e2 := huniq _ h2
  have e3 := e1.trans e2.symm
  have e4 : T.infiniteWeight w = s := congrArg Prod.fst e3
  have e5 : 2 * T.infiniteTau w = 0 := congrArg Prod.snd e3
  exact ⟨by linarith, by rw [e4, hs]⟩

theorem infiniteParams_of_hasInf : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ → ∀ (χ : HChar E) (hu : IsUnitary χ) (n : I → ℤ), Formalism.L2.Host.HChar.HasInf χ φ n → ∀ i : I, (toHecke χ hu).infiniteTau (InfinitePlace.mk (φ i)) = 0 ∧ ((toHecke χ hu).infiniteWeight (InfinitePlace.mk (φ i))).natAbs = (n i).natAbs := by
  intro E _ _ _ I _ φ hφ χ hu n hn i
  exact params χ hu (GlobalTheory.CMTypeCard.bijective_mk_of_isCMType hφ) n hn i
    (IsTotallyComplex.isComplex _)

end GlobalTheory.CompanionTheory.HeckeArch
