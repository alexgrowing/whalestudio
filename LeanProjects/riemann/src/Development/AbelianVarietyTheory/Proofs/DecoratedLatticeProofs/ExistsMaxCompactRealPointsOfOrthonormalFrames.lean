import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AutomorphicFormsFiniteIdeal
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSigmaList
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryActionAtRealPlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmoothFunctionsOfClosedRightDerivatives
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BoundedSubgroupOfIndefiniteUnitaryEqMaximalCompaStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory GlobalTheory.AutFinLit GlobalTheory.Published.AutFin
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies (LieAt LieInf atPlace IsExpFam IsSmoothInf wordDer)
open scoped TensorProduct DirectSum Classical

noncomputable section

namespace GlobalTheory.FrameCompact

open GlobalTheory.SmoothForms Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}
  {ε : D.what₂.Tau → Fin V.rank → Bool} {fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}

def comps (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (k : ∀ τ, Formalism.REAL.KG (ε τ)) : AlgInf V :=
  fun τ => (fr τ)⁻¹ * Formalism.REAL.toMK (k τ) * fr τ

theorem comps_unit (R : RealPoints θ V) (h : IsFrameFam V ε fr) (k : ∀ τ, Formalism.REAL.KG (ε τ)) :
    sigInf V (comps fr k) * comps fr k = 1 :=
  (unit_iff R _).2 fun τ => conj_mem_UH (h τ).1 (h τ).2 (k τ)

theorem continuous_comps : Continuous (comps (ε := ε) fr) := by
  have key : Continuous fun (k : ∀ τ, Formalism.REAL.KG (ε τ)) (τ : D.what₂.Tau) =>
      (fr τ)⁻¹ * Formalism.REAL.toMK (k τ) * fr τ := by
    refine continuous_pi fun τ => ?_
    have h1 : Continuous fun k : Formalism.REAL.KG (ε τ) => Formalism.REAL.toMK k :=
      (Formalism.REAL.isClosedEmbeddingMatrix _ (ε τ)).1.continuous.comp continuous_subtype_val
    exact (continuous_const.matrix_mul (h1.comp (continuous_apply τ))).matrix_mul continuous_const
  exact key

def frameHom (R : RealPoints θ V) (h : IsFrameFam V ε fr) : (∀ τ, Formalism.REAL.KG (ε τ)) →* GA D V :=
  MonoidHom.mk' (fun k => secInf θ V (comps fr k)) fun k l => by
    have a := secInf_spec R (comps_unit R h k)
    have b := secInf_spec R (comps_unit R h l)
    have c := secInf_spec R (comps_unit R h (k * l))
    refine R.2.2.1 _ c.1 _ (mul_mem a.1 b.1) fun τ => ?_
    have hd : IsUnit (fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (h τ).1
    rw [R.2.2.2.1, c.2, a.2, b.2]
    change (fr τ)⁻¹ * (Formalism.REAL.toMK (k τ) * Formalism.REAL.toMK (l τ)) * fr τ =
      (fr τ)⁻¹ * Formalism.REAL.toMK (k τ) * fr τ * ((fr τ)⁻¹ * Formalism.REAL.toMK (l τ) * fr τ)
    simp only [Matrix.mul_assoc]
    rw [mul_nonsing_inv_cancel_left _ _ hd]

theorem frameHom_spec (R : RealPoints θ V) (h : IsFrameFam V ε fr) (k : ∀ τ, Formalism.REAL.KG (ε τ)) :
    frameHom R h k ∈ GinfC V ∧ ∀ τ, infMat D.sp.cm.sig V.gram (θ τ) (frameHom R h k) =
      (fr τ)⁻¹ * Formalism.REAL.toMK (k τ) * fr τ :=
  secInf_spec R (comps_unit R h k)

theorem frameHom_single (hθ : IsInfFam θ) (R : RealPoints θ V) (h : IsFrameFam V ε fr) (τ : D.what₂.Tau)
    (k : Formalism.REAL.KG (ε τ)) : frameHom R h (Pi.mulSingle τ k) = kAt θ V τ (ε τ) (fr τ) k := by
  have a := frameHom_spec R h (Pi.mulSingle τ k)
  have b := isAtTau_kAt θ V hθ τ (h τ).1 (h τ).2 k
  refine R.2.2.1 _ a.1 _ b.1 fun τ' => ?_
  rw [a.2]
  by_cases c : τ' = τ
  · subst c
    rw [b.2.1, Pi.mulSingle_eq_same]
  · rw [b.2.2 _ c, Pi.mulSingle_eq_of_ne c]
    change (fr τ')⁻¹ * 1 * fr τ' = 1
    rw [Matrix.mul_one, nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (h τ').1)]

theorem isCompact_frameRange (hθ : IsInfFam θ) (R : RealPoints θ V) (h : IsFrameFam V ε fr) :
    IsCompact ((frameHom R h).range : Set (GA D V)) := by
  have hc : Continuous (frameHom R h) :=
    (GlobalTheory.Mem.DerClosed.continuousOn_secInf hθ V).comp_continuous continuous_comps (comps_unit R h)
  rw [MonoidHom.coe_range]
  exact _root_.isCompact_range hc

theorem conj_mem_Kset (hθ : IsInfFam θ) (R : RealPoints θ V) (h : IsFrameFam V ε fr) (K' : Subgroup (GA D V))
    (hc : IsCompact (K' : Set (GA D V))) (hle : (frameHom R h).range ≤ K') (τ : D.what₂.Tau) {g : GA D V}
    (hg : g ∈ K') : fr τ * infMat D.sp.cm.sig V.gram (θ τ) g * (fr τ)⁻¹ ∈ Formalism.REAL.Kset (ε τ) := by
  have hd : IsUnit (fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (h τ).1
  let f : GA D V → Matrix (Fin V.rank) (Fin V.rank) ℂ :=
    fun g => fr τ * infMat D.sp.cm.sig V.gram (θ τ) g * (fr τ)⁻¹
  have fc : Continuous f :=
    (continuous_const.matrix_mul (GlobalTheory.Mem.VolExists.continuous_infMat V.gram (hθ τ))).matrix_mul continuous_const
  have fm : ∀ a b, f (a * b) = f a * f b := fun a b => by
    simp only [f, R.2.2.2.1, Matrix.mul_assoc]
    rw [nonsing_inv_mul_cancel_left _ _ hd]
  have fk : ∀ k, f (frameHom R h k) = Formalism.REAL.toMK (k τ) := fun k => by
    simp only [f, (frameHom_spec R h k).2, Matrix.mul_assoc]
    rw [mul_nonsing_inv_cancel_left _ _ hd, mul_nonsing_inv _ hd, Matrix.mul_one]
  have f1 : f 1 = 1 := by
    rw [← map_one (frameHom R h), fk]
    rfl
  have key := GlobalTheory.T.bounded_subgroup_of_indefinite_unitary_eq_maximalCompact V.rank (ε τ) (f '' K') ?_ ?_ ?_ ?_ ?_
  · rw [← key]
    exact ⟨g, hg, rfl⟩
  · rintro _ ⟨a, -, rfl⟩
    have hu : (infMat D.sp.cm.sig V.gram (θ τ) a)ᴴ * gramAt D V τ * infMat D.sp.cm.sig V.gram (θ τ) a = gramAt D V τ :=
      GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V a τ
    have h1 : ((fr τ)⁻¹)ᴴ * (fr τ)ᴴ = 1 := by rw [← conjTranspose_mul, mul_nonsing_inv _ hd, conjTranspose_one]
    change (f a)ᴴ * Formalism.REAL.Jm (ε τ) * f a = Formalism.REAL.Jm (ε τ)
    calc (f a)ᴴ * Formalism.REAL.Jm (ε τ) * f a
        = ((fr τ)⁻¹)ᴴ * ((infMat D.sp.cm.sig V.gram (θ τ) a)ᴴ * ((fr τ)ᴴ * Formalism.REAL.Jm (ε τ) * fr τ) *
            infMat D.sp.cm.sig V.gram (θ τ) a) * (fr τ)⁻¹ := by
          simp only [f, conjTranspose_mul, Matrix.mul_assoc]
      _ = (((fr τ)⁻¹)ᴴ * (fr τ)ᴴ) * Formalism.REAL.Jm (ε τ) * (fr τ * (fr τ)⁻¹) := by
          rw [(h τ).2, hu, ← (h τ).2]
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, mul_nonsing_inv _ hd, Matrix.one_mul, Matrix.mul_one]
  · rw [← Formalism.REAL.range_toMK]
    rintro _ ⟨k, rfl⟩
    refine ⟨frameHom R h (Pi.mulSingle τ k), hle ⟨_, rfl⟩, ?_⟩
    rw [fk, Pi.mulSingle_eq_same]
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact ⟨a * b, mul_mem ha hb, fm a b⟩
  · rintro _ ⟨a, ha, rfl⟩
    refine ⟨a⁻¹, inv_mem ha, (inv_eq_left_inv ?_).symm⟩
    rw [← fm, inv_mul_cancel, f1]
  · have : ∀ i j, ∃ C : ℝ, ∀ a ∈ K', ‖f a i j‖ ≤ C := fun i j =>
      hc.exists_bound_of_continuousOn (fc.matrix_elem i j).continuousOn
    choose C hC using this
    obtain ⟨B, hB⟩ := (Set.finite_range fun p : Fin V.rank × Fin V.rank => C p.1 p.2).bddAbove
    refine ⟨B, ?_⟩
    rintro _ ⟨a, ha, rfl⟩ i j
    exact (hC i j a ha).trans (hB ⟨(i, j), rfl⟩)

theorem isMaxCompactInf_range (hθ : IsInfFam θ) (R : RealPoints θ V) (h : IsFrameFam V ε fr) :
    IsMaxCompactInf V (frameHom R h).range := by
  refine ⟨?_, isCompact_frameRange hθ R h, fun K' hi hc hle => le_antisymm (fun g hg => ?_) hle⟩
  · rintro _ ⟨k, rfl⟩
    exact (frameHom_spec R h k).1
  · have : ∀ τ, ∃ k : Formalism.REAL.KG (ε τ),
        Formalism.REAL.toMK k = fr τ * infMat D.sp.cm.sig V.gram (θ τ) g * (fr τ)⁻¹ := fun τ => by
      have := conj_mem_Kset hθ R h K' hc hle τ hg
      rw [← Formalism.REAL.range_toMK] at this
      exact this
    choose k hk using this
    refine ⟨k, R.2.2.1 _ (frameHom_spec R h k).1 _ (hi g hg) fun τ => ?_⟩
    have hd : IsUnit (fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (h τ).1
    rw [(frameHom_spec R h k).2, hk]
    simp only [Matrix.mul_assoc]
    rw [nonsing_inv_mul_cancel_left _ _ hd, nonsing_inv_mul _ hd, Matrix.mul_one]

theorem exists_maxCompact_of_frames : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D), ∀ (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), IsFrameFam V ε fr → ∃ K : Subgroup (GA D V), IsMaxCompactInf V K ∧ (∃ j : (∀ τ, Formalism.REAL.KG (ε τ)) →* K, Function.Surjective j ∧ ∀ τ k, (j (Pi.mulSingle τ k) : GA D V) = kAt θ V τ (ε τ) (fr τ) k) := by
  intro D θ hθ V ε fr h
  have R := (GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ V
  exact ⟨(frameHom R h).range, isMaxCompactInf_range hθ R h, (frameHom R h).rangeRestrict,
    (frameHom R h).rangeRestrict_surjective, fun τ k => frameHom_single hθ R h τ k⟩

end GlobalTheory.FrameCompact

end
