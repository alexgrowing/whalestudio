import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AtPlaceIffEqAtTau
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PointAtPlaceHom

open GlobalTheory.PointAtPlace

variable {D : D7} {θ : InfF D}

theorem infMat_mul (V : HSp D) (φ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (a b : GA D V) :
    infMat D.sp.cm.sig V.gram φ (a * b) = infMat D.sp.cm.sig V.gram φ a * infMat D.sp.cm.sig V.gram φ b :=
  archM_mul V φ a b

theorem infMat_one (V : HSp D) (φ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) :
    infMat D.sp.cm.sig V.gram φ 1 = 1 := archM_one V φ

theorem atTau_spec (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) : IsAtTau θ V τ g (atTau θ V τ g) := by
  have hu := existsUnique_isAtTau V τ θ hθ g hg
  unfold atTau
  rw [dif_pos hu.exists]
  exact hu.exists.choose_spec

theorem atTau_mem (V : HSp D) (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    atTau θ V τ g ∈ GinfC V := by
  unfold atTau
  split_ifs with h
  · exact h.choose_spec.1
  · exact one_mem _

theorem one_mem_UH {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ Formalism.QuantumDeterminants.UH H := by
  show (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * H * 1 = H
  simp

theorem mul_mem_UH {n : ℕ} {H g g' : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH H)
    (hg' : g' ∈ Formalism.QuantumDeterminants.UH H) : g * g' ∈ Formalism.QuantumDeterminants.UH H := by
  have h1 : gᴴ * H * g = H := hg
  have h2 : g'ᴴ * H * g' = H := hg'
  show (g * g')ᴴ * H * (g * g') = H
  calc (g * g')ᴴ * H * (g * g') = g'ᴴ * (gᴴ * H * g) * g' := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = H := by rw [h1, h2]

theorem atTau_one (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau) : atTau θ V τ 1 = 1 :=
  (existsUnique_isAtTau V τ θ hθ 1 (one_mem_UH _)).unique (atTau_spec hθ V τ (one_mem_UH _))
    ⟨one_mem _, infMat_one V _, fun _ _ => infMat_one V _⟩

theorem atTau_mul (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau) {g g' : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (hg' : g' ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) :
    atTau θ V τ (g * g') = atTau θ V τ g * atTau θ V τ g' := by
  have a := atTau_spec hθ V τ hg
  have b := atTau_spec hθ V τ hg'
  refine (existsUnique_isAtTau V τ θ hθ _ (mul_mem_UH hg hg')).unique (atTau_spec hθ V τ (mul_mem_UH hg hg'))
    ⟨mul_mem a.1 b.1, ?_, fun τ' h => ?_⟩
  · rw [infMat_mul, a.2.1, b.2.1]
  · rw [infMat_mul, a.2.2 τ' h, b.2.2 τ' h, Matrix.one_mul]

theorem comm_of_mem (V : HSp D) {a k : GA D V} (ha : a ∈ GinfC V) (hk : k ∈ GfC V) : a * k = k * a := by
  have a2 : finHom V a = 1 := ha
  have k1 : infHom V k = 1 := hk
  refine mul_inv_eq_one.1 (eq_one_of_mem V _ ?_ ?_)
  · show infHom V _ = 1
    simp only [map_mul, map_inv, k1, mul_one, one_mul, mul_inv_cancel]
  · show finHom V _ = 1
    simp only [map_mul, map_inv, a2, mul_one, one_mul, mul_inv_cancel]

open Classical in

theorem entry_eq {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ) (V : HSp D) (τ : D.what₂.Tau)
    {g : Matrix (Fin V.rank) (Fin V.rank) ℂ} {h : GA D V} (hh : IsAtTau θ V τ g h) (i j : Fin V.rank) :
    (matHom V h).1 i j = (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j +
      σ (Pi.single τ (g i j - (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) i j)) := by
  refine sub_eq_zero.1 (hσ.ext _ ?_ fun τ' => ?_)
  · have a2 : (finHom V h).1 = (finHom V 1).1 := by rw [map_one]; exact congrArg Units.val hh.1
    have e : finPart D ((matHom V h).1 i j) = finPart D ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) :=
      congrFun (congrFun a2 i) j
    rw [RingHom.map_sub, RingHom.map_add, hσ.fin, e, add_zero, sub_self]
  · have e1 : θ τ' (infPart D ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j)) =
        (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) i j := congrFun (congrFun (infMat_one V (θ τ')) i) j
    have e2 : θ τ' (infPart D ((matHom V h).1 i j)) = infMat D.sp.cm.sig V.gram (θ τ') h i j := rfl
    rw [RingHom.map_sub, RingHom.map_add, RingHom.map_sub, RingHom.map_add, hσ.comp, e1, e2]
    by_cases c : τ' = τ
    · subst c
      rw [hh.2.1, Pi.single_eq_same]; ring
    · rw [hh.2.2 τ' c, Pi.single_eq_of_ne c]; ring

theorem isAtTau_inv (V : HSp D) (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) {h : GA D V} (hh : IsAtTau θ V τ g h) :
    IsAtTau θ V τ ((gramAt D V τ)⁻¹ * gᴴ * gramAt D V τ) h⁻¹ := by
  have hu : IsUnit (gramAt D V τ).det := by
    have : (gramAt D V τ).det = tauE D τ V.gram.det := (RingHom.map_det (tauE D τ) V.gram).symm
    rw [this]
    exact ((_root_.map_ne_zero _).2 (Formalism.L2.Theta.gram_det_ne V)).isUnit
  have h1 : gᴴ * gramAt D V τ * g = gramAt D V τ := hg
  have h2 : (gramAt D V τ)⁻¹ * gᴴ * gramAt D V τ * g = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, h1, Matrix.nonsing_inv_mul _ hu]
  have k : ∀ φ, infMat D.sp.cm.sig V.gram φ h * infMat D.sp.cm.sig V.gram φ h⁻¹ = 1 := fun φ => by
    rw [← infMat_mul, mul_inv_cancel, infMat_one]
  refine ⟨inv_mem hh.1, ?_, fun τ' c => ?_⟩
  · have := k (θ τ)
    rw [hh.2.1] at this
    rw [← Matrix.one_mul (infMat _ _ _ h⁻¹), ← h2, Matrix.mul_assoc _ g, this, Matrix.mul_one]
  · have := k (θ τ')
    rwa [hh.2.2 τ' c, Matrix.one_mul] at this

theorem continuousOn_atTau (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau) :
    ContinuousOn (atTau θ V τ) (Formalism.QuantumDeterminants.UH (gramAt D V τ)) := by
  classical
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : ContinuousAdd (AE D) := IsModuleTopology.toContinuousAdd (AF D.host.F) _
  have key : ∀ (i j : Fin V.rank), Continuous fun g : Matrix (Fin V.rank) (Fin V.rank) ℂ =>
      (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j +
        σ (Pi.single τ (g i j - (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) i j)) := fun i j =>
    continuous_const.add (hσ.cont.comp ((continuous_single (A := fun _ : D.what₂.Tau => ℂ) τ).comp
      ((continuous_id.matrix_elem i j).sub continuous_const)))
  rw [continuousOn_iff_continuous_restrict]
  refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨?_, ?_⟩)
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    refine ((key i j).comp continuous_subtype_val).congr fun g => ?_
    exact (entry_eq hσ V τ (atTau_spec hθ V τ g.2) i j).symm
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    have c : Continuous fun g : Formalism.QuantumDeterminants.UH (gramAt D V τ) => (gramAt D V τ)⁻¹ * g.1ᴴ * gramAt D V τ :=
      (continuous_const.matrix_mul continuous_subtype_val.matrix_conjTranspose).matrix_mul continuous_const
    refine ((key i j).comp c).congr fun g => ?_
    exact (entry_eq hσ V τ (isAtTau_inv V τ g.2 (atTau_spec hθ V τ g.2)) i j).symm

theorem atTau_laws : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D) (τ : D.what₂.Tau), (∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∃! h, IsAtTau θ V τ g h) ∧ atTau θ V τ 1 = 1 ∧ (∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ g' ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), atTau θ V τ (g * g') = atTau θ V τ g * atTau θ V τ g') ∧ (∀ g, ∀ k ∈ GfC V, atTau θ V τ g * k = k * atTau θ V τ g) ∧ ContinuousOn (atTau θ V τ) (Formalism.QuantumDeterminants.UH (gramAt D V τ)) :=
  fun _ θ hθ V τ => ⟨fun g hg => existsUnique_isAtTau V τ θ hθ g hg, atTau_one hθ V τ,
    fun _ hg _ hg' => atTau_mul hθ V τ hg hg', fun g _ hk => comm_of_mem V (atTau_mem V τ g) hk,
    continuousOn_atTau hθ V τ⟩

end GlobalTheory.PointAtPlaceHom

end
