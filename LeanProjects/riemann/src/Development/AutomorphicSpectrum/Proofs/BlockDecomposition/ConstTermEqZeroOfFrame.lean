import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CompatibleThetaRestrictions
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsometryOfLinearIndependent
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ConstTermConj

open GlobalTheory.Cusp GlobalTheory.AutomorphicL2Unitary GlobalTheory.MixModel

section Abstract

variable {G : Type} [Group G] [TopologicalSpace G] {Γ N₁ N₂ : Subgroup G}
  [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [DiscreteTopology Γ]
  [LocallyCompactSpace N₁] [LocallyCompactSpace N₂]

theorem constTermOn_eq_of_conj {φ : G → ℂ} (hφ : LeftInv Γ φ) {γ : G} (hγ : γ ∈ Γ)
    (hN : ∀ n, n ∈ N₁ ↔ γ * n * γ⁻¹ ∈ N₂) (x : G) :
    constTermOn Γ N₂ φ x = constTermOn Γ N₁ φ (γ⁻¹ * x) := by
  let e : N₁ ≃ₜ* N₂ :=
    { toFun := fun n => ⟨γ * n * γ⁻¹, (hN _).1 n.2⟩
      invFun := fun n => ⟨γ⁻¹ * n * γ, (hN _).2 (by simp [mul_assoc])⟩
      left_inv := fun n => by simp [mul_assoc]
      right_inv := fun n => by simp [mul_assoc]
      map_mul' := fun a b => by simp [mul_assoc]
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let m := e.toHomeomorph.toMeasurableEquiv
  have h := isFundamentalDomain_stdDom (Γ.subgroupOf N₂) (Measure.haar.map e)
  have hp : MeasurePreserving m Measure.haar (Measure.haar.map e) := ⟨m.measurable, rfl⟩
  have h' : IsFundamentalDomain (Γ.subgroupOf N₁) (m ⁻¹' stdDom (Γ.subgroupOf N₂)) Measure.haar :=
    h.preimage_of_equiv hp.quasiMeasurePreserving
      (e := fun δ => ⟨e.symm δ, mul_mem (mul_mem (inv_mem hγ) δ.2) hγ⟩)
      ⟨fun a b hab => Subtype.ext (e.symm.injective (congrArg Subtype.val hab)),
        fun δ => ⟨⟨e δ, mul_mem (mul_mem hγ δ.2) (inv_mem hγ)⟩, Subtype.ext (e.symm_apply_apply _)⟩⟩
      fun δ n => (map_mul e _ _).trans (congrArg (· * e n) (e.apply_symm_apply _))
  rw [constTermOn_eq h hφ, constTermOn_eq h' hφ, ← hp.setIntegral_preimage_emb m.measurableEmbedding,
    measureReal_def, measureReal_def, hp.measure_preimage h.nullMeasurableSet]
  refine congrArg _ (integral_congr_ae (.of_forall fun n => ?_))
  change φ (γ * n * γ⁻¹ * x) = φ (n * (γ⁻¹ * x))
  rw [mul_assoc, mul_assoc, hφ γ hγ]

end Abstract

variable {D : D7} {V : HSp D} {r : ℕ}

theorem rat_mulVec_inc {n m : ℕ} (A : Matrix (Fin n) (Fin m) D.host.E) (x : Fin m → D.host.E) :
    (rat A).mulVec (fun i => incA D (x i)) = fun i => incA D ((A.mulVec x) i) := by
  funext i
  simp [Matrix.mulVec, dotProduct, rat, map_sum]

theorem conj_conditions {C₁ C₂ : Matrix (Fin V.rank) (Fin r) D.host.E}
    (g₀ gi : Matrix (Fin V.rank) (Fin V.rank) D.host.E) (h1 : g₀ * gi = 1)
    (hC : g₀ * C₁ = C₂) (hC' : gi * C₂ = C₁) (hH : C₂ᴴ * V.gram * g₀ = C₁ᴴ * V.gram)
    (m : Mx D V.rank V.rank) (a1 : m ⬝ rat C₁ = 0) (a2 : rat (C₁ᴴ * V.gram) ⬝ m = 0)
    (a3 : ∀ x : Fin V.rank → D.host.E, (C₁ᴴ * V.gram).mulVec x = 0 →
      ∃ a : Fin r → AE D, m.mulVec (fun i => incA D (x i)) = (rat C₁).mulVec a) :
    (rat g₀ ⬝ m ⬝ rat gi) ⬝ rat C₂ = 0 ∧ rat (C₂ᴴ * V.gram) ⬝ (rat g₀ ⬝ m ⬝ rat gi) = 0 ∧
      ∀ x : Fin V.rank → D.host.E, (C₂ᴴ * V.gram).mulVec x = 0 →
        ∃ a : Fin r → AE D, (rat g₀ ⬝ m ⬝ rat gi).mulVec (fun i => incA D (x i)) = (rat C₂).mulVec a := by
  refine ⟨?_, ?_, fun x hx => ?_⟩
  · rw [Matrix.mul_assoc, ← rat_mul, hC', Matrix.mul_assoc, a1, Matrix.mul_zero]
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← rat_mul, hH, a2, Matrix.zero_mul]
  · have hy : (C₁ᴴ * V.gram).mulVec (gi.mulVec x) = 0 := by
      rw [← hH, Matrix.mulVec_mulVec, Matrix.mul_assoc (C₂ᴴ * V.gram) g₀ gi, h1, Matrix.mul_one, hx]
    obtain ⟨a, ha⟩ := a3 _ hy
    refine ⟨a, ?_⟩
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, rat_mulVec_inc, ha, Matrix.mulVec_mulVec, ← rat_mul, hC]

theorem conj_mem_NI {C₁ C₂ : Matrix (Fin V.rank) (Fin r) D.host.E} (γ : GA D V)
    (g₀ gi : Matrix (Fin V.rank) (Fin V.rank) D.host.E) (h1 : g₀ * gi = 1) (h2 : gi * g₀ = 1)
    (hu : g₀ᴴ * V.gram * g₀ = V.gram) (hm : mt V γ = rat g₀) (hmi : mt V γ⁻¹ = rat gi)
    (hC : g₀ * C₁ = C₂) {n : GA D V} (hn : n ∈ NI V C₁) : γ * n * γ⁻¹ ∈ NI V C₂ := by
  have hC' : gi * C₂ = C₁ := by rw [← hC, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  have hH : C₂ᴴ * V.gram * g₀ = C₁ᴴ * V.gram := by
    rw [← hC, Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc g₀ᴴ, hu]
  have ii' : rat g₀ ⬝ rat gi = (1 : Mx D V.rank V.rank) := by rw [← rat_mul, h1, rat_one]
  have hle : NI V C₁ ≤ (NI V C₂).comap (MulAut.conj γ).toMonoidHom := by
    refine (Subgroup.closure_le _).2 fun g hg => Subgroup.subset_closure ?_
    obtain ⟨a1, a2, a3⟩ := hg
    have em : (matHom V ((MulAut.conj γ).toMonoidHom g)).1 - 1 = rat g₀ ⬝ ((matHom V g).1 - 1) ⬝ rat gi := by
      have e : (matHom V ((MulAut.conj γ).toMonoidHom g)).1 = mt V γ ⬝ mt V g ⬝ mt V γ⁻¹ := rfl
      rw [e, hm, hmi, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, ii']
      rfl
    have := conj_conditions g₀ gi h1 hC hC' hH _ a1 a2 a3
    rw [← em] at this
    exact this
  exact hle hn

theorem rank_eq_of_isIsoFrame {C : Matrix (Fin V.rank) (Fin r) D.host.E} (h : IsIsoFrame V C) : C.rank = r := by
  have := LinearIndependent.rank_matrix (M := Cᵀ) h.2.1
  simpa [Matrix.rank_transpose] using this

theorem constTerm_eq_zero_of_frame : ∀ (D : D7) (V : HSp D) (r : ℕ) (C₁ C₂ : Matrix (Fin V.rank) (Fin r) D.host.E)
    (h₁ : IsIsoFrame V C₁) (h₂ : IsIsoFrame V C₂) (φ : GA D V → ℂ), (∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) →
    GlobalTheory.Cusp.constTerm (GlobalTheory.Cusp.frameFlag h₁) φ = 0 → GlobalTheory.Cusp.constTerm (GlobalTheory.Cusp.frameFlag h₂) φ = 0 := by
  intro D V r C₁ C₂ h₁ h₂ φ hφ h0
  have hθ : (1 / 2 : D.host.E) + star (1 / 2 : D.host.E) = 1 := by
    have e : star (1 / 2 : D.host.E) = 1 / 2 := by simp [star_div₀]
    rw [e, add_halves]
  have e₁ : C₁ᴴ * V.gram * C₁ = 0 := h₁.2.2
  have e₂ : C₂ᴴ * V.gram * C₂ = 0 := h₂.2.2
  obtain ⟨g₀, hu, hC⟩ := GlobalTheory.WittTrace.exists_isometry_mul_eq D.host.E (1 / 2) hθ V.rank r V.gram C₁ C₂
    (gram_conjTranspose V) (gram_isUnit_det V) (rank_eq_of_isIsoFrame h₁) (rank_eq_of_isIsoFrame h₂) (e₁.trans e₂.symm)
  obtain ⟨gi, hgi⟩ : ∃ gi, gi = V.gram⁻¹ * (g₀ᴴ * V.gram) := ⟨_, rfl⟩
  have h2 : gi * g₀ = 1 := by
    rw [hgi, Matrix.mul_assoc, hu, Matrix.nonsing_inv_mul _ (gram_isUnit_det V)]
  have h1 : g₀ * gi = 1 := mul_eq_one_comm.1 h2
  have hC' : gi * C₂ = C₁ := by rw [← hC, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  have hu' : giᴴ * V.gram * gi = V.gram := by
    calc giᴴ * V.gram * gi = giᴴ * (g₀ᴴ * V.gram * g₀) * gi := by rw [hu]
      _ = (g₀ * gi)ᴴ * V.gram * (g₀ * gi) := by rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = V.gram := by rw [h1]; simp
  have hh : adj (rat g₀) * (gA V * rat g₀) = gA V := by
    rw [← rat_conjTranspose, gA, ← rat_mul, ← rat_mul, ← Matrix.mul_assoc, hu]
  obtain ⟨γ, hm⟩ : ∃ γ : GA D V, mt V γ = rat g₀ := ⟨ofMat V (rat g₀) hh, mt_ofMat V _ hh⟩
  have hmi : mt V γ⁻¹ = rat gi := by
    have e := mt_mul_inv V γ
    rw [hm] at e
    calc mt V γ⁻¹ = (rat gi * rat g₀) * mt V γ⁻¹ := by rw [← rat_mul, h2, rat_one, Matrix.one_mul]
      _ = rat gi := by rw [Matrix.mul_assoc, e, Matrix.mul_one]
  have hγ : γ ∈ GQ V := (mem_GQ_iff V γ).2 (hm ▸ rat_mem g₀)
  have hN : ∀ n, n ∈ NA (frameFlag h₁) ↔ γ * n * γ⁻¹ ∈ NA (frameFlag h₂) := fun n => by
    rw [NA_frameFlag, NA_frameFlag]
    refine ⟨conj_mem_NI γ g₀ gi h1 h2 hu hm hmi hC, fun h => ?_⟩
    have := conj_mem_NI γ⁻¹ gi g₀ h2 h1 hu' hmi (by simpa using hm) hC' h
    simpa [mul_assoc] using this
  funext x
  exact (constTermOn_eq_of_conj hφ hγ hN x).trans (congrFun h0 _)

end GlobalTheory.CompanionTheory.ConstTermConj

end
