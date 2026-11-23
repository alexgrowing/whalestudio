import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacobianCoordinates
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RootPatterns
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RootHaarLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGPinLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocFactorAll
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.RightInvOfLattice
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.HaarMeasureUniqueness
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RootMeasureTransportDoubleCoset

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Amp.PinRoot

open Formalism.QuantumDeterminants Formalism.L2.SG.RealObj

section Loc

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

private lemma mulVec_mem_spanLt' {n r : ℕ} {e : Fin r → Fin n → ℂ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : ∀ b : Fin r, (A - 1) *ᵥ e b ∈ spanLt e b.1) (a : ℕ) :
    ∀ y ∈ spanLt e a, A *ᵥ y ∈ spanLt e a := by
  have hle : spanLt e a ≤ (spanLt e a).comap (Matrix.toLin' A) := by
    unfold spanLt
    rw [Submodule.span_le]
    rintro _ ⟨b, hb, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, Matrix.toLin'_apply]
    have hsplit : A *ᵥ e b = e b + (A - 1) *ᵥ e b := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
    rw [hsplit]
    refine add_mem (Submodule.subset_span ⟨b, hb, rfl⟩) ?_
    refine Submodule.span_mono (Set.image_mono ?_) (hA b)
    intro c hc
    exact lt_trans (show c.1 < b.1 from hc) (show b.1 < a from hb)
  intro y hy
  exact hle hy

private lemma inN_mul' {n r : ℕ} {ε : Fin n → Bool} {e : Fin r → Fin n → ℂ} {z : Fin n → ℂ}
    {A B : Matrix (Fin n) (Fin n) ℂ} (hA : InN ε e z A) (hB : InN ε e z B) : InN ε e z (A * B) := by
  have key : ∀ x : Fin n → ℂ, (A * B - 1) *ᵥ x = A *ᵥ ((B - 1) *ᵥ x) + (A - 1) *ᵥ x := by
    intro x
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec]
    abel
  refine ⟨⟨fun a => ?_, ?_⟩, fun y hy => ?_⟩
  · rw [key]; exact add_mem (mulVec_mem_spanLt' hA.1.1 _ _ (hB.1.1 a)) (hA.1.1 a)
  · rw [key]; exact add_mem (mulVec_mem_spanLt' hA.1.1 _ _ hB.1.2) hA.1.2
  · rw [key]; exact add_mem (mulVec_mem_spanLt' hA.1.1 _ _ (hB.2 y hy)) (hA.2 y hy)

theorem ninf_mul {a b : X.B.I.Ginf} (ha : a ∈ X.NinfU u) (hb : b ∈ X.NinfU u) : a * b ∈ X.NinfU u := by
  intro v
  exact inN_mul' (ha v) (hb v)

private lemma mulVec_mem_spanLt_of_left_inv {n r : ℕ} {e : Fin r → Fin n → ℂ} {A Ai : Matrix (Fin n) (Fin n) ℂ}
    (hA : ∀ b : Fin r, (A - 1) *ᵥ e b ∈ spanLt e b.1) (h2 : Ai * A = 1) (a : ℕ) :
    ∀ y ∈ spanLt e a, Ai *ᵥ y ∈ spanLt e a := by
  intro y hy
  let f : spanLt e a →ₗ[ℂ] spanLt e a := (Matrix.toLin' A).restrict (fun x hx => mulVec_mem_spanLt' hA a x hx)
  have hinj : Function.Injective f := by
    intro x x' hxx
    have h := congrArg (fun w : spanLt e a => Ai *ᵥ (w : Fin n → ℂ)) hxx
    have hc : ∀ w : spanLt e a, ((f w : spanLt e a) : Fin n → ℂ) = A *ᵥ (w : Fin n → ℂ) := fun w => rfl
    simp only [hc, Matrix.mulVec_mulVec, h2, Matrix.one_mulVec] at h
    exact Subtype.ext h
  obtain ⟨w, hw⟩ := (LinearMap.injective_iff_surjective.mp hinj) ⟨y, hy⟩
  have hwv : A *ᵥ (w : Fin n → ℂ) = y := congrArg Subtype.val hw
  have hw' : (w : Fin n → ℂ) = Ai *ᵥ y := by
    rw [← hwv, Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
  rw [← hw']
  exact w.2

private lemma inN_of_left_inv {n r : ℕ} {ε : Fin n → Bool} {e : Fin r → Fin n → ℂ} {z : Fin n → ℂ}
    {A Ai : Matrix (Fin n) (Fin n) ℂ} (h2 : Ai * A = 1) (hA : InN ε e z A) : InN ε e z Ai := by
  have key : ∀ x : Fin n → ℂ, (Ai - 1) *ᵥ x = -(Ai *ᵥ ((A - 1) *ᵥ x)) := by
    intro x
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec, h2]
    abel
  refine ⟨⟨fun a => ?_, ?_⟩, fun y hy => ?_⟩
  · rw [key]; exact neg_mem (mulVec_mem_spanLt_of_left_inv hA.1.1 h2 _ _ (hA.1.1 a))
  · rw [key]; exact neg_mem (mulVec_mem_spanLt_of_left_inv hA.1.1 h2 _ _ hA.1.2)
  · rw [key]; exact neg_mem (mulVec_mem_spanLt_of_left_inv hA.1.1 h2 _ _ (hA.2 y hy))

private lemma uMat_expU_inv_mul {n : ℕ} {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) : uMat g⁻¹ * uMat g = 1 := by
  simp [uMat]

theorem ninf_inv {a : X.B.I.Ginf} (ha : a ∈ X.NinfU u) : a⁻¹ ∈ X.NinfU u := by
  intro v
  exact inN_of_left_inv (uMat_expU_inv_mul (a v)) (ha v)

theorem sinf_conj {a : X.B.I.Ginf} (ha : a ∈ X.SinfU u) {n : X.B.I.Ginf} (hn : n ∈ X.NinfU u) :
    a * n * a⁻¹ ∈ X.NinfU u := by
  obtain ⟨h, hh, m, hm, rfl⟩ := Formalism.L2.SG.Pf.Sinf.levi X u ha
  have hmn : m * n * m⁻¹ ∈ X.NinfU u := ninf_mul X u (ninf_mul X u hm hn) (ninf_inv X u hm)
  have hc := Formalism.L2.SG.Pf.Sinf.conj_ninf X u hh hmn
  have e : h * m * n * (h * m)⁻¹ = h * (m * n * m⁻¹) * h⁻¹ := by group
  rw [e]
  exact hc

theorem sinf_nh {a : X.B.I.Ginf} (ha : a ∈ X.SinfU u) (v : InfinitePlace X.B.I.F) :
    a v ∈ Formalism.L2.SG.Pf.WuDec.NHloc X u v := by
  obtain ⟨h, hh, m, hm, rfl⟩ := Formalism.L2.SG.Pf.Sinf.levi X u ha
  have hc := Formalism.L2.SG.Pf.Sinf.conj_ninf X u hh hm
  refine ⟨h v * m v * (h v)⁻¹, hc v, h v, fun y hy => hh v y hy, ?_⟩
  show h v * m v = h v * m v * (h v)⁻¹ * h v
  group

end Loc

end GlobalTheory.Amp.PinRoot

noncomputable section

namespace GlobalTheory.Amp.PinRoot

open Formalism.QuantumDeterminants Formalism.L2.SG.RealObj

section Gen

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]

theorem haar_conj (S T : Set G) (g : G) (hST : ∀ z, g * z * g⁻¹ ∈ T ↔ z ∈ S) {μ : Measure G}
    (h : SigmaFinite μ ∧ μ ≠ 0 ∧ μ Sᶜ = 0 ∧ ∀ s ∈ S, μ.map (fun x => s * x) = μ) :
    SigmaFinite (μ.map fun y => g * y * g⁻¹) ∧ (μ.map fun y => g * y * g⁻¹) ≠ 0 ∧
      (μ.map fun y => g * y * g⁻¹) Tᶜ = 0 ∧
      ∀ r ∈ T, (μ.map fun y => g * y * g⁻¹).map (fun x => r * x) = μ.map fun y => g * y * g⁻¹ := by
  obtain ⟨hσ, h0, hS, hinv⟩ := h
  have hm : ∀ x : G, Measurable (fun y : G => x * y * x⁻¹) := fun x =>
    (measurable_const_mul x).mul_const x⁻¹
  let E : G ≃ᵐ G :=
    { toFun := fun y => g * y * g⁻¹
      invFun := fun y => g⁻¹ * y * g
      left_inv := fun y => by simp [mul_assoc]
      right_inv := fun y => by simp [mul_assoc]
      measurable_toFun := hm g
      measurable_invFun := (measurable_const_mul g⁻¹).mul_const g }
  have hE : (fun y : G => g * y * g⁻¹) = ⇑E := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hE]
    refine SigmaFinite.of_map (μ.map E) E.symm.measurable.aemeasurable ?_
    have hback : (μ.map E).map E.symm = μ := by
      rw [Measure.map_map E.symm.measurable E.measurable, MeasurableEquiv.symm_comp_self, Measure.map_id]
    rw [hback]
    exact hσ
  · exact (Measure.map_ne_zero_iff (hm g).aemeasurable).mpr h0
  · rw [hE, MeasurableEquiv.map_apply]
    have hpre : ⇑E ⁻¹' Tᶜ = Sᶜ := by
      ext z
      simp only [Set.mem_preimage, Set.mem_compl_iff]
      exact not_congr (hST z)
    rw [hpre]
    exact hS
  · intro r hr
    have hs : g⁻¹ * r * g ∈ S := by
      rw [← hST]
      rw [show g * (g⁻¹ * r * g) * g⁻¹ = r by group]
      exact hr
    rw [Measure.map_map (measurable_const_mul r) (hm g)]
    have hcomp : (fun x : G => r * x) ∘ (fun y : G => g * y * g⁻¹) =
        (fun y : G => g * y * g⁻¹) ∘ (fun x : G => (g⁻¹ * r * g) * x) := by
      funext y
      simp only [Function.comp]
      group
    rw [hcomp, ← Measure.map_map (hm g) (measurable_const_mul _), hinv _ hs]

theorem haar_smul {S : Set G} {μ : Measure G}
    (h : SigmaFinite μ ∧ μ ≠ 0 ∧ μ Sᶜ = 0 ∧ ∀ s ∈ S, μ.map (fun x => s * x) = μ) {d : ℝ≥0∞} (h0 : d ≠ 0)
    (ht : d ≠ ⊤) :
    SigmaFinite (d • μ) ∧ d • μ ≠ 0 ∧ (d • μ) Sᶜ = 0 ∧ ∀ s ∈ S, (d • μ).map (fun x => s * x) = d • μ := by
  obtain ⟨hσ, h0', hS, hinv⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Formalism.L2.SG.NGPin.sf_smul μ ht
  · intro hz
    have h1 : (d • μ) Set.univ = 0 := by rw [hz]; simp
    rw [Measure.smul_apply, smul_eq_mul] at h1
    exact (mul_ne_zero h0 (Measure.measure_univ_ne_zero.mpr h0')) h1
  · rw [Measure.smul_apply, hS, smul_zero]
  · intro s hs
    rw [Measure.map_smul, hinv s hs]

end Gen

theorem eq_one_of_smul {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ] (h0 : μ ≠ 0)
    {c : ℝ≥0∞} (h : μ = c • μ) : c = 1 := by
  obtain ⟨k, hk⟩ : ∃ k, μ (spanningSets μ k) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply h0
    have hu : μ (⋃ k, spanningSets μ k) = 0 := measure_iUnion_null hcon
    rw [iUnion_spanningSets] at hu
    exact Measure.measure_univ_eq_zero.mp hu
  have htop : μ (spanningSets μ k) ≠ ⊤ := (measure_spanningSets_lt_top μ k).ne
  have hx : μ (spanningSets μ k) = c * μ (spanningSets μ k) := by
    have e1 := congrArg (fun m : Measure α => m (spanningSets μ k)) h
    simp only [Measure.smul_apply, smul_eq_mul] at e1
    exact e1
  have h3 : c * μ (spanningSets μ k) / μ (spanningSets μ k) =
      μ (spanningSets μ k) / μ (spanningSets μ k) := by rw [← hx]
  rwa [ENNReal.mul_div_cancel_right hk htop, ENNReal.div_self hk htop] at h3

private lemma inN_one' {n r : ℕ} (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) :
    InN ε e z 1 :=
  ⟨⟨fun a => by simp, by simp⟩, fun y _ => by simp⟩

section Loc

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem conj_loc_of {a : X.B.I.Ginf} (ha : a ∈ X.SinfU u) (v : InfinitePlace X.B.I.F) {n : Formalism.REAL.UJ (X.B.I.ε v)}
    (hn : n ∈ Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun b => rv X.B.I v (X.eR b)) (rv X.B.I v (X.zR u))) :
    a v * n * (a v)⁻¹ ∈
      Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun b => rv X.B.I v (X.eR b)) (rv X.B.I v (X.zR u)) := by
  classical
  let n' : X.B.I.Ginf := Function.update 1 v n
  have hn' : n' ∈ X.NinfU u := by
    intro w
    by_cases hw : w = v
    · subst hw
      have e : n' w = n := by simp [n']
      show InN _ _ _ (uMat (n' w))
      rw [e]
      exact hn
    · have e : n' w = 1 := by simp [n', Function.update_of_ne hw]
      show InN _ _ _ (uMat (n' w))
      rw [e]
      exact inN_one' _ _ _
  have h := sinf_conj X u ha hn' v
  have e : n' v = n := by simp [n']
  show InN _ _ _ (uMat (a v * n * (a v)⁻¹))
  rw [← e]
  exact h

end Loc

end GlobalTheory.Amp.PinRoot

noncomputable section

namespace GlobalTheory.Amp.PinRoot

open Formalism.QuantumDeterminants Formalism.L2.SG.RealObj

section Glob

variable {D : D7} (X : HidaSetting D)

def kst : ℝ≥0∞ := ENNReal.ofReal (D.host.ka / (X.B.g : ℝ) / Real.pi)

theorem kst_pos : 0 < D.host.ka / (X.B.g : ℝ) / Real.pi := by
  have hg : (0 : ℝ) < (X.B.g : ℝ) := by
    rw [X.g_eq]
    exact_mod_cast Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos
  have hv : 0 < D.host.v := by
    unfold Formalism.BasicNotions.Host.v Formalism.BasicNotions.Host.rdE
    apply div_pos _ two_pos
    apply Real.rpow_pos_of_pos
    exact abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero D.host.E)
  have hka : 0 < D.host.ka := by
    unfold Formalism.BasicNotions.Host.ka
    exact div_pos Real.pi_pos hv
  exact div_pos (div_pos hka hg) Real.pi_pos

theorem kst_ne_zero : kst X ≠ 0 := by
  unfold kst
  exact (ENNReal.ofReal_pos.mpr (kst_pos X)).ne'

theorem kst_ne_top : kst X ≠ ⊤ := by
  unfold kst
  exact ENNReal.ofReal_ne_top

private lemma smul_measure_ne_zero {α : Type*} [MeasurableSpace α] {c : ℝ≥0∞} {μ : Measure α} (hc : c ≠ 0)
    (hμ : μ ≠ 0) : c • μ ≠ 0 := by
  intro hz
  have h1 : (c • μ) Set.univ = 0 := by rw [hz]; simp
  rw [Measure.smul_apply, smul_eq_mul] at h1
  exact (mul_ne_zero hc (Measure.measure_univ_ne_zero.mpr hμ)) h1

theorem pin_pi (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (γ : X.B.I.Ginf) (hrep : IsPtRep X u u' w γ)
    (μ : Measure X.B.I.Ginf) (hH : IsHaarOnSet X.B.I (StInf X u u' γ) μ)
    (hm : μ.map (stCoord X u' w γ) = muStab X w) :
    ∃ m : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v)), (∀ v, IsHaarLoc (Formalism.L2.SG.NGPin.StV X u u' γ v) (m v)) ∧
      (∀ v, (m v).map (Formalism.L2.SG.NGPin.stCoordV X u' w γ v) =
        Measure.pi (fun _ : FreeE w => kst X • (volume : Measure ℂ))) ∧ μ = Measure.pi m := by
  classical
  have hsfk : SigmaFinite (kst X • (volume : Measure ℂ)) := Formalism.L2.SG.NGPin.sf_smul _ (kst_ne_top X)
  have hP := fun v => Formalism.L2.SG.NGPin.placeHaar_holds D X u u' w γ hrep v
  choose μv cv hμv hc0 hctop hmap using hP
  set K : ℝ≥0∞ := kst X ^ Fintype.card (FreeE w) with hK
  have hK0 : K ≠ 0 := pow_ne_zero _ (kst_ne_zero X)
  have hKt : K ≠ ⊤ := ENNReal.pow_ne_top (kst_ne_top X)
  have hpiK : Measure.pi (fun _ : FreeE w => kst X • (volume : Measure ℂ)) =
      K • Measure.pi (fun _ : FreeE w => (volume : Measure ℂ)) := by
    rw [Formalism.L2.SG.NGPin.pi_smul (fun _ : FreeE w => (volume : Measure ℂ)) (fun _ => kst X),
      Finset.prod_const, Finset.card_univ]
  have hd0 : ∀ v, K / cv v ≠ 0 := fun v => ENNReal.div_ne_zero.mpr ⟨hK0, hctop v⟩
  have hdt : ∀ v, K / cv v ≠ ⊤ := fun v => ENNReal.div_ne_top hKt (hc0 v)
  have hpv0 : Measure.pi (fun _ : FreeE w => (volume : Measure ℂ)) ≠ 0 := by
    intro h0
    have h1 := congrArg (fun m : Measure (FreeE w → ℂ) => m Set.univ) h0
    simp only [Measure.pi_univ, Measure.coe_zero, Pi.zero_apply] at h1
    exact (Finset.prod_ne_zero_iff.mpr (fun _ _ => by simp)) h1
  let m : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v)) := fun v => (K / cv v) • μv v
  have hmH : ∀ v, IsHaarLoc (Formalism.L2.SG.NGPin.StV X u u' γ v) (m v) := fun v =>
    haar_smul (hμv v) (hd0 v) (hdt v)
  have hmmap : ∀ v, (m v).map (Formalism.L2.SG.NGPin.stCoordV X u' w γ v) =
      Measure.pi (fun _ : FreeE w => kst X • (volume : Measure ℂ)) := by
    intro v
    simp only [m]
    rw [Measure.map_smul, hmap v, smul_smul, ENNReal.div_mul_cancel (hc0 v) (hctop v), hpiK]
  have hae : ∀ v, AEMeasurable (Formalism.L2.SG.NGPin.stCoordV X u' w γ v) (m v) := by
    intro v
    by_contra hn
    have h0 := Measure.map_of_not_aemeasurable hn
    rw [hmmap v, hpiK] at h0
    exact smul_measure_ne_zero hK0 hpv0 h0
  haveI : ∀ v, SigmaFinite (m v) := fun v => (hmH v).1
  haveI : ∀ v, SigmaFinite ((m v).map (Formalism.L2.SG.NGPin.stCoordV X u' w γ v)) := fun v => by
    rw [hmmap v]; infer_instance
  have hpimap : (Measure.pi m).map (stCoord X u' w γ) = muStab X w := by
    rw [Formalism.L2.SG.NGPin.stCoord_eq X u' w γ, Measure.pi_map_pi hae]
    simp only [hmmap]
    rfl
  refine ⟨m, hmH, hmmap, ?_⟩
  have hSt := Formalism.L2.SG.NGPin.stInf_eq_pi X u u' γ
  have hpiH : IsHaarOnSet X.B.I (StInf X u u' γ) (Measure.pi m) := by
    refine ⟨inferInstance, ?_, ?_, ?_⟩
    · intro h0
      have h1 := congrArg (fun μ' : Measure X.B.I.Ginf => μ' Set.univ) h0
      simp only [Measure.pi_univ, Measure.coe_zero, Pi.zero_apply] at h1
      exact (Finset.prod_ne_zero_iff.mpr (fun v _ => Measure.measure_univ_ne_zero.mpr (hmH v).2.1)) h1
    · rw [hSt]
      have hsub : (Set.univ.pi (Formalism.L2.SG.NGPin.StV X u u' γ))ᶜ ⊆
          ⋃ v, Function.eval v ⁻¹' (Formalism.L2.SG.NGPin.StV X u u' γ v)ᶜ := by
        intro x hx
        simp only [Set.mem_compl_iff, Set.mem_univ_pi, not_forall] at hx
        obtain ⟨v, hv⟩ := hx
        exact Set.mem_iUnion.mpr ⟨v, hv⟩
      refine measure_mono_null hsub (measure_iUnion_null fun v => ?_)
      exact Measure.pi_eval_preimage_null _ (hmH v).2.2.1
    · intro s hs
      rw [hSt] at hs
      have hinv : ∀ v, (m v).map (fun y => s v * y) = m v := fun v => (hmH v).2.2.2 (s v) (hs v (Set.mem_univ v))
      haveI : ∀ v, SigmaFinite ((m v).map (fun y => s v * y)) := fun v => by rw [hinv v]; infer_instance
      have e : (fun x : X.B.I.Ginf => s * x) = fun x v => (fun y => s v * y) (x v) := rfl
      rw [e, Measure.pi_map_pi (fun v => (measurable_const_mul (s v)).aemeasurable)]
      simp only [hinv]
  have hclosed : IsClosed (StInf X u u' γ) := by
    rw [← Formalism.L2.SG.NGPin.coe_StG X u u' γ]
    exact Formalism.L2.SG.NGPin.isClosed_StG X u u' γ
  have hgrp : QPK.IsGrp (StInf X u u' γ) := by
    rw [← Formalism.L2.SG.NGPin.coe_StG X u u' γ]
    exact ⟨(Formalism.L2.SG.NGPin.StG X u u' γ).one_mem, fun a ha b hb => (Formalism.L2.SG.NGPin.StG X u u' γ).mul_mem ha hb,
      fun a ha => (Formalism.L2.SG.NGPin.StG X u u' γ).inv_mem ha⟩
  obtain ⟨c, hc0', hct', hμc⟩ := QPK.haar_measure_uniqueness X.B.I.Ginf (StInf X u u' γ) hclosed hgrp μ (Measure.pi m) hH hpiH
  have hS : muStab X w = c • muStab X w := by
    have e := congrArg (fun μ' : Measure X.B.I.Ginf => μ'.map (stCoord X u' w γ)) hμc
    simp only [Measure.map_smul] at e
    rw [hm, hpimap] at e
    exact e
  obtain ⟨K', hK'0, hK't, hK'⟩ := Formalism.L2.SG.NGPin.muStab_eq X w
  haveI : SigmaFinite (muStab X w) := by
    rw [hK']; exact Formalism.L2.SG.NGPin.sf_smul _ hK't
  have hne : muStab X w ≠ 0 := by
    rw [hK']
    refine smul_measure_ne_zero hK'0 ?_
    intro h1
    have h2 := congrArg (fun μ' : Measure (InfinitePlace X.B.I.F → FreeE w → ℂ) => μ' Set.univ) h1
    simp only [Measure.pi_univ, Measure.coe_zero, Pi.zero_apply] at h2
    exact (Finset.prod_ne_zero_iff.mpr (fun _ _ => Finset.prod_ne_zero_iff.mpr (fun _ _ => by simp))) h2
  have hc1 := eq_one_of_smul (muStab X w) hne hS
  rw [hμc, hc1, one_smul]

private lemma one_mem_Nset (k r : ℕ) :
    (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ Formalism.QuantumDeterminants.Nset k r := by
  refine ⟨?_, fun a i _ => Matrix.one_apply, fun i j _ _ _ => Matrix.one_apply⟩
  show (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ᴴ * Formalism.QuantumDeterminants.Hpk k r * 1 = Formalism.QuantumDeterminants.Hpk k r
  simp

end Glob

end GlobalTheory.Amp.PinRoot

noncomputable section

namespace GlobalTheory.Amp.PinRoot

open Formalism.QuantumDeterminants Formalism.L2.SG.RealObj

section Base

variable {D : D7} (X : HidaSetting D)

theorem root_base {θ : ℝ} (C : Choice X θ) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (γ : X.B.I.Ginf)
    (τ : D.what₂.Tau) (hrep : IsPtRep X u u' w γ) (m : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ))))
    (hH : IsHaarLoc (Formalism.L2.SG.NGPin.StV X u u' γ (vOf X τ)) m)
    (hm : m.map (Formalism.L2.SG.NGPin.stCoordV X u' w γ (vOf X τ)) =
      Measure.pi (fun _ : FreeE w => kst X • (volume : Measure ℂ))) :
    IsRootMeasR D (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (Formalism.MainNotions.S.ThB.ptLoc D τ w)
      (trG (C.Q τ) (C.Qi τ) (γ (vOf X τ))) (m.map (Formalism.L2.SG.RealConjugatorData.cMr C γ τ)) := by
  have hst := Formalism.L2.SG.RootPatterns.stCoordV_comp (C := C) (u' := u') (w := w) (γ := γ) (τ := τ)
  have hZ := Formalism.L2.SG.RealFrameCoordinates.zhat_conjugator_eq_point (C := C) (u := u) (u' := u') (w := w) (γ := γ) (hrep := hrep) (τ := τ)
  have hmeasR : Measurable (Formalism.MainNotions.S.rootCoords D.R.k D.R.rS (zB X (C.Qi τ) u' τ) (Formalism.MainNotions.S.ThB.ptLoc D τ w)) :=
    GlobalTheory.Amp.RootMove.measurable_rootCoords _ _
  have hcm := (Formalism.L2.SG.RealConjugatorData.cMr_measEmb C γ τ)
  unfold IsRootMeasR
  refine ⟨1, (one_mem_Nset _ _), 1, (one_mem_Nset _ _), trG (C.Q τ) (C.Qi τ) (γ (vOf X τ)), by simp, hZ,
    m.map (Formalism.L2.SG.RealConjugatorData.cMr C γ τ), ?_, ?_, ?_⟩
  · rw [hcm.map_apply]
    refine measure_mono_null ?_ hH.2.2.1
    intro y hy hyS
    exact hy ((Formalism.L2.SG.RealConjugatorData.stV_iff (C := C) (γ := γ) (τ := τ) (u := u) (u' := u') y).1 hyS)
  · rw [Measure.map_map hmeasR hcm.measurable]
    set E := MeasurableEquiv.piCongrLeft (fun _ : Formalism.L2.SG.RealObj.FreeE w => ℂ) (Formalism.L2.SG.RootPatterns.idxF τ w)
      with hEdef
    have hg : Measurable (Formalism.MainNotions.S.rootCoords D.R.k D.R.rS (zB X (C.Qi τ) u' τ) (Formalism.MainNotions.S.ThB.ptLoc D τ w) ∘
        Formalism.L2.SG.RealConjugatorData.cMr C γ τ) := hmeasR.comp hcm.measurable
    have e2 : m.map (Formalism.MainNotions.S.rootCoords D.R.k D.R.rS (zB X (C.Qi τ) u' τ) (Formalism.MainNotions.S.ThB.ptLoc D τ w) ∘
        Formalism.L2.SG.RealConjugatorData.cMr C γ τ) =
        (m.map (E ∘ (Formalism.MainNotions.S.rootCoords D.R.k D.R.rS (zB X (C.Qi τ) u' τ) (Formalism.MainNotions.S.ThB.ptLoc D τ w) ∘
          Formalism.L2.SG.RealConjugatorData.cMr C γ τ))).map E.symm := by
      rw [Measure.map_map E.symm.measurable (E.measurable.comp hg)]
      congr 1
    rw [e2]
    have e3 : E ∘ (Formalism.MainNotions.S.rootCoords D.R.k D.R.rS (zB X (C.Qi τ) u' τ) (Formalism.MainNotions.S.ThB.ptLoc D τ w) ∘
        Formalism.L2.SG.RealConjugatorData.cMr C γ τ) = Formalism.L2.SG.NGPin.stCoordV X u' w γ (vOf X τ) := by
      rw [hst]
    rw [e3, hm]
    haveI : SigmaFinite (kst X • (volume : Measure ℂ)) := Formalism.L2.SG.NGPin.sf_smul _ (kst_ne_top X)
    have hmp0 := MeasureTheory.measurePreserving_piCongrLeft
      (fun _ : Formalism.L2.SG.RealObj.FreeE w => kst X • (volume : Measure ℂ)) (Formalism.L2.SG.RootPatterns.idxF τ w)
    have hmp := MeasureTheory.MeasurePreserving.symm _ hmp0
    rw [hmp.map_eq]
    rw [Formalism.L2.SG.NGPin.pi_smul (fun _ : ↥(Formalism.MainNotions.S.rootPat (Formalism.MainNotions.S.ThB.ptLoc D τ w)) => (volume : Measure ℂ))
      (fun _ => kst X)]
    rw [← MeasureTheory.volume_pi]
    congr 1
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe]
    unfold kst
    rw [← ENNReal.ofReal_pow (kst_pos X).le]
    congr 2
    have hg : (X.B.g : ℝ) = gg D := by
      rw [X.g_eq]
      simp [gg]
    rw [hg]
    field_simp
  · simp [Measure.map_id']

end Base

end GlobalTheory.Amp.PinRoot

noncomputable section

namespace GlobalTheory.Amp.PinRoot

open Formalism.QuantumDeterminants Formalism.L2.SG.RealObj

section Main

variable {D : D7} (X : HidaSetting D)

theorem conj_loc (u : D.what₂.Word) {a : X.B.I.Ginf} (ha : a ∈ X.SinfU u) (v : InfinitePlace X.B.I.F)
    (n : Formalism.REAL.UJ (X.B.I.ε v)) :
    a v * n * (a v)⁻¹ ∈
      Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun b => rv X.B.I v (X.eR b)) (rv X.B.I v (X.zR u)) ↔
    n ∈ Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun b => rv X.B.I v (X.eR b)) (rv X.B.I v (X.zR u)) := by
  constructor
  · intro h
    have h2 := conj_loc_of X u (Formalism.L2.SG.Pf.Sinf.sinf_inv' X u ha) v h
    have e : a⁻¹ v * (a v * n * (a v)⁻¹) * (a⁻¹ v)⁻¹ = n := by
      rw [Pi.inv_apply]; group
    rwa [e] at h2
  · exact conj_loc_of X u ha v

theorem sinf_conj_iff (u : D.what₂.Word) {a : X.B.I.Ginf} (ha : a ∈ X.SinfU u) (n : X.B.I.Ginf) :
    a * n * a⁻¹ ∈ X.NinfU u ↔ n ∈ X.NinfU u := by
  constructor
  · intro h
    have h2 := sinf_conj X u (Formalism.L2.SG.Pf.Sinf.sinf_inv' X u ha) h
    have e : a⁻¹ * (a * n * a⁻¹) * a⁻¹⁻¹ = n := by group
    rwa [e] at h2
  · exact sinf_conj X u ha

private lemma uMat_mul_flag_measures {n : ℕ} {ε : Fin n → Bool} (g h : Formalism.REAL.UJ ε) :
    uMat (g * h) = uMat g * uMat h := rfl

variable {θ : ℝ} (C : Choice X θ) (τ : D.what₂.Tau)

theorem trG_mul (x y : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    trG (C.Q τ) (C.Qi τ) (x * y) = trG (C.Q τ) (C.Qi τ) x * trG (C.Q τ) (C.Qi τ) y := by
  have hQ : C.Q τ * C.Qi τ = 1 := (C.isT τ).2.1
  simp only [trG, uMat_mul_flag_measures, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (C.Q τ) (C.Qi τ), hQ, Matrix.one_mul]

theorem trG_inv (x : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    trG (C.Q τ) (C.Qi τ) x⁻¹ = (trG (C.Q τ) (C.Qi τ) x)⁻¹ := by
  have hQ : C.Q τ * C.Qi τ = 1 := (C.isT τ).2.1
  have hQi : C.Qi τ * C.Q τ = 1 := (C.isT τ).1
  symm
  apply Matrix.inv_eq_left_inv
  simp only [trG, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (C.Q τ) (C.Qi τ), hQ, Matrix.one_mul, ← Matrix.mul_assoc (uMat x⁻¹) (uMat x),
    uMat_expU_inv_mul, Matrix.one_mul, hQi]

theorem cMr_trG (γ : X.B.I.Ginf) (y : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    Matrix.of (Formalism.L2.SG.RealConjugatorData.cMr C γ τ y) =
      trG (C.Q τ) (C.Qi τ) ((γ (vOf X τ))⁻¹ * y * γ (vOf X τ)) := by
  show C.Qi τ * (uMat (γ (vOf X τ)))⁻¹ * uMat y * (uMat (γ (vOf X τ)) * C.Q τ) =
    trG (C.Q τ) (C.Qi τ) ((γ (vOf X τ))⁻¹ * y * γ (vOf X τ))
  rw [trG, uMat_mul_flag_measures, uMat_mul_flag_measures, Formalism.L2.SG.RealConjugatorData.uMat_inv']
  simp only [Matrix.mul_assoc]

private lemma trG_mem_UH {D : D7} {X : HidaSetting D} {θ : ℝ} (C : Choice X θ) (τ : D.what₂.Tau)
    (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    trG (C.Q τ) (C.Qi τ) γ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) := by
  have hQ : C.Q τ * C.Qi τ = 1 := (C.isT τ).2.1
  have hH : (C.Q τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * C.Q τ = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := (C.isT τ).2.2.1
  have hU : (uMat γ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * uMat γ = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := γ.2
  show (trG (C.Q τ) (C.Qi τ) γ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * trG (C.Q τ) (C.Qi τ) γ = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS
  rw [← hH]
  unfold trG
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (C.Q τ) (C.Qi τ), hQ, Matrix.one_mul,
    ← Matrix.mul_assoc (C.Qi τ)ᴴ (C.Q τ)ᴴ, ← Matrix.conjTranspose_mul, hQ, Matrix.conjTranspose_one, Matrix.one_mul,
    ← Matrix.mul_assoc (Formalism.REAL.Jm (X.B.I.ε (vOf X τ))) (uMat γ)]
  rw [← Matrix.mul_assoc (uMat γ)ᴴ (Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * uMat γ) (C.Q τ),
    ← Matrix.mul_assoc (uMat γ)ᴴ (Formalism.REAL.Jm (X.B.I.ε (vOf X τ))) (uMat γ), hU]

end Main

theorem pinned_root : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (θ : ℝ) (C : Choice X θ) (u u' : D.what₂.Word) (s : TT Y u u') (w : Point D.host.E (D.R.rS + 1)) (μR : Measure X.B.I.Ginf), Formalism.L2.SG.VolPin.IsPinnedR s w μR → ∃ μl : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v)), μR = Measure.pi μl ∧ (∀ v, Formalism.L2.SG.RealObj.IsHaarLoc (Formalism.L2.SG.RealObj.StSet (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u))) (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u'))) (s.pt.1 v)) (μl v)) ∧ IsHaarOnSet X.B.I (Formalism.L2.SG.TermOp.Vanish.Rset s) μR ∧ ∀ τ, ∃ p, IsRootMeasR D (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) p (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (s.pt.1 (vOf X τ))) ((μl (vOf X τ)).map (fun y => Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) ((s.pt.1 (vOf X τ))⁻¹ * y * (s.pt.1 (vOf X τ)))))) := by
  intro D X Y θ C u u' s w μR h
  obtain ⟨γw, s0, s1, μw, hrep, hs0, hs1, hpt, hH, hm, hμR⟩ := h
  obtain ⟨m, hmH, hmmap, hμw⟩ := pin_pi X u u' w γw hrep μw hH hm
  haveI : ∀ v, SigmaFinite (m v) := fun v => (hmH v).1
  have hcjm : ∀ v, Measurable (fun y : Formalism.REAL.UJ (X.B.I.ε v) => s0 v * y * (s0 v)⁻¹) := fun v =>
    (measurable_const_mul (s0 v)).mul_const _
  have hST : ∀ v, ∀ z, s0 v * z * (s0 v)⁻¹ ∈
      StSet (InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)))
        (InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u'))) (s.pt.1 v) ↔
      z ∈ Formalism.L2.SG.NGPin.StV X u u' γw v := by
    intro v z
    have e : (s.pt.1 v)⁻¹ * (s0 v * z * (s0 v)⁻¹) * s.pt.1 v = s1 v * ((γw v)⁻¹ * z * γw v) * (s1 v)⁻¹ := by
      rw [hpt]
      simp only [Pi.mul_apply, Pi.inv_apply]
      group
    show (s0 v * z * (s0 v)⁻¹ ∈ InfCut.JacobianCoordinates.NLoc _ _ _ ∧
      (s.pt.1 v)⁻¹ * (s0 v * z * (s0 v)⁻¹) * s.pt.1 v ∈ InfCut.JacobianCoordinates.NLoc _ _ _) ↔ _
    rw [e]
    exact and_congr (conj_loc X u hs0 v z) (conj_loc X u' hs1 v _)
  let μl : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v)) := fun v => (m v).map (fun y => s0 v * y * (s0 v)⁻¹)
  have hμlH : ∀ v, IsHaarLoc
      (StSet (InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)))
        (InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u'))) (s.pt.1 v))
      (μl v) := fun v => haar_conj _ _ (s0 v) (hST v) (hmH v)
  refine ⟨μl, ?_, hμlH, ?_, ?_⟩
  · rw [hμR, hμw]
    haveI : ∀ v, SigmaFinite ((m v).map (fun y => s0 v * y * (s0 v)⁻¹)) := fun v => (hμlH v).1
    have e : (fun y : X.B.I.Ginf => s0 * y * s0⁻¹) = fun y v => (fun z => s0 v * z * (s0 v)⁻¹) (y v) := rfl
    rw [e, Measure.pi_map_pi (fun v => (hcjm v).aemeasurable)]
  · rw [hμR]
    refine haar_conj (StInf X u u' γw) (Formalism.L2.SG.TermOp.Vanish.Rset s) s0 ?_ hH
    intro z
    have e : (s.pt.1)⁻¹ * (s0 * z * s0⁻¹) * s.pt.1 = s1 * (γw⁻¹ * z * γw) * s1⁻¹ := by
      rw [hpt]
      group
    show (s0 * z * s0⁻¹ ∈ X.NinfU u ∧ (s.pt.1)⁻¹ * (s0 * z * s0⁻¹) * s.pt.1 ∈ X.NinfU u') ↔
      (z ∈ X.NinfU u ∧ γw⁻¹ * z * γw ∈ X.NinfU u')
    rw [e]
    exact and_congr (sinf_conj_iff X u hs0 z) (sinf_conj_iff X u' hs1 _)
  · intro τ
    refine ⟨Formalism.MainNotions.S.ThB.ptLoc D τ w, ?_⟩
    have hb := root_base X C u u' w γw τ hrep (m (vOf X τ)) (hmH _) (hmmap _)
    have hz := Formalism.L2.SG.Pf.zTr C u τ
    have hz' := Formalism.L2.SG.Pf.zTr C u' τ
    have hT : 0 < Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (zB X (C.Qi τ) u τ) := by
      rw [hz.2]
      exact Formalism.MainNotions.BridgeLemma.Tr_pos D u
    have hT' : 0 < Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (zB X (C.Qi τ) u' τ) := by
      rw [hz'.2]
      exact Formalism.MainNotions.BridgeLemma.Tr_pos D u'
    have ha : trG (C.Q τ) (C.Qi τ) (s0 (vOf X τ)) ∈ Formalism.QuantumDeterminants.Sset D.R.k D.R.rS (zB X (C.Qi τ) u τ) :=
      (Formalism.L2.SG.Pf.LocF.local_dictionary_all D X θ C u τ (s0 (vOf X τ))).2 (sinf_nh X u hs0 (vOf X τ))
    have ha' : trG (C.Q τ) (C.Qi τ) (s1 (vOf X τ)) ∈ Formalism.QuantumDeterminants.Sset D.R.k D.R.rS (zB X (C.Qi τ) u' τ) :=
      (Formalism.L2.SG.Pf.LocF.local_dictionary_all D X θ C u' τ (s1 (vOf X τ))).2 (sinf_nh X u' hs1 (vOf X τ))
    have hmove := GlobalTheory.Amp.RootMove.rootMeas_move D _ _ _ _ _ _ _ hz.1 hz'.1 hT hT'
      (trG_mem_UH C τ (γw (vOf X τ))) ha ha' hb
    have hg : trG (C.Q τ) (C.Qi τ) (s.pt.1 (vOf X τ)) =
        trG (C.Q τ) (C.Qi τ) (s0 (vOf X τ)) * trG (C.Q τ) (C.Qi τ) (γw (vOf X τ)) *
          (trG (C.Q τ) (C.Qi τ) (s1 (vOf X τ)))⁻¹ := by
      rw [hpt]
      simp only [Pi.mul_apply, Pi.inv_apply]
      rw [trG_mul X C τ, trG_mul X C τ, trG_inv X C τ]
    have hGm : Measurable (fun x : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS => fun i j => ((trG (C.Q τ) (C.Qi τ) (s1 (vOf X τ))) * Matrix.of x * (trG (C.Q τ) (C.Qi τ) (s1 (vOf X τ)))⁻¹) i j) := by
      apply Continuous.measurable
      fun_prop
    have hcm := (Formalism.L2.SG.RealConjugatorData.cMr_measEmb C γw τ).measurable
    have hFeq : (fun y : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) =>
        Matrix.of.symm (trG (C.Q τ) (C.Qi τ) ((s.pt.1 (vOf X τ))⁻¹ * y * s.pt.1 (vOf X τ)))) =
        (fun x : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS => fun i j => ((trG (C.Q τ) (C.Qi τ) (s1 (vOf X τ))) * Matrix.of x * (trG (C.Q τ) (C.Qi τ) (s1 (vOf X τ)))⁻¹) i j) ∘
          Formalism.L2.SG.RealConjugatorData.cMr C γw τ ∘ (fun y => (s0 (vOf X τ))⁻¹ * y * s0 (vOf X τ)) := by
      funext y
      simp only [Function.comp_apply]
      have e1 : (s.pt.1 (vOf X τ))⁻¹ * y * s.pt.1 (vOf X τ) = s1 (vOf X τ) * ((γw (vOf X τ))⁻¹ *
          ((s0 (vOf X τ))⁻¹ * y * s0 (vOf X τ)) * γw (vOf X τ)) * (s1 (vOf X τ))⁻¹ := by
        rw [hpt]
        simp only [Pi.mul_apply, Pi.inv_apply]
        group
      rw [e1, trG_mul X C τ, trG_mul X C τ, trG_inv X C τ, ← cMr_trG X C τ γw _]
      rfl
    have hF : Measurable (fun y : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) =>
        Matrix.of.symm (trG (C.Q τ) (C.Qi τ) ((s.pt.1 (vOf X τ))⁻¹ * y * s.pt.1 (vOf X τ)))) := by
      rw [hFeq]
      exact hGm.comp (hcm.comp ((measurable_const_mul _).mul_const _))
    have hμ : (μl (vOf X τ)).map (fun y =>
        Matrix.of.symm (trG (C.Q τ) (C.Qi τ) ((s.pt.1 (vOf X τ))⁻¹ * y * s.pt.1 (vOf X τ)))) =
        ((m (vOf X τ)).map (Formalism.L2.SG.RealConjugatorData.cMr C γw τ)).map
          (fun x : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS => fun i j => ((trG (C.Q τ) (C.Qi τ) (s1 (vOf X τ))) * Matrix.of x * (trG (C.Q τ) (C.Qi τ) (s1 (vOf X τ)))⁻¹) i j) := by
      have hcomp : (fun y : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) =>
          Matrix.of.symm (trG (C.Q τ) (C.Qi τ) ((s.pt.1 (vOf X τ))⁻¹ * y * s.pt.1 (vOf X τ)))) ∘
            (fun y => s0 (vOf X τ) * y * (s0 (vOf X τ))⁻¹) =
          (fun x : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS => fun i j => ((trG (C.Q τ) (C.Qi τ) (s1 (vOf X τ))) * Matrix.of x * (trG (C.Q τ) (C.Qi τ) (s1 (vOf X τ)))⁻¹) i j) ∘
            Formalism.L2.SG.RealConjugatorData.cMr C γw τ := by
        rw [hFeq]
        funext y
        simp only [Function.comp_apply]
        rw [show (s0 (vOf X τ))⁻¹ * (s0 (vOf X τ) * y * (s0 (vOf X τ))⁻¹) * s0 (vOf X τ) = y by group]
      show ((m (vOf X τ)).map (fun y => s0 (vOf X τ) * y * (s0 (vOf X τ))⁻¹)).map _ = _
      rw [Measure.map_map hF (hcjm _), Measure.map_map hGm hcm, hcomp]
    rw [hg, hμ]
    exact hmove

end GlobalTheory.Amp.PinRoot
