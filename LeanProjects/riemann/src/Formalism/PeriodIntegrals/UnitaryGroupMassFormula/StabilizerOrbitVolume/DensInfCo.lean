import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensInfTop

noncomputable section

namespace PI.VolStabSW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW Topology
open scoped TensorProduct
open PI.AdicCompletionValuation

def QuadCoord : Prop :=
  ∀ (V H : Type) [AddCommGroup V] [TopologicalSpace V] [AddCommGroup H] [TopologicalSpace H]
    (n m : ℕ) (eV : V ≃ₜ (Fin n → ℝ)) (eH : H ≃ₜ (Fin m → ℝ)) (Q : V → H) (β : V → V → H),
    (∀ x y, eV (x + y) = eV x + eV y) → (∀ x y, eH (x + y) = eH x + eH y) →
    Continuous (fun p : V × V => β p.1 p.2) → (∀ x y z, β (x + y) z = β x z + β y z) →
    (∀ x y, β x y = β y x) → (∀ x, β x x = Q x + Q x) →
    ContDiff ℝ 1 (fun y => eH (Q (eV.symm y))) ∧
      ∀ x y, fderiv ℝ (fun y => eH (Q (eV.symm y))) (eV x) (eV y) = eH (β x y)

theorem quadCoord_holds : QuadCoord := by
  intro V H _ _ _ _ n m eV eH Q β hV hH hβc hβa hβs hQ
  have hVs : ∀ y z, eV.symm (y + z) = eV.symm y + eV.symm z := by
    intro y z; apply eV.injective; rw [hV]; simp
  let b : (Fin n → ℝ) → (Fin n → ℝ) → (Fin m → ℝ) := fun y z => eH (β (eV.symm y) (eV.symm z))
  have hb1 : ∀ y y' z, b y z + b y' z = b (y + y') z := by
    intro y y' z; simp only [b, hVs, hβa, hH]
  have hb2 : ∀ y z z', b y (z + z') = b y z + b y z' := by
    intro y z z'; simp only [b, hVs]
    rw [hβs, hβa, hH, hβs (eV.symm z), hβs (eV.symm z')]
  have hbc : Continuous (fun p : (Fin n → ℝ) × (Fin n → ℝ) => b p.1 p.2) :=
    eH.continuous.comp (hβc.comp ((eV.symm.continuous.comp continuous_fst).prodMk
      (eV.symm.continuous.comp continuous_snd)))
  let L1 : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin m → ℝ) := fun y =>
    AddMonoidHom.toRealLinearMap (AddMonoidHom.mk' (b y) (hb2 y))
      (hbc.comp (continuous_const.prodMk continuous_id))
  have hL1 : ∀ y z, L1 y z = b y z := fun _ _ => rfl
  have hsm1 : ∀ (c : ℝ) y z, b (c • y) z = c • b y z := by
    intro c y z
    have : b (c • y) z = c • b y z := (AddMonoidHom.toRealLinearMap (AddMonoidHom.mk' (fun y => b y z)
      (fun y y' => (hb1 y y' z).symm)) (hbc.comp (continuous_id.prodMk continuous_const))).map_smul c y
    exact this
  let Bl : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) →L[ℝ] (Fin m → ℝ) :=
    { toFun := L1
      map_add' := fun y y' => by ext1 z; simp only [add_apply, hL1, hb1]
      map_smul' := fun c y => by
        ext1 z; simp only [smul_apply, hL1, hsm1, RingHom.id_apply] }
  let B : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin m → ℝ) := LinearMap.toContinuousLinearMap Bl
  have hB : ∀ y z, B y z = b y z := fun _ _ => rfl
  have hf : ∀ y, eH (Q (eV.symm y)) = (1/2 : ℝ) • B y y := by
    intro y
    rw [hB]
    simp only [b, hQ, hH]
    rw [← two_smul ℝ (eH (Q (eV.symm y))), smul_smul]
    norm_num
  have hfe : (fun y => eH (Q (eV.symm y))) = fun y => (1/2 : ℝ) • B y y := funext hf
  have hd : ∀ y, HasFDerivAt (fun y => (1/2 : ℝ) • B y y)
      ((1/2 : ℝ) • (B.precompR (Fin n → ℝ) y (ContinuousLinearMap.id ℝ _) +
        B.precompL (Fin n → ℝ) (ContinuousLinearMap.id ℝ _) y)) y :=
    fun y => by
      have h := (B.hasFDerivAt_of_bilinear (hasFDerivAt_id y) (hasFDerivAt_id y)).const_smul
        (1/2 : ℝ)
      exact h
  refine ⟨?_, fun x y => ?_⟩
  · rw [hfe]
    exact (B.isBoundedBilinearMap.contDiff.comp (contDiff_id.prodMk contDiff_id)).const_smul
      (1/2 : ℝ)
  · rw [hfe, (hd _).fderiv]
    show (1/2 : ℝ) • (B (eV x) (eV y) + B (eV y) (eV x)) = eH (β x y)
    rw [hB, hB]
    simp only [b, Homeomorph.symm_apply_apply]
    rw [hβs y x, ← two_smul ℝ (eH (β x y)), smul_smul]
    norm_num

section B

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

def gramB (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X Y : Fin n → Fin M → R ⊗[F] E) : Matrix (Fin n) (Fin n) (R ⊗[F] E) :=
  fun i j => hR R σ J (X i) (Y j) + hR R σ J (Y i) (X j)

theorem hR_add_left (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (x y z : Fin M → R ⊗[F] E) : hR R σ J (x + y) z = hR R σ J x z + hR R σ J y z := by
  simp only [hR, Formalism.UG.hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem hR_add_right (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (x y z : Fin M → R ⊗[F] E) : hR R σ J x (y + z) = hR R σ J x y + hR R σ J x z := by
  simp only [hR, Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hR_herm (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin M → R ⊗[F] E) :
    sigR R σ (hR R σ J x y) = hR R σ J y x := by
  have hinv : ∀ a : R ⊗[F] E, sigR R σ (sigR R σ a) = a := by
    intro a
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul r e => simp [sigR, hσ]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hJ' : ∀ i j, sigR R σ (JR R J i j) = JR R J j i := by
    intro i j
    simp [JR, inclR, sigR, hJ]
  simp only [hR, Formalism.UG.hform, map_sum, map_mul, hinv, hJ']
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem gramB_mem (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {M n : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : ∀ i j, σ (J j i) = J i j)
    (X Y : Fin n → Fin M → R ⊗[F] E) : gramB R σ J X Y ∈ HermR R σ n := by
  show ∀ a b, sigR R σ (gramB R σ J X Y b a) = gramB R σ J X Y a b
  intro a b
  simp only [gramB, map_add, hR_herm R σ hσ J hJ]
  ring

end B

section BTop

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [T2Space R]

theorem continuous_gramB_apply (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (a b : Fin n) : Continuous (fun p : (Fin n → Fin M → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) =>
      gramB R σ J p.1 p.2 a b) := by
  show Continuous (fun p : (Fin n → Fin M → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) =>
    hR R σ J (p.1 a) (p.2 b) + hR R σ J (p.2 a) (p.1 b))
  have hc := continuous_hR R σ J
  have e1 : Continuous (fun p : (Fin n → Fin M → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) =>
      ((p.1 a, p.2 b) : (Fin M → R ⊗[F] E) × (Fin M → R ⊗[F] E))) := by fun_prop
  have e2 : Continuous (fun p : (Fin n → Fin M → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) =>
      ((p.2 a, p.1 b) : (Fin M → R ⊗[F] E) × (Fin M → R ⊗[F] E))) := by fun_prop
  have h1 := Continuous.comp (g := fun q : (Fin M → R ⊗[F] E) × (Fin M → R ⊗[F] E) =>
      hR R σ J q.1 q.2) hc e1
  have h2 := Continuous.comp (g := fun q : (Fin M → R ⊗[F] E) × (Fin M → R ⊗[F] E) =>
      hR R σ J q.1 q.2) hc e2
  exact h1.add h2

theorem continuous_gramB (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    Continuous (fun p : (Fin n → Fin M → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) =>
      gramB R σ J p.1 p.2) := by
  exact continuous_pi fun a => continuous_pi fun b => continuous_gramB_apply R σ J a b

end BTop

def TensR : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  ∃ (n m : ℕ) (eV : (Fin a → Fin M → Ainf F ⊗[F] E) ≃ₜ (Fin n → ℝ))
    (eH : HermR (Ainf F) σ a ≃ₜ (Fin m → ℝ)),
    (∀ x y, eV (x + y) = eV x + eV y) ∧ ∀ x y, eH (x + y) = eH x + eH y

def FreeSurj : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  ∀ X : Fin a → Fin M → Ainf F ⊗[F] E, LinearIndependent (Ainf F ⊗[F] E) X →
    ∀ S : HermR (Ainf F) σ a, ∃ Y, gramB (Ainf F) σ J X Y = S

theorem coordInf_of (h1 : QuadCoord) (h2 : TensR) (h3 : FreeSurj) : CoordInf := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a hA1 hA2 X0 hT0 hdet
  obtain ⟨n, m, eV, eH, hV, hH⟩ := h2 F E σ hCM M J hJ ha hc a hA1 hA2 X0 hT0 hdet
  have hσ : ∀ x, σ (σ x) = x := sigma_invol σ hCM.2.2.2
  let Q : (Fin a → Fin M → Ainf F ⊗[F] E) → HermR (Ainf F) σ a := gramH (Ainf F) σ hσ J hJ.1
  let β : (Fin a → Fin M → Ainf F ⊗[F] E) → (Fin a → Fin M → Ainf F ⊗[F] E) →
      HermR (Ainf F) σ a := fun X Y => ⟨gramB (Ainf F) σ J X Y, gramB_mem (Ainf F) σ hσ J hJ.1 X Y⟩
  have hβc : Continuous (fun p : (Fin a → Fin M → Ainf F ⊗[F] E) ×
      (Fin a → Fin M → Ainf F ⊗[F] E) => β p.1 p.2) := by
    exact (continuous_gramB (Ainf F) σ J).subtype_mk _
  have hβa : ∀ x y z, β (x + y) z = β x z + β y z := by
    intro x y z; apply Subtype.ext; funext i j
    show gramB (Ainf F) σ J (x + y) z i j = gramB (Ainf F) σ J x z i j + gramB (Ainf F) σ J y z i j
    simp only [gramB, Pi.add_apply, hR_add_left, hR_add_right]
    abel
  have hβs : ∀ x y, β x y = β y x := by
    intro x y; apply Subtype.ext; funext i j
    simp only [β, gramB]; exact add_comm _ _
  have hQ : ∀ x, β x x = Q x + Q x := by
    intro x; apply Subtype.ext; funext i j; rfl
  obtain ⟨hC, hD⟩ := h1 _ _ n m eV eH Q β hV hH hβc hβa hβs hQ
  refine ⟨n, m, eV, eH, fun y => eH (Q (eV.symm y)), hV, hH, hC, fun X => ?_, fun X hX => ?_⟩
  · simp [Q, gramH]
  · intro t
    obtain ⟨Y, hY⟩ := h3 F E σ hCM M J hJ ha hc a hA1 hA2 X0 hT0 hdet X hX (eH.symm t)
    refine ⟨eV Y, ?_⟩
    rw [hD X Y]
    have : β X Y = eH.symm t := Subtype.ext hY
    rw [this, Homeomorph.apply_symm_apply]

theorem densInf_of_tens (h2 : TensR) (h3 : FreeSurj) : DensInf := by
  exact densInf_of_coord (coordInf_of quadCoord_holds h2 h3)

end PI.VolStabSW
