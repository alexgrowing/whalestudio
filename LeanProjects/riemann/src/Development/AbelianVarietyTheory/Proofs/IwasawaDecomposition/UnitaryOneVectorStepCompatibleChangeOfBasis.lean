import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdHermitianFibreProductChangeOfBasisStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryStabilizerAnisotropicVectorEquivComplemenStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryGroupPointsEquivOfChangeOfBasisStatement

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx.StepTr

open Formalism.UG in
theorem hform_eq {A : Type} [CommRing A] (σ : A →+* A) {n : ℕ} (J : Matrix (Fin n) (Fin n) A)
    (u w : Fin n → A) : hform σ J u w = (fun i => σ (u i)) ⬝ᵥ J.mulVec w := by
  unfold Formalism.UG.hform
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

open Formalism.UG in
theorem hform_basis {A : Type} [CommRing A] (σ : A →+* A) {n m : ℕ} (J : Matrix (Fin n) (Fin n) A)
    (P : Matrix (Fin n) (Fin m) A) (u w : Fin m → A) :
    hform σ (cT σ P * J * P) u w = hform σ J (P.mulVec u) (P.mulVec w) := by
  rw [hform_eq, hform_eq]
  have h1 : Matrix.vecMul (fun i => σ (u i)) (Formalism.UG.cT σ P) = fun i => σ (P.mulVec u i) := by
    unfold Formalism.UG.cT
    funext i
    rw [Matrix.vecMul_transpose, RingHom.map_mulVec]
    rfl
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, h1]

section

variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)

theorem isHermND_basis (hσ : ∀ z, σ (σ z) = z) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hJ : IsHermND σ J) (P : GL (Fin n) E) :
    IsHermND σ (Formalism.UG.cT (σ : E →+* E) (P : Matrix (Fin n) (Fin n) E) * J * P.val) := by
  obtain ⟨h1, h2⟩ := hJ
  refine ⟨fun i j => ?_, ?_⟩
  · unfold Formalism.UG.cT
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul, map_sum,
      map_mul, AlgHom.coe_toRingHom, hσ, h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  · have hP : (P : Matrix (Fin n) (Fin n) E).det ≠ 0 := (Matrix.isUnits_det_units P).ne_zero
    have hm : ((P : Matrix (Fin n) (Fin n) E).map (σ : E →+* E)).det =
        (σ : E →+* E) (P : Matrix (Fin n) (Fin n) E).det :=
      ((σ : E →+* E).map_det _).symm
    unfold Formalism.UG.cT
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hm]
    exact mul_ne_zero (mul_ne_zero ((map_ne_zero _).mpr hP) h2) hP

private theorem cT_mul_lemma {A : Type} [CommRing A] (τ : A →+* A) {k l m : ℕ}
    (X : Matrix (Fin k) (Fin l) A) (Y : Matrix (Fin l) (Fin m) A) :
    Formalism.UG.cT τ (X * Y) = Formalism.UG.cT τ Y * Formalism.UG.cT τ X := by
  unfold Formalism.UG.cT
  rw [Matrix.map_mul, Matrix.transpose_mul]

theorem stepData_basis (hσ : ∀ z, σ (σ z) = z) {M : ℕ} {J : Matrix (Fin (M + 1)) (Fin (M + 1)) E}
    {x x₂ : Fin 1 → Fin (M + 1) → E} {a : F} {B B₂ : Matrix (Fin (M + 1)) (Fin M) E}
    {J' : Matrix (Fin M) (Fin M) E} (P : GL (Fin (M + 1)) E) (Q : GL (Fin M) E)
    (h : StepData σ J x a B J')
    (hx : (P : Matrix (Fin (M + 1)) (Fin (M + 1)) E).mulVec (x₂ 0) = x 0)
    (hB : (P : Matrix (Fin (M + 1)) (Fin (M + 1)) E) * B₂ = B * (Q : Matrix (Fin M) (Fin M) E)) :
    StepData σ (Formalism.UG.cT (σ : E →+* E) (P : Matrix (Fin (M + 1)) (Fin (M + 1)) E) * J * P.val) x₂ a B₂
      (Formalism.UG.cT (σ : E →+* E) (Q : Matrix (Fin M) (Fin M) E) * J' * Q.val) := by
  obtain ⟨hJ, ha, hx0, hB0, hJ', hJ'nd⟩ := h
  refine ⟨isHermND_basis σ hσ hJ P, ha, ?_, fun j => ?_, ?_, isHermND_basis σ hσ hJ'nd Q⟩
  · rw [hE, hform_basis, hx]
    exact hx0
  · rw [hE, hform_basis, hx]
    have hcol : Matrix.mulVec (P : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (fun i => B₂ i j) =
        Matrix.mulVec B (fun k => (Q : Matrix (Fin M) (Fin M) E) k j) := by
      funext i
      change ((P : Matrix (Fin (M + 1)) (Fin (M + 1)) E) * B₂) i j = (B * (Q : Matrix (Fin M) (Fin M) E)) i j
      rw [hB]
    have hz : Matrix.vecMul (fun i => (σ : E →+* E) (x 0 i)) (J * B) = 0 := by
      funext k
      have h0 := hB0 k
      rw [hE, hform_eq, Matrix.dotProduct_mulVec] at h0
      rw [← Matrix.vecMul_vecMul]
      exact h0
    rw [hcol, hform_eq, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, hz, zero_dotProduct]
  · rw [hJ']
    have e1 := cT_mul_lemma (σ : E →+* E) B (Q : Matrix (Fin M) (Fin M) E)
    have e2 := cT_mul_lemma (σ : E →+* E) (P : Matrix (Fin (M + 1)) (Fin (M + 1)) E) B₂
    rw [hB, e1] at e2
    calc _ = (Formalism.UG.cT (σ : E →+* E) (Q : Matrix (Fin M) (Fin M) E) * Formalism.UG.cT (σ : E →+* E) B) * J *
          (B * (Q : Matrix (Fin M) (Fin M) E)) := by simp only [Matrix.mul_assoc]
      _ = (Formalism.UG.cT (σ : E →+* E) B₂ * Formalism.UG.cT (σ : E →+* E) (P : Matrix (Fin (M + 1)) (Fin (M + 1)) E)) * J *
          ((P : Matrix (Fin (M + 1)) (Fin (M + 1)) E) * B₂) := by rw [e2, ← hB]
      _ = _ := by simp only [Matrix.mul_assoc]

end

def tupHomeo {S : Type} [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] {n M : ℕ}
    (g : GL (Fin M) S) : (Fin n → Fin M → S) ≃ₜ (Fin n → Fin M → S) where
  toFun X := fun a => (g : Matrix (Fin M) (Fin M) S).mulVec (X a)
  invFun X := fun a => ((g⁻¹ : GL (Fin M) S) : Matrix (Fin M) (Fin M) S).mulVec (X a)
  left_inv X := by funext a; simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  right_inv X := by funext a; simp only [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  continuous_toFun := continuous_pi fun a => continuous_const.matrix_mulVec (continuous_apply a)
  continuous_invFun := continuous_pi fun a => continuous_const.matrix_mulVec (continuous_apply a)

theorem lrAct_one {S : Type} [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] {n M : ℕ}
    (g : GL (Fin M) S) : lrAct (g : Matrix (Fin M) (Fin M) S) (1 : Matrix (Fin n) (Fin n) S) =
      tupHomeo g := by
  funext X a
  change (g : Matrix (Fin M) (Fin M) S).mulVec (fun i => ∑ c, X c i * (1 : Matrix (Fin n) (Fin n) S) c a) =
    (g : Matrix (Fin M) (Fin M) S).mulVec (X a)
  congr 1
  funext i
  simp [Matrix.one_apply]

theorem map_frame {E S : Type} [CommRing E] [CommRing S] (φ : E →+* S) {n m : ℕ}
    {P : Matrix (Fin n) (Fin n) E} {Q : Matrix (Fin m) (Fin m) E} {B B₂ : Matrix (Fin n) (Fin m) E}
    (h : P * B₂ = B * Q) : P.map φ * B₂.map φ = B.map φ * Q.map φ := by
  rw [← Matrix.map_mul, ← Matrix.map_mul, h]

theorem frame_alg {S : Type} [CommRing S] {n m : ℕ} {g g₂ P : Matrix (Fin n) (Fin n) S}
    {k k₂ : Matrix (Fin m) (Fin m) S} {Q : GL (Fin m) S} {B B₂ : Matrix (Fin n) (Fin m) S}
    (hB : P * B₂ = B * Q.val) (h1 : g * P = P * g₂) (h2 : g₂ * B₂ = B₂ * k₂)
    (h3 : k * Q.val = Q.val * k₂) : g * B = B * k := by
  have key : g * B * Q.val = B * k * Q.val := by
    calc g * B * Q.val = g * (B * Q.val) := Matrix.mul_assoc _ _ _
      _ = (g * P) * B₂ := by rw [← hB, Matrix.mul_assoc]
      _ = P * (g₂ * B₂) := by rw [h1, Matrix.mul_assoc]
      _ = (P * B₂) * k₂ := by rw [h2, Matrix.mul_assoc]
      _ = B * (Q.val * k₂) := by rw [hB, Matrix.mul_assoc]
      _ = B * k * Q.val := by rw [← h3, Matrix.mul_assoc]
  calc g * B = g * B * Q.val * (Q⁻¹).val := by rw [Matrix.mul_assoc (g * B), Units.mul_inv, Matrix.mul_one]
    _ = B * k * Q.val * (Q⁻¹).val := by rw [key]
    _ = B * k := by rw [Matrix.mul_assoc (B * k), Units.mul_inv, Matrix.mul_one]

end GlobalTheory.GaugeEx.StepTr

open GlobalTheory.GaugeEx.StepTr in

theorem GlobalTheory.GaugeEx.stepRel_basis : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (s : StdMeas b) (M : ℕ) (J J₂ : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E) (x₂ : Fin 1 → Fin (M + 1) → E) (B₂ : Matrix (Fin (M + 1)) (Fin M) E) (J₂' : Matrix (Fin M) (Fin M) E) (P : GL (Fin (M + 1)) E) (Q : GL (Fin M) E) (eP : HA (AF F) σ J ≃* HA (AF F) σ J₂) (eQ : HA (AF F) σ J' ≃* HA (AF F) σ J₂') (μ : Measure (HA (AF F) σ J)) (μ' : Measure (HA (AF F) σ J')), StepData σ J x a B J' → J₂ = Formalism.UG.cT (σ : E →+* E) (P : Matrix (Fin (M + 1)) (Fin (M + 1)) E) * J * (P : Matrix (Fin (M + 1)) (Fin (M + 1)) E) → J₂' = Formalism.UG.cT (σ : E →+* E) (Q : Matrix (Fin M) (Fin M) E) * J' * (Q : Matrix (Fin M) (Fin M) E) → (P : Matrix (Fin (M + 1)) (Fin (M + 1)) E).mulVec (x₂ 0) = x 0 → (P : Matrix (Fin (M + 1)) (Fin (M + 1)) E) * B₂ = B * (Q : Matrix (Fin M) (Fin M) E) → (∀ g, FrameRel J J₂ (P : Matrix (Fin (M + 1)) (Fin (M + 1)) E) g (eP g)) → (∀ g, FrameRel J' J₂' (Q : Matrix (Fin M) (Fin M) E) g (eQ g)) → StepRel s σ J x a B J' μ μ' → StepData σ J₂ x₂ a B₂ J₂' ∧ StepRel s σ J₂ x₂ a B₂ J₂' (μ.map eP) (μ'.map eQ) := by
  intro F E iF nF iE nE iA σ hCM d b s M J J₂ x a B J' x₂ B₂ J₂' P Q eP eQ μ μ' hSD hJ₂ hJ₂' hx hB
    hePF heQF hR
  have hσ : ∀ z, σ (σ z) = z := by
    intro z
    let τ : E →+* ℂ := (IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom
    apply τ.injective
    rw [hCM.2.2.2 τ, hCM.2.2.2 τ, star_star]
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ hCM.2.2.1
  have hSD₂ : StepData σ J₂ x₂ a B₂ J₂' := by
    subst hJ₂ hJ₂'
    exact stepData_basis σ hσ P Q hSD hx hB
  refine ⟨hSD₂, ?_⟩
  intro ν₂ hν₂ e₂ he₂
  let PA : GL (Fin (M + 1)) (AF F ⊗[F] E) := Matrix.GeneralLinearGroup.map (inclR (AF F)) P
  let QA : GL (Fin M) (AF F ⊗[F] E) := Matrix.GeneralLinearGroup.map (inclR (AF F)) Q
  let L := tupHomeo (n := 1) PA
  have hL : lrAct ((P : Matrix (Fin (M + 1)) (Fin (M + 1)) E).map (inclR (AF F)))
      (1 : Matrix (Fin 1) (Fin 1) (AF F ⊗[F] E)) = ⇑L := lrAct_one PA
  have hν : IsStdX s σ J a (ν₂.map L) := by
    have h := GlobalTheory.T.stdHermitianFibreProduct_change_of_basis F E σ hCM d b s (M + 1) J J₂ P a ν₂ hJ₂ hν₂
    rwa [hL] at h
  have hcP := (GlobalTheory.T.unitary_group_points_equiv_of_change_of_basis F E σ (AF F) (M + 1) J J₂ P hJ₂).2 eP (fun g => hePF g)
  have hcQ := (GlobalTheory.T.unitary_group_points_equiv_of_change_of_basis F E σ (AF F) M J' J₂' Q hJ₂').2 eQ (fun g => heQF g)
  have hc₂ := (GlobalTheory.T.unitary_stabilizer_anisotropic_vector_equiv_complement F E σ hCM (AF F) M J₂ x₂ a B₂ J₂' hSD₂).2.2 e₂ (fun g => he₂ g)
  have hF : ∀ g : HA (AF F) σ J,
      (↑(HA.mat (AF F) σ J g) : Matrix (Fin (M + 1)) (Fin (M + 1)) (AF F ⊗[F] E)) *
          (PA : Matrix (Fin (M + 1)) (Fin (M + 1)) (AF F ⊗[F] E)) =
        (PA : Matrix (Fin (M + 1)) (Fin (M + 1)) (AF F ⊗[F] E)) *
          (↑(HA.mat (AF F) σ J₂ (eP g)) : Matrix (Fin (M + 1)) (Fin (M + 1)) (AF F ⊗[F] E)) :=
    fun g => hePF g
  have hsm1 : ∀ (g : HA (AF F) σ J) (Z : Fin 1 → Fin (M + 1) → AF F ⊗[F] E) (i : Fin 1),
      (g • Z) i = Matrix.mulVec (↑(HA.mat (AF F) σ J g) : Matrix (Fin (M + 1)) (Fin (M + 1)) (AF F ⊗[F] E)) (Z i) :=
    fun _ _ _ => rfl
  have hsm2 : ∀ (g : HA (AF F) σ J₂) (Z : Fin 1 → Fin (M + 1) → AF F ⊗[F] E) (i : Fin 1),
      (g • Z) i = Matrix.mulVec (↑(HA.mat (AF F) σ J₂ g) : Matrix (Fin (M + 1)) (Fin (M + 1)) (AF F ⊗[F] E)) (Z i) :=
    fun _ _ _ => rfl
  have hLa : ∀ (Z : Fin 1 → Fin (M + 1) → AF F ⊗[F] E) (i : Fin 1),
      L Z i = Matrix.mulVec (PA : Matrix (Fin (M + 1)) (Fin (M + 1)) (AF F ⊗[F] E)) (Z i) := fun _ _ => rfl
  have hX : ∀ i, Matrix.mulVec (PA : Matrix (Fin (M + 1)) (Fin (M + 1)) (AF F ⊗[F] E)) (ratTup (AF F) x₂ i) =
      ratTup (AF F) x i := by
    intro i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    funext k
    change (Matrix.mulVec ((P : Matrix (Fin (M + 1)) (Fin (M + 1)) E).map (inclR (AF F)))
      (fun j => inclR (AF F) (x₂ 0 j))) k = inclR (AF F) (x 0 k)
    rw [← hx, RingHom.map_mulVec]
    rfl
  have hLX : L (ratTup (AF F) x₂) = ratTup (AF F) x := funext fun i => (hLa _ i).trans (hX i)
  have hint : ∀ (g : HA (AF F) σ J) (Z : Fin 1 → Fin (M + 1) → AF F ⊗[F] E),
      L (eP g • Z) = g • L Z := by
    intro g Z
    funext i
    rw [hLa, hsm2, hsm1, hLa, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hF g]
  have hmem : ∀ g : HA (AF F) σ J, g ∈ Hstab (AF F) σ J x ↔ eP g ∈ Hstab (AF F) σ J₂ x₂ := by
    intro g
    simp only [Hstab, MulAction.mem_stabilizer_iff]
    constructor
    · intro h
      apply L.injective
      rw [hint, hLX, h]
    · intro h
      rw [← hLX, ← hint, h]
  let ePr : Hstab (AF F) σ J x ≃* Hstab (AF F) σ J₂ x₂ :=
    { toFun := fun g => ⟨eP g, (hmem g).1 g.2⟩
      invFun := fun g => ⟨eP.symm g, (hmem _).2 (by rw [MulEquiv.apply_symm_apply]; exact g.2)⟩
      left_inv := fun g => Subtype.ext (eP.symm_apply_apply _)
      right_inv := fun g => Subtype.ext (eP.apply_symm_apply _)
      map_mul' := fun g h => Subtype.ext (map_mul eP _ _) }
  let e : Hstab (AF F) σ J x ≃* HA (AF F) σ J' := ePr.trans (e₂.trans eQ.symm)
  have he : ∀ g : Hstab (AF F) σ J x, FrameRel J J' B (g : HA (AF F) σ J) (e g) := by
    intro g
    have h3 : FrameRel J' J₂' (Q : Matrix (Fin M) (Fin M) E) (e g) (e₂ (ePr g)) := by
      have h := heQF (e g)
      rwa [show eQ (e g) = e₂ (ePr g) from eQ.apply_symm_apply _] at h
    exact frame_alg (Q := QA) (map_frame (inclR (AF F)) hB) (hePF g) (he₂ (ePr g)) h3
  intro f hf s₂ hs₂
  have hsec : ∀ y, (∃ g : HA (AF F) σ J, g • ratTup (AF F) x = y) →
      eP.symm (s₂ (L.symm y)) • ratTup (AF F) x = y := by
    rintro y ⟨g, rfl⟩
    have h2 : eP g • ratTup (AF F) x₂ = L.symm (g • ratTup (AF F) x) := by
      rw [← hLX, ← hint, Homeomorph.symm_apply_apply]
    have h3 := hs₂ _ ⟨eP g, h2⟩
    generalize hY : L.symm (g • ratTup (AF F) x) = Y at h3 ⊢
    rw [← hLX, ← hint (eP.symm (s₂ Y)), MulEquiv.apply_symm_apply, h3, ← hY,
      Homeomorph.apply_symm_apply, hLX]
  have hPm : Measurable eP := hcP.1.measurable
  have hQm : Measurable eQ := hcQ.1.measurable
  have h2m : Measurable e₂.symm := by
    have hm : Measurable fun k : HA (AF F) σ J₂' => ((e₂.symm k : Hstab (AF F) σ J₂ x₂) : HA (AF F) σ J₂) :=
      (continuous_subtype_val.comp hc₂.2).measurable
    exact hm.subtype_mk
  have hesm : Measurable e.symm := by
    have hm : Measurable fun k : HA (AF F) σ J' => ((e.symm k : Hstab (AF F) σ J x) : HA (AF F) σ J) :=
      (hcP.2.comp (continuous_subtype_val.comp (hc₂.2.comp hcQ.1))).measurable
    exact hm.subtype_mk
  have hin : ∀ c : HA (AF F) σ J₂,
      Measurable fun h' : Hstab (AF F) σ J₂ x₂ => f (c * (h' : HA (AF F) σ J₂)) :=
    fun c => hf.comp ((continuous_mul_left c).measurable.comp measurable_subtype_coe)
  have hin1 : ∀ c : HA (AF F) σ J,
      Measurable fun h' : Hstab (AF F) σ J x => f (eP (c * (h' : HA (AF F) σ J))) :=
    fun c => hf.comp (hPm.comp ((continuous_mul_left c).measurable.comp measurable_subtype_coe))
  have hin2 : ∀ c : HA (AF F) σ J₂,
      Measurable fun k : HA (AF F) σ J₂' => f (c * ((e₂.symm k : Hstab (AF F) σ J₂ x₂) : HA (AF F) σ J₂)) :=
    fun c => (hin c).comp h2m
  have hmapL : ∀ G : (Fin 1 → Fin (M + 1) → AF F ⊗[F] E) → ℝ≥0∞,
      ∫⁻ y, G y ∂(ν₂.map ⇑L) = ∫⁻ y₂, G (L y₂) ∂ν₂ :=
    fun G => lintegral_map_equiv G L.toMeasurableEquiv
  have hC := hR (ν₂.map L) hν e he (fun g => f (eP g)) (hf.comp hPm)
    (fun y => eP.symm (s₂ (L.symm y))) hsec
  refine (lintegral_map hf hPm).trans (hC.trans ?_)
  rw [hmapL]
  refine lintegral_congr fun y₂ => ?_
  simp only [Homeomorph.symm_apply_apply]
  rw [lintegral_map (hin1 _) hesm, lintegral_map (hin _) h2m, lintegral_map (hin2 _) hQm]
  refine lintegral_congr fun k => congrArg f ?_
  rw [map_mul, MulEquiv.apply_symm_apply]
  exact congrArg (s₂ y₂ * ·) (eP.apply_symm_apply _)
