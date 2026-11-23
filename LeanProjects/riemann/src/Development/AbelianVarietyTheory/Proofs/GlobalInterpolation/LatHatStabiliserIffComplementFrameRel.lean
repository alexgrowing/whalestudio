import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InfiniteCoordinateUnfold
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.AdelicUnitaryHaarMeasure
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.StabilizerLattices
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FundamentalDomainNeZero
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FrameTransport
open NumberField MeasureTheory Matrix Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers GlobalTheory.Mem.Vol GlobalTheory.Mem.VolExists
open scoped ENNReal TensorProduct

noncomputable section

namespace GlobalTheory.StabFrame

section Lin

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem exists_mulVec_eq (σ : E →ₐ[F] E) {M M' : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (B : Matrix (Fin M) (Fin M') E) (N : Matrix (Fin M') (Fin M) E) (hN : N * B = 1) (x : Fin M → E)
    (hM : M' + 1 = M) (hB : ∀ j, hE σ J x (fun i => B i j) = 0) (hx : hE σ J x x ≠ 0) :
    (∀ z, hE σ J x (B *ᵥ z) = 0) ∧ ∀ y, hE σ J x y = 0 → B *ᵥ (N *ᵥ y) = y := by
  let φ : (Fin M → E) →ₗ[E] E :=
    { toFun := fun y => hE σ J x y
      map_add' := fun y z => by
        simp only [hE, Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := fun c y => by
        simp only [hE, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring }
  have hle : LinearMap.range B.mulVecLin ≤ LinearMap.ker φ := by
    rw [Matrix.range_mulVecLin, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact hB j
  have hinj : Function.Injective B.mulVecLin := fun z w h => by
    have := congrArg (N *ᵥ ·) h
    simpa [Matrix.mulVec_mulVec, hN] using this
  have h1 : Module.finrank E (LinearMap.range B.mulVecLin) = M' := by
    rw [LinearMap.finrank_range_of_inj hinj]; simp
  have hlt : LinearMap.ker φ < ⊤ := lt_top_iff_ne_top.2 fun h => hx (by
    have : x ∈ LinearMap.ker φ := h ▸ Submodule.mem_top
    exact this)
  have h2 := Submodule.finrank_lt_finrank_of_lt hlt
  rw [finrank_top, Module.finrank_fin_fun] at h2
  have heq := Submodule.eq_of_le_of_finrank_le hle (by omega)
  refine ⟨fun z => hle ⟨z, rfl⟩, fun y hy => ?_⟩
  have : y ∈ LinearMap.range B.mulVecLin := heq ▸ hy
  obtain ⟨z, rfl⟩ := this
  simp [Matrix.mulVec_mulVec, hN]

theorem map_mulVec_tmul (R : Type) [CommRing R] [Algebra F R] {m n : ℕ} (C : Matrix (Fin m) (Fin n) E)
    (a : R) (z : Fin n → E) :
    C.map (inclR (F := F) R) *ᵥ (fun i => a ⊗ₜ[F] z i) = fun i => a ⊗ₜ[F] (C *ᵥ z) i := by
  funext i
  simp [Matrix.mulVec, dotProduct, inclR, TensorProduct.tmul_sum]

variable [NumberField F]

theorem mulVec_mem_latHat {m n : ℕ} (C : Matrix (Fin m) (Fin n) E) {S : Set (Fin n → E)}
    {T : Set (Fin m → E)} (h : ∀ z ∈ S, C *ᵥ z ∈ T) {y : Fin n → Af F ⊗[F] E} (hy : y ∈ latHat F E S) :
    C.map (inclR (F := F) (Af F)) *ᵥ y ∈ latHat F E T := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, z, hz, rfl⟩ := hy
    exact AddSubgroup.subset_closure ⟨a, ha, _, h z hz, map_mulVec_tmul _ C a z⟩
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [Matrix.mulVec_add]; exact add_mem hy hz
  | neg y _ hy => rw [Matrix.mulVec_neg]; exact neg_mem hy

theorem mulVec_eq_of_mem_latHat {n : ℕ} (C : Matrix (Fin n) (Fin n) E) {S : Set (Fin n → E)}
    (h : ∀ z ∈ S, C *ᵥ z = z) {y : Fin n → Af F ⊗[F] E} (hy : y ∈ latHat F E S) :
    C.map (inclR (F := F) (Af F)) *ᵥ y = y := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, z, hz, rfl⟩ := hy
    rw [map_mulVec_tmul, h z hz]
  | zero => rw [Matrix.mulVec_zero]
  | add y z _ _ hy hz => rw [Matrix.mulVec_add, hy, hz]
  | neg y _ hy => rw [Matrix.mulVec_neg, hy]

theorem stabHat_iff {M M' : ℕ} (B : Matrix (Fin M) (Fin M') E) (N : Matrix (Fin M') (Fin M) E)
    (hN : N * B = 1) {P : Set (Fin M → E)} {L' : Set (Fin M' → E)} (h1 : ∀ z, z ∈ L' ↔ B *ᵥ z ∈ P)
    (h2 : ∀ y ∈ P, B *ᵥ (N *ᵥ y) = y) (a b : Matrix (Fin M) (Fin M) (Af F ⊗[F] E))
    (a' b' : Matrix (Fin M') (Fin M') (Af F ⊗[F] E)) (hb : b * a = 1) (hb' : a' * b' = 1)
    (hr : a * B.map (inclR (F := F) (Af F)) = B.map (inclR (F := F) (Af F)) * a') :
    StabHat F P a ↔ StabHat F L' a' := by
  set Bf := B.map (inclR (F := F) (Af F)) with hBf
  set Nf := N.map (inclR (F := F) (Af F)) with hNf
  have hNB : Nf * Bf = 1 := by
    rw [hBf, hNf, ← Matrix.map_mul, hN, Matrix.map_one _ (map_zero _) (map_one _)]
  have hBm : ∀ z ∈ latHat F E L', Bf *ᵥ z ∈ latHat F E P := fun z hz =>
    mulVec_mem_latHat B (fun w hw => (h1 w).1 hw) hz
  have hNm : ∀ y ∈ latHat F E P, Nf *ᵥ y ∈ latHat F E L' := fun y hy =>
    mulVec_mem_latHat N (fun w hw => (h1 _).2 (by rw [h2 w hw]; exact hw)) hy
  have hBN : ∀ y ∈ latHat F E P, Bf *ᵥ (Nf *ᵥ y) = y := fun y hy => by
    rw [Matrix.mulVec_mulVec, hBf, hNf, ← Matrix.map_mul]
    exact mulVec_eq_of_mem_latHat _ (fun w hw => by rw [← Matrix.mulVec_mulVec]; exact h2 w hw) hy
  have hiff : ∀ z, z ∈ latHat F E L' ↔ Bf *ᵥ z ∈ latHat F E P := fun z =>
    ⟨hBm z, fun hz => by simpa [Matrix.mulVec_mulVec, hNB] using hNm _ hz⟩
  have hcomm : ∀ z, a *ᵥ (Bf *ᵥ z) = Bf *ᵥ (a' *ᵥ z) := fun z => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hr]
  refine ⟨fun h z => ?_, fun h y => ⟨fun hy => ?_, fun hy => ?_⟩⟩
  · rw [hiff, hiff, ← hcomm]
    exact h _
  · rw [← hBN y hy, hcomm]
    exact hBm _ ((h _).1 (hNm y hy))
  · have e1 : a' *ᵥ (b' *ᵥ (Nf *ᵥ (a *ᵥ y))) = Nf *ᵥ (a *ᵥ y) := by
      rw [Matrix.mulVec_mulVec, hb', Matrix.one_mulVec]
    have e2 : y = Bf *ᵥ (b' *ᵥ (Nf *ᵥ (a *ᵥ y))) := by
      have := congrArg (b *ᵥ ·) (hcomm (b' *ᵥ (Nf *ᵥ (a *ᵥ y))))
      simp only [e1, hBN _ hy] at this
      rw [Matrix.mulVec_mulVec _ b a, Matrix.mulVec_mulVec _ b a, hb, Matrix.one_mulVec,
        Matrix.one_mulVec] at this
      exact this.symm
    rw [e2]
    exact hBm _ ((h _).2 (by rw [e1]; exact hNm _ hy))

def finPt (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (g : HA (AF F) σ J) : HA (Af F) σ J :=
  (⟨Formalism.UG.bc (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom (HA.mat (AF F) σ J g), by
    have hg : Formalism.UG.cT (sigR (AF F) σ) (HA.mat (AF F) σ J g).1 * JR (AF F) J * (HA.mat (AF F) σ J g).1 =
      JR (AF F) J := (show HR (AF F) σ J from g).2
    have := GlobalTheory.UnitarySplit.map_cond _ _ _ (GlobalTheory.UnitarySplit.map_sig (sndA F) σ) (JR (AF F) J)
      (HA.mat (AF F) σ J g).1
    rw [hg, GlobalTheory.UnitarySplit.map_JR] at this
    exact this.symm⟩ : HR (Af F) σ J)

theorem map_snd_incl {m n : ℕ} (C : Matrix (Fin m) (Fin n) E) :
    (C.map (inclR (F := F) (AF F))).map (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom =
      C.map (inclR (F := F) (Af F)) := by
  ext i j
  simp [inclR]

end Lin

theorem stab_iff_of_frameRel : StabTransitive → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → UnramifiedAtFinite F E → ∀ (M M' : ℕ) (J : Matrix (Fin M) (Fin M) E) (J' : Matrix (Fin M') (Fin M') E) (B : Matrix (Fin M) (Fin M') E) (x : Fin 1 → Fin M → E), M' + 1 = M → IsHermND σ J → IsHermND σ J' → Formalism.UG.cT (σ : E →+* E) B * J * B = J' → (∀ j, hE σ J (x 0) (fun i => B i j) = 0) → hE σ J (x 0) (x 0) ≠ 0 → ∀ (L : Submodule (𝓞 E) (Fin M → E)) (L' : Set (Fin M' → E)), IsSelfDualLat σ J L → ∀ β : F, (β = 1 ∨ β = -1) → x 0 ∈ L → hE σ J (x 0) (x 0) = algebraMap F E β → (∀ y, y ∈ L' ↔ B *ᵥ y ∈ L) → ∀ (g : HA (AF F) σ J) (g' : HA (AF F) σ J'), g ∈ Hstab (AF F) σ J x → FrameRel J J' B g g' → (g ∈ stab σ J (L : Set (Fin M → E)) ↔ g' ∈ stab σ J' L') := by
  intro H F E _ _ _ _ _ σ hCM hu M M' J J' B x hM hJ hJ' hBJ hB hx L L' hL β hβ hxL hq hL' g g' hg hr
  let p := (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom
  have hN : (J'⁻¹ * (Formalism.UG.cT (σ : E →+* E) B * J)) * B = 1 := by
    rw [Matrix.mul_assoc, hBJ, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hJ'.2)]
  obtain ⟨k1, k2⟩ := exists_mulVec_eq σ J B _ hN (x 0) hM hB hx
  have h3 := (H F E σ hCM hu M J hJ L hL β hβ (x 0) hxL hq).2.2
  have hgf : finPt σ J g ∈ Hstab (Af F) σ J (fun _ => x 0) := by
    have e : (HA.mat (AF F) σ J g).1 *ᵥ (fun i => inclR (AF F) (x 0 i)) = fun i => inclR (AF F) (x 0 i) :=
      congrFun (MulAction.mem_stabilizer_iff.1 hg) 0
    have e' : (p ∘ fun i => inclR (AF F) (x 0 i)) = fun i => inclR (Af F) (x 0 i) := by
      funext i
      simp [p, inclR]
    refine MulAction.mem_stabilizer_iff.2 (funext fun _ => funext fun i => ?_)
    have := RingHom.map_mulVec p (HA.mat (AF F) σ J g).1 (fun i => inclR (AF F) (x 0 i)) i
    rw [e, e'] at this
    exact this.symm.trans (congrFun e' i)
  have h4 : StabHat F (L : Set (Fin M → E)) (finMat σ J g) ↔
      StabHat F (perpIn σ J L (x 0)) (finMat σ J g) := by
    have := SetLike.ext_iff.1 h3 (finPt σ J g)
    rw [Subgroup.mem_inf, Subgroup.mem_inf, and_iff_left hgf, and_iff_left hgf] at this
    exact this
  refine h4.trans (stabHat_iff (P := perpIn σ J L (x 0)) B _ hN (fun z => (hL' z).trans ⟨fun h => ⟨h, k1 z⟩, fun h => h.1⟩)
    (fun y hy => k2 y hy.2) _ (finMat σ J g⁻¹) _ (finMat σ J' g'⁻¹) ?_ ?_ ?_)
  · rw [← Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.finMat_mul, inv_mul_cancel, Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.finMat_one]
  · rw [← Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.finMat_mul, mul_inv_cancel, Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.finMat_one]
  · have : ((HA.mat (AF F) σ J g).1 * B.map (inclR (AF F))).map p =
        (B.map (inclR (AF F)) * (HA.mat (AF F) σ J' g').1).map p := congrArg (fun X => Matrix.map X p) hr
    have := (Matrix.map_mul (f := p)).symm.trans (this.trans (Matrix.map_mul (f := p)))
    rw [map_snd_incl] at this
    exact this

end GlobalTheory.StabFrame
