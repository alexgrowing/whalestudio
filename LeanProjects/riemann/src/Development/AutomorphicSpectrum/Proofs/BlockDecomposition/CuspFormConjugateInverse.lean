import Mathlib
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.GelfandKazhdanDuality.IsCuspFormDualMap
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothConjugateInverseMem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartStarInvT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub

noncomputable section

open NumberField IsDedekindDomain Topology Matrix MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair GlobalTheory.DiscSpec
open PositivityTheory.PRW.GKD GlobalTheory.SmGL GlobalTheory.ThetaPull

namespace GlobalTheory.CompanionTheory.DualCusp

section Semilinear

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem qdet_semilinear {n : ℕ} (D : V →ₗ⋆[ℂ] V) (X Y : Fin n → Fin n → Module.End ℂ V)
    (h : ∀ i j v, Y i j (D v) = D (X i j v)) (u : ℂ) (v : V) :
    Formalism.REAL.qdet Y (star u) (D v) = D (Formalism.REAL.qdet X u v) := by
  have hp : ∀ {t : ℕ} (x y : Fin t → Module.End ℂ V), (∀ k v, y k (D v) = D (x k v)) →
      ∀ v, (List.ofFn y).prod (D v) = D ((List.ofFn x).prod v) := by
    intro t
    induction t with
    | zero => intro x y _ v; simp
    | succ t ih =>
      intro x y h v
      simp only [List.ofFn_succ, List.prod_cons, Module.End.mul_apply]
      rw [ih _ _ (fun k => h k.succ), h]
  have hT : ∀ (w : ℂ) (i j : Fin n) (v : V),
      Formalism.REAL.Tm Y (star w) i j (D v) = D (Formalism.REAL.Tm X w i j v) := by
    intro w i j v
    simp only [Formalism.REAL.Tm, LinearMap.add_apply, map_add, h]
    split_ifs
    · simp [Module.algebraMap_end_apply]
    · simp
  simp only [Formalism.REAL.qdet, Formalism.REAL.qminor, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, Module.End.intCast_apply, Module.End.intCast_apply, map_zsmul]
  congr 1
  refine hp _ _ (fun k v => ?_) v
  have := hT (u - (k : ℂ)) (id (σ k)) (id k) v
  simpa using this

end Semilinear

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

variable (E a) in

def dual : Sm E a →ₗ⋆[ℂ] Sm E a where
  toFun φ := ⟨fun g => star (φ.1 (invA E a g)), GlobalTheory.CompanionTheory.DualSm.conj_invA_mem_Sm φ.2⟩
  map_add' φ ψ := Subtype.ext (funext fun g => by simp)
  map_smul' c φ := Subtype.ext (funext fun g => by simp)

theorem dual_apply (φ : Sm E a) (g : GA E a) : (dual E a φ).1 g = star (φ.1 (invA E a g)) := rfl

theorem dual_dual (φ : Sm E a) : dual E a (dual E a φ) = φ :=
  Subtype.ext (funext fun g => by simp [dual_apply, invA_invA])

theorem dual_injective : Function.Injective (dual E a) :=
  Function.LeftInverse.injective (g := dual E a) dual_dual

theorem act_dual (o : Op E a) (φ : Sm E a) : act o (dual E a φ) = dual E a (act (invTOp o) φ) :=
  GlobalTheory.CompanionTheory.DualAct.act_star_invT o φ _ _ (fun _ => rfl) (fun _ => rfl)

theorem lieS_dual (i j : Fin a) (x : Cinf E) (φ : Sm E a) :
    lieS E a i j x (dual E a φ) = -dual E a (lieS E a j i x φ) := by
  have h := act_dual (.lie (toL (Matrix.single i j x))) φ
  have e : (toL (-(Matrix.of (toL (Matrix.single i j x)))ᵀ) : Lie E a) = -toL (Matrix.single j i x) := by
    change toL (-(Matrix.single i j x)ᵀ) = _
    rw [Matrix.transpose_single]
    rfl
  change lie E a _ _ = dual E a (lie E a (toL (-(Matrix.of (toL (Matrix.single i j x)))ᵀ)) φ) at h
  rw [e, map_neg, LinearMap.neg_apply, map_neg] at h
  exact h

theorem Eop_dual (τ : E →+* ℂ) (i j : Fin a) (φ : Sm E a) :
    Eop τ i j (dual E a φ) = dual E a ((-Eop (ComplexEmbedding.conjugate τ) j i) φ) := by
  have e1 : atEmb (ComplexEmbedding.conjugate τ) 1 = atEmb τ 1 := by rw [atEmb_conj, map_one]
  have e2 : atEmb (ComplexEmbedding.conjugate τ) Complex.I = -atEmb τ Complex.I := by
    rw [atEmb_conj, Complex.conj_I, atEmb_eq, atEmb_eq τ Complex.I]
    simp
  have c2 : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num]
    exact Complex.conj_ofReal _
  simp only [Eop, e1, e2, map_neg, LinearMap.neg_apply, LinearMap.smul_apply, LinearMap.sub_apply, lieS_dual,
    map_smulₛₗ, map_sub, c2, Complex.conj_I, neg_neg, smul_neg]
  module

theorem cap_dual (τ : E →+* ℂ) (u : ℂ) (φ : Sm E a) :
    cap τ u (dual E a φ) =
      dual E a (((-1 : ℂ) ^ a • cap (a := a) (ComplexEmbedding.conjugate τ) (-star u) : Module.End ℂ (Sm E a)) φ) := by
  have h := qdet_semilinear (dual E a) (fun i j => -Eop (ComplexEmbedding.conjugate τ) j i) (Eop τ)
    (fun i j v => Eop_dual τ i j v) (star u + ((a : ℂ) - 1) / 2) φ
  have e : star (star u + ((a : ℂ) - 1) / 2) = u + ((a : ℂ) - 1) / 2 := by simp
  have e' : (a : ℂ) - 1 - (star u + ((a : ℂ) - 1) / 2) = -star u + ((a : ℂ) - 1) / 2 := by ring
  rw [e, (GlobalTheory.CapelliNegT.glRel_negT_and_qdet _ a _ (glRel_Eop (ComplexEmbedding.conjugate τ))).2, e', ← cap, ← cap] at h
  exact h

theorem Zalg_dual {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) :
    ∃ z' ∈ Zalg E a, ∀ φ, z (dual E a φ) = dual E a (z' φ) := by
  induction hz using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨τ, u, rfl⟩ := hx
    exact ⟨_, Subalgebra.smul_mem _ (Algebra.subset_adjoin (by exact ⟨_, _, rfl⟩)) _, cap_dual τ u⟩
  | algebraMap c =>
    exact ⟨algebraMap ℂ _ (star c), Subalgebra.algebraMap_mem _ _, fun φ => by
      simp [Module.algebraMap_end_apply, map_smulₛₗ]⟩
  | add x y _ _ hx hy =>
    obtain ⟨x', h1, h2⟩ := hx
    obtain ⟨y', h3, h4⟩ := hy
    exact ⟨x' + y', add_mem h1 h3, fun φ => by simp [h2, h4]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨x', h1, h2⟩ := hx
    obtain ⟨y', h3, h4⟩ := hy
    exact ⟨x' * y', mul_mem h1 h3, fun φ => by simp [h2, h4]⟩

theorem finiteDimensional_map (S : Submodule ℂ (Sm E a)) (hS : FiniteDimensional ℂ S) :
    FiniteDimensional ℂ (S.map (dual E a)) := by
  obtain ⟨s, rfl⟩ := (Submodule.fg_iff_finiteDimensional S).2 hS
  rw [Submodule.map_span]
  exact (Submodule.fg_iff_finiteDimensional _).1 (Submodule.fg_span (s.finite_toSet.image _))

theorem continuous_invT {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous (invT a R) := by
  refine Units.continuous_iff.2 ⟨continuous_matrix fun i j => ?_, continuous_matrix fun i j => ?_⟩
  · change Continuous fun g : GL (Fin a) R => (g⁻¹).val j i
    exact Units.continuous_coe_inv.matrix_elem _ _
  · change Continuous fun g : GL (Fin a) R => g.val j i
    exact Units.continuous_val.matrix_elem _ _

omit [IsTotallyComplex E] in
theorem norm_toL_transpose_le (M : Matrix (Fin a) (Fin a) (Cinf E)) : ‖toL Mᵀ‖ ≤ ‖toL M‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j =>
    (norm_le_pi_norm (toL M j) i).trans (norm_le_pi_norm (toL M) j)

omit [IsTotallyComplex E] in
theorem height_invT_le (y : GL (Fin a) (Cinf E)) : height (invT a (Cinf E) y) ≤ height y := by
  have h1 : ‖toL (invT a (Cinf E) y).val‖ ≤ ‖toL (y⁻¹).val‖ := norm_toL_transpose_le (y⁻¹).val
  have h2 : ‖toL ((invT a (Cinf E) y)⁻¹).val‖ ≤ ‖toL y.val‖ := norm_toL_transpose_le y.val
  unfold height
  linarith

omit [IsTotallyComplex E] in

theorem height_invT (y : GL (Fin a) (Cinf E)) : height (invT a (Cinf E) y) = height y := by
  refine le_antisymm (height_invT_le y) ?_
  have h := height_invT_le (invT a (Cinf E) y)
  have e : invT a (Cinf E) (invT a (Cinf E) y) = y := Units.ext (Matrix.transpose_transpose y.val)
  rwa [e] at h

theorem isAutForm_dual {φ : Sm E a} (h : IsAutForm φ) : IsAutForm (dual E a φ) where
  left γ g := by
    rw [dual_apply, dual_apply, map_mul]
    have e : invA E a (ratGL E a γ) = ratGL E a (invT a E γ) :=
      (GlobalTheory.CompanionTheory.DualAct.map_invT (algebraMap E (Ad E)) γ).symm
    rw [e, h.left]
  level := by
    convert h.level.preimage (continuous_invT (a := a) (R := Af E)) using 1
    ext k
    exact (Eq.congr_left (act_dual (.fin k) φ)).trans dual_injective.eq_iff
  kfin := by
    have := h.kfin
    have := finiteDimensional_map _ this
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k => cptRep E a k φ)).map
      (dual E a)) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨_, rfl⟩, (act_dual (.cpt k) φ).symm⟩
  zfin := by
    have := finiteDimensional_map _ h.zfin
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) ''
      Zalg E a)).map (dual E a)) (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨z', h1, h2⟩ := Zalg_dual hz
    exact ⟨_, Submodule.subset_span ⟨z', h1, rfl⟩, (h2 φ).symm⟩
  growth g := by
    obtain ⟨C, N, h1⟩ := h.growth (invA E a g)
    refine ⟨C, N, fun y => ?_⟩
    have e : (dual E a φ).1 (g * infGL E a y) =
        star (φ.1 (invA E a g * infGL E a (invT a (Cinf E) y))) := by
      rw [dual_apply, map_mul, GlobalTheory.CompanionTheory.DualAct.invT_infGL]
    have h2 := h1 (invT a (Cinf E) y)
    rw [height_invT] at h2
    rw [e, norm_star]
    exact h2

omit [IsTotallyComplex E] in

theorem phiU_eq : PhiU a (Ad E) = ratGL E a (PhiU a E) := by
  ext i j
  change GlobalTheory.Tw.Phi a (Ad E) i j = algebraMap E (Ad E) (GlobalTheory.Tw.Phi a E i j)
  simp only [GlobalTheory.Tw.Phi, Matrix.of_apply]
  split_ifs <;> simp

theorem invA_eq (g : GA E a) :
    invA E a g = (PhiU a (Ad E))⁻¹ * thetaGL a (RingHom.id (Ad E)) g * PhiU a (Ad E) := by
  have e : GeneralLinearGroup.map (RingHom.id (Ad E)) g = g := by
    ext i j
    rfl
  change _ = (PhiU a (Ad E))⁻¹ * (PhiU a (Ad E) * invT a (Ad E) (GeneralLinearGroup.map (RingHom.id (Ad E)) g) *
    (PhiU a (Ad E))⁻¹) * PhiU a (Ad E)
  rw [e]
  group

omit [IsTotallyComplex E] in
theorem blockMap_id_mem_ratN {r s : ℕ} (h : r + s = a) {x : BlockIx a r → Ad E} (hx : x ∈ ratN E a r) :
    blockMap h (RingHom.id (Ad E)) x ∈ ratN E a s := by
  obtain ⟨y, rfl⟩ := hx
  refine ⟨blockMap h (RingHom.id E) y, funext fun p => ?_⟩
  change algebraMap E (Ad E) (_ * (-y _)) = _ * (-algebraMap E (Ad E) _)
  rw [map_mul, map_neg, map_pow, map_neg, map_one]

theorem isCuspidal_dual {φ : GA E a → ℂ} (hl : ∀ γ g, φ (ratGL E a γ * g) = φ g) (hφ : IsCuspidal φ) :
    IsCuspidal fun g => star (φ (invA E a g)) := by
  intro r h0 h1 _ _ μ 𝓕 hμ hF g
  obtain ⟨s, h⟩ : ∃ s, r + s = a := ⟨a - r, by omega⟩
  have h' : s + r = a := by omega
  let c := RingHom.id (Ad E)
  let β : (BlockIx a r → Ad E) ≃ₜ+ (BlockIx a s → Ad E) :=
    { toFun := blockMap h c
      invFun := blockMap h' c
      left_inv := blockMap_blockMap h h' _ fun _ => rfl
      right_inv := blockMap_blockMap h' h _ fun _ => rfl
      map_add' := map_add _
      continuous_toFun := continuous_blockMap h _ continuous_id
      continuous_invFun := continuous_blockMap h' _ continuous_id }
  let e : ratN E a s ≃ ratN E a r :=
    { toFun := fun y => ⟨β.symm y, blockMap_id_mem_ratN h' y.2⟩
      invFun := fun x => ⟨β x, blockMap_id_mem_ratN h x.2⟩
      left_inv := fun y => Subtype.ext (β.apply_symm_apply y)
      right_inv := fun x => Subtype.ext (β.symm_apply_apply x) }
  borelize (BlockIx a s → Ad E)
  let m := β.toHomeomorph.toMeasurableEquiv
  have h2 := hφ s (by omega) (by omega) (μ.map m) (m '' 𝓕) (β.isAddHaarMeasure_map μ)
    (hF.image_of_equiv m.toEquiv (MeasurePreserving.symm m ⟨m.measurable, rfl⟩).quasiMeasurePreserving e fun y x => by
      change β (β.symm y + x) = y + β x
      rw [map_add, β.apply_symm_apply]) (PhiU a (Ad E) * invA E a g)
  rw [m.measurableEmbedding.setIntegral_map, m.injective.preimage_image] at h2
  have e1 : ∀ x : BlockIx a r → Ad E,
      φ (invA E a (unip x * g)) = φ (unip (m x) * (PhiU a (Ad E) * invA E a g)) := fun x => by
    have hm : unip (m x) = thetaGL a c (unip x) := (thetaGL_unip h c x).symm
    rw [map_mul, invA_eq (unip x), hm, phiU_eq, ← map_inv, mul_assoc, mul_assoc, hl, ← mul_assoc]
  have h3 : ∫ x in 𝓕, φ (invA E a (unip x * g)) ∂μ = 0 := by
    rw [← h2]
    congr 1
    funext x
    exact e1 x
  change ∫ x in 𝓕, (starRingEnd ℂ) (φ (invA E a (unip x * g))) ∂μ = 0
  rw [integral_conj, h3, map_zero]

end GlobalTheory.CompanionTheory.DualCusp

open GlobalTheory.CompanionTheory.DualCusp in

theorem GlobalTheory.CompanionTheory.DualCusp.isCuspForm_conj_invA {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}
    (φ : Sm E a) (hψ : (fun g => star (φ.1 (invA E a g))) ∈ Sm E a) (h : IsCuspForm φ) :
    IsCuspForm (⟨fun g => star (φ.1 (invA E a g)), hψ⟩ : Sm E a) :=
  ⟨isAutForm_dual h.1, isCuspidal_dual h.1.left h.2⟩

end
