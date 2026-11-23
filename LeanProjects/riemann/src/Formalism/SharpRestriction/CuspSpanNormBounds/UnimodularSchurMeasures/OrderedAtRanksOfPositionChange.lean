import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.ExistsTowerOfLocalSetting
import Formalism.FormalDegreeBessel.FinalG

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ContDiff
open Formalism.MainNotions.S Formalism.MainNotions.CayleySignature Formalism.BasicNotions

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem exp_lie_algebra_mem_unitary (k r : ℕ) (X : CayleySignature.Mat k r) (hX : InLieHpk k r X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
  obtain ⟨-, hH2, -⟩ := Formalism.QuantumDeterminants.hpkFacts k r
  set Hm := Formalism.QuantumDeterminants.Hpk k r with hHm
  set Y : CayleySignature.Mat k r := (t : ℂ) • X with hYdef
  have hY : Yᴴ * Hm + Hm * Y = 0 := by
    have h1 : Yᴴ = (t : ℂ) • Xᴴ := by simp [hYdef, Matrix.conjTranspose_smul]
    have h2 : Xᴴ * Hm + Hm * X = 0 := hX
    rw [h1, hYdef, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, h2, smul_zero]
  have hinv : Hm⁻¹ = Hm := Matrix.inv_eq_right_inv hH2
  have hYh : Yᴴ = Hm * (-Y) * Hm⁻¹ := by
    rw [hinv]
    have h1 : Yᴴ * Hm = -(Hm * Y) := eq_neg_of_add_eq_zero_left hY
    calc Yᴴ = Yᴴ * (Hm * Hm) := by rw [hH2, Matrix.mul_one]
      _ = (Yᴴ * Hm) * Hm := by rw [Matrix.mul_assoc]
      _ = Hm * (-Y) * Hm := by rw [h1, Matrix.mul_neg]
  have hu : IsUnit Hm := ⟨⟨Hm, Hm, hH2, hH2⟩, rfl⟩
  have hdet : IsUnit (NormedSpace.exp Y).det := (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_exp Y)
  show (NormedSpace.exp Y)ᴴ * Hm * NormedSpace.exp Y = Hm
  rw [← Matrix.exp_conjTranspose, hYh, Matrix.exp_conj _ _ hu, hinv, Matrix.exp_neg]
  calc Hm * (NormedSpace.exp Y)⁻¹ * Hm * Hm * NormedSpace.exp Y
      = Hm * (NormedSpace.exp Y)⁻¹ * (Hm * Hm) * NormedSpace.exp Y := by simp only [Matrix.mul_assoc]
    _ = Hm * ((NormedSpace.exp Y)⁻¹ * NormedSpace.exp Y) := by rw [hH2, Matrix.mul_one, Matrix.mul_assoc]
    _ = Hm := by rw [Matrix.nonsing_inv_mul _ hdet, Matrix.mul_one]

theorem mat_mul_mem_UH_Hpk {k r : ℕ} {g h : CayleySignature.Mat k r} (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hh : h ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) : g * h ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
  have hg' : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hg
  have hh' : hᴴ * Formalism.QuantumDeterminants.Hpk k r * h = Formalism.QuantumDeterminants.Hpk k r := hh
  show (g * h)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (g * h) = Formalism.QuantumDeterminants.Hpk k r
  calc (g * h)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (g * h) = hᴴ * (gᴴ * Formalism.QuantumDeterminants.Hpk k r * g) * h := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Formalism.QuantumDeterminants.Hpk k r := by rw [hg', hh']

section Move

variable {k r : ℕ} {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H']
  [InnerProductSpace ℂ H']

theorem intertwiner_symm_apply (σ : CayleySignature.Mat k r → (H →L[ℂ] H)) (σ' : CayleySignature.Mat k r → (H' →L[ℂ] H')) (U : H ≃ₗᵢ[ℂ] H')
    (hU : ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ∀ x, U (σ g x) = σ' g (U x))
    (g : CayleySignature.Mat k r) (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (x' : H') :
    σ g (U.symm x') = U.symm (σ' g x') := by
  apply U.injective
  rw [hU g hg, U.apply_symm_apply, U.apply_symm_apply]

theorem smooth_vectors_intertwiner_symm (σ : CayleySignature.Mat k r → (H →L[ℂ] H)) (σ' : CayleySignature.Mat k r → (H' →L[ℂ] H')) (U : H ≃ₗᵢ[ℂ] H')
    (hU : ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ∀ x, U (σ g x) = σ' g (U x))
    {x' : H'} (hx : x' ∈ smoothVecs (k := k) (r := r) σ') : U.symm x' ∈ smoothVecs (k := k) (r := r) σ := by
  intro g₀ hg₀
  obtain ⟨Uo, F, hO, hmem, hF, hEq⟩ := hx g₀ hg₀
  refine ⟨Uo, fun g => U.symm (F g), hO, hmem, ?_, fun g hg hin => ?_⟩
  · exact ((U.symm.contDiff).restrict_scalars ℝ).comp_contDiffOn hF
  · have h1 : σ' g x' = F g := hEq g hg hin
    show σ g (U.symm x') = U.symm (F g)
    rw [intertwiner_symm_apply σ σ' U hU g hin, h1]

theorem deriv_isometry_symm_zero (U : H ≃ₗᵢ[ℂ] H') (f : ℝ → H') :
    deriv (fun t => U.symm (f t)) 0 = U.symm (deriv f 0) := by
  let e : H' ≃L[ℝ] H :=
    { toLinearEquiv := U.symm.toLinearEquiv.restrictScalars ℝ
      continuous_toFun := U.symm.continuous
      continuous_invFun := U.continuous }
  have he : ∀ y, e y = U.symm y := fun y => rfl
  by_cases hd : DifferentiableAt ℝ f 0
  · exact ((e : H' →L[ℝ] H).hasFDerivAt.comp_hasDerivAt 0 hd.hasDerivAt).deriv
  · have hd' : ¬ DifferentiableAt ℝ (fun t => U.symm (f t)) 0 := fun h =>
      hd ((e.comp_differentiableAt_iff (f := f) (x := 0)).1 h)
    rw [deriv_zero_of_not_differentiableAt hd, deriv_zero_of_not_differentiableAt hd', map_zero]

theorem derivative_word_intertwiner_symm (σ : CayleySignature.Mat k r → (H →L[ℂ] H)) (σ' : CayleySignature.Mat k r → (H' →L[ℂ] H')) (U : H ≃ₗᵢ[ℂ] H')
    (hU : ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ∀ x, U (σ g x) = σ' g (U x))
    (w : List (CayleySignature.Mat k r)) (hw : ∀ X ∈ w, InLieHpk k r X) (x' : H') :
    dsigW (k := k) (r := r) σ w (U.symm x') = U.symm (dsigW (k := k) (r := r) σ' w x') := by
  induction w with
  | nil => rfl
  | cons X w ih =>
    have ihw := ih (fun Y hY => hw Y (List.mem_cons_of_mem _ hY))
    show dsig σ X (dsigW σ w (U.symm x')) = U.symm (dsig σ' X (dsigW σ' w x'))
    rw [ihw]
    unfold dsig
    rw [← deriv_isometry_symm_zero U]
    congr 1
    funext t
    exact intertwiner_symm_apply σ σ' U hU _ (exp_lie_algebra_mem_unitary k r X (hw X List.mem_cons_self) t) _

theorem bessel_map_transport_sigma (σ : CayleySignature.Mat k r → (H →L[ℂ] H)) (σ' : CayleySignature.Mat k r → (H' →L[ℂ] H')) (U : H ≃ₗᵢ[ℂ] H')
    (hU : ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ∀ x, U (σ g x) = σ' g (U x))
    {Vp : Type} [NormedAddCommGroup Vp] [NormedSpace ℂ Vp] (z : Fin (2 * r + k + 1) → ℂ) (ψ : CayleySignature.Mat k r → ℂ)
    (π : CayleySignature.Mat k r → (Vp →L[ℂ] Vp)) (B : H → Vp) (N : ℕ)
    (hB : IsBesselMapSm z ψ σ π B) (hO : HasOrdLe k r N σ B) (hne : ∃ x ∈ smoothVecs (k := k) (r := r) σ, B x ≠ 0) :
    IsBesselMapSm z ψ σ' π (fun x' => B (U.symm x')) ∧ HasOrdLe k r N σ' (fun x' => B (U.symm x')) ∧
      ∃ x' ∈ smoothVecs (k := k) (r := r) σ', B (U.symm x') ≠ 0 := by
  have hs := fun {x' : H'} (hx : x' ∈ smoothVecs (k := k) (r := r) σ') => smooth_vectors_intertwiner_symm σ σ' U hU hx
  obtain ⟨b1, b2, b3, C, Ws, hWs, hbd⟩ := hB
  have hsum : ∀ (Ws : List (List (CayleySignature.Mat k r))), (∀ w ∈ Ws, ∀ X ∈ w, InLieHpk k r X) → ∀ v' : H',
      (Ws.map fun w => ‖dsigW (k := k) (r := r) σ w (U.symm v')‖) =
        (Ws.map fun w => ‖dsigW (k := k) (r := r) σ' w v'‖) := by
    intro Ws hWs v'
    refine List.map_congr_left fun w hw => ?_
    rw [derivative_word_intertwiner_symm σ σ' U hU w (hWs w hw), U.symm.norm_map]
  refine ⟨⟨fun v hv w hw => ?_, fun c v hv => ?_, fun h hh m hm v hv => ?_, C, Ws, hWs, fun v hv => ?_⟩, ?_, ?_⟩
  · show B (U.symm (v + w)) = _
    rw [map_add]; exact b1 _ (hs hv) _ (hs hw)
  · show B (U.symm (c • v)) = _
    rw [map_smul]; exact b2 c _ (hs hv)
  · show B (U.symm (σ' (h * m) v)) = _
    rw [← intertwiner_symm_apply σ σ' U hU _ (mat_mul_mem_UH_Hpk hh.1 hm.1)]
    exact b3 h hh m hm _ (hs hv)
  · rw [← hsum Ws hWs v]; exact hbd _ (hs hv)
  · obtain ⟨C', Ws', hW', hbd'⟩ := hO
    refine ⟨C', Ws', hW', fun v hv => ?_⟩
    rw [← hsum Ws' (fun w hw => (hW' w hw).2) v]; exact hbd' _ (hs hv)
  · obtain ⟨x, hx, hxne⟩ := hne
    refine ⟨U x, ?_, by rwa [U.symm_apply_apply]⟩
    have := smooth_vectors_intertwiner_symm σ' σ U.symm (fun g hg x' => (intertwiner_symm_apply σ σ' U hU g hg x').symm) hx
    simpa using this

theorem bessel_map_transport_pi (σ : CayleySignature.Mat k r → (H →L[ℂ] H)) {Vp Vp' : Type} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp]
    [NormedAddCommGroup Vp'] [InnerProductSpace ℂ Vp'] (z : Fin (2 * r + k + 1) → ℂ) (ψ : CayleySignature.Mat k r → ℂ)
    (π : CayleySignature.Mat k r → (Vp →L[ℂ] Vp)) (π' : CayleySignature.Mat k r → (Vp' →L[ℂ] Vp')) (A : Vp ≃ₗᵢ[ℂ] Vp')
    (hA : ∀ h ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ x, A (π h x) = π' h (A x)) (B : H → Vp) (N : ℕ)
    (hB : IsBesselMapSm z ψ σ π B) (hO : HasOrdLe k r N σ B) (hne : ∃ x ∈ smoothVecs (k := k) (r := r) σ, B x ≠ 0) :
    IsBesselMapSm z ψ σ π' (fun x => A (B x)) ∧ HasOrdLe k r N σ (fun x => A (B x)) ∧
      ∃ x ∈ smoothVecs (k := k) (r := r) σ, A (B x) ≠ 0 := by
  obtain ⟨b1, b2, b3, C, Ws, hWs, hbd⟩ := hB
  refine ⟨⟨fun v hv w hw => ?_, fun c v hv => ?_, fun h hh m hm v hv => ?_, C, Ws, hWs, fun v hv => ?_⟩, ?_, ?_⟩
  · show A (B (v + w)) = _
    rw [b1 v hv w hw, map_add]
  · show A (B (c • v)) = _
    rw [b2 c v hv, map_smul]
  · show A (B (σ (h * m) v)) = _
    rw [b3 h hh m hm v hv, map_smul, hA h hh]
  · show ‖A (B v)‖ ≤ _
    rw [A.norm_map]; exact hbd v hv
  · obtain ⟨C', Ws', hW', hbd'⟩ := hO
    exact ⟨C', Ws', hW', fun v hv => by
      show ‖A (B v)‖ ≤ _
      rw [A.norm_map]; exact hbd' v hv⟩
  · obtain ⟨x, hx, hxne⟩ := hne
    exact ⟨x, hx, fun h => hxne (A.injective (by rw [h, map_zero]))⟩

end Move

def DiscreteSeriesUniqueUpToUnitaryEquiv : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : CayleySignature.Mat k r → (H →L[ℂ] H)),
    IsDSHpk k r ε lam σ →
  ∀ (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H'] (σ' : CayleySignature.Mat k r → (H' →L[ℂ] H')),
    IsDSHpk k r ε lam σ' →
  ∃ U : H ≃ₗᵢ[ℂ] H', ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ∀ x, U (σ g x) = σ' g (U x)

def HighestWeightUnique : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (u : Fin k → ℝ), Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z →
    Formalism.QuantumDeterminants.IsHCParam u →
  ∀ (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [FiniteDimensional ℂ Vp]
    (π : CayleySignature.Mat k r → (Vp →L[ℂ] Vp)), IsHCTypeW k r z u π →
  ∀ (Vp' : Type) [NormedAddCommGroup Vp'] [InnerProductSpace ℂ Vp'] [FiniteDimensional ℂ Vp']
    (π' : CayleySignature.Mat k r → (Vp' →L[ℂ] Vp')), IsHCTypeW k r z u π' →
  ∃ A : Vp ≃ₗᵢ[ℂ] Vp', ∀ h ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ x, A (π h x) = π' h (A x)

def PositionChange : Prop :=
  ∀ (k r : ℕ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ), Formalism.QuantumDeterminants.IsHCParam u →
    Formalism.QuantumDeterminants.IsHCParam (lam48 k r v b) →
  ∀ (z z' : Fin (2 * r + k + 1) → ℂ) (c c' : Fin r → ℂ), Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → (∀ a, c a ≠ 0) →
    Formalism.QuantumDeterminants.inWb k r z' → 0 < Formalism.QuantumDeterminants.Tz k r z' → (∀ a, c' a ≠ 0) → (∃ g', IsFrameW k r z' g') →
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : CayleySignature.Mat k r → (H →L[ℂ] H)),
    IsDSHpk k r (eps48 k r) (lam48 k r v b) σ →
  ∀ (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [FiniteDimensional ℂ Vp]
    (π : CayleySignature.Mat k r → (Vp →L[ℂ] Vp)), IsHCTypeW k r z u π →
  ∀ (B : H → Vp) (N : ℕ), IsBesselMapSm z (psiGen k r z c) σ π B → HasOrdLe k r N σ B →
    (∃ x ∈ smoothVecs (k := k) (r := r) σ, B x ≠ 0) →
  ∃ (π' : CayleySignature.Mat k r → (Vp →L[ℂ] Vp)), IsHCTypeW k r z' u π' ∧
    ∃ B' : H → Vp, IsBesselMapSm z' (psiGen k r z' c') σ π' B' ∧ HasOrdLe k r N σ B' ∧
      ∃ x ∈ smoothVecs (k := k) (r := r) σ, B' x ≠ 0

theorem local_transport_of_position_change (hD : DiscreteSeriesUniqueUpToUnitaryEquiv) (hC : HighestWeightUnique) (hP : PositionChange) : LocalTransport := by
  intro k r u v b hu hl hsome z c hz hT hc H _ _ _ σ hσ Vp _ _ _ π hπ
  obtain ⟨z0, c0, hz0, hT0, hc0, H0, i1, i2, i3, σ0, hσ0, Vp0, j1, j2, j3, π0, hπ0, B0, hB0, hO0, hne0⟩ := hsome
  obtain ⟨π1, hπ1, B1, hB1, hO1, hne1⟩ :=
    hP k r u v b hu hl z0 z c0 c hz0 hT0 hc0 hz hT hc ⟨hπ.choose, hπ.choose_spec.1⟩ H0 σ0 hσ0 Vp0 π0 hπ0 B0 _ hB0 hO0 hne0
  obtain ⟨U, hU⟩ := hD k r _ _ hl H0 σ0 hσ0 H σ hσ
  obtain ⟨hB2, hO2, hne2⟩ := bessel_map_transport_sigma σ0 σ U hU z _ π1 B1 _ hB1 hO1 hne1
  obtain ⟨A, hA⟩ := hC k r z u hz hT hu Vp0 π1 hπ1 Vp π hπ
  obtain ⟨hB3, hO3, hne3⟩ := bessel_map_transport_pi σ z _ π1 π A hA _ _ hB2 hO2 hne2
  exact ⟨_, hB3, hO3, hne3⟩

theorem ordered_at_ranks_of_position_change (D : D7) (X : ThetaX D) (C : ℝ) (h3 : PointsLemma D X) (h4 : Step4 D X) (hD : DiscreteSeriesUniqueUpToUnitaryEquiv)
    (hC : HighestWeightUnique) (hP : PositionChange) : OrderedAtRanks D C :=
  ordered_at_ranks_of_tower_hyp D X C h3 h4 (local_transport_of_position_change hD hC hP)

end Formalism.MainNotions.LeviCoordinates

end
