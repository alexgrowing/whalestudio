import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarChart
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume GlobalTheory.FlagQuotHaar
open scoped ENNReal
open scoped Matrix
namespace GlobalTheory.FlagTransport
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
  {E' : Type} [Field E'] [NumberField E'] [IsCMField E']

theorem gram_eq (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G x = xᵀ * G.map τ * x.map (starRingEnd ℂ) := by
  ext a b
  simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]

theorem gram_mul_right (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (M N : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G (M * N) = Nᵀ * gram τ G M * N.map (starRingEnd ℂ) := by
  rw [gram_eq, gram_eq, Matrix.transpose_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc]

variable (X : Data E r) (X' : Data E' r) (e : X.Ψ ≃ X'.Ψ)

def entEquiv : Ent X ≃ Ent X' := Equiv.prodCongr e (Equiv.refl _)

def idxEquiv : Fin (nd X) ≃ Fin (nd X') :=
  (Fintype.equivFin (Ent X)).symm.trans ((entEquiv X X' e).trans (Fintype.equivFin (Ent X')))

def coordIso : V (nd X) ≃ₗᵢ[ℂ] V (nd X') := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (idxEquiv X X' e)

theorem coordIso_apply (z : V (nd X)) (k : Fin (nd X')) :
    coordIso X X' e z k = z ((idxEquiv X X' e).symm k) := rfl

theorem idxEquiv_symm_equivFin (τ' : X'.Ψ) (p : {p : Fin r × Fin r // p.2 < p.1}) :
    (idxEquiv X X' e).symm (Fintype.equivFin (Ent X') (τ', p)) = Fintype.equivFin (Ent X) (e.symm τ', p) := by
  show Fintype.equivFin (Ent X) ((entEquiv X X' e).symm
    ((Fintype.equivFin (Ent X')).symm (Fintype.equivFin (Ent X') (τ', p)))) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem nmat_coordIso (z : V (nd X)) (τ' : X'.Ψ) :
    nmat X' (coordIso X X' e z) τ' = nmat X z (e.symm τ') := by
  funext a b
  unfold nmat
  split_ifs with h
  · refine (coordIso_apply X X' e z _).trans ?_
    exact congrArg (fun k : Fin (nd X) => z k) (idxEquiv_symm_equivFin X X' e τ' _)
  · rfl
  · rfl

def coordIsoR : V (nd X) ≃ₗᵢ[ℝ] V (nd X') :=
  { (coordIso X X' e).toLinearEquiv.restrictScalars ℝ with norm_map' := (coordIso X X' e).norm_map }

theorem coordIso_mp : MeasurePreserving (coordIso X X' e) := (coordIsoR X X' e).measurePreserving

theorem map_restrict_withDensity {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
    {ν : Measure β} (S : α ≃ᵐ β) (hS : MeasurePreserving S μ ν) {Ω : Set α} {Ω' : Set β}
    (hΩ : S ⁻¹' Ω' = Ω) {d : α → ℝ≥0∞} {d' : β → ℝ≥0∞} (hd : ∀ x, d' (S x) = d x) :
    Measure.map S ((μ.restrict Ω).withDensity d) = (ν.restrict Ω').withDensity d' := by
  ext A hA
  rw [S.map_apply, withDensity_apply _ hA, withDensity_apply _ (S.measurable hA), ← hS.map_eq,
    S.restrict_map, S.restrict_map, lintegral_map_equiv, hΩ]
  simp_rw [hd]

theorem trF_cpt (z : V (nd X)) :
    trF X X' e (cpt X (baseFr X) z) = cpt X' (baseFr X') (coordIso X X' e z) := by
  funext τ'
  have hB : IsUnit (mat (baseFr X) (e.symm τ')).det :=
    isUnit_iff_ne_zero.2 (X.signature (e.symm τ')).choose_spec.1
  have h1 : mat (cpt X (baseFr X) z) (e.symm τ') =
      mat (baseFr X) (e.symm τ') * mat (nmat X z) (e.symm τ') := rfl
  have h2 : mat (nmat X' (coordIso X X' e z)) τ' = mat (nmat X z) (e.symm τ') := by
    unfold mat; rw [nmat_coordIso]
  show (mat (baseFr X') τ' * (mat (baseFr X) (e.symm τ'))⁻¹ * mat (cpt X (baseFr X) z) (e.symm τ') :
      Matrix (Fin r) (Fin r) ℂ) = (mat (baseFr X') τ' * mat (nmat X' (coordIso X X' e z)) τ' : Matrix (Fin r) (Fin r) ℂ)
  rw [h1, h2, Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hB]

theorem gram_cpt_base {F : Type} [Field F] [NumberField F] [IsCMField F] (Y : Data F r) (z : V (nd Y)) (τ : Y.Ψ) :
    gram τ.1 Y.Gm (mat (cpt Y (baseFr Y) z) τ) =
      (mat (nmat Y z) τ)ᵀ * sgnMat r Y.p0 * (mat (nmat Y z) τ).map (starRingEnd ℂ) := by
  have h1 : mat (cpt Y (baseFr Y) z) τ = mat (baseFr Y) τ * mat (nmat Y z) τ := rfl
  rw [h1, gram_mul_right, baseFr_mem Y τ]

variable {X X'} in
theorem dmin_coordIso (hp : X.p0 = X'.p0) (z : V (nd X)) (τ' : X'.Ψ) (i : Fin (r + 1)) :
    dmin X'.Gm (cpt X' (baseFr X') (coordIso X X' e z)) τ' i = dmin X.Gm (cpt X (baseFr X) z) (e.symm τ') i := by
  have h2 : mat (nmat X' (coordIso X X' e z)) τ' = mat (nmat X z) (e.symm τ') := by
    unfold mat; rw [nmat_coordIso]
  unfold dmin
  rw [gram_cpt_base, gram_cpt_base, h2, hp]

theorem det_cpt_base_ne {F : Type} [Field F] [NumberField F] [IsCMField F] (Y : Data F r) (z : V (nd Y)) (τ : Y.Ψ) :
    (mat (cpt Y (baseFr Y) z) τ).det ≠ 0 ↔ (mat (nmat Y z) τ).det ≠ 0 := by
  have h1 : mat (cpt Y (baseFr Y) z) τ = mat (baseFr Y) τ * mat (nmat Y z) τ := rfl
  have hB : (mat (baseFr Y) τ).det ≠ 0 := (Y.signature τ).choose_spec.1
  rw [h1, Matrix.det_mul, mul_ne_zero_iff]
  exact ⟨fun h => h.2, fun h => ⟨hB, h⟩⟩

variable {X X'} in
theorem mem_dom_coordIso (hp : X.p0 = X'.p0) (z : V (nd X)) :
    cpt X' (baseFr X') (coordIso X X' e z) ∈ X'.dom ↔ cpt X (baseFr X) z ∈ X.dom := by
  show (∀ τ' : X'.Ψ, _ ∧ _) ↔ (∀ τ : X.Ψ, _ ∧ _)
  refine Iff.trans ?_ e.symm.forall_congr_right
  refine forall_congr' fun τ' => ?_
  have h2 : mat (nmat X' (coordIso X X' e z)) τ' = mat (nmat X z) (e.symm τ') := by
    unfold mat; rw [nmat_coordIso]
  rw [det_cpt_base_ne, det_cpt_base_ne, h2, hp]
  simp only [dmin_coordIso e hp]

variable {X X'} in
theorem densF_coordIso (hp : X.p0 = X'.p0) (z : V (nd X)) :
    densF X' (baseFr X') (coordIso X X' e z) = densF X (baseFr X) z := by
  unfold densF
  simp only [dmin_coordIso e hp]
  exact (Fintype.prod_equiv e.symm _ _ fun _ => rfl)

variable {X X'} in
theorem map_muF (hp : X.p0 = X'.p0) :
    Measure.map (coordIso X X' e).toHomeomorph.toMeasurableEquiv (muF X (baseFr X)) = muF X' (baseFr X') := by
  unfold muF
  refine map_restrict_withDensity _ (coordIso_mp X X' e) ?_ ?_
  · ext z
    exact mem_dom_coordIso e hp z
  · intro z
    exact congrArg ENNReal.ofReal (densF_coordIso e hp z)

end

theorem lintegral_trF_cpt : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {E' : Type} [Field E']
    [NumberField E'] [IsCMField E'] (X : Data E r) (X' : Data E' r) (e : X.Ψ ≃ X'.Ψ), X.p0 = X'.p0 →
    ∀ (φ : Frame X'.Ψ r → ℝ≥0∞), Measurable φ →
      ∫⁻ z, φ (trF X X' e (cpt X (baseFr X) z)) ∂muF X (baseFr X) =
        ∫⁻ z, φ (cpt X' (baseFr X') z) ∂muF X' (baseFr X') := by
  intro E _ _ _ r E' _ _ _ X X' e hp φ _
  rw [← map_muF e hp, lintegral_map_equiv]
  simp_rw [trF_cpt]
  rfl

end GlobalTheory.FlagTransport
