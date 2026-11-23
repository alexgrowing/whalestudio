import Formalism.HermitianCurvature.HermitianCurvatureProofs.TransferSmoothOfRegularity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PositiveOrbitOpen

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def GEqs (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (J : B.Mat k r → E) : Prop :=
  Q.CkLev k r 0 (2 * r + k + 1) (Q.OmPlus k r z z') J ∧
  (∀ X ∈ JfS.lieOf (Nset k r), ∃ c : ℂ, ∀ g ∈ JF.Om k r z z', Formalism.REAL.RdV X J g = c • J g) ∧
  (∀ X ∈ JfS.lieOf (Nset k r), ∃ c : ℂ, ∀ g ∈ JF.Om k r z z', Q.LdV X J g = c • J g) ∧
  (∀ Bs : Fin k → Fin (2 * r + k + 1) → ℂ, Q.IsFrameOf k r [z] Bs → ∀ w : ℂ, ∃ c : ℂ,
    ∀ g ∈ JF.Om k r z z', Q.capLft k r Bs w J g = c • J g) ∧
  (∀ Bs : Fin k → Fin (2 * r + k + 1) → ℂ, Q.IsFrameOf k r [z'] Bs → ∀ w : ℂ, ∃ c : ℂ,
    ∀ g ∈ JF.Om k r z z', Q.capR k r Bs w J g = c • J g) ∧
  (∀ Y : ℝ, ∃ c : ℂ, ∀ g ∈ JF.Om k r z z', Q.CV k r (Y : ℂ) J g = c • J g)

def NDiff : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (m : ℕ∞) (J : B.Mat k r → (Wq →L[ℂ] Wp)),
    J ∈ Gr.FFlM m k r D.z D.z' D.π D.π' 0 (Q.OmPlus k r D.z D.z') →
    (∀ X ∈ JfS.lieOf (Nset k r), ∃ c : ℂ, ∀ g ∈ JF.Om k r D.z D.z', Formalism.REAL.RdV X J g = c • J g) ∧
    (∀ X ∈ JfS.lieOf (Nset k r), ∃ c : ℂ, ∀ g ∈ JF.Om k r D.z D.z', Q.LdV X J g = c • J g)

def UCap : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (u u' : ℕ → ℝ) (J : B.Mat k r → (Wq →L[ℂ] Wp)),
    Q.IsType k r D.z D.π u → Q.IsType k r D.z' D.π' u' →
    J ∈ Gr.FFlM ((2 * r + k + 1 : ℕ) : ℕ∞) k r D.z D.z' D.π D.π' 0 (Q.OmPlus k r D.z D.z') →
    (∀ Bs : Fin k → Fin (2 * r + k + 1) → ℂ, Q.IsFrameOf k r [D.z] Bs → ∀ w : ℂ, ∃ c : ℂ,
      ∀ g ∈ JF.Om k r D.z D.z', Q.capLft k r Bs w J g = c • J g) ∧
    (∀ Bs : Fin k → Fin (2 * r + k + 1) → ℂ, Q.IsFrameOf k r [D.z'] Bs → ∀ w : ℂ, ∃ c : ℂ,
      ∀ g ∈ JF.Om k r D.z D.z', Q.capR k r Bs w J g = c • J g)

def GEqsPost : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (J : B.Mat k r → E) (ℓ : E →L[ℂ] ℂ), GEqs k r z z' J → GEqs k r z z' (fun g => ℓ (J g))

def SmoothOfCoeffs : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] (Dm : Set (B.Mat k r))
    (J : B.Mat k r → E), (∀ ℓ : E →L[ℂ] ℂ, Q.SmoothLev k r 0 Dm (fun g => ℓ (J g))) → Q.SmoothLev k r 0 Dm J

def GChart : Prop :=
  ∀ (k r : ℕ), ∃ d : ℕ, ∀ g₀ ∈ B.GV k r, ∃ (O : Set (Fin d → ℝ)) (U : Set (B.Mat k r))
    (κ : (Fin d → ℝ) → B.Mat k r) (Φ : B.Mat k r → (Fin d → ℝ)),
    IsOpen O ∧ IsOpen U ∧ g₀ ∈ U ∧ ContDiffOn ℝ ∞ κ O ∧ ContDiffOn ℝ ∞ Φ U ∧
    (∀ x ∈ O, κ x ∈ B.GV k r ∧ κ x ∈ U ∧ Φ (κ x) = x) ∧ (∀ g ∈ U, g ∈ B.GV k r → Φ g ∈ O ∧ κ (Φ g) = g)

def ChartEqs : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (d : ℕ) (O : Set (Fin d → ℝ)) (U : Set (B.Mat k r))
    (κ : (Fin d → ℝ) → B.Mat k r) (Φ : B.Mat k r → (Fin d → ℝ)) (u : B.Mat k r → ℂ),
    1 ≤ k → inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' →
    IsOpen O → IsOpen U → ContDiffOn ℝ ∞ κ O → ContDiffOn ℝ ∞ Φ U →
    (∀ x ∈ O, κ x ∈ B.GV k r ∧ κ x ∈ U ∧ Φ (κ x) = x) → (∀ g ∈ U, g ∈ B.GV k r → Φ g ∈ O ∧ κ (Φ g) = g) →
    (∀ x ∈ O, κ x ∈ Q.OmPlus k r z z') → GEqs k r z z' u →
    ∃ (ι : Type) (_ : Fintype ι) (P : ι → SOp d),
      (∀ j i w, ContDiffOn ℝ ∞ ((P j).a i w) O) ∧ (∀ j, (P j).ord ≤ 2 * r + k + 1) ∧
      ContDiffOn ℝ ((2 * r + k + 1 : ℕ) : WithTop ℕ∞) (fun x => u (κ x)) O ∧
      (∀ j, ∀ x ∈ O, (P j).app (fun y => u (κ y)) x = 0) ∧
      ∀ x ∈ O, ∀ ξ : Fin d → ℝ, ξ ≠ 0 → (∀ j, (P j).symb x ξ = 0) →
        ∃ Ξ : B.Mat k r, B.inLie k r Ξ ∧ Ξ ≠ 0 ∧ IsNilpotent Ξ ∧
          (∀ X ∈ JfS.lieOf (UWset k r z) ∪ JfS.lieOf (Nset k r), (Matrix.trace (Ξ * X)).re = 0) ∧
          (∀ X ∈ JfS.lieOf (UWset k r z') ∪ JfS.lieOf (Nset k r),
            (Matrix.trace (Ξ * (κ x * X * (κ x)⁻¹))).re = 0)

def ClassToWeak : Prop :=
  ∀ (d N : ℕ) (P : SOp d) (U : Set (Fin d → ℝ)) (u : (Fin d → ℝ) → ℂ),
    IsOpen U → (∀ i w, ContDiffOn ℝ ∞ (P.a i w) U) → P.ord ≤ N → ContDiffOn ℝ (N : WithTop ℕ∞) u U →
    (∀ x ∈ U, P.app u x = 0) →
    ∀ φ : (Fin d → ℝ) → ℂ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U → ∫ x, u x * P.tr φ x = 0

def LieSsetSplit : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → 0 < Tz k r z →
    ∀ X ∈ JfS.lieOf (Sset k r z), ∃ A ∈ JfS.lieOf (UWset k r z), ∃ Bn ∈ JfS.lieOf (Nset k r), X = A + Bn

def GRegScalar : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (u : B.Mat k r → ℂ),
    1 ≤ k → inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → GEqs k r z z' u →
    Q.SmoothLev k r 0 (Q.OmPlus k r z z') u

theorem gRegJ_of (hN : NDiff) (hU : UCap) (hP : GEqsPost) (hC : SmoothOfCoeffs) (hS : GRegScalar) : GRegJ := by
  intro k r Wp Wq _ _ _ _ _ _ D u u' J hT hT' hF hCV
  have hG : GEqs k r D.z D.z' J := by
    obtain ⟨hn1, hn2⟩ := hN k r Wp Wq D _ J hF
    obtain ⟨hu1, hu2⟩ := hU k r Wp Wq D u u' J hT hT' hF
    refine ⟨?_, hn1, hn2, hu1, hu2, hCV⟩
    intro g₀ hg₀
    obtain ⟨U, F, hUo, hgU, hFc, hJF⟩ := hF.1 g₀ hg₀
    exact ⟨U, F, hUo, hgU, by simpa [Gr.smM] using hFc, hJF⟩
  exact hC k r (Wq →L[ℂ] Wp) _ J (fun ℓ =>
    hS k r D.z D.z' _ D.k_pos D.z_mem D.z'_mem D.T_pos D.T'_pos (hP k r D.z D.z' _ J ℓ hG))

theorem gRegScalar_of (hK : GChart) (hE : ChartEqs) (hW : ClassToWeak) (hR : EllRegW) (hSym : JfS.SymbolNil)
    (hL : LieSsetSplit) : GRegScalar := by
  intro k r z z' u hk hz hz' hT hT' hG g₀ hg₀
  obtain ⟨d, hd⟩ := hK k r
  have hg₀G : g₀ ∈ B.GV k r := hg₀.1.1
  obtain ⟨O, U, κ, Φ, hO, hU, hg₀U, hκ, hΦ, hκO, hΦU⟩ := hd g₀ hg₀G
  have hO' : IsOpen (O ∩ κ ⁻¹' Q.OmPlus k r z z') :=
    hκ.continuousOn.isOpen_inter_preimage hO (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.omPlus_open z z')
  have hU' : IsOpen (U ∩ Φ ⁻¹' (O ∩ κ ⁻¹' Q.OmPlus k r z z')) :=
    hΦ.continuousOn.isOpen_inter_preimage hU hO'
  have hΦg₀ : Φ g₀ ∈ O ∩ κ ⁻¹' Q.OmPlus k r z z' := by
    obtain ⟨h1, h2⟩ := hΦU g₀ hg₀U hg₀G
    refine ⟨h1, ?_⟩
    show κ (Φ g₀) ∈ Q.OmPlus k r z z'
    rw [h2]; exact hg₀.2
  have hκO' : ∀ x ∈ O ∩ κ ⁻¹' Q.OmPlus k r z z',
      κ x ∈ B.GV k r ∧ κ x ∈ U ∩ Φ ⁻¹' (O ∩ κ ⁻¹' Q.OmPlus k r z z') ∧ Φ (κ x) = x := by
    intro x hx
    obtain ⟨h1, h2, h3⟩ := hκO x hx.1
    refine ⟨h1, ⟨h2, ?_⟩, h3⟩
    show Φ (κ x) ∈ O ∩ κ ⁻¹' Q.OmPlus k r z z'
    rw [h3]; exact hx
  have hΦU' : ∀ g ∈ U ∩ Φ ⁻¹' (O ∩ κ ⁻¹' Q.OmPlus k r z z'), g ∈ B.GV k r →
      Φ g ∈ O ∩ κ ⁻¹' Q.OmPlus k r z z' ∧ κ (Φ g) = g :=
    fun g hg hgG => ⟨hg.2, (hΦU g hg.1 hgG).2⟩
  obtain ⟨ι, hι, P, hPc, hPo, huc, hPu, hsym⟩ := hE k r z z' d _ _ κ Φ u hk hz hz' hT hT' hO' hU'
    (hκ.mono Set.inter_subset_left) (hΦ.mono Set.inter_subset_left) hκO' hΦU' (fun x hx => hx.2) hG
  have := hι
  have hsm : ContDiffOn ℝ ∞ (fun x => u (κ x)) (O ∩ κ ⁻¹' Q.OmPlus k r z z') := by
    refine hR d ι P _ _ hO' hPc huc.continuousOn
      (fun j φ hφ hφc hφs => hW d _ (P j) _ _ hO' (hPc j) (hPo j) huc (hPu j) φ hφ hφc hφs) ?_
    intro x hx ξ hξ
    by_contra hall
    simp only [not_exists, not_not] at hall
    obtain ⟨Ξ, hΞ, hΞ0, hnil, hl, hr⟩ := hsym x hx ξ hξ hall
    apply hΞ0
    have hxG := (hκO' x hx).1
    have hxOm : κ x ∈ Q.OmPlus k r z z' := hx.2
    refine hSym k r z z' hk hz hz' hT hT' (κ x) hxG ⟨hxOm.2, fun a => hxOm.1 ⟨(a : ℕ) + 1, by omega⟩ a.isLt⟩
      Ξ hΞ hnil ?_ ?_
    · intro X hX
      obtain ⟨A, hA, Bn, hB, rfl⟩ := hL k r z hz hT X hX
      simp only [mul_add, Matrix.trace_add, Complex.add_re]
      rw [hl A (Or.inl hA), hl Bn (Or.inr hB), add_zero]
    · intro X hX
      obtain ⟨A, hA, Bn, hB, rfl⟩ := hL k r z' hz' hT' X hX
      simp only [mul_add, add_mul, Matrix.trace_add, Complex.add_re]
      rw [hr A (Or.inl hA), hr Bn (Or.inr hB), add_zero]
  refine ⟨U ∩ Φ ⁻¹' (O ∩ κ ⁻¹' Q.OmPlus k r z z'), fun g => u (κ (Φ g)), hU', ⟨hg₀U, hΦg₀⟩, ?_, ?_⟩
  · exact hsm.comp (hΦ.mono Set.inter_subset_left) (fun g hg => hg.2)
  · intro g hg hgG
    show u g = u (κ (Φ g))
    rw [(hΦU g hg.1 hgG.1).2]

theorem jfSmoothBuilt_of_leaves (hN : NDiff) (hU : UCap) (hP : GEqsPost) (hC : SmoothOfCoeffs) (hK : GChart)
    (hE : ChartEqs) (hW : ClassToWeak) (hR : EllRegW) (hSym : JfS.SymbolNil) (hL : LieSsetSplit) :
    JfSmoothBuilt :=
  transfer_smooth_of_regularity (gRegJ_of hN hU hP hC (gRegScalar_of hK hE hW hR hSym hL))

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
