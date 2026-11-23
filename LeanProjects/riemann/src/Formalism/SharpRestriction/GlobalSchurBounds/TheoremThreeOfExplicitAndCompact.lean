import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

noncomputable section

namespace Formalism.MainNotions.StandardLattice

open NumberField Formalism.BasicNotions Finset
open scoped ENNReal

def projection_sandwich_lattice (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ (W : HSpace D.host.E) (P Q : ℕ), W.SigOK → (∀ τ, W.sig τ = (P, Q)) → 3 ≤ W.rank →
    ∀ s : Bool, (if s then 1 ≤ P else 1 ≤ Q) → ∃ x : W.V, W.hT x x = (if s then 1 else -1)

def projection_lemma_base_level (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ (W : HSpace D.host.E) (P Q : ℕ), W.SigOK → (∀ τ, W.sig τ = (P, Q)) → 3 ≤ W.rank →
    ∀ s : Bool, (if s then 1 ≤ P else 1 ≤ Q) →
    ∀ x : W.V, W.hT x x = (if s then 1 else -1) →
      ∃ (W' : HSpace D.host.E) (ι : W'.V →ₗ[D.host.E] W.V),
        HSpace.IsIsomEmb W' W ι ∧ LinearMap.range ι = LinearMap.ker (W.hT x) ∧ W'.SigOK ∧
        (∀ τ, W'.sig τ = (if s then (P - 1, Q) else (P, Q - 1))) ∧
        D.vol W / D.vol W' = Formalism.HermitianLatticesTheory.massRatioRightSide D.host.E W.rank

theorem mass_volume_of_all_x (D : D7) (ha : projection_sandwich_lattice D) (hE : projection_lemma_base_level D) : Conclusion2 D := by
  intro W P Q h1 h2 h3 s hs
  obtain ⟨x, hx⟩ := ha W P Q h1 h2 h3 s hs
  exact ⟨x, hx, hE W P Q h1 h2 h3 s hs x hx⟩

section DS

open Formalism.MainNotions.S MeasureTheory Matrix
open scoped InnerProductSpace ComplexOrder

def DiscreteSeriesDegreeBoundsOfGap (D : D7) : Prop :=
  ∀ (N : ℕ) (ε : Fin N → Bool) (lam : Fin N → ℝ) (ep0 h0 : ℝ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (w : H),
    let p : ℝ := (Finset.univ.filter (fun a => ε a = true)).card
    let q : ℝ := (Finset.univ.filter (fun a => ε a = false)).card
    1 ≤ p → 1 ≤ q →
    Formalism.QuantumDeterminants.IsHCParam lam → Formalism.QuantumDeterminants.GapAtLeast ε lam h0 →
    Real.exp (-(N : ℝ)) ≤ ep0 → ep0 < 1 / 2 →
    8192 * min p q * (p * q) ^ 3 * Real.log N / ep0 ^ 2 ≤ h0 →
    IsDS ε lam σ → w ≠ 0 →
    (1 - ep0) * Formalism.QuantumDeterminants.fdegHC lam ≤ fdegOf ((D.s.cdScale N ε : ENNReal) • Formalism.REAL.muG ε) σ w ∧
    fdegOf ((D.s.cdScale N ε : ENNReal) • Formalism.REAL.muG ε) σ w ≤
      4 * (Module.finrank ℂ (lowKSub ε lam σ) : ℝ) * (3 * p * q * lamAbs lam) ^ (p * q)

def DiscreteSeriesUpperBoundOfLargeGap (D : D7) : Prop :=
  ∀ (N : ℕ) (ε : Fin N → Bool) (lam : Fin N → ℝ) (h0 : ℝ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (w : H),
    let p : ℝ := (Finset.univ.filter (fun a => ε a = true)).card
    let q : ℝ := (Finset.univ.filter (fun a => ε a = false)).card
    1 ≤ p → 1 ≤ q →
    Formalism.QuantumDeterminants.IsHCParam lam → Formalism.QuantumDeterminants.GapAtLeast ε lam h0 →
    120 * (N : ℝ) * (min p q) ^ ((3 : ℝ) / 2) ≤ h0 →
    IsDS ε lam σ → w ≠ 0 →
    fdegOf ((D.s.cdScale N ε : ENNReal) • Formalism.REAL.muG ε) σ w ≤
      4 * (Module.finrank ℂ (lowKSub ε lam σ) : ℝ) * (3 * p * q * lamAbs lam) ^ (p * q)

def FormalDegreeComparisonCompactCase (D : D7) : Prop :=
  ∀ (N : ℕ) (ε : Fin N → Bool) (lam : Fin N → ℝ) (ep0 : ℝ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (w : H),
    ((Finset.univ.filter (fun a => ε a = true)).card = 0 ∨ (Finset.univ.filter (fun a => ε a = false)).card = 0) →
    Formalism.QuantumDeterminants.IsHCParam lam → Real.exp (-(N : ℝ)) ≤ ep0 → ep0 < 1 / 2 →
    IsDS ε lam σ → w ≠ 0 →
    (1 - ep0) * Formalism.QuantumDeterminants.fdegHC lam ≤ fdegOf ((D.s.cdScale N ε : ENNReal) • Formalism.REAL.muG ε) σ w ∧
    fdegOf ((D.s.cdScale N ε : ENNReal) • Formalism.REAL.muG ε) σ w ≤ 4 * (Module.finrank ℂ (lowKSub ε lam σ) : ℝ)

end DS

def spectralGapLowerBound (D : D7) (ep0 : ℝ) : ℝ :=
  8192 * (min (pY D) (qY D) : ℕ) * ((pY D : ℝ) * (qY D : ℝ)) ^ 3 * Real.log (D.R.r : ℝ) / ep0 ^ 2

def SigmaDegreeTwoSidedBoundOfGap (D : D7) : Prop :=
  ∀ ep0 : ℝ, Real.exp (-(D.R.r : ℝ)) ≤ ep0 → ep0 < 1 / 2 → ∀ ρ : D.what₂.Tau,
    GapAtLeast (rowSgn D) (rowLam D ρ) (spectralGapLowerBound D ep0) →
    (1 - ep0) * dimV (rowLam D ρ) ≤ D.dsig ρ ∧
    D.dsig ρ ≤ 4 * dTau (rowSgn D) (rowLam D ρ) *
      (3 * (pY D : ℝ) * (qY D : ℝ) * lamAbs (rowLam D ρ)) ^ (pY D * qY D)

def SigmaDegreeBoundOfDiscreteSeriesBounds (D : D7) : Prop := DiscreteSeriesDegreeBoundsOfGap D → FamilyMassLastLine D → DsigEx D → SigmaDegreeTwoSidedBoundOfGap D

def DiscreteSeriesDegreeAndUpperBoundOfScale (D : D7) : Prop := Adm3 D → cdScaleTie D → DiscreteSeriesDegreeBoundsOfGap D ∧ DiscreteSeriesUpperBoundOfLargeGap D

def DstarM (D : D7) : ℝ := DstarP D (D.host.g 0) (D.host.g 1) (massI D D.R.r) D.dsig

def BaseVolumeEqualsMass (D : D7) : Prop := volY0 D = massI D D.R.r

theorem DstarD_eq_DstarM (D : D7) (h : BaseVolumeEqualsMass D) : DstarD D = DstarM D := by
  unfold DstarD DstarM; rw [h]

def piN (n g : ℕ) : ℝ := ∏ i ∈ Finset.Icc 1 n, (1 - ((g : ℝ) ^ i)⁻¹)

def LocalIndexFormulasAndBounds (D : D7) : Prop :=
  (∀ i : Fin 2,
    idxColLoc (D.host.g i) D.R.k = (D.host.g i : ℝ) ^ (D.R.k * (D.R.k + 1) / 2) * piN D.R.k (D.host.g i) ∧
    idxRowLoc (D.host.g i) D.R.k D.R.m =
      (D.host.g i : ℝ) ^ ((D.R.r ^ 2 + 3 * D.R.k + 1 + 2 * D.R.rS) / 2) * piN D.R.r (D.host.g i) ∧
    1 - 2 * ((D.host.g i : ℝ) ^ (D.R.k + 1))⁻¹ ≤ piN D.R.r (D.host.g i) / piN D.R.k (D.host.g i) ∧
    piN D.R.r (D.host.g i) / piN D.R.k (D.host.g i) ≤ 1) ∧
  ∀ n g : ℕ, 3 ≤ g → 1 / 2 ≤ piN n g ∧ piN n g ≤ 1

def IndexProductFormulasAndRatio (D : D7) : Prop :=
  idxPi D (D.host.g 0) (D.host.g 1) =
    ∏ i : Fin 2, ((D.host.g i : ℝ) ^ (D.R.k * (D.R.k + 1) / 2) * piN D.R.k (D.host.g i)) ^ D.R.f ∧
  idxSig D (D.host.g 0) (D.host.g 1) =
    ∏ i : Fin 2, ((D.host.g i : ℝ) ^ ((D.R.r ^ 2 + 3 * D.R.k + 1 + 2 * D.R.rS) / 2) *
      piN D.R.r (D.host.g i)) ^ D.R.f ∧
  idxSig D (D.host.g 0) (D.host.g 1) / idxPi D (D.host.g 0) (D.host.g 1) =
    ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) ^ (D.R.f * (D.R.m * (2 * D.R.k + D.R.m - 1) / 2)) *
      ∏ i : Fin 2, ∏ j ∈ Finset.Ioc D.R.k D.R.r, (1 - ((D.host.g i : ℝ) ^ j)⁻¹) ^ D.R.f

def RowsA (D : D7) (sc : Scale) (CY : ℝ) (Δ : ℝ) : Prop :=
  Real.log (2 * D.host.v) ≤ sc.L ∧
  (∀ i : Fin 2, Real.log (D.host.g i : ℝ) ≤ CY * sc.L) ∧
  44 ≤ D.R.m ∧ D.R.m ≤ D.R.k ∧ (D.R.m : ℝ) ≤ sc.x ∧ Real.log (2 * (D.R.k : ℝ)) ≤ sc.L ∧
  (∀ u ρ, uN D u ρ 0 - uN D u ρ (D.R.k - 1) ≤ 2 * sc.a) ∧
  (∀ u ρ, IsTop D ρ →
    (D.R.k : ℝ) * (4 * Δ) ≤ uN D u ρ 0 - vN D ρ 0 ∧ uN D u ρ (D.R.k - 1) ≤ -((D.R.k : ℝ) * (4 * Δ)))

def DataA (D : D7) (sc : Scale) (C0 CY : ℝ) (Δ : ℝ) (w : ℕ → D.what₂.Tau → ℝ) : Prop :=
  DataB D sc C0 Δ w ∧ RowsA D sc CY Δ

def LemmaFiveOneIdentity (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ u : D.what₂.Word,
    (D.R.f : ℝ) * D.R.k * logXuD D u =
      (D.R.f : ℝ) * (((D.R.m : ℝ) - 1) * D.R.k + (D.R.m : ℝ) * ((D.R.m : ℝ) - 1) / 2) *
          Real.log (D.host.v / Real.pi)
      - (D.R.f : ℝ) * (((D.R.m : ℝ) - 1) / 2) * Real.log (2 * D.host.v)
      + ∑ M ∈ Finset.Ioc D.R.k D.R.r, Real.log (Formalism.HermitianLatticesTheory.lValEta D.host.E M)
      + (D.R.f : ℝ) * ((D.R.m : ℝ) * (2 * D.R.k + D.R.m - 1) / 2) *
          Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ))
      + (D.R.f : ℝ) * ∑ i : Fin 2, ∑ j ∈ Finset.Ioc D.R.k D.R.r,
          Real.log (1 - ((D.host.g i : ℝ) ^ j)⁻¹)
      + ∑ ρ, Real.log (D.dsig ρ * facProd D.R.r / vand (uColR D u ρ))

def LogWordScaleClosedFormOfIndexFormulas (D : D7) : Prop := MassRatio₂ D → VolumeEqMass₂ D → IndexProductFormulasAndRatio D → LemmaFiveOneIdentity D

def lowS (D : D7) (sc : Scale) (w : ℕ → D.what₂.Tau → ℝ) : ℝ :=
  (∑ j ∈ range D.R.m, (1 / (D.R.f : ℝ)) * ∑ ρ, Real.log (w j ρ * D.host.v / Real.pi)) +
    (D.R.m : ℝ) * (∑ i : Fin 2, Real.log (D.host.g i : ℝ)) - 11 * sc.L

def Conclusion5Sharp (D : D7) (sc : Scale) (C0 CY : ℝ) : Prop :=
  ∀ (Δ : ℝ) (w : ℕ → D.what₂.Tau → ℝ), DataA D sc C0 CY Δ w → ∀ u : D.what₂.Word,
    lowS D sc w ≤ logXuD D u ∧ logXuD D u ≤ (15 + 3 * CY) * D.R.m * sc.L

def LogXuLowerBoundOfWeightFloor (D : D7) (sc : Scale) (C0 CY : ℝ) : Prop :=
  ∀ (Δ : ℝ) (w : ℕ → D.what₂.Tau → ℝ), DataA D sc C0 CY Δ w → ∀ wpp : ℝ, 0 < wpp →
    (∀ ρ j, j < D.R.m → wpp ≤ w j ρ) → 3 / 4 * sc.L ≤ Real.log wpp → ∀ u : D.what₂.Word,
    (D.R.m : ℝ) * Real.log wpp + (D.R.m : ℝ) * (∑ i : Fin 2, Real.log (D.host.g i : ℝ)) - 11 * sc.L
      ≤ logXuD D u ∧
    (D.R.m : ℝ) * sc.L / 2 ≤
      (D.R.m : ℝ) * Real.log wpp + (D.R.m : ℝ) * (∑ i : Fin 2, Real.log (D.host.g i : ℝ)) - 11 * sc.L

def VandermondeCountExplicit (D : D7) (sc : Scale) (C0 CY : ℝ) : Prop :=
  ∀ (Δ : ℝ) (w : ℕ → D.what₂.Tau → ℝ), DataA D sc C0 CY Δ w → ∀ Γ : ℝ, 1 ≤ Γ → ∀ u : D.what₂.Word,
    2 ≤ (D.mem u).A.T → D.R.f ≤ 2 ^ (D.R.k - 1) →
    Real.exp (logXuD D u) * Γ ^ (-(2 : ℝ) / (D.R.f * D.R.k)) ≤ ((D.mem u).A.T : ℝ) →
    ((D.mem u).A.T : ℝ) ≤
      Real.exp (logXuD D u) * Γ ^ (-(2 : ℝ) / (D.R.f * D.R.k)) * (1 + 1 / ((D.R.f : ℝ) * D.R.k)) →
    (DstarD D * Γ ^ (-(2 : ℝ)) / 2 ≤ duStarU D u * (((D.mem u).A.T : ℝ) ^ D.R.k - 1) ^ D.R.f ∧
      duStarU D u * (((D.mem u).A.T : ℝ) ^ D.R.k - 1) ^ D.R.f ≤ Real.exp 1 * (DstarD D * Γ ^ (-(2 : ℝ)))) ∧
    Real.log ((D.mem u).A.T : ℝ) ≤ logXuD D u + 1 ∧
    lowS D sc w - 2 * Real.log Γ / ((D.R.f : ℝ) * D.R.k) ≤ Real.log ((D.mem u).A.T : ℝ) ∧
    (2 * Real.log Γ / ((D.R.f : ℝ) * D.R.k) ≤ 1 →
      logXuD D u - 2 * Real.log Γ / ((D.R.f : ℝ) * D.R.k) ≤ Real.log ((D.mem u).A.T : ℝ) ∧
      logXuD D u - 1 ≤ logXuD D u - 2 * Real.log Γ / ((D.R.f : ℝ) * D.R.k) ∧
      (D.R.m : ℝ) * sc.L / 2 ≤ logXuD D u - 1)

def LemmaVStrong (D : D7) : Prop :=
  ∀ u : D.what₂.Word, 2 * Real.log (D.mem u).A.GamP / ((D.R.f : ℝ) * D.R.k) ≤ 1

def VandermondeVariationExplicitBound (D : D7) (sc : Scale) (C0 CY : ℝ) : Prop :=
  ∀ (Δ : ℝ) (w : ℕ → D.what₂.Tau → ℝ), DataA D sc C0 CY Δ w →
    (∀ (u u' : D.what₂.Word) (ρ : D.what₂.Tau),
      |Real.log (vand (uColR D u ρ)) - Real.log (vand (uColR D u' ρ))| ≤
        D.R.k * (1 + Real.log D.R.k) + 2) ∧
    ∀ u u' : D.what₂.Word, |logXuD D u - logXuD D u'| ≤ 1 + Real.log D.R.k + 2 / (D.R.k : ℝ)

def VandermondeCountBound (D : D7) (sc : Scale) (C0 CY : ℝ) : Prop :=
  Conclusion5Sharp D sc C0 CY ∧ LogXuLowerBoundOfWeightFloor D sc C0 CY ∧ VandermondeCountExplicit D sc C0 CY ∧ VandermondeVariationExplicitBound D sc C0 CY

def VandermondeCountExplicitBound (D : D7) (sc : Scale) (C0 CY : ℝ) : Prop :=
  VolumeMass D → SigmaDegreeTwoSidedBoundOfGap D → LocalIndexFormulasAndBounds D → Conclusion4b D → PartFourSectionBData D sc 8192 C0 → VandermondeCountBound D sc C0 CY

section Fam

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

def FamilyMassExplicit : Prop := ∀ x (i : Fm.Ix x), projection_sandwich_lattice (Fm.D x i) ∧ projection_lemma_base_level (Fm.D x i)
def FamilyTheoremThreeExplicit : Prop := ∀ x (i : Fm.Ix x), DiscreteSeriesDegreeBoundsOfGap (Fm.D x i) ∧ DiscreteSeriesUpperBoundOfLargeGap (Fm.D x i)
def FamilySigmaDegreeTwoSidedBound : Prop := ∀ x (i : Fm.Ix x), SigmaDegreeTwoSidedBoundOfGap (Fm.D x i)
def FamilyVolumeMassAndIndexFormulas : Prop := ∀ x (i : Fm.Ix x), BaseVolumeEqualsMass (Fm.D x i) ∧ LocalIndexFormulasAndBounds (Fm.D x i) ∧ IndexProductFormulasAndRatio (Fm.D x i)
def FamilyLemmaFiveOne : Prop := ∀ x (i : Fm.Ix x), LemmaFiveOneIdentity (Fm.D x i)

def FamilyVandermondeCountExplicit : Prop :=
  ∀ C0 CY : ℝ, ∃ x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x, VandermondeCountBound (Fm.D x i) (Fm.L x i).sc C0 CY

def FamilyLogGammaBound : Prop := ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, LemmaVStrong (Fm.D x i)

def FamilyMassExplicitOfVolumeAgreement : Prop := FamilyPartOne Fm → VolTieF Fm → FamilyMassExplicit Fm
def FamilyTheoremThreeExplicitStatement : Prop := FamilyTheoremThreeAdmitted Fm → FamilyTheoremThreeExplicit Fm
def FamilySigmaStatement : Prop := FamilyTheoremThreeExplicit Fm → FamilyTheoremThreeAdmitted Fm → DsigExF Fm → FamilySigmaDegreeTwoSidedBound Fm
def FamilyIndexFormulasOfMassVolumeBounds : Prop := FamilyMassVolumeBounds Fm → FamilyVolumeMassAndIndexFormulas Fm
def FamilyIdentityOfMassVolumeAndIndices : Prop := FamilyMassVolumeBounds Fm → FamilyVolumeMassAndIndexFormulas Fm → FamilyLemmaFiveOne Fm
def FamilyVandermondeCountBound : Prop := FamilyMassVolumeBounds Fm → FamilySigmaDegreeTwoSidedBound Fm → FamilyVolumeMassAndIndexFormulas Fm → FamilyPartFourSectionB Fm 8192 → FamilyVandermondeCountExplicit Fm

end Fam

theorem scale_one_le_L (sc : Scale) : 1 ≤ sc.L := Real.one_le_rpow sc.one_lt_alt.le sc.eps_pos.le

theorem lowB_le_lowS (D : D7) (sc : Scale) (C : ℝ) (w : ℕ → D.what₂.Tau → ℝ) (hC : 11 ≤ C) :
    lowB D sc C w ≤ lowS D sc w := by
  have hL := scale_one_le_L sc
  have h1 : 0 ≤ (D.R.m : ℝ) ^ 2 * sc.L / D.R.k := by positivity
  have h2 : 11 * sc.L ≤ C * (sc.L + (D.R.m : ℝ) ^ 2 * sc.L / D.R.k) := by nlinarith
  unfold lowB lowS
  linarith

theorem part_five_bound_of_explicit (D : D7) (sc : Scale) (C0 CY C : ℝ) (h : Conclusion5Sharp D sc C0 CY)
    (hR : ∀ Δ w, DataB D sc C0 Δ w → RowsA D sc CY Δ) (hC : 11 ≤ C) (hC' : 15 + 3 * CY ≤ C) :
    Conclusion5 D sc C0 C := by
  intro Δ w hB u
  obtain ⟨h1, h2⟩ := h Δ w ⟨hB, hR Δ w hB⟩ u
  have hL := scale_one_le_L sc
  refine ⟨le_trans (lowB_le_lowS D sc C w hC) h1, le_trans h2 ?_⟩
  have hm : (0 : ℝ) ≤ D.R.m := Nat.cast_nonneg _
  have : (15 + 3 * CY) * (D.R.m * sc.L) ≤ C * (D.R.m * sc.L) :=
    mul_le_mul_of_nonneg_right hC' (by positivity)
  nlinarith

theorem corollary_five_six_of_explicit (D : D7) (sc : Scale) (C0 CY : ℝ) (h : Conclusion5Sharp D sc C0 CY) : LogXuLowerBoundOfWeightFloor D sc C0 CY := by
  intro Δ w hA wpp hw0 hw hlog u
  have hL := scale_one_le_L sc
  have hA' := hA
  obtain ⟨hB, -, -, h44, -⟩ := hA'
  have hpi : Real.pi ≤ D.host.v := hB.1
  have hf : (0 : ℝ) < D.R.f := by
    have h2 : 2 ≤ D.R.f := le_trans D.R.two_le_m D.R.m_le_f
    exact_mod_cast lt_of_lt_of_le two_pos h2
  have hm : (44 : ℝ) ≤ D.R.m := by exact_mod_cast h44
  refine ⟨le_trans ?_ (h Δ w hA u).1, ?_⟩
  · unfold lowS
    have key : (D.R.m : ℝ) * Real.log wpp ≤
        ∑ j ∈ range D.R.m, (1 / (D.R.f : ℝ)) * ∑ ρ, Real.log (w j ρ * D.host.v / Real.pi) := by
      have e : ∀ j ∈ range D.R.m, Real.log wpp ≤
          (1 / (D.R.f : ℝ)) * ∑ ρ, Real.log (w j ρ * D.host.v / Real.pi) := by
        intro j hj
        have hj' : j < D.R.m := Finset.mem_range.1 hj
        have e1 : ∀ ρ ∈ (Finset.univ : Finset D.what₂.Tau), Real.log wpp ≤ Real.log (w j ρ * D.host.v / Real.pi) := by
          intro ρ _
          apply Real.log_le_log hw0
          rw [le_div_iff₀ Real.pi_pos]
          have := hw ρ j hj'
          nlinarith [Real.pi_pos]
        have e2 := Finset.card_nsmul_le_sum _ _ _ e1
        rw [Finset.card_univ, D.what₂.card_Tau, nsmul_eq_mul] at e2
        rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hf]
        linarith
      have e3 := Finset.card_nsmul_le_sum _ _ _ e
      rw [Finset.card_range, nsmul_eq_mul] at e3
      exact e3
    linarith
  · have hg : 0 ≤ ∑ i : Fin 2, Real.log (D.host.g i : ℝ) :=
      Finset.sum_nonneg fun i _ => Real.log_nonneg (by exact_mod_cast (D.host.g_prime i).one_lt.le)
    nlinarith

theorem variation_bound_of_explicit (D : D7) (sc : Scale) (C0 CY C : ℝ) (h : VandermondeVariationExplicitBound D sc C0 CY)
    (hR : ∀ Δ w, DataB D sc C0 Δ w → RowsA D sc CY Δ) (hC : 3 ≤ C) : VandermondeVariationBound D sc C0 C := by
  intro Δ w hB
  obtain ⟨h1, h2⟩ := h Δ w ⟨hB, hR Δ w hB⟩
  have hk : (5 : ℝ) ≤ D.R.k := by exact_mod_cast D.R.k_ge
  have hl : 1 ≤ Real.log D.R.k := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hkl : 5 ≤ (D.R.k : ℝ) * Real.log D.R.k := by nlinarith
  refine ⟨fun u u' ρ => le_trans (h1 u u' ρ) ?_, fun u u' => le_trans (h2 u u') ?_⟩
  · have : 3 * ((D.R.k : ℝ) * Real.log D.R.k) ≤ C * ((D.R.k : ℝ) * Real.log D.R.k) :=
      mul_le_mul_of_nonneg_right hC (by linarith)
    nlinarith
  · have h3 : 2 / (D.R.k : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    have : 3 * Real.log D.R.k ≤ C * Real.log D.R.k := mul_le_mul_of_nonneg_right hC (by linarith)
    linarith

theorem part_five_count_of_explicit (D : D7) (sc : Scale) (C0 CY C : ℝ) (h5 : Conclusion5Sharp D sc C0 CY) (h : VandermondeCountExplicit D sc C0 CY)
    (hR : ∀ Δ w, DataB D sc C0 Δ w → RowsA D sc CY Δ) (hC : 11 ≤ C) (hC' : 16 + 3 * CY ≤ C) :
    TorusPairsWithVariant D sc C0 C := by
  intro Δ w hB Γ hΓ u hT1 hT2
  have hA : DataA D sc C0 CY Δ w := ⟨hB, hR Δ w hB⟩
  have hL := scale_one_le_L sc
  have hfk : D.R.f ≤ 2 ^ (D.R.k - 1) := by
    have h1 : D.R.f ≤ D.R.k := D.R.f_le_k
    have h2 : D.R.k - 1 < 2 ^ (D.R.k - 1) := Nat.lt_two_pow_self
    omega
  obtain ⟨⟨a1, a2⟩, b, c, -⟩ := h Δ w hA Γ hΓ u (D.mem u).A.T_prime.two_le hfk hT1 hT2
  have hm : (44 : ℝ) ≤ D.R.m := by exact_mod_cast hA.2.2.2.1
  refine ⟨?_, ?_, ?_⟩
  · set D' := DstarD D * Γ ^ (-(2 : ℝ)) with hD'
    set dM := duStarU D u * (((D.mem u).A.T : ℝ) ^ D.R.k - 1) ^ D.R.f with hdM
    have he : (1 : ℝ) < Real.exp 1 := by have := Real.add_one_lt_exp (one_ne_zero); linarith
    have hD0 : 0 ≤ D' := by nlinarith
    rcases hD0.eq_or_lt with h0 | h0
    · rw [← h0, div_zero, Real.log_zero, abs_zero]; linarith
    · have r1 : 1 / 2 ≤ dM / D' := by rw [le_div_iff₀ h0]; linarith
      have r2 : dM / D' ≤ Real.exp 1 := by rw [div_le_iff₀ h0]; exact a2
      have l1 : Real.log (1 / 2) ≤ Real.log (dM / D') := Real.log_le_log (by norm_num) r1
      have l2 : Real.log (dM / D') ≤ 1 := by
        have := Real.log_le_log (by linarith) r2
        rwa [Real.log_exp] at this
      have l3 : -1 ≤ Real.log (1 / 2 : ℝ) := by
        rw [one_div, Real.log_inv]
        have := Real.log_two_lt_d9
        linarith
      rw [abs_le]
      constructor <;> linarith
  · have h2 := (h5 Δ w hA u).2
    have hmL : 1 ≤ (D.R.m : ℝ) * sc.L := by nlinarith
    have : (16 + 3 * CY) * (D.R.m * sc.L) ≤ C * (D.R.m * sc.L) :=
      mul_le_mul_of_nonneg_right hC' (by linarith)
    nlinarith
  · have := lowB_le_lowS D sc C w hC
    linarith

theorem part_five_all_of_explicit (D : D7) (sc : Scale) (C0 CY C : ℝ) (h : VandermondeCountBound D sc C0 CY)
    (hR : ∀ Δ w, DataB D sc C0 Δ w → RowsA D sc CY Δ) (hC : 11 ≤ C) (hC' : 16 + 3 * CY ≤ C) :
    Conclusion5₂ D sc C0 C :=
  ⟨part_five_bound_of_explicit D sc C0 CY C h.1 hR hC (by linarith), part_five_count_of_explicit D sc C0 CY C h.1 h.2.2.1 hR hC hC',
    variation_bound_of_explicit D sc C0 CY C h.2.2.2 hR (by linarith)⟩

def RowsAF {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop :=
  ∀ C0 : ℝ, ∃ x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ (i : Fm.Ix x) (Δ : ℝ) (w : ℕ → (Fm.D x i).what₂.Tau → ℝ),
    DataB (Fm.D x i) (Fm.L x i).sc C0 Δ w → RowsA (Fm.D x i) (Fm.L x i).sc C0 Δ

theorem part_five_family_of_explicit {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (h : FamilyVandermondeCountExplicit Fm) (hR : RowsAF Fm) : PartFiveFamilyBounds Fm := by
  intro C0
  obtain ⟨x0, hx0⟩ := h C0 C0
  obtain ⟨x1, hx1⟩ := hR C0
  refine ⟨max 11 (16 + 3 * C0), max x0 x1, fun x hx hxx i => ?_⟩
  exact part_five_all_of_explicit _ _ C0 C0 _ (hx0 x (le_trans (le_max_left _ _) hx) hxx i)
    (fun Δ w hB => hx1 x (le_trans (le_max_right _ _) hx) hxx i Δ w hB) (le_max_left _ _) (le_max_right _ _)

section DS

open Formalism.MainNotions.S MeasureTheory Matrix
open scoped InnerProductSpace ComplexOrder

theorem lamAbs_nonneg {N : ℕ} (lam : Fin N → ℝ) : 0 ≤ lamAbs lam :=
  Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => abs_nonneg _

theorem theorem_three_of_explicit_and_compact (D : D7) (C3 : ℝ) (hC : 8192 ≤ C3) (hS : DiscreteSeriesDegreeBoundsOfGap D) (hZ : FormalDegreeComparisonCompactCase D) : RepresentationDimensionGeneral D C3 := by
  intro N ε lam ep0 h0 H _ _ σ w p q hHC hgap he1 he2 hh hDS hw
  by_cases hpq : (Finset.univ.filter (fun a => ε a = true)).card = 0 ∨
      (Finset.univ.filter (fun a => ε a = false)).card = 0
  · obtain ⟨z1, z2⟩ := hZ N ε lam ep0 H σ w hpq hHC he1 he2 hDS hw
    refine ⟨z1, le_trans z2 ?_⟩
    have e : p * q = 0 := by
      rcases hpq with h | h
      · have : p = 0 := by show ((Finset.univ.filter (fun a => ε a = true)).card : ℝ) = 0; rw [h]; simp
        rw [this, zero_mul]
      · have : q = 0 := by show ((Finset.univ.filter (fun a => ε a = false)).card : ℝ) = 0; rw [h]; simp
        rw [this, mul_zero]
    rw [e, Real.rpow_zero, mul_one]
  · rw [not_or] at hpq
    have hp : 1 ≤ p := by
      show (1 : ℝ) ≤ ((Finset.univ.filter (fun a => ε a = true)).card : ℝ)
      exact_mod_cast Nat.one_le_iff_ne_zero.2 hpq.1
    have hq : 1 ≤ q := by
      show (1 : ℝ) ≤ ((Finset.univ.filter (fun a => ε a = false)).card : ℝ)
      exact_mod_cast Nat.one_le_iff_ne_zero.2 hpq.2
    have hN : (1 : ℝ) ≤ N := by
      have h1 : (Finset.univ.filter (fun a => ε a = true)).card ≤ N := by
        simpa using Finset.card_filter_le (Finset.univ : Finset (Fin N)) (fun a => ε a = true)
      have h2 : p ≤ N := by
        show ((Finset.univ.filter (fun a => ε a = true)).card : ℝ) ≤ N
        exact_mod_cast h1
      linarith
    have he : 0 < ep0 := lt_of_lt_of_le (Real.exp_pos _) he1
    have hm : 0 ≤ min p q := le_min (by linarith) (by linarith)
    have hl : 0 ≤ Real.log N := Real.log_nonneg hN
    have hyp : 8192 * min p q * (p * q) ^ 3 * Real.log N / ep0 ^ 2 ≤ h0 := by
      refine le_trans ?_ hh
      apply div_le_div_of_nonneg_right _ (by positivity)
      have h1 : 8192 * min p q * (p * q) ^ 3 ≤ C3 * min p q * (p * q) ^ 3 * N := by
        have : 8192 * (min p q * (p * q) ^ 3) ≤ C3 * N * (min p q * (p * q) ^ 3) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          nlinarith
        nlinarith
      exact mul_le_mul_of_nonneg_right h1 hl
    obtain ⟨s1, s2⟩ := hS N ε lam ep0 h0 H σ w hp hq hHC hgap he1 he2 hyp hDS hw
    refine ⟨s1, le_trans s2 ?_⟩
    have hla := lamAbs_nonneg lam
    have hb : 3 * p * q * lamAbs lam ≤ C3 * p * q * N * lamAbs lam := by
      have h3 : 3 ≤ C3 * N := by nlinarith
      have : 3 * (p * q * lamAbs lam) ≤ C3 * N * (p * q * lamAbs lam) :=
        mul_le_mul_of_nonneg_right h3 (by positivity)
      nlinarith
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) hb (by positivity)) (by positivity)

end DS

end Formalism.MainNotions.StandardLattice
