import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.Objects
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GroundTheory.Heights₂.Heights.LowerBoundFree Filter Topology

namespace HtBoundary

section Objects

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
  [∀ τ, Module Ω (E τ)] {Em : Type} [Field Em] [NumberField Em] [IsCMField Em]

def cuspWt (D : FullerData II Ψ K ι Ω E Em) (z : (Σ k, ι k) → ℂ) : ℝ :=
  phMu D.mu z + D.cuspU z / 2

variable (Em) in

def logDerivL : ℝ :=
  limUnder (𝓝[>] (1 : ℝ)) fun σ : ℝ =>
    (logDeriv (dedekindZeta Em) σ - logDeriv (dedekindZeta (maximalRealSubfield Em)) σ).re

variable (Em) in

def La (B : ℕ) : ℝ := Real.log (B * rootDiscr Em) + |logDerivL Em|

def Holds (Ch : ℝ) (D : FullerData II Ψ K ι Ω E Em) {M : XModel D.toComponentData}
    (S : BoundedRegularisationSetting M D.Xo D.mu.aMu (cuspWt D)) : Prop :=
  ∀ B p q : ℕ, 4 * D.f * D.N ^ 2 ≤ B → 1 ≤ p → p ≤ q → ∀ t' : ℝ, 0 < t' → t' ≤ 1 →
    ∀ W : Ideal (MRing ι), IsArithVar W 1 → mCoordIdeal D.y ≤ W → ¬ OffBoundary D.Bd W →
      -(Ch * D.f * D.j' * La Em B) - (p : ℝ) / q * D.KA ≤ htMUc D.mu S B p q t' W

end Objects

def Statement : Prop :=
  ∃ Ch : ℝ, ∀ (II : IntersectionSystem), IsIntersectionSystem II →
    ∀ (Ψ : Type) [Fintype Ψ] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
      (Em : Type) [Field Em] [NumberField Em] [IsCMField Em]
      (D : FullerData II Ψ K ι Ω E Em) (M : XModel D.toComponentData)
      (S : BoundedRegularisationSetting M D.Xo D.mu.aMu (cuspWt D)), S.IsTied → Holds Ch D S

namespace Flat

open GroundTheory.Heights₂.Heights.LowerBoundFree.Line GroundTheory.Heights₂.Heights.Regular.ProjectiveLine

variable (II : IntersectionSystem)
  (hII : ∀ W : Ideal (MRing (PBlk 2)), IsArithVar W 1 → 0 ≤ II Unit (PBlk 2) W 1 ![fsLine 2])

theorem lineF_eq : lineF = (lineDataHodge II hII).F () := by
  show Submodule.span Ω {Pi.single 0 1} = Submodule.span Ω ((Pi.basisFun Ω (Fin 2)) '' {i | (i : ℕ) < 1})
  congr 1
  ext v
  simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro rfl
    exact ⟨0, by simp, by simp⟩
  · rintro ⟨i, hi, rfl⟩
    rw [show i = 0 from Fin.ext (Nat.lt_one_iff.mp hi)]
    simp

def flatFuller : FullerData II Unit Unit (PBlk 2) Ω (fun _ => Fin 2 → Ω) Gauss.Em where
  toComponentDataHodge := lineDataHodge II hII
  herm := Gauss.gaussDatum
  per _ _ := 1
  per_witt _ _ _ := Gauss.gauss_signature
  per_torus _ _ _ := rfl
  nStrata := 0
  stratum := Fin.elim0
  stratum_sub s := s.elim0
  stratum_cover _ h := absurd h (Set.notMem_empty _)
  stratum_torus s := s.elim0
  torLat := Fin.elim0
  torLat_le s := s.elim0
  torLat_ne s := s.elim0
  torLat_iso s := s.elim0
  torLat_sat s := s.elim0
  nz_near s := s.elim0
  mu := lineHodge II hII
  mu_F _ := lineF_eq II hII
  htLat _ _ := (lineData II hII).W ()
  ht_away _ h := absurd h (Finset.notMem_empty _)

theorem flatFuller_cuspU (z : (Σ _ : Unit, Fin 2) → ℂ) : (flatFuller II hII).cuspU z = 0 := by
  simp [FullerData.cuspU, flatFuller, Real.iSup_of_isEmpty]

def flatBReg : BoundedRegularisationSetting lineModel (flatFuller II hII).Xo (flatFuller II hII).mu.aMu
    (cuspWt (flatFuller II hII)) where
  ref := refOne
  ref_deg := rfl
  ref_smooth := refOne_smooth
  B := cpBounded
  th_ref x y _ := th_ref_line x y
  ph_eq z hz := by
    have h0 : phMu (flatFuller II hII).mu z = 0 := phMu_line (II := II) (hII := hII) (mem_mcPts_line.1 hz.2)
    show (0 : ℝ) = _
    rw [cuspWt, flatFuller_cuspU, h0, refOne_h, Real.log_one]
    ring
  ρ := (ReciprocityTheory.AnForm.A.mollifierInhabit_thm 1).some
  η := cpEta
  Cη := cpCutoff.choose
  cutoff := cpCutoff.choose_spec
  e1 t := t
  e1_ge _ _ := le_rfl

end Flat

end HtBoundary

end GroundTheory.Heights₂.Heights.NineStatements
