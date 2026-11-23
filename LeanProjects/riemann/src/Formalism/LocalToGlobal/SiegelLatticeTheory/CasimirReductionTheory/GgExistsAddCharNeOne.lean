import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.DiscreteSeriesWeylDimension
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCPX
import Formalism.SharpRestriction.CuspSpanNormBounds.TheoremBConstants
import Formalism.SharpRestriction.CuspSpanNormBounds.LowestKTypeMultiplicity
import Formalism.SharpRestriction.CuspSpanNormBounds.ExpansionFromLemmaB
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.DegreeL2RangeHypothesis
import Formalism.PeriodIntegrals.KFinSmooth
import Formalism.HermitianCurvature.StatementB
import Formalism.HermitianLattices.StatementMass
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.PeriodIntegrals.UpqRep
import Formalism.PeriodIntegrals.PhMeasCore
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.FormalDegreeBessel.StatementDS
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.SphericalFunctionIntegrableOfLocal
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleySignature
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MassLand
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GGMirabolicBase
import Formalism.SharpRestriction.CuspSpanNormBounds.DiagonalEntryIdentity

noncomputable section

namespace Formalism.L2.SG.LitS

section Reexports

abbrev DSExists : Prop := Formalism.MainNotions.DiscreteSeriesWeylDimension.DiscreteSeriesExists

abbrev DSUnique : Prop := Formalism.MainNotions.BridgeLemma₂.deg_DSUniq

abbrev LowKMultOne : Prop := Formalism.MainNotions.DiscreteSeriesWeylDimension.LowKMultOne

abbrev HCMult : Prop := Formalism.MainNotions.BridgeCPX.HCMult

abbrev KFinSmooth : Prop := Formalism.MainNotions.DiscreteSeriesInnerProducts.KFinSmooth

abbrev LitFormalDegree : Prop := Formalism.MainNotions.TheoremBConstants.LitFormalDegree

abbrev HCFdeg : Prop := Formalism.MainNotions.LowestKTypeMultiplicity.HCFdeg

abbrev XiExists : Prop := Formalism.FourierDecayAlt.B.XiExists

abbrev SiegelMassRatio : Prop := Formalism.HermitianLatticesTheory.SiegelMassRatio

theorem kFinSmooth_pi (h : KFinSmooth) : PI.KFinSmooth := by
  intro k r ε lam H _ _ _ σ _ hσ v hv
  exact h k r ε lam H σ hσ v hv

abbrev HCMultDS : Prop := Formalism.MainNotions.BridgeCPX.HCMultDS

abbrev HCAdmDS : Prop := Formalism.MainNotions.BridgeCPX.HCAdmDS

theorem hcMultDS_of_hcMult (h : HCMult) : HCMultDS := Formalism.MainNotions.BridgeCPX.HCMultDS_of_HCMult h

theorem hcAdmDS_of_hcMultDS (h : HCMultDS) : HCAdmDS := Formalism.MainNotions.BridgeCPX.HCAdmDS_of_mult h

theorem kFinSmooth_of_hcMultDS (h : HCMultDS) : KFinSmooth :=
  fun _ _ _ _ _ _ _ _ _ hσ _ hv => Formalism.MainNotions.BridgeCPX.kfin_smoothVec (hcAdmDS_of_hcMultDS h) hσ hv

theorem kFinSmooth_of_hcMult (h : HCMult) : KFinSmooth := kFinSmooth_of_hcMultDS (hcMultDS_of_hcMult h)

end Reexports

section RealPlaces

open scoped InnerProductSpace Matrix

def thetaJ {n : ℕ} (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  -(Formalism.REAL.Jm ε * Yᴴ * Formalism.REAL.Jm ε)

def dsigC {n : ℕ} (ε : Fin n → Bool) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (Y : Matrix (Fin n) (Fin n) ℂ) (v : H) : H :=
  PI.PhMeasCore.dsig σ ((1 / 2 : ℂ) • (Y + thetaJ ε Y)) v +
    Complex.I • PI.PhMeasCore.dsig σ ((1 / (2 * Complex.I)) • (Y - thetaJ ε Y)) v

def dsigCW {n : ℕ} (ε : Fin n → Bool) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : List (Matrix (Fin n) (Fin n) ℂ) → H → H
  | [], v => v
  | Y :: w, v => dsigC ε σ Y (dsigCW ε σ w v)

def unitM {n : ℕ} (ab : Fin n × Fin n) : Matrix (Fin n) (Fin n) ℂ := Matrix.single ab.1 ab.2 1

def Egl (n : ℕ) : Fin n → Fin n → FreeAlgebra ℂ (Fin n × Fin n) := fun a b => FreeAlgebra.ι ℂ (a, b)

def actU {n : ℕ} (ε : Fin n → Bool) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (p : FreeAlgebra ℂ (Fin n × Fin n)) (v : H) : H :=
  Finsupp.sum (FreeAlgebra.equivMonoidAlgebraFreeMonoid p).coeff
    fun (w : FreeMonoid (Fin n × Fin n)) (c : ℂ) => c • dsigCW ε σ (w.toList.map unitM) v

theorem isDS_iff_pi {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin n → Bool)
    (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) :
    Formalism.MainNotions.S.IsDS ε lam σ ↔ PI.UpqRep.IsDS ε lam σ := Iff.rfl

def InfCharDS : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.QuantumDeterminants.IsHCParam lam → Formalism.MainNotions.S.IsDS ε lam σ →
    ∀ v ∈ PI.PhMeasCore.smoothVecs (Formalism.REAL.Jm ε) σ, ∀ Y : ℂ,
      actU ε σ (Formalism.REAL.qdet (Egl n) (Y + ((n : ℂ) - 1) / 2)) v =
        Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y • v

def KTypesCone : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.QuantumDeterminants.IsHCParam lam → Formalism.MainNotions.S.IsDS ε lam σ →
    ∀ (μ : Fin n → ℝ) (S : Submodule ℂ H), Formalism.MainNotions.S.IsKTypeOf ε σ μ S →
      ∃ c : Fin n → Fin n → ℕ, (∀ a b, c a b ≠ 0 → a < b ∧ ε a ≠ ε b) ∧
        μ = Formalism.QuantumDeterminants.lowK ε lam + ∑ a, ∑ b, (c a b : ℝ) • Formalism.REAL.root a b

end RealPlaces

section BesselPart

open Matrix
open scoped InnerProductSpace ContDiff

section BesselMultOne

open Formalism.MainNotions.S

theorem psi_eq_psiGen (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) :
    Formalism.QuantumDeterminants.psi k r z c = psiGen k r z (fun _ => c) := by
  funext g
  simp only [Formalism.QuantumDeterminants.psi, psiGen, Formalism.QuantumDeterminants.ell, ellA, Finset.mul_sum]

def BesselMultOne : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H))
    (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ) (Wp : Type) [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)),
    Formalism.QuantumDeterminants.IsHCParam lam → IsDSHpk k r ε lam σ → Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z →
    (∀ a, c a ≠ 0) → IsHCTypeW k r z u π →
    ∀ B₁ B₂ : H → Wp, IsBesselMapSm (k := k) (r := r) z (psiGen k r z c) σ π B₁ →
      IsBesselMapSm (k := k) (r := r) z (psiGen k r z c) σ π B₂ →
      ∃ a b : ℂ, (a ≠ 0 ∨ b ≠ 0) ∧ ∀ v ∈ smoothVecs (k := k) (r := r) σ, a • B₁ v + b • B₂ v = 0

theorem stJSZ_of_besselMultOne (h : BesselMultOne) : Formalism.MainNotions.S.UnitaryLevelOperators.stJSZ := by
  intro k r L B₁ B₂ hc hB₁ hB₂
  rw [psi_eq_psiGen] at hB₁ hB₂
  exact h k r L.ε L.lam L.Hs L.σ L.z (fun _ => L.c) L.u L.Wp L.π L.hlam L.hσ L.hz.1 L.hz.2 (fun _ => hc) L.hπ
    B₁ B₂ hB₁ hB₂

end BesselMultOne

end BesselPart

section GlobalHyps

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct ENNReal Matrix

def GFf (I : Formalism.MainNotions.S.AutInst) : Set I.Gf :=
  {x | ∃ γ : GL (Fin I.n) I.E, γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J ∧
    I.fmat x = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F))}

def BorelFinVol : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (μf : Measure I.Gf) [SigmaFinite μf], μf.IsHaarMeasure →
    ∀ fund : Set I.GA, I.IsFundDom (I.muA μf) fund → I.muA μf fund ≠ ⊤

def BorelClassFinite : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (U : Subgroup I.Gf), IsOpen (U : Set I.Gf) →
    ∃ S : Finset I.Gf, ∀ x : I.Gf, ∃ γ ∈ GFf I, ∃ s ∈ S, ∃ u ∈ U, x = γ * s * u

def BorelFinite : Prop := BorelFinVol ∧ BorelClassFinite

theorem finVol_of_borel (h : BorelFinVol) (X : Formalism.MainNotions.BridgeLemma.CData) (hH : X.μf.IsHaarMeasure)
    (hF : X.I.IsFundDom (X.I.muA X.μf) X.fund) : X.FinVol :=
  h X.I X.μf hH X.fund hF

def WeilQuotient : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G), IsClosed (H : Set G) →
    ∀ (μ : Measure G) (ν : Measure H), μ.IsHaarMeasure → μ.IsMulRightInvariant → ν.IsHaarMeasure →
      ν.IsMulRightInvariant →
      ∃ ρ : Measure (G ⧸ H), ρ ≠ 0 ∧ (∀ K : Set (G ⧸ H), IsCompact K → ρ K < ⊤) ∧
        (∀ (g : G) (s : Set (G ⧸ H)), MeasurableSet s → ρ ((fun y => g • y) ⁻¹' s) = ρ s) ∧
        (∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ g, f g ∂μ = ∫⁻ y, (∫⁻ h, f (y.out * h) ∂ν) ∂ρ) ∧
        ∀ ρ' : Measure (G ⧸ H), (∀ K : Set (G ⧸ H), IsCompact K → ρ' K < ⊤) →
          (∀ (g : G) (s : Set (G ⧸ H)), MeasurableSet s → ρ' ((fun y => g • y) ⁻¹' s) = ρ' s) →
          ∃ c : ℝ≥0∞, ρ' = c • ρ

section Herm

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def IsomOver (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ}
    (J J' : Matrix (Fin M) (Fin M) E) : Prop :=
  ∃ g : GL (Fin M) (R ⊗[F] E),
    Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ) (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR R J * (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR R J'

end Herm

def UnramAll {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) : Prop :=
  ∀ P : Ideal (𝓞 E), P.IsMaximal →
    ∃ θ t : 𝓞 E, algebraMap (𝓞 E) E t = σ (algebraMap (𝓞 E) E θ) ∧ θ - t ∉ P

def Landherr : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ → UnramAll σ →
    ∀ (M : ℕ) (J J' : Matrix (Fin M) (Fin M) E),
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsHermND σ J → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsHermND σ J' →
      (∀ v : HeightOneSpectrum (𝓞 F), IsomOver (v.adicCompletion F) σ J J') →
      (∀ τ : E →+* ℂ, ∃ P : Matrix (Fin M) (Fin M) ℂ, IsUnit P ∧ Pᴴ * J.map τ * P = J'.map τ) →
      ∃ γ : GL (Fin M) E, Formalism.UG.cT (σ : E →+* E) (γ : Matrix (Fin M) (Fin M) E) * J *
        (γ : Matrix (Fin M) (Fin M) E) = J'

def LandherrLocal : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ → ∀ (v : HeightOneSpectrum (𝓞 F)) (M : ℕ)
    (J J' : Matrix (Fin M) (Fin M) (v.adicCompletion F ⊗[F] E)),
      Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (v.adicCompletion F) σ) J = J →
      Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (v.adicCompletion F) σ) J' = J' → IsUnit J.det → IsUnit J'.det →
      (∃ c : v.adicCompletion F ⊗[F] E, IsUnit c ∧
        J'.det = c * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (v.adicCompletion F) σ c * J.det) →
      ∃ g : GL (Fin M) (v.adicCompletion F ⊗[F] E),
        Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (v.adicCompletion F) σ) (g : Matrix (Fin M) (Fin M) _) * J *
          (g : Matrix (Fin M) (Fin M) _) = J'

variable [Fact Formalism.HermitianLattices.Ext.L3.LandherrUnram] in

theorem landherrDefiniteUnram : Formalism.HermitianLattices.Ext.L3.LandherrUnram := Formalism.HermitianLattices.Ext.L3.landherrUnram

end GlobalHyps

section FiniteGroups

open Finset Matrix MeasureTheory

abbrev GelfandGraev : Prop := Formalism.L2.SG.GGMirabolic.GelfandGraevMultOne

theorem gg_exists_addChar_ne_one (F : Type) [Field F] [Fintype F] : ∃ ψ : AddChar F ℂ, ψ ≠ 1 := by
  refine ⟨AddChar.FiniteField.primitiveChar_to_Complex F, fun h => ?_⟩
  have hp := AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive F
  have h1 := hp (one_ne_zero : (1 : F) ≠ 0)
  rw [AddChar.mulShift_one] at h1
  exact h1 h

theorem gg_needs_irreducible :
    ¬ ∀ (F : Type) [Field F] [Fintype F] (k : ℕ) (ψ₀ : AddChar F ℂ), ψ₀ ≠ 1 →
      ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
        (π : Representation ℂ (GL (Fin k) F) V),
        ∀ ℓ₁ ℓ₂ : Module.Dual ℂ V, Formalism.L2.SG.GGMirabolic.IsWhit ψ₀ π ℓ₁ → Formalism.L2.SG.GGMirabolic.IsWhit ψ₀ π ℓ₂ → ℓ₁ ≠ 0 →
          ∃ c : ℂ, ℓ₂ = c • ℓ₁ := by
  intro h
  obtain ⟨ψ, hψ⟩ := gg_exists_addChar_ne_one (ZMod 2)
  have hW : ∀ ℓ : Module.Dual ℂ (Fin 2 → ℂ),
      Formalism.L2.SG.GGMirabolic.IsWhit ψ (Representation.trivial ℂ (GL (Fin 0) (ZMod 2)) (Fin 2 → ℂ)) ℓ := by
    intro ℓ u _ v
    simp [Formalism.L2.SG.GGMirabolic.psiU, Formalism.L2.SG.GGMirabolic.superdiag]
  obtain ⟨c, hc⟩ := h (ZMod 2) 0 ψ hψ (Fin 2 → ℂ) (Representation.trivial ℂ _ _)
    (LinearMap.proj 0) (LinearMap.proj 1) (hW _) (hW _) (by
      intro h0
      have := LinearMap.congr_fun h0 (Pi.single 0 1)
      simp at this)
  have := LinearMap.congr_fun hc (Pi.single 1 1)
  simp at this

theorem gg_trivial_isIrreducible (G : Type) [Group G] : (Representation.trivial ℂ G ℂ).IsIrreducible := by
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := fun W => ?_ }
  · have h1 : (1 : ℂ) ∈ (⊤ : Subrepresentation (Representation.trivial ℂ G ℂ)) := trivial
    rw [← h] at h1
    exact one_ne_zero ((Submodule.mem_bot ℂ).1 h1)
  · rcases eq_bot_or_eq_top W.toSubmodule with h | h
    · left
      exact Subrepresentation.ext h
    · right
      exact Subrepresentation.ext h

end FiniteGroups

section TextTau

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct ENNReal Matrix

namespace Size

variable (I : Formalism.MainNotions.S.AutInst)

def latSet (x : I.GA) : Set (Fin I.n → I.E) :=
  {u | (I.fmat x.2⁻¹) *ᵥ (fun i => Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (u i)) ∈ I.Lf}

def coordV (x : I.GA) (v : InfinitePlace I.F) (u : Fin I.n → I.E) : Fin I.n → ℂ :=
  (Formalism.MainNotions.S.uMat (x.1 v)⁻¹ * (I.P v)⁻¹) *ᵥ (fun i => I.φ v (u i))

def gramV (x : I.GA) (v : InfinitePlace I.F) {j : ℕ} (b : Fin j → Fin I.n → I.E) : Matrix (Fin j) (Fin j) ℂ :=
  fun a c => ∑ i, star (coordV I x v (b a) i) * coordV I x v (b c) i

structure Sub (x : I.GA) where
  j : ℕ
  j_pos : 1 ≤ j
  b : Fin j → Fin I.n → I.E
  b_ind : LinearIndependent I.E b
  B : Submodule (𝓞 I.E) (Fin I.n → I.E)
  B_lat : (B : Set (Fin I.n → I.E)) ⊆ latSet I x
  b_mem : ∀ a, b a ∈ B
  B_span : (B : Set (Fin I.n → I.E)) ⊆ Submodule.span I.E (Set.range b)

def ht {x : I.GA} (s : Sub I x) : ℝ :=
  (∏ v, (gramV I x v s.b).det.re) /
    (Nat.card (s.B ⧸ (Submodule.span (𝓞 I.E) (Set.range s.b)).comap s.B.subtype) : ℝ)

def size {x : I.GA} (s : Sub I x) : ℝ := ht I s ^ ((1 : ℝ) / (2 * (I.f : ℝ) * (s.j : ℝ)))

def tau1 (x : I.GA) : ℝ := min (1 / 2) (⨅ s : Sub I x, size I s)

end Size

def ReductionTau : Prop :=
  ∀ I : Formalism.MainNotions.S.AutInst, 1 ≤ I.n →
    Continuous (Size.tau1 I) ∧ ∀ x : I.GA, 0 < Size.tau1 I x ∧ Size.tau1 I x ≤ 1 / 2

end TextTau

section SpectralGap₂

open Finset Matrix MeasureTheory

section GapStatementAlt

open Formalism.MainNotions.S Formalism.MainNotions.CayleySignature

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def GapStatementAt (C : ℝ) : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ), RealPlaceNumericalSetting k r z c u v b → GapC C k r b →
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat k r → (H →L[ℂ] H)),
    IsDSHpk k r (eps48 k r) (lam48 k r v b) σ →
  ∀ (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [FiniteDimensional ℂ Vp]
    (π : Mat k r → (Vp →L[ℂ] Vp)), IsHCTypeW k r z u π →
  ∀ w : H, IsLowUnitH k r (eps48 k r) (lam48 k r v b) σ w →
  ∀ μG μS ν : Measure (Formalism.QuantumDeterminants.Mt k r),
    IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG → IsHaarOn (Formalism.QuantumDeterminants.Sset k r z) μS →
    IsQuotMeas μG μS ν →
  ∃ W : Mat k r → Vp,
    AEStronglyMeasurable (fun x => W (Matrix.of x)) μG ∧ AEStronglyMeasurable (fun x => W (Matrix.of x)) ν ∧
    IsSPsiEquiv z (psiGen k r z c) π W ∧ l2SG ν W < ⊤ ∧ l2SG ν W ≠ 0 ∧
    ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), rconv μG (eFun μG σ w) W x = W x

def GapStatementAlt : Prop := GapStatementAt 0

theorem gapStatementAt_iff (D : Formalism.BasicNotions.D7) (C : ℝ) : GapStatementAt C ↔ Formalism.MainNotions.CayleySignature.Conclusion2 D C := Iff.rfl

theorem gapC_zero_of_setting {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {c : Fin r → ℂ} {u : Fin k → ℝ}
    {v : Fin (k - 1) → ℝ} {b : Fin (2 * r + 2) → ℝ} (h : RealPlaceNumericalSetting k r z c u v b) : GapC 0 k r b := by
  obtain ⟨-, -, -, -, -, -, -, -, -, t, -, -, -, hg⟩ := h
  intro j hj
  have h1 := hg j hj
  have h3 : (0 : ℝ) ≤ 2 * ((rk48 k r + (2 * r + 2) * t : ℕ) : ℝ) ^ 3 + (t : ℝ) + 3 := by positivity
  rw [zero_mul]
  linarith

theorem gapStatement_iff_all : GapStatementAlt ↔ ∀ C : ℝ, GapStatementAt C := by
  constructor
  · intro h C k r z c u v b hS _
    exact h k r z c u v b hS (gapC_zero_of_setting hS)
  · intro h
    exact h 0

theorem interlaceSetting_example :
    RealPlaceNumericalSetting 2 0 (Formalism.QuantumDeterminants.bvec (2 : Fin 3)) (fun i => i.elim0) ![3 / 2, -1 / 2] ![1] ![1, 100000000000] := by
  refine ⟨by norm_num, ⟨1, rfl⟩, ?_, ?_, fun a => a.elim0, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have := i.isLt
    omega
  · simp [Formalism.QuantumDeterminants.Tz, Formalism.QuantumDeterminants.herm, Formalism.QuantumDeterminants.Hpk, Formalism.QuantumDeterminants.bvec, dotProduct, Matrix.mulVec,
      Fin.sum_univ_three, Pi.single_apply]
  · refine ⟨?_, ?_⟩
    · intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all <;> norm_num
    · intro a
      fin_cases a
      · exact ⟨1, by norm_num⟩
      · exact ⟨-1, by norm_num⟩
  · refine ⟨?_, ?_⟩
    · intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all [lam48] <;> norm_num
    · intro a
      fin_cases a
      · exact ⟨0, by norm_num [lam48]⟩
      · exact ⟨-2, by norm_num [lam48]⟩
      · exact ⟨-100000000001, by norm_num [lam48]⟩
  · refine ⟨?_, ?_⟩
    · intro i
      fin_cases i
      norm_num
    · intro _
      norm_num
  · intro i s
    fin_cases i <;> fin_cases s
    · exact ⟨0, by norm_num [lam48]⟩
    · exact ⟨2, by norm_num [lam48]⟩
    · exact ⟨100000000001, by norm_num [lam48]⟩
    · exact ⟨-2, by norm_num [lam48]⟩
    · exact ⟨0, by norm_num [lam48]⟩
    · exact ⟨99999999999, by norm_num [lam48]⟩
  · refine ⟨1799, by decide, by norm_num [rk48], by norm_num [rk48], ?_⟩
    intro j hj
    have hj0 : j = 0 := by
      ext
      simp at hj ⊢
      omega
    subst hj0
    norm_num [rk48]

end GapStatementAlt

end SpectralGap₂

section BesselNVPart

open Formalism.MainNotions.S Formalism.MainNotions.CayleySignature MeasureTheory
open scoped InnerProductSpace

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def BesselNV : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ),
    2 ≤ k → Even k → Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → (∀ a, c a ≠ 0) →
    Formalism.QuantumDeterminants.IsHCParam u → Formalism.QuantumDeterminants.IsHCParam (lam48 k r v b) → InterlacingCondition k r u v b →
    HalfIntegralDifference k r u v b →
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat k r → (H →L[ℂ] H)),
    IsDSHpk k r (eps48 k r) (lam48 k r v b) σ →
  ∀ (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [FiniteDimensional ℂ Vp]
    (π : Mat k r → (Vp →L[ℂ] Vp)), IsHCTypeW k r z u π →
  ∀ w : H, IsLowUnitH k r (eps48 k r) (lam48 k r v b) σ w →
  ∀ μW μN : Measure (Formalism.QuantumDeterminants.Mt k r), IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW → IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN →
  ∃ x x₀ : Mat k r, x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) ∧ x₀ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) ∧
    ∫ p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r,
      (⟪σ x₀ w, σ (Matrix.of p.1 * Matrix.of p.2) (σ x w)⟫_ℂ * star (psiGen k r z c (Matrix.of p.2))) •
        π (Matrix.of p.1)⁻¹ ∂(μW.prod μN) ≠ 0

theorem besselNV_numeric_example :
    2 ≤ 2 ∧ Even 2 ∧ Formalism.QuantumDeterminants.inWb 2 0 (Formalism.QuantumDeterminants.bvec (2 : Fin 3)) ∧ 0 < Formalism.QuantumDeterminants.Tz 2 0 (Formalism.QuantumDeterminants.bvec (2 : Fin 3)) ∧
      (∀ a : Fin 0, (fun i : Fin 0 => i.elim0 : Fin 0 → ℂ) a ≠ 0) ∧ Formalism.QuantumDeterminants.IsHCParam ![(3 : ℝ) / 2, -1 / 2] ∧
      Formalism.QuantumDeterminants.IsHCParam (lam48 2 0 ![1] ![1, 100000000000]) ∧
      InterlacingCondition 2 0 ![3 / 2, -1 / 2] ![1] ![1, 100000000000] ∧
      HalfIntegralDifference 2 0 ![3 / 2, -1 / 2] ![1] ![1, 100000000000] := by
  obtain ⟨-, hE, hz, hT, hc, hu, hl, hI, hH, -⟩ := interlaceSetting_example
  exact ⟨le_refl 2, hE, hz, hT, hc, hu, hl, hI, hH⟩

end BesselNVPart

end Formalism.L2.SG.LitS
