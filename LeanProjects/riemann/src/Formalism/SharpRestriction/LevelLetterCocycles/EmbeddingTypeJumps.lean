import Mathlib
import Formalism.LocalRingCardinality.DataParams₂
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.WeaklyAdmissibleFiltrations.StatementTor
import Formalism.GaloisCohomology.Statement
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
import Formalism.SharpRestriction.LevelLetterCocycles.ElementDenominator

noncomputable section

namespace Formalism.MainNotions.EmbeddingTypeJumps

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.FrobeniusOrbits
open scoped Pointwise

section Lemma1

variable (D : D7)

def InPhi (φ : D.host.E →+* ℂ) : Prop := φ ∈ D.host.cmType

abbrev decG (v : HeightOneSpectrum (𝓞 D.host.E)) : Subgroup (D.host.E ≃ₐ[ℚ] D.host.E) :=
  MulAction.stabilizer (D.host.E ≃ₐ[ℚ] D.host.E) v.asIdeal

abbrev ineG (v : HeightOneSpectrum (𝓞 D.host.E)) : Subgroup (D.host.E ≃ₐ[ℚ] D.host.E) :=
  Ideal.inertia (D.host.E ≃ₐ[ℚ] D.host.E) v.asIdeal

def Conclusion1 : Prop :=
  ∀ l ∈ ({D.host.q, D.host.d} : Finset ℕ), l % 4 = 3 ∧
    ∀ v ∈ placesOver D.host.E l,
      v.asIdeal.ramificationIdx ℤ = 2 ∧
      D.host.conj • v.asIdeal ≠ v.asIdeal ∧
      (l = D.host.q → ∀ σ ∈ decG D v, ∀ φ : D.host.E →+* ℂ,
        (InPhi D (φ.comp (σ : D.host.E →+* D.host.E)) ↔ InPhi D φ)) ∧
      (l = D.host.d → ∀ σ ∈ ineG D v, σ ≠ 1 → ∀ φ : D.host.E →+* ℂ,
        (InPhi D (φ.comp (σ : D.host.E →+* D.host.E)) ↔ ¬ InPhi D φ))

end Lemma1

def epsL (l : ℕ) : ℝ := ((l : ℝ) ^ 2)⁻¹

def polyVal (P : MvPolynomial (Fin 3) ℕ) (f r t : ℕ) : ℕ := MvPolynomial.eval ![f, r, t] P

def bndB (D : D7) (large₂ : SizeData₂ D) (C : ℝ) (P : MvPolynomial (Fin 3) ℕ) (l : ℕ) : ℝ :=
  C * D.R.f * (D.R.r * (large₂.sc.b / l + large₂.Sc + D.R.t + large₂.etaSz + Real.log large₂.sc.b) + D.R.m * large₂.sc.b) +
    (polyVal P D.R.f D.R.r D.R.t : ℝ) * Real.log large₂.sc.b

def TwLoc (D : D7) (i : D.nd.Loc) : Prop := D.what₂.muAt (D.nd.w i) ≠ D.what₂.mu0

def vZeta (D : D7) (i : D.nd.Loc) (v : HeightOneSpectrum (𝓞 D.host.E)) : ℚ :=
  lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {D.nd.zeta i v - 1})

section Glob

open Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.BasicNotions.Loc Formalism.MainNotions.N

variable {D : D7}
  (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))

def AtQD (i : D.nd.Loc) : Prop :=
  ((D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) ∧ TwLoc D i) ∧ HG D.nd D.naut i

def Conclusion2 (large₂ : SizeData₂ D) (C : ℝ) (P : MvPolynomial (Fin 3) ℕ) : Prop :=
  ∀ i : D.nd.Loc, (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) → TwLoc D i →
    large₂.sc.x ^ (2 * large₂.Ct + 5) < (D.nd.l i : ℝ) →
    ∀ π ∈ D.nd.Zgood i, Br.sFin D.loc D.nbr i (ρ i) π →
      (∀ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) < ⊤) →
      (D.nd.vcc i π : ℝ) ≤ bndB D large₂ C P (D.nd.l i) +
        ((∑ e ∈ Finset.Ioo 0 D.R.t, D.what₂.shaLen (D.nd.l i) e : ℚ) : ℝ) +
        (padicValNat (D.nd.l i) (hE D.host) : ℝ) +
        (Br.sPi D.loc D.nbr i (ρ i) π : ℝ) + epsL (D.nd.l i)

def admA (CA : ℝ) : Prop := Formalism.MainNotions.ElementDenominator.Conclusion1 D CA

def GlobalIndexAwayFromTypes : Prop :=
  ∀ (i : D.nd.Loc) (π : D.nd.X i) (dc : Formalism.MainNotions.TruncatedSeriesCountingIdentities.Decl D i)
    (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ) (e' : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ),
    Formalism.MainNotions.TruncatedSeriesCountingIdentities.admitted i (r i) (ρ i) π dc lenRow e' cB → Formalism.MainNotions.TruncatedSeriesCountingIdentities.GlobalLatticeIndexTheorem i (ρ i) π dc lenRow e' cB

def EndomorphismGoodPartBound : Prop := ∀ i : D.nd.Loc, Formalism.MainNotions.TruncatedSeriesCountingIdentities.EndomorphismIndexBound (D := D) i

def admG1 : Prop := ∀ i : D.nd.Loc, AtQD i → Formalism.MainNotions.TruncatedSeriesCountingIdentities.admG1 i (r i)

def admG2 : Prop :=
  ∀ i : D.nd.Loc, AtQD i → ∀ π ∈ D.nd.Zgood i, Formalism.MainNotions.TruncatedSeriesCountingIdentities.admG2 i (r i) (ρ i) π

def admG3 : Prop :=
  ∀ i : D.nd.Loc, AtQD i → ∀ π ∈ D.nd.Zgood i, Formalism.MainNotions.TruncatedSeriesCountingIdentities.admG3 i (r i) (ρ i) π

def admG4 : Prop := ∀ i : D.nd.Loc, AtQD i → Formalism.MainNotions.TruncatedSeriesCountingIdentities.admG4 i (r i)

def admG5 : Prop := ∀ i : D.nd.Loc, AtQD i → Formalism.MainNotions.TruncatedSeriesCountingIdentities.admG5 i (r i)

def admG6 : Prop := ∀ i : D.nd.Loc, AtQD i → Formalism.MainNotions.TruncatedSeriesCountingIdentities.admG6 i (r i)

def iwahoriAdmissibleSet : Prop :=
  ∀ i : D.nd.Loc, AtQD i → ∀ π ∈ D.nd.Zgood i,
    Formalism.MainNotions.TruncatedSeriesCountingIdentities.FamilyContinuous i (r i) ∧ Formalism.MainNotions.TruncatedSeriesCountingIdentities.admSS i (r i) ∧
      Formalism.MainNotions.TruncatedSeriesCountingIdentities.SemisimpleDecomposition i (r i) (ρ i) π ∧ Formalism.MainNotions.TruncatedSeriesCountingIdentities.CyclotomicInertiaImage (D := D) i

def LocalLiftingAdmitted (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (CLL : ℝ) : Prop := Formalism.MainNotions.LocalSituation.LocalLiftingWachEtale D HW F CLL

def H0ColumnLengthBound (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.LocalSituation.Conclusion2 D HW F

def admTB (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.LocalSituation.Conclusion4 D HW F

def admBK : Prop := Formalism.MainNotions.LocalSituation.Conclusion5 D

def KillingTwistedPlaces : Prop :=
  ∀ i : D.nd.Loc, (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) → TwLoc D i →
    ((∀ v ∈ placesOver D.host.E (D.nd.l i), v.asIdeal.ramificationIdx ℤ = 1) ∨
      D.R.t * D.R.r < Module.finrank D.host.E (CyclotomicField (D.nd.l i) D.host.E)) →
    ∀ π ∈ D.nd.Zgood i, (Br.sPi D.loc D.nbr i (ρ i) π : ℝ) ≤ epsL (D.nd.l i) ∧
      (D.R.t : ℝ) * ((∑ v ∈ D.nd.Q i, vZeta D i v : ℚ) : ℝ) ≤ epsL (D.nd.l i)

def WachHypothesisLocal (S : Formalism.MainNotions.LocalSituation.Sit) (E : S.Comparison₂) : Prop :=
  ∀ (Y : LocLat S.G S.Qp S.LL S.O) (M0 h0 : ℕ), Formalism.WeaklyAdmissibleFiltrations.IsCrys S.PD Y.ρ →
    (∀ a ∈ Formalism.MainNotions.LocalSituation.Jset S Y, -(M0 : ℤ) ≤ a ∧ a ≤ h0) → Formalism.MainNotions.LocalSituation.HypW S E Y M0 h0

def admW (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ i : D.nd.Loc, AtQD i →
    ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
      (C : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw) (h : Good (D.nbr i w hw).Kw 1 C.LL),
      WachHypothesisLocal (Formalism.MainNotions.LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 C.LL h)
        ((F (D.nd.l i)).E (D.nbr i w hw).Kw 1 C.LL h).tie

def TateLengthAllExponents (S : Formalism.MainNotions.LocalSituation.Sit) : Prop :=
  ∀ (e c : ℕ) (Ve : LocLat S.G S.Qp S.LL S.O), finrank S.LL Ve.V = 1 →
    (∀ g x, Ve.ρ g x = ((algebraMap S.Qp S.LL (S.PD.χ g : S.Qp))⁻¹) ^ e • x) →
    Module.length S.O ↥(Submodule.torsionBy S.O (DivisibleCohomology Ve.L ⧸ divisibleFiniteCohomology S.PD Ve.L)
        ((Formalism.MainNotions.LocalSituation.ell S : S.O) ^ c)) ≤
      (((finrank S.Qp S.K + 1) * c : ℕ) : ℕ∞) * lenOl S.PD (O := S.O)

def TateLengthCogenerators (HW : HWOf D.loc) : Prop :=
  ∀ i : D.nd.Loc, AtQD i →
    ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
      (C : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw) (h : Good (D.nbr i w hw).Kw 1 C.LL),
      TateLengthAllExponents (Formalism.MainNotions.LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 C.LL h)

def FontaineAtPlacesOverL : Prop := Formalism.MainNotions.LocalSituation.adm7 D

def LiteratureHypotheses : Prop :=
  ∀ i : D.nd.Loc, AtQD i →
    Formalism.MainNotions.TruncatedSeriesCountingIdentities.TameGeneratorConditions i ∧
    (∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
      (C : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw),
      Formalism.MainNotions.TruncatedSeriesCountingIdentities.TateDualityH2Torsion (Br.PD D.loc D.nbr i w hw) ↥C.LL.1 ↥(OL C.LL) ∧
      BlochKatoDim (Br.PD D.loc D.nbr i w hw) ↥C.LL.1) ∧
    Formalism.MainNotions.TruncatedSeriesCountingIdentities.LocalCoefficientCompatibility i ∧ Formalism.MainNotions.TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i ∧ Formalism.MainNotions.TruncatedSeriesCountingIdentities.admH2 i ∧ Formalism.MainNotions.TruncatedSeriesCountingIdentities.UnramifiedClassFieldBound i

def EmbTypeUc {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
    {hw : w ∈ placesOver D.host.E (D.nd.l i)}
    (τ₀ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw) : Prop :=
  (∀ x : D.host.E, ∃ y : D.what₂.LL,
    Br.toLLK (D.nbr i w hw) (D.nd.embK i y) = τ₀ (Br.cEw D.nbr i w hw x)) ∧
  ∃ φ ∈ D.host.cmType,
    ∀ (x : D.host.E) (y : D.what₂.LL),
      Br.toLLK (D.nbr i w hw) (D.nd.embK i y) = τ₀ (Br.cEw D.nbr i w hw x) →
        D.what₂.embLL y = starRingEnd ℂ (φ x)

def EmbTypeUe (ep : Bool) {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
    {hw : w ∈ placesOver D.host.E (D.nd.l i)}
    (τ₀ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw) : Prop :=
  if ep then Br.EmbTypeU D.nbr i w hw τ₀ else EmbTypeUc τ₀

def UpAt (ep : Bool) {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
    {hw : w ∈ placesOver D.host.E (D.nd.l i)} (C : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1) : Prop :=
  ∃ τ₀ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw,
    EmbTypeUe ep τ₀ ∧ ∀ x, τ x = C.inc (τ₀ x)

def DownAt (ep : Bool) {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
    {hw : w ∈ placesOver D.host.E (D.nd.l i)} (C : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1) : Prop :=
  ∃ τ₀ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw,
    EmbTypeUe (!ep) τ₀ ∧ ∀ x, τ x = C.inc (τ₀ x)

theorem not_upAt_and_downAt (ep : Bool) {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
    {hw : w ∈ placesOver D.host.E (D.nd.l i)} (C : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1) : ¬ (UpAt ep C τ ∧ DownAt ep C τ) := by
  rintro ⟨⟨τ₀, h0, e0⟩, ⟨τ₁, h1, e1⟩⟩
  have hτ : τ₀ = τ₁ := by
    ext x
    exact congrArg _ ((C.inc).injective ((e0 x).symm.trans (e1 x)))
  subst hτ
  have hd : (0 : ℝ) < Real.sqrt (D.host.d : ℝ) := by
    have := D.host.qd_big.2
    exact Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < D.host.d))
  have key : ∀ (ψ₁ ψ₂ : D.host.E →+* ℂ),
      ψ₁ ∈ D.host.cmType →
      ψ₂ ∈ D.host.cmType →
      (∃ y : D.what₂.LL, D.what₂.embLL y = ψ₁ (D.host.sqd) ∧
        D.what₂.embLL y = starRingEnd ℂ (ψ₂ (D.host.sqd))) → False := by
    intro ψ₁ ψ₂ m1 m2 ⟨y, hy1, hy2⟩
    have h := hy1.symm.trans hy2
    simp only [Formalism.HC.HostRaw.cmType, Set.mem_ofPred_eq] at m1 m2
    rw [m1, m2] at h
    have him := congrArg Complex.im h
    simp at him
    linarith
  cases ep with
  | true =>
    obtain ⟨hr, φ, hφ, hφr⟩ := h0
    obtain ⟨-, φ', hφ', hφ'r⟩ := h1
    obtain ⟨y, hy⟩ := hr (D.host.sqd)
    exact key φ φ' hφ hφ' ⟨y, hφr _ _ hy, hφ'r _ _ hy⟩
  | false =>
    obtain ⟨hr, φ, hφ, hφr⟩ := h0
    obtain ⟨-, φ', hφ', hφ'r⟩ := h1
    obtain ⟨y, hy⟩ := hr (D.host.sqd)
    exact key φ' φ hφ' hφ ⟨y, hφ'r _ _ hy, hφr _ _ hy⟩

def HodgeJumpWindowsAtDistinguishedPrimes (ep : Bool) (large₂ : SizeData₂ D) : Prop :=
  ∀ i : D.nd.Loc, AtQD i →
    ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
      (C : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw) (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1),
      ∃ (s : ℤ) (Jc Jl : Finset ℤ),
        large₂.etaSz + D.R.t + 1 < (s : ℝ) ∧ (s : ℝ) ≤ large₂.sc.b + large₂.etaSz + D.R.t + 1 ∧
        Jc.card = D.R.k - 1 ∧ Jl.card = D.R.m ∧
        (∀ a ∈ Jl,
          ((-large₂.etaSz + ((D.R.t : ℝ) - 1) / 2 ≤ (a : ℝ) ∧ a ≤ -2) ∨
            ((D.R.t : ℤ) + 1 ≤ a ∧ (a : ℝ) ≤ large₂.etaSz + ((D.R.t : ℝ) - 1) / 2)) ∧
          ¬ (0 ≤ a ∧ a < D.R.t) ∧ a ≠ -1 ∧ a ≠ D.R.t) ∧
        ((∀ a ∈ Jc, s ≤ a ∧ (a : ℝ) ≤ s + large₂.Sc) ∨ (∀ a ∈ Jc, -((s : ℝ) + large₂.Sc) ≤ a ∧ a ≤ -s)) ∧
        (UpAt ep C τ → ∀ a ∈ Jc, s ≤ a ∧ (a : ℝ) ≤ s + large₂.Sc) ∧
        (DownAt ep C τ → ∀ a ∈ Jc, -((s : ℝ) + large₂.Sc) ≤ a ∧ a ≤ -s) ∧
        ∀ (x : D.nd.X i) (a : ℤ),
          IsJumpV (Br.PD D.loc D.nbr i w hw)
              (matRep (Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (r i) x))) τ a ↔
            a ∈ Jc ∨ a ∈ Jl ∨ (0 ≤ a ∧ a < D.R.t)

def FontaineSubOfSumsAtDistinguishedPrimes : Prop :=
  ∀ i : D.nd.Loc, AtQD i →
    ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
      (C : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw),
      (∀ (V1 : Type) [AddCommGroup V1] [Module ↥C.LL.1 V1] [Module ℚ_[D.nd.l i] V1]
          [IsScalarTower ℚ_[D.nd.l i] ↥C.LL.1 V1] [FiniteDimensional ↥C.LL.1 V1]
          (ρ1 : Representation ↥C.LL.1 (Br.G D.nbr i w hw) V1),
          IsSubOfSums ρ1 (fun x : D.nd.X i => ⇑(Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C (rDuO D.nd i (r i) x))) →
          IsCrys (Br.PD D.loc D.nbr i w hw) ρ1 ∧
          ∀ τ a, IsJumpV (Br.PD D.loc D.nbr i w hw) ρ1 τ a →
            ∃ x : D.nd.X i, IsJumpV (Br.PD D.loc D.nbr i w hw)
              (matRep (Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (r i) x))) τ (-a - 1)) ∧
      (∀ π ∈ D.nd.Zgood i,
          IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C (T2O D.nd i (ρ i) π))) ∧
          ∀ τ (a : ℤ),
            ((IsJumpV (Br.PD D.loc D.nbr i w hw)
                (matRep (Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (r i) π))) τ (-a - 1) ∧
                ¬ (0 ≤ -a - 1 ∧ -a - 1 < (D.R.t : ℤ))) →
              multV (Br.PD D.loc D.nbr i w hw)
                (matRep (Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C (T2O D.nd i (ρ i) π))) τ a = 1) ∧
            (¬ (IsJumpV (Br.PD D.loc D.nbr i w hw)
                (matRep (Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (r i) π))) τ (-a - 1) ∧
                ¬ (0 ≤ -a - 1 ∧ -a - 1 < (D.R.t : ℤ))) →
              multV (Br.PD D.loc D.nbr i w hw)
                (matRep (Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C (T2O D.nd i (ρ i) π))) τ a = 0))

def ParametersPolynomiallyBounded (large₂ : SizeData₂ D) : Prop := large₂.Sc + large₂.etaSz + D.R.t + 2 ≤ large₂.sc.b

def Conclusion0 (D : D7) : Prop :=
  ∀ i : D.nd.Loc, (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) →
    ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      (∃ y : Om (D.nd.l i), y ^ 2 = -(D.nd.l i : Om (D.nd.l i)) ∧
        (D.nbr i w hw).Kw.1 = K0 (D.nbr i w hw).Kw ⊔ IntermediateField.adjoin ℚ_[D.nd.l i] {y}) ∧
      (D.nbr i w hw).Kw.1 ≤ Ks (D.nbr i w hw).Kw 1 ∧
      finrank ↥(K0 (D.nbr i w hw).Kw) ↥(D.nbr i w hw).Kw.1 = 2 ∧
      finrank ℚ_[D.nd.l i] ↥(Ks (D.nbr i w hw).Kw 1) =
        (D.nd.l i - 1) / 2 * finrank ℚ_[D.nd.l i] ↥(D.nbr i w hw).Kw.1

def admitted (ep : Bool) (CA : ℝ) (CLL : ℝ) (large₂ : SizeData₂ D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  admW (D := D) HW F ∧ admA (D := D) CA ∧ GlobalIndexAwayFromTypes r ρ ∧ EndomorphismGoodPartBound (D := D) ∧ admG1 r ∧ admG2 r ρ ∧ admG3 r ρ ∧
    admG4 r ∧ admG5 r ∧ admG6 r ∧ iwahoriAdmissibleSet r ρ ∧ LocalLiftingAdmitted (D := D) HW F CLL ∧ H0ColumnLengthBound (D := D) HW F ∧
    admTB (D := D) HW F ∧ TateLengthCogenerators (D := D) HW ∧ admBK (D := D) ∧ KillingTwistedPlaces ρ ∧ HodgeJumpWindowsAtDistinguishedPrimes r ep large₂ ∧ FontaineSubOfSumsAtDistinguishedPrimes r ρ ∧ FontaineAtPlacesOverL (D := D) ∧
    LiteratureHypotheses (D := D) ∧ ParametersPolynomiallyBounded large₂

def Stmt (CA : ℝ) (CLL : ℝ) (large₂ : SizeData₂ D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C : ℝ) (P : MvPolynomial (Fin 3) ℕ) :
    Prop :=
  ∀ ep : Bool, admitted r ρ ep CA CLL large₂ HW F → Conclusion0 D ∧ Conclusion1 D ∧ Conclusion2 ρ large₂ C P

def UniformExportStatement : Prop :=
  ∀ CA CLL : ℝ, ∃ (C : ℝ) (P : MvPolynomial (Fin 3) ℕ),
    ∀ (D : D7)
      (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
      (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
      (large₂ : SizeData₂ D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW),
      Stmt r ρ CA CLL large₂ HW F C P

end Glob

end Formalism.MainNotions.EmbeddingTypeJumps

end
