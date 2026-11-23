import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FrameTransport

noncomputable section

namespace Formalism.MainNotions.UnusedSlot34

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

section Ext

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)

def thetaS {n : ℕ} (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (S : Set (Fin n → Fin M → E))
    (h : HA (AF F) σ J) : ℂ :=
  ∑' X : S, Φ (actTup (AF F) (HA.mat (AF F) σ J h⁻¹) (ratTup (AF F) (X : Fin n → Fin M → E)))

def SWa1 : Prop :=
  AllSome (IsHaarH F E σ M J) fun μ => AllSome (IsFDH F E σ M J μ) fun 𝓕 => μ 𝓕 < ⊤

def SWa2 : Prop :=
  3 ≤ M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℂ)
    (Φinf : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℂ) (Φf : (Fin 1 → Fin M → Af F ⊗[F] E) → ℂ),
    IsSB Φf → Measurable Φinf → RapidDecay b Φinf → IsProdInfFin Φ Φinf Φf →
    AllSome (IsHaarH F E σ M J) fun μ => AllSome (IsFDH F E σ M J μ) fun 𝓕 =>
      ∫⁻ h in 𝓕, ∑' x : (Fin 1 → Fin M → E),
        ENNReal.ofReal ‖Φ (actTup (AF F) (HA.mat (AF F) σ J h⁻¹) (ratTup (AF F) x))‖ ∂μ < ⊤

def SWb1 : Prop :=
  3 ≤ M → ∀ (β : F) (d : ℕ) (b : Module.Basis (Fin d) F E)
    (Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℂ) (Φinf : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℂ)
    (Φf : (Fin 1 → Fin M → Af F ⊗[F] E) → ℂ)
    (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin 1 → Fin M → Fv F v ⊗[F] E) → ℂ),
    Continuous Φinf → RapidDecay b Φinf → IsPureFin b Φf Φv → IsProdInfFin Φ Φinf Φf →
    AllSome (IsHaarH F E σ M J) fun μ => AllSome (IsFDH F E σ M J μ) fun 𝓕 =>
    AllSome (IsCharAF F) fun ψ =>
    AllSome (SdW F E σ M J (Ainf F) (psiInf F ψ) 1) fun μinf =>
    AllSome (SdR (Ainf F) (psiInf F ψ)) fun νinf =>
    AllSome (fun μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin 1 → Fin M → Fv F v ⊗[F] E) =>
      ∀ v, SdW F E σ M J (Fv F v) (psiV F ψ v) 1 (μv v)) fun μv =>
    AllSome (fun νv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v) =>
      ∀ v, SdR (Fv F v) (psiV F ψ v) (νv v)) fun νv =>
    ∃ (ginf : Ainf F → ℂ) (gv : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℂ),
      IsContDensity μinf (fun X => qR (Ainf F) σ J (X 0)) id νinf Φinf ginf ∧
      (∀ v, IsContDensity (μv v) (fun X => qR (Fv F v) σ J (X 0)) id (νv v) (Φv v) (gv v)) ∧
      Multipliable (fun v => gv v (algebraMap F (Fv F v) β)) ∧
      meanC μ 𝓕 (thetaS F E σ M J Φ {x | x 0 ≠ 0 ∧ hE σ J (x 0) (x 0) = algebraMap F E β}) =
        ginf (algebraMap F (Ainf F) β) * ∏' v, gv v (algebraMap F (Fv F v) β)

def SWb2 : Prop :=
  3 ≤ M → ∀ (β : F), β ≠ 0 → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E)
    (Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℂ) (Φinf : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℂ)
    (Φf : (Fin 1 → Fin M → Af F ⊗[F] E) → ℂ)
    (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin 1 → Fin M → Fv F v ⊗[F] E) → ℂ),
    Measurable Φinf → (∀ X, 0 ≤ (Φinf X).re ∧ (Φinf X).im = 0) →
    IsPureFin b Φf Φv → (∀ v Y, 0 ≤ (Φv v Y).re ∧ (Φv v Y).im = 0) →
    IsProdInfFin Φ Φinf Φf →
    AllSome (IsHaarH F E σ M J) fun μ => AllSome (IsFDH F E σ M J μ) fun 𝓕 =>
    AllSome (IsCharAF F) fun ψ =>
    AllSome (SdW F E σ M J (Ainf F) (psiInf F ψ) 1) fun μinf =>
    AllSome (SdR (Ainf F) (psiInf F ψ)) fun νinf =>
    AllSome (fun μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin 1 → Fin M → Fv F v ⊗[F] E) =>
      ∀ v, SdW F E σ M J (Fv F v) (psiV F ψ v) 1 (μv v)) fun μv =>
    AllSome (fun νv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v) =>
      ∀ v, SdR (Fv F v) (psiV F ψ v) (νv v)) fun νv =>
    AllSome (fun fibInf : Ainf F → Measure (Fin 1 → Fin M → Ainf F ⊗[F] E) =>
      IsFibreFamily μinf (fun X => qR (Ainf F) σ J (X 0)) id Set.univ νinf
        {c : Ainf F | ∀ w, c w ≠ 0} fibInf) fun fibInf =>
    AllSome (fun fibV : ∀ v : HeightOneSpectrum (𝓞 F),
        Fv F v → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E) =>
      ∀ v, IsFibreFamily (μv v) (fun X => qR (Fv F v) σ J (X 0)) id Set.univ (νv v)
        {c | c ≠ 0} (fibV v)) fun fibV =>
    Multipliable (fun v => ∫⁻ X, ENNReal.ofReal (Φv v X).re ∂(fibV v (algebraMap F (Fv F v) β))) ∧
    meanL μ 𝓕 (fun h => ∑' x : {x : Fin 1 → Fin M → E | x 0 ≠ 0 ∧
        hE σ J (x 0) (x 0) = algebraMap F E β},
      ENNReal.ofReal (Φ (actTup (AF F) (HA.mat (AF F) σ J h⁻¹)
        (ratTup (AF F) (x : Fin 1 → Fin M → E)))).re) =
      (∫⁻ X, ENNReal.ofReal (Φinf X).re ∂(fibInf (algebraMap F (Ainf F) β))) *
        ∏' v, ∫⁻ X, ENNReal.ofReal (Φv v X).re ∂(fibV v (algebraMap F (Fv F v) β))

def SWc1 : Prop :=
  ∀ (n : ℕ), n + 2 ≤ M → ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b),
    T.det ≠ 0 → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E)
    (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (Φinf : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ)
    (Φf : (Fin n → Fin M → Af F ⊗[F] E) → ℂ)
    (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ),
    Continuous Φinf → RapidDecay b Φinf → IsPureFin b Φf Φv → IsProdInfFin Φ Φinf Φf →
    AllSome (IsHaarH F E σ M J) fun μ => AllSome (IsFDH F E σ M J μ) fun 𝓕 =>
    AllSome (IsCharAF F) fun ψ =>
    AllSome (SdW F E σ M J (Ainf F) (psiInf F ψ) n) fun μinf =>
    AllSome (SdHerm F E σ (Ainf F) (psiInf F ψ) n) fun νinf =>
    AllSome (fun μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E) =>
      ∀ v, SdW F E σ M J (Fv F v) (psiV F ψ v) n (μv v)) fun μv =>
    AllSome (fun νv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (HermR (Fv F v) σ n) =>
      ∀ v, SdHerm F E σ (Fv F v) (psiV F ψ v) n (νv v)) fun νv =>
    ∃ (ginf : HermR (Ainf F) σ n → ℂ) (gv : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ n → ℂ),
      IsContDensityOn μinf (gramR (Ainf F) σ J) Subtype.val νinf
        {S | IsUnit (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det} Φinf ginf ∧
      (∀ v, IsContDensityOn (μv v) (gramR (Fv F v) σ J) Subtype.val (νv v)
        {S | IsUnit (S : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)).det} (Φv v) (gv v)) ∧
      Multipliable (fun v => gv v (hermOf (Fv F v) σ T hT)) ∧
      meanC μ 𝓕 (thetaS F E σ M J Φ {X | gramE σ J X = T}) =
        ginf (hermOf (Ainf F) σ T hT) * ∏' v, gv v (hermOf (Fv F v) σ T hT)

def SWc2 : Prop :=
  ∀ (p : ℕ), 2 * p + 1 ≤ M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E)
    (Φ : (Fin p → Fin M → AF F ⊗[F] E) → ℂ) (Φinf : (Fin p → Fin M → Ainf F ⊗[F] E) → ℂ)
    (Φf : (Fin p → Fin M → Af F ⊗[F] E) → ℂ)
    (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin p → Fin M → Fv F v ⊗[F] E) → ℂ),
    Continuous Φinf → RapidDecay b Φinf → IsPureFin b Φf Φv → IsProdInfFin Φ Φinf Φf →
    AllSome (IsHaarH F E σ M J) fun μ => AllSome (IsFDH F E σ M J μ) fun 𝓕 =>
    AllSome (IsCharAF F) fun ψ =>
    AllSome (SdW F E σ M J (Ainf F) (psiInf F ψ) p) fun μinf =>
    AllSome (SdHerm F E σ (Ainf F) (psiInf F ψ) p) fun νinf =>
    AllSome (fun μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin p → Fin M → Fv F v ⊗[F] E) =>
      ∀ v, SdW F E σ M J (Fv F v) (psiV F ψ v) p (μv v)) fun μv =>
    AllSome (fun νv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (HermR (Fv F v) σ p) =>
      ∀ v, SdHerm F E σ (Fv F v) (psiV F ψ v) p (νv v)) fun νv =>
    AllSome (fun fibInf : HermR (Ainf F) σ p → Measure (Fin p → Fin M → Ainf F ⊗[F] E) =>
      IsFibreFamily μinf (gramR (Ainf F) σ J) Subtype.val
        {X | LinearIndependent (Ainf F ⊗[F] E) X} νinf Set.univ fibInf) fun fibInf =>
    AllSome (fun fibV : ∀ v : HeightOneSpectrum (𝓞 F),
        HermR (Fv F v) σ p → Measure (Fin p → Fin M → Fv F v ⊗[F] E) =>
      ∀ v, IsFibreFamily (μv v) (gramR (Fv F v) σ J) Subtype.val
        {X | LinearIndependent (Fv F v ⊗[F] E) X} (νv v) Set.univ (fibV v)) fun fibV =>
    Multipliable (fun v => ∫ X, Φv v X ∂(fibV v 0)) ∧
    meanC μ 𝓕 (thetaS F E σ M J Φ {X | LinearIndependent E X ∧ gramE σ J X = 0}) =
      (∫ X, Φinf X ∂(fibInf 0)) * ∏' v, ∫ X, Φv v X ∂(fibV v 0)

def SWc3 : Prop :=
  3 ≤ M → ∀ (x : Fin 1 → Fin M → E) (β : F), β ≠ 0 → hE σ J (x 0) (x 0) = algebraMap F E β →
    (∀ y : Fin 1 → Fin M → AF F ⊗[F] E, qR (AF F) σ J (y 0) = algebraMap F (AF F) β →
      ∃ g : HA (AF F) σ J, g • ratTup (AF F) x = y) →
    AllSome (IsCharAF F) fun ψ =>
    AllSome (IsHaarH F E σ M J) fun μ =>
    AllSome (IsXbetaMeasure F E σ M J ψ β) fun νX =>
    AllSome (fun μ' : Measure (Hstab (AF F) σ J x) =>
      μ'.IsHaarMeasure ∧ IsCompatible F E σ M J x μ μ' νX) fun μ' =>
    AllSome (IsFDH F E σ M J μ) fun 𝓕 =>
    AllSome (fun 𝓕' : Set (Hstab (AF F) σ J x) =>
      IsFundamentalDomain (HstabFin (AF F) σ J x) 𝓕' μ') fun 𝓕' => μ' 𝓕' = μ 𝓕

def SWc3G (G : GaugeFam F E σ) : Prop :=
  ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (J' : Matrix (Fin M) (Fin M) E)
    (x : Fin 1 → Fin (M + 1) → E) (β : F) (B : Matrix (Fin (M + 1)) (Fin M) E),
    3 ≤ M + 1 → IsHermND σ J → β ≠ 0 → hE σ J (x 0) (x 0) = algebraMap F E β →
    (∀ j, hE σ J (x 0) (fun i => B i j) = 0) →
    J' = Formalism.UG.cT (σ : E →+* E) B * J * B → IsHermND σ J' →
    (∀ y : Fin 1 → Fin (M + 1) → AF F ⊗[F] E,
      qR (AF F) σ J (y 0) = algebraMap F (AF F) β →
        ∃ g : HA (AF F) σ J, g • ratTup (AF F) x = y) →
    volHE G (M + 1) J = volHE G M J'

end Ext

def ForAllCM (P : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]
    (_σ : E →ₐ[F] E) (M : ℕ) (_J : Matrix (Fin M) (Fin M) E), Prop) : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
      P F E σ M J

def PoincareBundleExtensionCond : Prop := ForAllCM SWa1

def ZeroGainValuation : Prop := ForAllCM SWa2

def projection_sandwich_lattice : Prop := ForAllCM SWb1

def MassRatio₂ : Prop := ForAllCM SWb2

def LatticeChainWithoutLast : Prop := ForAllCM SWc1

def CoveringRadiusFunction : Prop := ForAllCM SWc2

def DefiniteLiftChain : Prop := ForAllCM SWc3

def Conclusion₂ : Prop := PoincareBundleExtensionCond ∧ ZeroGainValuation ∧ projection_sandwich_lattice ∧ MassRatio₂ ∧ LatticeChainWithoutLast ∧ CoveringRadiusFunction ∧ DefiniteLiftChain

section Data

open Formalism.BasicNotions

def AtD (D : D7) (P : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]
    (_σ : E →ₐ[F] E) (M : ℕ) (_J : Matrix (Fin M) (Fin M) E), Prop) : Prop :=
  letI := D.host.cmStar
  ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) D.host.E), IsHermND D.sp.cm.sig J →
    P D.host.F D.host.E D.sp.cm.sig M J

def CMFirstClauseA (D : D7) : Prop := AtD D SWa1
def CMFirstClauseB (D : D7) : Prop := AtD D SWa2
def CMSecondClauseA (D : D7) : Prop := AtD D SWb1
def CMSecondClauseB (D : D7) : Prop := AtD D SWb2
def CMThirdClauseA (D : D7) : Prop := AtD D SWc1
def CMThirdClauseB (D : D7) : Prop := AtD D SWc2
def CMThirdClauseAtData (D : D7) : Prop := AtD D SWc3

def CMClauses (D : D7) : Prop :=
  CMFirstClauseA D ∧ CMFirstClauseB D ∧ CMSecondClauseA D ∧ CMSecondClauseB D ∧ CMThirdClauseA D ∧ CMThirdClauseB D ∧ CMThirdClauseAtData D

theorem isCMExt_D (D : D7) :
    letI := D.host.cmStar; IsCMExt D.host.F D.host.E D.sp.cm.sig := by
  let _ := D.host.cmStar
  exact ⟨D.sp.cm.totReal, D.sp.cm.cmUnram.1, D.sp.cm.deg2, fun τ x => D.sp.cm.cmUnram.2.1 τ x⟩

def GaugeFamilyThirdClause (D : D7)
    (G : letI := D.host.cmStar; GaugeFam D.host.F D.host.E D.sp.cm.sig) : Prop :=
  letI := D.host.cmStar
  SWc3G D.host.F D.host.E D.sp.cm.sig G

def Stmt (D : D7) : Prop := Conclusion₂ ∧ CMClauses D

def ConclusionOnFamily {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∀ x (i : Fm.Ix x), Conclusion₂ ∧ CMClauses (Fm.D x i)
def KudlaFamilyStatement {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ConclusionOnFamily Fm

end Data

end Formalism.MainNotions.UnusedSlot34
