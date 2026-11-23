import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPushDown
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.JointExample
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PGlueRegularised
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MvPolynomial Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ContDiff

section Objects

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {K : Type} [Fintype K]
  {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type}
  [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)] {D : ComponentData II Ψ K ι Ω E}

def regularizedFlagPullbackLine (Pl : PlueckerData D) (H : HodgeData D) {M : XModel D} (S : LogLogRegularisationSetting M D.Xo (muLine H)) (B : ℕ)
    (t : ℝ) : HermLine Pl.ιY :=
  IndefiniteRowSideFullHecke.Inter.pullHerm Pl.isBlockMap_xV (muReg H S B t)

def flagFun (Pl : PlueckerData D) (H : HodgeData D) (Ba : AdaptedBasis H) {M : XModel D}
    (S : LogLogRegularisationSetting M D.Xo (muLine H)) (B : ℕ) {r : ℕ} (c : Fin r → ℝ)
    (N : Fin r → Fin D.flagDim0 → HermLine Pl.ιY) (t : ℝ) : ℝ :=
  ∑ m, c m * II _ Pl.ιY (Pl.flagPrime Ba) (D.n + 1 + D.flagDim0)
    (Fin.append (fun _ : Fin (D.n + 1) => regularizedFlagPullbackLine Pl H S B t) (N m))

def PPmuFib (Pl : PlueckerData D) (H : HodgeData D) (Ba : AdaptedBasis H) {M : XModel D}
    (S : LogLogRegularisationSetting M D.Xo (muLine H)) (B : ℕ) {r : ℕ} (c : Fin r → ℝ)
    (N : Fin r → Fin D.flagDim0 → HermLine Pl.ιY) : ℝ :=
  limUnder (𝓝[>] 0) (flagFun Pl H Ba S B c N)

def fibNum {Pl : PlueckerData D} {H : HodgeData D} {Ba : AdaptedBasis H} (G : GenFibre Pl.xV (Pl.flagPrime Ba))
    (J : IFamily G.Φ (fibreIdx Pl.ιY (Sum.inl : K → K ⊕ (Ψ × Fin (D.N - 1))))) {r : ℕ} (c : Fin r → ℝ)
    (N : Fin r → Fin D.flagDim0 → HermLine Pl.ιY) : ℝ :=
  ∑ m, c m * (J (fibreIdeal Sum.inl G) D.flagDim0 (fun j => fibreDeg Sum.inl (N m j).a) : ℝ)

end Objects

def AgreementOnBase.Statement : Prop :=
  ∀ (II : IntersectionSystem), IsFullIntersectionSystem II →
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
    (D : ComponentData II Ψ K ι Ω E) (Pl : PlueckerData D) (H : HodgeData D) (Ba : AdaptedBasis H)
    (M : XModel D) (S : LogLogRegularisationSetting M D.Xo (muLine H)) (B : ℕ) (G : GenFibre Pl.xV (Pl.flagPrime Ba))
    (J : IFamily G.Φ (fibreIdx Pl.ιY (Sum.inl : K → K ⊕ (Ψ × Fin (D.N - 1))))) (r : ℕ) (c : Fin r → ℝ)
    (N : Fin r → Fin D.flagDim0 → HermLine Pl.ιY),
    IsFieldIntersection J → (∀ m j, IsSmoothHerm (N m j)) →
    (∀ᶠ t in 𝓝[>] (0 : ℝ), IsSmoothHerm (muReg H S B t)) → ArLimExists H S B →
    Tendsto (flagFun Pl H Ba S B c N) (𝓝[>] 0) (𝓝 (fibNum G J c N * arLim H S B)) ∧
      PPmuFib Pl H Ba S B c N = fibNum G J c N * arLim H S B

theorem AgreementOnBase.proof (hPD : PushDown.Statement) : AgreementOnBase.Statement := by
  intro II hII Ψ _ _ K _ ι _ Ω _ _ E _ _ D Pl H Ba M S B G J r c N hJ hN hsm hlim
  obtain ⟨L, hL⟩ := hlim
  have hPush := (hPD II hII Ψ K ι Ω E D Pl H Ba).1
  have heq : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      fibNum G J c N * arLimFun H S B t = flagFun Pl H Ba S B c N t := by
    filter_upwards [hsm] with t ht
    unfold flagFun fibNum
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hPush G J (fun _ => muReg H S B t) (fun _ => regularizedFlagPullbackLine Pl H S B t) (N m) hJ (fun _ => ht)
      (fun _ => IndefiniteRowSideFullHecke.Inter.isPullHerm_pullHerm _ _) (hN m)]
    unfold arLimFun
    ring
  have hT : Tendsto (flagFun Pl H Ba S B c N) (𝓝[>] 0) (𝓝 (fibNum G J c N * L)) :=
    (hL.const_mul _).congr' heq
  have hA : arLim H S B = L := hL.limUnder_eq
  rw [hA]
  exact ⟨hT, hT.limUnder_eq⟩

section Inhabitants

open GroundTheory.Heights₂.Heights (CP)
open GroundTheory.Heights₂.Heights.Regular.ProjectiveLine
open Line

abbrev lineS : LogLogRegularisationSetting lineModel (lineData zeroSystem zero_hII).Xo (muLine (lineHodge zeroSystem zero_hII)) :=
  lineRegT zeroSystem zero_hII

end Inhabitants

end GroundTheory.Heights₂.Heights.AnalyticLimit

end
