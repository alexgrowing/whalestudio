import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FormsAtZero

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeSaw GlobalTheory.Fam
namespace GlobalTheory.MiTop
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : D.what₂.Word} (f : _root_.GlobalTheory.Fam.FamilyCharacter W u)
def col0_alt (t : W.P.T) (φ : D.what₂.Mu u) : (f.t t).Col 0 := D.e0Tw u (W.P.I.tup t) (D.eMu u φ).1
def descentToLevelZero (n : ℕ) (h : 2 * n + 2 * 0 + 2 = D.R.m) (t : W.P.T) (F : (f.t t).CT) :
    SmT (W.Q.Rl.MY 0) →ₗ[ℂ] (GA D (Yc D 0) → ℂ) :=
  ((f.t t).dn (2 * n + 1) ((f.t t).ioT (2 * n) h F)).1
def LinkVanishes (d : _root_.GlobalTheory.MiTop.BottomData W u) : Prop :=
  ∀ n (h₀ : 0 + 2 * n + 2 = D.R.m) t φ, _root_.GlobalTheory.MiTop.col0_alt f t φ ∈ (f.t t).Ram 0 ∧
    ∀ G y v, (f.t t).per 0 n h₀ (_root_.GlobalTheory.MiTop.col0_alt f t φ) G y v = d.per φ G.1 y v
def LinkTailCondition : Prop :=
  ∀ n (h : 2 * n = D.R.m) t φ (F : Fin ((W.P.A3.side3 W.P.Ps W.P.ψs W.P.Zs).nV t) → D.what₂.LL)
    (F' : Fin ((W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Df1.nV t) → D.what₂.LL), HEq F F' → ∀ G : (f.t t).CT, G.1 = _root_.GlobalTheory.Fam.leadingLinearMap W t F' →
    (f.t t).tail (2 * n) h ((f.t t).col (2 * n) (_root_.GlobalTheory.MiTop.col0_alt f t φ)) G =
      D.what₂.perCol u (W.P.I.tup t) φ (W.P.I.jA t ((rV0 D W.P.A3.A W.P.Ps W.P.ψs t).mulVec F))
def LinkDescends : Prop :=
  ∀ n (h : 2 * n + 2 * 0 + 2 = D.R.m) t (F' : Fin ((W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Df1.nV t) → D.what₂.LL),
    ∃ G : (f.t t).CT, G.1 = _root_.GlobalTheory.Fam.leadingLinearMap W t F' ∧ _root_.GlobalTheory.MiTop.descentToLevelZero f n h t G = _root_.GlobalTheory.MiTop.rowFormOfTuple W t F'
def LinkSurjective : Prop :=
  ∀ n (h : 2 * n + 2 * 0 + 2 = D.R.m), ∀ T ∈ _root_.GlobalTheory.MiTop.BaseRowSpace W, ∃ G : (f.t W.P.A3.A.μ0).CT, _root_.GlobalTheory.MiTop.descentToLevelZero f n h W.P.A3.A.μ0 G = T
def LinkCommutes : Prop :=
  ∀ n (h : 2 * n = D.R.m), ∃ (S : D.what₂.Mu u ≃ₗ[ℂ] D.what₂.Mu u) (r : ℝ) (s : ℂ), 0 < r ∧ (∀ φ, ‖S φ‖ = r * ‖φ‖) ∧ s ≠ 0 ∧
    ∀ t φ F, (f.t t).tail (2 * n) h ((f.t t).up n (_root_.GlobalTheory.MiTop.col0_alt f t φ)) F =
      s * (f.t t).tail (2 * n) h ((f.t t).col (2 * n) (_root_.GlobalTheory.MiTop.col0_alt f t (S φ))) F
variable (W)
def CoveredCondition : Prop :=
  ∀ w (p : ℕ), p.Prime → (∃ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q (W.Q.Rl.mu w), ((p : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → (p : 𝓞 D.what₂.LL) ∉ w.asIdeal
open Formalism.L2.Host in
theorem served' : _root_.GlobalTheory.MiTop.CoveredCondition W := by
  rintro w p hp ⟨PP, hP, h1⟩ h2
  have lev := W.Q.charW.base.lev
  have hr : ¬ (W.Q.Rl.xiH (W.Q.Rl.mu w)).UnrAt PP := (lev.Q_ram _ PP).2 (Or.inl hP)
  have hl : Formalism.EigenvalueLevelCeiling.plc w = p :=
    (Nat.prime_dvd_prime_iff_eq (Formalism.EigenvalueLevelCeiling.plc_prime w) hp).1
      ((ringChar.spec _ p).1 (by simpa using Ideal.Quotient.eq_zero_iff_mem.2 h2))
  by_cases hw : w ∈ W.Q.Rl.twPl
  · obtain ⟨ψ, Q, hψ, e⟩ := W.Q.charW.tup.mu_on w hw
    have e' : W.Q.Rl.xiH (W.Q.Rl.mu w) = W.Q.Rl.C.delAt (Formalism.EigenvalueLevelCeiling.plc w) * ψ := e
    have key : ∀ q : ℕ, q.Prime → OverP D.host q PP → q = p := fun q hq ho => by
      by_contra hne
      have hc : IsCoprime ((q : ℕ) : 𝓞 D.host.E) ((p : ℕ) : 𝓞 D.host.E) :=
        Nat.Coprime.cast ((Nat.coprime_primes hq hp).2 hne)
      obtain ⟨a, b, hab⟩ := hc
      have ho' : ((q : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := ho
      exact PP.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
        (hab ▸ PP.asIdeal.add_mem (PP.asIdeal.mul_mem_left _ ho') (PP.asIdeal.mul_mem_left _ h1)))
    have hd : (W.Q.Rl.C.delAt (Formalism.EigenvalueLevelCeiling.plc w)).UnrAt PP := by
      unfold CharFrame.delAt
      split_ifs with hh
      · refine W.Q.Rl.C.isDel'.unr PP fun ho => D.host.pde_ne ?_
        rw [← hh, hl, key _ D.host.pde'_prime ho]
      · exact W.Q.Rl.C.isDel.unr PP fun ho => hh (by rw [hl, key _ D.host.pde_prime ho])
    refine hr fun x hx => ?_
    have a1 := hd x hx
    have a2 := hψ.atl PP (hl ▸ h1) x
    rw [e']
    change (W.Q.Rl.C.delAt (Formalism.EigenvalueLevelCeiling.plc w)).loc PP x * ψ.loc PP x = 1
    rw [a1, a2, mul_one]
  · have e : W.Q.Rl.mu w = W.P.A3.A.μ0 := W.Q.charW.tup.mu_off w hw
    refine hr fun x _ => ?_
    rw [e, show W.Q.Rl.xiH W.P.A3.A.μ0 = 1 from lev.xi_base]
    rfl
theorem not_mem_Q_base' (PP : HeightOneSpectrum (𝓞 D.host.E)) : PP ∉ (_root_.GlobalTheory.Fam.pk_z W).Q W.P.A3.A.μ0 := by
  intro hP
  have lev := W.Q.charW.base.lev
  refine (lev.Q_ram _ PP).2 (Or.inl hP) fun x _ => ?_
  rw [show W.Q.Rl.xiH W.P.A3.A.μ0 = 1 from lev.xi_base]
  rfl
end GlobalTheory.MiTop
end
end
