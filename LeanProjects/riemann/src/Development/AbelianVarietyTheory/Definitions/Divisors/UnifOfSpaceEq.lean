import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
import Formalism.LocalToGlobal.ProjectiveLattices.VolProofs
import Formalism.LocalToGlobal.CMDeterminantIdeals.StatementC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.NonvanishingNearMaximum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DefiniteBound
import Development.AbelianVarietyTheory.Proofs.HeightProofs.NoCommonZeroIffOfSec
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelLatB

noncomputable section

namespace GlobalTheory.LevGeo

open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure Laws (D : D7) (j : ℕ) {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l)
    (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r)
    (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) : Prop where

  inR : InR D j

  host : H.d = D.host.d ∧ (H.rt : D.host.E) = D.host.sqrtMinusD ∧ H.rt0 = D.host.φ₀ D.host.sqrtMinusD ∧
    ∀ t : D.what₂.Tau, DV.tauEmb D t (H.rt : D.host.E) = H.rt0

  dat : IsDatW D j Dw

  levA : l.A = 1

  unf : ∀ σ, GoodEmb c σ → IsUnf (U σ)

  chiTriv : ∀ σ, GoodEmb c σ → ∀ a n, Dom a n → ∀ k, ∀ γ ∈ ((U σ).X k).Γ, ((U σ).X k).χ (laU (U σ) a n k) γ = 1

  dictU : ∀ σ, GoodEmb c σ → ∃ Kf th hr, IsLevelK (D.sp.W j) l.M Kf ∧ (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧
    DictIsUnif (D.sp.W j) (dict σ) Kf th hr ∧
    ∀ g τ k, ‖dmin ((U σ).X (dict σ g).1).Gm (dict σ g).2 τ k‖ = 1

  modelW : ∀ σ, GoodEmb c σ → ∃ hr : (D.sp.W j).rank = D.R.r, ∀ k, ModelW (D.sp.W j) hr ((U σ).X k)

section Derived

variable {D : D7} {j : ℕ} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
  {c : Coeff l} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r}
  {dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r}

theorem Laws.evalWD (_ : Laws D j Xo c U dict) : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) :=
  GlobalTheory.TransferCompare.evalWD_framed Xo c

theorem Laws.unTest (_ : Laws D j Xo c U dict) : ∀ σ, GoodEmb c σ → ∀ k x,
    FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) ((U σ).un k x) := fun σ _ k x =>
  haveI : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ)
  GlobalTheory.TransferCompare.allTest_framed Xo c (CAt σ) ((U σ).un k x)

theorem Laws.xiAbs (h : Laws D j Xo c U dict) : ∀ σ, GoodEmb c σ → ∀ k (τ : D.host.E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = xiR D := by
  intro σ hσ k τ
  obtain ⟨hr, hm⟩ := h.modelW σ hσ
  rw [(hm k).2, map_neg, norm_neg]
  exact ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatB.norm_embedding_hostFormConstant_eq D τ

end Derived

def coreDict {D : D7} (T : Core D) (j : ℕ) (σ : T.Q.c.F →+* ℂ) (g : GA D (D.sp.W j)) : Σ k, Frame ((T.U j σ).X k).Ψ D.R.r :=
  open Classical in if h : T.V j σ = D.sp.W j then T.dict j σ (h ▸ g) else T.dict j σ 1

theorem unif_of_space_eq {D : D7} {r : ℕ} {C : Type} {X : C → Data D.host.E r} (V W : HSp D) (h : V = W)
    (dict : GA D V → Σ k, Frame (X k).Ψ r) (M : ℕ) (Kf : Subgroup (GA D V)) (hK : IsLevelK V M Kf)
    (hd : ∃ th hr, (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧ DictIsUnif V dict Kf th hr)
    (hu : ∀ g τ k, ‖dmin (X (dict g).1).Gm (dict g).2 τ k‖ = 1) :
    ∃ Kf th hr, IsLevelK W M Kf ∧ (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧
      DictIsUnif W (fun g => dict (h ▸ g)) Kf th hr ∧
      ∀ (g : GA D W) τ k, ‖dmin (X (dict (h ▸ g)).1).Gm (dict (h ▸ g)).2 τ k‖ = 1 := by
  subst h
  obtain ⟨th, hr, h1, h2⟩ := hd
  exact ⟨Kf, th, hr, hK, h1, h2, hu⟩

theorem laws_core (D : D7) (T : CoreJ D) (j : ℕ) (h : LawsJ T) (hj : InR D j) :
    Laws D j (T.Q.Xo j) T.Q.c (T.U j) (coreDict T.toCore j) where
  inR := hj
  host := h.pins.1
  dat := h.pins.2.2.2 j hj
  levA := h.pins.2.1.2
  unf := h.unf j hj
  chiTriv := h.chiTriv j hj
  dictU := fun σ hσ => by
    have hV := h.spaceW j hj σ hσ
    have e : coreDict T.toCore j σ = fun g => T.dict j σ (hV ▸ g) := by
      funext g; simp only [coreDict, dif_pos hV]
    rw [e, h.pins.2.1.1]
    exact unif_of_space_eq _ _ hV (T.dict j σ) _ (T.Kf j σ) (h.levelK j hj σ hσ) (h.dictU j hj σ hσ)
      (h.muUnit j hj σ hσ).2.2.2
  modelW := fun σ hσ => by
    have := h.modelW j hj σ hσ
    rw [h.spaceW j hj σ hσ] at this
    exact this

section Consts

variable (E : Type) [Field E] [NumberField E] (r : ℕ)

def chartRad (w : ℝ) : ℝ := 1 / (200 * (r : ℝ) ^ 3 * (w + fdeg E))

def multBd (ε : ℝ) : ℝ := (1 + 2 * (2 * (fdeg E : ℝ) * r) ^ 2 * dE E / ε) ^ (2 * fdeg E * r ^ 2)

def dimFl : ℕ := fdeg E * (r * (r - 1) / 2)

def locConst (w ε : ℝ) : ℝ :=
  8 * ((dimFl E r).factorial : ℝ) / (Real.pi * chartRad E r w ^ 2) ^ dimFl E r * multBd E r ε

def massLev (M : ℕ) : ℝ := GlobalTheory.UCls.massBd E r M (classNumber E * M ^ (2 * fdeg E))

def epsLev (d M : ℕ) (w : ℝ) : ℝ := epStar (2 * M * Real.sqrt d) (fdeg E) w 1

def supConst (d M : ℕ) (w : ℝ) : ℝ := locConst E r w (epsLev E d M w) * massLev E r M

def cmLen (q d M : ℕ) (w : ℝ) : ℝ :=
  frameBasisRadius r q (fdeg E) (dE E) (Real.sqrt (epsLev E d M w)) (3 * frameRadius w r / 5)

def lamSup (q d M : ℕ) (Om s t : ℝ) : ℝ :=
  (Formalism.L2.LamCM.pDeg Om + 1 / 2 * Real.log (cmLen E r q d M (s + t + 1))) * (s + t) +
    s * Real.log (r * cmLen E r q d M (s + t + 1))

def lamPet (q d M : ℕ) (Om s t : ℝ) : ℝ := lamSup E r q d M Om s t + 1 / 2 * Real.log (supConst E r d M (s + t + 1))

theorem one_le_multBd {ε : ℝ} (hε : 0 < ε) : 1 ≤ multBd E r ε := by
  unfold multBd
  refine one_le_pow₀ (le_add_of_nonneg_right ?_)
  have : 0 ≤ dE E := abs_nonneg _
  positivity

example : dimFl E 1 = 0 := by simp [dimFl]

example : dimFl E 2 = fdeg E := by simp [dimFl]

example (d M : ℕ) (w : ℝ) : epsLev E d M w ≤ 1 := min_le_left _ _

end Consts

def absA {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
    (a : (E →+* ℂ) × ℕ → ℕ) : ℕ := ∑ b : E →+* ℂ, ∑ i : Fin (Dw.mult b), a (b, i)

end GlobalTheory.LevGeo
