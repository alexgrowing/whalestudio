import Mathlib
import Formalism.LocalToGlobal.LatticeGeometry.ViewsC
import Formalism.SharpRestriction.Divisibility.PrinLevClass
import Formalism.SharpRestriction.Divisibility.LatticeTransfer
import Formalism.SharpRestriction.Divisibility.PlaceRankTwoOne
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Formalism.SharpRestriction.Divisibility.ZetaProductPairs
import Formalism.SharpRestriction.Divisibility.InnerProductFormulaField
import Formalism.SharpRestriction.Divisibility.KudlaSiegelWeil
import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.SubsingletonRankIndicatorIff
import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.WeightAlgebra
import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.LiftErrorLocal
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.ExampleSatisfiesConditionsAtFive
import Formalism.LocalRingCardinality.DataExtra
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsProvisionalShimX
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SubRkOfPsiOfEqRkOfCEmb
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsProvisionalDivX

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Geo NumberField IsDedekindDomain

open Formalism.L2.Geo.PadPkg (md)

namespace GlobalTheory.VarietyModelRecord

structure VarietyWithModels (D : D7)
    (jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)) : Type 1 where

  shv : DV.ShimX D.what₂.Tau
  phiFr_unram : ∀ p y x, DV.UnramE D p → shv.phiFr p y x = shv.phiDR p y x

  Mp : ∀ (p : ℕ) [Fact p.Prime], PlL D p → Type

  model : ∀ (p : ℕ) [Fact p.Prime] (la : PlL D p), Mp p la →
    DV.Mdl D p shv.N (DV.rkOf (DV.PsiOf D (jC p la)) shv.N shv.j)

  CurveM : ∀ (p : ℕ) [Fact p.Prime] (la : PlL D p), Mp p la → Type

  degM : ∀ (p : ℕ) [Fact p.Prime] (la : PlL D p) (z : Mp p la), CurveM p la z →
    DV.Rt D.what₂.Tau shv.N → ℝ

  htMdl : ∀ (p : ℕ) [Fact p.Prime] (la : PlL D p), Mp p la

  htCurve : ∀ (p : ℕ) [Fact p.Prime], shv.CurveHT p ≃ Σ la : PlL D p, CurveM p la (htMdl p la)
  htCurve_deg : ∀ (p : ℕ) [Fact p.Prime] (c : shv.CurveHT p),
    degM p (htCurve p c).1 (htMdl p (htCurve p c).1) (htCurve p c).2 = shv.degHT p c

variable {D : D7} {G : DV.Geo D.what₂.LL} {Lev : Type}

def ofDatum (F : ShimFam D G Lev) (w : Dat D Lev) (h : w.Indef) : VarietyWithModels D F.jC where
  shv := toShimX (F.U w) h (F.levPr w.κ) (F.levPr_prime w.κ)
  phiFr_unram := (F.U w).pad.phiFr_unram
  Mp := fun p _ la => (F.U w).pad.Mp p la
  model := fun p _ la => md (F.U w).pad p la
  CurveM := fun p _ la => (F.U w).pad.CurveM p la
  degM := fun p _ la => (F.U w).pad.degM p la
  htMdl := fun p _ la => (F.U w).pad.htMdl p la
  htCurve := fun _ _ => Equiv.refl _
  htCurve_deg := fun _ _ _ => rfl

def filler (D : D7) (jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)) (r : ℕ)
    (lev : Finset ℕ) (hlev : ∀ p ∈ lev, p.Prime) : VarietyWithModels D jC where
  shv := provisionalShimX D.what₂.Tau (max r 2) 1 lev le_rfl (by omega) hlev
  phiFr_unram := fun _ _ _ _ => rfl
  Mp := fun _ _ _ => Unit
  model := fun p _ la _ => trivialAdmissibleModel D p (jC p la) (max r 2) 1 (by omega)
  CurveM := fun _ _ _ _ => Empty
  degM := fun _ _ _ _ _ _ => 0
  htMdl := fun _ _ _ => ()
  htCurve := fun _ _ =>
    { toFun := fun c => Empty.elim c
      invFun := fun c => c.2
      left_inv := fun c => Empty.elim c
      right_inv := fun c => Empty.elim c.2 }
  htCurve_deg := fun _ _ c => Empty.elim c

open Classical in

def atSpace (F : ShimFam D G Lev) (S : letI := D.host.cmStar; HSpace D.host.E) (κ : Lev) :
    VarietyWithModels D F.jC :=
  letI := D.host.cmStar
  if h : ∃ w : Dat D Lev, w.S = S ∧ w.κ = κ ∧ w.Indef then ofDatum F h.choose h.choose_spec.2.2
  else filler D F.jC S.rank (F.levPr κ) (F.levPr_prime κ)

theorem atSpace_datum (F : ShimFam D G Lev) (w : Dat D Lev) (h : w.Indef) :
    atSpace F w.S w.κ = ofDatum F w h := by
  have hex : ∃ w' : Dat D Lev, w'.S = w.S ∧ w'.κ = w.κ ∧ w'.Indef := ⟨w, rfl, rfl, h⟩
  have key : ∀ (w' : Dat D Lev) (h' : w'.Indef), w' = w → ofDatum F w' h' = ofDatum F w h := by
    rintro w' h' rfl
    rfl
  unfold atSpace
  rw [dif_pos hex]
  exact key _ _ (dat_ext D _ _ hex.choose_spec.1 hex.choose_spec.2.1)

theorem atSpace_cases (F : ShimFam D G Lev) (S : letI := D.host.cmStar; HSpace D.host.E)
    (κ : Lev) : (∃ (w : Dat D Lev) (h : w.Indef), w.S = S ∧ w.κ = κ ∧
      atSpace F S κ = ofDatum F w h) ∨
      atSpace F S κ = filler D F.jC (letI := D.host.cmStar; S.rank) (F.levPr κ)
        (F.levPr_prime κ) := by
  by_cases hex : ∃ w : Dat D Lev, w.S = S ∧ w.κ = κ ∧ w.Indef
  · obtain ⟨w, rfl, rfl, h⟩ := hex
    exact Or.inl ⟨w, h, rfl, rfl, atSpace_datum F w h⟩
  · right
    unfold atSpace
    rw [dif_neg hex]

theorem atSpace_N (F : ShimFam D G Lev) (S : letI := D.host.cmStar; HSpace D.host.E) (κ : Lev)
    (h2 : letI := D.host.cmStar; 2 ≤ S.rank) :
    (atSpace F S κ).shv.N = (letI := D.host.cmStar; S.rank) := by
  rcases atSpace_cases F S κ with ⟨w, h, rfl, rfl, e⟩ | e
  · rw [e]; rfl
  · rw [e]; exact max_eq_left h2

theorem atSpace_lev (F : ShimFam D G Lev) (S : letI := D.host.cmStar; HSpace D.host.E) (κ : Lev) :
    (atSpace F S κ).shv.lev = F.levPr κ := by
  rcases atSpace_cases F S κ with ⟨w, h, rfl, rfl, e⟩ | e
  · rw [e]; rfl
  · rw [e]; rfl

def reindexWeight (Tau : Type) {m n : ℕ} (e : m = n) :
    (Tau → Fin n → ℤ) →+ (Tau → Fin m → ℤ) where
  toFun := fun la τ i => la τ (Fin.cast e i)
  map_zero' := rfl
  map_add' := fun _ _ => rfl

def record (X₀ : DivX D) (F : ShimFam D G Lev)
    (iM : ∀ j (c : (F.Uw j).Comp), (X₀.MjH j).V →ₗ[D.what₂.LL] G.Fn ((F.Uw j).alg.Yv c))
    (hiM : ∀ j c x, iM j c x ∈ G.H0 ((F.Uw j).alg.Yv c) ((F.Uw j).alg.Lw c
      (fun τ i => DV.kapW D j τ (Fin.cast (datW_N D F.κg j) i))))
    (dH : ∀ j, (F.Uw j).Comp → D.what₂.Tau → ℝ) : DivX D :=
  letI := D.host.cmStar
  { X₀ with
    geo := G
    Lev := Lev
    levPr := F.levPr
    shv := fun S κ => (atSpace F S κ).shv
    shv_N := atSpace_N F
    shv_lev := atSpace_lev F
    PlP := fun p _ => PlL D p
    plpFin := fun p _ => finPl D p
    plpNe := fun p _ => plL_ne D p
    wtP := fun p _ => wtL D p
    divisorWeight_nonneg := fun p _ => wtL_nonneg D p
    divisorWeight_sum := fun p _ => wtL_sum D p
    plP := fun p _ => ProvisionalDivX.placeEquiv D p
    divisorWeight_def := fun p _ => ProvisionalDivX.wtL_eq_ramIdx_mul D p
    jC := F.jC
    Mp := fun S κ p _ => (atSpace F S κ).Mp p
    md := fun S κ p _ => (atSpace F S κ).model p
    phiFr_unram := fun S κ => (atSpace F S κ).phiFr_unram
    CurveM := fun S κ p _ => (atSpace F S κ).CurveM p
    degM := fun S κ p _ => (atSpace F S κ).degM p
    htMdl := fun S κ p _ => (atSpace F S κ).htMdl p
    htCurve := fun S κ p _ => (atSpace F S κ).htCurve p
    htCurve_deg := fun S κ p _ => (atSpace F S κ).htCurve_deg p
    Comp := fun j => (F.Uw j).Comp
    compFin := fun j => (F.Uw j).compFin
    degHH := dH
    Yv := fun j => (F.Uw j).alg.Yv
    Ybd := fun j => (F.Uw j).alg.Ybd
    Lw := fun j c => ((F.Uw j).alg.Lw c).comp (reindexWeight D.what₂.Tau (datW_N D F.κg j))
    iMj := iM
    iMj_mem := hiM }

theorem models_of_eq (F : ShimFam D G Lev) (w : Dat D Lev) (h : w.Indef)
    (A : VarietyWithModels D F.jC) (e : A = ofDatum F w h) (p : ℕ) [Fact p.Prime] :
    (∀ la, A.Mp p la = (F.U w).pad.Mp p la) ∧
    (∀ la, HEq (A.model p la) (md (F.U w).pad p la)) ∧
    (∀ la, HEq (A.CurveM p la) ((F.U w).pad.CurveM p la)) ∧
    (∀ la, HEq (A.degM p la) ((F.U w).pad.degM p la)) ∧
    (∀ la, HEq (A.htMdl p la) ((F.U w).pad.htMdl p la)) ∧
    ∀ (c : A.shv.CurveHT p) (c' : (F.U w).pad.CurveHT p), HEq c c' →
      (A.htCurve p c).1 = c'.1 ∧ HEq (A.htCurve p c).2 c'.2 := by
  subst e
  refine ⟨fun _ => rfl, fun _ => HEq.rfl, fun _ => HEq.rfl, fun _ => HEq.rfl, fun _ => HEq.rfl, ?_⟩
  intro c c' hc
  obtain rfl : c = c' := eq_of_heq hc
  exact ⟨rfl, HEq.rfl⟩

theorem record_tied (X₀ : DivX D) (F : ShimFam D G Lev)
    (iM : ∀ j (c : (F.Uw j).Comp), (X₀.MjH j).V →ₗ[D.what₂.LL] G.Fn ((F.Uw j).alg.Yv c))
    (hiM : ∀ j c x, iM j c x ∈ G.H0 ((F.Uw j).alg.Yv c) ((F.Uw j).alg.Lw c
      (fun τ i => DV.kapW D j τ (Fin.cast (datW_N D F.κg j) i))))
    (dH : ∀ j, (F.Uw j).Comp → D.what₂.Tau → ℝ) :
    TiedX (jC := F.jC) (ng := F.ng) (record X₀ F iM hiM dH) F.levPr F.levPr_prime F.κg
      (fun _ _ => Equiv.refl _) F.U (fun _ _ _ => Equiv.refl _) where
  shv :=
    { lev := rfl
      shv := fun w h => congrArg VarietyWithModels.shv (atSpace_datum F w h) }
  pl :=
    { wt := fun _ _ _ => rfl
      jc := fun _ _ _ => rfl
      mp := fun w h p _ => (models_of_eq F w h _ (atSpace_datum F w h) p).1
      md := fun w h p _ => (models_of_eq F w h _ (atSpace_datum F w h) p).2.1
      curveM := fun w h p _ => (models_of_eq F w h _ (atSpace_datum F w h) p).2.2.1
      degM := fun w h p _ => (models_of_eq F w h _ (atSpace_datum F w h) p).2.2.2.1
      htMdl := fun w h p _ => (models_of_eq F w h _ (atSpace_datum F w h) p).2.2.2.2.1
      htCurve := fun w h p _ => (models_of_eq F w h _ (atSpace_datum F w h) p).2.2.2.2.2 }
  geo :=
    { yv := fun _ _ _ _ => rfl
      ybd := fun _ _ _ _ => HEq.rfl
      lw := fun _ _ _ _ _ => HEq.rfl }
  lev_κg := F.levPr_κg

end GlobalTheory.VarietyModelRecord

namespace GlobalTheory

theorem exists_divX_tied : ∀ (D : D7) (X₀ : DivX D) (G : DV.Geo D.what₂.LL) (Lev : Type) (F : ShimFam D G Lev) (iM : ∀ j (c : (F.Uw j).Comp), (X₀.MjH j).V →ₗ[D.what₂.LL] G.Fn ((F.Uw j).alg.Yv c)), (∀ j c x, iM j c x ∈ G.H0 ((F.Uw j).alg.Yv c) ((F.Uw j).alg.Lw c (fun τ i => DV.kapW D j τ (Fin.cast (datW_N D F.κg j) i)))) → ∃ (X : DivX D) (hG : X.geo = G) (hL : X.Lev = Lev), X.MjH = X₀.MjH ∧ X.kapR = X₀.kapR ∧ X.logLam = X₀.logLam ∧ X.Qp = X₀.Qp ∧ ∃ (jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)) (ng : NgPkg) (U : ∀ w : Dat D X.Lev, ShimU D X.geo jC ng w) (lp : X.Lev → Finset ℕ) (hl : ∀ κ, ∀ p ∈ lp κ, p.Prime) (κg : X.Lev) (ePl : ∀ (p : ℕ) [Fact p.Prime], X.PlP p ≃ PlL D p) (eC : ∀ j, 1 ≤ j → j ≤ D.R.m → X.Comp j ≃ (U (datW D κg j)).Comp), HEq U F.U ∧ HEq κg F.κg ∧ TiedX X lp hl κg ePl U eC := by
  intro D X₀ G Lev F iM hiM
  exact ⟨VarietyModelRecord.record X₀ F iM hiM (fun _ _ _ => 0), rfl, rfl, rfl, rfl, rfl, rfl,
    F.jC, F.ng, F.U, F.levPr, F.levPr_prime, F.κg, fun _ _ => Equiv.refl _,
    fun _ _ _ => Equiv.refl _, HEq.rfl, HEq.rfl, VarietyModelRecord.record_tied X₀ F iM hiM _⟩

end GlobalTheory

end
