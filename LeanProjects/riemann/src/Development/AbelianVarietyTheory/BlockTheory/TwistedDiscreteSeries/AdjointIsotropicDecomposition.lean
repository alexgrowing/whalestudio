import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsGrowthSobNeTopOfIsAutFunSm
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory
open scoped ENNReal

namespace GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def adj (D : D7) {m n : ℕ} (A : Matrix (Fin m) (Fin n) D.host.E) : Matrix (Fin n) (Fin m) D.host.E :=
  Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) A

structure IsIsoSplit (V V' : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) : Prop where
  frame : IsIsoFrame V C
  isom : adj D B * V.gram * B = V'.gram
  orth : adj D C * V.gram * B = 0
  rank : V.rank = V'.rank + 2 * r

def ratMx (D : D7) (m n : ℕ) : AddSubgroup (Mx D m n) :=
  ((incA D).toAddMonoidHom.mapMatrix (m := Fin m) (n := Fin n)).range

def isoPart (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) (y : Mx D W.rank r) : WO V W :=
  HMul.hMul (y : Matrix (Fin W.rank) (Fin r) (AE D)) ((adj D C * V.gram).map (incA D))

def midPart (V V' W : HSp D) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (x : WO V' W) : WO V W :=
  HMul.hMul (x : Matrix (Fin W.rank) (Fin V'.rank) (AE D)) ((V'.gram⁻¹ * adj D B * V.gram).map (incA D))

def res (V V' W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r))
    (f : WO V W → ℂ) : WO V' W → ℂ :=
  fun x => ∫ y in 𝓨, f (isoPart V W C y + midPart V V' W B x) ∂μ

def Compatible (ψ : AddChar (AF D.host.F) ℂ) (V V' W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ))
    (ω' : GA D V' × GA D W →* Module.End ℂ (WO V' W → ℂ)) : Prop :=
  ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 →
    ∀ h f, IsThetaFunO ψ V W f → res V V' W C B μ 𝓨 (ω (1, h) f) = ω' (1, h) (res V V' W C B μ 𝓨 f)

def ConstTermFormula (ψ : AddChar (AF D.host.F) ℂ) (V V' W : HSp D) {r : ℕ}
    (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E)
    (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ))
    (ω' : GA D V' × GA D W →* Module.End ℂ (WO V' W → ℂ)) : Prop :=
  ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 →
  ∀ (ν : Measure (GA D W)) (𝓕 : Set (GA D W)), ν.IsHaarMeasure → IsFundamentalDomain (GQ W) 𝓕 ν →
  ∀ (κ : Measure (NI V C)) (𝓝 : Set (NI V C)), κ.IsHaarMeasure → IsFundamentalDomain (NIQ V C) 𝓝 κ →
  ∀ F : GA D W → ℂ, GlobalTheory.Grow.RapidDec W F → IsCuspFun W F →
  ∀ f, IsThetaFunO ψ V W f → ∀ g : GA D V,
    κ 𝓝 ≠ ∞ ∧
    (∀ x, IntegrableOn (fun y => ω (g, 1) f (isoPart V W C y + midPart V V' W B x)) 𝓨 μ) ∧
    IsThetaFunO ψ V' W (res V V' W C B μ 𝓨 (ω (g, 1) f)) ∧
    (∀ g₁, IntegrableOn (fun h => thetaKO ω g₁ h f * F h) 𝓕 ν) ∧
    IntegrableOn (fun h => thetaKO ω' 1 h (res V V' W C B μ 𝓨 (ω (g, 1) f)) * F h) 𝓕 ν ∧
    IntegrableOn (fun n : NI V C => Lift.liftInt ν 𝓕 (thetaKO ω) f F ((n : GA D V) * g)) 𝓝 κ ∧
    ∫ n in 𝓝, Lift.liftInt ν 𝓕 (thetaKO ω) f F ((n : GA D V) * g) ∂κ =
      ((κ 𝓝).toReal : ℂ) * Lift.liftInt ν 𝓕 (thetaKO ω') (res V V' W C B μ 𝓨 (ω (g, 1) f)) F 1

def TowerConstTermOfCompatible (D : D7) : Prop :=
  ∀ (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B →
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT χS' χT' : (AE D)ˣ →* Circle)
    (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ω' : GA D V' × GA D W →* Module.End ℂ (WO V' W → ℂ)),
    IsWeilDatumO ψ V W χS χT ω → IsWeilDatumO ψ V' W χS' χT' ω' → Compatible ψ V V' W C B ω ω' →
    ConstTermFormula ψ V V' W C B ω ω'

def CompatibleOfSameChar (D : D7) : Prop :=
  ∀ (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B →
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT χT' : (AE D)ˣ →* Circle)
    (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ω' : GA D V' × GA D W →* Module.End ℂ (WO V' W → ℂ)),
    IsWeilDatumO ψ V W χS χT ω → IsWeilDatumO ψ V' W χS χT' ω' → Compatible ψ V V' W C B ω ω'

def TowerConstTerm (D : D7) : Prop :=
  ∀ (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B →
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT χT' : (AE D)ˣ →* Circle)
    (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ω' : GA D V' × GA D W →* Module.End ℂ (WO V' W → ℂ)),
    IsWeilDatumO ψ V W χS χT ω → IsWeilDatumO ψ V' W χS χT' ω' → ConstTermFormula ψ V V' W C B ω ω'

def spaceThree (D : D7) : HSp D := Examples₂.stdSpace Examples₂.star_isIntegral 3 ![false, true, false] 2 1

def spaceOne (D : D7) : HSp D := Examples₂.stdSpace Examples₂.star_isIntegral 1 ![false] 1 0

theorem isIsoSplit_three (D : D7) :
    IsIsoSplit (spaceThree D) (spaceOne D) (r := 1)
      (Matrix.of fun (i : Fin 3) _ => (![1, 1, 0] : Fin 3 → D.host.E) i)
      (Matrix.of fun (i : Fin 3) _ => (![0, 0, 1] : Fin 3 → D.host.E) i) := by
  have hg : ∀ i j : Fin 3, (spaceThree D).gram i j =
      if i = j then (Examples₂.sgn (![false, true, false] i) : D.host.E) else 0 :=
    Examples₂.stdSpace_gram_apply Examples₂.star_isIntegral 3 ![false, true, false] 2 1
  have hg' : ∀ i j : Fin 1, (spaceOne D).gram i j = if i = j then (Examples₂.sgn (![false] i) : D.host.E) else 0 :=
    Examples₂.stdSpace_gram_apply Examples₂.star_isIntegral 1 ![false] 1 0
  refine ⟨⟨one_pos, ?_, ?_⟩, ?_, ?_, rfl⟩
  · refine linearIndependent_unique_iff.2 fun h => ?_
    have := congrFun h (0 : Fin 3)
    exact one_ne_zero this
  · funext a b
    change ∑ j : Fin 3, (∑ i : Fin 3, D.sp.cm.sig ((![1, 1, 0] : Fin 3 → D.host.E) i) * (spaceThree D).gram i j) *
      (![1, 1, 0] : Fin 3 → D.host.E) j = 0
    simp [Fin.sum_univ_three, hg, Examples₂.sgn]
  · funext (a : Fin 1) (b : Fin 1)
    change ∑ j : Fin 3, (∑ i : Fin 3, D.sp.cm.sig ((![0, 0, 1] : Fin 3 → D.host.E) i) * (spaceThree D).gram i j) *
      (![0, 0, 1] : Fin 3 → D.host.E) j = _
    rw [hg', Subsingleton.elim a 0, Subsingleton.elim b 0]
    simp [Fin.sum_univ_three, hg, Examples₂.sgn]
  · funext a b
    change ∑ j : Fin 3, (∑ i : Fin 3, D.sp.cm.sig ((![1, 1, 0] : Fin 3 → D.host.E) i) * (spaceThree D).gram i j) *
      (![0, 0, 1] : Fin 3 → D.host.E) j = 0
    simp [Fin.sum_univ_three, hg, Examples₂.sgn]

end GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition

end
