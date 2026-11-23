import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPeriodSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicPointUnitaryGroupGramOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadsGaussianSmulConstUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorNormalisingVectorNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfIsFiniteAdelicPointSameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteAdelicPointOfUnitaryGroupMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteAdelicPointOfUnitaryGroupOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicCharacterEqOneSplitInertStatement

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.VacTriv

theorem one_suppSplit {D : D7} {N : ℕ} : Formalism.MainNotions.StandardLatticesGL3.SuppSplit D (1 : GL (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) := by
  intro q _ _ i j k
  refine ⟨1, one_pos, Nat.coprime_one_left q, 0, zero_mem _, ?_⟩
  simp

theorem one_suppInert {D : D7} {N : ℕ} : Formalism.MainNotions.StandardLatticesGL3.SuppInert D (1 : GL (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) := by
  intro q _ _ i j k
  refine ⟨1, one_pos, Nat.coprime_one_left q, 0, zero_mem _, ?_⟩
  simp

theorem one_intG {D : D7} {N : ℕ} : Formalism.MainNotions.StandardLatticesGL3.IntG D (1 : GL (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) := by
  intro i j
  simp only [inv_one, Units.val_one, Matrix.one_apply]
  split_ifs
  · exact ⟨one_mem _, one_mem _⟩
  · exact ⟨zero_mem _, zero_mem _⟩

theorem vacuum_const_trivial : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∀ (e0 : VC D a d → ℂ) (W : WeilO D cc δ a d e0) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
  GlobalTheory.NormSum.Inp D → ∀ t0 : ℂ, Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → Even (a * d) → oddE0 D cc δ t0 a d e0 →
  HasFinPart χS W.chV W.ep → HasFinPart χT W.chV' (-W.ep') →
  ∀ f₀ : WO S T → ℂ, Reads ψ θ hS hT cc δ r e0 f₀ →
  (∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g : GA D S) (h : GA D T), IsFinPt S g x → IsFinPt T h y →
  ∃ c : ℂ, Reads ψ θ hS hT cc δ r (c • W.Om x y e0) (om (g, h) f₀)) →
  (∀ (x₁ : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y₁ : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g₁ : GA D S) (h₁ : GA D T)
    (x₂ : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y₂ : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g₂ : GA D S) (h₂ : GA D T) (c₁ c₂ : ℂ),
    IsFinPt S g₁ x₁ → IsFinPt T h₁ y₁ → IsFinPt S g₂ x₂ → IsFinPt T h₂ y₂ →
    Reads ψ θ hS hT cc δ r (c₁ • W.Om x₁ y₁ e0) (om (g₁, h₁) f₀) → Reads ψ θ hS hT cc δ r (c₂ • W.Om x₂ y₂ e0) (om (g₂, h₂) f₀) →
    Reads ψ θ hS hT cc δ r ((c₁ * c₂) • W.Om (x₁ * x₂) (y₁ * y₂) e0) (om (g₁ * g₂, h₁ * h₂) f₀)) →
  (∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g : GA D S) (h : GA D T), IsFinPt S g x → IsFinPt T h y →
  Formalism.MainNotions.StandardLatticesGL3.SuppSplit D (x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) → Formalism.MainNotions.StandardLatticesGL3.SuppSplit D (y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) →
  Reads ψ θ hS hT cc δ r (W.Om x y e0) (om (g, h) f₀)) →
  (∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g : GA D S) (h : GA D T), IsFinPt S g x → IsFinPt T h y →
  Formalism.MainNotions.StandardLatticesGL3.SuppInert D (x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) → Formalism.MainNotions.StandardLatticesGL3.SuppInert D (y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) →
  Formalism.MainNotions.StandardLatticesGL3.IntG D (x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) → Formalism.MainNotions.StandardLatticesGL3.IntG D (y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) →
  Reads ψ θ hS hT cc δ r (W.Om x y e0) (om (g, h) f₀)) →
  ∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g : GA D S) (h : GA D T), IsFinPt S g x → IsFinPt T h y →
  Reads ψ θ hS hT cc δ r (W.Om x y e0) (om (g, h) f₀) := by
  intro D ψ θ S T a d hS hT cc δ r hset e0 W χS χT om hW hInp t0 ht0 hev hodd hχS hχT f₀ hf₀ hline hmul hsplit hinert
  subst hS
  subst hT
  have hnz : ∀ x y, W.Om x y e0 ≠ 0 := GlobalTheory.T.weilOperator_normalisingVector_ne_zero cc δ t0 e0 W hset.crv hodd
  have huniq : ∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D S.rank) (y : Formalism.MainNotions.StandardLatticesGL3.GA D T.rank) (g : GA D S) (h : GA D T) (c c' : ℂ),
      Reads ψ θ rfl rfl cc δ r (c • W.Om x y e0) (om (g, h) f₀) →
      Reads ψ θ rfl rfl cc δ r (c' • W.Om x y e0) (om (g, h) f₀) → c = c' :=
    fun x y g h c c' h1 h2 => GlobalTheory.T.readsGaussian_smul_const_unique ψ θ S T rfl rfl cc δ r hset _ _ c c' (hnz x y) h1 h2
  have hone : ∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D S.rank) (y : Formalism.MainNotions.StandardLatticesGL3.GA D T.rank) (g : GA D S) (h : GA D T),
      Reads ψ θ rfl rfl cc δ r (W.Om x y e0) (om (g, h) f₀) →
      Reads ψ θ rfl rfl cc δ r ((1 : ℂ) • W.Om x y e0) (om (g, h) f₀) := fun x y g h hr => by rwa [one_smul]
  have p1S : IsFinPt S (1 : GA D S) (1 : Formalism.MainNotions.StandardLatticesGL3.GA D S.rank) := GlobalTheory.T.isFiniteAdelicPointOfUnitaryGroup_one S rfl
  have p1T : IsFinPt T (1 : GA D T) (1 : Formalism.MainNotions.StandardLatticesGL3.GA D T.rank) := GlobalTheory.T.isFiniteAdelicPointOfUnitaryGroup_one T rfl
  have exS : ∀ x : Formalism.MainNotions.StandardLatticesGL3.GA D S.rank, ∃ g, IsFinPt S g x :=
    fun x => GlobalTheory.BotFormula.exists_isFinPt_of_gram_one S hset.gS x rfl
  have exT : ∀ y : Formalism.MainNotions.StandardLatticesGL3.GA D T.rank, ∃ h, IsFinPt T h y :=
    fun y => GlobalTheory.BotFormula.exists_isFinPt_of_gram_one T hset.gT y rfl
  choose gx hgx using exS
  choose hy hhy using exT
  have gx1 : gx 1 = 1 := GlobalTheory.T.eq_of_isFiniteAdelicPoint_same S _ _ 1 (hgx 1) p1S
  have hy1 : hy 1 = 1 := GlobalTheory.T.eq_of_isFiniteAdelicPoint_same T _ _ 1 (hhy 1) p1T
  have gxm : ∀ x₁ x₂, gx x₁ * gx x₂ = gx (x₁ * x₂) :=
    fun x₁ x₂ => GlobalTheory.T.eq_of_isFiniteAdelicPoint_same S _ _ _ (GlobalTheory.T.isFiniteAdelicPointOfUnitaryGroup_mul S _ _ _ _ (hgx x₁) (hgx x₂)) (hgx (x₁ * x₂))
  have hym : ∀ y₁ y₂, hy y₁ * hy y₂ = hy (y₁ * y₂) :=
    fun y₁ y₂ => GlobalTheory.T.eq_of_isFiniteAdelicPoint_same T _ _ _ (GlobalTheory.T.isFiniteAdelicPointOfUnitaryGroup_mul T _ _ _ _ (hhy y₁) (hhy y₂)) (hhy (y₁ * y₂))
  choose cS hcS using fun x => hline x 1 (gx x) 1 (hgx x) p1T
  choose cT hcT using fun y => hline 1 y 1 (hy y) p1S (hhy y)

  have cS1 : cS 1 = 1 := by
    have h1 := hcS 1
    rw [gx1] at h1
    exact huniq _ _ _ _ _ _ h1 (hone _ _ _ _ (hsplit 1 1 1 1 p1S p1T (by simpa using one_suppSplit) (by simpa using one_suppSplit)))
  have cSm : ∀ x₁ x₂, cS (x₁ * x₂) = cS x₁ * cS x₂ := by
    intro x₁ x₂
    have h1 := hmul x₁ 1 (gx x₁) 1 x₂ 1 (gx x₂) 1 (cS x₁) (cS x₂) (hgx _) p1T (hgx _) p1T (hcS x₁) (hcS x₂)
    rw [mul_one, mul_one, gxm] at h1
    exact huniq _ _ _ _ _ _ (hcS (x₁ * x₂)) h1
  have cT1 : cT 1 = 1 := by
    have h1 := hcT 1
    rw [hy1] at h1
    exact huniq _ _ _ _ _ _ h1 (hone _ _ _ _ (hsplit 1 1 1 1 p1S p1T (by simpa using one_suppSplit) (by simpa using one_suppSplit)))
  have cTm : ∀ y₁ y₂, cT (y₁ * y₂) = cT y₁ * cT y₂ := by
    intro y₁ y₂
    have h1 := hmul 1 y₁ 1 (hy y₁) 1 y₂ 1 (hy y₂) (cT y₁) (cT y₂) p1S (hhy _) p1S (hhy _) (hcT y₁) (hcT y₂)
    rw [mul_one, mul_one, hym] at h1
    exact huniq _ _ _ _ _ _ (hcT (y₁ * y₂)) h1
  let νS : Formalism.MainNotions.StandardLatticesGL3.GA D S.rank →* ℂ := { toFun := cS, map_one' := cS1, map_mul' := cSm }
  let νT : Formalism.MainNotions.StandardLatticesGL3.GA D T.rank →* ℂ := { toFun := cT, map_one' := cT1, map_mul' := cTm }
  have tS : ∀ x, cS x = 1 := by
    intro x
    have := GlobalTheory.T.unitaryAdelicCharacter_eq_one_split_inert S hset.gS νS.toHomUnits
      (fun k hk => Units.ext (by
        rw [MonoidHom.coe_toHomUnits, Units.val_one]
        exact huniq _ _ _ _ _ _ (hcS k) (hone _ _ _ _ (hsplit k 1 (gx k) 1 (hgx k) p1T hk (by simpa using one_suppSplit)))))
      (fun k hk hki => Units.ext (by
        rw [MonoidHom.coe_toHomUnits, Units.val_one]
        exact huniq _ _ _ _ _ _ (hcS k) (hone _ _ _ _ (hinert k 1 (gx k) 1 (hgx k) p1T hk (by simpa using one_suppInert)
          hki (by simpa using one_intG))))) x
    have := congrArg Units.val this
    rwa [MonoidHom.coe_toHomUnits, Units.val_one] at this
  have tT : ∀ y, cT y = 1 := by
    intro y
    have := GlobalTheory.T.unitaryAdelicCharacter_eq_one_split_inert T hset.gT νT.toHomUnits
      (fun k hk => Units.ext (by
        rw [MonoidHom.coe_toHomUnits, Units.val_one]
        exact huniq _ _ _ _ _ _ (hcT k) (hone _ _ _ _ (hsplit 1 k 1 (hy k) p1S (hhy k) (by simpa using one_suppSplit) hk))))
      (fun k hk hki => Units.ext (by
        rw [MonoidHom.coe_toHomUnits, Units.val_one]
        exact huniq _ _ _ _ _ _ (hcT k) (hone _ _ _ _ (hinert 1 k 1 (hy k) p1S (hhy k) (by simpa using one_suppInert) hk
          (by simpa using one_intG) hki)))) y
    have := congrArg Units.val this
    rwa [MonoidHom.coe_toHomUnits, Units.val_one] at this
  intro x y g h hg hh
  have eg : g = gx x := GlobalTheory.T.eq_of_isFiniteAdelicPoint_same S _ _ x hg (hgx x)
  have eh : h = hy y := GlobalTheory.T.eq_of_isFiniteAdelicPoint_same T _ _ y hh (hhy y)
  subst eg eh
  have h1 := hmul x 1 (gx x) 1 1 y 1 (hy y) (cS x) (cT y) (hgx x) p1T p1S (hhy y) (hcS x) (hcT y)
  rw [tS, tT] at h1
  simp only [mul_one, one_mul, one_smul] at h1
  exact h1

end GlobalTheory.VacTriv
