import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmCurveBaseChangeComp
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HolomorphicUniformizationTangentUnimodularRiemann
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.SecJet GlobalTheory.CovTop

noncomputable section

namespace GlobalTheory.MBModel

open GlobalTheory.PullHermitian

section Val

variable {X Y : Scheme.{0}}

theorem rig_wchart_iff (x : Sp ℂ ⟶ X) (L : LB Y) (φ : X ⟶ Y) (ε : ℤ) (j : PUnit → L.ι) :
    ⊤ ≤ x ⁻¹ᵁ (L.LinComb (K := PUnit) (fun _ => φ) (fun _ => ε)).U j ↔ ⊤ ≤ (x ≫ φ) ⁻¹ᵁ L.U (j PUnit.unit) :=
  GlobalTheory.ThetaFn.le_wchart_unique L x φ j

theorem rig_inf_iff (x : Sp ℂ ⟶ X) (U V : X.Opens) : ⊤ ≤ x ⁻¹ᵁ (U ⊓ V) ↔ ⊤ ≤ x ⁻¹ᵁ U ∧ ⊤ ≤ x ⁻¹ᵁ V :=
  ⟨fun h => ⟨fun _ hp => (h hp).1, fun _ hp => (h hp).2⟩, fun h => inf_of x h.1 h.2⟩

theorem rig_val_ne (x : Sp ℂ ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)ˣ) : valAt' x U f.val ≠ 0 := by
  rw [valAt'_eq_unitVal x h]; exact Units.ne_zero _

theorem rig_val_linComb (x : Sp ℂ ⟶ X) (L : LB Y) (φ : X ⟶ Y) (ε : ℤ) (j j' : PUnit → L.ι)
    (h : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ L.U (j PUnit.unit)) (h' : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ L.U (j' PUnit.unit)) :
    valAt' x ((L.LinComb (K := PUnit) (fun _ => φ) (fun _ => ε)).U j ⊓
        (L.LinComb (K := PUnit) (fun _ => φ) (fun _ => ε)).U j')
      ((L.LinComb (K := PUnit) (fun _ => φ) (fun _ => ε)).g j j').val =
      valAt' (x ≫ φ) (L.U (j PUnit.unit) ⊓ L.U (j' PUnit.unit)) (L.g (j PUnit.unit) (j' PUnit.unit)).val ^ ε := by
  have a := inf_of x ((rig_wchart_iff x L φ ε j).2 h) ((rig_wchart_iff x L φ ε j').2 h')
  rw [valAt'_eq_unitVal x a, valAt'_eq_unitVal _ (inf_of _ h h'), ← Units.val_zpow_eq_zpow_val]
  exact congrArg Units.val (unitVal_linComb x L φ ε (j PUnit.unit) (j' PUnit.unit) a (inf_of _ h h'))

theorem rig_val_iso (x : Sp ℂ ⟶ X) {M N : LB X} (w : LB.Iso N M) (hw : w.IsGen) (i i' : M.ι) (j j' : N.ι)
    (hi : ⊤ ≤ x ⁻¹ᵁ M.U i) (hi' : ⊤ ≤ x ⁻¹ᵁ M.U i') (hj : ⊤ ≤ x ⁻¹ᵁ N.U j) (hj' : ⊤ ≤ x ⁻¹ᵁ N.U j') :
    valAt' x (M.U i ⊓ N.U j) (w.s (i, j)).val =
      valAt' x (M.U i ⊓ M.U i') (M.g i i').val * (valAt' x (N.U j ⊓ N.U j') (N.g j j').val)⁻¹ *
        valAt' x (M.U i' ⊓ N.U j') (w.s (i', j')).val := by
  have hV := inf_of x (inf_of x hi hj) (inf_of x hi' hj')
  exact (GlobalTheory.PowUnif.val_gen hw x (i, j) (i', j') hV).trans
    (congrArg (· * _) (GlobalTheory.PowUnif.val_div_g M N x i i' j j' hV))

theorem exists_rig_const {Z S : Scheme.{0}} (x : Sp ℂ ⟶ X) (ψ : X ⟶ Y) (φ : Y ⟶ Z) (s : Sp ℂ ⟶ S) (e : S ⟶ Z)
    (he : (x ≫ ψ) ≫ φ = s ≫ e) (L : LB X) (L' : LB Y) (M : LB Z) (n : ℕ) (r : LB.Gen (M.pull e)) (hr : r.IsGen)
    (w : LB.Iso (M.pull φ) L') (hw : w.IsGen) (w' : LB.Iso (L'.pull ψ) (lbPow L n)) (hw' : w'.IsGen)
    (fr : L.ι → ℂ) (hne : ∀ i, ⊤ ≤ x ⁻¹ᵁ L.U i → fr i ≠ 0)
    (hco : ∀ i i', ⊤ ≤ x ⁻¹ᵁ (L.U i ⊓ L.U i') → fr i = valAt' x (L.U i ⊓ L.U i') (L.g i i').val * fr i') :
    ∃ ρ : ℂ, (∀ (k : (lbPow L n).ι) (j : (L'.pull ψ).ι) (p : PUnit → M.ι),
      ⊤ ≤ x ⁻¹ᵁ ((lbPow L n).U k ⊓ (L'.pull ψ).U j) →
      ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ (L'.U (j PUnit.unit) ⊓ (M.pull φ).U p) →
      valAt' x ((lbPow L n).U k ⊓ (L'.pull ψ).U j) (w'.s (k, j)).val *
        valAt' (x ≫ ψ) (L'.U (j PUnit.unit) ⊓ (M.pull φ).U p) (w.s (j PUnit.unit, p)).val *
        valAt' s ((M.pull e).U p) (r.s p).val = ρ * fr (k PUnit.unit) ^ n) ∧ ρ ≠ 0 := by
  by_cases hex : ∃ (k : (lbPow L n).ι) (j : (L'.pull ψ).ι) (p : PUnit → M.ι),
      ⊤ ≤ x ⁻¹ᵁ ((lbPow L n).U k ⊓ (L'.pull ψ).U j) ∧ ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ (L'.U (j PUnit.unit) ⊓ (M.pull φ).U p)
  swap
  · exact ⟨1, fun k j p h₁ h₂ => (hex ⟨k, j, p, h₁, h₂⟩).elim, one_ne_zero⟩
  obtain ⟨k', j', p', h₁', h₂'⟩ := hex
  have hk : ∀ k : (lbPow L n).ι, ⊤ ≤ x ⁻¹ᵁ (lbPow L n).U k → ⊤ ≤ (x ≫ 𝟙 X) ⁻¹ᵁ L.U (k PUnit.unit) :=
    fun k h => (rig_wchart_iff x L _ _ k).1 h
  have hp : ∀ p : PUnit → M.ι, ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ (M.pull φ).U p → ⊤ ≤ (s ≫ e) ⁻¹ᵁ M.U (p PUnit.unit) :=
    fun p h => he ▸ (rig_wchart_iff _ M _ _ p).1 h
  have hs : ∀ p : PUnit → M.ι, ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ (M.pull φ).U p → ⊤ ≤ s ⁻¹ᵁ (M.pull e).U p :=
    fun p h => (rig_wchart_iff _ M _ _ p).2 (hp p h)
  obtain ⟨a', b'⟩ := (rig_inf_iff _ _ _).1 h₁'
  obtain ⟨c', d'⟩ := (rig_inf_iff _ _ _).1 h₂'
  have f' : fr (k' PUnit.unit) ≠ 0 := hne _ (by simpa using hk k' a')
  refine ⟨valAt' x ((lbPow L n).U k' ⊓ (L'.pull ψ).U j') (w'.s (k', j')).val *
        valAt' (x ≫ ψ) (L'.U (j' PUnit.unit) ⊓ (M.pull φ).U p') (w.s (j' PUnit.unit, p')).val *
        valAt' s ((M.pull e).U p') (r.s p').val / fr (k' PUnit.unit) ^ n, fun k j p h₁ h₂ => ?_,
    div_ne_zero (mul_ne_zero (mul_ne_zero (rig_val_ne x h₁' _) (rig_val_ne _ h₂' _)) (rig_val_ne s (hs p' d') _))
      (pow_ne_zero _ f')⟩
  obtain ⟨a, b⟩ := (rig_inf_iff _ _ _).1 h₁
  obtain ⟨c, d⟩ := (rig_inf_iff _ _ _).1 h₂
  have e₁ := rig_val_iso x w' hw' k k' j j' a a' b b'
  have e₂ := rig_val_iso (x ≫ ψ) w hw (j PUnit.unit) (j' PUnit.unit) p p' c c' d d'
  have e₃ := GlobalTheory.PowUnif.val_gen hr s p p' (inf_of s (hs p d) (hs p' d'))
  have g₁ := rig_val_linComb x L (𝟙 X) n k k' (hk k a) (hk k' a')
  have g₂ := rig_val_linComb x L' ψ 1 j j' c c'
  have g₃ := rig_val_linComb (x ≫ ψ) M φ 1 p p' (he ▸ hp p d) (he ▸ hp p' d')
  have g₄ := rig_val_linComb s M e 1 p p' (hp p d) (hp p' d')
  have n₂ := rig_val_ne (x ≫ ψ) (inf_of _ c c') (L'.g (j PUnit.unit) (j' PUnit.unit))
  have n₃ := rig_val_ne (s ≫ e) (inf_of _ (hp p d) (hp p' d')) (M.g (p PUnit.unit) (p' PUnit.unit))
  have f := hco (k PUnit.unit) (k' PUnit.unit) (inf_of x (by simpa using hk k a) (by simpa using hk k' a'))
  rw [Category.comp_id, zpow_natCast] at g₁
  rw [he] at g₃
  rw [zpow_one] at g₂ g₃ g₄
  rw [e₁, e₂, e₃, g₁, g₂, g₃, g₄, f, mul_pow]
  field_simp

end Val

theorem exists_rigIs_ne_zero : ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp K)) (AA : Over (Sp (𝓞 K))) [GrpObj AA] [IsCommMonObj AA] (φ : P.A.left ⟶ AA.left) (MM : RigLB AA) (N : ℕ) (w : LB.Iso (MM.L.pull φ) (lbPow P.L N)) (σ : K →+* ℂ) (Q : Out.PolAV (Sp ℂ)) (ψσ : Q.A.left ⟶ P.A.left) (wσ : LB.Iso ((lbPow P.L N).pull ψσ) (lbPow Q.L N)) (g : ℕ) (u : HolUnif Q.A Q.L g), GlobalTheory.MBModel.IsModel w → GlobalTheory.IsPolFibre σ P Q ψσ → wσ.IsGen → ∃ ρ' : ℂ, GlobalTheory.MBModel.RigIs w σ wσ u ρ' ∧ ρ' ≠ 0 := by
  intro K _ _ P AA _ _ φ MM N w σ Q ψσ wσ g u hM hF hw
  have he : ((u.ex 0).left ≫ ψσ) ≫ φ = spMap (σ.comp (algebraMap (𝓞 K) K)) ≫ eSec AA := by
    have h₁ := GlobalTheory.PolBaseChange.eSec_comm hF.2.1
    have h₂ := GlobalTheory.PolBaseChange.eSec_comm hM.2.2.2.1
    rw [GlobalTheory.PowUnif.ex_zero, GlobalTheory.PowUnif.one_left, h₁, Geo.Tor.spMap_comp]
    exact (Category.assoc _ _ _).trans ((congrArg (spMap σ ≫ ·) h₂).trans (Category.assoc _ _ _).symm)
  exact exists_rig_const (S := (𝟙_ (Over (Sp (𝓞 K)))).left) (u.ex 0).left ψσ φ _ (eSec AA) he Q.L (lbPow P.L N) MM.L N
    MM.rig MM.rigGen w hM.2.2.2.2.2.2.1 wσ hw (fun i => u.fr i 0) (fun i => u.fr_ne i 0) (fun i i' => u.fr_compat i i' 0)

end GlobalTheory.MBModel

end
