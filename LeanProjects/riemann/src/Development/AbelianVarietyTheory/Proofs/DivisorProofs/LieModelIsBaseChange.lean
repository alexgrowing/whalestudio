import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegRel
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenMovePow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilIsDiagRoot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilCommutatorPairingTorsionGeometricPoint
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitOnInjectiveOfCommRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsMultiplicativeGroup
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DiagSqAxes

theorem lift_mul_lift₂ {S : Scheme.{0}} {A B T : Over S} [GrpObj A] [GrpObj B] (x x' : T ⟶ A) (y y' : T ⟶ B) :
    lift x y * lift x' y' = lift (x * x') (y * y') := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [MonObj.mul_comp]

theorem weilIs_one_of_gen {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A)
    {L : LB A.left} (hL : L.IsLB) (t : L.Gen) (ht : t.IsGen) {N : ℕ} {T : Over S} {x y : T ⟶ A}
    (hx : x ^ N = 1) (hy : y ^ N = 1) : Out.WeilIs A L N x y 1 := by
  have hG := GlobalTheory.globalFns_holds
  have hM : (GlobalTheory.UU.trivRig A).L.IsLB := Out.Inh.trivLB_isLB _
  have h1 : Out.WeilIs A (GlobalTheory.UU.trivRig A).L N (x ≫ 𝟙 A) (y ≫ 𝟙 A) 1 := by
    rw [Category.comp_id, Category.comp_id]
    exact (GlobalTheory.UU.cubWeil_iff_weilIs (c := GlobalTheory.UU.trivCub A) hG hA hx hy 1).1 (GlobalTheory.UU.cubWeil_triv hx hy)
  have hw : LBIso (lbPow L 1) ((GlobalTheory.UU.trivRig A).L.pull (Over.Hom.left (𝟙 A))) :=
    LBIso.trans (GlobalTheory.isLB_lbPow hL 1) hL (pull_isLB hM _) (GlobalTheory.lbIso_lbPow_one hL)
      (GlobalTheory.ZH.AbelianFibre.lbIso_of_gens t ht (GlobalTheory.UU.unitGen _ _) (GlobalTheory.UU.unitGen_isGen _ _))
  have h2 := GlobalTheory.WeilIsogeny.weilIs_pull_hom hG hA hL hM (𝟙 A) hw h1
  simp only [Nat.cast_one, _root_.mul_one] at h2
  exact h2

theorem weilIs_axis {S : Scheme.{0}} {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
    (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) {P : LB B.left} (hP : P.IsLB) (ψ : A ⟶ B) [IsMonHom ψ]
    (ht : ∃ t : (P.pull ψ.left).Gen, t.IsGen) (κ : Type) [Field κ] [IsAlgClosed κ] (y : Sp κ ⟶ S) (N : ℕ)
    (hN : 0 < N) (hNk : (N : κ) ≠ 0) (a b : Over.mk y ⟶ A) (ha : a ^ N = 1) (hb : b ^ N = 1) :
    Out.WeilIs B P N (a ≫ ψ) (b ≫ ψ) 1 := by
  have hG := GlobalTheory.globalFns_holds
  obtain ⟨t, ht⟩ := ht
  have hL : (P.pull ψ.left).IsLB := pull_isLB hP _
  have pa : (a ≫ ψ) ^ N = 1 := by rw [← MonObj.pow_comp, ha, MonObj.one_comp]
  have pb : (b ≫ ψ) ^ N = 1 := by rw [← MonObj.pow_comp, hb, MonObj.one_comp]
  obtain ⟨c', hc'⟩ := GlobalTheory.WeilGeomPt.exists_weilIs_geomPt S B P hB hP κ y N hN hNk _ _ pa pb
  have h1 := GlobalTheory.WeilIsogeny.weilIs_pull_hom hG hA hL hP ψ (GlobalTheory.lbIso_lbPow_one hL) hc'
  simp only [Nat.cast_one, _root_.mul_one] at h1
  have h2 := weilIs_one_of_gen hA hL t ht ha hb
  rwa [GlobalTheory.CommutatorPairing.weilIs_unique hG hA hL h1 h2] at hc'

end GlobalTheory.DiagSqAxes

namespace GlobalTheory.DiagSqAxes

theorem weilIs_diag_sq : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (P : LB (G2 A).left), P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (y : Sp κ ⟶ S) (N : ℕ), 0 < N → (N : κ) ≠ 0 → ∀ (a b : Over.mk y ⟶ A), a ^ N = 1 → b ^ N = 1 → ∀ (c : (Γ((Over.mk y).left, ⊤))ˣ), Out.WeilIs (G2 A) P N (lift a 1) (lift 1 b) c → Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) N a b (c ^ 2) := by
  intro S A _ _ hA P hP h₂ h₁ hsym κ _ _ y N hN hNk a b ha hb c hc
  have hG := GlobalTheory.globalFns_holds
  have hAA : IsAbelianScheme (G2 A) := AbelianSchemeGerms.isAbelianScheme_tensor _ _ hA hA
  have e11 : Out.WeilIs (G2 A) P N (lift a 1) (lift b 1) 1 := by
    have h := weilIs_axis hA hAA hP (lift (𝟙 A) (1 : A ⟶ A)) h₁ κ y N hN hNk a b ha hb
    simpa only [comp_lift, Category.comp_id, MonObj.comp_one] using h
  have e22 : Out.WeilIs (G2 A) P N (lift 1 a) (lift 1 b) 1 := by
    have h := weilIs_axis hA hAA hP (lift (1 : A ⟶ A) (𝟙 A)) h₂ κ y N hN hNk a b ha hb
    simpa only [comp_lift, Category.comp_id, MonObj.comp_one] using h
  have e21 : Out.WeilIs (G2 A) P N (lift 1 a) (lift b 1) c := by
    have hw : LBIso (lbPow P 1) (P.pull (lift (snd A A) (fst A A)).left) :=
      LBIso.trans (GlobalTheory.isLB_lbPow hP 1) hP (pull_isLB hP _) (GlobalTheory.lbIso_lbPow_one hP) hsym
    have h' : Out.WeilIs (G2 A) P N (lift 1 a ≫ lift (snd A A) (fst A A)) (lift b 1 ≫ lift (snd A A) (fst A A)) c := by
      simpa only [comp_lift, lift_fst, lift_snd] using hc
    have h := GlobalTheory.WeilIsogeny.weilIs_pull_hom hG hAA hP hP _ hw h'
    simp only [Nat.cast_one, _root_.mul_one] at h
    exact h
  have r1 := GlobalTheory.DiagPairing.weilIs_mul_left hG hAA hP e11 e21
  have r2 := GlobalTheory.DiagPairing.weilIs_mul_left hG hAA hP hc e22
  rw [lift_mul_lift₂] at r1 r2
  have s := GlobalTheory.DiagPairing.weilIs_mul_left hG hAA hP (GlobalTheory.CommPairing.weilIs_symm hP r1)
    (GlobalTheory.CommPairing.weilIs_symm hP r2)
  have s' := GlobalTheory.CommPairing.weilIs_symm hP s
  rw [lift_mul_lift₂] at s'
  simp only [_root_.mul_one, _root_.one_mul] at s'
  have hd : Out.WeilIs (G2 A) P N (a ≫ lift (𝟙 A) (𝟙 A)) (b ≫ lift (𝟙 A) (𝟙 A)) (c ^ 2) := by
    simp only [comp_lift, Category.comp_id]
    convert s' using 1
    rw [← _root_.mul_inv, inv_inv, pow_two]
  have hD : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  have h := GlobalTheory.WeilIsogeny.weilIs_pull_hom hG hA hD hP (lift (𝟙 A) (𝟙 A)) (GlobalTheory.lbIso_lbPow_one hD) hd
  simp only [Nat.cast_one, _root_.mul_one] at h
  exact h

end GlobalTheory.DiagSqAxes
