import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinorAtMulTriangular
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open MvPolynomial Formalism.BasicNotions.DV
open GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag
open GlobalTheory.Cartier GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.WholeFlag
open IsDedekindDomain GlobalTheory.WholeFlag.Glue GlobalTheory.WholeFlag.GlueProof
open scoped Matrix
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.WholeFlag.GlueProof

theorem genAt_mul_chartC_unitAt : ∀ {F : Type} [Field F] [NumberField F] {Y : Var F} {C : CxSt F} {g : ℕ} (A : Fin g → Adl C Y) (p : ℕ) (V : Cover Y) (W : Y.X.Opens) {ι : Type} (U : ι → V.X.Opens) (H : ι → Matrix (Fin (g + g)) (Fin g) V.G.functionField) (J : Matrix (Fin (g + g)) (Fin (g + g)) ℤ) (d : Y.X → Fin g → Y.Fnˣ) (T : Y.X → Matrix (Fin g) (Fin g) Y.Fn) (L : Fin g → LB V.X) (m : ℕ) (r : ∀ i, ((L i).pull V.j).ι → V.G.functionFieldˣ), Hyp A p V W U H J d T L m r → ∀ (q : Idx ι L) (i : Fin g) (z : V.G), V.j z ∈ chartOpen V U H L m r q → UnitAt z (V.φ (genAt (A i).D (V.π z)) * chartC V H q i) := by
  intro F _ _ Y C g A p V W ι U H J d T L m r h q i z hz
  obtain ⟨_, _, _, _, hm, _, _, hTT, hGd0, hrl0, _, hHz0, _⟩ := h
  obtain ⟨hzU, hzL, hzmin⟩ := hz
  set Tz := T (V.π z) with hTz
  have hT : Tz.BlockTriangular id := (hTT (V.π z)).1
  have hTd : ∀ j, Tz j j = (d (V.π z) j : Y.Fn) := (hTT (V.π z)).2
  have hHz : ∀ r l, RegAt z ((H q.1 * (Tz.map V.φ)⁻¹) r l) := hHz0 q.1 z hzU
  have hGd : ∀ j, UnitAt z (V.φ (genAt (A j).D (V.π z) * d (V.π z) j)) := fun j => V.unitAt_φ (hGd0 j (V.π z))
  have hrl : ∀ j, UnitAt z (V.φ (genAt (A j).D (V.π z) ^ m) * (frames r q.2.2 j : V.G.functionField)) := by
    intro j
    apply hrl0 j (fun _ => q.2.2 j) z
    simp only [LB.pull, LB.LinComb, LB.wchart]
    simpa using hzL j
  have hmin : ∀ (k : ℕ) (hk : k ≤ g), UnitAt z (minorAt (H q.1 * (Tz.map V.φ)⁻¹) k hk (q.2.1 k)) := by
    intro k hk
    exact (unitAt_minor_of_nmin V (H q.1) (frames r q.2.2) m hm k hk (q.2.1 k) Tz (d (V.π z))
      (fun j => genAt (A j).D (V.π z)) hT hTd hHz hGd hrl).2 (unitAt_symm V |>.1 (hzmin k hk))
  have hd : ∀ j, (Tz.map V.φ) j j ≠ 0 := fun j => by
    rw [Matrix.map_apply, hTd, map_ne_zero]; exact Units.ne_zero _
  have hTm := blockTriangular_map V hT
  set a := minorAt (H q.1 * (Tz.map V.φ)⁻¹) ((i : ℕ) + 1) i.2 (q.2.1 ((i : ℕ) + 1)) with ha
  set b := minorAt (H q.1 * (Tz.map V.φ)⁻¹) (i : ℕ) i.2.le (q.2.1 (i : ℕ)) with hb
  have hua : UnitAt z a := hmin _ _
  have hub : UnitAt z b := hmin _ _
  set P := ∏ j : Fin (i : ℕ), (Tz.map V.φ) (Fin.castLE i.2.le j) (Fin.castLE i.2.le j) with hP
  have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => hd _
  have e1 : minorAt (H q.1) ((i : ℕ) + 1) i.2 (q.2.1 ((i : ℕ) + 1)) = a * (P * V.φ (d (V.π z) i)) := by
    rw [minor_eq_mul_inv (H q.1) _ hTm hd _ i.2, Fin.prod_univ_castSucc]
    congr 2
    have : Fin.castLE i.2 (Fin.last (i : ℕ)) = i := Fin.ext rfl
    rw [this, Matrix.map_apply, hTd]
  have e2 : minorAt (H q.1) (i : ℕ) i.2.le (q.2.1 (i : ℕ)) = b * P := minor_eq_mul_inv (H q.1) _ hTm hd _ i.2.le _
  have hdi : V.φ (d (V.π z) i) ≠ 0 := by rw [map_ne_zero]; exact Units.ne_zero _
  have hval : (chartC V H q i : V.G.functionField) = a / b * V.φ (d (V.π z) i) := by
    unfold chartC
    rw [dif_pos, Units.val_mk0, e1, e2]
    · field_simp [hub.ne_zero, hP0]
    · rw [e1, e2]
      exact div_ne_zero (mul_ne_zero hua.ne_zero (mul_ne_zero hP0 hdi)) (mul_ne_zero hub.ne_zero hP0)
  have e3 : V.φ (genAt (A i).D (V.π z)) * (chartC V H q i : V.G.functionField) =
      V.φ (genAt (A i).D (V.π z) * d (V.π z) i) * a * b⁻¹ := by
    rw [hval, map_mul]; ring
  rw [e3]
  exact ((hGd i).mul hua).mul hub.inv

end GlobalTheory.WholeFlag.GlueProof
