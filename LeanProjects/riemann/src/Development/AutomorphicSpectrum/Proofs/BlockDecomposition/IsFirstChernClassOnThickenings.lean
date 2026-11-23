import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.KatzMessingTheorem.BaseChange
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NegOnePowBoundaryTermsCancel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.B DividedPowers CompanionTheory.KM.G4

namespace GlobalTheory.CompanionTheory.KMGys

variable {k : Type} [Field k] (b : Base) (ht : b.t = 1) (κ : k →+* b.R ⧸ b.I)

def covFun (Y : SmV k) {ι : Type} (U : ι → Y.X.Opens) : b.Fun where
  ι := Empty
  A := ι
  Pt := (schFn Y.q).ptK κ
  str y := y.1.1
  str_map _ _ := rfl
  In i _ y := ⊤ ≤ y.1.2 ⁻¹ᵁ U i
  in_map := @fun _ _ _ φ y h => le_preimage_map φ y.1.2 h
  f _ i := i.elim
  f_map i := i.elim
  g _ _ i := i.elim
  g_map i := i.elim
  f_eq i := i.elim
  g_self i := i.elim
  g_comp i := i.elim
  prod_f {_ _ y} _ := by simp [ht]
  prod_g _ _ := by simp

def toCov (Y : SmV k) {ι : Type} (U : ι → Y.X.Opens) :
    GlobalTheory.LogCris.Mor ((schFn Y.q).cr b ht κ) (covFun b ht κ Y U) (RingHom.id b.R) where
  hp := rfl
  hI := ⟨by rw [Ideal.map_id], fun _ _ => rfl⟩
  a := 1
  ha := by simp
  m := 1
  ht := by simp [ht]
  e i := i.elim
  he j := j.elim
  c _ := ()
  pt := 𝟙 _
  str y r := rfl
  inc _ := trivial
  w _ i := i.elim
  w_map i := i.elim
  hf i := i.elim
  hg i := i.elim
  hw _ := Finset.prod_of_isEmpty (ι := Empty) _

open ReciprocityTheory.ChartRestriction.G.Semi in
open Classical in

def lbOn (Y : SmV k) (L : LB Y.X) (hL : L.IsLB) : GlobalTheory.LogCris.LB (covFun b ht κ Y L.U) where
  g i j B y := if h : ⊤ ≤ y.1.2 ⁻¹ᵁ (L.U i ⊓ L.U j) then
      Units.map (GlobalTheory.Cris.evalAt (B := B) y.1.2 (L.U i ⊓ L.U j) h : Γ(Y.X, L.U i ⊓ L.U j) →* B) (L.g i j) else 1
  g_map := @fun i j B B' φ y hi hj => by
    have h := le_preimage_inf y.1.2 hi hj
    rw [dif_pos h, dif_pos (show ⊤ ≤ (((covFun b ht κ Y L.U).Pt.map φ y)).1.2 ⁻¹ᵁ (L.U i ⊓ L.U j) from le_preimage_map φ y.1.2 h)]
    ext
    exact evalAt_map φ y.1.2 h _ _
  g_self := @fun i B y hi => by
    have h := le_preimage_inf y.1.2 hi hi
    rw [dif_pos h]
    ext
    have e := congrArg (fun u : Γ(Y.X, L.U i)ˣ => (u : Γ(Y.X, L.U i))) (hL.g_self i)
    simp only [Units.coe_map, MonoidHom.coe_coe, Units.val_one]
    rw [← evalAt_res y.1.2 (le_inf le_rfl le_rfl) h hi]
    exact (congrArg _ e).trans (map_one _)
  g_comp := @fun i j l B y hi hj hl => by
    have h12 := le_preimage_inf y.1.2 hi hj
    have h23 := le_preimage_inf y.1.2 hj hl
    have h13 := le_preimage_inf y.1.2 hi hl
    have h123 := le_preimage_inf y.1.2 h12 hl
    rw [dif_pos h12, dif_pos h23, dif_pos h13]
    ext
    have e := congrArg (fun u : Γ(Y.X, L.U i ⊓ L.U j ⊓ L.U l)ˣ => (u : Γ(Y.X, L.U i ⊓ L.U j ⊓ L.U l))) (hL.cocycle i j l)
    simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe] at e ⊢
    rw [← evalAt_res y.1.2 inf_le_left h12 h123, ← evalAt_res y.1.2 (le_inf (inf_le_left.trans inf_le_right) inf_le_right) h23 h123,
      ← evalAt_res y.1.2 (le_inf (inf_le_left.trans inf_le_left) inf_le_right) h13 h123, ← map_mul]
    exact congrArg _ e

def IsFirstChernClassOnThickenings (Y : SmV k) (L : ReciprocityTheory.ChartRestriction.G.Semi.LB Y.X) (hL : L.IsLB) (z : Hc b ht κ Y 2) : Prop :=
  GlobalTheory.LogCris.IsFirstChernClassOfLineBundle (lbOn b ht κ Y L hL) ((toCov b ht κ Y L.U).pull 2 z)

def powH {Y : SmV k} (x : Hc b ht κ Y 2) (j : ℕ) : Hc b ht κ Y (2 * j) :=
  Nat.rec (motive := fun j => Hc b ht κ Y (2 * j)) (one b ht κ Y) (fun _ y => cup b ht κ y x) j

end GlobalTheory.CompanionTheory.KMGys
