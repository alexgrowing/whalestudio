import Formalism.HermitianCurvature.HermitianCurvatureProofs.PictureMemLevelZeroClass
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyZeroNear
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftClosedUnderOperations
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeylCellConjTransposeMulApply
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
import Formalism.HermitianCurvature.HerGenC

namespace Formalism.FourierDecayAlt.P.PBF

open Finset Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.Q Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
open scoped ComplexConjugate ComplexOrder

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section BS

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def BSR (R : ℝ) (F : Mat k r → (Wq →L[ℂ] Wp)) : Prop := ∀ g ∈ GV k r, F g ≠ 0 → gN g ≤ R

theorem smoothLev_of_ckOn {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : CkOn ⊤ (GV k r) F) (D : Set (Mx k r)) :
    SmoothLev k r 0 D F := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hf', hff⟩ := hF g₀ hg₀.1.1
  exact ⟨U, f', hU, hgU, hf', fun g hg hgl => hff g hg hgl.1⟩

theorem mem_level_zero_of_mem_group {g : Mat k r} (hg : g ∈ GV k r) : g ∈ Glev k r 0 :=
  ⟨hg, fun a ha => absurd ha (Nat.not_lt_zero _)⟩

theorem tL_zero_fn (z z' : Fin (2 * r + k + 1) → ℂ) (Y : ℂ) (a b : Fin 2) {g : Mat k r} (hg : g ∈ GV k r) :
    tL k r z z' 0 Y a b (fun _ : Mx k r => (0 : Wq →L[ℂ] Wp)) g = 0 := by
  have h0 : SmoothLev k r 0 Set.univ (fun _ : Mx k r => (0 : Wq →L[ℂ] Wp)) :=
    fun _ _ => ⟨Set.univ, 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩
  have := (Formalism.FourierDecayAlt.P.transfer_linear_local (Wq →L[ℂ] Wp) k r z z' 0 Set.univ Y a b _ _ 1 isOpen_univ h0 h0 g
    ⟨mem_level_zero_of_mem_group hg, trivial⟩).1
  simp only [one_smul, add_zero] at this
  have h2 : tL k r z z' 0 Y a b (fun _ : Mx k r => (0 : Wq →L[ℂ] Wp)) g +
      tL k r z z' 0 Y a b (fun _ : Mx k r => (0 : Wq →L[ℂ] Wp)) g =
      tL k r z z' 0 Y a b (fun _ : Mx k r => (0 : Wq →L[ℂ] Wp)) g := this.symm
  simpa using h2

theorem bsr_tL (z z' : Fin (2 * r + k + 1) → ℂ) (Y : ℂ) (a b : Fin 2) {F : Mat k r → (Wq →L[ℂ] Wp)}
    (hF : CkOn ⊤ (GV k r) F) {R : ℝ} (hR : BSR R F) : BSR R (tL k r z z' 0 Y a b F) := by
  intro g hg hne
  by_contra hgt
  push Not at hgt
  let D : Set (Mx k r) := {h | R < gN h}
  have hD : IsOpen D := isOpen_lt continuous_const Formalism.FourierDecayAlt.P.B6.gN_continuous
  have h0 : SmoothLev k r 0 D (fun _ : Mx k r => (0 : Wq →L[ℂ] Wp)) :=
    fun _ _ => ⟨Set.univ, 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩
  have hloc := (Formalism.FourierDecayAlt.P.transfer_linear_local (Wq →L[ℂ] Wp) k r z z' 0 D Y a b F _ 1 hD
    (smoothLev_of_ckOn hF D) h0 g ⟨mem_level_zero_of_mem_group hg, hgt⟩).2 (fun x hx => by
      by_contra hx0
      have := hR x hx.1.1 hx0
      exact absurd hx.2 (not_lt.2 this))
  exact hne (hloc.trans (tL_zero_fn z z' Y a b hg))

end BS

section Wcell

variable {k r : ℕ}

theorem prod_w1_mem_unitary_Hpk (c : Fin r → ℂ) (hc : ∀ a, c a ≠ 0) (l : List (Fin r)) :
    (l.map fun a => w1 k r a (c a)).prod ∈ UH (Hpk k r) := by
  induction l with
  | nil =>
    show Matrix.conjTranspose (1 : Mx k r) * Hpk k r * 1 = Hpk k r
    simp
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons]
    exact Formalism.FourierDecayAlt.P.TwoByOneBlock.UH_mul (Formalism.FourierDecayAlt.P.Qx3.weyl_cell_mem_unitary a (hc a)) ih

theorem wCell_mul_GV {i : Fin (r + 1)} {c : Fin r → ℂ} (hc : ∀ a, c a ≠ 0) {g : Mx k r}
    (hg : g ∈ Glev k r (Fin.last r)) : wCell k r i c * g ∈ GV k r :=
  Formalism.FourierDecayAlt.P.TwoByOneBlock.UH_mul (prod_w1_mem_unitary_Hpk c hc _) hg.1

end Wcell

section Pics

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem pic_of_cptClause (D : RealPlaceData k r Wp Wq) {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
    (K0 : Submodule ℂ (RadSp k r D.z D.z' π π'))
    (hJc : ∀ (F : Mx k r → (Wq →L[ℂ] Wp)) (ε : ℝ), 0 < ε → (∀ (A' : ℝ) (m' : ℕ), InCC A' m' F) →
      HasCompactSupport F → (∀ g ∈ GV k r, F g ≠ 0 → ε ≤ Gf k r D.z D.z' g) →
      ∃ Φ ∈ K0, ∀ x ∈ DomR k r D.z D.z', (Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = resG k r (Fin.last r) (JF D F) x.1 x.2)
    {F : Mat k r → (Wq →L[ℂ] Wp)} {ε : ℝ} (hε : 0 < ε) (hF : JC.NiceCoef D ε F) {R : ℝ} (hR : BSR R F) :
    ∃ Φ ∈ K0, ∀ x ∈ DomR k r D.z D.z', (Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = resG k r (Fin.last r) (JF D F) x.1 x.2 := by
  classical
  let Ft : Mat k r → (Wq →L[ℂ] Wp) := Set.indicator (GV k r) F
  have hE : ∀ g ∈ GV k r, F g = Ft g := fun g hg => (Set.indicator_of_mem hg F).symm
  have hFt : JC.NiceCoef D ε Ft := Formalism.FourierDecayAlt.P.JCx2.mn_nice_congr hE hF
  have hcs : HasCompactSupport Ft := by
    refine HasCompactSupport.intro (Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le k r R) fun g hg => ?_
    by_cases hgG : g ∈ GV k r
    · show Set.indicator (GV k r) F g = 0
      rw [Set.indicator_of_mem hgG]
      by_contra h0
      exact hg (hR g hgG h0)
    · exact Set.indicator_of_notMem hgG F
  obtain ⟨Φ, hΦ, hpic⟩ := hJc Ft ε hε hFt.2.1 hcs hFt.2.2
  refine ⟨Φ, hΦ, fun x hx => (hpic x hx).trans ?_⟩
  unfold resG
  have hmem := wCell_mul_GV (k := k) (i := Fin.last r) (fun a => hx.1 a) hx.2.1
  rw [Formalism.FourierDecayAlt.P.Qx8.JF_congr D (F := F) (F' := Ft) (a := 1) (fun g hg => by rw [hE g hg, one_smul]) hmem, one_smul]

end Pics

section Closure

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem bsr_sum {k r : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Mat k r → (Wq →L[ℂ] Wp)) {R : ℝ}
    (h : ∀ i ∈ s, BSR R (f i)) : BSR R (fun g => ∑ i ∈ s, f i g) := by
  intro g hg hne
  obtain ⟨i, hi, hne'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  exact h i hi g hg hne'

theorem actOp_nice_bsr (P0 : M.Par) (T : D.LevTower P0.k P0.r Wp Wq) (s : ℂ) (j : Fin (P0.r + 1))
    (w : List C.Letter) (F : Ix (Fin w.length) → Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) {ε R : ℝ}
    (hF : ∀ a, JC.NiceCoef (T.bs j) ε (F a)) (hR : ∀ a, BSR R (F a)) (a : Ix (Fin w.length)) :
    JC.NiceCoef (T.bs j) ε (D.actOp (D.RRlev T s j w) F a) ∧ BSR R (D.actOp (D.RRlev T s j w) F a) := by
  let S : D.Op (Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) → Prop := fun Θ => ∀ G, JC.NiceCoef (T.bs j) ε G → BSR R G →
    JC.NiceCoef (T.bs j) ε (D.ap Θ G) ∧ BSR R (D.ap Θ G)
  have hcl : Formalism.FourierDecayAlt.P.JCx2.mnClosed S :=
    { zero := fun G _ _ => ⟨Formalism.FourierDecayAlt.P.JCx2.mn_nice_zero, fun g _ h => absurd rfl h⟩
      one := fun G hG hR => ⟨hG, hR⟩
      add := fun a b ha hb G hG hR => by
        obtain ⟨h1, h2⟩ := ha G hG hR
        obtain ⟨h3, h4⟩ := hb G hG hR
        refine ⟨Formalism.FourierDecayAlt.P.JCx2.mn_nice_add h1 h3, fun g hg hne => ?_⟩
        by_cases h : D.ap a G g = 0
        · have : D.ap b G g ≠ 0 := by
            intro h'; apply hne; show D.ap a G g + D.ap b G g = 0; rw [h, h', add_zero]
          exact h4 g hg this
        · exact h2 g hg h
      mul := fun a b ha hb G hG hR => by
        obtain ⟨h1, h2⟩ := hb G hG hR
        exact ha _ h1 h2
      cop := fun c G hG hR => ⟨Formalism.FourierDecayAlt.P.JCx2.mn_nice_smul c hG, fun g hg hne => hR g hg (by
        intro h0; apply hne; show c • G g = 0; rw [h0, smul_zero])⟩ }
  have hQQ : ∀ Y p q, S (D.QQlev T s j Y p q) := fun Y p q G hG hRG => by
    refine ⟨Formalism.FourierDecayAlt.P.JCx2.mn_nice_smul s (Formalism.FourierDecayAlt.P.JCx2.mn_tL_nice (T.bs j) ε G Y p q hG), fun g hg hne => ?_⟩
    refine bsr_tL (T.bs j).z (T.bs j).z' Y p q hG.1 hRG g hg ?_
    intro h0; apply hne; show s • tL P0.k (P0.r - j) (T.bs j).z (T.bs j).z' 0 Y p q G g = 0; rw [h0, smul_zero]
  have hR' := Formalism.FourierDecayAlt.P.JCx2.mn_rrop_closure hcl (D.QQlev T s j) hQQ (D.positionted w)
  refine ⟨Formalism.FourierDecayAlt.P.JCx2.mn_nice_sum' _ _ fun b _ => (hR' a b (F b) (hF b) (hR b)).1, ?_⟩
  intro g hg hne
  have e : D.actOp (D.RRlev T s j w) F a g = ∑ b, D.ap (D.RRlev T s j w a b) (F b) g := by
    simp only [D.actOp, Finset.sum_apply]
  exact bsr_sum Finset.univ (fun b => D.ap (D.RRlev T s j w a b) (F b))
    (fun b _ => (hR' a b (F b) (hF b) (hR b)).2) g hg (fun h0 => hne (e.trans h0))

theorem cpt_nice_bsr {k r : ℕ} {Bs : RealPlaceData k r Wp Wq} {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : KB.CptCoef Bs F) :
    (∃ ε, 0 < ε ∧ JC.NiceCoef Bs ε F) ∧ ∃ R, BSR R F :=
  ⟨Formalism.FourierDecayAlt.P.TLB.nice_of_cpt hF, hF.2.1⟩

end Closure

end

end Formalism.FourierDecayAlt.P.PBF
