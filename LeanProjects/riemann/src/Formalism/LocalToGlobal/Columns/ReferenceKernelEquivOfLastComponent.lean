import Formalism.LocalToGlobal.Columns.RefXi1Above
import Formalism.LocalToGlobal.Columns.ExistsYOfOfMemYbSet
import Formalism.LocalToGlobal.Columns.ChainOne

open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Eq

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (hQ : QE sel (mu : Chr X.F X.E X.K) = ∅) (m2 : ℕ) (Am : Amb X) (u : Pr.Word)

def oneAl (j : ℕ) (h : j ≤ m2 + 1) : (oneIdx Λ (QE sel (mu : Chr X.F X.E X.K)) m2).β j := ⟨(), h⟩

def oneG {j : ℕ} (g : FormG (Λ j)) : FrmG (Λ j) (LevQFam.top X.E X.K (R.N j) (QE sel (mu : Chr X.F X.E X.K))) := (g.1, g.2, 1)

variable {Λ sel mu}

theorem liftQ_oneG {j : ℕ} (g : FormG (Λ j)) (p : DecoSet X.E (R.N j) (Pr.vT u) Pr.vGs) :
    (liftQ hQ ((formAct (Λ j)).toSMul.smul g p) : ChPt (R := R) sel mu u j) =
      (frmAct (Λ j) (LevQFam.top X.E X.K (R.N j) (QE sel (mu : Chr X.F X.E X.K)))).toSMul.smul (oneG Λ sel mu g) (liftQ hQ p) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · funext ⟨P, hP⟩
    rw [hQ] at hP
    simp at hP

theorem frmRho_oneG {j : ℕ} (g : FormG (Λ j)) :
    frmRho (colValF W sel mu u j) (Λ j) (LevQFam.top X.E X.K (R.N j) (QE sel (mu : Chr X.F X.E X.K))) (oneG Λ sel mu g) =
      formRho (colVal W u j (Pr.vT u) Pr.vGs) (Λ j) g := by
  show (((Λ j).chr g.2 * (LevQFam.top X.E X.K (R.N j) (QE sel (mu : Chr X.F X.E X.K))).chr 1 : X.Kˣ) : X.K) •
      (colVal W u j (Pr.vT u) Pr.vGs).rho g.1 =
    (((Λ j).chr g.2 : X.Kˣ) : X.K) • (colVal W u j (Pr.vT u) Pr.vGs).rho g.1
  rw [map_one, mul_one]

variable (Λ sel mu)

def FixE : Prop :=
  ∀ h ∈ (Λ (m2 + 1)).grp, ∀ w : Pr.vGs,
    ((h w : GL (Fin (R.N (m2 + 1))) (𝓞 X.E ⧸ w.1.asIdeal)) : Matrix _ _ (𝓞 X.E ⧸ w.1.asIdeal)).mulVec (Loc.eN (𝓞 X.E ⧸ w.1.asIdeal) (R.N (m2 + 1)) R.k) =
      Loc.eN (𝓞 X.E ⧸ w.1.asIdeal) (R.N (m2 + 1)) R.k

def RefKEquiv (i : ℕ) : Prop :=
  ∀ (g : FormG (Λ i)) (g' : FormG (Λ (i + 1))) (p : DecoSet X.E (R.N i) (Pr.vT u) Pr.vGs) (p' : DecoSet X.E (R.N (i + 1)) (Pr.vT u) Pr.vGs),
    refK W Ch sel mu cst (oneIdx Λ (QE sel (mu : Chr X.F X.E X.K)) m2) (chTh W Ch sel mu cst Am u m2) (oneAl Λ sel mu m2) i
        (liftQ hQ ((formAct (Λ i)).toSMul.smul g p)) (liftQ hQ ((formAct (Λ (i + 1))).toSMul.smul g' p')) =
      (formRho (colVal W u (i + 1) (Pr.vT u) Pr.vGs) (Λ (i + 1)) g') ∘ₗ
        (refK W Ch sel mu cst (oneIdx Λ (QE sel (mu : Chr X.F X.E X.K)) m2) (chTh W Ch sel mu cst Am u m2) (oneAl Λ sel mu m2) i (liftQ hQ p) (liftQ hQ p')) ∘ₗ
          (formRho (colVal W u i (Pr.vT u) Pr.vGs) (Λ i) g⁻¹)

variable {W Λ Ch sel mu cst hQ m2 Am u}

theorem xiEquiv_of_refK (h : ∀ i, RefKEquiv W Λ Ch sel mu cst hQ m2 Am u i) :
    XiEquiv W Λ Ch sel mu cst Am u
      (refXi1 Ch sel mu cst (oneIdx Λ (QE sel (mu : Chr X.F X.E X.K)) m2) hQ m2 (oneAl Λ sel mu m2) u) := by
  unfold XiEquiv refXi1
  intro a
  unfold ClsEq xiKer XiRef
  intro g g' p p'
  exact h a g g' p p'

theorem refKEquiv_of_mat {i : ℕ} (hi : i < m2)
    (hM : MatEquiv W Ch sel mu cst (oneIdx Λ (QE sel (mu : Chr X.F X.E X.K)) m2) (chTh W Ch sel mu cst Am u m2)) :
    RefKEquiv W Λ Ch sel mu cst hQ m2 Am u i := by
  intro g g' p p'
  have e : ∀ (q : ChPt (R := R) sel mu u i) (q' : ChPt (R := R) sel mu u (i + 1)),
      refK W Ch sel mu cst (oneIdx Λ (QE sel (mu : Chr X.F X.E X.K)) m2) (chTh W Ch sel mu cst Am u m2) (oneAl Λ sel mu m2) i q q' =
        matK W Ch sel mu cst (oneIdx Λ (QE sel (mu : Chr X.F X.E X.K)) m2) (chTh W Ch sel mu cst Am u m2) i
          (oneAl Λ sel mu m2 i (by omega)) (oneAl Λ sel mu m2 (i + 1) (by omega)) q q' := by
    intro q q'
    unfold refK matK
    congr 1
    funext x
    unfold XiRef
    rw [dif_pos hi]
  rw [e, e, liftQ_oneG, liftQ_oneG]
  have h := hM i hi (oneAl Λ sel mu m2 i (by omega)) (oneAl Λ sel mu m2 (i + 1) (by omega)) (oneG Λ sel mu g) (oneG Λ sel mu g')
    (liftQ hQ p) (liftQ hQ p')
  refine h.trans ?_
  have h1 := frmRho_oneG (W := W) (u := u) (sel := sel) (mu := mu) g'
  have h2 := frmRho_oneG (W := W) (u := u) (sel := sel) (mu := mu) g⁻¹
  show (frmRho (colValF W sel mu u (i + 1)) (Λ (i + 1)) _ (oneG Λ sel mu g')) ∘ₗ _ ∘ₗ (frmRho (colValF W sel mu u i) (Λ i) _ (oneG Λ sel mu g)⁻¹) = _
  have h3 : (oneG Λ sel mu g)⁻¹ = oneG Λ sel mu g⁻¹ := by
    unfold oneG
    simp
  rw [h3, h1, h2]
  rfl

theorem lastVectorLine_equivariant (hF : FixE (R := R) Λ m2) (g' : FormG (Λ (m2 + 1))) (p' : DecoSet X.E (R.N (m2 + 1)) (Pr.vT u) Pr.vGs) :
    ((formAct (Λ (m2 + 1))).toSMul.smul g' p').1.y0 R.k = (fun v => g'.1.1 v) '' (p'.1.y0 R.k) := by
  unfold FixE at hF
  have hact : ((formAct (Λ (m2 + 1))).toSMul.smul g' p').1 = Deco.act ↑g'.1 ↑g'.2 p'.1 := rfl
  have hloc : ∀ (P : HeightOneSpectrum (𝓞 X.E)) (y : _),
      y ∈ (Deco.act ↑g'.1 ↑g'.2 p'.1).at P ↔ g'.1.1.symm y ∈ p'.1.at P := by
    intro P y
    change (∃ s ∈ P.asIdeal.primeCompl, s • y ∈ gmap g'.1.1 p'.1.N) ↔
      (∃ s ∈ P.asIdeal.primeCompl, s • g'.1.1.symm y ∈ p'.1.N)
    constructor
    · rintro ⟨s, hs, hy⟩
      obtain ⟨z, hz, hzy⟩ := Submodule.mem_map.mp hy
      refine ⟨s, hs, ?_⟩
      have e1 : g'.1.1.symm (s • y) = s • g'.1.1.symm y :=
        (g'.1.1.symm.toLinearMap.restrictScalars (𝓞 X.E)).map_smul s y
      rw [← e1, ← hzy]
      simpa using hz
    · rintro ⟨s, hs, hy⟩
      refine ⟨s, hs, Submodule.mem_map.mpr ⟨_, hy, ?_⟩⟩
      have e1 : g'.1.1 (s • g'.1.1.symm y) = s • g'.1.1 (g'.1.1.symm y) :=
        (g'.1.1.toLinearMap.restrictScalars (𝓞 X.E)).map_smul s _
      simpa using e1
  have hbe : ∀ (w : Pr.vGs) (y : _),
      (Deco.act ↑g'.1 ↑g'.2 p'.1).be w y = Loc.eN (𝓞 X.E ⧸ w.1.asIdeal) (R.N (m2 + 1)) R.k ↔
        p'.1.be w (g'.1.1.symm y) = Loc.eN (𝓞 X.E ⧸ w.1.asIdeal) (R.N (m2 + 1)) R.k := by
    intro w y
    have hM := hF g'.2.1 g'.2.2 w
    change (g'.2.1 w).1.mulVec (p'.1.be w (g'.1.1.symm y)) = _ ↔ _
    generalize p'.1.be w (g'.1.1.symm y) = z
    constructor
    · intro hz
      calc z = ((g'.2.1 w)⁻¹).1.mulVec ((g'.2.1 w).1.mulVec z) := by
            rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
        _ = ((g'.2.1 w)⁻¹).1.mulVec ((g'.2.1 w).1.mulVec
              (Loc.eN (𝓞 X.E ⧸ w.1.asIdeal) (R.N (m2 + 1)) R.k)) := by
            rw [hz, hM]
        _ = _ := by rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    · rintro rfl
      exact hM
  rw [hact]
  ext v
  simp only [Deco.y0, Deco.yOf, Set.mem_image, Set.mem_setOf_eq, Nat.cast_smul_eq_nsmul]
  constructor
  · intro H
    refine ⟨g'.1.1.symm v, fun w => ?_, by simp⟩
    obtain ⟨h1, h2⟩ := H w
    rw [hloc, map_nsmul] at h1
    rw [hbe, map_nsmul] at h2
    exact ⟨h1, h2⟩
  · rintro ⟨x, hx, rfl⟩ w
    obtain ⟨h1, h2⟩ := hx w
    rw [hloc, hbe, map_nsmul, LinearEquiv.symm_apply_apply]
    exact ⟨h1, h2⟩

theorem referenceKernelEquiv_of_lastComponent (hX : X.Ok) (hPr : Pr.Ok) (hF : FixE (R := R) Λ m2)
    (hY : YbHyp (R := R) sel mu cst (oneIdx Λ (QE sel (mu : Chr X.F X.E X.K)) m2) u m2 (oneAl Λ sel mu m2 (m2 + 1) le_rfl))
    (h1 : Cp1EquivOn W Ch sel mu cst (oneIdx Λ (QE sel (mu : Chr X.F X.E X.K)) m2) (chTh W Ch sel mu cst Am u m2)
      (oneAl Λ sel mu m2 (m2 + 1) le_rfl) hY) :
    RefKEquiv W Λ Ch sel mu cst hQ m2 Am u m2 := by
  intro g g' p p'
  have hmem : ∀ q' : DecoSet X.E (R.N (m2 + 1)) (Pr.vT u) Pr.vGs, q'.1.y0 R.k ∈ ybSet sel mu cst q'.1.N :=
    fun q' => yOf_mem_ybSet sel mu cst hX hPr (pc_rowSG hQ) q' _
  have e : ∀ (q : ChPt (R := R) sel mu u m2) (q' : DecoSet X.E (R.N (m2 + 1)) (Pr.vT u) Pr.vGs),
      refK W Ch sel mu cst (oneIdx Λ (QE sel (mu : Chr X.F X.E X.K)) m2) (chTh W Ch sel mu cst Am u m2) (oneAl Λ sel mu m2) m2 q (liftQ hQ q') =
        cp1K W Ch sel mu cst (oneIdx Λ (QE sel (mu : Chr X.F X.E X.K)) m2) (chTh W Ch sel mu cst Am u m2)
          (oneAl Λ sel mu m2 m2 (by omega)) q (liftQ hQ q') (q'.1.y0 R.k) := by
    intro q q'
    unfold refK cp1K
    rw [if_pos (show q'.1.y0 R.k ∈ ybSet sel mu cst (liftQ hQ q' : ChPt (R := R) sel mu u (m2 + 1)).deco.1.N from hmem q')]
    congr 1
    funext x
    unfold XiRef
    rw [dif_neg (lt_irrefl _), dif_pos rfl]
    rfl
  rw [e, e, lastVectorLine_equivariant hF, liftQ_oneG, liftQ_oneG]
  have h := h1 (oneAl Λ sel mu m2 m2 (by omega)) (oneG Λ sel mu g) (oneG Λ sel mu g') (liftQ hQ p) (liftQ hQ p') (p'.1.y0 R.k) (hmem p')
  refine h.trans ?_
  have h1' := frmRho_oneG (W := W) (u := u) (sel := sel) (mu := mu) g'
  have h2' := frmRho_oneG (W := W) (u := u) (sel := sel) (mu := mu) g⁻¹
  show (frmRho (colValF W sel mu u (m2 + 1)) (Λ (m2 + 1)) _ (oneG Λ sel mu g')) ∘ₗ _ ∘ₗ (frmRho (colValF W sel mu u m2) (Λ m2) _ (oneG Λ sel mu g)⁻¹) = _
  have h3 : (oneG Λ sel mu g)⁻¹ = oneG Λ sel mu g⁻¹ := by
    unfold oneG
    simp
  rw [h3, h1', h2']
  rfl

theorem refKEquiv_above {i : ℕ} (hi : m2 + 1 < i) : RefKEquiv W Λ Ch sel mu cst hQ m2 Am u i := by
  intro g g' p p'
  have e : ∀ (q : ChPt (R := R) sel mu u i) (q' : ChPt (R := R) sel mu u (i + 1)),
      refK W Ch sel mu cst (oneIdx Λ (QE sel (mu : Chr X.F X.E X.K)) m2) (chTh W Ch sel mu cst Am u m2) (oneAl Λ sel mu m2) i q q' = 0 := by
    intro q q'
    unfold refK
    refine kerOf_zero _ _ _ _ _ _ _ _ _ fun x => ?_
    unfold XiRef
    rw [dif_neg (by omega), dif_neg (by omega), if_neg (by omega)]
  rw [e, e]
  ext x
  exact (map_zero (formRho (colVal W u (i + 1) (Pr.vT u) Pr.vGs) (Λ (i + 1)) g')).symm ▸ rfl

end Eq

end Formalism.L2.Col
