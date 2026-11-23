import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CstD

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md Dt KA Set0 Coord LInv pt dia2 pri)
open GlobalTheory.CompanionTheory.UnfoldingAlt
open scoped NumberField.AdeleRing ENNReal Pointwise

namespace GlobalTheory.CompanionTheory.UnfoldingAlt.TiWhit

open GroundTheory.Automorphic.FourierWhittaker

abbrev pa : Pos 3 := ⟨(0, 1), by decide⟩

abbrev pb : Pos 3 := ⟨(0, 2), by decide⟩

abbrev pc : Pos 3 := ⟨(1, 2), by decide⟩

theorem setIntegral_sub_of_periodic {ι : Type*} [Fintype ι] (F : (ι → 𝔸[ℚ]) → ℂ)
    (hF : ∀ ξ ∈ vecLattice ℚ ι, ∀ x, F (ξ + x) = F x) (c : ι → 𝔸[ℚ]) :
    ∫ y in vecDomain ℚ ι, F (c - y) ∂vecMeasure ℚ ι = ∫ y in vecDomain ℚ ι, F y ∂vecMeasure ℚ ι := by
  have hD := isAddFundamentalDomain_vecDomain (K := ℚ) (ι := ι)
  let T : (ι → 𝔸[ℚ]) ≃+ (ι → 𝔸[ℚ]) := AddEquiv.neg _
  have hcn : Continuous fun x : ι → 𝔸[ℚ] => -x := continuous_neg
  have h1 := setIntegral_comp_addEquiv T hcn hcn
    (isAddFundamentalDomain_image_of_map_vecLattice T hcn (fun x => by
      change x ∈ vecLattice ℚ ι ↔ -x ∈ vecLattice ℚ ι
      exact (neg_mem_iff).symm))
    (f := fun u => F (c + u)) (fun ξ hξ x => by
      rw [show c + (ξ + x) = ξ + (c + x) by abel]
      exact hF ξ hξ _)
  have h2 : ∫ y in vecDomain ℚ ι, F (c + y) ∂vecMeasure ℚ ι =
      ∫ y in vecDomain ℚ ι, F y ∂vecMeasure ℚ ι := by
    have e1 : ∫ y in vecDomain ℚ ι, F (c + y) ∂vecMeasure ℚ ι =
        ∫ y in (fun y => c + y) '' vecDomain ℚ ι, F y ∂vecMeasure ℚ ι :=
      ((measurePreserving_add_left (vecMeasure ℚ ι) c).setIntegral_image_emb
        (measurableEmbedding_addLeft c) F _).symm
    have e2 : (fun y => c + y) '' vecDomain ℚ ι = c +ᵥ vecDomain ℚ ι := rfl
    rw [e1, e2]
    refine (hD.vadd_of_comm c).setIntegral_eq hD fun l x => ?_
    exact hF l l.2 x
  calc ∫ y in vecDomain ℚ ι, F (c - y) ∂vecMeasure ℚ ι
      = ∫ y in vecDomain ℚ ι, F (c + T y) ∂vecMeasure ℚ ι := by
        refine setIntegral_congr_fun measurableSet_vecDomain fun y _ => ?_
        change F (c - y) = F (c + -y)
        rw [sub_eq_add_neg]
    _ = _ := h1.trans h2

def sp : Pos 3 ≃ Fin 2 ⊕ Fin 1 where
  toFun p := if p = pa then Sum.inl 0 else if p = pc then Sum.inl 1 else Sum.inr 0
  invFun := Sum.elim (fun i => if i = 0 then pa else pc) (fun _ => pb)
  left_inv := by decide
  right_inv := by decide

def sw : Pos 3 ≃ Pos 3 where
  toFun p := if p = pa then pc else if p = pc then pa else p
  invFun p := if p = pa then pc else if p = pc then pa else p
  left_inv := by decide
  right_inv := by decide

def fl (X : Pos 3 → 𝔸[ℚ]) : Pos 3 → 𝔸[ℚ] := fun p => if p = pb then X pa * X pc - X pb else X p

theorem continuous_fl : Continuous fl := by
  refine continuous_pi fun p => ?_
  simp only [fl]
  split_ifs
  · have ha : Continuous fun X : Pos 3 → 𝔸[ℚ] => X pa := continuous_apply pa
    have hb : Continuous fun X : Pos 3 → 𝔸[ℚ] => X pb := continuous_apply pb
    have hc : Continuous fun X : Pos 3 → 𝔸[ℚ] => X pc := continuous_apply pc
    exact (ha.mul hc).sub hb
  · exact continuous_apply _

theorem setIntegral_comp_sw (h : (Pos 3 → 𝔸[ℚ]) → ℂ) :
    ∫ X in vecDomain ℚ (Pos 3), h (fun p => X (sw p)) ∂vecMeasure ℚ (Pos 3) =
      ∫ X in vecDomain ℚ (Pos 3), h X ∂vecMeasure ℚ (Pos 3) := by
  let E := MeasurableEquiv.piCongrLeft (fun _ : Pos 3 => 𝔸[ℚ]) sw
  have hE : MeasurePreserving E (vecMeasure ℚ (Pos 3)) (vecMeasure ℚ (Pos 3)) :=
    measurePreserving_piCongrLeft (fun _ : Pos 3 => GroundTheory.Global.adeleMeasure ℚ) sw
  have hsw : ∀ p, sw.symm p = sw p := fun p => rfl
  have hEX : ∀ X : Pos 3 → 𝔸[ℚ], E X = fun p => X (sw p) := by
    intro X
    funext p
    simp [E, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft, hsw]
  have hpre : E ⁻¹' vecDomain ℚ (Pos 3) = vecDomain ℚ (Pos 3) := by
    ext X
    simp only [Set.mem_preimage, hEX, vecDomain, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro hX p
      have := hX (sw p)
      simpa [hsw, show sw (sw p) = p from sw.left_inv p] using this
    · intro hX p
      exact hX _
  have := hE.setIntegral_preimage_emb E.measurableEmbedding h (vecDomain ℚ (Pos 3))
  rw [hpre] at this
  simpa only [hEX] using this

theorem setIntegral_comp_fl {h : (Pos 3 → 𝔸[ℚ]) → ℂ} (hc : Continuous h)
    (hp : ∀ (r : ℚ) (X : Pos 3 → 𝔸[ℚ]),
      h (fun p => if p = pb then algebraMap ℚ 𝔸[ℚ] r + X p else X p) = h X) :
    ∫ X in vecDomain ℚ (Pos 3), h (fl X) ∂vecMeasure ℚ (Pos 3) =
      ∫ X in vecDomain ℚ (Pos 3), h X ∂vecMeasure ℚ (Pos 3) := by
  rw [setIntegral_vecDomain_sum (h := fun X => h (fl X)) sp (hc.comp continuous_fl),
    setIntegral_vecDomain_sum sp hc]
  refine setIntegral_congr_fun measurableSet_vecDomain fun w _ => ?_
  have key := setIntegral_sub_of_periodic (ι := Fin 1)
    (fun y => h (fun i => Sum.elim w y (sp i))) ?_ (fun _ => w 0 * w 1)
  · rw [← key]
    refine setIntegral_congr_fun measurableSet_vecDomain fun y _ => ?_
    congr 1
    funext p
    have h1 : sp pa = Sum.inl 0 := by decide
    have h2 : sp pc = Sum.inl 1 := by decide
    have h3 : sp pb = Sum.inr 0 := by decide
    by_cases hb : p = pb
    · subst hb
      simp [fl, h1, h2, h3]
    · simp only [fl, if_neg hb]
      rcases hs : sp p with a | b
      · simp
      · exfalso
        apply hb
        have : b = 0 := Subsingleton.elim _ _
        subst this
        exact sp.injective (hs.trans h3.symm)
  · rintro _ ⟨ξ, rfl⟩ y
    rw [← hp (ξ 0) (fun i => Sum.elim w y (sp i))]
    congr 1
    funext p
    have h3 : sp pb = Sum.inr 0 := by decide
    by_cases hb : p = pb
    · subst hb
      simp [h3]
    · simp only [if_neg hb]
      rcases hs : sp p with a | b
      · simp
      · exfalso
        apply hb
        have : b = 0 := Subsingleton.elim _ _
        subst this
        exact sp.injective (hs.trans h3.symm)

theorem supSum_three (X : Pos 3 → 𝔸[ℚ]) : supSum 0 X = X pa + X pc := by
  have h : Finset.univ.filter (fun p : Pos 3 => p.1.2.val = p.1.1.val + 1 ∧ 0 ≤ p.1.2.val) =
      {pa, pc} := by decide
  rw [supSum, h, Finset.sum_pair (by decide)]

theorem uGL_eq_uni {R : Type*} [CommRing R] (X : Pos 3 → R) : uGL X = uni (X pa) (X pb) (X pc) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uni, uMat_apply]

theorem ti_mul {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n] (a b : GL n R) :
    ti (a * b) = ti a * ti b := by
  apply Units.ext
  change (b.inv * a.inv).transpose = a.inv.transpose * b.inv.transpose
  rw [Matrix.transpose_mul]

def cq : GL (Fin 3) ℚ := w3 * ti dl3

theorem transposeInv_sign_diag : ti dl3 = dl3 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ti, dl3, dg]

theorem ti_dia (γ : GL (Fin 3) ℚ) : ti (dia γ) = dia (ti γ) := by
  apply Units.ext
  ext i j
  simp [dia, ti, AdelicGLn.diagonal]

theorem coe_dia_cq :
    ((dia cq : G3) : Matrix (Fin 3) (Fin 3) 𝔸[ℚ]) = !![0, 0, 1; 0, -1, 0; 1, 0, 0] := by
  rw [show cq = w3 * dl3 by rw [cq, transposeInv_sign_diag]]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dl3, dg, w3, AdelicGLn.diagonal, Matrix.mul_apply, Fin.sum_univ_three]

theorem dia_cq : dia cq = w3 * ti (dia dl3) := by
  rw [ti_dia, transposeInv_sign_diag]
  apply Units.ext
  rw [coe_dia_cq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dl3, dg, w3, AdelicGLn.diagonal, Matrix.mul_apply, Fin.sum_univ_three]

theorem conj_uni (x y z : 𝔸[ℚ]) :
    w3 * ti (dia dl3) * ti (uni x y z) = uni z (z * x - y) x * (w3 * ti (dia dl3)) := by
  rw [← dia_cq]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_dia_cq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ti, uni, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem dia_uni_mul (r : ℚ) (x y z : 𝔸[ℚ]) :
    dia (uni (0 : ℚ) r 0) * uni x y z = uni x (algebraMap ℚ 𝔸[ℚ] r + y) z := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uni, AdelicGLn.diagonal, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem whittaker_ti : ∀ φ : G3 → ℂ, IsLeftInvariant φ → Continuous φ → ∀ g : G3,
    FourierWhittaker.whittaker (fun g : G3 => φ (ti g)) g = tr (FourierWhittaker.whittaker φ) g := by
  intro φ hL hc g
  obtain ⟨g', hg'⟩ : ∃ g' : G3, g' = w3 * ti (dia dl3) * ti g := ⟨_, rfl⟩
  have htr : tr (FourierWhittaker.whittaker φ) g = FourierWhittaker.whittaker φ g' := by
    simp only [tr, dualWhittakerAdelicGL3]
    rw [ti_mul, hg', mul_assoc]
  rw [htr]
  have hcont := continuous_wInt 0 hc g'
  have hpt : ∀ X : Pos 3 → 𝔸[ℚ], φ (ti (uGL X * g)) * (adelicChar ℚ (-supSum 0 X) : ℂ) =
      (fun Y => wInt 0 φ g' (fl Y)) (fun p => X (sw p)) := by
    intro X
    have h1 : sw pa = pc := by decide
    have h2 : sw pc = pa := by decide
    have h3 : sw pb = pb := by decide
    have ea : fl (fun p => X (sw p)) pa = X pc := by simp [fl, h1]
    have eb : fl (fun p => X (sw p)) pb = X pc * X pa - X pb := by simp [fl, h1, h2, h3]
    have ec : fl (fun p => X (sw p)) pc = X pa := by simp [fl, h2]
    simp only [wInt]
    rw [uGL_eq_uni (fl _), supSum_three (fl _), ea, eb, ec, supSum_three X, add_comm (X pc),
      ← hL cq, show AdelicGLn.diagonal ℚ 3 cq = w3 * ti (dia dl3) from dia_cq, ti_mul, ← mul_assoc,
      uGL_eq_uni X, conj_uni, hg', mul_assoc]
  have hper : ∀ (r : ℚ) (X : Pos 3 → 𝔸[ℚ]),
      wInt 0 φ g' (fun p => if p = pb then algebraMap ℚ 𝔸[ℚ] r + X p else X p) = wInt 0 φ g' X := by
    intro r X
    simp only [wInt]
    rw [uGL_eq_uni (fun p => _), supSum_three (fun p => _), uGL_eq_uni X, supSum_three X]
    simp only [if_neg (show pa ≠ pb by decide), if_neg (show pc ≠ pb by decide), if_true]
    rw [← dia_uni_mul, mul_assoc, hL]
  calc FourierWhittaker.whittaker (fun g : G3 => φ (ti g)) g
      = ∫ X in vecDomain ℚ (Pos 3), (fun Y => wInt 0 φ g' (fl Y)) (fun p => X (sw p))
          ∂vecMeasure ℚ (Pos 3) :=
        setIntegral_congr_fun measurableSet_vecDomain fun X _ => hpt X
    _ = ∫ X in vecDomain ℚ (Pos 3), wInt 0 φ g' (fl X) ∂vecMeasure ℚ (Pos 3) :=
        setIntegral_comp_sw (fun Y => wInt 0 φ g' (fl Y))
    _ = ∫ X in vecDomain ℚ (Pos 3), wInt 0 φ g' X ∂vecMeasure ℚ (Pos 3) :=
        setIntegral_comp_fl hcont hper
    _ = FourierWhittaker.whittaker φ g' := rfl

end GlobalTheory.CompanionTheory.UnfoldingAlt.TiWhit

end
