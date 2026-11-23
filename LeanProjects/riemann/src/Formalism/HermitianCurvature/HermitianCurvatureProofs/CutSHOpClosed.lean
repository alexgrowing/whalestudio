import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSH2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHFamAlg
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHFamDeriv
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHRepLin
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHCellTie
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHFamJFDeriv

open scoped ContDiff Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSH

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.PBH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section opc

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}

theorem opc_cc_zero (j : ℕ) (hj : j + 1 ≤ P.r) (t : ℂ) (c : Fin (P.r - (j + 1)) → ℂ) :
    cc (P := P) j hj t c ⟨0, by omega⟩ = t := by
  unfold cc consC
  simp

theorem opc_cc_line (j : ℕ) (hj : j + 1 ≤ P.r) (t v : ℂ) (s : ℝ) (c : Fin (P.r - (j + 1)) → ℂ) :
    cc (P := P) j hj (t + (s : ℂ) * v) c =
      cc (P := P) j hj t c + s • (Pi.single (⟨0, by omega⟩ : Fin (P.r - j)) v : Fin (P.r - j) → ℂ) := by
  funext l
  unfold cc consC
  by_cases hl : (l : ℕ) = 0
  · have e : l = ⟨0, by omega⟩ := Fin.ext hl
    simp [hl, Pi.single_apply, e, Complex.real_smul]
  · have hne : l ≠ ⟨0, by omega⟩ := fun h => hl (by rw [h])
    simp [hl, Pi.single_apply, hne]

theorem opc_mul (h2 : FamAlg) (h4 : RepLin) {T : D.LevTower P.k P.r Wp Wq}
    (hP : IsPlace P T.base.z T.base.z' T.base.π T.base.π') (hT : D.TowerNormalised T) {j : ℕ} {hj : j + 1 ≤ P.r}
    (hPs : IsPlace (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π')
    {Ψ Ψ' : RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'}
    {G : ℂ → B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp)} (hG : GoodFam T j G) (hR : Rep T j hj Ψ G)
    (m : ℂ → ℂ) (hm : ContDiffOn ℝ ∞ m {t | t ≠ 0})
    (hv : ∀ t : ℂ, t ≠ 0 → ∀ x ∈ DomR P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z',
      (Ψ' : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) (cc j hj t x.1) (gi j hj x.2) =
        m t • (Ψ : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) (cc j hj t x.1) (gi j hj x.2)) :
    InC T j hj Ψ' := by
  refine ⟨fun t γ => m t • G t γ, (h2 Wp Wq P T j G G hG hG m hm).2, fun t ht x hx => ?_⟩
  rw [hv t ht x hx, hR t ht x hx]
  exact (h4 Wp Wq P T hP hT j hj hPs G G hG hG t ht (m t) x hx).2.symm

theorem opc_two (h2 : FamAlg) (h3 : FamDeriv) (h4 : RepLin) {T : D.LevTower P.k P.r Wp Wq}
    (hP : IsPlace P T.base.z T.base.z' T.base.π T.base.π') (hT : D.TowerNormalised T) {j : ℕ} {hj : j + 1 ≤ P.r}
    (hPs : IsPlace (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π')
    {Ψ' : RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'}
    {G : ℂ → B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp)} (hG : GoodFam T j G)
    (m1 m2 : ℂ → ℂ) (hm1 : ContDiffOn ℝ ∞ m1 {t | t ≠ 0}) (hm2 : ContDiffOn ℝ ∞ m2 {t | t ≠ 0}) (v1 v2 : ℂ)
    (hv : ∀ t : ℂ, t ≠ 0 → ∀ x ∈ DomR P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z',
      (Ψ' : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) (cc j hj t x.1) (gi j hj x.2) =
        m1 t • resG P.k (P.r - (j + 1)) (Fin.last _) (B.JF (T.bs (j + 1)) (famP j G v1 t)) x.1 x.2 +
        m2 t • resG P.k (P.r - (j + 1)) (Fin.last _) (B.JF (T.bs (j + 1)) (famP j G v2 t)) x.1 x.2) :
    InC T j hj Ψ' := by
  have hd1 := h3 Wp Wq P T j G hG v1
  have hd2 := h3 Wp Wq P T j G hG v2
  have hA : GoodFam T j (fun t γ => m1 t • famP j G v1 t γ) := (h2 Wp Wq P T j _ _ hd1 hd1 m1 hm1).2
  have hB : GoodFam T j (fun t γ => m2 t • famP j G v2 t γ) := (h2 Wp Wq P T j _ _ hd2 hd2 m2 hm2).2
  refine ⟨fun t γ => m1 t • famP j G v1 t γ + m2 t • famP j G v2 t γ,
    (h2 Wp Wq P T j _ _ hA hB (fun _ => 1) contDiffOn_const).1, fun t ht x hx => ?_⟩
  have e0 := (h4 Wp Wq P T hP hT j hj hPs _ _ hA hB t ht 0 x hx).1
  have e1 := (h4 Wp Wq P T hP hT j hj hPs _ _ hd1 hd1 t ht (m1 t) x hx).2
  have e2 := (h4 Wp Wq P T hP hT j hj hPs _ _ hd2 hd2 t ht (m2 t) x hx).2
  rw [hv t ht x hx, ← e1, ← e2]
  exact e0.symm

theorem opc_fderiv (h5 : FamJFDeriv) (h6 : CellTie) (T : D.LevTower P.k P.r Wp Wq)
    (hP : IsPlace P T.base.z T.base.z' T.base.π T.base.π') (hT : D.TowerNormalised T) (j : ℕ) (hj : j + 1 ≤ P.r)
    (hPj : IsPlace (JC.parLev P j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')
    (hPs : IsPlace (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π')
    (Ψ : RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')
    (G : ℂ → B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp)) (hG : GoodFam T j G) (hR : Rep T j hj Ψ G)
    (t : ℂ) (ht : t ≠ 0) (x : (Fin (P.r - (j + 1)) → ℂ) × Mx P.k (P.r - (j + 1)))
    (hx : x ∈ DomR P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z') (v : ℂ) :
    fderiv ℝ (fun c' => (Ψ : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) c' (gi j hj x.2)) (cc j hj t x.1)
        (Pi.single (⟨0, by omega⟩ : Fin (P.r - j)) v) =
      resG P.k (P.r - (j + 1)) (Fin.last _) (B.JF (T.bs (j + 1)) (famP j G v t)) x.1 x.2 := by
  have hy := (h6 Wp Wq P T hP hT j hj hPj hPs t ht x hx).1
  obtain ⟨-, hs, -⟩ := Ψ.2
  obtain ⟨U, F, hU, hyU, hF, hΨF⟩ := hs _ hy
  have hg : gi j hj x.2 ∈ Glev P.k (P.r - j) (Fin.last _) := hy.2.1
  have hemb : Continuous fun c' : Fin (P.r - j) → ℂ => (c', gi j hj x.2) :=
    continuous_id.prodMk continuous_const
  have hev : (fun c' => (Ψ : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) c' (gi j hj x.2)) =ᶠ[𝓝 (cc j hj t x.1)]
      fun c' => F (c', gi j hj x.2) := by
    have hU' : ∀ᶠ c' in 𝓝 (cc j hj t x.1), (c', gi j hj x.2) ∈ U :=
      hemb.continuousAt.preimage_mem_nhds (hU.mem_nhds hyU)
    filter_upwards [hU'] with c' hc'
    exact hΨF (c', gi j hj x.2) hc' hg
  have hFd : DifferentiableAt ℝ (fun c' => F (c', gi j hj x.2)) (cc j hj t x.1) :=
    ((hF.contDiffAt (hU.mem_nhds hyU)).differentiableAt (by simp)).comp (cc j hj t x.1)
      (differentiableAt_id.prodMk (differentiableAt_const _))
  have hφ := (hFd.congr_of_eventuallyEq hev).hasFDerivAt
  have hφ' : HasFDerivAt (fun c' => (Ψ : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) c' (gi j hj x.2))
      (fderiv ℝ (fun c' => (Ψ : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) c' (gi j hj x.2)) (cc j hj t x.1))
      (cc j hj t x.1 + (0 : ℝ) • (Pi.single (⟨0, by omega⟩ : Fin (P.r - j)) v : Fin (P.r - j) → ℂ)) := by
    rw [zero_smul, add_zero]; exact hφ
  have hline := ((hasDerivAt_id (0 : ℝ)).smul_const
    (Pi.single (⟨0, by omega⟩ : Fin (P.r - j)) v : Fin (P.r - j) → ℂ)).const_add (cc j hj t x.1)
  rw [one_smul] at hline
  have hcomp := hφ'.comp_hasDerivAt (0 : ℝ) hline
  have hJ := h5 Wp Wq P T hP hT j hj hPs G hG t ht x hx v
  have hc : Continuous fun s : ℝ => t + (s : ℂ) * v :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hne : ∀ᶠ s : ℝ in 𝓝 0, t + (s : ℂ) * v ≠ 0 :=
    hc.continuousAt.eventually_ne (by simpa using ht)
  have heq : ((fun c' => (Ψ : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) c' (gi j hj x.2)) ∘
      fun s : ℝ => cc j hj t x.1 + id s • (Pi.single (⟨0, by omega⟩ : Fin (P.r - j)) v : Fin (P.r - j) → ℂ))
      =ᶠ[𝓝 0] fun s : ℝ =>
        resG P.k (P.r - (j + 1)) (Fin.last _) (B.JF (T.bs (j + 1)) (G (t + (s : ℂ) * v))) x.1 x.2 := by
    filter_upwards [hne] with s hs
    simp only [Function.comp, id]
    rw [← opc_cc_line]
    exact hR _ hs x hx
  exact hcomp.unique (hJ.congr_of_eventuallyEq heq)

end opc

theorem cutSH_opClosed_of (h2 : FamAlg) (h3 : FamDeriv) (h4 : RepLin) (h5 : FamJFDeriv) (h6 : CellTie) :
    OpClosed := by
  intro Wp Wq _ _ _ _ _ _ P T hP hT j hj hPj hPs X i Ψ hΨ
  obtain ⟨G, hG, hR⟩ := hΨ
  have hom : ∀ t : ℂ, t ≠ 0 → ∀ x ∈ DomR P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z',
      cc j hj t x.1 ∈ OmX (P.r - j) := fun t ht x hx => (h6 Wp Wq P T hP hT j hj hPj hPs t ht x hx).1.1
  have hD := fun v t ht x hx => opc_fderiv h5 h6 T hP hT j hj hPj hPs Ψ G hG hR t ht x hx v
  have hid : ContDiff ℝ ∞ (fun t : ℂ => t) := contDiff_id
  have hst : ContDiff ℝ ∞ (fun t : ℂ => star t) := Complex.conjCLE.contDiff
  fin_cases i
  · refine opc_two h2 h3 h4 hP hT hPs hG (fun t => t / 2) (fun t => -(t * Complex.I / 2))
      (hid.div_const 2).contDiffOn ((hid.mul contDiff_const).div_const 2).neg.contDiffOn 1 Complex.I
      (fun t ht x hx => ?_)
    rw [X.op_apply]
    change pOp (⟨0, by omega⟩ : Fin (P.r - j)) (fun c' => (Ψ : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) c' (gi j hj x.2))
      (cc j hj t x.1) = _
    unfold pOp
    rw [if_pos (hom t ht x hx), opc_cc_zero]
    unfold wirt
    rw [hD 1 t ht x hx, hD Complex.I t ht x hx]
    module
  · refine opc_mul h2 h4 hP hT hPs hG hR (fun t => t) hid.contDiffOn (fun t ht x hx => ?_)
    rw [X.op_apply]
    change cOp (⟨0, by omega⟩ : Fin (P.r - j)) (fun c' => (Ψ : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) c' (gi j hj x.2))
      (cc j hj t x.1) = _
    unfold cOp
    rw [opc_cc_zero]
  · refine opc_mul h2 h4 hP hT hPs hG hR (fun t => t⁻¹) (hid.contDiffOn.inv fun t ht => ht)
      (fun t ht x hx => ?_)
    rw [X.op_apply]
    change ciOp (⟨0, by omega⟩ : Fin (P.r - j)) (fun c' => (Ψ : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) c' (gi j hj x.2))
      (cc j hj t x.1) = _
    unfold ciOp
    rw [opc_cc_zero]
  · refine opc_two h2 h3 h4 hP hT hPs hG (fun t => star t / 2) (fun t => star t * Complex.I / 2)
      (hst.div_const 2).contDiffOn ((hst.mul contDiff_const).div_const 2).contDiffOn 1 Complex.I
      (fun t ht x hx => ?_)
    rw [X.op_apply]
    change pbOp (⟨0, by omega⟩ : Fin (P.r - j)) (fun c' => (Ψ : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) c' (gi j hj x.2))
      (cc j hj t x.1) = _
    unfold pbOp
    rw [if_pos (hom t ht x hx), opc_cc_zero]
    unfold wirtBar
    rw [hD 1 t ht x hx, hD Complex.I t ht x hx]
    module
  · refine opc_mul h2 h4 hP hT hPs hG hR (fun t => star t) hst.contDiffOn (fun t ht x hx => ?_)
    rw [X.op_apply]
    change cbOp (⟨0, by omega⟩ : Fin (P.r - j)) (fun c' => (Ψ : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) c' (gi j hj x.2))
      (cc j hj t x.1) = _
    unfold cbOp
    rw [opc_cc_zero]
  · refine opc_mul h2 h4 hP hT hPs hG hR (fun t => (star t)⁻¹)
      (hst.contDiffOn.inv fun t ht => star_ne_zero.mpr ht) (fun t ht x hx => ?_)
    rw [X.op_apply]
    change cbiOp (⟨0, by omega⟩ : Fin (P.r - j)) (fun c' => (Ψ : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) c' (gi j hj x.2))
      (cc j hj t x.1) = _
    unfold cbiOp
    rw [opc_cc_zero]

end Formalism.FourierDecayAlt.P.CutSH

theorem Formalism.FourierDecayAlt.P.cutSH_opClosed_of (h2 : Formalism.FourierDecayAlt.P.CutSH.FamAlg) (h3 : Formalism.FourierDecayAlt.P.CutSH.FamDeriv)
    (h4 : Formalism.FourierDecayAlt.P.CutSH.RepLin) (h5 : Formalism.FourierDecayAlt.P.CutSH.FamJFDeriv) (h6 : Formalism.FourierDecayAlt.P.CutSH.CellTie) :
    Formalism.FourierDecayAlt.P.CutSH.OpClosed :=
  Formalism.FourierDecayAlt.P.CutSH.cutSH_opClosed_of h2 h3 h4 h5 h6

theorem Formalism.FourierDecayAlt.P.cutSH_opClosed_of_famJFDeriv (h5 : Formalism.FourierDecayAlt.P.CutSH.FamJFDeriv) : Formalism.FourierDecayAlt.P.CutSH.OpClosed :=
  Formalism.FourierDecayAlt.P.CutSH.cutSH_opClosed_of Formalism.FourierDecayAlt.P.CutSH.family_algebraic Formalism.FourierDecayAlt.P.family_derivative
    Formalism.FourierDecayAlt.P.CutSH.representation_linear h5 Formalism.FourierDecayAlt.P.CutSH.cell_compatibility

theorem Formalism.FourierDecayAlt.P.operator_class_closed : Formalism.FourierDecayAlt.P.CutSH.OpClosed :=
  Formalism.FourierDecayAlt.P.cutSH_opClosed_of_famJFDeriv Formalism.FourierDecayAlt.P.family_orbital_derivative_identity
