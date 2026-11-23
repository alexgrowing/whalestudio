import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSH2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelPointCoordinates

open MeasureTheory
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSH

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.PBH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem fsv_zero' (t : ℂ) : fsv 0 t = 1 := by simp [fsv]

theorem fsv_mul' (s s' t : ℂ) : fsv s t * fsv s' t = fsv (s + s') t := by
  unfold fsv
  rw [← Complex.exp_add]
  congr 1
  simp only [map_add]
  ring

theorem fsv_contDiff' (s : ℂ) : ContDiff ℝ ∞ (fsv s) := by
  have hc : ContDiff ℝ ∞ (fun t : ℂ => conj t) := Complex.conjCLE.contDiff
  have h1 : ContDiff ℝ ∞ (fun t : ℂ => s * t - conj s * conj t) :=
    (contDiff_const.mul contDiff_id).sub (contDiff_const.mul hc)
  have he : ContDiff ℝ ∞ Complex.exp := Complex.contDiff_exp
  exact he.comp h1

section asm

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem cc_zero {P : M.Par} (j : ℕ) (hj : j + 1 ≤ P.r) (t : ℂ) (c : Fin (P.r - (j + 1)) → ℂ) :
    cc j hj t c ⟨0, by omega⟩ = t := by
  simp [cc, consC]

theorem vw_entry (hU : UUiwScalar) {V : Type} [AddCommGroup V] [Module ℂ V] (S : Type) [Fintype S] [DecidableEq S]
    (Wv Wv' : Module.End ℂ V) (s : ℂ) (w : List (Wd.Letter ℂ S)) (a b : Wd.Ix S) :
    ∃ lam : ℂ, ∀ Φ : V, (Wd.Vw (mkP Wv Wv') s w a b).1 Φ = lam • Wv Φ := by
  obtain ⟨lam, hlam⟩ := Algebra.mem_bot.1 (hU (Pr V) S s w a b)
  refine ⟨lam, fun Φ => ?_⟩
  have hab : Wd.Vw (mkP Wv Wv') s w a b = mkP Wv Wv' * Wd.UUiw (A := Pr V) s w a b := by
    simp [Wd.Vw, Wd.io, Matrix.scalar_apply, Matrix.diagonal_mul]
  rw [hab, ← hlam]
  change (Wv * algebraMap ℂ (Module.End ℂ V) lam) Φ = _
  rw [Module.End.mul_apply, Module.algebraMap_end_apply, map_smul]

theorem class0_form (hU : UUiwScalar) (S : Type) [Fintype S] [DecidableEq S] (P : M.Par)
    (T : D.LevTower P.k P.r Wp Wq) (j : ℕ) (hj : j + 1 ≤ P.r)
    (Lj : R.LevelData (Pr (RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')) (P.r - j))
    (stj : Fr.Start (Pr (RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'))) (l0 : ℕ) :
    ∀ (i : Fin ((JC.parLev P j).r + 1))
      (Ψ : RadSp (JC.parLev P j).k (JC.parLev P j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'),
      HerGenC S (JC.parLev P j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' Lj stj l0 (T.bs j) i Ψ → i = 0 →
      ∃ (F : B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp))
        (Φ : RadSp (JC.parLev P j).k (JC.parLev P j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π') (s κ : ℂ),
        JFOKCpt (JC.parLev P j) (T.bs j).z (T.bs j).z' F ∧
        IsRadJF (JC.parLev P j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' (T.bs j) F Φ ∧
        ∀ c g, (Ψ : Fn (JC.parLev P j).k (JC.parLev P j).r (Wq →L[ℂ] Wp)) c g =
          (κ * fsv s (c ⟨0, by change 0 < P.r - j; omega⟩)) •
            (Φ : Fn (JC.parLev P j).k (JC.parLev P j).r (Wq →L[ℂ] Wp)) c g := by
  intro i Ψ h
  induction h with
  | jf F Φ hF hΦ =>
    intro _
    exact ⟨F, Φ, 0, 1, hF, hΦ, fun c g => by simp [fsv_zero']⟩
  | slice l w a b Φ hw hΦ ih =>
    intro h
    exact absurd h (Fin.succ_ne_zero l)
  | waveC l w s Wv Wv' a b Φ hw hW hW' hΦ ih =>
    intro h
    have hl0 : l.val = 0 := by
      have := congrArg Fin.val h
      simpa using this
    obtain ⟨F, Φ0, s0, κ0, hF, hΦ0, hv⟩ := ih h
    obtain ⟨lam, hlam⟩ := vw_entry hU S Wv Wv' s w a b
    refine ⟨F, Φ0, s + s0, lam * κ0, hF, hΦ0, fun c g => ?_⟩
    have hcl : c l = c ⟨0, by change 0 < P.r - j; omega⟩ := congrArg c (Fin.ext hl0)
    rw [hlam, Submodule.coe_smul, Pi.smul_apply, Pi.smul_apply, hW, hv, smul_smul, smul_smul]
    beta_reduce
    rw [hcl, ← fsv_mul']
    congr 1
    ring
  | waveZ w s Wv Wv' a b Φ hw hW hW' hΦ ih =>
    intro h
    have := congrArg Fin.val h
    simp [JC.parLev] at this
    omega

variable {P : M.Par} {T : D.LevTower P.k P.r Wp Wq} {j : ℕ} {hj : j + 1 ≤ P.r}

theorem inC_add (h2 : FamAlg) (h4 : RepLin) (hP : IsPlace P T.base.z T.base.z' T.base.π T.base.π')
    (hT : D.TowerNormalised T)
    (hPs : IsPlace (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π')
    {Ψ Ψ' : RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'}
    (h : InC T j hj Ψ) (h' : InC T j hj Ψ') : InC T j hj (Ψ + Ψ') := by
  obtain ⟨G, hG, hR⟩ := h
  obtain ⟨G', hG', hR'⟩ := h'
  refine ⟨fun t γ => G t γ + G' t γ, (h2 Wp Wq P T j G G' hG hG' (fun _ => 1) contDiffOn_const).1,
    fun t ht x hx => ?_⟩
  rw [Submodule.coe_add, Pi.add_apply, Pi.add_apply, hR t ht x hx, hR' t ht x hx,
    (h4 Wp Wq P T hP hT j hj hPs G G' hG hG' t ht 0 x hx).1]

theorem inC_smul (h2 : FamAlg) (h4 : RepLin) (hP : IsPlace P T.base.z T.base.z' T.base.π T.base.π')
    (hT : D.TowerNormalised T)
    (hPs : IsPlace (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π')
    {Ψ : RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'}
    (h : InC T j hj Ψ) (a : ℂ) : InC T j hj (a • Ψ) := by
  obtain ⟨G, hG, hR⟩ := h
  refine ⟨fun t γ => a • G t γ, (h2 Wp Wq P T j G G hG hG (fun _ => a) contDiffOn_const).2,
    fun t ht x hx => ?_⟩
  rw [Submodule.coe_smul, Pi.smul_apply, Pi.smul_apply, hR t ht x hx,
    (h4 Wp Wq P T hP hT j hj hPs G G hG hG t ht a x hx).2]

theorem inC_seed (h6 : CellTie) (h7 : SliceFamGood) (h8 : SliceFamJF)
    (hP : IsPlace P T.base.z T.base.z' T.base.π T.base.π') (hT : D.TowerNormalised T)
    (hPj : IsPlace (JC.parLev P j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')
    (hPs : IsPlace (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π')
    (F : B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) (hF : JFOKCpt (JC.parLev P j) (T.bs j).z (T.bs j).z' F)
    (Φ : RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')
    (hΦ : IsRadJF (JC.parLev P j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' (T.bs j) F Φ) :
    InC T j hj Φ := by
  refine ⟨sliceFam T j hj F, h7 Wp Wq P T hP hT j hj hPj hPs F hF, fun t ht x hx => ?_⟩
  obtain ⟨hdom, hGV, hOm⟩ := h6 Wp Wq P T hP hT j hj hPj hPs t ht x hx
  have e1 : (Φ : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) (cc j hj t x.1) (gi j hj x.2) =
      resG P.k (P.r - j) (Fin.last _) (B.JF (T.bs j) F) (cc j hj t x.1) (gi j hj x.2) :=
    hΦ (cc j hj t x.1, gi j hj x.2) hdom
  have e2 := Formalism.FourierDecayAlt.P.PBP.resG_cast (k := P.k) (ρ := P.r - (j + 1)) (n := P.r - j) (by omega) ht
    (B.JF (T.bs j) F) x.1 x.2
  rw [e1]
  refine e2.trans ?_
  unfold resG
  rw [h8 Wp Wq P T hP hT j hj hPj hPs F hF t ht _ hGV hOm, smul_comm]
  congr 2

theorem inC_wave (h2 : FamAlg) (h4 : RepLin) (hP : IsPlace P T.base.z T.base.z' T.base.π T.base.π')
    (hT : D.TowerNormalised T)
    (hPs : IsPlace (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π')
    {Φ Ψ : RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'} (s κ : ℂ)
    (hv : ∀ c g, (Ψ : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) c g =
      (κ * fsv s (c ⟨0, by omega⟩)) • (Φ : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) c g)
    (h : InC T j hj Φ) : InC T j hj Ψ := by
  obtain ⟨G, hG, hR⟩ := h
  have hm : ContDiffOn ℝ ∞ (fun t : ℂ => κ * fsv s t) {t | t ≠ 0} :=
    (contDiff_const.mul (fsv_contDiff' s)).contDiffOn
  refine ⟨fun t γ => (κ * fsv s t) • G t γ, (h2 Wp Wq P T j G G hG hG _ hm).2, fun t ht x hx => ?_⟩
  rw [hv, cc_zero, hR t ht x hx, (h4 Wp Wq P T hP hT j hj hPs G G hG hG t ht _ x hx).2]

theorem inC_adjoin (h2 : FamAlg) (h4 : RepLin) (h9 : OpClosed)
    (hP : IsPlace P T.base.z T.base.z' T.base.π T.base.π') (hT : D.TowerNormalised T)
    (hPj : IsPlace (JC.parLev P j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')
    (hPs : IsPlace (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π')
    (X : ActualOps P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')
    (A : Module.End ℂ (RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'))
    (hA : A ∈ Algebra.adjoin ℂ (Set.range (X.op ⟨0, by omega⟩))) :
    ∀ Ψ, InC T j hj Ψ → InC T j hj (A Ψ) := by
  induction hA using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact fun Ψ h => h9 Wp Wq P T hP hT j hj hPj hPs X i Ψ h
  | algebraMap r =>
    intro Ψ h
    rw [Module.algebraMap_end_apply]
    exact inC_smul h2 h4 hP hT hPs h r
  | add x y _ _ hx hy =>
    intro Ψ h
    rw [LinearMap.add_apply]
    exact inC_add h2 h4 hP hT hPs (hx Ψ h) (hy Ψ h)
  | mul x y _ _ hx hy =>
    intro Ψ h
    rw [Module.End.mul_apply]
    exact hx _ (hy Ψ h)

theorem herKc_jf' {S : Type} [Fintype S] [DecidableEq S] {P : M.Par} {z z' : Fin (2 * P.r + P.k + 1) → ℂ}
    {π : Mx P.k P.r → (Wp →L[ℂ] Wp)} {π' : Mx P.k P.r → (Wq →L[ℂ] Wq)}
    {L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r} {st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))} {l0 : ℕ}
    {D : B.RealPlaceData P.k P.r Wp Wq} (F : Mx P.k P.r → (Wq →L[ℂ] Wp)) (hF : JFOKCpt P z z' F)
    (Φ : RadSp P.k P.r z z' π π') (hΦ : IsRadJF P z z' π π' D F Φ) : Φ ∈ herKc S P z z' π π' L st l0 D 0 :=
  Submodule.subset_span (HerGenC.jf F Φ hF hΦ)

theorem span_step
    (Tt : RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' →ₗ[ℂ]
      RadSp P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π')
    (A : Module.End ℂ (RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'))
    (K : Submodule ℂ (RadSp P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π'))
    (s : Set (RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')) (hgen : ∀ Ψ ∈ s, Tt (A Ψ) ∈ K) :
    ∀ Ψ ∈ Submodule.span ℂ s, Tt (A Ψ) ∈ K := by
  intro Ψ hΨ
  induction hΨ using Submodule.span_induction with
  | mem x hx => exact hgen x hx
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add]; exact K.add_mem hx hy
  | smul r x _ hx => rw [map_smul, map_smul]; exact K.smul_mem r hx

end asm

theorem sliceStepHer_of (h1 : FamJFOK) (h2 : FamAlg) (h4 : RepLin) (h6 : CellTie) (h7 : SliceFamGood)
    (h8 : SliceFamJF) (h9 : OpClosed) (h10 : BTlAdjoin) (h11 : UUiwScalar) : PTie.SliceStepHer := by
  intro Wp Wq _ _ _ _ _ _ P T hP hT j hj l0 _ _ Xj μj Lj stj Xs μs Ls sts hDj hDs Tt t ht hTt S _ _ w a b hw Ψ hΨ
  have hPj := hDj.1
  have hPs := hDs.1
  have hAct := hDj.2.2.1
  have hA := h10 Wp Wq P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' Xj Lj hAct S
    ⟨0, by change 0 < P.r - j; omega⟩ w a b
  have hΨ' : Ψ ∈ Submodule.span ℂ
      {Φ | HerGenC S (JC.parLev P j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' Lj stj l0 (T.bs j) 0 Φ} := hΨ
  refine span_step (P := P) (T := T) (j := j) Tt (bTl Lj ⟨0, by change 0 < P.r - j; omega⟩ w a b).1
    (herKc S (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π' Ls sts
      l0 (T.bs (j + 1)) 0) _ (fun Ψ hg => ?_) Ψ hΨ'
  obtain ⟨F, Φ, s, κ, hF, hΦ, hv⟩ := class0_form h11 S P T j hj Lj stj l0 0 Ψ hg rfl
  have hC0 : InC T j hj Φ := inC_seed h6 h7 h8 hP hT hPj hPs F hF Φ hΦ
  have hC : InC T j hj Ψ := inC_wave (Φ := Φ) h2 h4 hP hT hPs s κ hv hC0
  obtain ⟨G, hG, hR⟩ := inC_adjoin h2 h4 h9 hP hT hPj hPs Xj _ hA Ψ hC
  have hJ := h1 Wp Wq P T j G hG t ht
  have hRad : IsRadJF (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π'
      (T.bs (j + 1)) (G t) (Tt ((bTl Lj ⟨0, by change 0 < P.r - j; omega⟩ w a b).1 Ψ)) := fun x hx =>
    (hTt _ x.1 x.2).trans (hR t ht x hx)
  exact herKc_jf' (S := S) (P := JC.parLev P (j + 1)) (L := Ls) (st := sts) (l0 := l0) (G t) hJ _ hRad

end Formalism.FourierDecayAlt.P.CutSH

namespace Formalism.FourierDecayAlt.P

end Formalism.FourierDecayAlt.P
