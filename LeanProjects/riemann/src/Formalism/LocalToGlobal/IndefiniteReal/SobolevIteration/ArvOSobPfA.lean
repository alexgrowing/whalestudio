import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.ArvOSobPfSt
import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.OrbStPf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChainRuleSmooth.ExpIntertwine

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Mult
  MeasureTheory Matrix Filter Topology
open scoped ContDiff

namespace Formalism.IndefR.Tow.SobPf

section Gen

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem one_mem_UH (G : Matrix (Fin n) (Fin n) ℂ) : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ Formalism.QuantumDeterminants.UH G := by
  show (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * G * 1 = G
  simp

theorem zero_mem_lieG (G : Matrix (Fin n) (Fin n) ℂ) : (0 : Matrix (Fin n) (Fin n) ℂ) ∈ lieG G := by
  show (0 : Matrix (Fin n) (Fin n) ℂ)ᴴ * G + G * 0 = 0
  simp

theorem expS_mem_UH {G X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieG G) (t : ℝ) :
    NormedSpace.exp (t • X) ∈ Formalism.QuantumDeterminants.UH G := by
  have h := CCRuleCW.lie_smul G X hX t
  rw [Complex.coe_smul] at h
  exact CCRuleCW.exp_mem_UH G (t • X) h

theorem mul_mem_UH₂ (G : Matrix (Fin n) (Fin n) ℂ) :
    ∀ a ∈ Formalism.QuantumDeterminants.UH G, ∀ b ∈ Formalism.QuantumDeterminants.UH G, a * b ∈ Formalism.QuantumDeterminants.UH G := by
  intro a ha b hb
  have ha' : aᴴ * G * a = G := ha
  have hb' : bᴴ * G * b = G := hb
  show (a * b)ᴴ * G * (a * b) = G
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * G * (a * b) = bᴴ * (aᴴ * G * a) * b := by simp only [Matrix.mul_assoc]
    _ = G := by rw [ha', hb']

theorem smoothLin_holds : SmoothLin := by
  intro n H _ _ G π hπ
  exact ⟨OrbStPf.smoothVec_zero, fun c u v hu hv =>
    OrbStPf.smoothVec_add (OrbStPf.smoothVec_smul c hu) hv⟩

theorem foldLin_holds : FoldLin := by
  intro n H _ _ G π hπ l hl c u v hu hv
  have h := OrbStPf.word_lin (one_mem_UH G) (mul_mem_UH₂ G) hπ.2.1 (fun Y hY t => expS_mem_UH hY t) hπ.1 l hl
    (zero_mem_lieG G) hv hu c
  unfold dL
  rw [add_comm (c • u), h, add_comm]

theorem smooth_oneProd {G : Matrix (Fin n) (Fin n) ℂ} {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hπ : IsGRep G π) {w : H} (hw : SmoothVec (lieG G) π w) :
    ∀ {d : ℕ} (Y : Fin d → Matrix (Fin n) (Fin n) ℂ), (∀ i, Y i ∈ lieG G) → ∀ t : Fin d → ℝ,
      SmoothVec (lieG G) π (π (oneProd Y t) w) ∧ oneProd Y t ∈ Formalism.QuantumDeterminants.UH G := by
  intro d
  induction d with
  | zero =>
    intro Y _ t
    simp only [oneProd, List.ofFn_zero, List.prod_nil, hπ.1]
    exact ⟨hw, one_mem_UH G⟩
  | succ d ih =>
    intro Y hY t
    have e : oneProd Y t = NormedSpace.exp (t 0 • Y 0) * oneProd (fun i => Y i.succ) (fun i => t i.succ) := by
      simp [oneProd, List.ofFn_succ]
    obtain ⟨h1, h2⟩ := ih (fun i => Y i.succ) (fun i => hY _) (fun i => t i.succ)
    rw [e, hπ.2.1 _ (expS_mem_UH (hY 0) _) _ h2]
    exact ⟨OrbStPf.smoothVec_rep_exp (one_mem_UH G) (mul_mem_UH₂ G) hπ.2.1 (fun Y hY t => expS_mem_UH hY t) (hY 0) (t 0) h1,
      mul_mem_UH₂ G _ (expS_mem_UH (hY 0) _) _ h2⟩

end Gen

section Append

theorem append_line {N d : ℕ} (r : Fin N → ℝ) (t : Fin d → ℝ) (i : Fin N) (s : ℝ) :
    Fin.append (r + s • Pi.single i 1) t = Fin.append r t + s • Pi.single (Fin.castAdd d i) 1 := by
  funext j
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · simp [Pi.single_apply, Fin.castAdd_inj]
  · have hne : (Fin.natAdd N j : Fin (N + d)) ≠ Fin.castAdd d i := by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.coe_natAdd, Fin.coe_castAdd] at this
      omega
    simp [Pi.single_apply, hne]

theorem contDiff_append_left {N d : ℕ} (t : Fin d → ℝ) : ContDiff ℝ ∞ (fun r : Fin N → ℝ => Fin.append r t) := by
  refine contDiff_pi.2 fun j => ?_
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · simp only [Fin.append_left]
    exact contDiff_apply ℝ ℝ j
  · simp only [Fin.append_right]
    exact contDiff_const

theorem continuous_append_right {N d : ℕ} (r : Fin N → ℝ) :
    Continuous (fun t : Fin d → ℝ => Fin.append r t) := by
  refine continuous_pi fun j => ?_
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · simp only [Fin.append_left]
    exact continuous_const
  · simp only [Fin.append_right]
    exact continuous_apply j

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem pd_append {N d : ℕ} (f : (Fin (N + d) → ℝ) → E) (hf : Differentiable ℝ f) (t : Fin d → ℝ) (i : Fin N) :
    OrbStPf.pd i (fun r => f (Fin.append r t)) = fun r => OrbStPf.pd (Fin.castAdd d i) f (Fin.append r t) := by
  funext r
  simp only [OrbStPf.pd]
  have hg : Differentiable ℝ (fun r : Fin N → ℝ => Fin.append r t) :=
    (contDiff_infty_iff_fderiv.1 (contDiff_append_left t)).1
  rw [fderiv_comp' r (hf _) (hg r), ContinuousLinearMap.comp_apply]
  congr 1
  have h1 : HasDerivAt (fun s : ℝ => Fin.append (r + s • (Pi.single i 1 : Fin N → ℝ)) t)
      (fderiv ℝ (fun r : Fin N → ℝ => Fin.append r t) r (Pi.single i 1)) 0 := by
    have hl : HasDerivAt (fun s : ℝ => r + s • (Pi.single i 1 : Fin N → ℝ)) (Pi.single i 1) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single i 1 : Fin N → ℝ)).const_add r
    have h3 := (hg (r + (0 : ℝ) • (Pi.single i 1 : Fin N → ℝ))).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hl
    rw [zero_smul, add_zero] at h3
    exact h3
  have h2 : HasDerivAt (fun s : ℝ => Fin.append (r + s • (Pi.single i 1 : Fin N → ℝ)) t)
      (Pi.single (Fin.castAdd d i) 1) 0 := by
    simp only [append_line]
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const
      (Pi.single (Fin.castAdd d i) 1 : Fin (N + d) → ℝ)).const_add (Fin.append r t)
  exact h1.unique h2

private theorem pds_contDiff_lemma {N : ℕ} (L : List (Fin N)) (f : (Fin N → ℝ) → E)
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (OrbStPf.pds L f) := by
  induction L with
  | nil => exact hf
  | cons a L ih =>
    show ContDiff ℝ ∞ (fun p => fderiv ℝ (OrbStPf.pds L f) p (Pi.single a 1))
    exact (contDiff_infty_iff_fderiv.1 ih).2.clm_apply contDiff_const

theorem pds_append {N d : ℕ} (L : List (Fin N)) (f : (Fin (N + d) → ℝ) → E) (hf : ContDiff ℝ ∞ f)
    (t : Fin d → ℝ) :
    OrbStPf.pds L (fun r => f (Fin.append r t)) =
      fun r => OrbStPf.pds (L.map (Fin.castAdd d)) f (Fin.append r t) := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    have hg : ContDiff ℝ ∞ (OrbStPf.pds (L.map (Fin.castAdd d)) f) := pds_contDiff_lemma _ f hf
    show OrbStPf.pd a (OrbStPf.pds L fun r => f (Fin.append r t)) =
      fun r => OrbStPf.pd (Fin.castAdd d a) (OrbStPf.pds (L.map (Fin.castAdd d)) f) (Fin.append r t)
    rw [ih]
    exact pd_append _ (contDiff_infty_iff_fderiv.1 hg).1 t a

end Append

theorem foldCont_holds : FoldCont := by
  intro n H _ _ G π hπ w hw l hl d Y hY
  have hexp : ∀ Y ∈ lieG G, ∀ t : ℝ, NormedSpace.exp (t • Y) ∈ Formalism.QuantumDeterminants.UH G := fun Y hY t => expS_mem_UH hY t
  obtain ⟨Z, L, hZ, -, hval⟩ := OrbStPf.word_eval (one_mem_UH G) (mul_mem_UH₂ G) hπ.2.1 hexp l hl (zero_mem_lieG G)
  set W : Fin (l.length + 1 + d) → Matrix (Fin n) (Fin n) ℂ := Fin.append Z Y with hWdef
  have hW : ∀ i, W i ∈ lieG G := fun i =>
    Fin.addCases (fun a => by simpa [W, Fin.append_left] using hZ a) (fun b => by simpa [W, Fin.append_right] using hY b) i
  have hG : ContDiff ℝ ∞ (OrbStPf.orb π W w 0) := OrbStPf.contDiff_orb W hW hw 0
  have key : ∀ t, dL π l (π (oneProd Y t) w) =
      OrbStPf.pds (L.map (Fin.castAdd d)) (OrbStPf.orb π W w 0) (Fin.append 0 t) := by
    intro t
    have hv := (smooth_oneProd hπ hw Y hY t)
    have h0 := hval _ hv.1 0
    simp only [zero_smul, NormedSpace.exp_zero, hπ.1, ContinuousLinearMap.one_apply] at h0
    have e : OrbStPf.orb π Z (π (oneProd Y t) w) 0 = fun r => OrbStPf.orb π W w 0 (Fin.append r t) := by
      funext r
      have hA : (List.ofFn fun i => NormedSpace.exp (r i • Z i)).prod ∈ Formalism.QuantumDeterminants.UH G :=
        OrbStPf.list_prod_mem (one_mem_UH G) (mul_mem_UH₂ G) _ (fun a ha => by
          obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ha; exact hexp _ (hZ _) _)
      simp only [OrbStPf.orb, List.drop_zero]
      rw [List.ofFn_add (m := d), List.prod_append]
      have e1 : ∀ i : Fin (l.length + 1), Fin.append r t (Fin.castLE (Nat.le_add_right _ d) i) = r i :=
        fun i => Fin.append_left r t i
      have e2 : ∀ i : Fin (l.length + 1), Fin.append Z Y (Fin.castLE (Nat.le_add_right _ d) i) = Z i :=
        fun i => Fin.append_left Z Y i
      simp only [W, e1, e2, Fin.append_right]
      rw [show (List.ofFn fun j : Fin d => NormedSpace.exp (t j • Y j)).prod = oneProd Y t from rfl,
        hπ.2.1 _ hA _ hv.2]
      rfl
    unfold dL
    rw [h0, e, pds_append L _ hG t]
  rw [show (fun t => dL π l (π (oneProd Y t) w)) =
      fun t => OrbStPf.pds (L.map (Fin.castAdd d)) (OrbStPf.orb π W w 0) (Fin.append 0 t) from funext key]
  exact (OrbStPf.contDiff_pds _ hG).continuous.comp (continuous_append_right 0)

attribute [local instance] Formalism.BasicNotions.Host.cmStar in
theorem sobRepM_holds (D : D7) : SobRepM D := by
  intro S Ss M τ
  have hds := M.ds τ
  have hfr := M.fr_unit τ
  have hconj : ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D S τ),
      M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.MainNotions.S.UJset (M.ε τ) := fun g hg =>
    OrbStPf.conj_mem _ _ _ _ hfr (M.fr_gram τ) hg
  refine ⟨hds.1, OrbStPf.rep_one M τ, fun a ha b hb => OrbStPf.rep_mul M τ a b ha hb,
    fun g hg v => hds.2.2.1.2.1 _ (hconj g hg) v, fun v => ?_⟩
  have hc : Continuous fun g : Matrix (Fin S.rank) (Fin S.rank) ℂ => M.fr τ * g * (M.fr τ)⁻¹ :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  exact (hds.2.2.1.2.2 v).comp hc.continuousOn (fun g hg => hconj g hg)

end Formalism.IndefR.Tow.SobPf

end
