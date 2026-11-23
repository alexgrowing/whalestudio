import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open scoped ContDiff ComplexOrder

namespace GlobalTheory.ShFam.InterpSmooth

variable {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℝ E'] {U : Set E'}

theorem contDiffOn_iff_re_im {f : E' → ℂ} : ContDiffOn ℝ ∞ f U ↔
    ContDiffOn ℝ ∞ (fun v => (f v).re) U ∧ ContDiffOn ℝ ∞ (fun v => (f v).im) U := by
  refine ⟨fun h => ⟨Complex.reCLM.contDiff.comp_contDiffOn h, Complex.imCLM.contDiff.comp_contDiffOn h⟩, fun h => ?_⟩
  have := (Complex.ofRealCLM.contDiff.comp_contDiffOn h.1).add
    ((Complex.ofRealCLM.contDiff.comp_contDiffOn h.2).mul (contDiffOn_const (c := Complex.I)))
  refine this.congr fun v _ => ?_
  simp [Complex.re_add_im]

variable {n : ℕ}

def EntSm (A : E' → Matrix (Fin n) (Fin n) ℂ) (U : Set E') : Prop := ∀ a b, ContDiffOn ℝ ∞ (fun v => A v a b) U

theorem det_sm {A : E' → Matrix (Fin n) (Fin n) ℂ} (h : EntSm A U) : ContDiffOn ℝ ∞ (fun v => (A v).det) U := by
  simp only [Matrix.det_apply']
  exact ContDiffOn.sum fun σ _ => contDiffOn_const.mul (contDiffOn_prod fun i _ => h _ _)

theorem inv_sm {A : E' → Matrix (Fin n) (Fin n) ℂ} (h : EntSm A U) (h0 : ∀ v ∈ U, (A v).det ≠ 0) :
    EntSm (fun v => (A v)⁻¹) U := by
  intro a b
  have hadj : ContDiffOn ℝ ∞ (fun v => (A v).adjugate a b) U := by
    simp only [Matrix.adjugate_apply]
    refine det_sm (A := fun v => (A v).updateRow b (Pi.single a 1)) fun i k => ?_
    by_cases hi : i = b
    · simp only [Matrix.updateRow_apply, hi, ↓reduceIte]
      exact contDiffOn_const
    · simp only [Matrix.updateRow_apply, hi, ↓reduceIte]
      exact h _ _
  refine (((det_sm h).inv h0).mul hadj).congr fun v _ => ?_
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, Pi.inv_apply]

theorem mix_sm {s : E' → ℝ} {A B : E' → Matrix (Fin n) (Fin n) ℂ} (hs : ContDiffOn ℝ ∞ s U) (hA : EntSm A U)
    (hB : EntSm B U) : EntSm (fun v => mix (s v) (A v) (B v)) U := fun a b => by
  have hs' : ContDiffOn ℝ ∞ (fun v => ((s v : ℝ) : ℂ)) U := Complex.ofRealCLM.contDiff.comp_contDiffOn hs
  have h1 : ContDiffOn ℝ ∞ (fun v => ((1 - s v : ℝ) : ℂ)) U :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_const.sub hs)
  refine ((h1.mul (hA a b)).add (hs'.mul (hB a b))).congr fun v _ => ?_
  simp only [mix, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]

theorem dual_sm {A : E' → Matrix (Fin n) (Fin n) ℂ} (hA : EntSm A U) (hp : ∀ v ∈ U, (A v).PosDef) :
    EntSm (fun v => dualGram (A v)) U :=
  fun a b => (inv_sm hA (fun v hv => (hp v hv).det_pos.ne') b a).congr fun _ _ => rfl

theorem mixDual_sm {s : E' → ℝ} {A B : E' → Matrix (Fin n) (Fin n) ℂ} (hs : ContDiffOn ℝ ∞ s U) (hA : EntSm A U)
    (hB : EntSm B U) (hpA : ∀ v ∈ U, (A v).PosDef) (hpB : ∀ v ∈ U, (B v).PosDef)
    (hs01 : ∀ v ∈ U, s v ∈ Set.Icc (0 : ℝ) 1) : EntSm (fun v => mixDual (s v) (A v) (B v)) U :=
  dual_sm (mix_sm hs (dual_sm hA hpA) (dual_sm hB hpB)) fun v hv =>
    mix_posDef (hs01 v hv) (dualGram_posDef (hpA v hv)) (dualGram_posDef (hpB v hv))

theorem ite_sm {c : Prop} [Decidable c] {A B : E' → Matrix (Fin n) (Fin n) ℂ} (hA : EntSm A U) (hB : EntSm B U) :
    EntSm (fun v => if c then A v else B v) U := by
  by_cases hc : c
  · simp only [hc, ↓reduceIte]; exact hA
  · simp only [hc, ↓reduceIte]; exact hB

theorem spMap_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

end GlobalTheory.ShFam.InterpSmooth

namespace GlobalTheory.ShFam

open InterpSmooth

theorem ToroidalCompactificationData.smoothOn_eigMetAt_some : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ)
    (x : ToroidalCompactificationData s) (σ : κ.c.F →+* ℂ) (R : ℝ), 2 ≤ R →
    (x.hodge σ).SmoothOn (manifold s.T.Z σ) {y | ¬ LiesIn y (genBd s.T.Z)} →
    (x.eigMetAt σ (some R)).SmoothOn (manifold s.T.Z σ) Set.univ := by
  intro D A N j S κ s x σ R hR hH V φ F τ a b hφ
  classical
  set P := ptsIn (genStr s.T.Z) σ V.1 with hP
  set Bc := {y : CxPts (genStr s.T.Z) σ | ¬ LiesIn y (genBd s.T.Z)} with hBc
  have hBo : IsOpen Bc := isOpen_not_liesIn _

  have hphi : ∀ y (hy : y ∈ P), σ = (evHom hy).comp φ := fun y hy => by
    have e : spMap σ = spMap ((evHom hy).comp φ) := by
      rw [← y.2, ← spMap_evHom hy, Category.assoc, hφ, ← Spec.map_comp]; rfl
    exact spMap_inj e
  have hfr : ∀ y (hy : y ∈ P), ∃ f : EigFrame s.T.Z σ (y.1 ≫ genι s.T.Z), F.IsMap (evHom hy) f := fun y hy =>
    F.exists_isMap (evHom hy) (hphi y hy) (by rw [← Category.assoc, spMap_evHom hy])
  have huniq : ∀ y (hy : y ∈ P) (f f' : EigFrame s.T.Z σ (y.1 ≫ genι s.T.Z)), F.IsMap (evHom hy) f →
      F.IsMap (evHom hy) f' → f = f' := fun y hy f f' hf hf' => by
    have e : f.v = f'.v := funext fun τ => funext fun i => (hf τ i).trans (hf' τ i).symm
    cases f; cases f'
    cases e
    rfl

  choose g0 hg0r hg0i hg0 using fun a' b' => x.smoothOn_eigMet σ V φ F τ a' b' hφ
  choose g1 hg1r hg1i hg1 using fun a' b' => hH V φ F τ a' b' hφ
  let M0 := fun y => Matrix.of fun a' b' => g0 a' b' y
  let M1 := fun y => Matrix.of fun a' b' => g1 a' b' y
  have e0 : ∀ y (hy : y ∈ P) f, F.IsMap (evHom hy) f → (x.eigMet σ).gram y f τ = M0 y := fun y hy f hf =>
    Matrix.ext fun a' b' => hg0 a' b' y (Set.mem_univ y) hy f hf
  have e1 : ∀ y (hy : y ∈ P), y ∈ Bc → ∀ f, F.IsMap (evHom hy) f → (x.hodge σ).gram y f τ = M1 y :=
    fun y hy hb f hf => Matrix.ext fun a' b' => hg1 a' b' y hb hy f hf
  have p0 : ∀ y ∈ P, (M0 y).PosDef := fun y hy => by
    obtain ⟨f, hf⟩ := hfr y hy
    exact e0 y hy f hf ▸ (x.eigMet σ).pos y f τ
  have p1 : ∀ y ∈ P, y ∈ Bc → (M1 y).PosDef := fun y hy hb => by
    obtain ⟨f, hf⟩ := hfr y hy
    exact e1 y hy hb f hf ▸ (x.hodge σ).pos y f τ

  let g : CxPts (genStr s.T.Z) σ → ℂ := fun y =>
    if hy : y ∈ P then (x.eigMetAt σ (some R)).gram y (hfr y hy).choose τ a b else 0
  have hg : ∀ y (hy : y ∈ P) f, F.IsMap (evHom hy) f → (x.eigMetAt σ (some R)).gram y f τ a b = g y :=
    fun y hy f hf => by
      simp only [g, dif_pos hy]
      rw [huniq y hy f _ hf (hfr y hy).choose_spec]

  set W := {y : CxPts (genStr s.T.Z) σ | (∏ i, x.nrm σ i y) ^ 2 < Real.exp (Real.exp 1 - R ^ 3)} with hW
  have hcont : ∀ i, Continuous (x.nrm σ i) := fun i => continuous_iff_continuousAt.2 fun y => by
    obtain ⟨V', t, f, hy, -, hf, e⟩ := (x.nrm_div σ i).2 y
    have ho := isOpen_ptsIn (p := genStr s.T.Z) (σ := σ) V'.1
    have h1 : ContinuousOn (fun z => √(‖ev (genStr s.T.Z) σ V'.1 t z‖ ^ 2 * Real.exp (-f z))) (ptsIn _ σ V'.1) :=
      (((((manifold s.T.Z σ).holoOn_ev V'.1 t).continuousOn ho).norm.pow 2).mul
        ((hf.continuousOn ho).neg.rexp)).sqrt
    refine (h1.continuousAt (ho.mem_nhds hy)).congr (Filter.eventuallyEq_of_mem (ho.mem_nhds hy) fun z hz => ?_)
    rw [← e z hz, Real.sqrt_sq ((x.nrm_div σ i).1 z).1]
  have hWo : IsOpen W := isOpen_lt ((continuous_finset_prod _ fun i _ => hcont i).pow 2) continuous_const
  have hWbd : ∀ y, LiesIn y (genBd s.T.Z) → y ∈ W := fun y hy => by
    obtain ⟨i, hi⟩ := (x.liesIn_genBd_iff y).1 hy
    have h0 : x.nrm σ i y = 0 :=
      le_antisymm (not_lt.1 fun h => ((x.nrm_div σ i).pos_iff y).1 h hi) ((x.nrm_div σ i).1 y).1
    show (∏ i, x.nrm σ i y) ^ 2 < _
    rw [Finset.prod_eq_zero (Finset.mem_univ i) h0]
    simpa using Real.exp_pos _
  have hW0 : ∀ y ∈ W, x.wt σ R y = 0 := fun y hy => by
    by_cases hL : LiesIn y (genBd s.T.Z)
    · exact x.wt_eq_zero hR (Or.inl hL)
    · refine x.wt_eq_zero hR (Or.inr ?_)
      have hpos : 0 < (∏ i, x.nrm σ i y) ^ 2 := pow_pos (Finset.prod_pos fun i _ => x.nrm_pos hL i) 2
      have := (Real.log_lt_iff_lt_exp hpos).2 hy
      simp only [OddPrimesWithRootsOfUnity.r]
      linarith

  have hr : (manifold s.T.Z σ).SmoothOn Bc (x.r σ) := by
    refine AnRead.SmoothOn.congr (f := fun y => Real.exp 1 - ∑ i, Real.log (x.nrm σ i y ^ 2))
      (fun c => contDiffOn_const.sub (ContDiffOn.sum fun i _ => ((x.nrm_div σ i).smoothOn_log.mono
        fun y (hy : ¬ LiesIn y (genBd s.T.Z)) hi => hy ((x.liesIn_genBd_iff y).2 ⟨i, hi⟩)) c)) fun y hy => ?_
    simp only [OddPrimesWithRootsOfUnity.r]
    rw [← Finset.prod_pow, Real.log_prod fun i _ => pow_ne_zero _ (x.nrm_pos hy i).ne']
  have hw : (manifold s.T.Z σ).SmoothOn Bc (x.wt σ R) := by
    refine AnRead.SmoothOn.congr (f := fun y => cutWt x.kap R (x.r σ y)) (fun c => ?_) fun y hy => x.wt_eq hR hy
    have h1 := hr c
    have hpos : ∀ v, 0 < (x.r σ ∘ ((manifold s.T.Z σ).chart c).e.symm) v := fun v =>
      lt_of_lt_of_le (Real.exp_pos 1) (x.exp_le_r σ _)
    have hA := contDiff_cutoff.1.comp_contDiffOn ((h1.log fun v _ => (hpos v).ne').div_const (Real.log R))
    have hB := contDiffOn_const (c := (1 : ℝ)).add ((h1.div_const R).rpow_const_of_ne (p := x.kap)
      fun v _ => (div_pos (hpos v) (by linarith)).ne')
    refine (hA.div hB fun v _ => ?_).congr fun v _ => rfl
    exact (add_pos_of_pos_of_nonneg one_pos (Real.rpow_nonneg (div_nonneg (hpos v).le (by linarith)) _)).ne'

  have hgB : ∀ y ∈ P, y ∈ Bc → g y = (if τ (A.H.rt : D.host.E) = A.H.rt0 then mix (x.wt σ R y) (M0 y) (M1 y)
      else mixDual (x.wt σ R y) (M0 y) (M1 y)) a b := fun y hy hb => by
    obtain ⟨f, hf⟩ := hfr y hy
    rw [← hg y hy f hf]
    simp only [ToroidalCompactificationData.eigMetAt, EigMet.interp]
    rw [e0 y hy f hf, e1 y hy hb f hf]

  have hgW : ∀ y ∈ P, y ∈ W → g y = g0 a b y := fun y hy hw' => by
    obtain ⟨f, hf⟩ := hfr y hy
    rw [← hg y hy f hf, ← hg0 a b y (Set.mem_univ y) hy f hf]
    exact congrFun (congrFun (EigMet.interp_gram_zero (hs := x.wt_mem R) f (hW0 y hw')) a) b

  let T : Bool → Set (CxPts (genStr s.T.Z) σ) := fun β => cond β W Bc
  have key : ∀ β i, ContDiffOn ℝ ∞ (g ∘ ((manifold s.T.Z σ).chart i).e.symm)
      (((manifold s.T.Z σ).chart i).e.target ∩ ((manifold s.T.Z σ).chart i).e.symm ⁻¹' ((Set.univ ∩ P) ∩ T β)) := by
    intro β i
    have sub : ((manifold s.T.Z σ).chart i).e.target ∩ ((manifold s.T.Z σ).chart i).e.symm ⁻¹' ((Set.univ ∩ P) ∩ T β) ⊆
        ((manifold s.T.Z σ).chart i).e.target ∩ ((manifold s.T.Z σ).chart i).e.symm ⁻¹' (Set.univ ∩ P) :=
      fun v hv => ⟨hv.1, hv.2.1⟩
    have s0 : EntSm (fun v => M0 (((manifold s.T.Z σ).chart i).e.symm v))
        (((manifold s.T.Z σ).chart i).e.target ∩ ((manifold s.T.Z σ).chart i).e.symm ⁻¹' ((Set.univ ∩ P) ∩ T β)) :=
      fun a' b' => contDiffOn_iff_re_im.2 ⟨(hg0r a' b' i).mono sub, (hg0i a' b' i).mono sub⟩
    cases β
    · have sub1 : ((manifold s.T.Z σ).chart i).e.target ∩ ((manifold s.T.Z σ).chart i).e.symm ⁻¹'
          ((Set.univ ∩ P) ∩ T false) ⊆
          ((manifold s.T.Z σ).chart i).e.target ∩ ((manifold s.T.Z σ).chart i).e.symm ⁻¹' (Bc ∩ P) :=
        fun v hv => ⟨hv.1, hv.2.2, hv.2.1.2⟩
      have sub2 : ((manifold s.T.Z σ).chart i).e.target ∩ ((manifold s.T.Z σ).chart i).e.symm ⁻¹'
          ((Set.univ ∩ P) ∩ T false) ⊆
          ((manifold s.T.Z σ).chart i).e.target ∩ ((manifold s.T.Z σ).chart i).e.symm ⁻¹' Bc :=
        fun v hv => ⟨hv.1, hv.2.2⟩
      have s1 : EntSm (fun v => M1 (((manifold s.T.Z σ).chart i).e.symm v)) _ :=
        fun a' b' => contDiffOn_iff_re_im.2 ⟨(hg1r a' b' i).mono sub1, (hg1i a' b' i).mono sub1⟩
      have sw := (hw i).mono sub2
      have hf := ite_sm (c := τ (A.H.rt : D.host.E) = A.H.rt0) (mix_sm sw s0 s1)
        (mixDual_sm sw s0 s1 (fun v hv => p0 _ hv.2.1.2) (fun v hv => p1 _ hv.2.1.2 hv.2.2)
          fun v _ => x.wt_mem R _) a b
      refine hf.congr fun v hv => ?_
      simp only [Function.comp]
      rw [hgB _ hv.2.1.2 hv.2.2]
    · refine (s0 a b).congr fun v hv => ?_
      simp only [Function.comp]
      exact hgW _ hv.2.1.2 hv.2.2
  have hT : ∀ β, IsOpen (T β) := fun β => by cases β; exacts [hBo, hWo]
  have hc : ∀ y ∈ Set.univ ∩ P, ∃ β, y ∈ T β := fun y _ => by
    by_cases hL : LiesIn y (genBd s.T.Z)
    · exact ⟨true, hWbd y hL⟩
    · exact ⟨false, hL⟩
  refine ⟨g, AnRead.smoothOn_of_cover hT hc fun β i => (contDiffOn_iff_re_im.1 (key β i)).1,
    AnRead.smoothOn_of_cover hT hc fun β i => (contDiffOn_iff_re_im.1 (key β i)).2, fun y _ hy f hf => hg y hy f hf⟩

end GlobalTheory.ShFam
