import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSkewSignature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockEmb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpGLiAddSmul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InducedSectionZFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOfIsBlockEmb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineToGAdDerivative
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplMapSplitProj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspBlockConstantTermVanishing
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped ContDiff

noncomputable section

namespace GlobalTheory.BlockRealLine

open Matrix
open scoped TensorProduct
open Formalism.UG (cT bc)
open GlobalTheory.CuspRep (Cinf infEq sInf infGL expGLi)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

abbrev infComp (w : InfinitePlace F) : Ainf F ⊗[F] E →+* w.Completion ⊗[F] E :=
  (Algebra.TensorProduct.map (GlobalTheory.AutFunCompare.evW w) (AlgHom.id F E)).toRingHom

omit [NumberField E] in

theorem exists_place_of_prim {R : Type} [CommRing R] (j : Ainf F ⊗[F] E ≃+* R) (e : R) (he : e * e = e)
    (hp : ∀ f : R, f * f = f → f * e = f → f = 0 ∨ f = e) (y : Ainf F ⊗[F] E) (hy : j y = e) :
    ∃ w : InfinitePlace F, ∀ w', w' ≠ w → infComp w' y = 0 := by
  classical
  have hyy : y * y = y := j.injective (by rw [map_mul, hy, he])
  by_contra hne
  push_neg at hne
  obtain ⟨w0⟩ : Nonempty (InfinitePlace F) := inferInstance
  obtain ⟨w1, -, h1⟩ := hne w0
  obtain ⟨w2, h12, h2⟩ := hne w1
  let δ : Ainf F ⊗[F] E := (GlobalTheory.AutFunCompare.sgW w1 (1 : w1.Completion)) ⊗ₜ[F] (1 : E)
  have hδ1 : infComp w1 δ = 1 := by
    change (GlobalTheory.AutFunCompare.evW w1 (GlobalTheory.AutFunCompare.sgW w1 (1 : w1.Completion))) ⊗ₜ[F] (1 : E) = 1
    rw [show GlobalTheory.AutFunCompare.evW w1 (GlobalTheory.AutFunCompare.sgW w1 (1 : w1.Completion)) = 1 from Pi.single_eq_same w1 _]
    rfl
  have hδ2 : infComp w2 δ = 0 := by
    change (GlobalTheory.AutFunCompare.evW w2 (GlobalTheory.AutFunCompare.sgW w1 (1 : w1.Completion))) ⊗ₜ[F] (1 : E) = 0
    rw [show GlobalTheory.AutFunCompare.evW w2 (GlobalTheory.AutFunCompare.sgW w1 (1 : w1.Completion)) = 0 from Pi.single_eq_of_ne h12 _]
    exact TensorProduct.zero_tmul _ _
  have hδδ : δ * δ = δ := by
    change _ ⊗ₜ[F] _ * _ ⊗ₜ[F] _ = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, ← GlobalTheory.AutFunCompare.sgW_mul, mul_one]
  rcases hp (j (y * δ)) (by
      rw [← map_mul]; congr 1
      calc y * δ * (y * δ) = (y * y) * (δ * δ) := by ring
        _ = y * δ := by rw [hyy, hδδ]) (by
      rw [← hy, ← map_mul]; congr 1
      calc y * δ * y = (y * y) * δ := by ring
        _ = y * δ := by rw [hyy]) with h | h
  · apply h1
    have e0 : y * δ = 0 := j.injective (h.trans (map_zero j).symm)
    have := congrArg (infComp w1) e0
    rwa [map_mul, hδ1, mul_one, map_zero] at this
  · apply h2
    have e0 : y * δ = y := j.injective (h.trans hy.symm)
    have := congrArg (infComp w2) e0
    rwa [map_mul, hδ2, mul_zero, eq_comm] at this

omit [NumberField E] in

theorem single_prim [DecidableEq (InfinitePlace E)] (v : InfinitePlace E) (f : Cinf E) (h1 : f * f = f)
    (h2 : f * Pi.single v 1 = f) : f = 0 ∨ f = Pi.single v 1 := by
  have hne : ∀ u, u ≠ v → f u = 0 := fun u hu => by
    have := congrFun h2 u
    rw [Pi.mul_apply, Pi.single_eq_of_ne hu, mul_zero] at this
    exact this.symm
  by_cases hv : f v = 0
  · left
    funext u
    by_cases hu : u = v
    · subst hu; exact hv
    · exact hne u hu
  · right
    funext u
    by_cases hu : u = v
    · subst hu
      rw [Pi.single_eq_same]
      have h := congrFun h1 u
      rw [Pi.mul_apply] at h
      exact mul_left_cancel₀ hv (h.trans (mul_one _).symm)
    · rw [Pi.single_eq_of_ne hu]; exact hne u hu

end GlobalTheory.BlockRealLine

namespace GlobalTheory.BlockRealLine

open Matrix
open scoped TensorProduct
open Formalism.UG (cT bc)
open GlobalTheory.CuspRep (Cinf infEq infGL expGLi)

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField E] in

theorem compInf_eq_infComp (w : InfinitePlace F) (z : AF F ⊗[F] E) :
    compInf F E w z = infComp w (GlobalTheory.LFun.infTens F E z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x => rfl
  | add a b ha hb => simp only [map_add, ha, hb]

omit [NumberField E] in

theorem compInf_sigR (σ : E →ₐ[F] E) (w : InfinitePlace F) (z : AF F ⊗[F] E) :
    compInf F E w (sigR _ σ z) = sigR _ σ (compInf F E w z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x => rfl
  | add a b ha hb => simp only [map_add, ha, hb]

omit [NumberField F] [Algebra F E] in

theorem evalMat_exp {d : ℕ} (u : InfinitePlace E) (X : Matrix (Fin d) (Fin d) (Cinf E)) :
    (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) u).mapMatrix (NormedSpace.exp X) =
      NormedSpace.exp ((Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) u).mapMatrix X) := by
  letI : NormedRing (Matrix (Fin d) (Fin d) (Cinf E)) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin d) (Fin d) (Cinf E)) := Matrix.linftyOpNormedAlgebra
  haveI : CompleteSpace (Matrix (Fin d) (Fin d) (Cinf E)) := FiniteDimensional.complete ℝ _
  letI : NormedAlgebra ℚ (Matrix (Fin d) (Fin d) (Cinf E)) := NormedAlgebra.restrictScalars ℚ ℝ _
  letI : NormedRing (Matrix (Fin d) (Fin d) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin d) (Fin d) ℂ) := Matrix.linftyOpNormedAlgebra
  haveI : CompleteSpace (Matrix (Fin d) (Fin d) ℂ) := FiniteDimensional.complete ℝ _
  letI : NormedAlgebra ℚ (Matrix (Fin d) (Fin d) ℂ) := NormedAlgebra.restrictScalars ℚ ℝ _
  have hc : Continuous ((Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) u).mapMatrix :
      Matrix (Fin d) (Fin d) (Cinf E) → Matrix (Fin d) (Fin d) ℂ) :=
    LinearMap.continuous_of_finiteDimensional ((LinearMap.proj u : Cinf E →ₗ[ℝ] ℂ).mapMatrix)
  exact NormedSpace.map_exp (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) u).mapMatrix hc X

variable [IsTotallyComplex E]

theorem map_compInf_infGL {Φ : AF F ⊗[F] E ≃+* AdeleRing (𝓞 E) E} {j : Ainf F ⊗[F] E ≃+* InfiniteAdeleRing E}
    (hΦ : ∀ z, Φ z = (j (GlobalTheory.LFun.infTens F E z), GlobalTheory.LFun.finAdEquiv F E (GlobalTheory.LFun.finTens F E z)))
    [DecidableEq (InfinitePlace E)] {v : InfinitePlace E} {w' : InfinitePlace F}
    (hw : infComp w' (j.symm (infEq E (Pi.single v 1))) = 0) {d : ℕ} (y : GL (Fin d) (Cinf E))
    (hy : ∀ u, u ≠ v → ∀ a b, y.1 a b u = (1 : Matrix (Fin d) (Fin d) (Cinf E)) a b u) :
    ((infGL E d y).1.map Φ.symm).map (compInf F E w') = 1 := by
  have key : ∀ x, GlobalTheory.LFun.infTens F E (Φ.symm x) = j.symm x.1 := fun x => by
    have e := congrArg Prod.fst (hΦ (Φ.symm x))
    rw [RingEquiv.apply_symm_apply] at e
    rw [e, RingEquiv.symm_apply_apply]
  ext a b
  have hcv : y.1 a b - (1 : Matrix (Fin d) (Fin d) (Cinf E)) a b =
      (y.1 a b - (1 : Matrix (Fin d) (Fin d) (Cinf E)) a b) * Pi.single v 1 := by
    funext u
    by_cases hu : u = v
    · subst hu; simp
    · rw [Pi.mul_apply, Pi.single_eq_of_ne hu, mul_zero, Pi.sub_apply, hy u hu, sub_self]
  have hx : (infGL E d y).1 a b = (1 : Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Ad E)) a b +
      GlobalTheory.CuspRep.sInf E (y.1 a b - (1 : Matrix (Fin d) (Fin d) (Cinf E)) a b) := by
    change (1 : Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Ad E)) a b -
      GlobalTheory.CuspRep.sInf E ((1 : Matrix (Fin d) (Fin d) (Cinf E)) a b) + GlobalTheory.CuspRep.sInf E (y.1 a b) = _
    rw [map_sub]; abel
  have h0 : compInf F E w' (Φ.symm (GlobalTheory.CuspRep.sInf E (y.1 a b - (1 : Matrix (Fin d) (Fin d) (Cinf E)) a b))) = 0 := by
    rw [compInf_eq_infComp, key]
    change infComp w' (j.symm (infEq E (y.1 a b - (1 : Matrix (Fin d) (Fin d) (Cinf E)) a b))) = 0
    rw [hcv, map_mul, map_mul, map_mul, hw, mul_zero]
  simp only [Matrix.map_apply, hx, map_add, h0, add_zero]
  by_cases hab : a = b
  · subst hab; simp
  · simp [Matrix.one_apply_ne hab]

end SlopeTestRemainingChoices

end GlobalTheory.BlockRealLine

namespace GlobalTheory.BlockRealLine

open Matrix
open scoped TensorProduct
open Formalism.UG (cT bc)
open GlobalTheory.CuspRep (Cinf infEq infGL expGLi)

theorem isRealLine_blockEmb_exp : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [IsTotallyComplex E]
    [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf →
    ∀ (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
    ∀ (v : InfinitePlace E) (X : Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Cinf E)), (∀ i j, ∀ u, u ≠ v → X i j u = 0) →
      IsRealLine σ J fun t : ℝ => ι (GlobalTheory.CuspRep.infGL E d (GlobalTheory.CuspRep.expGLi d (t • X))) := by
  intro F E _ _ _ _ _ _ σ hcm n J _ r Xf Yf _ l d h ι hι v X hX
  classical
  obtain ⟨Φ, j, -, -, -, hΦ, hM⟩ := id hι
  obtain ⟨w, hw⟩ := exists_place_of_prim (j.trans (infEq E).symm) (Pi.single v (1 : ℂ))
    (by rw [← Pi.single_mul, one_mul]) (single_prim v) (j.symm (infEq E (Pi.single v 1))) (by simp)

  have hexp : ∀ t : ℝ, ∀ u, u ≠ v → ∀ a b,
      (expGLi d (t • X)).1 a b u = (1 : Matrix (Fin d) (Fin d) (Cinf E)) a b u := by
    intro t u hu a b
    have hz : (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) u).mapMatrix (t • X) = 0 := by
      ext a' b'
      change t • X a' b' u = 0
      rw [hX a' b' u hu, smul_zero]
    have H : (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) u).mapMatrix (NormedSpace.exp (t • X)) =
        (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) u).mapMatrix 1 := by
      rw [evalMat_exp, hz, NormedSpace.exp_zero, map_one]
    exact congrFun₂ H a b
  have hinv : ∀ t : ℝ, (expGLi d (t • X))⁻¹ = expGLi d ((-t) • X) := fun t => by
    have e := GlobalTheory.CuspRep.expGLi_add_smul d X (-t) t
    rw [neg_add_cancel, zero_smul, GlobalTheory.CuspRep.expGLi_zero] at e
    exact (eq_inv_of_mul_eq_one_left e.symm).symm

  have hcexp : Continuous fun t : ℝ => ((expGLi d (t • X) : GL (Fin d) (Cinf E)) : Matrix (Fin d) (Fin d) (Cinf E)) := by
    letI : NormedRing (Matrix (Fin d) (Fin d) (Cinf E)) := Matrix.linftyOpNormedRing
    letI : NormedAlgebra ℝ (Matrix (Fin d) (Fin d) (Cinf E)) := Matrix.linftyOpNormedAlgebra
    haveI : CompleteSpace (Matrix (Fin d) (Fin d) (Cinf E)) := FiniteDimensional.complete ℝ _
    exact continuous_iff_continuousAt.2 fun t => (hasDerivAt_exp_smul_const (𝕂 := ℝ) X t).continuousAt
  have hcGL : Continuous fun t : ℝ => expGLi d (t • X) := by
    refine Units.continuous_iff.2 ⟨hcexp, ?_⟩
    have e : (fun t : ℝ => (((expGLi d (t • X))⁻¹ : GL (Fin d) (Cinf E)) : Matrix (Fin d) (Fin d) (Cinf E))) =
        fun t => ((expGLi d ((-t) • X) : GL (Fin d) (Cinf E)) : Matrix (Fin d) (Fin d) (Cinf E)) :=
      funext fun t => by rw [hinv]
    rw [e]
    exact hcexp.comp continuous_neg
  have hcinf : Continuous (infGL E d) := by
    refine Continuous.units_map _ ?_
    have hs : Continuous (GlobalTheory.CuspRep.sInf E : Cinf E → GlobalTheory.CuspRep.Ad E) :=
      (GlobalTheory.CuspRep.continuous_infEq E).prodMk continuous_const
    exact continuous_const.sub continuous_const |>.add (continuous_id.matrix_map hs)
  let δ : ℝ → GAd σ J := fun t => ι (infGL E d (expGLi d (t • X)))
  have hc : Continuous δ := (GlobalTheory.BlockLevel.continuous_of_isBlockEmb hι).comp (hcinf.comp hcGL)
  have h0 : δ 0 = 1 := by simp only [δ, zero_smul, GlobalTheory.CuspRep.expGLi_zero, map_one]
  have hm : ∀ s t, δ (s + t) = δ s * δ t := fun s t => by
    simp only [δ, GlobalTheory.CuspRep.expGLi_add_smul, map_mul]

  have hinf : ∀ w', w' ≠ w → ∀ t, projArch σ J w' (δ t) = 1 := by
    intro w' hw' t
    have hM' := hM (infGL E d (expGLi d (t • X)))
    rw [← map_inv, hinv] at hM'
    have hQ : ((infGL E d (expGLi d ((-t) • X))).1.map Φ.symm).map ((compInf F E w').comp (sigR (AF F) σ)) = 1 := by
      have e : (compInf F E w').comp (sigR (AF F) σ) = (sigR _ σ).comp (compInf F E w') :=
        RingHom.ext (compInf_sigR σ w')
      rw [e, RingHom.coe_comp, ← Matrix.map_map, map_compInf_infGL hΦ (hw w' hw') _ (hexp (-t)),
        Matrix.map_one _ (map_zero _) (map_one _)]
    apply matHom_injective (w'.Completion) σ J
    rw [matHom_projArch, map_one]
    refine Units.ext ?_
    change (matHom (AF F) σ J (ι (infGL E d (expGLi d (t • X))))).1.map (compInf F E w') = 1
    rw [hM', GlobalTheory.BlockForms.LeviLoc.map_formula _ _ _ _ _ _ _ _ hQ, map_compInf_infGL hΦ (hw w' hw') _ (hexp t)]
    simp
  have hfin : ∀ v' t, proj σ J v' (δ t) = 1 := by
    intro v' t
    have hM' := hM (infGL E d (expGLi d (t • X)))
    rw [← map_inv] at hM'
    have hQ : ((infGL E d (expGLi d (t • X))⁻¹).1.map Φ.symm).map ((compFin F E v').comp (sigR (AF F) σ)) = 1 := by
      have e : (compFin F E v').comp (sigR (AF F) σ) = (sigR _ σ).comp (compFin F E v') :=
        RingHom.ext (GlobalTheory.BlockForms.LeviLoc.compFin_sigR σ v')
      rw [e, RingHom.coe_comp, ← Matrix.map_map, GlobalTheory.BlockForms.CuspGrowth.map_compFin_infGL hΦ,
        Matrix.map_one _ (map_zero _) (map_one _)]
    apply matHom_injective _ σ J
    rw [matHom_proj, map_one]
    refine Units.ext ?_
    change (matHom (AF F) σ J (ι (infGL E d (expGLi d (t • X))))).1.map (compFin F E v') = 1
    rw [hM', GlobalTheory.BlockForms.LeviLoc.map_formula _ _ _ _ _ _ _ _ hQ, GlobalTheory.BlockForms.CuspGrowth.map_compFin_infGL hΦ]
    simp
  have hδ : δ = fun t => embArch σ J w (projArch σ J w (δ t)) := by
    funext t
    refine GAd_ext σ J (fun w'' => ?_) fun v' => ?_
    · by_cases e : w'' = w
      · subst e; rw [projArch_embArch_self]
      · rw [projArch_embArch_ne σ J e, hinf w'' e t]
    · rw [proj_embArch, hfin v' t]
  have hline := GlobalTheory.LineDerSum.isRealLine_component hcm J δ hc h0 hm w
  rw [← hδ] at hline
  exact hline

end GlobalTheory.BlockRealLine
