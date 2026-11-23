import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ChartBaseRepresentativePenultimateStep
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FirstCoupledKernelEquivariantCosets
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CouplingCosetsRightTranslateInFramesTypePrime
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BaseCosetRepIntegralAfterScalingAtBadPrime
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.KerEquivFr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowTypeOneAddPrimeSmulEqOne
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV

noncomputable section

namespace GlobalTheory.CplRat

section Gen

variable {X : Fields} {Pr : Primes X} {R : Ranks}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}

open Classical in

theorem exists_pass_rat (p : ChPt (R := R) sel mu u j) (g : UF X.E (R.N j)) :
    ∃ κ : GLQ X.E (R.N j) (rowSG Pr sel mu),
      (∀ P, frsF sel mu (((g, 1, 1) : UF X.E (R.N j) × GLG X.E (R.N j) Pr.vGs × GLQ X.E (R.N j) (QE sel (mu : Chr X.F X.E X.K))) • p) P =
        g.1 * (frsF sel mu p P * ((κ P)⁻¹).1)) ∧
      (∀ P : rowSG Pr sel mu, GlobalTheory.TopStep.redGL (R.N j) P.1 (κ P) = 1) ∧ (∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → κ P = 1) := by
  have h : ∀ P : rowSG Pr sel mu, ∃ k : GLint X.E (R.N j) P.1,
      frsF sel mu (((g, 1, 1) : UF X.E (R.N j) × GLG X.E (R.N j) Pr.vGs × GLQ X.E (R.N j) (QE sel (mu : Chr X.F X.E X.K))) • p) P =
        g.1 * (frsF sel mu p P * (k⁻¹).1) ∧ GlobalTheory.TopStep.redGL (R.N j) P.1 k = 1 ∧ (P.1 ∉ Pr.vGs → k = 1) := by
    intro P
    by_cases hP : P.1 ∈ Pr.vGs
    · obtain ⟨κ0, h1, h2⟩ := liftFr_smul p.deco ((g, 1) : UF X.E (R.N j) × GLG X.E (R.N j) Pr.vGs) ⟨P.1, hP⟩
      have hr : GlobalTheory.TopStep.redGL (R.N j) P.1 κ0 = 1 := GlobalTheory.TopStep.redGL_eq κ0 fun x hx => by
        rw [h2 x hx]
        simp
      refine ⟨κ0⁻¹, ?_, by rw [map_inv, hr, inv_one], fun h => absurd hP h⟩
      unfold frsF
      rw [dif_pos hP, dif_pos hP, inv_inv]
      exact h1.trans (mul_assoc _ _ _)
    · refine ⟨1, ?_, map_one _, fun _ => rfl⟩
      unfold frsF
      rw [dif_neg hP, dif_neg hP]
      show g.1 * _ * (((1 : GLQ X.E (R.N j) (QE sel (mu : Chr X.F X.E X.K))) _)⁻¹).1 = _
      simp [mul_assoc]
      rfl
  choose κ hκ using h
  exact ⟨κ, fun P => (hκ P).1, fun P => (hκ P).2.1, fun P => (hκ P).2.2⟩

theorem levAt_one {n : ℕ} (Λ : LevFam X.E X.K n Pr.vGs) (Θ : LevQFam X.E X.K n (QE sel (mu : Chr X.F X.E X.K))) (P : rowSG Pr sel mu)
    (k : GLint X.E n P.1) (hr : GlobalTheory.TopStep.redGL n P.1 k = 1) (h1 : P.1 ∉ Pr.vGs → k = 1) : GlobalTheory.TopLaw.LevAt Λ Θ P k 1 := by
  refine ⟨fun hP => ?_, fun hQ hP => ?_⟩
  · have hm : GlobalTheory.TopStep.redGL n P.1 k ∈ (Λ ⟨P.1, hP⟩).H := by rw [hr]; exact one_mem _
    refine ⟨hm, ?_⟩
    rw [show (⟨_, hm⟩ : (Λ ⟨P.1, hP⟩).H) = 1 from Subtype.ext hr, map_one]
  · obtain rfl := h1 hP
    exact ⟨one_mem _, (map_one _).symm⟩

end Gen

section Cos

variable {X : Fields} {Pr : Primes X} {R : Ranks}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}

open Classical in

theorem sameCoset_pass (hX : X.Ok) (hPr : Pr.Ok) {n : ℕ} (P : rowSG Pr sel mu) (k : GLint X.E n P.1)
    (hr : GlobalTheory.TopStep.redGL n P.1 k = 1) (h1 : P.1 ∉ Pr.vGs → k = 1) (y0 : Sp X.E n)
    (hy0 : P.1 ∈ Pr.vGs → ∀ l, IntAt P.1 ((qOf P.1 : X.E) ^ 1 * y0 l)) (v : Sp X.E n) :
    SameCoset sel mu cst P (k.1 v) y0 ↔ SameCoset sel mu cst P v y0 := by
  by_cases hP : P.1 ∈ Pr.vGs
  · unfold SameCoset
    simp only [if_pos hP]
    have hk : k⁻¹ ∈ GlobalTheory.TopStep.prinCong n P.1 1 :=
      GlobalTheory.CplCosetPt.mem_prinCong_one_of_redGL (GlobalTheory.TopStep.qOf_notMem_sq hX hPr hP) _ (by rw [map_inv, hr, inv_one])
    exact GlobalTheory.CplCosetPt.sameCoset_loc P.1 0 1 1 k.1 1 k⁻¹ k.2 (one_mem _) hk (by simp) (by omega) y0 (hy0 hP)
      (fun l => by simpa using GlobalTheory.TopStep.intAt_zero) v
  · obtain rfl := h1 hP
    exact Iff.rfl

open Classical in

theorem coset_image (hX : X.Ok) (hPr : Pr.Ok) {n : ℕ} (fp fq : rowSG Pr sel mu → (Sp X.E n ≃ₗ[X.E] Sp X.E n))
    (g : Sp X.E n ≃ₗ[X.E] Sp X.E n) (κ : GLQ X.E n (rowSG Pr sel mu)) (hκ : ∀ P, fq P = g * (fp P * ((κ P)⁻¹).1))
    (hr : ∀ P : rowSG Pr sel mu, GlobalTheory.TopStep.redGL n P.1 (κ P) = 1) (h1 : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → κ P = 1)
    (y0 : rowSG Pr sel mu → Sp X.E n) (hy0 : ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs → ∀ l, IntAt P.1 ((qOf P.1 : X.E) ^ 1 * y0 P l)) :
    {y | ∀ P, SameCoset sel mu cst P ((fq P).symm y) (y0 P)} =
      (fun v => g v) '' {y | ∀ P, SameCoset sel mu cst P ((fp P).symm y) (y0 P)} := by
  have e : ∀ P y, (fq P).symm y = (κ P).1 ((fp P).symm (g.symm y)) := by
    intro P y
    apply (fq P).injective
    rw [LinearEquiv.apply_symm_apply, hκ P]
    show y = g (fp P (((κ P)⁻¹).1 ((κ P).1 ((fp P).symm (g.symm y)))))
    rw [Subgroup.coe_inv]
    show y = g (fp P ((κ P).1.symm ((κ P).1 ((fp P).symm (g.symm y)))))
    simp
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_image, e]
  constructor
  · intro h
    refine ⟨g.symm y, fun P => (sameCoset_pass hX hPr P (κ P) (hr P) (h1 P) (y0 P) (hy0 P) _).1 (h P), by simp⟩
  · rintro ⟨z, hz, rfl⟩ P
    rw [LinearEquiv.symm_apply_apply]
    exact (sameCoset_pass hX hPr P (κ P) (hr P) (h1 P) (y0 P) (hy0 P) _).2 (hz P)

open Classical in

theorem coset_mem_ybSet (p : ChPt (R := R) sel mu u j) (y0 : rowSG Pr sel mu → Sp X.E (R.N j))
    (hy0 : ∀ (P : rowSG Pr sel mu) l, IntAt P.1 ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 1 else cst.M) * y0 P l)) :
    {y | ∀ P, SameCoset sel mu cst P ((frsF sel mu p P).symm y) (y0 P)} ∈ ybSet sel mu cst p.deco.1.N := by
  obtain ⟨y, hy⟩ := GlobalTheory.CplCosetPt.exists_sameCoset_frames sel mu cst (frsF sel mu p) y0
  refine ⟨y, ?_, ?_⟩
  · rw [mem_locLat]
    intro P
    have hq0 : ((qOf P.1 : ℕ) : X.E) ≠ 0 := by
      have : qOf P.1 ≠ 0 := fun h0 => P.1.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
      exact_mod_cast this
    have hqI : IntAt P.1 ((qOf P.1 : ℕ) : X.E) := by simpa using IntAt.coe P.1 ((qOf P.1 : ℕ) : 𝓞 X.E)
    rw [← (frsF sel mu p P).apply_symm_apply (_ • y), GlobalTheory.TwV.Model.frsF_mem, GlobalTheory.TopStep.mem_stdAt]
    intro l
    rw [map_smul, Pi.smul_apply, smul_eq_mul]
    have hs := hy P l
    have h0 := hy0 P l
    by_cases hP : P.1 ∈ Pr.vGs
    · simp only [if_pos hP, pow_zero, inv_one, one_mul, pow_one] at hs h0 ⊢
      simp only [_root_.zpow_neg, zpow_one, inv_inv]
      have e : ((qOf P.1 : ℕ) : X.E) * (frsF sel mu p P).symm y l =
          ((qOf P.1 : ℕ) : X.E) * ((frsF sel mu p P).symm y - y0 P) l + ((qOf P.1 : ℕ) : X.E) * y0 P l := by
        simp only [Pi.sub_apply]; ring
      rw [e]
      exact (hqI.mul hs).add h0
    · simp only [if_neg hP] at hs h0 ⊢
      simp only [_root_.zpow_neg, zpow_natCast, inv_inv]
      have e : ((qOf P.1 : ℕ) : X.E) ^ cst.M * (frsF sel mu p P).symm y l =
          (((qOf P.1 : ℕ) : X.E) ^ cst.M * ((qOf P.1 : ℕ) : X.E) ^ cst.M) *
            ((((qOf P.1 : ℕ) : X.E) ^ cst.M)⁻¹ * ((frsF sel mu p P).symm y - y0 P) l) + ((qOf P.1 : ℕ) : X.E) ^ cst.M * y0 P l := by
        simp only [Pi.sub_apply]
        field_simp
        ring
      rw [e]
      exact (((GlobalTheory.TopStep.intAt_pow hqI _).mul (GlobalTheory.TopStep.intAt_pow hqI _)).mul hs).add h0
  · ext z
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq, mem_locLat]
    refine forall_congr' fun P => ?_
    rw [← GlobalTheory.TwV.Model.sameCoset_iff sel mu cst p P z y]
    exact ⟨fun h => GlobalTheory.TwV.Model.sameCoset_trans _ _ _ h (GlobalTheory.TwV.Model.sameCoset_symm _ _ _ (hy P)),
      fun h => GlobalTheory.TwV.Model.sameCoset_trans _ _ _ h (hy P)⟩

end Cos

section Main

theorem unitV_det_one {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {P : HeightOneSpectrum (𝓞 E)}
    (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (k : GLint E n P) (hr : GlobalTheory.TopStep.redGL n P k = 1) :
    LocE.unitV χ ((LinearEquiv.det k.1 : Eˣ) : E) = 1 := by
  rw [GlobalTheory.TopStep.unitV_congr χ (b := 1) ?_, GlobalTheory.Mem.Col2.IdxEx.Cong.unitV_one]
  rw [(GlobalTheory.TopStep.det_glint k).2, GlobalTheory.TopStep.reduction_one₂, ← GlobalTheory.TopStep.redGL_val, hr]
  simp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem xiPt_cpl_smul : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ i (hi : i + 1 ≤ D.R.m), i = t.m2 → ∀ β β' (x : UA D i (Nat.le_of_succ_le hi)) (x' : UA D (i + 1) hi) p p',
      IsPtAd A a i (Nat.le_of_succ_le hi) β x p → IsPtAd A a (i + 1) hi β' x' p' →
      ∀ (g : UF t.X.E (D.R.N i)) (g' : UF t.X.E (D.R.N (i + 1))) (w : HomE t.X.E (D.R.N i) (D.R.N (i + 1))),
      xiPt A i hi β β' (((g, 1, 1) : UF t.X.E (D.R.N i) × GLG t.X.E (D.R.N i) t.Pr.vGs × GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p)
        (((g', 1, 1) : UF t.X.E (D.R.N (i + 1)) × GLG t.X.E (D.R.N (i + 1)) t.Pr.vGs × GLQ t.X.E (D.R.N (i + 1)) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p')
        (g'.1.toLinearMap ∘ₗ w ∘ₗ g.1.symm.toLinearMap) = xiPt A i hi β β' p p' w) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPins hTie i hi hm β β' x x' p p' _ _ g g' w
  classical
  subst hm
  have hX : t.X.Ok := hPins.fields.ok
  have hPr := t.pr_ok
  have hL := t.idx_ok μ
  obtain ⟨κ, hκ, hr, h1⟩ := exists_pass_rat (R := D.R) p g
  obtain ⟨κ', hκ', hr', h1'⟩ := exists_pass_rat (R := D.R) p' g'
  have hy0 : ∀ (P : SB t μ) l, IntAt P.1 ((qOf P.1 : t.X.E) ^ (if P.1 ∈ t.Pr.vGs then 1 else (t.cst μ).M) *
      y0At A (t.m2 + 1) hi β' P l) := by
    intro P l
    have e : y0At A (t.m2 + 1) hi β' P = A.y0 β' P := by
      unfold y0At
      rw [dif_pos rfl]
    rw [e]
    exact GlobalTheory.TwU.BaseCosetInt.baseCosetRep_integral_after_scaling_at_bad_prime D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPins hTie β' P l
  have hY : cosetOf A (t.m2 + 1) hi β' p' ∈ ybSet t.sel (t.tup μ) (t.cst μ) p'.deco.1.N := coset_mem_ybSet p' _ hy0
  have hC : cosetOf A (t.m2 + 1) hi β' (((g', 1, 1) : UF t.X.E (D.R.N (t.m2 + 1)) × GLG t.X.E (D.R.N (t.m2 + 1)) t.Pr.vGs ×
      GLQ t.X.E (D.R.N (t.m2 + 1)) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p') =
      (fun v => g'.1 v) '' cosetOf A (t.m2 + 1) hi β' p' :=
    coset_image hX hPr _ _ g'.1 κ' hκ' hr' h1' _ (fun P hP l => by simpa [hP] using hy0 P l)
  have hY2 : (fun v => g'.1 v) '' cosetOf A (t.m2 + 1) hi β' p' ∈ ybSet t.sel (t.tup μ) (t.cst μ)
      ((((g', 1, 1) : UF t.X.E (D.R.N (t.m2 + 1)) × GLG t.X.E (D.R.N (t.m2 + 1)) t.Pr.vGs ×
        GLQ t.X.E (D.R.N (t.m2 + 1)) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p').deco.1.N) :=
    (ybSet_gmap t.sel (t.tup μ) (t.cst μ) _ g'.1 _).2 hY
  have law := GlobalTheory.CoupledLaw.xiCpl1_law (Ch := t.Ch) (L := t.idx μ) (al := A.ib t.m2 hi β)
    (b := A.ib (t.m2 + 1) (cpl_lt t μ) β') hX hPr hL hY hY2 hκ hκ' (a := fun _ => 1) (a' := fun _ => 1)
    (fun P => levAt_one _ _ P _ (hr P) (h1 P)) (fun P => levAt_one _ _ P _ (hr' P) (h1' P)) w
    (Formalism.L2.Ker.phiT_smul t.X.K p.deco p'.deco g 1 g' 1 w)
  have hprod : ∀ P : SB t μ, rhoS t.Ch t.sel (t.tup μ) t.m2 P ((LinearEquiv.det (κ⁻¹ P).1 : t.X.Eˣ) : t.X.E) *
      rhoT t.Ch t.sel (t.tup μ) t.m2 P ((LinearEquiv.det (κ'⁻¹ P).1 : t.X.Eˣ) : t.X.E) = 1 := by
    intro P
    unfold rhoS rhoT
    rw [Pi.inv_apply, Pi.inv_apply, unitV_det_one _ _ (by rw [map_inv, hr P, inv_one]),
      unitV_det_one _ _ (by rw [map_inv, hr' P, inv_one]), mul_one]
  rw [Finset.prod_eq_one fun P _ => hprod P, mul_one] at law
  simp only [Finset.prod_const_one, inv_one, mul_one, Units.val_one, one_mul] at law
  unfold xiPt
  rw [dif_neg (lt_irrefl _), if_pos rfl, dif_neg (lt_irrefl _), if_pos rfl, hC]
  exact law

end Main

end GlobalTheory.CplRat
