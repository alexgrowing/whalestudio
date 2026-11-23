import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalStabilizerDoubledVacuumEigenvalueEqOne
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.DblVacSiegelAny
open GlobalTheory.DblVacSiegel

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem piE_locIdele_self (P : HeightOneSpectrum (𝓞 E)) (y : (P.adicCompletion E)ˣ) :
    piE F P (locIdele F P y : AE F E) = y := by
  classical
  change (finAdEquiv F E (finTens F E (locIdele F P y : AE F E))) P = _
  rw [finTens_locIdele, GlobalTheory.CMVal.single_apply]
  exact Function.update_self _ _ _

theorem piE_locIdele_ne {P Q : HeightOneSpectrum (𝓞 E)} (h : Q ≠ P) (y : (P.adicCompletion E)ˣ) :
    piE F Q (locIdele F P y : AE F E) = 1 := by
  classical
  change (finAdEquiv F E (finTens F E (locIdele F P y : AE F E))) Q = _
  rw [finTens_locIdele, GlobalTheory.CMVal.single_apply]
  exact Function.update_of_ne h _ _

theorem eq_one_of_comp {x : (AE F E)ˣ} (h1 : infTens F E x = 1) (h2 : ∀ P, piE F P (x : AE F E) = 1) : x = 1 := by
  refine Units.ext (tens_ext (h1.trans (map_one _).symm) ((finAdEquiv F E).injective ?_))
  refine FiniteAdeleRing.ext _ fun P => ?_
  rw [Units.val_one, map_one, map_one]
  exact h2 P

theorem chr_eq_one_of_supp (χ : Chr F E) (S : Finset (HeightOneSpectrum (𝓞 E))) (hχ : ∀ P ∈ S, UnrAt χ P)
    (x : (AE F E)ˣ) (h1 : infTens F E x = 1) (hoff : ∀ P ∉ S, piE F P (x : AE F E) = 1)
    (hu : ∀ P ∈ S, Valued.v (piE F P (x : AE F E)) = 1) : χ x = 1 := by
  classical
  induction S using Finset.induction_on generalizing x with
  | empty =>
    rw [eq_one_of_comp h1 fun P => hoff P (Finset.notMem_empty P), map_one]
  | insert P S hPS ih =>
    let y : (P.adicCompletion E)ˣ := Units.map (piE F P).toMonoidHom x
    have hy : Formalism.L2.Host.IsUnitAt P y := hu P (Finset.mem_insert_self P S)
    have hl : χ (locIdele F P y) = 1 := Circle.ext (congrArg Units.val (hχ P (Finset.mem_insert_self P S) y hy))
    set x' := x * (locIdele F P y)⁻¹ with hx'
    have ex : (x' : AE F E) * (locIdele F P y : AE F E) = x := by
      rw [hx', Units.val_mul, mul_assoc, Units.inv_mul, mul_one]
    have hcomp : ∀ {R : Type} [CommRing R] (φ : AE F E →+* R), φ (locIdele F P y : AE F E) = 1 →
        φ (x' : AE F E) = φ x := fun φ h => by rw [← ex, map_mul, h, mul_one]
    have hx : x = x' * locIdele F P y := by rw [hx', inv_mul_cancel_right]
    rw [hx, map_mul, hl, mul_one]
    refine ih (fun Q hQ => hχ Q (Finset.mem_insert_of_mem hQ)) x' ?_ (fun Q hQ => ?_) (fun Q hQ => ?_)
    · rw [hcomp _ (infTens_locIdele P y), h1]
    · by_cases hQP : Q = P
      · subst hQP
        have e := congrArg (piE F Q) ex
        rw [map_mul, piE_locIdele_self] at e
        have h0 : (piE F Q (x : AE F E)) ≠ 0 := (Units.map (piE F Q).toMonoidHom x).ne_zero
        exact mul_right_cancel₀ h0 (e.trans (one_mul _).symm)
      · rw [hcomp _ (piE_locIdele_ne hQP y)]
        exact hoff Q (by simp [hQP, hQ])
    · have hQP : Q ≠ P := fun h => hPS (h ▸ hQ)
      rw [hcomp _ (piE_locIdele_ne hQP y)]
      exact hu Q (Finset.mem_insert_of_mem hQ)

theorem finite_under_eq (v : Pl F) : {P : HeightOneSpectrum (𝓞 E) | P.under (𝓞 F) = v}.Finite := by
  have h0 : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)]
    exact v.ne_bot
  refine (Ideal.finite_factors h0).subset fun P hP => ?_
  simp only [Set.mem_setOf_eq] at hP ⊢
  rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap, ← hP]
  exact le_rfl

theorem chr_det_eq_one_any {d : ℕ} (W : Spc F E d) (hL : W.L.IsLattice E) {v : Pl F} {χ : Chr F E}
    (hχ : ∀ P : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) = v → UnrAt χ P) (t : GL (Fin d) (AE F E))
    (h1 : At (evFin F v) ((t : Matrix (Fin d) (Fin d) (AE F E)) - 1))
    (ht : ∀ z ∈ GlobalTheory.InertSph.latAt W v, (t : Matrix (Fin d) (Fin d) (AE F E)) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v ∧
      ((t⁻¹ : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E)) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) :
    χ (Matrix.GeneralLinearGroup.det t) = 1 := by
  classical
  set δ := Matrix.GeneralLinearGroup.det t with hδ
  have hN := h1 (1 - GlobalTheory.LatVac.liftV v 1) (by rw [map_sub, map_one, GlobalTheory.LatVac.evFin_liftV, sub_self])
  have hφ : ∀ {R : Type} [CommRing R] (φ : AE F E →+* R),
      φ (algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1)) = 0 → φ (δ : AE F E) = 1 := by
    intro R _ φ hφ
    have : φ.mapMatrix (t : Matrix (Fin d) (Fin d) (AE F E)) = φ.mapMatrix 1 := by
      ext i j
      have h2 := congrArg φ (congrFun (congrFun hN i) j)
      rw [Matrix.smul_apply, Algebra.smul_def, map_mul, map_sub, map_sub, map_one, map_one, hφ, sub_zero, one_mul,
        Matrix.sub_apply, map_sub, Matrix.zero_apply, map_zero, sub_eq_zero] at h2
      exact h2
    rw [hδ, Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det, this, map_one, Matrix.det_one]
  refine chr_eq_one_of_supp χ (finite_under_eq (E := E) v).toFinset
    (fun P hP => hχ P ((finite_under_eq v).mem_toFinset.1 hP)) δ (hφ _ (TensorProduct.zero_tmul _ _))
    (fun P hP => ?_) (fun P hP => ?_)
  · have hPv : P.under (𝓞 F) ≠ v := fun h => hP ((finite_under_eq v).mem_toFinset.2 h)
    refine hφ _ ?_
    rw [piE_algebraMap rfl]
    exact (congrArg _ (evalV_singleFin_ne hPv 1)).trans (map_zero _)
  · have hu : P.under (𝓞 F) = v := (finite_under_eq v).mem_toFinset.1 hP
    let y : (P.adicCompletion E)ˣ := Units.map (piE F P).toMonoidHom δ
    have a1 : Valued.v (y : P.adicCompletion E) ≤ 1 := val_det_le_one W hL hu _ fun z hz => (ht z hz).1
    have a2 : Valued.v ((y⁻¹ : (P.adicCompletion E)ˣ) : P.adicCompletion E) ≤ 1 := by
      have := val_det_le_one W hL hu _ fun z hz => (ht z hz).2
      rw [← Matrix.GeneralLinearGroup.val_det_apply, map_inv] at this
      exact this
    have h0 : 0 < Valued.v (y : P.adicCompletion E) := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 y.ne_zero)
    rw [Units.val_inv_eq_inv_val, map_inv₀, inv_le_one₀ h0] at a2
    exact le_antisymm a1 a2

theorem eigen_eq_one_of_diag_any : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), v ∉ X.T →
    ∀ (dd : Darboux (symp (cA σ) (-1 : AE F E) (incM F G.V.J) (dbl (incM F G.W.J))) ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a'))))
      (omd : GlobalTheory.DblVac.UD σ G.W →* Module.End ℂ (((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → AF F) → ℂ)),
    IsDblCoord (cA σ) (-1 : AE F E) (incM F G.V.J) (incM F G.W.J) G.M.co dd →
    IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1 : AE F E) (incM F G.V.J) (dbl (incM F G.W.J)) dd X.β (diagCols (Fin (a + a'))) omd →
    ∀ r : (Fin a × Fin (a + a') → AF F) → ℂ, Rest (evFin F v) (G.M.vac v) r → tens (evFin F v) (G.M.vac v) r ≠ 0 →
    ∀ p ∈ GlobalTheory.DblVac.KD σ G.W v, p ∈ GlobalTheory.DblVac.PDiag σ G.W → ∀ μ : ℂ,
      omd p (boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x))) =
        μ • boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x)) → μ = 1 := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v hv dd omd hdd hW r hr h0 p hp hpd μ hμ
  obtain ⟨t, ht₀⟩ := hpd
  have ht : GlobalTheory.DblVac.matD p * (diagCols (Fin (a + a')) : Matrix (Fin (a + a') ⊕ Fin (a + a')) (Fin (a + a')) (AE F E)) =
      (diagCols (Fin (a + a')) : Matrix (Fin (a + a') ⊕ Fin (a + a')) (Fin (a + a')) (AE F E)) * (t : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) := ht₀
  have hF := hT.base.cm.1
  set Ψ := tens (evFin F v) (G.M.vac v) r with hΨ
  have hS := GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ Ψ hr.2 _ (GlobalTheory.SchAConj.star_mem_schA F _ Ψ hr.2)
  have hl := lDiag_box_ne_zero hF hr.2 h0
  have hS0 : (boxFun Ψ fun x => star (Ψ x)) ≠ 0 := fun h => hl (by rw [h, map_zero])
  have hn := norm_eq_one_of_eigen hF hW.2.1.unit hS hS0 hμ
  have hrule := hW.2.2 _ DiagForm.lDiag_adm (fun z φ hφ => by
    have e : z * (diagCols (Fin (a + a')) : Matrix _ _ (AE F E))ᵀ = Matrix.fromCols z z := by
      rw [diagCols, Matrix.transpose_fromRows, Matrix.mul_fromCols, Matrix.transpose_one, Matrix.mul_one]
    rw [e, Darboux.rho, hdd]
    exact DiagForm.lDiag_schr B.ψ _ _ hφ) p t ht _ hS
  have hvec : ∀ (g : GlobalTheory.DblVac.UD σ G.W) (s : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)),
      GlobalTheory.DblVac.matD g * (diagCols (Fin (a + a')) : Matrix (Fin (a + a') ⊕ Fin (a + a')) (Fin (a + a')) (AE F E)) = (diagCols (Fin (a + a')) : Matrix (Fin (a + a') ⊕ Fin (a + a')) (Fin (a + a')) (AE F E)) * s → ∀ z,
      (GlobalTheory.DblVac.matD g *ᵥ Sum.elim z z) ∘ Sum.inl = s *ᵥ z := fun g s hs z => by
    have e : ∀ z : Fin (a + a') → AE F E, (diagCols (Fin (a + a')) : Matrix (Fin (a + a') ⊕ Fin (a + a')) (Fin (a + a')) (AE F E)) *ᵥ z = Sum.elim z z := fun z => by
      rw [diagCols, Matrix.fromRows_mulVec, Matrix.one_mulVec]
    rw [← e, Matrix.mulVec_mulVec, hs, ← Matrix.mulVec_mulVec, e]
    rfl
  have ht' : GlobalTheory.DblVac.matD p⁻¹ * (diagCols (Fin (a + a')) : Matrix (Fin (a + a') ⊕ Fin (a + a')) (Fin (a + a')) (AE F E)) =
      (diagCols (Fin (a + a')) : Matrix (Fin (a + a') ⊕ Fin (a + a')) (Fin (a + a')) (AE F E)) * ((t⁻¹ : GL (Fin (a + a')) (AE F E)) : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) := by
    have e1 : GlobalTheory.DblVac.matD p⁻¹ * GlobalTheory.DblVac.matD p = 1 := p.1.inv_mul
    calc _ = GlobalTheory.DblVac.matD p⁻¹ * ((diagCols (Fin (a + a')) : Matrix (Fin (a + a') ⊕ Fin (a + a')) (Fin (a + a')) (AE F E)) * (t : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E))) *
          ((t⁻¹ : GL (Fin (a + a')) (AE F E)) : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, t.mul_inv, Matrix.mul_one]
      _ = _ := by rw [← ht, ← Matrix.mul_assoc, e1, Matrix.one_mul]
  have hβ : X.β (Matrix.GeneralLinearGroup.det t) = 1 := by
    refine chr_det_eq_one_any (v := v) G.W hT.geo.hW.lat (fun P hP => hT.chars.unrβ P fun h => hv (hP ▸ (h : P.under (𝓞 F) ∈ (X.T : Set (Pl F))))) t
      (fun u hu => ?_) fun z hz => ?_
    · have e1 : (GlobalTheory.DblVac.matD p - 1) * (diagCols (Fin (a + a')) : Matrix (Fin (a + a') ⊕ Fin (a + a')) (Fin (a + a')) (AE F E)) =
          (diagCols (Fin (a + a')) : Matrix (Fin (a + a') ⊕ Fin (a + a')) (Fin (a + a')) (AE F E)) * ((t : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) - 1) := by
        rw [Matrix.sub_mul, Matrix.mul_sub, ht, Matrix.one_mul, Matrix.mul_one]
      have e2 : (diagCols (Fin (a + a')) : Matrix (Fin (a + a') ⊕ Fin (a + a')) (Fin (a + a')) (AE F E)) * (u • ((t : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) - 1)) = 0 := by
        rw [Matrix.mul_smul, ← e1, ← Matrix.smul_mul, hp.1 u hu, Matrix.zero_mul]
      rw [diagCols, Matrix.fromRows_mul, Matrix.one_mul] at e2
      ext i j
      exact congrFun (congrFun e2 (Sum.inl i)) j
    · have hz' := hp.2 (Sum.elim z z) ⟨hz, hz⟩
      exact ⟨hvec p _ ht z ▸ hz'.1.1, hvec p⁻¹ _ ht' z ▸ hz'.2.1⟩
  rw [hμ, map_smul, smul_eq_mul, hβ, Circle.coe_one, one_mul] at hrule
  have hμ' := mul_right_cancel₀ hl hrule
  rw [hμ', Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _)] at hn
  rw [hμ', hn, Complex.ofReal_one]

theorem eigen_eq_one_of_diag_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), (∀ w : HeightOneSpectrum (𝓞 E), ¬ Formalism.UG.IsInertAt F E v w) → v ∉ X.T → PsiUnr B.ψ v →
    ∀ (dd : Darboux (symp (cA σ) (-1 : AE F E) (incM F G.V.J) (dbl (incM F G.W.J))) ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a'))))
      (omd : GlobalTheory.DblVac.UD σ G.W →* Module.End ℂ (((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → AF F) → ℂ)),
    IsDblCoord (cA σ) (-1 : AE F E) (incM F G.V.J) (incM F G.W.J) G.M.co dd →
    IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1 : AE F E) (incM F G.V.J) (dbl (incM F G.W.J)) dd X.β (diagCols (Fin (a + a'))) omd →
    ∀ r : (Fin a × Fin (a + a') → AF F) → ℂ, Rest (evFin F v) (G.M.vac v) r → tens (evFin F v) (G.M.vac v) r ≠ 0 →
    ∀ p ∈ GlobalTheory.DblVac.KD σ G.W v, p ∈ GlobalTheory.DblVac.PDiag σ G.W → ∀ μ : ℂ,
      omd p (boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x))) =
        μ • boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x)) → μ = 1 := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v _ hv _ dd omd hdd hW r hr h0 p hp hpd μ hμ
  exact eigen_eq_one_of_diag_any F E σ B a a' G X om om' hT v hv dd omd hdd hW r hr h0 p hp hpd μ hμ

end GlobalTheory.DblVacSiegelAny
