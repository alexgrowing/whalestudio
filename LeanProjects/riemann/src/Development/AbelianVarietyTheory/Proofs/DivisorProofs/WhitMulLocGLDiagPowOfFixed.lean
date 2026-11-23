import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShintaniFormulaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormGLContinuous
import GroundTheory.AutomorphicForms.MultiplicityOne.Functional

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.LFun GlobalTheory.PRep Formalism.UG
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.MultiplicityOne

namespace GlobalTheory.JSW

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem whit_mul_right (F : GA E a → ℂ) (y x : GA E a) : whit F (y * x) = whit (fun z => F (z * x)) y := by
  simp only [whit, whittaker, mul_assoc]

theorem integrableOn_whit {F : GA E a → ℂ} (hc : Continuous F) (y : GA E a) :
    IntegrableOn (fun X => F (uGL X * y) * (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ))
      (vecDomain E (Pos a)) (vecMeasure E (Pos a)) := by
  have hcont : Continuous fun X : Pos a → Ad E =>
      F (uGL X * y) * (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ) :=
    (hc.comp (continuous_uGL.mul continuous_const)).mul continuous_adelicChar_neg_supSum
  exact (hcont.continuousOn.integrableOn_compact isCompact_closure_vecDomain).mono_set subset_closure

theorem whit_add {F G : GA E a → ℂ} (hF : Continuous F) (hG : Continuous G) (y : GA E a) :
    whit (F + G) y = whit F y + whit G y := by
  unfold whit whittaker
  rw [← integral_add (integrableOn_whit hF y) (integrableOn_whit hG y)]
  congr 1
  funext X
  simp only [Pi.add_apply, add_mul]

theorem whit_smul (c : ℂ) (F : GA E a → ℂ) (y : GA E a) : whit (c • F) y = c * whit F y := by
  unfold whit whittaker
  rw [← integral_const_mul]
  congr 1
  funext X
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]

def psiLocChar (w : HeightOneSpectrum (𝓞 E)) : AddChar (w.adicCompletion E) ℂ where
  toFun := psiLoc w
  map_zero_eq_one' := by simp [psiLoc]
  map_add_eq_mul' x y := by simp only [psiLoc, map_add, AddChar.map_add_eq_mul, Circle.coe_mul]

theorem finGL_locGL_apply (w : HeightOneSpectrum (𝓞 E)) (k : GL (Fin a) (w.adicCompletion E)) (i j : Fin a) :
    ((finGL E a (locGL E a w k) : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) i j =
      (1 : Matrix (Fin a) (Fin a) (Ad E)) i j - sFin E (sLoc E w ((1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j))
        + sFin E (sLoc E w ((k : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j)) := by
  change (1 : Matrix (Fin a) (Fin a) (Ad E)) i j - sFin E ((1 : Matrix (Fin a) (Fin a) (Af E)) i j) +
    sFin E ((1 : Matrix (Fin a) (Fin a) (Af E)) i j - sLoc E w ((1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j)
      + sLoc E w ((k : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j)) = _
  rw [map_add, map_sub]
  abel

end GlobalTheory.JSW

namespace GlobalTheory.JSW
variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem GA_ext {x y : GA E a}
    (hinf : GeneralLinearGroup.map (RingHom.fst (InfiniteAdeleRing E) (Af E)) x =
      GeneralLinearGroup.map (RingHom.fst (InfiniteAdeleRing E) (Af E)) y)
    (hfin : ∀ v : HeightOneSpectrum (𝓞 E), GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) x =
      GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) y) : x = y := by
  ext i j
  refine Prod.ext ?_ (FiniteAdeleRing.ext _ fun v => ?_)
  · exact congrArg (fun m : GL (Fin a) (InfiniteAdeleRing E) => (m : Matrix (Fin a) (Fin a) (InfiniteAdeleRing E)) i j) hinf
  · exact congrArg (fun m : GL (Fin a) (v.adicCompletion E) => (m : Matrix (Fin a) (Fin a) (v.adicCompletion E)) i j) (hfin v)

theorem commute_finGL_locGL (w : HeightOneSpectrum (𝓞 E)) {g : GA E a}
    (hg : GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) g = 1) (k : GL (Fin a) (w.adicCompletion E)) :
    g * finGL E a (locGL E a w k) = finGL E a (locGL E a w k) * g := by
  have key : ∀ {R : Type} [CommRing R] (c : Ad E →+* R),
      (GeneralLinearGroup.map c g = 1 ∨ GeneralLinearGroup.map c (finGL E a (locGL E a w k)) = 1) →
      GeneralLinearGroup.map c (g * finGL E a (locGL E a w k)) =
        GeneralLinearGroup.map c (finGL E a (locGL E a w k) * g) := by
    intro R _ c h
    rw [map_mul, map_mul]
    rcases h with h | h <;> rw [h] <;> simp
  refine GA_ext (key _ (Or.inr ?_)) fun v => key _ ?_
  · exact map_cornerGL_of_zero _ _ (fun x => rfl) _
  · by_cases hv : v = w
    · subst hv; exact Or.inl hg
    · refine Or.inr ?_
      rw [finGL, map_cornerGL_of_hom (sFin E) ((pLoc E v).comp (pFin E)) (pLoc E v) (fun x => rfl)]
      exact pLoc_locGL_of_ne hv k

end GlobalTheory.JSW

namespace GlobalTheory.JSW
variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem finGL_locGL_eq_uGL (w : HeightOneSpectrum (𝓞 E)) {u : GL (Fin a) (w.adicCompletion E)}
    (hu : u ∈ GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin a)) :
    finGL E a (locGL E a w u) =
      uGL (fun p : Pos a => sFin E (sLoc E w ((u : Matrix (Fin a) (Fin a) (w.adicCompletion E)) p.1.1 p.1.2))) := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB _).1 hu
  ext i j
  rw [finGL_locGL_apply, coe_uGL, uMat_apply]
  by_cases hij : i = j
  · subst hij; simp [h2]
  · rw [if_neg hij, Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, map_zero, map_zero, sub_zero, zero_add]
    by_cases hlt : i < j
    · rw [dif_pos hlt]
    · rw [dif_neg hlt, h1 i j (lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hij)), map_zero, map_zero]

theorem sum_pos_superdiag {M : Type} [AddCommMonoid M] (f : Fin a → Fin a → M) :
    ∑ p ∈ Finset.univ.filter (fun p : Pos a => (p.1.2 : ℕ) = p.1.1 + 1 ∧ 0 ≤ (p.1.2 : ℕ)), f p.1.1 p.1.2 =
      ∑ i : Fin a, ∑ j ∈ Finset.univ.filter (fun j : Fin a => (j : ℕ) = (i : ℕ) + 1), f i j := by
  classical
  have hR : ∑ i : Fin a, ∑ j ∈ Finset.univ.filter (fun j : Fin a => (j : ℕ) = (i : ℕ) + 1), f i j =
      ∑ q ∈ Finset.univ.filter (fun q : Fin a × Fin a => (q.2 : ℕ) = q.1 + 1), f q.1 q.2 := by
    simp only [Finset.sum_filter]
    exact (Fintype.sum_prod_type' (fun x y : Fin a => if (y : ℕ) = (x : ℕ) + 1 then f x y else 0)).symm
  rw [hR]
  refine Finset.sum_bij (fun p _ => p.1) (fun p hp => ?_) (fun p _ q _ h => Subtype.ext h) (fun q hq => ?_)
    (fun p _ => rfl)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact hp.1
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    refine ⟨⟨q, ?_⟩, ?_, rfl⟩
    · rw [Fin.lt_def]; omega
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hq, Nat.zero_le _⟩

theorem supSum_sLoc (w : HeightOneSpectrum (𝓞 E)) (u : GL (Fin a) (w.adicCompletion E)) :
    supSum 0 (fun p : Pos a => sFin E (sLoc E w ((u : Matrix (Fin a) (Fin a) (w.adicCompletion E)) p.1.1 p.1.2))) =
      sFin E (sLoc E w (GlobalTheory.Whittaker.superDiag u)) := by
  classical
  let t : w.adicCompletion E →+ Ad E := (sFin E).toAddMonoidHom.comp (sLoc E w).toAddMonoidHom
  change supSum 0 (fun p : Pos a => t ((u : Matrix (Fin a) (Fin a) (w.adicCompletion E)) p.1.1 p.1.2)) =
    t (GlobalTheory.Whittaker.superDiag u)
  rw [GlobalTheory.Whittaker.superDiag, map_sum, supSum]
  simp only [map_sum]
  exact sum_pos_superdiag (fun i j => t ((u : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j))

end GlobalTheory.JSW

namespace GlobalTheory.JSW
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem whit_mul_locGL_diagPow_of_fixed (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E))
    (hψ : ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, psiLoc w (x * y) = 1) ↔ x ∈ Ov E w)
    (α : Fin a → ℂˣ) (hα : HasSatGL w (π.locRep w) (Finset.univ.val.map α))
    (φ : π.V) (hφ : φ ∈ fixed (π.locRep w) (KGL w a))
    (g : GA E a) (hg : GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) g = 1)
    (ϖ : (w.adicCompletion E)ˣ) (hϖ : IsUnifV E w (ϖ : w.adicCompletion E)) (l : Fin a → ℕ) :
    whit φ.1.1 (g * finGL E a (locGL E a w (diagPow ϖ l))) =
      sphW (qV E w) (fun i => (α i : ℂ)) l * whit φ.1.1 g := by
  classical
  have hcont : ∀ ψ : π.V, Continuous ψ.1.1 := fun ψ => (π.cusp _ ψ.2).1.continuous
  have hleft : AutomorphicForm.IsLeftInvariant φ.1.1 := fun γ y => by
    rw [show AdelicGLn.diagonal E a γ = ratGL E a γ from Units.ext (Matrix.ext fun _ _ => rfl)]
    exact (π.cusp _ φ.2).1.left γ y
  let f : π.V →ₗ[ℂ] (GL (Fin a) (w.adicCompletion E) → ℂ) :=
    { toFun := fun ψ h => whit ψ.1.1 (g * finGL E a (locGL E a w h))
      map_add' := fun ψ ψ' => funext fun h => whit_add (hcont ψ) (hcont ψ') _
      map_smul' := fun c ψ => funext fun h => whit_smul c ψ.1.1 _ }
  have hf : ∀ k (ψ : π.V), f (π.locRep w k ψ) = rightReg ℂ _ ℂ k (f ψ) := by
    intro k ψ
    funext h
    change whit (fun z => ψ.1.1 (z * finGL E a (locGL E a w k))) (g * finGL E a (locGL E a w h)) =
      whit ψ.1.1 (g * finGL E a (locGL E a w (h * k)))
    rw [map_mul, map_mul, ← mul_assoc, whit_mul_right ψ.1.1 (g * finGL E a (locGL E a w h))]
  by_cases h0 : φ = 0
  · subst h0
    have hz : ∀ y, whit ((0 : π.V) : Sm E a).1 y = 0 := fun y => by
      have e := whit_smul 0 (fun _ : GA E a => (0 : ℂ)) y
      rw [zero_mul] at e
      exact (congrArg (fun F => whit F y) (funext fun _ => (zero_mul _).symm)).trans e
    rw [hz, hz, mul_zero]
  have hsat := hα.2 φ hφ h0
  have hmain := GlobalTheory.T.shintani_formula_alt E w a (psiLocChar w) hψ (f φ) α ?_ ?_ ?_ ϖ hϖ l
  · change whit φ.1.1 (g * finGL E a (locGL E a w (diagPow ϖ l))) = _ * whit φ.1.1 (g * finGL E a (locGL E a w 1))
      at hmain
    rwa [map_one, map_one, mul_one] at hmain
  · intro u hu h
    change whit φ.1.1 (g * finGL E a (locGL E a w (u * h))) =
      psiLoc w (GlobalTheory.Whittaker.superDiag u) * whit φ.1.1 (g * finGL E a (locGL E a w h))
    rw [map_mul, map_mul, ← mul_assoc, commute_finGL_locGL w hg u, mul_assoc, finGL_locGL_eq_uGL w hu, whit,
      whittaker_uGL_mul (hcont φ) hleft, supSum_sLoc]
    rfl
  · intro h k hk
    change whit φ.1.1 (g * finGL E a (locGL E a w (h * k))) = whit φ.1.1 (g * finGL E a (locGL E a w h))
    rw [map_mul, map_mul, ← mul_assoc, whit_mul_right]
    congr 1
    funext z
    exact congrArg (fun ψ : π.V => ψ.1.1 z) (GlobalTheory.LGrp.mem_fixed.1 hφ k hk)
  · intro ϖ' hϖ' j hj
    rw [← map_heckeVec (Final.GLintComm E w a) (Tj_mem_hecke hϖ' j) f hf, hsat.2.2.2 ϖ' hϖ' j hj, map_smul]

end GlobalTheory.JSW

namespace GlobalTheory.JSW

theorem whit_mul_locGL_diagPow : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CuspSub E a)
    (w : HeightOneSpectrum (𝓞 E)) (α : Fin a → ℂˣ),
    (∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, GlobalTheory.JSW.psiLoc w (x * y) = 1) ↔ x ∈ Ov E w) →
    HasSatGL w (π.locRep w) (Finset.univ.val.map α) → ∀ φ ∈ π.V, (∀ k ∈ KGL w a, act (.fin (locGL E a w k)) φ = φ) →
    ∀ g : GA E a, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) g = 1 → ∀ (ϖ : (w.adicCompletion E)ˣ),
    IsUnifV E w (ϖ : w.adicCompletion E) → ∀ l : Fin a → ℕ,
    GlobalTheory.JSW.whit φ.1 (g * finGL E a (locGL E a w (GlobalTheory.JSW.diagPow ϖ l))) =
      GlobalTheory.JSW.sphW (qV E w) (fun i => (α i : ℂ)) l * GlobalTheory.JSW.whit φ.1 g := by
  intro E _ _ _ a π w α hψ hα φ hφV hφ g hg ϖ hϖ l
  exact whit_mul_locGL_diagPow_of_fixed π w hψ α hα ⟨φ, hφV⟩
    (GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext (hφ k hk)) g hg ϖ hϖ l

end GlobalTheory.JSW
