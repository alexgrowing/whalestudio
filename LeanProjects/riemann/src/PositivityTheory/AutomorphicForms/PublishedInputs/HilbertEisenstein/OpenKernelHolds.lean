import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.SSmooth
import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.LibOpenLevel

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published
open UpperTheory.HilbertEisensteinWeightOne.LibOpenLevel

namespace UpperTheory.HilbertEisensteinWeightOne.OpenKernelEisenstein

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem le_exp_neg_one {a : WithZero (Multiplicative ℤ)} (h : a < 1) : a ≤ WithZero.exp (-1) := by
  by_cases h0 : a = 0
  · simp [h0]
  · rw [← WithZero.exp_log h0] at h ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    exact WithZero.exp_le_exp.2 (by omega)

theorem val_le_of_mem {w : HeightOneSpectrum (𝓞 F)} : ∀ (c : ℕ) {z : w.adicCompletionIntegers F},
    z ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c →
    Valued.v (z : w.adicCompletion F) ≤ WithZero.exp (-(c : ℤ))
  | 0, z, _ => by
    simpa using (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 F) F w).1 z.2
  | c + 1, z, hz => by
    rw [pow_succ] at hz
    refine Submodule.mul_induction_on (C := fun z : w.adicCompletionIntegers F =>
      Valued.v (z : w.adicCompletion F) ≤ WithZero.exp (-((c + 1 : ℕ) : ℤ))) hz (fun a ha b hb => ?_) (fun x y hx hy => ?_)
    · have h1 := val_le_of_mem c ha
      have h2 : Valued.v (b : w.adicCompletion F) < 1 :=
        (Valuation.mem_maximalIdeal_iff _ (Valued.v : Valuation (w.adicCompletion F) _)).1 hb
      show Valued.v ((a : w.adicCompletion F) * b) ≤ _
      rw [map_mul, show (-((c + 1 : ℕ) : ℤ)) = -(c : ℤ) + -1 by push_cast; ring, WithZero.exp_add]
      exact mul_le_mul' h1 (le_exp_neg_one h2)
    · show Valued.v ((x : w.adicCompletion F) + y) ≤ _
      exact Valuation.map_add_le _ hx hy

def Cond (w : HeightOneSpectrum (𝓞 F)) (c : ℕ) (a : Fin 2 → w.adicCompletion F) : Prop :=
  Valued.v (a 0) ≤ WithZero.exp (-(c : ℤ)) ∧ Valued.v (a 1 - 1) ≤ WithZero.exp (-(c : ℤ))

theorem cond_mul {w : HeightOneSpectrum (𝓞 F)} {c : ℕ} {g : GL (Fin 2) (w.adicCompletion F)} (hg : g ∈ K1 w c)
    {a : Fin 2 → w.adicCompletion F} (ha : Cond w c a) : Cond w c (a ᵥ* (g : Matrix (Fin 2) (Fin 2) (w.adicCompletion F))) := by
  obtain ⟨h, hh, rfl⟩ := hg
  set I := IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c
  have hrow : ![(0 : (w.adicCompletionIntegers F) ⧸ I), 1] ᵥ*
      (Matrix.GeneralLinearGroup.map (n := Fin 2) (Ideal.Quotient.mk I) h : Matrix (Fin 2) (Fin 2) _) = ![0, 1] := hh
  have e0 : Ideal.Quotient.mk I ((h : Matrix (Fin 2) (Fin 2) _) 1 0) = 0 := by
    have := congrFun hrow 0
    simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_two] using this
  have e1 : Ideal.Quotient.mk I ((h : Matrix (Fin 2) (Fin 2) _) 1 1) = 1 := by
    have := congrFun hrow 1
    simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_two] using this
  have h10 := val_le_of_mem c (Ideal.Quotient.eq_zero_iff_mem.1 e0)
  have h11 := val_le_of_mem c (Ideal.Quotient.eq.1 (e1.trans (map_one _).symm))
  have hint : ∀ i j, Valued.v (((h : Matrix (Fin 2) (Fin 2) (w.adicCompletionIntegers F)) i j : w.adicCompletionIntegers F) :
      w.adicCompletion F) ≤ 1 :=
    fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 F) F w).1
      ((h : Matrix (Fin 2) (Fin 2) (w.adicCompletionIntegers F)) i j).2
  have he : WithZero.exp (-(c : ℤ)) ≤ 1 := by
    rw [← WithZero.exp_zero]; exact WithZero.exp_le_exp.2 (by omega)
  have ha1 : Valued.v (a 1) ≤ 1 := by
    have : a 1 = (a 1 - 1) + 1 := by ring
    rw [this]
    exact Valuation.map_add_le _ (ha.2.trans he) (by simp)
  have mle : ∀ {x y : w.adicCompletion F} {e f : WithZero (Multiplicative ℤ)}, Valued.v x ≤ e → Valued.v y ≤ f → Valued.v (x * y) ≤ e * f :=
    fun hx hy => by rw [map_mul]; exact mul_le_mul' hx hy
  set G : Matrix (Fin 2) (Fin 2) (w.adicCompletion F) :=
    ((Matrix.GeneralLinearGroup.map (w.adicCompletionIntegers F).subtype h : GL (Fin 2) (w.adicCompletion F)) :
      Matrix (Fin 2) (Fin 2) (w.adicCompletion F))
  have hG : ∀ i j, G i j = (((h : Matrix (Fin 2) (Fin 2) _) i j : w.adicCompletionIntegers F) : w.adicCompletion F) :=
    fun _ _ => rfl
  constructor
  · have e : (a ᵥ* G) 0 = a 0 * G 0 0 + a 1 * G 1 0 := by simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    rw [e, hG, hG]
    refine Valuation.map_add_le _ ?_ ?_
    · simpa using mle ha.1 (hint 0 0)
    · simpa using mle ha1 h10
  · have e : (a ᵥ* G) 1 - 1 = a 0 * G 0 1 + (a 1 - 1) * G 1 1 + (G 1 1 - 1) := by
      simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_two]; ring
    rw [e, hG, hG]
    refine Valuation.map_add_le _ (Valuation.map_add_le _ ?_ ?_) ?_
    · simpa using mle ha.1 (hint 0 1)
    · simpa using mle ha.2 (hint 1 1)
    · exact h11

theorem pInf_vecMul (x : Fin 2 → Ad F) (k : GL (Fin 2) (Af F)) (j : Fin 2) :
    UpperTheory.V.TR.pInf F ((x ᵥ* (finGL F 2 k : Matrix (Fin 2) (Fin 2) (Ad F))) j) = UpperTheory.V.TR.pInf F (x j) := by
  rw [RingHom.map_vecMul]
  have e : (finGL F 2 k : Matrix (Fin 2) (Fin 2) (Ad F)).map (UpperTheory.V.TR.pInf F) = 1 :=
    congrArg Units.val (UpperTheory.V.TR.pInf_finGL k)
  rw [e, Matrix.vecMul_one]
  rfl

theorem pLoc_vecMul (x : Fin 2 → Ad F) (k : GL (Fin 2) (Af F)) (w : HeightOneSpectrum (𝓞 F)) (j : Fin 2) :
    pLoc F w (pFin F ((x ᵥ* (finGL F 2 k : Matrix (Fin 2) (Fin 2) (Ad F))) j)) =
      ((fun i => pLoc F w (pFin F (x i))) ᵥ*
        (Matrix.GeneralLinearGroup.map (pLoc F w) k : Matrix (Fin 2) (Fin 2) (w.adicCompletion F))) j := by
  rw [RingHom.map_vecMul]
  have e : (finGL F 2 k : Matrix (Fin 2) (Fin 2) (Ad F)).map (pFin F) = k :=
    congrArg Units.val (pFin_finGL k)
  rw [e, RingHom.map_vecMul]
  rfl

theorem cond_glob {c : HeightOneSpectrum (𝓞 F) → ℕ} {k : GL (Fin 2) (Af F)} (hk : k ∈ Kc F c) {x : Fin 2 → Ad F}
    (hx : ∀ w, Valued.v (pLoc F w (pFin F (x 0))) ≤ WithZero.exp (-(c w : ℤ)) ∧
        Valued.v (pLoc F w (pFin F (x 1)) - 1) ≤ WithZero.exp (-(c w : ℤ))) :
    ∀ w, Valued.v (pLoc F w (pFin F ((x ᵥ* (finGL F 2 k : Matrix (Fin 2) (Fin 2) (Ad F))) 0))) ≤ WithZero.exp (-(c w : ℤ)) ∧
        Valued.v (pLoc F w (pFin F ((x ᵥ* (finGL F 2 k : Matrix (Fin 2) (Fin 2) (Ad F))) 1)) - 1) ≤
          WithZero.exp (-(c w : ℤ)) := fun w => by
  have := cond_mul (mem_Kc.1 hk w) (a := fun i => pLoc F w (pFin F (x i))) (hx w)
  rw [pLoc_vecMul, pLoc_vecMul]
  exact this

open Classical in
theorem phi_vecMul {c : HeightOneSpectrum (𝓞 F) → ℕ} {k : GL (Fin 2) (Af F)} (hk : k ∈ Kc F c) (x : Fin 2 → Ad F) :
    Phi c (x ᵥ* (finGL F 2 k : Matrix (Fin 2) (Fin 2) (Ad F))) = Phi c x := by
  have hinv : (x ᵥ* (finGL F 2 k : Matrix (Fin 2) (Fin 2) (Ad F))) ᵥ* (finGL F 2 k⁻¹ : Matrix (Fin 2) (Fin 2) (Ad F)) = x := by
    rw [Matrix.vecMul_vecMul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.vecMul_one]
  have key : (∀ w, Valued.v (pLoc F w (pFin F ((x ᵥ* (finGL F 2 k : Matrix (Fin 2) (Fin 2) (Ad F))) 0))) ≤
        WithZero.exp (-(c w : ℤ)) ∧
        Valued.v (pLoc F w (pFin F ((x ᵥ* (finGL F 2 k : Matrix (Fin 2) (Fin 2) (Ad F))) 1)) - 1) ≤
          WithZero.exp (-(c w : ℤ))) ↔
      (∀ w, Valued.v (pLoc F w (pFin F (x 0))) ≤ WithZero.exp (-(c w : ℤ)) ∧
        Valued.v (pLoc F w (pFin F (x 1)) - 1) ≤ WithZero.exp (-(c w : ℤ))) := by
    refine ⟨fun h => ?_, cond_glob hk⟩
    have := cond_glob (inv_mem hk) h
    rwa [hinv] at this
  simp only [Phi, pInf_vecMul]
  exact congrArg _ (if_congr key rfl rfl)

theorem det_mem {c : HeightOneSpectrum (𝓞 F) → ℕ} {k : GL (Fin 2) (Af F)} (hk : k ∈ Kc F c) (v : HeightOneSpectrum (𝓞 F)) :
    pLoc F v ((Matrix.GeneralLinearGroup.det k : (Af F)ˣ) : Af F) ∈ v.adicCompletionIntegers F := by
  obtain ⟨h, -, he⟩ := mem_Kc.1 hk v
  have e2 : (pLoc F v).mapMatrix (k : Matrix (Fin 2) (Fin 2) (Af F)) =
      (v.adicCompletionIntegers F).subtype.mapMatrix (h : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers F)) :=
    (congrArg Units.val he).symm
  have e : pLoc F v ((Matrix.GeneralLinearGroup.det k : (Af F)ˣ) : Af F) =
      (v.adicCompletionIntegers F).subtype (h : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers F)).det := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det, RingHom.map_det, e2]
  rw [e]
  exact SetLike.coe_mem _

theorem module_finGL {c : HeightOneSpectrum (𝓞 F) → ℕ} {k : GL (Fin 2) (Af F)} (hk : k ∈ Kc F c) :
    (IdeleGroup.ideleModule F (Matrix.GeneralLinearGroup.det (finGL F 2 k)) : ℝ) = 1 := by
  rw [UpperTheory.V.TR.det_finGL, IdeleGroup.ideleModule_apply]
  have h1 : IdeleGroup.infiniteModule (finId F (Matrix.GeneralLinearGroup.det k) : IdeleGroup F) = 1 := by
    unfold IdeleGroup.infiniteModule
    refine Finset.prod_eq_one fun w _ => ?_
    have e : ((finId F (Matrix.GeneralLinearGroup.det k) : IdeleGroup F) : Ad F).1 = 1 := by
      change (1 : InfiniteAdeleRing F) - 0 + 0 = 1
      simp
    rw [e, show (1 : InfiniteAdeleRing F) w = 1 from rfl, norm_one, one_pow]
  have h2 : IdeleGroup.finiteModule (finId F (Matrix.GeneralLinearGroup.det k) : IdeleGroup F) = 1 := by
    refine IdeleGroup.finiteModule_eq_one_of_mem ((IdeleGroup.mem_standardOpenSubgroup F).2 fun v => ⟨?_, ?_⟩)
    · change pLoc F v ((1 : Af F) - 1 + (Matrix.GeneralLinearGroup.det k : Af F)) ∈ _
      rw [sub_self, zero_add]
      exact det_mem hk v
    · change pLoc F v ((1 : Af F) - 1 + (Matrix.GeneralLinearGroup.det k⁻¹ : Af F)) ∈ _
      rw [sub_self, zero_add]
      exact det_mem (inv_mem hk) v
  rw [h1, h2, mul_one]

theorem absD_mul {c : HeightOneSpectrum (𝓞 F) → ℕ} {k : GL (Fin 2) (Af F)} (hk : k ∈ Kc F c) (g : GA F 2) :
    absD (g * finGL F 2 k) = absD g := by
  unfold absD
  rw [map_mul, map_mul, Positive.val_mul, module_finGL hk, mul_one]

theorem thetaS_mul {c : HeightOneSpectrum (𝓞 F) → ℕ} {k : GL (Fin 2) (Af F)} (hk : k ∈ Kc F c) (h : GA F 2) :
    thetaS (Phi c) (h * finGL F 2 k) = thetaS (Phi c) h := by
  simp only [thetaS, Units.val_mul, ← Matrix.vecMul_vecMul, phi_vecMul hk]

theorem eis_glob {ω : HChar F} {c : HeightOneSpectrum (𝓞 F) → ℕ} {k : GL (Fin 2) (Af F)} (hk : k ∈ Kc F c) (g : GA F 2) :
    Eis ω (Phi c) (g * finGL F 2 k) = Eis ω (Phi c) g := by
  have e : ∀ t u, eisInt ω (Phi c) (g * finGL F 2 k) t u = eisInt ω (Phi c) g t u := fun t u => by
    unfold eisInt
    rw [← mul_assoc, thetaS_mul hk, absD_mul hk]
  simp only [Eis, e]

end UpperTheory.HilbertEisensteinWeightOne.OpenKernelEisenstein

namespace UpperTheory.HilbertEisensteinWeightOne

theorem open_kernel_holds : SPois → SInt → SSmooth → SOpen := by
  intro _ _ _ F _ _ _ ω c hH hs
  exact LibOpenLevel.isOpen_stab_of_glob hH _ fun k hk g => OpenKernelEisenstein.eis_glob (LibOpenLevel.mem_Kc.2 hk) g

end UpperTheory.HilbertEisensteinWeightOne
