import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.EvalPB
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.EvalMF

noncomputable section

open Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS

theorem sum_gamma_nnMinus {M : Type*} [AddCommGroup M] [Module ℂ M] (m : ℕ)
    (E : Fin (m + 1) → Fin (m + 1) → Module.End ℂ M) (hE : IsGlRep E)
    (Q : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (hQ : Q⁻¹ * Q = 1) (c₀ : ℂ) (j₀ : Fin (m + 1)) (om : ℂ) (v : M) :
    ∑ d, (c₀ * Q⁻¹ d j₀) • Capelli.nnMinus E (Q (Fin.last m)) om v d =
      (c₀ * (-1 : ℂ) ^ (m + (j₀ : ℕ))) •
        Capelli.cminor (frameE Q E) (Fin.last m).succAbove j₀.succAbove om v := by
  have h := congrArg (fun f => f v) (capelliCov (Module.End ℂ M) m E Q⁻¹ Q om hE hQ (Fin.last m) j₀)
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, Fin.val_last] at h
  have hF : (fun a b => ∑ c', ∑ d', (Q⁻¹ c' a * Q b d') • E c' d') = frameE Q E := rfl
  rw [hF] at h
  rw [mul_smul, h, Finset.sum_comm, Finset.smul_sum]
  unfold Capelli.nnMinus
  simp_rw [Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => ?_
  congr 1
  rw [add_comm (c : ℕ)]
  ring

theorem gamma_formula {k r : ℕ} (P : Mat k r) (z : Fin (2 * r + k + 1) → ℂ)
    (hTz : 0 < Formalism.QuantumDeterminants.Tz k r z) (g g₀ : Mat k r) (hg₀ : Formalism.MainNotions.S.IsFrameW k r z g₀)
    (hd : IsUnit g₀.det) (hPd : IsUnit P.det) :
    ∃ c₀ : ℂ, c₀ ≠ 0 ∧ ∀ d, (P *ᵥ (g⁻¹ *ᵥ xOne k r z)) d =
      c₀ * (g₀⁻¹ * g * P⁻¹)⁻¹ d (if r = 0 then Fin.last _ else 0) := by
  have e : (g₀⁻¹ * g * P⁻¹)⁻¹ = P * (g⁻¹ * g₀) := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hd,
      Matrix.nonsing_inv_nonsing_inv _ hPd]
  have key : ∀ (c₀ : ℂ) (j : Fin (2 * r + k + 1)), g₀ *ᵥ (c₀ • Formalism.QuantumDeterminants.bvec j) = xOne k r z → ∀ d,
      (P *ᵥ (g⁻¹ *ᵥ xOne k r z)) d = c₀ * (g₀⁻¹ * g * P⁻¹)⁻¹ d j := fun c₀ j hj d => by
    rw [e, ← hj, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_smul, Matrix.mul_assoc]
    simp [Formalism.QuantumDeterminants.bvec]
  by_cases hr : r = 0
  · refine ⟨_, by exact_mod_cast (Real.sqrt_pos.mpr hTz).ne', key ((Real.sqrt (Formalism.QuantumDeterminants.Tz k r z) : ℝ) : ℂ) _ ?_⟩
    rw [if_pos hr, xOne, if_pos hr]
    have e2 : Fin.last (2 * r + k) = Formalism.QuantumDeterminants.wI k r (Fin.last k) :=
      Fin.ext (by simp [Formalism.QuantumDeterminants.wI]; omega)
    rw [e2]
    exact hg₀.2.2
  · refine ⟨1, one_ne_zero, key 1 _ ?_⟩
    rw [if_neg hr, xOne, if_neg hr, one_smul]
    exact (hg₀.2.1 ⟨0, Nat.pos_of_ne_zero hr⟩).1

open CapelliMinorRestriction in
theorem evalM : EvalMStatement := by
  intro k r ε u lam h H _ _ _ σ D E V T μ ι hσ hder hV hcas hK hμ hcoef hp hq hgap hHC hgapl z c Vp _ _ _
    π μW μN P hP hB x₀ w v ξ s g hx₀ hg hu hne
  obtain ⟨g₀, Dk, ψ', hfr, hlU, hψ0, hκ, hlW, hCD⟩ := frameLaw k r ε u lam h H σ D E V T μ ι hσ hder hV hcas
    hK hμ hcoef hp hq hgap hHC hgapl z c Vp π μW μN P hP hB x₀ w ξ g hx₀ hg
  have hPer := per_spec k r ε u h z c Vp π μW μN P hP hB hp hq hgap
  obtain ⟨hWb, hTz, hc, hHCW, hW, hN⟩ := hB
  have hE : IsGlRep E := hder.glRep
  have hPd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP.1
  have hH2 := ExponentialSlopeDerivatives.hpk_mul_self k r
  have hgd : IsUnit g.det := Matrix.isUnit_det_of_left_inverse (ExponentialSlopeDerivatives.inv_mul_of_UH hH2 hg)
  have hg₀d : IsUnit g₀.det := Matrix.isUnit_det_of_left_inverse (ExponentialSlopeDerivatives.inv_mul_of_UH hH2 hfr.1)
  set Q : Mat k r := g₀⁻¹ * g * P⁻¹ with hQdef
  have hQd : IsUnit Q.det := by
    rw [hQdef, Matrix.det_mul, Matrix.det_mul]
    exact ((Matrix.isUnit_nonsing_inv_det g₀ hg₀d).mul hgd).mul (Matrix.isUnit_nonsing_inv_det P hPd)
  have hQ1 : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q hQd
  have hQ2 : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q hQd
  set j₀ : Fin (2 * r + k + 1) := if r = 0 then Fin.last _ else 0 with hj₀
  obtain ⟨c₀, hc₀, hβ⟩ := gamma_formula P z hTz g g₀ hfr hg₀d hPd
  rw [← hQdef, ← hj₀] at hβ
  set ψ := Formalism.MainNotions.S.psiGen k r z c with hψdef
  set wH : H := ((w : D) : H) with hwH
  let L : H → Vp := fun m => per P μW μN ψ π (coefX σ x₀ wH m) ξ g
  have hInt : ∀ f : Fin (2 * r + k + 1) → D, (∀ c', f c' ∈ genSub E V) →
      Integrable (perI P ψ π (tMapD σ (xJ P z) x₀ wH (fun c' => ((f c' : D) : H))) ξ g) (μW.prod μN) := by
    intro f hf
    obtain ⟨hsm, -, hbd⟩ := tMapD_spec k r ε lam h H σ D E V T μ ι hσ hder hV hcas hK hμ hcoef hp hq hgap
      hHC hgapl (xJ P z) x₀ w hx₀ f hf
    obtain ⟨C, hC⟩ := hbd []
    exact hPer.1 _ C (cont_of_smoothOnG hsm.1) (fun g' hg' => hC g' hg') g hg ξ
  have hsing : ∀ (d : Fin (2 * r + k + 1)) (m : D),
      (fun c' => (((Pi.single d m : Fin (2 * r + k + 1) → D) c' : D) : H)) = Pi.single d (m : H) := by
    intro d m; funext c'
    by_cases hcd : c' = d
    · subst hcd; simp
    · simp [Pi.single_eq_of_ne hcd]
  have hsingM : ∀ (d : Fin (2 * r + k + 1)) (m : D), m ∈ genSub E V →
      ∀ c', (Pi.single d m : Fin (2 * r + k + 1) → D) c' ∈ genSub E V := by
    intro d m hm c'
    by_cases hcd : c' = d
    · subst hcd; simpa using hm
    · simp [Pi.single_eq_of_ne hcd]
  have hper1 : ∀ (d : Fin (2 * r + k + 1)) (m : H),
      per P μW μN ψ π (tMapD σ (xJ P z) x₀ wH (Pi.single d m)) ξ g = (c₀ * Q⁻¹ d j₀) • L m := by
    intro d m
    rw [ConjugateTransportSingles.per_tMapD_single σ z hWb P hPd μW μN hW hN ψ π x₀ wH d m ξ g hg, hβ d]
  have hIntS : ∀ (d : Fin (2 * r + k + 1)) (m : D), m ∈ genSub E V →
      Integrable (perI P ψ π (tMapD σ (xJ P z) x₀ wH (Pi.single d (m : H))) ξ g) (μW.prod μN) := by
    intro d m hm
    have := hInt _ (hsingM d m hm)
    rwa [hsing] at this
  obtain ⟨d₀, hd₀⟩ : ∃ d₀, Q⁻¹ d₀ j₀ ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    have := congrFun (congrFun hQ1 j₀) j₀
    simp [Matrix.mul_apply, hcon] at this
  have hβ0 : c₀ * Q⁻¹ d₀ j₀ ≠ 0 := mul_ne_zero hc₀ hd₀
  have hadd : ∀ m₁ m₂ : D, m₁ ∈ genSub E V → m₂ ∈ genSub E V →
      L ((m₁ : H) + (m₂ : H)) = L m₁ + L m₂ := by
    intro m₁ m₂ h₁ h₂
    refine smul_right_injective Vp hβ0 ?_
    dsimp only
    rw [smul_add, ← hper1, ← hper1, ← hper1]
    have e : tMapD σ (xJ P z) x₀ wH (Pi.single d₀ ((m₁ : H) + (m₂ : H))) = fun G =>
        tMapD σ (xJ P z) x₀ wH (Pi.single d₀ (m₁ : H)) G + tMapD σ (xJ P z) x₀ wH (Pi.single d₀ (m₂ : H)) G := by
      funext G
      simp only [ConjugateTransportSingles.tMapD_single, coefX_add, mul_add]
    rw [e]
    exact per_add P μW μN ψ π _ _ ξ g (hIntS d₀ m₁ h₁) (hIntS d₀ m₂ h₂)
  have hsmul : ∀ (a : ℂ) (m : H), L (a • m) = a • L m := by
    intro a m
    show per P μW μN ψ π (coefX σ x₀ wH (a • m)) ξ g = _
    rw [show coefX σ x₀ wH (a • m) = fun G => a * coefX σ x₀ wH m G from funext (coefX_smul σ x₀ wH m a)]
    exact per_smul P μW μN ψ π _ a ξ g
  let lin : genSub E V →ₗ[ℂ] Vp :=
    { toFun := fun m => L ((m : D) : H)
      map_add' := fun m₁ m₂ => by
        simp only [Submodule.coe_add]
        exact hadd _ _ m₁.2 m₂.2
      map_smul' := fun a m => by
        simp only [Submodule.coe_smul, RingHom.id_apply]
        exact hsmul a _ }
  set om : ℂ := ((-(LemK.thV lam s) : ℝ) : ℂ) with hom
  refine ⟨Q (Fin.last _), ?_⟩
  have hv : (v : D) ∈ genSub E V := le_gen E V v.2
  have hnn : ∀ d, Capelli.nnMinus E (Q (Fin.last _)) om (v : D) d ∈ genSub E V := by
    intro d
    unfold Capelli.nnMinus
    exact Submodule.sum_mem _ fun c' _ => Submodule.smul_mem _ _
      (CapelliMinorMembership.cminor_mem (fun a b x hx => gen_stable E V a b hx) _ _ _ _ hv)
  have hexp : per P μW μN ψ π (tMapD σ (xJ P z) x₀ wH
      (fun c' => ((Capelli.nnMinus E (Q (Fin.last _)) om (v : D) c' : D) : H))) ξ g =
      L (((∑ d, (c₀ * Q⁻¹ d j₀) • Capelli.nnMinus E (Q (Fin.last _)) om (v : D) d : D)) : H) := by
    rw [show tMapD σ (xJ P z) x₀ wH
        (fun c' => ((Capelli.nnMinus E (Q (Fin.last _)) om (v : D) c' : D) : H)) = fun G =>
        ∑ d, tMapD σ (xJ P z) x₀ wH
          (Pi.single d ((Capelli.nnMinus E (Q (Fin.last _)) om (v : D) d : D) : H)) G
        from funext (ConjugateTransportSingles.tMapD_sum σ (xJ P z) x₀ wH _)]
    rw [per_sum P μW μN ψ π Finset.univ _ ξ g (fun d _ => hIntS d _ (hnn d))]
    simp_rw [hper1]
    have hco : (((∑ d, (c₀ * Q⁻¹ d j₀) •
        (⟨_, hnn d⟩ : genSub E V) : genSub E V)) : D) =
        ∑ d, (c₀ * Q⁻¹ d j₀) • Capelli.nnMinus E (Q (Fin.last _)) om (v : D) d := by
      simp
    rw [← hco]
    show _ = lin _
    rw [map_sum]
    simp only [map_smul]
    rfl
  rw [hexp, sum_gamma_nnMinus (2 * r + k) E hE Q hQ2 c₀ j₀ om (v : D), Submodule.coe_smul, hsmul]
  refine smul_ne_zero (mul_ne_zero hc₀ (pow_ne_zero _ (by norm_num))) ?_
  have hinj : Function.Injective (capIdx k r) := fun a b hab =>
    Fin.ext (by simpa [capIdx] using congrArg Fin.val hab)
  have hS₃ : ∀ a b, ∀ x ∈ genSub E V,
      (fun a b => frameE Q E (capIdx k r a) (capIdx k r b)) a b x ∈ genSub E V :=
    fun a b x hx => gen_stable_frame E V Q _ _ hx
  have hfac : ∀ j : Fin k, (om - (r : ℂ)) + ((u j : ℝ) : ℂ) - ((k : ℂ) - 1) / 2 ≠ 0 := by
    intro j
    have e : (om - (r : ℂ)) + ((u j : ℝ) : ℂ) - ((k : ℂ) - 1) / 2 = (((u j - lam s + 1 / 2) : ℝ) : ℂ) := by
      simp only [hom, LemK.thV]
      push_cast
      ring
    rw [e, Complex.ofReal_ne_zero]
    intro h0
    exact hu j (by linarith)
  have hvL : lin ⟨(v : D), hv⟩ ≠ 0 := hne
  by_cases hr : r = 0
  · have hj : j₀ = Fin.last _ := by rw [hj₀, if_pos hr]
    rw [hj]
    have hk0 : k + 1 = 2 * r + k + 1 := by omega
    have hinj0 : Function.Injective (Fin.cast hk0) := Fin.cast_injective hk0
    have hS₀ : ∀ a b, ∀ x ∈ genSub E V,
        (fun a b => frameE Q E (Fin.cast hk0 a) (Fin.cast hk0 b)) a b x ∈ genSub E V :=
      fun a b x hx => gen_stable_frame E V Q _ _ hx
    have hD0 : ∀ i j, lin ∘ₗ resE (fun a b => frameE Q E (Fin.cast hk0 a) (Fin.cast hk0 b)) (genSub E V) hS₀
        (Fin.castSucc i) (Fin.castSucc j) = Dk i j ∘ₗ lin := by
      intro i j
      have ei : ∀ i : Fin k, Fin.cast hk0 (Fin.castSucc i) = capIdx k r (Capelli.wIdx k r i) := by
        intro i; apply Fin.ext; simp [capIdx, Capelli.wIdx]; omega
      refine LinearMap.ext fun m => ?_
      have := hlW i j (m : D) m.2
      rw [← ei, ← ei] at this
      exact this
    have hB := Capelli.whittakerZeroStatement (genSub E V) Vp k
      (resE (fun a b => frameE Q E (Fin.cast hk0 a) (Fin.cast hk0 b)) (genSub E V) hS₀) Dk lin om hD0
    have hB' := congrArg (fun f => f (⟨(v : D), hv⟩ : genSub E V)) hB
    simp only [LinearMap.comp_apply] at hB'
    have eC : (Fin.cast hk0 ∘ Fin.castSucc : Fin k → Fin (2 * r + k + 1)) =
        (Fin.last (2 * r + k)).succAbove ∘ Fin.cast (by omega : k = 2 * r + k) := by
      funext i; apply Fin.ext; simp [Fin.succAbove_last]
    have hLHS : L ((Capelli.cminor (frameE Q E) (Fin.last (2 * r + k)).succAbove
        (Fin.last (2 * r + k)).succAbove om (v : D) : D) : H) =
        lin (Capelli.cminor (resE (fun a b => frameE Q E (Fin.cast hk0 a) (Fin.cast hk0 b)) (genSub E V) hS₀)
          Fin.castSucc Fin.castSucc om ⟨(v : D), hv⟩) := by
      show _ = L (((Capelli.cminor (resE (fun a b => frameE Q E (Fin.cast hk0 a) (Fin.cast hk0 b)) (genSub E V) hS₀)
          Fin.castSucc Fin.castSucc om ⟨(v : D), hv⟩ : genSub E V) : D) : H)
      rw [cminor_resE, cminor_reindex (frameE Q E) (Fin.cast hk0) hinj0, eC, cminor_cast]
    rw [hLHS, hB', hCD]
    refine smul_ne_zero (Finset.prod_ne_zero_iff.mpr fun j _ => ?_) hvL
    have := hfac j
    simpa [hr] using this
  · have hj : j₀ = 0 := by rw [hj₀, if_neg hr]
    rw [hj]
    have hrp : 0 < r := Nat.pos_of_ne_zero hr
    have hl : ∀ a b, Capelli.blk k r a < Capelli.blk k r b →
        lin ∘ₗ resE (fun a b => frameE Q E (capIdx k r a) (capIdx k r b)) (genSub E V) hS₃ a b = ψ' a b • lin :=
      fun a b hab => LinearMap.ext fun m => hlU a b hab (m : D) m.2
    have hD : ∀ i j, lin ∘ₗ resE (fun a b => frameE Q E (capIdx k r a) (capIdx k r b)) (genSub E V) hS₃
        (Capelli.wIdx k r i) (Capelli.wIdx k r j) = Dk i j ∘ₗ lin :=
      fun i j => LinearMap.ext fun m => hlW i j (m : D) m.2
    have hGl : IsGlRep (resE (fun a b => frameE Q E (capIdx k r a) (capIdx k r b)) (genSub E V) hS₃) :=
      isGlRep_resE _ _ _ (isGlRep_reindex (frameE Q E) (capIdx k r) hinj (frameGl Q E hQ1 hQ2 hE))
    have hB := Capelli.capelliB (genSub E V) Vp k r
      (resE (fun a b => frameE Q E (capIdx k r a) (capIdx k r b)) (genSub E V) hS₃) Dk ψ' lin om hGl hrp
      hl hψ0 hD
    have hB' := congrArg (fun f => f (⟨(v : D), hv⟩ : genSub E V)) hB
    simp only [LinearMap.comp_apply, LinearMap.smul_apply] at hB'
    have hcast : k + 2 * r = 2 * r + k := by omega
    have eC : (capIdx k r ∘ Fin.castSucc : Fin (k + 2 * r) → Fin (2 * r + k + 1)) =
        (Fin.last (2 * r + k)).succAbove ∘ Fin.cast hcast := by
      funext i; apply Fin.ext; simp [capIdx, Fin.succAbove_last]
    have eS : (capIdx k r ∘ Fin.succ : Fin (k + 2 * r) → Fin (2 * r + k + 1)) =
        (0 : Fin (2 * r + k + 1)).succAbove ∘ Fin.cast hcast := by
      funext i; apply Fin.ext; simp [capIdx, Fin.succAbove_zero]
    have hLHS : L ((Capelli.cminor (frameE Q E) (Fin.last (2 * r + k)).succAbove
        (0 : Fin (2 * r + k + 1)).succAbove om (v : D) : D) : H) =
        lin (Capelli.cminor (resE (fun a b => frameE Q E (capIdx k r a) (capIdx k r b)) (genSub E V) hS₃)
          Fin.castSucc Fin.succ om ⟨(v : D), hv⟩) := by
      show _ = L (((Capelli.cminor (resE (fun a b => frameE Q E (capIdx k r a) (capIdx k r b)) (genSub E V) hS₃)
          Fin.castSucc Fin.succ om ⟨(v : D), hv⟩ : genSub E V) : D) : H)
      rw [cminor_resE, cminor_reindex (frameE Q E) (capIdx k r) hinj, eC, eS, cminor_cast]
    rw [hLHS, hB', hCD]
    exact smul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) (hκ hrp))
      (smul_ne_zero (Finset.prod_ne_zero_iff.mpr fun j _ => hfac j) hvL)

end ReciprocityTheory.ChartRestriction.DS.Lap
