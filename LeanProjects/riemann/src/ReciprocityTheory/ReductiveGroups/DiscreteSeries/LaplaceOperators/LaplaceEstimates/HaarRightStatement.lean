import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.PsiDatumStatement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.ReproducingKernels.DecDeriv
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.GapNeed
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.LFSingleNe
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.FrameForm
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.SIntEquiv
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.HermitianMeasures.HaarUp

noncomputable section

open Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS

def frameE {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M] (Q : Matrix (Fin n) (Fin n) ℂ)
    (E : Fin n → Fin n → Module.End ℂ M) (i j : Fin n) : Module.End ℂ M :=
  ∑ a, ∑ b, (Q⁻¹ a i * Q j b) • E a b

def capIdx (k r : ℕ) (i : Fin (k + 2 * r + 1)) : Fin (2 * r + k + 1) := Fin.cast (by omega) i

def coefL {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {Vp : Type*} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [CompleteSpace Vp]
    (P : Mat k r) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)) (ψ : Mat k r → ℂ) (π : Mat k r → (Vp →L[ℂ] Vp))
    (σ : Mat k r → (H →L[ℂ] H)) (x₀ : Mat k r) (w : H) (ξ : Vp) (g : Mat k r) (m : H) : Vp :=
  per P μW μN ψ π (coefX σ x₀ w m) ξ g

def HaarRightStatement : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)),
    Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z →
    Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW → Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN →
    (∀ h ∈ Formalism.QuantumDeterminants.UWset k r z, μW.map (fun x => fun i j => (Matrix.of x * h) i j) = μW) ∧
    (∀ m ∈ Formalism.QuantumDeterminants.Nset k r, μN.map (fun x => fun i j => (Matrix.of x * m) i j) = μN) ∧
    (∀ h ∈ Formalism.QuantumDeterminants.UWset k r z, μN.map (fun x => fun i j => (h * Matrix.of x * h⁻¹) i j) = μN)

def PerEquivStatement : Prop :=
  ∀ (k r : ℕ) (u : Fin k → ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (Vp : Type) [NormedAddCommGroup Vp]
    [InnerProductSpace ℂ Vp] [CompleteSpace Vp] (π : Mat k r → (Vp →L[ℂ] Vp)) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r))
    (P : Mat k r), IsBData z c u π μW μN →
    ∀ (F : Mat k r → ℂ) (ξ : Vp) (x : Mat k r), ∀ h ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ m ∈ Formalism.QuantumDeterminants.Nset k r,
      per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π F ξ (h * m * x) =
        Formalism.MainNotions.S.psiGen k r z c m • π h (per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π F ξ x)

theorem perEquiv : PerEquivStatement := by
  intro k r u z c Vp _ _ _ π μW μN P hB F ξ x h hh m hm
  exact EvaluationEquivalence.sInt_equiv hB (fun g => F (P * g * P⁻¹)) ξ x hh hm

def FrameLawStatement : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (u : Fin k → ℝ) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mat k r → (H →L[ℂ] H)) (D : Submodule ℂ H)
    (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ D) (V : Submodule ℂ D)
    (T : S7.KType ε (lowK ε lam)) (μ : Fin (2 * r + k + 1) → ℤ) (ι : V ≃ₗ[ℂ] T.V),
    IsURepOn (UJset ε) σ → IsDerivedOn ε σ D E → IsKIrrHW ε E (lowK ε lam) V →
    (∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v) →
    (∀ k' ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k' v) → S7.IsMu lam μ →
    (∀ g ∈ UJset ε, ∀ v v' : V,
      ⟪((v' : D) : H), σ g ((v : D) : H)⟫_ℂ = ⟪ι v', S7.PsiM T μ g (ι v)⟫_ℂ) →
    pOf ε = k + r → qOf ε = r + 1 → StepGap ε r h → S7.IsHCParam lam → GapAtLeast ε lam h →
    ∀ (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (Vp : Type) [NormedAddCommGroup Vp]
    [InnerProductSpace ℂ Vp] [CompleteSpace Vp] (π : Mat k r → (Vp →L[ℂ] Vp)) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r))
    (P : Mat k r), Formalism.MainNotions.S.IsCayley k r ε P → IsBData z c u π μW μN →
    ∀ (x₀ : Mat k r) (w : V) (ξ : Vp) (g : Mat k r), x₀ ∈ UJset ε → g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) →
      ∃ (g₀ : Mat k r) (Dk : Fin k → Fin k → Module.End ℂ Vp)
        (ψ' : Fin (k + 2 * r + 1) → Fin (k + 2 * r + 1) → ℂ),
        Formalism.MainNotions.S.IsFrameW k r z g₀ ∧
        (∀ a b, Capelli.blk k r a < Capelli.blk k r b → ∀ m ∈ genSub E V,
          coefL P μW μN (Formalism.MainNotions.S.psiGen k r z c) π σ x₀ ((w : D) : H) ξ g
              ((frameE (g₀⁻¹ * g * P⁻¹) E (capIdx k r a) (capIdx k r b) m : D) : H) =
            ψ' a b • coefL P μW μN (Formalism.MainNotions.S.psiGen k r z c) π σ x₀ ((w : D) : H) ξ g ((m : D) : H)) ∧
        (∀ a b, Capelli.blk k r a < Capelli.blk k r b → ¬ Capelli.IsSimplePair k r a b → ψ' a b = 0) ∧
        (0 < r → Capelli.kappa k r ψ' ≠ 0) ∧
        (∀ i j, ∀ m ∈ genSub E V,
          coefL P μW μN (Formalism.MainNotions.S.psiGen k r z c) π σ x₀ ((w : D) : H) ξ g
              ((frameE (g₀⁻¹ * g * P⁻¹) E (capIdx k r (Capelli.wIdx k r i)) (capIdx k r (Capelli.wIdx k r j)) m :
                D) : H) =
            Dk i j (coefL P μW μN (Formalism.MainNotions.S.psiGen k r z c) π σ x₀ ((w : D) : H) ξ g ((m : D) : H))) ∧
        ∀ (x : ℂ) (ζ : Vp), Capelli.capelliC Dk x ζ =
          (∏ j : Fin k, (x + ((u j : ℝ) : ℂ) - ((k : ℂ) - 1) / 2)) • ζ

theorem frameLaw : FrameLawStatement := by
  intro k r ε u lam h H _ _ _ σ D E V T μ ι hσ hD _ _ _ hμ hcoef hp hq hgap hHC hGap z c Vp _ _ _ π μW μN
    P hP hB x₀ w ξ g hx₀ hg
  obtain ⟨hq0, hneed⟩ := gapNeed k r ε h hp hq hgap
  have hdd := S0.DecDeriv.decDeriv _ ε lam h T μ hHC hGap hneed hq0 hμ
  have hb := CurveContinuity.per_gap hgap
  have hh0 : 0 ≤ h := by
    have h1 := hgap.1
    have : 0 ≤ 3 * ((2 * r + k + 1 : ℕ) : ℝ) / 2 := by positivity
    have := le_max_left (3 * ((2 * r + k + 1 : ℕ) : ℝ) / 2)
      (1 + ((2 * r + k + 1 : ℕ) : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ))
    linarith
  have ha0 : 0 ≤ aExp ε h := div_nonneg hh0 (by positivity)
  have hgood : ∀ m : D, m ∈ genSub E V → TmGood ε σ x₀ ((w : D) : H) (aExp ε h) (m : H) :=
    fun m hm => tmC_good_genSub hσ hD hμ hcoef ha0 (fun wd v₁ v₂ => hdd wd v₁ v₂) hx₀ w hm
  have hT := hB.2.1
  obtain ⟨g₀, hg₀, hρ⟩ := hB.2.2.2.1
  obtain ⟨dρ, hdρ, hcap⟩ := EvaluationEquivalence.exists_derived _ hρ
  set l : D → Vp := fun m => coefL P μW μN (Formalism.MainNotions.S.psiGen k r z c) π σ x₀ ((w : D) : H) ξ g (m : H)
    with hl
  have hact : ∀ X : Mat k r, ∀ m ∈ genSub E V, actM E X m ∈ genSub E V := fun X m hm => by
    simp only [actM, LinearMap.sum_apply, LinearMap.smul_apply]
    exact Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _
      (Submodule.mem_sInf.mpr fun S hS => hS.2 a b _ (Submodule.mem_sInf.mp hm S hS))
  let Λ : Mat k r → Module.End ℂ D := fun Z => actM E ((g * P⁻¹)⁻¹ * (g₀ * Z * g₀⁻¹) * (g * P⁻¹))
  have hΛ : ∀ Y1 Y2 : Mat k r, ∀ m ∈ genSub E V,
      l (Λ (Y1 + Complex.I • Y2) m) = l (Λ Y1 m) + Complex.I • l (Λ Y2 m) := fun Y1 Y2 m hm => by
    have e : Λ (Y1 + Complex.I • Y2) m = Λ Y1 m + Complex.I • Λ Y2 m := by
      simp only [Λ, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, actM,
        Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_smul, Finset.sum_add_distrib,
        LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum, smul_smul]
    rw [e]
    exact EvaluationEquivalence.per_lin hP hB hg hb ξ (hgood _ (hact _ m hm)) (hgood _ (hact _ m hm)) _
  have hfr : ∀ i j, frameE (g₀⁻¹ * g * P⁻¹) E i j = Λ (Matrix.single i j 1) := fun i j => by
    have e : (g * P⁻¹)⁻¹ * (g₀ * Matrix.single i j 1 * g₀⁻¹) * (g * P⁻¹) =
        (g₀⁻¹ * g * P⁻¹)⁻¹ * Matrix.single i j 1 * (g₀⁻¹ * g * P⁻¹) := by
      rw [Matrix.mul_assoc g₀⁻¹, Matrix.mul_inv_rev g₀⁻¹,
        Matrix.nonsing_inv_nonsing_inv _ (TransportGeo.uh_det hg₀.1)]
      simp only [Matrix.mul_assoc]
    simp only [Λ, e, frameE, actM]
    generalize g₀⁻¹ * g * P⁻¹ = Q
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    congr 1
    simp [Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq]
  have hder : ∀ Y : Mat k r, Yᴴ * Formalism.QuantumDeterminants.Hpk k r + Formalism.QuantumDeterminants.Hpk k r * Y = 0 → ∀ m ∈ genSub E V,
      HasDerivAt (fun t : ℝ => per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π (coefX σ x₀ ((w : D) : H) (m : H)) ξ
        (g₀ * NormedSpace.exp ((t : ℂ) • Y) * g₀⁻¹ * g)) (l (Λ Y m)) 0 := fun Y hY m hm => by
    have := EvaluationEquivalence.per_deriv hσ hD hx₀ hP hB hg hb ξ (EvaluationEquivalence.conj_lie hg₀.1 hY) m (hgood m hm)
      (hgood _ (hact _ m hm))
    simp only [EvaluationEquivalence.exp_conj_frame hg₀.1] at this
    exact this
  have h1W : (1 : Mat k r) ∈ Formalism.QuantumDeterminants.UWset k r z := (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z).one_mem
  have h1N : (1 : Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r := (Formalism.FourierDecayAlt.P.unipotent_radical_closed k r).one_mem
  have hπ := hcTypeW_uRep k r z u Vp π hB.1 hT hB.2.2.2.1
  have hN : ∀ Y : Mat k r, Y ∈ Base.N.levF (Base.levB k r) 0 →
      Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r = -Y → ∀ m ∈ genSub E V,
      l (Λ Y m) = (Complex.I * ((EvaluationEquivalence.LF z c Y).re : ℂ)) • l m := fun Y h1 h2 m hm => by
    obtain ⟨hY, hf⟩ := EvaluationEquivalence.lieN_facts c hg₀ hT h1 h2
    refine (hder Y hY m hm).unique ?_
    have h3 : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * (Complex.I * ((EvaluationEquivalence.LF z c Y).re : ℂ))))
        (Complex.I * ((EvaluationEquivalence.LF z c Y).re : ℂ)) 0 := by
      simpa using (Complex.ofRealCLM.hasDerivAt.mul_const
        (Complex.I * ((EvaluationEquivalence.LF z c Y).re : ℂ)) (x := (0 : ℝ))).cexp
    refine (h3.smul_const (l m)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    have h4 := perEquiv k r u z c Vp π μW μN P hB (coefX σ x₀ ((w : D) : H) (m : H)) ξ g 1 h1W _ (hf t).1
    rw [Matrix.one_mul, (hf t).2, hπ.1.1] at h4
    exact h4
  have hW : ∀ A : Matrix (Fin k) (Fin k) ℂ, Aᴴ = -A → ∀ m ∈ genSub E V,
      l (Λ (EvaluationEquivalence.emb0 k r A) m) = dρ A (l m) := fun A hA m hm => by
    refine (hder _ (EvaluationEquivalence.block_embedding_skew_hermitian hA) m hm).unique ?_
    refine (hdρ A hA (l m)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    have hu : NormedSpace.exp ((t : ℂ) • A) ∈ Matrix.unitaryGroup (Fin k) ℂ := by
      rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose,
        conjTranspose_smul, hA, Complex.star_def, Complex.conj_ofReal, smul_neg,
        ← Matrix.exp_add_of_commute _ _ (Commute.refl ((t : ℂ) • A)).neg_left, neg_add_cancel, NormedSpace.exp_zero]
    have h4 := perEquiv k r u z c Vp π μW μN P hB (coefX σ x₀ ((w : D) : H) (m : H)) ξ g _
      (EvaluationEquivalence.frame_mem_UW hg₀ hT hu) 1 h1N
    have h5 : Formalism.MainNotions.S.psiGen k r z c (1 : Mat k r) = 1 := by
      have h6 := Mult1.S0.A.psiGen_mul hB.1 c h1N h1N
      have h7 : Formalism.MainNotions.S.psiGen k r z c (1 : Mat k r) ≠ 0 := Complex.exp_ne_zero _
      rw [Matrix.one_mul] at h6
      exact (mul_right_eq_self₀.mp h6.symm).resolve_right h7
    rw [Matrix.mul_one, h5, one_smul] at h4
    simp only []
    rw [← map_smul, EvaluationEquivalence.exp_embed]
    exact h4
  refine ⟨g₀, fun i j => dρ (Matrix.single i j 1),
    fun a b => EvaluationEquivalence.psiC z c (Matrix.single (capIdx k r a) (capIdx k r b) 1), hg₀,
    fun a b hab m hm => ?_, fun a b _ hs => EvaluationEquivalence.psiC_zero z c hs, fun _ => ?_, fun i j m hm => ?_, hcap⟩
  · set Z : Mat k r := Matrix.single (capIdx k r a) (capIdx k r b) 1 with hZ
    have hZ1 : Z ∈ Base.N.levF (Base.levB k r) 0 := fun i j hij => by
      rw [hZ, Matrix.single_apply, if_neg]
      rintro ⟨rfl, rfl⟩
      have h8 : Base.levB k r (capIdx k r a) < Base.levB k r (capIdx k r b) := hab
      omega
    have hZ2 : Formalism.QuantumDeterminants.Hpk k r * Zᴴ * Formalism.QuantumDeterminants.Hpk k r ∈ Base.N.levF (Base.levB k r) 0 :=
      EvaluationEquivalence.st_mem hZ1
    obtain ⟨p1, p2, p3⟩ := EvaluationEquivalence.parts Z
    have m1 : ∀ s t : ℂ, s • (Z + t • (Formalism.QuantumDeterminants.Hpk k r * Zᴴ * Formalism.QuantumDeterminants.Hpk k r)) ∈
        Base.N.levF (Base.levB k r) 0 := fun s t i j hij => by
      simp only [Matrix.smul_apply, Matrix.add_apply, hZ1 i j hij, hZ2 i j hij, smul_zero, add_zero]
    show l (frameE _ E _ _ m) = _ • l m
    rw [hfr, ← hZ]
    conv_lhs => rw [p3]
    rw [hΛ _ _ m hm, hN _ (m1 _ _) p1 m hm, hN _ (m1 _ _) p2 m hm, smul_smul, ← add_smul,
      EvaluationEquivalence.psiC_parts]
    rfl
  · refine Finset.prod_ne_zero_iff.mpr fun a _ => Finset.prod_ne_zero_iff.mpr fun b _ => ?_
    split_ifs with hs
    · exact EvaluationEquivalence.psiC_ne hB.2.2.1 hT hs
    · exact one_ne_zero
  · set A : Matrix (Fin k) (Fin k) ℂ := Matrix.single i j 1 with hA
    have e1 : A = (1 / 2 : ℂ) • (A - Aᴴ) + Complex.I • ((-Complex.I / 2) • (A + Aᴴ)) := by
      ext a b
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
      linear_combination (A a b + Aᴴ a b) / 2 * Complex.I_mul_I
    have s1 : ((1 / 2 : ℂ) • (A - Aᴴ))ᴴ = -((1 / 2 : ℂ) • (A - Aᴴ)) := by
      rw [conjTranspose_smul, conjTranspose_sub, conjTranspose_conjTranspose, ← smul_neg, neg_sub]; simp
    have s2 : ((-Complex.I / 2) • (A + Aᴴ))ᴴ = -((-Complex.I / 2) • (A + Aᴴ)) := by
      rw [conjTranspose_smul, conjTranspose_add, conjTranspose_conjTranspose, add_comm, ← neg_smul]
      congr 1; simp; ring
    show l (frameE _ E _ _ m) = dρ A (l m)
    have e2 : (Matrix.single (capIdx k r (Capelli.wIdx k r i)) (capIdx k r (Capelli.wIdx k r j)) 1 : Mat k r) =
        EvaluationEquivalence.emb0 k r A := (EvaluationEquivalence.block_embedding_single i j).symm
    rw [hfr, e2]
    conv_lhs => rw [e1, map_add, map_smul _ Complex.I]
    rw [hΛ _ _ m hm, hW _ s1 m hm, hW _ s2 m hm]
    conv_rhs => rw [e1, map_add, map_smul _ Complex.I]
    rfl

end ReciprocityTheory.ChartRestriction.DS.Lap
