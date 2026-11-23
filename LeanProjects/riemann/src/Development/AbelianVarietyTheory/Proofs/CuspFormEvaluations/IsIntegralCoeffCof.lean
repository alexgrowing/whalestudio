import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.LetAct
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FrameLetterGLActionRepresentationKeepsHarmonic
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.InPsiOrConjugateUnit
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.MemOfForallLocP
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FrameReadingLeadingMinorProductExtremalStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LeadingMinorProductHarmonicGenerates
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HodgeWeightDominanceConditionStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.MemNabStdOfDetMulIntegral

open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.FrameRead
open scoped Classical

noncomputable section

namespace GlobalTheory.FrameRead.CoefMap

def harmSub {T : Type} (r : T → ℕ) (n : ℕ) (k : Type) [Field k] (cc : T → T) (isX : T → Prop) (a : T → ℕ → ℕ) :
    Submodule k (MvPolynomial (Letter T r n) k) where
  carrier := HHa r n k cc isX a
  add_mem' := by
    rintro P Q ⟨h1, h2, h3⟩ ⟨h1', h2', h3'⟩
    refine ⟨add_mem h1 h1', fun σ i i' h t => by rw [map_add, h2 σ i i' h t, h2' σ i i' h t], fun m hm => ?_⟩
    rcases Finset.mem_union.1 (support_add hm) with h | h
    · exact h3 m h
    · exact h3' m h
  zero_mem' := ⟨zero_mem _, fun σ i i' _ t => map_zero _, fun m hm => by simp at hm⟩
  smul_mem' := by
    rintro x P ⟨h1, h2, h3⟩
    exact ⟨Submodule.smul_mem _ x h1, fun σ i i' h t => by rw [map_smul, h2 σ i i' h t],
      fun m hm => h3 m (support_smul hm)⟩

theorem det_gen_ne_zero (K : Type) [Field K] {Ix : Type} (n : ℕ) (t : Ix) : (gen K n t).det ≠ 0 := by
  intro h
  have h1 := congrArg (eval (fun v : Ix × Fin n × Fin n => if v.2.1 = v.2.2 then (1 : K) else 0)) h
  rw [RingHom.map_det, map_zero] at h1
  have h2 : (eval (fun v : Ix × Fin n × Fin n => if v.2.1 = v.2.2 then (1 : K) else 0)).mapMatrix (gen K n t) = 1 := by
    ext p q
    simp [gen, Matrix.one_apply]
  rw [h2, Matrix.det_one] at h1
  exact one_ne_zero h1

theorem map_gen {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {Ix : Type} (n : ℕ) (t : Ix) :
    (MvPolynomial.map f).mapMatrix (gen R n t) = gen S n t := by
  ext p q : 2
  simp [gen]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H) {n : ℕ}
  {Ix : Type} [Fintype Ix] (pl : Ix → (E →+* ℂ))

theorem detFac_ne_zero (K : Type) [Field K] (a : (E →+* ℂ) × ℕ → ℕ) (s : Ix → ℤ) (lam : Ix → DomWeight n) :
    detFac Dw pl K a s lam ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun t _ => pow_ne_zero _ (det_gen_ne_zero K n t)

theorem map_cof {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (Q : MvPolynomial (LtN Dw n) R) :
    MvPolynomial.map f (cof Dw pl R n Q) = cof Dw pl S n (MvPolynomial.map f Q) := by
  induction Q using MvPolynomial.induction_on with
  | C x => simp [algHom_C]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p ℓ hp =>
    simp only [map_mul, hp, map_X]
    congr 1
    simp only [cof, aeval_X]
    split_ifs with h1 h2 h3
    · simp [gen]
    · rw [← map_gen f, ← RingHom.map_adjugate]
      rfl
    · simp
    · simp

theorem isIntegral_coeff_cof {K : Type} [Field K] (P : MvPolynomial (LtN Dw n) K)
    (hP : ∀ m, P.coeff m ∈ (integralClosure ℤ K).toSubring) (m) : IsIntegral ℤ ((cof Dw pl K n P).coeff m) := by
  obtain ⟨Q, rfl⟩ : ∃ Q, MvPolynomial.map (integralClosure ℤ K).toSubring.subtype Q = P := by
    refine ⟨∑ m ∈ P.support, monomial m ⟨P.coeff m, hP m⟩, ?_⟩
    simp only [map_sum, map_monomial, Subring.subtype_apply]
    exact P.as_sum.symm
  rw [← map_cof, coeff_map]
  exact ((cof Dw pl _ n Q).coeff m).2

set_option maxHeartbeats 1000000 in

theorem exists_ioLFRec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (n : ℕ) (Ix : Type) [Fintype Ix] (pl : Ix → (E →+* ℂ)), IsEnum H pl → Dw.p + Dw.q ≤ n → ∀ (l : Level H) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (s : Ix → ℤ) (lam : Ix → DomWeight n), (∀ τ, Antitone fun i => a (τ, i)) → WtIs Dw pl a s lam → ∃ (io : VVc c lam →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) (hw : VVc c lam), IoLFRec c (fun t => embF c (pl t)) lam a io hw := by
  intro E _ _ _ H Dw n Ix _ pl he hn l c a s lam ha hwt
  obtain ⟨ε, hε⟩ := GlobalTheory.T.frameReading_leadingMinorProduct_extremal E H Dw n Ix pl he hn l c a s lam ha hwt
  obtain ⟨him, hex, heq⟩ := GlobalTheory.T.hodge_weight_dominance_condition E H Dw n Ix pl he hn l c a s lam ha hwt
  obtain ⟨hpG, -, -⟩ := pG_mem_ne_zero_generates E H Dw n Ix pl he hn l c a ha
  obtain ⟨-, -, hstab⟩ := letAct_mul_one_mem_HHa E H Dw n Ix pl he hn c.F a
  obtain ⟨hs1, hs2, hs3⟩ := GlobalTheory.StdNab.nabAtr_stdLat E c.F Ix n (fun t => embF c (pl t)) lam
  have hD := detFac_ne_zero Dw pl c.F a s lam
  let S := harmSub Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))
  have hS : ∀ P, P ∈ S ↔ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) :=
    fun _ => Iff.rfl
  set e : c.F := ((ε : ℤ) : c.F) with he'
  have hee : e * e = 1 := by
    rw [he', ← Int.cast_mul, Int.units_coe_mul_self, Int.cast_one]
  have heI : IsIntegral ℤ e := isIntegral_intCast _
  set D := detFac Dw pl c.F a s lam with hDdef
  have hex' : ∀ F : VVc c lam, ∃! P, P ∈ S ∧ cof Dw pl c.F n P = e • (D * F.1) := fun F => by
    have := hex (e • F.1) (Submodule.smul_mem _ _ F.2)
    rwa [mul_smul_comm] at this
  choose φ hφ huniq using hex'
  have hu : ∀ (F : VVc c lam) P, P ∈ S → cof Dw pl c.F n P = e • (D * F.1) → φ F = P :=
    fun F P h1 h2 => (huniq F P ⟨h1, h2⟩).symm
  let io : VVc c lam →ₗ[c.F] MvPolynomial (LtN Dw n) c.F :=
    { toFun := φ
      map_add' := fun F G => hu _ _ (add_mem (hφ F).1 (hφ G).1) (by
        rw [map_add, (hφ F).2, (hφ G).2, Submodule.coe_add, mul_add, smul_add])
      map_smul' := fun x F => hu _ _ (Submodule.smul_mem _ _ (hφ F).1) (by
        rw [map_smul, (hφ F).2, Submodule.coe_smul, mul_smul_comm, smul_comm]; rfl) }
  have hio : ∀ F, io F = φ F := fun _ => rfl
  have hsurj : ∀ P ∈ S, ∃ F : VVc c lam, io F = P := fun P hP => by
    obtain ⟨F, hF, h⟩ := him P hP
    refine ⟨⟨e • F, Submodule.smul_mem _ _ hF⟩, hu _ _ hP ?_⟩
    rw [h, mul_smul_comm, smul_smul, hee, one_smul]
  have hwm : (ten fun t => extremal c.F n (lam t)) ∈ VV c.F lam := by
    obtain ⟨F, hF, h⟩ := him _ hpG.1
    rw [hε, ← mul_smul_comm] at h
    have h' := mul_left_cancel₀ hD h
    have : (ten fun t => extremal c.F n (lam t)) = e • F := by rw [← h', smul_smul, hee, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ hF
  refine ⟨io, ⟨_, hwm⟩, rfl, fun ga => if h : IsUnit ga.det then
      ∏ t, (((invTrK (embGL (fun t => embF c (pl t)) (Matrix.nonsingInvUnit ga h))) t : GL (Fin n) c.F) :
        Matrix (Fin n) (Fin n) c.F).det ^ (s t) else 0, hn, ?_, ?_, ?_, (hs1 _).2 hs2,
      fun x hx => hs3 x ((hs1 _).1 hx), hu _ _ hpG.1 hε, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro F hF
    have h := (hφ F).2
    rw [← hio, hF, map_zero] at h
    have h' := congrArg (fun x => e • x) h
    simp only [smul_zero, smul_smul, hee, one_smul] at h'
    exact Subtype.ext ((mul_eq_zero.1 h'.symm).resolve_left hD)
  · have : Submodule.span c.F (HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) = S :=
      Submodule.span_eq S
    rw [this]
    refine le_antisymm ?_ hsurj
    rintro _ ⟨F, rfl⟩
    exact (hφ F).1
  · intro ga hga F
    have h : IsUnit ga.det := by
      have := congrArg Matrix.det hga
      rw [Matrix.det_mul, Matrix.det_one] at this
      exact IsUnit.of_mul_eq_one_right _ this
    rw [gaStar_conj_eq_letAct E H Dw n Ix pl he hn l c ga h hga]
    simp only [dif_pos h, rhoM]
    set g := invTrK (embGL (fun t => embF c (pl t)) (Matrix.nonsingInvUnit ga h)) with hg
    refine hu _ _ (Submodule.smul_mem _ _ (hstab g _ (hφ F).1)) ?_
    have h1 := heq g _ (hφ F).1 (e • F.1) (Submodule.smul_mem _ _ F.2) (by rw [(hφ F).2, mul_smul_comm])
    rw [map_smul, hio, h1, smul_smul, ← Finset.prod_mul_distrib, map_smul, mul_smul_comm]
    have h2 : ∏ t, (g t : Matrix (Fin n) (Fin n) c.F).det ^ (s t) * (g t : Matrix (Fin n) (Fin n) c.F).det ^ (-(s t)) = 1 :=
      Finset.prod_eq_one fun t _ => by
        rw [← zpow_add₀ (Matrix.isUnits_det_units (g t)).ne_zero, add_neg_cancel, zpow_zero]
    rw [h2, one_smul]
    rfl
  · intro P hP
    obtain ⟨F, rfl⟩ := hsurj P hP.1
    refine ⟨F, (hs1 F).2 (GlobalTheory.DetSat.mem_nabStd_of_det_mul_integral c.F Ix n lam
      (fun t => ((degC Dw pl a t : ℤ) + (lam t).detShift - s t).toNat) F.1 F.2 fun m => ?_), rfl⟩
    have h : e • cof Dw pl c.F n (φ F) = D * F.1 := by rw [(hφ F).2, smul_smul, hee, one_smul]
    change IsIntegral ℤ ((D * F.1).coeff m)
    rw [← h, coeff_smul, smul_eq_mul]
    exact heI.mul (isIntegral_coeff_cof Dw pl (φ F) hP.2 m)

end GlobalTheory.FrameRead.CoefMap
