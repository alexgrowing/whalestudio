import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DecayNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHermitianOfSkew
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceCharacterAnnihilatorCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPrimeAdditiveCharacterUnramified
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNatMulIntegralMatricesSubsetOpenAddSubgrou

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ConeFinVanish

open scoped nonZeroDivisors

theorem rho_comm {R : Type} [CommRing R] [Invertible (2 : R)] {V : Type} [AddCommGroup V] [Module R V]
    {Bf : V → V → R} {κ : Type} [Fintype κ] (dc : Darboux Bf κ) (ψ : AddChar R ℂ) (a b : V) (φ : (κ → R) → ℂ) :
    dc.rho ψ a (dc.rho ψ b φ) = ψ (Bf a b) • dc.rho ψ b (dc.rho ψ a φ) := by
  funext x
  simp only [Darboux.rho, schr, Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← AddChar.map_add_eq_mul, dc.form]
  rw [add_right_comm x]
  congr 2
  simp only [add_dotProduct]
  ring

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem eventually_fixed {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] {κ : Type} [Fintype κ] {χ : R → ℂ} (hχ : IsLocallyConstant χ) (h0 : χ 0 = 1)
    {g : (κ → R) → ℂ} (hg : g ∈ SB (κ → R)) (s d : κ → R) (c : R) :
    ∀ᶠ α in 𝓝 (0 : R), ∀ z, χ (α * (z ⬝ᵥ d) + α * α * c) * g (z + α • s) = g z := by
  have key : ∀ (P : R × (κ → R) → ℂ × ℂ), IsLocallyConstant P →
      (∀ z, (P (0, z)).1 = (P (0, z)).2) →
      ∀ᶠ α in 𝓝 (0 : R), ∀ z ∈ tsupport g, (P (α, z)).1 = (P (α, z)).2 := by
    intro P hP hz
    refine IsCompact.eventually_forall_of_forall_eventually hg.2
      (P := fun α z => (P (α, z)).1 = (P (α, z)).2) fun z _ => ?_
    filter_upwards [hP.eventually_eq (0, z)] with p hp
    change (P p).1 = (P p).2
    rw [hp, hz]
  have c1 : Continuous fun p : R × (κ → R) => p.1 * (p.2 ⬝ᵥ d) + p.1 * p.1 * c := by
    have : Continuous fun p : R × (κ → R) => p.2 ⬝ᵥ d := continuous_snd.dotProduct continuous_const
    fun_prop
  have c2 : Continuous fun p : R × (κ → R) => p.2 + p.1 • s := by fun_prop
  have c3 : Continuous fun p : R × (κ → R) => p.2 - p.1 • s := by fun_prop
  have l0 := hg.1.comp_continuous (continuous_snd (X := R) (Y := κ → R))
  have e1 := key _ (((hχ.comp_continuous c1).mul (hg.1.comp_continuous c2)).prodMk l0)
    (fun z => by simp [h0])
  have e2 := key _ ((hg.1.comp_continuous c3).prodMk l0) (fun z => by simp)
  filter_upwards [e1, e2] with α h1 h2 z
  by_cases hz : z ∈ tsupport g
  · exact h1 z hz
  · have hz0 := image_eq_zero_of_notMem_tsupport hz
    by_cases hz' : z + α • s ∈ tsupport g
    · have := h2 _ hz'
      simp only [Function.comp_apply, add_sub_cancel_right] at this
      rw [← this, hz0, mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport hz', hz0, mul_zero]

theorem eventually_schr_pureA {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ} (hψ : Continuous ψ)
    {g : (κ → Af F) → ℂ} (hg : g ∈ SB (κ → Af F)) (w : (κ → AF F) × (κ → AF F)) :
    ∀ᶠ α in 𝓝 (0 : Af F), ∀ f : (κ → mixedEmbedding.mixedSpace F) → ℂ,
      schr ψ (pairA F 0 α • w) (pureA F f g) = pureA F f g := by
  filter_upwards [eventually_fixed (GlobalTheory.HeisSchA.finChar_isLocallyConstant ψ hψ) (AddChar.map_zero_eq_one _) hg
    (fun i => GlobalTheory.HeisSchA.p2 (w.1 i)) (fun i => GlobalTheory.HeisSchA.p2 (w.2 i))
    (GlobalTheory.HeisSchA.p2 (⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)))] with α hα f
  funext x
  have h := hα fun i => GlobalTheory.HeisSchA.p2 (x i)
  have e1 : x ⬝ᵥ (pairA F 0 α • w).2 + ⅟(2 : AF F) * ((pairA F 0 α • w).1 ⬝ᵥ (pairA F 0 α • w).2) =
      pairA F 0 α * (x ⬝ᵥ w.2 + pairA F 0 α * (⅟(2 : AF F) * (w.1 ⬝ᵥ w.2))) := by
    simp only [Prod.smul_fst, Prod.smul_snd, dotProduct_smul, smul_dotProduct, smul_eq_mul]
    ring
  have e2 : pairA F 0 α * (x ⬝ᵥ w.2 + pairA F 0 α * (⅟(2 : AF F) * (w.1 ⬝ᵥ w.2))) =
      GlobalTheory.HeisSchA.mk 0 (α * ((fun i => GlobalTheory.HeisSchA.p2 (x i)) ⬝ᵥ fun i => GlobalTheory.HeisSchA.p2 (w.2 i)) +
        α * α * GlobalTheory.HeisSchA.p2 (⅟(2 : AF F) * (w.1 ⬝ᵥ w.2))) := by
    refine Prod.ext (zero_mul _) ?_
    change GlobalTheory.HeisSchA.p2 (_ * _) = _ + _
    rw [map_mul, map_add, map_mul, RingHom.map_dotProduct]
    change α * (_ + α * _) = _
    rw [mul_add, mul_assoc]
    rfl
  have e3 : (fun i => ((x + (pairA F 0 α • w).1) i).1) = fun i => (x i).1 :=
    funext fun i => show (x i).1 + 0 * (w.1 i).1 = (x i).1 by rw [zero_mul, add_zero]
  have e3' : ∀ i, ((x + (pairA F 0 α • w).1) i).1 = (x i).1 := congrFun e3
  unfold schr pureA
  rw [e1, e2, ← GlobalTheory.HeisSchA.finChar_apply]
  simp only [e3']
  rw [mul_left_comm]
  congr 1

theorem exists_den {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) : ∃ D : ℕ, 0 < D ∧ ∀ y : Af F,
    (∀ α : Af F, (∀ v, α v ∈ v.adicCompletionIntegers F) → ψ (pairA F 0 (α * y)) = 1) →
      ∀ v : Pl F, (D : Fv F v) * y v ∈ v.adicCompletionIntegers F := by
  obtain ⟨a, ha, H⟩ := (GlobalTheory.StdDual.codiff F).isFractional
  have ha0 : Ideal.span {a} ≠ ⊥ := by simpa using nonZeroDivisors.ne_zero ha
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {a}))
  refine ⟨Ideal.absNorm (Ideal.span {a}), Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.1 ha0), fun y hy v => ?_⟩
  have hm := (GlobalTheory.SplitUnram.mem_adelicIdeal_codiff_iff hψ.1 (GlobalTheory.LatVacArith.psi_fin_rat hψ) y).2 hy v
  generalize y v = t at hm
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨x, hx, rfl⟩ := hx
    obtain ⟨o, ho⟩ := H x hx
    have e : ((Ideal.absNorm (Ideal.span {a}) : ℕ) : F) * x = algebraMap (𝓞 F) F (c * o) := by
      rw [map_mul, ho, Algebra.smul_def, ← mul_assoc, ← map_mul, hc, map_natCast]
    rw [← map_natCast (algebraMap F (v.adicCompletion F)), ← map_mul, e,
      HeightOneSpectrum.mem_adicCompletionIntegers, GlobalTheory.Idele.valued_algebraMap]
    exact v.valuation_le_one _
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | smul r x _ hx =>
    change _ * ((r : v.adicCompletion F) * x) ∈ _
    rw [mul_left_comm]
    exact mul_mem r.2 hx

omit [NumberField E] in

theorem hTens_vecMulVec {n d : ℕ} (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E)
    (x x' : Fin n → E) (y y' : Fin d → E) (l t : AE F E) :
    hTens (cA σ) (incM F JX) (incM F JW) (l • Matrix.vecMulVec (incV F x) (incV F y))
      (t • Matrix.vecMulVec (incV F x') (incV F y')) =
      l * cA σ t * inclR (F := F) (AF F) (form σ JX x x') * inclR (F := F) (AF F) (form σ JW y y') := by
  have hc : ∀ e : E, cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := fun e => rfl
  simp only [hTens, form, dotProduct, Matrix.mulVec, map_sum, map_mul, Matrix.smul_apply, Matrix.vecMulVec_apply,
    smul_eq_mul, incV, incM, Matrix.map_apply, hc, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext k; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring

theorem symp_shiftA (hcm : IsCMExt F E σ) {n d n₁ d₁ : ℕ} {JX : Matrix (Fin n) (Fin n) E}
    {JW : Matrix (Fin d) (Fin d) E} (hW : ∀ i j, σ (JW j i) = -JW i j) (H : Plane E n n₁) (H' : Plane E d d₁)
    (h : form σ JX H.x H.y = 1) (h' : form σ JW H'.x H'.y = 1) (l : (AE F E)ˣ) (t : AE F E) :
    symp (R := AF F) (cA σ) (-1) (incM F JX) (incM F JW) (shiftA H H' l)
      (t • Matrix.vecMulVec (incV F H.y) (incV F H'.x)) = Algebra.trace (AF F) (AE F E) (l.1 * cA σ t) := by
  have h2 : form σ JW H'.y H'.x = -1 := by
    have := GlobalTheory.ThK.HypSplit.form_skew hcm hW H'.y H'.x
    rw [h', map_one] at this
    exact (neg_eq_iff_eq_neg.1 this.symm)
  rw [symp, shiftA, hTens_vecMulVec, h, h2, map_one, map_neg, map_one]
  congr 1
  ring

theorem exists_trace_eq_coord (hcm : IsCMExt F E σ) (i : Fin (Module.finrank F E)) : ∃ c : AE F E,
    ∀ (a : AF F) (l : AE F E), Algebra.trace (AF F) (AE F E) (l * cA σ (a • c)) = a * GlobalTheory.IdeleDecay.coord F E l i := by
  classical
  refine ⟨inclR (F := F) (AF F) (σ ((Module.finBasis F E).traceDual i)), fun a l => ?_⟩
  have hc : ∀ e : E, cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := fun e => rfl
  rw [map_smul, hc, GlobalTheory.ThK.HypSplit.invol hcm, mul_smul_comm, map_smul, smul_eq_mul, mul_comm l]
  exact congrArg (a * ·) (GlobalTheory.TraceAnnCompact.trace_traceDual_mul (AF F) (Module.finBasis F E) i l)

theorem ev_shiftA_pure_eq_zero : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ g ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → FiniteAdeleRing (𝓞 F) F),
      ∃ m : ℕ, 0 < m ∧ ∀ l : (AE F E)ˣ,
        ¬ (∀ i v, evFin F v ((m : AF F) * GlobalTheory.IdeleDecay.coord F E l.1 i) ∈ v.adicCompletionIntegers F) →
        ∀ (f : SInf F (Fin (b + 2) × Fin (b + 2 + a'))) (y : Fin b × Fin (b + a') → AF F),
          e (G.M.co.rho B.ψ (shiftA H H' l) (pureA F f g)) y = 0 := by
  intro _ F E _ _ _ _ _ σ B b a' G G₁ H H' hC e he X om om' om₁ om₁' hT _ g hg
  have hψ := hT.base.std
  have hcm := hT.base.cm
  choose c hc using exists_trace_eq_coord (σ := σ) hcm
  let u : Fin (Module.finrank F E) → Matrix (Fin (b + 2)) (Fin (b + 2 + a')) (AE F E) :=
    fun i => c i • Matrix.vecMulVec (incV F H.y) (incV F H'.x)
  have hev := eventually_all.2 fun i => eventually_schr_pureA hψ.1 hg (G.M.co.e (u i))
  obtain ⟨N, hN, hNm⟩ := GlobalTheory.OpenSubAdele.exists_nat_mul_mem_of_mem_nhds hev
  obtain ⟨D, hD, hDm⟩ := exists_den hψ
  refine ⟨D * N, Nat.mul_pos hD hN, fun l hl f y => ?_⟩
  by_contra hne
  refine hl fun i v => ?_
  have key := hDm ((N : Af F) * GlobalTheory.HeisSchA.p2 (GlobalTheory.IdeleDecay.coord F E l.1 i)) (fun α hα => ?_) v
  · rw [Nat.cast_mul, mul_assoc, map_mul, map_natCast]
    rw [← map_natCast (GlobalTheory.HeisSchA.p2 (F := F)), ← map_mul] at key
    exact key
  have hfix := hNm α (Subring.mem_iInf.2 hα) i f
  set a : AF F := pairA F 0 ((N : Af F) * α) with ha
  have hu : a • u i = (a • c i) • Matrix.vecMulVec (incV F H.y) (incV F H'.x) := (smul_assoc _ _ _).symm
  have hfix' : G.M.co.rho B.ψ (a • u i) (pureA F f g) = pureA F f g := by
    rw [Darboux.rho, map_smul]
    exact hfix
  have hI : a • u i ∈ isoA H H' := Or.inl ⟨(a • c i) • incV F H.y, by rw [hu, Matrix.smul_vecMulVec]⟩
  have hΦ : pureA F f g ∈ schA F _ := Submodule.subset_span ⟨f, g, hg, rfl⟩
  have h1 := rho_comm G.M.co B.ψ (shiftA H H' l) (a • u i) (pureA F f g)
  rw [hfix'] at h1
  have h2 := congrFun (congrArg e h1) y
  rw [map_smul, he.inv _ hI _ (GlobalTheory.HeisSchA.rho_mem_schA G.M B.ψ hψ _ _ hΦ), Pi.smul_apply, smul_eq_mul, hu,
    symp_shiftA hcm hT.geo.hW.skew H H' hC.hH.xy hC.hH'.xy, hc] at h2
  have h3 : B.ψ (a * GlobalTheory.IdeleDecay.coord F E l.1 i) = 1 :=
    mul_right_cancel₀ hne (h2.symm.trans (one_mul _).symm)
  rw [← h3]
  congr 1
  refine Prod.ext (zero_mul _).symm ?_
  change α * ((N : Af F) * _) = (N : Af F) * α * _
  rw [mul_left_comm, mul_assoc]
  rfl

end GlobalTheory.ConeFinVanish
