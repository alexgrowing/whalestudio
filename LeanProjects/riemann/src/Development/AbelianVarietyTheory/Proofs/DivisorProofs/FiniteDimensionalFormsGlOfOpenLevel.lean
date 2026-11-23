import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkEquivInl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransposeMulIncl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalDomainMeasureFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFundamentalDomainUnipotent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteDimensionalSpaceAutomorphicSmoothing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CommuteCapOfCommuteEop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CapCommuteRtInfGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermAutomorphicFormIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermIntegralLeftInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermModerateGrowthStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraCapelliUniformDiagonalBlocksStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalSlowlyIncreasingKilledCapelliPoStatement

noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.LeviGA GlobalTheory.AutGrowth Polynomial
open Formalism.REAL (qdet)

namespace GlobalTheory.GLSlice

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a b : ℕ}

theorem qdet_eq_cap (τ : E →+* ℂ) (u : ℂ) : qdet (Eop (a := a) τ) u = cap τ (u - ((a : ℂ) - 1) / 2) := by
  rw [cap, sub_add_cancel]

theorem commute_aeval_rt (τ : E →+* ℂ) (u : ℂ) (P : ℂ[X]) (h : GA E a) :
    Commute (aeval (qdet (Eop (a := a) τ) u) P) (rt E a h) := by
  have h1 : Commute (qdet (Eop (a := a) τ) u) (rt E a h) := by
    rw [qdet_eq_cap, ← infGL_mul_finGL h, map_mul]
    exact (GlobalTheory.CapAdInv.cap_commute_rt_infGL E a τ _ _).mul_right (commute_cap_finRep τ _ _)
  induction P using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact hp.add_left hq
  | monomial n c =>
    rw [aeval_monomial]
    exact (Algebra.commute_algebraMap_left _ _).mul_left (h1.pow_left n)

theorem isOpen_stab {L : Subgroup (GL (Fin a) (Af E))} (hL : IsOpen (L : Set (GL (Fin a) (Af E)))) {φ : Sm E a}
    (h : ∀ k ∈ L, finRep E a k φ = φ) : IsOpen {k | finRep E a k φ = φ} :=
  isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset (hL.mem_nhds L.one_mem) h)

theorem lie_left {φ : Sm E a} {n : GA E a} (h : ∀ g, φ.1 (n * g) = φ.1 g) (X : Lie E a) (g : GA E a) :
    (lie E a X φ).1 (n * g) = (lie E a X φ).1 g := by
  have e : chart φ.1 (n * g) = chart φ.1 g := by
    funext x; simp only [chart, mul_assoc, h]
  rw [lie_apply, lie_apply, lieD, lieD, e]

theorem span_props (L : Subgroup (GL (Fin a) (Af E))) (W : Submodule ℂ (Kinf E a → ℂ))
    {X : Set (Module.End ℂ (Sm E a) → ℂ)} (hX : X.Finite) (N : ℕ) :
    ∃ Q : (E →+* ℂ) → ℂ → ℂ[X], (∀ τ u, Q τ u ≠ 0) ∧ ∀ φ ∈ Submodule.span ℂ (GlobalTheory.HCF.formsGL E a L W X N),
      (∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g) ∧ (∀ k ∈ L, finRep E a k φ = φ) ∧ φ.1 ∈ growth E a ∧
        ∀ τ u, aeval (qdet (Eop (a := a) τ) u) (Q τ u) φ = 0 := by
  refine ⟨fun τ u => ∏ χ ∈ hX.toFinset, (Polynomial.X - C (χ (qdet (Eop τ) u))) ^ N,
    fun τ u => Finset.prod_ne_zero_iff.2 fun χ _ => pow_ne_zero _ (X_sub_C_ne_zero _), fun φ hφ => ?_⟩
  induction hφ using Submodule.span_induction with
  | mem φ hφ =>
    obtain ⟨h1, h2, -, χ, hχ, h3⟩ := hφ
    refine ⟨h1.left, h2, h1.growth, fun τ u => ?_⟩
    beta_reduce
    generalize hz : qdet (Eop (a := a) τ) u = z
    have hzZ : z ∈ Zalg E a := by
      rw [← hz, qdet_eq_cap]; exact Algebra.subset_adjoin ⟨τ, _, rfl⟩
    have key : ∀ n : ℕ, (List.replicate n z).foldr (fun z f => z f - χ z • f) φ =
        aeval z ((Polynomial.X - C (χ z)) ^ n) φ := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [List.replicate_succ, List.foldr_cons, ih, pow_succ', map_mul, map_sub, aeval_X, aeval_C]
        rfl
    have h4 := h3 (List.replicate N z) List.length_replicate fun y hy => (List.eq_of_mem_replicate hy) ▸ hzZ
    obtain ⟨R, hR⟩ := Finset.dvd_prod_of_mem (fun χ : Module.End ℂ (Sm E a) → ℂ => (Polynomial.X - C (χ z)) ^ N)
      (hX.mem_toFinset.2 hχ)
    rw [hR, mul_comm, map_mul, Module.End.mul_apply, ← key, h4, map_zero]
  | zero => exact ⟨fun _ _ => rfl, fun _ _ => map_zero _, zero_mem _, fun _ _ => map_zero _⟩
  | add x y _ _ hx hy =>
    exact ⟨fun γ g => congrArg₂ (· + ·) (hx.1 γ g) (hy.1 γ g), fun k hk => by rw [map_add, hx.2.1 k hk, hy.2.1 k hk],
      add_mem hx.2.2.1 hy.2.2.1, fun τ u => by rw [map_add, hx.2.2.2, hy.2.2.2, add_zero]⟩
  | smul c x _ hx =>
    exact ⟨fun γ g => congrArg (c * ·) (hx.1 γ g), fun k hk => by rw [map_smul, hx.2.1 k hk],
      Submodule.smul_mem _ c hx.2.2.1, fun τ u => by rw [map_smul, hx.2.2.2, smul_zero]⟩

theorem exists_constTerm {L : Subgroup (GL (Fin a) (Af E))} (hL : IsOpen (L : Set (GL (Fin a) (Af E)))) {r : ℕ}
    [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] {μ : Measure (BlockIx a r → Ad E)}
    {𝓕 : Set (BlockIx a r → Ad E)} (hμ : μ.IsAddHaarMeasure) (h𝓕 : IsAddFundamentalDomain (ratN E a r) 𝓕 μ)
    (h1 : μ 𝓕 = 1) (φ : Sm E a) (hl : ∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g) (hf : ∀ k ∈ L, finRep E a k φ = φ) :
    ∃ ψ : Sm E a, (∀ g, ψ.1 g = ∫ x in 𝓕, φ.1 (unip x * g) ∂μ) ∧
      ∀ τ u (P : ℂ[X]), aeval (qdet (Eop (a := a) τ) u) P φ = 0 → aeval (qdet (Eop (a := a) τ) u) P ψ = 0 := by
  let Γ : Submodule ℂ (Sm E a × Sm E a) :=
    { carrier := {x | (∀ γ g, x.1.1 (ratGL E a γ * g) = x.1.1 g) ∧ (∀ k ∈ L, finRep E a k x.1 = x.1) ∧
        ∀ g, x.2.1 g = ∫ y in 𝓕, x.1.1 (unip y * g) ∂μ}
      zero_mem' := ⟨fun _ _ => rfl, fun _ _ => map_zero _, fun _ => (integral_zero _ _).symm⟩
      add_mem' := fun {x y} hx hy => ⟨fun γ g => congrArg₂ (· + ·) (hx.1 γ g) (hy.1 γ g),
        fun k hk => (map_add _ _ _).trans (congrArg₂ (· + ·) (hx.2.1 k hk) (hy.2.1 k hk)), fun g =>
          (congrArg₂ (· + ·) (hx.2.2 g) (hy.2.2 g)).trans (integral_add
            (CuspidalL2GL.integrableOn_unip (ContAut.continuous_of_isOpen_stab E a _ (isOpen_stab hL hx.2.1)) hx.1 μ h𝓕 g)
            (CuspidalL2GL.integrableOn_unip (ContAut.continuous_of_isOpen_stab E a _ (isOpen_stab hL hy.2.1)) hy.1 μ h𝓕 g)).symm⟩
      smul_mem' := fun c x hx => ⟨fun γ g => congrArg (c * ·) (hx.1 γ g),
        fun k hk => (map_smul _ _ _).trans (congrArg (c • ·) (hx.2.1 k hk)), fun g =>
          (congrArg (c * ·) (hx.2.2 g)).trans (integral_const_mul c _).symm⟩ }
  have hlie : ∀ X, ∀ x ∈ Γ, (lie E a X x.1, lie E a X x.2) ∈ Γ := fun X x hx => by
    refine ⟨fun γ g => lie_left (hx.1 γ) X g, fun k hk => ?_, fun g => ?_⟩
    · exact (LinearMap.congr_fun (lie_rt_fin X k) x.1).symm.trans (congrArg (lie E a X) (hx.2.1 k hk))
    · change lieD X x.2.1 g = _
      rw [funext hx.2.2]
      exact (GlobalTheory.T.constant_term_automorphic_form_integral E a r μ 𝓕 hμ h𝓕 h1 x.1 hx.1 (isOpen_stab hL hx.2.1)).2 X g
  refine ⟨⟨_, (GlobalTheory.T.constant_term_automorphic_form_integral E a r μ 𝓕 hμ h𝓕 h1 φ hl (isOpen_stab hL hf)).1⟩, fun _ => rfl, fun τ u P hP => ?_⟩
  have h := rel_aeval_qdet Γ (Eop τ) (Eop τ)
    (fun i j x hx => Γ.smul_mem (1 / 2 : ℂ) (Γ.sub_mem (hlie _ x hx) (Γ.smul_mem Complex.I (hlie _ x hx)))) u P
    (φ, ⟨_, (GlobalTheory.T.constant_term_automorphic_form_integral E a r μ 𝓕 hμ h𝓕 h1 φ hl (isOpen_stab hL hf)).1⟩) ⟨hl, hf, fun _ => rfl⟩
  refine Subtype.ext (funext fun g => (h.2.2 g).trans ?_)
  simp only [hP]
  exact integral_zero _ _

theorem infGL_unip {r : ℕ} (x : BlockIx a r → Cinf E) : infGL E a (unip x) = unip fun p => sInf E (x p) := by
  ext i j
  change (1 : Matrix (Fin a) (Fin a) (Ad E)) i j - sInf E ((1 : Matrix (Fin a) (Fin a) (Cinf E)) i j) +
    sInf E ((1 : Matrix (Fin a) (Fin a) (Cinf E)) i j + nilM x i j) =
    (1 : Matrix (Fin a) (Fin a) (Ad E)) i j + nilM (fun p => sInf E (x p)) i j
  rw [map_add, ← add_assoc, sub_add_cancel]
  simp only [nilM, Matrix.of_apply]
  split_ifs <;> simp

theorem lieS_upper {r : ℕ} (hr : r ≤ a) {ψ : Sm E a} (h : ∀ (y : BlockIx a r → Ad E) g, ψ.1 (unip y * g) = ψ.1 g)
    {i j : Fin a} (hi : (i : ℕ) < r) (hj : r ≤ (j : ℕ)) (z : Cinf E) (p : GA E r × GA E (a - r)) :
    (lieS E a i j z ψ).1 (blkGL hr p) = 0 := by
  classical
  let x : BlockIx a r → Cinf E := Pi.single ⟨(i, j), hi, hj⟩ z
  have e : ∀ t : ℝ, toL (unip (t • x)).val = oneL E a + t • toL (Matrix.single i j z) := fun t => by
    ext i' j' : 2
    change (1 : Matrix (Fin a) (Fin a) (Cinf E)) i' j' + nilM (t • x) i' j' =
      (1 : Matrix (Fin a) (Fin a) (Cinf E)) i' j' + t • Matrix.single i j z i' j'
    congr 1
    simp only [nilM, Matrix.of_apply, Matrix.single_apply, x, Pi.smul_apply, Pi.single_apply, Subtype.mk.injEq,
      Prod.mk.injEq]
    by_cases hh : i = i' ∧ j = j'
    · obtain ⟨rfl, rfl⟩ := hh
      simp [hi, hj]
    · rw [if_neg hh, smul_zero]
      split_ifs with h1 h2
      · exact absurd ⟨h2.1.symm, h2.2.symm⟩ hh
      · simp
      · rfl
  have hd := hasDerivAt_curve ψ (blkGL hr p) (fun t => unip (t • x)) (toL (Matrix.single i j z))
    (Units.ext (by simpa using e 0)) (by
      simp only [e]
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (toL (Matrix.single i j z))).const_add (oneL E a))
  have e2 : (fun t : ℝ => ψ.1 (blkGL hr p * infGL E a (unip (t • x)))) = fun _ => ψ.1 (blkGL hr p) := by
    funext t
    obtain ⟨y', hy'⟩ := blkGL_mul_unip hr p fun q => sInf E ((t • x) q)
    rw [infGL_unip, hy', h]
  rw [e2] at hd
  exact hd.unique (hasDerivAt_const _ _)

theorem exists_block_poly {r : ℕ} (hr : r ≤ a) (Q : (E →+* ℂ) → ℂ → ℂ[X]) (hQ : ∀ τ u, Q τ u ≠ 0) :
    ∃ q : (E →+* ℂ) → ℂ → ℂ[X], (∀ τ u, q τ u ≠ 0) ∧ ∀ ψ : Sm E a,
      (∀ (y : BlockIx a r → Ad E) g, ψ.1 (unip y * g) = ψ.1 g) →
      (∀ τ u, aeval (qdet (Eop (a := a) τ) u) (Q τ u) ψ = 0) → ∀ τ u p,
        (aeval (qdet (fun i j : Fin r => Eop (a := a) τ (fstIx hr i) (fstIx hr j)) u) (q τ u) ψ).1 (blkGL hr p) = 0 ∧
        (aeval (qdet (fun i j : Fin (a - r) => Eop (a := a) τ (sndIx hr i) (sndIx hr j)) u) (q τ u) ψ).1
          (blkGL hr p) = 0 := by
  let M' : Submodule ℂ (Sm E a) :=
    { carrier := {ψ | ∀ (y : BlockIx a r → Ad E) g, ψ.1 (unip y * g) = ψ.1 g}
      zero_mem' := fun _ _ => rfl
      add_mem' := fun hx hy y g => congrArg₂ (· + ·) (hx y g) (hy y g)
      smul_mem' := fun c _ hx y g => congrArg (c * ·) (hx y g) }
  let K : Submodule ℂ (Sm E a) :=
    { carrier := {ψ | ∀ p : GA E r × GA E (a - r), ψ.1 (blkGL hr p) = 0}
      zero_mem' := fun _ => rfl
      add_mem' := fun hx hy p => (congrArg₂ (· + ·) (hx p) (hy p)).trans (add_zero _)
      smul_mem' := fun c _ hx p => (congrArg (c * ·) (hx p)).trans (mul_zero _) }
  have hM : ∀ X, ∀ ψ ∈ M', lie E a X ψ ∈ M' := fun X ψ hψ y g => lie_left (hψ y) X g
  have key := fun τ : E →+* ℂ => GlobalTheory.T.harishChandra_capelli_uniform_diagonalBlocks (Sm E a) a r hr (Eop τ) (glRel_Eop τ) M' K
    (fun i j x hx => M'.smul_mem (1 / 2 : ℂ) (M'.sub_mem (hM _ x hx) (M'.smul_mem Complex.I (hM _ x hx))))
    (fun i j hi hj x hx => K.smul_mem (1 / 2 : ℂ) (K.sub_mem (lieS_upper hr hx hi hj _)
      (K.smul_mem Complex.I (lieS_upper hr hx hi hj _))))
    (fun i j hij x hx p => by
      obtain ⟨i, rfl⟩ := (blkEquiv hr).surjective i
      obtain ⟨j, rfl⟩ := (blkEquiv hr).surjective j
      obtain ⟨m₁, m₂⟩ := p
      rcases i with i | i <;> rcases j with j | j
      · have h0 : slice (fstIx hr) (blkGL hr (1, m₂)) x = 0 :=
          Subtype.ext (funext fun m => by rw [slice_apply, ← blkGL_eq_fst]; exact hx _)
        have h1 := Eop_slice (fstIx hr) (blkGL hr (1, m₂)) x τ i j
        rw [h0, map_zero] at h1
        rw [blkGL_eq_fst]
        exact (congrFun (congrArg Subtype.val h1) m₁).symm
      · simp at hij
      · simp at hij
      · have h0 : slice (sndIx hr) (blkGL hr (m₁, 1)) x = 0 :=
          Subtype.ext (funext fun m => by rw [slice_apply, ← blkGL_eq_snd]; exact hx _)
        have h1 := Eop_slice (sndIx hr) (blkGL hr (m₁, 1)) x τ i j
        rw [h0, map_zero] at h1
        rw [blkGL_eq_snd]
        exact (congrFun (congrArg Subtype.val h1) m₂).symm) (Q τ) (hQ τ)
  choose q hq0 hq using key
  exact ⟨q, hq0, fun ψ h1 h2 τ u p => ⟨(hq τ ψ h1 (h2 τ) u).1 p, (hq τ ψ h1 (h2 τ) u).2 p⟩⟩

theorem exists_translated {L : Subgroup (GL (Fin a) (Af E))} (hL : IsOpen (L : Set (GL (Fin a) (Af E))))
    {W : Submodule ℂ (Kinf E a → ℂ)} (hW : FiniteDimensional ℂ W) {X : Set (Module.End ℂ (Sm E a) → ℂ)} (hX : X.Finite)
    (N : ℕ) {r : ℕ} (hr : r ≤ a) [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)]
    {μ : Measure (BlockIx a r → Ad E)} {𝓕 : Set (BlockIx a r → Ad E)} (hμ : μ.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratN E a r) 𝓕 μ) (h1 : μ 𝓕 = 1) (t : GL (Fin a) (Af E)) (κ : Kinf E a) :
    ∃ (L' : Subgroup (GL (Fin a) (Af E))) (W' : Submodule ℂ (Kinf E a → ℂ)) (q : (E →+* ℂ) → ℂ → ℂ[X]),
      IsOpen (L' : Set (GL (Fin a) (Af E))) ∧ FiniteDimensional ℂ W' ∧ (∀ τ u, q τ u ≠ 0) ∧
      ∀ φ ∈ Submodule.span ℂ (GlobalTheory.HCF.formsGL E a L W X N), ∃ ψ : Sm E a,
        (∀ g, ψ.1 g = ∫ x in 𝓕, φ.1 (unip x * (g * finGL E a t * infGL E a (Unitary.toUnits κ))) ∂μ) ∧
        (∀ γ g, ψ.1 (ratGL E a (blkGL hr γ) * g) = ψ.1 g) ∧ (∀ k ∈ L', finRep E a k ψ = ψ) ∧
        (∀ g, (fun k : Kinf E a => (cptRep E a k ψ).1 g) ∈ W') ∧ ψ.1 ∈ growth E a ∧ ∀ τ u p,
        (aeval (qdet (fun i j : Fin r => Eop (a := a) τ (fstIx hr i) (fstIx hr j)) u) (q τ u) ψ).1 (blkGL hr p) = 0 ∧
        (aeval (qdet (fun i j : Fin (a - r) => Eop (a := a) τ (sndIx hr i) (sndIx hr j)) u) (q τ u) ψ).1
          (blkGL hr p) = 0 := by
  obtain ⟨Q, hQ0, hQ⟩ := span_props L W hX N
  obtain ⟨q, hq0, hq⟩ := exists_block_poly hr Q hQ0
  refine ⟨L.comap (MulAut.conj t⁻¹).toMonoidHom, W.map (LinearMap.funLeft ℂ ℂ fun k => κ⁻¹ * k * κ), q,
    hL.preimage (f := fun k => t⁻¹ * k * t⁻¹⁻¹) ((continuous_const.mul continuous_id).mul continuous_const),
    inferInstance, hq0, fun φ hφ => ?_⟩
  obtain ⟨hl, hf, hg, hz⟩ := hQ φ hφ
  obtain ⟨c, hc, hcz⟩ := exists_constTerm hL hμ h𝓕 h1 φ hl hf
  let ψ : Sm E a := rt E a (finGL E a t * infGL E a (Unitary.toUnits κ)) c
  have hψ : ∀ g, ψ.1 g = c.1 (g * (finGL E a t * infGL E a (Unitary.toUnits κ))) := fun _ => rfl
  refine ⟨ψ, fun g => by rw [hψ, hc, mul_assoc g], fun γ g => ?_, fun k hk => ?_, fun g => ?_, ?_, hq ψ ?_ ?_⟩
  · rw [hψ, hψ, hc, hc, mul_assoc]
    exact GlobalTheory.T.constant_term_integral_left_invariant E a r hr μ 𝓕 hμ h𝓕 h1 φ.1 hl γ _
  · refine Subtype.ext (funext fun g => ?_)
    have hk' : t⁻¹ * k * t⁻¹⁻¹ ∈ L := hk
    have e : g * finGL E a k * (finGL E a t * infGL E a (Unitary.toUnits κ)) =
        g * (finGL E a t * infGL E a (Unitary.toUnits κ)) * finGL E a (t⁻¹ * k * t⁻¹⁻¹) := by
      have e' : k * t = t * (t⁻¹ * k * t⁻¹⁻¹) := by group
      rw [mul_assoc g, mul_assoc g, mul_assoc (finGL E a t), infGL_comm, ← mul_assoc (finGL E a k),
        ← mul_assoc (finGL E a t), ← map_mul, ← map_mul, e']
    change ψ.1 (g * finGL E a k) = _
    rw [hψ, hψ, hc, hc, e]
    refine integral_congr_ae (.of_forall fun x => ?_)
    beta_reduce
    rw [← mul_assoc]
    exact congrFun (congrArg Subtype.val (hf _ hk')) _
  · refine ⟨_, GlobalTheory.HCFct.constTerm_cptTranslate_mem E a L W hW X N r μ 𝓕 hμ h𝓕 h1 φ hφ
      (g * (finGL E a t * infGL E a (Unitary.toUnits κ))), funext fun k => ?_⟩
    change _ = ψ.1 (g * infGL E a (Unitary.toUnits k))
    have e : g * infGL E a (Unitary.toUnits k) * (finGL E a t * infGL E a (Unitary.toUnits κ)) =
        g * (finGL E a t * infGL E a (Unitary.toUnits κ)) * infGL E a (Unitary.toUnits (κ⁻¹ * k * κ)) := by
      have e' : k * κ = κ * (κ⁻¹ * k * κ) := by group
      rw [mul_assoc g, mul_assoc g, ← mul_assoc (infGL E a _), infGL_comm, mul_assoc (finGL E a t),
        mul_assoc (finGL E a t), ← map_mul, ← map_mul, ← map_mul, ← map_mul, e']
    rw [hψ, hc, e]
    rfl
  · have g1 : c.1 ∈ growth E a := fun g => by
      simp only [hc]
      exact GlobalTheory.T.constant_term_moderate_growth E a r μ 𝓕 hμ h𝓕 h1 φ hl (isOpen_stab hL hf) hg g
    have g2 := SmoothFinite.growth_cptRep g1 κ
    intro g
    obtain ⟨C, n, h⟩ := g2 (g * finGL E a t)
    refine ⟨C, n, fun y => ?_⟩
    rw [hψ, ← mul_assoc, mul_assoc g, infGL_comm, ← mul_assoc]
    exact h y
  · intro y g
    rw [hψ, hψ, hc, hc, mul_assoc]
    exact constTerm_unip_invariant E a r μ 𝓕 hμ h𝓕 φ.1 hl y _
  · intro τ u
    rw [← Module.End.mul_apply, (commute_aeval_rt τ u _ _).eq, Module.End.mul_apply, hcz τ u _ (hz τ u), map_zero]

theorem exists_slice_space (f : Fin b ↪ Fin a)
    (hb : ∀ (L : Subgroup (GL (Fin b) (Af E))), IsOpen (L : Set (GL (Fin b) (Af E))) →
      ∀ W : Submodule ℂ (Kinf E b → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E b) → ℂ), X.Finite →
      ∀ N : ℕ, FiniteDimensional ℂ (Submodule.span ℂ (GlobalTheory.HCF.formsGL E b L W X N)))
    {L : Subgroup (GL (Fin a) (Af E))} (hL : IsOpen (L : Set (GL (Fin a) (Af E))))
    {W : Submodule ℂ (Kinf E a → ℂ)} (hW : FiniteDimensional ℂ W) (q : (E →+* ℂ) → ℂ → ℂ[X]) (hq : ∀ τ u, q τ u ≠ 0) :
    ∃ V : Submodule ℂ (GA E b → ℂ), FiniteDimensional ℂ V ∧ ∀ (ψ : Sm E a) (g : GA E a),
      (∀ γ m, ψ.1 (g * embGL f (ratGL E b γ * m)) = ψ.1 (g * embGL f m)) → (∀ k ∈ L, finRep E a k ψ = ψ) →
      (∀ g, (fun k : Kinf E a => (cptRep E a k ψ).1 g) ∈ W) → ψ.1 ∈ growth E a →
      (∀ τ u m, (aeval (qdet (fun i j : Fin b => Eop (a := a) τ (f i) (f j)) u) (q τ u) ψ).1 (g * embGL f m) = 0) →
      (fun m => ψ.1 (g * embGL f m)) ∈ V := by
  obtain ⟨V, hV, h⟩ := GlobalTheory.T.finiteDimensional_slowlyIncreasing_killed_capelliPolynomials E b hb (L.comap (embGL f)) (hL.preimage (continuous_embGL f))
    (W.map (LinearMap.funLeft ℂ ℂ (embK f))) inferInstance (fun τ u => q τ (u + ((b : ℂ) - 1) / 2)) fun τ u => hq τ _
  refine ⟨V.map (Sm E b).subtype, inferInstance, fun ψ g h1 h2 h3 h4 h5 =>
    ⟨slice f g ψ, h _ h1 (fun k hk => ?_) (fun m => ?_) (growth_slice f g ψ h4) fun τ u => ?_, rfl⟩⟩
  · refine Subtype.ext (funext fun m => ?_)
    change ψ.1 (g * embGL f (m * finGL E b k)) = ψ.1 (g * embGL f m)
    rw [map_mul, embGL_finGL, ← mul_assoc]
    exact congrFun (congrArg Subtype.val (h2 _ hk)) _
  · refine ⟨_, h3 (g * embGL f m), funext fun k => ?_⟩
    change ψ.1 (g * embGL f m * infGL E a (Unitary.toUnits (embK f k))) =
      ψ.1 (g * embGL f (m * infGL E b (Unitary.toUnits k)))
    rw [map_mul, embGL_infGL, toUnits_embK, mul_assoc]
  · rw [cap, aeval_qdet_slice]
    exact Subtype.ext (funext fun m => h5 τ _ m)

omit [IsTotallyComplex E] in
theorem ratGL_blkGL {r : ℕ} (hr : r ≤ a) (γ : GL (Fin r) E × GL (Fin (a - r)) E) :
    ratGL E a (blkGL hr γ) = blkGL hr (ratGL E r γ.1, ratGL E (a - r) γ.2) :=
  map_blkGL hr (algebraMap E (Ad E)) γ

theorem slice_fst : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), (∀ a' : ℕ, a' < a → ∀ (L' : Subgroup (GL (Fin a') (Af E))), IsOpen (L' : Set (GL (Fin a') (Af E))) → ∀ W' : Submodule ℂ (Kinf E a' → ℂ), FiniteDimensional ℂ W' → ∀ X' : Set (Module.End ℂ (Sm E a') → ℂ), X'.Finite → ∀ N' : ℕ, FiniteDimensional ℂ (Submodule.span ℂ (GlobalTheory.HCF.formsGL E a' L' W' X' N'))) → ∀ (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ, ∀ (r : ℕ), 0 < r → ∀ (hr : r < a), ∀ [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 → ∀ (t : GL (Fin a) (Af E)) (κ : Kinf E a), ∃ V₁ : Submodule ℂ (GA E r → ℂ), FiniteDimensional ℂ V₁ ∧ ∀ φ ∈ Submodule.span ℂ (GlobalTheory.HCF.formsGL E a L W X N), ∀ m₂ : GA E (a - r), (fun m₁ : GA E r => ∫ x in 𝓕, φ.1 (unip x * (GlobalTheory.LeviGA.blkGL hr.le (m₁, m₂) * finGL E a t * infGL E a (Unitary.toUnits κ))) ∂μ) ∈ V₁ := by
  intro E _ _ _ a hind L hL W hW X hX N r _ hr _ _ μ 𝓕 hμ h𝓕 h1 t κ
  obtain ⟨L', W', q, hL', hW', hq, h⟩ := exists_translated hL hW hX N hr.le hμ h𝓕 h1 t κ
  obtain ⟨V, hV, hs⟩ := exists_slice_space (fstIx hr.le) (hind r hr) hL' hW' q hq
  refine ⟨V, hV, fun φ hφ m₂ => ?_⟩
  obtain ⟨ψ, e, h2, h3, h4, h5, h6⟩ := h φ hφ
  have := hs ψ (blkGL hr.le (1, m₂)) (fun γ m => by
    rw [← blkGL_eq_fst, ← blkGL_eq_fst, ← h2 (γ, 1) (blkGL hr.le (m, m₂)), ratGL_blkGL, ← map_mul]
    simp) h3 h4 h5 fun τ u m => by rw [← blkGL_eq_fst]; exact (h6 τ u _).1
  simpa only [← blkGL_eq_fst, e] using this

end GlobalTheory.GLSlice

end
