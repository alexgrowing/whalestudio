import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.LAbove
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BlkInvVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.LevLaws
import Development.WeilBound.CuspidalAdmissibility.FixLev

open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace
open scoped NumberField.AdeleRing

private theorem blocks_read {R : Type} [CommRing R] {x y : Matrix (Fin 2) (Fin 2) R}
    {X : UPos (2 + 2) 2 → R} {A : Matrix (Fin (2 + 2)) (Fin (2 + 2)) R}
    (h : Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks x 0 0 y) = unipMatrix X * A) (i j : Fin 2) :
    A (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)) = x i j ∧
      A (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inr j)) = y i j := by
  have ent : ∀ a b : Fin 2 ⊕ Fin 2, (unipMatrix X * A) (finSumFinEquiv a) (finSumFinEquiv b) = Matrix.fromBlocks x 0 0 y a b := by
    intro a b
    rw [← h]
    simp
  have vl : ∀ a : Fin 2, ((finSumFinEquiv (Sum.inl a) : Fin (2 + 2)) : ℕ) < 2 := fun a => by
    rw [finSumFinEquiv_apply_left]
    exact a.2
  have vr : ∀ a : Fin 2, 2 ≤ ((finSumFinEquiv (Sum.inr a) : Fin (2 + 2)) : ℕ) := fun a => by
    rw [finSumFinEquiv_apply_right]
    exact Nat.le_add_right _ _
  have row : ∀ (a : Fin 2) (l : Fin (2 + 2)), blockEntry X (finSumFinEquiv (Sum.inr a)) l = 0 := by
    intro a l
    rw [blockEntry_apply, dif_neg]
    intro hh
    have := vr a
    omega
  have low : ∀ (a : Fin 2) (b : Fin (2 + 2)), (unipMatrix X * A) (finSumFinEquiv (Sum.inr a)) b = A (finSumFinEquiv (Sum.inr a)) b := by
    intro a b
    rw [unipMatrix, add_mul, one_mul, Matrix.add_apply, Matrix.mul_apply]
    simp [row]
  have c0 : ∀ a b : Fin 2, A (finSumFinEquiv (Sum.inr a)) (finSumFinEquiv (Sum.inl b)) = 0 := by
    intro a b
    rw [← low, ent]
    simp
  refine ⟨?_, ?_⟩
  · rw [show x i j = Matrix.fromBlocks x 0 0 y (Sum.inl i) (Sum.inl j) by simp, ← ent, unipMatrix, add_mul, one_mul,
      Matrix.add_apply, Matrix.mul_apply, Finset.sum_eq_zero, add_zero]
    intro l _
    obtain ⟨l, rfl⟩ := finSumFinEquiv.surjective l
    rcases l with l | l
    · rw [blockEntry_apply, dif_neg, zero_mul]
      intro hh
      have := vl l
      omega
    · rw [c0, mul_zero]
  · rw [← low, ent]
    simp

private theorem exists_depth {K : Type} [Field K] [NumberField K] (w : Pl K) {A B : Subgroup (Gw 2 w)}
    (hA : IsOpen (A : Set (Gw 2 w))) (hB : IsOpen (B : Set (Gw 2 w))) :
    ∃ m, GLnLocal.congruenceSubgroup (w.adicCompletion K) 2 m ≤ A ⊓ B := by
  have h : ((A ⊓ B : Subgroup (Gw 2 w)) : Set (Gw 2 w)) ∈ 𝓝 (1 : Gw 2 w) :=
    (hA.inter hB).mem_nhds ⟨one_mem _, one_mem _⟩
  obtain ⟨m, -, hm⟩ := (GLnLocal.hasBasis_nhds_one (w.adicCompletion K) 2).mem_iff.1 h
  exact ⟨m, hm⟩

private theorem finite_projection_integral_coe {K : Type} [Field K] [NumberField K] {n : ℕ} {u : FA K n}
    (hu : u ∈ AdelicGLn.integralFiniteGL K n) :
    ((fin1 u : G1 K n) : AdelicGLn.AdelicGL K n) = finEmb K n u :=
  congrArg Subtype.val (MultiplicityOne.finProj_of_mem (maxCompact_le_normOneGL (finEmb_mem_maxCompact hu)))

private theorem block_mem {K : Type} [Field K] [NumberField K] (S : Finset (Pl K)) {V : ∀ w : Pl K, Subgroup (Gw 2 w)}
    (m : Pl K → ℕ) (hV : ∀ w, GLnLocal.congruenceSubgroup (w.adicCompletion K) 2 (m w) ≤ V w)
    {d : FA K 2} (hd : d ∈ AdelicGLn.integralFiniteGL K 2) {u : FA K (2 + 2)} (f : Fin 2 → Fin (2 + 2)) (hf : Function.Injective f)
    (hu : u ∈ levOn S fun w : Pl K => GLnLocal.congruenceSubgroup (w.adicCompletion K) (2 + 2) (m w))
    (he : ∀ i j, (finEmb K (2 + 2) u) (f i) (f j) = (finEmb K 2 d) i j) : d ∈ levOn S V := by
  have hu' : ∀ v, finAt v (finEmb K (2 + 2) u) ∈ (if v ∈ S then GLnLocal.congruenceSubgroup (v.adicCompletion K) (2 + 2) (m v)
      else GLnLocal.integralGL (v.adicCompletion K) (2 + 2)) := hu
  have hint : ∀ v, finAt v (finEmb K 2 d) ∈ GLnLocal.integralGL (v.adicCompletion K) 2 := fun v => by
    rw [PositivityTheory.TfC.FixLev.finAt_finEmb]
    exact (AdelicGLn.mem_integralFiniteGL_iff_forall K 2).1 hd v
  change ∀ v, finAt v (finEmb K 2 d) ∈ (if v ∈ S then V v else GLnLocal.integralGL (v.adicCompletion K) 2)
  intro v
  by_cases hv : v ∈ S
  · rw [if_pos hv]
    refine hV v ((GLnLocal.mem_congruenceSubgroup_iff _ _).2 ⟨hint v, fun i j => ?_⟩)
    have h1 := hu' v
    rw [if_pos hv] at h1
    have h2 := ((GLnLocal.mem_congruenceSubgroup_iff _ _).1 h1).2 (f i) (f j)
    have h3 : finAt v (finEmb K (2 + 2) u) (f i) (f j) = finAt v (finEmb K 2 d) i j := by
      simp only [finAt_apply, he]
    rw [h3] at h2
    have h4 : (1 : Matrix (Fin (2 + 2)) (Fin (2 + 2)) (v.adicCompletion K)) (f i) (f j) =
        (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j := by
      simp [Matrix.one_apply, hf.eq_iff]
    rwa [h4] at h2
  · rw [if_neg hv]
    exact hint v

theorem UpperTheory.exists_level_indicator_unipotent_invariant :
    ∀ {K : Type} [Field K] [NumberField K] (S : Finset (Pl K)) (U₁ U₂ : ∀ w : Pl K, Subgroup (Gw 2 w)), Lev U₁ → Lev U₂ → ∃ (U : ∀ w : Pl K, Subgroup (Gw (2 + 2) w)) (χ : AdelicGLn.integralFiniteGL K (2 + 2) → ℂ), Lev U ∧ Continuous χ ∧ (∀ h, χ h = 0 ∨ χ h = 1) ∧ χ 1 = 1 ∧ (∀ (h₀ h : AdelicGLn.integralFiniteGL K (2 + 2)) X, fin1 (h₀ : FA K (2 + 2)) = nn X → χ (h₀ * h) = χ h) ∧ (∀ h u : AdelicGLn.integralFiniteGL K (2 + 2), (u : FA K (2 + 2)) ∈ levOn S U → χ (h * u) = χ h) ∧ ∀ (d₁ d₂ : AdelicGLn.integralFiniteGL K 2) (h : AdelicGLn.integralFiniteGL K (2 + 2)), fin1 (h : FA K (2 + 2)) = lv (fin1 (d₁ : FA K 2)) (fin1 (d₂ : FA K 2)) 0 → χ h ≠ 0 → (d₁ : FA K 2) ∈ levOn S U₁ ∧ (d₂ : FA K 2) ∈ levOn S U₂ := by
  intro K _ _ S U₁ U₂ h₁ h₂
  choose m hm using fun w : Pl K => exists_depth w (h₁ w).1.2 (h₂ w).1.2
  let U : ∀ w : Pl K, Subgroup (Gw (2 + 2) w) := fun w =>
    GLnLocal.congruenceSubgroup (w.adicCompletion K) (2 + 2) (m w)
  have hU : Lev U := fun w => ⟨⟨GLnLocal.isCompact_congruenceSubgroup _ _ _, GLnLocal.isOpen_congruenceSubgroup _ _ _⟩,
    GLnLocal.congruenceSubgroup_le _ _ _⟩
  obtain ⟨⟨-, hopen⟩, hle⟩ := (UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.levLaws (K := K) (2 + 2) S).1 U hU
  have fm : ∀ a b : FA K (2 + 2), fin1 (a * b) = fin1 a * fin1 b := fun a b => map_mul (MultiplicityOne.finProj K (2 + 2)) a b
  have fi : ∀ a : FA K (2 + 2), fin1 a⁻¹ = (fin1 a)⁻¹ := fun a => map_inv (MultiplicityOne.finProj K (2 + 2)) a
  let P : FA K (2 + 2) → Prop := fun h => ∃ X, ∃ u ∈ levOn S U, fin1 h = nn X * fin1 u
  have hR1 : ∀ (h u : FA K (2 + 2)), u ∈ levOn S U → P h → P (h * u) := by
    rintro h u hu ⟨X, v, hv, e⟩
    exact ⟨X, v * u, mul_mem hv hu, by rw [fm, e, fm, mul_assoc]⟩
  have hR : ∀ (h u : FA K (2 + 2)), u ∈ levOn S U → (P (h * u) ↔ P h) := fun h u hu =>
    ⟨fun hp => by simpa using hR1 _ _ (inv_mem hu) hp, hR1 h u hu⟩
  have hL1 : ∀ (h₀ h : FA K (2 + 2)) X, fin1 h₀ = nn X → P h → P (h₀ * h) := by
    rintro h₀ h X e ⟨Y, v, hv, e'⟩
    refine ⟨X + Y, v, hv, ?_⟩
    rw [fm, e, e', ← mul_assoc]
    exact congrArg (· * _) (unipOne_add 2 X Y).symm
  have hL : ∀ (h₀ h : FA K (2 + 2)) X, fin1 h₀ = nn X → (P (h₀ * h) ↔ P h) := by
    refine fun h₀ h X e => ⟨fun hp => ?_, hL1 h₀ h X e⟩
    have e' : fin1 h₀⁻¹ = nn (-X) := by
      rw [fi, e, inv_eq_iff_mul_eq_one]
      rw [← unipOne_add, add_neg_cancel, unipOne_zero]
    simpa using hL1 _ _ _ e' hp
  let χ : AdelicGLn.integralFiniteGL K (2 + 2) → ℂ := fun h => if P h then 1 else 0
  have hχR : ∀ h u : AdelicGLn.integralFiniteGL K (2 + 2), (u : FA K (2 + 2)) ∈ levOn S U → χ (h * u) = χ h := by
    intro h u hu
    simp only [χ, Subgroup.coe_mul, hR _ _ hu]
  refine ⟨U, χ, hU, ?_, fun h => ?_, ?_, ?_, hχR, ?_⟩
  · refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_)
    have ho : IsOpen {y : AdelicGLn.integralFiniteGL K (2 + 2) | ((x⁻¹ * y : AdelicGLn.integralFiniteGL K (2 + 2)) : FA K (2 + 2)) ∈ levOn S U} :=
      hopen.preimage (continuous_subtype_val.comp (continuous_const.mul continuous_id))
    filter_upwards [ho.mem_nhds (by simp)] with y hy
    have := hχR x _ hy
    rwa [mul_inv_cancel_left] at this
  · by_cases hp : P h
    · exact Or.inr (if_pos hp)
    · exact Or.inl (if_neg hp)
  · refine if_pos ⟨0, 1, one_mem _, ?_⟩
    rw [show nn (0 : UPos (2 + 2) 2 → 𝔸[K]) = 1 from unipOne_zero 2]
    simp
  · intro h₀ h X e
    simp only [χ, Subgroup.coe_mul, hL _ _ X e]
  · intro d₁ d₂ h e hne
    have hP : P h := by
      by_contra hn
      exact hne (if_neg hn)
    obtain ⟨X, u, hu, e'⟩ := hP
    have key : blk (finEmb K 2 d₁) (finEmb K 2 d₂) = unipGL X * finEmb K (2 + 2) u := by
      have a1 := congrArg Subtype.val e
      have a2 := congrArg Subtype.val e'
      rw [blkLaws.1, finite_projection_integral_coe d₁.2, finite_projection_integral_coe d₂.2] at a1
      rw [Subgroup.coe_mul, finite_projection_integral_coe (hle hu)] at a2
      have z0 : zt K 0 = 1 := by
        rw [zt, ← map_one (centralSection K 2)]
        exact congrArg _ (Subtype.ext Real.exp_zero)
      rw [neg_zero, z0, mul_one, mul_one] at a1
      exact a1.symm.trans a2
    have hb := blocks_read (x := (finEmb K 2 d₁).val) (y := (finEmb K 2 d₂).val) (X := X) (A := (finEmb K (2 + 2) u).val)
      (congrArg Units.val key)
    exact ⟨block_mem S m (fun w => (hm w).trans inf_le_left) d₁.2 (fun i => finSumFinEquiv (Sum.inl i))
        (fun _ _ h => Sum.inl_injective (finSumFinEquiv.injective h)) hu fun i j => (hb i j).1,
      block_mem S m (fun w => (hm w).trans inf_le_right) d₂.2 (fun i => finSumFinEquiv (Sum.inr i))
        (fun _ _ h => Sum.inr_injective (finSumFinEquiv.injective h)) hu fun i j => (hb i j).2⟩
