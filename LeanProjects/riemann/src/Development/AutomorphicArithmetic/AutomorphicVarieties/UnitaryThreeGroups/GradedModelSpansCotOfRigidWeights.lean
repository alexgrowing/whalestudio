import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Rigid0
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.TanDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.NormCob
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.AdRepBaseLiftApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ZetaReducibleRepEqSubInvAndIsUnit
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.NormO

open Matrix IsLocalRing UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.HV

private theorem baer_field {O K : Type} [CommRing O] [Field K] [Algebra O K]
    (hi : Function.Injective (algebraMap O K)) : Module.Baer O K := by
  intro I g
  by_cases hI : I = ⊥
  · subst hI
    refine ⟨0, fun x hx => ?_⟩
    have : x = 0 := hx
    subst this
    exact (map_zero g).symm
  · obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    have hk : algebraMap O K a ≠ 0 := fun h => ha0 (hi (by rw [h, map_zero]))
    refine ⟨LinearMap.toSpanSingleton O K (g ⟨a, ha⟩ / algebraMap O K a), fun x hx => ?_⟩
    have h1 : a • g ⟨x, hx⟩ = x • g ⟨a, ha⟩ := by
      rw [← map_smul, ← map_smul]
      congr 1
      exact Subtype.ext (mul_comm a x)
    rw [LinearMap.toSpanSingleton_apply, Algebra.smul_def, mul_div_assoc', div_eq_iff hk, ← Algebra.smul_def, ← h1,
      Algebra.smul_def, mul_comm]

private theorem exists_form {O K P : Type} [CommRing O] [Field K] [Algebra O K] [AddCommGroup P] [Module O P]
    (hi : Function.Injective (algebraMap O K)) (T : Submodule O P) (p : P) (hp : ∀ c : O, c ≠ 0 → c • p ∉ T) :
    ∃ lam : P →ₗ[O] K, lam p = 1 ∧ ∀ y ∈ T, lam y = 0 := by
  have hinj : Function.Injective (LinearMap.toSpanSingleton O (P ⧸ T) (T.mkQ p)) := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    by_contra h0
    apply hp c h0
    rw [LinearMap.toSpanSingleton_apply, ← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hc
    exact hc
  obtain ⟨h, hh⟩ := (baer_field hi).extension_property _ hinj (Algebra.linearMap O K)
  refine ⟨h ∘ₗ T.mkQ, ?_, fun y hy => ?_⟩
  · have := LinearMap.congr_fun hh 1
    simpa using this
  · rw [LinearMap.comp_apply, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero T).2 hy, map_zero]

private theorem spans_of_der {O A K ι : Type} [CommRing O] [IsDomain O] [CommRing A] [Algebra O A] [Field K]
    [Algebra O K] (hi : Function.Injective (algebraMap O K)) (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜]
    (x : A →ₐ[O] O) (hx : ∀ j, j ≠ 0 → ∀ f ∈ 𝒜 j, x f = 0) (j : ℤ) (F : ι → A) (hF : ∀ i, F i ∈ 𝒜 j)
    (T : Set A) (hT : ∀ t ∈ T, x t = 0 ∧ (t ∈ Set.range F ∨ ∃ i, i ≠ j ∧ t ∈ 𝒜 i))
    (h : ∀ D ∈ PtDer ((Algebra.ofId O K).comp x) K, HasWt 𝒜 j D → (∀ y ∈ Ideal.span T, D y = 0) → D = 0) :
    SpansCot x 𝒜 j F := by
  rintro p ⟨f, ⟨hfj, hfx⟩, rfl⟩
  by_contra hn
  push Not at hn
  obtain ⟨lam, h1, h0⟩ := exists_form hi (cotSpan x F) _ hn
  have hfx' : x f = 0 := hfx
  let e : A →ₗ[O] A := LinearMap.id - Algebra.linearMap O A ∘ₗ x.toLinearMap
  have he : ∀ a, e a = a - algebraMap O A (x a) := fun _ => rfl
  let δ : A →ₗ[O] K := lam ∘ₗ (satSq x).mkQ ∘ₗ e
  have hδ : ∀ a b, δ (a * b) = x a • δ b + x b • δ a := by
    intro a b
    have hm : ∀ a, e a ∈ RingHom.ker x := fun a => by simp [he, RingHom.mem_ker]
    have h2 : e a * e b ∈ satSq x := ⟨1, one_ne_zero, by
      rw [one_smul, pow_two]; exact Ideal.mul_mem_mul (hm a) (hm b)⟩
    have h3 : e (a * b) = e a * e b + (x a • e b + x b • e a) := by
      simp only [he, map_mul, Algebra.smul_def]; ring
    have h4 : (satSq x).mkQ (e a * e b) = 0 := (Submodule.Quotient.mk_eq_zero _).2 h2
    simp only [δ, LinearMap.comp_apply]
    rw [h3, map_add, h4, zero_add, map_add, map_smul, map_smul, map_add, map_smul, map_smul]
  let D : A →ₗ[O] K := δ ∘ₗ GradedAlgebra.proj 𝒜 j
  have hD1 : ∀ a ∈ 𝒜 j, D a = δ a := fun a ha => by
    simp only [D, LinearMap.comp_apply, GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_same 𝒜 ha]
  have hD0 : HasWt 𝒜 j D := fun i hi a ha => by
    simp only [D, LinearMap.comp_apply, GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_ne 𝒜 ha hi, map_zero]
  have hhom : ∀ i k, ∀ a ∈ 𝒜 i, ∀ b ∈ 𝒜 k, D (a * b) = x a • D b + x b • D a := by
    intro i k a ha b hb
    have hab : a * b ∈ 𝒜 (i + k) := SetLike.mul_mem_graded ha hb
    by_cases hik : i + k = j
    · rw [hD1 _ (hik ▸ hab), hδ]
      congr 1
      · by_cases hk : k = j
        · rw [hD1 b (hk ▸ hb)]
        · rw [hx i (by omega) a ha, zero_smul, zero_smul]
      · by_cases hk : i = j
        · rw [hD1 a (hk ▸ ha)]
        · rw [hx k (by omega) b hb, zero_smul, zero_smul]
    · rw [hD0 _ hik _ hab]
      have e1 : x a • D b = 0 := by
        by_cases h0 : i = 0
        · rw [hD0 k (by omega) b hb, smul_zero]
        · rw [hx i h0 a ha, zero_smul]
      have e2 : x b • D a = 0 := by
        by_cases h0 : k = 0
        · rw [hD0 i (by omega) a ha, smul_zero]
        · rw [hx k h0 b hb, zero_smul]
      rw [e1, e2, add_zero]
  have hder : ∀ a b, D (a * b) = x a • D b + x b • D a := by
    intro a b
    induction a using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | add a a' h h' => simp only [add_mul, map_add, h, h', add_smul, smul_add]; abel
    | homogeneous a =>
      induction b using DirectSum.Decomposition.inductionOn 𝒜 with
      | zero => simp
      | add b b' h h' => simp only [mul_add, map_add, h, h', add_smul, smul_add]; abel
      | homogeneous b => exact hhom _ _ _ a.2 _ b.2
  have hδ0 : ∀ a, x a = 0 → δ a = lam ((satSq x).mkQ a) := fun a ha => by
    simp only [δ, LinearMap.comp_apply, he, ha, map_zero, sub_zero]
  have hz : D = 0 := by
    refine h D (fun a b => ?_) hD0 (fun y hy => ?_)
    · rw [hder]
      simp [Algebra.smul_def]
    · suffices x y = 0 ∧ D y = 0 from this.2
      induction hy using Submodule.span_induction with
      | mem t ht =>
        obtain ⟨t0, ⟨i, rfl⟩ | ⟨i, hi, ht'⟩⟩ := hT t ht
        · refine ⟨t0, ?_⟩
          rw [hD1 _ (hF i), hδ0 _ t0]
          exact h0 _ (Submodule.subset_span ⟨i, rfl⟩)
        · exact ⟨t0, hD0 i hi t ht'⟩
      | zero => simp
      | add a b _ _ ha hb => simp [ha.1, ha.2, hb.1, hb.2]
      | smul a b _ hb =>
        rw [smul_eq_mul, map_mul, hder, hb.1, hb.2]
        simp
  have := hD1 f hfj
  rw [hz, hδ0 f hfx', h1] at this
  exact zero_ne_one this

private theorem norm_lt_one_of_mem {l : ℕ} [Fact l.Prime] (c : Coef l) (a : c.O) (ha : ¬ IsUnit a) :
    ‖(a : PadicAlgCl l)‖ < 1 := by
  by_cases h0 : a = 0
  · subst h0; simp
  have h := UpperTheory.V.Base.normO l c.O a h0
  have h1 : IsDiscreteValuationRing.addVal c.O a ≠ 0 := fun h =>
    ha (IsDiscreteValuationRing.addVal_eq_zero_iff.1 h)
  have h2 : IsDiscreteValuationRing.addVal c.O a ≠ ⊤ := fun h => h0 (IsDiscreteValuationRing.addVal_eq_top_iff.1 h)
  have h3 : (IsDiscreteValuationRing.addVal c.O a).toNat ≠ 0 := by
    rw [Ne, ENat.toNat_eq_zero]; tauto
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have h4 := pow_lt_one₀ (a := (l : ℝ)⁻¹) (by positivity) (inv_lt_one_of_one_lt₀ hl) h3
  by_contra hn
  exact absurd (h ▸ h4) (not_lt.2 (one_le_pow₀ (not_lt.1 hn)))

private theorem local_of_res {O R : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R]
    (x : R →ₐ[O] O) (y : R) (hy : y ∈ maximalIdeal R) : ¬ IsUnit (x y) := by
  intro hu
  have h2 : IsUnit (y - algebraMap O R (x y)) := by
    by_contra hn
    have h3 : y - algebraMap O R (x y) ∈ maximalIdeal R := hn
    have h4 : algebraMap O R (x y) ∈ maximalIdeal R := by simpa using Ideal.sub_mem _ hy h3
    exact h4 (hu.map _)
  have h5 := h2.map x
  simp at h5

private theorem map_reducible_three_dim {G R K : Type} [Group G] [CommRing R] [CommRing K] (f : R →+* K) (η : G →* ℤˣ) (Ψ : G →* Rˣ) :
    (GG.map f).comp (r0 η Ψ) = r0 η ((Units.map f.toMonoidHom).comp Ψ) := by
  refine MonoidHom.ext fun g => SemidirectProduct.ext (Units.ext ?_) rfl
  show (tor R (Ψ g) : Matrix (Fin 3) (Fin 3) R).map f = tor _ (((Units.map f.toMonoidHom).comp Ψ) g)
  rw [tor_val, tor_val, Matrix.diagonal_map (map_zero _)]
  congr 1
  funext i
  exact congrArg Units.val (map_zpow (Units.map f.toMonoidHom) (Ψ g) (wt1 i))

private theorem coboundary_torus_lie_zero {G K : Type} [Group G] [CommRing K] (η : G →* ℤˣ) (Ψ : G →* Kˣ)
    (X : Matrix (Fin 3) (Fin 3) K) (hX : X ∈ unitaryThreeTorusLieAlgebra K) : cob (r0 η Ψ) X = 0 := by
  rw [unitaryThreeTorusLieAlgebra, Submodule.mem_span_singleton] at hX
  obtain ⟨a, rfl⟩ := hX
  funext g
  ext i j
  rw [cob, Matrix.sub_apply, adRep_baseLift_apply]
  fin_cases i <;> fin_cases j <;> split_ifs <;> simp [wt, wt1, Fin.rev] <;> ring

private theorem spans_three {O A K : Type} [CommRing O] [IsDomain O] [CommRing A] [Algebra O A] [Field K]
    [Algebra O K] (hi : Function.Injective (algebraMap O K)) (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜]
    (x : A →ₐ[O] O) (hx : ∀ j, j ≠ 0 → ∀ f ∈ 𝒜 j, x f = 0) {r s r' s' m : ℕ} (Q : Eqns 𝒜 x r s r' s' m)
    (key : ∀ j : ℤ, j ≤ 0 → ∀ D ∈ PtDer ((Algebra.ofId O K).comp x) K, HasWt 𝒜 j D → (∀ y ∈ Q.ideal, D y = 0) →
      D = 0) : SpansCot x 𝒜 (-1) Q.F ∧ SpansCot x 𝒜 (-2) Q.G ∧ SpansCot x 𝒜 0 Q.Z := by
  have hF0 := fun i => hx _ (by decide) _ (Q.hF i)
  have hG0 := fun i => hx _ (by decide) _ (Q.hG i)
  have hE0 := fun i => hx _ (by decide) _ (Q.hE i)
  have hE0' := fun i => hx _ (by decide) _ (Q.hE' i)
  refine ⟨?_, ?_, ?_⟩
  · refine spans_of_der hi 𝒜 x hx _ _ Q.hF _ ?_ (key _ (by decide))
    rintro t ((((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩)
    · exact ⟨hF0 i, Or.inl ⟨i, rfl⟩⟩
    · exact ⟨hG0 i, Or.inr ⟨_, by decide, Q.hG i⟩⟩
    · exact ⟨hE0 i, Or.inr ⟨_, by decide, Q.hE i⟩⟩
    · exact ⟨hE0' i, Or.inr ⟨_, by decide, Q.hE' i⟩⟩
    · exact ⟨(Q.hZ i).2, Or.inr ⟨_, by decide, (Q.hZ i).1⟩⟩
  · refine spans_of_der hi 𝒜 x hx _ _ Q.hG _ ?_ (key _ (by decide))
    rintro t ((((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩)
    · exact ⟨hF0 i, Or.inr ⟨_, by decide, Q.hF i⟩⟩
    · exact ⟨hG0 i, Or.inl ⟨i, rfl⟩⟩
    · exact ⟨hE0 i, Or.inr ⟨_, by decide, Q.hE i⟩⟩
    · exact ⟨hE0' i, Or.inr ⟨_, by decide, Q.hE' i⟩⟩
    · exact ⟨(Q.hZ i).2, Or.inr ⟨_, by decide, (Q.hZ i).1⟩⟩
  · refine spans_of_der hi 𝒜 x hx _ _ (fun i => (Q.hZ i).1) _ ?_ (key _ (by decide))
    rintro t ((((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩)
    · exact ⟨hF0 i, Or.inr ⟨_, by decide, Q.hF i⟩⟩
    · exact ⟨hG0 i, Or.inr ⟨_, by decide, Q.hG i⟩⟩
    · exact ⟨hE0 i, Or.inr ⟨_, by decide, Q.hE i⟩⟩
    · exact ⟨hE0' i, Or.inr ⟨_, by decide, Q.hE' i⟩⟩
    · exact ⟨(Q.hZ i).2, Or.inl ⟨i, rfl⟩⟩

theorem UpperTheory.V.U3.gradedModel_spansCot_of_rigid_weights :
    ∀ {l : ℕ} [Fact l.Prime] {c : Coef l} {Γ H : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
      {η : Γ →* ℤˣ} {Ψ : Γ →* (c.O)ˣ} {N : Set Γ} {ι : H →* Γ} {hι : Continuous ι}
      {U : Univ (GCond.noCondition c.O (η.comp ι) (Ψ.comp ι))} {I : Ideal U.R} {cc g₁ : Γ} (S : SRing N hι U I cc g₁) (M : Model S (PadicAlgCl l)), l ≠ 2 → Marks η Ψ cc g₁ →
      M2 M.𝒜 M.Q.ideal → (∀ j : ℤ, j ≤ 0 → RigidWt j S.r.hom (toBar M.x₀)) → M1 M.Q := by
  intro l _ c Γ H _ _ _ _ _ _ η Ψ N ι hι U I cc g₁ S M hl hm h2 hrig
  have hi : Function.Injective (algebraMap c.O (PadicAlgCl l)) := Subtype.val_injective
  have hloc : IsLocPt (toBar M.x₀) := fun y hy => norm_lt_one_of_mem c _ (local_of_res M.x₀ y hy)
  have hq : (toBar M.x₀).comp M.q = (Algebra.ofId c.O (PadicAlgCl l)).comp M.x := by
    rw [← M.x₀_q]; rfl
  let Ψ' : Γ →* (PadicAlgCl l)ˣ := (Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom).comp Ψ
  have hpush : push (toBar M.x₀) S.r.hom = r0 η Ψ' := by
    rw [← map_reducible_three_dim, ← M.base]; rfl
  have hm' : Marks η Ψ' cc g₁ := by
    refine ⟨hm.csq, hm.ηc, by simp [Ψ', hm.Ψc], hm.ηg, ?_⟩
    simpa [Ψ'] using hm.Ψg.map (algebraMap c.O (PadicAlgCl l))
  have key : ∀ j : ℤ, j ≤ 0 → ∀ D ∈ PtDer ((Algebra.ofId c.O (PadicAlgCl l)).comp M.x) (PadicAlgCl l),
      HasWt M.𝒜 j D → (∀ y ∈ M.Q.ideal, D y = 0) → D = 0 := by
    intro j hj D hD hw hI
    rw [← hq] at hD
    obtain ⟨F, hF, hFD⟩ := M.der h2 _ hloc D hD hI
    obtain ⟨-, hn, -, -, hdet⟩ := tanCoc_determines S M hl hm F (hF ▸ hloc)
    have hgw : ∀ g, tanCoc F S.r.hom g ∈ gw (PadicAlgCl l) j := by
      intro g a b hab
      have e : ((((S.r.hom g).left⁻¹ : GL (Fin 3) S.R) : Matrix (Fin 3) (Fin 3) S.R).map fun x => (F x).fst) =
          (((push (dualFst F) S.r.hom g).left⁻¹ : GL (Fin 3) (PadicAlgCl l)) :
            Matrix (Fin 3) (Fin 3) (PadicAlgCl l)) := rfl
      rw [hF, hpush, unitaryThreeReflection_left, ← map_inv, tor_val] at e
      obtain ⟨f, hf, hfq⟩ := M.ent g a b
      rw [tanCoc, e, Matrix.mul_diagonal, Matrix.map_apply, ← hfq, hFD, hw _ hab f hf, zero_mul]
    obtain ⟨X, hX⟩ := hrig j hj F hF hgw
    rw [hF, hX, hpush] at hn
    have hT := (normCoc_cob_iff (r0 η Ψ') cc g₁ X (Ne.isUnit two_ne_zero) hm.ηc hm.ηg
      (baseRepGL3_normalised_of_psi_eq_one η Ψ' g₁ hm'.Ψc) (zeta_reducible_rep_eq_sub_inv_and_isUnit η Ψ' cc g₁ hm').2).1 hn
    rw [hpush, coboundary_torus_lie_zero η Ψ' X hT] at hX
    ext y
    have := hdet F rfl 1 0 (by rw [hX]; simp) (M.q y)
    rw [one_mul, zero_mul, add_zero] at this
    exact (hFD y).symm.trans this
  exact ⟨M.one_le, M.smooth, spans_three hi M.𝒜 M.x M.wring.fixed M.Q key⟩
