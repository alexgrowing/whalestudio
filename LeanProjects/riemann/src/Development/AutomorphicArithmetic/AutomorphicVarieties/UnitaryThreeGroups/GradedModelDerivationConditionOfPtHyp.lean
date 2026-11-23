import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Rigid0
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ModelSigns
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.TanDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.NormCob
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ZetaReducibleRepEqSubInvAndIsUnit

open Matrix IsLocalRing UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.HV

section SlopeTestRemainingChoices

variable {O A K : Type} [CommRing O] [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜]
  [Field K] [Algebra O K]

private theorem exists_twist (t : Kˣ) (D : A →ₗ[O] K) :
    ∃ E : A →ₗ[O] K, ∀ j, ∀ a ∈ 𝒜 j, E a = ((t ^ j : Kˣ) : K) * D a := by
  classical
  refine ⟨(DirectSum.toModule O ℤ K (fun j => ((t ^ j : Kˣ) : K) • (D ∘ₗ (𝒜 j).subtype))) ∘ₗ
    (DirectSum.decomposeLinearEquiv 𝒜).toLinearMap, ?_⟩
  intro j a ha
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, DirectSum.decomposeLinearEquiv_apply,
    DirectSum.decompose_of_mem 𝒜 ha]
  rw [← DirectSum.lof_eq_of O, DirectSum.toModule_lof]
  simp [smul_eq_mul]

private theorem act_tz (t : Kˣ) (ξ : A →ₐ[O] K) {j : ℤ} {a : A} (ha : a ∈ 𝒜 j) :
    act 𝒜 (tz t) ξ a = ((t ^ j : Kˣ) : K) * ξ a := act_of_mem 𝒜 _ ξ ha

private theorem twist_der (t : Kˣ) (ξ : A →ₐ[O] K) (D E : A →ₗ[O] K) (hD : D ∈ PtDer ξ K)
    (hE : ∀ j, ∀ a ∈ 𝒜 j, E a = ((t ^ j : Kˣ) : K) * D a) : E ∈ PtDer (act 𝒜 (tz t) ξ) K := by
  have hD' : ∀ f g : A, D (f * g) = ξ f • D g + ξ g • D f := hD
  show ∀ f g : A, E (f * g) = act 𝒜 (tz t) ξ f • E g + act 𝒜 (tz t) ξ g • E f
  intro f g
  refine DirectSum.Decomposition.inductionOn 𝒜 (motive := fun f => E (f * g) = act 𝒜 (tz t) ξ f • E g + act 𝒜 (tz t) ξ g • E f) ?_ ?_ ?_ f
  · simp
  · intro i a
    refine DirectSum.Decomposition.inductionOn 𝒜 (motive := fun g => E (a * g) = act 𝒜 (tz t) ξ a • E g + act 𝒜 (tz t) ξ g • E a) ?_ ?_ ?_ g
    · simp
    · intro j b
      have hab : (a : A) * b ∈ 𝒜 (i + j) := SetLike.GradedMul.mul_mem a.2 b.2
      rw [hE _ _ hab, hE _ _ b.2, hE _ _ a.2, act_tz 𝒜 t ξ a.2, act_tz 𝒜 t ξ b.2, hD', _root_.zpow_add, Units.val_mul]
      simp only [smul_eq_mul]
      ring
    · intro g g' h h'
      simp only [mul_add, map_add, smul_add, add_smul, smul_eq_mul] at h h' ⊢
      rw [h, h']
      ring
  · intro f f' h h'
    simp only [add_mul, map_add, smul_add, add_smul, smul_eq_mul] at h h' ⊢
    rw [h, h']
    ring

omit [GradedAlgebra 𝒜] in
private theorem twist_kills {x : A →ₐ[O] O} {r s r' s' m : ℕ} (Q : Eqns 𝒜 x r s r' s' m) (t : Kˣ)
    (ξ : A →ₐ[O] K) (D E : A →ₗ[O] K) (hξ : OnS Q.ideal ξ) (hE' : E ∈ PtDer ξ K)
    (hE : ∀ j, ∀ a ∈ 𝒜 j, E a = ((t ^ j : Kˣ) : K) * D a) (hD : ∀ y ∈ Q.ideal, D y = 0) :
    ∀ y ∈ Q.ideal, E y = 0 := by
  intro y hy
  have hξ' : ∀ f ∈ Q.ideal, ξ f = 0 := hξ
  have hE'' : ∀ f g : A, E (f * g) = ξ f • E g + ξ g • E f := hE'
  have hgen : ∀ z ∈ (Set.range Q.F ∪ Set.range Q.G ∪ Set.range Q.E ∪ Set.range Q.E' ∪ Set.range Q.Z), E z = 0 := by
    intro z hz
    have hzI : z ∈ Q.ideal := Ideal.subset_span hz
    obtain ⟨j, hj⟩ : ∃ j, z ∈ 𝒜 j := by
      rcases hz with (((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩
      exacts [⟨_, Q.hF i⟩, ⟨_, Q.hG i⟩, ⟨_, Q.hE i⟩, ⟨_, Q.hE' i⟩, ⟨_, (Q.hZ i).1⟩]
    rw [hE j z hj, hD z hzI, mul_zero]
  have hy' : y ∈ Submodule.span A (Set.range Q.F ∪ Set.range Q.G ∪ Set.range Q.E ∪ Set.range Q.E' ∪ Set.range Q.Z) := hy
  clear hy
  induction hy' using Submodule.span_induction with
  | mem z hz => exact hgen z hz
  | zero => simp
  | add a b _ _ ha hb => simp [ha, hb]
  | smul a b hb hb0 =>
    rw [smul_eq_mul, hE'', hb0, hξ' b hb]
    simp

private theorem cob_smul {G C : Type} [Group G] [CommRing C] {m : ℕ} (r : G →* GG m C) (a : C)
    (X : Matrix (Fin m) (Fin m) C) : cob r (a • X) = a • cob r X := by
  funext g
  simp only [cob, map_smul, Pi.smul_apply, smul_sub]

private theorem zmat_map {G R R' : Type} [Group G] [CommRing R] [CommRing R'] (f : R →+* R') (r : G →* GG 3 R)
    (c g₁ : G) (a b : Fin 3) : zmat c g₁ ((GG.map f).comp r) a b = f (zmat c g₁ r a b) := by
  simp [zmat]

private theorem normalised_map {G R R' : Type} [Group G] [CommRing R] [CommRing R'] (f : R →+* R')
    (r : G →* GG 3 R) (c g₁ : G) (h : Normalised c g₁ r) : Normalised c g₁ ((GG.map f).comp r) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [GG.map_mat, h.atc]
  · rw [zmat_map, h.z12, map_zero]
  · rw [zmat_map, h.z21, map_zero]

private theorem isUnit_zeta {O : Type} [CommRing O] [IsLocalRing O] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    {η : Γ →* ℤˣ} {Ψ : Γ →* Oˣ} {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (r : GLift O η Ψ R)
    {c g₁ : Γ} (h : Marks η Ψ c g₁) : IsUnit (zeta c g₁ r.hom) := by
  have hm : Marks η (barChar O Ψ) c g₁ := by
    refine ⟨h.csq, h.ηc, by simp [barChar, h.Ψc], h.ηg, ?_⟩
    have := h.Ψg.map (residue O)
    rw [map_sub, map_pow, map_one] at this
    exact this
  have h1 := (zeta_reducible_rep_eq_sub_inv_and_isUnit η (barChar O Ψ) c g₁ hm).2
  have h2 : (GG.map (res O R : R →+* ResidueField O)).comp r.hom = r0 η (barChar O Ψ) :=
    MonoidHom.ext r.red
  rw [← h2, zeta, zmat_map] at h1
  by_contra hn
  have h3 : res O R (zeta c g₁ r.hom) = 0 := (res_eq_zero_iff O R _).2 hn
  exact h1.ne_zero h3

end SlopeTestRemainingChoices

theorem UpperTheory.V.U3.gradedModel_derivationCondition_of_ptHyp :
    ∀ {l : ℕ} [Fact l.Prime] {c : Coef l} {Γ H : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
      {η : Γ →* ℤˣ} {Ψ : Γ →* (c.O)ˣ} {N : Set Γ} {ι : H →* Γ} {hι : Continuous ι}
      {U : Univ (GCond.noCondition c.O (η.comp ι) (Ψ.comp ι))} {I : Ideal U.R} {cc g₁ : Γ} (S : SRing N hι U I cc g₁) (M : Model S (PadicAlgCl l)), l ≠ 2 → Marks η Ψ cc g₁ →
      M2 M.𝒜 M.Q.ideal → PtHyp η S.r.hom M.x₀ → M4 M.𝒜 (PadicAlgCl l) M.Q.ideal := by
  intro l _ c Γ H _ _ _ _ _ _ η Ψ N ι hι U I cc g₁ S M hl hm hM2 hpt
  intro ξ hξ hsign D hD D' hD' hDI hD'I
  obtain ⟨t, f, hf, hact⟩ := M.pts hM2 ξ hξ
  obtain ⟨E, hE⟩ := exists_twist M.𝒜 t D
  obtain ⟨E', hE'⟩ := exists_twist M.𝒜 t D'
  have hEd : E ∈ PtDer (f.comp M.q) (PadicAlgCl l) := hact ▸ twist_der M.𝒜 t ξ D E hD hE
  have hE'd : E' ∈ PtDer (f.comp M.q) (PadicAlgCl l) := hact ▸ twist_der M.𝒜 t ξ D' E' hD' hE'
  have hon : OnS M.Q.ideal (f.comp M.q) := by
    intro y hy
    have : M.q y = 0 := by
      rw [← RingHom.mem_ker, M.ker_q]
      exact hy
    simp [this]
  have hEI : ∀ y ∈ M.Q.ideal, E y = 0 := twist_kills M.𝒜 M.Q t (f.comp M.q) D E hon hEd hE hDI
  have hE'I : ∀ y ∈ M.Q.ideal, E' y = 0 := twist_kills M.𝒜 M.Q t (f.comp M.q) D' E' hon hE'd hE' hD'I
  obtain ⟨F, hF, hFE⟩ := M.der hM2 f hf E hEd hEI
  obtain ⟨F', hF', hFE'⟩ := M.der hM2 f hf E' hE'd hE'I
  have htne : ∀ j : ℤ, ((t ^ j : (PadicAlgCl l)ˣ) : PadicAlgCl l) ≠ 0 := fun j => Units.ne_zero _
  have hneg : NegZero M.𝒜 (f.comp M.q) ↔ NegZero M.𝒜 ξ := by
    rw [← hact]
    constructor
    · intro h j hj y hy
      have := h j hj y hy
      rw [act_tz M.𝒜 t ξ hy] at this
      exact (mul_eq_zero.1 this).resolve_left (htne j)
    · intro h j hj y hy
      rw [act_tz M.𝒜 t ξ hy, h j hj y hy, mul_zero]
  have hpos : PosZero M.𝒜 (f.comp M.q) ↔ PosZero M.𝒜 ξ := by
    rw [← hact]
    constructor
    · intro h j hj y hy
      have := h j hj y hy
      rw [act_tz M.𝒜 t ξ hy] at this
      exact (mul_eq_zero.1 this).resolve_left (htne j)
    · intro h j hj y hy
      rw [act_tz M.𝒜 t ξ hy, h j hj y hy, mul_zero]
  have hsg := model_signs S M hl hm f hf
  have htwo : TwoPt η S.r.hom f :=
    ⟨hf, fun h => hsign.1 (hneg.1 (hsg.1.2 h)), fun h => hsign.2 (hpos.1 (hsg.2.1.2 h))⟩
  have hrig := hpt.rigid f htwo
  obtain ⟨X, hX⟩ := hrig F hF
  obtain ⟨X', hX'⟩ := hrig F' hF'
  have hN0 := ((S.rep S.R).1 (AlgHom.id _ _)).1
  have hN : Normalised cc g₁ S.r.hom := by
    refine ⟨?_, ?_, ?_⟩
    · have := hN0.atc
      simpa [GLift.map, GG.map_mat] using this
    · have := hN0.z12
      simp only [GLift.map] at this
      rw [zmat_map ((AlgHom.id c.O S.R : S.R →ₐ[c.O] S.R) : S.R →+* S.R)] at this
      simpa using this
    · have := hN0.z21
      simp only [GLift.map] at this
      rw [zmat_map ((AlgHom.id c.O S.R : S.R →ₐ[c.O] S.R) : S.R →+* S.R)] at this
      simpa using this
  have hright : ∀ g, (S.r.hom g).right = η g := by
    intro g
    have := congrArg SemidirectProduct.right (S.r.red g)
    simpa [GG.map, SemidirectProduct.map_right, rbar, r0] using this
  have hc : (push f S.r.hom cc).right = -1 := by
    simp [push, GG.map, SemidirectProduct.map_right, hright, hm.ηc]
  have hg : (push f S.r.hom g₁).right = 1 := by
    simp [push, GG.map, SemidirectProduct.map_right, hright, hm.ηg]
  have hPN : Normalised cc g₁ (push f S.r.hom) := normalised_map (f : S.R →+* PadicAlgCl l) S.r.hom cc g₁ hN
  have hz : IsUnit (zeta cc g₁ (push f S.r.hom)) := by
    have := (isUnit_zeta S.r hm).map (f : S.R →+* PadicAlgCl l)
    simpa [zeta, push, zmat_map] using this
  have h2 : IsUnit (2 : PadicAlgCl l) := isUnit_iff_ne_zero.2 two_ne_zero
  have hdet := tanCoc_determines S M hl hm F (hF ▸ hf)
  have hdet' := tanCoc_determines S M hl hm F' (hF' ▸ hf)
  have hXm : X ∈ unitaryThreeTorusLieAlgebra (PadicAlgCl l) := by
    have := hdet.2.1
    rw [hF, hX] at this
    exact (normCoc_cob_iff _ cc g₁ X h2 hc hg hPN hz).1 this
  have hX'm : X' ∈ unitaryThreeTorusLieAlgebra (PadicAlgCl l) := by
    have := hdet'.2.1
    rw [hF', hX'] at this
    exact (normCoc_cob_iff _ cc g₁ X' h2 hc hg hPN hz).1 this
  obtain ⟨x, rfl⟩ := Submodule.mem_span_singleton.1 hXm
  obtain ⟨x', rfl⟩ := Submodule.mem_span_singleton.1 hX'm
  obtain ⟨a, a', hne, hrel⟩ : ∃ a a' : PadicAlgCl l, (a ≠ 0 ∨ a' ≠ 0) ∧
      a • tanCoc F S.r.hom + a' • tanCoc F' S.r.hom = 0 := by
    rw [hX, hX', cob_smul, cob_smul]
    by_cases hx' : x' = 0
    · refine ⟨0, 1, Or.inr one_ne_zero, ?_⟩
      simp [hx']
    · refine ⟨x', -x, Or.inl hx', ?_⟩
      funext g
      simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_smul]
      rw [← add_smul]
      have : x' * x + -x * x' = 0 := by ring
      rw [this, zero_smul]
  have hall := hdet.2.2.2.2 F' (by rw [hF, hF']) a a' hrel
  have hEE : ∀ y : M.A, a * E y + a' * E' y = 0 := by
    intro y
    rw [← hFE y, ← hFE' y]
    exact hall (M.q y)
  refine ⟨a, a', hne, ?_⟩
  apply LinearMap.ext
  intro y
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.zero_apply, smul_eq_mul]
  refine DirectSum.Decomposition.inductionOn M.𝒜 (motive := fun y => a * D y + a' * D' y = 0) ?_ ?_ ?_ y
  · simp
  · intro j z
    have h := hEE z
    rw [hE j z z.2, hE' j z z.2] at h
    have h' : ((t ^ j : (PadicAlgCl l)ˣ) : PadicAlgCl l) * (a * D z + a' * D' z) = 0 := by
      rw [← h]
      ring
    exact (mul_eq_zero.1 h').resolve_left (htne j)
  · intro y y' h h'
    simp only [map_add]
    linear_combination h + h'
