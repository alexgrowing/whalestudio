import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.MopBase
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot

open Matrix IsLocalRing UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.U3.Mop

private theorem mat_symm {R : Type} [CommRing R] (x : GG 3 R) (h2 : x * x = 1) (hx : x.right = -1) :
    x.mat = Jmat R 3 * x.matᵀ * Jmat R 3 := by
  have h : x.left * theta x.left = 1 := by
    have := congrArg SemidirectProduct.left h2
    rwa [SemidirectProduct.mul_left, hx, sgnAct_neg_one] at this
  have h' : x.left = (theta x.left)⁻¹ := eq_inv_of_mul_eq_one_left h
  have := theta_inv_val x.left
  rw [← h'] at this
  exact this

private theorem norm_iff {G R : Type} [Group G] [CommRing R] (c g₁ : G) (r : G →* GG 3 R) (hc : c * c = 1)
    (hr : (r c).right = -1) : Normalised c g₁ r ↔ ∀ i, nEq c g₁ r i = 0 := by
  have hs := mat_symm (r c) (by rw [← map_mul, hc, map_one]) hr
  have hsym : ∀ i j, (r c).mat i j = (r c).mat j.rev i.rev := by
    intro i j
    conv_lhs => rw [hs]
    fin_cases j <;> simp [Matrix.mul_apply, Jmat, Fin.sum_univ_three]
  constructor
  · rintro ⟨h1, h2, h3⟩ i
    fin_cases i <;> simp [nEq, h1, h2, h3]
  · intro h
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    have h3 := h 3
    have h4 := h 4
    have h5 := h 5
    have h6 := h 6
    have h7 := h 7
    simp [nEq, sub_eq_zero] at h0 h1 h2 h3 h4 h5 h6 h7
    have e12 : (r c).mat 1 2 = (r c).mat 0 1 := hsym 1 2
    have e21 : (r c).mat 2 1 = (r c).mat 1 0 := hsym 2 1
    have e22 : (r c).mat 2 2 = (r c).mat 0 0 := hsym 2 2
    refine ⟨?_, h6, h7⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h0, h1, h2, h3, h4, h5, e12, e21, e22]

private theorem nEq_map {O : Type} [CommRing O] [IsLocalRing O] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    {η : Γ →* ℤˣ} {Ψ : Γ →* Oˣ} (c g₁ : Γ) {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R] [CommRing R']
    [Algebra O R'] [IsCO O R'] (r : GLift O η Ψ R) (f : R →ₐ[O] R') (i : Fin 8) :
    nEq c g₁ (r.map f).hom i = f (nEq c g₁ r.hom i) := by
  have hm : ∀ g, ((r.map f).hom g).mat = (r.hom g).mat.map f := fun g => GG.map_mat (f : R →+* R') (r.hom g)
  fin_cases i <;> simp [nEq, zmat, hm, map_sub, map_one]

private theorem ext_lemma {O : Type} [CommRing O] [IsLocalRing O] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    {η : Γ →* ℤˣ} {Ψ : Γ →* Oˣ} {R : Type} [CommRing R] [Algebra O R] [IsCO O R]
    (a b : GLift O η Ψ R) (h : ∀ x, (a.hom x).mat = (b.hom x).mat) : a = b := by
  apply GLift.ext
  apply MonoidHom.ext
  intro x
  apply SemidirectProduct.ext
  · exact Units.ext (h x)
  · rw [a.hasMult x, b.hasMult x]

private theorem gLift_map_hom_mat_eq_map {O : Type} [CommRing O] [IsLocalRing O] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    {η : Γ →* ℤˣ} {Ψ : Γ →* Oˣ} {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R] [CommRing R']
    [Algebra O R'] [IsCO O R'] (r : GLift O η Ψ R) (f : R →ₐ[O] R') (x : Γ) :
    ((r.map f).hom x).mat = (r.hom x).mat.map f :=
  GG.map_mat (f : R →+* R') (r.hom x)

private theorem comp_lemma_3 {O : Type} [CommRing O] [IsLocalRing O] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    {η : Γ →* ℤˣ} {Ψ : Γ →* Oˣ} {R R' R'' : Type} [CommRing R] [Algebra O R] [IsCO O R] [CommRing R']
    [Algebra O R'] [IsCO O R'] [CommRing R''] [Algebra O R''] [IsCO O R''] (r : GLift O η Ψ R)
    (f : R →ₐ[O] R') (g : R' →ₐ[O] R'') : r.map (g.comp f) = (r.map f).map g := by
  apply ext_lemma
  intro x
  rw [gLift_map_hom_mat_eq_map, gLift_map_hom_mat_eq_map, gLift_map_hom_mat_eq_map]
  ext i j
  simp

private theorem gLift_map_id {O : Type} [CommRing O] [IsLocalRing O] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    {η : Γ →* ℤˣ} {Ψ : Γ →* Oˣ} {R : Type} [CommRing R] [Algebra O R] [IsCO O R]
    (r : GLift O η Ψ R) : r.map (AlgHom.id O R) = r := by
  apply ext_lemma
  intro x
  rw [gLift_map_hom_mat_eq_map]
  ext i j
  simp

theorem UpperTheory.exists_surjection_univ_normCond_ker_span_nEq :
    ∀ {O : Type} [CommRing O] [IsLocalRing O] {Γ : Type} [Group Γ] [TopologicalSpace Γ] {η : Γ →* ℤˣ} {Ψ : Γ →* Oˣ} {P : GCond O η Ψ} (c g₁ : Γ)
          (B : Univ P) (S : Univ (NormCond c g₁ P)), c * c = 1 → η c = -1 →
          ∃ p : B.R →ₐ[O] S.R, Function.Surjective p ∧ B.r.map p = S.r ∧ RingHom.ker p = Ideal.span (Set.range (nEq c g₁ B.r.hom)) := by
  intro O _ _ Γ _ _ η Ψ P c g₁ B S hc hη
  have hr : ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (r : GLift O η Ψ R),
      (r.hom c).right = -1 := fun R _ _ _ r => by rw [r.hasMult c, hη]
  have hNS : NormCond c g₁ P S.R S.r := by
    have h := (S.rep S.R).1 (AlgHom.id O S.R)
    rwa [gLift_map_id] at h
  obtain ⟨p, hp, -⟩ := (B.rep S.R).2 S.r hNS.2
  have hI : Ideal.span (Set.range (nEq c g₁ B.r.hom)) ≤ RingHom.ker p := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker]
    show p (nEq c g₁ B.r.hom i) = 0
    rw [← nEq_map, hp]
    exact (norm_iff c g₁ S.r.hom hc (hr _ S.r)).1 hNS.1 i
  set I := Ideal.span (Set.range (nEq c g₁ B.r.hom)) with hIdef
  haveI : Nontrivial (B.R ⧸ I) :=
    Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top (RingHom.ker_ne_top _) hI)
  haveI : IsCO O (B.R ⧸ I) := co_quot O B.R (B.R ⧸ I) (Ideal.Quotient.mkₐ O I) (Ideal.Quotient.mkₐ_surjective O I)
  have hNq : NormCond c g₁ P (B.R ⧸ I) (B.r.map (Ideal.Quotient.mkₐ O I)) := by
    refine ⟨(norm_iff c g₁ _ hc (hr _ _)).2 (fun i => ?_), (B.rep _).1 _⟩
    rw [nEq_map]
    show Ideal.Quotient.mk I _ = 0
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨i, rfl⟩)
  obtain ⟨s, hs, -⟩ := (S.rep (B.R ⧸ I)).2 _ hNq
  have hsp : s.comp p = Ideal.Quotient.mkₐ O I := by
    obtain ⟨u, -, hu⟩ := (B.rep (B.R ⧸ I)).2 _ hNq.2
    have e1 := hu (s.comp p) (by
      show GLift.map (s.comp p) B.r = _
      rw [comp_lemma_3, hp, hs])
    have e2 := hu (Ideal.Quotient.mkₐ O I) rfl
    rw [e1, e2]
  have hker : RingHom.ker p = I := by
    refine le_antisymm (fun x hx => ?_) hI
    have h0 : Ideal.Quotient.mkₐ O I x = 0 := by
      rw [← hsp, AlgHom.comp_apply, RingHom.mem_ker.1 hx, map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.1 h0
  have hI' : ∀ a ∈ I, p a = 0 := fun a ha => RingHom.mem_ker.1 (hI ha)
  let p' := Ideal.Quotient.liftₐ I p hI'
  have hp'q : ∀ z, p' (Ideal.Quotient.mkₐ O I z) = p z := fun z => by
    show Ideal.Quotient.lift I (p : B.R →+* S.R) hI' (Ideal.Quotient.mk I z) = p z
    exact Ideal.Quotient.lift_mk I _ _
  have hpq : p'.comp (Ideal.Quotient.mkₐ O I) = p := AlgHom.ext hp'q
  have hid : p'.comp s = AlgHom.id O S.R := by
    obtain ⟨u, -, hu⟩ := (S.rep S.R).2 S.r hNS
    have e1 := hu (p'.comp s) (by
      show GLift.map (p'.comp s) S.r = S.r
      rw [comp_lemma_3, hs, ← comp_lemma_3, hpq, hp])
    have e2 := hu (AlgHom.id O S.R) (gLift_map_id _)
    rw [e1, e2]
  refine ⟨p, fun y => ?_, hp, hker⟩
  obtain ⟨z, hz⟩ := Ideal.Quotient.mkₐ_surjective O I (s y)
  refine ⟨z, ?_⟩
  rw [← hp'q, hz]
  exact congrArg (fun f => f y) hid
