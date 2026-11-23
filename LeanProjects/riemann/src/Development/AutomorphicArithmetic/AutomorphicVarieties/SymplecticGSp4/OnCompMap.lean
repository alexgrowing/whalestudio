import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LocDefs

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

namespace UpperTheory.V.GradeZeroInterpolatingElement

section

variable {R R' : Type} [CommRing R] [CommRing R']

private theorem adj_map' (f : R →+* R') (X : M4 R) : adj (f.mapMatrix X) = f.mapMatrix (adj X) := by
  ext i j
  simp [adj_apply, RingHom.mapMatrix_apply]

private theorem smul_map' (f : R →+* R') (a : R) (X : M4 R) : f.mapMatrix (a • X) = f a • f.mapMatrix X := by
  ext i j
  simp [RingHom.mapMatrix_apply]

private theorem isGSp_map (f : R →+* R') {ν : R} {g : M4 R} (h : IsGSp ν g) : IsGSp (f ν) (f.mapMatrix g) := by
  unfold IsGSp at h ⊢
  have h2 := congrArg f.mapMatrix h
  rw [map_mul, smul_map', map_one, ← adj_map'] at h2
  exact h2

private theorem aeval_map' (f : R →+* R') (X : M4 R) (p : Polynomial R) :
    Polynomial.aeval (f.mapMatrix X) (p.map f) = f.mapMatrix (Polynomial.aeval X p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.map_add, map_add, map_add, hp, hq, map_add]
  | monomial n a =>
    rw [Polynomial.map_monomial, Polynomial.aeval_monomial, Polynomial.aeval_monomial, map_mul, map_pow]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.algebraMap_matrix_apply]
    split_ifs <;> simp

private theorem prj_map (f : R →+* R') (c : Fin 4 → R) (X : M4 R) (i : Fin 4) :
    prj (fun a => f (c a)) (f.mapMatrix X) i = f.mapMatrix (prj c X i) := by
  simp only [prj]
  rw [← aeval_map']
  congr 1
  simp [Polynomial.map_prod]

private theorem ord_map {H : Type} [Group H] (f : R →+* R') {I : Subgroup H} {ps : Fin 4 → H → R} {s₀ : H}
    {r : H →* M4 R} {r' : H →* M4 R'} (hr : ∀ g, r' g = f.mapMatrix (r g)) {ps' : Fin 4 → H → R'}
    (hps : ∀ i g, ps' i g = f (ps i g)) (h : Ord I ps s₀ r) : Ord I ps' s₀ r' := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [hr, hps]
    rw [RingHom.mapMatrix_apply, Matrix.charpoly_map, h.charpoly, Polynomial.map_prod]
    simp
  · intro g i j hij
    simp only [hr, hps]
    rw [prj_map, prj_map, ← map_mul, ← map_mul, h.stable g i j hij, map_zero]
  · intro s hs i
    simp only [hr, hps]
    have e : f.mapMatrix (r s) - f (ps i s) • (1 : M4 R') = f.mapMatrix (r s - ps i s • 1) := by
      rw [map_sub, smul_map', map_one]
    rw [prj_map, e, ← map_mul, ← map_mul, h.inert s hs i, map_zero]

end

section

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c)
  {R : Type} [CommRing R] [Algebra c.O R] [IsCO c.O R] {R' : Type} [CommRing R'] [Algebra c.O R'] [IsCO c.O R']

private theorem condL_map (f : R →ₐ[c.O] R') (ρ : Lift c.O (D.rbarAt l) R) (h : D.condL R ρ) :
    D.condL R' (ρ.map f) := by
  unfold Raw.condL at h ⊢
  obtain ⟨h1, h2⟩ := h
  have hr : ∀ g, (ρ.map f).hom g = (f : R →+* R').mapMatrix (ρ.hom g) := by
    intro g
    ext a b
    rw [Lift.map_hom]
    rfl
  refine ⟨fun g => ?_, ord_map (f : R →+* R') hr (fun i g => (f.commutes _).symm) h2⟩
  rw [hr, ← f.commutes]
  exact isGSp_map (f : R →+* R') (h1 g)

private theorem condP_map (p : ℕ) (f : R →ₐ[c.O] R') (ρ : Lift c.O (D.rbarAt p) R) (h : D.condP p R ρ) :
    D.condP p R' (ρ.map f) := by
  refine ⟨fun g => ?_, fun g hg => ?_⟩
  · have := isGSp_map (f : R →+* R') (h.1 g)
    rw [RingHom.coe_coe, f.commutes] at this
    exact this
  · show (f : R →+* R').mapMatrix (ρ.hom g) = 1
    rw [h.2 g hg, map_one]

private theorem mult_map (f : R →ₐ[c.O] R') (ρ : Lift c.O D.rbar R) (h : D.Mult ρ.hom) : D.Mult (ρ.map f).hom := by
  intro g
  have hr : (ρ.map f).hom g = (f : R →+* R').mapMatrix (ρ.hom g) := by
    ext a b
    rw [Lift.map_hom]
    rfl
  rw [hr, ← f.commutes]
  exact isGSp_map (f : R →+* R') (h g)

private theorem unr_map (f : R →ₐ[c.O] R') (ρ : Lift c.O D.rbar R) (h : D.UnrT ρ.hom 1) :
    D.UnrT (ρ.map f).hom 1 := by
  intro A hA g hg h1
  show (f : R →+* R').mapMatrix (ρ.hom g) = 1
  rw [h A hA g hg h1, map_one]

private theorem hEl_map (f : R →ₐ[c.O] R') (ρ : Lift c.O D.rbar R) (i j : Fin 4) :
    D.hEl (ρ.map f).hom i j = f (D.hEl ρ.hom i j) := by
  simp [Raw.hEl, Lift.map_hom, map_add, map_mul, f.commutes]

private theorem loc_map (f : R →ₐ[c.O] R') (ρ : Lift c.O D.rbar R) (v : ℕ) :
    D.loc (ρ.map f) v = (D.loc ρ v).map f := by
  apply Lift.ext
  rfl

private theorem nrm_map (f : R →ₐ[c.O] R') (ρ : Lift c.O D.rbar R) (h : D.Nrm ρ.hom) : D.Nrm (ρ.map f).hom := by
  refine ⟨fun i j hij => ?_, ?_, ?_⟩
  · rw [Lift.map_hom, h.1 i j hij, map_zero]
  · rw [hEl_map, h.2.1, map_zero]
  · rw [hEl_map, h.2.2, map_zero]

end

private theorem onComp_map {O : Type} [CommRing O] [IsLocalRing O] {Γ ι : Type} [Group Γ] [TopologicalSpace Γ]
    [Fintype ι] [DecidableEq ι] {rbar : Γ →* Matrix ι ι (ResidueField O)} {P : Cond O rbar} {ρ₀ : Γ →* Matrix ι ι O}
    {R : Type} [CommRing R] [Algebra O R] [IsCO O R] {R' : Type} [CommRing R'] [Algebra O R'] [IsCO O R']
    (f : R →ₐ[O] R') {r : Lift O rbar R} (h : OnComp P ρ₀ r) : OnComp P ρ₀ (r.map f) := by
  obtain ⟨B, i1, i2, i3, i4, ρ', hP, hρ, y, hy⟩ := h
  refine ⟨B, i1, i2, i3, i4, ρ', hP, hρ, f.comp y, ?_⟩
  subst hy
  apply Lift.ext
  ext g a b
  simp [Lift.map_hom]

end UpperTheory.V.GradeZeroInterpolatingElement

theorem UpperTheory.V.GradeZeroInterpolatingElement.ptMap :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (R : Type) [CommRing R] [Algebra c.O R] [IsCO c.O R] (ρ : Lift c.O D.rbar R), (D.IsPt ρ → D.IsEq ρ) ∧ ∀ (R' : Type) [CommRing R'] [Algebra c.O R'] [IsCO c.O R'] (f : R →ₐ[c.O] R'), (D.IsPt ρ → D.IsPt (ρ.map f)) ∧ (D.IsEq ρ → D.IsEq (ρ.map f)) := by
  intro Ω _ _ _ l _ c D _ R _ _ _ ρ
  have hL : ∀ {S : Type} [CommRing S] [Algebra c.O S] [IsCO c.O S] (r : Lift c.O (D.rbarAt l) S),
      OnComp D.condL (D.r0At l) r → D.condL S r := by
    intro S _ _ _ r hr
    obtain ⟨B, i1, i2, i3, i4, ρ', hP, _, y, rfl⟩ := hr
    exact condL_map D y ρ' hP
  have hP : ∀ (p : ℕ) {S : Type} [CommRing S] [Algebra c.O S] [IsCO c.O S] (r : Lift c.O (D.rbarAt p) S),
      OnComp (D.condP p) (D.r0At p) r → D.condP p S r := by
    intro p S _ _ _ r hr
    obtain ⟨B, i1, i2, i3, i4, ρ', hQ, _, y, rfl⟩ := hr
    exact condP_map D p y ρ' hQ
  refine ⟨fun h => ⟨h.mult, h.unr, h.nrm, hL _ h.atL, fun p hp => hP p _ (h.atP p hp)⟩, ?_⟩
  intro R' _ _ _ f
  refine ⟨fun h => ⟨mult_map D f ρ h.mult, unr_map D f ρ h.unr, nrm_map D f ρ h.nrm, ?_, fun p hp => ?_⟩,
    fun h => ⟨mult_map D f ρ h.mult, unr_map D f ρ h.unr, nrm_map D f ρ h.nrm, ?_, fun p hp => ?_⟩⟩
  · rw [loc_map]
    exact onComp_map f h.atL
  · rw [loc_map]
    exact onComp_map f (h.atP p hp)
  · rw [loc_map]
    exact condL_map D f _ h.atL
  · rw [loc_map]
    exact condP_map D p f _ (h.atP p hp)
