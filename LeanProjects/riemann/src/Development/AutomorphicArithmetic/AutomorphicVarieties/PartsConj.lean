import Formalism.GaloisCohomology.Statement

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology

namespace UpperTheory.V

section Conj

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

def IsLift (τ : F ≃+* F) (σ : Ω ≃+* Ω) : Prop := ∀ x, σ (algebraMap F Ω x) = algebraMap F Ω (τ x)

variable {τ : F ≃+* F} {σ : Ω ≃+* Ω}

omit [NumberField F] in
theorem IsLift.symm (h : IsLift τ σ) : IsLift τ.symm σ.symm := fun x => by
  rw [RingEquiv.symm_apply_eq, h, RingEquiv.apply_symm_apply]

omit [NumberField F] in
theorem IsLift.trans {τ' : F ≃+* F} {σ' : Ω ≃+* Ω} (h : IsLift τ σ) (h' : IsLift τ' σ') :
    IsLift (τ.trans τ') (σ.trans σ') := fun x => by
  rw [RingEquiv.trans_apply, h, h', RingEquiv.trans_apply]

omit [NumberField F] in
theorem exists_isLift [IsAlgClosure F Ω] (τ : F ≃+* F) : ∃ σ : Ω ≃+* Ω, IsLift τ σ :=
  ⟨IsAlgClosure.equivOfEquiv Ω Ω τ, fun x => IsAlgClosure.equivOfEquiv_algebraMap Ω Ω τ x⟩

def conjGal (h : IsLift τ σ) : G F Ω →* G F Ω where
  toFun g := AlgEquiv.ofRingEquiv (f := (σ.trans g.toRingEquiv).trans σ.symm) fun x => by
    show σ.symm (g (σ (algebraMap F Ω x))) = _
    rw [h, AlgEquiv.commutes, ← h, RingEquiv.symm_apply_apply]
  map_one' := AlgEquiv.ext fun x => σ.symm_apply_apply x
  map_mul' g k := AlgEquiv.ext fun x => by
    show σ.symm (g (k (σ x))) = σ.symm (g (σ (σ.symm (k (σ x)))))
    rw [RingEquiv.apply_symm_apply]

omit [NumberField F] in
theorem conjGal_apply (h : IsLift τ σ) (g : G F Ω) (x : Ω) : conjGal h g x = σ.symm (g (σ x)) := rfl

omit [NumberField F] in
theorem apply_conjGal (h : IsLift τ σ) (g : G F Ω) (x : Ω) : σ (conjGal h g x) = g (σ x) :=
  σ.apply_symm_apply _

theorem continuous_conjGal [IsAlgClosure F Ω] (h : IsLift τ σ) : Continuous (conjGal h) := by
  refine continuous_of_continuousAt_one _ ?_
  rw [ContinuousAt, map_one]
  intro s hs
  obtain ⟨E, hE, hs⟩ := (krullTopology_mem_nhds_one_iff F Ω s).1 hs
  let b := Module.finBasis F E
  have ho : IsOpen (⋂ i, {g : G F Ω | g (σ (b i)) = σ (b i)}) :=
    isOpen_iInter_of_finite fun i => isOpen_setOf_apply (F := F) (σ (b i)) (fun t => t = σ (b i))
  rw [Filter.mem_map]
  refine Filter.mem_of_superset (ho.mem_nhds (Set.mem_iInter.2 fun i => rfl)) fun g hg => hs ?_
  have h1 : ∀ i, conjGal h g (b i) = b i := fun i =>
    σ.injective (by rw [apply_conjGal]; exact Set.mem_iInter.1 hg i)
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have e : (conjGal h g).toLinearMap ∘ₗ E.val.toLinearMap = E.val.toLinearMap :=
    b.ext h1
  exact LinearMap.congr_fun e ⟨x, hx⟩

theorem val_lt_one {A A' : ValuationSubring Ω} (hA : ∀ x, σ x ∈ A' ↔ x ∈ A) (x : Ω) :
    A'.valuation (σ x) < 1 ↔ A.valuation x < 1 := by
  rw [valuation_lt_one_iff' (Ω := Ω), valuation_lt_one_iff' (Ω := Ω), hA, ← map_inv₀, hA,
    map_eq_zero_iff _ σ.injective]

theorem conjGal_mem_Dec (h : IsLift τ σ) {A A' : ValuationSubring Ω} (hA : ∀ x, σ x ∈ A' ↔ x ∈ A) {g : G F Ω}
    (hg : g ∈ Dec (F := F) A') : conjGal h g ∈ Dec (F := F) A := by
  rw [mem_Dec]
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, AlgEquiv.smul_def, ← hA, ← hA,
    apply_conjGal]
  exact apply_mem_iff_of_mem_Dec ((Dec (F := F) A').inv_mem hg) _

theorem conjGal_mem_Ine (h : IsLift τ σ) {A A' : ValuationSubring Ω} (hA : ∀ x, σ x ∈ A' ↔ x ∈ A) {g : G F Ω}
    (hg : g ∈ Ine (F := F) A') : conjGal h g ∈ Ine (F := F) A := by
  refine ⟨conjGal_mem_Dec h hA hg.1, fun x hx => ?_⟩
  rw [← val_lt_one hA, map_sub, apply_conjGal]
  exact hg.2 _ ((A'.valuation_le_one_iff _).2 ((hA x).2 ((A.valuation_le_one_iff _).1 hx)))

def preplace (τ : F ≃+* F) (v : HeightOneSpectrum (𝓞 F)) : HeightOneSpectrum (𝓞 F) :=
  (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv τ)).symm v

omit [NumberField F] in
theorem mem_preplace (τ : F ≃+* F) (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F) :
    x ∈ (preplace τ v).asIdeal ↔ RingOfIntegers.mapRingEquiv τ x ∈ v.asIdeal := Iff.rfl

theorem isPlaceOver_preplace (h : IsLift τ σ) {A A' : ValuationSubring Ω} (hA : ∀ x, σ x ∈ A' ↔ x ∈ A)
    {v : HeightOneSpectrum (𝓞 F)} (hv : IsPlaceOver A' v) : IsPlaceOver A (preplace τ v) := by
  intro x
  rw [mem_preplace, ← hv, ← val_lt_one hA, h]
  rfl

omit [NumberField F] in
theorem preplace_mem_Above (τ : F ≃+* F) (l : ℕ) (v : HeightOneSpectrum (𝓞 F)) :
    preplace τ v ∈ Above F l ↔ v ∈ Above F l := by
  show ((l : ℕ) : 𝓞 F) ∈ (preplace τ v).asIdeal ↔ ((l : ℕ) : 𝓞 F) ∈ v.asIdeal
  rw [mem_preplace, map_natCast]

variable [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]

theorem conjGal_mem_NS (h : IsLift τ σ) {S : Set (HeightOneSpectrum (𝓞 F))} (hS : S = Above F l) {g : G F Ω}
    (hg : g ∈ NS Ω S) : conjGal h g ∈ NS Ω S := by
  have hc : IsClosed (((NS Ω S).comap (conjGal h) : Subgroup (G F Ω)) : Set (G F Ω)) :=
    (isClosed_NS Ω S).preimage (continuous_conjGal h)
  refine Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal ?_) hc hg
  intro k hk
  simp only [Set.mem_iUnion] at hk
  obtain ⟨v, hv, A', hA', hk⟩ := hk
  have hA : ∀ x, σ x ∈ A' ↔ x ∈ A'.comap σ.toRingHom := fun x => Iff.rfl
  show conjGal h k ∈ NS Ω S
  apply Subgroup.le_topologicalClosure
  apply Subgroup.subset_normalClosure
  simp only [Set.mem_iUnion]
  refine ⟨preplace τ v, ?_, A'.comap σ.toRingHom, isPlaceOver_preplace h hA hA', conjGal_mem_Ine h hA hk⟩
  subst hS
  exact fun hh => hv ((preplace_mem_Above τ l v).1 hh)

def conjGS (D : LData F Ω l) (h : IsLift τ σ) :
    GS Ω (D.S : Set (HeightOneSpectrum (𝓞 F))) →* GS Ω (D.S : Set (HeightOneSpectrum (𝓞 F))) :=
  QuotientGroup.map _ _ (conjGal h) fun _ hg => conjGal_mem_NS h D.hS hg

theorem conjGS_toGS (D : LData F Ω l) (h : IsLift τ σ) (g : G F Ω) :
    conjGS D h (toGS Ω _ g) = toGS Ω _ (conjGal h g) := rfl

theorem continuous_conjGS (D : LData F Ω l) (h : IsLift τ σ) : Continuous (conjGS D h) :=
  (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 ((continuous_toGS Ω _).comp (continuous_conjGal h))

theorem chi_toGS (D : LData F Ω l) (g : G F Ω) : D.chi (toGS Ω _ g) = cyclotomicCharacter Ω l g.toRingEquiv :=
  DFunLike.congr_fun D.hchi g

theorem chi_conjGS (D : LData F Ω l) (h : IsLift τ σ) (g : GS Ω (D.S : Set (HeightOneSpectrum (𝓞 F)))) :
    D.chi (conjGS D h g) = D.chi g := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ g
  refine (chi_toGS D (conjGal h g)).trans (Eq.trans ?_ (chi_toGS D g).symm)
  have e : (conjGal h g).toRingEquiv = σ⁻¹ * g.toRingEquiv * σ := rfl
  rw [e, map_mul, map_mul, map_inv, mul_comm, ← mul_assoc, mul_inv_cancel, one_mul]

variable (l) in

def twScal (σ : Ω ≃+* Ω) (e : ℤ) : ℤ_[l] := ((cyclotomicCharacter Ω l σ ^ (-e) : ℤ_[l]ˣ) : ℤ_[l])

theorem qzTw_apply (D : LData F Ω l) (e : ℤ) (g : GS Ω (D.S : Set (HeightOneSpectrum (𝓞 F)))) (m : QZ l) :
    qzTw D e g m = ((D.chi g ^ (-e) : ℤ_[l]ˣ) : ℤ_[l]) • m := rfl

def h1TwistConjByLift (D : LData F Ω l) (e : ℤ) (h : IsLift τ σ) : H1 (qzTw D e) →ₗ[ℤ_[l]] H1 (qzTw D e) :=
  (mapH1 ((qzTw D e).comp (conjGS D h)) (qzTw D e) (twScal l σ e • LinearMap.id) continuous_of_discreteTopology
    (fun g m => by
      show twScal l σ e • qzTw D e (conjGS D h g) m = qzTw D e g (twScal l σ e • m)
      rw [qzTw_apply, qzTw_apply, chi_conjGS, smul_comm])).comp
    (resH1 (qzTw D e) (conjGS D h) (continuous_conjGS D h))

theorem exists_cocycle_h1TwistConjByLift_mk_eq_mk (D : LData F Ω l) (e : ℤ) (h : IsLift τ σ) (z : Z1 (qzTw D e)) :
    ∃ z' : Z1 (qzTw D e), h1TwistConjByLift D e h (Submodule.Quotient.mk z) = Submodule.Quotient.mk z' ∧
      ∀ g, z'.1 g = twScal l σ e • z.1 (conjGS D h g) :=
  ⟨_, rfl, fun _ => rfl⟩

theorem mk_eq_mk_iff {R Γ M : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] (ρ : Representation R Γ M) (z z' : Z1 ρ) :
    (Submodule.Quotient.mk z : H1 ρ) = Submodule.Quotient.mk z' ↔ ∃ m, ∀ g, z.1 g - z'.1 g = ρ g m - m := by
  refine (Submodule.Quotient.eq _).trans ((mem_coboundaries1 _ _).trans ?_)
  first
    | exact Iff.rfl
    | exact ⟨fun ⟨m, hm⟩ => ⟨m, fun g => (hm g).symm⟩, fun ⟨m, hm⟩ => ⟨m, fun g => (hm g).symm⟩⟩

theorem mem_Sha_iff (D : LData F Ω l) (e : ℤ) (x : H1 (qzTw D e)) :
    x ∈ Sha D e ↔ ∀ v, resH1 (qzTw D e) (locFam D.S D.A v) (continuous_locFam D.S D.A v) x = 0 := by
  first
    | exact mem_Sha1 _ _ _ _
    | exact (mem_Sel _ _ _ _ _).trans (forall_congr' fun v => Submodule.mem_bot _)
    | exact (Submodule.mem_iInf _).trans (forall_congr' fun v => LinearMap.mem_ker)
    | (simp [Sha, Sha1, mem_Sel]; done)

theorem res_mk_eq_zero_iff (D : LData F Ω l) (e : ℤ) (v : D.S) (z : Z1 (qzTw D e)) :
    resH1 (qzTw D e) (locFam D.S D.A v) (continuous_locFam D.S D.A v) (Submodule.Quotient.mk z) = 0 ↔
      ∃ m, ∀ g : Dec (F := F) (D.A v), z.1 (toGS Ω _ g.1) = qzTw D e (toGS Ω _ g.1) m - m :=
  (Submodule.Quotient.mk_eq_zero _).trans (mem_coboundaries1 _ _)

theorem h1TwistConjByLift_mul_apply (D : LData F Ω l) (e : ℤ) {τ₁ τ₂ τ₃ : F ≃+* F} {σ₁ σ₂ σ₃ : Ω ≃+* Ω} (h₁ : IsLift τ₁ σ₁)
    (h₂ : IsLift τ₂ σ₂) (h₃ : IsLift τ₃ σ₃) (hσ : σ₃ = σ₂ * σ₁) (x : H1 (qzTw D e)) :
    h1TwistConjByLift D e h₃ x = h1TwistConjByLift D e h₂ (h1TwistConjByLift D e h₁ x) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨z₁, e₁, f₁⟩ := exists_cocycle_h1TwistConjByLift_mk_eq_mk D e h₁ z
  obtain ⟨z₂, e₂, f₂⟩ := exists_cocycle_h1TwistConjByLift_mk_eq_mk D e h₂ z₁
  obtain ⟨z₃, e₃, f₃⟩ := exists_cocycle_h1TwistConjByLift_mk_eq_mk D e h₃ z
  rw [e₁, e₂, e₃]
  congr 1
  refine Subtype.ext (funext fun g => ?_)
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ g
  have e4 : conjGS D h₃ (toGS Ω _ g) = conjGS D h₁ (conjGS D h₂ (toGS Ω _ g)) := by
    rw [conjGS_toGS, conjGS_toGS, conjGS_toGS]
    congr 1
    subst hσ
    rfl
  refine (f₃ _).trans (Eq.trans ?_ (f₂ _).symm)
  rw [f₁, smul_smul]
  refine congrArg₂ (· • ·) ?_ (congrArg z.1 e4)
  rw [twScal, twScal, twScal, hσ, map_mul, mul_zpow, Units.val_mul]

theorem h1TwistConjByLift_eq_self_of_forall_apply_eq (D : LData F Ω l) (e : ℤ) (h : IsLift τ σ) (hτ : ∀ x, τ x = x) (x : H1 (qzTw D e)) :
    h1TwistConjByLift D e h x = x := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨z₁, e₁, f₁⟩ := exists_cocycle_h1TwistConjByLift_mk_eq_mk D e h z
  let g₀ : G F Ω := AlgEquiv.ofRingEquiv (f := σ) fun x => by rw [h, hτ]
  rw [e₁]
  refine (mk_eq_mk_iff _ _ _).2 ⟨z.1 (toGS Ω _ g₀), fun g => ?_⟩
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ g
  have hc : ∀ g k, z.1 (g * k) = z.1 g + qzTw D e g (z.1 k) := ((mem_Z1_iff_cocycle _ z.1).1 z.2).2
  have e1 : toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 F))) g₀ * conjGS D h (toGS Ω _ g) = toGS Ω _ g * toGS Ω _ g₀ := by
    rw [conjGS_toGS, ← map_mul, ← map_mul]
    congr 1
    exact AlgEquiv.ext fun x => apply_conjGal h g x
  have e2 := congrArg z.1 e1
  rw [hc, hc, qzTw_apply, chi_toGS] at e2
  have e3 : z₁.1 (toGS Ω _ g) = z.1 (toGS Ω _ g) + qzTw D e (toGS Ω _ g) (z.1 (toGS Ω _ g₀)) - z.1 (toGS Ω _ g₀) := by
    rw [f₁, ← e2, add_sub_cancel_left]
    rfl
  show z₁.1 (toGS Ω _ g) - z.1 (toGS Ω _ g) = qzTw D e (toGS Ω _ g) (z.1 (toGS Ω _ g₀)) - z.1 (toGS Ω _ g₀)
  rw [e3]
  abel

theorem h1TwistConjByLift_eq_of_isLift_of_isLift (D : LData F Ω l) (e : ℤ) {σ' : Ω ≃+* Ω} (h : IsLift τ σ) (h' : IsLift τ σ') :
    h1TwistConjByLift D e h = h1TwistConjByLift D e h' := by
  refine LinearMap.ext fun x => ?_
  rw [h1TwistConjByLift_mul_apply D e (h.trans h'.symm) h' h (RingEquiv.ext fun y => (σ'.apply_symm_apply _).symm),
    h1TwistConjByLift_eq_self_of_forall_apply_eq D e (h.trans h'.symm) fun y => τ.symm_apply_apply y]

theorem h1TwistConjByLift_mem_sha_of_mem_sha (D : LData F Ω l) (e : ℤ) (h : IsLift τ σ) {x : H1 (qzTw D e)} (hx : x ∈ Sha D e) :
    h1TwistConjByLift D e h x ∈ Sha D e := by
  rw [mem_Sha_iff] at hx ⊢
  intro v
  have hw : preplace τ v.1 ∈ D.S := by
    rw [← Finset.mem_coe, D.hS, preplace_mem_Above, ← D.hS]
    exact v.2
  let w : D.S := ⟨_, hw⟩
  have hA : ∀ x, σ x ∈ D.A v ↔ x ∈ (D.A v).comap σ.toRingHom := fun x => Iff.rfl
  obtain ⟨g₀, hg₀⟩ := exists_smul_eq_of_isPlaceOver (F := F) (D.hA w) (isPlaceOver_preplace h hA (D.hA v))
  have h' : IsLift τ (g₀.toRingEquiv.trans σ) := fun y => by
    rw [RingEquiv.trans_apply, ← h]
    exact congrArg σ (g₀.commutes y)
  have hA' : ∀ x, (g₀.toRingEquiv.trans σ) x ∈ D.A v ↔ x ∈ D.A w := fun x => by
    refine (hA (g₀ x)).trans ?_
    rw [← hg₀, ← AlgEquiv.smul_def]
    exact ValuationSubring.smul_mem_pointwise_smul_iff
  rw [h1TwistConjByLift_eq_of_isLift_of_isLift D e h h']
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨z₁, e₁, f₁⟩ := exists_cocycle_h1TwistConjByLift_mk_eq_mk D e h' z
  obtain ⟨m, hm⟩ := (res_mk_eq_zero_iff D e w z).1 (hx w)
  rw [e₁]
  refine (res_mk_eq_zero_iff D e v z₁).2 ⟨twScal l (g₀.toRingEquiv.trans σ) e • m, fun g => ?_⟩
  rw [f₁, conjGS_toGS, hm ⟨_, conjGal_mem_Dec h' hA' g.2⟩, ← conjGS_toGS D h', qzTw_apply, chi_conjGS, map_smul,
    smul_sub, qzTw_apply]

def galoisActionOnCohomology (D : LData F Ω l) (e : ℤ) (τ : F ≃+* F) : Module.End ℤ_[l] (H1 (qzTw D e)) :=
  h1TwistConjByLift D e (exists_isLift (Ω := Ω) τ).choose_spec

theorem galois_action_cohomology_eq_conj (D : LData F Ω l) (e : ℤ) (h : IsLift τ σ) : galoisActionOnCohomology D e τ = h1TwistConjByLift D e h :=
  h1TwistConjByLift_eq_of_isLift_of_isLift D e _ h

theorem galois_action_cohomology_one (D : LData F Ω l) (e : ℤ) : galoisActionOnCohomology D e (1 : F ≃+* F) = 1 :=
  LinearMap.ext fun x => h1TwistConjByLift_eq_self_of_forall_apply_eq D e _ (fun _ => rfl) x

theorem galois_action_cohomology_mul (D : LData F Ω l) (e : ℤ) (τ₁ τ₂ : F ≃+* F) : galoisActionOnCohomology D e (τ₁ * τ₂) = galoisActionOnCohomology D e τ₁ * galoisActionOnCohomology D e τ₂ := by
  obtain ⟨σ₁, h₁⟩ := exists_isLift (Ω := Ω) τ₁
  obtain ⟨σ₂, h₂⟩ := exists_isLift (Ω := Ω) τ₂
  rw [galois_action_cohomology_eq_conj D e h₁, galois_action_cohomology_eq_conj D e h₂, galois_action_cohomology_eq_conj D e (τ := τ₁ * τ₂) (h₂.trans h₁)]
  exact LinearMap.ext fun x => h1TwistConjByLift_mul_apply D e h₂ h₁ _ rfl x

theorem galois_action_preserves_sha (D : LData F Ω l) (e : ℤ) (τ : F ≃+* F) {x : H1 (qzTw D e)} (hx : x ∈ Sha D e) :
    galoisActionOnCohomology D e τ x ∈ Sha D e :=
  h1TwistConjByLift_mem_sha_of_mem_sha D e _ hx

end Conj

end UpperTheory.V

end
