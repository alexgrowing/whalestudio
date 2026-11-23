import Mathlib
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

section Restrict

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

def restrictAut (Ω : IntermediateField F E) (τ : Ω ≃ₐ[F] Ω) (N : IntermediateField F E)
    (hN : N ≤ Ω) [Normal F N] : N ≃ₐ[F] N :=
  haveI : Normal F (IntermediateField.restrict hN) :=
    Normal.of_algEquiv (IntermediateField.restrictAlgEquiv hN)
  (IntermediateField.restrictAlgEquiv hN).trans
    ((τ.restrictNormal (IntermediateField.restrict hN)).trans
      (IntermediateField.restrictAlgEquiv hN).symm)

theorem coe_restrictAut (Ω : IntermediateField F E) (τ : Ω ≃ₐ[F] Ω) (N : IntermediateField F E)
    (hN : N ≤ Ω) [Normal F N] (y : N) :
    ((restrictAut Ω τ N hN y : N) : E) = ((τ ⟨y, hN y.2⟩ : Ω) : E) := by
  have : Normal F (IntermediateField.restrict hN) :=
    Normal.of_algEquiv (IntermediateField.restrictAlgEquiv hN)
  set e := IntermediateField.restrictAlgEquiv hN
  have he : ∀ w : N, ((e w : IntermediateField.restrict hN) : Ω) = ⟨w, hN w.2⟩ := fun w => rfl
  set z := τ.restrictNormal (IntermediateField.restrict hN) (e y)
  have h1 : ((z : IntermediateField.restrict hN) : Ω) = τ ⟨y, hN y.2⟩ := by
    have := AlgEquiv.restrictNormal_commutes τ (IntermediateField.restrict hN) (e y)
    rw [← he y]
    exact this
  change ((e.symm z : N) : E) = _
  have h2 : ((e (e.symm z) : IntermediateField.restrict hN) : Ω) = ⟨(e.symm z : E), hN (e.symm z).2⟩ :=
    he _
  rw [AlgEquiv.apply_symm_apply, h1] at h2
  exact (congrArg Subtype.val h2).symm

theorem restrictAut_mul (Ω : IntermediateField F E) (τ₁ τ₂ : Ω ≃ₐ[F] Ω) (N : IntermediateField F E)
    (hN : N ≤ Ω) [Normal F N] :
    restrictAut Ω (τ₁ * τ₂) N hN = restrictAut Ω τ₁ N hN * restrictAut Ω τ₂ N hN := by
  ext y
  rw [AlgEquiv.mul_apply, coe_restrictAut, coe_restrictAut]
  have : (⟨((restrictAut Ω τ₂ N hN y : N) : E), hN (restrictAut Ω τ₂ N hN y).2⟩ : Ω) =
      τ₂ ⟨y, hN y.2⟩ := Subtype.ext (coe_restrictAut Ω τ₂ N hN y)
  rw [this]
  rfl

end Restrict

section Glue

variable {F E : Type*} [Field F] [Field E] [Algebra F E] {ι : Type*}
variable (Ω : IntermediateField F E) (N : ι → IntermediateField F E) (hN : ∀ i, N i ≤ Ω)
  (hdir : Directed (· ≤ ·) N) (hcov : ∀ x ∈ Ω, ∃ i, x ∈ N i) (f : ∀ i, N i →ₐ[F] N i)
  (hf : ∀ i j (h : N i ≤ N j) (x : N i), ((f j ⟨x, h x.2⟩ : N j) : E) = ((f i x : N i) : E))

def glueFun (x : Ω) : E :=
  ((f (hcov x x.2).choose ⟨x, (hcov x x.2).choose_spec⟩ : N (hcov x x.2).choose) : E)

include hdir hf in
theorem glueFun_eq (i : ι) (x : Ω) (hx : (x : E) ∈ N i) :
    glueFun Ω N hcov f x = ((f i ⟨x, hx⟩ : N i) : E) := by
  obtain ⟨j, hj1, hj2⟩ := hdir (hcov x x.2).choose i
  unfold glueFun
  rw [← hf _ j hj1, ← hf i j hj2]

include hN in
theorem glueFun_mem (x : Ω) : glueFun Ω N hcov f x ∈ Ω :=
  hN _ (f _ _).2

def glueHom : Ω →ₐ[F] Ω where
  toFun x := ⟨glueFun Ω N hcov f x, glueFun_mem Ω N hN hcov f x⟩
  map_one' := by
    obtain ⟨i, hi⟩ := hcov 1 (one_mem Ω)
    apply Subtype.ext
    change glueFun Ω N hcov f 1 = ((1 : Ω) : E)
    rw [glueFun_eq Ω N hdir hcov f hf i 1 hi]
    have : (⟨((1 : Ω) : E), hi⟩ : N i) = 1 := rfl
    rw [this, map_one]; rfl
  map_mul' x y := by
    obtain ⟨i, hi⟩ := hcov x x.2
    obtain ⟨j, hj⟩ := hcov y y.2
    obtain ⟨k, hik, hjk⟩ := hdir i j
    apply Subtype.ext
    change glueFun Ω N hcov f (x * y) = glueFun Ω N hcov f x * glueFun Ω N hcov f y
    rw [glueFun_eq Ω N hdir hcov f hf k x (hik hi), glueFun_eq Ω N hdir hcov f hf k y (hjk hj),
      glueFun_eq Ω N hdir hcov f hf k (x * y) (mul_mem (hik hi) (hjk hj))]
    have : (⟨((x * y : Ω) : E), mul_mem (hik hi) (hjk hj)⟩ : N k) =
        ⟨(x : E), hik hi⟩ * ⟨(y : E), hjk hj⟩ := rfl
    rw [this, map_mul]; rfl
  map_zero' := by
    obtain ⟨i, hi⟩ := hcov 0 (zero_mem Ω)
    apply Subtype.ext
    change glueFun Ω N hcov f 0 = ((0 : Ω) : E)
    rw [glueFun_eq Ω N hdir hcov f hf i 0 hi]
    have : (⟨((0 : Ω) : E), hi⟩ : N i) = 0 := rfl
    rw [this, map_zero]; rfl
  map_add' x y := by
    obtain ⟨i, hi⟩ := hcov x x.2
    obtain ⟨j, hj⟩ := hcov y y.2
    obtain ⟨k, hik, hjk⟩ := hdir i j
    apply Subtype.ext
    change glueFun Ω N hcov f (x + y) = glueFun Ω N hcov f x + glueFun Ω N hcov f y
    rw [glueFun_eq Ω N hdir hcov f hf k x (hik hi), glueFun_eq Ω N hdir hcov f hf k y (hjk hj),
      glueFun_eq Ω N hdir hcov f hf k (x + y) (add_mem (hik hi) (hjk hj))]
    have : (⟨((x + y : Ω) : E), add_mem (hik hi) (hjk hj)⟩ : N k) =
        ⟨(x : E), hik hi⟩ + ⟨(y : E), hjk hj⟩ := rfl
    rw [this, map_add]; rfl
  commutes' c := by
    obtain ⟨i, hi⟩ := hcov _ (algebraMap_mem Ω c)
    apply Subtype.ext
    change glueFun Ω N hcov f (algebraMap F Ω c) = ((algebraMap F Ω c : Ω) : E)
    rw [glueFun_eq Ω N hdir hcov f hf i _ hi]
    have : (⟨((algebraMap F Ω c : Ω) : E), hi⟩ : N i) = algebraMap F (N i) c := rfl
    rw [this, AlgHom.commutes]; rfl

theorem coe_glueHom (i : ι) (x : Ω) (hx : (x : E) ∈ N i) :
    ((glueHom Ω N hN hdir hcov f hf x : Ω) : E) = ((f i ⟨x, hx⟩ : N i) : E) :=
  glueFun_eq Ω N hdir hcov f hf i x hx

def glueAut [Algebra.IsAlgebraic F Ω] : Ω ≃ₐ[F] Ω :=
  (Algebra.IsAlgebraic.algEquivEquivAlgHom F Ω).symm (glueHom Ω N hN hdir hcov f hf)

theorem coe_glueAut [Algebra.IsAlgebraic F Ω] (i : ι) (x : Ω) (hx : (x : E) ∈ N i) :
    ((glueAut Ω N hN hdir hcov f hf x : Ω) : E) = ((f i ⟨x, hx⟩ : N i) : E) :=
  coe_glueHom Ω N hN hdir hcov f hf i x hx

end Glue

section AutCongr

variable {F A B : Type*} [Field F] [Field A] [Field B] [Algebra F A] [Algebra F B]

theorem continuous_autCongr (e : A ≃ₐ[F] B) : Continuous (e.autCongr : Gal(A/F) → Gal(B/F)) := by
  apply continuous_of_continuousAt_one e.autCongr (continuousAt_def.mpr _)
  intro U hU
  rw [map_one, krullTopology_mem_nhds_one_iff] at hU
  obtain ⟨E, hE, hsub⟩ := hU
  rw [krullTopology_mem_nhds_one_iff]
  refine ⟨E.map e.symm.toAlgHom, ?_, ?_⟩
  · exact LinearEquiv.finiteDimensional (IntermediateField.equivMap E e.symm.toAlgHom).toLinearEquiv
  · intro σ hσ
    apply hsub
    rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
    intro x hx
    change e (σ (e.symm x)) = x
    rw [hσ (e.symm x) ⟨x, hx, rfl⟩, AlgEquiv.apply_symm_apply]

def autCongrHomeomorph (e : A ≃ₐ[F] B) : Gal(A/F) ≃ₜ* Gal(B/F) where
  toMulEquiv := e.autCongr
  continuous_toFun := continuous_autCongr e
  continuous_invFun := continuous_autCongr e.symm

end AutCongr

end GroundTheory.PAdicHodge
