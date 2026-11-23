import Mathlib
import GroundTheory.PAdicHodge.FWNatural
import GroundTheory.PAdicHodge.FWGlue
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

theorem le_algebraicClosure_of_finiteDimensional {F E : Type*} [Field F] [Field E] [Algebra F E]
    (L : IntermediateField F E) [FiniteDimensional F L] : L ≤ algebraicClosure F E :=
  le_algebraicClosure F E L

variable {K C : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField C] [IsUltrametricDist C] [NormedAlgebra K C] [IsAlgClosed C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField C p]

local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "C♭" => Tilt C NormedField.valuation (normInteger C) normInteger_integers p

variable (K C p) in

def FiniteGaloisTilt : Type _ :=
  {N : IntermediateField K♭ C♭ // FiniteDimensional K♭ N ∧ IsGalois K♭ N}

namespace FiniteGaloisTilt

instance (N : FiniteGaloisTilt K C p) : FiniteDimensional K♭ N.1 := N.2.1
instance (N : FiniteGaloisTilt K C p) : IsGalois K♭ N.1 := N.2.2
instance (N : FiniteGaloisTilt K C p) : IsGalois K (untiltField K C p N.1) :=
  isGalois_untiltField N.1

omit [IsAlgClosed C] in
theorem le_algebraicClosure (N : FiniteGaloisTilt K C p) : N.1 ≤ algebraicClosure K♭ C♭ :=
  le_algebraicClosure_of_finiteDimensional N.1

omit [IsAlgClosed C] in
theorem untiltField_le_algebraicClosure (N : FiniteGaloisTilt K C p) :
    untiltField K C p N.1 ≤ algebraicClosure K C :=
  le_algebraicClosure_of_finiteDimensional _

theorem exists_le (M : IntermediateField K♭ C♭) [FiniteDimensional K♭ M] :
    ∃ N : FiniteGaloisTilt K C p, M ≤ N.1 := by
  have : PerfectField K♭ := PerfectRing.toPerfectField K♭ p
  obtain ⟨N, hMN, hN, hgal⟩ := exists_isGalois_le M
  exact ⟨⟨N, hN, hgal⟩, hMN⟩

theorem directed : Directed (· ≤ ·) (fun N : FiniteGaloisTilt K C p => N.1) := fun N₁ N₂ => by
  obtain ⟨N, hN⟩ := exists_le (K := K) (C := C) (p := p) (N₁.1 ⊔ N₂.1)
  exact ⟨N, le_sup_left.trans hN, le_sup_right.trans hN⟩

theorem directed_untiltField :
    Directed (· ≤ ·) (fun N : FiniteGaloisTilt K C p => untiltField K C p N.1) := fun N₁ N₂ => by
  obtain ⟨N, h1, h2⟩ := directed N₁ N₂
  exact ⟨N, untiltField_mono h1, untiltField_mono h2⟩

theorem exists_mem (y : C♭) (hy : y ∈ algebraicClosure K♭ C♭) :
    ∃ N : FiniteGaloisTilt K C p, y ∈ N.1 := by
  have hint : IsIntegral K♭ y := ((mem_algebraicClosure_iff).1 hy).isIntegral
  have : FiniteDimensional K♭ (IntermediateField.adjoin K♭ {y}) := IntermediateField.adjoin.finiteDimensional hint
  obtain ⟨N, hN⟩ := exists_le (K := K) (C := C) (p := p) (IntermediateField.adjoin K♭ {y})
  exact ⟨N, hN (IntermediateField.mem_adjoin_simple_self K♭ y)⟩

theorem exists_mem_untiltField (x : C) (hx : x ∈ algebraicClosure K C) :
    ∃ N : FiniteGaloisTilt K C p, x ∈ untiltField K C p N.1 := by
  have hint : IsIntegral K x := ((mem_algebraicClosure_iff).1 hx).isIntegral
  have : FiniteDimensional K (IntermediateField.adjoin K {x}) := IntermediateField.adjoin.finiteDimensional hint
  obtain ⟨M, hM, hxM⟩ := exists_le_untiltField (p := p) (IntermediateField.adjoin K {x})
  obtain ⟨N, hN⟩ := exists_le (K := K) (C := C) (p := p) M
  exact ⟨N, untiltField_mono hN (hxM (IntermediateField.mem_adjoin_simple_self K x))⟩

end FiniteGaloisTilt

section Equiv

local notation "Ω" => algebraicClosure K C
local notation "Ω♭" => algebraicClosure K♭ C♭

variable (K C p) in

abbrev resTilt (τ : Ω♭ ≃ₐ[K♭] Ω♭) (N : FiniteGaloisTilt K C p) : N.1 ≃ₐ[K♭] N.1 :=
  restrictAut Ω♭ τ N.1 N.le_algebraicClosure

omit [IsAlgClosed C] in
theorem resTilt_mul (τ₁ τ₂ : Ω♭ ≃ₐ[K♭] Ω♭) (N : FiniteGaloisTilt K C p) :
    resTilt K C p (τ₁ * τ₂) N = resTilt K C p τ₁ N * resTilt K C p τ₂ N :=
  restrictAut_mul _ _ _ _ _

omit [IsAlgClosed C] in
theorem coe_untiltAut_resTilt (τ : Ω♭ ≃ₐ[K♭] Ω♭) {N N' : FiniteGaloisTilt K C p} (h : N.1 ≤ N'.1)
    (x : untiltField K C p N.1) :
    ((untiltAut N'.1 (resTilt K C p τ N') ⟨x, untiltField_mono h x.2⟩ : untiltField K C p N'.1) : C) =
      ((untiltAut N.1 (resTilt K C p τ N) x : untiltField K C p N.1) : C) :=
  coe_untiltAut_of_le h _ _ (fun y => by rw [coe_restrictAut, coe_restrictAut]) x

variable (K C p) in

def untiltGalFun (τ : Ω♭ ≃ₐ[K♭] Ω♭) : Ω ≃ₐ[K] Ω :=
  glueAut Ω (fun N : FiniteGaloisTilt K C p => untiltField K C p N.1)
    (fun N => N.untiltField_le_algebraicClosure) FiniteGaloisTilt.directed_untiltField
    (fun x hx => FiniteGaloisTilt.exists_mem_untiltField x hx)
    (fun N => (untiltAut N.1 (resTilt K C p τ N)).toAlgHom)
    (fun N N' h x => by
      obtain ⟨N'', h1, h2⟩ := FiniteGaloisTilt.directed N N'
      exact (coe_untiltAut_resTilt τ h2 ⟨x, h x.2⟩).symm.trans (coe_untiltAut_resTilt τ h1 x))

theorem coe_untiltGalFun (τ : Ω♭ ≃ₐ[K♭] Ω♭) (N : FiniteGaloisTilt K C p) (x : Ω)
    (hx : (x : C) ∈ untiltField K C p N.1) :
    ((untiltGalFun K C p τ x : Ω) : C) =
      ((untiltAut N.1 (resTilt K C p τ N) ⟨x, hx⟩ : untiltField K C p N.1) : C) :=
  coe_glueAut _ _ _ _ _ _ _ N x hx

variable (K C p) in

def tiltGalAlt (ρ : Ω ≃ₐ[K] Ω) (N : FiniteGaloisTilt K C p) : N.1 ≃ₐ[K♭] N.1 :=
  (MulEquiv.ofBijective (untiltAutHom (K := K) (C := C) (p := p) N.1)
    (untiltAutHom_bijective N.1).1).symm
    (restrictAut Ω ρ (untiltField K C p N.1) N.untiltField_le_algebraicClosure)

omit [IsAlgClosed C] in
theorem untiltAut_tiltGal (ρ : Ω ≃ₐ[K] Ω) (N : FiniteGaloisTilt K C p) :
    untiltAut N.1 (tiltGalAlt K C p ρ N) =
      restrictAut Ω ρ (untiltField K C p N.1) N.untiltField_le_algebraicClosure :=
  (MulEquiv.ofBijective (untiltAutHom (K := K) (C := C) (p := p) N.1)
    (untiltAutHom_bijective N.1).1).apply_symm_apply _

omit [IsAlgClosed C] in
theorem coe_tiltGal_of_le (ρ : Ω ≃ₐ[K] Ω) {N N' : FiniteGaloisTilt K C p} (h : N.1 ≤ N'.1)
    (y : N.1) : ((tiltGalAlt K C p ρ N' ⟨y, h y.2⟩ : N'.1) : C♭) = ((tiltGalAlt K C p ρ N y : N.1) : C♭) := by
  set σ'' := restrictAut N'.1 (tiltGalAlt K C p ρ N') N.1 h
  have hσ'' : untiltAut N.1 σ'' = untiltAut N.1 (tiltGalAlt K C p ρ N) := by
    rw [untiltAut_tiltGal]
    refine AlgEquiv.ext fun x => Subtype.ext ?_
    rw [← coe_untiltAut_of_le h σ'' (tiltGalAlt K C p ρ N')
      (fun y => (coe_restrictAut _ _ _ h y).symm) x, untiltAut_tiltGal, coe_restrictAut,
      coe_restrictAut]
  have := (untiltAutHom_bijective (K := K) (C := C) (p := p) N.1).1.1 hσ''
  rw [← this, coe_restrictAut]

variable (K C p) in

def tiltGalFun (ρ : Ω ≃ₐ[K] Ω) : Ω♭ ≃ₐ[K♭] Ω♭ :=
  glueAut Ω♭ (fun N : FiniteGaloisTilt K C p => N.1) (fun N => N.le_algebraicClosure)
    FiniteGaloisTilt.directed (fun y hy => FiniteGaloisTilt.exists_mem y hy)
    (fun N => (tiltGalAlt K C p ρ N).toAlgHom) (fun _ _ h y => coe_tiltGal_of_le ρ h y)

theorem coe_tiltGalFun (ρ : Ω ≃ₐ[K] Ω) (N : FiniteGaloisTilt K C p) (y : Ω♭) (hy : (y : C♭) ∈ N.1) :
    ((tiltGalFun K C p ρ y : Ω♭) : C♭) = ((tiltGalAlt K C p ρ N ⟨y, hy⟩ : N.1) : C♭) :=
  coe_glueAut _ _ _ _ _ _ _ N y hy

theorem resTilt_tiltGalFun (ρ : Ω ≃ₐ[K] Ω) (N : FiniteGaloisTilt K C p) :
    resTilt K C p (tiltGalFun K C p ρ) N = tiltGalAlt K C p ρ N :=
  AlgEquiv.ext fun y => Subtype.ext (by
    rw [coe_restrictAut]
    exact coe_tiltGalFun ρ N _ y.2)

theorem restrictAut_untiltGalFun (τ : Ω♭ ≃ₐ[K♭] Ω♭) (N : FiniteGaloisTilt K C p) :
    restrictAut Ω (untiltGalFun K C p τ) (untiltField K C p N.1) N.untiltField_le_algebraicClosure =
      untiltAut N.1 (resTilt K C p τ N) :=
  AlgEquiv.ext fun x => Subtype.ext (by
    rw [coe_restrictAut]
    exact coe_untiltGalFun τ N _ x.2)

theorem tiltGal_untiltGalFun (τ : Ω♭ ≃ₐ[K♭] Ω♭) (N : FiniteGaloisTilt K C p) :
    tiltGalAlt K C p (untiltGalFun K C p τ) N = resTilt K C p τ N := by
  apply (untiltAutHom_bijective (K := K) (C := C) (p := p) N.1).1.1
  change untiltAut _ _ = untiltAut _ _
  rw [untiltAut_tiltGal, restrictAut_untiltGalFun]

theorem tiltGalFun_untiltGalFun (τ : Ω♭ ≃ₐ[K♭] Ω♭) : tiltGalFun K C p (untiltGalFun K C p τ) = τ := by
  refine AlgEquiv.ext fun y => Subtype.ext ?_
  obtain ⟨N, hN⟩ := FiniteGaloisTilt.exists_mem (K := K) (C := C) (p := p) y y.2
  rw [coe_tiltGalFun _ N y hN, tiltGal_untiltGalFun, coe_restrictAut]

theorem untiltGalFun_tiltGalFun (ρ : Ω ≃ₐ[K] Ω) : untiltGalFun K C p (tiltGalFun K C p ρ) = ρ := by
  refine AlgEquiv.ext fun x => Subtype.ext ?_
  obtain ⟨N, hN⟩ := FiniteGaloisTilt.exists_mem_untiltField (K := K) (C := C) (p := p) x x.2
  rw [coe_untiltGalFun _ N x hN, resTilt_tiltGalFun, untiltAut_tiltGal, coe_restrictAut]

theorem untiltGalFun_mul (τ₁ τ₂ : Ω♭ ≃ₐ[K♭] Ω♭) :
    untiltGalFun K C p (τ₁ * τ₂) = untiltGalFun K C p τ₁ * untiltGalFun K C p τ₂ := by
  refine AlgEquiv.ext fun x => Subtype.ext ?_
  obtain ⟨N, hN⟩ := FiniteGaloisTilt.exists_mem_untiltField (K := K) (C := C) (p := p) x x.2
  have hmem : ((untiltGalFun K C p τ₂ x : Ω) : C) ∈ untiltField K C p N.1 := by
    rw [coe_untiltGalFun τ₂ N x hN]; exact Subtype.prop _
  have he : (⟨((untiltGalFun K C p τ₂ x : Ω) : C), hmem⟩ : untiltField K C p N.1) =
      untiltAut N.1 (resTilt K C p τ₂ N) ⟨x, hN⟩ := Subtype.ext (coe_untiltGalFun τ₂ N x hN)
  rw [AlgEquiv.mul_apply, coe_untiltGalFun τ₁ N _ hmem, he, coe_untiltGalFun _ N x hN,
    resTilt_mul, untiltAut_mul, AlgEquiv.mul_apply]

variable (K C p) in

def untiltGalEquiv : (Ω♭ ≃ₐ[K♭] Ω♭) ≃* (Ω ≃ₐ[K] Ω) where
  toFun := untiltGalFun K C p
  invFun := tiltGalFun K C p
  left_inv := tiltGalFun_untiltGalFun
  right_inv := untiltGalFun_tiltGalFun
  map_mul' := untiltGalFun_mul

theorem untiltGalEquiv_apply (τ : Ω♭ ≃ₐ[K♭] Ω♭) : untiltGalEquiv K C p τ = untiltGalFun K C p τ :=
  rfl

theorem untiltGalEquiv_fixes_iff (τ : Ω♭ ≃ₐ[K♭] Ω♭) (M : IntermediateField K♭ C♭)
    [FiniteDimensional K♭ M] :
    (∀ x : Ω, (x : C) ∈ untiltField K C p M → untiltGalEquiv K C p τ x = x) ↔
      (∀ y : Ω♭, (y : C♭) ∈ M → τ y = y) := by
  obtain ⟨N, hMN⟩ := FiniteGaloisTilt.exists_le (K := K) (C := C) (p := p) M
  have key := untiltAut_mem_fixingSubgroup_iff N.1 hMN (resTilt K C p τ N)
  constructor
  · intro hΨ
    have h1 : untiltAut N.1 (resTilt K C p τ N) ∈
        (IntermediateField.restrict (untiltField_mono (K := K) (p := p) hMN)).fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      apply Subtype.ext
      have := hΨ ⟨x, N.untiltField_le_algebraicClosure x.2⟩ ((IntermediateField.mem_restrict _ x).1 hx)
      rw [untiltGalEquiv_apply] at this
      have e := coe_untiltGalFun τ N ⟨(x : C), N.untiltField_le_algebraicClosure x.2⟩ x.2
      exact e.symm.trans (congrArg Subtype.val this)
    have h2 := key.1 h1
    rw [IntermediateField.mem_fixingSubgroup_iff] at h2
    intro y hy
    apply Subtype.ext
    have := congrArg Subtype.val (h2 ⟨y, hMN hy⟩ ((IntermediateField.mem_restrict hMN _).2 hy))
    rw [coe_restrictAut] at this
    exact this
  · intro hτ
    have h2 : resTilt K C p τ N ∈ (IntermediateField.restrict hMN).fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro y hy
      apply Subtype.ext
      rw [coe_restrictAut]
      exact congrArg Subtype.val (hτ _ ((IntermediateField.mem_restrict hMN y).1 hy))
    have h1 := key.2 h2
    rw [IntermediateField.mem_fixingSubgroup_iff] at h1
    intro x hx
    have hxN := untiltField_mono (K := K) (p := p) hMN hx
    rw [untiltGalEquiv_apply]
    apply Subtype.ext
    rw [coe_untiltGalFun τ N x hxN]
    exact congrArg Subtype.val (h1 ⟨x, hxN⟩ ((IntermediateField.mem_restrict _ _).2 hx))

theorem continuous_untiltGalEquiv : Continuous (untiltGalEquiv K C p) := by
  apply continuous_of_continuousAt_one (untiltGalEquiv K C p) (continuousAt_def.mpr _)
  intro U hU
  rw [map_one, krullTopology_mem_nhds_one_iff] at hU
  obtain ⟨E, hE, hsub⟩ := hU
  rw [krullTopology_mem_nhds_one_iff]
  have : FiniteDimensional K (IntermediateField.lift E) :=
    LinearEquiv.finiteDimensional (IntermediateField.liftAlgEquiv E).toLinearEquiv
  obtain ⟨M, hM, hEM⟩ := exists_le_untiltField (p := p) (IntermediateField.lift E)
  refine ⟨IntermediateField.restrict (le_algebraicClosure_of_finiteDimensional M),
    LinearEquiv.finiteDimensional (IntermediateField.restrictAlgEquiv _).toLinearEquiv, ?_⟩
  intro τ hτ
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hτ
  apply hsub
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  exact (untiltGalEquiv_fixes_iff τ M).2
    (fun y hy => hτ y ((IntermediateField.mem_restrict _ y).2 hy)) x
    (hEM ((IntermediateField.mem_lift x).2 hx))

theorem continuous_untiltGalEquiv_symm : Continuous (untiltGalEquiv K C p).symm := by
  apply continuous_of_continuousAt_one (untiltGalEquiv K C p).symm (continuousAt_def.mpr _)
  intro U hU
  rw [map_one, krullTopology_mem_nhds_one_iff] at hU
  obtain ⟨E, hE, hsub⟩ := hU
  rw [krullTopology_mem_nhds_one_iff]
  have : FiniteDimensional K♭ (IntermediateField.lift E) :=
    LinearEquiv.finiteDimensional (IntermediateField.liftAlgEquiv E).toLinearEquiv
  refine ⟨IntermediateField.restrict
    (le_algebraicClosure_of_finiteDimensional (untiltField K C p (IntermediateField.lift E))),
    LinearEquiv.finiteDimensional (IntermediateField.restrictAlgEquiv _).toLinearEquiv, ?_⟩
  intro ρ hρ
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hρ
  apply hsub
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  have hfix := (untiltGalEquiv_fixes_iff ((untiltGalEquiv K C p).symm ρ)
    (IntermediateField.lift E)).1 (fun x hx => by
      rw [MulEquiv.apply_symm_apply]
      exact hρ x ((IntermediateField.mem_restrict _ x).2 hx))
  intro y hy
  exact hfix y ((IntermediateField.mem_lift y).2 hy)

variable (K C p) in

def untiltGalHomeomorph : (Ω♭ ≃ₐ[K♭] Ω♭) ≃ₜ* (Ω ≃ₐ[K] Ω) where
  toMulEquiv := untiltGalEquiv K C p
  continuous_toFun := continuous_untiltGalEquiv
  continuous_invFun := continuous_untiltGalEquiv_symm

end Equiv

end GroundTheory.PAdicHodge
