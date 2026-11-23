import Mathlib
import GroundTheory.LocalFields.LocalArtinUniqueness

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel

section Semilinear

variable {K K' A B : Type*} [Field K] [Field K'] [Field A] [Field B] [Algebra K A] [Algebra K' B]
  (e : K ≃+* K') (f : A ≃+* B) (hf : ∀ x : K, f (algebraMap K A x) = algebraMap K' B (e x))

include hf in
theorem symm_algebraMap_transport (x : K') : f.symm (algebraMap K' B x) = algebraMap K A (e.symm x) := by
  rw [RingEquiv.symm_apply_eq, hf, RingEquiv.apply_symm_apply]

include hf in
theorem comp_algebraMap_transport :
    (algebraMap K' B).comp e.toRingHom = (f : A →+* B).comp (algebraMap K A) := by
  ext x
  exact (hf x).symm

def galTransport : (A ≃ₐ[K] A) ≃* (B ≃ₐ[K'] B) where
  toFun σ :=
    { (f.symm.trans σ.toRingEquiv).trans f with
      commutes' := fun c => by
        simp only [RingEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe,
          RingEquiv.coe_trans, Function.comp_apply, symm_algebraMap_transport e f hf,
          AlgEquiv.coe_ringEquiv, AlgEquiv.commutes, hf, RingEquiv.apply_symm_apply] }
  invFun τ :=
    { (f.trans τ.toRingEquiv).trans f.symm with
      commutes' := fun c => by
        simp only [RingEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe,
          RingEquiv.coe_trans, Function.comp_apply, hf, AlgEquiv.coe_ringEquiv, AlgEquiv.commutes,
          symm_algebraMap_transport e f hf, RingEquiv.symm_apply_apply] }
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp
  map_mul' _ _ := by ext; simp

theorem galTransport_apply (σ : A ≃ₐ[K] A) (a : A) : galTransport e f hf σ (f a) = f (σ a) := by
  simp [galTransport]

include e f hf in
theorem isMulCommutative_transport [IsMulCommutative (A ≃ₐ[K] A)] :
    IsMulCommutative (B ≃ₐ[K'] B) :=
  ⟨⟨fun σ τ => by
    obtain ⟨σ', rfl⟩ := (galTransport e f hf).surjective σ
    obtain ⟨τ', rfl⟩ := (galTransport e f hf).surjective τ
    rw [← map_mul, ← map_mul, mul_comm' σ' τ']⟩⟩

include e f hf in
theorem finiteDimensional_transport [FiniteDimensional K A] : FiniteDimensional K' B :=
  Module.Finite.of_equiv_equiv e f (comp_algebraMap_transport e f hf)

include e f hf in
theorem isGalois_transport [IsGalois K A] : IsGalois K' B :=
  IsGalois.of_equiv_equiv (comp_algebraMap_transport e f hf)

include e f hf in
theorem isAbelianGalois_transport [IsAbelianGalois K A] : IsAbelianGalois K' B :=
  have := isGalois_transport e f hf
  { toIsMulCommutative := isMulCommutative_transport e f hf }

include hf in
theorem norm_transport (a : A) : e (Algebra.norm K a) = Algebra.norm K' (f a) := by
  rw [Algebra.norm_eq_of_equiv_equiv e f (comp_algebraMap_transport e f hf), RingEquiv.apply_symm_apply]

end Semilinear

section IntermediateFieldTransport

variable {K K' Ω Ω' : Type*} [Field K] [Field K'] [Field Ω] [Field Ω'] [Algebra K Ω] [Algebra K' Ω']
  (e : K ≃+* K') (ε : Ω ≃+* Ω') (hε : ∀ x : K, ε (algebraMap K Ω x) = algebraMap K' Ω' (e x))

def transportField (M : IntermediateField K Ω) : IntermediateField K' Ω' :=
  (M.toSubfield.map (ε : Ω →+* Ω')).toIntermediateField fun x =>
    ⟨algebraMap K Ω (e.symm x), M.algebraMap_mem _, by
      change ε (algebraMap K Ω (e.symm x)) = _
      rw [hε, e.apply_symm_apply]⟩

theorem mem_transportField {M : IntermediateField K Ω} {y : Ω'} :
    y ∈ transportField e ε hε M ↔ ε.symm y ∈ M := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    change ε.symm (ε x) ∈ M
    rw [RingEquiv.symm_apply_apply]
    exact hx
  · intro h
    exact ⟨_, h, ε.apply_symm_apply y⟩

theorem apply_mem_transportField {M : IntermediateField K Ω} {x : Ω} :
    ε x ∈ transportField e ε hε M ↔ x ∈ M := by
  rw [mem_transportField, RingEquiv.symm_apply_apply]

def transportFieldEquiv (M : IntermediateField K Ω) : M ≃+* transportField e ε hε M where
  toFun x := ⟨ε x, (apply_mem_transportField e ε hε).2 x.2⟩
  invFun y := ⟨ε.symm y, (mem_transportField e ε hε).1 y.2⟩
  left_inv _ := Subtype.ext (ε.symm_apply_apply _)
  right_inv _ := Subtype.ext (ε.apply_symm_apply _)
  map_mul' _ _ := Subtype.ext (map_mul ε _ _)
  map_add' _ _ := Subtype.ext (map_add ε _ _)

@[simp]
theorem coe_transportFieldEquiv (M : IntermediateField K Ω) (x : M) :
    (transportFieldEquiv e ε hε M x : Ω') = ε x :=
  rfl

theorem transportFieldEquiv_algebraMap (M : IntermediateField K Ω) (x : K) :
    transportFieldEquiv e ε hε M (algebraMap K M x) = algebraMap K' (transportField e ε hε M) (e x) :=
  Subtype.ext (hε x)

theorem isAbelianGalois_transportField (M : IntermediateField K Ω) [IsAbelianGalois K M] :
    IsAbelianGalois K' (transportField e ε hε M) :=
  isAbelianGalois_transport e (transportFieldEquiv e ε hε M) (transportFieldEquiv_algebraMap e ε hε M)

theorem finiteDimensional_transportField (M : IntermediateField K Ω) [FiniteDimensional K M] :
    FiniteDimensional K' (transportField e ε hε M) :=
  finiteDimensional_transport e (transportFieldEquiv e ε hε M) (transportFieldEquiv_algebraMap e ε hε M)

theorem norm_transportField (M : IntermediateField K Ω) (z : M) :
    e (Algebra.norm K z) = Algebra.norm K' (transportFieldEquiv e ε hε M z) :=
  norm_transport e (transportFieldEquiv e ε hε M) (transportFieldEquiv_algebraMap e ε hε M) z

variable [IsGalois K Ω] [IsGalois K' Ω']

include hε in
theorem apply_mem_maximalAbelianExtension {y : Ω} (hy : y ∈ maximalAbelianExtension K Ω) :
    ε y ∈ maximalAbelianExtension K' Ω' := by
  obtain ⟨L, _, _, hyL⟩ := exists_finite_abelian_mem hy
  have := isAbelianGalois_transportField e ε hε L
  exact le_maximalAbelianExtension _ ((apply_mem_transportField e ε hε).2 hyL)

include hε in

theorem mem_maximalAbelianExtension_transport_iff {y : Ω} :
    ε y ∈ maximalAbelianExtension K' Ω' ↔ y ∈ maximalAbelianExtension K Ω := by
  refine ⟨fun h => ?_, apply_mem_maximalAbelianExtension e ε hε⟩
  have := apply_mem_maximalAbelianExtension e.symm ε.symm (symm_algebraMap_transport e ε hε) h
  rwa [RingEquiv.symm_apply_apply] at this

theorem transportField_maximalAbelianExtension :
    transportField e ε hε (maximalAbelianExtension K Ω) = maximalAbelianExtension K' Ω' := by
  ext y
  rw [mem_transportField, ← mem_maximalAbelianExtension_transport_iff e ε hε, RingEquiv.apply_symm_apply]

def maximalAbelianExtensionTransport :
    maximalAbelianExtension K Ω ≃+* maximalAbelianExtension K' Ω' :=
  (transportFieldEquiv e ε hε _).trans
    (IntermediateField.equivOfEq (transportField_maximalAbelianExtension e ε hε)).toRingEquiv

@[simp]
theorem coe_maximalAbelianExtensionTransport (y : maximalAbelianExtension K Ω) :
    (maximalAbelianExtensionTransport e ε hε y : Ω') = ε y :=
  rfl

theorem maximalAbelianExtensionTransport_algebraMap (x : K) :
    maximalAbelianExtensionTransport e ε hε (algebraMap K _ x) = algebraMap K' _ (e x) :=
  Subtype.ext (hε x)

end IntermediateFieldTransport

section Valuation

variable {K K' : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field K'] [ValuativeRel K'] [TopologicalSpace K'] [IsNonarchimedeanLocalField K']
  (e : K ≃+* K') (he : ∀ x y : K, e x ≤ᵥ e y ↔ x ≤ᵥ y)

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [TopologicalSpace K']
  [IsNonarchimedeanLocalField K'] in
include he in
theorem symm_vle_iff (x y : K') : e.symm x ≤ᵥ e.symm y ↔ x ≤ᵥ y := by
  rw [← he, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [TopologicalSpace K']
  [IsNonarchimedeanLocalField K'] in
include he in
theorem apply_mem_integer_iff (x : K) : e x ∈ 𝒪[K'] ↔ x ∈ 𝒪[K] := by
  rw [Valuation.mem_integer_iff, Valuation.mem_integer_iff, ← (valuation K').vle_one_iff,
    ← (valuation K).vle_one_iff, ← map_one e, he]

def integerEquivOfVle : 𝒪[K] ≃+* 𝒪[K'] where
  toFun x := ⟨e x, (apply_mem_integer_iff e he x).2 x.2⟩
  invFun y := ⟨e.symm y, by rw [← apply_mem_integer_iff e he, RingEquiv.apply_symm_apply]; exact y.2⟩
  left_inv _ := Subtype.ext (e.symm_apply_apply _)
  right_inv _ := Subtype.ext (e.apply_symm_apply _)
  map_mul' _ _ := Subtype.ext (map_mul e _ _)
  map_add' _ _ := Subtype.ext (map_add e _ _)

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [TopologicalSpace K']
  [IsNonarchimedeanLocalField K'] in
@[simp]
theorem coe_integerEquivOfVle (x : 𝒪[K]) : (integerEquivOfVle e he x : K') = e x :=
  rfl

def residueFieldEquivOfVle : 𝓀[K] ≃+* 𝓀[K'] :=
  IsLocalRing.ResidueField.mapEquiv (integerEquivOfVle e he)

include he in

theorem card_residueField_eq_of_vle : Nat.card 𝓀[K'] = Nat.card 𝓀[K] :=
  (Nat.card_congr (residueFieldEquivOfVle e he).toEquiv).symm

include he in
theorem natCast_residueField_ne_zero_iff (m : ℕ) : (m : 𝓀[K']) ≠ 0 ↔ (m : 𝓀[K]) ≠ 0 := by
  rw [← map_natCast (residueFieldEquivOfVle e he), Ne, map_eq_zero_iff _ (residueFieldEquivOfVle e he).injective]

include he in

theorem ord_apply_of_vle (x : Kˣ) : ord (e (x : K)) = ord (x : K) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hϖ' : Irreducible (integerEquivOfVle e he ϖ) :=
    (MulEquiv.irreducible_iff (f := (integerEquivOfVle e he).toMulEquiv) (x := ϖ)).2 hϖ
  set p := unitsEquivIntProd hϖ x
  have hx : (x : K) = (ϖ : K) ^ Multiplicative.toAdd p.1 * ((p.2 : 𝒪[K]) : K) := by
    rw [← coe_unitsOfIntProd hϖ, ← unitsEquivIntProd_symm_apply, MulEquiv.symm_apply_apply]
  set y : K'ˣ := unitsOfIntProd hϖ' (p.1, Units.map (integerEquivOfVle e he).toMonoidHom p.2)
  have hy : e (x : K) = (y : K') := by
    rw [coe_unitsOfIntProd, hx, map_mul, map_zpow₀]
    rfl
  have h2 : (unitsEquivIntProd hϖ' y).1 = p.1 := by
    change ((unitsEquivIntProd hϖ') ((unitsEquivIntProd hϖ').symm _)).1 = _
    rw [MulEquiv.apply_symm_apply]
  rw [unitsEquivIntProd_fst] at h2
  rw [hy]
  exact Multiplicative.ofAdd.injective (h2.trans (unitsEquivIntProd_fst hϖ x))

end Valuation

section Main

variable {K K' : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field K'] [ValuativeRel K'] [TopologicalSpace K'] [IsNonarchimedeanLocalField K']
  {Ω Ω' : Type*} [Field Ω] [Field Ω'] [Algebra K Ω] [Algebra K' Ω'] [IsSepClosure K Ω]
  [IsSepClosure K' Ω']
  (e : K ≃+* K') (he : ∀ x y : K, e x ≤ᵥ e y ↔ x ≤ᵥ y)
  (ε : Ω ≃+* Ω') (hε : ∀ x : K, ε (algebraMap K Ω x) = algebraMap K' Ω' (e x))

include he hε in
theorem apply_mem_maximalUnramifiedExtension_of_vle {y : Ω}
    (hy : y ∈ maximalUnramifiedExtension K Ω) : ε y ∈ maximalUnramifiedExtension K' Ω' := by
  rw [maximalUnramifiedExtension_eq_adjoin] at hy ⊢
  have hS : unramifiedRoots K Ω ⊆ (transportField e.symm ε.symm (symm_algebraMap_transport e ε hε)
      (IntermediateField.adjoin K' (unramifiedRoots K' Ω')) : Set Ω) := by
    intro ξ hξ
    rw [SetLike.mem_coe, mem_transportField, RingEquiv.symm_symm]
    apply IntermediateField.subset_adjoin
    obtain ⟨m, hm, hξm⟩ := mem_unramifiedRoots_iff.1 hξ
    exact mem_unramifiedRoots_iff.2 ⟨m, (natCast_residueField_ne_zero_iff e he m).2 hm, by
      rw [← map_pow, hξm, map_one]⟩
  have := (IntermediateField.adjoin_le_iff.2 hS) hy
  rwa [mem_transportField, RingEquiv.symm_symm] at this

variable (K Ω) in

def transportedArtinMap :
    K'ˣ →* (maximalAbelianExtension K' Ω' ≃ₐ[K'] maximalAbelianExtension K' Ω') :=
  (galTransport e (maximalAbelianExtensionTransport e ε hε)
    (maximalAbelianExtensionTransport_algebraMap e ε hε)).toMonoidHom.comp
      ((localArtinMap K Ω).comp (Units.map e.symm.toRingHom.toMonoidHom))

omit [ValuativeRel K'] [TopologicalSpace K'] [IsNonarchimedeanLocalField K'] in
theorem transportedArtinMap_apply (x' : K'ˣ) {y : Ω} (hy : y ∈ maximalAbelianExtension K Ω) :
    ((transportedArtinMap K Ω e ε hε x'
      ⟨ε y, (mem_maximalAbelianExtension_transport_iff e ε hε).2 hy⟩ :
        maximalAbelianExtension K' Ω') : Ω') =
      ε ((localArtinMap K Ω (Units.map e.symm.toRingHom.toMonoidHom x') ⟨y, hy⟩ :
        maximalAbelianExtension K Ω) : Ω) := by
  have h := galTransport_apply e (maximalAbelianExtensionTransport e ε hε)
    (maximalAbelianExtensionTransport_algebraMap e ε hε)
    (localArtinMap K Ω (Units.map e.symm.toRingHom.toMonoidHom x')) ⟨y, hy⟩
  exact congrArg Subtype.val h

omit [ValuativeRel K'] [TopologicalSpace K'] [IsNonarchimedeanLocalField K'] in
theorem transportedArtinMap_apply' (x' : K'ˣ) {y' : Ω'}
    (hy' : y' ∈ maximalAbelianExtension K' Ω') :
    ((transportedArtinMap K Ω e ε hε x' ⟨y', hy'⟩ : maximalAbelianExtension K' Ω') : Ω') =
      ε ((localArtinMap K Ω (Units.map e.symm.toRingHom.toMonoidHom x')
        ⟨ε.symm y', (mem_maximalAbelianExtension_transport_iff e ε hε).1
          (by rwa [RingEquiv.apply_symm_apply])⟩ : maximalAbelianExtension K Ω) : Ω) := by
  have h := transportedArtinMap_apply e ε hε x'
    ((mem_maximalAbelianExtension_transport_iff e ε hε).1 (by rwa [RingEquiv.apply_symm_apply] :
      ε (ε.symm y') ∈ maximalAbelianExtension K' Ω'))
  simp only [RingEquiv.apply_symm_apply] at h
  exact h

include he in

theorem transportedArtinMap_eq : transportedArtinMap K Ω e ε hε = localArtinMap K' Ω' := by
  have he' := symm_vle_iff e he
  have hε' := symm_algebraMap_transport e ε hε
  refine eq_localArtinMap_of (fun π' hπ' => ?_) (fun L' _ _ x' hx' => ?_)
  ·
    set π : Kˣ := Units.map e.symm.toRingHom.toMonoidHom π'
    have hπ : ord (π : K) = 1 := by
      rw [← hπ', ← ord_apply_of_vle e.symm he' π']
      rfl
    rw [eq_maximalUnramifiedExtensionFrobenius_iff]
    intro ξ hξ
    obtain ⟨m, hm, hξm⟩ := mem_unramifiedRoots_iff.1 hξ
    apply Subtype.ext
    rw [restrictAb_apply, transportedArtinMap_apply']
    have hur : ε.symm (ξ : Ω') ∈ maximalUnramifiedExtension K Ω := by
      have := apply_mem_maximalUnramifiedExtension_of_vle e.symm he' ε.symm hε' ξ.2
      exact this
    have h1 := localArtinMap_uniformizer_apply (Ω := Ω) hπ hur
    have hm' : (m : 𝓀[K]) ≠ 0 := (natCast_residueField_ne_zero_iff e he m).1 hm
    have hpow : (⟨ε.symm (ξ : Ω'), hur⟩ : maximalUnramifiedExtension K Ω) ^ m = 1 := by
      apply Subtype.ext
      have := congrArg Subtype.val hξm
      simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at this ⊢
      rw [← map_pow, this, map_one]
    rw [maximalUnramifiedExtensionFrobenius_apply_of_pow_eq_one hm' hpow] at h1
    rw [show (⟨ε.symm (ξ : Ω'), _⟩ : maximalAbelianExtension K Ω) =
      ⟨ε.symm (ξ : Ω'), maximalUnramifiedExtension_le_maximalAbelianExtension hur⟩ from rfl, h1]
    simp only [SubmonoidClass.coe_pow, map_pow, RingEquiv.apply_symm_apply,
      card_residueField_eq_of_vle e he]
  ·
    set L := transportField e.symm ε.symm hε' L'
    have : FiniteDimensional K L := finiteDimensional_transportField e.symm ε.symm hε' L'
    have : IsAbelianGalois K L := isAbelianGalois_transportField e.symm ε.symm hε' L'
    obtain ⟨z', rfl⟩ := hx'
    set x : Kˣ := Units.map e.symm.toRingHom.toMonoidHom (normUnits K' L' z')
    have hx : x ∈ (normUnits K L).range := by
      refine ⟨Units.map (transportFieldEquiv e.symm ε.symm hε' L').toRingHom.toMonoidHom z', ?_⟩
      apply Units.ext
      change Algebra.norm K (transportFieldEquiv e.symm ε.symm hε' L' (z' : L')) =
        e.symm (Algebra.norm K' (z' : L'))
      exact (norm_transportField e.symm ε.symm hε' L' (z' : L')).symm
    have hker : restrictAb L (le_maximalAbelianExtension L) (localArtinMap K Ω x) = 1 := by
      rw [← MonoidHom.comp_apply, ← MonoidHom.mem_ker, ker_restrictAb_localArtinMap]
      exact hx
    ext y'
    rw [restrictAb_apply, transportedArtinMap_apply', AlgEquiv.one_apply]
    have hyL : ε.symm (y' : Ω') ∈ L := by
      rw [mem_transportField, RingEquiv.symm_symm, RingEquiv.apply_symm_apply]
      exact y'.2
    have h2 := congrArg (fun ρ : L ≃ₐ[K] L => ((ρ ⟨ε.symm (y' : Ω'), hyL⟩ : L) : Ω)) hker
    simp only [restrictAb_apply, AlgEquiv.one_apply] at h2
    rw [h2, RingEquiv.apply_symm_apply]

include he in

theorem transport_localArtinMap_apply (x : Kˣ) {y : Ω} (hy : y ∈ maximalAbelianExtension K Ω) :
    ε ((localArtinMap K Ω x ⟨y, hy⟩ : maximalAbelianExtension K Ω) : Ω) =
      ((localArtinMap K' Ω' (Units.map e.toRingHom.toMonoidHom x)
        ⟨ε y, (mem_maximalAbelianExtension_transport_iff e ε hε).2 hy⟩ :
          maximalAbelianExtension K' Ω') : Ω') := by
  have hx : Units.map e.symm.toRingHom.toMonoidHom (Units.map e.toRingHom.toMonoidHom x) = x := by
    ext
    simp
  rw [← transportedArtinMap_eq e he ε hε, transportedArtinMap_apply, hx]

end Main

section Corollaries

variable {K K' : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field K'] [ValuativeRel K'] [TopologicalSpace K'] [IsNonarchimedeanLocalField K']

open Filter Topology in

theorem vle_apply_iff_of_continuous (e : K ≃+* K') (hc : Continuous e) (hc' : Continuous e.symm)
    (x y : K) : e x ≤ᵥ e y ↔ x ≤ᵥ y := by
  refine vle_map_iff_of_valuation_lt_one_iff e.toRingHom (fun z => ?_) x y
  rw [← tendsto_pow_atTop_nhds_zero_iff, ← tendsto_pow_atTop_nhds_zero_iff]
  constructor
  · intro h
    have := (hc'.tendsto 0).comp h
    simpa [Function.comp_def] using this
  · intro h
    have := (hc.tendsto 0).comp h
    simpa [Function.comp_def] using this

variable {Ω Ω' : Type*} [Field Ω] [Field Ω'] [Algebra K Ω] [Algebra K' Ω'] [IsSepClosure K Ω]
  [IsSepClosure K' Ω']

theorem transport_localArtinMap_apply_of_continuous (e : K ≃+* K') (hc : Continuous e)
    (hc' : Continuous e.symm) (ε : Ω ≃+* Ω')
    (hε : ∀ x : K, ε (algebraMap K Ω x) = algebraMap K' Ω' (e x)) (x : Kˣ) {y : Ω}
    (hy : y ∈ maximalAbelianExtension K Ω) :
    ε ((localArtinMap K Ω x ⟨y, hy⟩ : maximalAbelianExtension K Ω) : Ω) =
      ((localArtinMap K' Ω' (Units.map e.toRingHom.toMonoidHom x)
        ⟨ε y, (mem_maximalAbelianExtension_transport_iff e ε hε).2 hy⟩ :
          maximalAbelianExtension K' Ω') : Ω') :=
  transport_localArtinMap_apply e (vle_apply_iff_of_continuous e hc hc') ε hε x hy

variable [Algebra K Ω'] [IsSepClosure K Ω']

theorem localArtinMap_algEquiv_apply (ε : Ω ≃ₐ[K] Ω') (x : Kˣ) {y : Ω}
    (hy : y ∈ maximalAbelianExtension K Ω) :
    ε ((localArtinMap K Ω x ⟨y, hy⟩ : maximalAbelianExtension K Ω) : Ω) =
      ((localArtinMap K Ω' x ⟨ε y, (mem_maximalAbelianExtension_transport_iff (RingEquiv.refl K)
        ε.toRingEquiv (fun c => ε.commutes c)).2 hy⟩ : maximalAbelianExtension K Ω') : Ω') := by
  have h := transport_localArtinMap_apply (RingEquiv.refl K) (fun _ _ => Iff.rfl) ε.toRingEquiv
    (fun c => ε.commutes c) x hy
  have hx : Units.map (RingEquiv.refl K).toRingHom.toMonoidHom x = x := by
    ext
    rfl
  rw [hx] at h
  exact h

end Corollaries

end GroundTheory.LocalField
