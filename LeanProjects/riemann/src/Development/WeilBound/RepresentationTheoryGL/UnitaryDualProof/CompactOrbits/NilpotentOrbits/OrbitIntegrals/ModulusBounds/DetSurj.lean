import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.ModulusBounds.DetEqOfSurj

noncomputable section

set_option linter.unusedSectionVars false

open Matrix Module

namespace PositivityTheory.RgUd.T.Nil.Orb.BModbound

open PositivityTheory.RgUd.T

section Surj

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]

theorem det_surj (f : V →ₗ[K] V) (F : W →ₗ[K] W) (L : V →ₗ[K] W)
    (hL : Function.Surjective L) (h : ∀ v, L (f v) = F (L v)) (P : Submodule K V) (hP : P = LinearMap.ker L)
    (hf : ∀ y ∈ P, f y ∈ P) : LinearMap.det f = LinearMap.det (f.restrict hf) * LinearMap.det F := by
  subst hP
  rw [LinearMap.det_eq_det_mul_det (LinearMap.ker L) f hf]
  congr 1
  set e := L.quotKerEquivOfSurjective hL
  have key : (e : (V ⧸ LinearMap.ker L) →ₗ[K] W) ∘ₗ (LinearMap.ker L).mapQ (LinearMap.ker L) f hf =
      F ∘ₗ (e : (V ⧸ LinearMap.ker L) →ₗ[K] W) := by
    apply Submodule.linearMap_qext
    ext v
    simp [e, h]
  have hF : F = (e : (V ⧸ LinearMap.ker L) →ₗ[K] W) ∘ₗ (LinearMap.ker L).mapQ (LinearMap.ker L) f hf ∘ₗ
      (e.symm : W →ₗ[K] (V ⧸ LinearMap.ker L)) := by
    rw [← LinearMap.comp_assoc, key, LinearMap.comp_assoc]
    ext w
    simp
  rw [hF, LinearMap.det_conj]

end Surj

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem det_sq_lemma {K W : Type*} [Field K] [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (F D : W →ₗ[K] W) (B : W →ₗ[K] W →ₗ[K] K) (t : K) (ht : t ≠ 0)
    (hFD : ∀ w, F (D w) = t • D (F w)) (hB : ∀ a b, B (F a) (F b) = B a b)
    (hBD : ∀ a b, D b = 0 → B (D a) b = 0) (hnd : ∀ b, (∀ a, B a b = 0) → b = 0)
    (hdet : LinearMap.det F = 1) (hK : ∀ y ∈ LinearMap.ker D, F y ∈ LinearMap.ker D) :
    LinearMap.det (F.restrict hK) ^ 2 = t ^ (finrank K W - finrank K (LinearMap.ker D)) := by
  have hu : IsUnit F := (LinearMap.isUnit_iff_isUnit_det F).mpr (by rw [hdet]; exact isUnit_one)
  have hFinj : Function.Injective F := ((Module.End.isUnit_iff F).mp hu).1
  have hFKinj : Function.Injective (F.restrict hK) := by
    intro a b hab
    exact Subtype.ext (hFinj (congrArg Subtype.val hab))
  set eK := LinearEquiv.ofInjectiveEndo (F.restrict hK) hFKinj with heK
  have hI : ∀ y ∈ LinearMap.range D, F y ∈ LinearMap.range D := by
    rintro _ ⟨w, rfl⟩
    exact ⟨t • F w, by rw [map_smul, hFD]⟩
  have htK : ∀ y ∈ LinearMap.ker D, (t • F) y ∈ LinearMap.ker D := fun y hy =>
    Submodule.smul_mem _ t (hK y hy)
  have h3 := det_surj (t • F) (F.restrict hI) D.rangeRestrict D.surjective_rangeRestrict
    (fun v => Subtype.ext (by
      show D ((t • F) v) = F (D v)
      rw [LinearMap.smul_apply, map_smul, hFD])) (LinearMap.ker D)
    (LinearMap.ker_rangeRestrict D).symm htK
  have hres : (t • F).restrict htK = t • F.restrict hK := LinearMap.ext fun y => rfl
  rw [hres, LinearMap.det_smul, LinearMap.det_smul, hdet] at h3
  let ψ' : ↥(LinearMap.ker D) →ₗ[K] Module.Dual K W := B.flip ∘ₗ (LinearMap.ker D).subtype
  have hψ'inj : Function.Injective ψ' := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro b hb
    exact Subtype.ext (hnd b (fun a => LinearMap.congr_fun hb a))
  let ψ : W →ₗ[K] Module.Dual K ↥(LinearMap.ker D) :=
    ψ'.dualMap ∘ₗ (Module.evalEquiv K W).toLinearMap
  have hψ : ∀ w b, ψ w b = B w b := fun w b => rfl
  have hψsurj : Function.Surjective ψ :=
    (LinearMap.dualMap_surjective_of_injective hψ'inj).comp (Module.evalEquiv K W).surjective
  have hfψ : ∀ w, ψ (F w) = (eK.symm : ↥(LinearMap.ker D) →ₗ[K] ↥(LinearMap.ker D)).dualMap (ψ w) := by
    intro w
    ext b
    rw [LinearMap.dualMap_apply, hψ, hψ]
    have hb : (b : W) = F ((eK.symm b : ↥(LinearMap.ker D)) : W) :=
      congrArg Subtype.val (eK.apply_symm_apply b).symm
    rw [hb]
    exact hB w _
  have hker : LinearMap.ker ψ = LinearMap.range D := by
    symm
    apply Submodule.eq_of_le_of_finrank_eq
    · rintro _ ⟨a, rfl⟩
      rw [LinearMap.mem_ker]
      ext b
      rw [hψ, LinearMap.zero_apply]
      exact hBD a b (LinearMap.mem_ker.mp b.2)
    · have e1 := LinearMap.finrank_range_add_finrank_ker ψ
      have e2 := LinearMap.finrank_range_add_finrank_ker D
      rw [LinearMap.range_eq_top.mpr hψsurj, finrank_top, Subspace.dual_finrank_eq] at e1
      omega
  have h4 := det_surj F ((eK.symm : ↥(LinearMap.ker D) →ₗ[K] ↥(LinearMap.ker D)).dualMap) ψ hψsurj hfψ
    (LinearMap.range D) hker.symm hI
  rw [LinearMap.det_dualMap, hdet] at h4
  have hs : LinearMap.det (eK.symm : ↥(LinearMap.ker D) →ₗ[K] ↥(LinearMap.ker D)) *
      LinearMap.det (F.restrict hK) = 1 := by
    rw [← LinearMap.det_comp]
    have hid : (eK.symm : ↥(LinearMap.ker D) →ₗ[K] ↥(LinearMap.ker D)) ∘ₗ F.restrict hK = LinearMap.id :=
      LinearMap.ext fun y => eK.symm_apply_apply y
    rw [hid, LinearMap.det_id]
  have hdI : LinearMap.det (F.restrict hI) = LinearMap.det (F.restrict hK) := by
    calc LinearMap.det (F.restrict hI)
        = LinearMap.det (F.restrict hI) * (LinearMap.det (eK.symm : ↥(LinearMap.ker D) →ₗ[K] ↥(LinearMap.ker D)) *
          LinearMap.det (F.restrict hK)) := by rw [hs, mul_one]
      _ = (LinearMap.det (F.restrict hI) * LinearMap.det (eK.symm : ↥(LinearMap.ker D) →ₗ[K] ↥(LinearMap.ker D))) *
          LinearMap.det (F.restrict hK) := by ring
      _ = LinearMap.det (F.restrict hK) := by rw [← h4, one_mul]
  rw [hdI] at h3
  rw [pow_sub₀ t ht (Submodule.finrank_le _), eq_mul_inv_iff_mul_eq₀ (pow_ne_zero _ ht)]
  linear_combination -h3

private theorem det_sq_lemma_3 (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z) :
    IsSemisimpleModule ↥(Z.map (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) k ≃ₐ[k]
      Module.End k (Fin n → k)).toAlgHom) (Fin n → k) := by
  let φ : Matrix (Fin n) (Fin n) k →ₐ[k] Module.End k (Fin n → k) :=
    (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) k ≃ₐ[k] Module.End k (Fin n → k)).toAlgHom
  let Z' := Z.map φ
  have hcomm : ∀ a c : Z', a * c = c * a := by
    rintro ⟨_, z1, hz1, rfl⟩ ⟨_, z2, hz2, rfl⟩
    apply Subtype.ext
    show φ z1 * φ z2 = φ z2 * φ z1
    rw [← map_mul, ← map_mul, hZ.1 z1 hz1 z2 hz2]
  letI : CommRing Z' := { (inferInstance : Ring Z') with mul_comm := hcomm }
  haveI : IsReduced Z' := by
    constructor
    rintro ⟨_, z, hz, rfl⟩ ⟨m, hm⟩
    have hzm : (⟨z, hz⟩ : Z) ^ m = 0 := by
      apply Subtype.ext
      apply (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) k ≃ₐ[k] Module.End k (Fin n → k)).injective
      have h1 := congrArg Subtype.val hm
      simpa [φ] using h1
    have h2 := hZ.2.eq_zero _ ⟨m, hzm⟩
    apply Subtype.ext
    have h3 : z = 0 := congrArg Subtype.val h2
    simp [h3]
  haveI : IsArtinianRing Z' := IsArtinianRing.of_finite k Z'
  haveI : IsSemisimpleRing Z' := IsArtinianRing.isSemisimpleRing_of_isReduced Z'
  exact inferInstance

private theorem det_sq_lemma_2 [CharZero k] (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z)
    (b : Matrix (Fin n) (Fin n) k) (hb : b ∈ Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k)))
    (h : ∀ a ∈ Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k)), Matrix.trace (a * b) = 0) :
    b = 0 := by
  classical
  by_contra hb0
  let φ : Matrix (Fin n) (Fin n) k →ₐ[k] Module.End k (Fin n → k) :=
    (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) k ≃ₐ[k] Module.End k (Fin n → k)).toAlgHom
  have hφ : ∀ z v, φ z v = z *ᵥ v := fun z v => rfl
  let Z' := Z.map φ
  haveI : IsSemisimpleModule Z' (Fin n → k) := det_sq_lemma_3 Z hZ
  have hzb : ∀ z ∈ Z, z * b = b * z := fun z hz => (Subalgebra.mem_centralizer_iff k).mp hb z hz
  let β : (Fin n → k) →ₗ[Z'] (Fin n → k) :=
    { toFun := fun v => b *ᵥ v
      map_add' := fun u v => Matrix.mulVec_add b u v
      map_smul' := by
        rintro ⟨_, z, hz, rfl⟩ v
        show b *ᵥ (φ z v) = φ z (b *ᵥ v)
        rw [hφ, hφ, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hzb z hz] }
  have hβ : ∀ v, β v = b *ᵥ v := fun v => rfl
  have hβ0 : β ≠ 0 := by
    intro h0
    apply hb0
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    have := LinearMap.congr_fun h0 v
    rw [hβ] at this
    simpa [Matrix.toLin'_apply] using this
  obtain ⟨Wc, hWc⟩ := exists_isCompl (LinearMap.ker β)
  obtain ⟨U, hU⟩ := exists_isCompl (LinearMap.range β)
  let σ : ↥Wc ≃ₗ[Z'] ↥(LinearMap.range β) :=
    (Submodule.quotientEquivOfIsCompl _ _ hWc).symm.trans β.quotKerEquivRange
  have hσ : ∀ w : ↥Wc, ((σ w : ↥(LinearMap.range β)) : Fin n → k) = β w := by
    intro w
    simp [σ, Submodule.quotientEquivOfIsCompl_symm_apply, LinearMap.quotKerEquivRange_apply_mk]
  let π := (LinearMap.range β).projectionOnto U hU
  let pW := Wc.projectionOnto (LinearMap.ker β) hWc.symm
  let A : (Fin n → k) →ₗ[Z'] (Fin n → k) := Wc.subtype ∘ₗ (σ.symm : _ →ₗ[Z'] _) ∘ₗ π
  let P : (Fin n → k) →ₗ[Z'] (Fin n → k) := Wc.subtype ∘ₗ pW
  have hAP : A ∘ₗ β = P := by
    apply LinearMap.ext
    intro v
    show ((σ.symm (π (β v)) : ↥Wc) : Fin n → k) = (pW v : Fin n → k)
    congr 1
    rw [LinearEquiv.symm_apply_eq]
    apply Subtype.ext
    have h1 : ((π (β v) : ↥(LinearMap.range β)) : Fin n → k) = β v :=
      congrArg Subtype.val (Submodule.projectionOnto_apply_left hU ⟨β v, LinearMap.mem_range_self β v⟩)
    rw [h1, hσ]
    have hsplit := Submodule.projection_add_projection_eq_self hWc.symm v
    have hk : β ((LinearMap.ker β).projection Wc hWc.symm.symm v) = 0 :=
      LinearMap.mem_ker.mp (Submodule.projection_apply_mem _ v)
    conv_lhs => rw [← hsplit]
    rw [map_add, hk, add_zero]
    rfl
  let Pk : (Fin n → k) →ₗ[k] (Fin n → k) := P.restrictScalars k
  have hPk : ∀ v, Pk v = P v := fun v => rfl
  have hPidem : IsIdempotentElem Pk := by
    apply LinearMap.ext
    intro v
    exact congrArg Subtype.val (Submodule.projectionOnto_apply_left hWc.symm (pW v))
  have hWc0 : Wc ≠ ⊥ := by
    intro hW
    apply hβ0
    have htop := hWc.sup_eq_top
    rw [hW, sup_bot_eq] at htop
    exact LinearMap.ker_eq_top.mp htop
  have hP0 : Pk ≠ 0 := by
    intro hP
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWc0
    apply hw0
    have h1 := LinearMap.congr_fun hP w
    have h2 : ((pW w : ↥Wc) : Fin n → k) = w :=
      congrArg Subtype.val (Submodule.projectionOnto_apply_left hWc.symm ⟨w, hw⟩)
    rw [← h2]
    exact h1
  have htrP : LinearMap.trace k (Fin n → k) Pk ≠ 0 :=
    fun ht0 => hP0 ((LinearMap.IsIdempotentElem.trace_eq_zero_iff hPidem).mp ht0)
  let Ak : (Fin n → k) →ₗ[k] (Fin n → k) := A.restrictScalars k
  let a := LinearMap.toMatrix' Ak
  have ha : a ∈ Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k)) := by
    rw [Subalgebra.mem_centralizer_iff]
    intro z hz
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
    apply LinearMap.ext
    intro v
    have hs := A.map_smul (⟨φ z, Subalgebra.mem_map.mpr ⟨z, hz, rfl⟩⟩ : Z') v
    change A (φ z v) = φ z (A v) at hs
    show Matrix.toLin' z (A v) = A (Matrix.toLin' z v)
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← hφ, ← hφ, hs]
  have htr : Matrix.trace (a * b) = LinearMap.trace k (Fin n → k) Pk := by
    rw [LinearMap.trace_eq_matrix_trace k (Pi.basisFun k (Fin n)), LinearMap.toMatrix_eq_toMatrix']
    congr 1
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_toMatrix']
    apply LinearMap.ext
    intro v
    show A (β v) = P v
    rw [← hAP]
    rfl
  exact htrP (htr ▸ h a ha)

theorem det_sq [CharZero k] (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z) (x : Matrix (Fin n) (Fin n) k)
    (hx : x ∈ Bz Z) (g : GL (Fin n) k) (hg : g ∈ Gz Z) (t : k) (ht : t ≠ 0) (hgx : g.val * x * g⁻¹.val = t • x) :
    (LinearMap.det ((adL g).restrict (cA_inv Z x g hg t ht hgx))) ^ 2 =
      t ^ (finrank k (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))) - finrank k (cA Z x)) := by
  have hxC : x ∈ Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k)) :=
    (Subalgebra.mem_centralizer_iff k).mpr (fun a ha => hx a ha)
  set S := Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k)) with hS
  set C := Subalgebra.toSubmodule S with hC
  let Dx : Matrix (Fin n) (Fin n) k →ₗ[k] Matrix (Fin n) (Fin n) k :=
    LinearMap.mulRight k x - LinearMap.mulLeft k x
  have hDx : ∀ y, Dx y = y * x - x * y := fun y => rfl
  have hDC : ∀ y ∈ C, Dx y ∈ C := fun y hy => by
    rw [hDx]
    exact S.sub_mem (S.mul_mem hy hxC) (S.mul_mem hxC hy)
  let F := (adL g).restrict (cC_inv Z g hg)
  let D := Dx.restrict hDC
  let B : ↥C →ₗ[k] ↥C →ₗ[k] k :=
    ((LinearMap.mul k (Matrix (Fin n) (Fin n) k)).compr₂ (Matrix.traceLinearMap (Fin n) k k)).compl₁₂
      C.subtype C.subtype
  have hBapp : ∀ a b : ↥C, B a b = Matrix.trace ((a : Matrix (Fin n) (Fin n) k) * (b : Matrix (Fin n) (Fin n) k)) := fun a b => rfl
  have hFD : ∀ w, F (D w) = t • D (F w) := by
    intro w
    apply Subtype.ext
    show adL g ((w : Matrix (Fin n) (Fin n) k) * x - x * (w : Matrix (Fin n) (Fin n) k)) = t • (adL g (w : Matrix (Fin n) (Fin n) k) * x - x * adL g (w : Matrix (Fin n) (Fin n) k))
    rw [adL_apply, adL_apply]
    have e2 : ∀ P : Matrix (Fin n) (Fin n) k, t • (P * x - x * P) = P * (t • x) - (t • x) * P := by
      intro P
      rw [smul_sub, mul_smul_comm, smul_mul_assoc]
    rw [e2, ← hgx]
    simp only [mul_assoc, mul_sub, sub_mul, Units.inv_mul_cancel_left]
  have hB : ∀ a b, B (F a) (F b) = B a b := by
    intro a b
    rw [hBapp, hBapp]
    show Matrix.trace (adL g (a : Matrix (Fin n) (Fin n) k) * adL g (b : Matrix (Fin n) (Fin n) k)) = Matrix.trace ((a : Matrix (Fin n) (Fin n) k) * (b : Matrix (Fin n) (Fin n) k))
    rw [adL_apply, adL_apply]
    simp only [mul_assoc, Units.inv_mul_cancel_left]
    rw [Matrix.trace_mul_comm]
    simp only [mul_assoc, Units.inv_mul, mul_one]
  have hBD : ∀ a b, D b = 0 → B (D a) b = 0 := by
    intro a b hb
    have h0 : (b : Matrix (Fin n) (Fin n) k) * x - x * (b : Matrix (Fin n) (Fin n) k) = 0 := congrArg Subtype.val hb
    have hb' : (b : Matrix (Fin n) (Fin n) k) * x = x * (b : Matrix (Fin n) (Fin n) k) := sub_eq_zero.mp h0
    rw [hBapp]
    show Matrix.trace (((a : Matrix (Fin n) (Fin n) k) * x - x * (a : Matrix (Fin n) (Fin n) k)) * (b : Matrix (Fin n) (Fin n) k)) = 0
    rw [sub_mul, Matrix.trace_sub, sub_eq_zero, mul_assoc x, Matrix.trace_mul_comm x,
      mul_assoc (a : Matrix (Fin n) (Fin n) k) (b : Matrix (Fin n) (Fin n) k), hb', ← mul_assoc]
  have hnd : ∀ b, (∀ a, B a b = 0) → b = 0 := by
    intro b h
    apply Subtype.ext
    exact det_sq_lemma_2 Z hZ b b.2 (fun a ha => h ⟨a, ha⟩)
  have hK : ∀ y ∈ LinearMap.ker D, F y ∈ LinearMap.ker D := by
    intro y hy
    rw [LinearMap.mem_ker] at hy ⊢
    have := hFD y
    rw [hy, map_zero] at this
    exact (smul_eq_zero.mp this.symm).resolve_left ht
  have key := det_sq_lemma F D B t ht hFD hB hBD hnd (det_C Z hZ g hg) hK
  have hmap : (LinearMap.ker D).map C.subtype = cA Z x := by
    ext y
    simp only [Submodule.mem_map, LinearMap.mem_ker]
    constructor
    · rintro ⟨z, hz, rfl⟩
      have h0 : (z : Matrix (Fin n) (Fin n) k) * x - x * (z : Matrix (Fin n) (Fin n) k) = 0 := congrArg Subtype.val hz
      exact ⟨fun a ha => (Subalgebra.mem_centralizer_iff k).mp z.2 a ha, sub_eq_zero.mp h0⟩
    · rintro ⟨hyB, hyx⟩
      have hyC : y ∈ C := (Subalgebra.mem_centralizer_iff k).mpr (fun a ha => hyB a ha)
      exact ⟨⟨y, hyC⟩, Subtype.ext (sub_eq_zero.mpr hyx), rfl⟩
  let e : ↥(LinearMap.ker D) ≃ₗ[k] ↥(cA Z x) :=
    (Submodule.equivMapOfInjective C.subtype C.injective_subtype (LinearMap.ker D)).trans
      (LinearEquiv.ofEq _ _ hmap)
  have hG : (adL g).restrict (cA_inv Z x g hg t ht hgx) =
      (e : ↥(LinearMap.ker D) →ₗ[k] ↥(cA Z x)) ∘ₗ F.restrict hK ∘ₗ
        (e.symm : ↥(cA Z x) →ₗ[k] ↥(LinearMap.ker D)) := by
    apply LinearMap.ext
    intro y
    obtain ⟨z, rfl⟩ := e.surjective y
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    rfl
  have hfr : finrank k ↥S = finrank k ↥C := rfl
  rw [hG, LinearMap.det_conj, ← LinearEquiv.finrank_eq e, hfr]
  exact key
