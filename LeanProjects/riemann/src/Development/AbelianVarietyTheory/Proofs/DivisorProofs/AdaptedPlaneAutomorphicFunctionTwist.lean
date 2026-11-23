import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLeviLeviElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnSqFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermUnipotentIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviElementAdaptedStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThKCtFin

noncomputable section

namespace GlobalTheory.ThKCtFin.LeftInvLevi

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def planeMap {n n₁ : ℕ} (H : Plane E n n₁) : E × E × (Fin n₁ → E) →ₗ[E] (Fin n → E) where
  toFun p := p.1 • H.x + H.ι *ᵥ p.2.2 + p.2.1 • H.y
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, add_smul, Matrix.mulVec_add]
    abel
  map_smul' r p := by
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Matrix.mulVec_smul, RingHom.id_apply, smul_add, mul_smul]

theorem planeMap_apply {n n₁ : ℕ} (H : Plane E n n₁) (s t : E) (u : Fin n₁ → E) :
    planeMap H (s, t, u) = s • H.x + H.ι *ᵥ u + t • H.y := rfl

theorem planeMap_bij {n n₁ : ℕ} {B : Base F E} {Y : Spc F E n} {Y₁ : Spc F E n₁} {H : Plane E n n₁} {i₀ i₁ : ℕ}
    (hH : H.IsAdapted σ B Y Y₁ i₀ i₁) (hL : Y.L.IsLattice E) : Function.Bijective (planeMap H) := by
  have hs : Function.Surjective (planeMap H) := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hL.span_eq_top, Submodule.span_le]
    intro z hz
    obtain ⟨s, t, u, -, -, -, rfl⟩ := hH.split z hz
    exact ⟨(s, t, u), rfl⟩
  refine ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).2 hs, hs⟩
  simp only [Module.finrank_prod, Module.finrank_self, Module.finrank_fin_fun, hH.rank]
  omega

def scaleMap (n₁ : ℕ) (α β : E) : E × E × (Fin n₁ → E) →ₗ[E] E × E × (Fin n₁ → E) :=
  (α • LinearMap.id).prodMap ((β • LinearMap.id).prodMap LinearMap.id)

def scaleMat {n n₁ : ℕ} {H : Plane E n n₁} (hb : Function.Bijective (planeMap H)) (α β : E) : Matrix (Fin n) (Fin n) E :=
  LinearMap.toMatrix' ((LinearEquiv.ofBijective _ hb).toLinearMap ∘ₗ scaleMap n₁ α β ∘ₗ
    (LinearEquiv.ofBijective _ hb).symm.toLinearMap)

theorem scaleMat_mulVec {n n₁ : ℕ} {H : Plane E n n₁} (hb : Function.Bijective (planeMap H)) (α β s t : E)
    (u : Fin n₁ → E) : scaleMat hb α β *ᵥ planeMap H (s, t, u) = planeMap H (α * s, β * t, u) := by
  rw [scaleMat, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  have e : (LinearEquiv.ofBijective _ hb).symm (planeMap H (s, t, u)) = (s, t, u) :=
    (LinearEquiv.ofBijective _ hb).symm_apply_apply (s, t, u)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, e, scaleMap, LinearMap.prodMap_apply, LinearMap.smul_apply,
    LinearMap.id_apply, smul_eq_mul, LinearEquiv.ofBijective_apply]

theorem scaleMat_mul {n n₁ : ℕ} {H : Plane E n n₁} (hb : Function.Bijective (planeMap H)) (α β α' β' : E) :
    scaleMat hb α β * scaleMat hb α' β' = scaleMat hb (α * α') (β * β') := by
  rw [scaleMat, scaleMat, scaleMat, ← LinearMap.toMatrix'_comp]
  congr 1
  refine LinearMap.ext fun v => ?_
  simp [scaleMap, mul_smul]

theorem scaleMat_one {n n₁ : ℕ} {H : Plane E n n₁} (hb : Function.Bijective (planeMap H)) : scaleMat hb 1 1 = 1 := by
  rw [scaleMat, ← LinearMap.toMatrix'_id]
  congr 1
  refine LinearMap.ext fun v => ?_
  simp [scaleMap]

def scaleGL {n n₁ : ℕ} {H : Plane E n n₁} (hb : Function.Bijective (planeMap H)) (α β : Eˣ) : GL (Fin n) E :=
  ⟨scaleMat hb α β, scaleMat hb α⁻¹.1 β⁻¹.1, by rw [scaleMat_mul]; simp [scaleMat_one],
    by rw [scaleMat_mul]; simp [scaleMat_one]⟩

theorem incV_add {n : ℕ} (v w : Fin n → E) : incV F (v + w) = incV F v + incV F w := by
  funext i; simp [incV]

theorem incV_smul {n : ℕ} (s : E) (v : Fin n → E) : incV F (s • v) = inclR (F := F) (AF F) s • incV F v := by
  funext i; simp [incV]

theorem incV_mulVec {n m : ℕ} (M : Matrix (Fin n) (Fin m) E) (v : Fin m → E) :
    incV F (M *ᵥ v) = incM F M *ᵥ incV F v := funext fun i => RingHom.map_mulVec _ _ _ i

theorem incV_planeMap {n n₁ : ℕ} (H : Plane E n n₁) (s t : E) (u : Fin n₁ → E) :
    incV F (planeMap H (s, t, u)) = inclR (F := F) (AF F) s • incV F H.x + incM F H.ι *ᵥ incV F u +
      inclR (F := F) (AF F) t • incV F H.y := by
  rw [planeMap_apply, incV_add, incV_add, incV_smul, incV_smul, incV_mulVec]

theorem matrix_ext_mulVec {R : Type} [CommRing R] {k l : ℕ} {A B : Matrix (Fin k) (Fin l) R} (h : ∀ v, A *ᵥ v = B *ᵥ v) :
    A = B := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using this

theorem matA_ext {n n₁ : ℕ} {H : Plane E n n₁} (hs : Function.Surjective (planeMap H))
    {A B : Matrix (Fin n) (Fin n) (AE F E)} (hx : A *ᵥ incV F H.x = B *ᵥ incV F H.x)
    (hy : A *ᵥ incV F H.y = B *ᵥ incV F H.y) (hι : A * incM F H.ι = B * incM F H.ι) : A = B := by
  have key : ∀ v : Fin n → E, A *ᵥ incV F v = B *ᵥ incV F v := by
    intro v
    obtain ⟨⟨s, t, u⟩, rfl⟩ := hs v
    rw [incV_planeMap]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hx, hy, hι]
  ext i j
  have h := congrFun (key (Pi.single j 1)) i
  have e1 : incV F (Pi.single j (1 : E)) = Pi.single j 1 := by
    funext k
    by_cases hk : k = j
    · subst hk; simp [incV]
    · simp [incV, hk]
  rw [e1, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at h
  simpa using h

section Levi

variable {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {H' : Plane E d d₁}

theorem mat_mul' (g k : UA σ W.J) : mat (g * k) = mat g * mat k := rfl

theorem mat_one' : mat (1 : UA σ W₁.J) = 1 := rfl

theorem mat_inv_mul' (k : UA σ W.J) : mat k⁻¹ * mat k = 1 := by
  rw [← mat_mul', inv_mul_cancel]; rfl

theorem levi_mul {t s : (AE F E)ˣ} {m m' : UA σ W.J} (h : IsLevi (W₁ := W₁) H' t 1 m)
    (h' : IsLevi (W₁ := W₁) H' s 1 m') : IsLevi (W₁ := W₁) H' (t * s) 1 (m * m') := by
  have h2 := h.2.2
  have h2' := h'.2.2
  rw [mat_one', Matrix.mul_one] at h2 h2'
  refine ⟨?_, ?_, ?_⟩
  · rw [mat_mul', ← Matrix.mulVec_mulVec, h'.1, Matrix.mulVec_smul, h.1, smul_smul, Units.val_mul, mul_comm]
  · rw [mat_mul', ← Matrix.mulVec_mulVec, h'.2.1, Matrix.mulVec_smul, h.2.1, smul_smul, mul_inv_rev, Units.val_mul,
      map_mul]
  · rw [mat_mul', Matrix.mul_assoc, h2', h2, mat_one', Matrix.mul_one]

theorem levi_unique (hs : Function.Surjective (planeMap H')) {t : (AE F E)ˣ} {m m' : UA σ W.J}
    (h : IsLevi (W₁ := W₁) H' t 1 m) (h' : IsLevi (W₁ := W₁) H' t 1 m') : m = m' := by
  have e : mat m = mat m' := matA_ext hs (h.1.trans h'.1.symm) (h.2.1.trans h'.2.1.symm) (h.2.2.trans h'.2.2.symm)
  exact Subtype.ext (Units.ext e)

theorem inv_data {k : UA σ W.J} {a : (AE F E)ˣ} (hx : mat k *ᵥ incV F H'.x = a.1 • incV F H'.x)
    (hι : ∀ z, mat k *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z) :
    mat k⁻¹ *ᵥ incV F H'.x = (a⁻¹).1 • incV F H'.x ∧ ∀ z, mat k⁻¹ *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z := by
  refine ⟨?_, fun z => ?_⟩
  · calc mat k⁻¹ *ᵥ incV F H'.x = ((a⁻¹).1 * a.1) • (mat k⁻¹ *ᵥ incV F H'.x) := by rw [Units.inv_mul, one_smul]
      _ = (a⁻¹).1 • (mat k⁻¹ *ᵥ (a.1 • incV F H'.x)) := by rw [mul_smul, Matrix.mulVec_smul]
      _ = (a⁻¹).1 • incV F H'.x := by rw [← hx, Matrix.mulVec_mulVec, mat_inv_mul', Matrix.one_mulVec]
  · calc mat k⁻¹ *ᵥ (incM F H'.ι *ᵥ z) = mat k⁻¹ *ᵥ (mat k *ᵥ (incM F H'.ι *ᵥ z)) := by rw [hι]
      _ = incM F H'.ι *ᵥ z := by rw [Matrix.mulVec_mulVec, mat_inv_mul', Matrix.one_mulVec]

theorem conj_mem_unip {k : UA σ W.J} {a : (AE F E)ˣ} (hx : mat k *ᵥ incV F H'.x = a.1 • incV F H'.x)
    (hι : ∀ z, mat k *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z) {u : UA σ W.J} (hu : u ∈ unip σ W H') :
    k⁻¹ * u * k ∈ unip σ W H' := by
  obtain ⟨hx', hι'⟩ := inv_data hx hι
  have hle : unip σ W H' ≤ (unip σ W H').comap (MulAut.conj k⁻¹).toMonoidHom := by
    refine (Subgroup.closure_le _).2 fun s hs => ?_
    obtain ⟨hs1, hs2⟩ := hs
    simp only [Subgroup.coe_comap, Set.mem_preimage, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    refine Subgroup.subset_closure ⟨?_, fun z => ?_⟩
    · rw [mat_mul', mat_mul', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_smul, hs1,
        Matrix.mulVec_smul, hx', smul_smul, Units.mul_inv, one_smul]
    · obtain ⟨c, hc⟩ := hs2 z
      refine ⟨c * (a⁻¹).1, ?_⟩
      rw [mat_mul', mat_mul', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hι, hc, Matrix.mulVec_add,
        Matrix.mulVec_smul, hι', hx', smul_smul]
  simpa [MulAut.conj_apply] using hle hu

end Levi

theorem cA_inclR (x : E) : cA σ (inclR (F := F) (AF F) x) = inclR (F := F) (AF F) (σ x) := rfl

theorem levi_mem_ratU {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {H' : Plane E d d₁}
    (hb : Function.Bijective (planeMap H')) (γ : Eˣ) {m : UA σ W.J}
    (hm : IsLevi (W₁ := W₁) H' (Units.map (inclR (F := F) (AF F)).toMonoidHom γ) 1 m) : m ∈ ratU σ W.J := by
  let Q := scaleGL hb γ (Units.map σ.toMonoidHom γ⁻¹)
  have hQ : ∀ s t u, (Q : Matrix (Fin d) (Fin d) E) *ᵥ planeMap H' (s, t, u) =
      planeMap H' ((γ : E) * s, σ ((γ⁻¹ : Eˣ) : E) * t, u) := fun s t u => scaleMat_mulVec hb _ _ s t u
  have ex : H'.x = planeMap H' (1, 0, 0) := by simp [planeMap_apply]
  have ey : H'.y = planeMap H' (0, 1, 0) := by simp [planeMap_apply]
  have eι : ∀ u, H'.ι *ᵥ u = planeMap H' (0, 0, u) := fun u => by simp [planeMap_apply]
  have hQι : (Q : Matrix (Fin d) (Fin d) E) * H'.ι = H'.ι := matrix_ext_mulVec fun u => by
    rw [← Matrix.mulVec_mulVec, eι, hQ]; simp
  have e : mat m = incM F (Q : Matrix (Fin d) (Fin d) E) := by
    refine matA_ext hb.2 ?_ ?_ ?_
    · rw [hm.1, ← incV_mulVec, ex, hQ, ← ex]
      simp [planeMap_apply, incV_smul]
    · rw [hm.2.1, ← incV_mulVec, ey, hQ, ← ey]
      simp only [planeMap_apply, mul_zero, mul_one, zero_smul, Matrix.mulVec_zero, zero_add, add_zero, incV_smul]
      rw [← map_inv, Units.coe_map, ← cA_inclR]
      rfl
    · rw [hm.2.2, mat_one', Matrix.mul_one, incM, incM, ← Matrix.map_mul, hQι]
  refine Subgroup.mem_subgroupOf.2 ⟨Q, Units.ext ?_⟩
  exact e.symm

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 800000 in

theorem ctLevi_principal : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ → ∀ (hσ : ∀ x, σ (σ x) = x) (c : E) (hc : c ≠ 0), σ c = -c → ∀ f : UA σ G.W.J → ℂ, (∃ K, IsMaxCpt σ (c • G.W.J.map σ) K ∧ IsAut σ (c • G.W.J.map σ) K (fun x => f ((toGAd hσ G.W.J hc).symm x))) → ∀ (μ : Measure (unip σ G.W H')) (𝓕 : Set (unip σ G.W H')), μ.IsHaarMeasure → IsFundamentalDomain ((ratU σ G.W.J).subgroupOf (unip σ G.W H')) 𝓕 μ → μ 𝓕 = 1 → ∀ h : UA σ G.W.J, ∀ (γ : Eˣ) (t : (AE F E)ˣ), ctLevi σ G.W W₁ H' μ 𝓕 f h (Units.map (inclR (F := F) (AF F)).toMonoidHom γ * t) = ctLevi σ G.W W₁ H' μ 𝓕 f h t := by
  intro _ F E _ _ _ _ _ σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hH hσ c hc _ f hf μ 𝓕 hμ h𝓕 hmass h₀ γ t
  have hb : Function.Bijective (planeMap H') := planeMap_bij hH hT.geo.hW.lat
  have hex := GlobalTheory.T.exists_levi_element_adapted F E σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hH
  set γ' := Units.map (inclR (F := F) (AF F)).toMonoidHom γ
  set m := leviElt σ G.W W₁ H' γ'
  set lt := leviElt σ G.W W₁ H' t
  have hm : IsLevi (W₁ := W₁) H' γ' 1 m := isLevi_leviElt (hex γ')
  have hprod : leviElt σ G.W W₁ H' (γ' * t) = m * lt :=
    levi_unique hb.2 (isLevi_leviElt (hex _)) (levi_mul hm (isLevi_leviElt (hex t)))
  have hrat : m ∈ ratU σ G.W.J := levi_mem_ratU hb γ hm

  have hinv : ∀ g ∈ ratU σ G.W.J, ∀ x, f (g * x) = f x := by
    obtain ⟨K, -, hA⟩ := hf
    intro g hg x
    have hP : toGAd hσ G.W.J hc g ∈ ratPts σ (c • G.W.J.map σ) := by
      obtain ⟨q, hq⟩ := Subgroup.mem_subgroupOf.1 hg
      refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨q, ?_, hq⟩)
      exact unitary_of_map_inclR σ _ _ q _ (by rw [hq]; rfl) (toGAd hσ G.W.J hc g).2
    have := hA.mod.left _ hP (toGAd hσ G.W.J hc x)
    simpa [map_mul] using this

  have hι : ∀ z, mat m *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z := fun z => by
    rw [Matrix.mulVec_mulVec, hm.2.2, mat_one', Matrix.mul_one]
  obtain ⟨hx', hι'⟩ := inv_data hm.1 hι
  have hA : ∀ u ∈ unip σ G.W H', m⁻¹ * u * m ∈ unip σ G.W H' := fun u hu => conj_mem_unip hm.1 hι hu
  have hB : ∀ u ∈ unip σ G.W H', m * u * m⁻¹ ∈ unip σ G.W H' := fun u hu => by
    simpa using conj_mem_unip hx' hι' hu
  let ce : unip σ G.W H' ≃* unip σ G.W H' :=
    { toFun := fun u => ⟨m⁻¹ * u.1 * m, hA _ u.2⟩
      invFun := fun u => ⟨m * u.1 * m⁻¹, hB _ u.2⟩
      left_inv := fun u => Subtype.ext (by simp [mul_assoc])
      right_inv := fun u => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun u v => Subtype.ext (by simp [mul_assoc]) }
  have hce : ∀ u, (ce u).1 = m⁻¹ * u.1 * m := fun u => rfl
  have hces : ∀ u, (ce.symm u).1 = m * u.1 * m⁻¹ := fun u => rfl
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : IsTopologicalGroup (UA σ G.W.J) := inferInstance
  haveI : BorelSpace (UA σ G.W.J) := ⟨rfl⟩
  have hc1 : Continuous ce :=
    Continuous.subtype_mk ((continuous_const.mul continuous_subtype_val).mul continuous_const) _
  have hc2 : Continuous ce.symm :=
    Continuous.subtype_mk ((continuous_const.mul continuous_subtype_val).mul continuous_const) _
  let tt : unip σ G.W H' ≃ₜ unip σ G.W H' := ⟨ce.toEquiv, hc1, hc2⟩
  let me := tt.toMeasurableEquiv
  have hp : MeasurePreserving me μ (μ.map me) := ⟨me.measurable, rfl⟩
  have hHaar : (μ.map me).IsHaarMeasure := MulEquiv.isHaarMeasure_map μ ce hc1 hc2
  have hps : MeasurePreserving me.symm (μ.map me) μ := hp.symm

  let Γ := (ratU σ G.W.J).subgroupOf (unip σ G.W H')
  have hΓ : ∀ g : Γ, ce g.1 ∈ Γ := fun g => by
    refine Subgroup.mem_subgroupOf.2 ?_
    rw [hce]
    exact mul_mem (mul_mem (inv_mem hrat) (Subgroup.mem_subgroupOf.1 g.2)) hrat
  have hΓ' : ∀ g : Γ, ce.symm g.1 ∈ Γ := fun g => by
    refine Subgroup.mem_subgroupOf.2 ?_
    rw [hces]
    exact mul_mem (mul_mem hrat (Subgroup.mem_subgroupOf.1 g.2)) (inv_mem hrat)
  let eΓ : Γ → Γ := fun g => ⟨ce g.1, hΓ g⟩
  have heΓ : Function.Bijective eΓ :=
    ⟨fun x y hxy => Subtype.ext (ce.injective (congrArg Subtype.val hxy)),
      fun g => ⟨⟨ce.symm g.1, hΓ' g⟩, Subtype.ext (ce.apply_symm_apply g.1)⟩⟩
  have hfd : IsFundamentalDomain Γ (me.symm ⁻¹' 𝓕) (μ.map me) :=
    h𝓕.preimage_of_equiv hps.quasiMeasurePreserving heΓ fun g x => by
      show ce.symm (ce g.1 * x) = g.1 * ce.symm x
      rw [map_mul, ce.symm_apply_apply]
  have hset : me ⁻¹' (me.symm ⁻¹' 𝓕) = 𝓕 := by
    ext x
    simp
  have hmass' : (μ.map me) (me.symm ⁻¹' 𝓕) = 1 := by
    rw [MeasurableEquiv.map_apply, hset, hmass]
  have hCT := GlobalTheory.T.constant_term_unipotent_integral F E σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hH f hinv μ 𝓕 hμ h𝓕 hmass
  have key := hCT (μ.map me) (me.symm ⁻¹' 𝓕) hHaar hfd hmass' (lt * h₀)
  have hint := hp.setIntegral_preimage_emb me.measurableEmbedding (fun u : unip σ G.W H' => f (u.1 * (lt * h₀)))
    (me.symm ⁻¹' 𝓕)
  rw [hset] at hint
  have hpt : ∀ u : unip σ G.W H', f (u.1 * (m * lt * h₀)) = f ((me u).1 * (lt * h₀)) := fun u => by
    have h1 := hinv m⁻¹ (inv_mem hrat) (u.1 * (m * lt * h₀))
    rw [← h1]
    show f _ = f ((m⁻¹ * u.1 * m) * (lt * h₀))
    congr 1
    simp only [mul_assoc]
  rw [ctLevi_apply, ctLevi_apply, hprod]
  simp_rw [hpt]
  rw [hint]
  exact key.symm

end GlobalTheory.ThKCtFin.LeftInvLevi

end
