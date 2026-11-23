import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBTransport
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc

set_option autoImplicit false

noncomputable section

open TensorProduct

namespace ReciprocityTheory.ChartRestriction.G.DVR.FlatBC

variable {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

theorem flat_ker_rank_one (δ : M →ₗ[R] N) (θ : M) (hker : ∀ m, δ m = 0 ↔ ∃ r : R, m = r • θ)
    (hfree : ∀ r : R, r • θ = 0 → r = 0) (t : S ⊗[R] M) (ht : δ.lTensor S t = 0) :
    ∃! a : S, t = a ⊗ₜ[R] θ := by
  let ι : R →ₗ[R] M := LinearMap.toSpanSingleton R M θ
  have hex : Function.Exact ι δ := by
    intro m
    constructor
    · intro h
      obtain ⟨r, rfl⟩ := (hker m).1 h
      exact ⟨r, rfl⟩
    · rintro ⟨r, rfl⟩
      exact (hker _).2 ⟨r, rfl⟩
  have hinj : Function.Injective ι := fun r r' h => by
    have : (r - r') • θ = 0 := by rw [sub_smul]; exact sub_eq_zero.2 h
    exact sub_eq_zero.1 (hfree _ this)
  have hexS : Function.Exact (ι.lTensor S) (δ.lTensor S) := Module.Flat.lTensor_exact S hex
  have hinjS : Function.Injective (ι.lTensor S) := Module.Flat.lTensor_preserves_injective_linearMap ι hinj
  obtain ⟨x, hx⟩ := (hexS t).1 ht
  have key : ∀ a : S, ι.lTensor S (a ⊗ₜ[R] (1 : R)) = a ⊗ₜ[R] θ := fun a => by
    simp [ι, LinearMap.lTensor_tmul]
  have hxa : x = (TensorProduct.rid R S x) ⊗ₜ[R] (1 : R) := by
    conv_lhs => rw [← (TensorProduct.rid R S).symm_apply_apply x]
    rfl
  refine ⟨TensorProduct.rid R S x, ?_, fun a ha => ?_⟩
  · show t = _
    rw [← hx, ← key]; exact congrArg _ hxa
  · have h1 : ι.lTensor S (a ⊗ₜ[R] (1 : R)) = ι.lTensor S x := by rw [key, hx, ha]
    have h2 := congrArg (TensorProduct.rid R S) (hinjS h1)
    simpa using h2

theorem flat_ker_rank_one_r (δ : M →ₗ[R] N) (θ : M) (hker : ∀ m, δ m = 0 ↔ ∃ r : R, m = r • θ)
    (hfree : ∀ r : R, r • θ = 0 → r = 0) (t : M ⊗[R] S) (ht : δ.rTensor S t = 0) :
    ∃! a : S, t = θ ⊗ₜ[R] a := by
  have hcomm : ∀ t : M ⊗[R] S, δ.lTensor S (TensorProduct.comm R M S t) = TensorProduct.comm R N S (δ.rTensor S t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul m s => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  have ht' : δ.lTensor S (TensorProduct.comm R M S t) = 0 := by rw [hcomm, ht, map_zero]
  obtain ⟨a, ha, hu⟩ := flat_ker_rank_one δ θ hker hfree _ ht'
  refine ⟨a, ?_, fun b hb => hu b ?_⟩
  · apply (TensorProduct.comm R M S).injective
    rw [ha]; simp
  · rw [hb]; simp

omit [Module.Flat R S] in
lemma piLeft_apply_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (Mi : ι → Type*) [∀ i, AddCommGroup (Mi i)] [∀ i, Module R (Mi i)]
    (x : (∀ i, Mi i) ⊗[R] S) (i : ι) :
    (TensorProduct.piLeft (R := R) (N := S) (M := Mi)) x i = (LinearMap.proj i : (∀ i, Mi i) →ₗ[R] Mi i).rTensor S x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m s => simp
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

section Cover

open AlgebraicGeometry CategoryTheory TopologicalSpace ReciprocityTheory.ChartRestriction.G.Semi

theorem exists_affine_chart_cover {X : Scheme.{0}} [CompactSpace X] (L : LB X) (hL : L.IsLB) :
    ∃ (n : ℕ) (V : Fin n → X.Opens) (c : Fin n → L.ι), (∀ k, IsAffineOpen (V k)) ∧ (∀ k, V k ≤ L.U (c k)) ∧
      ⨆ k, V k = ⊤ := by
  classical
  have hx : ∀ x : X, ∃ (c : L.ι) (V : X.Opens), IsAffineOpen V ∧ V ≤ L.U c ∧ x ∈ V := by
    intro x
    have : x ∈ (⨆ i, L.U i : X.Opens) := by rw [hL.cover]; trivial
    obtain ⟨c, hc⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    obtain ⟨V, hV, hxV, hVc⟩ := (Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens) hc
    exact ⟨c, V, hV, hVc, hxV⟩
  choose c V hVa hVc hxV using hx
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (V x : Set X)) (fun x => (V x).isOpen)
    (fun x _ => Set.mem_iUnion.2 ⟨x, hxV x⟩)
  refine ⟨t.card, fun k => V (t.equivFin.symm k), fun k => c (t.equivFin.symm k), fun k => hVa _, fun k => hVc _, ?_⟩
  rw [eq_top_iff]
  intro y _
  obtain ⟨x, hx, hy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨t.equivFin ⟨x, hx⟩, by simpa using hy⟩

end Cover

section Cech

open AlgebraicGeometry CategoryTheory TopologicalSpace ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR

variable {Y : Scheme.{0}} (L : LB Y) {n : ℕ} (V : Fin n → Y.Opens) (c : Fin n → L.ι) (hVc : ∀ k, V k ≤ L.U (c k))

include hVc in
lemma pair_le (k l : Fin n) : V k ⊓ V l ≤ L.U (c k) ⊓ L.U (c l) := inf_le_inf (hVc k) (hVc l)

def ev (σ : LB.Sec L) : ∀ k, Γ(Y, V k) := fun k => rs (hVc k) (σ.f (c k))

def dfun (f : ∀ k, Γ(Y, V k)) : ∀ k l, Γ(Y, V k ⊓ V l) := fun k l =>
  rs inf_le_left (f k) - (res (pair_le L V c hVc k l) (L.g (c k) (c l))).val * rs inf_le_right (f l)

lemma dfun_ev (σ : LB.Sec L) : dfun L V c hVc (ev L V c hVc σ) = 0 := by
  funext k l
  have e := congrArg (rs (pair_le L V c hVc k l)) (σ.compat (c k) (c l))
  simp only [rs_mul, rs_rs, rs_units] at e
  simp only [dfun, ev, rs_rs, Pi.zero_apply]
  rw [sub_eq_zero]
  exact e

open ReciprocityTheory.ChartRestriction.G.Geo.Tor in
lemma gs_dfun {f : ∀ k, Γ(Y, V k)} (hf : dfun L V c hVc f = 0) (k l : Fin n) (y : Y) (hk : y ∈ V k) (hl : y ∈ V l) :
    gs (𝟙 Y) y (V k) (f k) = (gm (𝟙 Y) y (L.U (c k) ⊓ L.U (c l)) (L.g (c k) (c l))).val * gs (𝟙 Y) y (V l) (f l) := by
  have e := sub_eq_zero.1 (congrFun (congrFun hf k) l)
  have hy : y ∈ V k ⊓ V l := ⟨hk, hl⟩
  have e2 := congrArg (gs (𝟙 Y) y (V k ⊓ V l)) e
  rw [gs_res _ y _ hy, gs_mul _ y _ hy, gs_res _ y _ hy, gs_unit _ y _ hy, gm_res _ y _ hy] at e2
  exact e2

open ReciprocityTheory.ChartRestriction.G.Geo.Tor in

theorem exists_glue (hL : L.IsLB) (hcov : ⨆ k, V k = ⊤) (f : ∀ k, Γ(Y, V k)) (hf : dfun L V c hVc f = 0) :
    ∃ σ : LB.Sec L, ev L V c hVc σ = f := by
  classical
  have hcovi : ∀ i, L.U i ≤ ⨆ k, L.U i ⊓ V k := fun i y hy => by
    have : y ∈ (⨆ k, V k : Y.Opens) := by rw [hcov]; trivial
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hy, hk⟩
  have hle : ∀ i k, L.U i ⊓ V k ≤ L.U i ⊓ L.U (c k) := fun i k => inf_le_inf le_rfl (hVc k)
  let cand : ∀ i k, Γ(Y, L.U i ⊓ V k) := fun i k =>
    (res (hle i k) (L.g i (c k))).val * rs inf_le_right (f k)
  have gcand : ∀ i k y (hy : y ∈ L.U i ⊓ V k), gs (𝟙 Y) y _ (cand i k) =
      (gm (𝟙 Y) y (L.U i ⊓ L.U (c k)) (L.g i (c k))).val * gs (𝟙 Y) y (V k) (f k) := fun i k y hy => by
    simp only [cand]
    rw [gs_mul _ y _ hy, gs_unit _ y _ hy, gm_res _ y _ hy, gs_res _ y _ hy]
  have hcompat : ∀ i k l, rs (inf_le_left : (L.U i ⊓ V k) ⊓ (L.U i ⊓ V l) ≤ _) (cand i k) =
      rs (inf_le_right : (L.U i ⊓ V k) ⊓ (L.U i ⊓ V l) ≤ _) (cand i l) := fun i k l => fn_ext fun y hy => by
    rw [gs_res _ y _ hy, gs_res _ y _ hy, gcand i k y hy.1, gcand i l y hy.2,
      gs_dfun L V c hVc hf k l y hy.1.2 hy.2.2, ← mul_assoc, ← Units.val_mul,
      gm_cocycle hL (𝟙 Y) y (i := i) (j := c k) (k := c l) hy.1.1 (hVc k hy.1.2) (hVc l hy.2.2)]
  choose F hF _ using fun i => sec_glue (L.U i) (fun k => L.U i ⊓ V k) (fun _ => inf_le_left) (hcovi i)
    (cand i) (hcompat i)
  have gF : ∀ i k y (hyi : y ∈ L.U i) (hyk : y ∈ V k), gs (𝟙 Y) y (L.U i) (F i) =
      (gm (𝟙 Y) y (L.U i ⊓ L.U (c k)) (L.g i (c k))).val * gs (𝟙 Y) y (V k) (f k) := fun i k y hyi hyk => by
    have hyik : y ∈ L.U i ⊓ V k := ⟨hyi, hyk⟩
    have e := congrArg (gs (𝟙 Y) y (L.U i ⊓ V k)) (hF i k)
    rw [gs_res _ y _ hyik] at e
    rw [e, gcand i k y hyik]
  have hmemV : ∀ y : Y, ∃ k, y ∈ V k := fun y => by
    have : y ∈ (⨆ k, V k : Y.Opens) := by rw [hcov]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 this
  refine ⟨⟨F, fun i j => fn_ext fun y hy => ?_⟩, ?_⟩
  · obtain ⟨k, hk⟩ := hmemV y
    rw [gs_res _ y _ hy, gs_mul _ y _ hy, gs_res _ y _ hy, gs_unit _ y _ hy, gF i k y hy.1 hk, gF j k y hy.2 hk,
      ← mul_assoc, ← Units.val_mul, gm_cocycle hL (𝟙 Y) y (i := i) (j := j) (k := c k) hy.1 hy.2 (hVc k hk)]
  · funext k
    refine fn_ext fun y hy => ?_
    show gs (𝟙 Y) y (V k) (rs (hVc k) (F (c k))) = _
    rw [gs_res _ y _ hy, gF (c k) k y (hVc k hy) hy, gm_self hL (𝟙 Y) y (hVc k hy), Units.val_one, one_mul]

open ReciprocityTheory.ChartRestriction.G.Geo.Tor in
lemma gs_sec (σ : LB.Sec L) (i j : L.ι) (y : Y) (hi : y ∈ L.U i) (hj : y ∈ L.U j) :
    gs (𝟙 Y) y (L.U i) (σ.f i) = (gm (𝟙 Y) y (L.U i ⊓ L.U j) (L.g i j)).val * gs (𝟙 Y) y (L.U j) (σ.f j) := by
  have hy : y ∈ L.U i ⊓ L.U j := ⟨hi, hj⟩
  have e := congrArg (gs (𝟙 Y) y (L.U i ⊓ L.U j)) (σ.compat i j)
  rw [gs_res _ y _ hy, gs_mul _ y _ hy, gs_res _ y _ hy, gs_unit _ y _ hy] at e
  exact e

open ReciprocityTheory.ChartRestriction.G.Geo.Tor in

theorem ev_inj (hcov : ⨆ k, V k = ⊤) {σ τ : LB.Sec L} (h : ev L V c hVc σ = ev L V c hVc τ) : σ = τ := by
  have hf : σ.f = τ.f := by
    funext i
    refine fn_ext fun y hy => ?_
    have : y ∈ (⨆ k, V k : Y.Opens) := by rw [hcov]; trivial
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    have hk' := congrArg (gs (𝟙 Y) y (V k)) (congrFun h k)
    simp only [ev] at hk'
    rw [gs_res _ y _ hk, gs_res _ y _ hk] at hk'
    rw [gs_sec L σ i (c k) y hy (hVc k hk), gs_sec L τ i (c k) y hy (hVc k hk), hk']
  cases σ; cases τ
  simp only at hf
  subst hf
  rfl

end Cech

section Pushout

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] {X X' : Scheme.{0}}
  (p : X ⟶ Spec (CommRingCat.of R)) (p' : X' ⟶ Spec (CommRingCat.of S)) (φ : X' ⟶ X)
  (H : IsPullback φ p' p (Spec.map (CommRingCat.ofHom (algebraMap R S))))

def algX (U : X.Opens) : R →+* Γ(X, U) :=
  (p.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

include H in

theorem isPushout_sections (U : X.Opens) (hU : IsAffineOpen U) :
    IsPushout (CommRingCat.ofHom (algX p U)) (CommRingCat.ofHom (algebraMap R S))
      (φ.appLE U (φ ⁻¹ᵁ U ⊓ p' ⁻¹ᵁ ⊤) inf_le_left) (CommRingCat.ofHom (algX p' (φ ⁻¹ᵁ U ⊓ p' ⁻¹ᵁ ⊤))) := by
  have hST : (⊤ : (Spec (CommRingCat.of S)).Opens) ≤ Spec.map (CommRingCat.ofHom (algebraMap R S)) ⁻¹ᵁ ⊤ := le_top
  have hSX : U ≤ p ⁻¹ᵁ ⊤ := le_top
  haveI := isIso_pushoutSection_of_isAffineOpen H hST hSX rfl (isAffineOpen_top _) (isAffineOpen_top _) hU
  have hP := (isIso_pushoutSection_iff H hST hSX rfl).1 inferInstance
  refine hP.of_iso (Scheme.ΓSpecIso (CommRingCat.of R)) (Iso.refl _) (Scheme.ΓSpecIso (CommRingCat.of S)) (Iso.refl _)
    ?_ ?_ ?_ ?_
  · ext x; simp [algX]
  · have e : (Spec.map (CommRingCat.ofHom (algebraMap R S))).appLE ⊤ ⊤ hST =
        (Spec.map (CommRingCat.ofHom (algebraMap R S))).appTop := by
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      congr 1
    rw [e]
    exact Scheme.ΓSpecIso_naturality _
  · simp
  · ext x
    simp only [algX, CommRingCat.comp_apply, CommRingCat.hom_ofHom, RingHom.comp_apply, Iso.refl_hom,
      CommRingCat.id_apply]
    rw [← CommRingCat.comp_apply (Scheme.ΓSpecIso (CommRingCat.of S)).hom, Iso.hom_inv_id, CommRingCat.id_apply]

omit [Algebra R S] in
lemma rs_algX (U U' : X.Opens) (h : U' ≤ U) (r : R) :
    ReciprocityTheory.ChartRestriction.G.DVR.rs h (algX p U r) = algX p U' r := by
  simp only [algX, RingHom.comp_apply, ReciprocityTheory.ChartRestriction.G.DVR.rs]
  erw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

def eTens (U : X.Opens) (hU : IsAffineOpen U) :
    letI := (algX p U).toAlgebra
    Γ(X, U) ⊗[R] S ≃+* Γ(X', φ ⁻¹ᵁ U ⊓ p' ⁻¹ᵁ ⊤) :=
  letI := (algX p U).toAlgebra
  ((CommRingCat.isPushout_tensorProduct R Γ(X, U) S).isoIsPushout _ _
    (isPushout_sections p p' φ H U hU)).commRingCatIsoToRingEquiv

lemma eTens_tmul (U : X.Opens) (hU : IsAffineOpen U) (a : Γ(X, U)) (s : S) :
    letI := (algX p U).toAlgebra
    eTens p p' φ H U hU (a ⊗ₜ[R] s) = (φ.appLE U _ inf_le_left).hom a * algX p' _ s := by
  letI := (algX p U).toAlgebra
  have h1 := congrArg (fun q => q.hom a)
    (IsPushout.inl_isoIsPushout_hom _ _ (CommRingCat.isPushout_tensorProduct R Γ(X, U) S)
      (isPushout_sections p p' φ H U hU))
  have h2 := congrArg (fun q => q.hom s)
    (IsPushout.inr_isoIsPushout_hom _ _ (CommRingCat.isPushout_tensorProduct R Γ(X, U) S)
      (isPushout_sections p p' φ H U hU))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h1 h2
  have e : a ⊗ₜ[R] s = (a ⊗ₜ[R] (1 : S)) * ((1 : Γ(X, U)) ⊗ₜ[R] s) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [e, map_mul]
  exact congrArg₂ (· * ·) h1 h2

omit [Algebra R S] in

def rsL (U U' : X.Opens) (h : U' ≤ U) :
    letI := (algX p U).toAlgebra; letI := (algX p U').toAlgebra
    Γ(X, U) →ₗ[R] Γ(X, U') :=
  letI := (algX p U).toAlgebra; letI := (algX p U').toAlgebra
  { toFun := ReciprocityTheory.ChartRestriction.G.DVR.rs h
    map_add' := fun a b => map_add _ a b
    map_smul' := fun r a => by
      simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra, RingHom.id_apply]
      rw [ReciprocityTheory.ChartRestriction.G.DVR.rs_mul, rs_algX] }

omit [Algebra R S] in

def mulL (U : X.Opens) (u : Γ(X, U)) :
    letI := (algX p U).toAlgebra
    Γ(X, U) →ₗ[R] Γ(X, U) :=
  letI := (algX p U).toAlgebra
  { toFun := fun a => u * a
    map_add' := fun a b => mul_add u a b
    map_smul' := fun r a => by
      simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra, RingHom.id_apply]
      ring }

lemma eTens_rs (U U' : X.Opens) (hU : IsAffineOpen U) (hU' : IsAffineOpen U') (h : U' ≤ U)
    (x : letI := (algX p U).toAlgebra; Γ(X, U) ⊗[R] S) :
    letI := (algX p U).toAlgebra; letI := (algX p U').toAlgebra
    eTens p p' φ H U' hU' ((rsL p U U' h).rTensor S x) =
      ReciprocityTheory.ChartRestriction.G.DVR.rs (inf_le_inf (Scheme.Hom.preimage_mono φ h) le_rfl) (eTens p p' φ H U hU x) := by
  letI := (algX p U).toAlgebra; letI := (algX p U').toAlgebra
  induction x using TensorProduct.induction_on with
  | zero =>
    rw [map_zero, (eTens p p' φ H U' hU').map_zero, (eTens p p' φ H U hU).map_zero]
    exact (map_zero _).symm
  | tmul a s =>
    rw [LinearMap.rTensor_tmul, eTens_tmul, eTens_tmul, ReciprocityTheory.ChartRestriction.G.DVR.rs_mul, rs_algX]
    congr 1
    show (φ.appLE U' _ _).hom (ReciprocityTheory.ChartRestriction.G.DVR.rs h a) = ReciprocityTheory.ChartRestriction.G.DVR.rs _ ((φ.appLE U _ _).hom a)
    simp only [ReciprocityTheory.ChartRestriction.G.DVR.rs]
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]
  | add x y hx hy => simp only [map_add, hx, hy]

lemma eTens_mul (U : X.Opens) (hU : IsAffineOpen U) (u : Γ(X, U))
    (x : letI := (algX p U).toAlgebra; Γ(X, U) ⊗[R] S) :
    letI := (algX p U).toAlgebra
    eTens p p' φ H U hU ((mulL p U u).rTensor S x) = (φ.appLE U _ inf_le_left).hom u * eTens p p' φ H U hU x := by
  letI := (algX p U).toAlgebra
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, (eTens p p' φ H U hU).map_zero, mul_zero]
  | tmul a s =>
    rw [LinearMap.rTensor_tmul, eTens_tmul, eTens_tmul]
    show (φ.appLE U _ _).hom (u * a) * _ = _
    rw [map_mul]; ring
  | add x y hx hy => simp only [map_add, hx, hy, mul_add]

end Pushout

section Main

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] {X X' : Scheme.{0}}
  (p : X ⟶ Spec (CommRingCat.of R)) (p' : X' ⟶ Spec (CommRingCat.of S)) (φ : X' ⟶ X)
  (H : IsPullback φ p' p (Spec.map (CommRingCat.ofHom (algebraMap R S))))

omit [Algebra R S] in

def smulSec (L : LB X) (a : R) (θ : LB.Sec L) : LB.Sec L where
  f i := algX p (L.U i) a * θ.f i
  compat i j := by
    show ReciprocityTheory.ChartRestriction.G.DVR.rs _ (_ * _) = _ * ReciprocityTheory.ChartRestriction.G.DVR.rs _ (_ * _)
    have e : ReciprocityTheory.ChartRestriction.G.DVR.rs (inf_le_left : L.U i ⊓ L.U j ≤ L.U i) (θ.f i) =
        (L.g i j).val * ReciprocityTheory.ChartRestriction.G.DVR.rs (inf_le_right : L.U i ⊓ L.U j ≤ L.U j) (θ.f j) := θ.compat i j
    rw [rs_mul, rs_mul, rs_algX, rs_algX, e]
    ring

omit [Algebra R S] in
lemma ev_smulSec (L : LB X) {n : ℕ} (V : Fin n → X.Opens) (c : Fin n → L.ι) (hVc : ∀ k, V k ≤ L.U (c k))
    (a : R) (θ : LB.Sec L) (k : Fin n) :
    ev L V c hVc (smulSec p L a θ) k = algX p (V k) a * ev L V c hVc θ k := by
  simp only [ev, smulSec, rs_mul, rs_algX]

include H in

theorem flatBC_gen [Module.Flat R S] [CompactSpace X]
    (hinter : ∀ U W : X.Opens, IsAffineOpen U → IsAffineOpen W → IsAffineOpen (U ⊓ W))
    (L : LB X) (hL : L.IsLB) (θ : LB.Sec L)
    (hθ : ∀ σ : LB.Sec L, ∃! a : R, ∀ i, σ.f i = algX p (L.U i) a * θ.f i)
    (θ' : LB.Sec (L.pull φ))
    (hθ' : ∀ j (h : (L.pull φ).U j ≤ φ ⁻¹ᵁ L.U (j PUnit.unit)), θ'.f j = (φ.appLE _ _ h).hom (θ.f (j PUnit.unit))) :
    ∀ σ' : LB.Sec (L.pull φ), ∃! a : S, ∀ i, σ'.f i = algX p' ((L.pull φ).U i) a * θ'.f i := by
  classical
  obtain ⟨n, V, c, hVa, hVc, hcov⟩ := exists_affine_chart_cover L hL
  letI instV : ∀ k, Algebra R Γ(X, V k) := fun k => (algX p (V k)).toAlgebra
  letI instW : ∀ kl : Fin n × Fin n, Algebra R Γ(X, V kl.1 ⊓ V kl.2) := fun kl => (algX p _).toAlgebra
  let δ : (∀ k, Γ(X, V k)) →ₗ[R] (∀ kl : Fin n × Fin n, Γ(X, V kl.1 ⊓ V kl.2)) :=
    { toFun := fun f kl => dfun L V c hVc f kl.1 kl.2
      map_add' := fun f g => by
        funext kl
        simp only [dfun, Pi.add_apply, map_add, mul_add]
        abel
      map_smul' := fun r f => by
        funext kl
        simp only [dfun, RingHom.id_apply, Pi.smul_apply, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
        rw [rs_mul, rs_mul, rs_algX, rs_algX]
        ring }
  have hδ : ∀ m, δ m = 0 ↔ dfun L V c hVc m = 0 := fun m => by
    constructor
    · intro h; funext k l; exact congrFun h (k, l)
    · intro h; funext kl; exact congrFun (congrFun h kl.1) kl.2
  have hevsmul : ∀ (a : R) (σ : LB.Sec L), ev L V c hVc (smulSec p L a σ) = a • ev L V c hVc σ := fun a σ => by
    funext k
    rw [ev_smulSec]
    rfl
  have hker : ∀ m, δ m = 0 ↔ ∃ r : R, m = r • ev L V c hVc θ := fun m => by
    rw [hδ]
    constructor
    · intro h
      obtain ⟨σ, hσ⟩ := exists_glue L V c hVc hL hcov m h
      obtain ⟨a, ha, -⟩ := hθ σ
      have : σ = smulSec p L a θ := by
        cases σ with | mk f cp =>
        simp only [smulSec, LB.Sec.mk.injEq]
        funext i; exact ha i
      exact ⟨a, by rw [← hσ, this, hevsmul]⟩
    · rintro ⟨r, rfl⟩
      rw [← hevsmul, dfun_ev]
  have hfree : ∀ r : R, r • ev L V c hVc θ = 0 → r = 0 := fun r hr => by
    have e : smulSec p L r θ = smulSec p L 0 θ := ev_inj L V c hVc hcov (by rw [hevsmul, hevsmul, hr, zero_smul])
    have h1 : ∀ i, (smulSec p L 0 θ).f i = algX p (L.U i) r * θ.f i := fun i => by rw [← e]; rfl
    have h0 : ∀ i, (smulSec p L 0 θ).f i = algX p (L.U i) 0 * θ.f i := fun i => rfl
    exact (hθ (smulSec p L 0 θ)).unique h1 h0
  intro σ'
  have hV'c : ∀ k, φ ⁻¹ᵁ V k ⊓ p' ⁻¹ᵁ ⊤ ≤ (L.pull φ).U (fun _ => c k) := fun k y hy =>
    Set.mem_iInter.2 fun _ => hVc k hy.1
  let m' : ∀ k, Γ(X', φ ⁻¹ᵁ V k ⊓ p' ⁻¹ᵁ ⊤) := fun k => rs (hV'c k) (σ'.f (fun _ => c k))
  let t : (∀ k, Γ(X, V k)) ⊗[R] S := (TensorProduct.piLeft (R := R) (N := S) (M := fun k => Γ(X, V k))).symm
    (fun k => (eTens p p' φ H (V k) (hVa k)).symm (m' k))
  have hpt : ∀ k, (TensorProduct.piLeft (R := R) (N := S) (M := fun k => Γ(X, V k))) t k =
      (eTens p p' φ H (V k) (hVa k)).symm (m' k) := fun k => by
    simp only [t, LinearEquiv.apply_symm_apply]
  have ht : δ.rTensor S t = 0 := by
    apply (TensorProduct.piLeft (R := R) (N := S) (M := fun kl : Fin n × Fin n => Γ(X, V kl.1 ⊓ V kl.2))).injective
    rw [map_zero]
    funext kl
    obtain ⟨k, l⟩ := kl
    rw [piLeft_apply_eq, ← LinearMap.rTensor_comp_apply]
    have hdec : (LinearMap.proj (k, l) : (∀ kl : Fin n × Fin n, Γ(X, V kl.1 ⊓ V kl.2)) →ₗ[R] _).comp δ =
        (rsL p (V k) (V k ⊓ V l) inf_le_left).comp (LinearMap.proj k) -
          (mulL p (V k ⊓ V l) (res (pair_le L V c hVc k l) (L.g (c k) (c l))).val).comp
            ((rsL p (V l) (V k ⊓ V l) inf_le_right).comp (LinearMap.proj l)) := by
      ext f; rfl
    rw [hdec, LinearMap.rTensor_sub, LinearMap.sub_apply, LinearMap.rTensor_comp_apply, LinearMap.rTensor_comp_apply,
      LinearMap.rTensor_comp_apply, ← piLeft_apply_eq, ← piLeft_apply_eq, hpt, hpt]
    apply (eTens p p' φ H (V k ⊓ V l) (hinter _ _ (hVa k) (hVa l))).injective
    rw [map_sub, eTens_rs p p' φ H (V k) (V k ⊓ V l) (hVa k) _ inf_le_left, eTens_mul,
      eTens_rs p p' φ H (V l) (V k ⊓ V l) (hVa l) _ inf_le_right, RingEquiv.apply_symm_apply,
      RingEquiv.apply_symm_apply, Pi.zero_apply, map_zero, sub_eq_zero]
    refine ReciprocityTheory.ChartRestriction.G.Geo.Tor.fn_ext fun y hy => ?_
    have hyk : y ∈ (L.pull φ).U (fun _ => c k) := Set.mem_iInter.2 fun _ => hVc k hy.1.1
    have hyl : y ∈ (L.pull φ).U (fun _ => c l) := Set.mem_iInter.2 fun _ => hVc l hy.1.2
    have hyk' : y ∈ φ ⁻¹ᵁ V k ⊓ p' ⁻¹ᵁ ⊤ := ⟨hy.1.1, hy.2⟩
    have hyl' : y ∈ φ ⁻¹ᵁ V l ⊓ p' ⁻¹ᵁ ⊤ := ⟨hy.1.2, hy.2⟩
    have hφy : φ y ∈ V k ⊓ V l := hy.1
    simp only [m']
    rw [Geo.Tor.gs_mul _ y _ hy, Geo.Tor.gs_res _ y _ hy, Geo.Tor.gs_res _ y _ hyk', Geo.Tor.gs_res _ y _ hy,
      Geo.Tor.gs_res _ y _ hyl', Geo.Tor.gs_appLE φ _ _ _ (𝟙 _) y hy]
    erw [Category.id_comp, Geo.Tor.gs_unit _ y _ hφy, Geo.Tor.gm_res _ y _ hφy]
    erw [gs_sec (L.pull φ) σ' (fun _ => c k) (fun _ => c l) y hyk hyl,
      Geo.Tor.gm_pull_g L φ (𝟙 _) y (fun _ => c k) (fun _ => c l) hyk hyl, Category.id_comp]
  obtain ⟨a, ha, hu⟩ := flat_ker_rank_one_r δ (ev L V c hVc θ) hker hfree t ht
  let V' : Fin n → X'.Opens := fun k => φ ⁻¹ᵁ V k ⊓ p' ⁻¹ᵁ ⊤
  let c' : Fin n → (L.pull φ).ι := fun k => fun _ => c k
  have hcov' : ⨆ k, V' k = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have : φ y ∈ (⨆ k, V k : X.Opens) := by rw [hcov]; trivial
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hk, trivial⟩
  have hmk : ∀ (b : S) k, ev (L.pull φ) V' c' hV'c (smulSec p' (L.pull φ) b θ') k =
      eTens p p' φ H (V k) (hVa k) (ev L V c hVc θ k ⊗ₜ[R] b) := fun b k => by
    rw [eTens_tmul]
    simp only [ev, smulSec]
    rw [rs_mul, rs_algX, mul_comm]
    congr 1
    have hle : (L.pull φ).U (c' k) ≤ φ ⁻¹ᵁ L.U (c k) := fun y hy => Set.mem_iInter.1 hy PUnit.unit
    rw [hθ' (c' k) hle]
    simp only [rs]
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  have hev' : ev (L.pull φ) V' c' hV'c σ' = m' := rfl
  have hm'eq : ∀ (b : S), t = ev L V c hVc θ ⊗ₜ[R] b → σ' = smulSec p' (L.pull φ) b θ' := fun b hb => by
    apply ev_inj (L.pull φ) V' c' hV'c hcov'
    funext k
    rw [hev', hmk]
    have h1 := hpt k
    rw [hb, piLeft_apply_eq, LinearMap.rTensor_tmul] at h1
    rw [show ((LinearMap.proj k : (∀ k, Γ(X, V k)) →ₗ[R] Γ(X, V k)) (ev L V c hVc θ)) = ev L V c hVc θ k from rfl] at h1
    rw [h1, RingEquiv.apply_symm_apply]
  refine ⟨a, fun i => ?_, fun b hb => ?_⟩
  · rw [hm'eq a ha]; rfl
  · apply hu b
    have hσ : σ' = smulSec p' (L.pull φ) b θ' := by
      cases σ' with | mk f cp =>
      simp only [smulSec, LB.Sec.mk.injEq]
      funext i; exact hb i
    apply (TensorProduct.piLeft (R := R) (N := S) (M := fun k => Γ(X, V k))).injective
    funext k
    rw [hpt k, piLeft_apply_eq, LinearMap.rTensor_tmul]
    apply (eTens p p' φ H (V k) (hVa k)).injective
    rw [RingEquiv.apply_symm_apply, LinearMap.proj_apply, ← hmk, ← hev', hσ]

end Main

section IsoRel

open AlgebraicGeometry CategoryTheory TopologicalSpace ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {Y : Scheme.{0}} {L M : LB Y}

def IsoRel (w : LB.Iso L M) (s : LB.Sec L) (s' : LB.Sec M) : Prop :=
  ∀ (i : M.ι) (k : L.ι),
    (Y.presheaf.map (homOfLE (inf_le_left : M.U i ⊓ L.U k ≤ M.U i)).op).hom (s'.f i) =
      (show Γ(Y, M.U i ⊓ L.U k) from (w.s (i, k) : Γ(Y, (LB.div M L).U (i, k)))) *
        (Y.presheaf.map (homOfLE (inf_le_right : M.U i ⊓ L.U k ≤ L.U k)).op).hom (s.f k)

lemma gs_isoRel {w : LB.Iso L M} {s : LB.Sec L} {s' : LB.Sec M} (h : IsoRel w s s') (i : M.ι) (k : L.ι) (y : Y)
    (hi : y ∈ M.U i) (hk : y ∈ L.U k) :
    gs (𝟙 Y) y (M.U i) (s'.f i) = (gm (𝟙 Y) y ((LB.div M L).U (i, k)) (w.s (i, k))).val * gs (𝟙 Y) y (L.U k) (s.f k) := by
  have hy : y ∈ M.U i ⊓ L.U k := ⟨hi, hk⟩
  have e := congrArg (gs (𝟙 Y) y (M.U i ⊓ L.U k)) (h i k)
  rw [gs_res _ y _ hy, gs_mul _ y _ hy, gs_res _ y _ hy] at e
  rw [e]
  congr 1
  exact gs_unit _ y _ hy _

lemma isoRel_inj_left (hM : M.IsLB) {w : LB.Iso L M} {s t : LB.Sec L} {s' : LB.Sec M} (hs : IsoRel w s s')
    (ht : IsoRel w t s') : s = t := by
  have hf : s.f = t.f := by
    funext k
    refine fn_ext fun y hy => ?_
    obtain ⟨i, hi⟩ := exists_chart hM y
    have e1 := gs_isoRel hs i k y hi hy
    have e2 := gs_isoRel ht i k y hi hy
    rw [e1] at e2
    exact (Units.mul_right_inj _).1 e2.symm |>.symm
  cases s; cases t; simp only at hf; subst hf; rfl

lemma isoRel_inj_right (hL : L.IsLB) {w : LB.Iso L M} {s : LB.Sec L} {s' t' : LB.Sec M} (hs : IsoRel w s s')
    (ht : IsoRel w s t') : s' = t' := by
  have hf : s'.f = t'.f := by
    funext i
    refine fn_ext fun y hy => ?_
    obtain ⟨k, hk⟩ := exists_chart hL y
    rw [gs_isoRel hs i k y hy hk, gs_isoRel ht i k y hy hk]
  cases s'; cases t'; simp only at hf; subst hf; rfl

lemma gm_wgen {w : LB.Iso L M} (hw : w.IsGen) (i i' : M.ι) (k k' : L.ι) (y : Y) (hi : y ∈ M.U i) (hi' : y ∈ M.U i')
    (hk : y ∈ L.U k) (hk' : y ∈ L.U k') :
    gm (𝟙 Y) y ((LB.div M L).U (i, k)) (w.s (i, k)) =
      gm (𝟙 Y) y (M.U i ⊓ M.U i') (M.g i i') * (gm (𝟙 Y) y (L.U k ⊓ L.U k') (L.g k k'))⁻¹ *
        gm (𝟙 Y) y ((LB.div M L).U (i', k')) (w.s (i', k')) := by
  have hy : y ∈ (LB.div M L).U (i, k) ⊓ (LB.div M L).U (i', k') := ⟨⟨hi, hk⟩, ⟨hi', hk'⟩⟩
  have e := congrArg (gm (𝟙 Y) y _) (hw (i, k) (i', k'))
  rw [gm_res _ y _ hy, map_mul, gm_res _ y _ hy] at e
  rw [e]
  congr 1
  show gm (𝟙 Y) y _ (res _ (M.g i i') * (res _ (L.g k k'))⁻¹) = _
  erw [map_mul, map_inv, gm_res _ y _ hy, gm_res _ y _ hy]

lemma unit_alg {A : Type*} [CommRing A] (a b : Aˣ) (x : A) :
    ((a⁻¹ * b : Aˣ) : A) * ((a : A) * x) = (b : A) * x := by
  calc ((a⁻¹ * b : Aˣ) : A) * ((a : A) * x) = (((a⁻¹ : Aˣ) : A) * (a : A)) * ((b : A) * x) := by
        rw [Units.val_mul]; ring
    _ = (b : A) * x := by rw [Units.inv_mul, one_mul]

theorem exists_isoRel (hL : L.IsLB) (hM : M.IsLB) {w : LB.Iso L M} (hw : w.IsGen) (s : LB.Sec L) :
    ∃ s' : LB.Sec M, IsoRel w s s' := by
  classical
  have hcovi : ∀ i, M.U i ≤ ⨆ k, M.U i ⊓ L.U k := fun i y hy => by
    obtain ⟨k, hk⟩ := exists_chart hL y
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hy, hk⟩
  let cand : ∀ i k, Γ(Y, M.U i ⊓ L.U k) := fun i k =>
    (show Γ(Y, M.U i ⊓ L.U k) from (w.s (i, k) : Γ(Y, (LB.div M L).U (i, k)))) * rs inf_le_right (s.f k)
  have gcand : ∀ i k y (hy : y ∈ M.U i ⊓ L.U k), gs (𝟙 Y) y _ (cand i k) =
      (gm (𝟙 Y) y ((LB.div M L).U (i, k)) (w.s (i, k))).val * gs (𝟙 Y) y (L.U k) (s.f k) := fun i k y hy => by
    simp only [cand]
    erw [gs_mul _ y _ hy, gs_res _ y _ hy]
    congr 1
    exact gs_unit _ y _ hy _
  have hcompat : ∀ i k k', rs (inf_le_left : (M.U i ⊓ L.U k) ⊓ (M.U i ⊓ L.U k') ≤ _) (cand i k) =
      rs (inf_le_right : (M.U i ⊓ L.U k) ⊓ (M.U i ⊓ L.U k') ≤ _) (cand i k') := fun i k k' => fn_ext fun y hy => by
    rw [gs_res _ y _ hy, gs_res _ y _ hy, gcand i k y hy.1, gcand i k' y hy.2,
      gm_wgen hw i i k k' y hy.1.1 hy.1.1 hy.1.2 hy.2.2, gm_self hM (𝟙 Y) y hy.1.1, one_mul,
      gs_sec L s k k' y hy.1.2 hy.2.2]
    exact unit_alg _ _ _
  choose F hF _ using fun i => sec_glue (M.U i) (fun k => M.U i ⊓ L.U k) (fun _ => inf_le_left) (hcovi i)
    (cand i) (hcompat i)
  have gF : ∀ i k y (hyi : y ∈ M.U i) (hyk : y ∈ L.U k), gs (𝟙 Y) y (M.U i) (F i) =
      (gm (𝟙 Y) y ((LB.div M L).U (i, k)) (w.s (i, k))).val * gs (𝟙 Y) y (L.U k) (s.f k) := fun i k y hyi hyk => by
    have hyik : y ∈ M.U i ⊓ L.U k := ⟨hyi, hyk⟩
    have e := congrArg (gs (𝟙 Y) y (M.U i ⊓ L.U k)) (hF i k)
    rw [gs_res _ y _ hyik] at e
    rw [e, gcand i k y hyik]
  refine ⟨⟨F, fun i i' => fn_ext fun y hy => ?_⟩, fun i k => fn_ext fun y hy => ?_⟩
  · obtain ⟨k, hk⟩ := exists_chart hL y
    rw [gs_res _ y _ hy, gs_mul _ y _ hy, gs_res _ y _ hy, gs_unit _ y _ hy, gF i k y hy.1 hk, gF i' k y hy.2 hk,
      gm_wgen hw i i' k k y hy.1 hy.2 hk hk, gm_self hL (𝟙 Y) y hk, inv_one, mul_one, Units.val_mul, mul_assoc]
  · rw [gs_res _ y _ hy, gs_mul _ y _ hy, gs_res _ y _ hy, gF i k y hy.1 hy.2]
    congr 1
    exact (gs_unit _ y _ hy _).symm

end IsoRel

section IsoMain

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] {X X' : Scheme.{0}}
  (p : X ⟶ Spec (CommRingCat.of R)) (p' : X' ⟶ Spec (CommRingCat.of S)) (φ : X' ⟶ X)
  (H : IsPullback φ p' p (Spec.map (CommRingCat.ofHom (algebraMap R S))))

omit [Algebra R S] in
lemma isoRel_smul {L M : LB X} {w : LB.Iso L M} {s : LB.Sec L} {s' : LB.Sec M} (h : IsoRel w s s') (a : R) :
    IsoRel w (smulSec p L a s) (smulSec p M a s') := fun i k => by
  have e := h i k
  show rs _ (_ * _) = _ * rs _ (_ * _)
  rw [rs_mul, rs_mul, rs_algX, rs_algX]
  simp only [rs] at e ⊢
  rw [e]
  exact mul_left_comm _ _ _

include H in

theorem flatBC_iso [Module.Flat R S] [CompactSpace X]
    (hinter : ∀ U W : X.Opens, IsAffineOpen U → IsAffineOpen W → IsAffineOpen (U ⊓ W))
    (L : LB X) (hL : L.IsLB) (θ : LB.Sec L)
    (hθ : ∀ σ : LB.Sec L, ∃! a : R, ∀ i, σ.f i = algX p (L.U i) a * θ.f i)
    (L' : LB X') (hL' : L'.IsLB) (w : LB.Iso L' (L.pull φ)) (hw : w.IsGen) (σ' : LB.Sec L') (θ2 : LB.Sec (L.pull φ))
    (hσ : IsoRel w σ' θ2)
    (hθ2 : ∀ j (h : (L.pull φ).U j ≤ φ ⁻¹ᵁ L.U (j PUnit.unit)), θ2.f j = (φ.appLE _ _ h).hom (θ.f (j PUnit.unit))) :
    ∀ s' : LB.Sec L', ∃! a : S, ∀ i, s'.f i = algX p' (L'.U i) a * σ'.f i := by
  intro s'
  have hLp : (L.pull φ).IsLB := linComb_isLB L hL _ _
  obtain ⟨s2, hs2⟩ := exists_isoRel hL' hLp hw s'
  obtain ⟨a, ha, hu⟩ := flatBC_gen p p' φ H hinter L hL θ hθ θ2 hθ2 s2
  have hs2a : s2 = smulSec p' (L.pull φ) a θ2 := by
    cases s2 with | mk f cp =>
    simp only [smulSec, LB.Sec.mk.injEq]
    funext i; exact ha i
  refine ⟨a, fun i => ?_, fun b hb => hu b ?_⟩
  · have e : s' = smulSec p' L' a σ' := isoRel_inj_left hLp hs2 (hs2a ▸ isoRel_smul p' hσ a)
    rw [e]; rfl
  · have e : s' = smulSec p' L' b σ' := by
      cases s' with | mk f cp =>
      simp only [smulSec, LB.Sec.mk.injEq]
      funext i; exact hb i
    have e2 : s2 = smulSec p' (L.pull φ) b θ2 := isoRel_inj_right hL' hs2 (e ▸ isoRel_smul p' hσ b)
    intro J
    rw [e2]; rfl

end IsoMain

end ReciprocityTheory.ChartRestriction.G.DVR.FlatBC
