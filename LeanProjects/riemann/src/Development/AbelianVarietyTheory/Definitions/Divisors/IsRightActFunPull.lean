import Mathlib

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LevDesc

section Right

variable {G K R : Type} [Group G] [Field K] [CommRing R] [Algebra K R]

def IsRightAct (st : G → R →ₐ[K] R) : Prop :=
  (∀ x, st 1 x = x) ∧ ∀ h h' x, st (h * h') x = st h' (st h x)

theorem isRightAct_inv (ρ : G →* (R →ₐ[K] R)) : IsRightAct (fun h => ρ h⁻¹) :=
  ⟨fun x => by simp, fun h h' x => by simp only [mul_inv_rev, map_mul]; rfl⟩

theorem IsRightAct.comp {st : G → R →ₐ[K] R} (h : IsRightAct st) {G' : Type} [Group G'] (f : G' →* G) :
    IsRightAct (fun g => st (f g)) :=
  ⟨fun x => by simp only [map_one]; exact h.1 x, fun a b x => by simp only [map_mul]; exact h.2 _ _ x⟩

def funPull (K : Type) [Field K] {Z : Type} [MulAction G Z] (h : G) : (Z → K) →ₐ[K] (Z → K) :=
  Pi.algHom _ _ fun z => Pi.evalAlgHom K (fun _ : Z => K) (h • z)

theorem isRightAct_funPull {Z : Type} [MulAction G Z] : IsRightAct (funPull K (Z := Z) (G := G)) :=
  ⟨fun x => funext fun z => congrArg x (one_smul G z), fun h h' x => funext fun z => congrArg x (mul_smul h h' z)⟩

variable (st : G → R →ₐ[K] R)

def IsRightAct.equiv {st : G → R →ₐ[K] R} (hs : IsRightAct st) (h : G) : R ≃ₐ[K] R :=
  AlgEquiv.ofAlgHom (st h) (st h⁻¹)
    (AlgHom.ext fun x => (hs.2 _ _ x).symm.trans (by rw [inv_mul_cancel]; exact hs.1 x))
    (AlgHom.ext fun x => (hs.2 _ _ x).symm.trans (by rw [mul_inv_cancel]; exact hs.1 x))

theorem IsRightAct.equiv_apply {st : G → R →ₐ[K] R} (hs : IsRightAct st) (h : G) (x : R) :
    hs.equiv h x = st h x := rfl

def groupMat (u : R) : Matrix G G R := Matrix.of fun h g => st (h * g) u

theorem groupMat_apply (u : R) (h g : G) : groupMat st u h g = st (h * g) u := rfl

def eigen (χ : G →* Kˣ) : Submodule K R where
  carrier := {F | ∀ h, st h F = ((χ h : Kˣ) : K) • F}
  zero_mem' := fun h => by simp
  add_mem' := fun {a b} ha hb h => by rw [map_add, ha h, hb h, smul_add]
  smul_mem' := fun c a ha h => by rw [map_smul, ha h, smul_comm]

theorem mem_eigen {χ : G →* Kˣ} {F : R} : F ∈ eigen st χ ↔ ∀ h, st h F = ((χ h : Kˣ) : K) • F := Iff.rfl

def IsRightAct.leftRep {st : G → R →ₐ[K] R} (hs : IsRightAct st) : Representation K G R where
  toFun g := (st g⁻¹).toLinearMap
  map_one' := LinearMap.ext fun x => by rw [inv_one]; exact hs.1 x
  map_mul' g h := LinearMap.ext fun x => by rw [mul_inv_rev]; exact hs.2 _ _ x

theorem IsRightAct.leftRep_apply {st : G → R →ₐ[K] R} (hs : IsRightAct st) (g : G) (x : R) :
    hs.leftRep g x = st g⁻¹ x := rfl

theorem IsRightAct.mem_eigen_iff {st : G → R →ₐ[K] R} (hs : IsRightAct st) {χ : G →* Kˣ} {F : R} :
    F ∈ eigen st χ ↔ ∀ g, hs.leftRep g F = ((χ⁻¹ g : Kˣ) : K) • F :=
  ⟨fun h g => by rw [hs.leftRep_apply, h g⁻¹, map_inv]; rfl,
    fun h g => by have := h g⁻¹; rwa [hs.leftRep_apply, inv_inv, MonoidHom.inv_apply, map_inv, inv_inv] at this⟩

def IsRightAct.subRep {st : G → R →ₐ[K] R} (hs : IsRightAct st) (C : Submodule K R)
    (hC : ∀ h, ∀ x ∈ C, st h x ∈ C) : Representation K G C :=
  hs.leftRep.subrepresentation C fun g x hx => hC g⁻¹ x hx

theorem IsRightAct.subRep_apply {st : G → R →ₐ[K] R} (hs : IsRightAct st) (C : Submodule K R)
    (hC : ∀ h, ∀ x ∈ C, st h x ∈ C) (g : G) (x : C) : (hs.subRep C hC g x : R) = st g⁻¹ x := rfl

def algOp (e : MonoidAlgebra K G) : Module.End K R :=
  Finsupp.linearCombination K (fun g => (st g⁻¹).toLinearMap) e.coeff

theorem algOp_single (g : G) (a : K) (x : R) : algOp st (MonoidAlgebra.single g a) x = a • st g⁻¹ x := by
  simp [algOp]

theorem algOp_apply [Fintype G] (e : MonoidAlgebra K G) (x : R) :
    algOp st e x = ∑ g, e.coeff g • st g⁻¹ x := by
  rw [algOp, Finsupp.linearCombination_apply,
    Finsupp.sum_fintype _ (fun i a => a • (st i⁻¹).toLinearMap) (fun _ => zero_smul _ _), LinearMap.sum_apply]
  rfl

theorem IsRightAct.algOp_eq {st : G → R →ₐ[K] R} (hs : IsRightAct st) (e : MonoidAlgebra K G) :
    algOp st e = hs.leftRep.asAlgebraHom e := by
  induction e using MonoidAlgebra.induction_linear with
  | zero => simp [algOp]
  | add a b ha hb => rw [map_add, ← ha, ← hb]; simp [algOp]
  | single g a => ext x; rw [algOp_single, Representation.asAlgebraHom_single]; rfl

theorem IsRightAct.algOp_mul {st : G → R →ₐ[K] R} (hs : IsRightAct st) (e e' : MonoidAlgebra K G) :
    algOp st (e * e') = algOp st e * algOp st e' := by
  rw [hs.algOp_eq, hs.algOp_eq, hs.algOp_eq, map_mul]

theorem algOp_mem {C : Submodule K R} (hC : ∀ h, ∀ x ∈ C, st h x ∈ C) (e : MonoidAlgebra K G) {x : R} (hx : x ∈ C) :
    algOp st e x ∈ C := by
  rw [algOp, Finsupp.linearCombination_apply, Finsupp.sum, LinearMap.sum_apply]
  exact C.sum_mem fun g _ => C.smul_mem _ (hC _ x hx)

variable [Fintype G]

def tr (χ : G →* Kˣ) : R →ₗ[K] R := ∑ h, (((χ h)⁻¹ : Kˣ) : K) • (st h).toLinearMap

theorem tr_apply (χ : G →* Kˣ) (F : R) : tr st χ F = ∑ h, (((χ h)⁻¹ : Kˣ) : K) • st h F := by
  rw [tr, LinearMap.sum_apply]; rfl

def ph (χ : G →* Kˣ) (u : R) : R →ₗ[K] (G → R) :=
  LinearMap.pi fun h => tr st χ ∘ₗ LinearMap.mulRight K (st h u)

theorem ph_apply (χ : G →* Kˣ) (u f : R) (h : G) : ph st χ u f h = tr st χ (f * st h u) := rfl

def ps (u : R) : (G → R) →ₗ[K] R := ∑ h, LinearMap.mulRight K (st h u) ∘ₗ LinearMap.proj h

theorem ps_apply (u : R) (F : G → R) : ps st u F = ∑ h, F h * st h u := by
  rw [ps, LinearMap.sum_apply]; rfl

theorem IsRightAct.tr_mem_eigen {st : G → R →ₐ[K] R} (hs : IsRightAct st) (χ : G →* Kˣ) (F : R) :
    tr st χ F ∈ eigen st χ := fun g => by
  rw [tr_apply, map_sum, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulRight g) _ _ fun h => ?_
  rw [map_smul, ← hs.2, smul_smul, Equiv.coe_mulRight, map_mul]
  congr 1
  simp

theorem tr_of_mem_eigen {χ : G →* Kˣ} {F : R} (hF : F ∈ eigen st χ) : tr st χ F = (Fintype.card G : K) • F := by
  rw [tr_apply, Finset.sum_congr rfl (g := fun _ => F) fun h _ => by rw [hF h, smul_smul]; simp]
  simp [Nat.cast_smul_eq_nsmul]

theorem tr_mem {C : Submodule K R} (hC : ∀ h, ∀ x ∈ C, st h x ∈ C) (χ : G →* Kˣ) {x : R} (hx : x ∈ C) :
    tr st χ x ∈ C := by
  rw [tr_apply]; exact C.sum_mem fun g _ => C.smul_mem _ (hC _ x hx)

example [DecidableEq G] (h g : G) :
    groupMat (funPull K (Z := G)) (Pi.single (1 : G) (1 : K)) h g 1 = if h * g = 1 then 1 else 0 := by
  show (Pi.single (1 : G) (1 : K) : G → K) ((h * g) • (1 : G)) = _
  simp [Pi.single_apply]

end Right

section Lat

variable {G K R O : Type} [Group G] [Field K] [CommRing R] [Algebra K R] [CommRing O] [Algebra O K]
  {C : Submodule K R} [Module O C] [IsScalarTower O K C]

def latCap (L : Submodule O C) (W : Submodule K R) : Submodule O C :=
  L ⊓ (W.comap C.subtype).restrictScalars O

theorem mem_latCap {L : Submodule O C} {W : Submodule K R} {F : C} : F ∈ latCap L W ↔ F ∈ L ∧ (F : R) ∈ W := Iff.rfl

theorem latCap_le (L : Submodule O C) (W : Submodule K R) : latCap L W ≤ L := inf_le_left

def spanQ (N : Submodule O C) : Submodule K R := (Submodule.span K (N : Set C)).map C.subtype

omit [Algebra O K] [IsScalarTower O K C] in

theorem mem_spanQ {N : Submodule O C} {F : C} (hF : F ∈ N) : (F : R) ∈ spanQ N :=
  ⟨F, Submodule.subset_span hF, rfl⟩

def cutLat (N : Submodule O C) (T : Module.End K R) : Submodule O C := latCap N ((spanQ N).map T)

theorem mem_cutLat {N : Submodule O C} {T : Module.End K R} {F : C} :
    F ∈ cutLat N T ↔ F ∈ N ∧ ∃ x ∈ spanQ N, T x = F := Iff.rfl

theorem mem_cutLat_iff {N : Submodule O C} {T : Module.End K R} (hT : IsIdempotentElem T) {F : C} :
    F ∈ cutLat N T ↔ F ∈ N ∧ T F = F :=
  and_congr_right fun hF => ⟨fun ⟨x, _, e⟩ => by
      have e' : T x = F := e
      rw [← e']; exact congrArg (fun S : Module.End K R => S x) hT,
    fun e => ⟨F, mem_spanQ hF, e⟩⟩

theorem cutLat_one (N : Submodule O C) : cutLat N 1 = N :=
  Submodule.ext fun _ => (mem_cutLat_iff IsIdempotentElem.one).trans (and_iff_left rfl)

theorem cutLat_zero (N : Submodule O C) : cutLat N 0 = ⊥ :=
  Submodule.ext fun F => (mem_cutLat_iff IsIdempotentElem.zero).trans
    ⟨fun h => Subtype.ext h.2.symm, fun h => by obtain rfl : F = 0 := h; exact ⟨N.zero_mem, rfl⟩⟩

end Lat

section Quot

variable {O : Type} [CommRing O] (N : Type) [AddCommGroup N] [Module O N]

abbrev QMod (I : Ideal O) : Type := N ⧸ (I • (⊤ : Submodule O N))

abbrev QAut (I : Ideal O) : Type := QMod N I ≃ₗ[O] QMod N I

variable {N} {I J : Ideal O}

def qProj (h : I ≤ J) : QMod N I →ₗ[O] QMod N J := Submodule.factor (Submodule.smul_mono_left h)

theorem qProj_mk (h : I ≤ J) (x : N) : qProj h (Submodule.Quotient.mk x) = Submodule.Quotient.mk x := rfl

theorem qProj_surjective (h : I ≤ J) : Function.Surjective (qProj (N := N) h) :=
  Submodule.factor_surjective (Submodule.smul_mono_left h)

theorem qProj_eq_zero (h : I ≤ J) (q : QMod N I) : qProj h q = 0 ↔ q ∈ J • (⊤ : Submodule O (QMod N I)) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  have e : J • (⊤ : Submodule O (QMod N I)) = (J • (⊤ : Submodule O N)).map (I • (⊤ : Submodule O N)).mkQ := by
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]
  rw [qProj_mk, Submodule.Quotient.mk_eq_zero, e]
  refine ⟨fun hx => ⟨x, hx, rfl⟩, fun ⟨y, hy, hyx⟩ => ?_⟩
  have := Submodule.smul_mono_left h ((Submodule.Quotient.eq _).1 hyx)
  simpa using sub_mem hy this

theorem map_mem_smul_top {M M' : Type} [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O M'] (f : M →ₗ[O] M')
    {x : M} (hx : x ∈ J • (⊤ : Submodule O M)) : f x ∈ J • (⊤ : Submodule O M') := by
  have := Submodule.mem_map_of_mem (f := f) hx
  rw [Submodule.map_smul''] at this
  exact Submodule.smul_mono le_rfl le_top this

def endRed (h : I ≤ J) (γ : QMod N I →ₗ[O] QMod N I) : QMod N J →ₗ[O] QMod N J :=
  Submodule.liftQ _ (qProj h ∘ₗ γ ∘ₗ Submodule.mkQ _) fun _ hx =>
    (qProj_eq_zero h _).2 (map_mem_smul_top (γ ∘ₗ Submodule.mkQ _) hx)

theorem endRed_qProj (h : I ≤ J) (γ : QMod N I →ₗ[O] QMod N I) (q : QMod N I) :
    endRed h γ (qProj h q) = qProj h (γ q) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rfl

def autRed (h : I ≤ J) : QAut N I →* QAut N J where
  toFun γ := LinearEquiv.ofLinear (endRed h γ) (endRed h γ.symm)
    (LinearMap.ext fun q => by
      obtain ⟨q, rfl⟩ := qProj_surjective h q
      simp [endRed_qProj])
    (LinearMap.ext fun q => by
      obtain ⟨q, rfl⟩ := qProj_surjective h q
      simp [endRed_qProj])
  map_one' := LinearEquiv.ext fun q => by
    obtain ⟨q, rfl⟩ := qProj_surjective h q
    exact endRed_qProj h _ q
  map_mul' γ δ := LinearEquiv.ext fun q => by
    obtain ⟨q, rfl⟩ := qProj_surjective h q
    show endRed h _ _ = endRed h _ (endRed h _ _)
    simp [endRed_qProj]

theorem autRed_qProj (h : I ≤ J) (γ : QAut N I) (q : QMod N I) : autRed h γ (qProj h q) = qProj h (γ q) :=
  endRed_qProj h _ q

variable (N I J) in

def trivMod : Subgroup (QAut N I) where
  carrier := {γ | ∀ q, γ q - q ∈ J • (⊤ : Submodule O (QMod N I))}
  one_mem' := fun q => by simp
  mul_mem' := by
    intro γ δ hγ hδ q
    have h := Submodule.add_mem _ (hγ (δ q)) (hδ q)
    rwa [sub_add_sub_cancel] at h
  inv_mem' := by
    intro γ hγ q
    have h := Submodule.neg_mem _ (hγ (γ⁻¹ q))
    have e : γ (γ⁻¹ q) = q := γ.apply_symm_apply q
    rwa [e, neg_sub] at h

theorem mem_trivMod {γ : QAut N I} : γ ∈ trivMod N I J ↔ ∀ q, γ q - q ∈ J • (⊤ : Submodule O (QMod N I)) := Iff.rfl

theorem autRed_eq_one (h : I ≤ J) (γ : QAut N I) : autRed h γ = 1 ↔ γ ∈ trivMod N I J := by
  refine ⟨fun e q => (qProj_eq_zero h _).1 ?_, fun e => LinearEquiv.ext fun q => ?_⟩
  · rw [map_sub, ← autRed_qProj, e]; exact sub_self _
  · obtain ⟨q, rfl⟩ := qProj_surjective h q
    rw [autRed_qProj]
    exact sub_eq_zero.1 ((map_sub (qProj h) _ _).symm.trans ((qProj_eq_zero h _).2 (e q)))

theorem trivMod_mono {J' : Ideal O} (h : J ≤ J') : trivMod N I J ≤ trivMod N I J' :=
  fun _ hγ q => Submodule.smul_mono_left h (hγ q)

theorem smul_top_qMod : I • (⊤ : Submodule O (QMod N I)) = ⊥ :=
  eq_bot_iff.2 fun q hq => by
    have := (qProj_eq_zero (le_refl I) q).2 hq
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    exact this

theorem trivMod_sup : trivMod N I (I ⊔ J) = trivMod N I J := by
  ext γ
  rw [mem_trivMod, mem_trivMod, Submodule.sup_smul, smul_top_qMod, bot_sup_eq]

example : trivMod N I ⊤ = ⊤ ∧ trivMod N I I = ⊥ := by
  refine ⟨eq_top_iff.2 fun γ _ q => by simp, eq_bot_iff.2 fun γ hγ => LinearEquiv.ext fun q => ?_⟩
  have := hγ q
  rw [smul_top_qMod] at this
  exact sub_eq_zero.1 this

theorem mem_iInf_smul_top {ι M : Type} [Finite ι] [AddCommGroup M] [Module O M] {Js : ι → Ideal O}
    (hc : Pairwise (Function.onFun IsCoprime Js)) {x : M} (hx : ∀ i, x ∈ Js i • (⊤ : Submodule O M)) :
    x ∈ (⨅ i, Js i) • (⊤ : Submodule O M) := by
  rw [← Ideal.ker_tensorProductMk_quotient M Js hc, LinearMap.mem_ker]
  funext i
  apply (TensorProduct.quotTensorEquivQuotSMul M (Js i)).injective
  show TensorProduct.quotTensorEquivQuotSMul M (Js i) (1 ⊗ₜ x) = _
  rw [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, Pi.zero_apply, map_zero]
  exact (Submodule.Quotient.mk_eq_zero _).2 (hx i)

section CRT

variable {ι : Type} [Finite ι] {Js : ι → Ideal O} (hle : ∀ i, I ≤ Js i)
  (hc : Pairwise (Function.onFun IsCoprime Js)) (hI : ⨅ i, Js i ≤ I)

def crt : QMod N I ≃ₗ[O] ∀ i, QMod N (Js i) :=
  LinearEquiv.ofBijective (LinearMap.pi fun i => qProj (hle i)) ⟨by
    rw [injective_iff_map_eq_zero]
    intro q hq
    have := Submodule.smul_mono_left hI
      (mem_iInf_smul_top hc fun i => (qProj_eq_zero (hle i) q).1 (congrFun hq i))
    rwa [smul_top_qMod] at this, by
    intro y
    obtain ⟨x, hx⟩ := Ideal.pi_tensorProductMk_quotient_surjective N Js hc
      fun i => (TensorProduct.quotTensorEquivQuotSMul N (Js i)).symm (y i)
    refine ⟨Submodule.Quotient.mk x, funext fun i => ?_⟩
    have := congrArg (TensorProduct.quotTensorEquivQuotSMul N (Js i)) (congrFun hx i)
    rw [LinearEquiv.apply_symm_apply] at this
    exact (TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul _ x).symm.trans this⟩

theorem crt_apply (q : QMod N I) (i : ι) : crt hle hc hI q i = qProj (hle i) q := rfl

def crtAut : QAut N I ≃* ∀ i, QAut N (Js i) :=
  MulEquiv.ofBijective (Pi.monoidHom fun i => autRed (hle i)) ⟨by
    intro γ δ e
    refine LinearEquiv.ext fun q => (crt hle hc hI).injective (funext fun i => ?_)
    have e' : autRed (hle i) γ = autRed (hle i) δ := congrFun e i
    rw [crt_apply, crt_apply, ← autRed_qProj, ← autRed_qProj, e'], by
    intro g
    refine ⟨(crt hle hc hI).trans ((LinearEquiv.piCongrRight g).trans (crt hle hc hI).symm),
      funext fun i => LinearEquiv.ext fun q => ?_⟩
    obtain ⟨q, rfl⟩ := qProj_surjective (hle i) q
    show autRed (hle i) _ _ = _
    rw [autRed_qProj, ← crt_apply hle hc hI, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
      LinearEquiv.apply_symm_apply]
    rfl⟩

theorem crtAut_apply (γ : QAut N I) (i : ι) : crtAut hle hc hI γ i = autRed (hle i) γ := rfl

end CRT

end Quot

section Mat

variable {O : Type} [CommRing O] {M : Type} [AddCommGroup M] [Module O M] {r p : ℕ} (e : M ≃+ (Fin r → ZMod p))

def endMat : Module.End O M →* Matrix (Fin r) (Fin r) (ZMod p) where
  toFun γ := LinearMap.toMatrix' (AddMonoidHom.toZModLinearMap p
    (e.toAddMonoidHom.comp (γ.toAddMonoidHom.comp e.symm.toAddMonoidHom)))
  map_one' := by
    rw [← LinearMap.toMatrix'_id]
    congr 1
    refine LinearMap.ext fun x => ?_
    simp
  map_mul' γ δ := by
    rw [← LinearMap.toMatrix'_mul]
    congr 1
    refine LinearMap.ext fun x => ?_
    simp

theorem endMat_mulVec (γ : Module.End O M) (x : M) : (endMat e γ).mulVec (e x) = e (γ x) := by
  simp [endMat, LinearMap.toMatrix'_mulVec]

def autMat : (M ≃ₗ[O] M) →* GL (Fin r) (ZMod p) :=
  ((endMat e).comp (LinearEquiv.automorphismGroup.toLinearMapMonoidHom)).toHomUnits

theorem autMat_mulVec (γ : M ≃ₗ[O] M) (x : M) :
    (autMat e γ : Matrix (Fin r) (Fin r) (ZMod p)).mulVec (e x) = e (γ x) := endMat_mulVec e _ x

theorem autMat_injective : Function.Injective (autMat (O := O) e) := fun γ δ h =>
  LinearEquiv.ext fun x => e.injective (by rw [← autMat_mulVec, ← autMat_mulVec, h])

theorem autMat_surjective (hO : ∀ a : O, ∃ n : ℤ, ∀ x : M, a • x = n • x) :
    Function.Surjective (autMat (O := O) e) := fun g => by
  let f : M ≃+ M := e.trans ((Matrix.GeneralLinearGroup.toLin g).toLinearEquiv.toAddEquiv.trans e.symm)
  refine ⟨f.toLinearEquiv fun a x => ?_, Units.ext (Matrix.ext_of_mulVec_single fun i => ?_)⟩
  · obtain ⟨n, hn⟩ := hO a
    rw [hn, hn, map_zsmul]
  · rw [← e.apply_symm_apply (Pi.single i 1), autMat_mulVec]
    simp [f]

end Mat

end GlobalTheory.LevDesc
