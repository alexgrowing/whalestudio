import ReciprocityTheory.GroupCohomology.CupConnRightStatement
import ReciprocityTheory.GroupCohomology.HomogExistsStatement
import ReciprocityTheory.GroupCohomology.DEqZeroOfMemB
import ReciprocityTheory.GroupCohomology.HomogIso
import ReciprocityTheory.GroupCohomology.PrismOpZeroEval

namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal Cx Function

noncomputable section

universe u

section QI

variable {R : Type u} [CommRing R] {A B : Cx R}

theorem shp_hom_ext {φ ψ : Hom A B} (h : ∀ n, φ.f n = ψ.f n) : φ = ψ := by
  cases φ
  cases ψ
  congr 1
  funext n
  exact h n

theorem shp_bij_of_inv (φ : Hom A B) (ψ : Hom B A) (n : ℕ) (h1 : (ψ.comp φ).H n = (Hom.id A).H n)
    (h2 : (φ.comp ψ).H n = (Hom.id B).H n) : Bijective (φ.H n) := by
  have hcomp : ∀ {P Q S : Cx R} (α : Hom Q S) (β : Hom P Q) (x : P.H n),
      (α.comp β).H n x = α.H n (β.H n x) := by
    intro P Q S α β x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl
  have hid : ∀ {P : Cx R} (x : P.H n), (Hom.id P).H n x = x := by
    intro P x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl
  refine ⟨fun x y hxy => ?_, fun y => ⟨ψ.H n y, ?_⟩⟩
  · calc x = (Hom.id A).H n x := (hid x).symm
      _ = (ψ.comp φ).H n x := by rw [h1]
      _ = ψ.H n (φ.H n x) := hcomp ψ φ x
      _ = ψ.H n (φ.H n y) := by rw [hxy]
      _ = (ψ.comp φ).H n y := (hcomp ψ φ y).symm
      _ = (Hom.id A).H n y := by rw [h1]
      _ = y := hid y
  · rw [← hcomp φ ψ y, h2, hid]

theorem shp_qi_of_bij (φ : Hom A B) (h : ∀ n, Bijective (φ.f n)) : φ.QuasiIso := by
  let e : ∀ n, A.X n ≃ₗ[R] B.X n := fun n => LinearEquiv.ofBijective (φ.f n) (h n)
  have h1 : ∀ m (y : B.X m), φ.f m ((e m).symm y) = y := fun m y => (e m).apply_symm_apply y
  have h0 : ∀ m (x : A.X m), (e m).symm (φ.f m x) = x := fun m x => (e m).symm_apply_apply x
  let ψ : Hom B A := ⟨fun n => (e n).symm.toLinearMap, fun n x => by
    apply (h (n + 1)).1
    show φ.f (n + 1) ((e (n + 1)).symm (B.d n x)) = φ.f (n + 1) (A.d n ((e n).symm x))
    rw [φ.comm, h1, h1]⟩
  intro n
  apply shp_bij_of_inv φ ψ n
  · congr 1
    apply shp_hom_ext
    intro m
    ext x
    exact h0 m x
  · congr 1
    apply shp_hom_ext
    intro m
    ext y
    exact h1 m y

end QI

section Push

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {U : Subgroup G} {M : TRep R U} {C : TRep R G} (ev : Pair C M) (hφ : ev.φ = U.subtype)

include hφ in
theorem shp_phi (y : U) : ev.φ y = (y : G) := by
  rw [hφ]
  rfl

def shpPush (n : ℕ) : hcoch C G n →ₗ[R] hcoch M G n where
  toFun F := ⟨fun x => ev.u (F.1 x), ev.u_cont.comp F.2.1, fun g x => by
    have h := F.2.2 (g : G) x
    show ev.u (F.1 fun i => (g : G) * x i) = M.rho g (ev.u (F.1 x))
    rw [← ev.equiv, shp_phi ev hφ]
    exact congrArg ev.u h⟩
  map_add' F F' := Subtype.ext (funext fun x => map_add ev.u _ _)
  map_smul' c F := Subtype.ext (funext fun x => map_smul ev.u _ _)

theorem shpPush_apply (n : ℕ) (F : hcoch C G n) (x) : (shpPush ev hφ n F).1 x = ev.u (F.1 x) := rfl

theorem shpPush_hd (n : ℕ) (F : hcoch C G n) (F' : hcoch C G (n + 1)) (h : F'.1 = hd n F.1) :
    (shpPush ev hφ (n + 1) F').1 = hd n (shpPush ev hφ n F).1 := by
  funext x
  rw [shpPush_apply, h]
  simp only [hd, map_sum, map_zsmul, shpPush_apply]

variable (j : C.V → C(G, M.V)) (hj : Topology.IsEmbedding j) (hjc : ∀ c g, j c g = ev.u (C.rho g c))
  (hr : ∀ f : C(G, M.V), (∀ (x : U) g, f (x * g) = M.rho x (f g)) → f ∈ Set.range j)

include hj hjc hr in
theorem shpPush_bij (n : ℕ) : Bijective (shpPush ev hφ n) := by
  constructor
  · intro F F' hFF'
    apply Subtype.ext
    funext p
    apply hj.injective
    ext g
    rw [hjc, hjc, ← F.2.2 g p, ← F'.2.2 g p]
    have h' := congrArg (fun K : hcoch M G n => K.1 fun i => g • p i) hFF'
    simpa only [shpPush_apply] using h'
  · intro K
    have hKc : Continuous K.1 := K.2.1
    let m2 : C((Fin (n + 1) → G) × G, M.V) := ⟨fun q => K.1 fun i => q.2 * q.1 i,
      hKc.comp (continuous_pi fun i => continuous_snd.mul ((continuous_apply i).comp continuous_fst))⟩
    let Φ : (Fin (n + 1) → G) → C(G, M.V) := fun q => ContinuousMap.curry m2 q
    have hΦ : Continuous Φ := (ContinuousMap.curry m2).continuous
    have hΦr : ∀ q, ∃ c, j c = Φ q := by
      intro q
      refine hr _ fun u g => ?_
      show K.1 (fun i => (u : G) * g * q i) = M.rho u (K.1 fun i => g * q i)
      have h' := K.2.2 u (fun i => g * q i)
      simp only [mul_assoc]
      exact h'
    choose c hc using hΦr
    have hcont : Continuous c := by
      refine hj.isInducing.continuous_iff.2 ?_
      have hjc' : j ∘ c = Φ := funext hc
      rw [hjc']
      exact hΦ
    have hequiv : ∀ (g : G) q, c (fun i => g • q i) = C.rho g (c q) := by
      intro g q
      apply hj.injective
      ext h
      have e1 : C.rho h (C.rho g (c q)) = C.rho (h * g) (c q) := by
        rw [map_mul]
        rfl
      rw [hc, hjc, e1, ← hjc, hc]
      show K.1 (fun i => h * (g • q i)) = K.1 (fun i => h * g * q i)
      simp only [smul_eq_mul, mul_assoc]
    refine ⟨⟨c, hcont, hequiv⟩, Subtype.ext (funext fun q => ?_)⟩
    show ev.u (c q) = K.1 q
    have h' := congrArg (fun f : C(G, M.V) => f 1) (hc q)
    simp only [hjc, map_one, Module.End.one_apply] at h'
    rw [h']
    show K.1 (fun i => 1 * q i) = K.1 q
    simp only [one_mul]

end Push

theorem shapiro_holds : ShapiroStatement.{u} := by
  intro R _ G _ _ _ _ U M C ev hev hr'
  obtain ⟨hφ, j, hj, hjc, hrj⟩ := hev
  obtain ⟨r, hrc, hrx⟩ := hr'
  obtain ⟨eC, hC, hCf, -⟩ := homogIso_holds R G C
  obtain ⟨eM, hM, hMf, -⟩ := homogIso_holds R U M
  obtain ⟨B, eB, hB⟩ := homogExists_holds R U M G
  obtain ⟨P, hP⟩ : ∃ P : Hom C.coch B, ∀ n f, eB n (P.f n f) = shpPush ev hφ n (eC n f) :=
    ⟨⟨fun n => ((eB n).symm.toLinearMap.comp (shpPush ev hφ n)).comp (eC n).toLinearMap, fun n F => by
      apply (eB (n + 1)).injective
      apply Subtype.ext
      rw [hB]
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
      exact shpPush_hd ev hφ n _ _ (hC n F)⟩,
     fun n f => (eB n).apply_symm_apply _⟩
  obtain ⟨φ1, hφ1⟩ := (prism_holds R U M U G M.coch B eM eB hM hB).1 Subtype.val
    continuous_subtype_val (fun g x => rfl)
  obtain ⟨φ2, hφ2⟩ := (prism_holds R U M G U B M.coch eB eM hB hM).1 r hrc (fun g x => hrx g x)
  have h12 : ∀ n, (φ1.comp φ2).H n = (Hom.id M.coch).H n :=
    (prism_holds R U M U U M.coch M.coch eM eM hM hM).2 (fun u => r u) id (φ1.comp φ2) (Hom.id _)
      (hrc.comp continuous_subtype_val) continuous_id (fun g x => hrx g x) (fun g x => rfl)
      (fun n F x => by
        show (eM n (φ1.f n (φ2.f n F))).1 x = _
        rw [hφ1, hφ2])
      (fun n F x => rfl)
  have h21 : ∀ n, (φ2.comp φ1).H n = (Hom.id B).H n :=
    (prism_holds R U M G G B B eB eB hB hB).2 (fun g => (r g : G)) id (φ2.comp φ1) (Hom.id _)
      (continuous_subtype_val.comp hrc) continuous_id
      (fun g x => by
        show ((r (↑g * x) : U) : G) = ↑g * ↑(r x)
        rw [hrx, Subgroup.coe_mul])
      (fun g x => rfl)
      (fun n F x => by
        show (eB n (φ2.f n (φ1.f n F))).1 x = _
        rw [hφ2, hφ1])
      (fun n F x => rfl)
  have hPb : ∀ n, Bijective (P.f n) := fun n => by
    have hfun : ⇑(P.f n) = (eB n).symm ∘ (shpPush ev hφ n) ∘ (eC n) := by
      funext f
      simp only [Function.comp_apply]
      rw [← hP, LinearEquiv.symm_apply_apply]
    rw [hfun]
    exact (eB n).symm.bijective.comp
      ((shpPush_bij (ev := ev) (hφ := hφ) (j := j) (hj := hj) (hjc := hjc) (hr := hrj) n).comp
        (eC n).bijective)
  have hL : ∀ n f x, (eM n (ev.hom.f n f)).1 x =
      ev.u (C.rho (x 0 : G) (f.1 fun i => ((x i.castSucc : G))⁻¹ * x i.succ)) := by
    intro n f x
    rw [hMf]
    show M.rho (x 0) (ev.u (f.1 fun i => ev.φ ((x i.castSucc)⁻¹ * x i.succ))) = _
    rw [← ev.equiv]
    simp only [shp_phi ev hφ, Subgroup.coe_mul, Subgroup.coe_inv]
  have hR : ∀ n f x, (eM n ((φ1.comp P).f n f)).1 x =
      ev.u (C.rho (x 0 : G) (f.1 fun i => ((x i.castSucc : G))⁻¹ * x i.succ)) := by
    intro n f x
    show (eM n (φ1.f n (P.f n f))).1 x = _
    rw [hφ1, hP, shpPush_apply, hCf]
  have hev : ev.hom = φ1.comp P := shp_hom_ext fun n => LinearMap.ext fun f =>
    (eM n).injective (Subtype.ext (funext fun x => (hL n f x).trans (hR n f x).symm))
  intro n
  rw [hev]
  have hc : ∀ y, (φ1.comp P).H n y = φ1.H n (P.H n y) := fun y => by
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rfl
  have hfun : ⇑((φ1.comp P).H n) = φ1.H n ∘ P.H n := funext hc
  rw [hfun]
  exact (shp_bij_of_inv φ1 φ2 n (h21 n) (h12 n)).comp (shp_qi_of_bij P hPb n)

section Coind

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (U : Subgroup G) (M : TRep R U)

def coindSub : Submodule R C(G, M.V) where
  carrier := {f | ∀ (x : U) g, f (x * g) = M.rho x (f g)}
  zero_mem' := fun x g => by simp
  add_mem' := fun {a b} ha hb x g => by simp [ha x g, hb x g]
  smul_mem' c a ha x g := by simp [ha x g]

variable {U M}

def coindTr (g : G) : coindSub U M →ₗ[R] coindSub U M where
  toFun f := ⟨f.1.comp ⟨(· * g), continuous_mul_const g⟩, fun x h => by
    show f.1 (x * h * g) = M.rho x (f.1 (h * g))
    rw [mul_assoc]; exact f.2 x (h * g)⟩
  map_add' f f' := rfl
  map_smul' c f := rfl

@[simp] theorem coindTr_apply (g : G) (f : coindSub U M) (h : G) : (coindTr g f).1 h = f.1 (h * g) := rfl

variable (U M)

def coindRho : Representation R G (coindSub U M) where
  toFun := coindTr
  map_one' := LinearMap.ext fun f => Subtype.ext (ContinuousMap.ext fun h => by simp)
  map_mul' g g' := LinearMap.ext fun f => Subtype.ext (ContinuousMap.ext fun h => by
    show f.1 (h * (g * g')) = f.1 (h * g * g')
    rw [mul_assoc])

instance : ContinuousConstSMul R (coindSub U M) :=
  ⟨fun c => ((continuous_const_smul c).comp continuous_subtype_val).subtype_mk _⟩

variable [LocallyCompactSpace G]

theorem coindRho_cont : ContAction (coindRho U M) := by
  let m : C(G × G, G) := ⟨fun q => q.2 * q.1, continuous_snd.mul continuous_fst⟩
  have h1 : Continuous fun p : G × coindSub U M => (ContinuousMap.curry m p.1, (p.2 : C(G, M.V))) :=
    ((ContinuousMap.curry m).continuous.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)
  have h2 := ContinuousMap.continuous_comp'.comp h1
  show Continuous fun p : G × coindSub U M => coindRho U M p.1 p.2
  refine continuous_induced_rng.2 ?_
  exact h2

def coindRep : TRep R G where
  V := coindSub U M
  rho := coindRho U M
  cont := coindRho_cont U M

def coindEv : Pair (coindRep U M) M where
  φ := U.subtype
  u := { toFun := fun f => f.1 1, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  φ_cont := continuous_subtype_val
  u_cont := (continuous_eval_const 1).comp continuous_subtype_val
  equiv g f := by
    show f.1 (1 * (g : G)) = M.rho g (f.1 1)
    have h := f.2 g 1
    rw [mul_one] at h
    rw [one_mul]; exact h

theorem coindEv_isCoind : IsCoind U M (coindRep U M) (coindEv U M) := by
  unfold IsCoind
  refine ⟨rfl, fun f => f.1, Topology.IsEmbedding.subtypeVal, fun c g => ?_,
    fun f hf => ⟨⟨f, hf⟩, rfl⟩⟩
  show c.1 g = c.1 (1 * g)
  rw [one_mul]

end Coind

theorem coind_holds : CoindStatement.{u} := by
  intro R _ G _ _ _ _ U M
  exact ⟨coindRep U M, coindEv U M, coindEv_isCoind U M⟩

end

end ReciprocityTheory.Coh
