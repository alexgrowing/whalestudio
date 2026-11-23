import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.IndefiniteReal.RhoGeo

noncomputable section

open NumberField Module MeasureTheory
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Arith Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.L2.Pj
  Formalism.IndefR.FWT
open scoped InnerProductSpace

namespace GlobalTheory.TiedUnif

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Schur

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {μ : Measure (GA D V)} {𝓕 : Set (GA D V)}

theorem isMultiplicityInner_of_ne_zero {T T' : MMap M} (h : ipM M μ 𝓕 T T' ≠ 0) : IsMultIP M μ 𝓕 T T' (ipM M μ 𝓕 T T') :=
  ipM_spec M μ 𝓕 T T' (by
    by_contra hn
    exact h (by rw [ipM, dif_neg hn]))

theorem exists_schur (H : HMod (MMap M)) (d : ℂ) (h : ∀ x y : H.H, inner ℂ x y = d * ipM M μ 𝓕 (H.e x) (H.e y)) (x y : H.H) :
    ∃ c, IsMultIP M μ 𝓕 (H.e x) (H.e y) c ∧ inner ℂ x y = d * c := by
  have key : ∀ x y : H.H, inner ℂ x y ≠ (0 : ℂ) → ∃ c, IsMultIP M μ 𝓕 (H.e x) (H.e y) c ∧ inner ℂ x y = d * c :=
    fun x y hxy => ⟨_, isMultiplicityInner_of_ne_zero fun h0 => hxy (by rw [h, h0, mul_zero]), h x y⟩
  by_cases hxy : inner ℂ x y = (0 : ℂ)
  swap
  · exact key x y hxy
  by_cases hx : x = 0
  · subst hx
    refine ⟨0, fun v v' => ?_, by simp⟩
    simp
  have hxx : inner ℂ x x ≠ (0 : ℂ) := inner_self_ne_zero.2 hx
  obtain ⟨c₁, h₁, e₁⟩ := key x x hxx
  obtain ⟨c₂, h₂, e₂⟩ := key x (x + y) (by rwa [inner_add_right, hxy, add_zero])
  refine ⟨c₂ - c₁, fun v v' => ?_, by rw [mul_sub, ← e₁, ← e₂, inner_add_right]; ring⟩
  have hf : (fun g => star (H.e x v g) * H.e y v' g) =
      fun g => star (H.e x v g) * H.e (x + y) v' g - star (H.e x v g) * H.e x v' g := by
    funext g
    simp only [map_add, MultilinearMap.add_apply, Pi.add_apply]
    ring
  rw [hf]
  refine ⟨(h₂ v v').1.sub (h₁ v v').1, ?_⟩
  rw [integral_sub (h₂ v v').1 (h₁ v v').1, (h₂ v v').2, (h₁ v v').2, sub_mul]

theorem prod_inner_self {v : M.Vec} (hv : IsUnitV v) : ∏ τ, ⟪(v τ : M.H τ), (v τ : M.H τ)⟫_ℂ = 1 :=
  Finset.prod_eq_one fun τ _ => by rw [inner_self_eq_norm_sq_to_K, hv τ]; simp

theorem eq_smul_of_eval_eq (H : HMod (MMap M)) (d : ℂ) (h : ∀ x y : H.H, inner ℂ x y = d * ipM M μ 𝓕 (H.e x) (H.e y))
    {v v' : M.Vec} (hv : IsUnitV v) (hv' : IsUnitV v') {x y : H.H} (hxy : H.e x v = H.e y v') :
    x = (∏ τ, ⟪(v τ : M.H τ), (v' τ : M.H τ)⟫_ℂ) • y ∧ ‖x‖ = ‖y‖ := by
  set s : ℂ := ∏ τ, ⟪(v τ : M.H τ), (v' τ : M.H τ)⟫_ℂ with hs
  obtain ⟨c₁, h₁, e₁⟩ := exists_schur H d h x x
  obtain ⟨c₂, h₂, e₂⟩ := exists_schur H d h y y
  obtain ⟨c₃, h₃, e₃⟩ := exists_schur H d h x y
  have i₁ := (h₁ v v).2
  have i₂ := (h₂ v' v').2
  have i₃ := (h₃ v v').2
  rw [prod_inner_self hv, mul_one] at i₁
  rw [prod_inner_self hv', mul_one, ← hxy, i₁] at i₂
  rw [← hxy, i₁, ← hs] at i₃
  have n₁ : inner ℂ x x = inner ℂ y y := by rw [e₁, e₂, i₂]
  have n₂ : inner ℂ x (s • y) = inner ℂ x x := by rw [inner_smul_right, e₃, e₁, i₃]; ring
  have hn : ‖x‖ = ‖y‖ := by
    have := congrArg RCLike.re n₁
    rw [inner_self_eq_norm_sq, inner_self_eq_norm_sq] at this
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 this
  have hs1 : ‖s‖ ≤ 1 := by
    rw [hs, norm_prod]
    refine Finset.prod_le_one (fun _ _ => norm_nonneg _) fun τ _ => ?_
    have := norm_inner_le_norm (𝕜 := ℂ) (v τ : M.H τ) (v' τ : M.H τ)
    rwa [hv τ, hv' τ, mul_one] at this
  refine ⟨?_, hn⟩
  have h4 := norm_sub_sq (𝕜 := ℂ) x (s • y)
  rw [n₂, inner_self_eq_norm_sq, norm_smul, ← hn] at h4
  have h5 : ‖s‖ * ‖x‖ ≤ ‖x‖ := mul_le_of_le_one_left (norm_nonneg _) hs1
  have h6 : (‖s‖ * ‖x‖) ^ 2 ≤ ‖x‖ ^ 2 := pow_le_pow_left₀ (by positivity) h5 2
  have h7 : ‖x - s • y‖ ^ 2 = 0 := le_antisymm (by linarith) (sq_nonneg _)
  exact sub_eq_zero.1 (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h7))

theorem eq_of_eval_eq (H : HMod (MMap M)) (d : ℂ) (h : ∀ x y : H.H, inner ℂ x y = d * ipM M μ 𝓕 (H.e x) (H.e y))
    {v : M.Vec} (hv : IsUnitV v) {x y : H.H} (hxy : H.e x v = H.e y v) : x = y := by
  have := (eq_smul_of_eval_eq H d h hv hv hxy).1
  rwa [prod_inner_self hv, one_smul] at this

theorem exists_smul_of_eval_eq (H : HMod (MMap M)) (d : ℂ) (h : ∀ x y : H.H, inner ℂ x y = d * ipM M μ 𝓕 (H.e x) (H.e y))
    {v v' : M.Vec} (hv : IsUnitV v) (hv' : IsUnitV v') {C : Type} {x y : C → H.H} (hxy : ∀ f, H.e (x f) v = H.e (y f) v') :
    ∃ s : ℂ, s ≠ 0 ∧ ∀ f, x f = s • y f := by
  by_cases hs : (∏ τ, ⟪(v τ : M.H τ), (v' τ : M.H τ)⟫_ℂ) = 0
  · refine ⟨1, one_ne_zero, fun f => ?_⟩
    obtain ⟨h1, h2⟩ := eq_smul_of_eval_eq H d h hv hv' (hxy f)
    rw [hs, zero_smul] at h1
    rw [h1, norm_zero] at h2
    rw [h1, norm_eq_zero.1 h2.symm, smul_zero]
  · exact ⟨_, hs, fun f => (eq_smul_of_eval_eq H d h hv hv' (hxy f)).1⟩

end Schur

section Form

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] {C : Type} [AddCommGroup C] [Module K C]
  {WL : Type} [AddCommGroup WL] [Module L WL] [Module K WL] [IsScalarTower K L WL]
  {W : (L →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)] {G : Type} [Group G]

theorem exists_bases (F : FormsL L K WL W G) (h : F.IsKsForm) (e : C ≃ₗ[K] F.WK) :
    ∃ (n : ℕ) (b : Basis (Fin n) K C) (B : Basis (Fin n) L WL), ∀ k, B k = (e (b k) : WL) := by
  obtain ⟨n, b, hb, h1, h2, h3, h4⟩ := h
  have h5 : LinearIndependent K fun k => (⟨b k, hb k⟩ : F.WK) := LinearIndependent.of_comp F.WK.subtype h1
  have h6 : ⊤ ≤ Submodule.span K (Set.range fun k => (⟨b k, hb k⟩ : F.WK)) :=
    ((Submodule.span_range_subtype_eq_top_iff _ hb).2 h2).ge
  refine ⟨n, (Basis.mk h5 h6).map e.symm, Basis.mk h3 h4.ge, fun k => ?_⟩
  simp

theorem equivFun_eq_crd {F : FormsL L K WL W G} {e : C ≃ₗ[K] F.WK} {n : ℕ} {b : Basis (Fin n) K C} {B : Basis (Fin n) L WL}
    (hB : ∀ k, B k = (e (b k) : WL)) (f : C) : B.equivFun (e f : WL) = crd L b f := by
  rw [← LinearEquiv.eq_symm_apply, Basis.equivFun_symm_apply]
  conv_lhs => rw [← b.sum_repr f]
  simp only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul, crd_apply, hB, algebraMap_smul]

theorem indep_span (F : FormsL L K WL W G) (h : F.IsKsForm) (e : C ≃ₗ[K] F.WK) (σ : L →+* ℂ) {y : C → W σ} {s : ℂ} (hs : s ≠ 0)
    (hy : ∀ f, F.j σ (e f : WL) = s • y f)
    (h1 : ∀ (m : ℕ) (b : Fin m → C), LinearIndependent K b → LinearIndependent ℂ fun k => y (b k))
    (h2 : Submodule.span ℂ (Set.range y) = ⊤) :
    (∀ (m : ℕ) (x : Fin m → WL), LinearIndependent L x → LinearIndependent ℂ fun k => F.j σ (x k)) ∧
      Submodule.span ℂ (Set.range (F.j σ)) = ⊤ := by
  obtain ⟨n, b, B, hB⟩ := exists_bases F h e
  refine ⟨fun m x hx => ?_, ?_⟩
  · have h3 : LinearIndependent ℂ fun k => F.j σ (B k) := by
      have := (h1 n b b.linearIndependent).units_smul fun _ => Units.mk0 s hs
      convert this using 2 with k
      rw [hB, hy]
      rfl
    have h4 := extB_indep σ h3 (hx.map' B.equivFun.toLinearMap B.equivFun.ker)
    convert h4 using 2 with k
    conv_lhs => rw [← B.sum_repr (x k)]
    simp only [map_sum, map_smulₛₗ]
    rfl
  · rw [eq_top_iff, ← h2, Submodule.span_le]
    rintro _ ⟨f, rfl⟩
    have : y f = s⁻¹ • F.j σ (e f : WL) := by rw [hy, smul_smul, inv_mul_cancel₀ hs, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

variable {X : Type} [AddCommGroup X] [Module ℂ X]

theorem rhoIs_of_form (F : FormsL L K WL W G) (h : F.IsKsForm) (e : C ≃ₗ[K] F.WK) (σ : L →+* ℂ) (E : W σ →ₗ[ℂ] X)
    (act : G → X →ₗ[ℂ] X) (chi : G →* Lˣ) (ρ : G →* (WL →ₗ[L] WL))
    (hf : ∀ g (f : C), E (F.j σ (ρ g (e f : WL))) = σ ((chi g : Lˣ) : L) • act g (E (F.j σ (e f : WL)))) :
    RhoIs σ (F.j σ) E act chi ρ := by
  obtain ⟨n, b, B, hB⟩ := exists_bases F h e
  intro g x
  rw [← B.sum_repr x]
  simp only [map_sum, map_smulₛₗ, Finset.smul_sum, RingHom.id_apply, hB, hf]
  exact Finset.sum_congr rfl fun k _ => smul_comm _ _ _

theorem exists_ext_action (F : FormsL L K WL W G) (h : F.IsKsForm) (e : C ≃ₗ[K] F.WK) (ρC : G →* (C →ₗ[K] C)) :
    ∃ ρ : G →* (WL →ₗ[L] WL), ∀ g f, ρ g (e f : WL) = (e (ρC g f) : WL) := by
  obtain ⟨n, b, B, hB⟩ := exists_bases F h e
  refine ⟨(B.equivFun.symm.conjRingEquiv : _ →* _).comp (rhoB L b ρC), fun g f => ?_⟩
  show B.equivFun.symm (rhoB L b ρC g (B.equivFun (e f : WL))) = _
  rw [equivFun_eq_crd hB, rhoB_crd, ← equivFun_eq_crd hB, LinearEquiv.symm_apply_apply]

theorem injective_of_indep {σ : L →+* ℂ} (j : WL →ₛₗ[σ] W σ)
    (h : ∀ (m : ℕ) (x : Fin m → WL), LinearIndependent L x → LinearIndependent ℂ fun k => j (x k)) : Function.Injective j := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra h0
  exact (h 1 (fun _ => x) (linearIndependent_unique_iff.2 h0)).ne_zero 0 hx

end Form

section Comparison₂

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
  {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}

theorem subsingleton_of_jTop (hu : JUnif T R κ v₀) {i : Fin D.R.m} {σ : D.what₂.LL →+* ℂ} (h : jTop T R κ v₀ i σ = 0) :
    Subsingleton (R.HW i σ).H := by
  have h1 := (hu i σ).2
  rw [h] at h1
  refine subsingleton_of_forall_eq 0 fun x => ?_
  have hx : x ∈ Submodule.span ℂ (Set.range (0 : Cu T κ i →ₛₗ[res T σ] (R.HW i σ).H)) := h1 ▸ Submodule.mem_top
  refine (Submodule.mem_bot ℂ).1 ((Submodule.span_le.2 ?_ : _ ≤ (⊥ : Submodule ℂ _)) hx)
  rintro _ ⟨f, rfl⟩
  exact (Submodule.mem_bot ℂ).2 rfl

theorem jEvAt_of_nontrivial (hu : JUnif T R κ v₀) {i : Fin D.R.m} {σ : D.what₂.LL →+* ℂ} (hσ : GoodEmb T.Q.c (res T σ))
    (hn : ¬ Subsingleton (R.HW i σ).H) : ∃ hV, JEvAt T R κ v₀ i σ hV := by
  by_contra h
  refine hn (subsingleton_of_jTop hu ?_)
  by_cases hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i
  · exact jTop_good0 T R κ v₀ hσ hV fun h' => h ⟨hV, h'⟩
  · rw [jTop, if_pos hσ, dif_neg hV]

theorem jEvBarAt_of_nontrivial (hu : JUnif T R κ v₀) {i : Fin D.R.m} {σ : D.what₂.LL →+* ℂ} (hσ : ¬ GoodEmb T.Q.c (res T σ))
    (hn : ¬ Subsingleton (R.HW i σ).H) : ∃ hV, JEvBarAt T R κ i σ hV := by
  by_contra h
  exact hn (subsingleton_of_jTop hu (by rw [jTop, if_neg hσ, dif_neg h]))

theorem evAt_jK (t : FWTie T R κ v₀) {i : Fin D.R.m} {σ : D.what₂.LL →+* ℂ} (hσ : GoodEmb T.Q.c (res T σ))
    {hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i} (h : JEvAt T R κ v₀ i σ hV) (f : Cu T κ i) :
    evAt R i σ (v₀ i σ) (t.jK i σ f) = phiC T hV (wtA (κ i)) (f : T.R ((i : ℕ) + 1)) := by
  obtain ⟨jK, hjK⟩ := h
  obtain ⟨j', hj'⟩ := exists_ext_of_isKsForm (R.FW i) (t.ks i) (t.e i) σ jK
  exact t.ev i σ hσ hV ⟨j', fun f => (congrArg (evAt R i σ (v₀ i σ)) (hj' f)).trans (hjK f)⟩ f

theorem exists_jK_eq_smul (t : FWTie T R κ v₀) (he : R.models_HW) (hb : BarTie t) (hu : JUnif T R κ v₀) (i : Fin D.R.m)
    (σ : D.what₂.LL →+* ℂ) : ∃ s : ℂ, s ≠ 0 ∧ ∀ f, t.jK i σ f = s • jTop T R κ v₀ i σ f := by
  by_cases hn : Subsingleton (R.HW i σ).H
  · exact ⟨1, one_ne_zero, fun f => Subsingleton.elim _ _⟩
  by_cases hσ : GoodEmb T.Q.c (res T σ)
  · obtain ⟨hV, h⟩ := jEvAt_of_nontrivial hu hσ hn
    exact exists_smul_of_eval_eq (R.HW i σ) _ (he i σ).2.2 (t.hv₀ i σ).norm (t.hv₀ i σ).norm fun f =>
      (evAt_jK t hσ h f).trans (jTop_good T R κ v₀ hσ hV h f).symm
  · obtain ⟨hV, h⟩ := jEvBarAt_of_nontrivial hu hσ hn
    obtain ⟨v, hv, h1⟩ := (hb i σ hσ hV).1 h
    obtain ⟨v', hv', h2⟩ := jTop_bar T R κ v₀ hσ hV h
    exact exists_smul_of_eval_eq (R.HW i σ) _ (he i σ).2.2 hv hv' fun f => (h1 f).trans (h2 f).symm

theorem indep_span_of_tie (t : FWTie T R κ v₀) (he : R.models_HW) (hb : BarTie t) (hu : JUnif T R κ v₀) (i : Fin D.R.m)
    (σ : D.what₂.LL →+* ℂ) :
    (∀ (n : ℕ) (b : Fin n → (Fin (R.nW i) → D.what₂.LL)), LinearIndependent D.what₂.LL b →
      LinearIndependent ℂ fun k => (R.FW i).j σ (b k)) ∧ Submodule.span ℂ (Set.range ((R.FW i).j σ)) = ⊤ := by
  obtain ⟨s, hs, h⟩ := exists_jK_eq_smul t he hb hu i σ
  exact indep_span (C := Cu T κ i) (R.FW i) (t.ks i) (t.e i) σ hs h (hu i σ).1 (hu i σ).2

theorem chi_eq_chiTop (hc : R.grp_chiW) (i : Fin D.R.m) : (R.FW i).chi = chiTop R i := by
  have h1 : ChiIs R i (R.FW i).chi := fun g => (hc i g).trans (Units.coe_prod _ _).symm
  have h2 : ChiIs R i (chiTop R i) := by
    have hex : ∃ chi, ChiIs R i chi := ⟨_, h1⟩
    rw [chiTop, dif_pos hex]
    exact hex.choose_spec
  exact MonoidHom.ext fun g => Units.ext (D.what₂.embLL.injective ((h1 g).trans (h2 g).symm))

theorem jK_apply (t : FWTie T R κ v₀) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (f : Cu T κ i) :
    t.jK i σ f = (R.FW i).j σ ((t.e i f : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL) := rfl

theorem equiv_smul {H X : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup X] [Module ℂ X] (E : H →ₗ[ℂ] X) (a : X →ₗ[ℂ] X)
    {s c : ℂ} {x x' y y' : H} (hx : x = s • y) (hx' : x' = s • y') (h : E y = c • a (E y')) : E x = c • a (E x') := by
  rw [hx, hx', map_smul, map_smul, map_smul, h, smul_comm]

theorem exists_rhoIs_all (t : FWTie T R κ v₀) (he : R.models_HW) (hc : R.grp_chiW) (hb : BarTie t) (hu : JUnif T R κ v₀)
    (hg : GeoAct T R κ v₀) (i : Fin D.R.m) :
    ∃ ρ, ∀ σ, RhoIs σ ((R.FW i).j σ) (R.HW i σ).e (actW R i σ) (R.FW i).chi ρ := by
  obtain ⟨ρC, hρ⟩ := hg i
  obtain ⟨ρ, h1⟩ := exists_ext_action (C := Cu T κ i) (R.FW i) (t.ks i) (t.e i) ρC
  refine ⟨ρ, fun σ => rhoIs_of_form (C := Cu T κ i) (R.FW i) (t.ks i) (t.e i) σ (R.HW i σ).e (actW R i σ) (R.FW i).chi ρ
    fun g f => ?_⟩
  obtain ⟨s, -, h⟩ := exists_jK_eq_smul t he hb hu i σ
  have h2 := hρ.1 σ g f
  rw [← chi_eq_chiTop hc i] at h2
  have h3 := (congrArg ((R.FW i).j σ) (h1 g f)).trans ((jK_apply t i σ (ρC g f)).symm.trans (h (ρC g f)))
  have h4 := (jK_apply t i σ f).symm.trans (h f)
  have h5 := equiv_smul (R.HW i σ).e (actW R i σ g) h3 h4 h2
  exact h5

theorem lUnif_of_rhoIs_at (t : FWTie T R κ v₀) (he : R.models_HW) (hc : R.grp_chiW) (hb : BarTie t) (hu : JUnif T R κ v₀)
    (hg : GeoAct T R κ v₀)
    (h0 : ∀ i, ∃ σ, RhoIs σ ((R.FW i).j σ) (R.HW i σ).e (actW R i σ) (R.FW i).chi (R.FW i).ρ) : R.LUnif := by
  intro i σ
  refine ⟨(indep_span_of_tie t he hb hu i σ).1, (indep_span_of_tie t he hb hu i σ).2, ?_⟩
  obtain ⟨ρ, hρ⟩ := exists_rhoIs_all t he hc hb hu hg i
  obtain ⟨σ₁, h1⟩ := h0 i
  have e : (R.FW i).ρ = ρ := RhoIs.unique
    (injective_of_indep (W := fun σ => (R.HW i σ).H) _ (indep_span_of_tie t he hb hu i σ₁).1) (he i σ₁).1 h1 (hρ σ₁)
  have h2 := hρ σ
  rw [← e] at h2
  exact h2

theorem levChi_flag_datWp (i : Fin D.R.m) (k : GA D (Wc D i)) :
    levChi (Wc D i) (R.βW i) (flagL (R.datWp i R.triv)) k = 1 := by
  have h2 : Formalism.L2.DIV.ext1 (flagL (R.datWp i R.triv)).P.H (flagL (R.datWp i R.triv)).P.chi
      (Formalism.L2.DIV.rTup (R.βW i) (flagL (R.datWp i R.triv)) (finE (Wc D i) k)) = 1 := subgroupCharExtension_one_apply _ _
  unfold levChi Formalism.L2.DIV.levFn
  rw [h2]
  show ((1 * (∏ PP ∈ R.Pg, ∏ c ∈ Finset.range 0, _) * ∏ PP ∈ ∅, _ : ℂˣ) : ℂ) = 1
  simp

theorem exists_lift_actW (he : R.models_HW) (hw : R.models_gW) {i : Fin D.R.m} {σ : D.what₂.LL →+* ℂ}
    (hn : ¬ Subsingleton (R.HW i σ).H) (g : G) :
    ∃ k, IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k ∧
      ∀ (x : MMap (R.MW i σ)) v h, actW R i σ g x v h = x v (h * k) := by
  by_cases hk : ∃ k, IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k
  · refine ⟨hk.choose, hk.choose_spec, fun x v h => ?_⟩
    show actG0 (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) (x v) h = _
    unfold actG0
    rw [dif_pos hk]
    simp only [levChi_flag_datWp, inv_one, one_mul]
  · refine absurd (subsingleton_of_forall_eq 0 fun x => ?_) hn
    have h1 : (R.HW i σ).e (R.gW i σ g (R.gW i σ g⁻¹ x)) = 0 := by
      rw [hw]
      refine MultilinearMap.ext fun v => ?_
      show actG0 (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) _ = 0
      exact dif_neg hk
    rw [Representation.self_inv_apply] at h1
    exact (he i σ).1 (h1.trans (map_zero _).symm)

theorem equiv_of_values (he : R.models_HW) (hw : R.models_gW) {i : Fin D.R.m} {σ : D.what₂.LL →+* ℂ} {v : (R.MW i σ).Vec}
    (hv : IsUnitV v) {g : G} {k : GA D (Wc D i)} (hk : ∀ (x : MMap (R.MW i σ)) v h, actW R i σ g x v h = x v (h * k))
    {x y : (R.HW i σ).H} {c : ℂ} (h : ∀ h, evAt R i σ v x h = c * evAt R i σ v y (h * k)) :
    (R.HW i σ).e x = c • actW R i σ g ((R.HW i σ).e y) := by
  have h2 : actW R i σ g ((R.HW i σ).e y) = (R.HW i σ).e (R.gW i σ g y) := (hw i σ g _).symm
  have h3 : x = c • R.gW i σ g y := by
    refine eq_of_eval_eq (R.HW i σ) _ (he i σ).2.2 hv (funext fun h' => ?_)
    have h4 : (R.HW i σ).e (c • R.gW i σ g y) = c • actW R i σ g ((R.HW i σ).e y) := by
      rw [h2]; exact (R.HW i σ).e.map_smul _ _
    rw [h4]
    exact (h h').trans (congrArg (c * ·) (hk _ v h').symm)
  rw [h2]
  exact (congrArg (R.HW i σ).e h3).trans ((R.HW i σ).e.map_smul _ _)

variable {O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)}

theorem rhoIs_of_values (t : FWTie T R κ v₀) (he : R.models_HW) (hw : R.models_gW) (hr : RhoGeo t O) {i : Fin D.R.m}
    {σ : D.what₂.LL →+* ℂ} (hn : ¬ Subsingleton (R.HW i σ).H) {v : (R.MW i σ).Vec} (hv : IsUnitV v)
    {φ : T.R ((i : ℕ) + 1) → GA D (Wc D i) → ℂ} (hφ : ∀ f : Cu T κ i, evAt R i σ v (t.jK i σ f) = φ f)
    (hq : ∀ g k, IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k →
      ∀ f ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n,
        actLev T.Q.c (O i).lev2 g f ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n ∧
        ∀ h, φ (actLev T.Q.c (O i).lev2 g f) h = σ (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL) * φ f (h * k)) :
    RhoIs σ ((R.FW i).j σ) (R.HW i σ).e (actW R i σ) (R.FW i).chi (R.FW i).ρ := by
  have hk : ActKeeps (κ := κ) O i := fun g f hf => by
    obtain ⟨k, hk, -⟩ := exists_lift_actW he hw hn g
    exact (hq g k hk f hf).1
  refine rhoIs_of_form (C := Cu T κ i) (R.FW i) (t.ks i) (t.e i) σ (R.HW i σ).e (actW R i σ) (R.FW i).chi (R.FW i).ρ
    fun g f => ?_
  obtain ⟨k, hk1, hk2⟩ := exists_lift_actW he hw hn g
  have h0 := (hr i).1 hk g f
  refine h0.elim fun hf h1 => ?_
  have h5 := fun h => ((congrFun (hφ ⟨_, hf⟩) h).trans ((hq g k hk1 f f.2).2 h)).trans
    (congrArg (σ (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL) * ·) (congrFun (hφ f) (h * k)).symm)
  have h6 := equiv_of_values he hw hv hk2 h5
  have h7 := (congrArg ((R.FW i).j σ) h1.symm).trans (jK_apply t i σ ⟨_, hf⟩).symm
  have h8 := (congrArg (R.HW i σ).e h7).trans h6
  rw [jK_apply] at h8
  exact h8

theorem rhoIs_of_subsingleton {i : Fin D.R.m} {σ : D.what₂.LL →+* ℂ} (hn : Subsingleton (R.HW i σ).H) :
    RhoIs σ ((R.FW i).j σ) (R.HW i σ).e (actW R i σ) (R.FW i).chi (R.FW i).ρ := fun g x => by
  rw [Subsingleton.elim ((R.FW i).j σ ((R.FW i).ρ g x)) 0, Subsingleton.elim ((R.FW i).j σ x) 0, map_zero, map_zero, smul_zero]

omit [Algebra T.Q.c.F D.what₂.LL] in
theorem phiC_eq_phiAt (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ) (hV : T.V ((i : ℕ) + 1) σ = Wc D i)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R ((i : ℕ) + 1)) (h : GA D (Wc D i)) :
    phiC T hV a f h = (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) a : ℂ) * phiAt T i σ hV (T.cE ((i : ℕ) + 1) σ) f h := by
  have key : ∀ (W : HSp D) (hV : T.V ((i : ℕ) + 1) σ = W) (g : GA D W), phiC T hV a f g =
      (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) a : ℂ) * castDict hV (adel (T.V ((i : ℕ) + 1) σ) (T.dict ((i : ℕ) + 1) σ)
        (muPin (T.V ((i : ℕ) + 1) σ) (T.dict ((i : ℕ) + 1) σ) (T.mu ((i : ℕ) + 1) σ) (T.cE ((i : ℕ) + 1) σ))
        (rdU (T.U ((i : ℕ) + 1) σ) f)) g := by
    intro W hV g
    subst hV
    rfl
  exact key _ hV h

theorem phiC_equiv (hc : R.grp_chiW) {i : Fin D.R.m} {σ' : T.Q.c.F →+* ℂ} {hV : T.V ((i : ℕ) + 1) σ' = Wc D i}
    (hq : EqAt T R κ (O i) σ' hV (T.cE ((i : ℕ) + 1) σ')) (g : G) (k : GA D (Wc D i))
    (hk : IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k) (f : T.R ((i : ℕ) + 1))
    (hf : f ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n) :
    actLev T.Q.c (O i).lev2 g f ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n ∧
      ∃ y : T.Q.c.F, (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL) = algebraMap T.Q.c.F D.what₂.LL y ∧
        ∀ h, phiC T hV (wtA (κ i)) (actLev T.Q.c (O i).lev2 g f) h = σ' y * phiC T hV (wtA (κ i)) f (h * k) := by
  obtain ⟨h1, y, hy, h2⟩ := hq g k hk f hf
  refine ⟨h1, y, D.what₂.embLL.injective ((hc i g).trans hy.symm), fun h => ?_⟩
  rw [phiC_eq_phiAt, phiC_eq_phiAt, h2, mul_left_comm]

theorem rhoIs_of_eqAt (t : FWTie T R κ v₀) (he : R.models_HW) (hw : R.models_gW) (hc : R.grp_chiW) (hb : BarTie t)
    (hr : RhoGeo t O) (hu : JUnif T R κ v₀) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ)
    (h1 : GoodEmb T.Q.c (res T σ) → ∀ hV, EqAt T R κ (O i) (res T σ) hV (T.cE ((i : ℕ) + 1) (res T σ)))
    (h2 : ¬ GoodEmb T.Q.c (res T σ) → ∀ hV, EqAt T R κ (O i) (resC T σ) hV (T.cE ((i : ℕ) + 1) (resC T σ))) :
    RhoIs σ ((R.FW i).j σ) (R.HW i σ).e (actW R i σ) (R.FW i).chi (R.FW i).ρ := by
  by_cases hn : Subsingleton (R.HW i σ).H
  · exact rhoIs_of_subsingleton hn
  by_cases hσ : GoodEmb T.Q.c (res T σ)
  · obtain ⟨hV, h⟩ := jEvAt_of_nontrivial hu hσ hn
    refine rhoIs_of_values t he hw hr hn (t.hv₀ i σ).norm (φ := phiC T hV (wtA (κ i))) (evAt_jK t hσ h) fun g k hk f hf => ?_
    obtain ⟨h3, y, hy, h4⟩ := phiC_equiv hc (h1 hσ hV) g k hk f hf
    exact ⟨h3, fun h => by rw [hy]; exact h4 h⟩
  · obtain ⟨hV, h⟩ := jEvBarAt_of_nontrivial hu hσ hn
    obtain ⟨v, hv, h5⟩ := (hb i σ hσ hV).1 h
    refine rhoIs_of_values t he hw hr hn hv (φ := fun f g => starRingEnd ℂ (phiC T hV (wtA (κ i)) f g)) h5 fun g k hk f hf => ?_
    obtain ⟨h3, y, hy, h4⟩ := phiC_equiv hc (h2 hσ hV) g k hk f hf
    refine ⟨h3, fun h => ?_⟩
    show starRingEnd ℂ _ = _ * starRingEnd ℂ _
    rw [hy, h4, map_mul]
    exact congrArg (· * _) (Complex.conj_conj _)

variable (T R κ O) in

def EquivConstExist : Prop :=
  ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i,
    ∃ c', CUnit c' ∧ EqAt T R κ (O i) σ hV c'

variable (T R κ O) in

def EquivConstExistBase : Prop :=
  ∀ (i : Fin D.R.m) (hV : T.V ((i : ℕ) + 1) T.toCore.σ₀ = Wc D i), ∃ c', CUnit c' ∧ EqAt T R κ (O i) T.toCore.σ₀ hV c'

theorem EquivConstExist.base (h : EquivConstExist T R κ O) : EquivConstExistBase T R κ O :=
  fun i hV => h i _ T.good_σ₀ hV

variable {F : Face D A}

theorem lUnif_of_rhoGeo_equivAll (t : FWTie T R κ v₀) (hM : R.IsModels) (hG : R.IsGrp F) (hb : BarTie t) (hr : RhoGeo t O)
    (ha : EquivAll T R κ O) (hx : EquivConstExist T R κ O) (hu : JUnif T R κ v₀) : R.LUnif := fun i σ =>
  ⟨(indep_span_of_tie t hM.HW hb hu i σ).1, (indep_span_of_tie t hM.HW hb hu i σ).2,
    rhoIs_of_eqAt t hM.HW hM.gW hG.chiW hb hr hu i σ (fun h hV => ha i _ h hV (hx i _ h hV))
      fun h hV => ha i _ (good_resC T h) hV (hx i _ (good_resC T h) hV)⟩

end Comparison₂

end GlobalTheory.TiedUnif
