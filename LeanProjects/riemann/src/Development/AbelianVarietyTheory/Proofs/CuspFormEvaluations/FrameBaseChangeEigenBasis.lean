import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LiePush
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsLieBasisBaseChange
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.GlobalBasisAlgebra

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FrameBaseChange

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}

theorem spMap_spMap {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R' →+* R'')
    (g : R →+* R') : spMap f ≫ spMap g = spMap (f.comp g) := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

private theorem isTangent_iff_isTanAt_of_isGrpPullback {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {G' : Over (Sp S)} [GrpObj G']
    {φ : G'.left ⟶ Xo.univ.t.G.left} (h : IsGrpPullback G' Xo.univ.t.G x φ) (w : epsR S ⟶ G') :
    IsTangent w ↔ IsTanAt x (w.left ≫ φ) := by
  rw [Chart.tan_push h w]
  have hw1 : (w.left ≫ φ) ≫ Xo.univ.t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x := by
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w w]
    rfl
  exact ⟨fun h2 => ⟨hw1, h2⟩, fun h2 => h2.2⟩

private theorem isLieComb_iff_isCombAt_of_isGrpPullback {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {G' : Over (Sp S)} [GrpObj G']
    {φ : G'.left ⟶ Xo.univ.t.G.left} (h : IsGrpPullback G' Xo.univ.t.G x φ) {n : ℕ} (c : Fin n → S)
    (v : Fin n → (epsR S ⟶ G')) (w : epsR S ⟶ G') :
    IsLieComb c v w ↔ IsCombAt x (fun i => (v i).left ≫ φ) c (w.left ≫ φ) := by
  rw [Chart.comb_push h c v w]
  rfl

private theorem exists_tangent_lift_of_isGrpPullback {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {G' : Over (Sp S)} [GrpObj G']
    {φ : G'.left ⟶ Xo.univ.t.G.left} (h : IsGrpPullback G' Xo.univ.t.G x φ)
    (w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left) (hw : IsTanAt x w) : ∃ w' : epsR S ⟶ G', w'.left ≫ φ = w :=
  ⟨Over.homMk (h.1.lift w (spMap (algebraMap S (DualNumber S))) hw.1) (h.1.lift_snd _ _ _), h.1.lift_fst _ _ _⟩

theorem basis_baseChange {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (x : Sp S ⟶ Xo.X) {n : ℕ}
    (u : Fin n → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (hu : ∀ i, IsTanAt x (u i))
    (hb : ∀ w, IsTanAt x w → ∃! a : Fin n → S, IsCombAt x u a w) :
    (∀ i, IsTanAt (spMap ψ ≫ x) (spMap (dualMap ψ) ≫ u i)) ∧
    ∀ w, IsTanAt (spMap ψ ≫ x) w →
      ∃! a : Fin n → T, IsCombAt (spMap ψ ≫ x) (fun i => spMap (dualMap ψ) ≫ u i) a w := by
  classical
  have hS := isGrpPullback_pullback Xo.univ.t.G x
  have hT0 := isGrpPullback_pullback ((Over.pullback x).obj Xo.univ.t.G) (spMap ψ)
  have hT := hT0.comp hS
  have hsm : Smooth ((Over.pullback x).obj Xo.univ.t.G).hom := by
    have := Xo.univ.t.semi.smooth
    exact inferInstanceAs (Smooth (pullback.snd Xo.univ.t.G.hom x))
  choose vS hvS using fun i => exists_tangent_lift_of_isGrpPullback hS (u i) (hu i)
  have e1 : (fun i => (vS i).left ≫ pullback.fst Xo.univ.t.G.hom x) = u := funext hvS
  have hv : IsLieBasis vS := by
    refine ⟨fun i => (isTangent_iff_isTanAt_of_isGrpPullback hS (vS i)).2 (by rw [hvS i]; exact hu i), fun w hw => ?_⟩
    obtain ⟨a, ha, hu'⟩ := hb _ ((isTangent_iff_isTanAt_of_isGrpPullback hS w).1 hw)
    refine ⟨a, (isLieComb_iff_isCombAt_of_isGrpPullback hS a vS w).2 (by rw [e1]; exact ha), fun a' ha' => hu' a' ?_⟩
    have h2 := (isLieComb_iff_isCombAt_of_isGrpPullback hS a' vS w).1 ha'
    rwa [e1] at h2
  obtain ⟨v', hv', hv'φ⟩ := _root_.GlobalTheory.exists_isLieBasis_baseChange S T ψ _ _ _ hT0 hsm n vS hv
  have hd : Chart.dualMapR ψ = dualMap ψ := RingHom.ext fun r => rfl
  have hvT : ∀ i, (v' i).left ≫ (pullback.fst ((Over.pullback x).obj Xo.univ.t.G).hom (spMap ψ) ≫
      pullback.fst Xo.univ.t.G.hom x) = spMap (dualMap ψ) ≫ u i := by
    intro i
    rw [← Category.assoc, hv'φ i, Category.assoc, hvS i, hd]
  have e2 : (fun i => (v' i).left ≫ (pullback.fst ((Over.pullback x).obj Xo.univ.t.G).hom (spMap ψ) ≫
      pullback.fst Xo.univ.t.G.hom x)) = fun i => spMap (dualMap ψ) ≫ u i := funext hvT
  refine ⟨fun i => ?_, fun w hw => ?_⟩
  · rw [← hvT i]
    exact (isTangent_iff_isTanAt_of_isGrpPullback hT (v' i)).1 (hv'.1 i)
  · obtain ⟨w', hw'⟩ := exists_tangent_lift_of_isGrpPullback hT w hw
    obtain ⟨a, ha, hu'⟩ := hv'.2 w' ((isTangent_iff_isTanAt_of_isGrpPullback hT w').2 (by rw [hw']; exact hw))
    refine ⟨a, ?_, fun a' ha' => hu' a' ?_⟩
    · have h2 := (isLieComb_iff_isCombAt_of_isGrpPullback hT a v' w').1 ha
      rwa [e2, hw'] at h2
    · apply (isLieComb_iff_isCombAt_of_isGrpPullback hT a' v' w').2
      rw [e2, hw']
      exact ha'

variable {T : Type} [CommRing T] {x : Sp T ⟶ Xo.X}

def epsEnd (x : Sp T ⟶ Xo.X) (a : T) : tEps x ⟶ tEps x :=
  Over.homMk (spMap (epsMul a)) (by
    change spMap _ ≫ spMap _ ≫ x = spMap _ ≫ x
    rw [← Category.assoc, spMap_spMap]
    congr 2
    ext r <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl])

theorem epsEnd_comp (a b : T) : epsEnd x a ≫ epsEnd x b = epsEnd x (a * b) := by
  have h : (epsMul a).comp (epsMul b) = epsMul (a * b) := by
    ext r <;> simp [epsMul]
  apply Over.OverMorphism.ext
  show spMap (epsMul a) ≫ spMap (epsMul b) = spMap (epsMul (a * b))
  rw [spMap_spMap, h]

theorem epsEnd_zero (W : tEps x ⟶ Xo.univ.t.G) (hW : IsTanAt x W.left) : epsEnd x 0 ≫ W = 1 := by
  have h0 : epsMul (0 : T) = (algebraMap T (DualNumber T)).comp (TrivSqZeroExt.fstHom T T T).toRingHom := by
    ext r <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]
  have e : (Over.homMk (spMap (algebraMap T (DualNumber T))) rfl : tEps x ⟶ Over.mk x) ≫
      (1 : Over.mk x ⟶ Xo.univ.t.G) = 1 := MonObj.comp_one _
  apply Over.OverMorphism.ext
  show spMap (epsMul 0) ≫ W.left = _
  rw [h0, ← spMap_spMap, Category.assoc, hW.2, ← e]
  rfl

theorem isTanAt_epsEnd (a : T) (W : tEps x ⟶ Xo.univ.t.G) (hW : IsTanAt x W.left) :
    IsTanAt x (epsEnd x a ≫ W).left := by
  have h1 : (TrivSqZeroExt.fstHom T T T).toRingHom.comp (epsMul a) = (TrivSqZeroExt.fstHom T T T).toRingHom := by
    exact RingHom.ext fun r => by simp [epsMul]
  refine ⟨Over.w (epsEnd x a ≫ W), ?_⟩
  show spMap _ ≫ spMap (epsMul a) ≫ W.left = _
  rw [← Category.assoc, spMap_spMap, h1]
  exact hW.2

theorem isCombAt_iff {m : ℕ} (v : Fin m → (tEps x ⟶ Xo.univ.t.G)) (cf : Fin m → T)
    (W : tEps x ⟶ Xo.univ.t.G) :
    IsCombAt x (fun j => (v j).left) cf W.left ↔ ∏ j, epsEnd x (cf j) ≫ v j = W := by
  constructor
  · rintro ⟨u, hu, hprod⟩
    have e : u = fun j => epsEnd x (cf j) ≫ v j := funext fun j => Over.OverMorphism.ext (hu j)
    subst e
    apply Over.OverMorphism.ext
    rw [← hprod, Fin.prod_ofFn]
  · intro h
    refine ⟨fun j => epsEnd x (cf j) ≫ v j, fun j => rfl, ?_⟩
    rw [Fin.prod_ofFn, h]

theorem comp_prod {κ : Type} [Fintype κ] (f : tEps x ⟶ tEps x) (u : κ → (tEps x ⟶ Xo.univ.t.G)) :
    f ≫ ∏ k, u k = ∏ k, f ≫ u k := by
  exact map_prod (⟨⟨fun g => f ≫ g, MonObj.comp_one f⟩, MonObj.comp_mul f⟩ :
    (tEps x ⟶ Xo.univ.t.G) →* (tEps x ⟶ Xo.univ.t.G)) u Finset.univ

theorem prod_comp {κ : Type} [Fintype κ] (φ : Xo.univ.t.G ⟶ Xo.univ.t.G) [IsMonHom φ]
    (u : κ → (tEps x ⟶ Xo.univ.t.G)) : (∏ k, u k) ≫ φ = ∏ k, u k ≫ φ := by
  exact map_prod (IsMonHom.monoidHom φ (tEps x)) u Finset.univ

theorem exists_embK_ne (c : Coeff l) {σ τ : E →+* ℂ} (h : σ ≠ τ) : ∃ b : 𝓞 E, embK c σ b ≠ embK c τ b := by
  by_contra hne
  simp only [not_exists, not_not] at hne
  apply h
  have h2 : embF c σ = embF c τ := by
    apply IsLocalization.ringHom_ext (M := nonZeroDivisors (𝓞 E))
    ext b
    exact congrArg Subtype.val (hne b)
  ext e
  exact congrArg Subtype.val (RingHom.congr_fun h2 e)

theorem eigen_basis (c : Coeff l) [Algebra c.F T] (U : Lt1 Dw → (tEps x ⟶ Xo.univ.t.G))
    (hU : ∀ k, IsTanAt x (U k).left) (hE : ∀ k, IsEigAt c k.1 (U k).left)
    (hb : ∀ W : tEps x ⟶ Xo.univ.t.G, IsTanAt x W.left → ∃! a : Lt1 Dw → T, ∏ k, epsEnd x (a k) ≫ U k = W)
    (τ : E →+* ℂ) (W : tEps x ⟶ Xo.univ.t.G) (hW : IsTanAt x W.left) (hWE : IsEigAt c τ W.left) :
    ∃! a : Fin (Dw.mult τ) → T, ∏ i, epsEnd x (a i) ≫ U ⟨τ, i⟩ = W := by
  classical
  obtain ⟨a, ha, huniq⟩ := hb W hW
  have hUk : ∀ (k : Lt1 Dw) (b : 𝓞 E),
      U k ≫ Xo.univ.t.act.act b = epsEnd x (algebraMap c.F T (embK c k.1 b)) ≫ U k :=
    fun k b => Over.OverMorphism.ext (hE k b)
  have hWb : ∀ b : 𝓞 E, W ≫ Xo.univ.t.act.act b = epsEnd x (algebraMap c.F T (embK c τ b)) ≫ W :=
    fun b => Over.OverMorphism.ext (hWE b)
  have key : ∀ (b : 𝓞 E) (k : Lt1 Dw),
      a k * algebraMap c.F T (embK c k.1 b) = algebraMap c.F T (embK c τ b) * a k := by
    intro b
    have := Xo.univ.t.act.hom b
    have hW' : IsTanAt x (W ≫ Xo.univ.t.act.act b).left := by
      rw [hWb b]; exact isTanAt_epsEnd _ W hW
    obtain ⟨a', -, hu'⟩ := hb _ hW'
    have e1 : ∏ k, epsEnd x (a k * algebraMap c.F T (embK c k.1 b)) ≫ U k = W ≫ Xo.univ.t.act.act b := by
      rw [← ha, prod_comp]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [Category.assoc, hUk k b, ← Category.assoc, epsEnd_comp]
    have e2 : ∏ k, epsEnd x (algebraMap c.F T (embK c τ b) * a k) ≫ U k = W ≫ Xo.univ.t.act.act b := by
      rw [hWb b, ← ha, comp_prod]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← Category.assoc, epsEnd_comp]
    have := (hu' (fun k => a k * algebraMap c.F T (embK c k.1 b)) e1).trans
      (hu' (fun k => algebraMap c.F T (embK c τ b) * a k) e2).symm
    intro k
    exact congrFun this k
  have hz : ∀ k : Lt1 Dw, k.1 ≠ τ → a k = 0 := by
    intro k hk
    obtain ⟨b, hb'⟩ := exists_embK_ne c hk
    have hu : IsUnit (algebraMap c.F T (embK c k.1 b - embK c τ b)) :=
      ((sub_ne_zero.2 hb').isUnit).map (algebraMap c.F T)
    have h0 : a k * algebraMap c.F T (embK c k.1 b - embK c τ b) = 0 := by
      rw [map_sub, mul_sub, key b k]; ring
    exact hu.mul_left_eq_zero.1 h0
  have red : ∀ A : Lt1 Dw → T, (∀ k : Lt1 Dw, k.1 ≠ τ → A k = 0) →
      ∏ k, epsEnd x (A k) ≫ U k = ∏ i, epsEnd x (A ⟨τ, i⟩) ≫ U ⟨τ, i⟩ := by
    intro A hA
    rw [Fintype.prod_sigma, Finset.prod_eq_single τ]
    · intro σ _ hσ
      refine Finset.prod_eq_one fun i _ => ?_
      rw [hA ⟨σ, i⟩ hσ]
      exact epsEnd_zero _ (hU _)
    · intro h; exact absurd (Finset.mem_univ τ) h
  refine ⟨fun i => a ⟨τ, i⟩, ?_, ?_⟩
  · show ∏ i, epsEnd x (a ⟨τ, i⟩) ≫ U ⟨τ, i⟩ = W
    rw [← red a hz]
    exact ha
  · intro a'' ha''
    have hAτ : ∀ i, (fun k : Lt1 Dw => if h : k.1 = τ then a'' (h ▸ k.2) else 0) ⟨τ, i⟩ = a'' i :=
      fun i => dif_pos rfl
    have hAW : ∏ k, epsEnd x ((fun k : Lt1 Dw => if h : k.1 = τ then a'' (h ▸ k.2) else 0) k) ≫ U k = W := by
      rw [red _ (fun k hk => dif_neg hk)]
      refine (Finset.prod_congr rfl fun i _ => ?_).trans ha''
      rw [dif_pos rfl]
    have hA := huniq _ hAW
    funext i
    rw [← hAτ i, hA]

end GlobalTheory.FrameBaseChange

namespace GlobalTheory

open FrameBaseChange

theorem frame_baseChange_eigen_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (ψ : S →ₐ[c.F] T) (y : FrPt Xo c S) (τ : E →+* ℂ) (w : Sp (DualNumber T) ⟶ Xo.univ.t.G.left), IsTanAt (spMap ψ.toRingHom ≫ y.x) w → IsEigAt c τ w → ∃! a : Fin (Dw.mult τ) → T, IsCombAt (spMap ψ.toRingHom ≫ y.x) (fun i => spMap (dualMap ψ.toRingHom) ≫ y.u τ i) a w := by
  intro E _ _ _ H Dw l Xo c S T _ _ _ _ ψ y τ w hw hwE
  classical
  set e := (Fintype.equivFin (Lt1 Dw)).symm with he
  have hS : ∀ w, IsTanAt y.x w → ∃! a : Fin (Fintype.card (Lt1 Dw)) → S,
      IsCombAt y.x (fun i => y.u (e i).1 (e i).2) a w := by
    intro w hw
    obtain ⟨a, ha, hu⟩ := GlobalTheory.FrameTangent.frame_tangent_basis E H Dw l Xo c S y w hw
    refine ⟨fun i => a (e i), ha, fun a' ha' => ?_⟩
    have h2 := hu (fun k => a' (e.symm k)) (by simpa [he] using ha')
    funext i
    rw [← h2]
    simp
  obtain ⟨htanT, hbT⟩ := basis_baseChange ψ.toRingHom y.x (fun i => y.u (e i).1 (e i).2)
    (fun i => y.tan _ _) hS
  have hU : ∀ k : Lt1 Dw, IsTanAt (spMap ψ.toRingHom ≫ y.x) (spMap (dualMap ψ.toRingHom) ≫ y.u k.1 k.2) := by
    intro k
    have h2 := htanT (e.symm k)
    rwa [Equiv.apply_symm_apply] at h2
  have hcomm : ∀ s : c.F, (dualMap ψ.toRingHom).comp (epsMul (algebraMap c.F S s)) =
      (epsMul (algebraMap c.F T s)).comp (dualMap ψ.toRingHom) := by
    intro s
    ext r <;> simp [dualMap, epsMul, TrivSqZeroExt.algebraMap_eq_inl]
  have hE : ∀ k : Lt1 Dw, IsEigAt c k.1 (spMap (dualMap ψ.toRingHom) ≫ y.u k.1 k.2) := by
    intro k b
    have h1 := y.eig k.1 k.2 b
    calc (spMap (dualMap ψ.toRingHom) ≫ y.u k.1 k.2) ≫ (Xo.univ.t.act.act b).left
        = spMap (dualMap ψ.toRingHom) ≫ (y.u k.1 k.2 ≫ (Xo.univ.t.act.act b).left) := Category.assoc _ _ _
      _ = (spMap (dualMap ψ.toRingHom) ≫ spMap (epsMul (algebraMap c.F S (embK c k.1 b)))) ≫ y.u k.1 k.2 := by
        rw [h1, Category.assoc]
      _ = (spMap (epsMul (algebraMap c.F T (embK c k.1 b))) ≫ spMap (dualMap ψ.toRingHom)) ≫ y.u k.1 k.2 := by
        rw [spMap_spMap, spMap_spMap, hcomm]
      _ = _ := Category.assoc _ _ _
  let U : Lt1 Dw → (tEps (spMap ψ.toRingHom ≫ y.x) ⟶ Xo.univ.t.G) := fun k =>
    Over.homMk (spMap (dualMap ψ.toRingHom) ≫ y.u k.1 k.2) (hU k).1
  have hbU : ∀ W : tEps (spMap ψ.toRingHom ≫ y.x) ⟶ Xo.univ.t.G, IsTanAt (spMap ψ.toRingHom ≫ y.x) W.left →
      ∃! a : Lt1 Dw → T, ∏ k, epsEnd (spMap ψ.toRingHom ≫ y.x) (a k) ≫ U k = W := by
    intro W hW
    obtain ⟨a, ha, hu⟩ := hbT W.left hW
    have ha' := (isCombAt_iff (fun i => U (e i)) a W).1 ha
    refine ⟨fun k => a (e.symm k), ?_, fun a' ha'' => ?_⟩
    · show ∏ k, epsEnd (spMap ψ.toRingHom ≫ y.x) (a (e.symm k)) ≫ U k = W
      rw [← Equiv.prod_comp e (fun k => epsEnd (spMap ψ.toRingHom ≫ y.x) (a (e.symm k)) ≫ U k)]
      simpa using ha'
    · have h2 := hu (fun i => a' (e i))
        ((isCombAt_iff (fun i => U (e i)) _ W).2 ((Equiv.prod_comp e _).trans ha''))
      funext k
      rw [← h2]
      simp
  obtain ⟨a, ha, hu⟩ := eigen_basis c U hU hE hbU τ (Over.homMk w hw.1) hw hwE
  exact ⟨a, (isCombAt_iff (fun i => U ⟨τ, i⟩) a (Over.homMk w hw.1)).2 ha,
    fun a' ha' => hu a' ((isCombAt_iff (fun i => U ⟨τ, i⟩) a' (Over.homMk w hw.1)).1 ha')⟩

end GlobalTheory
