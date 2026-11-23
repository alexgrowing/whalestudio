import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SvalUpSec
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsDivOfExpandsAt
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.CstDvdOfCstMulEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.NuExtA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.LN GlobalTheory.TorRef GlobalTheory.IntegralCombination
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ClosedDvd

section General

variable {V : Type} [CommRing V] {X : Scheme.{0}}

def cstHom (p : X ⟶ Sp V) (x : X) : V →+* X.presheaf.stalk x where
  toFun := cst p x
  map_one' := by rw [cst, map_one, gs_eq p x ⊤ trivial, map_one, map_one]
  map_mul' a b := by rw [cst, map_mul]; exact gs_mul p x ⊤ trivial _ _
  map_zero' := by rw [cst, map_zero]; exact gs_zero p x ⊤ trivial
  map_add' a b := by rw [cst, map_add]; exact gs_add p x ⊤ trivial _ _

theorem cstHom_apply (p : X ⟶ Sp V) (x : X) (a : V) : cstHom p x a = cst p x a := rfl

theorem gs_constFn_id (p : X ⟶ Sp V) (U : X.Opens) (x : X) (hx : x ∈ U) (a : V) :
    gs (𝟙 X) x U (constFn p U a) = cst p x a := by
  have e := gs_constFn p U (𝟙 X) x hx a
  rwa [Category.id_comp] at e

theorem not_isUnit_cst (p : X ⟶ Sp V) (x : X) {a : V} (hx : a ∈ (p x).asIdeal) : ¬ IsUnit (cst p x a) := by
  intro hu
  rw [cst, gs_eq p x ⊤ (show p x ∈ (⊤ : (Sp V).Opens) from trivial)] at hu
  have hx' : x ∈ X.basicOpen ((p.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom a)) :=
    (Scheme.mem_basicOpen X _ x (show x ∈ p ⁻¹ᵁ ⊤ from trivial)).2 hu
  have e2 := Scheme.preimage_basicOpen p ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom a)
  rw [← e2] at hx'
  have hmem : p x ∈ (Sp V).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom a) := hx'
  have e := basicOpen_eq_of_affine (R := CommRingCat.of V) a
  exact ((congrArg (fun U : (Sp V).Opens => p x ∈ U) e).mp hmem) hx

theorem exists_fst_eq_of_le (p : X ⟶ Sp V) (J : Ideal V) (x : X) (hx : J ≤ (p x).asIdeal) :
    ∃ x', pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) x' = x := by
  have h1 : x ∈ Set.range (pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))) := by
    rw [Scheme.Pullback.range_fst]
    show p x ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk J))
    rw [range_comap_of_surjective (V ⧸ J) (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective, Ideal.mk_ker]
    exact hx
  exact h1

theorem germ_mem_of_thick (p : X ⟶ Sp V) (J : Ideal V) {r : V} {W : X.Opens}
    (a : Γ(X, W)) (x' : ↑(pullback p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))))
    (hx : pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) x' ∈ W)
    (h : cst (pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) ≫ p) x' r ∣
      gs (pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))) x' W a) :
    gs (𝟙 X) (pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) x') W a ∈
      Ideal.span {cst p (pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) x') r} ⊔
        J.map (cstHom p (pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) x')) := by
  let P := pullback p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))
  let f : P ⟶ X := pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) :=
    IsClosedImmersion.spec_of_quotient_mk (R := CommRingCat.of V) J
  have : IsClosedImmersion f := inferInstanceAs (IsClosedImmersion (pullback.fst _ _))
  have h' : cst (f ≫ p) x' r ∣ gs (𝟙 P) x' (f ⁻¹ᵁ W) ((f.app W).hom a) := by
    rw [gs_pull (𝟙 P) f x' W hx, Category.id_comp]; exact h
  obtain ⟨U', hU'W, hxU', t', ht'⟩ := loc_div (f ≫ p) (f ⁻¹ᵁ W) ((f.app W).hom a) r x' hx h'
  obtain ⟨O, hO, hOeq⟩ := f.isClosedEmbedding.isInducing.isOpen_iff.1 U'.isOpen
  have hxO : f x' ∈ O := by
    have : x' ∈ f.base ⁻¹' O := by rw [hOeq]; exact hxU'
    exact this
  obtain ⟨U, hU, hxU, hUsub⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 (Scheme.isBasis_affineOpens X)
    (show f x' ∈ (⟨O, hO⟩ ⊓ W : X.Opens) from ⟨hxO, hx⟩)
  have hUW : U ≤ W := hUsub.trans inf_le_right
  have hfU : f ⁻¹ᵁ U ≤ U' := fun y hy => by
    have hyO : f y ∈ O := (hUsub hy).1
    have : y ∈ f.base ⁻¹' O := hyO
    rw [hOeq] at this
    exact this
  obtain ⟨b, hb⟩ := Scheme.Hom.app_surjective f U hU ((P.presheaf.map (homOfLE hfU).op).hom t')
  have hd : (f.app U).hom ((X.presheaf.map (homOfLE hUW).op).hom a) = (f.app U).hom (constFn p U r * b) := by
    apply fn_ext
    intro y hy
    have hyW : f y ∈ W := hUW hy
    have L1 : gs (𝟙 P) y (f ⁻¹ᵁ U) ((f.app U).hom ((X.presheaf.map (homOfLE hUW).op).hom a)) =
        cst (f ≫ p) y r * gs (𝟙 P) y U' t' := by
      have e1 := gs_pull (𝟙 P) f y U hy ((X.presheaf.map (homOfLE hUW).op).hom a)
      rw [Category.id_comp, gs_res f y hUW hy] at e1
      have e2 := gs_pull (𝟙 P) f y W hyW a
      rw [Category.id_comp] at e2
      rw [e1, ← e2]
      exact ht' y (hfU hy)
    have L2 : gs (𝟙 P) y (f ⁻¹ᵁ U) ((f.app U).hom (constFn p U r * b)) =
        cst (f ≫ p) y r * gs (𝟙 P) y U' t' := by
      have e1 := gs_pull (𝟙 P) f y U hy (constFn p U r * b)
      rw [Category.id_comp, gs_mul f y U hy, gs_constFn p U f y hy] at e1
      have e3 := gs_pull (𝟙 P) f y U hy b
      rw [Category.id_comp, hb, gs_res (𝟙 P) y hfU hy] at e3
      rw [e1, e3]
    exact L1.trans L2.symm
  have hd0 : (f.app U).hom ((X.presheaf.map (homOfLE hUW).op).hom a - constFn p U r * b) = 0 := by
    rw [map_sub, hd, sub_self]
  have hmem := mem_map_of_app_fst_eq_zero p J hU _ hd0
  have hJ : ∀ c ∈ J.map (strMap p U), gs (𝟙 X) (f x') U c ∈ J.map (cstHom p (f x')) := by
    intro c hc
    refine Submodule.span_induction (p := fun c _ => gs (𝟙 X) (f x') U c ∈ J.map (cstHom p (f x')))
      ?_ ?_ ?_ ?_ hc
    · rintro _ ⟨v, hv, rfl⟩
      rw [← constFn_eq_strMap, gs_constFn_id p U _ hxU]
      exact Ideal.mem_map_of_mem (cstHom p (f x')) hv
    · rw [gs_zero (𝟙 X) (f x') U hxU]; exact zero_mem _
    · intro u v _ _ hu hv
      rw [gs_add (𝟙 X) (f x') U hxU]; exact add_mem hu hv
    · intro u v _ hv
      rw [smul_eq_mul, gs_mul (𝟙 X) (f x') U hxU]; exact Ideal.mul_mem_left _ _ hv
  have e : gs (𝟙 X) (f x') W a = cst p (f x') r * gs (𝟙 X) (f x') U b +
      gs (𝟙 X) (f x') U ((X.presheaf.map (homOfLE hUW).op).hom a - constFn p U r * b) := by
    rw [← gs_res (𝟙 X) (f x') hUW hxU a, ← gs_constFn_id p U _ hxU, ← gs_mul (𝟙 X) (f x') U hxU,
      ← gs_add (𝟙 X) (f x') U hxU, add_sub_cancel]
  show gs (𝟙 X) (f x') W a ∈ Ideal.span {cst p (f x') r} ⊔ J.map (cstHom p (f x'))
  rw [e]
  exact add_mem (Ideal.mem_sup_left (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))
    (Ideal.mem_sup_right (hJ _ hmem))

theorem mem_span_of_forall_pow {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (c s : A) (I : Ideal A)
    (hI : I ≠ ⊤) (h : ∀ e : ℕ, s ∈ Ideal.span {c} ⊔ I ^ (e + 1)) : s ∈ Ideal.span {c} := by
  have hK := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := A ⧸ Ideal.span {c}) I hI
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← Submodule.mem_bot A, ← hK, Submodule.mem_iInf]
  intro i
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 (h i)
  have hv' : v ∈ I ^ i := Ideal.pow_le_pow_right (Nat.le_succ i) hv
  rw [map_add, Ideal.Quotient.eq_zero_iff_mem.2 hu, zero_add]
  have e : Ideal.Quotient.mk (Ideal.span {c}) v = v • (1 : A ⧸ Ideal.span {c}) := by
    rw [Algebra.smul_def, mul_one]; rfl
  rw [e]
  exact Submodule.smul_mem_smul hv' trivial

end General

theorem dvd_on_thick {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (e k : ℕ)
    (σ : H0 U.LG.L k) (f f' : ∀ α, D.toPre.SecB k α) (r : R) (hf : ∀ α, SecIsMul D.toPre.P.A.hom r (f' α) (f α))
    (hE : U.ExpandsAt e k σ f') (y : (thickObj R I e G).left) (jL : U.LG.L.ι) (hy : fGl I G e y ∈ U.LG.L.U jL) :
    cst (fGl I G e ≫ G.hom) y r ∣ sv U k σ (fGl I G e) y jL := by
  obtain ⟨S, hS⟩ := expandsAt_val U e k σ f' hE
  choose J hJ using fun ψ : (thickObj R I e G).left ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (ψ y)
  have hJ' : Good D.toPre.P.L y J := hJ
  have H := (hS _ (𝟙 _) y J hJ').2 jL hy
  simp only [Category.id_comp] at H
  have hc : pGl U e ≫ D.toPre.P.A.hom = fGl I G e ≫ G.hom :=
    (Over.w (U.gt e).pG).trans (Over.w (fstG I e G)).symm
  have hF : ∀ α, sval (f' α) (pGl U e) y J = cst (fGl I G e ≫ G.hom) y r * sval (f α) (pGl U e) y J := fun α => by
    rw [← hc]
    exact secIsMul_gs (hf α) (pGl U e) y _ (hJ'.mem _ _)
  have hd : cst (fGl I G e ≫ G.hom) y r ∣
      (wv U e (𝟙 _) y (J (pGl U e)) jL ^ k).val * sv U k σ (fGl I G e) y jL := by
    rw [H]
    exact Finset.dvd_sum fun α _ => by rw [hF]; exact Dvd.dvd.mul_right (dvd_mul_right _ _) _
  exact (Units.isUnit _).dvd_mul_left.1 hd

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsNoetherianRing R →
    ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    (U : UnifPre (maximalIdeal R) D A G) (k : ℕ) (σ : H0 U.LG.L k) (f f' : ∀ α, D.toPre.SecB k α) (r : R),
    (∀ α, SecIsMul D.toPre.P.A.hom r (f' α) (f α)) → (∀ e, U.ExpandsAt e k σ f') →
    ∀ (j : Fin 1 → U.LG.L.ι) (x : G.left), x ∈ (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))).U j →
    G.hom x = closedPoint R → cst G.hom x r ∣ gs (𝟙 G.left) x _ (σ.f j) := by
  intro R _ _ _ hN D A G _ _ U k σ f f' r hf hE j x hx hxc
  have := U.smooth
  haveI : IsNoetherianRing R := hN
  haveI : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  obtain ⟨jL, rfl⟩ : ∃ jL, j = fun _ => jL := ⟨j 0, funext fun i => congrArg j (Subsingleton.elim i 0)⟩
  have hprime : (G.hom x).asIdeal = maximalIdeal R := by rw [hxc]; rfl
  rw [← Ideal.mem_span_singleton]
  refine mem_span_of_forall_pow _ _ ((maximalIdeal R).map (cstHom G.hom x)) ?_ fun e => ?_
  · intro ht
    have hle : (maximalIdeal R).map (cstHom G.hom x) ≤ maximalIdeal (G.left.presheaf.stalk x) :=
      Ideal.map_le_iff_le_comap.2 fun a ha => (mem_maximalIdeal _).2
        (not_isUnit_cst G.hom x (hprime ▸ ha))
    exact (Ideal.IsPrime.ne_top inferInstance) (top_le_iff.1 (ht ▸ hle))
  · obtain ⟨y, rfl⟩ := exists_fst_eq_of_le G.hom (maximalIdeal R ^ (e + 1)) x
      (hprime ▸ Ideal.pow_le_self (Nat.succ_ne_zero e))
    have hd := dvd_on_thick U e k σ f f' r hf (hE e) y jL (Set.mem_iInter.1 hx 0)
    have hm := germ_mem_of_thick G.hom (maximalIdeal R ^ (e + 1)) (σ.f fun _ => jL) y hx hd
    rwa [Ideal.map_pow] at hm

end GlobalTheory.ClosedDvd
