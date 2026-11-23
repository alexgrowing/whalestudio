import ReciprocityTheory.AnalyticForms.RegularLocalRings.StalkLoc
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FromSpecResidueFieldAppTopIso

namespace ReciprocityTheory.AnForm.R

open AlgebraicGeometry CategoryTheory MvPolynomial

noncomputable section

variable {W : Scheme.{0}} {sW : W ⟶ Spec (.of ℂ)}

theorem val_eval₂ {S : Scheme.{0}} (s : S ⟶ Spec (.of ℂ)) [LocallyOfFiniteType s] {U : S.Opens}
    {σ : Type} (u : σ → Γ(S, U)) (F : MvPolynomial σ ℂ) (x : S) (hx : x ∈ U)
    (hc : IsClosed ({x} : Set S)) :
    val s (eval₂ (constSec s U) u F) x hx = eval (fun t => val s (u t) x hx) F := by
  obtain ⟨φ, hφ⟩ := val_ringHom s U x hx hc
  rw [← hφ, eval₂_comp_left]
  have h1 : φ.comp (constSec s U) = RingHom.id ℂ := by
    ext c
    simp only [RingHom.comp_apply, hφ, RingHom.id_apply]
    exact val_const s U x hx hc c
  rw [h1]
  change eval₂ (RingHom.id ℂ) (φ ∘ u) F = eval₂ (RingHom.id ℂ) _ F
  congr 1
  funext t
  exact hφ (u t)

namespace AffPres

set_option backward.isDefEq.respectTransparency false in

theorem secHom_C (P : AffPres sW) (c : ℂ) : P.secHom (C c) = constSec sW P.V c := by
  have key : (Scheme.ΓSpecIso (.of ℂ)).inv ≫
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin P.n) ℂ ⧸ P.K)))).appTop ≫
      P.iso.hom.appTop ≫ P.V.topIso.hom =
      (Scheme.ΓSpecIso (.of ℂ)).inv ≫ sW.appLE ⊤ P.V le_top := by
    rw [← Scheme.Hom.comp_appTop_assoc, P.hover, Scheme.Hom.comp_appTop, Category.assoc]
    simp only [Scheme.Hom.appTop, Scheme.Hom.appLE, Scheme.Opens.ι_appTop,
      Scheme.Opens.topIso_hom, ← W.presheaf.map_comp]
    rfl
  have e3 : P.secHom (C c) = ((CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin P.n) ℂ ⧸ P.K))) ≫
      (Scheme.ΓSpecIso (.of (MvPolynomial (Fin P.n) ℂ ⧸ P.K))).inv ≫
      P.iso.hom.appTop ≫ P.V.topIso.hom) c := rfl
  rw [e3, Scheme.ΓSpecIso_inv_naturality_assoc, key]
  rfl

theorem secHom_surjective (P : AffPres sW) : Function.Surjective P.secHom := by
  intro a
  have h1 : Function.Surjective P.V.topIso.hom.hom :=
    (ConcreteCategory.bijective_of_isIso P.V.topIso.hom).2
  have h2 : Function.Surjective (P.iso.hom.app ⊤).hom :=
    (ConcreteCategory.bijective_of_isIso (P.iso.hom.app ⊤)).2
  have h3 : Function.Surjective (Scheme.ΓSpecIso (.of (MvPolynomial (Fin P.n) ℂ ⧸ P.K))).inv.hom :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso _).inv).2
  obtain ⟨a1, rfl⟩ := h1 a
  obtain ⟨a2, rfl⟩ := h2 a1
  obtain ⟨a3, rfl⟩ := h3 a2
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a3
  exact ⟨f, rfl⟩

theorem val_secHom [LocallyOfFiniteType sW] (P : AffPres sW) (y : W) (hy : y ∈ P.V)
    (hc : IsClosed ({y} : Set W)) (f : MvPolynomial (Fin P.n) ℂ) :
    val sW (P.secHom f) y hy = eval (P.coord y hy) f := by
  obtain ⟨φ, hφ⟩ := val_ringHom sW P.V y hy hc
  have hker : ∀ g ∈ ptIdeal (P.coord y hy), val sW (P.secHom g) y hy = 0 := by
    intro g hg
    rw [val_eq_zero_iff sW _ y hy hc, ← Scheme.germ_residue, CommRingCat.comp_apply]
    apply (IsLocalRing.residue_eq_zero_iff _).mpr
    have h2 : P.stalkEquiv y hy hc (W.presheaf.germ P.V y hy (P.secHom g)) ∈
        (IsLocalRing.maximalIdeal (W.presheaf.stalk y)).map (P.stalkEquiv y hy hc) := by
      rw [P.map_maximalIdeal_stalk y hy hc, P.stalkEquiv_germ]
      exact Ideal.mem_map_of_mem _ hg
    obtain ⟨w, hw, hwe⟩ := (Ideal.mem_map_of_equiv _ _).mp h2
    rw [(P.stalkEquiv y hy hc).injective hwe] at hw
    exact hw
  let ψ : MvPolynomial (Fin P.n) ℂ →+* ℂ := φ.comp P.secHom
  have hψ : ∀ g, ψ g = val sW (P.secHom g) y hy := fun g => hφ _
  have hC : ∀ c, ψ (C c) = c := fun c => by
    rw [hψ, secHom_C, val_const sW P.V y hy hc]
  have hX : ∀ j, ψ (MvPolynomial.X j) = P.coord y hy j := fun j => by
    have hm : X j - C (P.coord y hy j) ∈ ptIdeal (P.coord y hy) := by
      simp [ptIdeal, RingHom.mem_ker]
    have := hker _ hm
    rw [← hψ, map_sub, hC, sub_eq_zero] at this
    exact this
  have hext : ψ = MvPolynomial.eval (P.coord y hy) := by
    apply MvPolynomial.ringHom_ext
    · intro c; rw [hC, eval_C]
    · intro j; rw [hX, eval_X]
  rw [← hψ, hext]

end AffPres

theorem exists_ratio_core {S T : Scheme.{0}} (s : S ⟶ Spec (.of ℂ)) (t : T ⟶ Spec (.of ℂ))
    (g : S ⟶ T) (hg : g ≫ t = s) [LocallyOfFiniteType s] [LocallyOfFiniteType t]
    (V : T.Opens) (hV : IsAffineOpen V) {σ : Type} (u : σ → Γ(T, V))
    (hu : ∀ a : Γ(T, V), ∃ F : MvPolynomial σ ℂ, a = eval₂ (constSec t V) u F)
    {ι : Type} [Finite ι] (Ω : S.Opens) (e : ι → Γ(S, Ω)) (x : S) (hxΩ : x ∈ Ω)
    (hxV : g.base x ∈ V) (hc : IsClosed ({x} : Set S))
    (hsurj : Function.Surjective (g.stalkMap x)) :
    ∃ O : S.Opens, x ∈ O ∧ O ≤ Ω ⊓ g ⁻¹ᵁ V ∧
      ∃ (q : MvPolynomial σ ℂ) (F : ι → MvPolynomial σ ℂ),
        eval (fun a => val t (u a) (g.base x) hxV) q ≠ 0 ∧
        ∀ (y : S) (hyΩ : y ∈ Ω) (hyV : g.base y ∈ V), y ∈ O → IsClosed ({y} : Set S) →
          eval (fun a => val t (u a) (g.base y) hyV) q ≠ 0 ∧
          ∀ i, val s (e i) y hyΩ * eval (fun a => val t (u a) (g.base y) hyV) q =
            eval (fun a => val t (u a) (g.base y) hyV) (F i) := by
  classical
  cases nonempty_fintype ι
  let z : V := ⟨g.base x, hxV⟩
  let : Algebra Γ(T, V) (T.presheaf.stalk (g.base x)) :=
    TopCat.Presheaf.algebra_section_stalk T.presheaf z
  have : IsLocalization.AtPrime (T.presheaf.stalk (g.base x)) (hV.primeIdealOf z).asIdeal :=
    hV.isLocalization_stalk z
  have hw : ∀ i, ∃ w : T.presheaf.stalk (g.base x),
      g.stalkMap x w = S.presheaf.germ Ω x hxΩ (e i) := fun i => hsurj _
  choose w hw using hw
  obtain ⟨⟨b, hb⟩, hint⟩ :=
    IsLocalization.exist_integer_multiples_of_finite (hV.primeIdealOf z).asIdeal.primeCompl w
  have hint' : ∀ i, ∃ a : Γ(T, V), algebraMap Γ(T, V) (T.presheaf.stalk (g.base x)) a = b • w i :=
    fun i => hint i
  choose a ha using hint'
  have halg : ∀ c : Γ(T, V), algebraMap Γ(T, V) (T.presheaf.stalk (g.base x)) c =
      T.presheaf.germ V (g.base x) hxV c := fun c => rfl
  have hunit : IsUnit (T.presheaf.germ V (g.base x) hxV b) := by
    rw [← halg]
    exact IsLocalization.map_units (T.presheaf.stalk (g.base x))
      (⟨b, hb⟩ : (hV.primeIdealOf z).asIdeal.primeCompl)
  let Ω' : S.Opens := Ω ⊓ g ⁻¹ᵁ V
  have hΩ'V : Ω' ≤ g ⁻¹ᵁ V := inf_le_right
  have hΩ'Ω : Ω' ≤ Ω := inf_le_left
  have hxΩ' : x ∈ Ω' := ⟨hxΩ, hxV⟩
  have hgerm : ∀ c : Γ(T, V), S.presheaf.germ Ω' x hxΩ' (g.appLE V Ω' hΩ'V c) =
      g.stalkMap x (T.presheaf.germ V (g.base x) hxV c) := by
    intro c
    rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.appLE, CommRingCat.comp_apply,
      TopCat.Presheaf.germ_res_apply]
  have hEq : ∀ i, S.presheaf.germ Ω' x hxΩ'
      (g.appLE V Ω' hΩ'V b * S.presheaf.map (homOfLE hΩ'Ω).op (e i)) =
      S.presheaf.germ Ω' x hxΩ' (g.appLE V Ω' hΩ'V (a i)) := by
    intro i
    rw [map_mul, hgerm, hgerm, TopCat.Presheaf.germ_res_apply, ← hw i, ← map_mul]
    congr 1
    rw [← halg, ← halg, ha i, Algebra.smul_def]
  have hO := fun i => TopCat.Presheaf.germ_eq S.presheaf x hxΩ' hxΩ' _ _ (hEq i)
  choose Oi hxOi iU iV hOi using hO
  obtain ⟨q, hq⟩ := hu b
  choose F hF using fun i => hu (a i)
  let O : S.Opens := (g ⁻¹ᵁ T.basicOpen b) ⊓ Ω' ⊓ Finset.univ.inf Oi
  have hmemO : ∀ y, y ∈ O → y ∈ g ⁻¹ᵁ T.basicOpen b ∧ y ∈ Ω' ∧ ∀ i, y ∈ Oi i := by
    intro y hy
    refine ⟨hy.1.1, hy.1.2, fun i => ?_⟩
    have h2 := hy.2
    rw [TopologicalSpace.Opens.coe_finset_inf, Finset.inf_eq_iInf] at h2
    simp only [Set.iInf_eq_iInter, Set.mem_iInter] at h2
    exact h2 i (Finset.mem_univ i)

  have hne : ∀ (y : S) (hyV : g.base y ∈ V), IsClosed ({y} : Set S) →
      g.base y ∈ T.basicOpen b → eval (fun a => val t (u a) (g.base y) hyV) q ≠ 0 := by
    intro y hyV hcy hyb
    have hcy' := isClosed_image_of_closed s t g hg y hcy
    rw [← val_eval₂ t u q _ hyV hcy', ← hq]
    intro h0
    rw [val_eq_zero_iff t b _ hyV hcy', ← Scheme.germ_residue, CommRingCat.comp_apply] at h0
    have hu' := (T.mem_basicOpen b (g.base y) hyV).mp hyb
    exact (hu'.map (T.residue (g.base y)).hom).ne_zero h0
  refine ⟨O, ?_, fun y hy => (hmemO y hy).2.1, q, F, ?_, ?_⟩
  · refine ⟨⟨?_, hxΩ'⟩, ?_⟩
    · exact (T.mem_basicOpen b (g.base x) hxV).mpr hunit
    · show x ∈ ((Finset.univ.inf Oi : S.Opens) : Set S)
      rw [TopologicalSpace.Opens.coe_finset_inf, Finset.inf_eq_iInf]
      simp only [Set.iInf_eq_iInter, Set.mem_iInter]
      exact fun i _ => hxOi i
  · exact hne x hxV hc ((T.mem_basicOpen b (g.base x) hxV).mpr hunit)
  · intro y hyΩ hyV hyO hcy
    obtain ⟨hyb, hyΩ', hyOi⟩ := hmemO y hyO
    have hcy' := isClosed_image_of_closed s t g hg y hcy
    refine ⟨hne y hyV hcy hyb, fun i => ?_⟩
    obtain ⟨φ, hφ⟩ := val_ringHom s Ω' y hyΩ' hcy
    have h1 := congrArg (fun f => val s f y (hyOi i)) (hOi i)
    simp only at h1
    rw [show iU i = homOfLE (leOfHom (iU i)) from rfl, show iV i = homOfLE (leOfHom (iV i)) from rfl,
      val_restrict, val_restrict, ← hφ, map_mul, hφ, hφ, val_restrict] at h1
    rw [(val_comp s t g hg hΩ'V b y hyΩ' hcy).2, (val_comp s t g hg hΩ'V (a i) y hyΩ' hcy).2] at h1
    have e1 : val t b (g.base y) (hΩ'V hyΩ') = eval (fun a => val t (u a) (g.base y) hyV) q := by
      rw [hq]; exact val_eval₂ t u q _ hyV hcy'
    have e2 : val t (a i) (g.base y) (hΩ'V hyΩ') =
        eval (fun a => val t (u a) (g.base y) hyV) (F i) := by
      rw [hF i]; exact val_eval₂ t u (F i) _ hyV hcy'
    rw [e1, e2] at h1
    rw [mul_comm]
    exact h1

end

end ReciprocityTheory.AnForm.R
