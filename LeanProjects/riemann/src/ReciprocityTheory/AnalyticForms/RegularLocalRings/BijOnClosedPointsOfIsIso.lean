import ReciprocityTheory.AnalyticForms.RegularLocalRings.StalkLoc
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FromSpecResidueFieldAppTopIso
import ReciprocityTheory.AnalyticForms.RegularLocalRings.SecHomSurjective

namespace ReciprocityTheory.AnForm.R

open AlgebraicGeometry CategoryTheory MvPolynomial

noncomputable section

variable {W X : Scheme.{0}} {sW : W ⟶ Spec (.of ℂ)} {sX : X ⟶ Spec (.of ℂ)}

theorem isClosed_of_isClosed_open [LocallyOfFiniteType sW] (V : W.Opens) (x : V)
    (hx : IsClosed ({x} : Set V)) : IsClosed ({x.1} : Set W) := by
  have : JacobsonSpace W := LocallyOfFiniteType.jacobsonSpace sW
  apply isClosed_singleton_of_isLocallyClosed_singleton
  obtain ⟨t, ht, hteq⟩ := isClosed_induced_iff.mp hx
  refine ⟨(V : Set W), t, V.isOpen, ht, ?_⟩
  ext z
  constructor
  · rintro rfl
    exact ⟨x.2, (Set.ext_iff.mp hteq x).mpr rfl⟩
  · rintro ⟨hzV, hzt⟩
    have e : (⟨z, hzV⟩ : V) = x := (Set.ext_iff.mp hteq ⟨z, hzV⟩).mp hzt
    show z = x.1
    exact congrArg Subtype.val e

theorem bijOn_closedPoints_of_isIso (π : W ⟶ X) (hπ : π ≫ sX = sW) [LocallyOfFiniteType sW]
    [LocallyOfFiniteType sX] (U : X.Opens) [IsIso (π ∣_ U)] :
    Set.BijOn π.base {x | IsClosed ({x} : Set W) ∧ π.base x ∈ U}
      {y | IsClosed ({y} : Set X) ∧ y ∈ U} := by
  let h := Scheme.homeoOfIso (asIso (π ∣_ U))
  have hb : ∀ z, (h z).1 = π.base z.1 := fun z => morphismRestrict_base_coe π U z
  refine ⟨fun x hx => ⟨isClosed_image_of_closed sW sX π hπ x hx.1, hx.2⟩, ?_, ?_⟩
  · intro x₁ hx₁ x₂ hx₂ he
    have e1 : h ⟨x₁, hx₁.2⟩ = h ⟨x₂, hx₂.2⟩ :=
      Subtype.ext ((hb ⟨x₁, hx₁.2⟩).trans (he.trans (hb ⟨x₂, hx₂.2⟩).symm))
    exact congrArg Subtype.val (h.injective e1)
  · intro y hy
    let w := h.symm ⟨y, hy.2⟩
    have hw : h w = ⟨y, hy.2⟩ := h.apply_symm_apply _
    have hcl : IsClosed ({h w} : Set _) := by
      refine isClosed_induced_iff.mpr ⟨{y}, hy.1, Set.ext fun z => ⟨fun hz => ?_, fun hz => ?_⟩⟩
      · exact Subtype.ext (hz.trans (congrArg Subtype.val hw).symm)
      · exact (congrArg Subtype.val hz).trans (congrArg Subtype.val hw)
    have hcw : IsClosed ({w} : Set _) := by
      have := hcl.preimage h.continuous
      rwa [← Set.image_singleton, h.injective.preimage_image] at this
    have hW : JacobsonSpace W := LocallyOfFiniteType.jacobsonSpace sW
    refine ⟨w.1, ⟨?_, w.2⟩, (hb w).symm.trans (congrArg Subtype.val hw)⟩
    apply isClosed_singleton_of_isLocallyClosed_singleton
    obtain ⟨t, ht, hteq⟩ := isClosed_induced_iff.mp hcw
    refine ⟨((π ⁻¹ᵁ U : W.Opens) : Set W), t, (π ⁻¹ᵁ U).isOpen, ht, ?_⟩
    ext z
    constructor
    · rintro rfl
      exact ⟨w.2, (Set.ext_iff.mp hteq w).mpr rfl⟩
    · rintro ⟨hzV, hzt⟩
      have e : (⟨z, hzV⟩ : ((π ⁻¹ᵁ U : W.Opens) : Set W)) = w := (Set.ext_iff.mp hteq ⟨z, hzV⟩).mp hzt
      show z = w.1
      exact congrArg Subtype.val e

theorem exists_coord_inv (π : W ⟶ X) (hπ : π ≫ sX = sW) [LocallyOfFiniteType sW]
    [LocallyOfFiniteType sX] (U : X.Opens) [IsIso (π ∣_ U)] (PW : AffPres sW) (V : X.Opens)
    (hV : IsAffineOpen V) {σ : Type} [Finite σ] (u : σ → Γ(X, V))
    (hu : ∀ t : Γ(X, V), ∃ F : MvPolynomial σ ℂ, t = eval₂ (constSec sX V) u F)
    (x : W) (hxW : x ∈ PW.V) (hxV : π.base x ∈ V) (hxU : π.base x ∈ U)
    (hc : IsClosed ({x} : Set W)) :
    ∃ O : W.Opens, x ∈ O ∧ O ≤ PW.V ⊓ π ⁻¹ᵁ (U ⊓ V) ∧
      ∃ (q : MvPolynomial σ ℂ) (F : Fin PW.n → MvPolynomial σ ℂ),
        eval (fun t => val sX (u t) (π.base x) hxV) q ≠ 0 ∧
        ∀ (y : W) (hyW : y ∈ PW.V) (hyV : π.base y ∈ V), y ∈ O → IsClosed ({y} : Set W) →
          eval (fun t => val sX (u t) (π.base y) hyV) q ≠ 0 ∧
          ∀ l, PW.coord y hyW l * eval (fun t => val sX (u t) (π.base y) hyV) q =
            eval (fun t => val sX (u t) (π.base y) hyV) (F l) := by
  have hiso : IsIso (π.stalkMap x) := by
    let x' : (π ⁻¹ᵁ U : W.Opens) := ⟨x, hxU⟩
    have h1 : IsIso ((π ∣_ U).stalkMap x') := by
      first
      | exact inferInstance
      | exact (IsOpenImmersion.iff_isIso_stalkMap.mp (inferInstance : IsOpenImmersion (π ∣_ U))).2 x'
    have h2 : (MorphismProperty.isomorphisms CommRingCat) ((π ∣_ U).stalkMap x') := h1
    exact (MorphismProperty.isomorphisms CommRingCat).arrow_mk_iso_iff
      (morphismRestrictStalkMap π U x') |>.mp h2
  obtain ⟨O, hxO, hO, q, F, hq, hF⟩ := exists_ratio_core sW sX π hπ V hV u hu PW.V
    (fun l => PW.secHom (MvPolynomial.X l)) x hxW hxV hc (ConcreteCategory.bijective_of_isIso (π.stalkMap x)).2
  refine ⟨O ⊓ π ⁻¹ᵁ U, ⟨hxO, hxU⟩, ?_, q, F, hq, ?_⟩
  · intro y hy
    exact ⟨(hO hy.1).1, hy.2, (hO hy.1).2⟩
  · intro y hyW hyV hyO hcy
    obtain ⟨h1, h2⟩ := hF y hyW hyV hyO.1 hcy
    refine ⟨h1, fun l => ?_⟩
    rw [← h2 l, PW.val_secHom y hyW hcy, eval_X]

theorem exists_coord_fwd (π : W ⟶ X) (hπ : π ≫ sX = sW) [LocallyOfFiniteType sW]
    [LocallyOfFiniteType sX] (PW : AffPres sW) (V : X.Opens) {σ : Type} [Finite σ]
    (u : σ → Γ(X, V)) (x : W) (hxW : x ∈ PW.V) (hxV : π.base x ∈ V)
    (hc : IsClosed ({x} : Set W)) :
    ∃ O : W.Opens, x ∈ O ∧ O ≤ PW.V ⊓ π ⁻¹ᵁ V ∧
      ∃ (q : MvPolynomial (Fin PW.n) ℂ) (F : σ → MvPolynomial (Fin PW.n) ℂ),
        eval (PW.coord x hxW) q ≠ 0 ∧
        ∀ (y : W) (hyW : y ∈ PW.V) (hyV : π.base y ∈ V), y ∈ O → IsClosed ({y} : Set W) →
          eval (PW.coord y hyW) q ≠ 0 ∧
          ∀ t, val sX (u t) (π.base y) hyV * eval (PW.coord y hyW) q =
            eval (PW.coord y hyW) (F t) := by
  have : IsAffine PW.V.toScheme := IsAffine.of_isIso PW.iso.hom
  have hV : IsAffineOpen PW.V := this
  let u' : Fin PW.n → Γ(W, PW.V) := fun j => PW.secHom (MvPolynomial.X j)
  have hu' : ∀ a : Γ(W, PW.V), ∃ F : MvPolynomial (Fin PW.n) ℂ,
      a = eval₂ (constSec sW PW.V) u' F := by
    intro a
    obtain ⟨f, rfl⟩ := PW.secHom_surjective a
    refine ⟨f, ?_⟩
    conv_lhs => rw [← MvPolynomial.eval₂_eta f]
    rw [eval₂_comp_left]
    congr 1
    ext c
    exact PW.secHom_C c
  have hxW' : (𝟙 W : W ⟶ W).base x ∈ PW.V := hxW
  obtain ⟨O, hxO, hO, q, F, hq, hF⟩ := exists_ratio_core sW sW (𝟙 W) (Category.id_comp _) PW.V hV
    u' hu' (PW.V ⊓ π ⁻¹ᵁ V) (fun t => π.appLE V (PW.V ⊓ π ⁻¹ᵁ V) inf_le_right (u t)) x
    ⟨hxW, hxV⟩ hxW' hc (by rw [Scheme.Hom.stalkMap_id]; exact fun z => ⟨z, rfl⟩)
  have hcoord : ∀ (y : W) (hyW : y ∈ PW.V) (h : (𝟙 W : W ⟶ W).base y ∈ PW.V),
      IsClosed ({y} : Set W) → (fun a => val sW (u' a) ((𝟙 W : W ⟶ W).base y) h) = PW.coord y hyW := by
    intro y hyW h hcy
    funext j
    change val sW (PW.secHom (MvPolynomial.X j)) y hyW = _
    rw [PW.val_secHom y hyW hcy, eval_X]
  refine ⟨O, hxO, fun y hy => (hO hy).1, q, F, ?_, ?_⟩
  · rw [← hcoord x hxW hxW' hc]
    exact hq
  · intro y hyW hyV hyO hcy
    have hyW' : (𝟙 W : W ⟶ W).base y ∈ PW.V := hyW
    obtain ⟨h1, h2⟩ := hF y ⟨hyW, hyV⟩ hyW' hyO hcy
    rw [hcoord y hyW hyW' hcy] at h1 h2
    refine ⟨h1, fun t => ?_⟩
    rw [← h2 t, (val_comp sW sX π hπ inf_le_right (u t) y ⟨hyW, hyV⟩ hcy).2]

end

end ReciprocityTheory.AnForm.R
