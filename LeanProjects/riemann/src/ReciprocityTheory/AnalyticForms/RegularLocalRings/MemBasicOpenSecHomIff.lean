import ReciprocityTheory.AnalyticForms.RegularLocalRings.StalkLoc
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FromSpecResidueFieldAppTopIso

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace ReciprocityTheory.AnForm.R

noncomputable section

variable {W : Scheme.{0}} {s : W ⟶ Spec (.of ℂ)}

namespace AffPres

variable (P : AffPres s)

theorem mem_basicOpen_secHom_iff (x : W) (hx : x ∈ P.V) (f : MvPolynomial (Fin P.n) ℂ) :
    x ∈ W.basicOpen (P.secHom f) ↔ f ∉ P.ptOf x hx := by
  set g := (Scheme.ΓSpecIso (.of (MvPolynomial (Fin P.n) ℂ ⧸ P.K))).inv
    (Ideal.Quotient.mk P.K f) with hg
  have h1 : x ∈ W.basicOpen (P.secHom f) ↔
      (⟨x, hx⟩ : P.V.toScheme) ∈ P.V.toScheme.basicOpen (P.iso.hom.app ⊤ g) := by
    rw [Scheme.Opens.mem_basicOpen_toScheme]
    have e : P.secHom f = W.presheaf.map (eqToHom P.V.ι_image_top.symm).op (P.iso.hom.app ⊤ g) := rfl
    have e' := Scheme.basicOpen_res W (i := (eqToHom P.V.ι_image_top.symm).op)
      (f := (P.iso.hom.app ⊤ g : Γ(W, P.V.ι ''ᵁ ⊤)))
    rw [e]
    refine (Iff.of_eq (congrArg (fun O => x ∈ O) e')).trans ?_
    rw [TopologicalSpace.Opens.mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩
  have e2 := Scheme.preimage_basicOpen P.iso.hom g
  refine h1.trans (Iff.trans (Iff.of_eq (congrArg (fun O => (⟨x, hx⟩ : P.V.toScheme) ∈ O) e2.symm)) ?_)
  show P.iso.hom.base ⟨x, hx⟩ ∈ (Spec _).basicOpen g ↔ _
  have e4 := AlgebraicGeometry.basicOpen_eq_of_affine
    (R := .of (MvPolynomial (Fin P.n) ℂ ⧸ P.K)) (Ideal.Quotient.mk P.K f)
  rw [hg, e4]
  exact Iff.rfl

theorem secHom_C' (c : ℂ) : P.secHom (C c) = constSec s P.V c := by
  have e1 : P.secHom (C c) = P.V.topIso.hom (P.iso.hom.appTop
      ((Scheme.ΓSpecIso (.of (MvPolynomial (Fin P.n) ℂ ⧸ P.K))).inv (Ideal.Quotient.mk P.K (C c)))) := rfl
  have e2 : (Scheme.ΓSpecIso (.of (MvPolynomial (Fin P.n) ℂ ⧸ P.K))).inv (Ideal.Quotient.mk P.K (C c)) =
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin P.n) ℂ ⧸ P.K)))).appTop
        ((Scheme.ΓSpecIso (.of ℂ)).inv c) := by
    rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]
    rfl
  have e3 : P.iso.hom.appTop ((Spec.map (CommRingCat.ofHom
      (algebraMap ℂ (MvPolynomial (Fin P.n) ℂ ⧸ P.K)))).appTop ((Scheme.ΓSpecIso (.of ℂ)).inv c)) =
      (P.V.ι ≫ s).appTop ((Scheme.ΓSpecIso (.of ℂ)).inv c) := by
    rw [← P.hover]
    rfl
  have key : (Scheme.ΓSpecIso (.of ℂ)).inv ≫ s.appTop ≫
      W.presheaf.map (homOfLE (le_top : P.V.ι ''ᵁ ⊤ ≤ ⊤)).op ≫
        W.presheaf.map (eqToHom P.V.ι_image_top.symm).op =
      (Scheme.ΓSpecIso (.of ℂ)).inv ≫ s.appLE ⊤ P.V le_top := by
    rw [← Functor.map_comp]
    rfl
  rw [e1, e2, e3]
  exact congrArg (fun φ => φ.hom c) key

theorem eval_coord_eq_val [LocallyOfFiniteType s] (x : W) (hx : x ∈ P.V)
    (hc : IsClosed ({x} : Set W)) (f : MvPolynomial (Fin P.n) ℂ) :
    eval (P.coord x hx) f = val s (P.secHom f) x hx := by
  obtain ⟨φ, hφ⟩ := val_ringHom s P.V x hx hc
  set ψ := φ.comp P.secHom with hψdef
  have hC : ∀ c, ψ (C c) = c := by
    intro c
    rw [hψdef, RingHom.comp_apply, hφ, secHom_C', val_const s _ x hx hc]
  have hker : ∀ g, ψ g = 0 → g ∈ P.ptOf x hx := by
    intro g h
    by_contra hg
    rw [← mem_basicOpen_secHom_iff] at hg
    rw [hψdef, RingHom.comp_apply, hφ, val_eq_zero_iff s _ x hx hc,
      Scheme.evaluation_eq_zero_iff_notMem_basicOpen] at h
    exact h hg
  have hpr : P.ptOf x hx ≠ ⊤ :=
    Ideal.comap_ne_top _ (P.iso.hom.base ⟨x, hx⟩).isPrime.ne_top
  have hX : ∀ j, ψ (X j) = P.coord x hx j := by
    intro j
    have h1 : X j - C (ψ (X j)) ∈ P.ptOf x hx := hker _ (by rw [map_sub, hC, sub_self])
    have h2 : X j - C (P.coord x hx j) ∈ P.ptOf x hx :=
      Classical.epsilon_spec (p := fun c : ℂ => X j - C c ∈ P.ptOf x hx) ⟨_, h1⟩
    have h3 : C (ψ (X j) - P.coord x hx j) ∈ P.ptOf x hx := by
      have := sub_mem h2 h1
      rwa [sub_sub_sub_cancel_left, ← map_sub] at this
    by_contra hne
    have hu : IsUnit (C (ψ (X j) - P.coord x hx j) : MvPolynomial (Fin P.n) ℂ) :=
      (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hne)).map C
    exact hpr (Ideal.eq_top_of_isUnit_mem _ h3 hu)
  have hψ : ψ = eval (P.coord x hx) := by
    apply MvPolynomial.ringHom_ext
    · intro c; rw [hC, eval_C]
    · intro j; rw [hX, eval_X]
  rw [← hφ]
  exact (RingHom.congr_fun hψ f).symm

end AffPres

end

end ReciprocityTheory.AnForm.R
