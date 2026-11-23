import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonal
import Formalism.LocalToGlobal.ProjectiveLattices.UnifGen
import Formalism.LocalToGlobal.ProjectiveLattices.UnifDom

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open MeasureTheory
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Fam

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

theorem domStab_holds {g : ℕ} {ty : Fin g → (E →+* ℂ)} {σ' : KA l →+* ℂ} {F : FamilyUnif Xo σ' ty}
    (M : ModelsOf F r) : ∀ k, ∀ x ∈ (M.X k).dom, (∀ b ∈ Bor (M.X k).Ψ r, rmul x b ∈ (M.X k).dom) ∧
      ∀ γ ∈ (M.X k).Γ, lact γ x ∈ (M.X k).dom :=
  fun k _ hx => ⟨fun _ hb => dom_rmul _ hx hb, fun _ hγ => dom_lact _ hx ((M.X k).Γ_stab _ hγ)⟩

def CoverTri {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (M : ModelsOf F r) : Prop :=
  ∀ y : FrPt Xo c (CAt σ), ∃ k, ∃ x : (M.X k).dom, ∃ Pm : (F.Di k).La →+ (Fin g → ℂ),
    (∀ a j, Pm a j = perFr (M.X k) x.1 (M.φ k a : Fin r → E) (relab c σ (e j).1) (e j).2) ∧
    F.u k Pm = y.x ∧
    ∀ v : ∀ τ, Fin (Dw.mult τ) → (Sp (DualNumber (CAt σ)) ⟶ Xo.univ.t.G.left),
      (∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex k Pm z).left) (Pi.single (e.symm ⟨τ, i⟩) 1) (v τ i)) →
      ∀ τ (i : Fin (Dw.mult τ)), ∃ cf : Fin (Dw.mult τ) → CAt σ, IsUnit (cf i) ∧ (∀ j, i < j → cf j = 0) ∧
        IsCombAt y.x (v τ) cf (y.u τ i)

theorem coverU_of_coverTri {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (M : ModelsOf F r) (un : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ)) (hun : ∀ k x, FrameOK e F M k x (un k x))
    (hT : CoverTri e F M) : CoverU (unfOf e F M un) := by
  intro y
  obtain ⟨k, x, Pm, hPm, hxy, hv⟩ := hT y
  obtain ⟨Pm', hPm', -, hx', hd', -⟩ := hun k x
  have hP : Pm' = Pm := by
    ext a j
    rw [hPm', hPm]
  subst hP
  refine ⟨k, x, ?_⟩
  have hxx : y.x = (un k x).x := hxy.symm.trans hx'.symm
  refine frBor_of_tri (un k x) y hxx fun τ i => ?_
  obtain ⟨cf, h1, h2, h3⟩ := hv (un k x).u hd' τ i
  exact ⟨cf, h1, h2, by rw [← hxx]; exact h3⟩

def FibTri {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (M : ModelsOf F r) : Prop :=
  ∀ k k' (x : (M.X k).dom) (x' : (M.X k').dom) (Pm : (F.Di k).La →+ (Fin g → ℂ))
    (Pm' : (F.Di k').La →+ (Fin g → ℂ))
    (v v' : ∀ τ, Fin (Dw.mult τ) → (Sp (DualNumber (CAt σ)) ⟶ Xo.univ.t.G.left)),
    (∀ a j, Pm a j = perFr (M.X k) x.1 (M.φ k a : Fin r → E) (relab c σ (e j).1) (e j).2) →
    (∀ a j, Pm' a j = perFr (M.X k') x'.1 (M.φ k' a : Fin r → E) (relab c σ (e j).1) (e j).2) →
    F.u k Pm = F.u k' Pm' →
    (∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex k Pm z).left) (Pi.single (e.symm ⟨τ, i⟩) 1) (v τ i)) →
    (∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex k' Pm' z).left) (Pi.single (e.symm ⟨τ, i⟩) 1)
      (v' τ i)) →
    (∀ τ (i : Fin (Dw.mult τ)), ∃ cf : Fin (Dw.mult τ) → CAt σ, IsUnit (cf i) ∧ (∀ j, i < j → cf j = 0) ∧
      IsCombAt (F.u k Pm) (v τ) cf (v' τ i)) →
    ∃ γ ∈ (M.X k).Γ, ∃ b ∈ Bor (M.X k).Ψ r, (⟨k', x'.1⟩ : Σ k, Frame (M.X k).Ψ r) = ⟨k, rmul (lact γ x.1) b⟩

theorem fibreU_of {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (M : ModelsOf F r) (un : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ)) (hun : FramesOK e F M un)
    (hT : TanLin Xo) (hB : FibTri e F M) : FibreU (unfOf e F M un) := by
  intro k k' x x'
  constructor
  · rintro ⟨t, hx, hu, -⟩
    obtain ⟨Pm, hPm, -, hxP, hd, -⟩ := hun.1 k x
    obtain ⟨Pm', hPm', -, hxP', hd', -⟩ := hun.1 k' x'
    refine hB k k' x x' Pm Pm' (un k x).u (un k' x').u hPm hPm' (hxP.symm.trans (hx.symm.trans hxP')) hd hd'
      fun τ i => ?_
    obtain ⟨cf, hcf, htri, hcomb⟩ := hu τ i
    refine ⟨cf, by rw [hcf]; exact Units.isUnit _, htri, ?_⟩
    have e1 : (unfOf e F M un).un k x = un k x := rfl
    rw [e1, hxP] at hcomb
    exact hcomb
  · rintro ⟨γ, hγ, b, hb, heq⟩
    obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.1 heq
    have h3 : x'.1 = rmul (lact γ x.1) b := eq_of_heq h2
    have hxg : lact γ x.1 ∈ (M.X k').dom := (domStab_holds M k' x.1 x.2).2 γ hγ
    obtain ⟨t1, ht1, -⟩ := hun.2.2.1 k' γ hγ x hxg
    have hxb : rmul (⟨lact γ x.1, hxg⟩ : (M.X k').dom).1 b ∈ (M.X k').dom := by
      have hx2 := x'.2
      rw [h3] at hx2
      exact hx2
    obtain ⟨t2, ht2, -⟩ := hun.2.1 k' ⟨lact γ x.1, hxg⟩ b hb hxb
    have hx' : (⟨rmul (lact γ x.1) b, hxb⟩ : (M.X k').dom) = x' := Subtype.ext h3.symm
    rw [hx'] at ht2
    exact frBor_trans hT ht1 ht2

end Fam

section Genus

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
  {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

def ClassOcc (U : Unf Xo c σ r) (V : HSp D) (hr : V.rank = r)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) {g : ℕ} (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ) : Prop :=
  ∀ h : GA D V, ∃ k, ∃ γ ∈ GQ V,
      ((U.X k).Λ : Set (Fin r → D.host.E)) =
        (fun v : Fin V.rank → D.host.E => v ∘ Fin.cast hr.symm) '' (latG V (γ * h) : Set _) ∧
      (∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
        ∃ w ∈ latGHat V (γ * h),
        finVec V ((φ k (F.t (ik k) a) : Fin r → D.host.E) ∘ Fin.cast hr) -
          (finHom V (γ * h)).1.mulVec (finVec V (ι a)) = (l.M : ℕ) • w)

end Genus

section Rows

variable {D : D7}

theorem coverU_J {hN : N1c} {Q : Par D} {hpq : ∀ j, 1 ≤ (Q.Dw j).p + (Q.Dw j).q} {j : ℕ} {hj : InR D j}
    {σ : Q.c.F →+* ℂ} {hσ : GoodEmb Q.c σ} {hR : RelabType Q.c σ (Q.Dw j)} {hM : ModelEx hN Q hpq j hj σ hσ hR}
    (hF : FrameEx hM) (hT : CoverTri (letE (Q.Dw j)) (famJ hN Q hpq j σ hσ hR) (modelsJ hM)) :
    CoverU (unfJ hF) :=
  coverU_of_coverTri _ _ _ hF.choose hF.choose_spec.1 hT

theorem fibreU_J {hN : N1c} {Q : Par D} {hpq : ∀ j, 1 ≤ (Q.Dw j).p + (Q.Dw j).q} {j : ℕ} {hj : InR D j}
    {σ : Q.c.F →+* ℂ} {hσ : GoodEmb Q.c σ} {hR : RelabType Q.c σ (Q.Dw j)} {hM : ModelEx hN Q hpq j hj σ hσ hR}
    (hF : FrameEx hM) (hT : TanLin (Q.Xo j)) (hB : FibTri (letE (Q.Dw j)) (famJ hN Q hpq j σ hσ hR) (modelsJ hM)) :
    FibreU (unfJ hF) :=
  fibreU_of _ _ _ hF.choose hF.choose_spec hT hB

end Rows

end Formalism.L2.Pj
