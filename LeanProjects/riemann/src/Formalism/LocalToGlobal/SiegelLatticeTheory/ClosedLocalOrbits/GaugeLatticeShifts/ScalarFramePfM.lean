import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePf

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ScalarFramePf

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section GenericX

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V)

theorem identResp_generic {r : ℕ} (abelian₂ : Submodule M.L.O V) (f₀ f₁ f₂ : Fin (r + 1) → V) (T T' : F)
    (e : V ≃ₗ[E] V) (hiso : ∀ v w, H.h (e v) (e w) = H.h v w)
    (h12 : ∀ x ∈ H.X f₁, e x ∈ H.X f₂) (h21 : ∀ y ∈ H.X f₂, e.symm y ∈ H.X f₁)
    (hX0 : ∀ a ∈ H.X f₀, ∀ b ∈ H.X f₀, H.h a b = 0) (hX2 : ∀ a ∈ H.X f₂, ∀ b ∈ H.X f₂, H.h a b = 0)
    (hL : ∀ x ∈ abelian₂, e x ∈ abelian₂) (hL' : ∀ x ∈ abelian₂, e.symm x ∈ abelian₂)
    (hW0 : ∀ w ∈ H.W0 f₀ f₁, ∃ w₂ ∈ H.W0 f₀ f₂, w - w₂ ∈ H.X f₀ ∧ e w - w₂ ∈ H.X f₂)
    (homp : H.Dl f₀ f₂ (r + 1) • H.om' f₀ f₁ - H.Dl f₀ f₁ (r + 1) • H.om' f₀ f₂ ∈ H.X f₀)
    (hom : M.L.cj (H.Dl f₀ f₂ (r + 1)) • e (H.om f₀ f₁) - M.L.cj (H.Dl f₀ f₁ (r + 1)) • H.om f₀ f₂ ∈ H.X f₂)
    (hrat : H.Dl f₀ f₁ r * H.Dl f₀ f₂ (r + 1) = H.Dl f₀ f₂ r * H.Dl f₀ f₁ (r + 1))
    (hz : e (f₁ (Fin.last r)) - f₂ (Fin.last r) ∈ H.X f₂)
    (hI : ∀ g, M.split = some g → IotaG H (algebraMap F E (g.q : F)) abelian₂ f₀ f₁ f₂ e) :
    H.Ident (⟨abelian₂, f₀, f₁, T, T'⟩ : Loc.Term V M r) ⟨abelian₂, f₀, f₂, T, T'⟩ (LinearEquiv.refl _ _)
        (qEquiv H e hiso (H.X f₁) (H.X f₂) h12 h21) ∧
      H.Respects (⟨abelian₂, f₀, f₁, T, T'⟩ : Loc.Term V M r) ⟨abelian₂, f₀, f₂, T, T'⟩ (LinearEquiv.refl _ _)
        (qEquiv H e hiso (H.X f₁) (H.X f₂) h12 h21) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, hrat⟩, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro x y x₂ y₂ hx hy
    exact h_eq_of_sub_mem H _ hX0 x.2 y.2 ((mk_eq_iff H _ x x₂).1 hx) ((mk_eq_iff H _ y y₂).1 hy)
  · intro x y x₂ y₂ hx hy
    have hx' : e x - x₂ ∈ H.X f₂ := (mk_eq_iff H _ _ x₂).1 hx
    have hy' : e y - y₂ ∈ H.X f₂ := (mk_eq_iff H _ _ y₂).1 hy
    rw [h_eq_of_sub_mem H _ hX2 (perp_map H e hiso _ _ h21 x.2) (perp_map H e hiso _ _ h21 y.2) hx' hy',
      hiso]
  · intro w hw
    obtain ⟨w₂, hw₂, h1, h2⟩ := hW0 w hw
    refine ⟨w₂, hw₂, ?_, ?_⟩
    · intro x x₂ hx hx₂
      apply smul_mk_eq H
      rw [one_smul, one_smul, hx, hx₂]
      exact h1
    · intro x x₂ hx hx₂
      apply smul_mk_eq H
      show (1 : E) • e x - (1 : E) • (x₂ : V) ∈ H.X f₂
      rw [one_smul, one_smul, hx, hx₂]
      exact h2
  · intro x x₂ hx hx₂
    apply smul_mk_eq H
    rw [hx, hx₂]
    exact homp
  · intro x x₂ hx hx₂
    apply smul_mk_eq H
    show M.L.cj (H.Dl f₀ f₂ (r + 1)) • e x - M.L.cj (H.Dl f₀ f₁ (r + 1)) • (x₂ : V) ∈ H.X f₂
    rw [hx, hx₂]
    exact hom
  · ext w
    simp
  · intro x x₂ hx hx₂
    have : x = x₂ := Subtype.ext (hx.trans hx₂.symm)
    rw [this]
    rfl
  · ext w
    constructor
    · rintro ⟨_, ⟨x, hxΛ, rfl⟩, rfl⟩
      exact ⟨perpEquiv H e hiso _ _ h12 h21 x, hL _ hxΛ, rfl⟩
    · rintro ⟨x₂, hx₂Λ, rfl⟩
      refine ⟨H.mkW _ ⟨e.symm x₂, perp_map_symm H e hiso _ _ h12 x₂.2⟩,
        ⟨⟨e.symm x₂, perp_map_symm H e hiso _ _ h12 x₂.2⟩, hL' _ hx₂Λ, rfl⟩, ?_⟩
      show qEquiv H e hiso (H.X f₁) (H.X f₂) h12 h21 (Submodule.Quotient.mk _) = Submodule.Quotient.mk x₂
      rw [qEquiv_mk]
      congr 1
      exact Subtype.ext (e.apply_symm_apply x₂)
  · intro x x₂ hx hx₂
    apply smul_mk_eq H
    show (1 : E) • e x - (1 : E) • (x₂ : V) ∈ H.X f₂
    rw [one_smul, one_smul, hx, hx₂]
    exact hz
  · intro g hg
    obtain ⟨hA, hB⟩ := hI g hg
    ext ⟨a, b⟩
    constructor
    · rintro ⟨⟨a0, b0⟩, ⟨x', x, hx'Λ, hxΛ, hq, heq⟩, hmap⟩
      obtain ⟨y, y'', hyΛ, hy''Λ, hyp, hy''p, hxy, hxy'', hyq⟩ := hA x x' hxΛ hx'Λ x.2 x'.2 hq
      refine ⟨⟨y'', hy''p⟩, ⟨y, hyp⟩, hy''Λ, hyΛ, hyq, ?_⟩
      simp only [Prod.map, Prod.mk.injEq] at hmap heq
      obtain ⟨rfl, rfl⟩ := heq
      obtain ⟨rfl, rfl⟩ := hmap
      refine Prod.ext ?_ ?_
      · show qEquiv H e hiso (H.X f₁) (H.X f₂) h12 h21 (Submodule.Quotient.mk x') = Submodule.Quotient.mk _
        rw [qEquiv_mk, mk_eq_iff]
        exact hxy''
      · show Submodule.Quotient.mk x = Submodule.Quotient.mk _
        rw [mk_eq_iff]
        exact hxy
    · rintro ⟨x'', x, hx''Λ, hxΛ, hq, heq⟩
      obtain ⟨y, y', hyΛ, hy'Λ, hyp, hy'p, hxy, hxy', hyq⟩ := hB x x'' hxΛ hx''Λ x.2 x''.2 hq
      refine ⟨(H.mkW _ ⟨y', hy'p⟩, H.mkW _ ⟨y, hyp⟩), ⟨⟨y', hy'p⟩, ⟨y, hyp⟩, hy'Λ, hyΛ, hyq, rfl⟩, ?_⟩
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      refine Prod.ext ?_ ?_
      · show qEquiv H e hiso (H.X f₁) (H.X f₂) h12 h21 (Submodule.Quotient.mk _) = Submodule.Quotient.mk x''
        rw [qEquiv_mk, mk_eq_iff]
        have h := h12 _ hxy'
        rw [map_sub, LinearEquiv.apply_symm_apply] at h
        have h' := Submodule.neg_mem _ h
        rwa [neg_sub] at h'
      · show Submodule.Quotient.mk _ = Submodule.Quotient.mk x
        rw [mk_eq_iff]
        have h' := Submodule.neg_mem _ hxy
        rwa [neg_sub] at h'

end GenericX

section ConcreteX

variable {D : D7} (Z : LocDat D) (p : PlF D)

def phiP (Λ : Submodule (𝓞 D.host.E) (VS D).V) (f g1 g2 : Fin (D.R.rS + 1) → (VS D).V)
    (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hG : GFacts Λ f g1 g2 β) :
    (locH Z p).Wb (fun b => sF' Z p b • baseChange₂ D p (g1 b)) ≃ₗ[(D.s.atP p).Ep]
      (locH Z p).Wb (fun b => sF' Z p b • baseChange₂ D p (g2 b)) :=
  qEquiv (locH Z p) (betaP p β) (betaP_iso Z p β hG.iso) _ _
    (fun x hx => betaP_mem_X Z p β g1 g2 (sF' Z p) (isUnit_sF' Z p) hG.xmap hx)
    (fun y hy => betaP_symm_mem_X Z p β g1 g2 (sF' Z p) (isUnit_sF' Z p) hG.xmap' hy)

theorem identResp_lt (Λ : Submodule (𝓞 D.host.E) (VS D).V) (f g1 g2 : Fin (D.R.rS + 1) → (VS D).V)
    (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) (Tn T'n : ℕ) (hG : GFacts Λ f g1 g2 β)
    (hI : IotaEl Z p Λ f g1 g2 β) :
    (locH Z p).Ident (lt Z p Λ f g1 Tn T'n) (lt Z p Λ f g2 Tn T'n) (LinearEquiv.refl _ _) (phiP Z p Λ f g1 g2 β hG) ∧
      (locH Z p).Respects (lt Z p Λ f g1 Tn T'n) (lt Z p Λ f g2 Tn T'n) (LinearEquiv.refl _ _)
        (phiP Z p Λ f g1 g2 β hG) := by
  have hiso : ∀ v w, (locH Z p).h (betaP p β v) (betaP p β w) = (locH Z p).h v w := betaP_iso Z p β hG.iso
  refine identResp_generic (locH Z p) (lattice₂ D Z.M p Λ) (fun a => sF Z p a • baseChange₂ D p (f a))
    (fun b => sF' Z p b • baseChange₂ D p (g1 b)) (fun b => sF' Z p b • baseChange₂ D p (g2 b)) _ _ (betaP p β) hiso
    (fun x hx => betaP_mem_X Z p β g1 g2 (sF' Z p) (isUnit_sF' Z p) hG.xmap hx)
    (fun y hy => betaP_symm_mem_X Z p β g1 g2 (sF' Z p) (isUnit_sF' Z p) hG.xmap' hy) ?_ ?_
    (fun x hx => betaP_lat Z p β Λ hG.lam hx) (fun x hx => betaP_symm_lat Z p β Λ hG.lam' hx)
    (fun w hw => scalar_frame_w_zero_exists Z p Λ f g1 g2 β hG hw) ?_ ?_ ?_ ?_ hI
  · apply iso_span
    intro i j
    rw [h_bcP, brS, hG.fiso j i, map_zero, mul_zero]
  · apply iso_span
    intro i j
    rw [h_bcP, brS, hG.g2iso j i, map_zero, mul_zero]
  ·
    rw [om'_loc, om'_loc, dl_loc Z p f g2 (sF Z p) (sF' Z p) _ le_rfl,
      dl_loc Z p f g1 (sF Z p) (sF' Z p) _ le_rfl]
    rw [omp_combine]
    exact Submodule.smul_mem _ _ (bcP_mem_X Z p f (sF Z p) (isUnit_sF Z p) hG.omp)
  ·
    rw [om_loc, om_loc, dl_loc Z p f g2 (sF Z p) (sF' Z p) _ le_rfl,
      dl_loc Z p f g1 (sF Z p) (sF' Z p) _ le_rfl, map_smul, betaP_bc]
    rw [om_combine]
    exact Submodule.smul_mem _ _ (bcP_mem_X Z p g2 (sF' Z p) (isUnit_sF' Z p) hG.om)
  ·
    rw [dl_loc Z p f g1 (sF Z p) (sF' Z p) _ (Nat.le_succ _), dl_loc Z p f g2 (sF Z p) (sF' Z p) _ le_rfl,
      dl_loc Z p f g2 (sF Z p) (sF' Z p) _ (Nat.le_succ _), dl_loc Z p f g1 (sF Z p) (sF' Z p) _ le_rfl]
    have h := congrArg (D.s.atP p).ιE hG.ratio
    rw [map_mul, map_mul] at h
    linear_combination ((∏ i : Fin D.R.rS, (Z.M p).L.cj (sF Z p (Fin.castLE (Nat.le_succ _) i))) *
      (∏ i : Fin D.R.rS, sF' Z p (Fin.castLE (Nat.le_succ _) i)) *
      ((∏ i : Fin (D.R.rS + 1), (Z.M p).L.cj (sF Z p (Fin.castLE le_rfl i))) *
      (∏ i : Fin (D.R.rS + 1), sF' Z p (Fin.castLE le_rfl i)))) * h
  ·
    show betaP p β (sF' Z p (Fin.last _) • baseChange₂ D p (g1 (Fin.last _))) -
      sF' Z p (Fin.last _) • baseChange₂ D p (g2 (Fin.last _)) ∈ _
    rw [map_smul, betaP_bc, ← smul_sub, ← map_sub]
    exact Submodule.smul_mem _ _ (bcP_mem_X Z p g2 (sF' Z p) (isUnit_sF' Z p) hG.zmap)

end ConcreteX

end Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc
  Formalism.L2.SG.Pf.ScalarFramePf

theorem scalarFrameCT_explicit (hI : IotaStep) (D : D7) (Z : LocDat D) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T) (F' F'' : LFlag (VS D) D.R.rS T')
    (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) (Tn T'n : ℕ)
    (hF : FixedHyp D Λ F) (hl' : IsLift Λ F') (hl'' : IsLift Λ F'') (hc' : IsFixedConv Λ (gS D) F')
    (hc'' : IsFixedConv Λ (gS D) F'') (ha' : IsAdmissible Λ (gS D) F F') (ha'' : IsAdmissible Λ (gS D) F F'')
    (hP : IsPair Λ F F' F'' β (gS D)) (hg' : IsGeneric Λ (gS D) F F') (hg'' : IsGeneric Λ (gS D) F F'')
    (hs : Lat.s0 Λ F F' F'' β D.R.k = 1) (hsc : IsScalar Λ F F' F'' β) (hG' : Gval F F' ≠ 0)
    (hG'' : Gval F F'' ≠ 0) (hT : T ≠ 0) (hT' : T' ≠ 0) (p : PlF D) :
    (locH Z p).Ident (locTerm Z p Λ F F' Tn T'n) (locTerm Z p Λ F F'' Tn T'n) (LinearEquiv.refl _ _)
        (phiP Z p Λ (frame F) (frameAct (frame F') (admXi D Λ F F')⁻¹) (frameAct (frame F'') (admXi D Λ F F'')⁻¹) β
          (gfacts_of Λ F F' F'' β hF hl' hl'' hc' hc'' hP hs hsc hG' hG'' hT hT')) ∧
      (locH Z p).Respects (locTerm Z p Λ F F' Tn T'n) (locTerm Z p Λ F F'' Tn T'n) (LinearEquiv.refl _ _)
        (phiP Z p Λ (frame F) (frameAct (frame F') (admXi D Λ F F')⁻¹) (frameAct (frame F'') (admXi D Λ F F'')⁻¹) β
          (gfacts_of Λ F F' F'' β hF hl' hl'' hc' hc'' hP hs hsc hG' hG'' hT hT')) :=
  identResp_lt Z p Λ (frame F) (frameAct (frame F') (admXi D Λ F F')⁻¹)
    (frameAct (frame F'') (admXi D Λ F F'')⁻¹) β Tn T'n
    (gfacts_of Λ F F' F'' β hF hl' hl'' hc' hc'' hP hs hsc hG' hG'' hT hT')
    (hI D Z Λ F F' F'' β hF hl' hl'' hc' hc'' ha' ha'' hP hg' hg'' hs hsc hG' hG'' hT hT' p)

end Formalism.L2.SG.Pf
