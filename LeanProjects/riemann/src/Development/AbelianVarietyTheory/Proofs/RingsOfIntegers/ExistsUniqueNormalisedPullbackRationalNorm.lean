import Mathlib
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsTranslatedNormalisedPullbackSection
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory

namespace NormPullUniq

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] (L : RigLB A)

theorem isNormPull_unique (hp : Function.Surjective A.hom.appTop.hom) (φ : A ⟶ A) (a b : ℤ)
    {T : Over S} {s : LB.Sec (LPow A L.L b T)} {s₁ s₂ : LB.Sec (LPow A L.L a T)}
    (h₁ : IsNormPull A L φ a b s s₁) (h₂ : IsNormPull A L φ a b s s₂) : s₁ = s₂ := by
  have hL := L.isLB
  obtain ⟨α₀, α, hα₀, nα, cα, tα⟩ := h₁
  obtain ⟨β₀, β, hβ₀, nβ, cβ, tβ⟩ := h₂
  have key : ∀ j, s₁.f j = s₂.f j :=
    sec_ext_val hL (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) (s := s₁) (s' := s₂)
      fun y J hJ => by
        refine (twist_val tα (𝟙 _) y hJ).trans (Eq.trans ?_ (twist_val tβ (𝟙 _) y hJ).symm)
        rw [val_corr hJ cα (𝟙 _), val_corr hJ cβ (𝟙 _), val_pull hJ, val_pull hJ]
        rw [gen_unique hL A.hom (eSec A) NormMulUniv.eSec_hom hp hα₀ hβ₀ (fun w I hI => by
          have a := val_corr hI nα (𝟙 _)
          have b := val_corr hI nβ (𝟙 _)
          rw [val_pull hI, Category.id_comp] at a b
          exact a.trans b.symm) _ _ y J hJ]
  obtain ⟨f₁, p₁⟩ := s₁
  obtain ⟨f₂, p₂⟩ := s₂
  obtain rfl : f₁ = f₂ := funext key
  rfl

end NormPullUniq

theorem existsUnique_pulls : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (a : 𝓞 E) (N k k' : ℕ), a * H.bar a = (N : 𝓞 E) → k' = k * N → ∀ F : SecN Xo x k, ∃! F' : SecN Xo x k', Pulls Xo a F F' := by
  intro E _ _ _ H Dw l Xo S _ x a N k k' ha hk F
  subst hk
  letI := H.starRing
  have := Xo.univ.t.act.hom a
  have hL := Xo.univ.t.PP.isLB
  have h := PullGenG.hasGen_pull Xo.univ.t.PP Xo.univ.t.cub Xo.univ.t.act.toRingAct H.w0 a N ha (Xo.univ.t.adj a)
    Xo.univ.t.prim k
  obtain ⟨β, hβ⟩ := h.gen hL (K' := Fin 2) ![𝟙 Xo.univ.t.G.left, (Xo.univ.t.act.act a).left]
    ![((k * N : ℕ) : ℤ), -(k : ℤ)] rfl
  obtain ⟨F', hF'⟩ := TransPullEx.exists_isNormPull Xo.univ.t.PP (Xo.univ.t.act.act a) ((k * N : ℕ) : ℤ) k β hβ F
  exact ⟨F', hF', fun F'' hF'' => NormPullUniq.isNormPull_unique Xo.univ.t.PP
    (SemiRigid.globalFns _ _ (ObjDim.isAbelianScheme Xo.univ)).2 _ _ _ hF'' hF'⟩

end GlobalTheory
