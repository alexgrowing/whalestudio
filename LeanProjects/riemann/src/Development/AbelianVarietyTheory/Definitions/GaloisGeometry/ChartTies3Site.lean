import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MemberChainFormsLevelPrimeEqMember
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StabilisesColumnBaseLatticeIffFirstFactor

noncomputable section

section
namespace GlobalTheory.Port

open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.ChartsLv

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ
  Formalism.MainNotions.G.CmpJ.PStabEq Formalism.MainNotions.G.KAat Formalism.MainNotions.G.ChartsLv
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem formsLev_re {a b : ℕ} (h : a = b) (σ : E →ₐ[F] E) (J : Matrix (Fin a) (Fin a) E) (J' : Matrix (Fin b) (Fin b) E)
    (hJ : ∀ x y, J' x y = J (Fin.cast h.symm x) (Fin.cast h.symm y)) {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
    (S : Formalism.L2.Forms.StepLevel F E σ J' T f bad) (v : HeightOneSpectrum (𝓞 F)) :
    ((S.Uloc v).comap (reGL h _).toMonoidHom ≤ levelVL σ J v (reL h.symm S.Lb)) ∧
    ((T : 𝓞 F) ∉ v.asIdeal → SelfDualAt σ J v (reL h.symm S.Lb)) ∧
    (v ∉ bad → (T : 𝓞 F) ∉ v.asIdeal → levelVL σ J v (reL h.symm S.Lb) ≤ (S.Uloc v).comap (reGL h _).toMonoidHom) := by
  subst h
  obtain rfl : J' = J := by ext x y; exact hJ x y
  rw [reL_rfl]
  refine ⟨fun x hx => ?_, fun hT => ?_, fun hb hT x hx => ?_⟩
  · have hx' : reGL rfl _ x ∈ S.Uloc v := hx
    rw [Formalism.L2.Forms.reGL_rfl] at hx'
    exact S.Uloc_lev v hx'
  · exact self_dual_lattice_at F E a σ J' v S.Lb T S.Lb_fin (fun x hx y hy => S.Lb_int y hy x hx) (fun y hy => S.Lb_dual y hy) hT
  · show reGL rfl _ x ∈ S.Uloc v
    rw [Formalism.L2.Forms.reGL_rfl, S.Uloc_hyp v hb hT]
    exact hx

end Gen

variable {D : D7} {X0 : Formalism.L2.Herm.Herm0 D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
  {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
  {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P}

set_option maxHeartbeats 4000000 in

theorem hypTJC_site (Z : SiteD X0 u w hg M) (Fl : Fills (D.gat u w hg)) (ht : Fl.t = D.R.t)
    (hT : ∀ i hi, ¬ D.what₂.places.resChar w ∣ (Z.Fo i hi).T) (i : ℕ) (hi : i + 1 ≤ D.R.m) (β : (Z.Fo i hi).Ch) :
    HypTJC ((Z.loc Fl ht i hi).t β) :=
  hypTJC_of_le ((Z.loc Fl ht i hi).t β)
    (fun w' _ => (formsLev_re (rankN D (i + 1) hi) D.sp.cm.sig (D.sp.X (i + 1)).gram (gramN D (i + 1) hi) (gramN_apply D (i + 1) hi)
      ((Z.Fo i hi).K β).lev w').1)
    (fun w' h => (formsLev_re (rankN D (i + 1) hi) D.sp.cm.sig (D.sp.X (i + 1)).gram (gramN D (i + 1) hi) (gramN_apply D (i + 1) hi)
      ((Z.Fo i hi).K β).lev w').2.1 (T_not_mem hg.1 (hT i hi) w' h))

set_option maxHeartbeats 4000000 in

theorem hypTJ_site (Z : SiteD X0 u w hg M) (Fl : Fills (D.gat u w hg)) (ht : Fl.t = D.R.t)
    (hT : ∀ i hi, ¬ D.what₂.places.resChar w ∣ (Z.Fo i hi).T)
    (hbad : ∀ i hi, ∀ w' ∈ (Z.Fo i hi).bad, ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∉ w'.asIdeal)
    (i : ℕ) (hi : i + 1 ≤ D.R.m) (β : (Z.Fo i hi).Ch) : HypTJ ((Z.loc Fl ht i hi).t β) :=
  hypTJ_of_ge ((Z.loc Fl ht i hi).t β)
    (fun w' h => (formsLev_re (rankN D (i + 1) hi) D.sp.cm.sig (D.sp.X (i + 1)).gram (gramN D (i + 1) hi) (gramN_apply D (i + 1) hi)
      ((Z.Fo i hi).K β).lev w').2.2 (fun hb => hbad i hi w' hb h) (T_not_mem hg.1 (hT i hi) w' h))
    (fun w' h => (formsLev_re (rankN D (i + 1) hi) D.sp.cm.sig (D.sp.X (i + 1)).gram (gramN D (i + 1) hi) (gramN_apply D (i + 1) hi)
      ((Z.Fo i hi).K β).lev w').2.1 (T_not_mem hg.1 (hT i hi) w' h))

variable {Tw : TwForms D} {μ : D.what₂.Tup}

end GlobalTheory.Port

end

end
