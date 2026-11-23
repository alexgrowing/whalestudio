import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedModelTorsionLabelsExist
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UTorsClosed
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.DeltaIsGreatest
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaTorsionPreimageUniformisedModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelPointRescaleSameTorsionPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedModelTransportDeeperUnitarySetupStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.UPoinc.ULift

theorem psiQ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀) (l : u.Lab) (q : u.D.toPre.X → ℝ) (hq : ∀ χ, u.PsiNorm χ (Real.exp (-q χ))) (χ : u.D.toPre.X) : l.q χ = q χ := by
  have h := Real.exp_injective (GlobalTheory.ZH.RealCase.psiNorm_unique u χ (l.q_eq χ) (hq χ))
  linarith

set_option maxHeartbeats 1000000 in

theorem labels_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf), ∀ (X₁ : USetup C) (D : UDeep X₁) (w₁ : UWit X₁) (w₂ : UWit D.X), D.Comparison₂ w₁ w₂ → ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (ct : UCTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) ct.T.P.D.toPre.X), UIsLabW X₁ w₁ ct yy₁ → ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = ct.y), ∃ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) ct.T.P.D.toPre.X, UIsLabW D.X w₂ (D.lift ct y h) yy ∧ D.Compat yy₁ yy := by
  intro E _ _ _ H Dw hpq l Xo cf C X₁ D w₁ w₂ hT p _ z₁ ct yy₁ hL y h
  unfold UIsLabW at hL
  obtain ⟨c₀, hc, R', fg, frac, hth, hev, ρ', u', hS, hi, hu, hR, G, iG, α, β, hα, hβ, hLB, hm, y₀, hy₀, u, lb, j,
    hq, hyy, hcong⟩ := hL
  obtain ⟨c₂, hc₂, R₂, fg₂, frac₂, hth₂, hev₂, ρ₂, u₂', hS₂, hi₂, hu₂, hR₂, G₂, iG₂, α₂, β₂, hα₂, hβ₂, hLB₂, hm₂,
    y₂, hy₂, hint₂, u₂, e, T, hpsi, hpt, hw, hfw, hbw⟩ :=
    GlobalTheory.T.uniformised_model_transport_deeper_unitary_setup E H Dw hpq l Xo cf C X₁ D w₁ w₂ hT p z₁ ct y h c₀ hc R' fg frac hth hev ρ' u' hS hi hu hR G iG α β
      hα hβ hLB hm y₀ hy₀ u
  obtain ⟨hLaws, hLaws2⟩ := GlobalTheory.abelianSchemeLaws_all
  obtain ⟨lb₂⟩ := GlobalTheory.ZH.labels_exist hLaws hLaws2 GlobalTheory.ZH.uTors_closed _ _ _ ρ₂ p y₂ u₂ hint₂
  have hmap : (nsmulAddMonoidHom (D.X.S.r * D.X.S.N) : u₂.D.toPre.X →+ u₂.D.toPre.X).range ≤
      AddSubgroup.comap (e.trans j).toAddMonoidHom
        (nsmulAddMonoidHom (D.X.S.r * D.X.S.N) : ct.T.P.D.toPre.X →+ ct.T.P.D.toPre.X).range := by
    rintro _ ⟨z, rfl⟩
    exact ⟨(e.trans j) z, by simp [map_nsmul]⟩
  refine ⟨(QuotientAddGroup.map _ _ (e.trans j).toAddMonoidHom hmap).comp lb₂.yy, ?_, ?_⟩
  · unfold UIsLabW
    refine ⟨c₂, hc₂, R₂, fg₂, frac₂, hth₂, hev₂, ρ₂, u₂', hS₂, hi₂, hu₂, hR₂, G₂, iG₂, α₂, β₂, hα₂, hβ₂, hLB₂, hm₂,
      y₂, hy₂, u₂, lb₂, e.trans j, ?_, ?_, ?_⟩
    · intro χ
      rw [psiQ u₂ lb₂ (fun χ => lb.q (e χ)) (fun χ => hpsi χ _ (lb.q_eq (e χ))) χ]
      exact hq (e χ)
    · intro a χ hχ
      rw [AddMonoidHom.comp_apply, hχ, QuotientAddGroup.map_mk]
      rfl
    · intro k a pk pk' x x' w w' hk hx hx' hwx hwx' hww
      obtain ⟨q, hqy, hq'⟩ := hfw k pk x hk hx
      obtain ⟨q', hqy', hq''⟩ := hfw k pk' x' hk hx'
      obtain ⟨v, hvα, hvβ⟩ := hw x w hwx
      obtain ⟨v', hvα', hvβ'⟩ := hw x' w' hwx'
      have hc := hcong k a q q' (T x) (T x') v v' hk hq' hq'' hvα hvα'
        (by rw [hvβ', hww, ← Category.assoc v, hvβ, Category.assoc])
      rw [hqy, hqy'] at hc
      exact hc
  · unfold UDeep.Compat
    intro a μ hμ
    have hN₁ : 0 < X₁.S.N := by rw [X₁.ρ.N_eq]; exact pow_pos (pow_pos X₁.ρ.n_prime.pos _) _
    have hr₁ : 0 < X₁.S.r := by
      obtain ⟨i, -, hi'⟩ := X₁.ρ.r_eq
      rw [hi']; exact pow_pos X₁.ρ.n_prime.pos _
    have hN₂ : 0 < D.X.S.N := by rw [D.X.ρ.N_eq]; exact pow_pos (pow_pos D.X.ρ.n_prime.pos _) _
    have hr₂ : 0 < D.X.S.r := by
      obtain ⟨i, -, hi'⟩ := D.X.ρ.r_eq
      rw [hi']; exact pow_pos D.X.ρ.n_prime.pos _
    have hk1 : 1 ≤ X₁.S.r * X₁.S.N := Nat.mul_pos hr₁ hN₁
    have hk2 : 1 ≤ D.X.S.r * D.X.S.N := Nat.mul_pos hr₂ hN₂
    have hdvd : X₁.S.r * X₁.S.N ∣ D.X.S.r * D.X.S.N := by
      rw [D.sq]
      exact Dvd.dvd.mul_left (D.dvd.trans (dvd_pow_self _ two_ne_zero)) _
    have hd : D.X.S.r * D.X.S.N / (X₁.S.r * X₁.S.N) * (X₁.S.r * X₁.S.N) = D.X.S.r * D.X.S.N :=
      Nat.div_mul_cancel hdvd
    have hd1 : 1 ≤ D.X.S.r * D.X.S.N / (X₁.S.r * X₁.S.N) := Nat.div_pos (Nat.le_of_dvd hk2 hdvd) hk1
    obtain ⟨pk₀, x₀, hx₀, hx₀φ⟩ := GlobalTheory.Poinc.exists_qkPt_of_utest _ _ _ ρ' p y₀ u a
    have h1 : lb.yy a = QuotientAddGroup.mk pk₀.y := lb.yy_eq a pk₀ x₀ hx₀ hx₀φ
    have h2 := hyy a pk₀.y h1
    obtain ⟨pk', hpk'y, hpk'⟩ := GlobalTheory.QLevelRescale.exists_qkPt_rescale _ _ _ ρ' p y₀ u (X₁.S.r * X₁.S.N)
      (D.X.S.r * D.X.S.N) (D.X.S.r * D.X.S.N / (X₁.S.r * X₁.S.N)) pk₀ x₀ hk1 hd1 hd.symm hx₀
    obtain ⟨pk₂, hpk₂y, hpk₂⟩ := hbw _ pk' x₀ hk2 hpk'
    have hx₂ : (T.symm x₀).left ≫ u₂.φ = spMap y₂ ≫ (ρ₂.pt (D.lab a)).left :=
      (hpt (T.symm x₀) a).2 (by rw [Equiv.apply_symm_apply]; exact hx₀φ)
    have h3 : lb₂.yy (D.lab a) = QuotientAddGroup.mk pk₂.y := lb₂.yy_eq (D.lab a) pk₂ (T.symm x₀) hpk₂ hx₂
    rw [AddMonoidHom.comp_apply, h3, QuotientAddGroup.map_mk]
    have h4 : (e.trans j).toAddMonoidHom pk₂.y = (D.X.S.r * D.X.S.N / (X₁.S.r * X₁.S.N)) • j pk₀.y := by
      show j (e pk₂.y) = _
      rw [hpk₂y, hpk'y, map_nsmul]
    rw [h4]
    rw [h2] at hμ
    rw [QuotientAddGroup.eq] at hμ ⊢
    obtain ⟨z, hz⟩ := hμ
    refine ⟨z, ?_⟩
    rw [nsmulAddMonoidHom_apply] at hz ⊢
    calc (D.X.S.r * D.X.S.N) • z
        = (D.X.S.r * D.X.S.N / (X₁.S.r * X₁.S.N)) • (X₁.S.r * X₁.S.N) • z := by rw [smul_smul, hd]
      _ = _ := by rw [hz, smul_add, smul_neg]

end GlobalTheory.UPoinc.ULift
