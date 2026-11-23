import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedModelTorsionLabelsExist
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UTorsClosed
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.DeltaIsGreatest
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupRescaleIntoLocalRingClassicalTraitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaTorsionPreimageUniformisedModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelPointRescaleSameTorsionPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedModelTransportDeeperThetaSetupStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.GLift

theorem psiQ : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (q : u.D.toPre.X → ℝ), (∀ χ, u.PsiNorm χ (Real.exp (-q χ))) → ∀ χ, l.q χ = q χ := by
  intro o Ω _ _ _ S ρ p _ y₀ u l q hq χ
  have := GlobalTheory.ZH.RealCase.psiNorm_unique u χ (l.q_eq χ) (hq χ)
  exact neg_injective (Real.exp_injective this)

theorem labels_lift : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁), ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (c : CTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab X₁ ε₁ c yy₁ → ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y), ∃ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X), IsLab D.X D.ε (D.lift c y h) yy ∧ D.Compat yy₁ yy := by
  intro g n F W Z i X₁ hg hn hodd himm he8 hth hproj ε₁ hdiag D p _ z₁ c yy₁ hLab y h
  obtain ⟨c₀, hc, R', fg, frac, hth', hev, ρ', ε', hS, hi, hR, y₀, hy₀, u, l, j, hq, hyy, hmat⟩ := hLab
  obtain ⟨c₂, hc₂, R₂, fg₂, frac₂, hth₂, hev₂, ρ₂, ε₂, hS₂, hi₂, hR₂, y₂, hy₂, hint₂⟩ :=
    GlobalTheory.T.thetaSetup_rescale_into_localRing_classicalTrait g n F W Z i D.X hg hn hodd himm he8 hth D.proj D.ε D.diag p (y (cPt p)) (D.lift c y h)
  obtain ⟨u₂, e, T, hpsi, htor, heps, hfw, hbw⟩ := GlobalTheory.T.uniformisedModel_transport_deeperThetaSetup g n F W Z i X₁ hg hn hodd himm he8 hth hproj ε₁ hdiag D p z₁ c y h
    c₀ hc R' fg frac hth' hev ρ' ε' hS hi hR y₀ hy₀ u c₂ hc₂ R₂ fg₂ frac₂ hth₂ hev₂ ρ₂ ε₂ hS₂ hi₂ hR₂ y₂ hy₂
  obtain ⟨l₂⟩ := GlobalTheory.ZH.labels_exist GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2 GlobalTheory.ZH.uTors_closed _ _ _ ρ₂ p y₂ u₂ hint₂
  set L₂ : ℕ := D.X.S.r * D.X.S.N with hL₂
  set L₁ : ℕ := X₁.S.r * X₁.S.N with hL₁
  let jj : u₂.D.toPre.X ≃+ (Fin 8 → c.T.D.toPre.X) := e.trans j
  have hrange : (nsmulAddMonoidHom L₂ : u₂.D.toPre.X →+ u₂.D.toPre.X).range ≤
      ((nsmulAddMonoidHom L₂ : (Fin 8 → c.T.D.toPre.X) →+ (Fin 8 → c.T.D.toPre.X)).range).comap jj.toAddMonoidHom := by
    rintro _ ⟨z, rfl⟩
    exact ⟨jj z, by simp⟩
  let f := QuotientAddGroup.map _ _ jj.toAddMonoidHom hrange
  have hf : ∀ χ, f (QuotientAddGroup.mk χ) = QuotientAddGroup.mk (jj χ) := fun χ => rfl
  refine ⟨f.comp l₂.yy, ⟨c₂, hc₂, R₂, fg₂, frac₂, hth₂, hev₂, ρ₂, ε₂, hS₂, hi₂, hR₂, y₂, hy₂, u₂, l₂, jj, ?_, ?_, ?_⟩, ?_⟩
  · intro χ
    rw [GlobalTheory.Poinc.GLift.psiQ _ _ _ ρ₂ p y₂ u₂ l₂ (fun χ => l.q (e χ)) (fun χ => hpsi χ _ (l.q_eq (e χ))) χ]
    exact hq (e χ)
  · intro a χ ha
    simp only [AddMonoidHom.comp_apply, ha]
    rfl
  · intro m pk pk' x x' E hm hx hx' hxx
    obtain ⟨q₁, hq₁y, hq₁⟩ := hfw m pk x hm hx
    obtain ⟨q₁', hq₁y', hq₁'⟩ := hfw m pk' x' hm hx'
    have := hmat m q₁ q₁' (T x) (T x') E hm hq₁ hq₁' (heps x x' E hxx)
    rw [hq₁y, hq₁y'] at this
    exact this
  · intro a μ hμ
    obtain ⟨pk, x, hx, hxa⟩ := GlobalTheory.T.exists_thetaTorsion_preimage_uniformised_model _ _ _ ρ' p y₀ u a
    have h1 := l.yy_eq a pk x hx hxa
    have h2 := hyy a pk.y h1
    have hL₁pos : 1 ≤ L₁ := by
      obtain ⟨jr, hjr, hr⟩ := X₁.ρ.r_eq
      have h1' : 0 < X₁.S.r := by rw [hr]; exact pow_pos X₁.ρ.n_prime.pos _
      have h2' : 0 < X₁.S.N := by rw [X₁.ρ.N_eq]; exact pow_pos (pow_pos X₁.ρ.n_prime.pos _) _
      exact Nat.mul_pos h1' h2'
    have hdvd : L₁ ∣ L₂ := by
      obtain ⟨t, ht⟩ := D.dvd
      refine ⟨t * (D.m * D.X.S.r), ?_⟩
      rw [hL₂, D.sq, ht]; ring
    have hL₂pos : 1 ≤ L₂ := by
      obtain ⟨jr, hjr, hr⟩ := D.X.ρ.r_eq
      have h1' : 0 < D.X.S.r := by rw [hr]; exact pow_pos D.X.ρ.n_prime.pos _
      have h2' : 0 < D.X.S.N := by rw [D.X.ρ.N_eq]; exact pow_pos (pow_pos D.X.ρ.n_prime.pos _) _
      exact Nat.mul_pos h1' h2'
    have hdpos : 1 ≤ L₂ / L₁ := by
      rw [Nat.one_le_div_iff (by omega)]
      exact Nat.le_of_dvd (by omega) hdvd
    obtain ⟨pk', hpk'y, hpk'⟩ := GlobalTheory.T.exists_levelPoint_rescale_same_torsionPoint _ _ _ ρ' p y₀ u L₁ L₂ (L₂ / L₁) pk x hL₁pos hdpos
      (Nat.div_mul_cancel hdvd).symm hx
    obtain ⟨pk₂, hpk₂y, hpk₂⟩ := hbw L₂ pk' x hL₂pos hpk'
    have h3 := (htor (T.symm x) a).2 (by simpa using hxa)
    have h4 := l₂.yy_eq (D.lab a) pk₂ (T.symm x) hpk₂ h3
    show f (l₂.yy (D.lab a)) = _
    rw [h4, hf]
    have h5 : jj pk₂.y = (L₂ / L₁) • j pk.y := by
      show j (e pk₂.y) = _
      rw [hpk₂y, hpk'y, map_nsmul]
    rw [h5]
    rw [hμ] at h2
    obtain ⟨z, hz⟩ := (QuotientAddGroup.eq).1 h2.symm
    apply (QuotientAddGroup.eq).2
    refine ⟨z, ?_⟩
    simp only [nsmulAddMonoidHom_apply] at hz ⊢
    rw [← smul_neg, ← smul_add, ← hz, smul_smul, Nat.div_mul_cancel hdvd]

end GlobalTheory.Poinc.GLift
