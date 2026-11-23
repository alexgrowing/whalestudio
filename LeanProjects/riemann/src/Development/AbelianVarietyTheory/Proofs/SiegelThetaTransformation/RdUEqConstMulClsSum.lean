import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.DatEqZero
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.CmHostUnitAddConjEqOne
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RationalSchwartzBruhatAlgebraIntegralLinear
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HMatMulVecPerCrd
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaSeriesTestFunctionHolomorphicWeight
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUnique
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ConstOfNormFactorUnitFr
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FgOfSmulLe
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FramedPointGeneratorIsThetaLevelOne
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSymplOfSelfDual
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnalyticFibreUnitFrameUniformisation
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UniformisationComponentLatticesMarkings
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ProdLevelOneThetaEqVacuumTheta
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsLiftMarked
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.InjectiveOfKerCountable
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeometricLiftsOfFrames
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ClassSumEvalComplexPointEqClassicalStatement

open AlgebraicGeometry CategoryTheory NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj GlobalTheory.Dict GlobalTheory.ClsVal
open scoped Classical

namespace GlobalTheory.ClsVal.Reach

open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.IndefiniteRowSideFullHecke.DeltaDatumCombinedCoefficient (fnAt basePt)
open GlobalTheory.LevelCoverCompare (fnRule evR_fnRule fnRule_mem fnAt_comp)
attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l l₂ : Geo.Tor.Level H}

theorem re_eq_zero_of_sq {d : ℕ} {t : ℂ} (hd : 0 < d) (h : t ^ 2 = -(d : ℂ)) : t.re = 0 := by
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp only [sq, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re,
    Complex.natCast_im, neg_zero] at h1 h2
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  by_contra h0
  have h3 : t.im = 0 := by
    have : t.re * t.im = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_left h0
  rw [h3] at h1
  nlinarith [mul_self_nonneg t.re]

theorem comp_eq_of_marked {Xo : Moduli Dw l₂} {c : Coeff l₂} [inst : Algebra c.F ℂ] (hσ : GoodEmb c (algebraMap c.F ℂ))
    (hA : l.A = 1) (hA₂ : l₂.A = 1) (t : Xo.X ⟶ Sp (KA l)) {r g : ℕ} {X : Data E r}
    {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r} {e : Fin g ≃ Lt1 Dw} {L : Lt E r} (hr : 1 ≤ r)
    (hs : IsSympl X bas) {mk : Dw.La →ₗ[𝓞 E] (Fin r → E)} (hm : ∀ a, mk a ∈ L) {x x' : Frame X.Ψ r} (hx : x ∈ X.dom)
    (hx' : x' ∈ X.dom) {y y' : FrPt Xo c ℂ} (A : AnFib X bas idx e x L y) (A' : AnFib X bas idx e x' L y')
    (hk : A.Marked mk) (hk' : A'.Marked mk) : y.x ≫ t = y'.x ≫ t := by
  obtain ⟨σ, rfl⟩ : ∃ σ : c.F →+* ℂ, inst = σ.toAlgebra := ⟨algebraMap c.F ℂ, Algebra.algebra_ext _ _ fun _ => rfl⟩
  letI : Algebra c.F ℂ := σ.toAlgebra
  let ρ : KA l := (baseKA l).ρ
  let u : KA l := (1 + ρ) / (1 - ρ)
  let g₀ : Γ(Xo.XF c, ⊤) := (pullback.fst _ _ ≫ t : Xo.XF c ⟶ Sp (KA l)).appTop.hom (toΓ (KA l) u)
  have hre : ∀ β : KA l →+* ℂ, (β ρ).re = 0 := fun β =>
    re_eq_zero_of_sq H.d_prime.pos (by rw [← map_pow, (baseKA l).ρ_sq]; simp)
  have hne : ∀ β : KA l →+* ℂ, 1 - β ρ ≠ 0 := fun β h => by
    have := congrArg Complex.re h
    simp [hre β] at this
  have hval : ∀ (z : FrPt Xo c ℂ) (β : KA l →+* ℂ), z.x ≫ t = Geo.Tor.spMap β →
      evR Xo c (fnRule g₀) z = (1 + β ρ) / (1 - β ρ) := fun z β hβ => by
    have h1 : fnAt (basePt z) g₀ = fnAt (basePt z ≫ pullback.fst _ _ ≫ t) (toΓ (KA l) u) := rfl
    have h2 : fnAt (𝟙 (Sp (KA l))) (toΓ (KA l) u) = u := by
      simp [fnAt, toΓ]
    rw [evR_fnRule, h1, basePt, pullback.lift_fst_assoc, hβ, ← Category.comp_id (Geo.Tor.spMap β), fnAt_comp, h2]
    simp [u]
  have h1 : ∀ z : FrPt Xo c (CAt σ), ‖Formalism.L2.PjFree.toC (evR Xo c (fnRule g₀) z)‖ = 1 := fun z => by
    obtain ⟨β, hβ⟩ := LevelFibre.exists_spMap (A := KA l) (B := ℂ) (z.x ≫ t)
    refine (congrArg norm (hval z β hβ)).trans ?_
    rw [norm_div, div_eq_one_iff_eq (norm_ne_zero_iff.2 (hne β)), Complex.norm_def, Complex.norm_def]
    simp [Complex.normSq_apply, hre β]
  obtain ⟨β, hβ⟩ := LevelFibre.exists_spMap (y.x ≫ t)
  obtain ⟨β', hβ'⟩ := LevelFibre.exists_spMap (y'.x ≫ t)
  have h := evR_eq_of_marked σ hσ hA₂ (fnRule_mem g₀) h1 hr hs hm x hx x' hx' y y' A A' hk hk'
  rw [hval y β hβ, hval y' β' hβ', div_eq_div_iff (hne β) (hne β')] at h
  rw [hβ, hβ', MarkLift.emb_ext hA (β := β) (β' := β') (by linear_combination (1 / 2 : ℂ) * h)]

theorem exists_lift_of_reached {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} (d : DeltaDat Xo c n) [Algebra c.F ℂ]
    [Algebra d.c₂.F ℂ] (hk : ∀ t : c.F, algebraMap d.c₂.F ℂ (d.eF t) = algebraMap c.F ℂ t)
    (hσ : GoodEmb d.c₂ (algebraMap d.c₂.F ℂ)) (hlev : d.IsLev) (hA : l.A = 1) (hA₂ : d.l₂.A = 1) {r g : ℕ} (hr : 1 ≤ r)
    {X : Data E r} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r} {e : Fin g ≃ Lt1 Dw}
    {x : Frame X.Ψ r} {L : Lt E r} {y : FrPt Xo c ℂ} (A : AnFib X bas idx e x L y) (hsym : IsSympl X bas)
    (hx : x ∈ X.dom) (hL : SelfD X L) {mk mk₂ : Dw.La →ₗ[𝓞 E] (Fin r → E)} (hm : IsMark l L mk) (hmk : A.Marked mk)
    (hm₂ : IsMark d.l₂ L mk₂) (ho₂ : MarkOver l d.l₂ L mk mk₂) {x₀ : Frame X.Ψ r} (hx₀ : x₀ ∈ X.dom) {y₀ : FrPt Xo c ℂ}
    {z₀ : FrPt d.Xo₂ d.c₂ ℂ} (A₀ : AnFib X bas idx e x₀ L z₀) (h₀ : FrOver d z₀ y₀) (hA₀ : A₀.Marked mk₂) :
    ∃ (y₂ : FrPt d.Xo₂ d.c₂ ℂ) (A₂ : AnFib X bas idx e x L y₂), FrOver d y₂ y ∧ A₂.Marked mk₂ ∧
      ∀ θ, A.Reads 1 y.s θ → A₂.Reads 1 y₂.s θ := by
  obtain ⟨y₃, h₃⟩ := hlev.2.2.2.2.2.2.1 ℂ hk y
  obtain ⟨A₃, ex₃, rd₃, mk₃, hm₃, hmk₃, ho₃⟩ := MarkLift.anFib_lift_ex E H Dw l Xo c n d hk hlev r g X bas idx e x L y A
    hsym hx hL y₃ h₃ mk hmk
  rcases Nat.eq_zero_or_pos (Dw.p + Dw.q) with h0 | hpq
  · haveI := Dw.fin
    haveI := Dw.proj
    haveI : Subsingleton Dw.La := Module.finrank_zero_iff.1 (Dw.rank.trans h0)
    have : mk₂ = mk₃ := LinearMap.ext fun a => by rw [Subsingleton.elim a 0, map_zero, map_zero]
    exact ⟨y₃, A₃, h₃, this ▸ hmk₃, rd₃⟩
  obtain ⟨hd, hM, hc, hI, hI', hE, hlift, hrest⟩ := id hlev
  obtain ⟨k, hk₁, hk₂⟩ := MarkLift.exists_aut hd hm hm₃ hm₂ ho₃ ho₂
  obtain ⟨ρ, ν, iρ, hν⟩ := LevelActionLaws.exists_move hpq (by rw [hA₂]; exact Nat.coprime_one_left _) d.Xo₂ k
  have hpd : d.pd = d.l₂.M / l.M := by
    rw [hM, Nat.mul_div_cancel_left _ (lt_of_lt_of_le (by norm_num) l.three_le)]
  have L₁ : OverMove.Lev d.m := ⟨hpd ▸ hE.1, hE.2⟩
  have hρs : inv ρ ≫ d.Xo₂.s = d.Xo₂.s := by rw [IsIso.inv_comp_eq, hν.1]
  have hM0 : (d.l₂.M : E) ≠ 0 := Nat.cast_ne_zero.2 (LevelFibre.level_pos d.l₂).ne'
  have hper : ∀ u t, t ∈ L → A.ex (pv X idx x ((d.l₂.M : E)⁻¹ • (u + d.l₂.M • t))) =
      A.ex (pv X idx x ((d.l₂.M : E)⁻¹ • u)) := fun u t ht => by
    rw [smul_add, ← Nat.cast_smul_eq_nsmul E, smul_smul, inv_mul_cancel₀ hM0, one_smul, pv, per_add]
    exact (A.ex_add (pv X idx x _) (pv X idx x t)).trans (by rw [(A.ex_ker _).2 ⟨t, ht, rfl⟩, _root_.mul_one])
  have hpres : ∀ (f : Dw.La →ₗ[𝓞 E] Dw.La) a, a ∈ Mfr d.l₂ • (⊤ : Submodule (𝓞 E) Dw.La) →
      f a ∈ Mfr d.l₂ • (⊤ : Submodule (𝓞 E) Dw.La) := fun f a ha => by
    have := Submodule.mem_map_of_mem (f := f) ha
    rw [Submodule.map_smul''] at this
    exact Submodule.smul_mono le_rfl le_top this

  have key : ∀ {ρ' : d.Xo₂.X ⟶ Xo.X} (m' : SABMap d.Xo₂.univ.t Xo.univ.t ρ') (w : FrPt d.Xo₂ d.c₂ ℂ)
      (B : AnFib X bas idx e x L w), (∀ z, (B.ex z).left ≫ m'.φ = (A.ex z).left) →
      (∀ a, (w.x ≫ (d.Xo₂.univ.eta (liftLa k a)).left) ≫ m'.φ = (y₃.x ≫ (d.Xo₂.univ.eta a).left) ≫ d.m.φ) →
      B.Marked mk₂ := by
    intro ρ' m' w B hB hw a' ha'
    have ha := hpres (liftLa k.symm) a' ha'
    have hδ : liftLa k (liftLa k.symm a') - a' ∈ d.l₂.Mb • (⊤ : Submodule (𝓞 E) Dw.La) := by
      rw [← Submodule.Quotient.eq]
      have h1 := liftLa_spec k (liftLa k.symm a')
      rw [liftLa_spec k.symm a', k.apply_symm_apply] at h1
      exact h1
    obtain ⟨u, hu, v, hv, huv⟩ := LevelFibre.level_split d.l₂
    obtain ⟨b, -, hb⟩ := MarkLift.modN_of_mem_half d.l₂ hu (Submodule.sub_mem _ (hpres (liftLa k) _ ha) ha')
    obtain ⟨b', hb'⟩ := MarkLift.modN_of_mem_bar d.l₂ hv hδ
    have e₀ : mk₂ (liftLa k (liftLa k.symm a')) = mk₂ a' + d.l₂.M • mk₂ (b + b') := by
      rw [← map_nsmul, smul_add, ← hb, ← hb', ← add_smul, huv, one_smul, ← map_add, add_sub_cancel]
    obtain ⟨t, ht, e₁⟩ := hk₂ _ ha
    have e₂ := (hper _ t ht).symm.trans ((congrArg (fun q => A.ex (pv X idx x ((d.l₂.M : E)⁻¹ • q))) (e₁.symm.trans e₀)).trans (hper _ _ (hm₂.mem _)))
    apply Over.OverMorphism.ext
    apply m'.cart.1.hom_ext
    · refine Eq.trans ?_ (hB _).symm
      rw [← e₂, ← ex₃, ← hmk₃ _ ha, levPt, levPt, LevelFibre.unit_left, LevelFibre.unit_left,
        ← LevelActionLaws.eta_congr d.Xo₂ hδ]
      exact hw _
    · rw [Over.w, Over.w]

  obtain ⟨m', hm'⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ d.m ν
  have hm'' : m'.φ = ν.φ ≫ d.m.φ := hm'
  let d' : DeltaDat Xo c n := { d with r := ρ ≫ d.r, m := m' }
  have hfix : ∀ a, (d.Xo₂.univ.eta (liftLa k a) ^ d.pd).left = (d.Xo₂.univ.eta a ^ d.pd).left := fun a => by
    apply d.m.cart.1.hom_ext
    · rw [hE.1, hE.1, LevelActionLaws.eta_congr Xo (hk₁ a)]
    · rw [LevelFibre.sec_w, LevelFibre.sec_w]
  have hl' : ∀ (K : Type) [Field K] [Algebra c.F K] [Algebra d.c₂.F K],
      (∀ a : c.F, algebraMap d.c₂.F K (d.eF a) = algebraMap c.F K a) → ∀ (y : FrPt Xo c K) (w : FrPt d.Xo₂ d.c₂ K),
      FrOver d w y → ∃ w' : FrPt d.Xo₂ d.c₂ K, w'.x = w.x ≫ inv ρ ∧ FrOver d' w' y := fun K _ _ _ hK y w hw =>
    (frames_lift_to_cover firstFiveLaws.1 E H Dw l Xo c n d').1 K hK y _
      (by change (w.x ≫ inv ρ) ≫ ρ ≫ d.r = _; rw [Category.assoc, IsIso.inv_hom_id_assoc, hw.1])
      (by change (w.x ≫ inv ρ) ≫ d.Xo₂.s = _; rw [Category.assoc, hρs, w.x_over])
  have hlev' : d'.IsLev := by
    refine ⟨hd, hM, hc, hI, hI', ⟨fun a => ?_, fun a => ?_⟩, fun K _ _ _ _ hK y => ?_, hrest⟩
    · change (d.Xo₂.univ.eta a ^ d.pd).left ≫ m'.φ = (ρ ≫ d.r) ≫ _
      rw [hm'', ← hfix, ← Category.assoc, OverMove.pow_left_comp ν (hν.2.1 a), Category.assoc, hE.1, Category.assoc]
    · change (d.Xo₂.univ.etaA a ^ (d.l₂.A / l.A)).left ≫ m'.φ = (ρ ≫ d.r) ≫ _
      rw [hm'', ← Category.assoc, OverMove.pow_left_comp ν (σ := d.Xo₂.univ.etaA a) (hν.2.2 a), Category.assoc, hE.2,
        Category.assoc]
    · obtain ⟨w, hw⟩ := hlift K hK y
      obtain ⟨w', -, hw'⟩ := hl' K hK y w hw
      exact ⟨w', hw'⟩
  obtain ⟨y₄, hy₄, h₄⟩ := hl' ℂ hk y y₃ h₃
  have hyρ : y₄.x ≫ ρ = y₃.x := by rw [hy₄, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  obtain ⟨A₄, ex₄, -⟩ := MarkLift.anFib_lift_ex E H Dw l Xo c n d' hk hlev' r g X bas idx e x L y A
    hsym hx hL y₄ h₄ mk hmk
  have hA₄ : A₄.Marked mk₂ := key m' y₄ A₄ ex₄ fun a => by
    rw [hm'', ← Category.assoc, Category.assoc y₄.x, hν.2.1, ← Category.assoc y₄.x, hyρ]
  have hs := comp_eq_of_marked hσ hA hA₂ (d.r ≫ Xo.s) hr hsym hm₂.mem hx hx₀ A₄ A₀ hA₄ hA₀
  rw [← Category.assoc z₀.x, h₀.1, y₀.x_over, ← y.x_over, ← h₃.1, ← hyρ, ← Category.assoc] at hs
  obtain ⟨hb, hη⟩ := MarkLift.move_fibre L₁ hν hk₁ (x := y₄.x) rfl hs.symm
  rw [hyρ] at hb hη
  obtain ⟨y₂, hy₂, h₂⟩ := (frames_lift_to_cover firstFiveLaws.1 E H Dw l Xo c n d).1 ℂ hk y y₄.x
    (hb.symm.trans h₃.1) y₄.x_over
  obtain ⟨A₂, ex₂, rd₂, -⟩ := MarkLift.anFib_lift_ex E H Dw l Xo c n d hk hlev r g X bas idx e x L y A hsym
    hx hL y₂ h₂ mk hmk
  exact ⟨y₂, A₂, h₂, key d.m y₂ A₂ ex₂ fun a => by rw [hy₂, hη], rd₂⟩

end GlobalTheory.ClsVal.Reach

namespace GlobalTheory.ClsVal.Const

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ}

theorem exists_const (X : Data E r) (la : Wt X.Ψ r) (ρ : ℝ) (hρ : 0 < ρ)
    (κ : ∀ x ∈ X.dom, IsUnitFr X x → ℂ) (hκ : ∀ x hx hu, ‖κ x hx hu‖ = ρ) :
    ∃ C : ℂ, ‖C‖ = ρ ∧ ∀ R T : Frame X.Ψ r → ℂ, DifferentiableOn ℂ R X.dom → DifferentiableOn ℂ T X.dom →
      (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, R (rmul x b) = bchar la b * R x ∧ T (rmul x b) = bchar la b * T x) →
      (∀ x hx hu, R x = κ x hx hu * T x) → ∀ x ∈ X.dom, R x = C * T x := by
  obtain ⟨C, -, hC⟩ := const_of_norm_factor_unitFr E r X la
    {q : (Frame X.Ψ r → ℂ) × (Frame X.Ψ r → ℂ) // DifferentiableOn ℂ q.1 X.dom ∧ DifferentiableOn ℂ q.2 X.dom ∧
      (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, q.1 (rmul x b) = bchar la b * q.1 x ∧ q.2 (rmul x b) = bchar la b * q.2 x) ∧
      ∀ x hx hu, q.1 x = κ x hx hu * q.2 x} (fun q => q.1.1) (fun q => q.1.2) ρ hρ
    (fun q => ⟨q.2.1, q.2.2.1, q.2.2.2.1⟩) (fun x hx hu => ⟨κ x hx hu, hκ x hx hu, fun q => q.2.2.2.2 x hx hu⟩)
  by_cases h : ‖C‖ = ρ
  · exact ⟨C, h, fun R T h1 h2 h3 h4 => hC ⟨⟨R, T⟩, h1, h2, h3, h4⟩⟩
  refine ⟨ρ, by simp [hρ.le], fun R T h1 h2 h3 h4 x hx => ?_⟩
  have h5 : ∀ y ∈ X.dom, R y = C * T y := hC ⟨⟨R, T⟩, h1, h2, h3, h4⟩
  obtain ⟨b, hb, hxb, hu⟩ := exists_unitFr_rmul X hx
  have h6 : T (rmul x b) = 0 := by
    by_contra h0
    exact h (by rw [mul_right_cancel₀ h0 ((h5 _ hxb).symm.trans (h4 _ hxb hu)), hκ])
  rw [(h3 x hx b hb).2, mul_eq_zero, or_iff_right (bchar_ne_zero_of_mem_bor la hb)] at h6
  rw [h5 x hx, h6, mul_zero, mul_zero]

theorem isSB_smul_tf (a : ℂ) {φ : TF n g} (h : IsSB φ) : IsSB (a • φ) :=
  (isSB_algebra_haar_linear ℚ _ _ φ φ h h).2.1 a

theorem isSB_gphi {X : Data E r} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r)
    (hs : IsSympl X bas) (hn : Even n) {w : E} (hw : IsIntegral ℤ w) (hw' : w + cc w = 1) {L : Lt E r}
    (hL : SelfD X L) {M : ℕ} {Λ : Lt E n} (hΛ : Λ ∈ Vset E n M) {v : TF n g} (hv : IsSB v) {Q : Type}
    (W : Q → ℂ) (Y : Q → Matrix (Fin n) (Fin r) E) : IsSB (gphi X bas w Λ L v W Y) := by
  obtain ⟨⟨v', hv'⟩, -, h, -⟩ := TensVac.vacua E r X g bas idx n hs hn w hw hw' L hL M Λ hΛ
  refine finsum_induction (fun φ : TF n g => IsSB φ) isSB_zero
    (fun φ ψ h h' => (isSB_algebra_haar_linear ℚ _ _ φ ψ h h').1) fun q =>
    isSB_smul_tf _ ((heisG_laws E r X g bas idx n hs hn).2.2.2 _ _ ?_).1
  rw [h v hv v' hv']
  exact isSB_smul_tf _ hv'.1

end GlobalTheory.ClsVal.Const

open GlobalTheory.ClsVal.Const in

theorem GlobalTheory.ClsVal.rdU_eq_const_mul_clsSum : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → 1 ≤ r → l.A = 1 → ∀ (W : UW U) (k : U.Comp) (n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ), Dom a n → ∀ (Dc : Dic Dw c σ (U.X k) W.g Dw.p n a), Dc.e = W.e → ∀ v : TF n W.g, IsVac (U.X k) Dc.bas (H.w0 : E) (tens (stdL E n) (U.X k).Λ) v → ∃ C : ℂ, (∀ x ∈ (U.X k).dom, IsUnitFr (U.X k) x → ∀ (θ : (Fin W.g → ℂ) → ℂ) (κ : ℂ), IsTheta1 (U.X k) Dc.bas Dc.idx (H.w0 : E) x (U.X k).Λ θ → MeanOne (U.X k) Dc.bas Dc.idx x (U.X k).Λ θ → (∀ z : Fin n → Fin W.g → ℂ, ∏ b, θ (z b) = κ * thA (U.X k) Dc.bas Dc.idx v x z) → ‖κ‖ = ‖C‖) ∧ C ≠ 0 ∧ ∀ (d : DeltaDat Xo c n) [Algebra d.c₂.F ℂ], (∀ t : c.F, algebraMap d.c₂.F ℂ (d.eF t) = σ t) → d.IsLev → d.l₂.A = 1 → (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) → ∀ cv : (Dw.La →ₗ[𝓞 E] (Fin r → E)) → ℂ, (∀ mk, ‖cv mk‖ = 1) → CvIs d (U.X k) Dc.bas Dc.idx W.e (U.X k).Λ cv → ∀ mk₂ : Dw.La →ₗ[𝓞 E] (Fin r → E), IsMark d.l₂ (U.X k).Λ mk₂ → MarkOver l d.l₂ (U.X k).Λ (W.mark k) mk₂ → (Dw.p = Dw.q → (∀ h : KA l ≤ KA d.l₂, d.r ≫ Xo.s = d.Xo₂.s ≫ Geo.Tor.spMap (IntermediateField.inclusion h).toRingHom) ∨ ∃ (x₀ : (U.X k).dom) (y₂ : FrPt d.Xo₂ d.c₂ ℂ) (A₂ : AnFib (U.X k) Dc.bas Dc.idx W.e x₀ (U.X k).Λ y₂), (letI : Algebra c.F ℂ := σ.toAlgebra; FrOver d y₂ (unC U k x₀)) ∧ A₂.Marked mk₂) → ∀ (Cl : Type) [Fintype Cl] (w : Cl → (Fin n → LevQ Dw d.l₂) → c.F) (La : Cl → GenLat E n) (Nc gam : Cl → ℕ) (vol : c.F) (ep : Cl → c.F) (Vs : Type) [AddCommGroup Vs] [Module c.F Vs] (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) (xs : Cl → Vs), LatsOK d.l₂.M La Nc → (∀ j, io (xs j) ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) → ∀ Y : Cl → (Fin n → LevQ Dw d.l₂) → Matrix (Fin n) (Fin r) E, (∀ j, IsRoots d.l₂ (U.X k).Λ mk₂ (Nc j) (Y j)) → ∀ f ∈ sec Xo c a n, IsThClsD Xo c d w La Nc gam vol ep io xs f → ∀ x ∈ (U.X k).dom, Formalism.L2.PjFree.rdU U f k x = C * cv mk₂ * clsSum σ (U.X k) Dc.hr Dc.bas Dc.idx Dc.eL w La Nc gam vol ep (fun j => io (xs j)) (U.X k).Λ v Y x := by
  intro hCI E _ _ _ H Dw l Xo c σ r U hσ hU hr1 hA1 W k n a hdom Dc hDe v hv
  letI : Algebra c.F ℂ := σ.toAlgebra
  have hn : Even n := hdom.2
  obtain ⟨-, hL, hmk, -⟩ := uw_lattice E H Dw l Xo c σ r U hσ hU hr1 W k
  have hw : IsIntegral ℤ (H.w0 : E) := H.w0.isIntegral_coe
  have hw' : (H.w0 : E) + cc (H.w0 : E) = 1 := by
    rw [cc, ← H.bar_eq]
    exact_mod_cast congrArg (fun t : 𝓞 E => (t : E)) (PullbackSections.CVA.cmHostUnit_add_conj_eq_one H)
  obtain ⟨ρ, hρ, hnorm⟩ := VacNorm.norm_factor_eq E r _ _ Dc.bas Dc.idx n Dc.sympl hn _ hw hw' _ hL v hv
  have hpt : ∀ x (hx : x ∈ (U.X k).dom), IsUnitFr (U.X k) x → ∃ κ : ℂ, ‖κ‖ = ρ ∧
      ∃ (A : AnFib (U.X k) Dc.bas Dc.idx W.e x (U.X k).Λ (unC U k ⟨x, hx⟩)) (θ : (Fin W.g → ℂ) → ℂ),
        A.Marked (W.mark k) ∧ A.Reads 1 (unC U k ⟨x, hx⟩).s θ ∧
        ∀ z : Fin n → Fin W.g → ℂ, ∏ b, θ (z b) = κ * thA (U.X k) Dc.bas Dc.idx v x z := by
    intro x hx hux
    obtain ⟨A, hA, θ, hθ, hmean⟩ := uw_anFib E H Dw l Xo c σ r U hσ hU hr1 W k Dc.bas Dc.idx Dc.sympl
      (hDe ▸ Dc.per_eq) (hDe ▸ Dc.ty_eq) ⟨x, hx⟩ hux
    have hT := isTheta1_of_reads_generator E H Dw l Xo c r _ _ Dc.bas Dc.idx W.e x _ _ A Dc.sympl hx hL θ hθ
    obtain ⟨κ, hκ⟩ := VacProd.prod_eq_mul_thA E r _ _ Dc.bas Dc.idx n Dc.sympl hn _ hw hw' _ hL v hv x hx θ hT
    exact ⟨κ, hnorm x hx hux θ κ hT hmean hκ, A, θ, hA, hθ, hκ⟩
  choose κ hκ hpt using hpt
  obtain ⟨C, hC, hCe⟩ := Const.exists_const (U.X k) (Formalism.L2.PjFree.laU U a n k) ρ hρ κ hκ
  refine ⟨C, fun x hx hu θ κ' h1 h2 h3 => (hnorm x hx hu θ κ' h1 h2 h3).trans hC.symm,
    norm_pos_iff.1 (hC ▸ hρ), ?_⟩
  intro d _ halg hlev hA2 hnab cv _ hcv mk₂ hmk₂ hover hK Cl _ w La Nc gam vol ep Vs _ _ io xs hlat hP Y hY f hf hcls
    x hx
  have hM : 0 < d.l₂.M := lt_of_lt_of_le (by norm_num) d.l₂.three_le
  have hth := fun j => theta_holomorphic_weight E r _ _ _ Dc.hr Dc.bas Dc.idx n Dc.sympl hn _ _ _
    (isSB_gphi Dc.idx Dc.sympl hn hw hw' hL
      ((GenLatCmp.genLat_vset E n (La j).La).2.1 _ (Nc j) hM (hlat j).1 (hlat j).2.1 (hlat j).2.2) hv.1
      (fun q => σ (w j q)) (Y j)) _ (Dc.mem _ (hP j))
  rw [Dc.wt_eq] at hth
  have hsec := hU.2.2.2.2.1 a n hdom f hf k
  rw [_root_.mul_assoc]
  refine hCe (Formalism.L2.PjFree.rdU U f k) (fun x => cv mk₂ * clsSum σ (U.X k) Dc.hr Dc.bas Dc.idx Dc.eL w La Nc gam vol ep
    (fun j => io (xs j)) (U.X k).Λ v Y x) hsec.1 ?_ (fun x hx b hb => ⟨hsec.2.1 x hx b hb, ?_⟩) ?_ x hx
  · exact (DifferentiableOn.fun_sum fun j _ => (hth j).1.const_mul _).const_mul _
  · simp only [clsSum]
    rw [mul_left_comm]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [(hth j).2.1 x hx b hb, mul_left_comm]
    rfl
  · intro x hx hux
    obtain ⟨A, θ, hA, hθ, hprod⟩ := hpt x hx hux
    obtain ⟨y₂, A₂, hy₂, hA₂, hrd⟩ : ∃ (y₂ : FrPt d.Xo₂ d.c₂ ℂ) (A₂ : AnFib (U.X k) Dc.bas Dc.idx W.e x (U.X k).Λ y₂),
        FrOver d y₂ (unC U k ⟨x, hx⟩) ∧ A₂.Marked mk₂ ∧
          ∀ θ, A.Reads 1 (unC U k ⟨x, hx⟩).s θ → A₂.Reads 1 y₂.s θ := by
      by_cases hK' : Dw.p = Dw.q → ∀ h : KA l ≤ KA d.l₂,
          d.r ≫ Xo.s = d.Xo₂.s ≫ Geo.Tor.spMap (IntermediateField.inclusion h).toRingHom
      · exact MarkLift.exists_lift_marked E H Dw l Xo c n d halg hlev hA1 hA2 hK' r _ _ Dc.bas Dc.idx W.e x _ _ A
          Dc.sympl hx hL _ mk₂ hmk hA hmk₂ hover
      · obtain ⟨hpq, hK''⟩ := Classical.not_imp.1 hK'
        obtain ⟨x₀, z₀, A₀, h₀, hA₀⟩ := (hK hpq).resolve_left hK''
        have hσ₂ : GoodEmb d.c₂ (algebraMap d.c₂.F ℂ) := by
          have h1 : d.eF (IntermediateField.inclusion c.le (baseKA l).ρ) =
              IntermediateField.inclusion d.c₂.le (baseKA d.l₂).ρ := Subtype.ext rfl
          change algebraMap d.c₂.F ℂ (IntermediateField.inclusion d.c₂.le (baseKA d.l₂).ρ) = _
          rw [← h1, halg]
          exact hσ
        exact Reach.exists_lift_of_reached d halg hσ₂ hlev hA1 hA2 hr1 A Dc.sympl hx hL hmk hA hmk₂ hover x₀.2 A₀ h₀ hA₀
    have hval := GlobalTheory.T.classSum_eval_complex_point_eq_classical hCI E H Dw l Xo c n d halg hnab r _ _ Dc.bas Dc.idx W.e x _ _ y₂ A₂ hy₂ Dc.sympl hx hL
      _ Dc.hr Dc.eL hU.1 hn (hDe ▸ Dc.dir_eq) θ v _ (hrd θ hθ) hv hprod mk₂ hmk₂ hA₂ Cl w La Nc gam vol ep Vs io xs a
      hlat hP Y hY f hcls
    have hrd' : Formalism.L2.PjFree.rdU U f k x = evR Xo c f (unC U k ⟨x, hx⟩) := dif_pos hx
    rw [hcv x hx y₂ A₂ mk₂ hmk₂ hA₂] at hval
    rw [hrd', hval, mul_comm (cv mk₂), _root_.mul_assoc]
    rfl
