import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.GoodMap
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.JunkEx
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ExponentMulAbsPow
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ParUniq
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.NormEqProd
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ParDual
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ParOne
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.TwTame
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.TameArt
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ClBasic
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.WDBasic
import Development.DiscreteGroups.GlobalIrreducibility.DzLDepth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Zero.LLC

section SlopeTestRemainingChoices

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

private theorem charZero_compl (w : HeightOneSpectrum (𝓞 E)) : CharZero (w.adicCompletion E) :=
  charZero_of_injective_algebraMap (algebraMap E _).injective

private theorem twist_congr (V : WD h) {ξ ξ' : Weil h →* ℂˣ} (hξ : GlobalTheory.WeilDeligne.IsSmooth ξ)
    (hξ' : GlobalTheory.WeilDeligne.IsSmooth ξ') (e : ξ = ξ') : V.lpTwist ξ hξ = V.lpTwist ξ' hξ' := by
  subst e; rfl

private theorem tw_congr (y : IrrGL (w.adicCompletion E)) {χ χ' : (w.adicCompletion E)ˣ →* ℂˣ} (hχ : IsSmoothChar χ)
    (hχ' : IsSmoothChar χ') (e : χ = χ') : y.tw χ hχ = y.tw χ' hχ' := by
  subst e; rfl

private theorem good_cases {x : IrrGL (w.adicCompletion E)} (hc : x.IsCusp) (hg : GoodCusp x) :
    x.1 = 1 ∨ ((∃ (g : ℕ) (_ : Fact g.Prime) (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i) ∧
      ∃ (y : IrrGL (w.adicCompletion E)) (χ : (w.adicCompletion E)ˣ →* ℂˣ) (hχ : IsSmoothChar χ),
        y.IsCusp ∧ DZ y ∧ x = y.tw χ hχ) := by
  haveI := charZero_compl (E := E) w
  rcases hg with h1 | ⟨hq, y, χ, hχ, hd, rfl⟩
  · exact Or.inl h1
  · exact Or.inr ⟨hq, y, χ, hχ, ((clBasic _ y).2.1 χ hχ).2.1.1 hc, hd, rfl⟩

private theorem goodCusp_self {y : IrrGL (w.adicCompletion E)}
    (hq : ∃ (g : ℕ) (_ : Fact g.Prime) (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i) (hd : DZ y) : GoodCusp y :=
  Or.inr ⟨hq, y, 1, isSmoothChar_one, hd, (IrrGL.tw_one y _).symm⟩

variable {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a}

private theorem lpTw_eq (ha : IsLocalArtin h a) (V : WD h) (s : ℝ) :
    V.lpTw s = V.lpTwist ((absPow (w.adicCompletion E) s).comp a) (ha.smooth (isSmoothChar_absPow _)) :=
  twist_congr V _ _ (ha.absPow_comp s).symm

private theorem twist_twist (ha : IsLocalArtin h a) (V : WD h) {χ χ' : (w.adicCompletion E)ˣ →* ℂˣ} (hχ : IsSmoothChar χ)
    (hχ' : IsSmoothChar χ') (hm : IsSmoothChar (χ * χ')) :
    (V.lpTwist (χ.comp a) (ha.smooth hχ)).lpTwist (χ'.comp a) (ha.smooth hχ') =
      V.lpTwist ((χ * χ').comp a) (ha.smooth hm) := by
  obtain ⟨-, -, -, -, -, -, -, -, c9⟩ := wDBasic E Ω A w h V
  have e : (χ * χ').comp a = χ.comp a * χ'.comp a := MonoidHom.ext fun _ => rfl
  have hs : GlobalTheory.WeilDeligne.IsSmooth (χ.comp a * χ'.comp a) := e ▸ ha.smooth hm
  rw [(c9 _ (ha.smooth hχ)).2.2.2.1 _ (ha.smooth hχ') hs]
  exact twist_congr V _ _ e.symm

private theorem twist_one (ha : IsLocalArtin h a) (V : WD h) (h1 : IsSmoothChar (1 : (w.adicCompletion E)ˣ →* ℂˣ)) :
    V.lpTwist ((1 : (w.adicCompletion E)ˣ →* ℂˣ).comp a) (ha.smooth h1) = V := by
  obtain ⟨-, -, -, -, -, -, -, -, c9⟩ := wDBasic E Ω A w h V
  exact (c9 _ (ha.smooth h1)).2.2.2.2.1 (MonoidHom.one_comp a)

private structure Gm (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a)
    (r : IrrGL (w.adicCompletion E) → WD h) : Prop where
  one : ∀ χ hχ, r (.ofChar χ hχ) = WD.lpOfChar h (χ.comp a) (ha.smooth hχ)
  tw : ∀ x, x.IsCusp → GoodCusp x → ∀ χ hχ, r (x.tw χ hχ) = (r x).lpTwist (χ.comp a) (ha.smooth hχ)
  par : (∃ (g : ℕ) (_ : Fact g.Prime) (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i) →
    ∀ y, y.IsCusp → DZ y → Par a y (r y)

variable {r : IrrGL (w.adicCompletion E) → WD h}

private theorem Gm.basic (H : Gm a ha r) {x : IrrGL (w.adicCompletion E)} (hc : x.IsCusp) (hg : GoodCusp x) :
    IsIrrWD (r x) ∧ (r x).lpDim = x.1 ∧
      ∀ ω, HasCentralChar x.rep ω → ∀ σ, ((r x).eig σ).prod = (ω (a σ) : ℂ) := by
  haveI := charZero_compl (E := E) w
  rcases good_cases hc hg with h1 | ⟨hq, y, χ, hχ, hy, hd, rfl⟩
  · obtain ⟨χ, hχ, rfl⟩ := ((clBasic _ x).2.2.2.2.1 h1).2
    obtain ⟨p1, p2, p3, p4, -⟩ := parOne E Ω A w h a ha χ hχ
    rw [H.one]
    refine ⟨p1, p2, fun ω hω σ => ?_⟩
    obtain ⟨ω₀, -, -, hu⟩ := (clBasic _ (IrrGL.ofChar χ hχ)).1
    rw [hu ω hω, ← hu χ p3]
    exact p4 σ
  · have P := H.par hq y hy hd
    obtain ⟨-, -, -, c4, -, -, -, -, c9⟩ := wDBasic E Ω A w h (r y)
    obtain ⟨t1, t2, t3, -⟩ := c9 _ (ha.smooth hχ)
    rw [H.tw y hy (goodCusp_self hq hd)]
    refine ⟨t2 P.irr, t1.trans (P.dim.trans ((clBasic _ y).2.1 χ hχ).1.symm), fun ω hω σ => ?_⟩
    obtain ⟨ω₀, -, h₀, -⟩ := (clBasic _ y).1
    obtain ⟨ω₁, -, -, hu⟩ := (clBasic _ (y.tw χ hχ)).1
    have h₁ := ((clBasic _ y).2.1 χ hχ).2.2.2.2 ω₀ h₀
    rw [hu ω hω, ← hu _ h₁, t3 σ, P.central ω₀ h₀ σ, P.dim]
    simp

private theorem Gm.dual (H : Gm a ha r) {x y : IrrGL (w.adicCompletion E)} (hc : x.IsCusp) (hg : GoodCusp x)
    (hd : DualCl x y) : r y = (r x).lpDual := by
  haveI := charZero_compl (E := E) w
  rcases good_cases hc hg with h1 | ⟨hq, u, χ, hχ, hu, hdz, rfl⟩
  · obtain ⟨χ, hχ, rfl⟩ := ((clBasic _ x).2.2.2.2.1 h1).2
    have hi := hχ.inv
    obtain ⟨-, -, -, -, -, -, -, p8, -⟩ := parOne E Ω A w h a ha χ hχ
    obtain ⟨d1, d2⟩ := p8 hi
    have := ((clBasic _ (IrrGL.ofChar χ hχ)).2.2.2.2.2.2 _ d1).2.2.2.2.1 y hd
    rw [this, H.one, H.one, d2]
  · obtain ⟨u', hu'⟩ := (clBasic _ u).2.2.2.2.2.1
    obtain ⟨-, f2, f3, -, -, f6, -⟩ := (clBasic _ u).2.2.2.2.2.2 u' hu'
    have hi := hχ.inv
    have ey := ((clBasic _ (u.tw χ hχ)).2.2.2.2.2.2 _ (f6 χ hχ hi)).2.2.2.2.1 y hd
    have hu'c : u'.IsCusp := f2.2 hu
    have hu'd : DZ u' := f3.2 hdz
    have P := H.par hq u hu hdz
    have P' := H.par hq u' hu'c hu'd
    obtain ⟨g, hgp, i, hi'⟩ := hq
    have D := parDual E Ω A w h a ha g i hi' u u' hu hdz hu' (r u) P
    have U := (parUniq E Ω A w h a ha g i hi' u' hu'c hu'd (r u') P').1 _ D
    have hq' : ∃ (g : ℕ) (_ : Fact g.Prime) (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i := ⟨g, hgp, i, hi'⟩
    rw [ey, H.tw u' hu'c (goodCusp_self hq' hu'd), H.tw u hu (goodCusp_self hq' hdz), ← U]
    obtain ⟨-, -, -, -, -, -, -, -, c9⟩ := wDBasic E Ω A w h (r u)
    have hcomp : χ⁻¹.comp a = (χ.comp a)⁻¹ := MonoidHom.ext fun _ => rfl
    have hs : GlobalTheory.WeilDeligne.IsSmooth (χ.comp a)⁻¹ := hcomp ▸ ha.smooth hi
    rw [(c9 _ (ha.smooth hχ)).2.2.2.2.2.1 hs]
    exact twist_congr _ _ _ hcomp

private theorem Gm.tw_inj (H : Gm a ha r) {u v : IrrGL (w.adicCompletion E)}
    (hq : ∃ (g : ℕ) (_ : Fact g.Prime) (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i)
    (hu : u.IsCusp) (hud : DZ u) (hv : v.IsCusp) (hvd : DZ v) {χ χ' : (w.adicCompletion E)ˣ →* ℂˣ}
    (hχ : IsSmoothChar χ) (hχ' : IsSmoothChar χ') (e : r (u.tw χ hχ) = r (v.tw χ' hχ')) :
    u.tw χ hχ = v.tw χ' hχ' := by
  haveI := charZero_compl (E := E) w
  have Pu := H.par hq u hu hud
  have Pv := H.par hq v hv hvd
  rw [H.tw u hu (goodCusp_self hq hud), H.tw v hv (goodCusp_self hq hvd)] at e
  have hi := hχ.inv
  have hψ : IsSmoothChar (χ' * χ⁻¹) := hχ'.mul hi
  have e2 := congrArg (fun V => V.lpTwist (χ⁻¹.comp a) (ha.smooth hi)) e
  rw [twist_twist ha _ hχ hi (hχ.mul hi), twist_twist ha _ hχ' hi hψ] at e2
  have e3 : r u = (r v).lpTwist ((χ' * χ⁻¹).comp a) (ha.smooth hψ) := by
    rw [← e2, twist_congr (r u) (ha.smooth (hχ.mul hi)) (ha.smooth (isSmoothChar_one))
      (by rw [mul_inv_cancel]), twist_one ha _ isSmoothChar_one]
  have hpos : 0 < (r v).lpDim := by rw [Pv.dim]; exact hv.1
  obtain ⟨-, -, -, -, -, -, -, -, c9⟩ := wDBasic E Ω A w h (r v)
  have wild := (c9 _ (ha.smooth hψ)).2.2.2.2.2.2.2 hpos Pv.tame (e3 ▸ Pu.tame)
  have tc : TameChar (χ' * χ⁻¹) := (tameArt E Ω A w h a ha _ hψ).2 wild
  obtain ⟨g, hgp, i, hi'⟩ := hq
  have T := parTw E Ω A w h a ha g i hi' v hv hvd (r v) Pv _ hψ tc
  rw [← e3] at T
  have hc' : (v.tw _ hψ).IsCusp := ((clBasic _ v).2.1 _ hψ).2.1.2 hv
  have hd' : DZ (v.tw _ hψ) := (twTame _ v _ hψ hv.1 hvd).2 tc
  have U := (parUniq E Ω A w h a ha g i hi' u hu hud (r u) Pu).2 _ hc' hd' T
  subst U
  rw [((clBasic _ v).2.1 _ hψ).2.2.2.1 χ hχ (hψ.mul hχ)]
  exact tw_congr v _ _ (by rw [inv_mul_cancel_right])

end SlopeTestRemainingChoices

theorem cuspEx : CuspEx := by
  intro E Ω _ _ _ _ _ A w h a ha
  haveI := charZero_compl (E := E) w
  classical
  obtain ⟨r₀, H1, H2, H3⟩ := goodMap E Ω A w h a ha
  have H : Gm a ha r₀ := ⟨H1, H2, H3⟩
  obtain ⟨e, he⟩ := expo E Ω A w h a ha
  haveI : Nonempty (WD h) := ⟨WD.lpZero h⟩
  choose! J hJ using junkEx E Ω A w h
  let r : IrrGL (w.adicCompletion E) → WD h := fun x => if GoodCusp x then r₀ x else (J x.1).lpTw (e x)
  have rg : ∀ x, GoodCusp x → r x = r₀ x := fun x hx => if_pos hx
  have rb : ∀ x, ¬ GoodCusp x → r x = (J x.1).lpTw (e x) := fun x hx => if_neg hx
  have two : ∀ x : IrrGL (w.adicCompletion E), x.IsCusp → ¬ GoodCusp x → 2 ≤ x.1 := by
    intro x hx hb
    have h0 := hx.1
    have h1 : x.1 ≠ 1 := fun h1 => hb (Or.inl h1)
    omega
  have hirr : ∀ x, x.IsCusp → IsIrrWD (r x) ∧ (r x).lpDim = x.1 := by
    intro x hx
    by_cases hg : GoodCusp x
    · rw [rg x hg]
      exact ⟨(H.basic hx hg).1, (H.basic hx hg).2.1⟩
    · rw [rb x hg]
      obtain ⟨j1, j2, -, -⟩ := hJ _ (two x hx hg)
      obtain ⟨-, -, -, -, -, -, -, -, c9⟩ := wDBasic E Ω A w h (J x.1)
      exact ⟨(c9 _ _).2.1 j1, ((c9 _ _).1).trans j2⟩
  have hcen : ∀ x : IrrGL (w.adicCompletion E), x.IsCusp → GoodCusp x → ∀ ω, HasCentralChar x.rep ω →
      ∀ σ, ((r x).eig σ).prod = (ω (a σ) : ℂ) := by
    intro x hx hg
    rw [rg x hg]
    exact (H.basic hx hg).2.2
  refine ⟨r, ⟨fun x hx => (hirr x hx).1, fun x hx => (hirr x hx).2, fun χ hχ => ?_, fun x hx s => ?_,
    fun x hx ω hω σ => ?_, fun x hx hg χ hχ => ?_, hcen, fun x y hx _ hg hd => ?_, fun x y hx hy hgy eq => ?_,
    fun x hx hg hd => ?_, fun x hx => ?_⟩⟩
  · rw [rg _ (Or.inl rfl)]
    exact H1 χ hχ
  · have hiff := ((clBasic _ x).2.1 _ (isSmoothChar_absPow (s : ℂ))).2.2.1
    by_cases hg : GoodCusp x
    · have hg' : GoodCusp (x.nu s) := hiff.2 hg
      rw [rg _ hg', rg x hg, lpTw_eq ha]
      exact H2 x hx hg _ _
    · have hg' : ¬ GoodCusp (x.nu s) := fun q => hg (hiff.1 q)
      have d : (x.nu s).1 = x.1 := ((clBasic _ x).2.1 _ (isSmoothChar_absPow (s : ℂ))).1
      rw [rb _ hg', rb x hg, d, (he x hx.1).1 s, WD.lpTw_add]
  · by_cases hg : GoodCusp x
    · rw [hcen x hx hg ω hω σ]
    · rw [rb x hg]
      exact (he x hx.1).2 ω hω _ (hJ _ (two x hx hg)).2.1 (hJ _ (two x hx hg)).2.2.1 σ
  · have hg' : GoodCusp (x.tw χ hχ) := ((clBasic _ x).2.1 χ hχ).2.2.1.2 hg
    rw [rg _ hg', rg x hg]
    exact H2 x hx hg χ hχ
  · have hg' : GoodCusp y := ((clBasic _ x).2.2.2.2.2.2 y hd).2.2.2.1.2 hg
    rw [rg y hg', rg x hg]
    exact H.dual hx hg hd
  · have hd : x.1 = y.1 := by rw [← (hirr x hx).2, ← (hirr y hy).2, eq]
    rw [rg y hgy] at eq
    by_cases hgx : GoodCusp x
    · rw [rg x hgx] at eq
      by_cases h1 : y.1 = 1
      · obtain ⟨χ', hχ', rfl⟩ := ((clBasic _ y).2.2.2.2.1 h1).2
        obtain ⟨χ, hχ, rfl⟩ := ((clBasic _ x).2.2.2.2.1 (hd.trans h1)).2
        rw [H1, H1] at eq
        have p := (parOne E Ω A w h a ha χ hχ).2.2.2.1
        have q := (parOne E Ω A w h a ha χ' hχ').2.2.2.1
        have key : χ = χ' := by
          refine MonoidHom.ext fun u => ?_
          obtain ⟨σ, rfl⟩ := ha.surj u
          refine Units.ext ?_
          rw [← p σ, ← q σ, eq]
        subst key
        rfl
      · rcases good_cases hy hgy with h1' | ⟨hq, v, χ', hχ', hv, hvd, rfl⟩
        · exact absurd h1' h1
        · rcases good_cases hx hgx with h1' | ⟨-, u, χ, hχ, hu, hud, rfl⟩
          · exact absurd (hd.symm.trans h1') h1
          · exact H.tw_inj hq hu hud hv hvd hχ hχ' eq
    · exfalso
      have hx2 := two x hx hgx
      rw [rb x hgx] at eq
      rcases good_cases hy hgy with h1' | ⟨hq, v, χ, hχ, hv, hvd, rfl⟩
      · omega
      · rw [H2 v hv (goodCusp_self hq hvd) χ hχ] at eq
        have e2 := congrArg (fun V => V.lpTw (-(e x))) eq
        rw [WD.lpTw_add, add_neg_cancel, WD.lpTw_zero, lpTw_eq ha,
          twist_twist ha _ hχ (isSmoothChar_absPow _) (hχ.mul (isSmoothChar_absPow _))] at e2
        exact (hJ _ hx2).2.2.2 hq (r₀ v) _ _ (H3 hq v hv hvd).tame e2
  · rcases good_cases hx hg with h1 | ⟨hq, -, -, -, -, -, -⟩
    · obtain ⟨χ, hχ, rfl⟩ := ((clBasic _ x).2.2.2.2.1 h1).2
      obtain ⟨-, -, -, -, p5, p6, -⟩ := parOne E Ω A w h a ha χ hχ
      rw [rg _ hg, H1]
      exact (p6 (p5.1 hd)).tame
    · rw [rg x hg]
      exact (H3 hq x hx hd).tame
  · intro g _ i hi n hn D R hR θ hθ τ hτ hN σ hσ hInf
    subst hσ
    have hd : DZ (cls σ) := DiscreteGroups.sglob.DzType.lDepth E w g i hi n τ σ hInf
    have hq : ∃ (g : ℕ) (_ : Fact g.Prime) (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i := ⟨g, inferInstance, i, hi⟩
    rw [rg _ (goodCusp_self hq hd)]
    exact (H3 hq _ hx hd).type g i hi n hn D R hR θ hθ τ hτ hN σ rfl hInf

end UpperTheory.Zero.LLC

end
