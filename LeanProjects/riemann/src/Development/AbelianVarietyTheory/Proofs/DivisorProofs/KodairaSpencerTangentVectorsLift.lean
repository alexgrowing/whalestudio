import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKSIffKsRel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvRFrMapOfIsReduced
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeSpectrumDualNumberEq
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagTan

theorem le_preimage_of_trivSqZeroExt {L M : Type} [Field L] [AddCommGroup M] [Module L M] [Module Lᵐᵒᵖ M]
    [IsCentralScalar L M] {T : Scheme.{0}} (φ : TrivSqZeroExt L M →+* L) (hφ : ∀ a, φ a = a.fst)
    (x : Sp (TrivSqZeroExt L M) ⟶ T) (V : T.Opens) (h : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ V) : ⊤ ≤ x ⁻¹ᵁ V := by
  intro s _
  let q : PrimeSpectrum L := ⟨⊥, Ideal.isPrime_bot⟩
  have hp : (spMap φ) q = s := by
    refine PrimeSpectrum.ext (Ideal.ext fun a => ?_)
    change φ a ∈ (⊥ : Ideal L) ↔ a ∈ s.asIdeal
    rw [Ideal.mem_bot, hφ]
    constructor
    · intro ha
      refine s.2.mem_of_pow_mem 2 ?_
      rw [show a ^ 2 = 0 by
        rw [pow_two, show a = TrivSqZeroExt.inr a.snd from TrivSqZeroExt.ext ha rfl, TrivSqZeroExt.inr_mul_inr]]
      exact s.asIdeal.zero_mem
    · intro ha
      by_contra h0
      exact s.2.ne_top (s.asIdeal.eq_top_of_isUnit_mem ha (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (Ne.isUnit h0)))
  have h₁ : (spMap φ ≫ x) q ∈ V := h (Set.mem_univ _)
  exact hp ▸ h₁

theorem IsKS.sum_of_der : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {K : Type} [Field K] [Algebra c.F K] {y : FrPt Xo c K} (hy : KSIso (psiSet H) y)
    {ι : Type} [Fintype ι] {x : ι → (Sp (DualNumber K) ⟶ Xo.X)} (hx : ∀ a, GlobalTheory.FlagTan.IsTanX y (x a))
    {Mx : ι → HIx Dw (psiSet H) → K} (hM : ∀ a, GlobalTheory.FlagTan.IsKS (psiSet H) y (x a) (Mx a))
    {x' : Sp (DualNumber K) ⟶ Xo.X} (hx' : GlobalTheory.FlagTan.IsTanX y x') (m : ι → K)
    (h : ∀ (O : Xo.X.Opens) (f : Γ(Xo.X, O)) (h' : ⊤ ≤ x' ⁻¹ᵁ O) (hc : ∀ a, ⊤ ≤ x a ⁻¹ᵁ O),
      (evalPt x' O h' f).snd = ∑ a, m a * (evalPt (x a) O (hc a) f).snd), GlobalTheory.FlagTan.IsKS (psiSet H) y x' (∑ a, m a • Mx a) := by
  intro E _ _ _ H Dw l Xo c K _ _ y hy ι _ x hx Mx hM x' hx' m h
  obtain ⟨X, -, hXy, hX⟩ := hy
  have ex : ∀ a, x a = spMap (dir c (Mx a)).toRingHom ≫ X := fun a => ((hX _ (hx a)).2 _).1 (hM a)
  refine ((hX x' hx').2 _).2 ?_
  obtain ⟨U, hU, hpU, -⟩ := Opens.isBasis_iff_nbhd.1 Xo.X.isBasis_affineOpens
    (Opens.mem_top (y.x (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K)))
  have hyU : ⊤ ≤ y.x ⁻¹ᵁ U := fun s _ => by
    have : s = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K) := Subsingleton.elim _ _
    subst this
    exact hpU
  have hXU : ⊤ ≤ X ⁻¹ᵁ U :=
    le_preimage_of_trivSqZeroExt (TrivSqZeroExt.fstHom c.F K (HIx Dw (psiSet H) → K)).toRingHom (fun _ => rfl) X U
      (by rw [hXy]; exact hyU)
  have htan : ∀ z : Sp (DualNumber K) ⟶ Xo.X, IsTanX y z → ⊤ ≤ z ⁻¹ᵁ U := fun z hz =>
    le_preimage_of_trivSqZeroExt (red c K).toRingHom (fun _ => rfl) z U (by rw [hz.2]; exact hyU)
  have hev : ∀ (N : HIx Dw (psiSet H) → K) (z : Sp (DualNumber K) ⟶ Xo.X)
      (hz : z = spMap (dir c N).toRingHom ≫ X) (hzU : ⊤ ≤ z ⁻¹ᵁ U) (f : Γ(Xo.X, U)),
      evalPt z U hzU f = dir c N (evalPt X U hXU f) := by
    intro N z hz hzU f
    subst hz
    exact evalPt_spMap_comp _ X U hXU hzU f
  have hx'U := htan x' hx'
  have hcU : ∀ a, ⊤ ≤ x a ⁻¹ᵁ U := fun a => htan _ (hx a)
  set M'' : HIx Dw (psiSet H) → K := ∑ a, m a • Mx a
  have hzU : ⊤ ≤ (spMap (dir c M'').toRingHom ≫ X) ⁻¹ᵁ U := by
    intro s hs
    exact hXU (Set.mem_univ _)
  refine ext_evalPt hU hx'U hzU (RingHom.ext fun f => ?_)
  rw [hev M'' _ rfl hzU f]
  refine TrivSqZeroExt.ext ?_ ?_
  · have e1 := evalPt_spMap_comp (red c K).toRingHom x' U hx'U (by rw [hx'.2]; exact hyU) f
    have e2 := evalPt_spMap_comp (TrivSqZeroExt.fstHom c.F K (HIx Dw (psiSet H) → K)).toRingHom X U hXU
      (by rw [hXy]; exact hyU) f
    simp only [hx'.2, hXy] at e1 e2
    rw [fst_dir]
    exact e1.symm.trans e2
  · rw [h U f hx'U hcU, snd_dir]
    simp only [fun a => hev (Mx a) (x a) (ex a) (hcU a) f, snd_dir, M'', Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun k _ => by ring

end GlobalTheory.FlagTan
