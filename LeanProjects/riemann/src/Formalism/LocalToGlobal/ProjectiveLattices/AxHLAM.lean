import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
import Formalism.LocalToGlobal.ProjectiveLattices.XcLat
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.WeightedPrimeSumBound

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0
  Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {Tc : Core D} (hL : LawsCore Tc) (j : ℕ)

def ProdInLat (ka : WeightFamilies.Wt D j) {N : ℕ} (wR : Fin (N + 1) → Tc.R j) (n : ℕ) : Prop :=
  ∀ s : Fin n → Fin (N + 1), ∃ F : (recB hL).Cusp j ka, F ∈ (recB hL).Mlat j ka ∧ (F : Tc.R j) = ∏ k, wR (s k)

def SupPTGe (h : GenFrEx (Tc.Q.Xo j) Tc.Q.c)
    (fn : ∀ σ : Tc.Q.c.F →+* ℂ, FrPt (Tc.Q.Xo j) Tc.Q.c (CAt σ) → Ix (Tc.Q.Dw j) → ℝ)
    (yP : ∀ Z : Comp (Tc.Q.Xo j) Tc.Q.c, ∀ P : Om Z →+* ℂ, FrPt (Tc.Q.Xo j) Tc.Q.c (CAt (sgOf P)))
    (ka : WeightFamilies.Wt D j) : Prop :=
  ∀ (Z : Comp (Tc.Q.Xo j) Tc.Q.c) (F : (recB hL).Cusp j ka), F ∈ (recB hL).Mlat j ka →
    evC h Z (F : Tc.R j) ≠ 0 →
    ∃ F' ∈ (recB hL).Mlat j ka, F' ≠ 0 ∧ ∀ sg : Tc.Q.c.F →+* ℂ,
      (recB hL).supN j ka sg F' ≤
        ⨆ P : PT (Ω := Om Z) sg, nrmC fn (yP Z) (wtZ (wtA ka) ka.n) (valC h (wtA ka) ka.n (F : Tc.R j) Z) P

section Ev

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem evC_prod (h : GenFrEx Xo c) (hgt : GenFromTest Xo c h) (Z : Comp Xo c) {n : ℕ} (f : Fin n → Rul Xo c) :
    evC h Z (∏ k, f k) = ∏ k, evC h Z (f k) := by
  let φ : Rul Xo c →* Om Z :=
    { toFun := evC h Z
      map_one' := evalAt_one _ _ _ (hgt Z)
      map_mul' := fun a b => evalAt_mul _ _ a b _ }
  exact map_prod φ f Finset.univ

theorem evC_add (h : GenFrEx Xo c) (Z : Comp Xo c) (f g : Rul Xo c) :
    evC h Z (f + g) = evC h Z f + evC h Z g := evalAt_add _ _ f g _

theorem evC_zero (h : GenFrEx Xo c) (Z : Comp Xo c) : evC h Z (0 : Rul Xo c) = 0 := evalAt_zero _ _ _

theorem evC_smul (h : GenFrEx Xo c) (Z : Comp Xo c) (a : c.F) (f : Rul Xo c) :
    evC h Z (a • f) = algebraMap c.F (Om Z) a * evC h Z f := evalAt_smul _ _ a f _

theorem smul_single_AC (Z : Comp Xo c) (a : 𝓞 c.F) (G : WTZ E) (e : Om Z) :
    a • (AddMonoidAlgebra.single G e : AC Z) = AddMonoidAlgebra.single G (algebraMap c.F (Om Z) (a : c.F) * e) := by
  first
  | rw [AddMonoidAlgebra.smul_single]
  | erw [AddMonoidAlgebra.smul_single]
  rw [Algebra.smul_def]
  congr 1

theorem valC_smul (h : GenFrEx Xo c) (a : 𝓞 c.F) (u : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c) (Z : Comp Xo c) :
    valC h u n ((a : c.F) • f) Z = a • valC h u n f Z := by
  simp only [valC, evC_smul]
  exact (smul_single_AC Z a _ _).symm

end Ev

set_option maxHeartbeats 1000000 in
theorem coe_smul_cusp {D : D7} {Tc : Core D} (hL : LawsCore Tc) (j : ℕ) (ka : WeightFamilies.Wt D j)
    (a : 𝓞 Tc.Q.c.F) (F : (recB hL).Cusp j ka) :
    ((a • F : (recB hL).Cusp j ka) : Tc.R j) = ((a : Tc.Q.c.F) • (F : Tc.R j)) := by
  rfl

def LamConst (large₂ : SizeData₂ D) (C A : ℝ) (ka : WeightFamilies.Wt D j) (P : ℝ) (n : ℕ) (s : ℝ) : Prop :=
  WeightFamilies.PP0v D large₂ C A * (1 + Real.log ka.size) * ka.size ≤ P * n * s

theorem htLAM_of [Fintype (Comp (Tc.Q.Xo j) Tc.Q.c)] (h : GenFrEx (Tc.Q.Xo j) Tc.Q.c)
    (δ : ∀ Z : Comp (Tc.Q.Xo j) Tc.Q.c, AddValuation (Om Z) (WithTop ℤ) → Ix (Tc.Q.Dw j) → ℤ)
    (fn : ∀ σ : Tc.Q.c.F →+* ℂ, FrPt (Tc.Q.Xo j) Tc.Q.c (CAt σ) → Ix (Tc.Q.Dw j) → ℝ)
    (yP : ∀ Z : Comp (Tc.Q.Xo j) Tc.Q.c, ∀ P : Om Z →+* ℂ, FrPt (Tc.Q.Xo j) Tc.Q.c (CAt (sgOf P)))
    (Dd N T i g0 : ℕ) (cc : ℝ) (uL uF uka ude uet uta1 uta2 : WtR D.host.E)
    (wR : Fin (N + 1) → Tc.R j) (jc : Comp (Tc.Q.Xo j) Tc.Q.c → Fin (N + 1))
    (np : ℕ) (thpR : Fin np → Tc.R j) (n0 : ℕ) (th0R : Fin n0 → Tc.R j) (uF0 : WtR D.host.E)
    (nk : ℕ) (thkR : Fin nk → Tc.R j) (MR : Set (Tc.R j)) (etR ta1R ta2R : Tc.R j)
    (nu : HeightOneSpectrum (𝓞 Tc.Q.c.F) → ℝ)
    (ip : (Tc.Q.c.F →+* ℂ) → (∀ Z : Comp (Tc.Q.Xo j) Tc.Q.c, AC Z) → (∀ Z : Comp (Tc.Q.Xo j) Tc.Q.c, AC Z) → ℂ)
    (wsize : WTZ D.host.E → ℝ) (DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r : ℝ)
    (large₂ : SizeData₂ D) (C A : ℝ) (ka : WeightFamilies.Wt D j)
    (hgt : GenFromTest (Tc.Q.Xo j) Tc.Q.c h)
    (hka : wtZ (wtA ka) ka.n = (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).n96 • wtZ uL.1 uL.2)
    (hlam : LAMwAt large₂ (recB hL) j ka C A)
    (hprod : ProdInLat hL j ka wR (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).n96)
    (hsup : SupPTGe hL j h fn yP ka)
    (hc : LamConst j large₂ C A ka PP0' (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).n96 (wsize (wtZ uL.1 uL.2))) :
    (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).HtLAM := by
  classical
  intro Z g hg hgZ
  obtain ⟨F, hFM, rfl⟩ : ∃ F : (recB hL).Cusp j ka, F ∈ (recB hL).Mlat j ka ∧
      g = valC h (wtA ka) ka.n (F : Tc.R j) := by
    clear hgZ
    induction hg using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨s, rfl⟩ := hx
      obtain ⟨F, hFM, hF⟩ := hprod s
      refine ⟨F, hFM, ?_⟩
      funext Z
      rw [hF]
      beta_reduce
      rw [Finset.prod_apply]
      change ∏ k, AddMonoidAlgebra.single (wtZ uL.1 uL.2) (evC h Z (wR (s k))) =
        AddMonoidAlgebra.single (wtZ (wtA ka) ka.n) (evC h Z (∏ k, wR (s k)))
      rw [AddMonoidAlgebra.prod_single, hka, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        evC_prod h hgt Z]
    | zero =>
      refine ⟨0, Submodule.zero_mem _, ?_⟩
      funext Z
      simp [valC, evC_zero]
    | add x y _ _ hx hy =>
      obtain ⟨F, hFM, rfl⟩ := hx
      obtain ⟨G, hGM, rfl⟩ := hy
      refine ⟨F + G, Submodule.add_mem _ hFM hGM, ?_⟩
      funext Z
      simp [valC, evC_add, AddMonoidAlgebra.single_add]
    | smul a x _ hx =>
      obtain ⟨F, hFM, rfl⟩ := hx
      refine ⟨a • F, Submodule.smul_mem _ a hFM, ?_⟩
      funext Z
      show a • valC h (wtA ka) ka.n (F : Tc.R j) Z = valC h (wtA ka) ka.n ((a • F : (recB hL).Cusp j ka) : Tc.R j) Z
      rw [coe_smul_cusp hL j ka a F]
      exact (valC_smul h a _ _ _ Z).symm
  have hev : evC h Z (F : Tc.R j) ≠ 0 := fun h0 => hgZ (by simp [valC, h0])
  obtain ⟨F', hF'M, hF'0, hle⟩ := hsup Z F hFM hev
  have hl := hlam F' hF'M hF'0
  refine (neg_le_neg hc).trans (hl.trans ?_)
  unfold WeightFamilies.meanLogSup meanK
  refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun sg _ => ?_) (Nat.cast_nonneg _)
  have hpos : 0 < (recB hL).supN j ka sg F' :=
    lt_of_le_of_ne ((recB hL).supN_nonneg _ _ _ _)
      (fun h0 => hF'0 (((recB hL).supN_eq_zero _ _ _ _).1 h0.symm))
  refine Real.log_le_log hpos ((hle sg).trans (le_of_eq ?_))
  change _ = ⨆ P : PT (Ω := Om Z) sg, nrmC fn (yP Z) (_ • wtZ uL.1 uL.2) _ P
  rw [hka]

end Formalism.L2.Pj
