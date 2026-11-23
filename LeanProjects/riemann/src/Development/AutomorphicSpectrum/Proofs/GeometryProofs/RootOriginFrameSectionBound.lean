import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LabelSigBijective
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegralityStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Formalism.LocalToGlobal.ProjectiveLattices.ChartWD
import Formalism.LocalToGlobal.ProjectiveLattices.ReadAlg
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd

section IntWeight

variable {K : Type} [Field K] {ι : Type}
  {pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type}
  {mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T], (S →ₐ[K] T) → pts S → pts T → Prop}
  {borR : ∀ {S : Type} [CommRing S] [Algebra K S], (ι → Sˣ) → pts S → pts S → Prop}

theorem evalAt_bor_zpow [Fintype ι] (h : BorChart pts mapR borR) (e : ι → ℤ) {f : Rules pts}
    (hf : IsNatural pts mapR f)
    (hw : ∀ (p : TRing K) (t : ι → (p.R)ˣ) (y y' : pts p.R), borR t y y' →
      f p y' = ((∏ i, t i ^ e i : (p.R)ˣ) : p.R) * f p y)
    (S : Type) [CommRing S] [Algebra K S] (t : ι → Sˣ)
    (y y' : pts S) (hy : FromTest pts mapR y) (hy' : FromTest pts mapR y') (hb : borR t y y') :
    evalAt pts mapR f y' = ((∏ i, t i ^ e i : Sˣ) : S) * evalAt pts mapR f y := by
  unfold evalAt
  rw [dif_pos hy, dif_pos hy']
  apply eq_of_locM (K := K)
  intro m hm
  obtain ⟨A, u, c, c', B, uB, uB', tB, π, π', cB, hc, hc', hπ, hπ', hbB, e1, e2, e3⟩ := h S t y y' hb m
  rw [map_mul, chartAt_val hf hc' hy'.choose_spec.choose_spec.choose_spec,
    chartAt_val hf hc hy.choose_spec.choose_spec.choose_spec, ← e1, ← e2, AlgHom.comp_apply, AlgHom.comp_apply,
    ← hf A B π u uB hπ, ← hf A B π' u uB' hπ', hw B tB uB uB' hbB, map_mul]
  congr 1
  have key : ∀ i, Units.map cB.toRingHom.toMonoidHom (tB i) = Units.map (locM K m).toRingHom.toMonoidHom (t i) :=
    fun i => Units.ext (by simpa using e3 i)
  have h1 : cB ((∏ i, tB i ^ e i : (B.R)ˣ) : B.R) =
      ((Units.map cB.toRingHom.toMonoidHom (∏ i, tB i ^ e i) : (Localization.AtPrime m)ˣ) : Localization.AtPrime m) := rfl
  have h2 : locM K m ((∏ i, t i ^ e i : Sˣ) : S) =
      ((Units.map (locM K m).toRingHom.toMonoidHom (∏ i, t i ^ e i) : (Localization.AtPrime m)ˣ) :
        Localization.AtPrime m) := rfl
  rw [h1, h2, map_prod, map_prod]
  simp_rw [map_zpow, key]

end IntWeight

section Abs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {c : Coeff l}

def absHom (p : ℕ) [hp : Fact p.Prime] (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (e : ℕ) : T.Fr →*₀ ℝ where
  toFun := absT p la T e
  map_zero' := by simp [absT]
  map_one' := by
    have h1 : vV T.V (1 : T.Fr) = 0 := by simp [vV]
    simp [absT, h1]
  map_mul' x y := by
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
    by_cases hx : x = 0
    · simp [absT, hx]
    by_cases hy : y = 0
    · simp [absT, hy]
    simp only [absT, if_neg hx, if_neg hy, if_neg (mul_ne_zero hx hy)]
    rw [← Real.rpow_add hp0, vV_mul hx hy]
    congr 1
    push_cast
    ring

theorem absHom_apply (p : ℕ) [Fact p.Prime] (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (e : ℕ) (x : T.Fr) :
    absHom p la T e x = absT p la T e x := rfl

theorem absT_of_nval {p : ℕ} [hp : Fact p.Prime] {la : HeightOneSpectrum (𝓞 c.F)} {T : CDVR} {e : ℕ} (he : 0 < e)
    (hr : 0 < ramOverZ la) (t : Ix Dw → T.Frˣ) (n : Ix Dw → ℤ) {g w : T.Fr}
    (hg : g = ((∏ i, t i ^ n i : T.Frˣ) : T.Fr) * w) {s : ℝ}
    (hs : nval T.V e g = ((ramOverZ la * s : ℝ) : EReal)) :
    absT p la T e w = (p : ℝ) ^ (-s) * ∏ j, tOf p la T e t j ^ n j := by
  have hg0 : g ≠ 0 := by
    rintro rfl
    rw [nval_zero] at hs
    exact EReal.coe_ne_top _ hs.symm
  have he' : (e : ℝ) ≠ 0 := by exact_mod_cast he.ne'
  have hr' : (ramOverZ la : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have hv : (vV T.V g : ℝ) / e = ramOverZ la * s := by
    rw [nval_of_ne hg0] at hs
    exact_mod_cast hs
  have hag : absT p la T e g = (p : ℝ) ^ (-s) := by
    unfold absT
    rw [if_neg hg0]
    congr 1
    rw [← div_div, hv]
    field_simp
  have hu : absT p la T e ((∏ i, t i ^ n i : T.Frˣ) : T.Fr) = ∏ j, (tOf p la T e t j ^ n j)⁻¹ := by
    rw [Units.coe_prod, ← absHom_apply, map_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, absHom_apply, tOf, inv_zpow, inv_inv]
  have hm : absT p la T e g = absT p la T e ((∏ i, t i ^ n i : T.Frˣ) : T.Fr) * absT p la T e w := by
    rw [hg, ← absHom_apply, map_mul]
    rfl
  have hne : ∀ j, tOf p la T e t j ^ n j ≠ 0 := fun j => zpow_ne_zero _ (tOf_pos la T e t j).ne'
  have hP : (∏ j, tOf p la T e t j ^ n j) * ∏ j, (tOf p la T e t j ^ n j)⁻¹ = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun j _ => mul_inv_cancel₀ (hne j)
  rw [← hag, hm, hu]
  linear_combination (-absT p la T e w) * hP

end Abs

theorem readsZ_of_isIntPt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or), ∀ (A : Subring RM.Ω) (p : ℕ) [Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p) (ev : A →+* PadicAlgCl p), z ∈ Small.algPts p (mCoordIdeal RM.y) → (∀ x : A, Small.HasVal RM.y 0 (x : RM.Ω) z (ev x)) → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (evT : A →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), FinRd.IsIntPt Fr A ev la T io e y evT zT t → ∀ x : (Ref.pjSys Xo c).Pt la, (∀ f, (Ref.pjSys Xo c).val x f = nval T.V e (evI y f)) → FinRd.ReadsZ Fr z x (FinRd.tOf p la T e t) := by
  intro E _ _ _ H Dw l Xo c O _ β Y SS RM Sys Fx Or Fr A p _ z ev hz hev la T io e y evT zT t hI x hx a f hf
  letI := io.toAlgebra
  letI := Small.cstAlg Or
  obtain ⟨hp, hO, -, -, -, hn, ⟨q, φ, ψ, yq, hφ, hψ, hA⟩, hb⟩ := hI
  have hS : ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeSt := GlobalTheory.firstFiveLaws.1.secBaseChange
  have hWD := (GlobalTheory.T.framedModuli_algebraicLaws_chart_weight_integrality hS E H Dw l Xo c).2.2.1
  have hrd : Fr.rd f = φ (f q yq) := Fr.rd_eq_of_frMap hWD hf.1 q φ yq hφ
  obtain ⟨hmem, hψe⟩ := hA (f q yq)
  have hm : Fr.rd f ∈ A := hrd ▸ hmem
  have hft : Formalism.L2.Pj.FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) zT := ⟨q, ψ, yq, hψ⟩
  have hzT : evR Xo c f zT = ψ (f q yq) := by
    unfold evR evalAt
    rw [dif_pos hft]
    exact hWD f hf.1 T.Fr _ q _ ψ _ yq zT hft.choose_spec.choose_spec.choose_spec hψ
  have hbor : evI y f = ((∏ i, t i ^ exZ Dw a i : T.Frˣ) : T.Fr) * evR Xo c f zT :=
    evalAt_bor_zpow (GlobalTheory.T.framedModuli_algebraicLaws_chart_weight_integrality hS E H Dw l Xo c).2.1 (exZ Dw a) hf.1
      (fun p t y y' hb => by rw [hf.2 p t y y' hb, Units.coe_prod]) T.Fr t zT y.1 hft y.2.1 hb
  have hnorm : ‖ev ⟨Fr.rd f, hm⟩‖ = absT p la T e (evR Xo c f zT) := by
    rw [hn, hzT, hψe]
    exact congrArg (absT p la T e) (congrArg evT (Subtype.ext hrd))
  refine ⟨ev ⟨Fr.rd f, hm⟩, hev ⟨Fr.rd f, hm⟩, fun htop => ?_, fun s hs => ?_⟩
  · have h0 : evI y f = 0 := by
      by_contra hne
      rw [hx, nval_of_ne hne] at htop
      exact EReal.coe_ne_top _ htop
    have hw : evR Xo c f zT = 0 := by
      rw [h0] at hbor
      exact (mul_eq_zero.1 hbor.symm).resolve_left (Units.ne_zero _)
    rw [← norm_eq_zero, hnorm, hw]
    simp [absT]
  · rw [hnorm]
    exact absT_of_nval hO.1 (ram_pos hp) t (exZ Dw a) hbor (by rw [← hx]; exact hs)

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd
