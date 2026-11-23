import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsThClsDGalRul
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsReducedIntegralBasisHarmonicPolynomials
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisConjCoverFunctionEqConstMulConjTupleStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjFourierCoefficientsConjugateTuplesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisConjClassScalarsAndVolumeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoefficientMapCommutesFieldAutomorphismStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.GalEqCls

theorem isThClsD_transfer {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
    {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {n : ℕ}
    {d d' : Formalism.L2.Pj.DeltaDat Xo c n} (hd : d' = d)
    {Cl Cl' : Type} [Fintype Cl] [Fintype Cl'] (e : Cl ≃ Cl')
    (w : Cl → (Fin n → LevQ Dw d.l₂) → c.F) (w' : Cl' → (Fin n → LevQ Dw d'.l₂) → c.F)
    (hw : ∀ k, HEq (w k) (w' (e k)))
    (La : Cl → GenLat E n) (La' : Cl' → GenLat E n) (hLa : ∀ k, La' (e k) = La k)
    (Nc : Cl → ℕ) (Nc' : Cl' → ℕ) (hNc : ∀ k, Nc' (e k) = Nc k)
    (gam : Cl → ℕ) (gam' : Cl' → ℕ) (hgam : ∀ k, gam' (e k) = gam k)
    (vol : c.F) (ep : Cl → c.F) (ep' : Cl' → c.F) (hep : ∀ k, ep' (e k) = ep k)
    {Vs : Type} [AddCommGroup Vs] [Module c.F Vs] (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F)
    (x : Cl → Vs) (x' : Cl' → Vs) (hx : ∀ k, x' (e k) = x k) (f : Rul Xo c)
    (h : IsThClsD Xo c d w La Nc gam vol ep io x f) : IsThClsD Xo c d' w' La' Nc' gam' vol ep' io x' f := by
  subst hd
  intro k _ _ A A₂ hk y y₂ hy
  obtain ⟨vc, hvc, he⟩ := @h k _ _ A A₂ hk y y₂ hy
  refine ⟨fun cl => vc (e.symm cl), fun cl => ?_, ?_⟩
  · obtain ⟨k', rfl⟩ := e.surjective cl
    dsimp only
    rw [e.symm_apply_apply, ← eq_of_heq (hw k'), hLa, hNc, hx]
    exact hvc k'
  · rw [he]
    congr 1
    rw [← e.sum_comp]
    refine Finset.sum_congr rfl fun k' _ => ?_
    dsimp only
    rw [e.symm_apply_apply, hgam, hep]

theorem galRul_isSum : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (τ : ℂ ≃+* ℂ) (ta : M.c'.F ≃+* M.c'.F), (∀ a : M.c'.F, ((ta a : M.c'.F) : ℂ) = τ (a : ℂ)) → FixBase T R i τ → GlobalTheory.CompRat.CurveOver T.Q.H M.c'.F 1 → (∀ t x, ((R.xi (tup t) x : Circle) : ℂ) ∈ M.c'.F) → ∃ (hf : Fixes M.c' ta) (k0 : ℂ), IsRoot1 k0 ∧ ∀ (a b : Tp) (e : M.Cl' a ≃ M.Cl' b), SameCover M a b e → ConjTup R τ (tup a) (tup b) → ∃ (u : M.c'.F) (s : (AE D)ˣ), (u : ℂ) = k0 * ((R.xi (tup b) s : Circle) : ℂ) ∧ ∀ (xs : M.Cl' a → VsV D i M.c'.F) (xs' : M.Cl' b → VsV D i M.c'.F), (∀ k, (xs' (e k) : Pol M.c'.F D.what₂.Tau (Vc D i).rank) = MvPolynomial.map (ta : M.c'.F →+* M.c'.F) (xs k : Pol M.c'.F D.what₂.Tau (Vc D i).rank)) → ∀ f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) M.c' (wtA (κ i)) (Vc D i).rank, GlobalTheory.OneMapAll.IsSum M a xs f → u • galRul hf f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) M.c' (wtA (κ i)) (Vc D i).rank ∧ GlobalTheory.OneMapAll.IsSum M b xs' (u • galRul hf f) := by
  intro hC D G _ _ Pl0 T0 A T _ R F κ v₀ hcore hFW i Tp tup M hP τ ta hta hfix hcurve hxi
  have hf : Fixes M.c' ta := ⟨fun φ x => Subtype.ext (by rw [hta]; exact hfix.host φ x),
    fun a => Subtype.ext (by rw [hta]; exact hfix.core ⟨a, T.Q.c.le a.2⟩)⟩
  obtain ⟨k0, hk0, hcxi⟩ := GlobalTheory.T.galoisConj_coverFunction_eq_const_mul_conjTuple D G Pl0 T0 A T R F κ v₀ hcore hFW i Tp tup M hP τ ta hta hfix hcurve hxi
  have hk0ne : k0 ≠ 0 := by
    rintro rfl
    obtain ⟨n, hn, hkn⟩ := hk0
    rw [zero_pow hn.ne'] at hkn
    exact zero_ne_one hkn
  refine ⟨hf, k0⁻¹, ?_, ?_⟩
  · obtain ⟨n, hn, hkn⟩ := hk0
    exact ⟨n, hn, by rw [inv_pow, hkn, inv_one]⟩
  intro a b e hsame hconj
  obtain ⟨⟨cx, hcx⟩, hU, hdict, -, -, hcl⟩ := id hsame
  obtain ⟨h₂, ka, s1, hka, hev⟩ := hcxi a b cx hcx hU hdict hconj
  obtain ⟨u, s2, w', hu, hw'eq, hw⟩ :=
    GlobalTheory.T.conj_fourierCoefficients_conjugate_tuples D G Pl0 T0 A T R F κ v₀ hcore hFW i Tp tup M hP τ ta hta hfix a b e hsame hconj
  obtain ⟨hvol, hep⟩ := GlobalTheory.T.galoisConj_classScalars_and_volume D G Pl0 T0 A T R F κ v₀ hcore hFW i Tp tup M hP τ ta hta hfix a b e hsame hconj
  have hkane : ka ≠ 0 := fun h0 => by
    have h1 : ((ka : ℂ)) = 0 := by rw [h0]; rfl
    rw [hka] at h1
    exact mul_ne_zero hk0ne (Circle.coe_ne_zero _) h1
  have hune : u ≠ 0 := fun h0 => by
    have h1 : ((u : ℂ)) = 0 := by rw [h0]; rfl
    rw [hu] at h1
    exact Circle.coe_ne_zero _ h1
  refine ⟨(ka * u)⁻¹, (s1 * s2)⁻¹, ?_, ?_⟩
  · have e1 : (((ka * u)⁻¹ : M.c'.F) : ℂ) = ((ka : ℂ) * (u : ℂ))⁻¹ := by push_cast; rfl
    rw [e1, hka, hu, map_inv, map_mul, Circle.coe_inv, Circle.coe_mul]
    ring
  intro xs xs' hxs f hfs hsum
  obtain ⟨-, cga, hio⟩ := hP.io
  have hio' := fun v => GlobalTheory.HarmBasis.mem_HHa_of_mem_span subset_rfl (hio.2.2.1 ▸ LinearMap.mem_range_self M.io v)
  obtain ⟨hLev, -, hN⟩ := hP.cov a
  have hδ := hLev.2.2.2.2.2.2.2.1
  have key := GlobalTheory.GalTw.isThClsD_galRul hC _ _ _ _ (T.Q.Xo ((i : ℕ) + 1)) M.c' ta hf (Vc D i).rank (M.dδ a) h₂ hN hδ cx
    ka u hkane hune hev (M.Cl' a) (M.w a) w' (M.La a) (M.Nc a) (M.gam a) (M.vol a) (M.ep a) (VsV D i M.c'.F) M.io
    (wtA (κ i)) hio' hw xs (fun k => xs' (e k))
    (fun k => GlobalTheory.T.coefficientMap_commutes_fieldAutomorphism D G Pl0 T0 A T R F κ v₀ hcore hFW i Tp tup M hP τ ta hta hfix (xs k) (xs' (e k)) (hxs k))
    (Vc D i).rank f hfs hsum
  refine ⟨key.1, ?_⟩
  have key2 := key.2
  rw [hvol] at key2
  exact isThClsD_transfer hcx e w' (M.w b) hw'eq (M.La a) (M.La b) (fun k => (hcl k).2.1) (M.Nc a) (M.Nc b)
    (fun k => (hcl k).2.2.1) (M.gam a) (M.gam b) (fun k => (hcl k).2.2.2) (M.vol b) (fun k => ta (M.ep a k)) (M.ep b)
    (fun k => (hep k).symm) M.io (fun k => xs' (e k)) xs' (fun _ => rfl) _ key2

end GlobalTheory.GalEqCls
