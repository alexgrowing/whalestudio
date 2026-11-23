import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsAnalyticFrameOfAnalyticFibre
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SectionReadingExistsUniqueIsTheta
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnFrameA

namespace GlobalTheory.AnUniq

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

theorem exp_eq {S : Scheme.{0}} {G : Over S} [GrpObj G] {y : Sp ℂ ⟶ S} {g : ℕ}
    {e e' : (Fin g → ℂ) → (Over.mk y ⟶ G)} (he : ∀ z w, e (z + w) = e z * e w)
    (he' : ∀ z w, e' (z + w) = e' z * e' w)
    (hol : IsHolTo Set.univ (fun z => (e z).left)) (hol' : IsHolTo Set.univ (fun z => (e' z).left))
    (u : Fin g → (Sp (DualNumber ℂ) ⟶ G.left)) (hd : ∀ i, IsDerivAt0 (fun z => (e z).left) (Pi.single i 1) (u i))
    (hd' : ∀ i, IsDerivAt0 (fun z => (e' z).left) (Pi.single i 1) (u i)) : e = e' := by
  have h0 : e 0 = e' 0 := (HolHom.map_zero_eq_one he).trans (HolHom.map_zero_eq_one he').symm
  refine HolHom.eq_of_fderiv_eq he he' hol hol' fun U hU f =>
    ContinuousLinearMap.coe_injective ((Pi.basisFun ℂ _).ext fun i => ?_)
  rw [Pi.basisFun_apply]
  exact (((HolHom.isDerivAt0_iff _ _ _).1 (hd i)).2 U hU f).symm.trans
    (((HolHom.isDerivAt0_iff _ _ _).1 (hd' i)).2 U (h0 ▸ hU :) f)

theorem fr_eq {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ}
    (Φ Φ' : AnFr A L x0 g) (he : ∀ z, Φ'.e z = Φ.e z) (hH : ∀ z w, hermForm Φ'.Hm z w = hermForm Φ.Hm z w)
    (j : L.L.ι) (z : Fin g → ℂ) (hj : ⊤ ≤ (Φ.e z).left ⁻¹ᵁ L.L.U j) : Φ.fr j z = Φ'.fr j z := by
  choose c hc using Φ.exists_chart_e
  have ne' : ∀ j z, ⊤ ≤ (Φ.e z).left ⁻¹ᵁ L.L.U j → Φ'.fr j z ≠ 0 := fun j z h => Φ'.fr_ne j z (by rw [he]; exact h)
  let q : (Fin g → ℂ) → ℂ := fun z => Φ.fr (c z) z / Φ'.fr (c z) z
  have key : ∀ j z, ⊤ ≤ (Φ.e z).left ⁻¹ᵁ L.L.U j → q z = Φ.fr j z / Φ'.fr j z := fun j z h => by
    have hz : ⊤ ≤ (Φ.e z).left ⁻¹ᵁ (L.L.U j ⊓ L.L.U (c z)) := fun p hp => ⟨h hp, hc z hp⟩
    have h1 := Φ.fr_g j (c z) z hz
    have h2 := Φ'.fr_g j (c z) z (by rw [he]; exact hz)
    rw [he] at h2
    rw [h1, h2, mul_div_mul_left _ _ (left_ne_zero_of_mul (h1 ▸ Φ.fr_ne j z h))]
  have hq : Differentiable ℂ q := fun z0 => by
    have hO : IsOpen {z | ⊤ ≤ (Φ.e z).left ⁻¹ᵁ L.L.U (c z0)} := (Φ.hol (L.L.U (c z0)) 0).1
    have h' : DifferentiableOn ℂ (Φ'.fr (c z0)) {z | ⊤ ≤ (Φ.e z).left ⁻¹ᵁ L.L.U (c z0)} := by
      simpa only [he] using Φ'.fr_hol (c z0)
    have hd : DifferentiableOn ℂ q {z | ⊤ ≤ (Φ.e z).left ⁻¹ᵁ L.L.U (c z0)} :=
      ((Φ.fr_hol (c z0)).mul (h'.inv fun z hz => ne' _ z hz)).congr fun z hz =>
        (key _ z hz).trans (div_eq_mul_inv _ _)
    exact hd.differentiableAt (hO.mem_nhds (hc z0))
  have hper : ∀ z (a : Φ.lat), ‖q (z + Φ.lat.subtype a)‖ = ‖q z‖ := fun z a => by
    have ha' : (a : Fin g → ℂ) ∈ Φ'.lat := (Φ'.e_ker _).1 ((he _).trans ((Φ.e_ker _).2 a.2))
    have h : ⊤ ≤ (Φ.e (z + a)).left ⁻¹ᵁ L.L.U (c z) := by rw [Φ.e_add_lat a.2]; exact hc z
    have h1 := Φ.fr_per a a.2 (c z) z (hc z)
    have h2 := Φ'.fr_per a ha' (c z) z (by rw [he]; exact hc z)
    rw [hH, hH] at h2
    change ‖q (z + a)‖ = _
    rw [key _ _ h, key _ _ (hc z), h1, h2, norm_div, norm_div, norm_mul, norm_mul, norm_mul, norm_mul,
      Φ.χ_norm _ a.2, Φ'.χ_norm _ ha',
      mul_div_mul_left _ _ (mul_ne_zero one_ne_zero (norm_ne_zero_iff.2 (Complex.exp_ne_zero _)))]
  have hc0 := norm_periodic_const_range Φ.lat.subtype
    (by rw [AddSubgroup.coe_subtype, Subtype.range_coe]; exact Φ.span) q hq hper z 0
  have h0 : q 0 = 1 := by
    have := Φ'.fr_0 (c 0) (by rw [he]; exact hc 0)
    rw [← Φ.fr_0 (c 0) (hc 0)] at this
    change Φ.fr (c 0) 0 / Φ'.fr (c 0) 0 = 1
    rw [this, div_self (Φ.fr_ne _ _ (hc 0))]
  rw [h0, key j z hj] at hc0
  exact (div_eq_one_iff_eq (ne' j z hj)).1 hc0

end GlobalTheory.AnUniq

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.AnUniq.anFib_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (A A' : AnFib X bas idx e x L y), IsSympl X bas → x ∈ X.dom → SelfD X L → A.ex = A'.ex ∧ ∀ ϑ, A.Reads 1 y.s ϑ ↔ A'.Reads 1 y.s ϑ := by
  intro E _ _ _ H Dw l Xo c _ r g X bas idx e x L y A A' hs hx hL
  have hex : A.ex = A'.ex := AnUniq.exp_eq A.ex_add A'.ex_add A.hol A'.hol (fun i => y.u (e i).1 (e i).2)
    (fun i => by simpa only [Equiv.symm_apply_apply] using A.der (e i))
    (fun i => by simpa only [Equiv.symm_apply_apply] using A'.der (e i))
  obtain ⟨Φ, k₁, f₁, -, m₁, -⟩ := AnFib.exists_anPt E H Dw l Xo c r g X bas idx e x L y A hs hx hL
  obtain ⟨Φ', k₂, f₂, -, m₂, -⟩ := AnFib.exists_anPt E H Dw l Xo c r g X bas idx e x L y A' hs hx hL
  have hfr := AnUniq.fr_eq Φ.toAnFr Φ'.toAnFr (fun z => by rw [k₁, k₂, hex]) (fun z w => by rw [m₁, m₂])
  simp only [k₁, f₁, f₂] at hfr
  refine ⟨hex, fun ϑ => ⟨fun h j z pt h1 h2 hj => ?_, fun h j z pt h1 h2 hj => ?_⟩⟩
  · rw [← hex] at h1 hj
    rw [← hfr j z hj]
    exact h j z pt h1 h2 hj
  · rw [hfr j z hj]
    rw [hex] at h1 hj
    exact h j z pt h1 h2 hj
