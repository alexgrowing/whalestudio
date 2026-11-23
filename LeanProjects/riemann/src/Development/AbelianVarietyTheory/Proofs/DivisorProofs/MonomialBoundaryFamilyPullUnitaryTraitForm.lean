import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.USt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPelUnifPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPelUnifPsiCoord
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SystemPrimesDistinctLevelsGeThree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UChart

theorem trait_pull {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {φ : InvFun (𝓞 E)} {R : Type} [CommRing R] [IsDomain R]
    [IsLocalRing R] (C : MonoFam Xo c φ R) (hR : GlobalTheory.Mum.Base R) (W : Type) [CommRing W] [IsDomain W]
    [IsLocalRing W] (hW : GlobalTheory.UU.CDVR W) (ϖ : W) (ρ : R →+* W) (hinj : Function.Injective ρ) (hloc : IsLocalHom ρ)
    (w : Fin C.m → ℕ) (u : Fin C.m → Wˣ) (hs : ∀ i, ρ (C.s i) = u i * ϖ ^ w i) :
    ∃ (t : SAB H (Sp W)) (P : PELUnif (maximalIdeal W) t) (e : P.D.toPre.X ≃ₗ[𝓞 E] C.P.D.toPre.X)
      (be : LinearMap.BilinForm ℤ P.D.toPre.X),
      Nonempty (SABMap t C.t (spMap ρ)) ∧
      (∀ κ : Sp (FractionRing W) ⟶ Sp (FractionRing R), κ ≫ jK R = jK W ≫ spMap ρ →
        ∃ tK : SAB H (Sp (FractionRing W)), Nonempty (SABMap tK t (jK W)) ∧
          Nonempty (SABMap tK Xo.univ.t ((κ ≫ C.y) ≫ pullback.fst _ _))) ∧
      be = ∑ i, (w i : ℤ) • pull e.toLinearMap ((l.M' : ℤ) • C.δ i) ∧
      be ∈ levelForms H 1 P.D.toPre.X ∧ IsMonomial P.D.toPre ![ϖ] ![be] ∧
      φ.evalZ be = ∑ i, (w i : ℝ) * φ.evalZ ((l.M' : ℤ) • C.δ i) := by
  obtain ⟨h1, -, h3, h4, h5⟩ := GlobalTheory.firstFiveLaws
  obtain ⟨hdvr, hcomp, -⟩ := hW
  have hWa : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hcomp⟩
  have hI : (maximalIdeal R).map ρ ≤ maximalIdeal W := ((IsLocalRing.local_hom_TFAE ρ).out 0 2).1 hloc
  obtain ⟨t', m₀, P', hD, -, -, -, -, hlin, -⟩ := GlobalTheory.ArcDataDescent.exists_pelUnif_pull h3.cubePull h1.polBaseChange
    h4.unifBaseChange h5 hR.1 hWa C.t C.P ρ hinj hI
  let e : P'.D.toPre.X ≃ₗ[𝓞 E] C.P.D.toPre.X := { hD.xe with map_smul' := hlin }
  have he : ∀ y, e y = hD.xe y := fun _ => rfl
  refine ⟨t', P', e, ∑ i, (w i : ℤ) • pull e.toLinearMap ((l.M' : ℤ) • C.δ i), ⟨m₀⟩, ?_, rfl, ?_, ?_, ?_⟩
  · intro κ hκ
    obtain ⟨tKR, ⟨n1⟩, ⟨n2⟩⟩ := C.gen
    obtain ⟨tK, ⟨k⟩⟩ := GlobalTheory.Models.Inhab.exists_pull κ tKR
    obtain ⟨a, -⟩ := sabComp pullCubComp E H _ _ _ C.t tKR tK (jK R) κ n1 k
    rw [hκ] at a
    obtain ⟨b, -⟩ := sabCancel pullCubCancel E H _ _ _ C.t t' tK (spMap ρ) (jK W) m₀ a
    obtain ⟨d, -⟩ := sabComp pullCubComp E H _ _ _ Xo.univ.t tKR tK _ κ n2 k
    rw [← Category.assoc] at d
    exact ⟨tK, ⟨b⟩, ⟨d⟩⟩
  · rw [← balForms_eq_levelForms]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (pull_mem _ (Submodule.smul_mem _ _ (C.cone.mem i)))
  · intro y
    obtain ⟨u0, n, hn, hc⟩ := C.mono (hD.xe y)
    obtain ⟨u', hu'⟩ := GlobalTheory.PelCoordPull.psiCoord_pull hD y _ hc
    refine ⟨u' * Units.map ρ.toMonoidHom u0 * ∏ i, u i ^ n i, fun _ => ∑ i, w i * n i, fun j => ?_, ?_⟩
    · fin_cases j
      show (∑ i, (w i : ℤ) • pull e.toLinearMap ((l.M' : ℤ) • C.δ i)) y y = 2 * ((∑ i, w i * n i : ℕ) : ℤ)
      rw [LinearMap.sum_apply, LinearMap.sum_apply]
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h2 : ((l.M' : ℤ) • C.δ i) (hD.xe y) (hD.xe y) = 2 * n i := hn i
      rw [LinearMap.smul_apply, LinearMap.smul_apply, pull_apply]
      rw [show (e.toLinearMap y) = hD.xe y from rfl, h2]
      simp only [smul_eq_mul]; ring
    · convert hu' using 1
      simp only [Fin.prod_univ_one, Matrix.cons_val_zero, map_mul, map_prod, map_pow, hs, Units.val_mul,
        Units.coe_map, Units.coe_prod, Units.val_pow_eq_pow_val, mul_pow, Finset.prod_mul_distrib,
        ← pow_mul, Finset.prod_pow_eq_pow_sum, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
      ring
  · have hsum : (∑ i, (w i : ℤ) • pull e.toLinearMap ((l.M' : ℤ) • C.δ i)) =
        pull e.toLinearMap (∑ i, (w i : ℤ) • ((l.M' : ℤ) • C.δ i)) := by
      ext a b; simp [LinearMap.sum_apply, pull_apply]
    rw [hsum, evalZ_pull φ e.surjective]
    have hl := C.cone.linearOn_smul l.M' (fun i => (w i : ℝ)) (fun i => Nat.cast_nonneg _)
    refine Eq.trans ?_ hl
    unfold InvFun.evalZ
    congr 1
    funext a b
    simp [LinearMap.sum_apply]

end GlobalTheory.UChart

namespace GlobalTheory.UChart

theorem pull_trait : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (ψ : R →+* W), Function.Injective ψ → IsLocalHom ψ → ∀ (ϖ : W), Irreducible ϖ → ∀ (w : Fin C.m → ℕ), (∀ i, Associated (ψ (C.s i)) (ϖ ^ w i)) → ∀ κ : Sp (FractionRing W) ⟶ Sp (FractionRing R), κ ≫ jK R = jK W ≫ spMap ψ → ∃ (t : SAB H (Sp W)) (tK : SAB H (Sp (FractionRing W))) (P : PELUnif (maximalIdeal W) t), Nonempty (SABMap tK t (jK W)) ∧ Nonempty (SABMap tK Xo.univ.t ((κ ≫ C.y) ≫ pullback.fst _ _)) ∧ ∃ be ∈ levelForms H 1 P.D.toPre.X, IsMonomial P.D.toPre ![ϖ] ![be] ∧ φ.evalZ be = ∑ i, (w i : ℝ) * φ.evalZ ((l.M' : ℤ) • C.δ i) := by
  intro E _ _ _ H Dw l Xo c φ R _ _ _ hR C W _ _ _ hW ψ hinj hloc ϖ _ w hw κ hκ
  choose v hv using hw
  obtain ⟨t, P, e, be, -, htK, -, hbe, hmon, hev⟩ :=
    trait_pull C hR W hW ϖ ψ hinj hloc w (fun i => (v i)⁻¹) (fun i => by rw [← hv i, mul_left_comm, Units.inv_mul, _root_.mul_one])
  obtain ⟨tK, h1, h2⟩ := htK κ hκ
  exact ⟨t, tK, P, h1, h2, be, hbe, hmon, hev⟩

end GlobalTheory.UChart
