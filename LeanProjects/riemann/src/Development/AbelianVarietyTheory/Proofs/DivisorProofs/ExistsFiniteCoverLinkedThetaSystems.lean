import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import Development.AbelianVarietyTheory.Definitions.Divisors.SpecializesGenericImage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftGenericFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSystemRealisationRegularAtPrimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointsFiniteUnitaryModuliCoefficientFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteSurjectiveCoverFromOpensStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelStructureNormalModelUnitaryModuliPoinStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSpreadUniversalAbelianSchemeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryActionBaseChangeSubalgebraStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.USep
open GlobalTheory.UCovSep

namespace GlobalTheory.UCovSep

set_option maxHeartbeats 1000000 in

theorem exists_linked_cov : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∀ n : ℕ, n.Prime → Odd n → ∀ j₀ : ℕ, ∃ (j : ℕ) (Y : Scheme.{0}) (q : Y ⟶ Xo.XF c), j₀ ≤ j ∧ IsFinite q ∧ Surjective q ∧ ∀ (K : Type) [Field K] (y' : Sp K ⟶ Y), ∃ (X₁ : GlobalTheory.GSep.GSet) (act : 𝓞 E → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (u : Sp (ratHull X₁.S.R) ⟶ Xo.XF c) (π : X₁.M.Z ⟶ C.Z) (yM : Sp K ⟶ X₁.M.Z), GlobalTheory.GSep.ULink C X₁ act u π ∧ X₁.S.r * X₁.S.N = (n ^ j) ^ 2 ∧ (∃ (U : C.Z.Opens) (g' : X₁.M.Z ⟶ U.toScheme), IsFinite g' ∧ g' ≫ U.ι = π ∧ Set.range (pullback.fst C.z (spMap C.b)) ⊆ (U : Set C.Z)) ∧ yM ≫ π = y' ≫ q ≫ C.i ∧ ∀ a ∈ X₁.S.R, a ∈ X₁.M.O (yM (closedPoint K)) := by
  intro E _ _ _ H Dw hpq l Xo c C n hn ho j₀
  classical
  haveI : Finite (genericPoints (Xo.XF c)) := (GlobalTheory.T.genericPoints_finite_unitaryModuli_coefficientField E H Dw l Xo c).to_subtype
  letI : Fintype (genericPoints (Xo.XF c)) := Fintype.ofFinite _
  choose g₀ hA using fun τ : genericPoints (Xo.XF c) => GlobalTheory.T.exists_levelStructure_normalModel_unitaryModuliPoint E H Dw hpq l Xo c C τ.1 n hn ho
  choose k j₁ hk _hB hj₁ big using fun τ : genericPoints (Xo.XF c) =>
    GlobalTheory.UPoinc.GSetup.exists_big_level (g₀ τ) n hn.two_le 0
  set J := j₀ + ∑ τ, (k τ + j₁ τ) + 1 with hJ
  have hkJ : ∀ τ, k τ + j₁ τ + j₀ + 1 ≤ J := fun τ => by
    have := Finset.single_le_sum (f := fun τ => k τ + j₁ τ) (fun _ _ => Nat.zero_le _) (Finset.mem_univ τ)
    omega
  choose o₁ Ω i₁ i₂ i₃ i₄ ze uτ A₁ lev M U g hAg hun hx hUO hpt hMn hMp hgf hrange using fun τ => hA τ (4 * J)
  obtain ⟨Y, q, hqf, hqs, hY⟩ := GlobalTheory.T.exists_finite_surjective_cover_from_opens (Xo.XF c) C.Z C.i (genericPoints (Xo.XF c)) (fun τ => (M τ).Z) U g hgf
    (fun τ => by
      rintro _ ⟨x, rfl⟩
      exact hrange τ ⟨C.iF x, rfl⟩)
    (fun x => by
      obtain ⟨τ, hτ, hsp⟩ := GlobalTheory.exists_mem_genericPoints_specializes x
      refine ⟨⟨τ, hτ⟩, (M ⟨τ, hτ⟩).pt (closedPoint (Ω ⟨τ, hτ⟩)), ?_⟩
      have h₁ : (g ⟨τ, hτ⟩ ≫ (U ⟨τ, hτ⟩).ι) ((M ⟨τ, hτ⟩).pt (closedPoint (Ω ⟨τ, hτ⟩))) = C.i τ := by
        refine (congrArg (fun χ : Sp (Ω ⟨τ, hτ⟩) ⟶ C.Z => χ (closedPoint (Ω ⟨τ, hτ⟩))) (hpt ⟨τ, hτ⟩)).trans ?_
        exact congrArg C.i (hx ⟨τ, hτ⟩ (closedPoint (Ω ⟨τ, hτ⟩)))
      rw [h₁]
      exact hsp.map C.i.continuous)
  refine ⟨J, Y, q, by omega, hqf, hqs, fun K _ y' => ?_⟩
  obtain ⟨t, yM, hyM⟩ := hY K y'
  letI := i₁ t
  letI := i₂ t
  letI := i₃ t
  haveI := i₄ t
  obtain ⟨R, P, act, u, 𝔭, hRfg, hfr, hPg, hS, ⟨levR⟩, hact, hUA, hu, h𝔭, hreg𝔭⟩ :=
    GlobalTheory.T.exists_local_spread_universal_abelian_scheme E H Dw hpq l Xo c C (o₁ t) (Ω t) (M t) (g t ≫ (U t).ι) (uτ t) (hMn t) (hpt t)
      (A₁ t) (n ^ (4 * J)) (ze t) (by rw [Nat.cast_pow]; exact (hun t).pow _) (hUO t) (lev t) K yM (y' ≫ q)
      (by rw [Category.assoc]; simpa only [Category.assoc] using hyM)
  have e : (n ^ (2 * J - 2 * k t) * (n ^ k t) ^ 2) ^ 2 = n ^ (4 * J) := by
    rw [← pow_mul, ← pow_add, ← pow_mul]
    congr 1
    have := hkJ t
    omega
  obtain ⟨S, ρ, hR, φ, hreg, -, hN, hr, hgS, hpb, hL, -⟩ := GlobalTheory.T.exists_thetaSystem_realisation_regular_at_prime (o₁ t) (Ω t) R hRfg hfr 𝔭 h𝔭 P n (k t)
    (2 * J - 2 * k t) (ze t) hn ho (hk t) (by have := hkJ t; omega) (hun t) hS (e ▸ levR)
  obtain ⟨act', hact', -, hUA'⟩ := GlobalTheory.T.unitaryAction_baseChange_subalgebra E H Dw l Xo c (o₁ t) (Ω t) R S.R hR P ρ.P φ hpb hL act u hact hUA
  have hu' : spMap (ratHull S.R).val.toRingHom ≫ spMap (Subalgebra.inclusion (ratHull_mono hR)).toRingHom ≫ u = uτ t := by
    rw [← hu, ← Category.assoc, ← Spec.map_comp]; rfl
  have hgen : ∀ w, (spMap (ratHull S.R).val.toRingHom ≫ spMap (Subalgebra.inclusion (ratHull_mono hR)).toRingHom ≫ u) w ∈
      genericPoints (Xo.XF c) := fun w => by rw [hu', hx t w]; exact t.2
  have hptS : (M t).pt ≫ (g t ≫ (U t).ι) =
      spMap (ratHull S.R).val.toRingHom ≫ (spMap (Subalgebra.inclusion (ratHull_mono hR)).toRingHom ≫ u) ≫ C.i := by
    rw [hpt t, ← hu', Category.assoc]
  have hbig : S.Big := big t _ (by have := hkJ t; omega) (o₁ t) (Ω t) S (hgS.trans (hPg.trans (hAg t))) hN hr
  let X₁ : GlobalTheory.GSep.GSet :=
    { o₁ := o₁ t, Ω₁ := Ω t, S := S, ρ := ρ, big := hbig, M := M t, normal := hMn t, projM := hMp t,
      div := C.thetaInt (o₁ t) (Ω t) S ρ _ hUA'.uOver hgen (M t) (g t ≫ (U t).ι)
        (hMn t) hptS }
  refine ⟨X₁, act', spMap (Subalgebra.inclusion (ratHull_mono hR)).toRingHom ≫ u, g t ≫ (U t).ι, yM,
    ⟨hact', hUA', hgen, hptS⟩, ?_, ⟨U t, g t, hgf t, rfl, hrange t⟩, by simpa only [Category.assoc] using hyM, ?_⟩
  · show S.r * S.N = _
    rw [hr, hN, ← pow_mul, ← pow_add, ← pow_mul]
    congr 1
    have := hkJ t
    omega
  · intro a ha
    obtain ⟨a', b', hb', rfl⟩ := hreg a ha
    exact hreg𝔭 a' b' hb'

end GlobalTheory.UCovSep
