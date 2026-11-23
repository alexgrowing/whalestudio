import Mathlib
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ModuliUnivEtaKilled
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ConnectionLinearInSectionStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaGroupShiftHalfTorsionRootStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.UniversalWeilPairingPullbackExistsUnique
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.TorsionIsotropicCommutatorPairingStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsotropicEnumerationSurjectiveLocalRingStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.InZhGeoInjStableStatement
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpTie
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndBC
import Formalism.LocalToGlobal.ProjectiveLattices.ThExpBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

namespace GlobalTheory

theorem shortSum_toΓ_injective (S : Type) [CommRing S] : Function.Injective (toΓ S) := by
  intro a b h
  have hinv : ∀ x : S, (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom (toΓ S x) = x := by
    intro x
    unfold toΓ
    rw [← CommRingCat.comp_apply, Iso.inv_hom_id]
    rfl
  rw [← hinv a, ← hinv b, h]

private theorem eq_one_of_sq_eq_one_of_pow_odd_sq_eq_one {M : Type*} [CommMonoid M] (x : M) (N : ℕ) (hN : Odd N)
    (h2 : x ^ 2 = 1) (hN2 : x ^ (N ^ 2) = 1) : x = 1 := by
  obtain ⟨k, hk⟩ := hN.pow (n := 2)
  rw [hk, pow_succ, pow_mul, h2, one_pow, _root_.one_mul] at hN2
  exact hN2

set_option maxHeartbeats 1000000 in

theorem shortSum_indep_local : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → Λ.TrivAt l.M → Λ.LevOK N l.M → ∀ (P : MvPolynomial (LtN Dw n) c.F) (T : Type) [CommRing T] [IsLocalRing T] [Algebra c.F T] (y : FrPt Xo c T) (z1 : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G)) (tp1 : (Fin n → LevQ Dw l) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G)) (F1 : (Fin n → LevQ Dw l) → Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))) (z2 : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G)) (tp2 : (Fin n → LevQ Dw l) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G)) (F2 : (Fin n → LevQ Dw l) → Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))), (∀ i, InZh Xo Λ N (z1 i)) → GeoInj Xo y.x z1 → (∀ q b, tp1 q b ^ N = levPt Xo y.x (levRep (q b)) ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (tp1 q b)) → (∀ q i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N y.s (z1 i b) (tp1 q b) (F1 q i b)) → (∀ i, InZh Xo Λ N (z2 i)) → GeoInj Xo y.x z2 → (∀ q b, tp2 q b ^ N = levPt Xo y.x (levRep (q b)) ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (tp2 q b)) → (∀ q i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N y.s (z2 i b) (tp2 q b) (F2 q i b)) → ∀ q, ∑ i, ∑ m ∈ P.support, algebraMap c.F T (P.coeff m) * ∏ b, nab y ((N : ℤ) ^ 2) (F1 q i b) (colOf m b) = ∑ i, ∑ m ∈ P.support, algebraMap c.F T (P.coeff m) * ∏ b, nab y ((N : ℤ) ^ 2) (F2 q i b) (colOf m b) := by
  intro hL E _ _ _ H Dw l Xo c _ nab hnab n Λ N hU hTr hLev P T _ _ _ y z1 tp1 F1 z2 tp2 F2 hz1 hg1 htp1 hF1 hz2 hg2 htp2 hF2 q
  obtain ⟨hNodd, hMN, hNL⟩ := hLev
  have hN0 : 0 < N := hNodd.pos
  have hLa : Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ.La := hNL.trans inf_le_left
  have hsurj := (GlobalTheory.T.isotropic_enumeration_surjective_local_ring hL E H Dw l Xo T y.x n Λ N hU hN0 hLa z1 hz1 hg1).1
  have h58 := GlobalTheory.T.torsion_isotropic_commutator_pairing hL E H Dw l Xo T y.x n Λ N hU hN0 hLa
  have h56 := GlobalTheory.T.inZh_geoInj_stable_alt E H Dw l Xo n Λ N
  have h57 := (GlobalTheory.UnivPairing.weilIs_univ_pull_exists_unique hL E H Dw l Xo N hN0).2.1

  have hz2inj : Function.Injective z2 := by
    intro i i' h
    let g : ptO Xo (spMap (IsLocalRing.residue T) ≫ y.x) ⟶ ptO Xo y.x :=
      Over.homMk (spMap (IsLocalRing.residue T)) rfl
    exact hg2 (IsLocalRing.ResidueField T) (IsLocalRing.residue T) g rfl
      (congrArg (fun (w : Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G)) (b : Fin n) => g ≫ w b) h)

  obtain ⟨u, hu⟩ : ∃ u : Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G), ∀ b, u b = (tp1 q b)⁻¹ * tp2 q b :=
    ⟨_, fun _ => rfl⟩
  have htp : ∀ b, tp2 q b = tp1 q b * u b := fun b => by
    rw [hu, mul_inv_cancel_left]
  have hlev : ∀ a : Dw.La, levPt Xo y.x a ^ N = 1 := by
    intro a
    obtain ⟨k, hk⟩ := hMN
    unfold levPt
    rw [← MonObj.comp_pow, hk, pow_mul, (GlobalTheory.moduli_univ_eta_killed hL E H Dw l Xo a).2.2, one_pow,
      MonObj.comp_one]
  have hu1 : ∀ b, u b ^ N = 1 := fun b => by
    rw [hu, mul_pow, inv_pow, (htp1 q b).1, (htp2 q b).1, inv_mul_cancel]
  have hsq : ∀ x : ptO Xo y.x ⟶ Xo.univ.t.G, x ^ N = 1 → x ^ (N ^ 2) = 1 := fun x hx => by
    rw [sq, pow_mul, hx, one_pow]
  have ht2 : ∀ b, tp1 q b ^ (N ^ 2) = 1 := fun b => by
    rw [sq, pow_mul, (htp1 q b).1, hlev]
  have hkill : ∀ b, ∃ j, KilledBy Xo (l.Mb ^ j) (tp1 q b) ∧ KilledBy Xo (l.Mb ^ j) (u b) := by
    intro b
    obtain ⟨j1, hj1⟩ := (htp1 q b).2
    obtain ⟨j2, hj2⟩ := (htp2 q b).2
    have mono : ∀ {i j : ℕ} (t : ptO Xo y.x ⟶ Xo.univ.t.G), i ≤ j →
        KilledBy Xo (l.Mb ^ i) t → KilledBy Xo (l.Mb ^ j) t :=
      fun t hij ht a ha => ht a (Ideal.pow_le_pow_right hij ha)
    refine ⟨max j1 j2, mono _ (le_max_left _ _) hj1, ?_⟩
    intro a ha
    have := Xo.univ.t.act.hom a
    have k1 := mono _ (le_max_left _ _) hj1 a ha
    have k2 := mono _ (le_max_right _ _) hj2 a ha
    have h1 : ((tp1 q b)⁻¹ ≫ Xo.univ.t.act.act a) * (tp1 q b ≫ Xo.univ.t.act.act a) = 1 := by
      rw [← MonObj.mul_comp, inv_mul_cancel, MonObj.one_comp]
    rw [k1, _root_.mul_one] at h1
    rw [hu, MonObj.mul_comp, h1, k2, _root_.one_mul]
  have hInU : InZh Xo Λ N u := h56.2.2.2 hTr (ptO Xo y.x) u (fun b => by
    obtain ⟨j, -, hj⟩ := hkill b
    exact ⟨hu1 b, j, hj⟩)

  have hw : ∀ i, ∃ j, z1 j = fun b => u b * z2 i b := fun i =>
    hsurj _ (h56.2.1 _ u (z2 i) hInU (hz2 i))
  choose ρ hρ using hw
  have hρinj : Function.Injective ρ := by
    intro i i' h
    apply hz2inj
    funext b
    have hii := (hρ i).symm.trans ((congrArg z1 h).trans (hρ i'))
    exact mul_left_cancel (show u b * z2 i b = u b * z2 i' b from congrFun hii b)
  have hρbij : Function.Bijective ρ := Finite.injective_iff_bijective.mp hρinj

  have key : ∀ i, (∑ m ∈ P.support, algebraMap c.F T (P.coeff m) *
        ∏ b, nab y ((N : ℤ) ^ 2) (F2 q i b) (colOf m b)) =
      ∑ m ∈ P.support, algebraMap c.F T (P.coeff m) *
        ∏ b, nab y ((N : ℤ) ^ 2) (F1 q (ρ i) b) (colOf m b) := by
    intro i
    have he : ∀ b, ∃ e : Γ((ptO Xo y.x).left, ⊤)ˣ,
        WeilIs Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (u b) (z2 i b) e := fun b =>
      (h57 (ptO Xo y.x) (u b) (z2 i b) (hsq _ (hu1 b)) ((hz2 i).1 b)).imp fun _ h => h.1
    choose e he using he
    have hpe : ∏ b, e b = 1 := h58.1 u (z2 i) e hInU (hz2 i) he
    have hr : ∀ b, ∃ r : T, (toΓ T r) ^ 2 = ((e b : Γ((ptO Xo y.x).left, ⊤))) ∧ r ^ (N ^ 2) = 1 ∧
        ∀ α, nab y ((N : ℤ) ^ 2) (F2 q i b) α = r * nab y ((N : ℤ) ^ 2) (F1 q (ρ i) b) α := by
      intro b
      obtain ⟨j, hj1, hj2⟩ := hkill b
      have hW1 := h58.2 (tp1 q b) (u b) j (ht2 b) (hsq _ (hu1 b)) hj1 hj2
      have hA : IsUUOver Xo.univ.t.G Xo.univ.t.PP N y.s (z2 i b) (tp1 q b * u b) (F2 q i b) := by
        rw [← htp b]
        exact hF2 q i b
      have hB : IsUUOver Xo.univ.t.G Xo.univ.t.PP N y.s (u b * z2 i b) (tp1 q b) (F1 q (ρ i) b) := by
        have h1 := hF1 q (ρ i) b
        rw [hρ i] at h1
        exact h1
      obtain ⟨r, hr1, hr2, hr3⟩ := GlobalTheory.T.thetaGroup_shift_halfTorsion_root hL E H Dw l Xo T y.x N hNodd y.s (tp1 q b) (u b) (z2 i b)
        (e b) (ht2 b) (hsq _ (hu1 b)) ((hz2 i).1 b) hW1 (he b) _ _ hA hB
      exact ⟨r, hr1, hr2, GlobalTheory.T.connection_linear_in_section E H Dw l Xo c nab hnab T y N _ _ r hr3⟩
    choose r hr using hr
    have hprod : ∏ b, r b = 1 := by
      apply eq_one_of_sq_eq_one_of_pow_odd_sq_eq_one _ N hNodd
      · apply shortSum_toΓ_injective T
        rw [map_one, map_pow, map_prod, ← Finset.prod_pow,
          Finset.prod_congr rfl (fun b _ => (hr b).1), ← Units.coe_prod, hpe, Units.val_one]
      · rw [← Finset.prod_pow]
        exact Finset.prod_eq_one (fun b _ => (hr b).2.1)
    refine Finset.sum_congr rfl (fun m _ => ?_)
    congr 1
    rw [Finset.prod_congr rfl (fun b _ => (hr b).2.2 (colOf m b)), Finset.prod_mul_distrib, hprod, _root_.one_mul]
  rw [Finset.sum_congr rfl (fun i _ => key i)]
  exact (hρbij.sum_comp (fun j => ∑ m ∈ P.support, algebraMap c.F T (P.coeff m) *
    ∏ b, nab y ((N : ℤ) ^ 2) (F1 q j b) (colOf m b))).symm

end GlobalTheory
