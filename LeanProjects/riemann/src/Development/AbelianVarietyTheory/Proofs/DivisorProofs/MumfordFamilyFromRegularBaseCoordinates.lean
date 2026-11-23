import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GensOfPsiUnitOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationDataNsmulRescaleKeepsLawsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiAbelianPelUniformisationOfNormStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRootOfIsAlgClosed

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon.FamFrom

theorem rescale_inv_psi {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (g : D.X → (FractionRing R)ˣ) (χ : D.X) :
    (GlobalTheory.PolDeg.rescale (GlobalTheory.PolDeg.rescale D g) (fun y => (g y)⁻¹)).psi χ = D.psi χ := by
  show GlobalTheory.UU.scaleGen _ (GlobalTheory.UU.scaleGen _ _) = _
  unfold GlobalTheory.UU.scaleGen
  generalize D.psi χ = b
  cases b
  congr 1
  funext j
  have h1 : unitOn ((g χ)⁻¹) * unitOn (g χ) = 1 := by
    have hu : unitOn ((g χ)⁻¹ * g χ) = unitOn ((g χ)⁻¹) * unitOn (g χ) := map_mul _ _ _
    rw [← hu, inv_mul_cancel]
    exact Units.ext (map_one _)
  rw [← _root_.mul_assoc, ← map_mul, h1, map_one, _root_.one_mul]

theorem isPullDeg_rescale_inv {W R : Type} [CommRing W] [IsDomain W] [CommRing R] [IsDomain R] (φ : W →+* R)
    (D₀ : DegPre W) (D : DegPre R) (g : D.X → (FractionRing R)ˣ) (hD : IsPullDeg φ D₀ D) :
    ∃ h : IsPullDeg φ D₀ (GlobalTheory.PolDeg.rescale (GlobalTheory.PolDeg.rescale D g) (fun y => (g y)⁻¹)),
      (∀ y, h.xe y = hD.xe y) ∧ h.e.hom.left = hD.e.hom.left :=
  ⟨{ hD with psi_pr := fun x => (rescale_inv_psi D g x).symm ▸ hD.psi_pr x }, fun _ => rfl, rfl⟩

end GlobalTheory.UCanon.FamFrom

namespace GlobalTheory.UCanon.FamFrom

theorem main : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (iw : L.W →+* R), Function.Injective iw → ∀ (m N : ℕ) (s : Fin m ⊕ Fin N → R) (ε : Fin m ⊕ Fin N → LinearMap.BilinForm ℤ L.D.X), (∀ k, ε k ∈ balForms H.bar L.D.X) → (∀ i, s (.inl i) ∈ maximalIdeal R ∧ s (.inl i) ≠ 0) → (∀ j, IsUnit (s (.inr j))) → (∀ i y, 0 ≤ ε (.inl i) y y) → (∀ y, y ≠ 0 → 0 < ∑ i, ε (.inl i) y y) → Nontrivial L.D.X → ∃ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (e : P.D.toPre.X ≃ₗ[𝓞 E] L.D.X), DivFrom L P.D.toPre P.oD iw s ε e ∧ IsMonomial P.D.toPre (fun i => s (.inl i)) (fun i => (l.M' : ℤ) • pull e.toLinearMap (ε (.inl i))) := by
  intro E _ _ _ H Dl l c L R _ _ _ hB iw hiw m N s ε hε hs hu hpos hdef hnt
  letI := H.starRing
  have hw : H.w0 + star H.w0 = 1 := GlobalTheory.TauTwist.halfUnit_add_star H
  have hM : 0 < l.M' := Nat.lcm_pos (by have := l.three_le; omega) l.A_pos
  letI iD : Module (𝓞 E) (mulDeg L.D l.M').X := L.mod
  obtain ⟨he0, hb0, hU0, oa0, hoa0, hW0⟩ := GlobalTheory.T.degenerationDataNsmulRescale_keeps_laws L.W L.D (𝓞 E) L.oa H.w0 l.M' L.even L.bimult L.w0 L.gen
  have hne : ∃ i, ε (.inl i) ≠ 0 := by
    obtain ⟨y, hy⟩ := exists_ne (0 : L.D.X)
    have h := hdef y hy
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero h.ne'
    exact ⟨i, fun h0 => hi (by rw [h0]; rfl)⟩
  obtain ⟨D'', hD, iM, e, hxe, hPE, hTB, hPI, hfin, ⟨oa1, hoa1, hPW⟩, hmono, -, -, -⟩ :=
    GlobalTheory.UTautData.main L.W R (maximalIdeal R) iw hiw (mulDeg L.D l.M') (𝓞 E) oa0 H.w0 hw he0 hb0 hW0 hU0
      (fun i => s (.inl i)) (fun i => (hs i).2) (fun i => (hs i).1) (fun j => (hu j).unit) l.M' hM
      (fun i => ε (.inl i)) (fun j => ε (.inr j)) (fun i => hε _) hpos (fun j => hε _) hdef hne

  set T := GlobalTheory.UTautData.taut D'' e H.w0 (fun i => s (.inl i)) (fun i => (hs i).2) (fun j => (hu j).unit) l.M'
    (fun i => ε (.inl i)) (fun j => ε (.inr j)) with hT
  let D1 : DegData R (maximalIdeal R) := ⟨T, hPE, hTB, hPI, hfin⟩
  obtain ⟨t, P, hPD, hmod, hoD⟩ := GlobalTheory.T.exists_semiAbelian_pelUniformisation_of_norm H R hB D1 (inst := iM) oa1 hPW
  have key : ∀ (Dd : DegData R (maximalIdeal R)) [im : Module (𝓞 E) Dd.toPre.X] (od : Dd.toPre.OAct (𝓞 E)),
      Dd = D1 → HEq im iM → HEq od oa1 → ∃ e' : Dd.toPre.X ≃ₗ[𝓞 E] L.D.X,
        DivFrom L Dd.toPre od iw s ε e' ∧
        IsMonomial Dd.toPre (fun i => s (.inl i)) (fun i => (l.M' : ℤ) • pull e'.toLinearMap (ε (.inl i))) := by
    rintro Dd im od rfl h1 h2
    have h1' := eq_of_heq h1
    subst im
    have h2' := eq_of_heq h2
    subst od
    letI : Module (𝓞 E) D1.toPre.X := iM
    let e₁ : D1.toPre.X ≃ₗ[𝓞 E] L.D.X := e
    refine ⟨e₁, ?_, hmono⟩
    obtain ⟨h2p, hx2, he2⟩ := isPullDeg_rescale_inv iw (mulDeg L.D l.M') D''
      (GlobalTheory.UTautData.scaleFn (GlobalTheory.UTautData.coordsK (fun i => s (.inl i)) (fun i => (hs i).2) (fun j => (hu j).unit))
        H.w0 (GlobalTheory.UTautData.forms l.M' (fun i => pull e.toLinearMap (ε (.inl i)))
          (fun j => pull e.toLinearMap (ε (.inr j))))) hD
    refine ⟨_, h2p, fun y => ?_, fun y => (hx2 y).trans (hxe y).symm, fun x => ?_⟩
    · rw [inv_inv]
      refine (GlobalTheory.UTautData.scaleFn_coe _ _ _ _ _ _ _ _).trans ?_
      rw [Fintype.prod_sum_type]
      congr 1
      · refine Finset.prod_congr rfl fun i _ => ?_
        have h3 : e₁ (H.w0 • y) = H.w0 • e₁ y := e₁.map_smul H.w0 y
        show _ = algebraMap R (FractionRing R) (s (.inl i)) ^ ((l.M' : ℤ) * ε (.inl i) (e₁ y) (H.w0 • e₁ y))
        rw [← h3]
        rfl
      · refine Finset.prod_congr rfl fun j _ => ?_
        have h3 : e₁ (H.w0 • y) = H.w0 • e₁ y := e₁.map_smul H.w0 y
        show _ = algebraMap R (FractionRing R) (s (.inr j)) ^ ((l.M' : ℤ) * ε (.inr j) (e₁ y) (H.w0 • e₁ y))
        rw [← h3, (hu j).unit_spec]
        rfl
    · rw [he2]
      have h := hoa1 x
      rw [hoa0] at h
      exact h
  obtain ⟨e', h1, h2⟩ := key P.D P.oD hPD hmod hoD
  exact ⟨t, P, e', h1, h2⟩

end GlobalTheory.UCanon.FamFrom
