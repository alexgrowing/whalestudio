import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionValueUniqueBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TopLeOfClosedPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
open GlobalTheory.CompanionTheory.Ar.Sl.Reg

open GlobalTheory.CompanionTheory.Ar.Sl.Transl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.Reg

theorem valF_comp_valR {O C : Type} [CommRing O] [Field C] [Algebra O C] {X : Scheme.{0}} (a : Sp O ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ a ⁻¹ᵁ U) (f : Γ(X, U)) :
    valF (spMap (algebraMap O C) ≫ a) U f = algebraMap O C (valR a U h f) := by
  have h' : ⊤ ≤ (spMap (algebraMap O C) ≫ a) ⁻¹ᵁ U := fun x _ => h (x := spMap (algebraMap O C) x) trivial
  have e₀ : (spMap (algebraMap O C)).appLE ⊤ ⊤ (by first | exact le_rfl | simp) = (spMap (algebraMap O C)).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  have e : (spMap (algebraMap O C) ≫ a).appLE U ⊤ h' = a.appLE U ⊤ h ≫ (spMap (algebraMap O C)).appTop := by
    rw [← e₀]
    exact (Scheme.Hom.appLE_comp_appLE (spMap (algebraMap O C)) a U ⊤ ⊤ h _).symm
  have n := congrArg (fun φ => φ.hom ((a.appLE U ⊤ h).hom f))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap O C)))
  rw [valF, dif_pos h', e]
  exact n

theorem valR_unit {O : Type} [CommRing O] {X : Scheme.{0}} (a : Sp O ⟶ X) (U : X.Opens) (h : ⊤ ≤ a ⁻¹ᵁ U)
    (f : Γ(X, U)ˣ) : IsUnit (valR a U h f.val) :=
  f.isUnit.map (valR a U h)

theorem unit_alg {O : Type} [CommRing O] (t r0 r2 r1 : O) (u0 u1 u2 : Oˣ) (e0 : u0.val = r0) (e1 : u1.val = r1)
    (e2 : u2.val = r2) (M n : ℕ) :
    t ^ M * (u1 ^ n * ((u0 * u2 ^ M) ^ n)⁻¹ : Oˣ).val * (r0 * r2 ^ M) ^ n = t ^ M * r1 ^ n := by
  subst e0 e1 e2
  have : ((u1 ^ n * ((u0 * u2 ^ M) ^ n)⁻¹ * (u0 * u2 ^ M) ^ n : Oˣ)).val = (u1 ^ n : Oˣ).val := by
    rw [inv_mul_cancel_right]
  simp only [Units.val_mul, Units.val_pow_eq_pow_val] at this ⊢
  rw [_root_.mul_assoc, this]

theorem torsVal_eq_unit_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (n : ℕ) (s : Out.H0 D.t.PP.L n) (O C : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [Field C] [Algebra O C] [FaithfulSMul O C] (ρ : 𝓞 L →+* O) (y : Over.mk (spMap ρ) ⟶ D.t.G) (N : ℕ), 1 ≤ N → y ^ N = 1 → ∀ (i : D.t.PP.L.ι) (h : ⊤ ≤ (show Sp O ⟶ D.t.G.left from y.left) ⁻¹ᵁ (LB.LinComb D.t.PP.L (K := Fin 1) (fun _ => 𝟙 _) (fun _ => (n : ℤ))).U (fun _ => i)) (b : Sp C ⟶ Sp (𝓞 L)), b = spMap (algebraMap O C) ≫ spMap ρ → ∀ (yC : Over.mk b ⟶ D.t.G), yC.left = spMap (algebraMap O C) ≫ y.left → ∀ T : C, TorsVal D.t.PP s yC N T → ∃ ε : Oˣ, T = algebraMap O C (valR (show Sp O ⟶ D.t.G.left from y.left) _ h (s.f fun _ => i) ^ (N ^ 2) * ε) := by
  intro E _ _ _ H L _ _ D n s O C _ _ _ _ _ _ ρ y N hN hy i h b hb yC hyC T hT
  subst hb
  obtain ⟨-, hyCN, w, -, -, hw, -, -, -⟩ := id hT
  let e : Sp O ⟶ D.t.G.left := (1 : Over.mk (spMap ρ) ⟶ D.t.G).left
  obtain ⟨i₀, h₀⟩ := exists_chart D.t.PP.isLB (e (IsLocalRing.closedPoint O))
  have he : ⊤ ≤ e ⁻¹ᵁ D.t.PP.L.U i₀ := top_le_of_closedPoint _ h₀
  have eN : (show Sp O ⟶ D.t.G.left from y.left) ≫ ((𝟙 D.t.G : D.t.G ⟶ D.t.G) ^ N).left = e := by
    show y.left ≫ _ = _
    rw [left_pow, hy]
  have e1 : e ≫ ((𝟙 D.t.G : D.t.G ⟶ D.t.G) ^ N).left = e := by
    show (1 : Over.mk (spMap ρ) ⟶ D.t.G).left ≫ _ = _
    rw [left_pow, one_pow]
  have hrig : spMap ρ ≫ eSec D.t.G = e := (one_left (Over.mk (spMap ρ))).symm
  have hi : ⊤ ≤ (show Sp O ⟶ D.t.G.left from y.left) ⁻¹ᵁ D.t.PP.L.U i := fun x _ =>
    Set.mem_iInter.1 (h (x := x) trivial) 0
  have hY : ⊤ ≤ (show Sp O ⟶ D.t.G.left from y.left) ⁻¹ᵁ
      LB.wchart D.t.PP.L (![((𝟙 D.t.G : D.t.G ⟶ D.t.G) ^ N).left, 𝟙 D.t.G.left] : Fin 2 → _) ![i₀, i] := by
    intro x _
    refine Set.mem_iInter.2 fun k => ?_
    fin_cases k
    · show (((show Sp O ⟶ D.t.G.left from y.left) ≫ ((𝟙 D.t.G : D.t.G ⟶ D.t.G) ^ N).left) x) ∈ D.t.PP.L.U i₀
      rw [eN]; exact he (x := x) trivial
    · exact hi (x := x) trivial
  have hZ : ⊤ ≤ e ⁻¹ᵁ
      LB.wchart D.t.PP.L (![((𝟙 D.t.G : D.t.G ⟶ D.t.G) ^ N).left, 𝟙 D.t.G.left] : Fin 2 → _) ![i₀, i₀] := by
    intro x _
    refine Set.mem_iInter.2 fun k => ?_
    fin_cases k
    · show ((e ≫ ((𝟙 D.t.G : D.t.G ⟶ D.t.G) ^ N).left) x) ∈ D.t.PP.L.U i₀
      rw [e1]; exact he (x := x) trivial
    · exact he (x := x) trivial
  have hR : ⊤ ≤ (show Sp O ⟶ (𝟙_ (Over (Sp (𝓞 L)))).left from spMap ρ) ⁻¹ᵁ
      LB.wchart D.t.PP.L (K := PUnit) (fun _ => eSec D.t.G) (fun _ => i₀) := by
    intro x _
    refine Set.mem_iInter.2 fun _ => ?_
    show (spMap ρ ≫ eSec D.t.G) x ∈ D.t.PP.L.U i₀
    rw [hrig]; exact he (x := x) trivial
  obtain ⟨u1, e1'⟩ := valR_unit _ _ hY (w.s ![i₀, i])
  obtain ⟨u0, e0'⟩ := valR_unit _ _ hZ (w.s ![i₀, i₀])
  obtain ⟨u2, e2'⟩ := valR_unit (X := (𝟙_ (Over (Sp (𝓞 L)))).left) _ _ hR (D.t.PP.rig.s fun _ => i₀)
  have hone : (1 : Over.mk (spMap (algebraMap O C) ≫ spMap ρ) ⟶ D.t.G).left = spMap (algebraMap O C) ≫ e := by
    show _ = spMap (algebraMap O C) ≫ (1 : Over.mk (spMap ρ) ⟶ D.t.G).left
    rw [one_left, one_left]
    simp
  refine ⟨u1 ^ n * ((u0 * u2 ^ (N ^ 2)) ^ n)⁻¹, ?_⟩
  have hT' : TorsVal D.t.PP s yC N (algebraMap O C (valR (show Sp O ⟶ D.t.G.left from y.left) _ h (s.f fun _ => i) ^ (N ^ 2) *
      (u1 ^ n * ((u0 * u2 ^ (N ^ 2)) ^ n)⁻¹ : Oˣ).val)) := by
    refine ⟨hN, hyCN, w, i₀, i, hw, ?_, ?_, ?_⟩
    · rw [hone]
      exact fun x _ => he (x := spMap (algebraMap O C) x) trivial
    · rw [hyC]
      exact fun x _ => hi (x := spMap (algebraMap O C) x) trivial
    · rw [hone, hyC]
      erw [valF_comp_valR e _ hZ, valF_comp_valR (X := (𝟙_ (Over (Sp (𝓞 L)))).left) _ _ hR,
        valF_comp_valR _ _ h, valF_comp_valR _ _ hY]
      have key := congrArg (algebraMap O C) (unit_alg (valR (show Sp O ⟶ D.t.G.left from y.left) _ h (s.f fun _ => i)) _ _ _
        u0 u1 u2 e0' e1' e2' (N ^ 2) n)
      simp only [map_mul, map_pow] at key ⊢
      exact key
  exact (GlobalTheory.T.torsion_value_unique_base_change E H L D n s C _ yC N hN hyCN).1.unique hT hT'

end GlobalTheory.CompanionTheory.Ar.Sl.Reg
