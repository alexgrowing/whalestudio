import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.GenProd
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.NuGeIffOfIsActOfOfPowEqOne
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpBijFAndExpandsFLin
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FrameSqEqOfSymmetricThetaElementStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SymmetricFramePhiPowOrderEqIdStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.SymLiftPhi

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem exists_ratio (hG : GlobalFnsSt) {k : ℕ} (p : QkPt D F k) {w w' : Frm D F k p.g.b} (hw : w.IsGen) (hw' : w'.IsGen) :
    ∃ c : F, (∀ z J, Good D.P.L z J → (val w' (𝟙 _) z J).val ^ k = gs (𝟙 _) z ⊤
        ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c ^ k)) * (val w (𝟙 _) z J).val ^ k) ∧
      ∀ s t : Fam D F k, PhiRel D F k p w s t → PhiRel D F k p w' s (c • t) := by
  obtain ⟨a, ha⟩ := H1.exists_const D.P.L D.P.isLB (𝟙 _) (fun a => ⟨a, rfl⟩)
    (LB.mulGen D.P.L _ _ _ _ w' (LB.invGen D.P.L _ _ w))
    (mulGen_isGen _ _ _ _ _ _ _ hw' (invGen_isGen _ _ _ _ hw)) (fun U _ h => by
      refine (prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := U) _ rfl (prod_neg _ _ rfl)).trans ?_
      exact mul_inv_cancel _)
  obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 a
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ (TF (R := R) F).left) (z : Z) (J), Good D.P.L z J →
      (val w' r z J).val = gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) * (val w r z J).val := by
    intro Z r z J hJ
    have e := ha Z r z J hJ
    rw [val_mul hJ, val_inv, Category.comp_id] at e
    refine Eq.trans ?_ (congrArg (· * (val w r z J).val) e)
    rw [← Units.val_mul, inv_mul_cancel_right]
  refine ⟨c, fun z J hJ => ?_, fun s t h => ?_⟩
  · rw [hv _ _ z J hJ, mul_pow, gs_eq _ z ⊤ trivial, gs_eq _ z ⊤ trivial, map_pow, map_pow, map_pow]
  · rw [phiRel_iff hG p w hw] at h
    rw [phiRel_iff hG p w' hw']
    intro α β hαβ T ρ z J hJ
    refine (sval_smul c t β ρ.left z hJ).trans ?_
    rw [h α β hαβ T ρ z J hJ, val_mul hJ, val_mul hJ]
    simp only [Units.val_mul]
    rw [hv _ _ z J hJ]
    simp only [Over.comp_left]
    ring

theorem phiRel_of_val_eq (hG : GlobalFnsSt) {k : ℕ} (p : QkPt D F k) {w w' : Frm D F k p.g.b} (hw : w.IsGen)
    (hw' : w'.IsGen) (h : ∀ z J, Good D.P.L z J → val w (𝟙 _) z J = val w' (𝟙 _) z J) {s t : Fam D F k}
    (hs : PhiRel D F k p w' s t) : PhiRel D F k p w s t := by
  have hc := corr_of_val D.P.isLB h
  rw [phiRel_iff hG p w' hw'] at hs
  rw [phiRel_iff hG p w hw]
  intro α β hαβ T ρ z J hJ
  rw [hs α β hαβ T ρ z J hJ, val_mul hJ, val_mul hJ, val_corr hJ hc]

end GlobalTheory.UT.SymLiftPhi

namespace GlobalTheory.UT
open SymLiftPhi in

theorem symLift_acts_as_phi : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (N : ℕ), Odd N → ∀ (p : QkPt D.toPre F N) x, QkToAkU U.toUnifPre F N p x → ∀ (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F)), SymLift A.A A.L N N x θ → ∀ (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ w, TXFrame N p w → ∀ t t' s s', U.ExpandsF F N w₀ t s → U.ExpandsF F N w₀ t' s' → IsActOf A.A A.L N θ t t' → PhiRel D.toPre F N p w s s' := by
  intro hL R _ _ _ I hI D A G _ _ hG U F _ _ _ N hN p x hx θ hθ w₀ hw₀ w hw t t' s s' hs hs' hact
  have hN1 : 1 ≤ N := hN.pos
  have gf : GlobalFnsSt := hL.1.globalFns
  obtain ⟨hxN, hx'⟩ := hx w₀ hw₀
  obtain ⟨w', hw', H⟩ := hx' θ hθ.pt_eq
  obtain ⟨b₁, b₂⟩ := (expBijF_and_expandsF_lin hL R I hI D A G hG U).1 F N hN1 w₀ hw₀
  obtain ⟨Φ, hΦ⟩ := phiFun_of hL.1 R I D F N hN1 p w hw.1
  obtain ⟨Φ', hΦ'⟩ := phiFun_of hL.1 R I D F N hN1 p w' hw'
  obtain ⟨c, hc, hcΦ⟩ := exists_ratio gf p hw.1 hw'
  have e : Φ' = c • Φ := LinearMap.ext fun u => ((hΦ' _ _).1 (hcΦ u _ ((hΦ _ _).2 rfl))).symm
  have h₁ : ∀ u, (Φ ^ N) u = u := fun u => by
    have := GlobalTheory.T.symmetricFrame_phi_pow_order_eq_id hL R I hI D F N hN p w hw (fun i => (Φ ^ (i : ℕ)) u) (fun i => (hΦ _ _).2 (by
      simp [pow_succ']))
    simpa using this
  have h₂ : ∀ u, (Φ' ^ N) u = u := fun u => by
    choose act hact using fun v => GlobalTheory.ThetaNu.exists_isActOf A.isLB θ v
    obtain ⟨v, hv, -⟩ := b₂ u
    have key : ∀ i : ℕ, U.ExpandsF F N w₀ (act^[i] v) ((Φ' ^ i) u) := fun i => by
      induction i with
      | zero => exact hv
      | succ i ih =>
        obtain ⟨u', hu', -⟩ := b₁ (act^[i + 1] v)
        have := (hΦ' _ _).1 (H _ _ _ _ ih hu' (by rw [Function.iterate_succ_apply']; exact hact _))
        rw [pow_succ', Module.End.mul_apply, ← this]
        exact hu'
    have hp := GlobalTheory.thetaGrp_act_iterate_eq_of_pow_eq_one _ A.A A.L A.isLB N _ θ N (hθ.pt_eq ▸ hxN) hθ.pow_eq
      (fun i => act^[i] v) (fun i => by
        rw [Fin.val_succ, Fin.val_castSucc, Function.iterate_succ_apply']; exact hact _)
    have hp' : act^[N] v = v := SecOps.sec_ext hp
    have kN := key N
    rw [hp'] at kN
    exact (b₁ v).unique kN hv
  by_cases hcN : c ^ N = 1
  · have hT : TXFrame N p w' := ⟨hw', GlobalTheory.T.frame_sq_eq_of_symmetric_thetaElement hL R I hI D A G hG U F N hN1 p θ w₀ w' hw₀ hw' H hθ.sym,
      fun κ hκ z J hJ => by
        have a := hc z J hJ
        rw [hcN, map_one, gs_eq _ z ⊤ trivial, map_one, map_one, _root_.one_mul,
          ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val] at a
        rw [Units.ext a]
        exact hw.2.2 κ hκ z J hJ⟩
    exact phiRel_of_val_eq gf p hw.1 hw' ((GlobalTheory.UT.SymFrame.main hL R I hI D F N hN p).2 w w' hw hT) (H t t' s s' hs hs' hact)
  · have z : ∀ u : Fam D.toPre F N, u = 0 := fun u => by
      have a := h₂ u
      rw [e, smul_pow, LinearMap.smul_apply, h₁] at a
      have b : (c ^ N - 1) • u = 0 := by rw [sub_smul, a, one_smul, sub_self]
      exact (smul_eq_zero.1 b).resolve_left (sub_ne_zero.2 hcN)
    exact (hΦ _ _).2 ((z _).trans (z _).symm)

end GlobalTheory.UT
end
