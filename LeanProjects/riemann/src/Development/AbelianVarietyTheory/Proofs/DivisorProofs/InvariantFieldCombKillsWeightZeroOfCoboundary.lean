import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogDerivPolarizationRaynaudEqPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianPartConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentVectorEqZeroOfLogDerivCoboundaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudCechRelationDlogDescendsToAbelianPartStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatUniq

theorem comb_kills_weight_zero : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [Algebra ℚ R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (K : Type) (Wk : K → Y.H.left.Opens) (jk : K → Q.P.L.ι), (∀ k, ∃ V : Q.P.A.left.Opens, Wk k = Y.q.left ⁻¹ᵁ V) → ⨆ k, Wk k = ⊤ → (∀ k, Wk k ≤ Y.q.left ⁻¹ᵁ Q.P.L.U (jk k)) → ∀ (P : ∀ k, Γ(Y.H.left, Wk k)) (e : Fin n → R), (∀ k, IsWt Y 0 _ (P k)) → (∀ k k' (Wo : Y.H.left.Opens), Wo ≤ Wk k ⊓ Wk k' → rsT (P k') Wo - rsT (P k) Wo = ∑ a, constFn Y.H.hom Wo (e a) * dlg Y.H Y.q.left Q.P.L (dd a) (jk k) (jk k') Wo) → ∀ (V : Q.P.A.left.Opens) f, IsWt Y 0 (Y.q.left ⁻¹ᵁ V) f → ∑ a, constFn Y.H.hom _ (e a) * dd a _ f = 0 := by
  intro R _ _ _ _ _ Q O _ _ _ oa Y n v dd hinv K Wk jk hWk hcov hjk P e hP hcob V f hf
  haveI : IsMonHom Y.q := Y.q_linear.isMonHom
  obtain ⟨dw, hdw⟩ := GlobalTheory.RayBasis.exists_isInv (∑ a, e a • v a)
  obtain ⟨δ, hδ⟩ := GlobalTheory.RayBasis.exists_isInv (GlobalTheory.Heat.LiePush.pushL Y.q (∑ a, e a • v a))
  have hcomb : ∀ (W : Y.H.left.Opens) (s : Γ(Y.H.left, W)),
      dw W s = ∑ a, constFn Y.H.hom W (e a) * dd a W s := by
    intro W s
    have h := GlobalTheory.Heat.LiePush.isInv_pbT (𝟙 Y.H) hdw (w := v) hinv e
      (PullbackSections.tanM_ext (by rw [GlobalTheory.Heat.LiePush.tv_pushL]; exact Category.comp_id _)) W s W le_rfl
    simpa only [Over.id_left, GlobalTheory.Heat.LiePush.pbT_id] using h
  have hpull : ∀ (U : Q.P.A.left.Opens) (s : Γ(Q.P.A.left, U)) (W : Y.H.left.Opens), W ≤ Y.q.left ⁻¹ᵁ U →
      dw W (pbT Y.q.left s W) = pbT Y.q.left (δ U s) W := by
    intro U s W hW
    have h := GlobalTheory.Heat.LiePush.isInv_pbT Y.q hdw (g := 1) (w := fun _ => GlobalTheory.Heat.LiePush.pushL Y.q (∑ a, e a • v a))
      (d' := fun _ => δ) (fun _ => hδ) (fun _ => 1) (by simp) U s W hW
    have h1 : constFn Q.P.A.hom U (1 : R) = 1 := by simp [constFn]
    simpa [h1] using h
  obtain ⟨Vs, b, hVcov, hVle, hb⟩ := GlobalTheory.T.raynaud_cech_relation_dlog_descends_to_abelian_part R Q O oa Y dw δ hpull K Wk jk hWk hcov hjk P hP
    (fun k k' Wo hWo => by
      rw [hcob k k' Wo hWo]
      simp only [dlg, hcomb, Finset.sum_mul, _root_.mul_assoc])
  have hw0 : GlobalTheory.Heat.LiePush.pushL Y.q (∑ a, e a • v a) = 0 := GlobalTheory.T.tangentVector_eq_zero_of_logDeriv_coboundary R Q.P _ δ hδ K Vs jk hVcov hVle b hb
  have hδ0 : ∀ (U : Q.P.A.left.Opens) (s : Γ(Q.P.A.left, U)), δ U s = 0 := by
    intro U s
    have h := GlobalTheory.Heat.LiePush.isInv_pbT (𝟙 Q.P.A) hδ (g := 0) (w := Fin.elim0) (d' := Fin.elim0)
      (fun a => a.elim0) Fin.elim0
      (by rw [hw0, map_zero]; simp) U s U le_rfl
    simpa only [Over.id_left, GlobalTheory.Heat.LiePush.pbT_id, Finset.univ_eq_empty, Finset.sum_empty] using h
  obtain ⟨g, hg⟩ := GlobalTheory.Heat.AbConst.exists_app_eq Y hf
  have hfg : f = pbT Y.q.left g (Y.q.left ⁻¹ᵁ V) := by
    rw [← hg, GlobalTheory.KS.pbT_of_le _ le_rfl, Scheme.Hom.app_eq_appLE]
  rw [← hcomb, hfg, hpull V g _ le_rfl, hδ0, GlobalTheory.KS.pbT_zero]

end GlobalTheory.HeatUniq
