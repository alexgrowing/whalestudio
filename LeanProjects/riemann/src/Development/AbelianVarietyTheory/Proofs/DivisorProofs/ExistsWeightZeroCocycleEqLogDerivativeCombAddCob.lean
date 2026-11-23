import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeISupInfPreimage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantHeatOperatorPreservesWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniquePullbackOfRaynaudTorusWeightZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantFieldsCechH1RelationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogDerivPolarizationRaynaudEqPullbackStatement
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

namespace GlobalTheory.PullbackWeightZero

theorem valR_pbT {A : Type} [CommRing A] {X Z : Scheme.{0}} (x : Sp A ⟶ Z) (q : Z ⟶ X) (V : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ (q ⁻¹ᵁ V)) (f : Γ(X, V)) :
    valR x (q ⁻¹ᵁ V) (pbT q f (q ⁻¹ᵁ V)) = valR (x ≫ q) V f := by
  rw [GlobalTheory.Heat.WtAlg.valR_eq' x _ h, GlobalTheory.KS.pbT_of_le q le_rfl, GlobalTheory.Heat.WtAlg.valR_eq' (x ≫ q) V h]
  rw [← Scheme.Hom.appLE_comp_appLE x q V (q ⁻¹ᵁ V) ⊤ le_rfl h]
  rfl

theorem isWt_pbT : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (V : Q.P.A.left.Opens) (f : Γ(Q.P.A.left, V)), IsWt Y 0 _ (pbT Y.q.left f (Y.q.left ⁻¹ᵁ V)) := by
  intro R _ _ Q O _ _ _ oa Y V f S _ φ x x' c a a' ha ha' hV hV' hq hc
  rw [GlobalTheory.Heat.WtAlg.c_zero x x' c hc, Units.val_one, _root_.one_mul, valR_pbT _ _ _ hV', valR_pbT _ _ _ hV]
  subst ha ha'
  have e : x'.left ≫ Y.q.left = x.left ≫ Y.q.left := by
    rw [← Over.comp_left, ← Over.comp_left, hq]
  rw [e]

theorem descend : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (V : Q.P.A.left.Opens) (f : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V)), IsWt Y 0 _ f → ∃! f' : Γ(Q.P.A.left, V), pbT Y.q.left f' (Y.q.left ⁻¹ᵁ V) = f := GlobalTheory.T.existsUnique_pullback_of_raynaudTorusWeight_zero

theorem h1cover : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (g : ℕ) (w : Fin g → TanM (𝟙 (Sp R)) Dd.toPre.P.A) (dd' : Fin g → Fld Dd.toPre.P.A.left), (∀ a, IsInv Dd.toPre.P.A (w a) (dd' a)) → (∀ u : TanM (𝟙 (Sp R)) Dd.toPre.P.A, ∃ cf : Fin g → R, u = ∑ a, cf a • w a) → ∀ (J : Type) (V : J → Dd.toPre.P.A.left.Opens) (j : J → Dd.toPre.P.L.ι), ⨆ i, V i = ⊤ → (∀ i, V i ≤ Dd.toPre.P.L.U (j i)) → ∀ z : C1 V, IsCoc V z → ∃ (c : Fin g → R) (y : ∀ i, Γ(Dd.toPre.P.A.left, V i)), ∀ i i', z i i' = ∑ a, constFn Dd.toPre.P.A.hom _ (c a) * rsT (dlg Dd.toPre.P.A (𝟙 _) Dd.toPre.P.L (dd' a) (j i) (j i') (Dd.toPre.P.L.U (j i) ⊓ Dd.toPre.P.L.U (j i'))) (V i ⊓ V i') + (rsT (y i') (V i ⊓ V i') - rsT (y i) (V i ⊓ V i')) := GlobalTheory.T.invariant_fields_cech_h1_relation

theorem liepush : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∃ (g : ℕ) (w : Fin g → TanM (𝟙 (Sp R)) Dd.toPre.P.A) (dd' : Fin g → Fld Dd.toPre.P.A.left) (M : Fin n → Fin g → R) (N : Fin g → Fin n → R), (∀ a, IsInv Dd.toPre.P.A (w a) (dd' a)) ∧ (∀ u : TanM (𝟙 (Sp R)) Dd.toPre.P.A, ∃ cf : Fin g → R, u = ∑ a, cf a • w a) ∧ (∀ a a', ∑ b, N a b * M b a' = if a = a' then 1 else 0) ∧ ∀ (b : Fin n) (i i' : Dd.toPre.P.L.ι) (W : Y.H.left.Opens), W ≤ Y.q.left ⁻¹ᵁ (Dd.toPre.P.L.U i ⊓ Dd.toPre.P.L.U i') → dlg Y.H Y.q.left Dd.toPre.P.L (dd b) i i' W = pbT Y.q.left (∑ a, constFn Dd.toPre.P.A.hom _ (M b a) * dlg Dd.toPre.P.A (𝟙 _) Dd.toPre.P.L (dd' a) i i' (Dd.toPre.P.L.U i ⊓ Dd.toPre.P.L.U i')) W := GlobalTheory.T.exists_logDeriv_polarization_raynaud_eq_pullback

theorem alg_sum {Γ₀ R : Type} [CommRing Γ₀] [CommRing R] {g n : ℕ} (κ : R →+* Γ₀) (c' : Fin g → R) (N : Fin g → Fin n → R)
    (M : Fin n → Fin g → R) (hNM : ∀ a a', ∑ b, N a b * M b a' = if a = a' then 1 else 0) (X : Fin g → Γ₀) :
    ∑ a, κ (c' a) * X a = ∑ b, κ (∑ a, c' a * N a b) * ∑ a', κ (M b a') * X a' := by
  have e : ∀ a', ∑ b, (∑ a, c' a * N a b) * M b a' = c' a' := by
    intro a'
    simp_rw [Finset.sum_mul, _root_.mul_assoc]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hNM]
    simp
  simp_rw [Finset.mul_sum, ← _root_.mul_assoc, ← map_mul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, ← map_sum, e]

theorem h1_pull : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (J : Type) (V : J → Dd.toPre.P.A.left.Opens) (j : J → Dd.toPre.P.L.ι), ⨆ i, V i = ⊤ → (∀ i, V i ≤ Dd.toPre.P.L.U (j i)) → ∀ z : C1 V, IsCoc V z → ∃ (c : Fin n → R) (y : ∀ i, Γ(Dd.toPre.P.A.left, V i)), ∀ i i', pbT Y.q.left (z i i') (Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i') = ∑ b, constFn Y.H.hom _ (c b) * dlg Y.H Y.q.left Dd.toPre.P.L (dd b) (j i) (j i') (Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i') + (pbT Y.q.left (y i') (Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i') - pbT Y.q.left (y i) (Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i')) := by
  intro R _ _ _ _ _ _ Dd O _ _ _ oa Y n v dd hdd J V j hcov hle z hz
  obtain ⟨g, w, dd', M, N, hw, hsp, hNM, hdl⟩ := liepush R Dd O oa Y n v dd hdd
  obtain ⟨c', y, hc'⟩ := h1cover R Dd g w dd' hw hsp J V j hcov hle z hz
  refine ⟨fun b => ∑ a, c' a * N a b, y, fun i i' => ?_⟩
  have hW : Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i' ≤
      Y.q.left ⁻¹ᵁ (Dd.toPre.P.L.U (j i) ⊓ Dd.toPre.P.L.U (j i')) :=
    Y.q.left.preimage_mono (inf_le_inf (hle i) (hle i'))
  have hq : Y.q.left ≫ Dd.toPre.P.A.hom = Y.H.hom := Over.w Y.q
  rw [hc' i i', GlobalTheory.KS.pbT_add, GlobalTheory.KS.pbT_sub, GlobalTheory.KS.pbT_rsT _ (O₂ := Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i') inf_le_right le_rfl,
    GlobalTheory.KS.pbT_rsT _ (O₂ := Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i') inf_le_left le_rfl]
  congr 1
  simp only [hdl _ _ _ _ hW, GlobalTheory.KS.pbT_sum, GlobalTheory.KS.pbT_mul]
  simp only [GlobalTheory.KS.pbT_constFn _ _ hW, GlobalTheory.KS.pbT_constFn _ Y.q.left (O₀ := V i ⊓ V i') (O := Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i') le_rfl,
    GlobalTheory.KS.pbT_rsT _ (O₂ := Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i') (inf_le_inf (hle i) (hle i')) le_rfl, hq]
  exact alg_sum ((Y.H.hom.appLE ⊤ _ (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) c' N M hNM _

theorem exists_comb_dlg_add_cob : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (J : Type) (V : J → Dd.toPre.P.A.left.Opens) (j : J → Dd.toPre.P.L.ι),
    ⨆ i, V i = ⊤ → (∀ i, V i ≤ Dd.toPre.P.L.U (j i)) → (∀ z : C1 (fun i => Y.q.left ⁻¹ᵁ V i), IsCoc _ z → (∀ i i', IsWt Y 0 _ (z i i')) →
      ∃ (c : Fin n → R) (y : ∀ i, Γ(Y.H.left, Y.q.left ⁻¹ᵁ V i)), (∀ i, IsWt Y 0 _ (y i)) ∧ ∀ i i',
        z i i' = ∑ b, constFn Y.H.hom _ (c b) * dlg Y.H Y.q.left Dd.toPre.P.L (dd b) (j i) (j i') _ +
          (rsT (y i') (Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i') - rsT (y i) (Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i'))) := by
  intro R _ _ _ _ _ _ Dd O _ _ _ oa Y n v dd hdd J V j hcov hle z hz hw
  have hA := descend R Dd.toPre O oa Y
  have hB := isWt_pbT R Dd.toPre O oa Y
  choose z' hz' using fun i i' => (hA (V i ⊓ V i') (z i i') (hw i i')).exists
  have hcoc : IsCoc V z' := by
    intro i i' i''
    apply (hA (V i ⊓ V i' ⊓ V i'') _ (hB _ (rsT (z' i i'') (V i ⊓ V i' ⊓ V i'')))).unique _ rfl
    rw [GlobalTheory.KS.pbT_add, GlobalTheory.KS.pbT_rsT _ inf_le_left le_rfl, GlobalTheory.KS.pbT_rsT _ (le_inf (inf_le_left.trans inf_le_right) inf_le_right) le_rfl,
      GlobalTheory.KS.pbT_rsT _ (le_inf (inf_le_left.trans inf_le_left) inf_le_right) le_rfl]
    have e1 : rsT (z i i') (Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i' ⊓ Y.q.left ⁻¹ᵁ V i'') =
        pbT Y.q.left (z' i i') (Y.q.left ⁻¹ᵁ (V i ⊓ V i' ⊓ V i'')) := by
      rw [← hz' i i']; exact GlobalTheory.KS.rsT_pbT _ le_rfl inf_le_left _
    have e2 : rsT (z i' i'') (Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i' ⊓ Y.q.left ⁻¹ᵁ V i'') =
        pbT Y.q.left (z' i' i'') (Y.q.left ⁻¹ᵁ (V i ⊓ V i' ⊓ V i'')) := by
      rw [← hz' i' i'']; exact GlobalTheory.KS.rsT_pbT _ le_rfl (le_inf (inf_le_left.trans inf_le_right) inf_le_right) _
    have e3 : rsT (z i i'') (Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i' ⊓ Y.q.left ⁻¹ᵁ V i'') =
        pbT Y.q.left (z' i i'') (Y.q.left ⁻¹ᵁ (V i ⊓ V i' ⊓ V i'')) := by
      rw [← hz' i i'']; exact GlobalTheory.KS.rsT_pbT _ le_rfl (le_inf (inf_le_left.trans inf_le_left) inf_le_right) _
    rw [← e1, ← e2, ← e3]
    exact hz i i' i''
  obtain ⟨c, y', hc⟩ := h1_pull R Dd O oa Y n v dd hdd J V j hcov hle z' hcoc
  refine ⟨c, fun i => pbT Y.q.left (y' i) (Y.q.left ⁻¹ᵁ V i), fun i => hB _ _, fun i i' => ?_⟩
  rw [GlobalTheory.KS.rsT_pbT _ le_rfl inf_le_left, GlobalTheory.KS.rsT_pbT _ le_rfl inf_le_right, ← hc i i']
  exact (hz' i i').symm

end GlobalTheory.PullbackWeightZero
