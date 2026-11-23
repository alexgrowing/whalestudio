import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianPartConst
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeISupInfPreimage
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothRayQuotient
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
namespace GlobalTheory.Heat.AbDescent

theorem pbT_id {X : Scheme.{0}} {U V : X.Opens} (hV : V ≤ U) (s : Γ(X, U)) : pbT (𝟙 X) s V = rsT s V := by
  rw [GlobalTheory.KS.pbT_of_le (𝟙 X) hV, GlobalTheory.KS.rsT_of_le hV]
  simp [Scheme.Hom.appLE, resG]
  rfl

theorem pbT_pbT_id {Z X : Scheme.{0}} (q : Z ⟶ X) {U V : X.Opens} (hV : V ≤ U) {W : Z.Opens} (hW : W ≤ q ⁻¹ᵁ V)
    (s : Γ(X, U)) : pbT q (pbT (𝟙 X) s V) W = pbT q s W := by
  rw [pbT_id hV, GlobalTheory.KS.pbT_rsT q hV hW]

theorem descent : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (δH : Fld Y.H.left) (δ : Fld Q.P.A.left), (∀ (U : Q.P.A.left.Opens) (s : Γ(Q.P.A.left, U)) (W : Y.H.left.Opens), W ≤ Y.q.left ⁻¹ᵁ U → δH W (pbT Y.q.left s W) = pbT Y.q.left (δ U s) W) → ∀ (K : Type) (Wk : K → Y.H.left.Opens) (jk : K → Q.P.L.ι), (∀ k, ∃ V : Q.P.A.left.Opens, Wk k = Y.q.left ⁻¹ᵁ V) → ⨆ k, Wk k = ⊤ → (∀ k, Wk k ≤ Y.q.left ⁻¹ᵁ Q.P.L.U (jk k)) → ∀ (P : ∀ k, Γ(Y.H.left, Wk k)), (∀ k, IsWt Y 0 _ (P k)) → (∀ k k' (Wo : Y.H.left.Opens), Wo ≤ Wk k ⊓ Wk k' → rsT (P k') Wo - rsT (P k) Wo = dlg Y.H Y.q.left Q.P.L δH (jk k) (jk k') Wo) → ∃ (V : K → Q.P.A.left.Opens) (b : ∀ k, Γ(Q.P.A.left, V k)), ⨆ k, V k = ⊤ ∧ (∀ k, V k ≤ Q.P.L.U (jk k)) ∧ ∀ k k', rsT (b k') (V k ⊓ V k') - rsT (b k) (V k ⊓ V k') = dlg Q.P.A (𝟙 _) Q.P.L δ (jk k) (jk k') (V k ⊓ V k') := by
  intro R _ _ Q O _ _ _ oa Y δH δ hpb K Wk jk hV hcov hle P hP hrel
  have := Y.smooth_q
  have := (AbConst.surjective_q Y).1
  choose V hV using hV
  have hb : ∀ k, ∃ b : Γ(Q.P.A.left, V k), pbT Y.q.left b (Wk k) = P k := by
    intro k
    have key : ∀ (W : Y.H.left.Opens) (hW : W = Y.q.left ⁻¹ᵁ V k) (p : Γ(Y.H.left, W)), IsWt Y 0 W p →
        ∃ b : Γ(Q.P.A.left, V k), pbT Y.q.left b W = p := by
      intro W hW p hp
      subst hW
      obtain ⟨a, ha⟩ := AbConst.exists_app_eq Y hp
      exact ⟨a, by rw [GlobalTheory.KS.pbT_of_le _ le_rfl, ← ha, Scheme.Hom.app_eq_appLE]⟩
    exact key _ (hV k) _ (hP k)
  choose b hb using hb
  have hVle : ∀ k, V k ≤ Q.P.L.U (jk k) := by
    intro k y hy
    obtain ⟨x, rfl⟩ := Y.q.left.surjective y
    have hx : x ∈ Wk k := by rw [hV k]; exact hy
    exact hle k hx
  refine ⟨V, b, ?_, hVle, ?_⟩
  · rw [eq_top_iff]
    intro y _
    obtain ⟨x, rfl⟩ := Y.q.left.surjective y
    have hx : x ∈ ⨆ k, Wk k := by rw [hcov]; trivial
    rw [TopologicalSpace.Opens.mem_iSup] at hx ⊢
    obtain ⟨k, hk⟩ := hx
    exact ⟨k, by rw [hV k] at hk; exact hk⟩
  · intro k k'
    have hWo : Y.q.left ⁻¹ᵁ (V k ⊓ V k') ≤ Wk k ⊓ Wk k' := by
      rw [hV k, hV k']
      exact fun x hx => ⟨hx.1, hx.2⟩
    have h := hrel k k' _ hWo
    apply FunDescent.app_injective Y.q.left (V k ⊓ V k')
    have e : ∀ s : Γ(Q.P.A.left, V k ⊓ V k'),
        (Y.q.left.app (V k ⊓ V k')).hom s = pbT Y.q.left s (Y.q.left ⁻¹ᵁ (V k ⊓ V k')) := fun s => by
      rw [GlobalTheory.KS.pbT_of_le _ le_rfl, Scheme.Hom.app_eq_appLE]
    rw [e, e, GlobalTheory.KS.pbT_sub, GlobalTheory.KS.pbT_rsT _ inf_le_right le_rfl, GlobalTheory.KS.pbT_rsT _ inf_le_left le_rfl]
    have hbk : ∀ j, Y.q.left ⁻¹ᵁ (V k ⊓ V k') ≤ Wk j →
        pbT Y.q.left (b j) (Y.q.left ⁻¹ᵁ (V k ⊓ V k')) = rsT (P j) (Y.q.left ⁻¹ᵁ (V k ⊓ V k')) := by
      intro j hj
      rw [← hb j, GlobalTheory.KS.rsT_pbT _ (hV j).le hj]
    rw [hbk k' (hWo.trans inf_le_right), hbk k (hWo.trans inf_le_left), h]
    have hUo : V k ⊓ V k' ≤ Q.P.L.U (jk k) ⊓ Q.P.L.U (jk k') := inf_le_inf (hVle k) (hVle k')
    unfold dlg
    rw [GlobalTheory.KS.pbT_mul, ← hpb (V k ⊓ V k') (pbT (𝟙 _) (Q.P.L.g (jk k) (jk k')).val (V k ⊓ V k')) _ le_rfl,
      pbT_pbT_id _ hUo le_rfl, pbT_pbT_id _ hUo le_rfl]

end GlobalTheory.Heat.AbDescent
