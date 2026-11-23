import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageTrQ
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeatTrans

theorem chart_rel_of_sval : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (x : 𝟙_ (Over (Sp R)) ⟶ Y.H) (k : ℕ) (σ : SecM (GlobalTheory.HeatTrans.tr Y.H x ≫ Y.q.left) Q.P.L k) (τ : SecM Y.q.left Q.P.L k), (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval σ r z J = sval τ (r ≫ GlobalTheory.HeatTrans.tr Y.H x) z J) → ∀ (c : Q.P.L.ι) (U : Y.H.left.Opens), U ≤ Y.q.left ⁻¹ᵁ Q.P.L.U c → rsT (σ.f fun _ => c) (GlobalTheory.HeatTrans.tr Y.H x ⁻¹ᵁ U) = pbT (GlobalTheory.HeatTrans.tr Y.H x) (rsT (τ.f fun _ => c) U) (GlobalTheory.HeatTrans.tr Y.H x ⁻¹ᵁ U) := by
  intro R _ _ Q O _ _ _ oa Y x k σ τ hst c U hU
  have hWσ : tr Y.H x ⁻¹ᵁ U ≤ LB.wchart Q.P.L (fun _ : Fin 1 => tr Y.H x ≫ Y.q.left) (fun _ => c) := fun y hy =>
    Set.mem_iInter.2 fun _ => hU hy
  have hWτ : U ≤ LB.wchart Q.P.L (fun _ : Fin 1 => Y.q.left) (fun _ => c) := fun y hy =>
    Set.mem_iInter.2 fun _ => hU hy
  have e1 : rsT (σ.f fun _ => c) (tr Y.H x ⁻¹ᵁ U) = resG _ hWσ (σ.f fun _ => c) := GlobalTheory.KS.rsT_of_le hWσ _
  have e2 : rsT (τ.f fun _ => c) U = resG _ hWτ (τ.f fun _ => c) := GlobalTheory.KS.rsT_of_le hWτ _
  rw [e1, e2, GlobalTheory.KS.pbT_of_le (tr Y.H x) le_rfl]
  apply fn_ext
  intro y hy
  obtain ⟨J, hJ, hJc⟩ := exists_good Q.P.L Q.P.isLB y (K := Fin 1) (fun _ => tr Y.H x ≫ Y.q.left) (fun _ => c)
    (fun _ _ _ => rfl) (fun _ => Set.mem_iInter.1 (hWσ hy) 0)
  have h1 := hst Y.H.left (𝟙 _) y J hJ
  rw [sval_of σ (𝟙 _) y J (fun _ => c) (fun _ => by rw [Category.id_comp]; exact hJc 0),
    sval_of τ (𝟙 _ ≫ tr Y.H x) y J (fun _ => c) (fun _ => by rw [Category.id_comp]; exact hJc 0)] at h1
  have hTy : (tr Y.H x) ((𝟙 Y.H.left : Y.H.left ⟶ Y.H.left) y) ∈ U := hy
  refine (gs_res (𝟙 _) y hWσ hy _).trans (h1.trans ?_)
  rw [← Scheme.Hom.app_eq_appLE]
  exact ((gs_pull (𝟙 _) (tr Y.H x) y U hTy _).trans (gs_res _ y hWτ hTy _)).symm

end GlobalTheory.HeatTrans
