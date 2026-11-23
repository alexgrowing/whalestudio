import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusInvariantFieldConstCoeffs
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsChartOfMemRedKer
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LieBasisCoordinatesBijectiveTangent
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

namespace GlobalTheory.HeatMod.TorField

open TrivSqZeroExt (inl inr)

theorem residue_eq_zero_of_sq {B : Type} [CommRing B] [IsLocalRing B] (x : B) (h : x * x = 0) :
    IsLocalRing.residue B x = 0 :=
  (IsLocalRing.residue_eq_zero_iff x).2 ((IsLocalRing.mem_maximalIdeal x).2 (mem_nonunits_iff.2 fun hu => by
    have := hu.mul hu
    rw [h] at this
    exact not_isUnit_zero this))

theorem lieExp_comp_q_eq_one : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (v : Fin n → TanM (𝟙 (Sp R)) Y.H) (u : Fin n → (epsR R ⟶ Y.H)), (∀ a, IsTangent (u a)) → (∀ a, (u a).left = (tv (v a)).left) → ∀ (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ e : Fin n → R, (∀ (V : Q.P.A.left.Opens) f, IsWt Y 0 (Y.q.left ⁻¹ᵁ V) f → ∑ a, constFn Y.H.hom _ (e a) * dd a _ f = 0) → ∀ (B : Type) [CommRing B] [IsLocalRing B] (ψ : DualNumber R →+* B), spMap ψ ≫ (GlobalTheory.SqZero.lieExp u (fun a => (TrivSqZeroExt.inr (e a) : DualNumber R)) (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _) ≫ Y.q).left = spMap ψ ≫ (1 : epsR R ⟶ Q.P.A).left := by
  intro R _ _ Q O _ _ _ oa Y n v u ht hu dd hd e hw B _ _ ψ
  letI : Algebra R B := (ψ.comp (TrivSqZeroExt.inlHom R R)).toAlgebra
  let ψ' : DualNumber R →ₐ[R] B := { ψ with commutes' := fun r => rfl }
  have hqm : IsMonHom Y.q := Y.q_linear.isMonHom
  let c : Fin n → DualNumber R := fun a => inr (e a)
  have hc : ∀ a, c a * c a = 0 := fun _ => TrivSqZeroExt.inr_mul_inr _ _ _
  let p : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) (DualNumber R) ⟶ Y.H := GlobalTheory.SqZero.lieExp u c hc
  let z : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) B ⟶ Y.H := 1
  let t : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) B ⟶ Y.H := ReciprocityTheory.ChartRestriction.G.Chart.spMap ψ' ≫ p
  have hψ : (ReciprocityTheory.ChartRestriction.G.Chart.spMap ψ').left = spMap ψ := ReciprocityTheory.ChartRestriction.G.Chart.spMap_left ψ'
  have e1 : spMap ψ ≫ (p ≫ Y.q).left = t.left ≫ Y.q.left := by
    rw [← hψ]; rfl
  have e2 : spMap ψ ≫ (1 : epsR R ⟶ Q.P.A).left = z.left ≫ Y.q.left := by
    rw [← hψ, ← Over.comp_left, ← Over.comp_left]
    congr 1
    rw [ReciprocityTheory.ChartRestriction.G.Chart.comp_one', MonObj.one_comp]
  show spMap ψ ≫ (p ≫ Y.q).left = _
  rw [e1, e2]

  refine ReciprocityTheory.ChartRestriction.G.PullbackSections.hom_ext_of_local (R := CommRingCat.of B) ?_ ?_
  · letI : Algebra R (IsLocalRing.ResidueField B) :=
      ((IsLocalRing.residue B).comp (algebraMap R B)).toAlgebra
    let r : B →ₐ[R] IsLocalRing.ResidueField B := { IsLocalRing.residue B with commutes' := fun _ => rfl }
    have htan : IsTangent p :=
      GlobalTheory.Reg.isTangent_of_isLieComb ht ((GlobalTheory.SqZero.isLieComb_iff_lieExp e p).2 rfl)
    have hrc : r.comp ψ' = (Algebra.ofId R (IsLocalRing.ResidueField B)).comp (ReciprocityTheory.ChartRestriction.G.Chart.fstD R) :=
      DualNumber.algHom_ext (by
        have : r (ψ' DualNumber.eps) = 0 := residue_eq_zero_of_sq _ (by
          rw [← map_mul, DualNumber.eps_mul_eps, map_zero])
        rw [AlgHom.comp_apply, this, AlgHom.comp_apply]
        simp [ReciprocityTheory.ChartRestriction.G.Chart.fstD])
    have hr : ReciprocityTheory.ChartRestriction.G.Chart.spMap r ≫ t = ReciprocityTheory.ChartRestriction.G.Chart.spMap r ≫ z := by
      rw [ReciprocityTheory.ChartRestriction.G.Chart.comp_one']
      show ReciprocityTheory.ChartRestriction.G.Chart.spMap r ≫ ReciprocityTheory.ChartRestriction.G.Chart.spMap ψ' ≫ p = 1
      rw [← Category.assoc, ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp, hrc, ← ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp,
        Category.assoc, show ReciprocityTheory.ChartRestriction.G.Chart.spMap (ReciprocityTheory.ChartRestriction.G.Chart.fstD R) ≫ p = 1 from
          (ReciprocityTheory.ChartRestriction.G.Chart.isTan_iff p).2 htan, ReciprocityTheory.ChartRestriction.G.Chart.comp_one']
    have H : (ReciprocityTheory.ChartRestriction.G.Chart.spMap r).left ≫ t.left ≫ Y.q.left =
        (ReciprocityTheory.ChartRestriction.G.Chart.spMap r).left ≫ z.left ≫ Y.q.left := by
      rw [← Category.assoc, ← Category.assoc]
      exact congrArg (fun f => Over.Hom.left f ≫ Y.q.left) hr
    rw [ReciprocityTheory.ChartRestriction.G.Chart.spMap_left] at H
    have hcp : (Spec.map (CommRingCat.ofHom r.toRingHom)).base (IsLocalRing.closedPoint (IsLocalRing.ResidueField B)) =
        IsLocalRing.closedPoint (CommRingCat.of B) := IsLocalRing.comap_closedPoint (IsLocalRing.residue B)
    rw [← hcp]
    exact congrArg (fun f => f (IsLocalRing.closedPoint (IsLocalRing.ResidueField B))) H
  · intro U h₁ h₂
    have H : ∀ g, valR (t.left ≫ Y.q.left) U g = valR (z.left ≫ Y.q.left) U g := by
      intro g
      have hz : ⊤ ≤ z.left ⁻¹ᵁ (Y.q.left ⁻¹ᵁ U) := h₂
      let e' : Fin n → B := fun a => ψ' (c a)
      have he' : ∀ i j, e' i * e' j = 0 := fun i j => by
        simp only [e', ← map_mul, c, TrivSqZeroExt.inr_mul_inr, map_zero]
      obtain ⟨b₁, b₂⟩ := valR_prod hu ht hd e' he' z (Y.q.left ⁻¹ᵁ U) hz Finset.univ
      have ht' : t = (∏ i ∈ Finset.univ, (ReciprocityTheory.ChartRestriction.G.Chart.spMap (GlobalTheory.SqZero.epsTo R (e' i) (he' i i)) ≫ u i :
          ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) B ⟶ Y.H)) * z := by
        rw [_root_.mul_one]
        exact GlobalTheory.SqZero.comp_lieExp u ψ' c hc
      rw [← ht'] at b₁ b₂
      have hF : pbT Y.q.left g (Y.q.left ⁻¹ᵁ U) = (Y.q.left.appLE U (Y.q.left ⁻¹ᵁ U) le_rfl).hom g :=
        GlobalTheory.KS.pbT_of_le _ le_rfl g
      have hwF := hw U _ (isWt_pbT Y U g (Y.q.left ⁻¹ᵁ U) le_rfl)
      rw [← GlobalTheory.Points.valR_appLE t.left Y.q.left le_rfl b₁ g, ← GlobalTheory.Points.valR_appLE z.left Y.q.left le_rfl hz g,
        ← hF, b₂]
      have hz' : z.left ≫ Y.H.hom = spMap (algebraMap R B) := Over.w z
      have key : ∀ i, e' i = ψ (inr 1) * algebraMap R B (e i) := fun i => by
        show ψ (inr (e i)) = ψ (inr 1) * ψ (inl (e i))
        rw [← map_mul]
        congr 1
        ext <;> simp
      have hv := congrArg (valR z.left (Y.q.left ⁻¹ᵁ U)) hwF
      rw [GlobalTheory.ZH.CrdCalc.valR_eq _ _ hz, map_sum, GlobalTheory.ZH.CrdCalc.valR_eq _ _ hz, map_zero] at hv
      simp only [← GlobalTheory.ZH.CrdCalc.valR_eq _ _ hz, WtAlg.valR_mul'' _ _ hz,
        GlobalTheory.Points.valR_constFn_of_over _ _ _ hz' _ hz] at hv
      simp only [key, _root_.mul_assoc, ← Finset.mul_sum, hv, mul_zero, add_zero]
    ext g
    have := H g
    rw [GlobalTheory.ZH.CrdCalc.valR_eq _ _ h₁, GlobalTheory.ZH.CrdCalc.valR_eq _ _ h₂] at this
    exact (Scheme.ΓSpecIso (CommRingCat.of B)).commRingCatIsoToRingEquiv.injective this

end GlobalTheory.HeatMod.TorField
