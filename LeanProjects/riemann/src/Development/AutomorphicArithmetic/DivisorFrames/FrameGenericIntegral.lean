import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ExistsIsMapToFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagBundleIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentSectionsOnNormalModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentBasisOfSplitTorsion
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.VB GlobalTheory.TangentOrigin GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.LineNorm GlobalTheory.BcLie GlobalTheory.CovTest GlobalTheory.Mean4O GlobalTheory.Cartier GlobalTheory.TrueCx
open scoped ComplexOrder

private theorem UpperTheory.norm_mulVec_le_one {R C : Type} [CommRing R] [NormedField C] [IsUltrametricDist C] (φ : R →+* C)
    (hφ : ∀ r, ‖φ r‖ ≤ 1) {m n : ℕ} (S : Matrix (Fin m) (Fin n) R) (a : Fin n → C) (ha : ∀ i, ‖a i‖ ≤ 1) (k : Fin m) :
    ‖(S.map φ *ᵥ a) k‖ ≤ 1 := by
  change ‖∑ i, φ (S k i) * a i‖ ≤ 1
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hφ _) (norm_nonneg _) (ha i)

open GlobalTheory.LineNorm.Chart ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.LieMet in
open Formalism.MainNotions.DIV.Cons (intO) in
theorem UpperTheory.frame_generic_integral :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (F : Type) [Field F] [NumberField F] (e : F ≃+* c.F) (Y : Var F) (ρ : Y.X ⟶ gen Z) (_ : ρ ≫ genStr Z ≫ spMap e.toRingHom = Y.str) (g₀ : GenFrame e ρ) (τ : E →+* ℂ) (X : Scheme.{0}) (j : Y.X ⟶ X) (ρ' : X ⟶ Z.X), j ≫ ρ' = ρ ≫ genι Z → ∀ (V : X.Opens) (P : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Y.Fn), SplitOn g₀ τ j ρ' V P → LatOn g₀ τ j V P := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ _ e Y ρ _ g₀ τ X j ρ' hj V P hS v hpf ε y yt hyt hin φ f hf a w hw
  obtain ⟨hV, hξ, g, b, S, S', he, hSS, -, hP⟩ := hS
  have hX : Z.X.IsSeparated := by
    have : IsProper Z.s := by exact isProper_toroidalModel_structureMap Z
    exact ⟨by rw [← Limits.terminal.comp_from Z.s]; infer_instance⟩
  obtain ⟨hp, h1, -⟩ := ioOf_spec F v ε
  obtain ⟨γ, hγ⟩ := exists_ringHom hV yt hin
  have hy : j (below y.1) ∈ V := by
    have : (spMap ε.O.subtype ≫ yt) (IsLocalRing.closedPoint _) ∈ V := hin (Set.mem_univ _)
    rwa [hyt] at this
  obtain ⟨α, hα⟩ := exists_stalkHom hV j _ hy
  have hα' : spMap α ≫ hV.fromSpec ≫ ρ' = stalkPt Y (below y.1) ≫ ρ ≫ genι Z := by
    rw [← Category.assoc, hα, Category.assoc, hj]; rfl
  have hι : spMap (evalPt _ V hξ) ≫ hV.fromSpec = genericPt Y ≫ j :=
    GlobalTheory.Points.specMap_valMap_fromSpec hV _ hξ
  have hαι : (toFn (below y.1)).comp α = evalPt _ V hξ :=
    ringHom_ext hV (by
      rw [← spMap_comp', Category.assoc, hα, ← Category.assoc, hι]
      exact congrArg (· ≫ j) (gen_eq _))
  have hι' : spMap (evalPt _ V hξ) ≫ hV.fromSpec ≫ ρ' = genericPt Y ≫ ρ ≫ genι Z := by
    rw [← Category.assoc, hι, Category.assoc, hj]
  have hc : ∀ i, IsCombAtG Z.t (spMap α ≫ hV.fromSpec ≫ ρ') (fun k => spMap (dualMap α) ≫ b k)
      (fun k => α (S k i)) (f.v τ i) := fun i => by
    obtain ⟨s, hs, -⟩ := he.2 _ α (f.v τ i) (by rw [hα']; exact f.tan τ i)
    have h2 := coord_map α (toFn (below y.1)) hs
    rw [hαι] at h2
    obtain ⟨w', h3, h4⟩ := hP i
    obtain rfl : w' = spMap (dualMap (toFn (below y.1))) ≫ f.v τ i :=
      ((comb_iff (g₀.tan τ) _ _).1 h3).trans ((comb_iff (g₀.tan τ) _ _).1 (hf.2 i)).symm
    rw [← hι'] at h4
    have h5 := (he.2 _ (evalPt _ V hξ) _ (comb_tan (fun k => isTan_map _ rfl (he.1 k)) h2)).unique h2 h4
    have h6 : s = fun k => α (S k i) := funext fun k => toFn_injective _
      ((congrFun h5 k).trans (RingHom.congr_fun hαι _).symm)
    rwa [h6] at hs
  have hσ : (Scheme.stalkClosedPointTo y.1).hom.comp α = ε.O.subtype.comp γ := ringHom_ext hV (by
    rw [← spMap_comp', ← spMap_comp', Category.assoc, Category.assoc, hα, hγ, hyt, ← Category.assoc]
    exact congrArg (· ≫ j) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk y.1))
  obtain ⟨ψ, hψ⟩ : ∃ ψ, ψ = valP ε y := ⟨_, rfl⟩
  rw [← hψ] at hw ⊢
  have hn : ∀ r, ‖ψ.comp α r‖ ≤ 1 := fun r => by
    have : (Scheme.stalkClosedPointTo y.1).hom (α r) = γ r := RingHom.congr_fun hσ r
    rw [hψ]
    refine (h1 _).2 ?_
    rw [this]
    exact (γ r).2
  let θ : Γ(X, V) →+* ↥(intO ℂ_[resP v]) := (ψ.comp α).codRestrict _ hn
  have hθ : (intO ℂ_[resP v]).subtype.comp θ = ψ.comp α := rfl
  have hx : spMap ψ ≫ stalkPt Y (below y.1) ≫ ρ ≫ genι Z = spMap (ψ.comp α) ≫ hV.fromSpec ≫ ρ' := by
    rw [← hα', ← Category.assoc, spMap_comp']
  have hx' : spMap (intO ℂ_[resP v]).subtype ≫ spMap θ ≫ hV.fromSpec ≫ ρ' = spMap (ψ.comp α) ≫ hV.fromSpec ≫ ρ' := by
    rw [← hθ, ← Category.assoc, spMap_comp']
  have key := GlobalTheory.HTPres.mem_latDR_iff Z.t hX _ he ℂ_[resP v] θ
  rw [hx', hθ] at key
  rw [hx] at hw ⊢
  have h7 := comb_comb (fun k => isTan_map _ rfl (he.1 k)) (fun i => coord_map α ψ (hc i)) hw
  have h8 : (∑ i, a i • fun k => ψ (α (S k i))) = S.map (ψ.comp α) *ᵥ a := by
    funext k
    simp [mulVec, dotProduct, Finset.sum_apply, _root_.mul_comm]
  rw [key _ _ h7, h8]
  refine ⟨fun h => ?_, UpperTheory.norm_mulVec_le_one _ hn S a⟩
  have := UpperTheory.norm_mulVec_le_one _ hn S' _ h
  rwa [mulVec_mulVec, ← Matrix.map_mul, hSS, Matrix.map_one _ (map_zero _) (map_one _), one_mulVec] at this
