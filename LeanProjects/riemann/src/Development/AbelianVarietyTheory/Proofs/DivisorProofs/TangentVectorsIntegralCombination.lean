import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DrAtNonneg
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GrNormPosOfBasis
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenframeGenericAffineOpen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntOIsLocalRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeftInverseOfIntegralSolutionsStatement
open NumberField IsDedekindDomain Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovHt.Link GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal
open AlgebraicGeometry CategoryTheory
open GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)

set_option autoImplicit false

namespace GlobalTheory.SatTanNorm

attribute [local instance] Over.cartesianMonoidalCategory

section Comb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X)

theorem grNorm_eq_one_of_comb {C : Type} [NontriviallyNormedField C] {x : Sp C ⟶ X}
    {Λ : Set (Sp (DualNumber C) ⟶ t.G.left)} {m : ℕ} {v : Fin m → (Sp (DualNumber C) ⟶ t.G.left)}
    (hv : ∀ i, IsTanAtG t x (v i))
    (hΛ : ∀ (cf : Fin m → C) (w : Sp (DualNumber C) ⟶ t.G.left), IsCombAtG t x v cf w → (w ∈ Λ ↔ ∀ i, ‖cf i‖ ≤ 1))
    (k : Fin m) : grNorm t x Λ v k = 1 := by
  classical
  refine IsLeast.csInf_eq ⟨⟨Pi.single k 1, by simp, fun j hj => by simp [Pi.single_apply, hj.ne'], ?_, by simp⟩, ?_⟩
  · obtain ⟨w, -, hw⟩ := Guard.exists_comb hv (Pi.single k 1)
    refine ⟨w, (hΛ _ w hw).2 fun i => ?_, hw⟩
    by_cases hi : i = k
    · subst hi; simp
    · simp [Pi.single_apply, hi]
  · rintro r ⟨cf, h0, -, ⟨w, hw, hc⟩, rfl⟩
    exact one_le_inv₀ (norm_pos_iff.2 h0) |>.2 ((hΛ cf w hc).1 hw k)

end Comb

theorem grNorm_latDR_eq_one_of_saturated : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (V Fr : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field Fr] [Algebra V Fr] [IsFractionRing V Fr] (xV : Sp V ⟶ X) (m : ℕ) (v : Fin m → (Sp (DualNumber V) ⟶ t.G.left)), (∀ i, IsTanAtG t xV (v i)) → (∀ (cf : Fin m → Fr) (u : Sp (DualNumber V) ⟶ t.G.left), IsTanAtG t xV u → IsCombAtG t (spMap (algebraMap V Fr) ≫ xV) (fun i => spMap (dualMap (algebraMap V Fr)) ≫ v i) cf (spMap (dualMap (algebraMap V Fr)) ≫ u) → ∀ i, ∃ a : V, algebraMap V Fr a = cf i) → ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] (ψ : V →+* C), (∀ z, ‖ψ z‖ ≤ 1) → (∃! xO : Sp ↥(intO C) ⟶ X, spMap (intO C).subtype ≫ xO = spMap ψ ≫ xV) → ∀ i, grNorm t (spMap ψ ≫ xV) (latDR t (spMap ψ ≫ xV)) (fun k => spMap (dualMap ψ) ≫ v k) i = 1 := by
  intro E _ _ _ H X t V Fr _ _ _ _ _ _ xV m v hv hsat C _ _ ψ hψ huniq
  classical
  obtain ⟨xO, hxO, huO⟩ := huniq
  obtain ⟨n, D, hD, hDb⟩ := GlobalTheory.LieLocBasis.exists_lie_basis_stable E H X t V xV
  have h1 : spMap (RingHom.id V) = 𝟙 _ := Spec.map_id _
  have h2 : dualMap (RingHom.id V) = RingHom.id _ := by
    refine RingHom.ext fun z => ?_
    ext <;> simp [dualMap]
  have h3 : spMap (dualMap (RingHom.id V)) = 𝟙 _ := by rw [h2]; exact Spec.map_id _
  have hD0 : ∀ w, IsTanAtG t xV w → ∃! a : Fin n → V, IsCombAtG t xV D a w := by
    have h := hDb _ (RingHom.id V)
    simp only [h1, h3, Category.id_comp] at h
    exact h
  choose a ha using fun i => (hD0 (v i) (hv i)).exists
  let A : Matrix (Fin n) (Fin m) V := fun j i => a i j

  obtain ⟨B, hBA⟩ := GlobalTheory.T.left_inverse_of_integral_solutions V Fr n m A (fun cf b hb => by
    let α := algebraMap V Fr
    obtain ⟨u, hu, hub⟩ := Guard.exists_comb hD b
    obtain ⟨w, -, hw⟩ := Guard.exists_comb (fun i => GlobalTheory.FactorDepth.isTanAtG_map t α (hv i)) cf
    have hDα := fun j => GlobalTheory.FactorDepth.isTanAtG_map t α (hD j)
    have hl := tanLinG (fun j => spMap (dualMap α) ≫ D j) hDα (fun i => spMap (dualMap α) ≫ v i) (A.map α) cf w
      (fun i => GlobalTheory.LatDRFree.comb_map t α (ha i)) hw
    rw [hb] at hl
    have e := Guard.comb_unique hDα hl (GlobalTheory.LatDRFree.comb_map t α hub)
    rw [e] at hw
    exact hsat cf u hu hw)

  let ψ' : V →+* ↥(intO C) := ψ.codRestrict (intO C) hψ
  have hsub : (intO C).subtype.comp ψ' = ψ := RingHom.ext fun _ => rfl
  have e1 : spMap (intO C).subtype ≫ spMap ψ' ≫ xV = spMap ψ ≫ xV := by
    rw [← Category.assoc, spMap_comp', hsub]
  have e2 : ∀ j, spMap (dualMap (intO C).subtype) ≫ spMap (dualMap ψ') ≫ D j = spMap (dualMap ψ) ≫ D j := by
    intro j
    rw [← Category.assoc, spMap_comp', GlobalTheory.ShFam.ChartValue.dualMap_comp', hsub]
  have hx0 : spMap ψ' ≫ xV = xO := huO _ e1
  have hDC := fun j => GlobalTheory.FactorDepth.isTanAtG_map t ψ (hD j)
  have hDO := fun j => GlobalTheory.FactorDepth.isTanAtG_map t ψ' (hD j)
  have hBA' : (B.map ψ) * (A.map ψ) = 1 := by
    rw [← Matrix.map_mul, hBA, Matrix.map_one _ (map_zero ψ) (map_one ψ)]
  have mem : ∀ z : C, z ∈ intO C ↔ ‖z‖ ≤ 1 := fun _ => Iff.rfl
  intro i
  refine grNorm_eq_one_of_comb t (fun k => GlobalTheory.FactorDepth.isTanAtG_map t ψ (hv k)) (fun cf w hc => ?_) i
  have hl := tanLinG (fun j => spMap (dualMap ψ) ≫ D j) hDC (fun i => spMap (dualMap ψ) ≫ v i) (A.map ψ) cf w
    (fun i => GlobalTheory.LatDRFree.comb_map t ψ (ha i)) hc
  constructor
  · rintro ⟨xO', hx', vO, hvO, rfl⟩
    have ex : xO' = spMap ψ' ≫ xV := (huO _ hx').trans hx0.symm
    subst ex
    obtain ⟨c, hcO, -⟩ := hDb (↥(intO C)) ψ' vO hvO
    have hm := GlobalTheory.LatDRFree.comb_map t (intO C).subtype hcO
    simp only [e1, e2] at hm
    have ec := (hDb C ψ _ (Guard.comb_tan hDC hm)).unique hl hm
    have hcf : cf = (B.map ψ).mulVec ((A.map ψ).mulVec cf) := by
      rw [Matrix.mulVec_mulVec, hBA', Matrix.one_mulVec]
    intro k
    rw [hcf, ec, ← mem]
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Subring.coe_subtype]
    exact Subring.sum_mem _ fun l _ => Subring.mul_mem _ ((mem _).2 (hψ _)) (c l).2
  · intro hcf
    let c : Fin n → ↥(intO C) := fun j => ⟨(A.map ψ).mulVec cf j, by
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
      exact Subring.sum_mem _ fun l _ => Subring.mul_mem _ ((mem _).2 (hψ _)) ((mem _).2 (hcf l))⟩
    obtain ⟨vO, hvO, hcO⟩ := Guard.exists_comb hDO c
    have hm := GlobalTheory.LatDRFree.comb_map t (intO C).subtype hcO
    simp only [e1, e2] at hm
    refine ⟨spMap ψ' ≫ xV, e1, vO, hvO, Guard.comb_unique hDC hm hl⟩

end GlobalTheory.SatTanNorm
