import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn

noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH

namespace GlobalTheory.UMin.NormIso

def toFld (K : Type) [Field K] : ((Sp K).presheaf.stalk (IsLocalRing.closedPoint K))ˣ →* Kˣ :=
  Units.map (stalkClosedPointIso (CommRingCat.of K)).hom.hom.toMonoidHom

theorem toFld_gm {K : Type} [Field K] {X : Scheme.{0}} (x : Sp K ⟶ X) (U : X.Opens)
    (h : x (IsLocalRing.closedPoint K) ∈ U) (a : Γ(X, U)ˣ) :
    (toFld K (gm x _ U a)).val = valF x U a.val := by
  have hU : ⊤ ≤ x ⁻¹ᵁ U := (GlobalTheory.Points.le_preimage_iff x U).2 h
  have e := GlobalTheory.Points.germ_stalkClosedPointTo_eq_valMap x U hU
  refine Eq.trans ?_ ((congrArg (fun φ => φ.hom a.val) e).trans (GlobalTheory.Points.valR_eq x U hU _).symm)
  exact congrArg (stalkClosedPointIso (CommRingCat.of K)).hom.hom ((gm_val x _ U h a).trans
    (Scheme.Hom.germ_stalkMap_apply x U (IsLocalRing.closedPoint K) h a.val).symm)

theorem toFld_gm_spMap {K K' : Type} [Field K] [Field K'] (σ : K →+* K') {X : Scheme.{0}} (x : Sp K ⟶ X)
    (U : X.Opens) (h : x (IsLocalRing.closedPoint K) ∈ U) (a : Γ(X, U)ˣ) :
    toFld K' (gm (spMap σ ≫ x) _ U a) = Units.map σ.toMonoidHom (toFld K (gm x _ U a)) := by
  have hU : ⊤ ≤ x ⁻¹ᵁ U := (GlobalTheory.Points.le_preimage_iff x U).2 h
  apply Units.ext
  rw [toFld_gm (spMap σ ≫ x) U (hU (x := spMap σ (IsLocalRing.closedPoint K')) trivial)]
  show _ = σ (toFld K (gm x _ U a)).val
  rw [toFld_gm x U h]
  exact GlobalTheory.Points.valR_spMap_comp σ x U hU _

variable {k Ω : Type} [CommRing k] [Field Ω] [Algebra k Ω] {M : RatModel k Ω}

theorem pt_mem {U : M.Z.Opens} (hU : (U : Set M.Z).Nonempty) : M.pt (IsLocalRing.closedPoint Ω) ∈ U :=
  M.top_le_preimage_pt hU (x := IsLocalRing.closedPoint Ω) trivial

theorem unit_ext_pt {U : M.Z.Opens} {a b : Γ(M.Z, U)ˣ}
    (h : M.pt (IsLocalRing.closedPoint Ω) ∈ U → toFld Ω (gm M.pt _ U a) = toFld Ω (gm M.pt _ U b)) : a = b := by
  by_cases hU : (U : Set M.Z).Nonempty
  · have e := congrArg Units.val (h (pt_mem hU))
    rw [toFld_gm _ _ (pt_mem hU), toFld_gm _ _ (pt_mem hU)] at e
    exact Units.ext (M.valF_injective hU e)
  · exact unit_ext fun x hx => absurd ⟨x, hx⟩ hU

theorem exists_unit {U : M.Z.Opens} (c : Ωˣ) (h : ∀ z ∈ U, c.val ∈ M.O z ∧ (c⁻¹).val ∈ M.O z) :
    ∃ a : Γ(M.Z, U)ˣ, M.pt (IsLocalRing.closedPoint Ω) ∈ U → toFld Ω (gm M.pt _ U a) = c := by
  by_cases hU : (U : Set M.Z).Nonempty
  · obtain ⟨f, hf⟩ := (RatModel.mem_ringOn_iff_exists hU).1 (RatModel.mem_ringOn.2 fun z hz => (h z hz).1)
    obtain ⟨g, hg⟩ := (RatModel.mem_ringOn_iff_exists hU).1 (RatModel.mem_ringOn.2 fun z hz => (h z hz).2)
    have e : f * g = 1 := M.res_injective U hU (by
      rw [map_mul, map_one, M.res_apply, M.res_apply, hf, hg, c.mul_inv])
    exact ⟨⟨f, g, e, (mul_comm _ _).trans e⟩, fun hp => Units.ext ((toFld_gm _ _ hp _).trans hf)⟩
  · exact ⟨1, fun hp => absurd ⟨_, hp⟩ hU⟩

variable {Ω' : Type} [Field Ω'] [Algebra Ω Ω'] [Algebra k Ω'] [IsScalarTower k Ω Ω'] {M' : RatModel k Ω'}
  {π : M'.Z ⟶ M.Z}

theorem norm_mem_O [FiniteDimensional Ω Ω'] (hN : Geo.Tor.IsNormalScheme M.Z) [IsFinite π]
    (hπ : M'.pt ≫ π = spMap (algebraMap Ω Ω') ≫ M.pt) {z : M.Z} {U : M.Z.Opens} (hz : z ∈ U) {W : M'.Z.Opens}
    (hW : π ⁻¹ᵁ U ≤ W) (f : Γ(M'.Z, W)) : Algebra.norm Ω (valF M'.pt W f) ∈ M.O z := by
  have hH : M.IsHom M' (IsScalarTower.toAlgHom k Ω Ω') π := hπ
  obtain ⟨V, hV, hzV, hle⟩ := exists_isAffineOpen_mem_and_subset hz
  have hle' : π ⁻¹ᵁ V ≤ W := fun y hy => hW (hle hy)
  have hne : (V : Set M.Z).Nonempty := ⟨z, hzV⟩
  have hne' : ((π ⁻¹ᵁ V : M'.Z.Opens) : Set M'.Z).Nonempty := by
    refine ⟨M'.pt (IsLocalRing.closedPoint Ω'), ?_⟩
    show (M'.pt ≫ π) (IsLocalRing.closedPoint Ω') ∈ V
    rw [hπ]
    exact M.top_le_preimage_pt hne (x := spMap (algebraMap Ω Ω') (IsLocalRing.closedPoint Ω')) trivial
  have hfin : (π.app V).hom.Finite := IsFinite.finite_app π V hV
  have hint := hfin.to_isIntegral (resG M'.Z hle' f)
  let ρ : Γ(M.Z, V) →+* M.O z := (M.res V hne).codRestrict (M.O z) fun a => by
    rw [M.res_apply]; exact RatModel.valF_mem_O hzV a
  have hc : (algebraMap (M.O z) Ω').comp ρ = (M'.res _ hne').comp (π.app V).hom := by
    ext a
    show algebraMap Ω Ω' (M.res V hne a) = M'.res _ hne' (π.app V a)
    rw [M.res_apply, M'.res_apply, hH.valF_app hne]
    rfl
  have h1 : IsIntegral (M.O z) (valF M'.pt W f) := by
    obtain ⟨P, hP, hP0⟩ := hint
    refine ⟨P.map ρ, hP.map ρ, ?_⟩
    rw [Polynomial.eval₂_map, hc, ← M'.valF_resG hle' hne', ← M'.res_apply _ hne', ← Polynomial.hom_eval₂, hP0,
      map_zero]
  have := M.isIntegrallyClosed_O hN z
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 (Algebra.isIntegral_norm Ω h1)
  exact hy ▸ y.2

theorem lbIso_lbPow_finrank [FiniteDimensional Ω Ω'] (hN : Geo.Tor.IsNormalScheme M.Z) [IsFinite π]
    (hπ : M'.pt ≫ π = spMap (algebraMap Ω Ω') ≫ M.pt) (A B : LB M.Z) (e : ℕ)
    (H : LBIso (A.pull π) (B.pull π)) :
    LBIso (lbPow A (Module.finrank Ω Ω' * e)) (lbPow B (Module.finrank Ω Ω' * e)) := by
  obtain ⟨w, hw⟩ := H
  set d := Module.finrank Ω Ω' * e with hd
  let N : Ω'ˣ →* Ωˣ := Units.map (Algebra.norm Ω)
  have hNa : ∀ c : Ωˣ, N (Units.map (algebraMap Ω Ω').toMonoidHom c) = c ^ Module.finrank Ω Ω' := fun c =>
    Units.ext (Algebra.norm_algebraMap c.val)
  have hle : ∀ p : (PUnit → B.ι) × (PUnit → A.ι), π ⁻¹ᵁ ((LB.div (lbPow B d) (lbPow A d)).U p) ≤
      (LB.div (B.pull π) (A.pull π)).U p := fun p y hy =>
    ⟨mem_pull.2 (mem_powChart.1 hy.1), mem_pull.2 (mem_powChart.1 hy.2)⟩
  have hpt : ∀ {U : M.Z.Opens}, M.pt (IsLocalRing.closedPoint Ω) ∈ U →
      π (M'.pt (IsLocalRing.closedPoint Ω')) ∈ U := fun {U} h => by
    show (M'.pt ≫ π) (IsLocalRing.closedPoint Ω') ∈ U
    rw [hπ]
    exact M.top_le_preimage_pt ⟨_, h⟩ (x := spMap (algebraMap Ω Ω') (IsLocalRing.closedPoint Ω')) trivial
  have hex : ∀ p : (PUnit → B.ι) × (PUnit → A.ι), ∃ a : Γ(M.Z, (LB.div (lbPow B d) (lbPow A d)).U p)ˣ,
      M.pt (IsLocalRing.closedPoint Ω) ∈ (LB.div (lbPow B d) (lbPow A d)).U p →
      toFld Ω (gm M.pt _ _ a) = N (toFld Ω' (gm M'.pt _ _ (w.s p))) ^ e := fun p => by
    refine exists_unit _ fun z hz => ?_
    have hp := hle p (hpt (pt_mem ⟨z, hz⟩))
    have key : ∀ u : Γ(M'.Z, (LB.div (B.pull π) (A.pull π)).U p)ˣ,
        (N (toFld Ω' (gm M'.pt _ _ u)) ^ e).val ∈ M.O z := fun u => by
      rw [Units.val_pow_eq_pow_val]
      refine pow_mem ?_ e
      show Algebra.norm Ω (toFld Ω' (gm M'.pt _ _ u)).val ∈ _
      rw [toFld_gm _ _ hp]
      exact norm_mem_O hN hπ hz (hle p) _
    refine ⟨key _, ?_⟩
    rw [← inv_pow, ← map_inv, ← map_inv, ← map_inv]
    exact key _
  choose s hs using hex
  refine ⟨⟨s⟩, fun p q => unit_ext_pt fun hy => ?_⟩
  have hy' : M'.pt (IsLocalRing.closedPoint Ω') ∈ (LB.div (B.pull π) (A.pull π)).U p ⊓
      (LB.div (B.pull π) (A.pull π)).U q := ⟨hle p (hpt hy.1), hle q (hpt hy.2)⟩
  have e₁ := congrArg (gm M'.pt (IsLocalRing.closedPoint Ω') _) (hw p q)
  rw [gm_res _ _ _ hy', map_mul, gm_res _ _ _ hy'] at e₁
  replace e₁ := e₁.trans (congrArg (· * _) (gm_div (A.pull π) (B.pull π) _ _ p q hy'))
  rw [gm_pull_g B π _ _ _ _ hy'.1.1 hy'.2.1, gm_pull_g A π _ _ _ _ hy'.1.2 hy'.2.2, hπ] at e₁
  have e₂ := congrArg (fun u => N (toFld Ω' u) ^ e) e₁
  simp only [map_mul, map_inv] at e₂
  have hB : M.pt (IsLocalRing.closedPoint Ω) ∈ B.U (p.1 PUnit.unit) ⊓ B.U (q.1 PUnit.unit) :=
    ⟨mem_powChart.1 hy.1.1, mem_powChart.1 hy.2.1⟩
  have hA : M.pt (IsLocalRing.closedPoint Ω) ∈ A.U (p.2 PUnit.unit) ⊓ A.U (q.2 PUnit.unit) :=
    ⟨mem_powChart.1 hy.1.2, mem_powChart.1 hy.2.2⟩
  rw [toFld_gm_spMap (algebraMap Ω Ω') M.pt _ hB, toFld_gm_spMap (algebraMap Ω Ω') M.pt _ hA, hNa, hNa] at e₂
  rw [gm_res _ _ _ hy, map_mul, gm_res _ _ _ hy]
  refine Eq.trans ?_ (congrArg (fun u => toFld Ω (u * _)) (gm_div (lbPow A d) (lbPow B d) _ _ p q hy)).symm
  rw [gm_lbPow_g d _ _ _ _ hy.1.1 hy.2.1, gm_lbPow_g d _ _ _ _ hy.1.2 hy.2.2, map_mul, map_mul, map_inv, map_pow,
    map_pow, hs p hy.1, hs q hy.2, e₂, mul_pow, mul_pow, inv_pow, ← pow_mul, ← pow_mul]

theorem lbIso_lbPow_of_pull : ∀ (k Ω : Type) [CommRing k] [IsNoetherianRing k] [Field Ω] [CharZero Ω] [Algebra k Ω] (M : RatModel k Ω) (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [Algebra k Ω'] [IsScalarTower k Ω Ω'] [FiniteDimensional Ω Ω'] (M' : RatModel k Ω') (π : M'.Z ⟶ M.Z) (A B : LB M.Z) (d : ℕ), Geo.Tor.IsNormalScheme M.Z → IsFinite π → M'.pt ≫ π = spMap (algebraMap Ω Ω') ≫ M.pt → A.IsLB → B.IsLB → Module.finrank Ω Ω' ∣ d → LBIso (A.pull π) (B.pull π) → LBIso (lbPow A d) (lbPow B d) := by
  intro k Ω _ _ _ _ _ M Ω' _ _ _ _ _ M' π A B d hN _ hπ _ _ ⟨e, he⟩ H
  subst he
  exact lbIso_lbPow_finrank hN hπ A B e H

end GlobalTheory.UMin.NormIso
