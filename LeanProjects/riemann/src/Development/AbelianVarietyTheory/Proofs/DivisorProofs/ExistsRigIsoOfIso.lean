import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsRigidifiedIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SixthLawsAndUnifUniq
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.NonemptyTorusExtensionOfIsPowGrp
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8LB
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGlueRigidifiedLineBundlesCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RigLBIso

open ReciprocityTheory.ChartRestriction.G.Geo.Tor in

theorem exists_rig_iso_of_iso : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L₁ L₂ : RigLB G), LBIso L₁.L L₂.L → ∃ wL : LB.Iso L₁.L L₂.L, wL.IsGen ∧ LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec G) (fun _ => 1)) L₁.rig L₂.rig := by
  rintro S G _ _ L₁ L₂ ⟨w, hw⟩
  have hw₀ : PGen (isoPullId w (F := 𝟙 G.left) rfl) := isoPullId_pgen hw rfl
  obtain ⟨c, hc⟩ := GlobalTheory.Unif.RigidifyIso.exists_ratio (K := PUnit) (φ' := fun _ => eSec G)
    (φ := fun _ => eSec G) (ε := fun _ => 1) hw₀ L₂.isLB L₁.isLB (𝟙 _)
    (fun _ => by rw [Category.comp_id, Category.id_comp]) L₁.rig L₁.rigGen L₂.rig L₂.rigGen
  let π : G.left ⟶ (𝟙_ (Over S)).left := G.hom
  have hs : eSec G ≫ π = 𝟙 _ := Over.w η[G]
  let wL : LB.Iso L₁.L L₂.L := ⟨fun i => res (le_top : _ ≤ π ⁻¹ᵁ ⊤) (pullU π ⊤ c) * w.s i⟩
  have hv : ∀ (Y : Scheme.{0}) (f : Y ⟶ G.left) (y : Y) (j : L₂.L.ι) (k : L₁.L.ι), f y ∈ L₂.L.U j →
      f y ∈ L₁.L.U k → gv wL f y j k = gm (f ≫ π) y ⊤ c * gv w f y j k := by
    intro Y f y j k hj hk
    have hz : f y ∈ L₂.L.U j ⊓ L₁.L.U k := ⟨hj, hk⟩
    exact (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res f y _ hz _).trans (gm_pull f π y ⊤ trivial c)) rfl)
  refine ⟨wL, ?_, ?_⟩
  · rintro p q
    apply unit_ext
    intro x hx
    have h1 : (𝟙 G.left) x ∈ L₂.L.U p.1 := hx.1.1
    have h2 : (𝟙 G.left) x ∈ L₁.L.U p.2 := hx.1.2
    have h3 : (𝟙 G.left) x ∈ L₂.L.U q.1 := hx.2.1
    have h4 : (𝟙 G.left) x ∈ L₁.L.U q.2 := hx.2.2
    have eL : gm (𝟙 G.left) x _ (res (inf_le_left : (L₂.L.div L₁.L).U p ⊓ (L₂.L.div L₁.L).U q ≤ _) (wL.s p)) =
        gv wL (𝟙 G.left) x p.1 p.2 := gm_res (𝟙 G.left) x _ hx _
    have eR : gm (𝟙 G.left) x _ ((L₂.L.div L₁.L).g p q *
        res (inf_le_right : (L₂.L.div L₁.L).U p ⊓ (L₂.L.div L₁.L).U q ≤ _) (wL.s q)) =
        gm (𝟙 G.left) x _ (L₂.L.g p.1 q.1) * (gm (𝟙 G.left) x _ (L₁.L.g p.2 q.2))⁻¹ * gv wL (𝟙 G.left) x q.1 q.2 :=
      (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_div L₁.L L₂.L (𝟙 G.left) x p q hx) (gm_res (𝟙 G.left) x _ hx _))
    rw [eL, eR, hv _ _ x _ _ h1 h2, hv _ _ x _ _ h3 h4, gm_isGen hw (𝟙 G.left) x p.1 q.1 p.2 q.2 h1 h3 h2 h4]
    exact mul_left_comm _ _ _
  · rintro ⟨P, Q⟩
    apply unit_ext
    intro x hx
    have hj : (eSec G) x ∈ L₂.L.U (P PUnit.unit) := Set.mem_iInter.1 hx.1 PUnit.unit
    have hk : (eSec G) x ∈ L₁.L.U (Q PUnit.unit) := Set.mem_iInter.1 hx.2 PUnit.unit
    have hj' : (𝟙 _ ≫ eSec G) x ∈ L₂.L.U (P PUnit.unit) := Set.mem_iInter.1 hx.1 PUnit.unit
    have hk' : (𝟙 _ ≫ eSec G) x ∈ L₁.L.U (Q PUnit.unit) := Set.mem_iInter.1 hx.2 PUnit.unit
    have hc' := hc _ (𝟙 _) x P Q (by simp only [Category.comp_id]; exact hx.1) hx.2
    have ep : ReciprocityTheory.ChartRestriction.G.Geo.Tor.pw (isoPullId w (F := 𝟙 G.left) rfl) (K := PUnit) (fun _ => eSec G) (fun _ => 1)
        (𝟙 _) x P Q = gv w (𝟙 _ ≫ eSec G) x (P PUnit.unit) (Q PUnit.unit) := by
      show ∏ k : PUnit, _ = _
      rw [Fintype.prod_unique, zpow_one]
      exact gw_isoPullId w rfl _ x _ _ hj' hk'
    rw [Category.comp_id, ep] at hc'
    have eL : gm (𝟙 _) x _ (res (inf_le_left : LB.wchart L₂.L (fun _ => eSec G) P ⊓ LB.wchart L₁.L (fun _ => eSec G) Q ≤ _)
        (L₂.rig.s P)) = gm (𝟙 _) x _ (L₂.rig.s P) := gm_res (𝟙 _) x _ hx _
    have eR : gm (𝟙 _) x _ (@id (Γ((𝟙_ (Over S)).left, LB.wchart L₂.L (fun _ => eSec G) P ⊓ LB.wchart L₁.L (fun _ => eSec G) Q)ˣ) ((LB.linCombIso wL (K := PUnit) (fun _ => eSec G) (fun _ => 1)).s (P, Q)) *
        res (inf_le_right : LB.wchart L₂.L (fun _ => eSec G) P ⊓ LB.wchart L₁.L (fun _ => eSec G) Q ≤ _) (L₁.rig.s Q)) =
        gv wL (𝟙 _ ≫ eSec G) x (P PUnit.unit) (Q PUnit.unit) * gm (𝟙 _) x _ (L₁.rig.s Q) := by
      refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ (gm_res (𝟙 _) x _ hx _))
      show gm (𝟙 _) x _ (∏ _k : PUnit, (res _ (pullU (eSec G) _ (wL.s (P PUnit.unit, Q PUnit.unit)))) ^ (1 : ℤ)) = _
      rw [Fintype.prod_unique, zpow_one]
      exact (gm_res (𝟙 _) x _ hx _).trans (gm_pull (𝟙 _) (eSec G) x (L₂.L.U (P PUnit.unit) ⊓ L₁.L.U (Q PUnit.unit)) ⟨hj, hk⟩ _)
    refine eL.trans (hc'.trans (Eq.trans ?_ eR.symm))
    rw [hv _ _ x _ _ hj' hk', Category.assoc, hs, Category.comp_id]
    exact (mul_assoc _ _ _).symm

end GlobalTheory.RigLBIso
