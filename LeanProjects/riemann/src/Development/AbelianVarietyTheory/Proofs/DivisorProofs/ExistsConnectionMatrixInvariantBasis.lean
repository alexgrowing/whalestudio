import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightZeroCocycleEqLogDerivativeCombAddCobStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusInvariantDerivationLiftsRaynaudCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferenceInvariantLiftsIsWeightZeroCechCocycleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantLiftAddInvariantCombinationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymmetricKodairaSpencerInvariantLiftsStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
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

namespace GlobalTheory.HeatInvLift

theorem rsT_of_le' {Z : Scheme.{0}} {O₀ O : Z.Opens} (h : O ≤ O₀) (s : Γ(Z, O₀)) : rsT s O = resG Z h s := dif_pos h

theorem rsT_rsT' {Z : Scheme.{0}} {O₀ O₁ O₂ : Z.Opens} (h₁ : O₁ ≤ O₀) (h₂ : O₂ ≤ O₁) (s : Γ(Z, O₀)) :
    rsT (rsT s O₁) O₂ = rsT s O₂ := by
  rw [rsT_of_le' h₁, rsT_of_le' h₂, rsT_of_le' (h₂.trans h₁), ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem rsT_pbT' {Z X : Scheme.{0}} (m : Z ⟶ X) {O₀ : X.Opens} {O₁ O₂ : Z.Opens} (h₁ : O₁ ≤ m ⁻¹ᵁ O₀) (h₂ : O₂ ≤ O₁)
    (s : Γ(X, O₀)) : rsT (pbT m s O₁) O₂ = pbT m s O₂ := by
  rw [rsT_of_le' h₂]
  unfold pbT
  rw [dif_pos h₁, dif_pos (h₂.trans h₁), ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

theorem rsT_constFn' {R : Type} [CommRing R] {Z : Scheme.{0}} (p : Z ⟶ Sp R) {O₀ O : Z.Opens} (h : O ≤ O₀) (a : R) :
    rsT (constFn p O₀ a) O = constFn p O a := by
  rw [rsT_of_le' h]
  exact congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.appLE_map p (U := ⊤) (V := O₀) (fun _ _ => trivial) (homOfLE h).op)

theorem rsT_field {Z : Scheme.{0}} {δ : ∀ W : Z.Opens, Γ(Z, W) → Γ(Z, W)} (hδ : IsField ⊤ δ) {O₀ O : Z.Opens}
    (h : O ≤ O₀) (s : Γ(Z, O₀)) : rsT (δ O₀ s) O = δ O (rsT s O) := by
  rw [rsT_of_le' h, rsT_of_le' h, hδ.2.2 O₀ O h le_top s]

theorem rsT_add' {Z : Scheme.{0}} {O₀ : Z.Opens} (s t : Γ(Z, O₀)) (O : Z.Opens) : rsT (s + t) O = rsT s O + rsT t O := by
  unfold rsT; split_ifs <;> simp

theorem rsT_sub' {Z : Scheme.{0}} {O₀ : Z.Opens} (s t : Γ(Z, O₀)) (O : Z.Opens) : rsT (s - t) O = rsT s O - rsT t O := by
  unfold rsT; split_ifs <;> simp

theorem rsT_mul' {Z : Scheme.{0}} {O₀ : Z.Opens} (s t : Γ(Z, O₀)) (O : Z.Opens) : rsT (s * t) O = rsT s O * rsT t O := by
  unfold rsT; split_ifs <;> simp

theorem rsT_sum' {Z : Scheme.{0}} {O₀ : Z.Opens} {K : Type} (S : Finset K) (s : K → Γ(Z, O₀)) (O : Z.Opens) :
    rsT (∑ b ∈ S, s b) O = ∑ b ∈ S, rsT (s b) O := by
  unfold rsT; split_ifs <;> simp

end GlobalTheory.HeatInvLift

open GlobalTheory.HeatInvLift

namespace GlobalTheory.HeatInvLift

theorem exists_invLift_symmKS : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ D : Derivation ℤ R R,
  ∃ (Θ : Matrix (Fin n) (Fin n) R) (J : Type) (V : J → Dd.toPre.P.A.left.Opens) (j : J → Dd.toPre.P.L.ι) (d : J → Fld Y.H.left),
    Θᵀ = Θ ∧ ⨆ i, V i = ⊤ ∧ (∀ i, V i ≤ Dd.toPre.P.L.U (j i)) ∧ (∀ i, IsLift Y.H ⇑D (Y.q.left ⁻¹ᵁ V i) (d i)) ∧
    (∀ i (α : Dd.toPre.X) (V' : Dd.toPre.P.A.left.Opens), Y.q.left ⁻¹ᵁ V' ≤ Y.q.left ⁻¹ᵁ V i → ∀ f,
      IsWt Y α (Y.q.left ⁻¹ᵁ V') f → IsWt Y α (Y.q.left ⁻¹ᵁ V') (d i _ f)) ∧
    ∀ i i' (W : Y.H.left.Opens), W ≤ Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i' → ∀ f, d i W f - d i' W f =
      ∑ a, ∑ b, constFn Y.H.hom W (Θ a b) * dlg Y.H Y.q.left Dd.toPre.P.L (dd b) (j i) (j i') W * dd a W f := by
  intro R _ _ _ _ _ _ Dd O _ _ _ oa Y n v dd hdd D
  obtain ⟨J, V, j, d₀, hc, hle, hl₀, hw₀⟩ := GlobalTheory.T.exists_torusInvariant_derivationLifts_raynaudCover R Dd O oa Y D
  obtain ⟨z, hzc, hzw, hz⟩ := GlobalTheory.T.difference_invariantLifts_isWeightZeroCechCocycle R Dd O oa Y n v dd hdd D J V d₀ hl₀ hw₀
  have H := fun a => GlobalTheory.T.exists_weightZeroCocycle_eq_logDerivative_comb_add_coboundary R Dd O oa Y n v dd hdd J V j hc hle (z a) (hzc a) (hzw a)
  choose c y hyw hy using H
  have hA := fun i => GlobalTheory.T.torusInvariantLift_add_invariantCombination R Dd O oa Y n v dd hdd D (V i) (d₀ i) (fun a => y a i) (hl₀ i) (hw₀ i) (fun a => hyw a i)
  have hrel : ∀ i i' (W : Y.H.left.Opens), W ≤ Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i' → ∀ f,
      (d₀ i W f + ∑ a, rsT (y a i) W * dd a W f) - (d₀ i' W f + ∑ a, rsT (y a i') W * dd a W f) =
        ∑ a, ∑ b, constFn Y.H.hom W (Matrix.of c a b) * dlg Y.H Y.q.left Dd.toPre.P.L (dd b) (j i) (j i') W * dd a W f := by
    intro i i' W hW f
    rw [add_sub_add_comm, hz i i' W hW f]
    have hU : Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i' ≤
        Y.q.left ⁻¹ᵁ (Dd.toPre.P.L.U (j i) ⊓ Dd.toPre.P.L.U (j i')) :=
      fun x hx => ⟨hle i hx.1, hle i' hx.2⟩
    have key : ∀ a, rsT (z a i i') W = ∑ b, constFn Y.H.hom W (c a b) *
        dlg Y.H Y.q.left Dd.toPre.P.L (dd b) (j i) (j i') W + (rsT (y a i') W - rsT (y a i) W) := by
      intro a
      rw [hy a i i', rsT_add', rsT_sub', rsT_rsT' inf_le_right hW, rsT_rsT' inf_le_left hW]
      congr 1
      rw [rsT_sum']
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [rsT_mul', rsT_constFn' _ hW]
      congr 1
      unfold dlg
      rw [rsT_mul', rsT_field (hdd b).1 hW, rsT_pbT' _ hU hW, rsT_pbT' _ hU hW]
    simp only [key, Matrix.of_apply, add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_mul]
    ring
  obtain ⟨Θ, hs, hΘ⟩ := GlobalTheory.T.exists_symmetric_kodairaSpencer_invariantLifts R Dd O oa Y n v dd hdd D J V j
    (fun i W f => d₀ i W f + ∑ a, rsT (y a i) W * dd a W f) hc hle (fun i => (hA i).1) (fun i => (hA i).2)
    (Matrix.of c) hrel
  exact ⟨Θ, J, V, j, _, hs, hc, hle, fun i => (hA i).1, fun i => (hA i).2, hΘ⟩

end GlobalTheory.HeatInvLift
