import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantLiftsSubEqSumInvariantFields
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantFieldCombinationKillingFunctionsCoeffZeStatement
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

namespace GlobalTheory.DiffCoc

theorem rsT_rsT {Z : Scheme.{0}} {O₀ T : Z.Opens} (s : Γ(Z, O₀)) (hT : T ≤ O₀) (O : Z.Opens) (hO : O ≤ T) :
    rsT (rsT s T) O = rsT s O := by
  unfold rsT
  rw [dif_pos hT, dif_pos hO, dif_pos (hO.trans hT)]
  simp [resG]

theorem rsT_add {Z : Scheme.{0}} {O₀ : Z.Opens} (s t : Γ(Z, O₀)) (O : Z.Opens) (hO : O ≤ O₀) :
    rsT (s + t) O = rsT s O + rsT t O := by
  unfold rsT
  rw [dif_pos hO, dif_pos hO, dif_pos hO, map_add]

theorem rsT_sub {Z : Scheme.{0}} {O₀ : Z.Opens} (s t : Γ(Z, O₀)) (O : Z.Opens) (hO : O ≤ O₀) :
    rsT (s - t) O = rsT s O - rsT t O := by
  unfold rsT
  rw [dif_pos hO, dif_pos hO, dif_pos hO, map_sub]

theorem isLift_mono {R : Type} [CommRing R] {G : Over (Sp R)} {D : R → R} {W W' : G.left.Opens} (h : W' ≤ W)
    {d : Fld G.left} (hd : IsLift G D W d) : IsLift G D W' d :=
  ⟨⟨fun O hO => hd.1.1 O (hO.trans h), fun O hO => hd.1.2.1 O (hO.trans h),
    fun O O' h' hO => hd.1.2.2 O O' h' (hO.trans h)⟩, fun O hO => hd.2 O (hO.trans h)⟩

theorem diff_isCoc : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (J : Type) (V : J → Dd.toPre.P.A.left.Opens) (d : J → Fld Y.H.left), (∀ i, IsLift Y.H ⇑D (Y.q.left ⁻¹ᵁ V i) (d i)) → (∀ i, (∀ (α : Dd.toPre.X) (V' : Dd.toPre.P.A.left.Opens), Y.q.left ⁻¹ᵁ V' ≤ Y.q.left ⁻¹ᵁ V i → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V') f → IsWt Y α (Y.q.left ⁻¹ᵁ V') (d i _ f))) → ∃ z : Fin n → C1 (fun i => Y.q.left ⁻¹ᵁ V i), (∀ a, IsCoc _ (z a)) ∧ (∀ a i i', IsWt Y 0 _ (z a i i')) ∧ ∀ i i' (W : Y.H.left.Opens), W ≤ Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i' → ∀ f, d i W f - d i' W f = ∑ a, rsT (z a i i') W * dd a W f := by
  intro R _ _ _ _ _ _ Dd O _ _ _ oa Y n v dd hdd D J V d hlift hwt
  have hsm : Smooth Y.H.hom := (GlobalTheory.isSemiAbelian_of_isGt _ _ _ Y.isGt).smooth
  have hl : ∀ i i', Y.q.left ⁻¹ᵁ (V i ⊓ V i') ≤ Y.q.left ⁻¹ᵁ V i := fun i i' =>
    (inf_le_left : Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i' ≤ Y.q.left ⁻¹ᵁ V i)
  have hr : ∀ i i', Y.q.left ⁻¹ᵁ (V i ⊓ V i') ≤ Y.q.left ⁻¹ᵁ V i' := fun i i' =>
    (inf_le_right : Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i' ≤ Y.q.left ⁻¹ᵁ V i')
  have hex : ∀ i i', ∃ h : Fin n → Γ(Y.H.left, Y.q.left ⁻¹ᵁ (V i ⊓ V i')), (∀ a, IsWt Y 0 _ (h a)) ∧
      ∀ (O' : Y.H.left.Opens), O' ≤ Y.q.left ⁻¹ᵁ (V i ⊓ V i') → ∀ f,
        d i O' f - d i' O' f = ∑ a, rsT (h a) O' * dd a O' f := fun i i' =>
    GlobalTheory.VertCoeff.lifts_sub_eq_sum_invFields R Dd.toPre O oa Y n v dd hdd (V i ⊓ V i') D (d i) (d i')
      (isLift_mono (hl i i') (hlift i)) (isLift_mono (hr i i') (hlift i'))
      (fun α V' hV' f hf => hwt i α V' (fun x hx => (hV' hx).1) f hf)
      (fun α V' hV' f hf => hwt i' α V' (fun x hx => (hV' hx).2) f hf)
  choose h hw hh using hex
  refine ⟨fun a i i' => h i i' a, fun a i j k => ?_, fun a i i' => hw i i' a, fun i i' W hW f => hh i i' W hW f⟩

  let U : J → Y.H.left.Opens := fun i => Y.q.left ⁻¹ᵁ V i
  let T := U i ⊓ U j ⊓ U k
  have hij : T ≤ Y.q.left ⁻¹ᵁ (V i ⊓ V j) :=
    (le_inf (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) : T ≤ U i ⊓ U j)
  have hjk : T ≤ Y.q.left ⁻¹ᵁ (V j ⊓ V k) :=
    (le_inf (inf_le_left.trans inf_le_right) inf_le_right : T ≤ U j ⊓ U k)
  have hik : T ≤ Y.q.left ⁻¹ᵁ (V i ⊓ V k) :=
    (le_inf (inf_le_left.trans inf_le_left) inf_le_right : T ≤ U i ⊓ U k)
  let c : Fin n → Γ(Y.H.left, T) := fun b =>
    rsT (h i j b) T + rsT (h j k b) T - rsT (h i k b) T
  have hc : ∀ O, O ≤ T → ∀ f, ∑ b, rsT (c b) O * dd b O f = 0 := by
    intro O hO f
    have e : ∀ b, rsT (c b) O = rsT (h i j b) O + rsT (h j k b) O - rsT (h i k b) O := fun b => by
      simp only [c]
      rw [rsT_sub _ _ _ hO, rsT_add _ _ _ hO, rsT_rsT _ hij _ hO, rsT_rsT _ hjk _ hO, rsT_rsT _ hik _ hO]
    simp only [e, sub_mul, add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [← hh i j O (hO.trans hij) f, ← hh j k O (hO.trans hjk) f, ← hh i k O (hO.trans hik) f]
    ring
  have h0 := GlobalTheory.T.invariant_field_combination_killing_functions_coeff_zero R Y.H hsm n v dd hdd T c hc a
  simp only [c] at h0
  exact (sub_eq_zero.1 h0)

end GlobalTheory.DiffCoc
