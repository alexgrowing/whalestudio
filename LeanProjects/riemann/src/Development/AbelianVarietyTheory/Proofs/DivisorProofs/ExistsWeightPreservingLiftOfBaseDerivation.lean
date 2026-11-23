import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantHeatOperatorPreservesWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueWeightDecompositionRaynaudAffineStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRaynaudTorusWeightFunctionMulStatement
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

namespace GlobalTheory.WtLift

variable {X A : Type} [AddCommGroup X] [CommRing A] (P : X → A → Prop)
  (hadd : ∀ χ a b, P χ a → P χ b → P χ (a + b)) (hzero : ∀ χ, P χ 0)
  (hmul : ∀ χ ψ a b, P χ a → P ψ b → P (χ + ψ) (a * b))
  (hdec : ∀ f : A, ∃! F : X →₀ A, (∀ χ, P χ (F χ)) ∧ f = F.sum (fun _ t => t))

include hdec in

def dec (f : A) : X →₀ A := (hdec f).exists.choose

include hdec in
theorem dec_spec (f : A) : (∀ χ, P χ (dec P hdec f χ)) ∧ f = (dec P hdec f).sum (fun _ t => t) :=
  (hdec f).exists.choose_spec

include hdec in
theorem dec_eq {f : A} {F : X →₀ A} (hF : ∀ χ, P χ (F χ)) (hs : f = F.sum (fun _ t => t)) : dec P hdec f = F :=
  (hdec f).unique (dec_spec P hdec f) ⟨hF, hs⟩

include hadd hdec in
theorem dec_add (a b : A) : dec P hdec (a + b) = dec P hdec a + dec P hdec b := by
  refine dec_eq P hdec (fun χ => ?_) ?_
  · rw [Finsupp.add_apply]; exact hadd _ _ _ ((dec_spec P hdec a).1 χ) ((dec_spec P hdec b).1 χ)
  · rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), ← (dec_spec P hdec a).2, ← (dec_spec P hdec b).2]

include hzero hdec in
theorem dec_single {α : X} {f : A} (hf : P α f) : dec P hdec f = Finsupp.single α f := by
  classical
  refine dec_eq P hdec (fun χ => ?_) ?_
  · rw [Finsupp.single_apply]; split_ifs with h
    · exact h ▸ hf
    · exact hzero χ
  · rw [Finsupp.sum_single_index rfl]

include hzero hdec in
theorem dec_zero : dec P hdec (0 : A) = 0 := by
  rw [dec_single P hzero hdec (hzero 0), Finsupp.single_zero]

include hzero hmul hdec in
theorem dec_mul {χ : X} {f : A} (hf : P χ f) (h : A) (ψ : X) :
    dec P hdec (f * h) (χ + ψ) = f * dec P hdec h ψ := by
  set G : X →₀ A := Finsupp.mapDomain (fun ψ => χ + ψ) ((dec P hdec h).mapRange (f * ·) (mul_zero f)) with hG
  have hinj : Function.Injective (fun ψ : X => χ + ψ) := add_right_injective χ
  have hGv : ∀ ψ, G (χ + ψ) = f * dec P hdec h ψ := fun ψ => by
    rw [hG, Finsupp.mapDomain_apply hinj, Finsupp.mapRange_apply]
  have key : dec P hdec (f * h) = G := by
    refine dec_eq P hdec (fun ω => ?_) ?_
    · have e : ω = χ + (ω - χ) := by abel
      rw [e, hGv]; exact hmul _ _ _ _ hf ((dec_spec P hdec h).1 _)
    · rw [hG, Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl),
        Finsupp.sum_mapRange_index (fun _ => rfl), ← Finsupp.mul_sum, ← (dec_spec P hdec h).2]
  rw [key, hGv]

variable (δ₀ : A → A)

def proj (f : A) : A := (dec P hdec f).sum (fun χ t => dec P hdec (δ₀ t) χ)

include hadd hzero hdec in
theorem proj_add (h0 : ∀ a b, δ₀ (a + b) = δ₀ a + δ₀ b) (a b : A) :
    proj P hdec δ₀ (a + b) = proj P hdec δ₀ a + proj P hdec δ₀ b := by
  have hz : δ₀ 0 = 0 := by
    have := h0 0 0; simp only [add_zero] at this; exact left_eq_add.mp this
  unfold proj
  rw [dec_add P hadd hdec, Finsupp.sum_add_index']
  · intro χ; rw [hz, dec_zero P hzero hdec, Finsupp.zero_apply]
  · intro χ s t; rw [h0, dec_add P hadd hdec, Finsupp.add_apply]

include hzero hdec in
theorem proj_of_wt (hz : δ₀ 0 = 0) {α : X} {f : A} (hf : P α f) : proj P hdec δ₀ f = dec P hdec (δ₀ f) α := by
  unfold proj; rw [dec_single P hzero hdec hf, Finsupp.sum_single_index]
  rw [hz, dec_zero P hzero hdec]; rfl

include hzero hdec in

theorem induction_wt (Qp : A → Prop) (q0 : Qp 0) (qadd : ∀ a b, Qp a → Qp b → Qp (a + b))
    (qw : ∀ χ a, P χ a → Qp a) (f : A) : Qp f := by
  rw [(dec_spec P hdec f).2, Finsupp.sum]
  exact Finset.sum_induction _ Qp qadd q0 (fun χ _ => qw χ _ ((dec_spec P hdec f).1 χ))

include hadd hzero hmul hdec in
theorem proj_mul (h0 : ∀ a b, δ₀ (a + b) = δ₀ a + δ₀ b) (h1 : ∀ a b, δ₀ (a * b) = a * δ₀ b + b * δ₀ a) (a b : A) :
    proj P hdec δ₀ (a * b) = a * proj P hdec δ₀ b + b * proj P hdec δ₀ a := by
  have hz : δ₀ 0 = 0 := by
    have := h0 0 0; simp only [add_zero] at this; exact left_eq_add.mp this
  have pz : proj P hdec δ₀ 0 = 0 := by
    unfold proj; rw [dec_zero P hzero hdec, Finsupp.sum_zero_index]
  have hom : ∀ χ ψ x y, P χ x → P ψ y →
      proj P hdec δ₀ (x * y) = x * proj P hdec δ₀ y + y * proj P hdec δ₀ x := by
    intro χ ψ x y hx hy
    rw [proj_of_wt P hzero hdec δ₀ hz (hmul _ _ _ _ hx hy), proj_of_wt P hzero hdec δ₀ hz hy,
      proj_of_wt P hzero hdec δ₀ hz hx, h1, dec_add P hadd hdec, Finsupp.add_apply, dec_mul P hzero hmul hdec hx,
      add_comm χ ψ, dec_mul P hzero hmul hdec hy]
  have padd := proj_add P hadd hzero hdec δ₀ h0

  have step : ∀ ψ y, P ψ y → ∀ x, proj P hdec δ₀ (x * y) = x * proj P hdec δ₀ y + y * proj P hdec δ₀ x := by
    intro ψ y hy
    refine induction_wt P hzero hdec _ ?_ ?_ (fun χ x hx => hom χ ψ x y hx hy)
    · rw [zero_mul, pz, zero_mul, mul_zero, add_zero]
    · intro x x' ex ex'; rw [add_mul, padd, padd, ex, ex']; ring
  revert b
  intro b
  refine induction_wt P hzero hdec (fun y => proj P hdec δ₀ (a * y) = a * proj P hdec δ₀ y + y * proj P hdec δ₀ a)
    ?_ ?_ (fun ψ y hy => step ψ y hy a) b
  · simp only [mul_zero, pz, zero_mul, add_zero]
  · intro y y' ey ey'; rw [mul_add, padd, ey, ey', padd]; ring

include hzero hdec in
theorem proj_wt (hz : δ₀ 0 = 0) {α : X} {f : A} (hf : P α f) : P α (proj P hdec δ₀ f) := by
  rw [proj_of_wt P hzero hdec δ₀ hz hf]; exact (dec_spec P hdec _).1 α

end GlobalTheory.WtLift

namespace GlobalTheory.WtLift

theorem exists_isWt_lift : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (V : Q.P.A.left.affineOpens) (D : Derivation ℤ R R) (δ₀ : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V.1) → Γ(Y.H.left, Y.q.left ⁻¹ᵁ V.1)), (∀ a b, δ₀ (a + b) = δ₀ a + δ₀ b) → (∀ a b, δ₀ (a * b) = a * δ₀ b + b * δ₀ a) → (∀ r, δ₀ (constFn Y.H.hom _ r) = constFn Y.H.hom _ (D r)) → ∃ δ : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V.1) → Γ(Y.H.left, Y.q.left ⁻¹ᵁ V.1), (∀ a b, δ (a + b) = δ a + δ b) ∧ (∀ a b, δ (a * b) = a * δ b + b * δ a) ∧ (∀ r, δ (constFn Y.H.hom _ r) = constFn Y.H.hom _ (D r)) ∧ ∀ (α : Q.X) f, IsWt Y α _ f → IsWt Y α _ (δ f) := by
  intro R _ _ Q O _ _ _ oa Y V D δ₀ h0 h1 hc
  have hadd : ∀ (χ : Q.X) (a b : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V.1)), IsWt Y χ _ a → IsWt Y χ _ b → IsWt Y χ _ (a + b) :=
    fun χ a b ha hb => WtAlg.isWt_add ha hb
  have hzero : ∀ χ : Q.X, IsWt Y χ (Y.q.left ⁻¹ᵁ V.1) 0 := fun χ => WtAlg.isWt_zero (Y := Y) χ _
  have hmul : ∀ (χ ψ : Q.X) (a b : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V.1)), IsWt Y χ _ a → IsWt Y ψ _ b →
      IsWt Y (χ + ψ) _ (a * b) :=
    fun χ ψ a b ha hb => GlobalTheory.T.isRaynaudTorusWeightFunction_mul R Q O oa Y _ χ ψ a b ha hb
  have hdec := GlobalTheory.T.existsUnique_weightDecomposition_raynaud_affine R Q O oa Y V.1 V.2
  have hz : δ₀ 0 = 0 := by
    have := h0 0 0; simp only [add_zero] at this; exact left_eq_add.mp this
  refine ⟨proj (fun χ f => IsWt Y χ _ f) hdec δ₀, proj_add _ hadd hzero hdec δ₀ h0,
    proj_mul _ hadd hzero hmul hdec δ₀ h0 h1, fun r => ?_, fun α f hf => proj_wt _ hzero hdec δ₀ hz hf⟩
  rw [proj_of_wt _ hzero hdec δ₀ hz (WtAlg.isWt_constFn (Y := Y) _ r), hc,
    dec_single _ hzero hdec (WtAlg.isWt_constFn (Y := Y) _ (D r)), Finsupp.single_eq_same]

end GlobalTheory.WtLift
