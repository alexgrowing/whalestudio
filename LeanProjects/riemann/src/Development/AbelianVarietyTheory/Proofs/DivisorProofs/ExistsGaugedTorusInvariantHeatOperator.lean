import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeISupInfPreimage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantLiftAddInvariantCombination
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PresBasicOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusInvariantHeatOperatorOfSymmetricRelat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRaynaudTorusWeightFunctionInvariantField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantHeatOperatorPreservesWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeatOperatorGluedPullbackBundlePower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatGaugeCoverOpenLeHeatOperatorOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaugedLocalHeatOperatorPowerMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaugeUnitsTransitionRelationOnOverlapsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaugedChartFunctionEqGaugePowerMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaugeUnitHasGeneratorWeightOnPreimagesStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Heat.Gauge

open GlobalTheory.KS

theorem gauge_op {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] {n : ℕ} {X : Scheme.{0}}
    (m m₁ : G.left ⟶ X) (L : LB X) (dd : Fin n → Fld G.left) (D : R → R) (h₁ : Heat G m₁ L dd D)
    (e : LB.Gen (LB.LinComb L ![m, m₁] ![1, -1])) (hdd : ∀ a, IsField ⊤ (dd a)) (c : R) (hc : 2 * c = 1)
    (p : h₁.J × (Fin 2 → L.ι)) (k : ℕ) (O : G.left.Opens) (hO : O ≤ W m h₁ p) (f : Γ(G.left, O)) :
    op G dd h₁.Θ h₁.u (gD m h₁ e p) (gP m h₁ e c p) (gP' m h₁ e c p) k O (rsT (gU m h₁ e p).val O ^ k * f) =
      rsT (gU m h₁ e p).val O ^ k * op G dd h₁.Θ h₁.u (h₁.d p.1) (h₁.p p.1) (h₁.p' p.1) k O f :=
  GlobalTheory.T.gauged_local_heat_operator_power_mul _ G n X m m₁ L dd D h₁ e hdd c hc p k O hO f

theorem gauge_cocycle {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] {n : ℕ} {X : Scheme.{0}}
    (m m₁ : G.left ⟶ X) (L : LB X) (dd : Fin n → Fld G.left) (D : R → R) (h₁ : Heat G m₁ L dd D)
    (e : LB.Gen (LB.LinComb L ![m, m₁] ![1, -1])) (hL : L.IsLB) (he : e.IsGen) (p p' : h₁.J × (Fin 2 → L.ι))
    (O : G.left.Opens) (hO : O ≤ W m h₁ p ⊓ W m h₁ p') :
    pbT m (L.g (p.2 0) (p'.2 0)).val O * rsT (gU m h₁ e p').val O =
      rsT (gU m h₁ e p).val O * pbT m₁ (L.g (h₁.j p.1) (h₁.j p'.1)).val O :=
  GlobalTheory.T.gauge_units_transition_relation_on_overlaps _ G n X m m₁ L dd D h₁ e hL he p p' O hO

theorem gauge_chart {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] {n : ℕ} {X : Scheme.{0}}
    (m m₁ : G.left ⟶ X) (L : LB X) (dd : Fin n → Fld G.left) (D : R → R) (h₁ : Heat G m₁ L dd D)
    (e : LB.Gen (LB.LinComb L ![m, m₁] ![1, -1])) (hL : L.IsLB) (he : e.IsGen) (k : ℕ) (σ : SecM m₁ L k)
    (ρ : SecM m L k)
    (hρ : ∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J →
      sval ρ r z J = sval σ r z J * ((val e r z J) ^ k).val)
    (p : h₁.J × (Fin 2 → L.ι)) :
    rsT (ρ.f fun _ => p.2 0) (W m h₁ p) = (gU m h₁ e p).val ^ k * rsT (σ.f fun _ => h₁.j p.1) (W m h₁ p) :=
  GlobalTheory.T.gauged_chart_function_eq_gauge_power_mul _ G n X m m₁ L dd D h₁ e hL he k σ ρ hρ p

theorem gauge_wt {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) {O : Type} [CommRing O] [StarRing O]
    [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) {n : ℕ} (dd : Fin n → Fld Y.H.left) (D : R → R)
    (x : 𝟙_ (Over (Sp R)) ⟶ Y.H) (h₁ : Heat Y.H ((𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left) Q.P.L dd D)
    (e : LB.Gen (LB.LinComb Q.P.L ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] ![1, -1])) (β : Q.X)
    (hwe : ∀ (j : Fin 2 → Q.P.L.ι) (V : Q.P.A.left.Opens),
      Y.q.left ⁻¹ᵁ V ≤ LB.wchart Q.P.L ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] j →
        IsWt Y β (Y.q.left ⁻¹ᵁ V) (rsT (e.s j).val (Y.q.left ⁻¹ᵁ V)))
    (p : h₁.J × (Fin 2 → Q.P.L.ι)) (V : Q.P.A.left.Opens) (hV : Y.q.left ⁻¹ᵁ V ≤ W Y.q.left h₁ p) :
    IsWt Y β (Y.q.left ⁻¹ᵁ V) (rsT (gU Y.q.left h₁ e p).val (Y.q.left ⁻¹ᵁ V)) :=
  GlobalTheory.T.gauge_unit_has_generator_weight_on_preimages _ Q O oa Y n dd D x h₁ e β hwe p V hV

section General

variable {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] {n : ℕ} {X : Scheme.{0}}
  (m m₁ : G.left ⟶ X) (L : LB X) (dd : Fin n → Fld G.left) (D : R → R) (h₁ : Heat G m₁ L dd D)
  (e : LB.Gen (LB.LinComb L ![m, m₁] ![1, -1]))

theorem gauge_cover (hL : L.IsLB) : ⨆ p, W m h₁ p = ⊤ := by
  refine eq_top_iff.2 fun y _ => ?_
  have hy : y ∈ ⨆ i, h₁.W i := by rw [h₁.cover]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  obtain ⟨a, ha⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart hL (m y)
  obtain ⟨b, hb⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart hL (m₁ y)
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨(i, ![a, b]), hi, Set.mem_iInter.2 (Fin.forall_fin_two.2 ⟨ha, hb⟩)⟩

theorem gauge_lift (hF : ∀ a, IsField ⊤ (dd a)) (h0 : ∀ a O r, dd a O (constFn G.hom O r) = 0)
    (p : h₁.J × (Fin 2 → L.ι)) : IsLift G D (W m h₁ p) (gD m h₁ e p) := by
  have hd₁ := h₁.lift p.1
  refine ⟨GlobalTheory.Heat.Adjust.isField_add_comb (h₁.d p.1) dd (fun a => gY m h₁ e a p)
    (isField_mono hd₁.1 (heatGaugeCoverOpen_le_heatOperatorOpen m h₁ p)) hF, fun O' hO r => ?_⟩
  show h₁.d p.1 O' (constFn G.hom O' r) + ∑ a, rsT (gY m h₁ e a p) O' * dd a O' (constFn G.hom O' r) = _
  rw [hd₁.2 O' (hO.trans (heatGaugeCoverOpen_le_heatOperatorOpen m h₁ p)) r]
  simp [h0]

theorem gauge_glue (hL : L.IsLB) (he : e.IsGen) (hF : ∀ a, IsField ⊤ (dd a)) (c : R) (hc : 2 * c = 1) (k : ℕ)
    (p p' : h₁.J × (Fin 2 → L.ι)) (O' : G.left.Opens) (hO : O' ≤ W m h₁ p ⊓ W m h₁ p') (f : Γ(G.left, O')) :
    op G dd h₁.Θ h₁.u (gD m h₁ e p) (gP m h₁ e c p) (gP' m h₁ e c p) k O' (pbT m (L.g (p.2 0) (p'.2 0)).val O' ^ k * f) =
      pbT m (L.g (p.2 0) (p'.2 0)).val O' ^ k *
        op G dd h₁.Θ h₁.u (gD m h₁ e p') (gP m h₁ e c p') (gP' m h₁ e c p') k O' f := by
  have hOp : O' ≤ W m h₁ p := hO.trans inf_le_left
  have hOp' : O' ≤ W m h₁ p' := hO.trans inf_le_right
  have hco := gauge_cocycle G m m₁ L dd D h₁ e hL he p p' O' hO
  have hA' : rsT (gU m h₁ e p').val O' * rsT (gU m h₁ e p')⁻¹.val O' = 1 := by
    rw [← GlobalTheory.KS.rsT_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, GlobalTheory.KS.rsT_one hOp']
  have hk := congrArg (· ^ k) hco
  have hk' := congrArg (· ^ k) hA'
  simp only [one_pow, mul_pow] at hk hk'
  have e1 : pbT m (L.g (p.2 0) (p'.2 0)).val O' ^ k * f =
      rsT (gU m h₁ e p).val O' ^ k *
        (pbT m₁ (L.g (h₁.j p.1) (h₁.j p'.1)).val O' ^ k * (rsT (gU m h₁ e p')⁻¹.val O' ^ k * f)) := by
    linear_combination (-(pbT m (L.g (p.2 0) (p'.2 0)).val O' ^ k * f)) * hk' +
      (rsT (gU m h₁ e p')⁻¹.val O' ^ k * f) * hk
  have ef : f = rsT (gU m h₁ e p').val O' ^ k * (rsT (gU m h₁ e p')⁻¹.val O' ^ k * f) := by
    linear_combination (-f) * hk'
  rw [e1, gauge_op G m m₁ L dd D h₁ e hF c hc p k O' hOp,
    h₁.glue k p.1 p'.1 O' (le_inf (hOp.trans (heatGaugeCoverOpen_le_heatOperatorOpen m h₁ p)) (hOp'.trans (heatGaugeCoverOpen_le_heatOperatorOpen m h₁ p')))]
  conv_rhs => rw [ef, gauge_op G m m₁ L dd D h₁ e hF c hc p' k O' hOp']
  linear_combination (-(op G dd h₁.Θ h₁.u (h₁.d p'.1) (h₁.p p'.1) (h₁.p' p'.1) k O'
    (rsT (gU m h₁ e p')⁻¹.val O' ^ k * f))) * hk

end General

theorem gauge_acts {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] {n : ℕ} {X : Scheme.{0}}
    (m m₁ : G.left ⟶ X) (L : LB X) (dd : Fin n → Fld G.left) (D : R → R) (h₁ : Heat G m₁ L dd D)
    (e : LB.Gen (LB.LinComb L ![m, m₁] ![1, -1])) (hL : L.IsLB) (he : e.IsGen) (hF : ∀ a, IsField ⊤ (dd a))
    (c : R) (hc : 2 * c = 1) (k : ℕ) (σ σ' : SecM m₁ L k) (ρ ρ' : SecM m L k)
    (hρ : ∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J →
      sval ρ r z J = sval σ r z J * ((val e r z J) ^ k).val)
    (hρ' : ∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J →
      sval ρ' r z J = sval σ' r z J * ((val e r z J) ^ k).val)
    (hA : h₁.Acts k σ σ') (p : h₁.J × (Fin 2 → L.ι)) :
    rsT (ρ'.f fun _ => p.2 0) (W m h₁ p) = op G dd h₁.Θ h₁.u (gD m h₁ e p) (gP m h₁ e c p) (gP' m h₁ e c p) k
      (W m h₁ p) (rsT (ρ.f fun _ => p.2 0) (W m h₁ p)) := by
  have c1 := gauge_chart G m m₁ L dd D h₁ e hL he k σ ρ hρ p
  have c2 := gauge_chart G m m₁ L dd D h₁ e hL he k σ' ρ' hρ' p
  have hU : rsT (gU m h₁ e p).val (W m h₁ p) = (gU m h₁ e p).val := GlobalTheory.KS.rsT_self _
  rw [c1, c2, ← hU, gauge_op G m m₁ L dd D h₁ e hF c hc p k _ le_rfl, hU]
  congr 1
  have hWc : h₁.W p.1 ≤ (LB.LinComb L (K := Fin 1) (fun _ => m₁) fun _ => (k : ℤ)).U (fun _ => h₁.j p.1) :=
    GlobalTheory.Heat.Glue.le_wchart _ (h₁.le p.1)
  rw [← GlobalTheory.KS.rsT_rsT hWc (heatGaugeCoverOpen_le_heatOperatorOpen m h₁ p) (σ'.f fun _ => h₁.j p.1), hA p.1,
    op_rsT G dd hF _ _ _ _ _ k (h₁.lift p.1).1 le_rfl (heatGaugeCoverOpen_le_heatOperatorOpen m h₁ p),
    GlobalTheory.KS.rsT_rsT hWc (heatGaugeCoverOpen_le_heatOperatorOpen m h₁ p)]

theorem gauge_basic {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) {O : Type} [CommRing O] [StarRing O]
    [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) {n : ℕ} (v : Fin n → TanM (𝟙 (Sp R)) Y.H) (dd : Fin n → Fld Y.H.left)
    (hinv : ∀ a, IsInv Y.H (v a) (dd a)) (D : R → R)
    (x : 𝟙_ (Over (Sp R)) ⟶ Y.H) (h₁ : Heat Y.H ((𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left) Q.P.L dd D)
    (hB₁ : ∀ i, (∃ V : Q.P.A.left.Opens, h₁.W i = Y.q.left ⁻¹ᵁ V) ∧ IsWt Y 0 _ (h₁.p i) ∧ IsWt Y 0 _ (h₁.p' i) ∧
      ∀ (α : Q.X) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ h₁.W i → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V) f →
        IsWt Y α (Y.q.left ⁻¹ᵁ V) (h₁.d i _ f))
    (e : LB.Gen (LB.LinComb Q.P.L ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] ![1, -1])) (β : Q.X)
    (hwe : ∀ (j : Fin 2 → Q.P.L.ι) (V : Q.P.A.left.Opens),
      Y.q.left ⁻¹ᵁ V ≤ LB.wchart Q.P.L ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] j →
        IsWt Y β (Y.q.left ⁻¹ᵁ V) (rsT (e.s j).val (Y.q.left ⁻¹ᵁ V)))
    (c : R) (p : h₁.J × (Fin 2 → Q.P.L.ι)) :
    (∃ V : Q.P.A.left.Opens, W Y.q.left h₁ p = Y.q.left ⁻¹ᵁ V) ∧ IsWt Y 0 _ (gP Y.q.left h₁ e c p) ∧
      IsWt Y 0 _ (gP' Y.q.left h₁ e c p) ∧
      ∀ (α : Q.X) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ W Y.q.left h₁ p → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V) f →
        IsWt Y α (Y.q.left ⁻¹ᵁ V) (gD Y.q.left h₁ e p _ f) := by
  obtain ⟨τ, hτ⟩ := trans_factor Q oa Y x
  obtain ⟨⟨V₁, hV₁⟩, hp₁, hp₁', hd₁⟩ := hB₁ p.1
  let Vp : Q.P.A.left.Opens := V₁ ⊓ (Q.P.L.U (p.2 0) ⊓ τ ⁻¹ᵁ Q.P.L.U (p.2 1))
  have hm₁ : ∀ y, ((𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left) y = τ (Y.q.left y) := fun y => by
    rw [hτ, Scheme.Hom.comp_apply]
  have hWp : W Y.q.left h₁ p = Y.q.left ⁻¹ᵁ Vp := by
    refine TopologicalSpace.Opens.ext (Set.ext fun y => ⟨fun hy => ?_, fun hy => ?_⟩)
    · have h1 : y ∈ Y.q.left ⁻¹ᵁ V₁ := hV₁ ▸ hy.1
      have h2 := Set.mem_iInter.1 hy.2
      refine ⟨h1, h2 0, ?_⟩
      show τ (Y.q.left y) ∈ Q.P.L.U (p.2 1)
      rw [← hm₁]; exact h2 1
    · have h1 : y ∈ h₁.W p.1 := hV₁ ▸ hy.1
      refine ⟨h1, Set.mem_iInter.2 (Fin.forall_fin_two.2 ⟨hy.2.1, ?_⟩)⟩
      show ((𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left) y ∈ Q.P.L.U (p.2 1)
      rw [hm₁]; exact hy.2.2
  have tr : ∀ (α : Q.X) (W₀ : Y.H.left.Opens), W₀ = Y.q.left ⁻¹ᵁ Vp → ∀ f : Γ(Y.H.left, W₀),
      IsWt Y α (Y.q.left ⁻¹ᵁ Vp) (rsT f (Y.q.left ⁻¹ᵁ Vp)) → IsWt Y α W₀ f := by
    rintro α W₀ rfl f h
    rwa [GlobalTheory.KS.rsT_self] at h
  have hU : IsWt Y β (W Y.q.left h₁ p) (gU Y.q.left h₁ e p).val :=
    tr β _ hWp _ (gauge_wt Q oa Y dd D x h₁ e β hwe p Vp hWp.ge)
  have hdW : ∀ α f, IsWt Y α (W Y.q.left h₁ p) f → IsWt Y α (W Y.q.left h₁ p) (h₁.d p.1 (W Y.q.left h₁ p) f) := by
    have hle : Y.q.left ⁻¹ᵁ Vp ≤ h₁.W p.1 := hWp ▸ heatGaugeCoverOpen_le_heatOperatorOpen Y.q.left h₁ p
    rw [hWp]
    exact fun α => hd₁ α Vp hle
  have hinvU : (gU Y.q.left h₁ e p).val * (gU Y.q.left h₁ e p)⁻¹.val = 1 := Units.mul_inv _
  have hL0 : ∀ a, IsWt Y 0 (W Y.q.left h₁ p) (gL Y.q.left h₁ e a p) := fun a =>
    GlobalTheory.Heat.WtPres.isWt_div (GlobalTheory.Heat.IsInv.isWt Y (v a) (dd a) (hinv a) β _ _ hU) hU hinvU
  have hE0 : IsWt Y 0 (W Y.q.left h₁ p) (gE Y.q.left h₁ e p) :=
    GlobalTheory.Heat.WtPres.isWt_div (hdW β _ hU) hU hinvU
  have hY0 : ∀ a, IsWt Y 0 (W Y.q.left h₁ p) (gY Y.q.left h₁ e a p) := fun a =>
    GlobalTheory.Heat.WtAlg.isWt_sum _ _ fun b _ => GlobalTheory.Heat.WtAlg.isRaynaudTorusWeightFunction_weightZero_mul (GlobalTheory.Heat.WtAlg.isWt_constFn _ _) (hL0 b)
  refine ⟨⟨Vp, hWp⟩, ?_, ?_, fun α V hV f hf => ?_⟩
  · refine GlobalTheory.Heat.WtAlg.isWt_sub (GlobalTheory.Heat.WtAlg.isWt_sub
      (GlobalTheory.Heat.Adjust.isWt_rsT Y (heatGaugeCoverOpen_le_heatOperatorOpen Y.q.left h₁ p) hp₁) hE0) ?_
    refine GlobalTheory.Heat.WtAlg.isRaynaudTorusWeightFunction_weightZero_mul (GlobalTheory.Heat.WtAlg.isWt_constFn _ _) ?_
    exact GlobalTheory.Heat.WtAlg.isWt_sum _ _ fun a _ => GlobalTheory.Heat.WtAlg.isWt_sum _ _ fun b _ =>
      GlobalTheory.Heat.WtAlg.isRaynaudTorusWeightFunction_weightZero_mul (GlobalTheory.Heat.WtAlg.isRaynaudTorusWeightFunction_weightZero_mul (GlobalTheory.Heat.WtAlg.isWt_constFn _ _) (hL0 a)) (hL0 b)
  · refine GlobalTheory.Heat.WtAlg.isWt_sub (GlobalTheory.Heat.WtAlg.isWt_add
      (GlobalTheory.Heat.Adjust.isWt_rsT Y (heatGaugeCoverOpen_le_heatOperatorOpen Y.q.left h₁ p) hp₁') ?_) ?_
    · refine GlobalTheory.Heat.WtAlg.isRaynaudTorusWeightFunction_weightZero_mul (GlobalTheory.Heat.WtAlg.isWt_constFn _ _) ?_
      exact GlobalTheory.Heat.WtAlg.isWt_sum _ _ fun a _ => GlobalTheory.Heat.WtAlg.isWt_sum _ _ fun b _ =>
        GlobalTheory.Heat.WtAlg.isRaynaudTorusWeightFunction_weightZero_mul (GlobalTheory.Heat.WtAlg.isWt_constFn _ _)
          (GlobalTheory.Heat.IsInv.isWt Y (v a) (dd a) (hinv a) 0 _ _ (hL0 b))
    · exact GlobalTheory.Heat.WtAlg.isWt_sum _ _ fun a _ =>
        GlobalTheory.Heat.WtAlg.isRaynaudTorusWeightFunction_weightZero_mul (GlobalTheory.Heat.WtAlg.isWt_constFn _ _) (hL0 a)
  · show IsWt Y α _ (h₁.d p.1 _ f + ∑ a, rsT (gY Y.q.left h₁ e a p) _ * dd a _ f)
    exact GlobalTheory.Heat.WtAlg.isWt_add (hd₁ α V (hV.trans (heatGaugeCoverOpen_le_heatOperatorOpen Y.q.left h₁ p)) f hf)
      (GlobalTheory.Heat.WtAlg.isWt_sum _ _ fun a _ => GlobalTheory.Heat.WtAlg.isRaynaudTorusWeightFunction_weightZero_mul
        (GlobalTheory.Heat.Adjust.isWt_rsT Y hV (hY0 a)) (GlobalTheory.Heat.IsInv.isWt Y (v a) (dd a) (hinv a) α _ _ hf))

theorem exists_gauge_heat : ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra ℚ R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (v : Fin n → TanM (𝟙 (Sp R)) Y.H) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (x : 𝟙_ (Over (Sp R)) ⟶ Y.H) (h₁ : Heat Y.H ((𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left) Q.P.L dd ⇑D), (∀ i, (∃ V : Q.P.A.left.Opens, h₁.W i = Y.q.left ⁻¹ᵁ V) ∧ IsWt Y 0 _ (h₁.p i) ∧ IsWt Y 0 _ (h₁.p' i) ∧ ∀ (α : Q.X) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ h₁.W i → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V) f → IsWt Y α (Y.q.left ⁻¹ᵁ V) (h₁.d i _ f)) → ∀ (e : LB.Gen (LB.LinComb Q.P.L (K := Fin 2) ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] ![1, -1])) (β : Q.X), e.IsGen → (∀ (j : Fin 2 → Q.P.L.ι) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ LB.wchart Q.P.L ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] j → IsWt Y β (Y.q.left ⁻¹ᵁ V) (rsT (e.s j).val (Y.q.left ⁻¹ᵁ V))) → ∃ h' : Heat Y.H Y.q.left Q.P.L dd ⇑D, IsBasic Y h' ∧ h'.Θ = h₁.Θ ∧ h'.u = h₁.u ∧ ∀ (k : ℕ) (σ σ' : SecM ((𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left) Q.P.L k) (ρ ρ' : SecM Y.q.left Q.P.L k), (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval ρ r z J = sval σ r z J * ((val e r z J) ^ k).val) → (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval ρ' r z J = sval σ' r z J * ((val e r z J) ^ k).val) → h₁.Acts k σ σ' → h'.Acts k ρ ρ' := by
  intro R _ _ _ Q O _ _ _ oa Y n v dd hinv D x h₁ hB₁ e β he hwe
  have hL : Q.P.L.IsLB := Q.P.isLB
  have hF : ∀ a, IsField ⊤ (dd a) := fun a => (hinv a).1
  have hc : 2 * algebraMap ℚ R (1 / 2) = 1 := by
    rw [← map_ofNat (algebraMap ℚ R) 2, ← map_mul]
    norm_num
  refine ⟨⟨h₁.Θ, h₁.symm, h₁.u, h₁.J × (Fin 2 → Q.P.L.ι), W Y.q.left h₁, fun p => p.2 0,
    gD Y.q.left h₁ e, gP Y.q.left h₁ e (algebraMap ℚ R (1 / 2)), gP' Y.q.left h₁ e (algebraMap ℚ R (1 / 2)),
    gauge_cover Y.H _ _ Q.P.L dd _ h₁ hL, fun p => W_le_m Y.q.left h₁ p,
    gauge_lift Y.H _ _ Q.P.L dd _ h₁ e hF (fun a O' r => GlobalTheory.Heat.Adjust.inv_constFn Y.H (v a) (dd a) (hinv a) O' r),
    fun k p p' O' hO f => gauge_glue Y.H _ _ Q.P.L dd _ h₁ e hL he hF _ hc k p p' O' hO f⟩,
    gauge_basic Q oa Y v dd hinv _ x h₁ hB₁ e β hwe _, rfl, rfl, ?_⟩
  intro k σ σ' ρ ρ' hρ hρ' hA p
  exact gauge_acts Y.H _ _ Q.P.L dd _ h₁ e hL he hF _ hc k σ σ' ρ ρ' hρ hρ' hA p

end GlobalTheory.Heat.Gauge
