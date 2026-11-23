import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeatOperatorGluedPullbackBundlePower
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
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.HeatUniq.FourierChart

open GlobalTheory.KS GlobalTheory.Heat.Glue

theorem images_eq : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (dd : Fin n → Fld Y.H.left) (D : R → R), (∀ a, IsField ⊤ (dd a)) → ∀ (h h' : Heat Y.H Y.q.left Q.P.L dd D), IsBasic Y h → IsBasic Y h' → ∀ (k : ℕ) (α : Q.X) (C : R), (∀ (i : h.J) (i' : h'.J) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ h.W i ⊓ h'.W i' → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V) f → op Y.H dd h.Θ h.u (h.d i) (h.p i) (h.p' i) k (Y.q.left ⁻¹ᵁ V) (pbT Y.q.left (Q.P.L.g (h.j i) (h'.j i')).val (Y.q.left ⁻¹ᵁ V) ^ k * f) = pbT Y.q.left (Q.P.L.g (h.j i) (h'.j i')).val (Y.q.left ⁻¹ᵁ V) ^ k * (op Y.H dd h'.Θ h'.u (h'.d i') (h'.p i') (h'.p' i') k (Y.q.left ⁻¹ᵁ V) f + constFn Y.H.hom _ C * f)) → ∀ (τ₁ τ₁' τ₂ τ₂'' : SecM Y.q.left Q.P.L k), (∀ (y : Y.H.left) J, Good Q.P.L y J → sval τ₁ (𝟙 Y.H.left) y J = sval τ₂ (𝟙 Y.H.left) y J) → (∀ (j : Q.P.L.ι) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ Y.q.left ⁻¹ᵁ Q.P.L.U j → IsWt Y α (Y.q.left ⁻¹ᵁ V) (rsT (τ₂.f fun _ => j) (Y.q.left ⁻¹ᵁ V))) → h.Acts k τ₁ τ₁' → h'.Acts k τ₂ τ₂'' → ∀ (y : Y.H.left) J, Good Q.P.L y J → sval τ₁' (𝟙 Y.H.left) y J = sval τ₂'' (𝟙 Y.H.left) y J + gs (𝟙 _) y ⊤ (scal Y.H.hom C) * sval τ₂ (𝟙 Y.H.left) y J := by
  intro R _ _ Q Oa _ _ _ oa Y n dd D hdd h h' hb hb' k α C hloc τ₁ τ₁' τ₂ τ₂'' hgerm hwt hA hA'
  have hL : Q.P.L.IsLB := Q.P.isLB

  have e1 : ∀ c : Fin 1 → Q.P.L.ι, τ₁.f c = τ₂.f c := by
    intro c
    refine fn_ext fun x hx => ?_
    obtain ⟨J, hJ, hJc⟩ := exists_good Q.P.L hL x (fun _ : Fin 1 => 𝟙 Y.H.left ≫ Y.q.left) c
      (fun a b _ => by rw [Subsingleton.elim a b]) (fun k => by
        simpa using Set.mem_iInter.1 hx k)
    have := hgerm x J hJ
    rwa [sval_of τ₁ (𝟙 _) x J c hJc, sval_of τ₂ (𝟙 _) x J c hJc] at this

  have loc : ∀ (hh : Heat Y.H Y.q.left Q.P.L dd D) (i : hh.J) (O : Y.H.left.Opens) (hO : O ≤ hh.W i)
      (f : Γ(Y.H.left, hh.W i)),
      rsT (op Y.H dd hh.Θ hh.u (hh.d i) (hh.p i) (hh.p' i) k (hh.W i) f) O =
        op Y.H dd hh.Θ hh.u (hh.d i) (hh.p i) (hh.p' i) k O (rsT f O) := by
    intro hh i O hO f
    have hd : ∀ g, resG Y.H.left hO (hh.d i (hh.W i) g) = hh.d i O (resG Y.H.left hO g) :=
      fun g => ((hh.lift i).1.2.2 (hh.W i) O hO le_rfl g).symm
    have hdd' : ∀ a g, resG Y.H.left hO (dd a (hh.W i) g) = dd a O (resG Y.H.left hO g) :=
      fun a g => ((hdd a).2.2 (hh.W i) O hO le_top g).symm
    have hc : ∀ r, resG Y.H.left hO (constFn Y.H.hom (hh.W i) r) = constFn Y.H.hom O r :=
      fun r => (rsT_of_le hO _).symm.trans (rsT_constFn Y.H.hom hO r)
    have hp : ∀ p : Γ(Y.H.left, hh.W i), resG Y.H.left hO (rsT p (hh.W i)) = rsT p O := fun p => by
      rw [← rsT_of_le hO, rsT_rsT le_rfl hO]
    rw [rsT_of_le hO, rsT_of_le hO]
    simp only [op, map_add, map_sub, map_mul, map_sum, map_pow, map_natCast, map_ofNat, hd, hdd', hc, hp]

  have actO : ∀ (hh : Heat Y.H Y.q.left Q.P.L dd D) (τ τ' : SecM Y.q.left Q.P.L k), hh.Acts k τ τ' →
      ∀ (i : hh.J) (O : Y.H.left.Opens), O ≤ hh.W i →
      rsT (τ'.f fun _ => hh.j i) O =
        op Y.H dd hh.Θ hh.u (hh.d i) (hh.p i) (hh.p' i) k O (rsT (τ.f fun _ => hh.j i) O) := by
    intro hh τ τ' hAc i O hO
    have hW : hh.W i ≤ (LB.LinComb Q.P.L (K := Fin 1) (fun _ => Y.q.left) fun _ => (k : ℤ)).U (fun _ => hh.j i) := le_wchart _ (hh.le i)
    rw [← rsT_rsT hW hO (τ'.f _), hAc i, loc hh i O hO, rsT_rsT hW hO]

  have chart : ∀ (i : h.J) (i' : h'.J), ∃ O : Y.H.left.Opens, O = h.W i ⊓ h'.W i' ∧
      rsT (τ₁'.f fun _ => h'.j i') O =
        rsT (τ₂''.f fun _ => h'.j i') O + constFn Y.H.hom O C * rsT (τ₂.f fun _ => h'.j i') O := by
    intro i i'
    obtain ⟨V, hV⟩ := (hb i).1
    obtain ⟨V', hV'⟩ := (hb' i').1
    have hO : Y.q.left ⁻¹ᵁ (V ⊓ V') = h.W i ⊓ h'.W i' := by rw [hV, hV']; rfl
    refine ⟨Y.q.left ⁻¹ᵁ (V ⊓ V'), hO, ?_⟩
    have hO1 : Y.q.left ⁻¹ᵁ (V ⊓ V') ≤ h.W i := hO.le.trans inf_le_left
    have hO2 : Y.q.left ⁻¹ᵁ (V ⊓ V') ≤ h'.W i' := hO.le.trans inf_le_right
    have hOc : Y.q.left ⁻¹ᵁ (V ⊓ V') ≤ LB.wchart Q.P.L (fun _ : Fin 1 => Y.q.left) (fun _ => h.j i) ⊓
        LB.wchart Q.P.L (fun _ : Fin 1 => Y.q.left) (fun _ => h'.j i') :=
      le_inf (hO1.trans (le_wchart _ (h.le i))) (hO2.trans (le_wchart _ (h'.le i')))
    have hOU : Y.q.left ⁻¹ᵁ (V ⊓ V') ≤ Y.q.left ⁻¹ᵁ (Q.P.L.U (h.j i) ⊓ Q.P.L.U (h'.j i')) :=
      fun y hy => ⟨h.le i (hO1 hy), h'.le i' (hO2 hy)⟩
    have hunit : pbT Y.q.left (Q.P.L.g (h.j i) (h'.j i')).val (Y.q.left ⁻¹ᵁ (V ⊓ V')) *
        pbT Y.q.left (Q.P.L.g (h.j i) (h'.j i'))⁻¹.val (Y.q.left ⁻¹ᵁ (V ⊓ V')) = 1 := by
      rw [← pbT_mul, Units.mul_inv, pbT_one _ hOU]
    have hw := hwt (h'.j i') (V ⊓ V') (hO2.trans (h'.le i'))
    have key := hloc i i' (V ⊓ V') hO.le _ hw
    have s1 := sec_rel Y.q.left k τ₁ (fun _ => h.j i) (fun _ => h'.j i') hOc
    have s1' := sec_rel Y.q.left k τ₁' (fun _ => h.j i) (fun _ => h'.j i') hOc
    have a1 := actO h τ₁ τ₁' hA i _ hO1
    have a2 := actO h' τ₂ τ₂'' hA' i' _ hO2
    beta_reduce at s1 s1'
    rw [e1, e1] at s1
    rw [e1, s1, key, ← a2, s1'] at a1
    have hu : IsUnit (pbT Y.q.left (Q.P.L.g (h.j i) (h'.j i')).val (Y.q.left ⁻¹ᵁ (V ⊓ V')) ^ k) :=
      (show IsUnit _ from ⟨⟨_, _, hunit, by rw [mul_comm]; exact hunit⟩, rfl⟩).pow k
    exact hu.mul_left_cancel a1

  intro y J hJ
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (show y ∈ ⨆ i, h.W i by rw [h.cover]; trivial)
  obtain ⟨i', hi'⟩ := TopologicalSpace.Opens.mem_iSup.1 (show y ∈ ⨆ i, h'.W i by rw [h'.cover]; trivial)
  obtain ⟨O, hOeq, hid⟩ := chart i i'
  have hyO : y ∈ O := hOeq ▸ ⟨hi, hi'⟩
  have hOc : O ≤ LB.wchart Q.P.L (fun _ : Fin 1 => Y.q.left) (fun _ => h'.j i') :=
    hOeq ▸ (inf_le_right.trans (le_wchart _ (h'.le i')))
  have hyJ := hJ.mem (fun _ : Fin 1 => Y.q.left) (𝟙 Y.H.left)
  have hyj' : (𝟙 Y.H.left) y ∈ LB.wchart Q.P.L (fun _ : Fin 1 => Y.q.left) (fun _ => h'.j i') := hOc hyO
  have tr : ∀ τ : SecM Y.q.left Q.P.L k, sval τ (𝟙 Y.H.left) y J =
      (trF (fun _ : Fin 1 => Y.q.left) (fun _ => (k : ℤ)) (𝟙 Y.H.left) y
        (fun _ => J (𝟙 Y.H.left ≫ Y.q.left)) (fun _ => h'.j i')).val *
        gs (𝟙 Y.H.left) y O (rsT (τ.f fun _ => h'.j i') O) := by
    intro τ
    refine (sec_trans τ (𝟙 Y.H.left) y hyJ hyj').trans (congrArg _ ?_)
    rw [rsT_of_le (show O ≤ (LB.LinComb Q.P.L (K := Fin 1) (fun _ => Y.q.left) fun _ => (k : ℤ)).U (fun _ => h'.j i') from hOc)]
    exact (gs_res (𝟙 Y.H.left) y hOc hyO _).symm
  have hc : gs (𝟙 Y.H.left) y O (constFn Y.H.hom O C) = gs (𝟙 _) y ⊤ (scal Y.H.hom C) := by
    rw [gs_constFn Y.H.hom O (𝟙 Y.H.left) y hyO C, Category.id_comp, cst, gs_eq Y.H.hom y ⊤ trivial]
    exact (gs_eq (𝟙 _) y ⊤ trivial _).symm
  rw [tr τ₁', tr τ₂'', tr τ₂, hid, gs_add _ _ _ hyO, gs_mul _ _ _ hyO, hc]
  ring

end GlobalTheory.HeatUniq.FourierChart
