import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SqNormIntegralFundamentalDomainEqL2NormSq

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.TensLatMove

variable {D : D7}

def emb (D : D7) : AfE D →ₗ[D.host.F] AE D :=
  TensorProduct.map (GlobalTheory.AdelicLatMove.finIncl D) LinearMap.id

theorem emb_tmul (e : D.host.E) (α : Af D.host.F) :
    emb D (α ⊗ₜ[D.host.F] e) = (pairA D.host.F 0 α) ⊗ₜ[D.host.F] e := rfl

theorem finPart_tmul (x : AF D.host.F) (e : D.host.E) :
    Formalism.L2.Theta.finPart D (x ⊗ₜ[D.host.F] e) = (sndA D.host.F x) ⊗ₜ[D.host.F] e := rfl

theorem emb_mul (a : AE D) (x : AfE D) : emb D (Formalism.L2.Theta.finPart D a * x) = a * emb D x := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, add_mul, ha, hb]
  | tmul y e =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, mul_add, ha, hb]
    | tmul α f =>
      rw [finPart_tmul, Algebra.TensorProduct.tmul_mul_tmul, emb_tmul, emb_tmul,
        Algebra.TensorProduct.tmul_mul_tmul]
      congr 1
      exact Prod.ext (mul_zero y.1).symm rfl

def outer (S T : HSp D) (v : Fin S.rank → AfE D) (u : Fin T.rank → AfE D) : WO S T :=
  Matrix.of fun a k => emb D (u a * v k)

def outerHom (S T : HSp D) : (Fin S.rank → AfE D) →+ (Fin T.rank → AfE D) →+ WO S T :=
  AddMonoidHom.mk' (fun v => AddMonoidHom.mk' (fun u => outer S T v u) (fun u u' => by
      ext i j
      simp only [outer, Matrix.of_apply, Matrix.add_apply, Pi.add_apply, map_add, add_mul]))
    (fun v v' => AddMonoidHom.ext fun u => by
      ext i j
      simp only [outer, AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, Matrix.of_apply, Matrix.add_apply,
        Pi.add_apply, map_add, mul_add])

theorem intAf_mul {α β : Af D.host.F} (hα : α ∈ Formalism.MainNotions.StandardLattice.intAf D.host.F) (hβ : β ∈ Formalism.MainNotions.StandardLattice.intAf D.host.F) :
    α * β ∈ Formalism.MainNotions.StandardLattice.intAf D.host.F := fun v => by
  rw [map_mul]; exact mul_mem (hα v) (hβ v)

theorem intAf_one : (1 : Af D.host.F) ∈ Formalism.MainNotions.StandardLattice.intAf D.host.F := fun v => by
  rw [map_one]; exact one_mem _

theorem outer_pure (S T : HSp D) (s : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E) (α β : Af D.host.F) :
    outer S T (fun i => α ⊗ₜ[D.host.F] s i) (fun i => β ⊗ₜ[D.host.F] t i) =
      Matrix.of fun a k => (pairA D.host.F 0 (β * α)) ⊗ₜ[D.host.F] (vecMulVec s t k a) := by
  ext a k
  simp only [outer, Matrix.of_apply, Algebra.TensorProduct.tmul_mul_tmul, emb_tmul, vecMulVec_apply, mul_comm (t a)]

theorem outer_mem (S T : HSp D) (Λ : Lt D.host.E S.rank) (L : Lt D.host.E T.rank)
    (v : Fin S.rank → AfE D) (hv : v ∈ hatV Λ) (u : Fin T.rank → AfE D) (hu : u ∈ hatV L) :
    outer S T v u ∈ hatA S T (tens Λ L) := by
  change outerHom S T v u ∈ _
  induction hv using AddSubgroup.closure_induction with
  | mem s hs =>
    induction hu using AddSubgroup.closure_induction with
    | mem t ht =>
      obtain ⟨α, hα, x, hx, rfl⟩ := hs
      obtain ⟨β, hβ, y, hy, rfl⟩ := ht
      apply AddSubgroup.subset_closure
      exact ⟨β * α, intAf_mul hβ hα, vecMulVec x y, AddSubgroup.subset_closure ⟨x, hx, y, hy, rfl⟩,
        outer_pure S T x y α β⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | neg y _ hy => rw [map_neg]; exact neg_mem hy
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | neg y _ hy => rw [map_neg]; exact neg_mem hy

theorem hatA_le (S T : HSp D) (Λ : Lt D.host.E S.rank) (L : Lt D.host.E T.rank) (K : AddSubgroup (WO S T))
    (hK : ∀ v ∈ hatV Λ, ∀ u ∈ hatV L, outer S T v u ∈ K) : hatA S T (tens Λ L) ≤ K := by
  rw [hatA, AddSubgroup.closure_le]
  rintro _ ⟨α, hα, y, hy, rfl⟩
  change _ ∈ K
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨s, hs, t, ht, rfl⟩ := hy
    have e := outer_pure S T s t 1 α
    rw [mul_one] at e
    rw [← e]
    exact hK _ (AddSubgroup.subset_closure ⟨1, intAf_one, s, hs, rfl⟩) _
      (AddSubgroup.subset_closure ⟨α, hα, t, ht, rfl⟩)
  | zero =>
    convert zero_mem K using 1
    ext a k
    simp
  | add y z _ _ hy hz =>
    convert add_mem hy hz using 1
    ext a k
    simp [TensorProduct.tmul_add]
  | neg y _ hy =>
    convert neg_mem hy using 1
    ext a k
    simp [TensorProduct.tmul_neg]

theorem actO_outer (S T : HSp D) (hS : S.gram = 1) (h : GA D S) (g : GA D T) (v : Fin S.rank → AfE D)
    (u : Fin T.rank → AfE D) :
    actO S T h g (outer S T v u) = outer S T (fmtC S h *ᵥ v) (fmt T g *ᵥ u) := by
  have key := GlobalTheory.AdelicLatMove.gram_mul_inv S h
  have h1 : S.gram.map (incA D) = 1 := by rw [hS, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [h1, Matrix.one_mul, Matrix.mul_one] at key
  ext i j
  simp only [actO, key, outer, Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply, Matrix.map_apply]
  simp only [← emb_mul, ← map_sum, mul_comm (emb D _)]
  congr 1
  simp only [fmt, fmtC, Formalism.L2.Theta.cM, Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
  ring

def actHom (S T : HSp D) (h : GA D S) (g : GA D T) : WO S T →+ WO S T :=
  AddMonoidHom.mk' (actO S T h g) (fun x y => by simp only [actO, Matrix.mul_add, Matrix.add_mul])

theorem mem_hatA_iff (S T : HSp D) (hS : S.gram = 1) (h : GA D S) (g : GA D T) (Λ Λ' : Lt D.host.E S.rank)
    (L L' : Lt D.host.E T.rank) (h1 : IsMov (fmtC S h) Λ Λ') (h2 : IsMov (fmt T g) L L') (u : WO S T) :
    u ∈ hatA S T (tens Λ' L') ↔ ∃ u₀ ∈ hatA S T (tens Λ L), u = actO S T h g u₀ := by
  constructor
  · intro hu
    have := hatA_le S T Λ' L' ((hatA S T (tens Λ L)).map (actHom S T h g)) (fun v hv w hw => by
      obtain ⟨v₀, hv₀, rfl⟩ := (h1 v).1 hv
      obtain ⟨w₀, hw₀, rfl⟩ := (h2 w).1 hw
      exact ⟨_, outer_mem S T Λ L v₀ hv₀ w₀ hw₀, actO_outer S T hS h g v₀ w₀⟩) hu
    obtain ⟨u₀, hu₀, e⟩ := this
    exact ⟨u₀, hu₀, e.symm⟩
  · rintro ⟨u₀, hu, rfl⟩
    refine hatA_le S T Λ L ((hatA S T (tens Λ' L')).comap (actHom S T h g)) (fun v hv w hw => ?_) hu
    change actO S T h g _ ∈ hatA S T (tens Λ' L')
    rw [actO_outer S T hS]
    exact outer_mem S T Λ' L' _ ((h1 _).2 ⟨v, hv, rfl⟩) _ ((h2 _).2 ⟨w, hw, rfl⟩)

theorem hatA_move : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ (h : GA D S) (g : GA D T) (Λ Λ' : Lt D.host.E S.rank) (L L' : Lt D.host.E T.rank), IsMov (fmtC S h) Λ Λ' → IsMov (fmt T g) L L' → (∀ u, u ∈ hatA S T (tens Λ' L') ↔ ∃ u₀ ∈ hatA S T (tens Λ L), u = actO S T h g u₀) ∧ ∀ om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ), IsWeak C.ψ S T om → ∀ f, C.IsTh f → IsLatVac (heisO C.ψ S T) (hatA S T (tens Λ L)) f → IsLatVac (heisO C.ψ S T) (hatA S T (tens Λ' L')) (om (h, g) f) := by
  intro D S T C h g Λ Λ' L L' h1 h2
  have hΛ := mem_hatA_iff S T C.m.gS h g Λ Λ' L L' h1 h2
  refine ⟨hΛ, fun om hW f hth hlat => ⟨fun u hu => ?_, fun e he u hu hh => ?_⟩⟩
  · obtain ⟨u₀, hu₀, rfl⟩ := (hΛ u).1 hu
    rw [← GlobalTheory.WeilVacMove.actO_two_nsmul, ← hW.om_heis h g _ f hth, hlat.1 u₀ hu₀]
  · obtain ⟨u₀, hu₀, rfl⟩ := (hΛ u).1 hu
    have h0 : IsHalf e u₀ := by
      have := GlobalTheory.WeilVacMove.isHalf_actO e h⁻¹ g⁻¹ hh
      rwa [GlobalTheory.WeilVacMove.actO_inv_actO] at this
    rw [← hW.om_heis h g _ f hth, hlat.2 e he u₀ hu₀ h0]

end GlobalTheory.TensLatMove

end
