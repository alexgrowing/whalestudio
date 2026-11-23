import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.AdelicLatMove

variable {D : D7}

def finIncl (D : D7) : Af D.host.F →ₗ[D.host.F] AF D.host.F :=
  LinearMap.inr D.host.F (Ainf D.host.F) (Af D.host.F)

def finEmb (D : D7) : EAf D →ₗ[D.host.F] AE D :=
  (TensorProduct.map (finIncl D) LinearMap.id).comp
    (TensorProduct.comm D.host.F D.host.E (Af D.host.F)).toLinearMap

theorem finEmb_tmul (e : D.host.E) (α : Af D.host.F) :
    finEmb D (e ⊗ₜ[D.host.F] α) = (pairA D.host.F 0 α) ⊗ₜ[D.host.F] e := rfl

theorem toEAf_tmul (x : AF D.host.F) (e : D.host.E) :
    toEAf D (x ⊗ₜ[D.host.F] e) = e ⊗ₜ[D.host.F] (sndA D.host.F x) := rfl

theorem finEmb_mul (a : AE D) (x : EAf D) : finEmb D (toEAf D a * x) = a * finEmb D x := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, add_mul, ha, hb]
  | tmul y e =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, mul_add, ha, hb]
    | tmul f α =>
      rw [toEAf_tmul, Algebra.TensorProduct.tmul_mul_tmul, finEmb_tmul, finEmb_tmul,
        Algebra.TensorProduct.tmul_mul_tmul]
      congr 1
      exact Prod.ext (mul_zero y.1).symm rfl

def cF (D : D7) : EAf D →+* EAf D := Formalism.UG.sigR D.sp.cm.sig (Af D.host.F)

theorem cF_tmul (e : D.host.E) (α : Af D.host.F) :
    cF D (e ⊗ₜ[D.host.F] α) = star e ⊗ₜ[D.host.F] α := rfl

theorem toEAf_cA (a : AE D) : toEAf D (cA D a) = cF D (toEAf D a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul y e => rfl

theorem toEAf_incA (e : D.host.E) : toEAf D (incA D e) = eToEAf D e := rfl

def rankOne (S T : HSp D) (a : D.host.E) (s : Fin S.rank → EAf D) (t : Fin T.rank → EAf D) : WO S T :=
  Matrix.of fun i j => finEmb D (eToEAf D a * t i * ∑ k, cF D (s k) * eToEAf D (S.gram k j))

theorem rankOne_add_left (S T : HSp D) (a : D.host.E) (s s' : Fin S.rank → EAf D) (t : Fin T.rank → EAf D) :
    rankOne S T a (s + s') t = rankOne S T a s t + rankOne S T a s' t := by
  ext i j
  simp only [rankOne, Matrix.of_apply, Matrix.add_apply, Pi.add_apply, map_add, add_mul, mul_add,
    Finset.sum_add_distrib]

theorem rankOne_add_right (S T : HSp D) (a : D.host.E) (s : Fin S.rank → EAf D) (t t' : Fin T.rank → EAf D) :
    rankOne S T a s (t + t') = rankOne S T a s t + rankOne S T a s t' := by
  ext i j
  simp only [rankOne, Matrix.of_apply, Matrix.add_apply, Pi.add_apply, map_add, add_mul, mul_add]

def rankOneHom (S T : HSp D) (a : D.host.E) : (Fin S.rank → EAf D) →+ (Fin T.rank → EAf D) →+ WO S T :=
  AddMonoidHom.mk' (fun s => AddMonoidHom.mk' (fun t => rankOne S T a s t) (rankOne_add_right S T a s))
    (fun s s' => AddMonoidHom.ext fun t => rankOne_add_left S T a s s' t)

def pureSet {n : ℕ} (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Set (Fin n → EAf D) :=
  {y | ∃ α ∈ Formalism.UG.intAd D.host.F, ∃ x ∈ Λ, y = fun i => x i ⊗ₜ[D.host.F] α}

theorem smul_mem_closure {n : ℕ} (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (r : EAf D)
    (hr : r ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    ∀ y ∈ AddSubgroup.closure (pureSet Λ), r • y ∈ AddSubgroup.closure (pureSet Λ) := by
  induction hr using Subring.closure_induction with
  | mem r hr =>
    intro y hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨α, hα, x, hx, rfl⟩ := hy
      apply AddSubgroup.subset_closure
      rcases hr with ⟨⟨_, b, rfl⟩, rfl⟩ | ⟨⟨β, hβ⟩, rfl⟩
      · refine ⟨α, hα, b • x, Λ.smul_mem b hx, ?_⟩
        ext i
        simp [Algebra.smul_def]
      · refine ⟨β * α, mul_mem hβ hα, x, hx, ?_⟩
        ext i
        simp
    | zero => simp
    | add y z _ _ hy hz => rw [smul_add]; exact add_mem hy hz
    | neg y _ hy => rw [smul_neg]; exact neg_mem hy
  | zero => intro y _; simp
  | one => intro y hy; simpa using hy
  | add a b _ _ ha hb => intro y hy; rw [add_smul]; exact add_mem (ha y hy) (hb y hy)
  | neg a _ ha => intro y hy; rw [neg_smul]; exact neg_mem (ha y hy)
  | mul a b _ _ ha hb => intro y hy; rw [mul_smul]; exact ha _ (hb y hy)

theorem mem_closure_of_mem_hatL {n : ℕ} (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (y : Fin n → EAf D)
    (hy : y ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) : y ∈ AddSubgroup.closure (pureSet Λ) := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    exact AddSubgroup.subset_closure ⟨1, one_mem _, x, hx, rfl⟩
  | zero => exact zero_mem _
  | add y z _ _ hy hz => exact add_mem hy hz
  | smul r y _ hy => exact smul_mem_closure Λ r.1 r.2 y hy

theorem pure_mem_hatL {n : ℕ} (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (α : Af D.host.F)
    (hα : α ∈ Formalism.UG.intAd D.host.F) (x : Fin n → D.host.E) (hx : x ∈ Λ) :
    (fun i => x i ⊗ₜ[D.host.F] α) ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
  have h1 : ((1 : D.host.E) ⊗ₜ[D.host.F] α : EAf D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    Subring.subset_closure (Or.inr ⟨⟨α, hα⟩, rfl⟩)
  have h2 : (fun i => x i ⊗ₜ[D.host.F] (1 : Af D.host.F)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ :=
    Submodule.subset_span ⟨x, hx, rfl⟩
  have h3 := Submodule.smul_mem _ (⟨_, h1⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) h2
  convert h3 using 1
  ext i
  change _ = ((1 : D.host.E) ⊗ₜ[D.host.F] α : EAf D) * _
  simp

theorem rankOne_pure (S T : HSp D) (a : D.host.E) (s : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E)
    (α β : Af D.host.F) :
    rankOne S T a (fun i => s i ⊗ₜ[D.host.F] α) (fun i => t i ⊗ₜ[D.host.F] β) =
      Matrix.of fun i j => (pairA D.host.F 0 (β * α)) ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) := by
  ext i j
  simp only [rankOne, Matrix.of_apply]
  rw [← finEmb_tmul]
  congr 1
  simp only [cF_tmul, eToEAf, Algebra.TensorProduct.includeLeftRingHom_apply,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [← TensorProduct.sum_tmul, Algebra.TensorProduct.tmul_mul_tmul]

theorem rankOne_mem_latO (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (a : D.host.E) (ha : a ∈ D.host.AA)
    (s : Fin S.rank → EAf D) (hs : s ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛS)
    (t : Fin T.rank → EAf D) (ht : t ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛT) :
    rankOne S T a s t ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
      fun _ => True := by
  have hs' := mem_closure_of_mem_hatL ΛS s hs
  have ht' := mem_closure_of_mem_hatL ΛT t ht
  clear hs ht
  change rankOneHom S T a s t ∈ _
  induction hs' using AddSubgroup.closure_induction with
  | mem s hs =>
    induction ht' using AddSubgroup.closure_induction with
    | mem t ht =>
      obtain ⟨α, hα, x, hx, rfl⟩ := hs
      obtain ⟨β, hβ, y, hy, rfl⟩ := ht
      apply AddSubgroup.subset_closure
      exact ⟨β * α, (mul_mem hβ hα : β * α ∈ Formalism.UG.intAd D.host.F), fun _ h => absurd trivial h, a, ha, x, hx, y, hy,
        rankOne_pure S T a x y α β⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | neg y _ hy => rw [map_neg]; exact neg_mem hy
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | neg y _ hy => rw [map_neg]; exact neg_mem hy

theorem mt_mul (V : HSp D) (g g' : GA D V) : mt V (g * g') = mt V g * mt V g' := by
  simp [Formalism.L2.Theta.mt]

theorem mt_one (V : HSp D) : mt V 1 = 1 := by simp [Formalism.L2.Theta.mt]

theorem gram_mul_inv (V : HSp D) (g : GA D V) :
    V.gram.map (incA D) * mt V g⁻¹ = ((mt V g).map (cA D))ᵀ * V.gram.map (incA D) := by
  have h : ((mt V g).map (cA D))ᵀ * V.gram.map (incA D) * mt V g = V.gram.map (incA D) := g.2
  conv_lhs => rw [← h]
  rw [Matrix.mul_assoc, ← mt_mul, mul_inv_cancel, mt_one, Matrix.mul_one]

theorem actO_rankOne (S T : HSp D) (g : GA D S) (h : GA D T) (a : D.host.E) (s : Fin S.rank → EAf D)
    (t : Fin T.rank → EAf D) :
    actO S T g h (rankOne S T a s t) =
      rankOne S T a ((mt S g).map (toEAf D) *ᵥ s) ((mt T h).map (toEAf D) *ᵥ t) := by
  ext i j
  have key : ∀ k, ∑ l, eToEAf D (S.gram k l) * toEAf D (mt S g⁻¹ l j) =
      ∑ l, cF D (toEAf D (mt S g l k)) * eToEAf D (S.gram l j) := by
    intro k
    have := congrArg (toEAf D) (congrFun (congrFun (gram_mul_inv S g) k) j)
    simpa only [Matrix.mul_apply, map_sum, map_mul, Matrix.map_apply, Matrix.transpose_apply, toEAf_cA,
      toEAf_incA] using this
  have key2 : ∑ l, (∑ k, cF D (s k) * eToEAf D (S.gram k l)) * toEAf D (mt S g⁻¹ l j) =
      ∑ k, cF D (((mt S g).map (toEAf D) *ᵥ s) k) * eToEAf D (S.gram k j) := by
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, Finset.sum_mul]
    rw [Finset.sum_comm, Finset.sum_comm (f := fun k l => cF D (toEAf D (mt S g k l)) * cF D (s l) * _)]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [mul_assoc, mul_left_comm _ (cF D (s k))]
    rw [← Finset.mul_sum, ← Finset.mul_sum, key]
  simp only [actO, rankOne, Matrix.mul_apply, Matrix.of_apply]
  rw [← key2]
  simp only [← finEmb_mul, ← map_sum, mul_comm (finEmb D _)]
  congr 1
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
  rw [Finset.mul_sum (f := fun l => (∑ k, cF D (s k) * eToEAf D (S.gram k l)) * toEAf D (mt S g⁻¹ l j))]
  refine Finset.sum_congr rfl fun l _ => ?_
  generalize (∑ k, cF D (s k) * eToEAf D (S.gram k l)) = w
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

theorem mulVec_mem_hatL {n : ℕ} (M : Matrix (Fin n) (Fin n) (EAf D))
    (Λ Λ' : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (β β' : GL (Fin n) (EAf D))
    (hβ : Formalism.L2.DIV.IsFrame β Λ) (hβ' : Formalism.L2.DIV.IsFrame β' Λ') (hM : β'.val = M * β.val)
    (x : Fin n → EAf D) (hx : x ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) :
    M *ᵥ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ' := by
  rw [hβ' _]
  have e : (β'⁻¹).val * M = (β⁻¹).val := by
    have h1 : M = β'.val * (β⁻¹).val := by
      rw [hM, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
    rw [h1, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  rw [Matrix.mulVec_mulVec, e]
  exact (hβ x).1 hx

theorem actO_mem_latO (S T : HSp D) (g : GA D S) (h : GA D T)
    (ΛS ΛS' : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT ΛT' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (βS βS' : GL (Fin S.rank) (EAf D)) (βT βT' : GL (Fin T.rank) (EAf D))
    (hS : Formalism.L2.DIV.IsFrame βS ΛS) (hS' : Formalism.L2.DIV.IsFrame βS' ΛS')
    (hT : Formalism.L2.DIV.IsFrame βT ΛT) (hT' : Formalism.L2.DIV.IsFrame βT' ΛT')
    (hg : βS'.val = (mt S g).map (toEAf D) * βS.val) (hh : βT'.val = (mt T h).map (toEAf D) * βT.val)
    (u : WO S T)
    (hu : u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) :
    actO S T g h u ∈
      latO S T (ΛS' : Set (Fin S.rank → D.host.E)) (ΛT' : Set (Fin T.rank → D.host.E)) fun _ => True := by
  induction hu using AddSubgroup.closure_induction with
  | mem u hu =>
    obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hu
    have e := rankOne_pure S T a s t 1 α
    rw [mul_one] at e
    rw [← e, actO_rankOne]
    exact rankOne_mem_latO S T ΛS' ΛT' a ha _
      (mulVec_mem_hatL _ ΛS ΛS' βS βS' hS hS' hg _ (pure_mem_hatL ΛS 1 (one_mem _) s hs)) _
      (mulVec_mem_hatL _ ΛT ΛT' βT βT' hT hT' hh _ (pure_mem_hatL ΛT α hα t ht))
  | zero => simp only [actO, Matrix.mul_zero, Matrix.zero_mul]; exact zero_mem _
  | add y z _ _ hy hz => simp only [actO, Matrix.mul_add, Matrix.add_mul] at hy hz ⊢; exact add_mem hy hz
  | neg y _ hy => simp only [actO, Matrix.mul_neg, Matrix.neg_mul] at hy ⊢; exact neg_mem hy

theorem frame_inv (V : HSp D) (g : GA D V) (β β' : GL (Fin V.rank) (EAf D))
    (hg : β'.val = (mt V g).map (toEAf D) * β.val) : β.val = (mt V g⁻¹).map (toEAf D) * β'.val := by
  rw [hg, ← Matrix.mul_assoc, ← Matrix.map_mul, ← mt_mul, inv_mul_cancel, mt_one,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]

theorem actO_actO_inv (S T : HSp D) (g : GA D S) (h : GA D T) (u : WO S T) :
    actO S T g h (actO S T g⁻¹ h⁻¹ u) = u := by
  simp only [actO, inv_inv]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← mt_mul, mul_inv_cancel, mt_one, Matrix.one_mul, Matrix.mul_assoc,
    ← mt_mul, mul_inv_cancel, mt_one, Matrix.mul_one]

theorem mem_latO_iff_exists_actO : ∀ (D : D7) (S T : HSp D) (g : GA D S) (h : GA D T) (ΛS ΛS' : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT ΛT' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS βS' : GL (Fin S.rank) (EAf D)) (βT βT' : GL (Fin T.rank) (EAf D)), Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βS' ΛS' → Formalism.L2.DIV.IsFrame βT ΛT → Formalism.L2.DIV.IsFrame βT' ΛT' → Submodule.IsLattice D.host.E ΛS → Submodule.IsLattice D.host.E ΛS' → Submodule.IsLattice D.host.E ΛT → Submodule.IsLattice D.host.E ΛT' → βS'.val = (mt S g).map (toEAf D) * βS.val → βT'.val = (mt T h).map (toEAf D) * βT.val → ∀ u : WO S T, u ∈ (latO S T (ΛS' : Set (Fin S.rank → D.host.E)) (ΛT' : Set (Fin T.rank → D.host.E)) fun _ => True) ↔ ∃ u₀ ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), u = actO S T g h u₀ := by
  intro D S T g h ΛS ΛS' ΛT ΛT' βS βS' βT βT' hS hS' hT hT' _ _ _ _ hg hh u
  constructor
  · intro hu
    exact ⟨_, actO_mem_latO S T g⁻¹ h⁻¹ ΛS' ΛS ΛT' ΛT βS' βS βT' βT hS' hS hT' hT (frame_inv S g _ _ hg)
      (frame_inv T h _ _ hh) u hu, (actO_actO_inv S T g h u).symm⟩
  · rintro ⟨u₀, hu, rfl⟩
    exact actO_mem_latO S T g h ΛS ΛS' ΛT ΛT' βS βS' βT βT' hS hS' hT hT' hg hh u₀ hu

end GlobalTheory.AdelicLatMove

end
