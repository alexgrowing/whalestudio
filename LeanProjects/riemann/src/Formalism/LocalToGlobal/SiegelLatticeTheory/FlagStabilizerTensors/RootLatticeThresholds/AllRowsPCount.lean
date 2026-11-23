import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsLab

noncomputable section

open MonoidAlgebra

namespace Formalism.L2.SG.Pf.AllRowsPCount

open Formalism.L2.SG.Pf.AllRowsGA Formalism.L2.SG.Pf.AllRowsTr

section Gen

variable {ι : Type} [Fintype ι] [DecidableEq ι] {G : ι → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]
  [∀ i, DecidableEq (G i)] (p : ι → Prop) [DecidablePred p]

def Sub : Subgroup (∀ i, G i) where
  carrier := {γ | ∀ i, ¬ p i → γ i = 1}
  one_mem' := fun _ _ => rfl
  mul_mem' := fun ha hb i hi => by simp [Pi.mul_apply, ha i hi, hb i hi]
  inv_mem' := fun ha i hi => by simp [Pi.inv_apply, ha i hi]

def proj : (∀ i, G i) →* (∀ i, G i) where
  toFun := fun γ i => if p i then γ i else 1
  map_one' := by funext i; split_ifs <;> rfl
  map_mul' := fun a b => by funext i; simp only [Pi.mul_apply]; split_ifs <;> simp

theorem proj_apply (γ : ∀ i, G i) (i : ι) : proj p γ i = if p i then γ i else 1 := rfl

theorem proj_mem (γ : ∀ i, G i) : proj p γ ∈ Sub p :=
  fun i hi => by rw [proj_apply, if_neg hi]

theorem proj_of_mem {γ : ∀ i, G i} (h : γ ∈ Sub p) : proj p γ = γ := by
  funext i
  rw [proj_apply]
  split_ifs with hi
  · rfl
  · exact (h i hi).symm

theorem proj_eq_one_of {q : ι → Prop} {b : ∀ i, G i} (hb : b ∈ Sub q) (hpq : ∀ i, p i → ¬ q i) : proj p b = 1 := by
  funext i
  rw [proj_apply, Pi.one_apply]
  split_ifs with hi
  · exact hb i (hpq i hi)
  · rfl

variable {p}

end Gen

section Res

variable {G : Type} [Group G] [Fintype G] [DecidableEq G] (H : Subgroup G) [Fintype H]

def res (A : MonoidAlgebra ℂ G) : MonoidAlgebra ℂ H :=
  MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm fun h => A.coeff (h : G))

theorem res_coeff (A : MonoidAlgebra ℂ G) (h : H) : (res H A).coeff h = A.coeff (h : G) := by
  simp [res]

variable {H}

theorem res_mul (A B : MonoidAlgebra ℂ G) (hA : ∀ γ, A.coeff γ ≠ 0 → γ ∈ H) (h : H) :
    (A * B).coeff (h : G) = (res H A * res H B).coeff h := by
  classical
  rw [MonoidAlgebra.coeff_mul_apply_left, MonoidAlgebra.coeff_mul_apply_left,
    Finsupp.sum_fintype _ _ (fun _ => zero_mul _), Finsupp.sum_fintype _ _ (fun _ => zero_mul _),
    ← Finset.sum_filter_of_ne (p := fun x => x ∈ H) (fun x _ hx => hA x (left_ne_zero_of_mul hx)),
    Finset.sum_subtype (p := fun x => x ∈ H) (F := ‹Fintype H›) _ (fun x => by simp)]
  simp only [res_coeff, Subgroup.coe_mul, Subgroup.coe_inv]

end Res

section Dlev

open Classical
open NumberField Matrix
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.SG.HidaSetting Formalism.L2.SG.AllRowsOf Formalism.L2.SG.Pf.AllRowsRhoX
  Formalism.L2.SG.Pf.AllRowsFin Formalism.L2.SG.Pf.AllRowsRho Formalism.L2.SG.Pf.AllRowsRedKerA Formalism.L2.SG.Pf.RowDictPf
  Formalism.L2.SG.Pf.RedBasicsPf PIW.AdelClassFin

variable {D : D7} (X : HidaSetting D)

theorem gj_mem_wB (j : Fin 2) (v : D.nd.PlG j) :
    ((D.host.g j : ℕ) : 𝓞 X.B.I.E) ∈ (wB X (D.naut.plGw j v)).asIdeal := by
  show RingOfIntegers.mapRingEquiv X.ιE ((D.host.g j : ℕ) : 𝓞 X.B.I.E) ∈ (D.naut.plGw j v).asIdeal
  rw [map_natCast]; exact D.naut.plGw_over j v

theorem ker_part (j : Fin 2) (z : KSub X.B.I) :
    (∀ v : D.nd.PlG j, rhoX X z ⟨j, v⟩ = 1) ↔ (z : X.B.I.Gf) ∈ X.B.I.Kg (D.host.g j) := by
  constructor
  · intro h
    refine Formalism.L2.SG.Pf.AllRowsRedKer.redKerP_holds X j _ z.2 fun v => ?_
    have := goodAt_rhoX X z ⟨j, v⟩
    rw [h v] at this
    simpa using this
  · intro hz v
    apply Units.ext
    rw [rhoX_apply, rhoB_val, Units.val_one]
    refine matB_eq (redBX X ⟨j, v⟩) z.2 (redMatB_one_of (redBX X ⟨j, v⟩) fun i => ?_)
    obtain ⟨w, hw, hxw⟩ := hz.2 _ (DictLat.iv_mem X.B.I ((redBX X ⟨j, v⟩).hb.1 i))
    have e2 : X.B.I.fmat z *ᵥ iv X.B.I ((redBX X ⟨j, v⟩).b i) - iv X.B.I ((redBX X ⟨j, v⟩).b i) =
        (X.B.I.fmat z - 1) *ᵥ iv X.B.I ((redBX X ⟨j, v⟩).b i) := by rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    rw [e2, hxw]
    have hg : ((D.host.g j : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) =
        Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) ((((D.host.g j : ℕ) : 𝓞 X.B.I.E)) : X.B.I.E) := by simp
    rw [hg]
    exact smul_mem X.B.I _ (gj_mem_wB X j v) hw

theorem part_iff_j (k : Fin 2) (x y : KSub X.B.I) :
    proj (fun kv : (Σ k', D.nd.PlG k') => ¬ kv.1 = k) (rhoX X x) =
      proj (fun kv : (Σ k', D.nd.PlG k') => ¬ kv.1 = k) (rhoX X y) ↔
      ((x⁻¹ * y : KSub X.B.I) : X.B.I.Gf) ∈ X.B.I.Kg (D.host.g (1 - k)) := by
  have hfin : ∀ a : Fin 2, ¬ a = k ↔ a = 1 - k := by
    intro a
    fin_cases a <;> fin_cases k <;> decide
  rw [← ker_part X (1 - k) (x⁻¹ * y)]
  constructor
  · intro h v
    have hv := congrFun h ⟨1 - k, v⟩
    rw [proj_apply, proj_apply, if_pos ((hfin _).2 rfl), if_pos ((hfin _).2 rfl)] at hv
    rw [map_mul, map_inv, Pi.mul_apply, Pi.inv_apply, hv, inv_mul_cancel]
  · intro h
    funext ⟨k', v⟩
    simp only [proj_apply]
    by_cases hk : k' = k
    · rw [if_neg (not_not.2 hk), if_neg (not_not.2 hk)]
    · obtain rfl : k' = 1 - k := (hfin k').1 hk
      rw [if_pos hk, if_pos hk]
      have hv := h v
      rw [map_mul, map_inv, Pi.mul_apply, Pi.inv_apply, inv_mul_eq_one] at hv
      exact hv

theorem part_iff_k (k : Fin 2) (x y : KSub X.B.I) :
    proj (fun kv : (Σ k', D.nd.PlG k') => kv.1 = k) (rhoX X x) =
      proj (fun kv : (Σ k', D.nd.PlG k') => kv.1 = k) (rhoX X y) ↔
      ((x⁻¹ * y : KSub X.B.I) : X.B.I.Gf) ∈ X.B.I.Kg (D.host.g k) := by
  rw [← ker_part X k (x⁻¹ * y)]
  constructor
  · intro h v
    have hv := congrFun h ⟨k, v⟩
    rw [proj_apply, proj_apply, if_pos rfl, if_pos rfl] at hv
    rw [map_mul, map_inv, Pi.mul_apply, Pi.inv_apply, hv, inv_mul_cancel]
  · intro h
    funext ⟨k', v⟩
    simp only [proj_apply]
    by_cases hk : k' = k
    · subst hk
      rw [if_pos rfl, if_pos rfl]
      have hv := h v
      rw [map_mul, map_inv, Pi.mul_apply, Pi.inv_apply, inv_mul_eq_one] at hv
      exact hv
    · rw [if_neg hk, if_neg hk]

open Classical in

def redD (k : Fin 2) : X.B.I.RedDatum (D.host.g (1 - k) ^ 1) (D.host.g k ^ 1) where
  G₁ := ↥(Sub (fun kv : (Σ k', D.nd.PlG k') => ¬ kv.1 = k))
  G₂ := ↥(Sub (fun kv : (Σ k', D.nd.PlG k') => kv.1 = k))
  fin₁ := Fintype.ofFinite _
  fin₂ := Fintype.ofFinite _
  red := fun x => if hx : x ∈ X.B.I.Kset then
    (⟨proj _ (rhoX X ⟨x, hx⟩), proj_mem _ _⟩, ⟨proj _ (rhoX X ⟨x, hx⟩), proj_mem _ _⟩) else 1
  red_mul := fun x hx y hy => by
    have hxy : x * y ∈ X.B.I.Kset := Formalism.L2.SG.Pf.unitaryCongruence.K_mul X.B.I hx hy
    simp only [dif_pos hx, dif_pos hy, dif_pos hxy]
    have e : (⟨x * y, hxy⟩ : KSub X.B.I) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
    rw [e]
    ext <;> simp [map_mul]
  red_surj := fun ab => by
    obtain ⟨a, b⟩ := ab
    have hS := Formalism.L2.SG.Pf.AllRowsAdd.hS_X X
    have hm : ((sec hS ((a : G0g D.nd) * (b : G0g D.nd)) : KSub X.B.I) : X.B.I.Gf) ∈ X.B.I.Kset := (sec hS _).2
    refine ⟨(sec hS ((a : G0g D.nd) * (b : G0g D.nd)) : X.B.I.Gf), hm, ?_⟩
    rw [dif_pos hm]
    have e : (⟨(sec hS ((a : G0g D.nd) * (b : G0g D.nd)) : X.B.I.Gf), (sec hS _).2⟩ : KSub X.B.I) =
        sec hS ((a : G0g D.nd) * (b : G0g D.nd)) := rfl
    rw [e, rho_sec]
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · show proj _ ((a : G0g D.nd) * (b : G0g D.nd)) = (a : G0g D.nd)
      rw [map_mul, proj_of_mem _ a.2,
        proj_eq_one_of _ b.2 (fun (i : Σ k' : Fin 2, D.nd.PlG k') (hi : ¬ i.1 = k) h => hi h), mul_one]
    · show proj _ ((a : G0g D.nd) * (b : G0g D.nd)) = (b : G0g D.nd)
      rw [map_mul, proj_of_mem _ b.2,
        proj_eq_one_of _ a.2 (fun (i : Σ k' : Fin 2, D.nd.PlG k') (hi : i.1 = k) h => h hi), one_mul]
  red_fib₁ := fun x hx y hy => by
    simp only [dif_pos hx, dif_pos hy, pow_one]
    rw [Subtype.ext_iff]
    exact part_iff_j X k ⟨x, hx⟩ ⟨y, hy⟩
  red_fib₂ := fun x hx y hy => by
    simp only [dif_pos hx, dif_pos hy, pow_one]
    rw [Subtype.ext_iff]
    exact part_iff_k X k ⟨x, hx⟩ ⟨y, hy⟩

end Dlev

section Cyl

open Classical
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.SG.AllRowsOf Formalism.L2.SG.Pf.AllRowsES Formalism.L2.SG.Pf.AllRowsTr

variable {D : D7}

def Gt (k : Fin 2) (t : Tup D k) (kv : Σ k' : Fin 2, D.nd.PlG k') :
    MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :=
  if kv.1 = k then D.ntypes.eSer kv.1 (Function.update (0 : Tup2 D) k t kv.1 kv.2) else 1

theorem sumW_single (k : Fin 2) (f : Polynomial (ZMod (D.host.g k))) (g : GL (Fin D.R.r) (ZMod (D.host.g k))) :
    ∑ c : Fin D.R.r → ZMod (D.host.g k),
      (if Formalism.CyclotomicNorms.monicOf c = f then (D.ntypes.eSer k (Formalism.CyclotomicNorms.monicOf c)).coeff g else 0) =
      (D.ntypes.eSer k f).coeff g := by
  classical
  by_cases hf : f.Monic ∧ f.natDegree = D.R.r
  · have hc0 := Formalism.L2.SG.Pf.RowDictPf.monicOf_coeff hf.1 hf.2
    rw [Finset.sum_eq_single (fun i : Fin D.R.r => f.coeff i)]
    · rw [if_pos hc0, hc0]
    · intro c _ hc
      rw [if_neg]
      intro h
      apply hc
      exact monicOf_inj (h.trans hc0.symm)
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [Finset.sum_eq_zero fun c _ => if_neg fun (h : Formalism.CyclotomicNorms.monicOf c = f) =>
      hf (h ▸ Formalism.L2.SG.Pf.RowDictPf.monicOf_monic c)]
    rw [D.ntypes.eSer_zero k f (fun h => hf ⟨h.1, h.2.1⟩)]
    rfl

theorem sumW_all (k : Fin 2) (g : GL (Fin D.R.r) (ZMod (D.host.g k))) :
    ∑ c : Fin D.R.r → ZMod (D.host.g k), (D.ntypes.eSer k (Formalism.CyclotomicNorms.monicOf c)).coeff g =
      (1 : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k)))).coeff g := by
  rw [← Formalism.L2.SG.AllRowsOf.sum_eSer' k, MonoidAlgebra.coeff_sum, Finsupp.finset_sum_apply]

open Classical in

theorem ES_cyl_pA (k : Fin 2) (S : Finset (Tup D k)) : ES (cyl D k (S : Set (Tup D k))) = ∑ t ∈ S, pA (Gt k t) := by
  apply MonoidAlgebra.ext; ext γ
  rw [ES_eq, MonoidAlgebra.coeff_sum, Finset.sum_apply', MonoidAlgebra.coeff_sum, Finset.sum_apply']
  simp only [Ea_coeff, pA_coeff]
  rw [Finset.sum_filter]
  have h1 : ∀ a : CV D, (if tupOf a ∈ cyl D k (S : Set (Tup D k)) then
      ∏ kv : (Σ k : Fin 2, D.nd.PlG k), (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (a kv))).coeff (γ kv) else 0) =
      ∑ t ∈ S, (if tupOf a k = t then
        ∏ kv : (Σ k : Fin 2, D.nd.PlG k), (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (a kv))).coeff (γ kv) else 0) := by
    intro a
    rw [Finset.sum_ite_eq]
    exact if_congr Iff.rfl rfl rfl
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  set G : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), (Fin D.R.r → ZMod (D.host.g kv.1)) → ℂ := fun kv c =>
    if kv.1 = k then (if Formalism.CyclotomicNorms.monicOf c = Function.update (0 : Tup2 D) k t kv.1 kv.2 then
      (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf c)).coeff (γ kv) else 0)
    else (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf c)).coeff (γ kv) with hG
  have h2 : ∀ a : CV D, (if tupOf a k = t then ∏ kv : (Σ k : Fin 2, D.nd.PlG k),
      (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (a kv))).coeff (γ kv) else 0) = ∏ kv, G kv (a kv) := by
    intro a
    have hG' : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), G kv (a kv) =
        if (kv.1 = k → Formalism.CyclotomicNorms.monicOf (a kv) = Function.update (0 : Tup2 D) k t kv.1 kv.2) then
          (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (a kv))).coeff (γ kv) else 0 := by
      intro kv
      by_cases hk : kv.1 = k
      · simp only [hG, hk, if_true, true_implies]
      · simp only [hG, hk, if_false, false_implies, if_true]
    rw [Finset.prod_congr rfl fun kv _ => hG' kv, Finset.prod_ite_zero]
    congr 1
    apply propext
    constructor
    · intro h kv _ hk
      obtain ⟨k', v⟩ := kv
      simp only at hk
      subst hk
      rw [Function.update_self, ← h]
      rfl
    · intro h
      funext v
      have := h ⟨k, v⟩ (Finset.mem_univ _) rfl
      rw [Function.update_self] at this
      exact this
  simp_rw [h2]
  rw [← Fintype.prod_sum]
  refine Finset.prod_congr rfl fun kv _ => ?_
  unfold Gt
  by_cases hk : kv.1 = k
  · simp only [hG, hk, if_true]
    exact sumW_single kv.1 _ _
  · simp only [hG, hk, if_false]
    exact sumW_all kv.1 _

end Cyl

section Char

open Classical
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.SG.AllRowsOf Formalism.L2.SG.Pf.AllRowsTr Formalism.L2.SG.Pf.AllRowsWt
  Formalism.L2.SG.Pf.AllRowsEtOne Formalism.L2.SG.Pf.AllRowsKpp Formalism.L2.SG.Pf.AllRowsGA

variable {D : D7} (P : G0g D.nd) (ψ : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), AddChar (ZMod (D.host.g kv.1)) ℂ)

def Fv (kv : Σ k : Fin 2, D.nd.PlG k) : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :=
  MonoidAlgebra.single (P kv) 1 * eJv kv (ψ kv) * MonoidAlgebra.single (P kv)⁻¹ 1

theorem Fv_idem (kv : Σ k : Fin 2, D.nd.PlG k) : Fv P ψ kv * Fv P ψ kv = Fv P ψ kv := by
  have h1 : MonoidAlgebra.single (P kv)⁻¹ (1 : ℂ) * MonoidAlgebra.single (P kv) 1 = 1 := by
    rw [MonoidAlgebra.single_mul_single, inv_mul_cancel, mul_one, MonoidAlgebra.one_def]
  unfold Fv
  have e : ∀ a b c : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g kv.1))),
      a * b * c * (a * b * c) = a * (b * (c * a) * b) * c := fun a b c => by simp only [mul_assoc]
  rw [e, h1, mul_one, eJ_idem]

theorem Fv_coeff (kv : Σ k : Fin 2, D.nd.PlG k) (g : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :
    (Fv P ψ kv).coeff g = if PJ D.R.k (D.R.m / 2 - 1) (((P kv)⁻¹ * g * P kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :
        Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) then
      (ψ kv (phiJ D.R.k (D.R.m / 2 - 1) (((P kv)⁻¹ * g * P kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :
        Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))))⁻¹ / (cJ D (D.host.g kv.1) : ℂ) else 0 := by
  haveI : Fact (D.host.g kv.1).Prime := ⟨D.host.g_prime kv.1⟩
  unfold Fv
  rw [MonoidAlgebra.coeff_mul_single_apply, MonoidAlgebra.coeff_single_mul_apply, one_mul, mul_one, inv_inv,
    ← mul_assoc, eJ_coeff, card_PJ]

variable (p : (Σ k : Fin 2, D.nd.PlG k) → Prop)

def Ep : MonoidAlgebra ℂ (G0g D.nd) := pA (fun kv => if p kv then Fv P ψ kv else 1)

theorem one_coeff_ne {G : Type} [Group G] {g : G} (h : (1 : MonoidAlgebra ℂ G).coeff g ≠ 0) : g = 1 := by
  exact Finset.mem_one.1 (MonoidAlgebra.support_coeff_one_subset (Finsupp.mem_support_iff.2 h))

theorem Ep_supp (γ : G0g D.nd) (h : (Ep P ψ p).coeff γ ≠ 0) : γ ∈ Sub p := by
  intro i hi
  rw [Ep, pA_coeff] at h
  have hi' := Finset.prod_ne_zero_iff.1 h i (Finset.mem_univ _)
  rw [if_neg hi] at hi'
  exact one_coeff_ne hi'

theorem Ep_idem : Ep P ψ p * Ep P ψ p = Ep P ψ p := by
  rw [Ep, pA_mul]
  congr 1
  funext kv
  split_ifs
  · exact Fv_idem P ψ kv
  · exact one_mul 1

end Char

section CharIdem

open Classical
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.SG.AllRowsOf Formalism.L2.SG.Pf.AllRowsTr Formalism.L2.SG.Pf.AllRowsWt
  Formalism.L2.SG.Pf.AllRowsEtOne Formalism.L2.SG.Pf.AllRowsKpp Formalism.L2.SG.Pf.AllRowsGA

variable {D : D7} (P : G0g D.nd) (ψ : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), AddChar (ZMod (D.host.g kv.1)) ℂ)
  (p : (Σ k : Fin 2, D.nd.PlG k) → Prop)

abbrev cj (γ : G0g D.nd) (kv : Σ k : Fin 2, D.nd.PlG k) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)) :=
  (((P kv)⁻¹ * γ kv * P kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))

theorem cj_mul (a b : G0g D.nd) (kv : Σ k : Fin 2, D.nd.PlG k) : cj P (a * b) kv = cj P a kv * cj P b kv := by
  simp only [cj, Pi.mul_apply]
  rw [← Units.val_mul]
  congr 1
  group

theorem cj_one (kv : Σ k : Fin 2, D.nd.PlG k) : cj P 1 kv = 1 := by
  simp [cj]

def Uj : Subgroup (Sub p : Subgroup (G0g D.nd)) where
  carrier := {a | ∀ kv, p kv → PJ D.R.k (D.R.m / 2 - 1) (cj P (a : G0g D.nd) kv)}
  one_mem' := fun kv _ => by
    show PJ D.R.k (D.R.m / 2 - 1) (cj P 1 kv)
    rw [cj_one]; exact jPred_one _ _
  mul_mem' := fun {a b} ha hb kv hk => by
    show PJ D.R.k (D.R.m / 2 - 1) (cj P ((a : G0g D.nd) * (b : G0g D.nd)) kv)
    rw [cj_mul]; exact Formalism.L2.SG.AllRowsOf.J_mul (ha kv hk) (hb kv hk)
  inv_mem' := fun {a} ha kv hk => by
    show PJ D.R.k (D.R.m / 2 - 1) (cj P ((a : G0g D.nd)⁻¹) kv)
    have h := PJ_inv ((P kv)⁻¹ * (a : G0g D.nd) kv * P kv) (ha kv hk)
    unfold cj
    convert h using 2
    simp only [Pi.inv_apply]
    group

def chij (a : G0g D.nd) : ℂ := ∏ kv, if p kv then ψ kv (phiJ D.R.k (D.R.m / 2 - 1) (cj P a kv)) else 1

theorem chij_mul (a b : G0g D.nd) (ha : ∀ kv, p kv → PJ D.R.k (D.R.m / 2 - 1) (cj P a kv))
    (hb : ∀ kv, p kv → PJ D.R.k (D.R.m / 2 - 1) (cj P b kv)) :
    chij P ψ p (a * b) = chij P ψ p a * chij P ψ p b := by
  unfold chij
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun kv _ => ?_
  split_ifs with h
  · rw [cj_mul, Formalism.L2.SG.AllRowsOf.phiJ_mul (ha kv h).1 (hb kv h).1 (hb kv h).2, AddChar.map_add_eq_mul]
  · rw [mul_one]

theorem chij_norm (a : G0g D.nd) : ‖chij P ψ p a‖ = 1 := by
  unfold chij
  rw [norm_prod]
  refine Finset.prod_eq_one fun kv _ => ?_
  split_ifs
  · exact AddChar.norm_apply _ _
  · exact norm_one

def cjc : ℂ := ∏ kv : (Σ k : Fin 2, D.nd.PlG k), if p kv then ((cJ D (D.host.g kv.1) : ℂ))⁻¹ else 1

theorem cjc_ne : cjc (D := D) p ≠ 0 := by
  unfold cjc
  refine Finset.prod_ne_zero_iff.2 fun kv _ => ?_
  split_ifs
  · exact inv_ne_zero (Nat.cast_ne_zero.2 (cJ_pos D kv.1).ne')
  · exact one_ne_zero

theorem res_Ep_coeff (a : Sub p) :
    (res (Sub p) (Ep P ψ p)).coeff a = if a ∈ Uj P p then (chij P ψ p a)⁻¹ * cjc p else 0 := by
  rw [res_coeff, Ep, pA_coeff]
  split_ifs with hU
  · have hU' : ∀ kv, p kv → PJ D.R.k (D.R.m / 2 - 1) (cj P (a : G0g D.nd) kv) := hU
    rw [chij, cjc, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun kv _ => ?_
    by_cases hp : p kv
    · rw [if_pos hp, if_pos hp, if_pos hp, Fv_coeff, if_pos (hU' kv hp), div_eq_mul_inv]
    · rw [if_neg hp, if_neg hp, if_neg hp, a.2 kv hp, MonoidAlgebra.coeff_one_one, inv_one, one_mul]
  · have hU' : ¬ ∀ kv, p kv → PJ D.R.k (D.R.m / 2 - 1) (cj P (a : G0g D.nd) kv) := hU
    push_neg at hU'
    obtain ⟨kv, hp, hJ⟩ := hU'
    refine Finset.prod_eq_zero (Finset.mem_univ kv) ?_
    rw [if_pos hp, Fv_coeff, if_neg hJ]

end CharIdem

section CharIdem2

open Classical
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.SG.AllRowsOf Formalism.L2.SG.Pf.AllRowsTr Formalism.L2.SG.Pf.AllRowsWt
  Formalism.L2.SG.Pf.AllRowsEtOne Formalism.L2.SG.Pf.AllRowsKpp Formalism.L2.SG.Pf.AllRowsGA

variable {D : D7} (P : G0g D.nd) (ψ : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), AddChar (ZMod (D.host.g kv.1)) ℂ)
  (p : (Σ k : Fin 2, D.nd.PlG k) → Prop)

theorem chij_one : chij P ψ p 1 = 1 := by
  unfold chij
  refine Finset.prod_eq_one fun kv _ => ?_
  split_ifs
  · rw [cj_one, Formalism.L2.SG.Pf.AllRowsEtOne.phiJ_one', AddChar.map_zero_eq_one]
  · rfl

theorem res_Ep_idem : res (Sub p) (Ep P ψ p) * res (Sub p) (Ep P ψ p) = res (Sub p) (Ep P ψ p) := by
  ext h
  rw [← res_mul _ _ (Ep_supp P ψ p) h, Ep_idem, res_coeff]

theorem charIdem_Ep : Formalism.MainNotions.S.IsCharIdemFin (res (Sub p) (Ep P ψ p)) := by
  have hcoef := res_Ep_coeff P ψ p
  have hc0 := cjc_ne (D := D) p

  have hχinv : ∀ x ∈ Uj P p, (chij P ψ p ((x : Sub p) : G0g D.nd))⁻¹ *
      (chij P ψ p (((x⁻¹ : Sub p)) : G0g D.nd))⁻¹ = 1 := by
    intro x hx
    rw [← mul_inv, ← chij_mul P ψ p _ _ hx ((Uj P p).inv_mem hx), Subgroup.coe_inv, mul_inv_cancel, chij_one,
      inv_one]
  have hterm : ∀ x : Sub p, (res (Sub p) (Ep P ψ p)).coeff x * (res (Sub p) (Ep P ψ p)).coeff (x⁻¹ * 1) =
      if x ∈ Uj P p then cjc p * cjc p else 0 := by
    intro x
    rw [mul_one, hcoef, hcoef]
    by_cases hx : x ∈ Uj P p
    · rw [if_pos hx, if_pos ((Uj P p).inv_mem hx), if_pos hx]
      calc (chij P ψ p ((x : Sub p) : G0g D.nd))⁻¹ * cjc p * ((chij P ψ p ((x⁻¹ : Sub p) : G0g D.nd))⁻¹ * cjc p)
          = ((chij P ψ p ((x : Sub p) : G0g D.nd))⁻¹ * (chij P ψ p ((x⁻¹ : Sub p) : G0g D.nd))⁻¹) *
            (cjc p * cjc p) := by ring
        _ = cjc p * cjc p := by rw [hχinv x hx, one_mul]
    · rw [if_neg hx, if_neg hx, zero_mul]

  have hsum : (res (Sub p) (Ep P ψ p) * res (Sub p) (Ep P ψ p)).coeff 1 =
      cjc p * cjc p * (Nat.card (Uj P p) : ℂ) := by
    rw [MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_fintype _ _ (fun _ => zero_mul _),
      Finset.sum_congr rfl (fun x _ => hterm x), Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
      nsmul_eq_mul, mul_comm, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h1 : (res (Sub p) (Ep P ψ p)).coeff 1 = cjc p := by
    rw [hcoef, if_pos (Uj P p).one_mem, Subgroup.coe_one, chij_one, inv_one, one_mul]
  have hc : cjc p * (Nat.card (Uj P p) : ℂ) = 1 := by
    have h := congrArg (fun f => MonoidAlgebra.coeff f 1) (res_Ep_idem P ψ p)
    rw [hsum, h1] at h
    exact mul_left_cancel₀ hc0 (by rw [mul_one, ← mul_assoc, h])
  refine ⟨Uj P p, fun a => chij P ψ p a, fun a ha b hb => ?_, fun a _ => chij_norm P ψ p a, fun a => ?_⟩
  · show chij P ψ p ((a * b : Sub p) : G0g D.nd) = _
    rw [Subgroup.coe_mul]
    exact chij_mul P ψ p a b ha hb
  · rw [hcoef]
    split_ifs
    · rw [div_eq_mul_inv, eq_inv_of_mul_eq_one_left hc]
    · rfl

end CharIdem2

section Gen2

variable {ι : Type} [Fintype ι] [DecidableEq ι] {G : ι → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]
  [∀ i, DecidableEq (G i)]

theorem mul_coeff_compl' {p q : ι → Prop} [DecidablePred p] [DecidablePred q] (hpq : ∀ i, q i ↔ ¬ p i)
    (A B : MonoidAlgebra ℂ (∀ i, G i)) (hA : ∀ γ, A.coeff γ ≠ 0 → γ ∈ Sub p)
    (hB : ∀ γ, B.coeff γ ≠ 0 → γ ∈ Sub q) (γ : ∀ i, G i) :
    (A * B).coeff γ = A.coeff (proj p γ) * B.coeff (proj q γ) := by
  have hpq' : proj p γ * proj q γ = γ := by
    funext i
    rw [Pi.mul_apply, proj_apply, proj_apply]
    by_cases h : p i
    · rw [if_pos h, if_neg (fun hq => (hpq i).1 hq h), mul_one]
    · rw [if_neg h, if_pos ((hpq i).2 h), one_mul]
  have e : (proj p γ)⁻¹ * γ = proj q γ := by
    rw [inv_mul_eq_iff_eq_mul, hpq']
  rw [MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_eq_single (proj p γ), e]
  · intro h hh hne
    have hBz : B.coeff (h⁻¹ * γ) = 0 := by
      by_contra hne'
      apply hne
      calc h = proj p h * proj p (h⁻¹ * γ) := by
            rw [proj_of_mem p (hA h hh), proj_eq_one_of p (hB _ hne') (fun i hi hq => (hpq i).1 hq hi), mul_one]
        _ = proj p γ := by rw [← map_mul, mul_inv_cancel_left]
    show A.coeff h * B.coeff (h⁻¹ * γ) = 0
    rw [hBz, mul_zero]
  · intro _
    exact zero_mul _

theorem mul_supp {H : Subgroup (∀ i, G i)} (A B : MonoidAlgebra ℂ (∀ i, G i)) (hA : ∀ γ, A.coeff γ ≠ 0 → γ ∈ H)
    (hB : ∀ γ, B.coeff γ ≠ 0 → γ ∈ H) (γ : ∀ i, G i) (h : (A * B).coeff γ ≠ 0) : γ ∈ H := by
  rw [MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum] at h
  obtain ⟨x, hx, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have h1 := hA x (Finsupp.mem_support_iff.1 hx)
  have h2 := hB _ (right_ne_zero_of_mul hne)
  simpa using H.mul_mem h1 h2

theorem sum_supp {κ : Type} (T : Finset κ) {H : Subgroup (∀ i, G i)} (A : κ → MonoidAlgebra ℂ (∀ i, G i))
    (hA : ∀ t, ∀ γ, (A t).coeff γ ≠ 0 → γ ∈ H) (γ : ∀ i, G i) (h : (∑ t ∈ T, A t).coeff γ ≠ 0) : γ ∈ H := by
  rw [MonoidAlgebra.coeff_sum, Finsupp.finset_sum_apply] at h
  obtain ⟨t, -, ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact hA t γ ht

end Gen2

section Assemble

open Classical
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.SG.HidaSetting Formalism.L2.SG.AllRowsOf Formalism.L2.SG.Pf.AllRowsTr
  Formalism.L2.SG.Pf.AllRowsEtOne Formalism.L2.SG.Pf.AllRowsKpp Formalism.L2.SG.Pf.AllRowsGA Formalism.L2.SG.Pf.AllRowsES
  Formalism.L2.SG.Pf.AllRowsRhoX Formalism.L2.SG.Pf.AllRowsFin Formalism.L2.SG.Pf.AllRowsEtAlg

variable {D : D7}

def TS (k : Fin 2) (S : Set (Tup D k)) : Finset (Tup D k) :=
  (Finset.univ.filter (fun a : CV D => tupOf a k ∈ S)).image (fun a => tupOf a k)

theorem ES_TS (k : Fin 2) (S : Set (Tup D k)) : ES (cyl D k S) = ES (cyl D k (TS k S : Set (Tup D k))) := by
  have key : ∀ a, tupOf a ∈ cyl D k S ↔ tupOf a ∈ cyl D k (TS k S : Set (Tup D k)) := by
    intro a
    simp only [cyl, Set.mem_setOf_eq, TS, Finset.coe_image, Finset.coe_filter, Finset.mem_univ, true_and,
      Set.mem_image, Set.mem_setOf_eq]
    exact ⟨fun h => ⟨a, h, rfl⟩, fun ⟨b, hb, e⟩ => e ▸ hb⟩
  simp only [ES, key]

theorem Gt_supp (k : Fin 2) (t : Tup D k) (γ : G0g D.nd) (h : (pA (Gt k t)).coeff γ ≠ 0) :
    γ ∈ Sub (fun kv : (Σ k' : Fin 2, D.nd.PlG k') => kv.1 = k) := by
  intro i hi
  rw [pA_coeff] at h
  have hi' := Finset.prod_ne_zero_iff.1 h i (Finset.mem_univ _)
  rw [Gt, if_neg hi] at hi'
  exact one_coeff_ne hi'

theorem ES_supp (k : Fin 2) (S : Set (Tup D k)) (γ : G0g D.nd) (h : (ES (cyl D k S)).coeff γ ≠ 0) :
    γ ∈ Sub (fun kv : (Σ k' : Fin 2, D.nd.PlG k') => kv.1 = k) := by
  rw [ES_TS, ES_cyl_pA] at h
  exact sum_supp _ _ (fun t => Gt_supp k t) γ h

end Assemble

section Main

open Classical
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.SG.HidaSetting Formalism.L2.SG.AllRowsOf Formalism.L2.SG.Pf.AllRowsTr Formalism.L2.SG.Pf.AllRowsWt
  Formalism.L2.SG.Pf.AllRowsEtOne Formalism.L2.SG.Pf.AllRowsKpp Formalism.L2.SG.Pf.AllRowsGA Formalism.L2.SG.Pf.AllRowsES
  Formalism.L2.SG.Pf.AllRowsRhoX Formalism.L2.SG.Pf.AllRowsFin Formalism.L2.SG.Pf.AllRowsEtAlg

variable {D : D7} (X : HidaSetting D)

theorem Kg_dvd {d m : ℕ} (h : d ∣ m) {x : X.B.I.Gf} (hx : x ∈ X.B.I.Kg m) : x ∈ X.B.I.Kg d := by
  obtain ⟨c, rfl⟩ := h
  refine ⟨hx.1, fun y hy => ?_⟩
  obtain ⟨z, hz, e⟩ := hx.2 y hy
  refine ⟨c • z, nsmul_mem hz c, ?_⟩
  rw [e, Nat.cast_mul, mul_smul]
  simp only [Nat.cast_smul_eq_nsmul]

theorem Kg_eq (k : Fin 2) :
    X.B.I.Kg X.B.g = X.B.I.Kg (D.host.g (1 - k) ^ 1) ∩ X.B.I.Kg (D.host.g k ^ 1) := by
  rw [pow_one, pow_one]
  have hg : X.B.g = D.host.g (1 - k) * D.host.g k := by
    rw [X.g_eq]; fin_cases k
    · exact mul_comm _ _
    · rfl
  ext x
  constructor
  · intro hx
    rw [hg] at hx
    exact ⟨Kg_dvd X (dvd_mul_right _ _) hx, Kg_dvd X (dvd_mul_left _ _) hx⟩
  · rintro ⟨h1, h2⟩
    rw [hg]
    refine Formalism.L2.SG.AllRowsOf.Kg_inter X.B.I ?_ h1 h2
    refine (Nat.coprime_primes (D.host.g_prime _) (D.host.g_prime _)).2 ?_
    fin_cases k
    · exact D.host.g_ne.symm
    · exact D.host.g_ne

theorem isCountIdem_cyl (k : Fin 2) (S : Set (Tup D k)) :
    X.B.I.IsCountIdem X.B.μf (D.host.g (1 - k)) (eT X (cyl D k S)) := by
  have hS := Formalism.L2.SG.Pf.AllRowsAdd.hS_X X
  obtain ⟨P, ψ, -, hK⟩ := Formalism.L2.SG.Pf.AllRowsClosed.kppShape_holds X
  have hmem := fun x => (hK x).1
  have hchi := fun x => (hK x).2
  let pj : (Σ k' : Fin 2, D.nd.PlG k') → Prop := fun kv => ¬ kv.1 = k
  let pk : (Σ k' : Fin 2, D.nd.PlG k') → Prop := fun kv => kv.1 = k
  have hsplit : Ehat hS = Ep P ψ pj * Ep P ψ pk := by
    rw [Ehat_eq hS P ψ hmem hchi]
    unfold Ep
    rw [pA_mul]
    congr 1
    funext kv
    by_cases hk : kv.1 = k
    · simp only [pj, pk, hk, not_true_eq_false, if_false, if_true, one_mul]; rfl
    · simp only [pj, pk, hk, not_false_eq_true, if_true, if_false, mul_one]; rfl
  have hz2 : res (Sub pk) (ES (cyl D k S)) * res (Sub pk) (ES (cyl D k S)) = res (Sub pk) (ES (cyl D k S)) := by
    apply MonoidAlgebra.ext; ext a
    rw [← res_mul _ _ (ES_supp k S) a, ES_idem, res_coeff]
  have hzc : ∀ y, res (Sub pk) (ES (cyl D k S)) * y = y * res (Sub pk) (ES (cyl D k S)) :=
    central_of_class _ fun g h => by
      rw [res_coeff, res_coeff]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact ES_conj _ _ _
  refine ⟨1, 1, D.host.g k, redD X k, res (Sub pj) (Ep P ψ pj), res (Sub pk) (ES (cyl D k S)),
    res (Sub pk) (Ep P ψ pk), D.host.g_prime k, ?_, charIdem_Ep P ψ pj, ?_, charIdem_Ep P ψ pk, hz2, hzc, ?_⟩
  · fin_cases k
    · exact D.host.g_ne
    · exact D.host.g_ne.symm
  · intro x hx hf
    have hred : (redD X k).red x = (⟨proj pj (rhoX X ⟨x, hx⟩), proj_mem _ _⟩, ⟨proj pk (rhoX X ⟨x, hx⟩), proj_mem _ _⟩) := by
      show (if hx : x ∈ X.B.I.Kset then _ else 1) = _
      exact dif_pos hx
    have hf' : (res (Sub pj) (Ep P ψ pj)).coeff (⟨proj pj (rhoX X ⟨x, hx⟩), proj_mem _ _⟩ : Sub pj) ≠ 0 := by
      rw [hred] at hf; exact hf
    rw [res_Ep_coeff] at hf'
    split_ifs at hf' with hU
    · set γ := proj pj (rhoX X ⟨x, hx⟩) with hγ
      have hJ : ∀ kv, JPred D.R.k (D.R.m / 2 - 1) (cjM P γ kv) := by
        intro kv
        by_cases hk : kv.1 = k
        · have h1 : γ kv = 1 := proj_mem pj _ kv (by simp [pj, hk])
          show PJ D.R.k (D.R.m / 2 - 1) (cj P γ kv)
          have h2 : cj P γ kv = 1 := by unfold cj; rw [h1]; simp
          rw [h2]; exact jPred_one _ _
        · exact hU kv hk
      have hy : ((sec hS γ : KSub X.B.I) : X.B.I.Gf) ∈ X.K2 := (hmem (sec hS γ)).2 (by rw [rho_sec]; exact hJ)
      have hdiv : D.host.g (1 - k) ∣ X.B.g := by
        rw [X.g_eq]; fin_cases k
        · exact dvd_mul_left _ _
        · exact dvd_mul_right _ _
      have hyU := levelSubgroup_unipotent_mod X hdiv hy
      have hz := (part_iff_j X k (sec hS γ) ⟨x, hx⟩).1 (by rw [rho_sec, hγ, proj_of_mem _ (proj_mem _ _)])
      have := unipMod_mul_Kg X hy.1 hyU hz
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left] using this
    · exact absurd rfl hf'
  · intro x
    by_cases hx : x ∈ X.B.I.Kset
    · rw [if_pos hx]
      have hred : (redD X k).red x = (⟨proj pj (rhoX X ⟨x, hx⟩), proj_mem _ _⟩, ⟨proj pk (rhoX X ⟨x, hx⟩), proj_mem _ _⟩) := by
        show (if hx : x ∈ X.B.I.Kset then _ else 1) = _
        exact dif_pos hx
      rw [hred]
      have h1 := val_hat hS (biInv_eT X (cyl D k S)) ⟨x, hx⟩
      have hV : V X = (X.B.μf (X.B.I.Kg (D.host.g (1 - k) ^ 1) ∩ X.B.I.Kg (D.host.g k ^ 1))).toReal := by
        unfold V; rw [Kg_eq X k]
      rw [show eT X (cyl D k S) x = eT X (cyl D k S) ((⟨x, hx⟩ : KSub X.B.I) : X.B.I.Gf) from rfl, h1, hat_eT' hS,
        hsplit, mul_assoc, ← hV]
      rw [mul_coeff_compl' (p := pj) (q := pk) (fun kv => by simp [pj, pk]) _ _ (Ep_supp P ψ pj)
        (mul_supp _ _ (Ep_supp P ψ pk) (ES_supp k S))]
      have a1 : ∀ h : Sub pj, (res (Sub pj) (Ep P ψ pj)).coeff h = (Ep P ψ pj).coeff (h : G0g D.nd) :=
        fun h => res_coeff _ _ _
      have a2 : ∀ h : Sub pk, (res (Sub pk) (ES (cyl D k S)) * res (Sub pk) (Ep P ψ pk)).coeff h =
          (Ep P ψ pk * ES (cyl D k S)).coeff (h : G0g D.nd) := fun h => by
        rw [hzc (res (Sub pk) (Ep P ψ pk)), ← res_mul (Ep P ψ pk) (ES (cyl D k S)) (Ep_supp P ψ pk)]
      show _ = (res (Sub pj) (Ep P ψ pj)).coeff (⟨proj pj (rhoX X ⟨x, hx⟩), proj_mem _ _⟩ : Sub pj) *
        (res (Sub pk) (ES (cyl D k S)) * res (Sub pk) (Ep P ψ pk)).coeff
          (⟨proj pk (rhoX X ⟨x, hx⟩), proj_mem _ _⟩ : Sub pk) / (V X : ℂ)
      simp only [a1, a2]
    · rw [if_neg hx]; exact eT_of_not_mem X _ hx

end Main

section Comparison₂

variable {D : Formalism.BasicNotions.D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem pCountTie_holds (ψ₀ : ∀ k : Fin 2, AddChar (ZMod (D.host.g k)) ℂ) (hψ₀ : ∀ k, ψ₀ k ≠ 1)
    (hL : Formalism.L2.SG.AllRowsOf.RowsLab X) :
    Formalism.MainNotions.N.CylinderCountFamily.PCountTie D (Formalism.L2.SG.Pf.AllRowsClosed.allRowsOfL X ψ₀ hψ₀ hL).toAt :=
  fun k S => Or.inr (Formalism.L2.SG.Pf.AllRowsPCount.isCountIdem_cyl X k S)

end Comparison₂

end Formalism.L2.SG.Pf.AllRowsPCount
