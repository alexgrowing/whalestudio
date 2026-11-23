import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyLinearEquivOfPiFinPowFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisDescentSemilinearBijectiveStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

noncomputable section
namespace GlobalTheory.HilbertNinety

variable {F F' : Type} [Field F] [Field F'] [Algebra F F']

theorem mapS_mul (s : F' ≃ₐ[F] F') {n : ℕ} (x y : Matrix (Fin n) (Fin n) F') :
    (x * y).map s = x.map s * y.map s :=
  Matrix.map_mul (f := (s : F' →+* F'))

theorem mapS_add (s : F' ≃ₐ[F] F') {n : ℕ} (x y : Matrix (Fin n) (Fin n) F') :
    (x + y).map s = x.map s + y.map s :=
  Matrix.map_add _ (map_add s) x y

theorem mapS_smul (s : F' ≃ₐ[F] F') {n : ℕ} (c : F') (x : Matrix (Fin n) (Fin n) F') :
    (c • x).map s = s c • x.map s := by
  ext i j; simp

theorem mapS_pow_succ (s : F' ≃ₐ[F] F') {n : ℕ} (j : ℕ) (x : Matrix (Fin n) (Fin n) F') :
    x.map ⇑(s ^ (j + 1)) = (x.map s).map ⇑(s ^ j) := by
  ext i k; simp [pow_succ, AlgEquiv.mul_apply]

theorem coe_galAct (s : F' ≃ₐ[F] F') {n : ℕ} (x : GL (Fin n) F') :
    ((galAct F F' n s x : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') = (x : Matrix (Fin n) (Fin n) F').map s := by
  rfl

theorem nrmG_succ (s : F' ≃ₐ[F] F') {n : ℕ} (j : ℕ) (δ : GL (Fin n) F') :
    nrmG (galAct F F' n) s (j + 1) δ = nrmG (galAct F F' n) s j δ * galAct F F' n (s ^ j) δ := by
  unfold nrmG
  rw [List.range_succ, List.map_append, List.prod_append]
  simp

def tw (s : F' ≃ₐ[F] F') {n : ℕ} (B : Subalgebra F' (Matrix (Fin n) (Fin n) F'))
    (hB : ∀ x ∈ B, x.map s ∈ B) (δ : GL (Fin n) F')
    (hδ : ((δ⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') ∈ B) : Module.End F B where
  toFun v := ⟨(v : Matrix (Fin n) (Fin n) F').map s * ((δ⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F'),
    B.mul_mem (hB _ v.2) hδ⟩
  map_add' v w := by
    apply Subtype.ext
    simp [mapS_add, add_mul]
  map_smul' c v := by
    apply Subtype.ext
    have : ((c • v : B) : Matrix (Fin n) (Fin n) F') = algebraMap F F' c • (v : Matrix (Fin n) (Fin n) F') := by
      rw [algebraMap_smul]; rfl
    simp only [RingHom.id_apply]
    rw [this, mapS_smul, AlgEquiv.commutes, smul_mul_assoc, algebraMap_smul]
    rfl

theorem tw_apply (s : F' ≃ₐ[F] F') {n : ℕ} (B : Subalgebra F' (Matrix (Fin n) (Fin n) F'))
    (hB : ∀ x ∈ B, x.map s ∈ B) (δ : GL (Fin n) F')
    (hδ : ((δ⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') ∈ B) (v : B) :
    ((tw s B hB δ hδ v : B) : Matrix (Fin n) (Fin n) F') =
      (v : Matrix (Fin n) (Fin n) F').map s * ((δ⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') := rfl

theorem tw_semilin (s : F' ≃ₐ[F] F') {n : ℕ} (B : Subalgebra F' (Matrix (Fin n) (Fin n) F'))
    (hB : ∀ x ∈ B, x.map s ∈ B) (δ : GL (Fin n) F')
    (hδ : ((δ⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') ∈ B) (c : F') (v : B) :
    tw s B hB δ hδ (c • v) = s c • tw s B hB δ hδ v := by
  apply Subtype.ext
  simp only [tw_apply, SetLike.val_smul, mapS_smul, smul_mul_assoc]

theorem tw_pow (s : F' ≃ₐ[F] F') {n : ℕ} (B : Subalgebra F' (Matrix (Fin n) (Fin n) F'))
    (hB : ∀ x ∈ B, x.map s ∈ B) (δ : GL (Fin n) F')
    (hδ : ((δ⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') ∈ B) (j : ℕ) (v : B) :
    (((tw s B hB δ hδ ^ j) v : B) : Matrix (Fin n) (Fin n) F') =
      (v : Matrix (Fin n) (Fin n) F').map ⇑(s ^ j) *
        (((nrmG (galAct F F' n) s j δ)⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') := by
  induction j generalizing v with
  | zero =>
    ext i k
    simp [nrmG]
  | succ j ih =>
    rw [pow_succ, Module.End.mul_apply, ih, tw_apply, mapS_mul, ← mapS_pow_succ, nrmG_succ, mul_inv_rev,
      Units.val_mul, ← map_inv, coe_galAct, mul_assoc]

theorem nrmG_one (s : F' ≃ₐ[F] F') {n : ℕ} (j : ℕ) :
    nrmG (galAct F F' n) s j (1 : GL (Fin n) F') = 1 := by
  unfold nrmG
  apply List.prod_eq_one
  intro x hx
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  exact map_one _

theorem pow_finrank_eq_one [Finite F'] (s : F' ≃ₐ[F] F') : s ^ Module.finrank F F' = 1 := by
  rw [← IsGalois.card_aut_eq_finrank]
  exact pow_card_eq_one'

theorem tw_pow_finrank [Finite F'] (s : F' ≃ₐ[F] F') {n : ℕ} (B : Subalgebra F' (Matrix (Fin n) (Fin n) F'))
    (hB : ∀ x ∈ B, x.map s ∈ B) (δ : GL (Fin n) F')
    (hδ : ((δ⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') ∈ B)
    (h1 : nrmG (galAct F F' n) s (Module.finrank F F') δ = 1) :
    tw s B hB δ hδ ^ Module.finrank F F' = 1 := by
  refine LinearMap.ext fun v => Subtype.ext ?_
  rw [tw_pow, pow_finrank_eq_one, h1]
  ext i k
  simp

def fix (s : F' ≃ₐ[F] F') {n : ℕ} (B : Subalgebra F' (Matrix (Fin n) (Fin n) F')) :
    Subring (Matrix (Fin n) (Fin n) F') where
  carrier := {x | x ∈ B ∧ x.map s = x}
  mul_mem' ha hb := ⟨B.mul_mem ha.1 hb.1, by rw [mapS_mul, ha.2, hb.2]⟩
  one_mem' := ⟨B.one_mem, Matrix.map_one _ (map_zero s) (map_one s)⟩
  add_mem' ha hb := ⟨B.add_mem ha.1 hb.1, by rw [mapS_add, ha.2, hb.2]⟩
  zero_mem' := ⟨B.zero_mem, by ext; simp⟩
  neg_mem' {x} h := ⟨B.neg_mem h.1, by
    rw [show (-x).map s = -(x.map s) by ext; simp, h.2]⟩

def keyP (s : F' ≃ₐ[F] F') {n : ℕ} (B : Subalgebra F' (Matrix (Fin n) (Fin n) F')) (δ : GL (Fin n) F') :
    Submodule (fix s B) (Matrix (Fin n) (Fin n) F') where
  carrier := {x | x ∈ B ∧ x.map s * ((δ⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') = x}
  zero_mem' := ⟨B.zero_mem, by ext; simp⟩
  add_mem' ha hb := ⟨B.add_mem ha.1 hb.1, by rw [mapS_add, add_mul, ha.2, hb.2]⟩
  smul_mem' r x hx := by
    refine ⟨?_, ?_⟩
    · rw [Subring.smul_def, smul_eq_mul]; exact B.mul_mem r.2.1 hx.1
    · rw [Subring.smul_def, smul_eq_mul, mapS_mul, r.2.2, mul_assoc, hx.2]

def sumMap (s : F' ≃ₐ[F] F') {n : ℕ} (B : Subalgebra F' (Matrix (Fin n) (Fin n) F'))
    (P : Submodule (fix s B) (Matrix (Fin n) (Fin n) F')) {ι : Type} [Fintype ι] (b : Module.Basis ι F F') :
    (ι → P) →ₗ[fix s B] Matrix (Fin n) (Fin n) F' where
  toFun v := ∑ i, b i • (v i : Matrix (Fin n) (Fin n) F')
  map_add' v w := by simp [smul_add, Finset.sum_add_distrib]
  map_smul' r v := by
    simp only [Pi.smul_apply, Submodule.coe_smul, Subring.smul_def, smul_eq_mul, RingHom.id_apply,
      Finset.mul_sum, Matrix.mul_smul]

theorem sumMap_mem (s : F' ≃ₐ[F] F') {n : ℕ} (B : Subalgebra F' (Matrix (Fin n) (Fin n) F')) (δ : GL (Fin n) F')
    {ι : Type} [Fintype ι] (b : Module.Basis ι F F') (v : ι → keyP s B δ) :
    sumMap s B (keyP s B δ) b v ∈ B :=
  B.sum_mem fun i _ => B.smul_mem (v i).2.1 _

theorem sumMap_transfer (s : F' ≃ₐ[F] F') {n : ℕ} (B : Subalgebra F' (Matrix (Fin n) (Fin n) F'))
    (hB : ∀ x ∈ B, x.map s ∈ B) (δ : GL (Fin n) F')
    (hδ : ((δ⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') ∈ B)
    {ι : Type} [Fintype ι] (b : Module.Basis ι F F')
    (hbij : Function.Bijective (fun v : ι → LinearMap.ker (tw s B hB δ hδ - 1) => ∑ i, b i • (v i : B))) :
    Function.Injective (sumMap s B (keyP s B δ) b) ∧
      ∀ y ∈ B, ∃ v, sumMap s B (keyP s B δ) b v = y := by
  have hker : ∀ w : B, w ∈ LinearMap.ker (tw s B hB δ hδ - 1) ↔
      (w : Matrix (Fin n) (Fin n) F').map s * ((δ⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') = w := by
    intro w
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, Module.End.one_apply, ← tw_apply s B hB δ hδ w]
    exact Subtype.ext_iff
  let toK : keyP s B δ → LinearMap.ker (tw s B hB δ hδ - 1) := fun p =>
    ⟨⟨p, p.2.1⟩, (hker _).2 p.2.2⟩
  have hcoe : ∀ v : ι → keyP s B δ,
      (((∑ i, b i • ((toK (v i) : LinearMap.ker (tw s B hB δ hδ - 1)) : B)) : B) : Matrix (Fin n) (Fin n) F') =
        sumMap s B (keyP s B δ) b v := by
    intro v
    simp [toK, sumMap]
  refine ⟨fun v w h => ?_, fun y hy => ?_⟩
  · have h2 : (fun i => toK (v i)) = (fun i => toK (w i)) := by
      apply hbij.1
      apply Subtype.ext
      simp only
      rw [hcoe v, hcoe w, h]
    funext i
    have := congrFun h2 i
    apply Subtype.ext
    have := congrArg (fun z : LinearMap.ker (tw s B hB δ hδ - 1) => ((z : B) : Matrix (Fin n) (Fin n) F')) this
    simpa [toK] using this
  · obtain ⟨u, hu⟩ := hbij.2 ⟨y, hy⟩
    refine ⟨fun i => ⟨((u i : B) : Matrix (Fin n) (Fin n) F'), (u i : B).2, (hker _).1 (u i).2⟩, ?_⟩
    have := congrArg (fun z : B => (z : Matrix (Fin n) (Fin n) F')) hu
    simpa [sumMap] using this

set_option synthInstance.maxHeartbeats 400000 in

theorem hilbert90_matrix_subalgebra_norm_one : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'),
    (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (n : ℕ) (B : Subalgebra F' (Matrix (Fin n) (Fin n) F')),
    (∀ x ∈ B, x.map s ∈ B) → ∀ ε : GL (Fin n) F', (ε : Matrix (Fin n) (Fin n) F') ∈ B → nrm s ε = 1 →
    ∃ x : GL (Fin n) F', (x : Matrix (Fin n) (Fin n) F') ∈ B ∧ ε = x⁻¹ * galAct F F' n s x := by
  intro F F' _ _ _ _ s hs n B hB ε hεB hnrm
  haveI hMf : Finite (Matrix (Fin n) (Fin n) F') := inferInstanceAs (Finite (Fin n → Fin n → F'))
  haveI : Finite (GL (Fin n) F') := Finite.of_injective (fun u : GL (Fin n) F' => (u : Matrix (Fin n) (Fin n) F'))
    (fun u v h => Units.ext h)
  have hinv : ((ε⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') ∈ B := by
    have hpos := (isOfFinOrder_of_finite ε).orderOf_pos
    have he : ε⁻¹ = ε ^ (orderOf ε - 1) := by
      refine (eq_inv_of_mul_eq_one_left ?_).symm
      rw [← pow_succ, Nat.sub_add_cancel hpos, pow_orderOf_eq_one]
    rw [he, Units.val_pow_eq_pow_val]
    exact pow_mem hεB _
  have h1 : (((1 : GL (Fin n) F')⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') ∈ B := by
    simpa using B.one_mem
  set l := Module.finrank F F'
  have hl : 0 < l := Module.finrank_pos
  let b := Module.finBasis F F'
  have hT := GlobalTheory.T.galoisDescent_sum_basis_smul_ker_bijective F F' s hs B (tw s B hB ε hinv) (tw_semilin s B hB ε hinv)
    (tw_pow_finrank s B hB ε hinv hnrm) (Fin l) b
  have hT0 := GlobalTheory.T.galoisDescent_sum_basis_smul_ker_bijective F F' s hs B (tw s B hB 1 h1) (tw_semilin s B hB 1 h1)
    (tw_pow_finrank s B hB 1 h1 (nrmG_one s _)) (Fin l) b
  obtain ⟨injM, surjM⟩ := sumMap_transfer s B hB ε hinv b hT
  obtain ⟨injN, surjN⟩ := sumMap_transfer s B hB 1 h1 b hT0
  have hrange : LinearMap.range (sumMap s B (keyP s B ε) b) = LinearMap.range (sumMap s B (keyP s B 1) b) := by
    ext y
    constructor
    · rintro ⟨v, rfl⟩
      obtain ⟨w, hw⟩ := surjN _ (sumMap_mem s B ε b v)
      exact ⟨w, hw⟩
    · rintro ⟨v, rfl⟩
      obtain ⟨w, hw⟩ := surjM _ (sumMap_mem s B 1 b v)
      exact ⟨w, hw⟩
  let e : (Fin l → keyP s B ε) ≃ₗ[fix s B] (Fin l → keyP s B 1) :=
    ((LinearEquiv.ofInjective _ injM).trans (LinearEquiv.ofEq _ _ hrange)).trans
      (LinearEquiv.ofInjective _ injN).symm
  obtain ⟨ψ⟩ := GlobalTheory.T.nonempty_linearEquiv_of_pi_fin_pow_finite (fix s B) (keyP s B ε) (keyP s B 1) l hl ⟨e⟩
  have h1N : (1 : Matrix (Fin n) (Fin n) F') ∈ keyP s B 1 :=
    ⟨B.one_mem, by simp [Matrix.map_one _ (map_zero s) (map_one s)]⟩
  set x : Matrix (Fin n) (Fin n) F' := ((ψ.symm ⟨1, h1N⟩ : keyP s B ε) : Matrix (Fin n) (Fin n) F') with hxdef
  have hxM : x ∈ keyP s B ε := (ψ.symm ⟨1, h1N⟩).2
  have hgen : ∀ m : keyP s B ε, ∃ r : fix s B, (m : Matrix (Fin n) (Fin n) F') = (r : Matrix (Fin n) (Fin n) F') * x := by
    intro m
    have hmem : ((ψ m : keyP s B 1) : Matrix (Fin n) (Fin n) F') ∈ fix s B := by
      refine ⟨(ψ m).2.1, ?_⟩
      have := (ψ m).2.2
      simpa using this
    let r0 : fix s B := ⟨_, hmem⟩
    refine ⟨r0, ?_⟩
    have hr : (ψ m : keyP s B 1) = r0 • (⟨1, h1N⟩ : keyP s B 1) := by
      apply Subtype.ext
      simp [Subring.smul_def, r0]
    have := congrArg (fun z => ((ψ.symm z : keyP s B ε) : Matrix (Fin n) (Fin n) F')) hr
    simp only [LinearEquiv.symm_apply_apply, map_smul, Submodule.coe_smul, Subring.smul_def, smul_eq_mul] at this
    exact this
  obtain ⟨v, hv⟩ := surjM 1 B.one_mem
  choose r hr using fun i => hgen (v i)
  set c : Matrix (Fin n) (Fin n) F' := ∑ i, b i • (r i : Matrix (Fin n) (Fin n) F')
  have hcx : c * x = 1 := by
    rw [← hv]
    simp only [c, sumMap, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_mul, smul_mul_assoc, hr]
  have hxc : x * c = 1 := mul_eq_one_comm.1 hcx
  let X : GL (Fin n) F' := ⟨x, c, hxc, hcx⟩
  have hX : (X : Matrix (Fin n) (Fin n) F') = x := rfl
  refine ⟨X, hX ▸ hxM.1, ?_⟩
  have hsX : galAct F F' n s X = X * ε := by
    apply Units.ext
    rw [coe_galAct, Units.val_mul, hX]
    calc x.map s = x.map s * ((ε⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') * (ε : Matrix (Fin n) (Fin n) F') := by
          rw [mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
      _ = x * ε := by rw [hxM.2]
  rw [hsX, inv_mul_cancel_left]

end GlobalTheory.HilbertNinety
