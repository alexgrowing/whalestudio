import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulPEqOfTranslInvariant
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

namespace PDivGroup

variable {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R)

open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv in
set_option autoImplicit false in
variable {p : ℕ} {R : Type} [CommRing R] (G : _root_.GlobalTheory.PDivGroup p R) in

theorem _root_.GlobalTheory.PDivGroup.transl_eq_of_cobOne_eq_pullTwo (n : ℕ) (x : G.A (n + 1))
    (t : G.A n ⊗[R] G.A n)
    (h : _root_.GlobalTheory.PDiv.cobOne R _ x = _root_.GlobalTheory.PDiv.pullbackTwo (G.mulP n) t)
    (h1 : G.resOne n x = 0) :
    G.transl n x = x ⊗ₜ 1 := by
  set f := G.mulP n
  set ρ := G.resOne n
  have hcomul : comul x = x ⊗ₜ[R] 1 + 1 ⊗ₜ[R] x +
      TensorProduct.map (f : G.A n →ₗ[R] G.A (n + 1))
        (f : G.A n →ₗ[R] G.A (n + 1)) t := by
    have := h
    unfold _root_.GlobalTheory.PDiv.cobOne _root_.GlobalTheory.PDiv.pullbackTwo at this
    simp only [LinearMap.sub_apply, LinearMap.flip_apply, TensorProduct.mk_apply] at this
    rw [← this]; abel
  have hε : counit x = (0 : R) := by
    have := CoalgHomClass.counit_comp_apply ρ x
    rw [h1, map_zero] at this
    exact this.symm
  have hρf : (ρ : G.A (n + 1) →ₗ[R] G.A 1) ∘ₗ
      (f : G.A n →ₗ[R] G.A (n + 1))
        = Algebra.linearMap R _ ∘ₗ counit := by
    ext a
    exact _root_.GlobalTheory.PDivGroup.resOne_mulP G n a
  have hεf : (counit : _ →ₗ[R] R) ∘ₗ
      (f : G.A n →ₗ[R] G.A (n + 1)) = counit := by
    ext a
    exact CoalgHomClass.counit_comp_apply f a
  have hzero : TensorProduct.map (f : G.A n →ₗ[R] G.A (n + 1))
      (counit : _ →ₗ[R] R) t = 0 := by
    have := congrArg (LinearMap.lTensor _ (counit : _ →ₗ[R] R)) hcomul
    rw [Coalgebra.lTensor_counit_comul, map_add, map_add, LinearMap.lTensor_tmul,
      LinearMap.lTensor_tmul, hε, counit_one, ← LinearMap.comp_apply, LinearMap.lTensor_comp_map,
      hεf, tmul_zero, add_zero] at this
    simpa using this
  rw [_root_.GlobalTheory.PDivGroup.transl_apply, hcomul, map_add, map_add, LinearMap.lTensor_tmul,
    LinearMap.lTensor_tmul, ← LinearMap.comp_apply, LinearMap.lTensor_comp_map, hρf,
    ← LinearMap.lTensor_comp_map, LinearMap.comp_apply, hzero, map_zero, add_zero]
  have h1' : G.resOne n x = 0 := h1
  simp [h1']

end PDivGroup

open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv in
set_option autoImplicit false in

theorem _root_.GlobalTheory.cocycle_mem_range_cob_of_pullback_mulP :
    ∀ {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] (G : _root_.GlobalTheory.PDivGroup p R)
      (c : G.cocycles) (B : G.funs),
        G.cob B = _root_.GlobalTheory.PDivGroup.cocyclesMap ((p : ℤ_[p]) • 𝟙 G) c → B.1 1 = 0 →
        c ∈ LinearMap.range G.cob := by
  intro p _ R _ G c B hB hB1
  have hcobf : ∀ {m m' : ℕ} (f : G.A m →ₐc[R] G.A m') (a),
      _root_.GlobalTheory.PDiv.cobOne R _ (f a)
        = _root_.GlobalTheory.PDiv.pullbackTwo f (_root_.GlobalTheory.PDiv.cobOne R _ a) := by
    intro m m' f a
    unfold _root_.GlobalTheory.PDiv.cobOne _root_.GlobalTheory.PDiv.pullbackTwo
    simp only [LinearMap.sub_apply, LinearMap.flip_apply, TensorProduct.mk_apply, map_sub,
      TensorProduct.map_tmul]
    rw [← CoalgHomClass.map_comp_comul_apply f a]
    simp
  have hpull : ∀ {m m' m'' : ℕ} (f : G.A m' →ₐc[R] G.A m'')
      (g : G.A m →ₐc[R] G.A m') (z),
      _root_.GlobalTheory.PDiv.pullbackTwo (f.comp g) z
        = _root_.GlobalTheory.PDiv.pullbackTwo f (_root_.GlobalTheory.PDiv.pullbackTwo g z) := by
    intro m m' m'' f g z
    unfold _root_.GlobalTheory.PDiv.pullbackTwo
    rw [← LinearMap.comp_apply, ← TensorProduct.map_comp]
    rfl
  have hlevel : ∀ n, _root_.GlobalTheory.PDiv.cobOne R _ (B.1 (n + 1))
      = _root_.GlobalTheory.PDiv.pullbackTwo (G.mulP n) (c.1 n) := by
    intro n
    have h := congrArg (fun z => z.1 (n + 1)) hB
    unfold _root_.GlobalTheory.PDivGroup.cob _root_.GlobalTheory.PDivGroup.cocyclesMap at h
    simp only [LinearMap.coe_mk, AddHom.coe_mk] at h
    rw [h, _root_.GlobalTheory.PDivGroup.natCast_smul_id_app, ← _root_.GlobalTheory.PDivGroup.mulP_comp_res, hpull]
    congr 1
    exact (c.2 n).2
  have hres1 : ∀ n, G.resOne n (B.1 (n + 1)) = 0 := by
    intro n
    rw [_root_.GlobalTheory.PDivGroup.resOne_funs, hB1]
  have hex : ∀ n, ∃ e, G.mulP n e = B.1 (n + 1) := fun n =>
    _root_.GlobalTheory.PDivGroup.exists_mulP_eq_of_transl_eq G n _
      (_root_.GlobalTheory.PDivGroup.transl_eq_of_cobOne_eq_pullTwo G n _ _ (hlevel n) (hres1 n))
  choose e he using hex
  have hcompat : ∀ n, G.res n (e (n + 1)) = e n := by
    intro n
    apply _root_.GlobalTheory.PDivGroup.Test.mulP_injective G n
    rw [_root_.GlobalTheory.PDivGroup.mulP_res, ← _root_.GlobalTheory.PDivGroup.res_mulP, he, he]
    exact B.2 (n + 1)
  refine ⟨⟨e, hcompat⟩, ?_⟩
  apply Subtype.ext
  funext n
  apply _root_.GlobalTheory.PDivGroup.pullbackTwo_mulP_injective G n
  rw [← hlevel, ← he, hcobf]
  rfl

end GlobalTheory
