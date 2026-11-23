import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

open TensorProduct Coalgebra Bialgebra GlobalTheory.PDiv

namespace GlobalTheory

namespace PDivGroup

variable {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R)

open scoped TensorProduct in
set_option autoImplicit false in
open TensorProduct Coalgebra Bialgebra in
variable {p : ℕ} {R : Type} [CommRing R] (G : _root_.GlobalTheory.PDivGroup p R) in
theorem _root_.GlobalTheory.PDivGroup.ker_resOne (n : ℕ) :
    RingHom.ker (G.resOne n :
      G.A (n + 1) →ₐ[R] G.A 1) =
      _root_.GlobalTheory.PDiv.torsionIdeal R (G.A (n + 1)) p := by
  induction n with
  | zero =>
    have hid : (G.resOne 0 :
        G.A 1 →ₐ[R] G.A 1) = AlgHom.id R _ := by
      ext a; exact G.resOne_zero a
    rw [hid]
    refine le_antisymm ?_ ?_
    · intro a ha
      have : a = 0 := ha
      simp [this]
    · refine (_root_.GlobalTheory.PDiv.torsionIdeal_le_ker_iff p
        (AlgHom.id R (G.A (0 + 1)))).2 ?_
      simpa using G.pts_pow_self 1 (WithConv.toConv (AlgHom.id R (G.A 1)))
  | succ n ih =>
    have hcomp : (G.resOne (n + 1) :
        G.A (n + 2) →ₐ[R] G.A 1) =
        (G.resOne n :
          G.A (n + 1) →ₐ[R] G.A 1).comp
          (G.res (n + 1) :
            G.A (n + 2) →ₐ[R] G.A (n + 1)) := by
      ext a; exact G.resOne_succ n a
    have hsurj : Function.Surjective (G.res (n + 1) :
        G.A (n + 2) →ₐ[R] G.A (n + 1)) :=
      G.res_surjective (n + 1)
    have hker : RingHom.ker ((G.resOne n :
        G.A (n + 1) →ₐ[R] G.A 1).comp
          (G.res (n + 1) :
            G.A (n + 2) →ₐ[R] G.A (n + 1))) =
        Ideal.comap (G.res (n + 1) :
          G.A (n + 2) →ₐ[R] G.A (n + 1))
          (RingHom.ker (G.resOne n :
            G.A (n + 1) →ₐ[R] G.A 1)) := by
      ext a; exact Iff.rfl
    rw [hcomp, hker, ih, ← _root_.GlobalTheory.PDiv.map_torsionIdeal
      (G.res_surjective (n + 1)) p]
    erw [Ideal.comap_map_of_surjective _ hsurj]
    refine sup_eq_left.mpr ?_
    have h0 : Ideal.comap (G.res (n + 1) :
        G.A (n + 2) →ₐ[R] G.A (n + 1)) ⊥ =
        _root_.GlobalTheory.PDiv.torsionIdeal R (G.A (n + 2)) (p ^ (n + 1)) := by
      rw [← G.ker_res (n + 1)]
      ext a; exact Iff.rfl
    rw [h0]
    exact _root_.GlobalTheory.PDiv.torsionIdeal_le_of_dvd (dvd_pow_self p (Nat.succ_ne_zero n))

open scoped TensorProduct in
set_option autoImplicit false in
open TensorProduct Coalgebra Bialgebra in
variable {p : ℕ} {R : Type} [CommRing R] (G : _root_.GlobalTheory.PDivGroup p R) in
theorem _root_.GlobalTheory.PDivGroup.kerIdeal_mulP (n : ℕ) :
    _root_.GlobalTheory.PDiv.kerIdeal (G.mulP n) =
      _root_.GlobalTheory.PDiv.torsionIdeal R (G.A (n + 1)) p := by
  unfold _root_.GlobalTheory.PDiv.torsionIdeal
  rw [← G.mulP_comp_res n,
    _root_.GlobalTheory.PDiv.kerIdeal_comp_of_surjective _ (G.res_surjective n)]

end PDivGroup

section TensorQuot

variable {R k M : Type} [CommRing R] [CommRing k] [Algebra R k] [AddCommGroup M] [Module R M]

end TensorQuot

namespace PDivGroup

end PDivGroup

open scoped TensorProduct in
set_option autoImplicit false in
open TensorProduct Coalgebra Bialgebra in
private theorem mem_ker_smul_univ_of_one_tmul_eq_zero {R k M : Type} [CommRing R] [CommRing k]
    [Algebra R k] [AddCommGroup M] [Module R M] (hk : Function.Surjective (algebraMap R k))
    {m : M} (hm : (1 : k) ⊗ₜ[R] m = 0) :
    m ∈ RingHom.ker (algebraMap R k) • (⊤ : Submodule R M) := by
  set f : R →ₐ[R] k := Algebra.ofId R k
  have hf : Function.Surjective f := hk
  let e : (R ⧸ RingHom.ker f) ≃ₐ[R] k := Ideal.quotientKerAlgEquivOfSurjective hf
  have hker : RingHom.ker f = RingHom.ker (algebraMap R k) := rfl
  let g : k ⊗[R] M ≃ₗ[R] M ⧸ (RingHom.ker f • (⊤ : Submodule R M)) :=
    (LinearEquiv.rTensor M e.symm.toLinearEquiv).trans
      (quotTensorEquivQuotSMul M (RingHom.ker f))
  have h1 : e.symm 1 = Ideal.Quotient.mk (RingHom.ker f) 1 := by simp
  have h2 : g ((1 : k) ⊗ₜ[R] m) = Submodule.Quotient.mk m := by
    simp only [g, LinearEquiv.trans_apply, LinearEquiv.rTensor_tmul,
      AlgEquiv.toLinearEquiv_apply, h1, quotTensorEquivQuotSMul_mk_tmul, one_smul]
  rw [hm, map_zero, eq_comm, Submodule.Quotient.mk_eq_zero] at h2
  exact hker ▸ h2

open scoped TensorProduct in
set_option autoImplicit false in
open TensorProduct Coalgebra Bialgebra in
theorem _root_.GlobalTheory.fibre_statement : ∀ (p : ℕ) (R k : Type) [CommRing R] [CommRing k]
    [Algebra R k], Function.Surjective (algebraMap R k) → ∀ (G : _root_.GlobalTheory.PDivGroup p R) (n : ℕ),
      Function.Surjective (fun a : G.A (n + 1) =>
        ((1 : k) ⊗ₜ[R] G.resOne n a : k ⊗[R] G.A 1)) ∧
      ∀ a : G.A (n + 1),
        ((1 : k) ⊗ₜ[R] G.resOne n a : k ⊗[R] G.A 1) = 0 ↔
          a ∈ (RingHom.ker ((algebraMap R k).comp
            (Bialgebra.counitAlgHom R (G.A n) :
              G.A n →+* R))).map
            ((G.mulP n : G.A n →ₐ[R] G.A (n + 1)) :
              G.A n →+* G.A (n + 1)) := by
  intro p R k _ _ _ hk G n
  set ρ := G.resOne n
  set μ := G.mulP n
  set J := RingHom.ker ((algebraMap R k).comp
    (Bialgebra.counitAlgHom R (G.A n) : G.A n →+* R))
  set L := J.map ((μ : G.A n →ₐ[R] G.A (n + 1)) :
    G.A n →+* G.A (n + 1))
  have hρ : Function.Surjective ρ := G.resOne_surjective n
  have hJ : ∀ x : G.A n, x ∈ J ↔
      algebraMap R k (Bialgebra.counitAlgHom R (G.A n) x) = 0 :=
    fun x => Iff.rfl
  refine ⟨?_, fun a => ⟨fun ha => ?_, fun ha => ?_⟩⟩
  · intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul c x =>
      obtain ⟨r, rfl⟩ := hk c
      obtain ⟨y, rfl⟩ := hρ x
      refine ⟨r • y, ?_⟩
      show (1 : k) ⊗ₜ[R] ρ (r • y) = _
      rw [map_smul, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
        Algebra.algebraMap_eq_smul_one]
    | add s t hs ht =>
      obtain ⟨a, rfl⟩ := hs
      obtain ⟨b, rfl⟩ := ht
      exact ⟨a + b, by simp [TensorProduct.tmul_add]⟩
  · have hmem := mem_ker_smul_univ_of_one_tmul_eq_zero hk ha
    have hle : RingHom.ker (algebraMap R k) • (⊤ : Submodule R (G.A 1)) ≤
        (L.restrictScalars R).map
          (ρ : G.A (n + 1) →ₐ[R] G.A 1).toLinearMap := by
      refine Submodule.smul_le.mpr fun r hr x _ => ?_
      obtain ⟨y, rfl⟩ := hρ x
      refine ⟨r • y, ?_, map_smul _ r y⟩
      show r • y ∈ L
      rw [Algebra.smul_def]
      refine Ideal.mul_mem_right _ _ ?_
      have h1 : algebraMap R (G.A (n + 1)) r =
          (μ : G.A n →ₐ[R] G.A (n + 1))
            (algebraMap R (G.A n) r) := (AlgHom.commutes _ r).symm
      rw [h1]
      refine Ideal.mem_map_of_mem _ ((hJ _).mpr ?_)
      rw [AlgHom.commutes]
      exact hr
    obtain ⟨b, hb, hab⟩ := hle hmem
    have hker : a - b ∈ RingHom.ker
        (ρ : G.A (n + 1) →ₐ[R] G.A 1) := by
      rw [RingHom.mem_ker, map_sub, sub_eq_zero]
      exact hab.symm
    rw [_root_.GlobalTheory.PDivGroup.ker_resOne,
      ← _root_.GlobalTheory.PDivGroup.kerIdeal_mulP] at hker
    have haug : _root_.GlobalTheory.PDiv.kerIdeal μ ≤ L := by
      unfold _root_.GlobalTheory.PDiv.kerIdeal
      refine Ideal.map_mono fun x hx => (hJ x).mpr ?_
      rw [show Bialgebra.counitAlgHom R (G.A n) x = 0 from hx, map_zero]
    have := L.add_mem (haug hker) hb
    rwa [sub_add_cancel] at this
  · let ψ : G.A (n + 1) →+* k ⊗[R] G.A 1 :=
      (Algebra.TensorProduct.includeRight :
        G.A 1 →ₐ[R] k ⊗[R] G.A 1).toRingHom.comp
        (ρ : G.A (n + 1) →ₐ[R] G.A 1).toRingHom
    have hL : L ≤ RingHom.ker ψ := by
      refine Ideal.map_le_iff_le_comap.mpr fun j hj => ?_
      rw [Ideal.mem_comap, RingHom.mem_ker]
      show (1 : k) ⊗ₜ[R] ρ (μ j) = 0
      rw [G.resOne_mulP, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
        TensorProduct.smul_tmul', ← Algebra.algebraMap_eq_smul_one]
      have := (hJ j).mp hj
      rw [Bialgebra.counitAlgHom_apply] at this
      rw [this, TensorProduct.zero_tmul]
    exact hL ha

end GlobalTheory
