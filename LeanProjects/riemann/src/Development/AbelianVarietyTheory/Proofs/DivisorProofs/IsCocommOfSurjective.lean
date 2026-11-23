import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHopfIdealKerIdealOfBialgHomStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PDivGroup.KerGrp

set_option autoImplicit false in
open CategoryTheory TensorProduct Coalgebra Bialgebra in

theorem _root_.GlobalTheory.PDivGroup.KerGrp.isCocomm_of_surjective {k A B : Type} [CommRing k] [CommRing A] [CommRing B]
    [Bialgebra k A] [Bialgebra k B] [IsCocomm k A] (f : A →ₐc[k] B)
    (hf : Function.Surjective f) : IsCocomm k B := by
  constructor
  ext b
  obtain ⟨a, rfl⟩ := hf b
  have hcomm : ∀ y : A ⊗[k] A, TensorProduct.comm k B B (TensorProduct.map (f : A →ₗ[k] B)
      (f : A →ₗ[k] B) y) = TensorProduct.map (f : A →ₗ[k] B) (f : A →ₗ[k] B)
      (TensorProduct.comm k A A y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  have hA : TensorProduct.comm k A A (comul a) = comul a :=
    LinearMap.congr_fun (Coalgebra.comm_comp_comul (R := k) (A := A)) a
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  rw [← CoalgHomClass.map_comp_comul_apply, hcomm, hA]

set_option autoImplicit false in
open CategoryTheory TensorProduct Coalgebra Bialgebra in

theorem _root_.GlobalTheory.PDivGroup.KerGrp.map_res_kerIdeal {p : ℕ} {k : Type} [CommRing k] {G H : _root_.GlobalTheory.PDivGroup p k} (u : G ⟶ H)
    (n : ℕ) : Ideal.map (G.res n : G.A (n + 1) →ₐ[k] G.A n) (_root_.GlobalTheory.PDiv.kerIdeal (u.app (n + 1))) =
      _root_.GlobalTheory.PDiv.kerIdeal (u.app n) := by
  have hc := congrArg (fun g : H.A (n + 1) →ₐc[k] G.A n =>
    ((g : H.A (n + 1) →ₐ[k] G.A n) :
      H.A (n + 1) →+* G.A n))
    (_root_.GlobalTheory.PDivGroup.Hom.comm u n)
  have hres : Ideal.map (H.res n : H.A (n + 1) →ₐ[k]
      H.A n) (_root_.GlobalTheory.PDiv.augIdeal k (H.A (n + 1))) =
      _root_.GlobalTheory.PDiv.augIdeal k (H.A n) :=
    _root_.GlobalTheory.PDiv.kerIdeal_of_surjective (H.10 n)
  unfold _root_.GlobalTheory.PDiv.kerIdeal
  change Ideal.map ((G.res n : G.A (n + 1) →ₐ[k]
      G.A n) : G.A (n + 1) →+* G.A n)
      (Ideal.map ((u.app (n + 1) : H.A (n + 1) →ₐ[k]
        G.A (n + 1)) : H.A (n + 1) →+* G.A (n + 1))
        (_root_.GlobalTheory.PDiv.augIdeal k (H.A (n + 1)))) =
    Ideal.map ((u.app n : H.A n →ₐ[k] G.A n) :
      H.A n →+* G.A n)
      (_root_.GlobalTheory.PDiv.augIdeal k (H.A n))
  rw [Ideal.map_map]

  rw [show ((G.res n : G.A (n + 1) →ₐ[k] G.A n) :
      G.A (n + 1) →+* G.A n).comp
      ((u.app (n + 1) : H.A (n + 1) →ₐ[k] G.A (n + 1)) :
        H.A (n + 1) →+* G.A (n + 1)) =
      ((u.app n : H.A n →ₐ[k] G.A n) :
        H.A n →+* G.A n).comp
      ((H.res n : H.A (n + 1) →ₐ[k] H.A n) :
        H.A (n + 1) →+* H.A n) from hc, ← Ideal.map_map]
  rw [← hres]
  rfl

theorem exists_of_family {p : ℕ} {k : Type} [Field k] (G : PDivGroup p k)
    (u : G ⟶ G) (h₀ : ℕ) (B : ℕ → Type) [∀ n, CommRing (B n)] [∀ n, HopfAlgebra k (B n)]
    (π : ∀ n, G.A n →ₐc[k] B n) (hπ : ∀ n, Function.Surjective (π n))
    (hk : ∀ n, RingHom.ker (π n) = kerIdeal (u.app n))
    (h : ∀ n : ℕ, Module.finrank k (B n) = p ^ (n * h₀)) :
    ∃ (K : PDivGroup p k) (i : K ⟶ G), ∀ n : ℕ, Function.Surjective (i.app n) ∧
      RingHom.ker (i.app n) = kerIdeal (u.app n) := by
  haveI : ∀ n, IsCocomm k (B n) := fun n => isCocomm_of_surjective (π n) (hπ n)
  have hle : ∀ n, RingHom.ker (π (n + 1)) ≤ RingHom.ker ((π n).comp (G.res n)) := fun n a ha => by
    have : G.res n a ∈ RingHom.ker (π n) := by
      rw [hk, ← map_res_kerIdeal]
      rw [hk] at ha
      exact Ideal.mem_map_of_mem (G.res n : G.A (n + 1) →ₐ[k] G.A n) ha
    exact this
  let r := fun n => liftSurj (π (n + 1)) (hπ (n + 1)) ((π n).comp (G.res n)) (hle n)
  have hr : ∀ n a, r n (π (n + 1) a) = π n (G.res n a) := fun n a => liftSurj_apply ..
  let K : PDivGroup p k :=
    { height := h₀
      A := B
      finite := fun n => Module.Finite.of_surjective (π n : G.A n →ₗ[k] B n) (hπ n)
      rank_eq := fun n q => by rw [Module.rankAtStalk_eq_finrank_of_free, h]; rfl
      res := r
      res_surjective := fun n b => by
        obtain ⟨c, rfl⟩ := hπ n b
        obtain ⟨a, rfl⟩ := G.res_surjective n c
        exact ⟨_, hr n a⟩
      ker_res := fun n => by
        rw [← map_torsionIdeal (hπ (n + 1)), ← G.ker_res]
        refine le_antisymm (fun b hb => ?_) (Ideal.map_le_iff_le_comap.2 fun a ha => ?_)
        · obtain ⟨a, rfl⟩ := hπ _ b
          have h1 : G.res n a ∈ RingHom.ker (π n) := (hr n a).symm.trans hb
          rw [hk, ← map_res_kerIdeal] at h1
          obtain ⟨c, hc, e⟩ := (Ideal.mem_map_iff_of_surjective
            (G.res n : G.A (n + 1) →ₐ[k] G.A n) (G.res_surjective n)).1 h1
          rw [← hk] at hc
          have hc' : π (n + 1) c = 0 := hc
          have e' : G.res n c = G.res n a := e
          have h2 : a - c ∈ RingHom.ker (G.res n) := by
            rw [RingHom.mem_ker, map_sub, e', sub_self]
          have h3 : π (n + 1) a = π (n + 1) (a - c) := by rw [map_sub, hc', sub_zero]
          rw [h3]
          exact Ideal.mem_map_of_mem (π (n + 1) : G.A (n + 1) →ₐ[k] B (n + 1)) h2
        · have ha' : G.res n a = 0 := ha
          change r n (π (n + 1) a) = 0
          rw [hr, ha', map_zero] }
  exact ⟨K, ⟨π, fun n => BialgHom.ext fun a => hr n a⟩, fun n => ⟨hπ n, hk n⟩⟩

set_option autoImplicit false in
open CategoryTheory TensorProduct Coalgebra Bialgebra in

theorem _root_.GlobalTheory.PDivGroup.KerGrp.exists_kernel (p : ℕ) [Fact p.Prime] (k : Type) [Field k] (G : _root_.GlobalTheory.PDivGroup p k)
    (u : G ⟶ G) (h₀ : ℕ)
    (h : ∀ n : ℕ, Module.finrank k (G.A n ⧸ _root_.GlobalTheory.PDiv.kerIdeal (u.app n)) = p ^ (n * h₀)) :
    ∃ (K : _root_.GlobalTheory.PDivGroup p k) (i : K ⟶ G), ∀ n : ℕ, Function.Surjective (i.app n) ∧
      RingHom.ker (i.app n) = _root_.GlobalTheory.PDiv.kerIdeal (u.app n) := by
  classical
  obtain ⟨I, hIdef⟩ : ∃ I : ∀ n, Ideal (G.A n),
      ∀ n, I n = _root_.GlobalTheory.PDiv.kerIdeal (u.app n) := ⟨_, fun n => rfl⟩
  haveI hH : ∀ n, (I n).IsHopfIdeal k := fun n => by
    rw [hIdef]
    exact _root_.GlobalTheory.PDiv.isHopfIdeal_kerIdeal_of_bialgHom k _ _ (u.app n)
  have hq : ∀ n, Function.Surjective (Bialgebra.Quotient.mkBialgHom (R := k) (I n)) := by
    intro n x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨a, by simp⟩
  haveI hcoc : ∀ n, IsCocomm k (G.A n ⧸ I n) := fun n =>
    _root_.GlobalTheory.PDivGroup.KerGrp.isCocomm_of_surjective _ (hq n)
  have hmapI : ∀ n, Ideal.map (G.res n : G.A (n + 1) →ₐ[k]
      G.A n) (I (n + 1)) = I n := by
    intro n
    rw [hIdef, hIdef]
    exact _root_.GlobalTheory.PDivGroup.KerGrp.map_res_kerIdeal u n
  have hle : ∀ n, I (n + 1) ≤ (I n).comap (G.res n :
      G.A (n + 1) →ₐ[k] G.A n) := fun n =>
    Ideal.map_le_iff_le_comap.1 (hmapI n).le
  let φ : ∀ n, (G.A (n + 1) ⧸ I (n + 1)) →ₐ[k] (G.A n ⧸ I n) :=
    fun n => Ideal.quotientMapₐ (I n) (G.res n :
      G.A (n + 1) →ₐ[k] G.A n) (hle n)
  have hφ : ∀ n a, φ n (Ideal.Quotient.mk (I (n + 1)) a) =
      Ideal.Quotient.mk (I n) (G.res n a) := fun n a => rfl
  have hcounit : ∀ n, (Bialgebra.counitAlgHom k _).comp (φ n) =
      Bialgebra.counitAlgHom k (G.A (n + 1) ⧸ I (n + 1)) := by
    intro n
    refine AlgHom.ext fun x => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    change CoalgebraStruct.counit (R := k) (Ideal.Quotient.mk (I n) (G.res n a)) =
      CoalgebraStruct.counit (R := k) (Ideal.Quotient.mk (I (n + 1)) a)
    rw [← Bialgebra.Quotient.mkBialgHom_apply (R := k), ← Bialgebra.Quotient.mkBialgHom_apply (R := k),
      CoalgHomClass.counit_comp_apply, CoalgHomClass.counit_comp_apply,
      CoalgHomClass.counit_comp_apply]
  have hcomul : ∀ n, (Algebra.TensorProduct.map (φ n) (φ n)).comp (Bialgebra.comulAlgHom k _) =
      (Bialgebra.comulAlgHom k _).comp (φ n) := by
    intro n
    refine AlgHom.ext fun x => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Algebra.TensorProduct.map (φ n) (φ n)
        (CoalgebraStruct.comul (R := k) (Ideal.Quotient.mk (I (n + 1)) a)) =
      CoalgebraStruct.comul (R := k) (Ideal.Quotient.mk (I n) (G.res n a))
    rw [← Bialgebra.Quotient.mkBialgHom_apply (R := k) (I (n + 1)),
      ← Bialgebra.Quotient.mkBialgHom_apply (R := k) (I n),
      ← CoalgHomClass.map_comp_comul_apply (Bialgebra.Quotient.mkBialgHom (R := k) (I (n + 1))),
      ← CoalgHomClass.map_comp_comul_apply (Bialgebra.Quotient.mkBialgHom (R := k) (I n)),
      ← CoalgHomClass.map_comp_comul_apply (G.res n)]
    generalize CoalgebraStruct.comul (R := k) a = y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [hφ]
    | add x y hx hy => simp only [map_add, hx, hy]
  let r : ∀ n, (G.A (n + 1) ⧸ I (n + 1)) →ₐc[k] (G.A n ⧸ I n) :=
    fun n => BialgHom.ofAlgHom (φ n) (hcounit n) (hcomul n)
  have hr : ∀ n a, r n (Ideal.Quotient.mk (I (n + 1)) a) =
      Ideal.Quotient.mk (I n) (G.res n a) := fun n a => rfl
  have hrs : ∀ n, Function.Surjective (r n) := by
    intro n x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := G.10 n a
    exact ⟨Ideal.Quotient.mk _ b, hr n b⟩
  have hker : ∀ n, RingHom.ker (r n) =
      _root_.GlobalTheory.PDiv.torsionIdeal k (G.A (n + 1) ⧸ I (n + 1)) (p ^ n) := by
    intro n
    ext x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [RingHom.mem_ker, hr, Ideal.Quotient.eq_zero_iff_mem,
      ← _root_.GlobalTheory.PDiv.map_torsionIdeal (hq (n + 1))]
    change _ ↔ Ideal.Quotient.mk (I (n + 1)) a ∈ Ideal.map (Ideal.Quotient.mk (I (n + 1))) _
    rw [Ideal.mem_quotient_iff_mem_sup, ← G.ker_res n]
    change a ∈ Ideal.comap (G.res n : G.A (n + 1) →ₐ[k]
      G.A n) (I n) ↔ _
    rw [← hmapI n, Ideal.comap_map_of_surjective (G.res n :
      G.A (n + 1) →ₐ[k] G.A n) (G.10 n),
      ← RingHom.ker_eq_comap_bot, sup_comm]
    all_goals rfl
  have hkq : ∀ n, RingHom.ker (Bialgebra.Quotient.mkBialgHom (R := k) (I n)) =
      _root_.GlobalTheory.PDiv.kerIdeal (u.app n) := by
    intro n
    rw [← hIdef]
    ext x
    simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
  refine ⟨_root_.GlobalTheory.PDivGroup.mk h₀ (fun n => G.A n ⧸ I n)
    (commRing := fun n => inferInstance) (hopf := fun n => inferInstance) (cocomm := hcoc)
    (finite := fun n => Module.Finite.of_surjective (Ideal.Quotient.mkₐ k (I n)).toLinearMap
      Ideal.Quotient.mk_surjective)
    (projective := fun n => inferInstance) (fun n q => ?_) r hrs hker,
    _root_.GlobalTheory.PDivGroup.Hom.mk (fun n => Bialgebra.Quotient.mkBialgHom (R := k) (I n))
      (fun n => ?_), fun n => ⟨hq n, ?_⟩⟩
  · rw [Module.rankAtStalk_eq_finrank_of_free]
    have hn := h n
    rw [← hIdef] at hn
    simpa using hn
  · exact DFunLike.ext _ _ fun a => rfl
  · exact hkq n

end GlobalTheory.PDivGroup.KerGrp
