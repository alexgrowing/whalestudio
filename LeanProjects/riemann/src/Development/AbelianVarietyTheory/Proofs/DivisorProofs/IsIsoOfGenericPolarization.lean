import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralCartierDualStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDualIntegralCounitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotangentDimsLeHeightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteHopfPointsSeparateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DUnitMemRangeOfMemKerIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.PrismaticDieudonnePerfdIff
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolIso

theorem inj_of_bc {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    {A B : Type} [CommRing A] [CommRing B] [HopfAlgebra R A] [HopfAlgebra R B] [Module.Projective R A]
    (f : A →ₐc[R] B) (h : Function.Injective (bcMap K f)) : Function.Injective f := by
  intro x y hxy
  have hi : Function.Injective (fun a : A => (1 : K) ⊗ₜ[R] a) := by
    have h1 := Module.Flat.rTensor_preserves_injective_linearMap (M := A) (Algebra.linearMap R K)
      (IsFractionRing.injective R K)
    intro a b hab
    apply (TensorProduct.lid R A).symm.injective
    apply h1
    simpa using hab
  apply hi
  apply h
  simp [hxy]

theorem exists_integral_of_local {R D : Type} [CommRing R] [CommRing D] [Bialgebra R D] (y : R)
    (h : ∀ q : Ideal R, q.IsMaximal → ∃ s ∉ q, ∃ Λ : D,
      (∀ d : D, d * Λ = algebraMap R D (Coalgebra.counit (R := R) d) * Λ) ∧
        Coalgebra.counit (R := R) Λ = s * y) :
    ∃ Λ : D, (∀ d : D, d * Λ = algebraMap R D (Coalgebra.counit (R := R) d) * Λ) ∧
      Coalgebra.counit (R := R) Λ = y := by
  let I : Ideal R :=
    { carrier := {s | ∃ Λ : D, (∀ d : D, d * Λ = algebraMap R D (Coalgebra.counit (R := R) d) * Λ) ∧
        Coalgebra.counit (R := R) Λ = s * y}
      zero_mem' := ⟨0, fun d => by simp, by simp⟩
      add_mem' := by
        rintro a b ⟨Λ, hΛ, ha⟩ ⟨Λ', hΛ', hb⟩
        exact ⟨Λ + Λ', fun d => by rw [mul_add, mul_add, hΛ, hΛ'], by rw [map_add, ha, hb, add_mul]⟩
      smul_mem' := by
        rintro c a ⟨Λ, hΛ, ha⟩
        refine ⟨c • Λ, fun d => by rw [mul_smul_comm, mul_smul_comm, hΛ], ?_⟩
        rw [map_smul, ha, smul_eq_mul, smul_eq_mul, _root_.mul_assoc] }
  have hI : I = ⊤ := by
    by_contra hne
    obtain ⟨q, hq, hIq⟩ := Ideal.exists_le_maximal I hne
    obtain ⟨s, hs, Λ, hΛ, hε⟩ := h q hq
    exact hs (hIq ⟨Λ, hΛ, hε⟩)
  obtain ⟨Λ, hΛ, hε⟩ : (1 : R) ∈ I := hI ▸ Submodule.mem_top
  exact ⟨Λ, hΛ, by rw [hε, _root_.one_mul]⟩

def cotBC (R k : Type) [CommRing R] [CommRing k] [Algebra R k] (A : Type) [CommRing A] [Bialgebra R A] :
    Cot k (k ⊗[R] A) ≃ₗ[k] k ⊗[R] Cot R A :=
  ((AugCot.baseChangeEquiv k (counitAlgHom R A)).trans
    (AugCot.congr (AlgEquiv.refl : (k ⊗[R] A) ≃ₐ[k] (k ⊗[R] A)) (by
      refine AlgHom.ext fun x => ?_
      induction x with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul r a => simp [Algebra.smul_def, mul_comm]))).symm

def cotDualBC (R k : Type) [CommRing R] [CommRing k] [Algebra R k] (A : Type) [CommRing A] [HopfAlgebra R A]
    [Module.Finite R A] [Module.Projective R A] [IsCocomm R A] :
    Cot k (CartierDual k (k ⊗[R] A)) ≃ₗ[k] k ⊗[R] Cot R (CartierDual R A) :=
  ((AugCot.baseChangeEquiv k (counitAlgHom R (CartierDual R A))).trans
    (AugCot.congr (CartierDual.baseChange R k A).toAlgEquiv (by
      refine AlgHom.ext fun x => ?_
      induction x with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul r φ => simp [Algebra.TensorProduct.one_def, Algebra.smul_def, mul_comm]))).symm

theorem finrank_cot_le {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R) (k : Type) [Field k] [Algebra R k]
    (hp : algebraMap R k p = 0) [FiniteDimensional k (k ⊗[R] Cot R (G.A 1))] (n : ℕ) :
    Module.finrank k (k ⊗[R] Cot R (G.A n)) ≤ Module.finrank k (k ⊗[R] Cot R (G.A 1)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · haveI : Subsingleton (Cot R (G.A 0)) := ⟨fun a b => (G.cot_zero_eq_zero a).trans (G.cot_zero_eq_zero b).symm⟩
    haveI : Subsingleton (k ⊗[R] Cot R (G.A 0)) := inferInstance
    rw [Module.finrank_zero_of_subsingleton]
    exact Nat.zero_le _
  obtain ⟨f, hf, hker⟩ := G.exists_res_le (m := 1) (n := n) hn
  have hk := G.ker_cotMap_of_ker_eq hf hker
  have hex : Function.Exact (((p : R) ^ 1) • LinearMap.id : Cot R (G.A n) →ₗ[R] Cot R (G.A n)) (cotMap f) := by
    intro w
    rw [← LinearMap.mem_ker, hk, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
    simp [eq_comm]
  have hex2 := lTensor_exact k hex (cotMap_surjective hf)
  have hz : LinearMap.lTensor k (((p : R) ^ 1) • LinearMap.id : Cot R (G.A n) →ₗ[R] Cot R (G.A n)) = 0 := by
    refine TensorProduct.ext' fun c w => ?_
    rw [LinearMap.lTensor_tmul, LinearMap.smul_apply, LinearMap.id_apply, pow_one, TensorProduct.tmul_smul,
      algebra_compatible_smul k, hp, zero_smul, LinearMap.zero_apply]
  have hinj : Function.Injective ((cotMap f).baseChange k) := by
    rw [LinearMap.baseChange_eq_ltensor, injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := (hex2 x).1 hx
    rw [hz, LinearMap.zero_apply]
  exact LinearMap.finrank_le_finrank_of_injective hinj

theorem nakayama (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (q : Ideal R) [q.IsPrime] (g : ℕ) (hg : Module.finrank q.ResidueField (q.ResidueField ⊗[R] M) ≤ g) :
    ∃ (x : Fin g → M) (r : R), r ∉ q ∧ ∀ w : M, r • w ∈ Submodule.span R (Set.range x) := by
  classical
  set κ := q.ResidueField
  let f : M →ₗ[R] κ ⊗[R] M := TensorProduct.mk R κ M 1
  obtain ⟨n, v, hv⟩ := Module.Finite.exists_fin (R := R) (M := M)
  have hspan : Submodule.span κ (Set.range (f ∘ v)) = ⊤ := by
    suffices h : ∀ z, z ∈ Submodule.span κ (Set.range (f ∘ v)) from eq_top_iff.2 fun z _ => h z
    intro z
    induction z with
    | zero => exact zero_mem _
    | add a b ha hb => exact add_mem ha hb
    | tmul c m =>
      have hm : m ∈ Submodule.span R (Set.range v) := hv ▸ Submodule.mem_top
      have : (1 : κ) ⊗ₜ[R] m ∈ Submodule.span κ (Set.range (f ∘ v)) := by
        induction hm using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨i, rfl⟩ := hy
          exact Submodule.subset_span ⟨i, rfl⟩
        | zero => simp
        | add a b _ _ ha hb => rw [TensorProduct.tmul_add]; exact add_mem ha hb
        | smul a y _ hy =>
          rw [TensorProduct.tmul_smul, algebra_compatible_smul κ]
          exact Submodule.smul_mem _ _ hy
      have e : c ⊗ₜ[R] m = c • ((1 : κ) ⊗ₜ[R] m) := by rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
      rw [e]
      exact Submodule.smul_mem _ _ this
  obtain ⟨T, a, ha, hsa, hli⟩ := exists_linearIndependent' κ (f ∘ v)
  haveI : Finite T := Finite.of_injective a ha
  letI := Fintype.ofFinite T
  have hcard : Fintype.card T ≤ g := by
    have hb := Module.Basis.mk hli (by rw [hsa, hspan])
    rw [← Module.finrank_eq_card_basis hb]
    exact hg
  let e := Fintype.equivFin T
  let x : Fin g → M := fun i => if h : (i : ℕ) < Fintype.card T then v (a (e.symm ⟨i, h⟩)) else 0
  have hx : Submodule.span κ (Set.range (f ∘ x)) = ⊤ := by
    rw [eq_top_iff, ← hspan, ← hsa]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨j, rfl⟩
    refine Submodule.subset_span ⟨⟨e j, lt_of_lt_of_le (e j).2 hcard⟩, ?_⟩
    simp [x, (e j).2]
  set N := Submodule.span R (Set.range x)
  let L : κ ⊗[R] M →ₗ[κ] κ ⊗[R] (M ⧸ N) := N.mkQ.baseChange κ
  have hL : L = 0 := by
    have h1 : Submodule.span κ (Set.range (f ∘ x)) ≤ LinearMap.ker L := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨i, rfl⟩
      change N.mkQ.baseChange κ ((1 : κ) ⊗ₜ[R] x i) = 0
      rw [LinearMap.baseChange_tmul, Submodule.mkQ_apply,
        (Submodule.Quotient.mk_eq_zero N).2 (Submodule.subset_span ⟨i, rfl⟩), TensorProduct.tmul_zero]
    rw [hx] at h1
    exact LinearMap.ker_eq_top.1 (eq_top_iff.2 h1)
  have hsurj : Function.Surjective L := by
    change Function.Surjective (N.mkQ.baseChange κ)
    rw [LinearMap.baseChange_eq_ltensor]
    exact LinearMap.lTensor_surjective _ N.mkQ_surjective
  haveI hsub : Subsingleton (κ ⊗[R] (M ⧸ N)) := ⟨fun y z => by
    obtain ⟨y, rfl⟩ := hsurj y
    obtain ⟨z, rfl⟩ := hsurj z
    rw [hL]; rfl⟩
  have hns : (⟨q, inferInstance⟩ : PrimeSpectrum R) ∉ Module.support R (M ⧸ N) := by
    rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct, not_nontrivial_iff_subsingleton]
    exact hsub
  rw [Module.mem_support_iff_of_finite] at hns
  obtain ⟨r, hr, hrq⟩ := Set.not_subset.1 hns
  refine ⟨x, r, hrq, fun w => ?_⟩
  have := (Module.mem_annihilator.1 hr) (Submodule.Quotient.mk w)
  rw [← Submodule.Quotient.mk_smul] at this
  exact (Submodule.Quotient.mk_eq_zero N).1 this

theorem finrank_cot_dual_le {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] (GG : PDivGroup p R) (g : ℕ)
    (k : Type) [Field k] [IsAlgClosed k] [CharP k p] [Algebra R k] (hh : GG.height = 2 * g)
    (hk : g ≤ Module.finrank k (k ⊗[R] Cot R (GG.A 1))) (n : ℕ) :
    Module.finrank k (k ⊗[R] Cot R (GG.dual.A n)) ≤ g := by
  have hd := GlobalTheory.T.cotangent_dims_le_height p k (GG.baseChange k)
  have e1 : Module.finrank k (Cot k ((GG.baseChange k).A 1)) = Module.finrank k (k ⊗[R] Cot R (GG.A 1)) :=
    (cotBC R k (GG.A 1)).finrank_eq
  have e2 : Module.finrank k (Cot k ((GG.baseChange k).dual.A 1)) =
      Module.finrank k (k ⊗[R] Cot R (GG.dual.A 1)) :=
    (cotDualBC R k (GG.A 1)).finrank_eq
  have hb : (GG.baseChange k).height = GG.height := rfl
  rw [e1, e2, hb, hh] at hd
  have hp : algebraMap R k p = 0 := by rw [map_natCast]; exact CharP.cast_eq_zero k p
  exact (finrank_cot_le GG.dual k hp n).trans (by omega)

theorem gens : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (GG : PDivGroup p R) (g : ℕ), GG.height = 2 * g →
    (∀ (k : Type) [Field k] [IsAlgClosed k] [CharP k p] [Algebra R k],
      g ≤ Module.finrank k (k ⊗[R] Cot R (GG.A 1))) →
    ∀ (n : ℕ) (q : Ideal R) [q.IsPrime], (p : R) ∈ q →
      ∃ (x : Fin g → Cot R (GG.dual.A n)) (r : R), r ∉ q ∧
        ∀ w : Cot R (GG.dual.A n), r • w ∈ Submodule.span R (Set.range x) := by
  intro p _ R _ GG g hh hk n q _ hpq
  let k := AlgebraicClosure q.ResidueField
  have hker : RingHom.ker (algebraMap R k) = q := by
    rw [IsScalarTower.algebraMap_eq R q.ResidueField k, RingHom.ker_comp_of_injective _
      (algebraMap q.ResidueField k).injective, Ideal.ker_algebraMap_residueField]
  have hp0 : (p : k) = 0 := by
    rw [← map_natCast (algebraMap R k)]
    exact (RingHom.mem_ker).1 (hker.symm ▸ hpq)
  haveI : CharP k p := (CharP.charP_iff_prime_eq_zero Fact.out).2 hp0
  have hf : Module.finrank q.ResidueField (q.ResidueField ⊗[R] Cot R (GG.dual.A n)) =
      Module.finrank k (k ⊗[R] Cot R (GG.dual.A n)) := by
    rw [← (TensorProduct.AlgebraTensorModule.cancelBaseChange R q.ResidueField k k
      (Cot R (GG.dual.A n))).finrank_eq]
    exact Module.finrank_baseChange.symm
  exact nakayama R _ q g (hf ▸ finrank_cot_dual_le GG g k hh (hk k) n)

end GlobalTheory.PolIso

open GlobalTheory.PolIso in

theorem GlobalTheory.PDivGroup.isIso_of_isIso_baseChange_of_cot : ∀ (p : ℕ) [Fact p.Prime] (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (GG : PDivGroup p R) (φ : GG ⟶ GG.dual) (g : ℕ), GG.height = 2 * g → IsIso (PDivGroup.baseChangeMap K φ) → (∀ (k : Type) [Field k] [IsAlgClosed k] [CharP k p] [Algebra R k], g ≤ Module.finrank k (k ⊗[R] Cot R (GG.A 1))) → IsIso φ := by
  intro p _ R K _ _ _ _ _ _ _ _ GG φ g hh hK hk
  have hbc : ∀ n, Function.Injective (bcMap K (φ.app n)) := by
    intro n a b hab
    have e := congrArg (fun f => Hom.app f n) (IsIso.inv_hom_id (baseChangeMap K φ))
    have e' : ∀ c, (Hom.app (inv (baseChangeMap K φ)) n) (bcMap K (φ.app n) c) = c := fun c =>
      DFunLike.congr_fun e c
    rw [← e' a, ← e' b]
    exact congrArg _ hab
  have bij : ∀ n, Function.Bijective (φ.app n) := by
    intro n
    have inj : Function.Injective (φ.app n) := inj_of_bc (φ.app n) (hbc n)
    obtain ⟨Λ, hΛ, hε⟩ := exists_integral_of_local (D := GG.dual.A n) ((p : R) ^ (n * g)) (fun q hq => by
      by_cases hp : (p : R) ∈ q
      · obtain ⟨x, r, hr, hx⟩ := gens p R GG g hh hk n q hp
        obtain ⟨k, Λ, hΛ, hε⟩ := GlobalTheory.T.exists_integral_cartier_dual R (GG.dual.A n) g x r ((p : R) ^ n) hx
          (fun w => GG.dual.pow_smul_cot n w)
        refine ⟨r ^ k, fun h => hr (hq.isPrime.mem_of_pow_mem k h), Λ, hΛ, ?_⟩
        rw [hε, pow_mul]
      · obtain ⟨k, Λ, hΛ, hε⟩ := GlobalTheory.T.exists_integral_cartier_dual R (GG.dual.A n) g 0 ((p : R) ^ n) ((p : R) ^ n)
          (fun w => by rw [GG.dual.pow_smul_cot n w]; exact zero_mem _)
          (fun w => GG.dual.pow_smul_cot n w)
        refine ⟨((p : R) ^ n) ^ k, fun h => hp (hq.isPrime.mem_of_pow_mem n
          (hq.isPrime.mem_of_pow_mem k h)), Λ, hΛ, ?_⟩
        rw [hε, pow_mul])
    have hcard := (GlobalTheory.T.finite_hopf_points_separate R K (GG.A n)).2.2 ⟨⊥, Ideal.isPrime_bot⟩
    rw [GG.rank_eq n] at hcard
    refine ⟨inj, GlobalTheory.T.cartier_dual_integral_counit R K (GG.A n) (φ.app n) Λ ((p : R) ^ (n * g)) hΛ hε ?_ inj⟩
    rw [← hcard, hh, map_pow, map_natCast, ← pow_mul]
    push_cast
    ring_nf
  let e : GG ≅ GG.dual :=
    { hom := φ
      inv := ⟨fun n => ((BialgEquiv.ofBijective (φ.app n) (bij n)).symm : GG.A n →ₐc[R] GG.dual.A n),
        fun n => BialgHom.ext fun a => by
          obtain ⟨b, rfl⟩ := (bij (n + 1)).2 a
          have k := fun m x => (BialgEquiv.ofBijective (φ.app m) (bij m)).symm_apply_apply x
          exact (congrArg (GG.dual.res n) (k (n + 1) b)).trans
            ((k n _).symm.trans (congrArg (BialgEquiv.ofBijective (φ.app n) (bij n)).symm
              (res_app φ n b).symm))⟩
      hom_inv_id := hom_ext fun n => BialgHom.ext fun a =>
        (BialgEquiv.ofBijective (φ.app n) (bij n)).apply_symm_apply a
      inv_hom_id := hom_ext fun n => BialgHom.ext fun a =>
        (BialgEquiv.ofBijective (φ.app n) (bij n)).symm_apply_apply a }
  exact e.isIso_hom
