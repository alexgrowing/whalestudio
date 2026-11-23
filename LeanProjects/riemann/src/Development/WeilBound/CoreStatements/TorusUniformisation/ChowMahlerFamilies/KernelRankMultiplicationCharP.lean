import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdAd
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBGen
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBSer
import Development.AbelianVarietyTheory.Definitions.Divisors.FibreRankCompOfSurjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubeDescendsAlongEtaleIsogeny
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatAndSurjectiveOfIsFiniteAbelianEnd
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LocallyQuasiFiniteOfFiniteGeometricPoints
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FormalGermDimensionUnique
import Development.WeilBound.CoreStatements.HodgeTatePoints.GermCompOneAssocOfConstantCoeffZero

namespace PositivityTheory.Xgn.JetKernelRank

section Weyl
open Module

theorem finrank_eq_mul_ker {k V : Type} [Field k] (p : ℕ) [CharP k p] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (X D : V →ₗ[k] V) (h : ∀ v, D (X v) = X (D v) + v) (hp : X ^ p = 0) :
    finrank k V = p * finrank k (LinearMap.ker X) := by
  have h1 : ∀ (n : ℕ) v, D ((X ^ (n + 1)) v) = (X ^ (n + 1)) (D v) + ((n + 1 : ℕ) : k) • (X ^ n) v := by
    intro n
    induction n with
    | zero => intro v; simp [h]
    | succ n ih =>
      intro v
      rw [pow_succ' X (n + 1), Module.End.mul_apply, h, ih, Module.End.mul_apply, map_add, map_smul,
        ← Module.End.mul_apply X (X ^ n), ← pow_succ', Nat.cast_succ (n + 1), add_smul, one_smul, add_assoc]
  have h2 : ∀ j, j < p → LinearMap.ker X ≤ LinearMap.range (X ^ j) := by
    intro j
    induction j with
    | zero => intro _ v _; exact ⟨v, by simp⟩
    | succ j ih =>
      intro hj v hv
      obtain ⟨w, rfl⟩ := ih (by omega) hv
      have e : (X ^ (j + 1)) w = 0 := by rw [pow_succ', Module.End.mul_apply]; exact hv
      have e2 := h1 j w
      rw [e, map_zero] at e2
      have hne : ((j + 1 : ℕ) : k) ≠ 0 := fun h0 =>
        absurd (Nat.le_of_dvd (by omega) ((CharP.cast_eq_zero_iff k p _).1 h0)) (by omega)
      refine ⟨-(((j + 1 : ℕ) : k)⁻¹ • D w), ?_⟩
      rw [map_neg, map_smul, eq_neg_of_add_eq_zero_left e2.symm, smul_neg, neg_neg, smul_smul,
        inv_mul_cancel₀ hne, one_smul]
  have h3 : ∀ j, j < p → finrank k (LinearMap.range (X ^ j)) =
      finrank k (LinearMap.range (X ^ (j + 1))) + finrank k (LinearMap.ker X) := by
    intro j hj
    have := (X.domRestrict (LinearMap.range (X ^ j))).finrank_range_add_finrank_ker
    rw [LinearMap.range_domRestrict, ← LinearMap.range_comp, LinearMap.ker_domRestrict,
      (Submodule.comapSubtypeEquivOfLe (h2 j hj)).finrank_eq] at this
    rw [← this, pow_succ']; rfl
  have h4 : ∀ j, j ≤ p → finrank k V = finrank k (LinearMap.range (X ^ j)) + j * finrank k (LinearMap.ker X) := by
    intro j
    induction j with
    | zero => intro _; rw [pow_zero, Module.End.one_eq_id, LinearMap.range_id, finrank_top]; simp
    | succ j ih => intro hj; rw [ih (by omega), h3 j (by omega)]; ring
  have := h4 p le_rfl
  rwa [hp, LinearMap.range_zero, finrank_bot, zero_add] at this

variable {k C : Type} [Field k] [CommRing C] [Algebra k C]

theorem finrank_quot_add {V : Type} [AddCommGroup V] [Module k V] [Module C V] [IsScalarTower k C V]
    [FiniteDimensional k V] (N : Submodule C V) : finrank k (V ⧸ N) + finrank k N = finrank k V := by
  have := (N.mkQ.restrictScalars k).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.2 (show Function.Surjective (N.mkQ.restrictScalars k) from N.mkQ_surjective), finrank_top, LinearMap.ker_restrictScalars,
    Submodule.ker_mkQ] at this
  exact this

theorem exists_quot {V : Type} [AddCommGroup V] [Module k V] [Module C V] [IsScalarTower k C V]
    (N : Submodule C V) (T : V →ₗ[k] V) (h : ∀ v ∈ N, T v ∈ N) :
    ∃ T' : (V ⧸ N) →ₗ[k] (V ⧸ N), ∀ v, T' (N.mkQ v) = N.mkQ (T v) := by
  let e := Submodule.Quotient.restrictScalarsEquiv k N
  refine ⟨(N.restrictScalars k).liftQ (N.mkQ.restrictScalars k ∘ₗ T) (fun v hv => ?_) ∘ₗ e.symm.toLinearMap,
    fun v => ?_⟩
  · simpa using h v hv
  · simp [e]

theorem loc (p : ℕ) [CharP k p] (χ : C →ₐ[k] k) (s : ℕ) : ∀ (V : Type) [AddCommGroup V] [Module k V] [Module C V]
    [IsScalarTower k C V] [FiniteDimensional k V], (∀ c, χ c = 0 → ∀ v : V, c ^ p • v = 0) →
    ∀ (T : Fin s → V →ₗ[k] V) (δ : Fin s → C → C), (∀ i c v, T i (c • v) = c • T i v + δ i c • v) →
    ∀ x : Fin s → C, (∀ i, χ (x i) = 0) → (∀ i j, χ (δ i (x j)) = if i = j then 1 else 0) →
    p ^ s ∣ finrank k V := by
  induction s with
  | zero => intros; simp
  | succ s ih =>
    intro V _ _ _ _ _ hV T δ hT x hx hδ
    let w : C := ∑ i ∈ Finset.range p, (1 - δ 0 (x 0)) ^ i
    have hw : ∀ v : V, (w * δ 0 (x 0)) • v = v := fun v => by
      have h1 := geom_sum_mul_neg (1 - δ 0 (x 0)) p
      rw [sub_sub_cancel] at h1
      have h2 := hV (1 - δ 0 (x 0)) (by rw [map_sub, hδ]; simp) v
      rw [h1, sub_smul, h2, one_smul, sub_zero]
    let X : V →ₗ[C] V := LinearMap.lsmul C V (x 0)
    let N := LinearMap.range X
    have a1 := finrank_eq_mul_ker p (X.restrictScalars k) (w • T 0) (fun v => by
      simp only [X, LinearMap.smul_apply, LinearMap.restrictScalars_apply, LinearMap.lsmul_apply, hT, smul_add,
        ← mul_smul, hw, mul_comm w]
      rw [mul_comm (δ 0 (x 0)), hw]) (by
      have : ∀ n (v : V), ((X.restrictScalars k) ^ n) v = x 0 ^ n • v := fun n => by
        induction n with
        | zero => simp
        | succ n ih => intro v; rw [pow_succ, Module.End.mul_apply, ih, pow_succ, mul_smul]; rfl
      ext v; rw [this, hV _ (hx 0)]; rfl)
    have a2 := (X.restrictScalars k).finrank_range_add_finrank_ker
    have a3 := finrank_quot_add (k := k) N
    have a4 : finrank k (LinearMap.range (X.restrictScalars k)) = finrank k N := by
      rw [LinearMap.range_restrictScalars]; rfl
    have a5 : finrank k V = p * finrank k (V ⧸ N) := by rw [a1]; congr 1; omega
    have b : ∀ j : Fin s, ∃ T' : (V ⧸ N) →ₗ[k] (V ⧸ N), ∀ v, T' (N.mkQ v) =
        N.mkQ ((T j.succ - (δ j.succ (x 0) * w) • T 0) v) := fun j => exists_quot N _ (by
      rintro _ ⟨v, rfl⟩
      refine ⟨(T j.succ - (δ j.succ (x 0) * w) • T 0) v, ?_⟩
      simp only [X, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.lsmul_apply, hT, smul_add, smul_sub,
        ← mul_smul]
      rw [mul_assoc _ w (δ 0 (x 0)), mul_smul _ (w * _), hw, mul_comm (x 0)]
      abel)
    choose T' hT' using b
    have : FiniteDimensional k (V ⧸ N) := Module.Finite.of_surjective (N.mkQ.restrictScalars k) N.mkQ_surjective
    have := ih (V ⧸ N) (fun c hc v => by
        obtain ⟨v, rfl⟩ := N.mkQ_surjective v
        rw [← map_smul, hV c hc, map_zero]) T' (fun j c => δ j.succ c - δ j.succ (x 0) * w * δ 0 c)
      (fun j c v => by
        obtain ⟨v, rfl⟩ := N.mkQ_surjective v
        rw [← map_smul N.mkQ, hT', hT', ← map_smul N.mkQ, ← map_smul N.mkQ, ← map_add]
        congr 1
        simp only [LinearMap.smul_apply, LinearMap.sub_apply, hT, smul_add, smul_sub, ← mul_smul, sub_smul]
        rw [mul_comm c]
        abel) (fun j => x j.succ) (fun j => hx _) (fun i j => by
        simp [hδ])
    rw [a5, pow_succ']
    exact mul_dvd_mul_left _ this

theorem glob [IsAlgClosed k] [Module.Finite k C] (p : ℕ) [Fact p.Prime] [CharP k p] {s : ℕ} (δ : Fin s → C → C)
    (hx : ∀ χ : C →ₐ[k] k, ∃ x : Fin s → C, (∀ i, χ (x i) = 0) ∧ ∀ i j, χ (δ i (x j)) = if i = j then 1 else 0)
    (n : ℕ) : ∀ (V : Type) [AddCommGroup V] [Module k V] [Module C V]
    [IsScalarTower k C V] [FiniteDimensional k V], finrank k V = n →
    ∀ (T : Fin s → V →ₗ[k] V), (∀ i c v, T i (c • v) = c • T i v + δ i c • v) → p ^ s ∣ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ _ _ _ hn T hT
  rcases subsingleton_or_nontrivial V with h0 | h0
  · rw [← hn, finrank_zero_of_subsingleton]; exact dvd_zero _
  have : Module.Finite C V := Module.Finite.of_restrictScalars_finite k C V
  have hA : Module.annihilator C V ≠ ⊤ := fun h => by
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    exact hv ((one_smul C v).symm.trans (Module.mem_annihilator.1 (h ▸ Submodule.mem_top) v))
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hA
  letI := Ideal.Quotient.field m
  let e : k ≃ₐ[k] C ⧸ m :=
    .ofBijective (Algebra.ofId k _) IsAlgClosed.algebraMap_bijective_of_isIntegral
  let χ : C →ₐ[k] k := e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ k m)
  have hχ : ∀ c, χ c = 0 → c ∈ m := fun c hc =>
    Ideal.Quotient.eq_zero_iff_mem.1 ((map_eq_zero_iff _ e.symm.injective).1 hc)
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  let J : Ideal C := Ideal.span {a | ∃ c, χ c = 0 ∧ a = c ^ p}
  have hJ : J ≤ m := Ideal.span_le.2 (by rintro _ ⟨c, hc, rfl⟩; exact Ideal.pow_mem_of_mem m (hχ c hc) _ (by omega))
  let N : Submodule C V := J • ⊤
  have hN : N ≠ ⊤ := fun h => by
    obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul J ⊤
      (Module.Finite.fg_top (R := C) (M := V)) h.ge
    have : r ∈ m := hle (Module.mem_annihilator.2 fun v => hr v trivial)
    exact hm.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using m.sub_mem this (hJ hr1)))
  have hpow : ∀ i c (n : ℕ) v, T i (c ^ (n + 1) • v) = c ^ (n + 1) • T i v + ((n + 1 : ℕ) : k) • (c ^ n * δ i c) • v := by
    intro i c n
    induction n with
    | zero => intro v; simp [hT]
    | succ n ih =>
      intro v
      rw [pow_succ' c (n + 1), mul_smul, hT, ih, smul_add, smul_comm c ((n + 1 : ℕ) : k), Nat.cast_succ (n + 1),
        add_smul ((n + 1 : ℕ) : k), one_smul, ← mul_smul c (c ^ n * _), ← mul_smul (δ i c), ← mul_assoc, ← pow_succ',
        mul_comm (δ i c), add_assoc, mul_smul c]
  have hTN : ∀ i, ∀ v ∈ N, T i v ∈ N := fun i v hv => by
    refine Submodule.smul_induction_on hv (fun a ha v _ => ?_) (fun a b ha hb => by rw [map_add]; exact N.add_mem ha hb)
    induction ha using Submodule.span_induction generalizing v with
    | mem a ha =>
      obtain ⟨c, hc, rfl⟩ := ha
      have := hpow i c (p - 1) v
      rw [Nat.sub_add_cancel (by omega), CharP.cast_eq_zero, zero_smul, add_zero] at this
      rw [this]
      exact Submodule.smul_mem_smul (Ideal.subset_span ⟨c, hc, rfl⟩) trivial
    | zero => simp
    | add a b _ _ ha hb => rw [add_smul, map_add]; exact N.add_mem (ha v trivial) (hb v trivial)
    | smul a b _ hb => rw [smul_eq_mul, mul_comm, mul_smul]; exact hb _ trivial
  have : FiniteDimensional k (V ⧸ N) := Module.Finite.of_surjective (N.mkQ.restrictScalars k) N.mkQ_surjective
  have : FiniteDimensional k N := Module.Finite.of_injective (N.subtype.restrictScalars k) Subtype.val_injective
  have a3 := finrank_quot_add (k := k) N
  have : Nontrivial (V ⧸ N) := Submodule.Quotient.nontrivial_iff.2 hN
  have a4 : 0 < finrank k (V ⧸ N) := finrank_pos
  choose T' hT' using fun i => exists_quot N (T i) (hTN i)
  obtain ⟨x, x1, x2⟩ := hx χ
  have b1 := loc p χ s (V ⧸ N) (fun c hc v => by
      obtain ⟨v, rfl⟩ := N.mkQ_surjective v
      rw [← map_smul]
      exact (Submodule.Quotient.mk_eq_zero _).2 (Submodule.smul_mem_smul (Ideal.subset_span ⟨c, hc, rfl⟩) trivial))
    T' δ (fun j c v => by
      obtain ⟨v, rfl⟩ := N.mkQ_surjective v
      rw [← map_smul N.mkQ, hT', hT', ← map_smul N.mkQ, ← map_smul N.mkQ, ← map_add, hT]) x x1 x2
  have b2 := ih (finrank k N) (by omega) N rfl
    (fun i => ⟨⟨fun v => ⟨T i v, hTN i v v.2⟩, fun a b => Subtype.ext (map_add _ _ _)⟩,
      fun a b => Subtype.ext (map_smul (T i) a b.1)⟩) (fun i c v => Subtype.ext (hT i c v.1))
  rw [← hn, ← a3]
  exact dvd_add b1 b2

end Weyl

section Hopf
open Module TensorProduct Coalgebra Bialgebra WithConv

variable {k H : Type} [Field k] [CommRing H] [HopfAlgebra k H]

noncomputable def inv (D : H →ₗ[k] k) : H →ₗ[k] H :=
  (TensorProduct.rid k H).toLinearMap ∘ₗ D.lTensor H ∘ₗ comul

theorem inv_mul (D : H →ₗ[k] k) (hD : ∀ a b, D (a * b) = counit (R := k) a * D b + D a * counit (R := k) b)
    (a b : H) : inv D (a * b) = a * inv D b + inv D a * b := by
  let β : H ⊗[k] H →ₗ[k] H := (TensorProduct.rid k H).toLinearMap ∘ₗ D.lTensor H
  let e : H ⊗[k] H →ₗ[k] H := (TensorProduct.rid k H).toLinearMap ∘ₗ (counit (R := k)).lTensor H
  have he : ∀ a, e (comul a) = a := fun a => by simp [e]
  have key : ∀ s t, β (s * t) = e s * β t + β s * e t := fun s t => by
    induction s with
    | zero => simp
    | add x y hx hy => simp only [add_mul, map_add, hx, hy]; ring
    | tmul a a' =>
      induction t with
      | zero => simp
      | add x y hx hy => simp only [mul_add, map_add, hx, hy]; ring
      | tmul b b' => simp [β, e, hD, Algebra.smul_def]; ring
  have := key (comul a) (comul b)
  rw [he, he, ← Bialgebra.comul_mul] at this
  exact this

theorem exists_transl (χ : H →ₐ[k] k) : ∃ σ : H →ₐ[k] H, (∀ y, χ (σ y) = counit y) ∧
    ∀ (D : H →ₗ[k] k) y, χ (inv D (σ y)) = D y := by
  let u : WithConv (H →ₐ[k] H) := toConv ((Algebra.ofId k H).comp χ)
  let v : WithConv (H →ₐ[k] H) := u⁻¹
  let e : WithConv (H →ₐ[k] H) := toConv (AlgHom.id k H)
  have hu' : ∀ f : H →ₐ[k] H, f.comp u.ofConv = u.ofConv := fun f ↦ by
    ext y; simp [u]
  have hv' : ∀ f : H →ₐ[k] H, f.comp v.ofConv = v.ofConv := fun f ↦ by
    change f.comp (u.ofConv.comp _) = u.ofConv.comp _
    rw [← AlgHom.comp_assoc, hu']
  have he : ∀ f : H →ₐ[k] H, f.comp e.ofConv = f := fun f ↦ rfl
  have h1 : (u * e).ofConv.comp (v * e).ofConv = e.ofConv := by
    rw [AlgHom.comp_convMul_distrib, he, hv', toConv_ofConv, toConv_ofConv, inv_mul_cancel_left]
  have h2 : u.ofConv.comp (v * e).ofConv = (1 : WithConv (H →ₐ[k] H)).ofConv := by
    rw [AlgHom.comp_convMul_distrib, he, hv', toConv_ofConv, toConv_ofConv, inv_mul_cancel]
  refine ⟨(v * e).ofConv, fun y => ?_, fun D y => ?_⟩
  · have := congrArg χ (DFunLike.congr_fun h2 y)
    simpa [u] using this
  · have h3 : ∀ x, χ (inv D x) = D ((u * e) x) := fun x => by
      rw [AlgHom.convMul_apply, inv]
      simp only [LinearMap.comp_apply]
      generalize comul (R := k) x = t
      induction t with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul a b => simp [u, e]; rw [← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
    rw [h3]
    exact congrArg D (DFunLike.congr_fun h1 y)

theorem dvd_quot [IsAlgClosed k] [Module.Finite k H] (p : ℕ) [Fact p.Prime] [CharP k p] {s : ℕ}
    (D : Fin s → H →ₗ[k] k) (hD : ∀ i a b, D i (a * b) = counit (R := k) a * D i b + D i a * counit (R := k) b)
    (hli : LinearIndependent k D) (I : Ideal H) (hI : ∀ i, ∀ a ∈ I, inv (D i) a ∈ I) :
    p ^ s ∣ finrank k (H ⧸ I) := by
  have h1 : ∀ i, D i 1 = 0 := fun i => by simpa using hD i 1 1
  have hs : Function.Surjective (LinearMap.pi D) := by
    rw [← LinearMap.range_eq_top]
    by_contra hne
    obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    have e : ∀ v : Fin s → k, f v = ∑ i, f (Pi.single i 1) * v i := fun v => by
      conv_lhs => rw [pi_eq_sum_univ' v]
      simp [mul_comm]
    have := Fintype.linearIndependent_iff.1 hli (fun i => f (Pi.single i 1)) (by
      ext a
      have := hf (LinearMap.mem_range_self _ a)
      rw [LinearMap.mem_ker, e] at this
      simpa using this)
    exact hf0 (LinearMap.ext fun v => by simp [e v, this])
  choose y hy using fun j => hs (Pi.single j 1)
  choose T hT using fun i => exists_quot (k := k) I (inv (D i)) (hI i)
  refine glob p (fun i => inv (D i)) (fun χ => ?_) _ (H ⧸ I) rfl T (fun i c v => ?_)
  · obtain ⟨σ, s1, s2⟩ := exists_transl χ
    refine ⟨fun j => σ (y j - counit (R := k) (y j) • 1), fun j => by rw [s1]; simp, fun i j => ?_⟩
    have := congrFun (hy j) i
    rw [s2, map_sub, map_smul, h1, smul_zero, sub_zero]
    exact this.trans (Pi.single_apply _ _ _)
  · obtain ⟨v, rfl⟩ := I.mkQ_surjective v
    rw [← map_smul I.mkQ, hT, hT, ← map_smul I.mkQ, ← map_smul I.mkQ, ← map_add, smul_eq_mul, inv_mul _ (hD i)]
    rfl

open GlobalTheory GlobalTheory.PDiv in
theorem hopf_dvd [IsAlgClosed k] [Module.Finite k H] [IsCocomm k H] (p : ℕ) [Fact p.Prime] [CharP k p] {r s : ℕ}
    (f : Fin r → H) (hf : ∀ i, comul (f i) = f i ⊗ₜ[k] 1 + 1 ⊗ₜ[k] f i) (hf0 : ∀ i, counit (R := k) (f i) = 0)
    (hfi : LinearIndependent k f)
    (D : Fin s → H →ₗ[k] k) (hD : ∀ i a b, D i (a * b) = counit (R := k) a * D i b + D i a * counit (R := k) b)
    (hli : LinearIndependent k D) (h0 : ∀ i j, D i (f j) = 0) : p ^ (r + s) ∣ finrank k H := by
  let P := SymmetricAlgebra k (Fin r → k)
  letI : HopfAlgebra k P := HopfAlgebra.ofAlgHom (SymmetricAlgebra.lift (-SymmetricAlgebra.ι k (Fin r → k)))
    (by
      ext x; simp [P, SymmetricAlgebra.algebraMapInv_ι]
      erw [Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul]; simp)
    (by ext x; simp [P, SymmetricAlgebra.algebraMapInv_ι])
  let l : (Fin r → k) →ₗ[k] H := Fintype.linearCombination k f
  have hl : ∀ i, l (Pi.single i 1) = f i := fun i => by simp [l]
  let F : P →ₐc[k] H := BialgHom.ofAlgHom (SymmetricAlgebra.lift l)
    (by ext x; simp [P, SymmetricAlgebra.algebraMapInv_ι, hl, hf0]) (by ext x; simp [P, hl, hf])
  have hF : ∀ x, F (SymmetricAlgebra.ι k _ x) = l x := fun x => SymmetricAlgebra.lift_ι_apply _ x
  rw [finrank_eq_ker_mul_range k H P F, pow_add, mul_comm]
  have h1 : ∀ i, D i 1 = 0 := fun i => by simpa using hD i 1 1
  refine mul_dvd_mul (dvd_quot p D hD hli _ fun i a ha => ?_) ?_
  · have key : ∀ x : P, counit (R := k) x = 0 → F x ∈ kerIdeal F := fun x hx => Ideal.mem_map_of_mem _ hx
    have k2 : ∀ x : P, inv (D i) (F x) = 0 := fun x => by
      induction x using SymmetricAlgebra.induction with
      | algebraMap c => simp [inv, Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.one_def, h1]
      | ι x => simp [hF, l, Fintype.linearCombination_apply, inv, hf, h0, h1]
      | mul a b ha hb => rw [map_mul, inv_mul _ (hD i), ha, hb]; simp
      | add a b ha hb => rw [map_add, map_add, ha, hb, add_zero]
    induction ha using Submodule.span_induction with
    | mem a ha => obtain ⟨x, -, rfl⟩ := ha; exact (k2 x).symm ▸ zero_mem _
    | zero => simp
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | smul a b hb' hb =>
      rw [smul_eq_mul, inv_mul _ (hD i)]
      exact add_mem (Ideal.mul_mem_left _ _ hb) (Ideal.mul_mem_left _ _ hb')
  · let G := CartierDual.mapAlgHom (F : P →ₗc[k] H)
    have e1 : finrank k (CartierDual k H ⧸ RingHom.ker G) =
        finrank k (LinearMap.range (F : P →ₐ[k] H).toLinearMap) := by
      rw [← LinearMap.finrank_range_dualMap_eq_finrank_range]
      have a1 := finrank_quot_add (k := k) (RingHom.ker G)
      have a2 := ((F : P →ₐ[k] H).toLinearMap.dualMap ∘ₗ
        (CartierDual.toDual k H).toLinearMap).finrank_range_add_finrank_ker
      rw [LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)] at a2
      have a3 : LinearMap.ker ((F : P →ₐ[k] H).toLinearMap.dualMap ∘ₗ
        (CartierDual.toDual k H).toLinearMap) = (RingHom.ker G).restrictScalars k := by
        ext φ
        exact ⟨fun h => CartierDual.ext_apply fun x => DFunLike.congr_fun h x,
          fun h => LinearMap.ext fun x => congrArg (fun q : CartierDual k P => q x) h⟩
      rw [a3] at a2
      exact Nat.add_right_cancel (a1.trans a2.symm)
    rw [← e1]
    have ev : ∀ (φ : CartierDual k H) (b a : H), inv (CartierDual.evalAt k H b) φ a = φ (a * b) := fun φ b a => by
      rw [← CartierDual.pair_comul_tmul, inv]
      simp only [LinearMap.comp_apply]
      generalize comul (R := k) φ = t
      induction t with
      | zero => simp
      | add x y hx hy => simp only [map_add, LinearMap.add_apply, ← hx, ← hy]; rfl
      | tmul a b => simp [mul_comm]
    refine dvd_quot p (fun i => CartierDual.evalAt k H (f i)) (fun i φ ψ => ?_) ?_ _ fun i φ hφ => ?_
    · simp [CartierDual.mul_apply, hf, add_comm]
    · refine hfi.map' _ (LinearMap.ker_eq_bot'.2 fun a ha => ?_)
      exact CartierDual.eq_of_forall_apply (R := k) fun φ => (DFunLike.congr_fun ha φ).trans (map_zero _).symm
    · refine CartierDual.ext_apply fun x => ?_
      have := congrArg (fun q : CartierDual k P => q (x * SymmetricAlgebra.ι k _ (Pi.single i 1))) hφ
      change inv (CartierDual.evalAt k H (f i)) φ (F x) = 0
      rw [ev, ← hl, ← hF, ← map_mul]
      exact this

end Hopf

section Coef
open TensorProduct TrivSqZeroExt

variable {k : Type} [Field k] {r : ℕ} {B : Type} [CommRing B] [Algebra k B]

abbrev Sq (k : Type) [Field k] (r : ℕ) : Type := TrivSqZeroExt k (Fin r → k)

variable (k r B) in

noncomputable def c0 : B ⊗[k] Sq k r →ₐ[k] B :=
  (Algebra.TensorProduct.rid k k B).toAlgHom.comp (Algebra.TensorProduct.map (AlgHom.id k B) (fstHom k k _))

noncomputable def co (i : Fin r) : B ⊗[k] Sq k r →ₗ[k] B :=
  (TensorProduct.rid k B).toLinearMap ∘ₗ (LinearMap.proj i ∘ₗ sndHom k (Fin r → k)).lTensor B

@[simp] theorem constant_term_tensor (b : B) (x : Sq k r) : c0 k r B (b ⊗ₜ[k] x) = x.fst • b := by simp [c0]

@[simp] theorem co_tmul (i : Fin r) (b : B) (x : Sq k r) : co i (b ⊗ₜ[k] x) = x.snd i • b := by simp [co]

theorem co_mul (i : Fin r) (s t : B ⊗[k] Sq k r) : co i (s * t) = c0 k r B s * co i t + co i s * c0 k r B t := by
  induction s with
  | zero => simp
  | add x y hx hy => simp only [add_mul, map_add, hx, hy]; ring
  | tmul a a' =>
    induction t with
    | zero => simp
    | add x y hx hy => simp only [mul_add, map_add, hx, hy]; ring
    | tmul b b' => simp [snd_mul, Algebra.smul_def]; ring

theorem co_map {B' : Type} [CommRing B'] [Algebra k B'] (θ : B →ₐ[k] B') (i : Fin r) (s : B ⊗[k] Sq k r) :
    co i (Algebra.TensorProduct.map θ (AlgHom.id k _) s) = θ (co i s) := by
  induction s with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a a' => simp

theorem map_lineCoeffConst {B' : Type} [CommRing B'] [Algebra k B'] (θ : B →ₐ[k] B') (s : B ⊗[k] Sq k r) :
    c0 k r B' (Algebra.TensorProduct.map θ (AlgHom.id k _) s) = θ (c0 k r B s) := by
  induction s with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a a' => simp

noncomputable def dir (l : Fin r → k) : Sq k r →ₐ[k] DualNumber k := TrivSqZeroExt.map (dotProductBilin k k l)

theorem map_dir (l : Fin r → k) (s : B ⊗[k] Sq k r) :
    Algebra.TensorProduct.map (AlgHom.id k B) (dir l) s =
      c0 k r B s ⊗ₜ[k] 1 + (∑ i, l i • co i s) ⊗ₜ[k] (DualNumber.eps : DualNumber k) := by
  induction s with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, smul_add, Finset.sum_add_distrib, add_tmul]; abel
  | tmul a x =>
    have : dir l x = x.fst • 1 + (∑ i, l i * x.snd i) • (DualNumber.eps : DualNumber k) := by
      ext <;> simp [dir, dotProduct]
    rw [Algebra.TensorProduct.map_tmul, this]
    simp [tmul_add, smul_smul, ← Finset.sum_smul, smul_tmul]

theorem linalg {d : ℕ} (M N P : Matrix (Fin d) (Fin d) k)
    (T : ((Fin d → k) × (Fin d → k)) →ₗ[k] ((Fin d → k) × (Fin d → k)))
    (hT : ∀ y, T y = (M.mulVec y.1, N.transpose.mulVec y.2 - P.transpose.mulVec y.1)) :
    ∃ (r s : ℕ) (u : Fin s → Fin d → k) (v : Fin r → Fin d → k), LinearIndependent k u ∧ LinearIndependent k v ∧
      (∀ j, M.mulVec (u j) = 0) ∧ (∀ i, N.mulVec (v i) = 0) ∧ (∀ i j, u j ⬝ᵥ P.mulVec (v i) = 0) ∧
      Module.finrank k (LinearMap.ker T) ≤ r + s := by
  let π := (LinearMap.fst k _ _).domRestrict (LinearMap.ker T)
  let U := LinearMap.range π
  let V := LinearMap.ker N.mulVecLin
  have hU : ∀ u ∈ U, ∃ φ, M.mulVec u = 0 ∧ N.transpose.mulVec φ = P.transpose.mulVec u := by
    rintro _ ⟨⟨y, hy⟩, rfl⟩
    rw [LinearMap.mem_ker, hT, Prod.mk_eq_zero, sub_eq_zero] at hy
    exact ⟨y.2, hy⟩
  refine ⟨_, _, fun j => (Module.finBasis k U j).1, fun i => (Module.finBasis k V i).1,
    (Module.finBasis k U).linearIndependent.map' U.subtype (Submodule.ker_subtype _),
    (Module.finBasis k V).linearIndependent.map' V.subtype (Submodule.ker_subtype _),
    fun j => (hU _ (Module.finBasis k U j).2).choose_spec.1, fun i => (Module.finBasis k V i).2, fun i j => ?_, ?_⟩
  · obtain ⟨φ, -, h⟩ := hU _ (Module.finBasis k U j).2
    have hv : N.mulVec (Module.finBasis k V i).1 = 0 := (Module.finBasis k V i).2
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, ← h, Matrix.mulVec_transpose,
      ← Matrix.dotProduct_mulVec, hv, dotProduct_zero]
  · have a1 := π.finrank_range_add_finrank_ker
    have a2 := N.mulVecLin.finrank_range_add_finrank_ker
    have a3 := N.transpose.mulVecLin.finrank_range_add_finrank_ker
    have a4 : Module.finrank k (LinearMap.range N.transpose.mulVecLin) =
      Module.finrank k (LinearMap.range N.mulVecLin) := Matrix.rank_transpose N
    have key : ∀ y : LinearMap.ker π, y.1.1.1 = 0 ∧ N.transpose.mulVec y.1.1.2 = 0 := fun y => by
      have h1 : y.1.1.1 = 0 := y.2
      have h2 := y.1.2
      rw [LinearMap.mem_ker, hT, Prod.mk_eq_zero, h1, Matrix.mulVec_zero, Matrix.mulVec_zero, sub_zero] at h2
      exact ⟨h1, h2.2⟩
    have a5 : Module.finrank k (LinearMap.ker π) ≤ Module.finrank k (LinearMap.ker N.transpose.mulVecLin) :=
      LinearMap.finrank_le_finrank_of_injective
        (f := (LinearMap.snd k _ _ ∘ₗ (LinearMap.ker T).subtype ∘ₗ (LinearMap.ker π).subtype).codRestrict _
          fun y => (key y).2) fun a b e => Subtype.ext (Subtype.ext (Prod.ext ((key a).1.trans (key b).1.symm)
            (congrArg Subtype.val e)))
    change _ ≤ Module.finrank k V + Module.finrank k U
    simp only [U, V]
    omega

end Coef

end PositivityTheory.Xgn.JetKernelRank

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

local notation "hm" φ:max => Formalism.L2.Pj.homAt (𝟙 (Sp _)) φ

namespace PositivityTheory.Xgn.JetKernelRank

noncomputable section

section Pair
open ReciprocityTheory.ChartRestriction.G.DVR

def AdSum {S : Scheme.{0}} {G : Over S} [GrpObj G] (f g : G ⟶ G) {K : Type} [Fintype K]
    (φ : K → ((G ⊗ G).left ⟶ G.left)) (ε : K → ℤ) : Prop :=
  ∀ {T : Over S} (x y : T ⟶ G) (U : Type) [CommGroup U] (h : (T.left ⟶ G.left) → U),
    ∏ i, h ((lift x y).left ≫ φ i) ^ ε i = h (x * (y ≫ g)).left * (h x.left)⁻¹ *
      (h (y ≫ g).left)⁻¹ * ((h ((x ≫ f) * y).left)⁻¹ * h (x ≫ f).left * h y.left)

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (hA : IsAbelianScheme G) {L : LB G.left}
  (hL : L.IsLB) {f g : G ⟶ G} [IsMonHom f] [IsMonHom g] {K : Type} [Fintype K]
  {φ : K → ((G ⊗ G).left ⟶ G.left)} {ε : K → ℤ} {w : LB.Gen (LB.LinComb L φ ε)} (hw : w.IsGen) (hW : AdSum f g φ ε)
include hA hL hw hW

theorem pair_ax {T : Over S} (x : T ⟶ G) {z : T.left} {J} (hJ : Good L z J) :
    val₂ w z J x 1 = val₂ w z J 1 1 ∧ val₂ w z J 1 x = val₂ w z J 1 1 := by
  have hp := (GlobalTheory.globalFns_holds _ _ hA).2
  constructor
  · have := GlobalTheory.CubeDescent.val_eq_of_section hL hw (toUnit G) η[G] (toUnit_unique _ _) hp
      (lift (𝟙 G) 1) (lift 1 1) (fun U _ h => by
        rw [hW, hW]
        simp only [MonObj.one_comp, _root_.mul_one]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel) (fun y J _ => by congr 2; simp [Hom.one_def]) x z J hJ
    simpa only [val₂, comp_lift, Category.comp_id, MonObj.comp_one] using this
  · have := GlobalTheory.CubeDescent.val_eq_of_section hL hw (toUnit G) η[G] (toUnit_unique _ _) hp
      (lift 1 (𝟙 G)) (lift 1 1) (fun U _ h => by
        rw [hW, hW]
        simp only [MonObj.one_comp, _root_.one_mul]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel) (fun y J _ => by congr 2; simp [Hom.one_def]) x z J hJ
    simpa only [val₂, comp_lift, Category.comp_id, MonObj.comp_one] using this

omit [IsMonHom g] in
theorem pair_mul {T : Over S} (x y v : T ⟶ G) (hx : x ≫ f = 1) (hv : v ≫ g = 1) {z : T.left} {J} (hJ : Good L z J) :
    val₂ w z J (y * x) v * val₂ w z J 1 v = val₂ w z J y v * val₂ w z J x v := by
  have := ratio_const GlobalTheory.globalFns_holds hA hL (fun U _ h => by
      refine (hW _ _ U h).trans (Eq.trans ?_ (hW _ _ U h).symm)
      simp only [MonObj.mul_comp, Category.assoc, hx, hv, MonObj.comp_one, _root_.mul_one, mul_inv_cancel])
    (pullGen_isGen _ _ _ _ hw (lift (snd T G * (fst T G ≫ x)) (fst T G ≫ v)).left)
    (pullGen_isGen _ _ _ _ hw (lift (snd T G) (fst T G ≫ v)).left) (𝟙 T) y hJ
  simpa only [val_ros _ _ hJ, MonObj.comp_mul, lift_snd, lift_fst_assoc, Category.id_comp, _root_.one_mul] using this

theorem pair_nondeg [Flat f.left] [Surjective f.left] [QuasiCompact f.left] (hK : Out.KTriv G L)
    {R : Type} [CommRing R] [IsLocalRing R] (s : Sp R ⟶ S) (v : Over.mk s ⟶ G) (hv : v ≫ g = 1)
    (h : ∀ (T : Over S) (ρ : T ⟶ Over.mk s) (x : T ⟶ G), x ≫ f = 1 → ∀ z J, Good L z J →
      val₂ w z J x (ρ ≫ v) = val₂ w z J 1 (ρ ≫ v)) : v = 1 := by
  let T : Over S := Over.mk s
  let π : T ⊗ G ⟶ T ⊗ G := 𝟙 T ⊗ₘ f
  have : IsIso (𝟙 T : T ⟶ T).left := inferInstanceAs (IsIso (𝟙 T.left))
  have : Flat π.left := GlobalTheory.AbelianQuotient.flat_tensorHom _ _
  have : Surjective π.left := GlobalTheory.AbelianQuotient.surjective_tensorHom _ _
  have : QuasiCompact π.left := GlobalTheory.AbelianQuotient.quasiCompact_tensorHom _ _
  have p₁ : π ≫ fst T G = fst T G := by simp [π]
  have p₂ : π ≫ snd T G = snd T G ≫ f := by simp [π]
  let ψ : Fin 4 → ((T ⊗ G).left ⟶ G.left) :=
    ![(snd T G * (fst T G ≫ v)).left, (snd T G).left, (fst T G ≫ v).left, (1 : T ⊗ G ⟶ G).left]
  obtain ⟨σ, hσ, vσ⟩ := exists_gen hL (φ' := fun k => π.left ≫ ψ k) (ε' := ![1, -1, -1, 1]) (fun U _ h => by
      refine (prod_neg _ _ (hW (snd T G) (fst T G ≫ v) U h)).trans ?_
      rw [Fin.prod_univ_four]
      show _ = h (π ≫ (snd T G * (fst T G ≫ v))).left ^ (1 : ℤ) * h (π ≫ snd T G).left ^ (-1 : ℤ) *
        h (π ≫ fst T G ≫ v).left ^ (-1 : ℤ) * h (π ≫ (1 : T ⊗ G ⟶ G)).left ^ (1 : ℤ)
      rw [MonObj.comp_mul, MonObj.comp_one, ← Category.assoc π, p₁, p₂, Category.assoc, hv, MonObj.comp_one,
        _root_.mul_one]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
      module)
    (LB.invGen L _ _ (LB.pullGen L _ _ w (lift (snd T G) (fst T G ≫ v)).left))
    (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ hw _))
  obtain ⟨u, hu⟩ := GlobalTheory.CubeDescent.exists_gen_descend hL π.left ψ _ σ hσ fun Z g₁ g₂ z J hJ e => by
    let T' : Over S := Over.mk (g₂ ≫ (T ⊗ G).hom)
    let k₂ : T' ⟶ T ⊗ G := Over.homMk g₂ rfl
    let k₁ : T' ⟶ T ⊗ G := Over.homMk g₁ (by
      change g₁ ≫ (T ⊗ G).hom = g₂ ≫ (T ⊗ G).hom
      rw [← Over.w π, reassoc_of% e])
    have e' : k₁ ≫ π = k₂ ≫ π := Over.OverMorphism.ext e
    have e₁ : k₁ ≫ fst T G = k₂ ≫ fst T G := by simpa only [Category.assoc, p₁] using e' =≫ fst _ _
    have e₂ : (k₁ ≫ snd T G) ≫ f = (k₂ ≫ snd T G) ≫ f := by simpa only [Category.assoc, p₂] using e' =≫ snd _ _
    rw [vσ _ _ z J hJ, vσ _ _ z J hJ, val_inv, val_inv]
    refine congrArg (·⁻¹) ((val_ros w k₁ hJ _ _).trans (Eq.trans ?_ (val_ros w k₂ hJ _ _).symm))
    have hx : ((k₂ ≫ snd T G)⁻¹ * (k₁ ≫ snd T G)) ≫ f = 1 := by
      rw [MonObj.mul_comp, GrpObj.inv_comp, e₂, inv_mul_cancel]
    have a := pair_mul hA hL hw hW _ (k₂ ≫ snd T G) ((k₂ ≫ fst T G) ≫ v) hx
      (by rw [Category.assoc, hv, MonObj.comp_one]) hJ
    rw [mul_inv_cancel_left, h T' _ _ hx z J hJ] at a
    rw [← Category.assoc, ← Category.assoc, e₁]
    exact mul_right_cancel a
  obtain ⟨c, hc⟩ := DVR.exists_gen_of_local (V := R) L hL (![v.left, (1 : T ⟶ G).left] : Fin 2 → _) ![1, -1]
  have s₀ : ψ 0 = (lift (fst T G ≫ v) (snd T G) ≫ μ[G]).left := by
    show (snd T G * (fst T G ≫ v)).left = ((fst T G ≫ v) * snd T G).left
    rw [mul_comm]
  have s₃ : ψ 3 = (fst T G).left ≫ (1 : T ⟶ G).left :=
    congrArg (fun q : T ⊗ G ⟶ G => q.left) (MonObj.comp_one (fst T G)).symm
  obtain ⟨w', hw', -⟩ := exists_gen hL
    (φ' := (![(lift (fst T G ≫ v) (snd T G) ≫ μ[G]).left, (snd T G).left] : Fin 2 → _)) (ε' := ![1, -1])
    (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans ?_
      rw [Fin.prod_univ_four, Fin.prod_univ_two, Fin.prod_univ_two]
      show h (ψ 0) ^ (1 : ℤ) * h (snd T G).left ^ (-1 : ℤ) * h ((fst T G).left ≫ v.left) ^ (-1 : ℤ) *
        h (ψ 3) ^ (1 : ℤ) * (h ((fst T G).left ≫ v.left) ^ (1 : ℤ) *
        h ((fst T G).left ≫ (1 : T ⟶ G).left) ^ (-1 : ℤ)) =
        h (lift (fst T G ≫ v) (snd T G) ≫ μ[G]).left ^ (1 : ℤ) * h (snd T G).left ^ (-1 : ℤ)
      rw [s₀, s₃]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module)
    (LB.mulGen L _ _ _ _ u (LB.pullGen L _ _ c (fst T G).left))
    (mulGen_isGen _ _ _ _ _ _ _ hu (pullGen_isGen _ _ _ _ hc _))
  exact hK R s v fun _ => ⟨⊤, trivial, gen_chartPull (chartPullPull _ _ _ rfl) w' hw'⟩

omit hA in
theorem pair_exists {T : Over S} (x v : T ⟶ G) (hx : x ≫ f = 1) (hv : v ≫ g = 1) :
    ∃ u : Γ(T.left, ⊤)ˣ, ∀ (T' : Over S) (ρ : T' ⟶ T) z J, Good L z J →
      val₂ w z J (ρ ≫ x) (ρ ≫ v) = gm ρ.left z ⊤ u := by
  obtain ⟨u, hu⟩ := Formalism.MainNotions.ModuliIntegralCharts.H1.GermB.exists_ratio L hL (fun U _ h => by
      refine (hW x v U h).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      rw [hx, hv, _root_.mul_one, _root_.one_mul]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_one]
      abel) _ (pullGen_isGen _ _ _ _ hw (lift x v).left) (LB.oneGen L) (LB.isGen_oneGen L)
  refine ⟨u, fun T' ρ z J hJ => ?_⟩
  have := hu _ ρ.left z J hJ
  rwa [val_ros _ _ hJ, val_one, _root_.mul_one] at this

end Pair

section Ker
open Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.GermD TensorProduct

variable {k : Type} [Field k]

abbrev Ov (k : Type) [Field k] (R : Type) [CommRing R] [Algebra k R] : Over (Sp k) := overAt (𝟙 (Sp k)) R

theorem hm_inj {A B : Type} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] {φ ψ : A →ₐ[k] B}
    (h : hm φ = hm ψ) : φ = ψ := by
  have e : Spec.map (CommRingCat.ofHom (φ : A →+* B)) = Spec.map (CommRingCat.ofHom (ψ : A →+* B)) :=
    congrArg (fun q => q.left) h
  exact AlgHom.coe_ringHom_injective (congrArg CommRingCat.Hom.hom (Spec.map_injective e))

theorem hm_surj {A B : Type} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] (y : Ov k B ⟶ Ov k A) :
    ∃ φ : A →ₐ[k] B, hm φ = y := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (R := CommRingCat.of A) (S := CommRingCat.of B) y.left
  have e : y.left ≫ spMap (algebraMap k A) ≫ 𝟙 _ = spMap (algebraMap k B) ≫ 𝟙 _ := Over.w y
  rw [Category.comp_id, Category.comp_id, ← hφ, spMap, ← Spec.map_comp] at e
  have e' := congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  exact ⟨⟨φ.hom, fun c => DFunLike.congr_fun e' c⟩, Over.OverMorphism.ext hφ⟩

theorem exists_tensor {A B : Type} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] {T : Over (Sp k)}
    (y : T ⟶ Ov k A) (ρ : T ⟶ Ov k B) : ∃ τ : T ⟶ Ov k (A ⊗[k] B),
      τ ≫ hm Algebra.TensorProduct.includeLeft = y ∧ τ ≫ hm Algebra.TensorProduct.includeRight = ρ := by
  have e₁ : y.left ≫ spMap (algebraMap k A) ≫ 𝟙 _ = T.hom := Over.w y
  have e₂ : ρ.left ≫ spMap (algebraMap k B) ≫ 𝟙 _ = T.hom := Over.w ρ
  rw [Category.comp_id] at e₁ e₂
  let l := pullback.lift y.left ρ.left (e₁.trans e₂.symm) ≫ (pullbackSpecIso k A B).hom
  have l₁ : l ≫ Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) = y.left := by
    rw [Category.assoc, pullbackSpecIso_hom_fst, pullback.lift_fst]
  have l₂ : l ≫ Spec.map (CommRingCat.ofHom (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight : B →ₐ[k] A ⊗[k] B))) = ρ.left := by
    rw [Category.assoc, pullbackSpecIso_hom_snd, pullback.lift_snd]
  refine ⟨Over.homMk l ?_, Over.OverMorphism.ext l₁, Over.OverMorphism.ext l₂⟩
  refine Eq.trans ?_ ((congrArg (· ≫ spMap (algebraMap k A)) l₁).trans e₁)
  have := Over.w (hm (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] B))
  change _ ≫ _ ≫ 𝟙 _ = _ at this
  rw [Category.comp_id] at this
  exact (congrArg (l ≫ ·) this.symm).trans (Category.assoc _ _ _).symm

variable {G : Over (Sp k)} [GrpObj G] {f : G ⟶ G} {A : Type} [CommRing A] [Algebra k A]

theorem exists_ker (i : Sp A ⟶ G.left) (hp : IsPullback i (spMap (algebraMap k A)) f.left (η[G]).left) :
    ∃ κ : Ov k A ⟶ G, κ ≫ f = 1 ∧ ∀ (T : Over (Sp k)) (x : T ⟶ G), x ≫ f = 1 → ∃! y : T ⟶ Ov k A, y ≫ κ = x := by
  have e : (η[G]).left ≫ G.hom = 𝟙 _ := Over.w _
  have hi : i ≫ G.hom = spMap (algebraMap k A) ≫ 𝟙 _ := by
    rw [← Over.w f, ← Category.assoc, hp.w, Category.assoc, e]; rfl
  have one : ∀ T : Over (Sp k), (1 : T ⟶ G).left = T.hom ≫ (η[G]).left := fun T => by
    rw [Hom.one_def, Over.comp_left, Over.toUnit_left]
  refine ⟨Over.homMk i hi, Over.OverMorphism.ext ?_, fun T x hx => ?_⟩
  · rw [one]
    exact hp.w.trans (congrArg (· ≫ _) (Category.comp_id _).symm)
  · have hx' : x.left ≫ f.left = T.hom ≫ (η[G]).left := (congrArg (fun q => q.left) hx).trans (one T)
    refine ⟨Over.homMk (hp.lift _ _ hx') ((Category.assoc _ _ _).symm.trans
      ((Category.comp_id _).trans (hp.lift_snd _ _ _))), Over.OverMorphism.ext (hp.lift_fst _ _ _), fun y hy => ?_⟩
    refine Over.OverMorphism.ext (hp.hom_ext ((congrArg (fun q => q.left) hy).trans (hp.lift_fst _ _ _).symm) ?_)
    have := Over.w y
    change _ ≫ _ ≫ 𝟙 _ = _ at this
    rw [Category.comp_id] at this
    exact this.trans (hp.lift_snd _ _ _).symm

variable {κ : Ov k A ⟶ G} (h₁ : κ ≫ f = 1)
  (h₂ : ∀ (T : Over (Sp k)) (x : T ⟶ G), x ≫ f = 1 → ∃! y : T ⟶ Ov k A, y ≫ κ = x)
include h₁ h₂

theorem pt_inj {R : Type} [CommRing R] [Algebra k R] {φ ψ : A →ₐ[k] R} (h : hm φ ≫ κ = hm ψ ≫ κ) : φ = ψ :=
  hm_inj ((h₂ _ (hm ψ ≫ κ) (by rw [Category.assoc, h₁, MonObj.comp_one])).unique h rfl)

omit h₁ in
theorem pt_surj {R : Type} [CommRing R] [Algebra k R] (x : Ov k R ⟶ G) (h : x ≫ f = 1) :
    ∃ φ : A →ₐ[k] R, hm φ ≫ κ = x := by
  obtain ⟨y, hy, -⟩ := h₂ _ x h
  obtain ⟨φ, rfl⟩ := hm_surj y
  exact ⟨φ, hy⟩

omit h₁ in
theorem flat_surj [IsAlgClosed k] [Module.Finite k A] [IsMonHom f] (hA : IsAbelianScheme G) :
    Flat f.left ∧ Surjective f.left ∧ QuasiCompact f.left := by
  have := hA.proper
  have := hA.smooth
  have := hA.geomConnected
  have : IsProper (f.left ≫ G.hom) := by rw [Over.w]; infer_instance
  have : IsProper f.left := .of_comp _ G.hom
  have : LocallyQuasiFinite f.left := GlobalTheory.locallyQuasiFinite_of_finite_geometric_ker _ G G f inferInstance
    inferInstance inferInstance fun Ω _ _ t => by
      obtain ⟨β, rfl⟩ : ∃ β : k →+* Ω, t = spMap β ≫ 𝟙 _ := by
        obtain ⟨β, rfl⟩ := Spec.map_surjective (R := CommRingCat.of k) (S := CommRingCat.of Ω) t
        exact ⟨β.hom, (Category.comp_id _).symm⟩
      let _ := β.toAlgebra
      choose φ hφ using fun x : {x : Ov k Ω ⟶ G // x ≫ f = 1} => pt_surj h₂ x.1 x.2
      exact Finite.of_injective φ fun a b e => Subtype.ext ((hφ a).symm.trans (e ▸ hφ b))
  have : IsFinite f.left := .of_isProper_of_locallyQuasiFinite _
  have := GlobalTheory.grpObj_geometricallyIntegral_of_smooth _ G
  have : IsIntegral G.left := GeometricallyIntegral.isIntegral_of_subsingleton G.hom
  have := GlobalTheory.flat_and_surjective_of_isFinite_grpEnd k G f
  exact ⟨this.1, this.2, inferInstance⟩

open Algebra.TensorProduct in
theorem ker_dvd [IsCommMonObj G] [IsMonHom f] [IsAlgClosed k] [Module.Finite k A] (p : ℕ) [Fact p.Prime] [CharP k p]
    {r s : ℕ} (Δ : A →ₐ[k] A ⊗[k] A) (hΔ : hm Δ ≫ κ = (hm includeLeft ≫ κ) * (hm includeRight ≫ κ))
    (ε : A →ₐ[k] k) (hε : hm ε ≫ κ = 1)
    (u : Fin r → A) (hf : ∀ i, Δ (u i) = u i ⊗ₜ[k] 1 + 1 ⊗ₜ[k] u i) (hf0 : ∀ i, ε (u i) = 0)
    (hfi : LinearIndependent k u)
    (D : Fin s → A →ₗ[k] k) (hD : ∀ i a b, D i (a * b) = ε a * D i b + D i a * ε b)
    (hli : LinearIndependent k D) (h0 : ∀ i j, D i (u j) = 0) : p ^ (r + s) ∣ Module.finrank k A := by
  obtain ⟨σ, hσ⟩ := pt_surj h₂ κ⁻¹ (by rw [GrpObj.inv_comp, h₁, inv_one])
  have mul : ∀ {R : Type} [CommRing R] [Algebra k R] (θ : A ⊗[k] A →ₐ[k] R), hm (θ.comp Δ) ≫ κ =
      (hm (θ.comp includeLeft) ≫ κ) * (hm (θ.comp includeRight) ≫ κ) := fun θ => by
    rw [← homAt_comp, Category.assoc, hΔ, MonObj.comp_mul, ← Category.assoc, ← Category.assoc, homAt_comp, homAt_comp]
  have one : ∀ {R : Type} [CommRing R] [Algebra k R] (θ : k →ₐ[k] R), hm (θ.comp ε) ≫ κ = 1 := fun θ => by
    rw [← homAt_comp, Category.assoc, hε, MonObj.comp_one]
  have hid : hm (AlgHom.id k A) ≫ κ = κ := by rw [homAt_id, Category.id_comp]
  have cg : ∀ {R : Type} [CommRing R] [Algebra k R] {φ ψ : A →ₐ[k] R}, φ = ψ → hm φ ≫ κ = hm ψ ≫ κ :=
    fun h => by rw [h]
  letI : Bialgebra k A := Bialgebra.ofAlgHom Δ ε
    (pt_inj h₁ h₂ (by
      let a := (Algebra.TensorProduct.assoc k k k A A A).toAlgHom
      have e₁ : (a.comp (Algebra.TensorProduct.map Δ (.id k A))).comp includeLeft =
        (a.comp includeLeft).comp Δ := by ext x; simp
      have e₂ : (Algebra.TensorProduct.map (.id k A) Δ).comp includeRight =
        (includeRight : A ⊗[k] A →ₐ[k] A ⊗[k] (A ⊗[k] A)).comp Δ := by ext x; simp
      rw [← AlgHom.comp_assoc, mul, mul, e₁, e₂, mul, mul, _root_.mul_assoc]
      exact congrArg₂ (· * ·) (cg (by ext x; simp [a, Algebra.TensorProduct.one_def])) (congrArg₂ (· * ·)
        (cg (by ext x; simp [a, Algebra.TensorProduct.one_def])) (cg (by ext x; simp [a, Algebra.TensorProduct.one_def])))))
    (pt_inj h₁ h₂ (by
      have e₁ : (Algebra.TensorProduct.map ε (.id k A)).comp includeLeft =
        (includeLeft : k →ₐ[k] k ⊗[k] A).comp ε := by ext x; simp
      rw [mul, e₁, one, _root_.one_mul]
      exact cg (by ext x; simp)))
    (pt_inj h₁ h₂ (by
      have e₁ : (Algebra.TensorProduct.map (.id k A) ε).comp includeRight =
        (includeRight : k →ₐ[k] A ⊗[k] k).comp ε := by ext x; simp
      rw [mul, e₁, one, _root_.mul_one]
      exact cg (by ext x; simp)))
  letI : HopfAlgebra k A := HopfAlgebra.ofAlgHom σ
    (pt_inj h₁ h₂ (by
      refine (mul _).trans (Eq.trans ?_ (one _).symm)
      exact (congrArg₂ (· * ·) ((cg (Algebra.TensorProduct.lift_comp_includeLeft _ _ fun _ _ => Commute.all _ _)).trans hσ)
        ((cg (Algebra.TensorProduct.lift_comp_includeRight _ _ fun _ _ => Commute.all _ _)).trans hid)).trans
        (inv_mul_cancel _)))
    (pt_inj h₁ h₂ (by
      refine (mul _).trans (Eq.trans ?_ (one _).symm)
      exact (congrArg₂ (· * ·) ((cg (Algebra.TensorProduct.lift_comp_includeLeft _ _ fun _ _ => Commute.all _ _)).trans hid)
        ((cg (Algebra.TensorProduct.lift_comp_includeRight _ _ fun _ _ => Commute.all _ _)).trans hσ)).trans
        (mul_inv_cancel _)))
  have : Coalgebra.IsCocomm k A := ⟨by
    have : (Algebra.TensorProduct.comm k A A).toAlgHom.comp Δ = Δ := pt_inj h₁ h₂ (by
      rw [mul, hΔ, mul_comm]
      exact congrArg₂ (· * ·) (cg (by ext x; simp)) (cg (by ext x; simp)))
    exact congr(($this).toLinearMap)⟩
  exact hopf_dvd p u hf hf0 hfi D hD hli h0

end Ker

section Eval
open MvPolynomial Formalism.L2.Pj

variable {k R : Type} [CommRing k] [CommRing R] [Algebra k R]

theorem aeval_one {I : Type} [Fintype I] [DecidableEq I] (c : I → R) (hc : ∀ i j, c i * c j = 0) (P : MvPolynomial I k) :
    aeval c P = algebraMap k R (coeff 0 P) + ∑ i, coeff (Finsupp.single i 1) P • c i := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [coeff_C, (Finsupp.single_ne_zero.2 one_ne_zero).symm]
  | add P Q hP hQ => simp only [map_add, hP, hQ, coeff_add, add_smul, Finset.sum_add_distrib]; abel
  | mul_X P n hP =>
    rw [map_mul, hP, aeval_X, add_mul, Finset.sum_mul]
    simp only [smul_mul_assoc, hc, smul_zero, Finset.sum_const_zero, add_zero, coeff_mul_X']
    rw [Finset.sum_eq_single n]
    · simp [Algebra.smul_def]
    · intro b _ hb; simp [Finsupp.single_apply, hb, hb.symm]
    · simp

theorem aeval_two {d : ℕ} (a b : Fin d → R) (ha : ∀ i j, a i * a j = 0) (hb : ∀ i j, b i * b j = 0)
    (P : MvPolynomial (Fin 2 × Fin d) k) :
    aeval (fun q : Fin 2 × Fin d => ![a, b] q.1 q.2) P = algebraMap k R (coeff 0 P) +
      ∑ i, coeff (Finsupp.single (0, i) 1) P • a i + ∑ j, coeff (Finsupp.single (1, j) 1) P • b j +
      ∑ i, ∑ j, coeff (Finsupp.single (0, i) 1 + Finsupp.single (1, j) 1) P • (a i * b j) := by
  have h3 : ∀ i j l, a i * b j * a l = 0 := fun i j l => by rw [mul_right_comm, ha, zero_mul]
  have h4 : ∀ i j l, a i * b j * b l = 0 := fun i j l => by rw [_root_.mul_assoc, hb, mul_zero]
  induction P using MvPolynomial.induction_on with
  | C a =>
    have : ∀ i j : Fin d, ¬ (0 : Fin 2 × Fin d →₀ ℕ) = Finsupp.single (0, i) 1 + Finsupp.single (1, j) 1 := fun i j h => by
      simpa using DFunLike.congr_fun h (0, i)
    simp [coeff_C, (Finsupp.single_ne_zero.2 one_ne_zero).symm, this]
  | add P Q hP hQ => simp only [map_add, hP, hQ, coeff_add, add_smul, Finset.sum_add_distrib]; abel
  | mul_X P n hP =>
    rw [map_mul, hP, aeval_X]
    obtain ⟨l, n⟩ := n
    fin_cases l
    · simp only [add_mul, Finset.sum_mul, smul_mul_assoc, ha, h3, smul_zero, Finset.sum_const_zero, add_zero,
        coeff_mul_X', Fin.zero_eta, Matrix.cons_val_zero]
      rw [Finset.sum_eq_single n (f := fun i => _ • a i), Finset.sum_eq_single n (f := fun i => ∑ j, _ • (a i * b j))]
      · simp [Algebra.smul_def, Finsupp.single_apply, mul_comm]
      · intro b _ hb; simp [Finsupp.single_apply, hb, hb.symm]
      · simp
      · intro b _ hb; simp [Finsupp.single_apply, hb, hb.symm]
      · simp
    · simp only [add_mul, Finset.sum_mul, smul_mul_assoc, hb, h4, smul_zero, Finset.sum_const_zero, add_zero,
        coeff_mul_X', Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [Finset.sum_comm, Finset.sum_eq_single n (f := fun i => _ • b i),
        Finset.sum_eq_single n (f := fun j => ∑ i, _ • (a i * b j))]
      · simp [Algebra.smul_def, Finsupp.single_apply, mul_comm]
      · intro b _ hb; simp [Finsupp.single_apply, hb, hb.symm]
      · simp
      · intro b _ hb; simp [Finsupp.single_apply, hb, hb.symm]
      · simp

theorem span_sq {I : Type} (c : I → R) (hc : ∀ i j, c i * c j = 0) : Ideal.span (Set.range c) ^ 2 = ⊥ := by
  rw [pow_two, Ideal.span_mul_span', Ideal.span_eq_bot]
  rintro _ ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
  exact hc i j

variable (k) in

def th1 {d : ℕ} (m : ℕ) (a : Fin d → R) (ha : ∀ i j, a i * a j = 0) : Jet k (Fin 1 × Fin d) (m + 1) →ₐ[k] R :=
  liftJet (aeval fun q => a q.2) (by
    simp only [aeval_X]
    exact le_bot_iff.1 ((Ideal.pow_le_pow_right (by omega)).trans (span_sq _ fun i j => ha _ _).le))

variable (k) in

def th2 {d : ℕ} (a b : Fin d → R) (ha : ∀ i j, a i * a j = 0) (hb : ∀ i j, b i * b j = 0) :
    Jet k (Fin 2 × Fin d) 3 →ₐ[k] R :=
  liftJet (aeval fun q => ![a, b] q.1 q.2) (by
    simp only [aeval_X]
    have : Ideal.span (Set.range fun q : Fin 2 × Fin d => ![a, b] q.1 q.2) ≤
        Ideal.span (Set.range a) ⊔ Ideal.span (Set.range b) := Ideal.span_le.2 (by
      rintro _ ⟨⟨l, i⟩, rfl⟩
      fin_cases l
      · exact Ideal.mem_sup_left (Ideal.subset_span ⟨i, rfl⟩)
      · exact Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩))
    refine le_bot_iff.1 ((Ideal.pow_right_mono this _).trans
      ((Ideal.sup_pow_add_le_pow_sup_pow (n := 2) (m := 2)).trans ?_))
    rw [span_sq _ ha, span_sq _ hb, bot_sup_eq])

theorem first_jet_mk {d : ℕ} (m : ℕ) (a : Fin d → R) (ha : ∀ i j, a i * a j = 0) (P) :
    th1 k m a ha (Ideal.Quotient.mk _ P) = aeval (fun q => a q.2) P := rfl

theorem second_jet_mk {d : ℕ} (a b : Fin d → R) (ha : ∀ i j, a i * a j = 0) (hb : ∀ i j, b i * b j = 0) (P) :
    th2 k a b ha hb (Ideal.Quotient.mk _ P) = aeval (fun q => ![a, b] q.1 q.2) P := rfl

theorem subst_X {κ κ' : Type} (m : ℕ) (φ : κ → MvPolynomial κ' k) (s : κ) (h : constantCoeff (φ s) = 0) :
    jetSubstP m φ (Ideal.Quotient.mk _ (X s)) = Ideal.Quotient.mk _ (φ s) := by
  rw [jetSubstP, Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.jetMap_mk, aeval_X, h, map_zero, sub_zero]

theorem aeval_trunc {d : ℕ} (m : ℕ) (a : Fin d → R) (ha : ∀ i j, a i * a j = 0) (φ : Germ.Pt k 1 d)
    (hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0) (j : Fin d) :
    aeval (fun q : Fin 1 × Fin d => a q.2) (psTrunc (m + 1) (φ j)) = ∑ i, lin φ 1 j i • a i := by
  rw [aeval_one _ (fun i j => ha _ _), Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun.coeff_psTrunc _ _ _ (by simp),
    MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hφ, map_zero, zero_add, Fintype.sum_prod_type, Fin.sum_univ_one]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun.coeff_psTrunc _ _ _ (by simp)]
  rfl

theorem second_jet_expansion {d : ℕ} (a b : Fin d → R) (ha : ∀ i j, a i * a j = 0) (hb : ∀ i j, b i * b j = 0)
    (f : Germ.PS k 2 d) : ∃ α β : Fin d → k, th2 k a b ha hb (psJet 3 f) =
      algebraMap k R (MvPowerSeries.constantCoeff f) + ∑ i, α i • a i + ∑ j, β j • b j +
      ∑ i, ∑ j, bil f 1 1 i j • (a i * b j) := by
  refine ⟨fun i => coeff (Finsupp.single (0, i) 1) (psTrunc 3 f), fun i => coeff (Finsupp.single (1, i) 1) (psTrunc 3 f),
    (aeval_two a b ha hb _).trans ?_⟩
  rw [Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun.coeff_psTrunc _ _ _ (by simp), MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun.coeff_psTrunc _ _ _ (by simp)]
  rfl

end Eval

section Chart
open Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.GermD ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)] {k : Type} [Field k]
  {t : SAB H (Sp k)} {d : ℕ} (g : GermAt t (𝟙 (Sp k)) d) {R : Type} [CommRing R] [Algebra k R]

def cp (a : Fin d → R) (ha : ∀ i j, a i * a j = 0) : Ov k R ⟶ t.G := hm (th1 k 2 a ha) ≫ g.x 3

theorem cp_congr {a b : Fin d → R} (ha : ∀ i j, a i * a j = 0) (hb : ∀ i j, b i * b j = 0) (h : a = b) :
    cp g a ha = cp g b hb := by subst h; rfl

theorem cp_nat {R' : Type} [CommRing R'] [Algebra k R'] (θ : R →ₐ[k] R') (a : Fin d → R) (ha : ∀ i j, a i * a j = 0)
    (b : Fin d → R') (hb : ∀ i j, b i * b j = 0) (h : ∀ i, θ (a i) = b i) : hm θ ≫ cp g a ha = cp g b hb := by
  rw [cp, cp, ← Category.assoc, homAt_comp]
  congr 2
  exact jet_hom_ext fun s => by simp [first_jet_mk, h]

theorem first_jet_zero (m : ℕ) (a : Fin d → R) (ha : ∀ i j, a i * a j = 0) (h : a = 0) :
    hm (th1 k m a ha) ≫ g.x (m + 1) = 1 := by
  have : th1 k m a ha = (Algebra.ofId k R).comp jetAug := jet_hom_ext fun s => by
    rw [AlgHom.comp_apply, GermB.jetAug_X]; simp [first_jet_mk, h]
  rw [this, ← homAt_comp, Category.assoc, g.chart.zero, MonObj.comp_one]

theorem cp_zero (a : Fin d → R) (ha : ∀ i j, a i * a j = 0) (h : a = 0) : cp g a ha = 1 := first_jet_zero g 2 a ha h

theorem cp_act (c : 𝓞 E) (a : Fin d → R) (ha : ∀ i j, a i * a j = 0) (h : ∀ j, ∑ i, rho g.B c j i • a i = 0) :
    cp g a ha ≫ t.act.act c = 1 := by
  rw [cp, Category.assoc, g.chart.act, ← Category.assoc, homAt_comp, ← cp_zero g (0 : Fin d → R) (by simp) rfl, cp]
  congr 2
  refine jet_hom_ext fun s => ?_
  rw [AlgHom.comp_apply, subst_X, first_jet_mk, aeval_trunc 2 a ha _ (g.B.A.const c), first_jet_mk]
  · exact (h s.2).trans (MvPolynomial.aeval_X (fun q : Fin 1 × Fin d => (0 : Fin d → R) q.2) s).symm
  · exact (FBIdPh.cc_psTrunc _ _).trans (g.B.A.const _ _)

theorem first_jet_truncate (m : ℕ) (a : Fin d → R) (ha : ∀ i j, a i * a j = 0) :
    hm (th1 k (m + 1) a ha) ≫ g.x (m + 1 + 1) = hm (th1 k m a ha) ≫ g.x (m + 1) := by
  have : th1 k (m + 1) a ha = (th1 k m a ha).comp jetTrunc := jet_hom_ext fun s => by
    rw [AlgHom.comp_apply, jetTrunc_mk, first_jet_mk, first_jet_mk]
  rw [this, ← homAt_comp, Category.assoc, g.chart.trunc]

theorem cp_eq (a : Fin d → R) (ha : ∀ i j, a i * a j = 0) : cp g a ha = hm (th1 k 0 a ha) ≫ g.x 1 :=
  (first_jet_truncate g 1 a ha).trans (first_jet_truncate g 0 a ha)

theorem jet_inj (hs : ∀ a : 𝓞 E, star a = H.bar a) (a : Fin d → Jet k Unit 1) (ha : ∀ i j, a i * a j = 0)
    (h0 : ∀ i, (jetAug : Jet k Unit 1 →ₐ[k] k) (a i) = 0) (h : cp g a ha = 1) : a = 0 := by
  have h3 := ((GlobalTheory.CompanionTheory.Ar.GermUniv.germ_chart_universal E H hs _ t k _ d g).2 Unit 1 1 (MonObj.comp_one _)).unique
    (y₁ := th1 k 0 a ha) (y₂ := th1 k 0 0 (by simp))
    ⟨fun q => by rw [first_jet_mk, MvPolynomial.aeval_X, h0], h.symm.trans (cp_eq g a ha)⟩
    ⟨fun q => by rw [first_jet_mk, MvPolynomial.aeval_X]; exact map_zero _, (first_jet_zero g 0 _ _ rfl).symm⟩
  funext i
  have h4 := DFunLike.congr_fun h3 (Ideal.Quotient.mk _ (MvPolynomial.X (0, i)))
  rwa [first_jet_mk, first_jet_mk, MvPolynomial.aeval_X, MvPolynomial.aeval_X] at h4

theorem exists_dual (k : Type) [Field k] : ∃ (x : Jet k Unit 1) (θ : DualNumber k →ₐ[k] Jet k Unit 1),
    x * x = 0 ∧ (∀ c : k, θ (TrivSqZeroExt.inr c) = c • x) ∧ (jetAug : Jet k Unit 1 →ₐ[k] k) x = 0 ∧
      ∀ c : k, c • x = 0 → c = 0 := by
  have hx : (Ideal.Quotient.mk _ (MvPolynomial.X ()) : Jet k Unit 1) * Ideal.Quotient.mk _ (MvPolynomial.X ()) = 0 := by
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, ← pow_two]
    exact Ideal.pow_mem_pow (X_mem_orig _) 2
  refine ⟨_, DualNumber.lift ⟨(Algebra.ofId _ _, _), hx, fun _ => Commute.all _ _⟩, hx, fun c => ?_,
    GermB.jetAug_X _ _, fun c hc => ?_⟩
  · rw [DualNumber.lift_apply_apply, TrivSqZeroExt.fst_inr, map_zero, zero_add, TrivSqZeroExt.snd_inr,
      Algebra.smul_def, Algebra.ofId_apply]
  · have h5 : (jetTan () : Jet k Unit (0 + 1) →ₐ[k] DualNumber k) (Ideal.Quotient.mk _ (MvPolynomial.X ())) =
        DualNumber.eps := (MvPolynomial.aeval_X _ _).trans (if_pos rfl)
    have h4 := congrArg (jetTan () : Jet k Unit (0 + 1) →ₐ[k] DualNumber k) hc
    rw [map_smul, h5, map_zero] at h4
    simpa using congrArg TrivSqZeroExt.snd h4

theorem cp_inj (hs : ∀ a : 𝓞 E, star a = H.bar a) (w : Fin d → k) (ha)
    (h : cp g (fun i => (TrivSqZeroExt.inr (w i) : DualNumber k)) ha = 1) : w = 0 := by
  obtain ⟨x, θ, hx, hθ, h0, hi⟩ := exists_dual k
  have hb : ∀ i j, (w i • x) * (w j • x) = 0 := fun i j => by rw [smul_mul_smul_comm, hx, smul_zero]
  have h1 := cp_nat g θ _ ha _ hb fun i => hθ _
  rw [h, MonObj.comp_one] at h1
  have := jet_inj g hs _ hb (fun i => by rw [map_smul, h0, smul_zero]) h1.symm
  exact funext fun i => hi _ (congrFun this i)

variable {K : Type} [Fintype K] {φ : K → ((t.G ⊗ t.G).left ⟶ t.G.left)} {ε : K → ℤ}
  (w : LB.Gen (LB.LinComb t.PP.L φ ε))

def Chi (x v : Ov k R ⟶ t.G) (c : R) : Prop :=
  ∀ (T : Over (Sp k)) (ρ : T ⟶ Ov k R) z J, Good t.PP.L z J →
    (val₂ w z J (ρ ≫ x) (ρ ≫ v)).val = cst (V := R) ρ.left z c

theorem second_jet_rename (a b : Fin d → R) (ha : ∀ i j, a i * a j = 0) (hb : ∀ i j, b i * b j = 0) (l : Fin 2)
    (f : Germ.PS k 1 d) : th2 k a b ha hb (Ideal.Quotient.mk _ (psIn d 3 ![l] f)) =
      MvPolynomial.aeval (fun q => ![a, b] l q.2) (psTrunc (2 + 1) f) := by
  rw [second_jet_mk, psIn, MvPolynomial.aeval_rename]
  refine congrArg (fun q : Fin 1 × Fin d → R => MvPolynomial.aeval q (psTrunc 3 f)) (funext fun ⟨q, i⟩ => ?_)
  obtain rfl := Subsingleton.elim q 0
  rfl

theorem second_jet_left_substitution (a b : Fin d → R) (ha : ∀ i j, a i * a j = 0) (hb : ∀ i j, b i * b j = 0) (f : Germ.Pt k 1 d)
    (hf : ∀ j, MvPowerSeries.constantCoeff (f j) = 0) (h : ∀ j, ∑ i, lin f 1 j i • a i = 0) :
    (th2 k a b ha hb).comp (jetSubstP 3 fun p : Fin 2 × Fin d =>
      (![fun j => psIn d 3 ![0] (f j), fun j => MvPolynomial.X ((1 : Fin 2), j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) k) p.1 p.2) =
    (th1 k 2 b hb).comp (jetSubstP 3 fun p : Fin 2 × Fin d =>
      (![fun _ => 0, fun j => MvPolynomial.X ((0 : Fin 1), j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) k) p.1 p.2) := by
  refine jet_hom_ext (Prod.forall.2 (Fin.forall_fin_two.2 ⟨fun j => ?_, fun j => ?_⟩))
  · rw [AlgHom.comp_apply, AlgHom.comp_apply, subst_X, subst_X]
    · simp only [Matrix.cons_val_zero]
      rw [second_jet_rename, Matrix.cons_val_zero, aeval_trunc 2 a ha _ hf j, h, map_zero, map_zero]
    · simp
    · simp only [Matrix.cons_val_zero]
      rw [FBIdPh.cc_psIn, hf]
  · rw [AlgHom.comp_apply, AlgHom.comp_apply, subst_X, subst_X] <;> simp [first_jet_mk, second_jet_mk]

theorem second_jet_right_substitution (a b : Fin d → R) (ha : ∀ i j, a i * a j = 0) (hb : ∀ i j, b i * b j = 0) (f : Germ.Pt k 1 d)
    (hf : ∀ j, MvPowerSeries.constantCoeff (f j) = 0) (h : ∀ j, ∑ i, lin f 1 j i • b i = 0) :
    (th2 k a b ha hb).comp (jetSubstP 3 fun p : Fin 2 × Fin d =>
      (![fun j => MvPolynomial.X ((0 : Fin 2), j), fun j => psIn d 3 ![1] (f j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) k) p.1 p.2) =
    (th1 k 2 a ha).comp (jetSubstP 3 fun p : Fin 2 × Fin d =>
      (![fun j => MvPolynomial.X ((0 : Fin 1), j), fun _ => 0] :
        Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) k) p.1 p.2) := by
  refine jet_hom_ext (Prod.forall.2 (Fin.forall_fin_two.2 ⟨fun j => ?_, fun j => ?_⟩))
  · rw [AlgHom.comp_apply, AlgHom.comp_apply, subst_X, subst_X] <;> simp [first_jet_mk, second_jet_mk]
  · rw [AlgHom.comp_apply, AlgHom.comp_apply, subst_X, subst_X]
    · simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [second_jet_rename, Matrix.cons_val_one, Matrix.cons_val_zero, aeval_trunc 2 b hb _ hf j, h, map_zero, map_zero]
    · simp
    · simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [FBIdPh.cc_psIn, hf]

theorem second_jet_point (a b : Fin d → R) (ha : ∀ i j, a i * a j = 0) (hb : ∀ i j, b i * b j = 0) :
    hm (th2 k a b ha hb) ≫ jptG t _ d g.x 3 (0 : Fin 2) = cp g a ha ∧
      hm (th2 k a b ha hb) ≫ jptG t _ d g.x 3 (1 : Fin 2) = cp g b hb := by
  have e₀ : (th2 k a b ha hb).comp (jetCopy d 3 (0 : Fin 2)) = th1 k 2 a ha :=
    jet_hom_ext fun s => by simp [jetCopy, jetMap_mk, first_jet_mk, second_jet_mk]
  have e₁ : (th2 k a b ha hb).comp (jetCopy d 3 (1 : Fin 2)) = th1 k 2 b hb :=
    jet_hom_ext fun s => by simp [jetCopy, jetMap_mk, first_jet_mk, second_jet_mk]
  constructor
  · rw [jptG, cp, ← Category.assoc, homAt_comp, e₀]
  · rw [jptG, cp, ← Category.assoc, homAt_comp, e₁]

theorem val_pe {n : ℕ} (ψ : Fin 2 → Fin d → MvPolynomial (Fin n × Fin d) k) (θ : Jet k (Fin n × Fin d) 3 →ₐ[k] R)
    {T : Over (Sp k)} (ρ : T ⟶ Ov k R) {z} {J} (hJ : Good t.PP.L z J) :
    val (peG t _ d g.x g.e 3 ψ) (ρ ≫ hm θ).left z J =
      val (L := t.PP.L) (φ := cφG t ![jptG t _ d g.x 3 (0 : Fin 2), jptG t _ d g.x 3 (1 : Fin 2)]) (ε := cε 2) (g.e 3)
        (ρ ≫ hm (θ.comp (jetSubstP 3 fun p : Fin 2 × Fin d => ψ p.1 p.2))).left z J := by
  refine (val_pull hJ _ _ _).trans ?_
  rw [← Over.comp_left, Category.assoc, homAt_comp]

theorem val_ax {Z : Scheme.{0}} (r : Z ⟶ (jOG (𝟙 (Sp k)) d 3 1).left) {z} {J} (hJ : Good t.PP.L z J) :
    val (peG t _ d g.x g.e 3 ![fun _ => 0, fun j => MvPolynomial.X ((0 : Fin 1), j)]) r z J = 1 ∧
    val (peG t _ d g.x g.e 3 ![fun j => MvPolynomial.X ((0 : Fin 1), j), fun _ => 0]) r z J = 1 :=
  ⟨(val_corr hJ (g.axes 3).1 r).trans (val_one _), (val_corr hJ (g.axes 3).2 r).trans (val_one _)⟩

theorem val_left (a b : Fin d → R) (ha : ∀ i j, a i * a j = 0) (hb : ∀ i j, b i * b j = 0) (f : Germ.Pt k 1 d)
    (hf : ∀ j, MvPowerSeries.constantCoeff (f j) = 0) (h : ∀ j, ∑ i, lin f 1 j i • a i = 0)
    {T : Over (Sp k)} (ρ : T ⟶ Ov k R) {z} {J} (hJ : Good t.PP.L z J) :
    val (peG t _ d g.x g.e 3 ![fun j => psIn d 3 ![0] (f j), fun j => MvPolynomial.X ((1 : Fin 2), j)])
      (ρ ≫ hm (th2 k a b ha hb)).left z J = 1 := by
  rw [val_pe g _ _ ρ hJ, second_jet_left_substitution a b ha hb f hf h]
  exact (val_pe g _ _ ρ hJ).symm.trans (val_ax g (ρ ≫ hm (th1 k 2 b hb)).left hJ).1

theorem val_right (a b : Fin d → R) (ha : ∀ i j, a i * a j = 0) (hb : ∀ i j, b i * b j = 0) (f : Germ.Pt k 1 d)
    (hf : ∀ j, MvPowerSeries.constantCoeff (f j) = 0) (h : ∀ j, ∑ i, lin f 1 j i • b i = 0)
    {T : Over (Sp k)} (ρ : T ⟶ Ov k R) {z} {J} (hJ : Good t.PP.L z J) :
    val (peG t _ d g.x g.e 3 ![fun j => MvPolynomial.X ((0 : Fin 2), j), fun j => psIn d 3 ![1] (f j)])
      (ρ ≫ hm (th2 k a b ha hb)).left z J = 1 := by
  rw [val_pe g _ _ ρ hJ, second_jet_right_substitution a b ha hb f hf h]
  exact (val_pe g _ _ ρ hJ).symm.trans (val_ax g (ρ ≫ hm (th1 k 2 a ha)).left hJ).2

theorem gm_unit {B : Type} [CommRing B] [Algebra k B] (U : Bˣ) (θ : B →ₐ[k] R) {T : Over (Sp k)} (ρ : T ⟶ Ov k R) (z) :
    (gm (ρ ≫ hm θ).left z ⊤ (unitΓ U)).val = cst (V := R) ρ.left z (θ U) :=
  (gs_unit _ z ⊤ trivial (unitΓ U)).symm.trans (cst_comp ρ.left (θ : B →+* R) z U.val)

theorem chi_chart (c : 𝓞 E) (U : (Jet k (Fin 2 × Fin d) 3)ˣ)
    (h : LB.Gen.Corr t.PP.L _ _ _ _ (LB.mulGen t.PP.L _ _ _ _
      (LB.pullGen t.PP.L _ _ w (lift (jptG t _ d g.x 3 (0 : Fin 2)) (jptG t _ d g.x 3 (1 : Fin 2))).left)
      (peG t _ d g.x g.e 3 ![fun j => psIn d 3 ![0] (g.B.A.act c j), fun j => MvPolynomial.X ((1 : Fin 2), j)]))
      (scaleGenG t _ _ (unitΓ U) (peG t _ d g.x g.e 3
        ![fun j => MvPolynomial.X ((0 : Fin 2), j), fun j => psIn d 3 ![1] (g.B.A.act (H.bar c) j)])))
    (a b : Fin d → R) (ha : ∀ i j, a i * a j = 0) (hb : ∀ i j, b i * b j = 0)
    (h₁ : ∀ j, ∑ i, rho g.B c j i • a i = 0) (h₂ : ∀ j, ∑ i, rho g.B (H.bar c) j i • b i = 0) :
    Chi w (cp g a ha) (cp g b hb) (th2 k a b ha hb U) := by
  intro T ρ z J hJ
  obtain ⟨j₀, j₁⟩ := second_jet_point g a b ha hb
  have e₀ := val_left g a b ha hb _ (g.B.A.const c) h₁ ρ hJ
  have e₁ := val_right g a b ha hb _ (g.B.A.const _) h₂ ρ hJ
  have e₂ := val_ros w (ρ ≫ hm (th2 k a b ha hb)) hJ (jptG t _ d g.x 3 (0 : Fin 2)) (jptG t _ d g.x 3 (1 : Fin 2))
  rw [Category.assoc, Category.assoc, j₀, j₁] at e₂
  have e := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) e₂ e₀)).symm.trans
    ((val_corr hJ h (ρ ≫ hm (th2 k a b ha hb)).left).trans
      ((GermB.val_scale t _ _ _ _ _ _ _ hJ).trans (congrArg₂ (· * ·) rfl e₁)))
  exact (congrArg Units.val (mul_right_cancel e)).trans (gm_unit U _ ρ z)

variable {w}

theorem Chi.unique {x v : Ov k R ⟶ t.G} {c c' : R} (h : Chi w x v c) (h' : Chi w x v c') : c = c' :=
  cst_ext fun z => by
    choose J hJ using fun ψ : Sp R ⟶ t.G.left => exists_chart t.PP.isLB (ψ z)
    exact (h _ (𝟙 _) z J hJ).symm.trans (h' _ (𝟙 _) z J hJ)

theorem Chi.nat {x v : Ov k R ⟶ t.G} {c : R} (h : Chi w x v c) {R' : Type} [CommRing R'] [Algebra k R']
    (θ : R →ₐ[k] R') : Chi w (hm θ ≫ x) (hm θ ≫ v) (θ c) := fun T ρ z J hJ => by
  rw [← Category.assoc, ← Category.assoc, h T _ z J hJ]
  exact cst_comp ρ.left (θ : R →+* R') z c

variable {f f' : t.G ⟶ t.G} [IsMonHom f] [IsMonHom f'] (hA : IsAbelianScheme t.G) (hw : w.IsGen)
  (hW : AdSum f f' φ ε)
include hw hW

theorem chi_exists (x v : Ov k R ⟶ t.G) (hx : x ≫ f = 1) (hv : v ≫ f' = 1) : ∃ c, Chi w x v c := by
  obtain ⟨u, hu⟩ := pair_exists t.PP.isLB hw hW x v hx hv
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom u.val, fun T ρ z J hJ => ?_⟩
  rw [hu T ρ z J hJ, ← gs_unit _ z ⊤ trivial, cst]
  congr 1
  exact (congrArg (fun q => CommRingCat.Hom.hom q u.val) (Scheme.ΓSpecIso (CommRingCat.of R)).hom_inv_id).symm

include hA

theorem chi_one (h : Chi w (1 : Ov k R ⟶ t.G) 1 1) (x : Ov k R ⟶ t.G) : Chi w x 1 1 ∧ Chi w 1 x 1 := by
  constructor <;> intro T ρ z J hJ <;> have := h T ρ z J hJ <;> rw [MonObj.comp_one] at this ⊢
  · rw [(pair_ax hA t.PP.isLB hw hW _ hJ).1, this]
  · rw [(pair_ax hA t.PP.isLB hw hW _ hJ).2, this]

theorem chi_mul (h : Chi w (1 : Ov k R ⟶ t.G) 1 1) {x y v : Ov k R ⟶ t.G} (hx : x ≫ f = 1) (hv : v ≫ f' = 1)
    {c c' : R} (h₁ : Chi w y v c) (h₂ : Chi w x v c') : Chi w (y * x) v (c * c') := fun T ρ z J hJ => by
  have e := congrArg Units.val (pair_mul hA t.PP.isLB hw hW (ρ ≫ x) (ρ ≫ y) (ρ ≫ v)
    (by rw [Category.assoc, hx, MonObj.comp_one]) (by rw [Category.assoc, hv, MonObj.comp_one]) hJ)
  have e' := (chi_one hA hw hW h v).2 T ρ z J hJ
  rw [MonObj.comp_one, cst_one] at e'
  rw [Units.val_mul, Units.val_mul, e', h₁ T ρ z J hJ, h₂ T ρ z J hJ, _root_.mul_one] at e
  rw [MonObj.comp_mul, e, cst_mul]

end Chart

end

end PositivityTheory.Xgn.JetKernelRank

open PositivityTheory.Xgn.JetKernelRank Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.GermD ReciprocityTheory.ChartRestriction.G.DVR TensorProduct
  Algebra.TensorProduct TrivSqZeroExt in
theorem PositivityTheory.Xgn.JetKernelRank.main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (t : SAB H (Sp k)), IsProper t.G.hom → Out.KTriv t.G t.PP.L → ∀ (d : ℕ) (g : GermAt t (𝟙 (Sp k)) d) (a : 𝓞 E) (A : Type) [CommRing A] [Algebra k A] [Module.Finite k A] (i : Sp A ⟶ t.G.left), IsPullback i (spMap (algebraMap k A)) (t.act.act a).left (η[t.G]).left → p ^ Module.finrank k (LinearMap.ker (rhoH g.B a)) ∣ Module.finrank k A := by
  intro E _ _ _ H _ hs k _ _ p _ _ t hpr hK d g a A _ _ _ i hp
  have hA := AbelianSchemeGerms.isAbelianScheme_of_proper t.G t.semi
  have := t.act.hom a
  have := t.act.hom (H.bar a)
  obtain ⟨κ, h₁, h₂⟩ := exists_ker i hp
  obtain ⟨w, hw, hU⟩ := g.frame.ad a
  obtain ⟨U, hU₁, hU₂⟩ := hU 3
  have hW : AdSum (t.act.act a) (t.act.act (H.bar a))
      (Sum.elim (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)])
        (cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G])) (Sum.elim (cε 2) (fun I => -cε 2 I)) :=
    fun {T} p q U _ h => by
      refine (prod_sum₂ (K := ULift.{0} (Finset (Fin 2))) (K' := ULift.{0} (Finset (Fin 2))) (U := U) _
        (prod_cube₂ _ _ fun r => h ((lift p q).left ≫ r))
        (prod_neg _ _ (prod_cube₂ _ _ fun r => h ((lift p q).left ≫ r)))).trans ?_
      simp only [← Over.comp_left, MonObj.comp_mul, MonObj.comp_one, lift_fst, lift_snd, lift_fst_assoc,
        lift_snd_assoc]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
  obtain ⟨r, s, u, v, lu, lv, hu, hv, huv, hle⟩ :=
    linalg (rho g.B a) (rho g.B (star a)) (bil (g.B.ad a) 1 1) _ (rhoH_apply g.B a)
  rw [hs] at hv
  refine (pow_dvd_pow p hle).trans ?_
  have cc : MvPowerSeries.constantCoeff (g.B.ad a) = 1 := by
    rw [← PositivityTheory.HtPt.Ca.cc_ev (a := ![0, Germ.pt k (n := 1) d 0]) (fun j i => by fin_cases j <;> simp [Germ.pt]),
      g.B.adjoint_zero_fst, map_one]
  have h11 : ∀ (R : Type) [CommRing R] [Algebra k R], Chi w (1 : Ov k R ⟶ t.G) 1 1 := fun R _ _ => by
    have h0 : ∀ i j : Fin d, (0 : Fin d → R) i * (0 : Fin d → R) j = 0 := by simp
    have := chi_chart g w a U hU₂ 0 0 h0 h0 (by simp) (by simp)
    obtain ⟨α, β, e⟩ := second_jet_expansion (k := k) 0 0 h0 h0 (g.B.ad a)
    rw [cp_zero g _ _ rfl, hU₁, e, cc] at this
    simpa using this
  have sq : ∀ {n : ℕ} (v : Fin n → Fin d → k) (i j : Fin d),
      (inr (fun l => v l i) : Sq k n) * inr (fun l => v l j) = 0 := fun v i j => inr_mul_inr _ _ _
  have kill : ∀ {n : ℕ} (v : Fin n → Fin d → k) (M : Matrix (Fin d) (Fin d) k), (∀ l, M.mulVec (v l) = 0) →
      ∀ j, ∑ i, M j i • (inr (fun l => v l i) : Sq k n) = 0 := fun v M h j => by
    refine TrivSqZeroExt.ext (by simp [fst_sum]) (funext fun l => ?_)
    simpa [snd_sum, Matrix.mulVec, dotProduct] using congrFun (h l) j
  have dirv : ∀ {n : ℕ} (v : Fin n → Fin d → k), LinearIndependent k v → ∀ l : Fin n → k,
      hm (dir l) ≫ cp g _ (sq v) = 1 → ∀ i, l i = 0 := fun v lv l h => by
    rw [cp_nat g _ _ _ (fun j => (inr ((∑ i, l i • v i) j) : DualNumber k)) (fun _ _ => inr_mul_inr _ _ _)
      (fun j => by simp [dir, dotProduct])] at h
    exact Fintype.linearIndependent_iff.1 lv l (cp_inj g hs _ _ h)
  let z : Ov k (Sq k r) ⟶ t.G := cp g _ (sq v)
  have hz : z ≫ t.act.act (H.bar a) = 1 := cp_act g _ _ _ (kill v _ hv)
  have ker : ∀ {T : Over (Sp k)} (y : T ⟶ Ov k A), (y ≫ κ) ≫ t.act.act a = 1 := fun y => by
    rw [Category.assoc, h₁, MonObj.comp_one]
  have ker' : ∀ {T : Over (Sp k)} (y : T ⟶ Ov k (Sq k r)), (y ≫ z) ≫ t.act.act (H.bar a) = 1 := fun y => by
    rw [Category.assoc, hz, MonObj.comp_one]
  obtain ⟨ψ, hψ⟩ := pt_surj h₂ (cp g _ (sq u)) (cp_act g _ _ _ (kill u _ hu))
  obtain ⟨e, he⟩ := pt_surj h₂ (1 : Ov k k ⟶ t.G) (MonObj.one_comp _)
  obtain ⟨Δ, hΔ⟩ := pt_surj h₂ ((hm (includeLeft : A →ₐ[k] A ⊗[k] A) ≫ κ) * (hm includeRight ≫ κ))
    (by rw [MonObj.mul_comp, ker, ker, _root_.mul_one])
  obtain ⟨c, hc⟩ := chi_exists hw hW (hm (includeLeft : A →ₐ[k] A ⊗[k] Sq k r) ≫ κ) (hm includeRight ≫ z)
    (ker _) (ker' _)
  have N : ∀ {B C : Type} [CommRing B] [Algebra k B] [CommRing C] [Algebra k C] (θ : A →ₐ[k] B) (ν : Sq k r →ₐ[k] C),
      Chi w (hm includeLeft ≫ hm θ ≫ κ) (hm includeRight ≫ hm ν ≫ z) (Algebra.TensorProduct.map θ ν c) :=
    fun θ ν => by
      have := hc.nat (Algebra.TensorProduct.map θ ν)
      rwa [← Category.assoc, ← Category.assoc, homAt_comp, homAt_comp, map_comp_includeLeft, map_comp_includeRight,
        ← homAt_comp, ← homAt_comp, Category.assoc, Category.assoc] at this
  have c1 : c0 k r A c = 1 := by
    have := hc.nat (c0 k r A)
    rw [← Category.assoc (hm (c0 k r A)) (hm includeRight), homAt_comp,
      cp_nat g _ _ _ 0 (by simp) (fun j => by simp), cp_zero g _ _ rfl] at this
    exact this.unique (chi_one hA hw hW (h11 A) _).1
  have fψ : ∀ x, (ψ x).fst = e x := by
    have : (fstHom k k _).comp ψ = e := pt_inj h₁ h₂ (by
      rw [← homAt_comp, Category.assoc, hψ, he, cp_nat g _ _ _ 0 (by simp) (fun j => by simp), cp_zero g _ _ rfl])
    exact fun x => DFunLike.congr_fun this x
  have f0 : ∀ i, e (co i c) = 0 := fun i => by
    have := N e (AlgHom.id k _)
    rw [he, MonObj.comp_one] at this
    rw [← co_map, this.unique (chi_one hA hw hW (h11 _) _).2, Algebra.TensorProduct.one_def]
    simp
  refine ker_dvd h₁ h₂ p Δ hΔ e he (fun i => co i c) (fun i => ?_) f0 (Fintype.linearIndependent_iff.2 fun l hl => ?_)
    (fun j => LinearMap.proj j ∘ₗ sndHom k _ ∘ₗ ψ.toLinearMap) (fun j x y => ?_)
    (Fintype.linearIndependent_iff.2 fun l hl => ?_) (fun j i => ?_)
  · have a₁ := N Δ (AlgHom.id k _)
    rw [hΔ, MonObj.comp_mul] at a₁
    have a₂ := chi_mul hA hw hW (h11 _) (by rw [← Category.assoc]; exact ker _)
      (by rw [← Category.assoc]; exact ker' _) (N (includeLeft : A →ₐ[k] A ⊗[k] A) (AlgHom.id k _))
      (N (includeRight : A →ₐ[k] A ⊗[k] A) (AlgHom.id k _))
    rw [← co_map, a₁.unique a₂, co_mul, co_map, co_map, map_lineCoeffConst, map_lineCoeffConst, c1]
    simp [add_comm]
  · obtain ⟨_, _, _⟩ := flat_surj h₂ hA
    have a₁ := N (AlgHom.id k A) (dir l)
    rw [map_dir, hl, c1, zero_tmul, add_zero, ← Algebra.TensorProduct.one_def, homAt_id, Category.id_comp] at a₁
    refine dirv v lv l (pair_nondeg hA t.PP.isLB hw hW hK _ (hm (dir l) ≫ z) (ker' _) fun T ρ x hx y J hJ => ?_)
    obtain ⟨x, rfl, -⟩ := h₂ T x hx
    obtain ⟨τ, rfl, rfl⟩ := exists_tensor x ρ
    have a₂ := (a₁ T τ y J hJ).trans ((chi_one hA hw hW (h11 _)
      (hm (includeRight : DualNumber k →ₐ[k] A ⊗[k] DualNumber k) ≫ hm (dir l) ≫ z)).2 T τ y J hJ).symm
    rw [MonObj.comp_one] at a₂
    simpa only [Category.assoc] using Units.ext a₂
  · simp [snd_mul, fψ, mul_comm]
  · refine dirv u lu l ?_
    have : (dir l).comp ψ = (Algebra.ofId k _).comp e := AlgHom.ext fun x => by
      have := DFunLike.congr_fun hl x
      ext
      · simp [dir, fψ, algebraMap_eq_inl]
      · simpa [dir, dotProduct, algebraMap_eq_inl] using this
    rw [← hψ, ← Category.assoc, homAt_comp, this, ← homAt_comp, Category.assoc, he, MonObj.comp_one]
  · have a₁ := N ψ (AlgHom.id k _)
    let a' : Fin d → Sq k s ⊗[k] Sq k r := fun m => inr (fun l => u l m) ⊗ₜ 1
    let b' : Fin d → Sq k s ⊗[k] Sq k r := fun m => 1 ⊗ₜ inr (fun l => v l m)
    have ha : ∀ i j, a' i * a' j = 0 := fun i j => by simp [a']
    have hb : ∀ i j, b' i * b' j = 0 := fun i j => by simp [b']
    rw [hψ, homAt_id, Category.id_comp, cp_nat g _ _ _ a' ha (fun _ => rfl), cp_nat g _ _ _ b' hb (fun _ => rfl)] at a₁
    have a₂ := chi_chart g w a U hU₂ a' b' ha hb
      (fun m => by simpa [a', sum_tmul, smul_tmul'] using congrArg (· ⊗ₜ[k] (1 : Sq k r)) (kill u _ hu m))
      (fun m => by simpa [b', tmul_sum] using congrArg ((1 : Sq k s) ⊗ₜ[k] ·) (kill v _ hv m))
    obtain ⟨α, β, e'⟩ := second_jet_expansion (k := k) a' b' ha hb (g.B.ad a)
    have a₃ := congrArg (fun q => (co i q).snd j) ((a₁.unique a₂).trans ((congrArg _ hU₁).trans e'))
    simp only [co_map] at a₃
    refine a₃.trans (Eq.trans ?_ (huv i j))
    simp [a', b', snd_sum, Algebra.TensorProduct.algebraMap_apply, Matrix.mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem PositivityTheory.Xgn.kernel_rank_multiplication_char_p : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (t : SAB H (Sp k)), IsProper t.G.hom → Out.KTriv t.G t.PP.L → ∀ (d : ℕ) (g : GermAt t (𝟙 (Sp k)) d) (a : 𝓞 E) (A : Type) [CommRing A] [Algebra k A] [Module.Finite k A] (i : Sp A ⟶ t.G.left), IsPullback i (spMap (algebraMap k A)) (t.act.act a).left (η[t.G]).left → p ^ Module.finrank k (LinearMap.ker (rhoH g.B a)) ∣ Module.finrank k A := by
  exact PositivityTheory.Xgn.JetKernelRank.main
