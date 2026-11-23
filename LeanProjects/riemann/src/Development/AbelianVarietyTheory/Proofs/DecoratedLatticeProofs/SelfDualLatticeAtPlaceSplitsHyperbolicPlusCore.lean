import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingPreservesSupportedUnitarySubgro
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IwaDecomp

variable {D : D7}

theorem intAt_mul' {v : Pl D} {a b : AE D} (ha : a ∈ intAt D (· = v)) (hb : b ∈ intAt D (· = v)) :
    a * b ∈ intAt D (· = v) :=
  ⟨Ideal.mul_mem_right _ _ ha.1, by rw [map_mul]; exact GlobalTheory.HostAdeleIso.intAE_mul_mem D ha.2 hb.2⟩

theorem intAt_zero' {v : Pl D} : (0 : AE D) ∈ intAt D (· = v) :=
  ⟨zero_mem _, by rw [map_zero]; exact zero_mem _⟩

theorem intAt_add' {v : Pl D} {a b : AE D} (ha : a ∈ intAt D (· = v)) (hb : b ∈ intAt D (· = v)) :
    a + b ∈ intAt D (· = v) :=
  ⟨add_mem ha.1 hb.1, by rw [RingHom.map_add]; exact add_mem ha.2 hb.2⟩

theorem intAt_sum' {v : Pl D} {ι : Type} (s : Finset ι) (f : ι → AE D) (h : ∀ i ∈ s, f i ∈ intAt D (· = v)) :
    ∑ i ∈ s, f i ∈ intAt D (· = v) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact intAt_zero'
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact intAt_add' (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem intAt_intCast_mul {v : Pl D} (N : ℤ) {a : AE D} (ha : a ∈ intAt D (· = v)) :
    (N : AE D) * a ∈ intAt D (· = v) :=
  ⟨Ideal.mul_mem_left _ _ ha.1, by rw [map_mul, map_intCast, ← zsmul_eq_mul]; exact zsmul_mem ha.2 N⟩

theorem intAt_natCast_mul {v : Pl D} (n : ℕ) {a : AE D} (ha : a ∈ intAt D (· = v)) :
    (n : AE D) * a ∈ intAt D (· = v) := by
  have := intAt_intCast_mul (v := v) (n : ℤ) ha
  rwa [Int.cast_natCast] at this

theorem exists_nat_incA_mul (v : Pl D) (c : D.host.E) :
    ∃ n : ℕ, 0 < n ∧ ∀ a ∈ intAt D (· = v), incA D c * ((n : AE D) * a) ∈ intAt D (· = v) := by
  have halg : IsAlgebraic ℤ c :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ D.host.E).2 (Algebra.IsAlgebraic.isAlgebraic c)
  obtain ⟨N, hN, hint⟩ := halg.exists_integral_multiple
  refine ⟨N.natAbs * N.natAbs, Nat.mul_pos (Int.natAbs_pos.2 hN) (Int.natAbs_pos.2 hN), fun a ha => ?_⟩
  have key : ∀ b ∈ intAt D (· = v), incA D (N • c) * b ∈ intAt D (· = v) := by
    intro b hb
    refine ⟨Ideal.mul_mem_left _ _ hb.1, ?_⟩
    rw [map_mul]
    have hc : finPart D (incA D (N • c)) = (1 : Af D.host.F) ⊗ₜ[D.host.F] (N • c) := rfl
    rw [hc]
    refine GlobalTheory.HostAdeleIso.intAE_mul_mem D ?_ hb.2
    refine AddSubgroup.subset_closure ⟨1, fun w => ?_, ⟨N • c, hint⟩, rfl⟩
    rw [map_one]
    exact one_mem _
  have hcast : ((N.natAbs * N.natAbs : ℕ) : AE D) = (N : AE D) * (N : AE D) := by
    have h1 : ((N.natAbs * N.natAbs : ℕ) : ℤ) = N * N := by rw [Nat.cast_mul]; exact Int.natAbs_mul_self' N
    have h2 : (((N.natAbs * N.natAbs : ℕ) : ℤ) : AE D) = ((N * N : ℤ) : AE D) := by rw [h1]
    rw [Int.cast_natCast] at h2
    rw [h2, Int.cast_mul]
  have e : incA D c * (((N.natAbs * N.natAbs : ℕ) : AE D) * a) = incA D (N • c) * ((N : AE D) * a) := by
    rw [hcast, zsmul_eq_mul, map_mul, map_intCast]
    ring
  rw [e]
  exact key _ (intAt_intCast_mul N ha)

end GlobalTheory.IwaDecomp

namespace GlobalTheory.IwaDecomp

variable {D : D7}

theorem hermAt_smul_left (S : HSp D) (t : AE D) (y x : Fin S.rank → AE D) :
    hermAt S (t • y) x = t * hermAt S y x := by
  simp only [hermAt, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hermAt_eq_dot (S : HSp D) (x y : Fin S.rank → AE D) :
    hermAt S x y = (fun i => cA D (y i)) ⬝ᵥ (gA S *ᵥ x) := by
  simp only [hermAt, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hermAt_colMul (S : HSp D) {ρ : ℕ} (M : Mx D S.rank ρ) (i : Fin ρ) (a : AE D) (z : Fin S.rank → AE D) :
    hermAt S z (colMul M i a) = cA D a * ((adj M ⬝ gA S) *ᵥ z) i := by
  simp only [hermAt, colMul, adj, Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    map_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

theorem mulVec_eq_sum_colMul {m n : ℕ} (M : Mx D m n) (a : Fin n → AE D) :
    M *ᵥ a = ∑ i, colMul M i (a i) := by
  funext k
  simp only [Matrix.mulVec, dotProduct, colMul, Finset.sum_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem wittCoreProjection_conjTranspose_gram_eq {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) : adj d.p0 ⬝ gA S₀ = gA S ⬝ d.j0 := by
  rw [d.p0_eq, adj_mul, adj_mul, adj_adj, adj_giA, adj_gA, Matrix.mul_assoc, Matrix.mul_assoc, giA_mul_gA,
    Matrix.mul_one]

theorem adelicHermitianForm_wittCoreInclusion_left {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (y : Fin S₀.rank → AE D) (w : Fin S.rank → AE D) :
    hermAt S (d.j0 *ᵥ y) w = hermAt S₀ y (d.p0 *ᵥ w) := by
  rw [hermAt_eq_dot, hermAt_eq_dot]
  have h1 : (fun i => cA D ((d.p0 *ᵥ w) i)) = d.p0.map (cA D) *ᵥ fun i => cA D (w i) := by
    funext i
    exact RingHom.map_mulVec (cA D) d.p0 w i
  rw [h1]
  conv_rhs => rw [dotProduct_comm, dotProduct_mulVec, dotProduct_comm, ← mulVec_transpose]
  change _ = (fun i => cA D (w i)) ⬝ᵥ (adj d.p0 *ᵥ (gA S₀ *ᵥ y))
  rw [Matrix.mulVec_mulVec, ← wittCoreProjection_conjTranspose_gram_eq, ← Matrix.mulVec_mulVec]

theorem decomp_vec {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (z : Fin S.rank → AE D) :
    z = d.jX *ᵥ (d.pX *ᵥ z) + d.j0 *ᵥ (d.p0 *ᵥ z) + d.jY *ᵥ (d.pY *ᵥ z) := by
  have h := congrArg (· *ᵥ z) d.sum_eq_one
  simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, Matrix.one_mulVec] at h
  exact h.symm

end GlobalTheory.IwaDecomp

namespace GlobalTheory.IwaDecomp

variable {D : D7}

def lamZero {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (v : Pl D) (N : AddSubgroup (Fin S.rank → AE D)) :
    AddSubgroup (Fin S₀.rank → AE D) where
  carrier := {s | (∀ i, s i ∈ idAt D (· = v)) ∧ d.j0 *ᵥ s ∈ N}
  zero_mem' := ⟨fun _ => zero_mem _, by rw [Matrix.mulVec_zero]; exact N.zero_mem⟩
  add_mem' := fun {a b} ha hb => ⟨fun i => add_mem (ha.1 i) (hb.1 i), by
    rw [Matrix.mulVec_add]; exact N.add_mem ha.2 hb.2⟩
  neg_mem' := fun {a} ha => ⟨fun i => neg_mem (ha.1 i), by
    rw [Matrix.mulVec_neg]; exact N.neg_mem ha.2⟩

theorem exists_nat_wittCoreInclusion_integral_at_place {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (v : Pl D) :
    ∃ n : ℕ, 0 < n ∧ ∀ s : Fin S₀.rank → AE D, (∀ i, s i ∈ intAt D (· = v)) →
      ∀ k, (d.j0 *ᵥ ((n : AE D) • s)) k ∈ intAt D (· = v) := by
  classical
  choose nf hnf hmul using fun kl : Fin S.rank × Fin S₀.rank => exists_nat_incA_mul v (d.i₀ kl.1 kl.2)
  refine ⟨∏ kl, nf kl, Finset.prod_pos fun kl _ => hnf kl, fun s hs k => ?_⟩
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
  refine intAt_sum' _ _ fun l _ => ?_
  obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem nf (Finset.mem_univ (k, l))
  have e : d.j0 k l = incA D (d.i₀ k l) := rfl
  rw [e, hq, Nat.cast_mul, mul_assoc]
  exact hmul (k, l) _ (intAt_natCast_mul q (hs l))

theorem selfDual_split : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : Pl D) (ε : AE D) (hεε : ε * ε = ε)
    (hεc : cA D ε = ε) (hεI : ε ∈ intAt D (· = v)) (hε : ∀ a, a ∈ idAt D (· = v) ↔ ε * a = a)
    (N : AddSubgroup (Fin S.rank → AE D)) (α β : Fin ρ → AE D), IsSDAt S v N → (∀ i, α i ∈ idAt D (· = v)) →
    (∀ i, β i ∈ idAt D (· = v)) → (∀ i, α i * β i = ε) → (∀ i, colMul d.jX i (α i) ∈ N) →
    (∀ i, colMul d.jY i (cA D (β i)) ∈ N) → ∃ Λ₀ : AddSubgroup (Fin S₀.rank → AE D), IsSDAt S₀ v Λ₀ ∧
      ∀ z : Fin S.rank → AE D, (∀ i, z i ∈ idAt D (· = v)) →
        (z ∈ N ↔ (∀ i, (d.pX *ᵥ z) i * β i ∈ intAt D (· = v)) ∧
          (∀ i, (d.pY *ᵥ z) i * cA D (α i) ∈ intAt D (· = v)) ∧ d.p0 *ᵥ z ∈ Λ₀) := by
  intro D S S₀ ρ d v ε _ hεc _ hε N α β hN _ _ hαβ hXα hYβ

  have hsmul : ∀ t ∈ intAt D (· = v), ∀ y ∈ N, t • y ∈ N := by
    intro t ht y hy
    have hys := hN.1 y hy
    refine (hN.2.2 (t • y) fun i => Ideal.mul_mem_left _ t (hys i)).2 fun x hx => ?_
    rw [hermAt_smul_left]
    exact intAt_mul' ht ((hN.2.2 y hys).1 hy x hx)

  have hX : ∀ a : Fin ρ → AE D, (∀ i, a i ∈ idAt D (· = v)) → (∀ i, a i * β i ∈ intAt D (· = v)) →
      d.jX *ᵥ a ∈ N := by
    intro a ha hab
    rw [mulVec_eq_sum_colMul]
    refine AddSubgroup.sum_mem _ fun i _ => ?_
    have e : colMul d.jX i (a i) = (a i * β i) • colMul d.jX i (α i) := by
      have e1 : a i * β i * α i = a i := by
        rw [mul_assoc, mul_comm (β i), hαβ i, mul_comm, (hε _).1 (ha i)]
      funext k
      simp only [colMul, Pi.smul_apply, smul_eq_mul]
      rw [← mul_assoc, e1]
    rw [e]
    exact hsmul _ (hab i) _ (hXα i)

  have hY : ∀ b : Fin ρ → AE D, (∀ i, b i ∈ idAt D (· = v)) → (∀ i, b i * cA D (α i) ∈ intAt D (· = v)) →
      d.jY *ᵥ b ∈ N := by
    intro b hb hba
    rw [mulVec_eq_sum_colMul]
    refine AddSubgroup.sum_mem _ fun i _ => ?_
    have e : colMul d.jY i (b i) = (b i * cA D (α i)) • colMul d.jY i (cA D (β i)) := by
      have e1 : b i * cA D (α i) * cA D (β i) = b i := by
        rw [mul_assoc, ← map_mul, hαβ i, hεc, mul_comm, (hε _).1 (hb i)]
      funext k
      simp only [colMul, Pi.smul_apply, smul_eq_mul]
      rw [← mul_assoc, e1]
    rw [e]
    exact hsmul _ (hba i) _ (hYβ i)

  have hfwd : ∀ z ∈ N, (∀ i, (d.pX *ᵥ z) i * β i ∈ intAt D (· = v)) ∧
      (∀ i, (d.pY *ᵥ z) i * cA D (α i) ∈ intAt D (· = v)) ∧ d.j0 *ᵥ (d.p0 *ᵥ z) ∈ N := by
    intro z hz
    have hzs := hN.1 z hz
    have hpair := (hN.2.2 z hzs).1 hz
    have h1 : ∀ i, (d.pX *ᵥ z) i * β i ∈ intAt D (· = v) := by
      intro i
      have := hpair _ (hYβ i)
      rwa [hermAt_colMul, ← d.pX_eq, cA_cA, mul_comm] at this
    have h2 : ∀ i, (d.pY *ᵥ z) i * cA D (α i) ∈ intAt D (· = v) := by
      intro i
      have := hpair _ (hXα i)
      rwa [hermAt_colMul, ← d.pY_eq, mul_comm] at this
    refine ⟨h1, h2, ?_⟩
    have hXm := hX _ (mulVec_mem_idAt d.pX hzs) h1
    have hYm := hY _ (mulVec_mem_idAt d.pY hzs) h2
    have key : ∀ X Y Z w : Fin S.rank → AE D, w = X + Z + Y → Z = w - X - Y := fun X Y Z w h => by
      rw [h]; abel
    have e := key _ _ _ _ (decomp_vec d z)
    rw [e]
    exact N.sub_mem (N.sub_mem hz hXm) hYm
  have hmem : ∀ s, s ∈ lamZero d v N ↔ (∀ i, s i ∈ idAt D (· = v)) ∧ d.j0 *ᵥ s ∈ N := fun _ => Iff.rfl
  refine ⟨lamZero d v N, ⟨fun y hy => ((hmem y).1 hy).1, ?_, ?_⟩, ?_⟩
  · obtain ⟨mN, hmN, hNm⟩ := hN.2.1
    obtain ⟨n, hn, hjn⟩ := exists_nat_wittCoreInclusion_integral_at_place d v
    refine ⟨mN * n, Nat.mul_pos hmN hn, fun y hy => (hmem _).2 ⟨fun i => ?_, ?_⟩⟩
    · exact Ideal.mul_mem_left _ _ (hy i).1
    · have e : d.j0 *ᵥ (((mN * n : ℕ) : AE D) • y) = (mN : AE D) • (d.j0 *ᵥ ((n : AE D) • y)) := by
        funext k
        simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Nat.cast_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => by ring
      rw [e]
      exact hNm _ (hjn y hy)
  · intro y hy
    have hjs : ∀ i, (d.j0 *ᵥ y) i ∈ idAt D (· = v) := mulVec_mem_idAt d.j0 hy
    constructor
    · intro hyΛ x hx
      have e : hermAt S₀ y x = hermAt S (d.j0 *ᵥ y) (d.j0 *ᵥ x) := by
        rw [adelicHermitianForm_wittCoreInclusion_left, Matrix.mulVec_mulVec, d.p0_j0, Matrix.one_mulVec]
      rw [e]
      exact (hN.2.2 _ hjs).1 ((hmem y).1 hyΛ).2 _ ((hmem x).1 hx).2
    · intro h
      refine (hmem y).2 ⟨hy, (hN.2.2 _ hjs).2 fun w hw => ?_⟩
      rw [adelicHermitianForm_wittCoreInclusion_left]
      exact h _ ((hmem _).2 ⟨mulVec_mem_idAt d.p0 (hN.1 w hw), (hfwd w hw).2.2⟩)
  · intro z hz
    constructor
    · intro hzN
      obtain ⟨h1, h2, h3⟩ := hfwd z hzN
      exact ⟨h1, h2, (hmem _).2 ⟨mulVec_mem_idAt d.p0 hz, h3⟩⟩
    · rintro ⟨h1, h2, h3⟩
      rw [decomp_vec d z]
      exact N.add_mem (N.add_mem (hX _ (mulVec_mem_idAt d.pX hz) h1) ((hmem _).1 h3).2)
        (hY _ (mulVec_mem_idAt d.pY hz) h2)

end GlobalTheory.IwaDecomp
