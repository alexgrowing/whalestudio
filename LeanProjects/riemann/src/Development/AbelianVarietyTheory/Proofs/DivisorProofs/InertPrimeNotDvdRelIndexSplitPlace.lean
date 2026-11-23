import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulMemLatO
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AddNsmulResidueAssoc
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIntegralSplitIdempotentOverTwo
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsOpenNsmulCompletedHomLatticeFiniteAdelic
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ThetaNormSqSumHeisenbergTranslatesDistinctChars
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EventuallyFinEqOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ActAApply

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitIndex

open GlobalTheory.SplitScalar

variable {D : D7}

theorem finPart_cA_eq_zero {a : AE D} (h : finPart D a = 0) : finPart D (cA D a) = 0 := by
  rw [← realIdem_mul_of_real h, RingHom.map_mul, cA_realIdem, RingHom.map_mul, finPart_realIdem, zero_mul]

theorem tmul_split {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (β : Af F) (x : F) (k : ℕ) (t : E) :
    (algebraMap F (Af F) x + k • β) ⊗ₜ[F] t =
      (1 : Af F) ⊗ₜ[F] (algebraMap F E x * t) + k • (β ⊗ₜ[F] t) := by
  rw [TensorProduct.add_tmul, TensorProduct.smul_tmul', Algebra.algebraMap_eq_smul_one x,
    TensorProduct.smul_tmul, Algebra.smul_def x t]

theorem map_add_nsmul {A B : Type} [Ring A] [Ring B] (f : A →+* B) (k : ℕ) (a s : A) :
    f (a + k • s) = f a + k • f s := by rw [map_add, map_nsmul]

theorem zero_eq_map_add_nsmul_zero {E A B : Type} [Ring E] [Ring A] [Ring B] (g : E →+* A) (f : A →+* B) (k : ℕ) :
    0 = f (g 0 + k • 0) := by simp

theorem add_nsmul_residue_add {E A B : Type} [Ring E] [Ring A] [Ring B] (g : E →+* A) (f : A →+* B) (k : ℕ) (r r' : E)
    (s s' : A) : f (g r + k • s) + f (g r' + k • s') = f (g (r + r') + k • (s + s')) := by
  rw [← map_add, map_add g, smul_add]; congr 1; abel

theorem neg_nsmul_residue {E A B : Type} [Ring E] [Ring A] [Ring B] (g : E →+* A) (f : A →+* B) (k : ℕ) (r : E)
    (s : A) : -f (g r + k • s) = f (g (-r) + k • (-s)) := by
  rw [← map_neg, map_neg g, smul_neg, neg_add]

theorem approx {k : ℕ} (hk : 0 < k) {z : Af D.host.F ⊗[D.host.F] D.host.E} (hz : z ∈ intAE D) :
    ∃ (r : 𝓞 D.host.E) (s : AE D), finPart D s ∈ intAE D ∧ finPart D (cA D s) ∈ intAE D ∧
      z = finPart D (incA D (r : D.host.E) + k • s) := by
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, t, rfl⟩ := hw
    obtain ⟨x, β, hβ, hx⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat D.host.F k hk).2 α hα
    refine ⟨algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x * t, pairA D.host.F 0 β ⊗ₜ[D.host.F] (t : D.host.E),
      AddSubgroup.subset_closure ⟨β, hβ, t, rfl⟩,
      AddSubgroup.subset_closure ⟨β, hβ, GlobalTheory.FinWeil.sgO D t, ?_⟩, ?_⟩
    · rw [GlobalTheory.FinWeil.coe_sgO, ← GlobalTheory.SplitIdem.star_eq_conj]
      rfl
    · rw [hx]
      refine Eq.trans ?_ (map_add_nsmul (finPart D) k _ _).symm
      exact tmul_split β (x : D.host.F) k (t : D.host.E)
  | zero => exact ⟨0, 0, by rw [RingHom.map_zero]; exact zero_mem _,
      by rw [RingHom.map_zero, RingHom.map_zero]; exact zero_mem _,
      zero_eq_map_add_nsmul_zero (incA D) (finPart D) k⟩
  | add x x' _ _ h h' =>
    obtain ⟨r, s, h1, h2, rfl⟩ := h
    obtain ⟨r', s', h1', h2', rfl⟩ := h'
    refine ⟨r + r', s + s', by rw [RingHom.map_add]; exact add_mem h1 h1',
      by rw [RingHom.map_add, RingHom.map_add]; exact add_mem h2 h2', ?_⟩
    exact add_nsmul_residue_add (incA D) (finPart D) k _ _ s s'
  | neg x _ h =>
    obtain ⟨r, s, h1, h2, rfl⟩ := h
    refine ⟨-r, -s, by rw [RingHom.map_neg]; exact neg_mem h1,
      by rw [RingHom.map_neg, RingHom.map_neg]; exact neg_mem h2, ?_⟩
    exact neg_nsmul_residue (incA D) (finPart D) k _ s

theorem core_mem {O A M : Type} [CommRing O] [CommRing A] [AddCommGroup M] [Module A M] (ι : O →+* A)
    (Λ : AddSubgroup M) (hΛ : ∀ r : O, ∀ u ∈ Λ, ι r • u ∈ Λ) (q : ℕ) (y : M) (hq : q • y ∈ Λ) (r r' : O)
    (h1 : ι (1 - r) • y ∈ Λ) (h2 : ι r' • y ∈ Λ)
    (hP : ∀ P : Ideal O, P.IsMaximal → (q : O) ∈ P → r' ∈ P → r ∈ P) : y ∈ Λ := by
  let I : Ideal O :=
    { carrier := {a | ι a • y ∈ Λ}
      add_mem' := fun {a b} ha hb => by
        show ι (a + b) • y ∈ Λ
        rw [map_add, add_smul]; exact add_mem ha hb
      zero_mem' := by
        show ι 0 • y ∈ Λ
        rw [map_zero, zero_smul]; exact zero_mem _
      smul_mem' := fun c a ha => by
        show ι (c * a) • y ∈ Λ
        rw [map_mul, mul_smul]; exact hΛ c _ ha }
  by_contra hy
  have hI : I ≠ ⊤ := fun h => by
    have : (1 : O) ∈ I := by rw [h]; trivial
    exact hy (by simpa [I] using this)
  obtain ⟨P, hPm, hIP⟩ := Ideal.exists_le_maximal I hI
  have hqI : (q : O) ∈ I := by
    show ι (q : O) • y ∈ Λ
    rw [map_natCast, Nat.cast_smul_eq_nsmul]; exact hq
  have hr := hP P hPm (hIP hqI) (hIP h2)
  have := add_mem (hIP h1 : 1 - r ∈ P) hr
  rw [sub_add_cancel] at this
  exact hPm.ne_top ((Ideal.eq_top_iff_one _).2 this)

theorem wachExpansion_smul_compatible {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (q : ℕ) (e f b s : A) (x : M)
    (h : (f - (b + q • s)) * e = 0) : b • e • x = (f * e) • x - s • e • q • x := by
  have : b * e = f * e - s * e * q := by
    rw [nsmul_eq_mul] at h
    linear_combination -h
  rw [smul_smul, this, sub_smul, mul_smul (s * e), mul_smul s, Nat.cast_smul_eq_nsmul]

theorem core_split {O A M : Type} [CommRing O] [CommRing A] [AddCommGroup M] [Module A M] (ι : O →+* A)
    (Λ : AddSubgroup M) (p : A → Prop) (hΛ : ∀ a, p a → ∀ u ∈ Λ, a • u ∈ Λ) (hι : ∀ r, p (ι r)) (q : ℕ) (x : M)
    (hx : q • x ∈ Λ) (e f s s' : A) (he : p e) (hs : p s) (hs' : p s') (hee : e * e = e) (hef : e * f = 0)
    (r r' : O) (h1 : (e - (ι r + q • s)) * e = 0) (h2 : (f - (ι r' + q • s')) * e = 0)
    (hP : ∀ P : Ideal O, P.IsMaximal → (q : O) ∈ P → r' ∈ P → r ∈ P) : e • x ∈ Λ := by
  have hqe : e • q • x ∈ Λ := hΛ e he _ hx
  refine core_mem ι Λ (fun a => hΛ _ (hι a)) q (e • x) (by rw [smul_comm]; exact hqe) r r' ?_ ?_ hP
  · rw [map_sub, map_one, sub_smul, one_smul, wachExpansion_smul_compatible q e e _ s x h1, hee, sub_sub_cancel]
    exact hΛ s hs _ hqe
  · rw [wachExpansion_smul_compatible q e f _ s' x h2, mul_comm, hef, zero_smul, zero_sub]
    exact neg_mem (hΛ _ hs' _ hqe)

theorem mem_of_inert {q : ℕ} (hq : q.Prime) (hin : Formalism.MainNotions.StandardLatticesGL3.InertQ D q) (r : 𝓞 D.host.E)
    (P : Ideal (𝓞 D.host.E)) (hP : P.IsMaximal) (hqP : (q : 𝓞 D.host.E) ∈ P) (hr : GlobalTheory.FinWeil.sgO D r ∈ P) :
    r ∈ P := by
  have hne : P ≠ ⊥ := fun h => by
    rw [h, Ideal.mem_bot] at hqP
    exact hq.ne_zero (by exact_mod_cast hqP)
  have hc := hin P hP.isPrime hne hqP
  rw [← hc] at hr
  exact Ideal.smul_mem_pointwise_smul_iff.1 hr

theorem mul_splitIdem_eq_zero {e : AE D} (he : IsSplitIdem D e) {a : AE D} (ha : finPart D a = 0) : a * e = 0 :=
  adele_ext (by rw [RingHom.map_mul, infPart_splitIdem he, mul_zero, RingHom.map_zero])
    (by rw [RingHom.map_mul, ha, zero_mul, RingHom.map_zero])

theorem finPart_incA_mem (a : 𝓞 D.host.E) : finPart D (incA D (a : D.host.E)) ∈ intAE D :=
  AddSubgroup.subset_closure ⟨1, fun _ => one_mem _, a, rfl⟩

theorem split_mem {S T : HSp D} {e : AE D} (he : IsSplitIdem D e) {Λ : AddSubgroup (WO S T)}
    (hΛ : ∀ a : AE D, finPart D a ∈ intAE D → ∀ u ∈ Λ, a • u ∈ Λ) {q : ℕ} (hq : q.Prime)
    (hin : Formalism.MainNotions.StandardLatticesGL3.InertQ D q) {x : WO S T} (hx : q • x ∈ Λ) : e • x ∈ Λ := by
  have heI : finPart D e ∈ intAE D :=
    GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, he.1])
  obtain ⟨r, s, hs, hs', hz⟩ := approx hq.pos heI
  have h0 : finPart D (e - (incA D (r : D.host.E) + q • s)) = 0 := by rw [RingHom.map_sub, ← hz, sub_self]
  have h0' := finPart_cA_eq_zero h0
  rw [RingHom.map_sub, map_add_nsmul, GlobalTheory.DualPairCheck.cA_incA, GlobalTheory.SplitIdem.star_eq_conj,
    ← GlobalTheory.FinWeil.coe_sgO] at h0'
  exact core_split ((incA D).comp (algebraMap (𝓞 D.host.E) D.host.E)) Λ (fun a => finPart D a ∈ intAE D) hΛ
    finPart_incA_mem q x hx e (cA D e) s (cA D s) heI hs hs' he.1 he.2.1 r (GlobalTheory.FinWeil.sgO D r)
    (mul_splitIdem_eq_zero he h0) (mul_splitIdem_eq_zero he h0') (mem_of_inert hq hin r)

theorem not_dvd_of_saturated {M : Type} [AddCommGroup M] (Λ Λ' : AddSubgroup M) (h0 : Λ.relIndex Λ' ≠ 0)
    {q : ℕ} (hq : q.Prime) (h : ∀ x ∈ Λ', q • x ∈ Λ → x ∈ Λ) : ¬ q ∣ Λ.relIndex Λ' := by
  intro hdvd
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Finite (Λ' ⧸ Λ.addSubgroupOf Λ') := Nat.finite_of_card_ne_zero h0
  obtain ⟨g, hg⟩ := exists_prime_addOrderOf_dvd_card' (G := Λ' ⧸ Λ.addSubgroupOf Λ') q hdvd
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective g
  have hqx : q • (x : M) ∈ Λ := by
    have h := addOrderOf_nsmul_eq_zero (QuotientAddGroup.mk x : Λ' ⧸ Λ.addSubgroupOf Λ')
    rw [hg, ← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff] at h
    exact h
  have h2 : (QuotientAddGroup.mk x : Λ' ⧸ Λ.addSubgroupOf Λ') = 0 :=
    (QuotientAddGroup.eq_zero_iff _).2 (h x x.2 hqx)
  rw [h2, addOrderOf_zero] at hg
  exact hq.one_lt.ne hg

theorem mem_of_parts {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (Λ : AddSubgroup M) (e f : A) (x : M)
    (h1 : e • x ∈ Λ) (h2 : f • x ∈ Λ) (h3 : (1 - (e + f)) • x ∈ Λ) : x ∈ Λ := by
  have h := add_mem (add_mem h1 h2) h3
  rwa [← add_smul, ← add_smul, add_sub_cancel, one_smul] at h

theorem not_dvd_relIndex : ∀ (D : D7) (S T : HSp D) (e : AE D), IsSplitIdem D e → ∀ Λ Λ' : AddSubgroup (WO S T), (∀ a : AE D, finPart D a ∈ intAE D → ∀ u ∈ Λ, a • u ∈ Λ) → (∀ a : AE D, finPart D a ∈ intAE D → ∀ u ∈ Λ', a • u ∈ Λ') → (∀ u ∈ Λ', u.map (infPart D) = 0) → (∀ u ∈ Λ', (1 - (e + cA D e)) • u ∈ Λ) → Λ.relIndex Λ' ≠ 0 → ∀ q : ℕ, q.Prime → Formalism.MainNotions.StandardLatticesGL3.InertQ D q → ¬ q ∣ Λ.relIndex Λ' := by
  intro D S T e he Λ Λ' hΛ _ _ h1 h0 q hq hin
  exact not_dvd_of_saturated Λ Λ' h0 hq fun x hx hqx => mem_of_parts Λ e (cA D e) x
    (split_mem he hΛ hq hin hqx) (split_mem (isSplitIdem_conj he) hΛ hq hin hqx) (h1 x hx)

end GlobalTheory.SplitIndex

end
