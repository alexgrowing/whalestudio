import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingPreservesSupportedUnitarySubgro
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTameRamified
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EventuallyIncAMulMemIntAt

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix
open NumberField
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.IwaIdeals

variable {D : D7}

theorem mem_intAt_iff {P : Pl D → Prop} {a : AE D} :
    a ∈ intAt D P ↔ a ∈ idAt D P ∧ a ∈ GlobalTheory.RamLine.intRing D := by
  rw [GlobalTheory.RamLine.mem_intRing]; rfl

theorem intAt_mul {P : Pl D → Prop} {a b : AE D} (ha : a ∈ intAt D P) (hb : b ∈ intAt D P) :
    a * b ∈ intAt D P :=
  mem_intAt_iff.2 ⟨Ideal.mul_mem_right _ _ (mem_intAt_iff.1 ha).1,
    mul_mem (mem_intAt_iff.1 ha).2 (mem_intAt_iff.1 hb).2⟩

theorem incA_mem_intRing (o : NumberField.RingOfIntegers D.host.E) :
    incA D (o : D.host.E) ∈ GlobalTheory.RamLine.intRing D :=
  (GlobalTheory.NormOneChar.diagInt D.host.F D.host.E o).2

theorem exists_nat_intRing {ι : Type} [Fintype ι] (z : ι → D.host.E) :
    ∃ K : ℕ, 0 < K ∧ ∀ j, (K : AE D) * incA D (z j) ∈ GlobalTheory.RamLine.intRing D := by
  classical
  choose N hN hz using fun j => GlobalTheory.AdIdem.exists_nat_mul_integral D.host.E (z j)
  refine ⟨∏ j, N j, Finset.prod_pos fun j _ => hN j, fun j => ?_⟩
  obtain ⟨c, hc⟩ : N j ∣ ∏ j, N j := Finset.dvd_prod_of_mem N (Finset.mem_univ j)
  obtain ⟨o, ho⟩ := hz j
  have h1 : (N j : AE D) * incA D (z j) = incA D (o : D.host.E) := by
    rw [show (o : D.host.E) = algebraMap _ D.host.E o from rfl, ho, map_mul, map_natCast]
  rw [hc, Nat.cast_mul, mul_comm ((N j : ℕ) : AE D), mul_assoc, h1]
  exact mul_mem (natCast_mem _ c) (incA_mem_intRing o)

theorem mulVec_colMul {k m n : ℕ} (P : Mx D k m) (x : Mx D m n) (i : Fin n) (b : AE D) :
    P *ᵥ colMul x i b = fun l => b * (P ⬝ x) l i := by
  funext l
  simp only [Matrix.mulVec, dotProduct, colMul, Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem hermAt_colMul (S : HSp D) {n : ℕ} (x : Mx D S.rank n) (i : Fin n) (a : AE D) (y : Fin S.rank → AE D) :
    hermAt S (colMul x i a) y = cA D (((adj x ⬝ gA S) *ᵥ y) i) * a := by
  have hG : ∀ k l, cA D (gA S k l) = gA S l k := fun k l => congrFun (congrFun (adj_gA S) l) k
  simp only [hermAt, colMul, Matrix.mulVec, dotProduct, Matrix.mul_apply, adj, Matrix.transpose_apply,
    Matrix.map_apply, map_sum, map_mul, GlobalTheory.RamLine.cA_cA', hG, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem exists_gen_mod {E : Type} [Field E] [NumberField E] (J : Ideal (𝓞 E)) (hJ : J ≠ ⊥) (p : ℤ) (hp : p ≠ 0) :
    ∃ x ∈ J, ∃ n : ℤ, p ∣ n - 1 ∧ ∀ y ∈ J, ∃ z : 𝓞 E, (n : 𝓞 E) * y = z * x := by
  have hp' : (p : 𝓞 E) ≠ 0 := Int.cast_ne_zero.2 hp
  have h0 : Ideal.span {(p : 𝓞 E)} * J ≠ 0 :=
    mul_ne_zero (fun h => hp' (Ideal.span_singleton_eq_bot.1 h)) hJ
  obtain ⟨x, hx⟩ := IsDedekindDomain.exists_sup_span_eq (I := Ideal.span {(p : 𝓞 E)} * J) (J := J)
    Ideal.mul_le_right h0
  have hxJ : x ∈ J := by
    rw [← hx]
    exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self x)
  obtain ⟨n, hn, hle⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup (I := Ideal.span {p})
    (N := (Ideal.span {x}).restrictScalars ℤ) (N' := J.restrictScalars ℤ) (P := J.restrictScalars ℤ)
    (IsNoetherian.noetherian _) le_rfl (by
      intro y hy
      have hy' : y ∈ Ideal.span {(p : 𝓞 E)} * J ⊔ Ideal.span {x} := by rw [hx]; exact hy
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hy'
      obtain ⟨c, hc, rfl⟩ := Ideal.mem_span_singleton_mul.1 ha
      rw [add_comm]
      refine Submodule.add_mem_sup hb ?_
      rw [← zsmul_eq_mul]
      exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self p) hc)
  refine ⟨x, hxJ, n, Ideal.mem_span_singleton.1 hn, fun y hy => ?_⟩
  have : n • y ∈ (Ideal.span {x}).restrictScalars ℤ := hle (Submodule.smul_mem_pointwise_smul y n _ hy)
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 this
  exact ⟨z, by rw [hz, zsmul_eq_mul]⟩

theorem inv_int_mul_mem {v : Pl D} (n : ℤ) (hn : (n : 𝓞 D.host.F) ∉ v.asIdeal) {a : AE D} (ha : a ∈ intAt D (· = v)) :
    incA D (n : D.host.E)⁻¹ * a ∈ intAt D (· = v) := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hn (by rw [Int.cast_zero]; exact zero_mem _)
  have hNF : (n : D.host.F) ≠ 0 := Int.cast_ne_zero.2 hn0
  have hNE : (n : D.host.E) ≠ 0 := Int.cast_ne_zero.2 hn0
  refine ⟨Ideal.mul_mem_left _ _ ha.1, ?_⟩
  have hc : finPart D (incA D (n : D.host.E)⁻¹) = (1 : Af D.host.F) ⊗ₜ[D.host.F] (n : D.host.E)⁻¹ := rfl
  rw [map_mul, hc, ← GlobalTheory.FinPl.AeUnit.idem_mul_finPart D v ha.1, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul,
    one_mul, mul_one]
  refine GlobalTheory.HostAdeleIso.intAE_mul_mem D ?_ ha.2
  refine AddSubgroup.subset_closure ⟨_, GlobalTheory.FinPl.AeUnit.inv_smul_singleV_mem v n hn, 1, ?_⟩
  rw [GlobalTheory.FinPl.AeUnit.tmul_eq_inv_smul_tmul n hNF, zsmul_eq_mul, mul_inv_cancel₀ hNE]
  rfl

theorem mul_mem_intAt_of_intRing {P : Pl D → Prop} {a b : AE D} (ha : a ∈ GlobalTheory.RamLine.intRing D) (hb : b ∈ intAt D P) :
    a * b ∈ intAt D P :=
  mem_intAt_iff.2 ⟨Ideal.mul_mem_left _ _ (mem_intAt_iff.1 hb).1, mul_mem ha (mem_intAt_iff.1 hb).2⟩

theorem intAt_add {P : Pl D → Prop} {a b : AE D} (ha : a ∈ intAt D P) (hb : b ∈ intAt D P) :
    a + b ∈ intAt D P :=
  mem_intAt_iff.2 ⟨add_mem (mem_intAt_iff.1 ha).1 (mem_intAt_iff.1 hb).1,
    add_mem (mem_intAt_iff.1 ha).2 (mem_intAt_iff.1 hb).2⟩

theorem exists_approx {v : Pl D} {ε : AE D} (hεI : ε ∈ intAt D (· = v)) (hε : ∀ a, a ∈ idAt D (· = v) ↔ ε * a = a)
    (M : ℕ) (hM : 0 < M) {a : AE D} (ha : a ∈ intAt D (· = v)) :
    ∃ (o : 𝓞 D.host.E), ∃ t ∈ intAt D (· = v), a = incA D (o : D.host.E) * ε + (M : AE D) * t := by
  obtain ⟨o, w, hw, e⟩ := GlobalTheory.CharFin.exists_int_add_nsmul D.host.F D.host.E M hM (finPart D a)
    (mem_intAt_iff.1 ha).2
  have hME : (M : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  have hi : (M : AE D) * incA D (M : D.host.E)⁻¹ = 1 := by
    rw [← map_natCast (incA D), ← map_mul, mul_inv_cancel₀ hME, map_one]
  have ha' := (hε a).1 ha.1
  refine ⟨o, ε * (incA D (M : D.host.E)⁻¹ * (a - incA D (o : D.host.E))),
    mem_intAt_iff.2 ⟨Ideal.mul_mem_right _ _ hεI.1, mul_mem (mem_intAt_iff.1 hεI).2 ?_⟩, ?_⟩
  · have e1 : finPart D (a - incA D (o : D.host.E)) = finPart D (M : AE D) * w := by
      rw [RingHom.map_sub, map_natCast, ← nsmul_eq_mul]
      exact sub_eq_of_eq_add' e
    have e2 : finPart D (incA D (M : D.host.E)⁻¹ * (a - incA D (o : D.host.E))) = w := by
      rw [RingHom.map_mul, e1, ← mul_assoc, ← RingHom.map_mul, mul_comm _ (M : AE D), hi, RingHom.map_one, one_mul]
    exact (show finPart D (incA D (M : D.host.E)⁻¹ * (a - incA D (o : D.host.E))) ∈
      GlobalTheory.CharFin.hatRing D.host.F D.host.E from by rw [e2]; exact hw)
  · linear_combination (-1 : AE D) * ha' - (ε * (a - incA D (o : D.host.E))) * hi

theorem principal_of_dense {E : Type} [Field E] [NumberField E] {A : Type} [CommRing A] (inc : E →+* A) (O : Set A) (ε : A)
    (hεε : ε * ε = ε) (hfix : ∀ a ∈ O, ε * a = a) (hadd : ∀ a ∈ O, ∀ b ∈ O, a + b ∈ O) (hmul : ∀ a ∈ O, ∀ b ∈ O, a * b ∈ O)
    (hint : ∀ o : 𝓞 E, inc (o : E) * ε ∈ O) (p : ℤ) (hp : p ≠ 0)
    (hinv : ∀ n : ℤ, p ∣ n - 1 → n ≠ 0 ∧ ∀ a ∈ O, inc (n : E)⁻¹ * a ∈ O)
    (happ : ∀ M : ℕ, 0 < M → ∀ a ∈ O, ∃ (o : 𝓞 E), ∃ t ∈ O, a = inc (o : E) * ε + (M : A) * t)
    (I : AddSubgroup A) (N : ℕ) (hN : 0 < N) (hmod : ∀ o ∈ O, ∀ a ∈ I, o * a ∈ I) (hlow : (N : A) * ε ∈ I)
    (hup : ∀ a ∈ I, (N : A) * a ∈ O) :
    ∃ α β : A, α ∈ I ∧ ε * β = β ∧ α * β = ε ∧ ∀ a, ε * a = a → (a ∈ I ↔ a * β ∈ O) := by
  have hNE : (N : E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hi : (N : A) * inc (N : E)⁻¹ = 1 := by
    rw [← map_natCast inc, ← map_mul, mul_inv_cancel₀ hNE, map_one]
  let ι : 𝓞 E →+* A := inc.comp (algebraMap (𝓞 E) E)
  have hι : ∀ o : 𝓞 E, ι o = inc (o : E) := fun _ => rfl
  generalize inc (N : E)⁻¹ = ν at hi
  let J : Ideal (𝓞 E) :=
    { carrier := {o | ι o * (ν * ε) ∈ I}
      zero_mem' := by
        change ι 0 * (ν * ε) ∈ I
        rw [RingHom.map_zero, zero_mul]; exact zero_mem _
      add_mem' := fun {a b} ha hb => by
        change ι (a + b) * (ν * ε) ∈ I
        rw [RingHom.map_add, add_mul]; exact add_mem ha hb
      smul_mem' := fun r o ho => by
        change ι (r * o) * (ν * ε) ∈ I
        have h := hmod _ (hint r) _ ho
        have e : ι (r * o) * (ν * ε) = inc (r : E) * ε * (ι o * (ν * ε)) := by
          rw [RingHom.map_mul, ← hι]
          linear_combination (-(ι r * ι o * ν)) * hεε
        rw [e]; exact h }
  have hJ : ∀ o, o ∈ J ↔ ι o * (ν * ε) ∈ I := fun _ => Iff.rfl
  have hNN : ((N : 𝓞 E) * N) ∈ J := by
    rw [hJ, RingHom.map_mul, map_natCast]
    have e : (N : A) * N * (ν * ε) = N * ε := by linear_combination ((N : A) * ε) * hi
    rw [e]; exact hlow
  have hN' : (N : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hJ0 : J ≠ ⊥ := fun h => mul_ne_zero hN' hN' ((Submodule.mem_bot _).1 (h ▸ hNN))
  obtain ⟨x, hxJ, n, hn, hgen⟩ := exists_gen_mod J hJ0 p hp
  obtain ⟨hn0, hninv⟩ := hinv n hn
  have hx0 : x ≠ 0 := by
    rintro rfl
    obtain ⟨z, hz⟩ := hgen _ hNN
    rw [mul_zero] at hz
    exact mul_ne_zero (Int.cast_ne_zero.2 hn0) (mul_ne_zero hN' hN') hz
  have hxE : (x : E) ≠ 0 := fun h => hx0 (RingOfIntegers.coe_eq_zero_iff.1 h)
  have hx : ι x * inc (x : E)⁻¹ = 1 := by
    rw [hι, ← map_mul, mul_inv_cancel₀ hxE, map_one]
  have hni : (n : A) * inc (n : E)⁻¹ = 1 := by
    rw [← map_intCast inc, ← map_mul, mul_inv_cancel₀ (Int.cast_ne_zero.2 hn0), map_one]
  generalize inc (x : E)⁻¹ = ξ at hx
  have key : ∀ y ∈ J, ι y * ξ * ε ∈ O := by
    intro y hy
    obtain ⟨z, hz⟩ := hgen y hy
    have h1 := congrArg ι hz
    rw [RingHom.map_mul, RingHom.map_mul, map_intCast] at h1
    have h2 := hninv _ (hint z)
    rw [← hι] at h2
    generalize inc (n : E)⁻¹ = μ at hni h2
    have e : ι y * ξ * ε = μ * (ι z * ε) := by
      linear_combination (-(ι y * ξ * ε)) * hni + (μ * ξ * ε) * h1 + (μ * ι z * ε) * hx
    rw [e]; exact h2
  have hα : ι x * (ν * ε) ∈ I := hxJ
  have hαβ : ι x * (ν * ε) * ((N : A) * ξ * ε) = ε := by
    linear_combination (ι x * ν * N * ξ) * hεε + (ι x * ξ * ε) * hi + ε * hx
  refine ⟨ι x * (ν * ε), (N : A) * ξ * ε, hα, by linear_combination ((N : A) * ξ) * hεε, hαβ, fun a ha => ⟨fun h => ?_, fun h => ?_⟩⟩
  · obtain ⟨o, t, ht, e⟩ := happ (N * N) (Nat.mul_pos hN hN) _ (hup a h)
    rw [← hι, Nat.cast_mul] at e
    have ht' := hfix t ht
    have e1 : a = ι o * (ν * ε) + t * ((N : A) * ε) := by
      linear_combination ν * e - a * hi + ((N : A) * t) * hi - (N : A) * ht'
    have ho : o ∈ J := by
      rw [hJ, eq_sub_of_add_eq e1.symm]
      exact sub_mem h (hmod t ht _ hlow)
    have e2 : a * ((N : A) * ξ * ε) = ι o * ξ * ε + t * (ι ((N : 𝓞 E) * N) * ξ * ε) := by
      rw [RingHom.map_mul, map_natCast]
      linear_combination (ξ * ε) * e + (ι o * ξ) * hεε
    rw [e2]
    exact hadd _ (key o ho) _ (hmul _ ht _ (key _ hNN))
  · have e : a = a * ((N : A) * ξ * ε) * (ι x * (ν * ε)) := by
      linear_combination (-1 : A) * ha - a * hαβ
    rw [e]
    exact hmod _ h _ hα

theorem principal_at {v : Pl D} {ε : AE D} (hεI : ε ∈ intAt D (· = v)) (hε : ∀ a, a ∈ idAt D (· = v) ↔ ε * a = a)
    (I : AddSubgroup (AE D)) (N : ℕ) (hN : 0 < N) (hI : ∀ a ∈ I, a ∈ idAt D (· = v))
    (hmod : ∀ o ∈ intAt D (· = v), ∀ a ∈ I, o * a ∈ I) (hlow : (N : AE D) * ε ∈ I)
    (hup : ∀ a ∈ I, (N : AE D) * a ∈ intAt D (· = v)) :
    ∃ α β : AE D, α ∈ idAt D (· = v) ∧ β ∈ idAt D (· = v) ∧ α * β = ε ∧
      ∀ a ∈ idAt D (· = v), a ∈ I ↔ a * β ∈ intAt D (· = v) := by
  have hinv : ∀ n : ℤ, ((Ideal.absNorm v.asIdeal : ℕ) : ℤ) ∣ n - 1 →
      n ≠ 0 ∧ ∀ a ∈ intAt D (· = v), incA D (n : D.host.E)⁻¹ * a ∈ intAt D (· = v) := by
    rintro n ⟨c, hc⟩
    have hnv : (n : 𝓞 D.host.F) ∉ v.asIdeal := by
      intro h
      have h1 : ((n - 1 : ℤ) : 𝓞 D.host.F) ∈ v.asIdeal := by
        rw [hc, Int.cast_mul, Int.cast_natCast]
        exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)
      have h2 := sub_mem h h1
      rw [Int.cast_sub, Int.cast_one, sub_sub_cancel] at h2
      exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h2)
    refine ⟨?_, fun a ha => inv_int_mul_mem n hnv ha⟩
    rintro rfl
    exact hnv (by rw [Int.cast_zero]; exact zero_mem _)
  obtain ⟨α, β, h1, h2, h3, h4⟩ := principal_of_dense (incA D) (intAt D (· = v)) ε ((hε ε).1 hεI.1)
    (fun a ha => (hε a).1 ha.1) (fun a ha b hb => intAt_add ha hb) (fun a ha b hb => intAt_mul ha hb)
    (fun o => mul_mem_intAt_of_intRing (incA_mem_intRing o) hεI) _
    (Int.natCast_ne_zero.2 fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)) hinv
    (fun M hM a ha => exists_approx hεI hε M hM ha) I N hN hmod hlow hup
  exact ⟨α, β, hI α h1, (hε β).2 h2, h3, fun a ha => h4 a ((hε a).1 ha)⟩

theorem colMul_add {m n : ℕ} (x : Mx D m n) (i : Fin n) (a b : AE D) :
    colMul x i (a + b) = colMul x i a + colMul x i b := funext fun k => add_mul a b (x k i)

theorem mul_eq_of_unit {A : Type} [CommRing A] {ε a α β : A} (t : A) (ha : ε * a = a) (h : α * β = ε) :
    t * a = t * β * (a * α) := by
  linear_combination (-t) * ha - (t * a) * h

theorem mul_rearr {A : Type} [CommRing A] (m K ε x : A) : m * K * ε * x = m * (K * x * ε) := by ring

set_option maxHeartbeats 800000 in

theorem ideals_at_place : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L : Lat S) (L₀ : Lat S₀) (v : Pl D) (ε : AE D) (hεε : ε * ε = ε) (hεc : cA D ε = ε) (hεI : ε ∈ intAt D (· = v)) (hε : ∀ a, a ∈ idAt D (· = v) ↔ ε * a = a), IsSDAt S v (latV S L (· = v)) → MonoAt d L L₀ v → ∃ α β : Fin ρ → AE D, (∀ i, α i ∈ idAt D (· = v)) ∧ (∀ i, β i ∈ idAt D (· = v)) ∧ (∀ i, α i * β i = ε) ∧ (∀ i, ∀ a ∈ idAt D (· = v), colMul d.jX i a ∈ latV S L (· = v) ↔ a * β i ∈ intAt D (· = v)) ∧ (∀ i, ∀ a ∈ idAt D (· = v), colMul d.jY i a ∈ latV S L (· = v) ↔ a * cA D (α i) ∈ intAt D (· = v)) := by
  intro D S S₀ ρ d L L₀ v ε hεε hεc hεI hε hSD hMono
  unfold MonoAt at hMono
  generalize latV S L (· = v) = Λ at hSD hMono ⊢
  obtain ⟨hsupp, ⟨m, hm, hmul⟩, hdual⟩ := hSD
  have hpair : ∀ y ∈ Λ, ∀ x ∈ Λ, hermAt S y x ∈ intAt D (· = v) := fun y hy => (hdual y (hsupp y hy)).1 hy
  have hc : ∀ a ∈ intAt D (· = v), cA D a ∈ intAt D (· = v) := fun a ha =>
    mem_intAt_iff.2 ⟨(hε _).2 (by rw [← hεc, ← RingHom.map_mul, (hε a).1 ha.1]),
      GlobalTheory.RamLine.cA_mem (mem_intAt_iff.1 ha).2⟩
  have hX : ∀ i a y, hermAt S (colMul d.jX i a) y = cA D ((d.pY *ᵥ y) i) * a := fun i a y => by
    rw [hermAt_colMul, d.pY_eq]
  have hY : ∀ i a y, hermAt S (colMul d.jY i a) y = cA D ((d.pX *ᵥ y) i) * a := fun i a y => by
    rw [hermAt_colMul, d.pX_eq]
  obtain ⟨K, hK, hKz⟩ := exists_nat_intRing (D := D)
    (Sum.elim (fun p : Fin S.rank × Fin ρ => d.e p.1 p.2) (fun p : Fin S.rank × Fin ρ => d.e' p.1 p.2))
  have hcol : ∀ (x : Mx D S.rank ρ) (i : Fin ρ), (∀ k, (K : AE D) * x k i ∈ GlobalTheory.RamLine.intRing D) →
      colMul x i (((m * K : ℕ) : AE D) * ε) ∈ Λ := by
    intro x i h
    have h1 := hmul (fun k => (K : AE D) * x k i * ε) fun k => mul_mem_intAt_of_intRing (h k) hεI
    have e : colMul x i (((m * K : ℕ) : AE D) * ε) = (m : AE D) • fun k => (K : AE D) * x k i * ε := by
      funext k
      rw [Pi.smul_apply, smul_eq_mul, Nat.cast_mul, colMul]
      exact mul_rearr _ _ _ _
    rw [e]; exact h1
  have key : ∀ i, ∃ α β : AE D, α ∈ idAt D (· = v) ∧ β ∈ idAt D (· = v) ∧ α * β = ε ∧
      ∀ a ∈ idAt D (· = v), colMul d.jX i a ∈ Λ ↔ a * β ∈ intAt D (· = v) := by
    intro i
    let I : AddSubgroup (AE D) :=
      Λ.comap (AddMonoidHom.mk' (colMul d.jX i) (colMul_add d.jX i)) ⊓ (idAt D (· = v)).toAddSubgroup
    have hI : ∀ a, a ∈ I ↔ colMul d.jX i a ∈ Λ ∧ a ∈ idAt D (· = v) := fun _ => Iff.rfl
    obtain ⟨α, β, h1, h2, h3, h4⟩ := principal_at hεI hε I (m * K) (Nat.mul_pos hm hK) (fun a ha => ((hI a).1 ha).2)
      (fun o ho a ha => by
        obtain ⟨ha1, ha2⟩ := (hI a).1 ha
        have hoa : o * a ∈ idAt D (· = v) := Ideal.mul_mem_left _ _ ha2
        refine (hI _).2 ⟨(hdual (colMul d.jX i (o * a)) fun k => Ideal.mul_mem_right _ _ hoa).2 fun x hx => ?_, hoa⟩
        have h := hpair _ ha1 x hx
        rw [hX] at h ⊢
        rw [mul_left_comm]
        exact intAt_mul ho h)
      ((hI _).2 ⟨hcol d.jX i fun k => hKz (Sum.inl (k, i)), Ideal.mul_mem_left _ _ hεI.1⟩)
      (fun a ha => by
        obtain ⟨ha1, ha2⟩ := (hI a).1 ha
        have h := hpair _ ha1 _ (hcol d.jY i fun k => hKz (Sum.inr (k, i)))
        rw [hX, mulVec_colMul, d.pY_jY] at h
        simp only [Matrix.one_apply_eq, mul_one] at h
        rwa [RingHom.map_mul, map_natCast, hεc, mul_assoc, (hε a).1 ha2] at h)
    exact ⟨α, β, h1, h2, h3, fun a ha => ⟨fun h => (h4 a ha).1 ((hI a).2 ⟨h, ha⟩), fun h => ((hI a).1 ((h4 a ha).2 h)).1⟩⟩
  choose α β h1 h2 h3 h4 using key
  refine ⟨α, β, h1, h2, h3, h4, fun i a ha => ⟨fun h => ?_, fun h => ?_⟩⟩
  · have h5 := hpair _ h _ ((h4 i _ (h1 i)).2 (by rw [h3]; exact hεI))
    rw [hY, mulVec_colMul, d.pX_jX] at h5
    simp only [Matrix.one_apply_eq, mul_one] at h5
    rwa [mul_comm] at h5
  · refine (hdual (colMul d.jY i a) fun k => Ideal.mul_mem_right _ _ ha).2 fun x hx => ?_
    have ht := (h4 i _ (mulVec_mem_idAt d.pX (hsupp x hx) i)).1 (((hMono x).1 hx).1 i)
    have h5 := intAt_mul (hc _ ht) h
    have h6 := congrArg (cA D) (h3 i)
    rw [RingHom.map_mul, hεc] at h6
    rw [RingHom.map_mul] at h5
    rw [hY]
    exact (mul_eq_of_unit (cA D ((d.pX *ᵥ x) i)) ((hε a).1 ha) h6).symm ▸ h5

end GlobalTheory.IwaIdeals

end
