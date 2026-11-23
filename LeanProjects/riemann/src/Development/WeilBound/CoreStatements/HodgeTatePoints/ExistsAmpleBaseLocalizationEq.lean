import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsLastRest
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsSumEqOneOfMulEqOne
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PGraphClosedLocal
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PAmpleAffineGen

namespace PositivityTheory.HtPt.KtwS.SectionsOverLocalization

open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver)

noncomputable section

section LocRings

variable {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω]

theorem coe_ne_zero_of_not_mem_ideal {A : Subalgebra S Ω} {p : Ideal A} {b : A} (hb : b ∉ p) : (b : Ω) ≠ 0 := by
  intro h
  apply hb
  rw [show b = 0 from Subtype.ext h]
  exact p.zero_mem

theorem mem_locIn_iff (A : Subalgebra S Ω) (p : Ideal A) [hp : p.IsPrime] (z : Ω) :
    z ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn A p ↔ ∃ a b : A, b ∉ p ∧ z = a / b := by
  have h1 : (1 : A) ∉ p := fun h => hp.ne_top ((Ideal.eq_top_iff_one _).mpr h)
  constructor
  · intro hz
    let R : Subring Ω :=
      { carrier := {z | ∃ a b : A, b ∉ p ∧ z = a / b}
        mul_mem' := by
          rintro _ _ ⟨a, b, hb, rfl⟩ ⟨a', b', hb', rfl⟩
          exact ⟨a * a', b * b', fun h => (hp.mem_or_mem h).elim hb hb', by
            simp only [Subalgebra.coe_mul]; rw [div_mul_div_comm]⟩
        one_mem' := ⟨1, 1, h1, by simp⟩
        add_mem' := by
          rintro _ _ ⟨a, b, hb, rfl⟩ ⟨a', b', hb', rfl⟩
          exact ⟨a * b' + b * a', b * b', fun h => (hp.mem_or_mem h).elim hb hb', by
            simp only [Subalgebra.coe_mul, Subalgebra.coe_add]
            rw [div_add_div _ _ (coe_ne_zero_of_not_mem_ideal hb) (coe_ne_zero_of_not_mem_ideal hb')]⟩
        zero_mem' := ⟨0, 1, h1, by simp⟩
        neg_mem' := by
          rintro _ ⟨a, b, hb, rfl⟩
          exact ⟨-a, b, hb, by simp [neg_div]⟩ }
    have hle : IndefiniteRowSideFullHecke.Kleiman2.locIn A p ≤ R := Subring.closure_le.mpr fun z hz => hz
    exact hle hz
  · rintro ⟨a, b, hb, rfl⟩
    exact Subring.subset_closure ⟨a, b, hb, rfl⟩

theorem le_locIn (A : Subalgebra S Ω) (p : Ideal A) [hp : p.IsPrime] {a : Ω} (ha : a ∈ A) :
    a ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn A p :=
  (mem_locIn_iff A p a).mpr ⟨⟨a, ha⟩, 1, fun h => hp.ne_top ((Ideal.eq_top_iff_one _).mpr h), by simp⟩

def locAlg (A : Subalgebra S Ω) (p : Ideal A) [p.IsPrime] : Subalgebra S Ω :=
  { (IndefiniteRowSideFullHecke.Kleiman2.locIn A p).toSubsemiring with
    algebraMap_mem' := fun r => le_locIn A p (A.algebraMap_mem r) }

def locMax (A : Subalgebra S Ω) (p : Ideal A) [hp : p.IsPrime] : Ideal (locAlg A p) where
  carrier := {z | ∃ a b : A, a ∈ p ∧ b ∉ p ∧ (z : Ω) = a / b}
  add_mem' := by
    rintro z z' ⟨a, b, ha, hb, hz⟩ ⟨a', b', ha', hb', hz'⟩
    refine ⟨a * b' + b * a', b * b', p.add_mem (p.mul_mem_right _ ha) (p.mul_mem_left _ ha'),
      fun h => (hp.mem_or_mem h).elim hb hb', ?_⟩
    simp only [Subalgebra.coe_add, Subalgebra.coe_mul]
    rw [hz, hz', div_add_div _ _ (coe_ne_zero_of_not_mem_ideal hb) (coe_ne_zero_of_not_mem_ideal hb')]
  zero_mem' := ⟨0, 1, p.zero_mem, fun h => hp.ne_top ((Ideal.eq_top_iff_one _).mpr h), by simp⟩
  smul_mem' := by
    rintro c z ⟨a, b, ha, hb, hz⟩
    obtain ⟨u, v, hv, hc⟩ := (mem_locIn_iff A p c).mp c.2
    refine ⟨u * a, v * b, p.mul_mem_left _ ha, fun h => (hp.mem_or_mem h).elim hv hb, ?_⟩
    simp only [smul_eq_mul, Subalgebra.coe_mul]
    rw [hz, hc, div_mul_div_comm]

theorem locMax_isPrime (A : Subalgebra S Ω) (p : Ideal A) [hp : p.IsPrime] : (locMax A p).IsPrime := by
  refine ⟨?_, ?_⟩
  · rw [Ne, Ideal.eq_top_iff_one]
    rintro ⟨a, b, ha, hb, h1⟩
    have hb0 := coe_ne_zero_of_not_mem_ideal hb
    have hab : (a : Ω) = b := by
      rw [eq_div_iff hb0] at h1
      simpa using h1.symm
    exact hb (by rw [show b = a from Subtype.ext hab.symm]; exact ha)
  · rintro z z' ⟨a, b, ha, hb, hzz⟩
    obtain ⟨u, v, hv, hz⟩ := (mem_locIn_iff A p z).mp z.2
    obtain ⟨u', v', hv', hz'⟩ := (mem_locIn_iff A p z').mp z'.2
    have hv0 := coe_ne_zero_of_not_mem_ideal hv
    have hv0' := coe_ne_zero_of_not_mem_ideal hv'
    have hb0 := coe_ne_zero_of_not_mem_ideal hb
    have key : u * u' * b = a * (v * v') := by
      apply Subtype.ext
      simp only [Subalgebra.coe_mul] at hzz ⊢
      rw [hz, hz', div_mul_div_comm, div_eq_div_iff (mul_ne_zero hv0 hv0') hb0] at hzz
      rw [hzz]
    have hmem : u * u' * b ∈ p := by rw [key]; exact p.mul_mem_right _ ha
    rcases hp.mem_or_mem hmem with h | h
    · rcases hp.mem_or_mem h with h | h
      · exact Or.inl ⟨u, v, h, hv, hz⟩
      · exact Or.inr ⟨u', v', h, hv', hz'⟩
    · exact absurd h hb

instance (A : Subalgebra S Ω) (p : Ideal A) [p.IsPrime] : (locMax A p).IsPrime := locMax_isPrime A p

theorem inv_mem_of_not_mem_locMax {A : Subalgebra S Ω} {p : Ideal A} [hp : p.IsPrime] {z : locAlg A p}
    (hz : z ∉ locMax A p) : (z : Ω) ≠ 0 ∧ (z : Ω)⁻¹ ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn A p := by
  obtain ⟨u, v, hv, huv⟩ := (mem_locIn_iff A p z).mp z.2
  have hu : u ∉ p := fun hu => hz ⟨u, v, hu, hv, huv⟩
  refine ⟨?_, ?_⟩
  · rw [huv]
    exact div_ne_zero (coe_ne_zero_of_not_mem_ideal hu) (coe_ne_zero_of_not_mem_ideal hv)
  · rw [huv, inv_div]
    exact Subring.subset_closure ⟨v, u, hu, rfl⟩

theorem not_mem_locMax_of_inv_mem {A : Subalgebra S Ω} {p : Ideal A} [hp : p.IsPrime] {z : locAlg A p}
    (hz0 : (z : Ω) ≠ 0) (hz : (z : Ω)⁻¹ ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn A p) : z ∉ locMax A p := by
  rintro ⟨a, b, ha, hb, hab⟩
  obtain ⟨c, d, hd, hcd⟩ := (mem_locIn_iff A p _).mp hz
  have hb0 := coe_ne_zero_of_not_mem_ideal hb
  have hd0 := coe_ne_zero_of_not_mem_ideal hd
  have key : b * d = a * c := by
    apply Subtype.ext
    simp only [Subalgebra.coe_mul]
    have h1 : (z : Ω) * (z : Ω)⁻¹ = 1 := mul_inv_cancel₀ hz0
    rw [hcd] at h1
    rw [hab, div_mul_div_comm, div_eq_one_iff_eq (mul_ne_zero hb0 hd0)] at h1
    exact h1.symm
  have hmem : b * d ∈ p := by rw [key]; exact p.mul_mem_right _ ha
  exact (hp.mem_or_mem hmem).elim hb hd

theorem not_mem_locMax_of_not_mem {A : Subalgebra S Ω} {p : Ideal A} [hp : p.IsPrime] {a : A} (ha : a ∉ p) :
    (⟨a, le_locIn A p a.2⟩ : locAlg A p) ∉ locMax A p := by
  have ha0 : (a : Ω) ≠ 0 := coe_ne_zero_of_not_mem_ideal ha
  refine not_mem_locMax_of_inv_mem ha0 ?_
  rw [show ((a : Ω))⁻¹ = (1 : A) / a by simp]
  exact Subring.subset_closure ⟨1, a, ha, rfl⟩

theorem locIn_comap_eq (A T : Subalgebra S Ω) (p : Ideal A) [hp : p.IsPrime] (hT : T ≤ locAlg A p)
    (hA : ∀ a ∈ A, a ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn T ((locMax A p).comap (Subalgebra.inclusion hT))) :
    IndefiniteRowSideFullHecke.Kleiman2.locIn T ((locMax A p).comap (Subalgebra.inclusion hT)) = IndefiniteRowSideFullHecke.Kleiman2.locIn A p := by
  have : ((locMax A p).comap (Subalgebra.inclusion hT)).IsPrime := Ideal.comap_isPrime _ _
  apply le_antisymm
  · refine Subring.closure_le.mpr ?_
    rintro _ ⟨t, t', ht', rfl⟩
    obtain ⟨-, hinv⟩ := inv_mem_of_not_mem_locMax (z := Subalgebra.inclusion hT t') ht'
    rw [div_eq_mul_inv]
    exact (IndefiniteRowSideFullHecke.Kleiman2.locIn A p).mul_mem (hT t.2) hinv
  · refine Subring.closure_le.mpr ?_
    rintro _ ⟨a, b, hb, rfl⟩
    rw [div_eq_mul_inv]
    refine Subring.mul_mem _ (hA a a.2) ?_
    obtain ⟨t, t', ht', hbt⟩ := (mem_locIn_iff T _ b).mp (hA b b.2)
    have hb0 := coe_ne_zero_of_not_mem_ideal hb
    have ht'0 := coe_ne_zero_of_not_mem_ideal ht'
    have htt : (t : Ω) = b * t' := by rw [hbt]; field_simp
    have ht : t ∉ (locMax A p).comap (Subalgebra.inclusion hT) := by
      intro h
      have e : Subalgebra.inclusion hT t = (⟨b, le_locIn A p b.2⟩ : locAlg A p) * Subalgebra.inclusion hT t' :=
        Subtype.ext (by simp [htt])
      rw [Ideal.mem_comap, e] at h
      rcases (locMax_isPrime A p).mem_or_mem h with h | h
      · exact not_mem_locMax_of_not_mem hb h
      · exact ht' h
    rw [show ((b : Ω))⁻¹ = t' / t by rw [hbt, inv_div]]
    exact Subring.subset_closure ⟨t', t, ht, rfl⟩

theorem mem_of_forall_locIn (B : Subalgebra S Ω) (z : Ω)
    (h : ∀ q : Ideal B, q.IsPrime → z ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn B q) : z ∈ B := by
  by_contra hz
  obtain ⟨q, hq, hle⟩ := Ideal.exists_le_maximal (mulMemIdeal B z) (by
    rw [Ne, Ideal.eq_top_iff_one]
    intro h1
    apply hz
    simpa [mulMemIdeal] using h1)
  have := hq.isPrime
  obtain ⟨a, b, hb, hab⟩ := (mem_locIn_iff B q z).mp (h q hq.isPrime)
  apply hb
  apply hle
  show (b : Ω) * z ∈ B
  have hb0 := coe_ne_zero_of_not_mem_ideal hb
  rw [show (b : Ω) * z = a by rw [hab]; field_simp]
  exact a.2

theorem mem_of_pow_mul_mem' (A : Subalgebra S Ω) (M : Submodule A Ω) {m : ℕ} (e : Fin m → A)
    (he : ∑ c, e c = 1) (t : Ω) (h : ∀ c, ∃ K : ℕ, (e c : Ω) ^ K * t ∈ M) : t ∈ M := by
  classical
  choose K hK using h
  let D : Ideal A := M.comap (LinearMap.toSpanSingleton A Ω t)
  have hspan : Ideal.span (Set.range e) = ⊤ := by
    rw [Ideal.eq_top_iff_one, ← he]
    exact Ideal.sum_mem _ fun c _ => Ideal.subset_span ⟨c, rfl⟩
  have hpow := Ideal.span_pow_eq_top _ hspan (∑ c, K c)
  have hle : Ideal.span ((fun a => a ^ (∑ c, K c)) '' Set.range e) ≤ D := by
    rw [Ideal.span_le]
    rintro _ ⟨_, ⟨c, rfl⟩, rfl⟩
    have hc : K c ≤ ∑ c, K c := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
    show (LinearMap.toSpanSingleton A Ω t) (e c ^ ∑ c, K c) ∈ M
    rw [LinearMap.toSpanSingleton_apply, ← Nat.sub_add_cancel hc, pow_add, mul_smul]
    refine M.smul_mem _ ?_
    have := hK c
    rwa [Subalgebra.smul_def, smul_eq_mul, SubmonoidClass.coe_pow]
  rw [hpow] at hle
  have h1 := hle (Submodule.mem_top : (1 : A) ∈ ⊤)
  simpa [D] using h1

theorem chartRingOver_oneBlock_eq_adjoin {n : ℕ} (h : Fin n → Ω) (c : Unit → Fin n) :
    chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock h) c = Algebra.adjoin S (Set.range fun b => h b / h (c ())) := by
  unfold chartRingOver
  congr 1
  ext z
  constructor
  · rintro ⟨⟨⟨⟩, a⟩, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨⟨(), a⟩, rfl⟩

theorem div_mem_chartRingOver_oneBlock {n : ℕ} (h : Fin n → Ω) (l b : Fin n) :
    h b / h l ∈ chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock h) (fun _ => l) :=
  Algebra.subset_adjoin ⟨⟨(), b⟩, rfl⟩

end LocRings

section Forward

variable {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem exists_inv_of_span_eq (Q : Kleiman.LineBundle S x) {m : ℕ} (h : Fin m → Ω)
    {i : Fin (N + 1)} (hi : x i ≠ 0)
    (hgen : Submodule.span (Kleiman.chartRing S x (Kleiman.singleChart hi)) (Set.range h) =
      Q.sub (Kleiman.singleChart hi)) :
    ∃ w : Fin m → Ω, (∀ a b, h a * w b ∈ Kleiman.chartRing S x (Kleiman.singleChart hi)) ∧
      ∑ b, h b * w b = 1 := by
  obtain ⟨Q', hQ'⟩ := Q.invertible (Kleiman.singleChart hi)
  rw [← hgen] at hQ'
  exact exists_sum_eq_one_of_mul_eq_one _ Q' _ hQ'

theorem exists_not_mem_of_sum_eq_one {T : Subalgebra S Ω} (q : Ideal T) [hq : q.IsPrime] {K : ℕ}
    (a b : Fin K → Ω) (ha : ∀ k, a k ∈ T) (hb : ∀ k, b k ∈ T) (hab : ∑ k, a k * b k = 1) :
    ∃ k, (⟨b k, hb k⟩ : T) ∉ q := by
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  apply hq.ne_top
  rw [Ideal.eq_top_iff_one]
  have h1 : (1 : T) = ∑ k, (⟨a k, ha k⟩ : T) * ⟨b k, hb k⟩ := by
    apply Subtype.ext
    simp only [Subalgebra.coe_one, AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_mul]
    exact hab.symm
  rw [h1]
  exact Ideal.sum_mem _ fun k _ => q.mul_mem_left _ (hcon k)

theorem exists_ampleBase_localization_eq (Q : Kleiman.LineBundle S x) {r : ℕ} {h : Fin (r + 1) → Ω}
    (hva : Kleiman.IsVeryAmpleBy Q.toSubSystem h) {i : Fin (N + 1)} (hi : x i ≠ 0) (A : Subalgebra S Ω)
    (hA : A = Kleiman.chartRing S x (Kleiman.singleChart hi)) (p : Ideal A) [hp : p.IsPrime] :
    ∃ l, h l ≠ 0 ∧ ∃ q : Ideal (chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock h) (fun _ => l)), q.IsPrime ∧
      IndefiniteRowSideFullHecke.Kleiman2.locIn _ q = IndefiniteRowSideFullHecke.Kleiman2.locIn A p := by
  obtain ⟨w, hw', hsum⟩ := exists_inv_of_span_eq Q h hi (hva.generates _)
  have hw : ∀ a b, h a * w b ∈ A := fun a b => by rw [hA]; exact hw' a b
  obtain ⟨l, hl⟩ := exists_not_mem_of_sum_eq_one p (fun _ => (1 : Ω)) (fun k => h k * w k)
    (fun _ => A.one_mem) (fun k => hw k k) (by simpa using hsum)
  have hl0 : h l * w l ≠ 0 := coe_ne_zero_of_not_mem_ideal hl
  have hhl : h l ≠ 0 := left_ne_zero_of_mul hl0
  have hwl : w l ≠ 0 := right_ne_zero_of_mul hl0
  set B := chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock h) (fun _ => l) with hBdef
  have hBeq : B = Kleiman.ampleBase (S := S) h l := chartRingOver_oneBlock_eq_adjoin h _
  have hBA : B ≤ locAlg A p := by
    intro y hy
    rw [hBeq] at hy
    refine (Algebra.adjoin_le ?_) hy
    rintro _ ⟨c, rfl⟩
    have e : h c / h l = (h c * w l) / (h l * w l) := by field_simp
    show h c / h l ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn A p
    rw [e]
    exact Subring.subset_closure ⟨⟨_, hw c l⟩, ⟨_, hw l l⟩, hl, rfl⟩
  refine ⟨l, hhl, _, Ideal.comap_isPrime _ _, locIn_comap_eq A B p hBA ?_⟩
  intro z hz
  obtain ⟨K, a, b, J, ha, hb, hab, hbJ⟩ := hva.affine l hhl
  have hAmB : ∀ y ∈ Kleiman.ampleRing Q.toSubSystem 1 (h l), y ∈ B := fun y hy => by
    rw [hBeq]; exact hva.closed l hhl hy
  obtain ⟨k, hk⟩ := exists_not_mem_of_sum_eq_one ((locMax A p).comap (Subalgebra.inclusion hBA)) a b
    (fun k => hAmB _ (ha k)) (fun k => hAmB _ (hb k)) hab
  obtain ⟨hb0, hbinv⟩ := inv_mem_of_not_mem_locMax (z := Subalgebra.inclusion hBA ⟨b k, hAmB _ (hb k)⟩) hk
  have hb0' : b k ≠ 0 := hb0
  have hbinv' : (b k)⁻¹ ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn A p := hbinv
  rw [hA] at hz
  have hzU : z ∈ Kleiman.chartRing S x (AmpleAffineGen.unionChart (J k) (Kleiman.singleChart hi)) :=
    Kleiman.chartRing_mono (AmpleAffineGen.subset_unionChart_right _ _) hz
  obtain ⟨D, hD⟩ := AmpleAffineGen.exists_pow_mul_mem (J k) (Kleiman.singleChart hi) hzU
  have hu : AmpleAffineGen.chartRatio (J k) (Kleiman.singleChart hi) ∈ Kleiman.chartRing S x (J k) :=
    AmpleAffineGen.chartRatio_mem _ _
  have huv := AmpleAffineGen.chartRatio_mul_chartRatio (Kleiman.singleChart hi) (J k)
  have huinv : (AmpleAffineGen.chartRatio (J k) (Kleiman.singleChart hi))⁻¹ =
      AmpleAffineGen.chartRatio (Kleiman.singleChart hi) (J k) := (eq_inv_of_mul_eq_one_right huv).symm
  have hu0 : AmpleAffineGen.chartRatio (J k) (Kleiman.singleChart hi) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at huv
    exact zero_ne_one huv
  obtain ⟨e₁, he₁⟩ := GraphClosedAlt.exists_pow_mul_mem_ampleRing Q.toSubSystem (h l) (b k) (J k) (hb k)
    (hbJ k) hD
  obtain ⟨e₂, he₂⟩ := GraphClosedAlt.exists_pow_mul_mem_ampleRing Q.toSubSystem (h l) (b k) (J k) (hb k)
    (hbJ k) (pow_mem hu D)
  set u := AmpleAffineGen.chartRatio (J k) (Kleiman.singleChart hi) with hudef
  have hγB : b k ^ (e₁ + e₂) * u ^ D ∈ B := by
    have e : b k ^ (e₁ + e₂) * u ^ D = b k ^ e₁ * (b k ^ e₂ * u ^ D) := by rw [pow_add]; ring
    rw [e]
    exact B.mul_mem (B.pow_mem (hAmB _ (hb k)) _) (hAmB _ he₂)
  have hβB : b k ^ (e₁ + e₂) * u ^ D * z ∈ B := by
    have e : b k ^ (e₁ + e₂) * u ^ D * z = b k ^ e₂ * (b k ^ e₁ * (u ^ D * z)) := by rw [pow_add]; ring
    rw [e]
    exact B.mul_mem (B.pow_mem (hAmB _ (hb k)) _) (hAmB _ he₁)
  have hγ0 : b k ^ (e₁ + e₂) * u ^ D ≠ 0 := mul_ne_zero (pow_ne_zero _ hb0') (pow_ne_zero _ hu0)
  have hγq : (⟨_, hγB⟩ : B) ∉ (locMax A p).comap (Subalgebra.inclusion hBA) := by
    rw [Ideal.mem_comap]
    refine not_mem_locMax_of_inv_mem hγ0 ?_
    have e : (b k ^ (e₁ + e₂) * u ^ D)⁻¹ = ((b k)⁻¹) ^ (e₁ + e₂) * (u⁻¹) ^ D := by
      rw [mul_inv, inv_pow, inv_pow]
    show (b k ^ (e₁ + e₂) * u ^ D)⁻¹ ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn A p
    rw [e, huinv]
    refine Subring.mul_mem _ (Subring.pow_mem _ hbinv' _) (Subring.pow_mem _ ?_ _)
    exact le_locIn A p (by rw [hA]; exact AmpleAffineGen.chartRatio_mem _ _)
  have := Ideal.comap_isPrime (Subalgebra.inclusion hBA) (locMax A p)
  rw [mem_locIn_iff]
  refine ⟨⟨_, hβB⟩, ⟨_, hγB⟩, hγq, ?_⟩
  show z = b k ^ (e₁ + e₂) * u ^ D * z / (b k ^ (e₁ + e₂) * u ^ D)
  rw [mul_div_cancel_left₀ z hγ0]

theorem exists_ampleBase_locIn_eq (Q : Kleiman.LineBundle S x) {r : ℕ} {h : Fin (r + 1) → Ω}
    (hva : Kleiman.IsVeryAmpleBy Q.toSubSystem h) {i : Fin (N + 1)} (hi : x i ≠ 0)
    (p : Ideal (chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) (fun _ => i))) (hp : p.IsPrime) :
    ∃ l, h l ≠ 0 ∧ ∃ q : Ideal (chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock h) (fun _ => l)), q.IsPrime ∧
      IndefiniteRowSideFullHecke.Kleiman2.locIn _ q = IndefiniteRowSideFullHecke.Kleiman2.locIn _ p :=
  exists_ampleBase_localization_eq Q hva hi _ (chartRingOver_oneBlock x (fun _ => i) hi) p

theorem exists_chart_localization_eq (Q : Kleiman.LineBundle S x) {r : ℕ} {h : Fin (r + 1) → Ω}
    (hva : Kleiman.IsVeryAmpleBy Q.toSubSystem h) {l : Fin (r + 1)} (hl : h l ≠ 0) (B : Subalgebra S Ω)
    (hBeq : B = Kleiman.ampleBase (S := S) h l) (q : Ideal B) [hq : q.IsPrime] :
    ∃ i, x i ≠ 0 ∧ ∃ p : Ideal (chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) (fun _ => i)), p.IsPrime ∧
      IndefiniteRowSideFullHecke.Kleiman2.locIn _ p = IndefiniteRowSideFullHecke.Kleiman2.locIn B q := by
  have hAmB : ∀ y ∈ Kleiman.ampleRing Q.toSubSystem 1 (h l), y ∈ B := fun y hy => by
    rw [hBeq]; exact hva.closed l hl hy
  obtain ⟨K, a, b, J, ha, hb, hab, hbJ⟩ := hva.affine l hl
  obtain ⟨k, hk⟩ := exists_not_mem_of_sum_eq_one q a b (fun k => hAmB _ (ha k)) (fun k => hAmB _ (hb k)) hab
  obtain ⟨i, hiJ⟩ := (J k).2.1
  have hi : x i ≠ 0 := (Kleiman.mem_support x).mp ((J k).2.2 hiJ)
  set A := chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) (fun _ => i) with hAdef
  have hA : A = Kleiman.chartRing S x (Kleiman.singleChart hi) := chartRingOver_oneBlock x (fun _ => i) hi
  have hb0 : b k ≠ 0 := coe_ne_zero_of_not_mem_ideal hk
  have hAB : A ≤ locAlg B q := by
    intro z hz
    rw [hA] at hz
    have hzJ : z ∈ Kleiman.chartRing S x (J k) :=
      Kleiman.chartRing_mono (Finset.singleton_subset_iff.mpr hiJ) hz
    obtain ⟨e, he⟩ := GraphClosedAlt.exists_pow_mul_mem_ampleRing Q.toSubSystem (h l) (b k) (J k) (hb k)
      (hbJ k) hzJ
    have hbe : (⟨b k, hAmB _ (hb k)⟩ : B) ^ e ∉ q := fun h' => hk (hq.mem_of_pow_mem _ h')
    show z ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn B q
    rw [mem_locIn_iff]
    refine ⟨⟨_, hAmB _ he⟩, _, hbe, ?_⟩
    show z = b k ^ e * z / (b k ^ e)
    rw [mul_div_cancel_left₀ z (pow_ne_zero _ hb0)]
  refine ⟨i, hi, _, Ideal.comap_isPrime _ _, locIn_comap_eq B A q hAB ?_⟩
  obtain ⟨w, hw', hsum⟩ := exists_inv_of_span_eq Q h hi (hva.generates _)
  have hw : ∀ a b, h a * w b ∈ A := fun a b => by rw [hA]; exact hw' a b
  obtain ⟨m, hm⟩ := exists_not_mem_of_sum_eq_one (locMax B q) (fun m => h m / h l) (fun m => h l * w m)
    (fun m => le_locIn B q (by rw [hBeq]; exact Algebra.subset_adjoin ⟨m, rfl⟩)) (fun m => hAB (hw l m)) (by
      rw [← hsum]
      refine Finset.sum_congr rfl fun m _ => ?_
      field_simp)
  have hm' : (⟨h l * w m, hw l m⟩ : A) ∉ (locMax B q).comap (Subalgebra.inclusion hAB) := hm
  have hwm : h l * w m ≠ 0 := coe_ne_zero_of_not_mem_ideal hm'
  have hw0 : w m ≠ 0 := right_ne_zero_of_mul hwm
  have hBle : B ≤ locAlg A ((locMax B q).comap (Subalgebra.inclusion hAB)) := by
    intro y hy
    rw [hBeq] at hy
    refine (Algebra.adjoin_le ?_) hy
    rintro _ ⟨c, rfl⟩
    show h c / h l ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn A _
    rw [show h c / h l = (h c * w m) / (h l * w m) by field_simp]
    exact Subring.subset_closure ⟨⟨_, hw c m⟩, ⟨_, hw l m⟩, hm', rfl⟩
  intro z hz
  exact hBle hz

theorem exists_chart_locIn_eq (Q : Kleiman.LineBundle S x) {r : ℕ} {h : Fin (r + 1) → Ω}
    (hva : Kleiman.IsVeryAmpleBy Q.toSubSystem h) {l : Fin (r + 1)} (hl : h l ≠ 0)
    (q : Ideal (chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock h) (fun _ => l))) (hq : q.IsPrime) :
    ∃ i, x i ≠ 0 ∧ ∃ p : Ideal (chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) (fun _ => i)), p.IsPrime ∧
      IndefiniteRowSideFullHecke.Kleiman2.locIn _ p = IndefiniteRowSideFullHecke.Kleiman2.locIn _ q := by
  have hB : chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock h) (fun _ => l) = Kleiman.ampleBase (S := S) h l := by
    rw [chartRingOver_oneBlock_eq_adjoin]
    rfl
  exact exists_chart_localization_eq Q hva hl _ hB q

theorem modelPts_eq_of_isVeryAmpleBy (Q : Kleiman.LineBundle S x) {r : ℕ} {h : Fin (r + 1) → Ω}
    (hva : Kleiman.IsVeryAmpleBy Q.toSubSystem h) :
    IndefiniteRowSideFullHecke.Kleiman2.modelPts S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) = IndefiniteRowSideFullHecke.Kleiman2.modelPts S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock h) := by
  ext z
  constructor
  · rintro ⟨c, hc, p, hp, rfl⟩
    obtain ⟨i, rfl⟩ : ∃ i, c = fun _ => i := ⟨c (), funext fun _ => rfl⟩
    obtain ⟨l, hl, q, hq, heq⟩ := exists_ampleBase_locIn_eq Q hva (hc ()) p hp
    exact ⟨fun _ => l, fun _ => hl, q, hq, heq.symm⟩
  · rintro ⟨c, hc, q, hq, rfl⟩
    obtain ⟨l, rfl⟩ : ∃ l, c = fun _ => l := ⟨c (), funext fun _ => rfl⟩
    obtain ⟨i, hi, p, hp, heq⟩ := exists_chart_locIn_eq Q hva (hc ()) q hq
    exact ⟨fun _ => i, fun _ => hi, p, hp, heq.symm⟩

theorem sum_mul_eq_of_sum {n : ℤ} {m' : ℕ} {u x' : Fin m' → Ω} {a b : Ω} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ∑ l, u l * (x' l * (a ^ n * b ^ (-1 : ℤ))) = 1) : ∑ l, u l * x' l = a ^ (-n) * b := by
  have han : a ^ n ≠ 0 := zpow_ne_zero n ha
  have h1 : a ^ n * b ^ (-1 : ℤ) * (a ^ (-n) * b) = 1 := by
    rw [zpow_neg_one, zpow_neg]
    field_simp
  have e1 : ∑ l, u l * x' l = (∑ l, u l * (x' l * (a ^ n * b ^ (-1 : ℤ)))) * (a ^ (-n) * b) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    calc u l * x' l = u l * x' l * (a ^ n * b ^ (-1 : ℤ) * (a ^ (-n) * b)) := by rw [h1, mul_one]
      _ = _ := by ring
  rw [e1, h, one_mul]

theorem veryAmple_of_isVeryAmpleBy (Q : Kleiman.LineBundle S x) (n : ℤ) {m : ℕ} (s : Fin m → Ω)
    (hgen : IsGraphGen Q n s) (hx : ∃ i, x i ≠ 0) {r : ℕ} {h : Fin (r + 1) → Ω}
    (hva : Kleiman.IsVeryAmpleBy Q.toSubSystem h) :
    IndefiniteRowSideFullHecke.Kleiman2.VeryAmple S (graphVec x s) (graphDeg n) := by
  refine ⟨r + 1, h, fun j => ?_, ?_, ?_⟩
  · rw [← secs_eq_secOver Q n s hgen]
    exact hva.mem_secs j
  · intro c hc
    obtain ⟨i, j, rfl⟩ : ∃ (i : Fin (N + 1)) (j : Fin m), c = graphChart i j :=
      ⟨c (Sum.inl ()), c (Sum.inr ()), graphChart_eta c⟩
    have hi : x i ≠ 0 := hc (Sum.inl ())
    have hj : s j ≠ 0 := hc (Sum.inr ())
    have hσ : x i ^ (-n) * s j ∈ Q.sub (Kleiman.singleChart hi) := by
      rw [← span_graphGens_eq Q n s hgen hi]
      exact Submodule.subset_span ⟨j, rfl⟩
    rw [← hva.generates (Kleiman.singleChart hi)] at hσ
    obtain ⟨u, hu⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hσ
    refine ⟨fun l => u l, fun l => chartRing_le_graphRing x s hi j (u l).2, ?_⟩
    rw [prod_graph, graphDeg_inl, graphDeg_inr, neg_neg]
    simp only [Subalgebra.smul_def, smul_eq_mul] at hu
    have hxn : x i ^ n ≠ 0 := zpow_ne_zero n hi
    calc ∑ l, (u l : Ω) * (h l * (x i ^ n * s j ^ (-1 : ℤ)))
        = (∑ l, (u l : Ω) * h l) * (x i ^ n * s j ^ (-1 : ℤ)) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun l _ => by ring
      _ = 1 := by
          rw [hu, zpow_neg, zpow_neg_one]
          field_simp
  · have hM : IndefiniteRowSideFullHecke.Kleiman2.modelPts S (graphVec x s) = IndefiniteRowSideFullHecke.Kleiman2.modelPts S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) :=
      (GraphModel.full S N Ω x Q n m s hx hgen).2
    show IndefiniteRowSideFullHecke.Kleiman2.modelPts S (graphVec x s) = IndefiniteRowSideFullHecke.Kleiman2.modelPts S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock h)
    rw [hM]
    exact modelPts_eq_of_isVeryAmpleBy Q hva

end Forward

section Backward

variable {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem mem_sub_of_mem_secs {F : Kleiman.SubSystem S x Ω} {t : Ω} (ht : t ∈ F.secs) (I : Kleiman.Chart x) :
    t ∈ F.sub I :=
  (Submodule.mem_iInf _).mp ht I

theorem mem_span_of_generatesOver (Q : Kleiman.LineBundle S x) (n : ℤ) {m : ℕ} (s : Fin m → Ω)
    (hgen : IsGraphGen Q n s) {n' : ℕ} (x' : Fin n' → Ω)
    (hgo : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.GeneratesOver S (graphVec x s) (graphDeg n) x')
    {i : Fin (N + 1)} (hi : x i ≠ 0) {t : Ω} (ht : t ∈ Q.sub (Kleiman.singleChart hi)) :
    t ∈ Submodule.span (Kleiman.chartRing S x (Kleiman.singleChart hi)) (Set.range x') := by
  have hA : chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) (fun _ => i) =
      Kleiman.chartRing S x (Kleiman.singleChart hi) := chartRingOver_oneBlock x (fun _ => i) hi
  obtain ⟨w, hw, hsum⟩ := exists_graph_inverse Q n s hgen hi
  have hw' : ∀ a b, x i ^ (-n) * s a * w b ∈ Kleiman.chartRing S x (Kleiman.singleChart hi) :=
    fun a b => by rw [← hA]; exact hw a b
  have htw : ∀ c, t * w c ∈ Kleiman.chartRing S x (Kleiman.singleChart hi) := by
    intro c
    rw [← span_graphGens_eq Q n s hgen hi] at ht
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp ht
    rw [Finset.sum_mul]
    refine Subalgebra.sum_mem _ fun b _ => ?_
    rw [Subalgebra.smul_def, smul_eq_mul, mul_assoc]
    exact Subalgebra.mul_mem _ (a b).2 (hw' b c)
  refine mem_of_pow_mul_mem' _ _ (fun c => ⟨_, hw' c c⟩)
    (Subtype.ext (by simp only [AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_one]; exact hsum)) t
    fun c => ?_
  by_cases hc : s c = 0
  · exact ⟨1, by simp [hc]⟩
  obtain ⟨u, hu, husum⟩ := hgo (graphChart i c) (by rintro (⟨⟩ | ⟨⟩); exacts [hi, hc])
  rw [prod_graph, graphDeg_inl, graphDeg_inr, neg_neg] at husum
  have hσ := sum_mul_eq_of_sum hi hc husum
  obtain ⟨-, hle⟩ := graphRing_between hi n s w hw hc c
  have hM : ∀ l, ∃ M : ℕ, (x i ^ (-n) * s c * w c) ^ M * u l ∈ Kleiman.chartRing S x (Kleiman.singleChart hi) :=
    fun l => by
      obtain ⟨M, hM⟩ := hle (hu l)
      exact ⟨M, by rw [← hA]; exact hM⟩
  choose M hM using hM
  refine ⟨∑ l, M l + 1, ?_⟩
  set e := x i ^ (-n) * s c * w c with he
  have hkey : e ^ (∑ l, M l + 1) * t = ∑ l, (e ^ (∑ l, M l) * u l * (t * w c)) * x' l := by
    rw [pow_succ]
    calc e ^ (∑ l, M l) * e * t = e ^ (∑ l, M l) * (x i ^ (-n) * s c) * (t * w c) := by rw [he]; ring
      _ = ∑ l, (e ^ (∑ l, M l) * u l * (t * w c)) * x' l := by
          rw [← hσ, Finset.mul_sum, Finset.sum_mul]
          exact Finset.sum_congr rfl fun l _ => by ring
  show e ^ (∑ l, M l + 1) * t ∈ _
  rw [hkey]
  refine Submodule.sum_mem _ fun l _ => ?_
  have hcoef : e ^ (∑ l, M l) * u l * (t * w c) ∈ Kleiman.chartRing S x (Kleiman.singleChart hi) := by
    obtain ⟨K, hK⟩ := Nat.exists_eq_add_of_le
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ l) : M l ≤ ∑ l, M l)
    rw [hK, pow_add, mul_comm (e ^ M l) (e ^ K), mul_assoc (e ^ K)]
    exact Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (hw' c c) _) (hM l)) (htw c)
  have e2 : (e ^ (∑ l, M l) * u l * (t * w c)) * x' l =
      (⟨_, hcoef⟩ : Kleiman.chartRing S x (Kleiman.singleChart hi)) • x' l := by
    rw [Subalgebra.smul_def, smul_eq_mul]
  rw [e2]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)

theorem generates_of_generatesOver (Q : Kleiman.LineBundle S x) (n : ℤ) {m : ℕ} (s : Fin m → Ω)
    (hgen : IsGraphGen Q n s) {n' : ℕ} (x' : Fin n' → Ω)
    (hgo : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.GeneratesOver S (graphVec x s) (graphDeg n) x')
    (hsecs : ∀ l, x' l ∈ Q.secs) (I : Kleiman.Chart x) :
    Submodule.span (Kleiman.chartRing S x I) (Set.range x') = Q.sub I := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨l, rfl⟩
    exact mem_sub_of_mem_secs (hsecs l) I
  · intro t ht
    obtain ⟨i, hiI⟩ := I.2.1
    have hi : x i ≠ 0 := (Kleiman.mem_support x).mp (I.2.2 hiI)
    have hsub : (Kleiman.singleChart hi).1 ⊆ I.1 := Finset.singleton_subset_iff.mpr hiI
    obtain ⟨a, ⟨v, hv⟩, hat⟩ := (Q.mem_iff (Kleiman.singleChart hi) I hsub t).mp ht
    have h1 := mem_span_of_generatesOver Q n s hgen x' hgo hi hat
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp h1
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨fun l => (↑v⁻¹ : Kleiman.chartRing S x I) * Kleiman.chartIncl hsub (c l), ?_⟩
    have hvv : ((↑v⁻¹ : Kleiman.chartRing S x I) : Ω) * (a : Ω) = 1 := by
      have h2 := congrArg Subtype.val v.inv_mul
      rw [hv] at h2
      simp only [Subalgebra.coe_mul, Subalgebra.coe_one] at h2
      exact h2
    simp only [Subalgebra.smul_def, smul_eq_mul] at hc ⊢
    calc ∑ l, ((↑v⁻¹ * Kleiman.chartIncl hsub (c l) : Kleiman.chartRing S x I) : Ω) * x' l
        = ((↑v⁻¹ : Kleiman.chartRing S x I) : Ω) * ∑ l, (c l : Ω) * x' l := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun l _ => ?_
          simp only [Subalgebra.coe_mul]
          rw [mul_assoc]
          rfl
      _ = t := by rw [hc, ← mul_assoc, hvv, one_mul]

theorem closed_of_modelPts (Q : Kleiman.LineBundle S x) (n : ℤ) {m : ℕ} (s : Fin m → Ω)
    (hgen : IsGraphGen Q n s) {r : ℕ} (x' : Fin (r + 1) → Ω)
    (hgo : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.GeneratesOver S (graphVec x s) (graphDeg n) x')
    (hpts : IndefiniteRowSideFullHecke.Kleiman2.modelPts S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') =
      IndefiniteRowSideFullHecke.Kleiman2.modelPts S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x))
    (j : Fin (r + 1)) (hj : x' j ≠ 0) :
    Kleiman.ampleRing Q.toSubSystem 1 (x' j) ⊆ Kleiman.ampleBase (S := S) x' j := by
  intro z hz
  have hBeq : chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') (fun _ => j) = Kleiman.ampleBase (S := S) x' j := by
    rw [chartRingOver_oneBlock_eq_adjoin]
    rfl
  rw [← hBeq]
  apply mem_of_forall_locIn
  intro q hq
  have hmem : IndefiniteRowSideFullHecke.Kleiman2.locIn _ q ∈ IndefiniteRowSideFullHecke.Kleiman2.modelPts S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) := by
    rw [← hpts]
    exact ⟨fun _ => j, fun _ => hj, q, hq, rfl⟩
  obtain ⟨c, hc, p, hp, hpeq⟩ := hmem
  obtain ⟨i, rfl⟩ : ∃ i, c = fun _ => i := ⟨c (), funext fun _ => rfl⟩
  have hi : x i ≠ 0 := hc ()
  rw [hpeq]
  have hA : chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) (fun _ => i) =
      Kleiman.chartRing S x (Kleiman.singleChart hi) := chartRingOver_oneBlock x (fun _ => i) hi
  obtain ⟨w, hw, hsum⟩ := exists_graph_inverse Q n s hgen hi
  obtain ⟨c', hc'⟩ := exists_not_mem_of_sum_eq_one p (fun _ => (1 : Ω)) (fun k => x i ^ (-n) * s k * w k)
    (fun _ => Subalgebra.one_mem _) (fun k => hw k k) (by simpa using hsum)
  have hsc' : s c' ≠ 0 := fun h0 => coe_ne_zero_of_not_mem_ideal hc' (by simp [h0])
  obtain ⟨-, hle⟩ := graphRing_between hi n s w hw hsc' c'
  have hgr : ∀ g ∈ graphRing S x s i c', g ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn _ p := by
    intro g hg
    obtain ⟨M, hM⟩ := hle hg
    have hpow : (⟨x i ^ (-n) * s c' * w c', hw c' c'⟩ : chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) (fun _ => i)) ^ M ∉ p :=
      fun h' => hc' (hp.mem_of_pow_mem _ h')
    have h0 := coe_ne_zero_of_not_mem_ideal hpow
    rw [mem_locIn_iff]
    refine ⟨⟨_, hM⟩, _, hpow, ?_⟩
    simp only [SubmonoidClass.coe_pow] at h0 ⊢
    rw [mul_div_cancel_left₀ g h0]
  have hxl : ∀ l, x' l / x' j ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn _ p := fun l => by
    rw [← hpeq]
    exact le_locIn _ q (div_mem_chartRingOver_oneBlock x' j l)
  obtain ⟨u, hu, husum⟩ := hgo (graphChart i c') (by rintro (⟨⟩ | ⟨⟩); exacts [hi, hsc'])
  rw [prod_graph, graphDeg_inl, graphDeg_inr, neg_neg] at husum
  have hσ' := sum_mul_eq_of_sum hi hsc' husum
  have hσ : x i ^ (-n) * s c' / x' j ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn _ p := by
    rw [← hσ', Finset.sum_div]
    exact Subring.sum_mem _ fun l _ => by
      rw [mul_div_assoc]
      exact Subring.mul_mem _ (hgr _ (hu l)) (hxl l)
  have hQ : ∀ t ∈ Q.sub (Kleiman.singleChart hi), t / x' j ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn _ p := by
    intro t ht
    rw [← span_graphGens_eq Q n s hgen hi] at ht
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp ht
    rw [Finset.sum_div]
    refine Subring.sum_mem _ fun b _ => ?_
    have e2 : a b • (x i ^ (-n) * s b) / x' j = a b * (s b / s c') * (x i ^ (-n) * s c' / x' j) := by
      rw [Subalgebra.smul_def, smul_eq_mul]
      field_simp
    rw [e2]
    refine Subring.mul_mem _ (Subring.mul_mem _ (le_locIn _ p ?_) (hgr _ (div_mem_graphRing_inr x s i c' b))) hσ
    rw [hA]
    exact (a b).2
  have hpowQ : ∀ e : ℕ, ∀ t ∈ Q.sub (Kleiman.singleChart hi) ^ e,
      t / x' j ^ e ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn (chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) (fun _ => i)) p := by
    intro e
    induction e with
    | zero =>
      intro t ht
      rw [pow_zero] at ht
      obtain ⟨a, rfl⟩ := Submodule.mem_one.mp ht
      rw [pow_zero, div_one]
      refine le_locIn _ p ?_
      rw [hA]
      exact a.2
    | succ e ih =>
      intro t ht
      rw [pow_succ] at ht
      refine Submodule.mul_induction_on
        (C := fun t => t / x' j ^ (e + 1) ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn (chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) (fun _ => i)) p)
        ht ?_ ?_
      · intro a ha b hb
        rw [pow_succ, ← div_mul_div_comm]
        exact Subring.mul_mem _ (ih a ha) (hQ b hb)
      · intro a b ha hb
        rw [add_div]
        exact Subring.add_mem _ ha hb
  obtain ⟨e, he⟩ := Set.mem_iInter.mp hz (Kleiman.singleChart hi)
  rw [one_mul, Kleiman.SubSystem.pow_sub] at he
  have h3 := hpowQ e _ he
  rwa [mul_div_assoc, div_self (pow_ne_zero _ hj), mul_one] at h3

theorem affine_of_modelPts (Q : Kleiman.LineBundle S x) {r : ℕ} (x' : Fin (r + 1) → Ω)
    (hsecs : ∀ l, x' l ∈ Q.secs)
    (hpts : IndefiniteRowSideFullHecke.Kleiman2.modelPts S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') =
      IndefiniteRowSideFullHecke.Kleiman2.modelPts S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x))
    (j : Fin (r + 1)) (hj : x' j ≠ 0) :
    ∃ (K : ℕ) (a b : Fin K → Ω) (J : Fin K → Kleiman.Chart x),
      (∀ k, a k ∈ Kleiman.ampleRing Q.toSubSystem 1 (x' j)) ∧
      (∀ k, b k ∈ Kleiman.ampleRing Q.toSubSystem 1 (x' j)) ∧
      ∑ k, a k * b k = 1 ∧ ∀ (k : Fin K) (I : Kleiman.Chart x), ∃ e : ℕ,
        b k ^ e * (Kleiman.xProd I ^ (J k).1.card / Kleiman.xProd (J k) ^ I.1.card) ∈
          Kleiman.ampleChart Q.toSubSystem 1 (x' j) I := by
  have hBeq : chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') (fun _ => j) =
      Algebra.adjoin S (Set.range fun b => x' b / x' j) := chartRingOver_oneBlock_eq_adjoin x' _
  have hBamp : ∀ z ∈ chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') (fun _ => j),
      z ∈ Kleiman.ampleRing Q.toSubSystem 1 (x' j) := by
    intro z hz
    refine Set.mem_iInter.mpr fun I => ?_
    have hxI : x' j ∈ (Q.toSubSystem.pow 1).sub I := by
      rw [Kleiman.SubSystem.pow_sub, pow_one]
      exact mem_sub_of_mem_secs (hsecs j) I
    rw [hBeq] at hz
    refine (Algebra.adjoin_le (S := AmpleAffineGen.ampleSubalg Q.toSubSystem 1 (x' j) I hxI) ?_) hz
    rintro _ ⟨l, rfl⟩
    refine ⟨1, ?_⟩
    show x' l / x' j * x' j ^ 1 ∈ (Q.toSubSystem.pow 1).sub I
    rw [pow_one, div_mul_cancel₀ _ hj, Kleiman.SubSystem.pow_sub, pow_one]
    exact mem_sub_of_mem_secs (hsecs l) I
  let G : Set (chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') (fun _ => j)) :=
    {g | ∃ i, x i ≠ 0 ∧ ∀ a : Fin (N + 1), ∃ e : ℕ,
      (g : Ω) ^ e * (x a / x i) ∈ chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') (fun _ => j)}
  have hG : Ideal.span G = ⊤ := by
    by_contra hne
    obtain ⟨q, hq, hle⟩ := Ideal.exists_le_maximal _ hne
    have hqp := hq.isPrime
    have hmem : IndefiniteRowSideFullHecke.Kleiman2.locIn _ q ∈ IndefiniteRowSideFullHecke.Kleiman2.modelPts S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) := by
      rw [← hpts]
      exact ⟨fun _ => j, fun _ => hj, q, hqp, rfl⟩
    obtain ⟨c, hc, p, hp, hpeq⟩ := hmem
    obtain ⟨i, rfl⟩ : ∃ i, c = fun _ => i := ⟨c (), funext fun _ => rfl⟩
    have hi : x i ≠ 0 := hc ()
    have hfr : ∀ a : Fin (N + 1), ∃ β γ : chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') (fun _ => j),
        γ ∉ q ∧ x a / x i = β / γ := by
      intro a
      refine (mem_locIn_iff _ q _).mp ?_
      rw [hpeq]
      refine le_locIn _ p ?_
      rw [chartRingOver_oneBlock x _ hi]
      exact (Kleiman.ratio hi a).2
    choose β γ hγ hβγ using hfr
    have hγ0 : ∀ a, (γ a : Ω) ≠ 0 := fun a => coe_ne_zero_of_not_mem_ideal (hγ a)
    have hg : ∏ a, γ a ∉ q := fun h' => by
      obtain ⟨a, -, ha⟩ := Ideal.IsPrime.prod_mem_iff.mp h'
      exact hγ a ha
    have hgG : ∏ a, γ a ∈ G := by
      refine ⟨i, hi, fun a => ⟨1, ?_⟩⟩
      have e1 : ((∏ a, γ a : chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') (fun _ => j)) : Ω) ^ 1 * (x a / x i) =
          β a * ∏ a' ∈ Finset.univ.erase a, (γ a' : Ω) := by
        rw [pow_one, hβγ a, SubmonoidClass.coe_finsetProd,
          ← Finset.mul_prod_erase Finset.univ (fun a => (γ a : Ω)) (Finset.mem_univ a)]
        field_simp [hγ0 a]
      rw [e1]
      exact Subalgebra.mul_mem _ (β a).2 (Subalgebra.prod_mem _ fun a' _ => (γ a').2)
    exact hg (hle (Ideal.subset_span hgG))
  have h1 : (1 : chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') (fun _ => j)) ∈ Ideal.span G := by
    rw [hG]
    exact Submodule.mem_top
  obtain ⟨K, f, g, hfg⟩ := Submodule.mem_span_set'.mp h1
  have hgood : ∀ k, ∃ i, x i ≠ 0 ∧ ∀ a : Fin (N + 1), ∃ e : ℕ,
      ((g k : chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') (fun _ => j)) : Ω) ^ e * (x a / x i) ∈
        chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') (fun _ => j) := fun k => (g k).2
  choose i hi hgi using hgood
  refine ⟨K, fun k => f k, fun k => (g k : chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') (fun _ => j)),
    fun k => Kleiman.singleChart (hi k), fun k => hBamp _ (f k).2, fun k => hBamp _ (g k).1.2, ?_, ?_⟩
  · have h2 := congrArg Subtype.val hfg
    simp only [AddSubmonoidClass.coe_finsetSum, smul_eq_mul, Subalgebra.coe_mul, Subalgebra.coe_one] at h2
    exact h2
  · intro k I
    choose e he using hgi k
    refine ⟨∑ a ∈ I.1, e a, ?_⟩
    have hc1 : (Kleiman.singleChart (hi k)).1.card = 1 := Finset.card_singleton _
    have hx1 : Kleiman.xProd (Kleiman.singleChart (hi k)) = x (i k) := Finset.prod_singleton _ _
    have e3 : ((g k : chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') (fun _ => j)) : Ω) ^ (∑ a ∈ I.1, e a) *
        (Kleiman.xProd I ^ 1 / x (i k) ^ I.1.card) =
        ∏ a ∈ I.1, (((g k : chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') (fun _ => j)) : Ω) ^ e a *
          (x a / x (i k))) := by
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_div_distrib, Finset.prod_const, pow_one]
      rfl
    rw [hc1, hx1, e3]
    exact Set.mem_iInter.mp (hBamp _ (Subalgebra.prod_mem _ fun a _ => he a)) I

theorem isVeryAmple_of_veryAmple (Q : Kleiman.LineBundle S x) (n : ℤ) {m : ℕ} (s : Fin m → Ω)
    (hgen : IsGraphGen Q n s) (hx : ∃ i, x i ≠ 0)
    (hV : IndefiniteRowSideFullHecke.Kleiman2.VeryAmple S (graphVec x s) (graphDeg n)) : Kleiman.IsVeryAmple Q.toSubSystem := by
  obtain ⟨n', x', hsec, hgo, hsame⟩ := hV
  obtain ⟨hnz, hM⟩ := GraphModel.full S N Ω x Q n m s hx hgen
  have hpts : IndefiniteRowSideFullHecke.Kleiman2.modelPts S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') =
      IndefiniteRowSideFullHecke.Kleiman2.modelPts S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) := hsame.symm.trans hM
  have hsecs : ∀ l, x' l ∈ Q.secs := fun l => by
    rw [secs_eq_secOver Q n s hgen]
    exact hsec l
  cases n' with
  | zero =>
    exfalso
    obtain ⟨i, hi⟩ := hx
    obtain ⟨j, hj⟩ := hnz (Sum.inr ())
    obtain ⟨u, -, hu⟩ := hgo (graphChart i j) (by rintro (⟨⟩ | ⟨⟩); exacts [hi, hj])
    simp at hu
  | succ r =>
    exact ⟨r, x',
      { mem_secs := hsecs
        generates := generates_of_generatesOver Q n s hgen x' hgo hsecs
        closed := closed_of_modelPts Q n s hgen x' hgo hpts
        affine := affine_of_modelPts Q x' hsecs hpts }⟩

end Backward

section Zero

variable {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem isVeryAmple_of_forall_eq_zero (Q : Kleiman.LineBundle S x) (hx : ∀ i, x i = 0) :
    Kleiman.IsVeryAmple Q.toSubSystem := by
  have hno : ∀ I : Kleiman.Chart x, False := fun I => by
    obtain ⟨i, hi⟩ := I.2.1
    exact (Kleiman.mem_support x).mp (I.2.2 hi) (hx i)
  exact ⟨0, fun _ => 0,
    { mem_secs := fun _ => zero_mem _
      generates := fun I => (hno I).elim
      closed := fun _ h => (h rfl).elim
      affine := fun _ h => (h rfl).elim }⟩

theorem veryAmple_of_forall_eq_zero (n : ℤ) {m : ℕ} (s : Fin m → Ω) (hx : ∀ i, x i = 0) :
    IndefiniteRowSideFullHecke.Kleiman2.VeryAmple S (graphVec x s) (graphDeg n) := by
  refine ⟨0, Fin.elim0, fun j => j.elim0, fun c hc => (hc (Sum.inl ()) (hx (c (Sum.inl ())))).elim, ?_⟩
  show IndefiniteRowSideFullHecke.Kleiman2.modelPts S (graphVec x s) =
    IndefiniteRowSideFullHecke.Kleiman2.modelPts S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (Fin.elim0 : Fin 0 → Ω))
  ext z
  constructor
  · rintro ⟨c, hc, -⟩
    exact (hc (Sum.inl ()) (hx (c (Sum.inl ())))).elim
  · rintro ⟨c, -⟩
    exact (c ()).elim0

end Zero

theorem VeryAmpleEq.full : VeryAmpleEq.Statement := by
  intro S _ N Ω _ _ x Q n m s hgen
  by_cases hx : ∃ i, x i ≠ 0
  · exact ⟨fun ⟨_, _, hva⟩ => veryAmple_of_isVeryAmpleBy Q n s hgen hx hva,
      isVeryAmple_of_veryAmple Q n s hgen hx⟩
  · simp only [not_exists, not_not] at hx
    exact iff_of_true (isVeryAmple_of_forall_eq_zero Q hx) (veryAmple_of_forall_eq_zero n s hx)

end

end PositivityTheory.HtPt.KtwS.SectionsOverLocalization
