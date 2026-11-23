import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnChartAsm
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUnique
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructureProperties

namespace GlobalTheory.Dict.Poisson

section Orbit

open Matrix Complex NumberField GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.SW.TensVac GlobalTheory.SW.TensLat
open scoped ComplexConjugate Real Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {w : E} {A A' : AddSubgroup (Matrix (Fin n) (Fin r) E)}

theorem mem_of_fix (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) (hn : Even n)
    (hA : Good X w A) {p : TF n g} (hp : IsSB p) (h0 : p ≠ 0)
    (hfix : ∀ u ∈ A, epsW X w u • heisG X bas u p = p) {y}
    (hy : epsW X w y • heisG X bas y p = p) : y ∈ A := by
  by_contra hyA
  obtain ⟨v, hv, huniq⟩ := GlobalTheory.SW.TensVac.Good.vac hs hA
  obtain ⟨c, rfl⟩ := huniq p hp hfix
  have hc : c ≠ 0 := by
    rintro rfl
    exact h0 (zero_smul ℂ v)
  have hvy : epsW X w y • heisG X bas y v = v := by
    rw [heisG_smul, smul_comm] at hy
    exact smul_right_injective _ hc hy
  have h1 := GlobalTheory.SW.TensVac.Good.ip_eq_zero idx hs hn hA hv hyA
  rw [hvy, hv.2.1] at h1
  exact one_ne_zero h1

theorem fourier_of_reps (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) (hn : Even n)
    (hA : Good X w A) (hA' : Good X w A') {p : TF n g} (hp : IsSB p)
    (hfix : ∀ u ∈ A, epsW X w u • heisG X bas u p = p) {ι : Type}
    (Y : ι → Matrix (Fin n) (Fin r) E) (hY : ∀ q, Y q ∈ A') (hY1 : ∀ q, epsW X w (Y q) = 1)
    (hinj : ∀ q q', Y q - Y q' ∈ A → q = q') (hsurj : ∀ y ∈ A', ∃ q, y - Y q ∈ A)
    {u : Matrix (Fin n) (Fin r) E} (hu : u ∈ A) (hu1 : epsW X w u = 1) :
    ∑ᶠ q, cexp (-(2 * Real.pi * I * ((∑ b, EF X (u b) (Y q b) : ℚ) : ℂ))) • heisG X bas (Y q) p =
      ((Nat.card ι : ℕ) : ℂ) • heisG X bas u (projA X bas w A' p) := by
  classical
  have hzero : ∀ y : Matrix (Fin n) (Fin r) E, heisG X bas y (0 : TF n g) = 0 := fun y => by
    have h := heisG_smul (X := X) (bas := bas) y (0 : ℂ) (0 : TF n g)
    rwa [zero_smul, zero_smul] at h
  by_cases hp0 : p = 0
  · subst hp0
    have hproj : projA X bas w A' (0 : TF n g) = 0 := by
      unfold projA
      rw [finsum_mem_eq_zero_of_forall_eq_zero, smul_zero]
      rintro ψ ⟨y, -, rfl⟩
      simp [hzero]
    rw [hproj, hzero, smul_zero]
    simp [hzero]
  have hF : ∀ q, epsW X w (Y q) • heisG X bas (Y q) p = heisG X bas (Y q) p := fun q => by
    rw [hY1, one_smul]
  have hrange : (fun y => epsW X w y • heisG X bas y p) '' (A' : Set (Matrix (Fin n) (Fin r) E)) =
      Set.range (fun q => heisG X bas (Y q) p) := by
    ext ψ
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨q, hq⟩ := hsurj y hy
      refine ⟨q, ?_⟩
      have hd : y - Y q ∈ A' := sub_mem hy (hY q)
      have h := GlobalTheory.SW.TensVac.Good.rho_rho idx hs hn hA' (hY q) hd hp
      rw [hfix _ hq, add_sub_cancel] at h
      show heisG X bas (Y q) p = epsW X w y • heisG X bas y p
      rw [← h, hF]
    · rintro ⟨q, rfl⟩
      exact ⟨Y q, hY q, hF q⟩
  have hinjF : Function.Injective (fun q => heisG X bas (Y q) p) := by
    intro q q' hqq
    simp only at hqq
    apply hinj
    have hd : Y q - Y q' ∈ A' := sub_mem (hY q) (hY q')
    have h1 := GlobalTheory.SW.TensVac.Good.rho_rho idx hs hn hA' (hY q') hd hp
    rw [add_sub_cancel, hF, hqq, ← hF q'] at h1
    have hneg : -Y q' ∈ A' := neg_mem (hY q')
    have cancel : ∀ φ : TF n g, IsSB φ → epsW X w (-Y q') • heisG X bas (-Y q')
        (epsW X w (Y q') • heisG X bas (Y q') φ) = φ := fun φ hφ => by
      rw [GlobalTheory.SW.TensVac.Good.rho_rho idx hs hn hA' hneg (hY q') hφ, neg_add_cancel,
        rho_zero idx hs hn hφ]
    have hsb := rho_sb idx hs hn (w := w) (Y q - Y q') hp
    have h2 : epsW X w (-Y q') • heisG X bas (-Y q') (epsW X w (Y q') • heisG X bas (Y q')
        (epsW X w (Y q - Y q') • heisG X bas (Y q - Y q') p)) =
        epsW X w (-Y q') • heisG X bas (-Y q') (epsW X w (Y q') • heisG X bas (Y q') p) := by
      rw [h1]
    rw [cancel _ hsb, cancel _ hp] at h2
    exact mem_of_fix idx hs hn hA hp hp0 hfix h2
  have hfin : (Set.range fun q => heisG X bas (Y q) p).Finite := by
    rw [← hrange]; exact GlobalTheory.SW.TensVac.Good.finite idx hs hn hA' hp
  have hfinι : Finite ι := by
    have := hfin.to_subtype
    exact Finite.of_injective
      (fun q => (⟨_, q, rfl⟩ : Set.range fun q => heisG X bas (Y q) p))
      (fun a b h => hinjF (congrArg Subtype.val h))
  haveI := Fintype.ofFinite ι
  have hproj : projA X bas w A' p =
      ((Nat.card ι : ℕ) : ℂ)⁻¹ • ∑ q, heisG X bas (Y q) p := by
    unfold projA
    rw [hrange, finsum_mem_range hinjF, ← Set.image_univ, Set.ncard_image_of_injective _ hinjF,
      Set.ncard_univ, finsum_eq_sum_of_fintype]
  have hsum : heisG X bas u (∑ q, heisG X bas (Y q) p) =
      ∑ q, heisG X bas u (heisG X bas (Y q) p) := by
    have e : ∑ q, heisG X bas (Y q) p =
        ∑ φ ∈ Finset.univ.image (fun q => heisG X bas (Y q) p), φ := by
      rw [Finset.sum_image (fun a _ b _ h => hinjF h)]
    rw [e, heisG_sum, Finset.sum_image (fun a _ b _ h => hinjF h)]
  have hup : heisG X bas u p = p := by
    have h := hfix u hu
    rwa [hu1, one_smul] at h
  have hterm : ∀ q, heisG X bas u (heisG X bas (Y q) p) =
      cexp (-(2 * Real.pi * I * ((∑ b, EF X (u b) (Y q b) : ℚ) : ℂ))) • heisG X bas (Y q) p := by
    intro q
    have l1 := (laws idx hs hn u hp).2.2.1 (Y q)
    have l2 := (laws idx hs hn (Y q) hp).2.2.1 u
    rw [hup, sumEF_swap hs, add_comm] at l2
    rw [l1, l2, smul_smul]
    congr 1
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hproj, heisG_smul, hsum, finsum_eq_sum_of_fintype]
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  · rw [smul_inv_smul₀ (Nat.cast_ne_zero.2 Nat.card_pos.ne')]
    exact Finset.sum_congr rfl fun q _ => (hterm q).symm

end Orbit

section Ideals

variable {O V : Type} [CommRing O] [AddCommGroup V] [Module O V] {P Q : Ideal O} {M : ℕ}

theorem exists_of_mem_span_smul {B : Submodule O V} {x : V}
    (hx : x ∈ Ideal.span {(M : O)} • B) : ∃ u ∈ B, x = M • u := by
  rw [Submodule.ideal_span_singleton_smul] at hx
  obtain ⟨u, hu, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
  exact ⟨u, hu, Nat.cast_smul_eq_nsmul O M u⟩

theorem exists_of_mem_smul (h : Q * P = Ideal.span {(M : O)}) {B : Submodule O V} {x : V}
    (hx : x ∈ P • B) {b : O} (hb : b ∈ Q) : ∃ u ∈ B, b • x = M • u := by
  have hm : b • x ∈ (Q * P) • B := by
    rw [Submodule.mul_smul]; exact Submodule.smul_mem_smul hb hx
  rw [h] at hm
  exact exists_of_mem_span_smul hm

theorem exists_of_mem_inter (h : Q * P = Ideal.span {(M : O)}) (hc : Q ⊔ P = ⊤)
    {B : Submodule O V} {x : V} (hx : x ∈ P • B) (hx' : x ∈ Q • B) : ∃ u ∈ B, x = M • u := by
  have h1 : (1 : O) ∈ Q ⊔ P := by rw [hc]; exact Submodule.mem_top
  obtain ⟨q, hq, p, hp, hqp⟩ := Submodule.mem_sup.1 h1
  have hq' : q • x ∈ Ideal.span {(M : O)} • B := by
    rw [← h, Submodule.mul_smul]; exact Submodule.smul_mem_smul hq hx
  have hp' : p • x ∈ Ideal.span {(M : O)} • B := by
    rw [← h, mul_comm Q P, Submodule.mul_smul]; exact Submodule.smul_mem_smul hp hx'
  have hs := add_mem hq' hp'
  rw [← add_smul, hqp, one_smul] at hs
  exact exists_of_mem_span_smul hs

end Ideals

section Lattice

open Matrix Complex NumberField GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.SW.TensVac GlobalTheory.SW.TensLat GlobalTheory.SW.Base
open scoped ComplexConjugate Real Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r n : ℕ}

theorem ctr_nat (y : Matrix (Fin n) (Fin r) E) (s : ℕ) (v : Fin n → E) :
    ctr y ((s : E) • v) = (s : E) • ctr y v := by
  unfold ctr
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, cc, map_mul, map_natCast, mul_smul]
  rfl

theorem ctr_smul (a : E) (y : Matrix (Fin n) (Fin r) E) (v : Fin n → E) :
    ctr (a • y) v = a • ctr y v := by
  unfold ctr
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_comm]
  rfl

theorem ctr_single (y : Matrix (Fin n) (Fin r) E) (k : Fin n) : ctr y (Pi.single k 1) = y k := by
  unfold ctr
  rw [Finset.sum_eq_single k]
  · simp [cc]
  · intro b _ hb
    simp [hb, cc]
  · simp

theorem ctr_rows {B : Lt E r} {y : Matrix (Fin n) (Fin r) E} (hy : ∀ k, y k ∈ B) {v : Fin n → E}
    (hv : v ∈ stdL E n) : ctr y v ∈ B := by
  have hsm : ∀ (a : E) (v : Fin n → E), ctr y (a • v) = cc a • ctr y v := by
    intro a v
    unfold ctr
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, cc, map_mul, mul_smul]
    rfl
  have hadd : ∀ v v' : Fin n → E, ctr y (v + v') = ctr y v + ctr y v' := by
    intro v v'
    unfold ctr
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.add_apply, cc, map_add, add_smul]
    rfl
  unfold stdL at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    rw [ctr_single]; exact hy k
  | zero =>
    have : ctr y (0 : Fin n → E) = 0 := by simp [ctr]
    rw [this]; exact B.zero_mem
  | add x x' _ _ h1 h2 =>
    rw [hadd]; exact B.add_mem h1 h2
  | smul c x _ h =>
    rw [← algebraMap_smul E c x, hsm]
    exact int_smul_mem (map_isIntegral_int _ (RingOfIntegers.isIntegral_coe c)) h

variable {M N s : ℕ} {Λ : Lt E n} {L : Lt E r} {P Q : Ideal (𝓞 E)}

theorem row_mem (hΛ : Λ ∈ Vset E n M) (hs : ∀ v ∈ stdL E n, (s : E) • v ∈ Λ) {B : Lt E r}
    {y : Matrix (Fin n) (Fin r) E} (hy : y ∈ tens Λ B) (k : Fin n) : (s : E) • y k ∈ B := by
  have hk : (s : E) • (Pi.single k 1 : Fin n → E) ∈ Λ := hs _ (Submodule.subset_span ⟨k, rfl⟩)
  have h := (mem_tens_iff hΛ B y).1 hy _ hk
  rwa [ctr_nat, ctr_single] at h

theorem smul_mem_std (hΛ : Λ ∈ Vset E n M) (hN : ∀ v ∈ stdL E n, (N : E) • v ∈ Λ) {v : Fin n → E}
    (hv : v ∈ Λ) : (N : E) • v ∈ stdL E n := by
  have hint : ∀ k, IsIntegral ℤ ((N : E) * v k) := by
    intro k
    have hk : (N : E) • (Pi.single k 1 : Fin n → E) ∈ Λ := hN _ (Submodule.subset_span ⟨k, rfl⟩)
    have h := (hΛ.2.1 v).1 hv _ hk
    have e : herm 1 v ((N : E) • (Pi.single k 1 : Fin n → E)) = (N : E) * v k := by
      simp [herm, Matrix.one_apply, Pi.single_apply, cc, mul_comm]
      rw [Finset.sum_eq_single k (fun b _ hb => by simp [hb]) (by simp)]
      simp
    rwa [e] at h
  have e : (N : E) • v = ∑ k, ((N : E) * v k) • (Pi.single k 1 : Fin n → E) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [e]
  exact Submodule.sum_mem _ fun k _ => int_smul_mem (hint k) (Submodule.subset_span ⟨k, rfl⟩)

omit [IsCMField E] in
theorem nat_smul_mem_smul {k : ℕ} (hk : (k : 𝓞 E) ∈ P) {x : Fin r → E} (hx : x ∈ L) :
    (k : E) • x ∈ P • L := by
  have h := Submodule.smul_mem_smul hk hx
  rwa [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul E]

omit [IsCMField E] in

theorem mem_of_two (hM : Odd M) (hsM : s.Coprime M) (hMQ : (M : 𝓞 E) ∈ Q) (hc : Q ⊔ P = ⊤) {j : ℕ}
    {z : Fin r → E} (ha : ∀ t ∈ Q ^ j, t • z ∈ P • L) {b : 𝓞 E}
    (hb2 : ((2 * s : ℕ) : E) • b • z ∈ L) : b • z ∈ P • L := by
  have hQP : Q ^ j ⊔ P = ⊤ := by
    have h := (Ideal.isCoprime_iff_sup_eq.2 hc).pow_left (m := j)
    exact Ideal.isCoprime_iff_sup_eq.1 h
  have hQbz : ∀ t ∈ Q ^ j, t • (b • z) ∈ P • L := fun t ht => by
    rw [smul_comm]; exact Submodule.smul_mem _ b (ha t ht)
  have hQw : ∀ t ∈ Q ^ j, t • (((2 * s : ℕ) : E) • b • z) ∈ P • L := fun t ht => by
    rw [smul_comm, Nat.cast_smul_eq_nsmul]; exact nsmul_mem (hQbz t ht) _
  have hwP : ((2 * s : ℕ) : E) • b • z ∈ P • L := by
    have h1 : (1 : 𝓞 E) ∈ Q ^ j ⊔ P := by rw [hQP]; exact Submodule.mem_top
    obtain ⟨q, hq, p, hp, hqp⟩ := Submodule.mem_sup.1 h1
    have e : ((2 * s : ℕ) : E) • b • z = q • (((2 * s : ℕ) : E) • b • z) + p • (((2 * s : ℕ) : E) • b • z) := by
      rw [← add_smul, hqp, one_smul]
    rw [e]; exact add_mem (hQw q hq) (Submodule.smul_mem_smul hp hb2)
  have hcop : Nat.Coprime (2 * s) (M ^ j) :=
    Nat.Coprime.pow_right j (Nat.Coprime.mul_left (Nat.coprime_two_left.2 hM) hsM)
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hcop
  have hMj : (M : 𝓞 E) ^ j ∈ Q ^ j := Ideal.pow_mem_pow hMQ j
  have e : b • z = u • (((2 * s : ℕ) : E) • b • z) + v • (((M : 𝓞 E) ^ j) • (b • z)) := by
    rw [← algebraMap_smul E ((M : 𝓞 E) ^ j) (b • z), ← Int.cast_smul_eq_zsmul E,
      ← Int.cast_smul_eq_zsmul E, smul_smul, smul_smul, ← add_smul]
    have h : (u : E) * ((2 * s : ℕ) : E) + (v : E) * algebraMap (𝓞 E) E ((M : 𝓞 E) ^ j) = 1 := by
      rw [map_pow, map_natCast]; exact_mod_cast huv
    rw [h, one_smul]
  rw [e]; exact add_mem (zsmul_mem hwP u) (zsmul_mem (hQbz _ hMj) v)

theorem half_away (hΛ : Λ ∈ Vset E n M) (hsM : s.Coprime M)
    (hs : ∀ v ∈ Λ, (s : E) • v ∈ stdL E n) (hMP : (M : 𝓞 E) ∈ P) (hNP : (N : 𝓞 E) ∈ P)
    (hN : ∀ v ∈ stdL E n, (N : E) • v ∈ Λ) {Y : Matrix (Fin n) (Fin r) E} {t : 𝓞 E}
    (h : ∀ k, ∃ u ∈ L, t • Y k = (2 * N) • u) {v : Fin n → E} (hv : v ∈ Λ) :
    t • ctr ((2 : E)⁻¹ • Y) v ∈ P • L := by
  choose u hu hYu using h
  have hstd : ∀ x ∈ stdL E n, ∀ k, IsIntegral ℤ (x k) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      intro k
      by_cases hka : k = a
      · subst hka; simpa using isIntegral_one
      · simpa [Pi.single_apply, hka] using isIntegral_zero
    | zero => intro k; exact isIntegral_zero
    | add x y _ _ h1 h2 => intro k; exact (h1 k).add (h2 k)
    | smul c x _ h =>
      intro k
      rw [Pi.smul_apply, Algebra.smul_def]
      exact (RingOfIntegers.isIntegral_coe c).mul (h k)
  have e : t • ctr ((2 : E)⁻¹ • Y) v = ∑ k, cc (v k) • ((N : E) • u k) := by
    rw [ctr_smul, ctr, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_comm t ((2 : E)⁻¹), smul_comm t (cc (v k)), hYu k, ← Nat.cast_smul_eq_nsmul E,
      Nat.cast_mul, Nat.cast_ofNat]
    simp only [smul_smul]
    congr 1
    ring
  rw [e]
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hsM
  have hab' : (a : E) * s + b * M = 1 := by exact_mod_cast hab
  refine Submodule.sum_mem _ fun k _ => ?_
  have c1 : cc ((s : E) * v k) = (s : E) * cc (v k) := by simp [cc]
  have c2 : cc ((N : E) * v k) = (N : E) * cc (v k) := by simp [cc]
  have e2 : cc (v k) • ((N : E) • u k) = (a : E) • ((N : E) • (cc ((s : E) * v k) • u k)) +
      (b : E) • ((M : E) • (cc ((N : E) * v k) • u k)) := by
    rw [c1, c2]
    simp only [smul_smul, ← add_smul]
    congr 1
    linear_combination (-(cc (v k) * (N : E))) * hab'
  rw [e2]
  have i1 : IsIntegral ℤ (cc ((s : E) * v k)) := map_isIntegral_int _ (hstd _ (hs v hv) k)
  have i2 : IsIntegral ℤ (cc ((N : E) * v k)) :=
    map_isIntegral_int _ (hstd _ (smul_mem_std hΛ hN hv) k)
  refine add_mem ?_ ?_
  · rw [Int.cast_smul_eq_zsmul]
    exact zsmul_mem (nat_smul_mem_smul hNP (int_smul_mem i1 (hu k))) a
  · rw [Int.cast_smul_eq_zsmul]
    exact zsmul_mem (nat_smul_mem_smul hMP (int_smul_mem i2 (hu k))) b

theorem half_mem (hΛ : Λ ∈ Vset E n M) (hM : Odd M) (hMP : (M : 𝓞 E) ∈ P) (hMQ : (M : 𝓞 E) ∈ Q)
    (hc : Q ⊔ P = ⊤) (hMN : M ∣ N) (hN : ∀ v ∈ stdL E n, (N : E) • v ∈ Λ)
    {Y : Matrix (Fin n) (Fin r) E} (h1 : ∀ k, ∀ b ∈ Q, b • Y k ∈ L)
    (h2 : ∀ k, ∃ j : ℕ, ∀ t ∈ Q ^ j, ∃ u ∈ L, t • Y k = (2 * N) • u) :
    (2 : E)⁻¹ • Y ∈ tens Λ (idq P Q L) := by
  obtain ⟨s, -, hsM, hs, -⟩ := hΛ.2.2
  choose j hj using h2
  have hNP : (N : 𝓞 E) ∈ P := by
    obtain ⟨c, rfl⟩ := hMN
    rw [Nat.cast_mul]; exact Ideal.mul_mem_right _ _ hMP
  rw [mem_tens_iff hΛ]
  intro v hv b hb
  refine mem_of_two (j := ∑ k, j k) hM hsM hMQ hc ?_ ?_
  · intro t ht
    refine half_away hΛ hsM hs hMP hNP hN (fun k => ?_) hv
    exact hj k t (Ideal.pow_le_pow_right
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)) ht)
  · have hrow : ∀ k, ((b : E) • Y) k ∈ L := fun k => by
      have h := h1 k b hb
      rw [← algebraMap_smul E b (Y k)] at h
      exact h
    have e : ((2 * s : ℕ) : E) • b • ctr ((2 : E)⁻¹ • Y) v = ctr ((b : E) • Y) ((s : E) • v) := by
      rw [show ((b : 𝓞 E) : E) = algebraMap (𝓞 E) E b from rfl, ctr_smul, ctr_smul, ctr_nat,
        ← algebraMap_smul E b]
      simp only [smul_smul]
      congr 1
      push_cast
      ring
    rw [e]
    exact ctr_rows hrow (hs v hv)

theorem half_mem' (hΛ : Λ ∈ Vset E n M) {u : Matrix (Fin n) (Fin r) E}
    (hu : u ∈ tens Λ ((Ideal.span {2} * Q) • L)) : (2 : E)⁻¹ • u ∈ tens Λ L := by
  rw [mem_tens_iff hΛ] at hu ⊢
  intro w hw
  have h1 : ctr u w ∈ Ideal.span {((2 : ℕ) : 𝓞 E)} • L := by
    have h := Submodule.smul_mono_left
      (Ideal.mul_le_left : Ideal.span {(2 : 𝓞 E)} * Q ≤ Ideal.span {(2 : 𝓞 E)}) (hu w hw)
    simpa using h
  obtain ⟨x, hx, hx2⟩ := exists_of_mem_span_smul h1
  rw [ctr_smul, hx2, ← Nat.cast_smul_eq_nsmul E, smul_smul, Nat.cast_ofNat,
    inv_mul_cancel₀ two_ne_zero, one_smul]
  exact hx

omit [IsCMField E] in
theorem two_half (y : Matrix (Fin n) (Fin r) E) : 2 • (2 : E)⁻¹ • y = y := by
  rw [two_smul, ← add_smul, ← two_mul, mul_inv_cancel₀ two_ne_zero, one_smul]

theorem rows_of_mem (hΛ : Λ ∈ Vset E n M) {y : Matrix (Fin n) (Fin r) E} (hy : y ∈ tens Λ L)
    (k : Fin n) (h : (M : E) • y k ∈ L) : y k ∈ L := by
  obtain ⟨t, -, htM, -, ht⟩ := hΛ.2.2
  have h1 := row_mem hΛ ht hy k
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 htM
  have e : y k = a • ((t : E) • y k) + b • ((M : E) • y k) := by
    rw [← Int.cast_smul_eq_zsmul E, ← Int.cast_smul_eq_zsmul E, smul_smul, smul_smul, ← add_smul]
    have h2 : ((a : E) * t + b * M) = 1 := by exact_mod_cast hab
    rw [h2, one_smul]
  rw [e]; exact add_mem (zsmul_mem h1 a) (zsmul_mem h b)

theorem exists_rows (hΛ : Λ ∈ Vset E n M) (hM : 1 < M) (hMQ : (M : 𝓞 E) ∈ Q)
    {y : Matrix (Fin n) (Fin r) E} (hy : y ∈ tens Λ (idq P Q L)) :
    ∃ y' : Matrix (Fin n) (Fin r) E, (∀ k, (M : E) • y' k ∈ P • L) ∧
      ∀ Y ∈ tens Λ (idq P Q L), (∀ k, Y k - y' k ∈ L) → y - Y ∈ tens Λ L := by
  obtain ⟨s, -, hsM, hs, hs'⟩ := hΛ.2.2
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hsM
  have hab' : (a : E) * s + b * M = 1 := by exact_mod_cast hab
  have hsub : ∀ (A A' : Matrix (Fin n) (Fin r) E) (w : Fin n → E),
      ctr (A - A') w = ctr A w - ctr A' w := by
    intro A A' w
    unfold ctr
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← smul_sub]
    rfl
  have hcast : ∀ x : Fin r → E, (M : E) • x = (M : 𝓞 E) • x := fun x => by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  have hML : ∀ x ∈ idq P Q L, (M : E) • x ∈ L := fun x hx => by
    have h : (M : 𝓞 E) • x ∈ P • L := hx _ hMQ
    rw [hcast]
    exact Submodule.smul_le_right h
  refine ⟨((a : E) * s) • y, fun k => ?_, fun Y hY hYk => ?_⟩
  · have h1 : (s : E) • y k ∈ idq P Q L := row_mem hΛ hs' hy k
    have h2 : (M : 𝓞 E) • ((s : E) • y k) ∈ P • L := h1 _ hMQ
    have e : (M : E) • (((a : E) * s) • y) k = a • ((M : 𝓞 E) • ((s : E) • y k)) := by
      rw [← hcast, ← Int.cast_smul_eq_zsmul E]
      show (M : E) • (((a : E) * s) • y k) = (a : E) • ((M : E) • ((s : E) • y k))
      simp only [smul_smul]
      congr 1
      ring
    rw [e]
    exact zsmul_mem h2 a
  · rw [mem_tens_iff hΛ]
    intro w hw
    have hx : ctr (y - Y) w ∈ idq P Q L := (mem_tens_iff hΛ _ _).1 (sub_mem hy hY) w hw
    have hy' : ctr y w ∈ idq P Q L := (mem_tens_iff hΛ _ _).1 hy w hw
    have hD : ∀ k, (Y - ((a : E) * s) • y) k ∈ L := fun k => hYk k
    have hsx : (s : E) • ctr (y - Y) w ∈ L := by
      have e : y - Y = ((b : E) * M) • y - (Y - ((a : E) * s) • y) := by
        have h0 : ((b : E) * M) • y + ((a : E) * s) • y = y := by
          rw [← add_smul, show (b : E) * M + a * s = 1 by linear_combination hab', one_smul]
        calc y - Y = (((b : E) * M) • y + ((a : E) * s) • y) - Y := by rw [h0]
          _ = _ := by abel
      rw [← ctr_nat, e, hsub, ctr_nat, ctr_smul]
      refine sub_mem ?_ (ctr_rows hD (hs w hw))
      have e3 : (s : E) • (((b : E) * M) • ctr y w) = ((s * b : ℤ) : E) • ((M : E) • ctr y w) := by
        simp only [smul_smul]
        congr 1
        push_cast
        ring
      rw [e3, Int.cast_smul_eq_zsmul]
      exact zsmul_mem (hML _ hy') _
    have e4 : ctr (y - Y) w = a • ((s : E) • ctr (y - Y) w) + b • ((M : E) • ctr (y - Y) w) := by
      rw [← Int.cast_smul_eq_zsmul E, ← Int.cast_smul_eq_zsmul E, smul_smul, smul_smul, ← add_smul,
        hab', one_smul]
    rw [e4]
    exact add_mem (zsmul_mem hsx a) (zsmul_mem (hML _ hx) b)

end Lattice

end GlobalTheory.Dict.Poisson

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.Poisson

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (l : Geo.Tor.Level H)

theorem conjI_Mfr : conjI (Mfr l) = l.Mb := by
  unfold conjI Mfr
  have hset : {a : 𝓞 E | ∃ b ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E), ((a : 𝓞 E) : E) = cc ((b : 𝓞 E) : E)} =
      (l.Mb : Set (𝓞 E)) := by
    ext a
    simp only [Set.mem_setOf_eq, SetLike.mem_coe]
    constructor
    · rintro ⟨b, hb, hab⟩
      obtain ⟨x, hx, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ H.bar.surjective).1 hb
      have hax : a = x := by
        apply RingOfIntegers.ext
        rw [hab, H.bar_eq, cc, IsCMField.complexConj_apply_apply]
      rwa [hax]
    · intro ha
      refine ⟨H.bar a, Ideal.mem_map_of_mem _ ha, ?_⟩
      rw [H.bar_eq, cc, IsCMField.complexConj_apply_apply]
  rw [hset, Ideal.span_eq]

theorem M_mem : (l.M : 𝓞 E) ∈ Mfr l ∧ (l.M : 𝓞 E) ∈ l.Mb := by
  have h : (l.M : 𝓞 E) ∈ l.Mb * Mfr l := by
    unfold Mfr; rw [l.prod]; exact Ideal.mem_span_singleton_self _
  refine ⟨?_, ?_⟩
  · exact (Ideal.mul_le_right : l.Mb * Mfr l ≤ Mfr l) h
  · exact (Ideal.mul_le_left : l.Mb * Mfr l ≤ l.Mb) h

theorem selfD_shift {r : ℕ} {X : Data E r} {L : Lt E r} (hL : SelfD X L) :
    SelfD X (idq (Mfr l) (conjI (Mfr l)) L) := by
  rw [conjI_Mfr]
  have hbar : ∀ a : 𝓞 E, ((H.bar a : 𝓞 E) : E) = cc (a : E) := fun a => H.bar_eq a
  have hbarbar : ∀ a : 𝓞 E, H.bar (H.bar a) = a := fun a => by
    apply RingOfIntegers.ext
    simp only [hbar, cc, IsCMField.complexConj_apply_apply]
  have hmemM : ∀ a ∈ l.Mb, H.bar a ∈ Mfr l := fun a ha => Ideal.mem_map_of_mem _ ha
  have hmemN : ∀ a ∈ Mfr l, H.bar a ∈ l.Mb := fun a ha => by
    obtain ⟨x, hx, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ H.bar.surjective).1 ha
    simpa [hbarbar] using hx
  have hco : ∀ (a : 𝓞 E) (v : Fin r → E), a • v = (a : E) • v := fun a v =>
    (algebraMap_smul E a v).symm
  have hadd : ∀ u u' v : Fin r → E, EF X (u + u') v = EF X u v + EF X u' v := by
    intro u u' v
    rw [GlobalTheory.SW.TensLat.EF_eq_bilin, GlobalTheory.SW.TensLat.EF_eq_bilin, GlobalTheory.SW.TensLat.EF_eq_bilin,
      LinearMap.map_add₂]
  have hsm : ∀ (a : 𝓞 E) (u v : Fin r → E), EF X (a • u) v = EF X u (H.bar a • v) := by
    intro a u v
    rw [hco, hco, GlobalTheory.SW.TensLat.EF_smul, hbar]
  have hM0 : (l.M : E) ≠ 0 := Nat.cast_ne_zero.2 (by have := l.three_le; omega)
  have hcop : l.Mb ⊔ Mfr l = ⊤ := l.coprime
  obtain ⟨m, hm, m', hm', hmm⟩ :=
    Submodule.mem_sup.1 (show (1 : 𝓞 E) ∈ l.Mb ⊔ Mfr l by rw [hcop]; exact Submodule.mem_top)
  have hMN : Mfr l • L ≤ L := Submodule.smul_le_right
  have hmemL' : ∀ v, v ∈ idq (Mfr l) l.Mb L ↔ ∀ b ∈ l.Mb, b • v ∈ Mfr l • L := fun v => Iff.rfl
  have C : ∀ z ∈ Mfr l • L, ∀ y ∈ idq (Mfr l) l.Mb L, ∃ k : ℤ, EF X z y = k := by
    intro z hz y hy
    refine Submodule.smul_induction_on (p := fun z => ∃ k : ℤ, EF X z y = k) hz ?_ ?_
    · intro mu hmu ℓ hℓ
      rw [hsm]
      exact (hL.2 ℓ).1 hℓ _ (hMN ((hmemL' y).1 hy _ (hmemN mu hmu)))
    · rintro z1 z2 ⟨k1, h1⟩ ⟨k2, h2⟩
      exact ⟨k1 + k2, by rw [hadd, h1, h2]; push_cast; ring⟩
  have hFG : (idq (Mfr l) l.Mb L).FG := by
    let f : (Fin r → E) →ₗ[𝓞 E] (Fin r → E) := (l.M : 𝓞 E) • LinearMap.id
    have hf : Function.Injective f := by
      intro a b hab
      have h : (l.M : 𝓞 E) • a = (l.M : 𝓞 E) • b := hab
      rw [hco, hco] at h
      push_cast at h
      exact smul_right_injective _ hM0 h
    have hle : (idq (Mfr l) l.Mb L).map f ≤ L := by
      rintro _ ⟨v, hv, rfl⟩
      exact hMN ((hmemL' v).1 hv _ (M_mem l).2)
    have hN : IsNoetherian (𝓞 E) L := isNoetherian_of_fg_of_noetherian L hL.1
    exact Submodule.fg_of_fg_map_injective f hf (isNoetherian_submodule.1 hN _ hle)
  refine ⟨hFG, fun x => ⟨fun hx y hy => ?_, fun hx => ?_⟩⟩
  · have e : EF X x y = EF X (m • x) y + EF X (m' • x) y := by
      rw [← hadd, ← add_smul, hmm, one_smul]
    obtain ⟨k1, h1⟩ := C _ ((hmemL' x).1 hx m hm) y hy
    obtain ⟨k2, h2⟩ := C _ ((hmemL' y).1 hy _ (hmemN m' hm')) x hx
    refine ⟨k1 - k2, ?_⟩
    rw [e, h1, hsm, GlobalTheory.SW.TensLat.EF_swap X (H.bar m' • y) x, h2]
    push_cast
    ring
  · have step1 : ∀ ν ∈ l.Mb, ν • x ∈ L := by
      intro ν hν
      refine (hL.2 _).2 fun ℓ hℓ => ?_
      have hyL' : H.bar ν • ℓ ∈ idq (Mfr l) l.Mb L := (hmemL' _).2 fun b hb => by
        rw [smul_comm]
        exact Submodule.smul_mem_smul (hmemM ν hν) (L.smul_mem b hℓ)
      obtain ⟨k, hk⟩ := hx _ hyL'
      exact ⟨k, by rw [hsm, hk]⟩
    have step2 : ∀ ν1 ∈ l.Mb, ∀ ν2 ∈ l.Mb, (ν1 * ν2) • x ∈ Mfr l • L := by
      intro ν1 h1 ν2 h2
      have hz : (l.M : E)⁻¹ • ((ν1 * ν2) • x) ∈ L := by
        refine (hL.2 _).2 fun ℓ hℓ => ?_
        have hy : (l.M : E)⁻¹ • ((H.bar ν1 * H.bar ν2) • ℓ) ∈ idq (Mfr l) l.Mb L :=
          (hmemL' _).2 fun b hb => by
            have hbm : b * H.bar ν1 ∈ Ideal.span {(l.M : 𝓞 E)} := by
              rw [← l.prod]; exact Ideal.mul_mem_mul hb (hmemM ν1 h1)
            obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hbm
            have hc' : (c : E) * l.M = (b : E) * (H.bar ν1 : E) := by
              have := congrArg (fun t : 𝓞 E => (t : E)) hc
              push_cast at this
              exact this
            have e : b • ((l.M : E)⁻¹ • ((H.bar ν1 * H.bar ν2) • ℓ)) = H.bar ν2 • (c • ℓ) := by
              rw [hco, hco, hco, hco]
              simp only [smul_smul]
              congr 1
              push_cast
              field_simp
              linear_combination (H.bar ν2 : E) * hc'.symm
            rw [e]
            exact Submodule.smul_mem_smul (hmemM ν2 h2) (L.smul_mem c hℓ)
        obtain ⟨k, hk⟩ := hx _ hy
        refine ⟨k, ?_⟩
        rw [← hk, GlobalTheory.SW.TensLat.EF_smul, hsm]
        congr 1
        rw [map_mul, cc, map_inv₀, map_natCast, smul_comm]
      have e2 : (ν1 * ν2) • x = (l.M : 𝓞 E) • ((l.M : E)⁻¹ • ((ν1 * ν2) • x)) := by
        rw [hco (l.M : 𝓞 E), smul_smul]
        push_cast
        rw [mul_inv_cancel₀ hM0, one_smul]
      rw [e2]
      exact Submodule.smul_mem_smul (M_mem l).1 hz
    rw [hmemL']
    intro b hb
    have e : b • x = (m * b) • x + m' • (b • x) := by
      rw [smul_smul, ← add_smul, ← add_mul, hmm, _root_.one_mul]
    rw [e]
    exact add_mem (step2 m hm b hb) (Submodule.smul_mem_smul hm' (step1 b hb))

end GlobalTheory.Dict.Poisson

theorem GlobalTheory.Dict.poisson_roots : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : E, IsIntegral ℤ w → w + cc w = 1 → ∀ (L : Lt E r) (mk : Dw.La →ₗ[𝓞 E] (Fin r → E)), SelfD X L → IsMark l L mk → ∀ Λ ∈ Vset E n l.M, ∀ N : ℕ, NOK Λ N l.M → ∀ Y : (Fin n → LevQ Dw l) → Matrix (Fin n) (Fin r) E, IsRoots l L mk N Y → ∀ p : TF n g, IsSB p → (∀ u ∈ tens Λ L, epsW X w u • heisG X bas u p = p) → ∀ u ∈ tens Λ ((Ideal.span {2} * conjI (Mfr l)) • L), ∑ᶠ q, cexp (-(2 * Real.pi * I * ((∑ b, EF X (u b) (Y q b) : ℚ) : ℂ))) • heisG X bas (Y q) p = ((Nat.card (Fin n → LevQ Dw l) : ℕ) : ℂ) • heisG X bas u (projA X bas w (tens Λ (idq (Mfr l) (conjI (Mfr l)) L)) p) := by
  intro E _ _ _ H Dw l r g X bas idx n hs hn w hw hw1 L mk hL hmk Λ hΛ N hNOK Y hY p hp hfix u hu
  classical
  have hQ : conjI (Mfr l) = l.Mb := GlobalTheory.Dict.Poisson.conjI_Mfr l
  rw [hQ] at hu ⊢
  have hMP : (l.M : 𝓞 E) ∈ Mfr l := (GlobalTheory.Dict.Poisson.M_mem l).1
  have hMQ : (l.M : 𝓞 E) ∈ l.Mb := (GlobalTheory.Dict.Poisson.M_mem l).2
  have hc : l.Mb ⊔ Mfr l = ⊤ := l.coprime
  have hprod : l.Mb * Mfr l = Ideal.span {(l.M : 𝓞 E)} := l.prod
  have hM0 : (l.M : E) ≠ 0 := Nat.cast_ne_zero.2 (by have := l.three_le; omega)
  have hMs : ∀ x ∈ L, (l.M : E) • x ∈ L := fun x hx => by
    rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hx _
  obtain ⟨-, hMN, hNle⟩ := hNOK
  have hN : ∀ v ∈ stdL E n, (N : E) • v ∈ Λ := by
    intro v hv
    have hv' : v ∈ Formalism.L2.Pj.stdLat E n := by
      refine (Submodule.span_le.2 ?_) hv
      rintro _ ⟨a, rfl⟩
      show Pi.single a 1 ∈ Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E)
      rw [Submodule.mem_pi]
      intro j _
      by_cases h : j = a
      · subst h; rw [Pi.single_eq_same]; exact Submodule.one_le.1 le_rfl
      · rw [Pi.single_eq_of_ne h]; exact Submodule.zero_mem _
    have h1 : (N : 𝓞 E) • v ∈ Ideal.span {(N : 𝓞 E)} • Formalism.L2.Pj.stdLat E n :=
      Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hv'
    have h2 : (N : 𝓞 E) • v ∈ Λ ⊓ Formalism.L2.Pj.stdLat E n := hNle h1
    have h3 := (Submodule.mem_inf.1 h2).1
    rwa [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul E] at h3
  have hA : GlobalTheory.SW.TensVac.Good X w (tens Λ L) := by
    have h := GlobalTheory.SW.TensLat.tens_selfDual_semichar_index E r X g bas idx n hs hn w hw hw1 L hL
      l.M Λ hΛ
    exact ⟨h.1, h.2.1, h.2.2.1⟩
  have hL' := GlobalTheory.Dict.Poisson.selfD_shift l hL
  rw [hQ] at hL'
  have hA' : GlobalTheory.SW.TensVac.Good X w (tens Λ (idq (Mfr l) l.Mb L)) := by
    have h := GlobalTheory.SW.TensLat.tens_selfDual_semichar_index E r X g bas idx n hs hn w hw hw1 _ hL'
      l.M Λ hΛ
    exact ⟨h.1, h.2.1, h.2.2.1⟩
  have hcoord : ∀ q, (2 : E)⁻¹ • Y q ∈ tens Λ (idq (Mfr l) l.Mb L) := by
    intro q
    refine GlobalTheory.Dict.Poisson.half_mem hΛ l.odd hMP hMQ hc hMN hN (fun k b hb => ?_)
      (fun k => (hY q k).2)
    obtain ⟨a, ha, -, hya⟩ := (hY q k).1
    obtain ⟨c, -, hc'⟩ := GlobalTheory.Dict.Poisson.exists_of_mem_smul hprod ha hb
    have e1 : b • (((l.M : E)⁻¹) • mk a) = mk c := by
      rw [smul_comm, ← map_smul mk b a, hc', map_nsmul, ← Nat.cast_smul_eq_nsmul E, smul_smul,
        inv_mul_cancel₀ hM0, one_smul]
    have e : b • Y q k = b • (Y q k - ((l.M : E)⁻¹) • mk a) + mk c := by
      rw [smul_sub, e1, sub_add_cancel]
    rw [e]
    exact add_mem (L.smul_mem b hya) (hmk.mem c)
  have hYA' : ∀ q, Y q ∈ tens Λ (idq (Mfr l) l.Mb L) := fun q => by
    have h := nsmul_mem (hcoord q) 2
    rwa [GlobalTheory.Dict.Poisson.two_half] at h
  have hY1 : ∀ q, epsW X w (Y q) = 1 := fun q => by
    have h := GlobalTheory.SW.TensVac.Good.eps_two hs hA' (hcoord q)
    rwa [GlobalTheory.Dict.Poisson.two_half] at h
  have hu2 := GlobalTheory.Dict.Poisson.half_mem' hΛ hu
  have huA : u ∈ tens Λ L := by
    have h := nsmul_mem hu2 2
    rwa [GlobalTheory.Dict.Poisson.two_half] at h
  have hu1 : epsW X w u = 1 := by
    have h := GlobalTheory.SW.TensVac.Good.eps_two hs hA hu2
    rwa [GlobalTheory.Dict.Poisson.two_half] at h
  have hinj : ∀ q q', Y q - Y q' ∈ tens Λ L → q = q' := by
    intro q q' hd
    funext k
    obtain ⟨a, ha, hqa, hya⟩ := (hY q k).1
    obtain ⟨a', ha', hqa', hya'⟩ := (hY q' k).1
    have hML : (l.M : E) • (Y q - Y q') k ∈ L := by
      have e : (l.M : E) • (Y q k - Y q' k) = (l.M : E) • (Y q k - (l.M : E)⁻¹ • mk a) -
          (l.M : E) • (Y q' k - (l.M : E)⁻¹ • mk a') + (mk a - mk a') := by
        rw [smul_sub, smul_sub, smul_sub, smul_smul, smul_smul, mul_inv_cancel₀ hM0, one_smul,
          one_smul]
        abel
      rw [show (Y q - Y q') k = Y q k - Y q' k from rfl, e]
      exact add_mem (sub_mem (hMs _ hya) (hMs _ hya')) (sub_mem (hmk.mem a) (hmk.mem a'))
    have hrow := GlobalTheory.Dict.Poisson.rows_of_mem hΛ hd k hML
    have hz : (l.M : E)⁻¹ • mk a - (l.M : E)⁻¹ • mk a' ∈ L := by
      have e : (l.M : E)⁻¹ • mk a - (l.M : E)⁻¹ • mk a' =
          (Y q k - Y q' k) - (Y q k - (l.M : E)⁻¹ • mk a) + (Y q' k - (l.M : E)⁻¹ • mk a') := by
        abel
      rw [e]
      exact add_mem (sub_mem hrow hya) hya'
    obtain ⟨b', hb'⟩ := hmk.inj (a - a') (sub_mem ha ha') ⟨_, hz, by
      rw [map_sub, ← smul_sub, ← Nat.cast_smul_eq_nsmul E, smul_smul, mul_inv_cancel₀ hM0,
        one_smul]⟩
    rw [← hqa, ← hqa']
    refine (Submodule.Quotient.eq _).2 ?_
    rw [hb', ← Nat.cast_smul_eq_nsmul (𝓞 E)]
    exact Submodule.smul_mem_smul hMQ Submodule.mem_top
  have hsurj : ∀ y ∈ tens Λ (idq (Mfr l) l.Mb L), ∃ q, y - Y q ∈ tens Λ L := by
    intro y hy
    obtain ⟨y', hy'1, hy'2⟩ :=
      GlobalTheory.Dict.Poisson.exists_rows hΛ (by have := l.three_le; omega) hMQ hy
    choose a ha v hv hav using fun k => hmk.surj _ (hy'1 k)
    refine ⟨fun k => Submodule.Quotient.mk (a k), hy'2 _ (hYA' _) fun k => ?_⟩
    obtain ⟨a', ha', hqa', hya'⟩ := (hY (fun k => Submodule.Quotient.mk (a k)) k).1
    have hdiff : a' - a k ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) := (Submodule.Quotient.eq _).1 hqa'
    obtain ⟨c, -, hc'⟩ := GlobalTheory.Dict.Poisson.exists_of_mem_inter hprod hc (sub_mem ha' (ha k)) hdiff
    have hy'k : y' k = (l.M : E)⁻¹ • mk (a k) + v k := by
      have h : (l.M : E)⁻¹ • ((l.M : E) • y' k) = (l.M : E)⁻¹ • (mk (a k) + l.M • v k) := by
        rw [hav k]
      rw [smul_smul, inv_mul_cancel₀ hM0, one_smul, smul_add, ← Nat.cast_smul_eq_nsmul E, smul_smul,
        inv_mul_cancel₀ hM0, one_smul] at h
      exact h
    have e2 : (l.M : E)⁻¹ • mk a' = (l.M : E)⁻¹ • mk (a k) + mk c := by
      have h2 : a' = a k + l.M • c := by rw [← hc']; abel
      rw [h2, map_add, map_nsmul, smul_add, ← Nat.cast_smul_eq_nsmul E, smul_smul,
        inv_mul_cancel₀ hM0, one_smul]
    have e : Y (fun k => Submodule.Quotient.mk (a k)) k - y' k =
        (Y (fun k => Submodule.Quotient.mk (a k)) k - (l.M : E)⁻¹ • mk a') + mk c - v k := by
      rw [hy'k, e2]; abel
    rw [e]
    exact sub_mem (add_mem hya' (hmk.mem c)) (hv k)
  exact GlobalTheory.Dict.Poisson.fourier_of_reps idx hs hn hA hA' hp hfix Y hYA' hY1 hinj hsurj huA hu1
