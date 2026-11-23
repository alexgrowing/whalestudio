import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLatIntVec

noncomputable section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.TorCard

theorem torsion_exact_bound {R A B C : Type*} [CommRing R] [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [Module R A] [Module R B] [Module R C] (I : Ideal R)
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) (hf : Function.Injective f)
    (hfg : ∀ b, g b = 0 → ∃ a, f a = b)
    [Finite {x : A // ∀ a ∈ I, a • x = 0}] [Finite {x : C // ∀ a ∈ I, a • x = 0}] :
    Finite {x : B // ∀ a ∈ I, a • x = 0} ∧
      Nat.card {x : B // ∀ a ∈ I, a • x = 0} ≤
        Nat.card {x : A // ∀ a ∈ I, a • x = 0} * Nat.card {x : C // ∀ a ∈ I, a • x = 0} := by
  classical
  let TB := {x : B // ∀ a ∈ I, a • x = 0}
  let TA := {x : A // ∀ a ∈ I, a • x = 0}
  let TC := {x : C // ∀ a ∈ I, a • x = 0}
  let h : TB → TC := fun b => ⟨g b.1, fun a ha => by rw [← map_smul, b.2 a ha, map_zero]⟩

  let s : TC → TB := fun c => if hc : ∃ b, h b = c then hc.choose else ⟨0, fun a _ => smul_zero a⟩
  have hs : ∀ b : TB, h (s (h b)) = h b := by
    intro b
    have hc : ∃ b', h b' = h b := ⟨b, rfl⟩
    simp only [s, dif_pos hc]
    exact hc.choose_spec
  have hk : ∀ b : TB, ∃ a, f a = b.1 - (s (h b)).1 := by
    intro b
    apply hfg
    have := congrArg Subtype.val (hs b)
    simp only [h] at this
    rw [map_sub, this, sub_self]
  let k : TB → A := fun b => (hk b).choose
  have hkf : ∀ b, f (k b) = b.1 - (s (h b)).1 := fun b => (hk b).choose_spec
  have hkt : ∀ b, ∀ a ∈ I, a • k b = 0 := by
    intro b a ha
    apply hf
    rw [map_smul, hkf, map_zero, smul_sub, b.2 a ha, (s (h b)).2 a ha, sub_zero]
  let Φ : TB → TA × TC := fun b => (⟨k b, hkt b⟩, h b)
  have hΦ : Function.Injective Φ := by
    intro b b' e
    have e1 : k b = k b' := congrArg (fun z : TA × TC => z.1.1) e
    have e2 : h b = h b' := congrArg (fun z : TA × TC => z.2) e
    have e3 := hkf b
    rw [e1, hkf b', e2] at e3
    exact Subtype.ext (sub_left_injective e3).symm
  refine ⟨Finite.of_injective Φ hΦ, ?_⟩
  calc Nat.card TB ≤ Nat.card (TA × TC) := Nat.card_le_card_of_injective Φ hΦ
    _ = _ := Nat.card_prod _ _

variable {K : Type} [Field K] [NumberField K]

theorem exists_smul_mem {m : ℕ} {L : Submodule (𝓞 K) (Fin m → K)} (hL : IsLat L)
    (v : Fin m → K) : ∃ t : 𝓞 K, t ≠ 0 ∧ t • v ∈ L := by
  have hv : v ∈ Submodule.span K (L : Set (Fin m → K)) := by rw [hL.2]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨t, ht, hty⟩ := hy
    refine ⟨s * t, mul_ne_zero hs ht, ?_⟩
    have e : (s * t) • (x + y) = t • (s • x) + s • (t • y) := by
      rw [smul_add, smul_smul, smul_smul, mul_comm t s]
    rw [e]
    exact L.add_mem (L.smul_mem _ hsx) (L.smul_mem _ hty)
  | smul c x _ hx =>
    obtain ⟨t, ht, htx⟩ := hx
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) c
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have hbK : algebraMap (𝓞 K) K b ≠ 0 := by
      simpa using hb0
    refine ⟨b * t, mul_ne_zero hb0 ht, ?_⟩
    have e : (b * t) • ((algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b) • x) = a • (t • x) := by
      ext i
      change (b * t) • ((algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b) * x i) = a • (t • x i)
      simp only [Algebra.smul_def, map_mul]
      field_simp
    rw [e]
    exact L.smul_mem _ htx

theorem rank_one (𝔠 : Submodule (𝓞 K) K) (hfg : 𝔠.FG) (h0 : 𝔠 ≠ ⊥)
    (𝔞 : Ideal (𝓞 K)) (h𝔞 : 𝔞 ≠ ⊥) :
    Finite {x : K ⧸ 𝔠 // ∀ a ∈ 𝔞, a • x = 0} ∧
      Nat.card {x : K ⧸ 𝔠 // ∀ a ∈ 𝔞, a • x = 0} ≤ Ideal.absNorm 𝔞 := by
  classical
  obtain ⟨d, hd, hdi⟩ := FractionalIdeal.isFractional_of_fg (S := (𝓞 K)⁰) hfg
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  obtain ⟨a₀, ha₀, ha₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔞
  obtain ⟨c₀, hc₀, hc₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
  set e : 𝓞 K := d * a₀ with he
  have he0 : e ≠ 0 := mul_ne_zero hd0 ha₀0
  have heK : algebraMap (𝓞 K) K e ≠ 0 := by simpa using he0
  let J : Ideal (𝓞 K) :=
    { carrier := {o | ∀ a ∈ 𝔞, a • (algebraMap (𝓞 K) K o / algebraMap (𝓞 K) K e) ∈ 𝔠}
      add_mem' := by
        intro x y hx hy a ha
        have := 𝔠.add_mem (hx a ha) (hy a ha)
        rw [map_add, add_div, smul_add]
        exact this
      zero_mem' := by
        intro a _
        simp
      smul_mem' := by
        intro c x hx a ha
        have := 𝔠.smul_mem c (hx a ha)
        have e1 : a • (algebraMap (𝓞 K) K (c • x) / algebraMap (𝓞 K) K e) =
            c • a • (algebraMap (𝓞 K) K x / algebraMap (𝓞 K) K e) := by
          rw [smul_eq_mul]
          simp only [Algebra.smul_def, map_mul]
          ring
        rw [e1]
        exact this }
  have hJmem : ∀ o, o ∈ J ↔ ∀ a ∈ 𝔞, a • (algebraMap (𝓞 K) K o / algebraMap (𝓞 K) K e) ∈ 𝔠 :=
    fun _ => Iff.rfl
  have hJ0 : J ≠ ⊥ := by
    obtain ⟨o, ho⟩ := hdi c₀ hc₀
    have ho' : algebraMap (𝓞 K) K o = algebraMap (𝓞 K) K d * c₀ := by
      rw [ho, Algebra.smul_def]
    have hdK : algebraMap (𝓞 K) K d ≠ 0 := by simpa using hd0
    have ho0 : o ≠ 0 := by
      intro h
      rw [h, map_zero] at ho'
      exact mul_ne_zero hdK hc₀0 ho'.symm
    intro hbot
    have hmem : e * o ∈ J := by
      intro a _
      have e1 : a • (algebraMap (𝓞 K) K (e * o) / algebraMap (𝓞 K) K e) = (a * d) • c₀ := by
        rw [map_mul, mul_div_cancel_left₀ _ heK, ho', Algebra.smul_def, Algebra.smul_def, map_mul]
        ring
      rw [e1]
      exact 𝔠.smul_mem _ hc₀
    rw [hbot, Ideal.mem_bot] at hmem
    exact mul_ne_zero he0 ho0 hmem
  have hmulmem : ∀ z ∈ 𝔞 * J, algebraMap (𝓞 K) K z / algebraMap (𝓞 K) K e ∈ 𝔠 := by
    intro z hz
    refine Submodule.mul_induction_on hz ?_ ?_
    · intro a ha j hj
      have := hj a ha
      rw [Algebra.smul_def] at this
      rw [map_mul, mul_div_assoc]
      exact this
    · intro x y hx hy
      rw [map_add, add_div]
      exact 𝔠.add_mem hx hy

  have hle : (𝔞 * J) ≤ J := Ideal.mul_le_right
  have hleA : (𝔞 * J).toAddSubgroup ≤ J.toAddSubgroup := hle
  have hNJ : Ideal.absNorm J ≠ 0 := by
    simpa [Ideal.absNorm_eq_zero_iff] using hJ0
  have hN𝔞 : Ideal.absNorm 𝔞 ≠ 0 := by
    simpa [Ideal.absNorm_eq_zero_iff] using h𝔞
  have hidx : (𝔞 * J).toAddSubgroup.relIndex J.toAddSubgroup = Ideal.absNorm 𝔞 := by
    have h1 := AddSubgroup.relIndex_mul_index hleA
    have h2 : ∀ I : Ideal (𝓞 K), I.toAddSubgroup.index = Ideal.absNorm I := by
      intro I
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
      rfl
    rw [h2, h2, map_mul] at h1
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hNJ) h1
  let Q := ↥J.toAddSubgroup ⧸ (𝔞 * J).toAddSubgroup.addSubgroupOf J.toAddSubgroup
  have hQfin : Finite Q := by
    apply Nat.finite_of_card_ne_zero
    have : Nat.card Q = Ideal.absNorm 𝔞 := hidx
    rw [this]
    exact hN𝔞
  have hQcard : Nat.card Q = Ideal.absNorm 𝔞 := hidx

  have hrep : ∀ t : {x : K ⧸ 𝔠 // ∀ a ∈ 𝔞, a • x = 0}, ∃ o : ↥J.toAddSubgroup,
      Submodule.Quotient.mk (algebraMap (𝓞 K) K o.1 / algebraMap (𝓞 K) K e) = t.1 := by
    rintro ⟨t, ht⟩
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ t
    have hx : ∀ a ∈ 𝔞, a • x ∈ 𝔠 := by
      intro a ha
      have := ht a ha
      rwa [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at this
    obtain ⟨o, ho⟩ := hdi _ (hx a₀ ha₀)
    have ho' : algebraMap (𝓞 K) K o / algebraMap (𝓞 K) K e = x := by
      have hda : algebraMap (𝓞 K) K d * algebraMap (𝓞 K) K a₀ ≠ 0 := by
        rw [← map_mul]
        exact heK
      rw [ho, he, Algebra.smul_def, Algebra.smul_def, map_mul, ← mul_assoc]
      exact mul_div_cancel_left₀ x hda
    refine ⟨⟨o, ?_⟩, by simp only [ho']⟩
    intro a ha
    rw [ho']
    exact hx a ha
  choose r hr using hrep
  let ψ : {x : K ⧸ 𝔠 // ∀ a ∈ 𝔞, a • x = 0} → Q := fun t => QuotientAddGroup.mk (r t)
  have hψ : Function.Injective ψ := by
    intro t t' h
    have h1 := QuotientAddGroup.eq.mp h
    rw [AddSubgroup.mem_addSubgroupOf] at h1
    have h2 := hmulmem _ h1
    apply Subtype.ext
    rw [← hr t, ← hr t']
    rw [Submodule.Quotient.eq]
    have h3 := 𝔠.neg_mem h2
    convert h3 using 1
    simp
    ring
  refine ⟨Finite.of_injective ψ hψ, ?_⟩
  calc _ ≤ Nat.card Q := Nat.card_le_card_of_injective ψ hψ
    _ = _ := hQcard

def ins (K : Type) [Field K] [NumberField K] (m : ℕ) :
    (Fin m → K) →ₗ[𝓞 K] (Fin (m + 1) → K) where
  toFun x := Fin.cons 0 x
  map_add' x y := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  map_smul' c x := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

def hd (K : Type) [Field K] [NumberField K] (m : ℕ) : (Fin (m + 1) → K) →ₗ[𝓞 K] K :=
  LinearMap.proj 0

theorem ins_injective (m : ℕ) : Function.Injective (ins K m) := by
  intro x y h
  ext j
  exact congrFun h j.succ

theorem isLat_comap_ins {m : ℕ} {L : Submodule (𝓞 K) (Fin (m + 1) → K)} (hL : IsLat L) :
    IsLat (L.comap (ins K m)) := by
  refine ⟨?_, ?_⟩
  · haveI : IsNoetherian (𝓞 K) L := isNoetherian_of_fg_of_noetherian L hL.1
    have h1 : (L.comap (ins K m)).map (ins K m) ≤ L := Submodule.map_comap_le _ _
    exact Submodule.fg_of_fg_map_injective _ (ins_injective m) (isNoetherian_submodule.mp this _ h1)
  · rw [eq_top_iff]
    intro v _
    obtain ⟨t, ht, htv⟩ := exists_smul_mem hL (ins K m v)
    have hmem : t • v ∈ L.comap (ins K m) := by
      rw [Submodule.mem_comap, map_smul]
      exact htv
    have htK : algebraMap (𝓞 K) K t ≠ 0 := by simpa using ht
    have e : v = (algebraMap (𝓞 K) K t)⁻¹ • (t • v) := by
      ext i
      change v i = (algebraMap (𝓞 K) K t)⁻¹ * (t • v i)
      rw [Algebra.smul_def]
      field_simp
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

theorem map_hd_ne_bot {m : ℕ} {L : Submodule (𝓞 K) (Fin (m + 1) → K)} (hL : IsLat L) :
    L.map (hd K m) ≠ ⊥ := by
  obtain ⟨t, ht, htv⟩ := exists_smul_mem hL (Pi.single 0 1)
  intro h
  have h1 : hd K m (t • Pi.single 0 1) ∈ L.map (hd K m) := Submodule.mem_map_of_mem htv
  rw [h, Submodule.mem_bot] at h1
  have h2 : algebraMap (𝓞 K) K t = 0 := by
    have h3 : hd K m (t • Pi.single 0 1) = t • (1 : K) := by
      simp [hd]
    rw [h3, Algebra.smul_def, mul_one] at h1
    exact h1
  exact ht (by simpa using h2)

theorem torsion_card_le_by_rank (𝔞 : Ideal (𝓞 K)) (h𝔞 : 𝔞 ≠ ⊥) (m : ℕ) :
    ∀ L : Submodule (𝓞 K) (Fin m → K), IsLat L →
      Finite {x : (Fin m → K) ⧸ L // ∀ a ∈ 𝔞, a • x = 0} ∧
        Nat.card {x : (Fin m → K) ⧸ L // ∀ a ∈ 𝔞, a • x = 0} ≤ Ideal.absNorm 𝔞 ^ m := by
  induction m with
  | zero =>
    intro L _
    have hs : Subsingleton {x : (Fin 0 → K) ⧸ L // ∀ a ∈ 𝔞, a • x = 0} := by
      refine ⟨fun x y => Subtype.ext ?_⟩
      obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ x.1
      obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective _ y.1
      rw [← ha, ← hb, Subsingleton.elim a b]
    refine ⟨inferInstance, ?_⟩
    simpa using Finite.card_le_one_iff_subsingleton.mpr hs
  | succ m ih =>
    intro L hL
    obtain ⟨fA, cA⟩ := ih _ (isLat_comap_ins hL)
    obtain ⟨fC, cC⟩ := rank_one (L.map (hd K m)) (hL.1.map _) (map_hd_ne_bot hL) 𝔞 h𝔞
    let f := (L.comap (ins K m)).mapQ L (ins K m) le_rfl
    let g := L.mapQ (L.map (hd K m)) (hd K m) (Submodule.le_comap_map _ _)
    have hf : Function.Injective f := by
      refine (injective_iff_map_eq_zero f).2 ?_
      intro x hx
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [Submodule.Quotient.mk_eq_zero]
      have h1 : Submodule.Quotient.mk (p := L) (ins K m a) = 0 := hx
      rwa [Submodule.Quotient.mk_eq_zero] at h1
    have hfg : ∀ b, g b = 0 → ∃ a, f a = b := by
      intro b hb
      obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
      have h1 : Submodule.Quotient.mk (p := L.map (hd K m)) (hd K m b) = 0 := hb
      rw [Submodule.Quotient.mk_eq_zero] at h1
      obtain ⟨l, hl, hle⟩ := Submodule.mem_map.mp h1
      refine ⟨Submodule.Quotient.mk (Fin.tail (b - l)), ?_⟩
      have h2 : ins K m (Fin.tail (b - l)) = b - l := by
        ext i
        refine Fin.cases ?_ (fun j => ?_) i
        · have h3 : l 0 = b 0 := hle
          simp [ins, h3]
        · simp [ins, Fin.tail]
      change Submodule.Quotient.mk (p := L) (ins K m (Fin.tail (b - l))) = _
      rw [h2, Submodule.Quotient.eq]
      have := L.neg_mem hl
      convert this using 1
      abel
    obtain ⟨fB, cB⟩ := torsion_exact_bound 𝔞 f g hf hfg
    refine ⟨fB, cB.trans ?_⟩
    rw [pow_succ]
    exact Nat.mul_le_mul cA cC

theorem tor_card : ∀ (K : Type) [Field K] [NumberField K] (m : ℕ)
    (L : Submodule (𝓞 K) (Fin m → K)), IsLat L → ∀ 𝔞 : Ideal (𝓞 K), 𝔞 ≠ ⊥ →
      Finite {x : (Fin m → K) ⧸ L // ∀ a ∈ 𝔞, a • x = 0} ∧
        Nat.card {x : (Fin m → K) ⧸ L // ∀ a ∈ 𝔞, a • x = 0} ≤ Ideal.absNorm 𝔞 ^ m :=
  fun _ _ _ m L hL 𝔞 h𝔞 => torsion_card_le_by_rank 𝔞 h𝔞 m L hL

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.TorCard
