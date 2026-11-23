import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.AllPartsTransfer

open Module NumberField

noncomputable section

namespace Formalism.IndefR.LatticeTransfer

open Formalism.IndefR.TransferLatticeStatement

namespace IdempotentLemmas

variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]

lemma charOf_conj {T : Type} [AddCommGroup T] [Module K T] (τ : Representation K G T)
    (g h : G) : charOf τ (h * g * h⁻¹) = charOf τ g := by
  unfold charOf
  by_cases hf : Module.Finite K T
  · rw [map_mul τ, map_mul τ, LinearMap.trace_mul_comm K (τ h * τ g), ← mul_assoc, ← map_mul τ,
      inv_mul_cancel, map_one, one_mul]
  · have h0 : LinearMap.trace K T = 0 := by
      first
      | exact LinearMap.trace_eq_zero_of_not_finite hf
      | exact LinearMap.trace_eq_zero_of_not_finite (R := K) (M := T) hf
      | (rw [LinearMap.trace, dif_neg]; rintro ⟨_, ⟨b⟩⟩; exact hf (Module.Finite.of_basis b))
      | (unfold LinearMap.trace; rw [dif_neg]; rintro ⟨_, ⟨b⟩⟩; exact hf (Module.Finite.of_basis b))
    simp [h0]

lemma eS_mul_rho {T V : Type} [AddCommGroup T] [Module K T] [AddCommGroup V] [Module K V]
    (τ : Representation K G T) (ρ : Representation K G V) (y : G) :
    eS τ ρ * ρ y = (charOf τ 1 / (Fintype.card G : K)) • ∑ g : G, charOf τ (y * g⁻¹) • ρ g := by
  unfold eS
  rw [smul_mul_assoc, Finset.sum_mul]
  congr 1
  simp_rw [smul_mul_assoc, ← map_mul]
  exact Fintype.sum_equiv (Equiv.mulRight y) _ _ (fun x => by simp [mul_inv_rev])

lemma eS_mul_asAlg {T V : Type} [AddCommGroup T] [Module K T] [AddCommGroup V] [Module K V]
    (τ : Representation K G T) (ρ : Representation K G V) (a : MonoidAlgebra K G) :
    eS τ ρ * ρ.asAlgebraHom a = (charOf τ 1 / (Fintype.card G : K)) •
      ∑ g : G, LinearMap.trace K T (τ.asAlgebraHom a * τ g⁻¹) • ρ g := by
  induction a using MonoidAlgebra.induction_on with
  | of y =>
    rw [Representation.asAlgebraHom_of, Representation.asAlgebraHom_of, eS_mul_rho]
    simp only [charOf, ← map_mul]
  | add f g hf hg =>
    rw [map_add, mul_add, hf, hg, ← smul_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [map_add, add_mul, map_add, add_smul]
  | smul r f hf =>
    rw [map_smul, mul_smul_comm, hf, smul_comm r, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [map_smul, smul_mul_assoc, map_smul, smul_eq_mul, mul_smul]

lemma eS_comm {T V : Type} [AddCommGroup T] [Module K T] [AddCommGroup V] [Module K V]
    (τ : Representation K G T) (ρ : Representation K G V) (g : G) :
    eS τ ρ * ρ g = ρ g * eS τ ρ := by
  rw [eS_mul_rho]
  unfold eS
  rw [mul_smul_comm, Finset.mul_sum]
  congr 1
  simp_rw [mul_smul_comm, ← map_mul]
  symm
  refine Fintype.sum_equiv (Equiv.mulLeft g) _ _ (fun x => ?_)
  simp only [Equiv.coe_mulLeft]
  congr 1
  rw [show g * (g * x)⁻¹ = g * x⁻¹ * g⁻¹ by group, charOf_conj]

lemma trace_eS {T U : Type} [AddCommGroup T] [Module K T] [AddCommGroup U] [Module K U]
    (τ : Representation K G T) (σ : Representation K G U) :
    LinearMap.trace K U (eS τ σ) =
      charOf τ 1 / (Fintype.card G : K) * ∑ x : G, charOf τ x⁻¹ * charOf σ x := by
  unfold eS
  rw [map_smul, map_sum, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_smul, smul_eq_mul]
  rfl

lemma sum_char_eq [CharZero K] {T U : Type} [AddCommGroup T] [Module K T] [FiniteDimensional K T]
    [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    (τ : Representation K G T) (σ : Representation K G U) :
    ∑ x : G, charOf τ x⁻¹ * charOf σ x =
      (Fintype.card G : K) * finrank K (Representation.IntertwiningMap τ σ) := by
  have hc : (Nat.card G : K) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have : Invertible (Nat.card G : K) := invertibleOfNonzero hc
  have h := Representation.card_inv_mul_sum_char_mul_char_eq_finrank τ σ
  rw [← Nat.card_eq_fintype_card, ← h, mul_inv_cancel_left₀ hc]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [mul_comm]
  rfl

lemma finrank_int_self {T : Type} [AddCommGroup T] [Module K T] [Nontrivial T]
    (τ : Representation K G T)
    (h : ∀ f : T →ₗ[K] T, (∀ g : G, f ∘ₗ τ g = τ g ∘ₗ f) → ∃ c : K, f = c • LinearMap.id) :
    finrank K (Representation.IntertwiningMap τ τ) = 1 := by
  have hne : Representation.IntertwiningMap.id τ ≠ 0 := by
    obtain ⟨v, hv⟩ := exists_ne (0 : T)
    intro h0
    apply hv
    have := congrArg (fun f : Representation.IntertwiningMap τ τ => f v) h0
    simpa using this
  rw [finrank_eq_one_iff_of_nonzero' _ hne]
  intro w
  obtain ⟨c, hc⟩ := h w.toLinearMap (fun g => w.isIntertwining' g)
  refine ⟨c, ?_⟩
  apply DFunLike.ext
  intro v
  have hv : w v = c • v := by
    rw [← Representation.IntertwiningMap.toLinearMap_apply, hc]
    simp
  rw [hv]
  simp

lemma int_eq_zero {T U : Type} [AddCommGroup T] [Module K T] [FiniteDimensional K T]
    [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    (τ : Representation K G T) (σ : Representation K G U)
    (hτ : ∀ W : Submodule K T, (∀ g : G, ∀ w ∈ W, τ g w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hσ : ∀ W : Submodule K U, (∀ g : G, ∀ w ∈ W, σ g w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hch : charOf τ ≠ charOf σ) (f : Representation.IntertwiningMap τ σ) : f = 0 := by
  by_contra hf
  have hf' : f.toLinearMap ≠ 0 := fun h =>
    hf (Representation.IntertwiningMap.ext (by simpa using h))
  have hker : LinearMap.ker f.toLinearMap = ⊥ := by
    rcases hτ (LinearMap.ker f.toLinearMap) (fun g w hw => by
      simp only [LinearMap.mem_ker, Representation.IntertwiningMap.toLinearMap_apply] at hw ⊢
      rw [f.isIntertwining, hw, map_zero]) with h | h
    · exact h
    · exact absurd (LinearMap.ker_eq_top.mp h) hf'
  have hrange : LinearMap.range f.toLinearMap = ⊤ := by
    rcases hσ (LinearMap.range f.toLinearMap) (fun g w hw => by
      obtain ⟨v, rfl⟩ := hw
      exact ⟨τ g v, LinearMap.congr_fun (f.isIntertwining' g) v⟩) with h | h
    · exact absurd (LinearMap.range_eq_bot.mp h) hf'
    · exact h
  let e : T ≃ₗ[K] U := LinearEquiv.ofBijective f.toLinearMap
    ⟨LinearMap.ker_eq_bot.mp hker, LinearMap.range_eq_top.mp hrange⟩
  have he : ∀ x, e x = f x := fun x => rfl
  apply hch
  funext g
  have hconj : e.conj (τ g) = σ g := by
    apply LinearMap.ext
    intro u
    rw [LinearEquiv.conj_apply_apply, he, f.isIntertwining, ← he, LinearEquiv.apply_symm_apply]
  show LinearMap.trace K T (τ g) = LinearMap.trace K U (σ g)
  rw [← hconj, LinearMap.trace_conj']

def eAlg {T : Type} [AddCommGroup T] [Module K T] (τ : Representation K G T) :
    MonoidAlgebra K G :=
  ∑ x : G, MonoidAlgebra.single x (charOf τ 1 / (Fintype.card G : K) * charOf τ x⁻¹)

lemma asAlg_eAlg {T V : Type} [AddCommGroup T] [Module K T] [AddCommGroup V] [Module K V]
    (τ : Representation K G T) (ρ : Representation K G V) :
    ρ.asAlgebraHom (eAlg τ) = eS τ ρ := by
  unfold eAlg eS
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Representation.asAlgebraHom_single, mul_smul]

lemma comm_epP [NumberField K] {V : Type} [AddCommGroup V] [Module K V]
    (ρ : Representation K G V) (X : Module.End K V) (hX : ∀ g, X * ρ g = ρ g * X)
    (H : Subgroup G) (χ : H →* (𝓞 K)ˣ) : X * epP H χ ρ = epP H χ ρ * X := by
  unfold epP
  rw [mul_smul_comm, smul_mul_assoc, Finset.mul_sum, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, hX]

lemma idem_gen {V : Type} [AddCommGroup V] [Module K V] {H : Type} [Group H] {_ : Fintype H}
    (a : H → K) (ha : ∀ h k, a h * a k = a (h * k)) (π : H →* Module.End K V)
    (hn : (Nat.card H : K) ≠ 0) :
    ((Nat.card H : K)⁻¹ • ∑ h : H, a h • π h) * ((Nat.card H : K)⁻¹ • ∑ h : H, a h • π h) =
      (Nat.card H : K)⁻¹ • ∑ h : H, a h • π h := by
  have key : (∑ h : H, a h • π h) * (∑ h : H, a h • π h) = (Nat.card H : K) • ∑ h : H, a h • π h := by
    rw [Finset.sum_mul]
    have e0 : ∀ h : H, (a h • π h) * ∑ k : H, a k • π k = ∑ m : H, a m • π m := by
      intro h
      rw [Finset.mul_sum]
      have e : ∀ k : H, (a h • π h) * (a k • π k) = a (h * k) • π (h * k) := by
        intro k
        rw [smul_mul_smul_comm, ha, map_mul]
      simp_rw [e]
      exact Equiv.sum_comp (Equiv.mulLeft h) (fun m => a m • π m)
    simp_rw [e0]
    rw [Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul, Nat.card_eq_fintype_card]
  rw [smul_mul_smul_comm, key, smul_smul]
  congr 1
  field_simp

end IdempotentLemmas

open IdempotentLemmas

theorem keyZero : KeyZero := by
  intro K _ G _ _ T _ _ τ V _ _ ρ a ha
  rw [← Module.End.mul_eq_comp]
  simpa [ha] using eS_mul_asAlg τ ρ a

theorem schur : Schur := by
  intro K _ _ G _ _ S T _ _ _ τ hgood
  obtain ⟨hnt, hirr, habs, hinj⟩ := hgood
  have hcomm : ∀ s t, ∃ c : K, eS (τ s) (τ t) = c • LinearMap.id := fun s t =>
    habs t _ (fun g => by
      rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp]
      exact eS_comm (τ s) (τ t) g)
  have hdim : ∀ s, charOf (τ s) 1 = (finrank K (T s) : K) := fun s => by
    unfold charOf
    rw [map_one, LinearMap.trace_one]
  have hpos : ∀ s, (finrank K (T s) : K) ≠ 0 := fun s => by
    haveI := hnt s
    exact_mod_cast (Module.finrank_pos (R := K) (M := T s)).ne'
  have hcard : (Fintype.card G : K) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have htr : ∀ s t, LinearMap.trace K (T t) (eS (τ s) (τ t)) =
      (finrank K (T s) : K) * finrank K (Representation.IntertwiningMap (τ s) (τ t)) := by
    intro s t
    rw [trace_eS, sum_char_eq, hdim]
    field_simp
  have hone : ∀ s, finrank K (Representation.IntertwiningMap (τ s) (τ s)) = 1 := fun s => by
    haveI := hnt s
    exact finrank_int_self (τ s) (habs s)
  have hsum : ∀ s, ∑ x : G, charOf (τ s) x⁻¹ * charOf (τ s) x = (Fintype.card G : K) := by
    intro s
    rw [sum_char_eq, hone s, Nat.cast_one, mul_one]
  refine ⟨fun s => ?_, fun s t hst => ?_, hsum⟩
  · obtain ⟨c, hc⟩ := hcomm s s
    have h1 := htr s s
    rw [hc, map_smul, LinearMap.trace_id, smul_eq_mul, hone s, Nat.cast_one, mul_one] at h1
    have h2 : (c - 1) * (finrank K (T s) : K) = 0 := by rw [sub_mul, h1, one_mul, sub_self]
    have h3 : c = 1 := sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_right (hpos s))
    rw [hc, h3, one_smul]
  · obtain ⟨c, hc⟩ := hcomm s t
    have hne : charOf (τ s) ≠ charOf (τ t) := fun h => hst (hinj s t h)
    haveI : Subsingleton (Representation.IntertwiningMap (τ s) (τ t)) :=
      ⟨fun f g => (int_eq_zero (τ s) (τ t) (hirr s) (hirr t) hne f).trans
        (int_eq_zero (τ s) (τ t) (hirr s) (hirr t) hne g).symm⟩
    have h1 := htr s t
    rw [hc, map_smul, LinearMap.trace_id, smul_eq_mul,
      Module.finrank_zero_of_subsingleton (R := K) (M := Representation.IntertwiningMap (τ s) (τ t)),
      Nat.cast_zero, mul_zero] at h1
    have h3 : c = 0 := (mul_eq_zero.1 h1).resolve_right (hpos t)
    rw [hc, h3, zero_smul]

theorem idemE : IdemE := by
  intro K _ _ G _ _ S T _ _ _ τ hgood V _ _ ρ
  obtain ⟨h1, h2, -⟩ := schur K G S T τ hgood
  have key : ∀ s t, eS (τ s) ρ ∘ₗ eS (τ t) ρ = (charOf (τ s) 1 / (Fintype.card G : K)) •
      ∑ g : G, LinearMap.trace K (T s) (eS (τ t) (τ s) * τ s g⁻¹) • ρ g := by
    intro s t
    rw [← Module.End.mul_eq_comp, ← asAlg_eAlg (τ t) ρ, eS_mul_asAlg, asAlg_eAlg]
  refine ⟨fun s => ?_, fun s t hst => ?_⟩
  · rw [key, h1 s]
    unfold eS
    congr 1
  · rw [key, h2 t s (Ne.symm hst)]
    simp

theorem idemP_of (h : CharFacts) : IdemP := by
  intro K _ _ G _ _ V _ _ _ _ ρ
  have hs' : ∀ (r : 𝓞 K) (v : V), ((r : K)) • v = r • v := fun r v => algebraMap_smul K r v
  have hcard : (Fintype.card G : K) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  refine ⟨fun T _ _ _ τ => ⟨fun g => eS_comm τ ρ g,
    fun H χ => comm_epP ρ (eS τ ρ) (fun g => eS_comm τ ρ g) H χ, fun A hA a ha => ?_⟩,
    fun H χ => ⟨?_, fun A hA a ha => ?_⟩⟩
  · have hint : ∀ x : G, IsIntegral ℤ (charOf τ 1 * charOf τ x⁻¹) :=
      fun x => (h K G T τ 1).1.mul (h K G T τ x⁻¹).1
    have hd : (Fintype.card G : K) * (charOf τ 1 / (Fintype.card G : K)) = charOf τ 1 := by
      field_simp
    rw [← hs', show ((Fintype.card G : 𝓞 K) : K) = (Fintype.card G : K) by simp, eS,
      LinearMap.smul_apply, smul_smul, hd, LinearMap.sum_apply, Finset.smul_sum]
    refine A.sum_mem fun x _ => ?_
    rw [LinearMap.smul_apply, smul_smul]
    have hx : charOf τ 1 * charOf τ x⁻¹ ∈ integralClosure ℤ K := hint x
    let r : 𝓞 K := ⟨_, hx⟩
    have hm := A.smul_mem r (hA x a ha)
    have he : (charOf τ 1 * charOf τ x⁻¹) • ρ x a = r • ρ x a := hs' r (ρ x a)
    rw [he]
    exact hm
  · have hn : (Nat.card H : K) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    show epP H χ ρ * epP H χ ρ = epP H χ ρ
    unfold epP
    exact idem_gen (fun h : H => (((χ h⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K))
      (fun h k => by simp only [mul_inv_rev, map_mul, Units.val_mul]; ring)
      (ρ.comp H.subtype) hn
  · have hn : (Nat.card H : K) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    have hI : ((Fintype.card G : 𝓞 K) : K) * (Nat.card H : K)⁻¹ = ((H.index : 𝓞 K) : K) := by
      have hG : (Fintype.card G : K) = (Nat.card H : K) * H.index := by
        rw [← Nat.card_eq_fintype_card, ← H.card_mul_index, Nat.cast_mul]
      simp only [map_natCast]
      rw [hG]
      field_simp
    rw [← hs']
    unfold epP
    rw [LinearMap.smul_apply, smul_smul, hI, hs', LinearMap.sum_apply]
    refine A.smul_mem _ (A.sum_mem fun h _ => ?_)
    rw [LinearMap.smul_apply, hs']
    exact A.smul_mem _ (hA _ _ ha)

end Formalism.IndefR.LatticeTransfer
