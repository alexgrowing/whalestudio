import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LemmaKOfSteps

noncomputable section

open NumberField NumberField.InfinitePlace IsDedekindDomain UpperTheory.V.KL UpperTheory.V.ZK

namespace LateralTheory.Q.SFewOfCut

theorem one_add_pow_eq (w : ℤ) (d : ℕ) : ∃ t : ℤ, (1 + w) ^ d = 1 + w * (d + w * t) := by
  induction d with
  | zero => exact ⟨0, by simp⟩
  | succ d ih =>
    obtain ⟨t, ht⟩ := ih
    exact ⟨t + d + w * t, by rw [pow_succ, ht]; push_cast; ring⟩

theorem not_dvd_pow_sub_one (l c M d : ℕ) (hl : l.Prime) (hM : M < l ^ c) (hd0 : 0 < d) (hd : d < M) :
    ¬ (l : ℤ) ^ (c + M) ∣ (1 + (l : ℤ) ^ c) ^ d - 1 := by
  obtain ⟨t, ht⟩ := one_add_pow_eq ((l : ℤ) ^ c) d
  have hl0 : (l : ℤ) ^ c ≠ 0 := pow_ne_zero _ (by exact_mod_cast hl.ne_zero)
  rw [ht, add_sub_cancel_left, pow_add, mul_dvd_mul_iff_left hl0]
  intro h
  have key : ∀ j, j ≤ c → j ≤ M → l ^ j ≤ d := by
    intro j hjc hjM
    have h1 : (l : ℤ) ^ j ∣ (d : ℤ) + (l : ℤ) ^ c * t := (pow_dvd_pow _ hjM).trans h
    have h2 : (l : ℤ) ^ j ∣ (d : ℤ) := (dvd_add_left ((pow_dvd_pow _ hjc).mul_right t)).1 h1
    exact Nat.le_of_dvd hd0 (by exact_mod_cast h2)
  rcases le_total c M with h1 | h1
  · have := key c le_rfl h1; omega
  · have := key M h1 le_rfl
    have := Nat.lt_pow_self (n := M) hl.one_lt
    omega

theorem cast_dvd_of_not_dvd (l ν w : ℕ) (hl : l.Prime) (f : ℤ) (hf : ¬ (l : ℤ) ^ w ∣ f) :
    (f : ZMod (l ^ ν)) ∣ (l : ZMod (l ^ ν)) ^ w := by
  induction w generalizing f with
  | zero => simp at hf
  | succ w ih =>
    by_cases h : (l : ℤ) ∣ f
    · obtain ⟨g, rfl⟩ := h
      have hg : ¬ (l : ℤ) ^ w ∣ g := fun h => hf (by rw [pow_succ']; exact mul_dvd_mul_left _ h)
      rw [pow_succ']
      push_cast
      exact mul_dvd_mul_left _ (ih g hg)
    · have hc : IsCoprime f ((l : ℤ) ^ ν) :=
        (((Nat.prime_iff_prime_int.1 hl).irreducible.coprime_iff_not_dvd.2 h).symm).pow_right
      obtain ⟨a, b, hab⟩ := hc
      have h0 : ((l : ZMod (l ^ ν))) ^ ν = 0 := by exact_mod_cast ZMod.natCast_self (l ^ ν)
      have h1 : (f : ZMod (l ^ ν)) * a = 1 := by
        have := congrArg (Int.cast : ℤ → ZMod (l ^ ν)) hab
        push_cast at this
        rw [h0] at this
        linear_combination this
      exact (Dvd.intro _ h1).trans (one_dvd _)

theorem not_dvd_sub (l c M i j : ℕ) (hl : l.Prime) (hc : 1 ≤ c) (hM : M < l ^ c) (hij : j < i) (hi : i < M) :
    ¬ (l : ℤ) ^ (c + M) ∣ (1 + (l : ℤ) ^ c) ^ i - (1 + (l : ℤ) ^ c) ^ j := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij.le
  intro h
  have h1 : (1 + (l : ℤ) ^ c) ^ (j + d) - (1 + (l : ℤ) ^ c) ^ j =
      (1 + (l : ℤ) ^ c) ^ j * ((1 + (l : ℤ) ^ c) ^ d - 1) := by ring
  rw [h1] at h
  have hco : IsCoprime (l : ℤ) (1 + (l : ℤ) ^ c) := by
    obtain ⟨c', rfl⟩ := Nat.exists_eq_add_of_le hc
    exact ⟨-(l : ℤ) ^ c', 1, by ring⟩
  exact not_dvd_pow_sub_one l c M d hl hM (by omega) (by omega) (hco.pow.dvd_of_dvd_mul_left h)

theorem pe_dvd (l c ν M E : ℕ) (hl : l.Prime) (hc : 1 ≤ c) (hM : M < l ^ c) (hE : E < M) :
    (pe (1 + l ^ c) M E : ZMod (l ^ ν)) ∣ (l : ZMod (l ^ ν)) ^ (M * (c + M)) := by
  have h1 : (pe (1 + l ^ c) M E : ZMod (l ^ ν)) ∣
      ∏ _j ∈ (Finset.range M).erase E, (l : ZMod (l ^ ν)) ^ (c + M) := by
    unfold pe
    rw [Int.cast_prod]
    refine Finset.prod_dvd_prod_of_dvd _ _ fun j hj => cast_dvd_of_not_dvd l ν _ hl _ ?_
    rw [Finset.mem_erase, Finset.mem_range] at hj
    push_cast
    rcases lt_or_gt_of_ne hj.1 with h | h
    · exact not_dvd_sub l c M E j hl hc hM h hE
    · rw [dvd_sub_comm]
      exact not_dvd_sub l c M j E hl hc hM h hj.2
  refine h1.trans ?_
  rw [Finset.prod_const, ← pow_mul, mul_comm]
  refine pow_dvd_pow _ (Nat.mul_le_mul_right _ ?_)
  exact (Finset.card_erase_le).trans (Finset.card_range M).le

theorem exists_index (G : Type) [CommGroup G] [Finite G] [IsCyclic G] (q : ℕ) (hq : q ∣ Nat.card G) :
    ∃ v : G →* Cq q, ∀ u, v u = 1 → ∃ s, u = s ^ q := by
  let e : Multiplicative (ZMod (Nat.card G)) ≃* G := zmodCyclicMulEquiv inferInstance
  haveI : NeZero (Nat.card G) := ⟨Nat.card_pos.ne'⟩
  refine ⟨(AddMonoidHom.toMultiplicative (ZMod.castHom hq (ZMod q)).toAddMonoidHom).comp e.symm.toMonoidHom, ?_⟩
  intro u hu
  obtain ⟨x, rfl⟩ := e.surjective u
  have h1 : ZMod.castHom hq (ZMod q) (Multiplicative.toAdd x) = 0 := by
    simpa using congrArg Multiplicative.toAdd hu
  obtain ⟨n, hn⟩ := ZMod.natCast_zmod_surjective (Multiplicative.toAdd x)
  rw [← hn, map_natCast, ZMod.natCast_eq_zero_iff] at h1
  obtain ⟨m, rfl⟩ := h1
  refine ⟨e (Multiplicative.ofAdd (m : ZMod _)), ?_⟩
  rw [← map_pow, ← ofAdd_nsmul, nsmul_eq_mul, ← Nat.cast_mul, hn, ofAdd_toAdd]

theorem prim_map {R k : Type} [CommRing R] [IsDomain R] [Field k] (r : R →+* k) (l ν : ℕ) (hl : l.Prime)
    (hν : 1 ≤ ν) (hr : r l ≠ 0) (ζ : Rˣ) (hζ : IsPrimitiveRoot ζ (l ^ ν)) :
    IsPrimitiveRoot (Units.map (r : R →* k) ζ) (l ^ ν) := by
  haveI : Fact l.Prime := ⟨hl⟩
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hν
  have h1 : Units.map (r : R →* k) ζ ^ l ^ (n + 1) = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
  have h2 : ¬ Units.map (r : R →* k) ζ ^ l ^ n = 1 := by
    intro h
    have h3 : IsPrimitiveRoot ((ζ : R) ^ l ^ n) l :=
      (IsPrimitiveRoot.coe_units_iff.2 hζ).pow (pow_pos hl.pos _) (pow_succ l n)
    have h4 := congrArg r (h3.geom_sum_eq_zero hl.one_lt)
    have h5 : r ((ζ : R) ^ l ^ n) = 1 := by simpa using congrArg Units.val h
    rw [map_sum] at h4
    simp only [map_pow r ((ζ : R) ^ l ^ n), h5] at h4
    apply hr
    simpa using h4
  rw [← orderOf_eq_prime_pow h2 h1]
  exact IsPrimitiveRoot.orderOf _

section Res

variable {F : Type} [Field F] {k : Type} [Field k] {r : 𝓞 F →+* k}

theorem res_one : Res r 1 1 := ⟨1, 1, by simp, by simp, by simp⟩

theorem res_mul {α β : Fˣ} {u w : kˣ} (h : Res r α u) (h' : Res r β w) : Res r (α * β) (u * w) := by
  obtain ⟨a, b, hb, h1, h2⟩ := h
  obtain ⟨a', b', hb', h1', h2'⟩ := h'
  refine ⟨a * a', b * b', by rw [map_mul]; exact mul_ne_zero hb hb', ?_, ?_⟩
  · have e1 : ((b * b' : 𝓞 F) : F) = (b : F) * (b' : F) := rfl
    have e2 : ((a * a' : 𝓞 F) : F) = (a : F) * (a' : F) := rfl
    rw [e1, e2, ← h1, ← h1', Units.val_mul]; ring
  · rw [map_mul, map_mul, h2, h2', Units.val_mul]; ring

theorem res_inv {α : Fˣ} {u : kˣ} (h : Res r α u) : Res r α⁻¹ u⁻¹ := by
  obtain ⟨a, b, hb, h1, h2⟩ := h
  refine ⟨b, a, by rw [h2]; exact mul_ne_zero u.ne_zero hb, ?_, ?_⟩
  · rw [← h1, Units.inv_mul_cancel_left]
  · rw [h2, Units.inv_mul_cancel_left]

theorem res_pow {α : Fˣ} {u : kˣ} (h : Res r α u) (n : ℕ) : Res r (α ^ n) (u ^ n) := by
  induction n with
  | zero => simpa using res_one
  | succ n ih => rw [pow_succ, pow_succ]; exact res_mul ih h

end Res

theorem isPrimFam_pi {R A I : Type} [CommRing R] [CommRing A] {m : ℕ}
    (Φ : I → ∀ n : ℕ, Ch A (GL (Fin n) R) (m + 1) →ₗ[A] A) (h : ∀ i, IsPrimFam (Φ i)) :
    IsPrimFam fun n => LinearMap.pi fun i => Φ i n :=
  ⟨fun n z hz => funext fun i => (h i).bdry n z hz, fun n n' hn z hz => funext fun i => (h i).stab n n' hn z hz,
    fun d n z hz => funext fun i => (h i).psi d n z hz⟩

theorem sFewOf : SFewOf := by
  classical
  intro hT hP hC hU hD L F _ _ _ _ _ hL l c ν e hl ζ γ hlay hc hr S hS hinj
  choose 𝔡 h𝔡 using hS
  choose N y b hy hb hval using fun α : S => hC L F l c ν e ζ γ hlay hc α (𝔡 α α.2) (h𝔡 α α.2)
  have hl0 : (l : 𝓞 F) ≠ 0 := by exact_mod_cast hl.out.ne_zero
  have hb0 : (l : 𝓞 F) * ∏ α, b α ≠ 0 := mul_ne_zero hl0 (Finset.prod_ne_zero_iff.2 fun α _ => hb α)
  let I : Type := {P : HeightOneSpectrum (𝓞 F) // (l : 𝓞 F) * ∏ α, b α ∉ P.asIdeal ∧
    Function.Surjective ((Ideal.Quotient.mk P.asIdeal).comp (algebraMap (𝓞 L) (𝓞 F)))}
  have main : ∀ P : I, ∃ Φ : ∀ n : ℕ, Ch (ZMod (l ^ ν)) (GL (Fin n) (𝓞 L)) (2 * e + 2 + 1) →ₗ[ZMod (l ^ ν)]
      ZMod (l ^ ν), IsPrimFam Φ ∧ ∀ α α' : S, l ^ (2 * e + 2) • Φ _ (y α) = l ^ (2 * e + 2) • Φ _ (y α') →
        letI := P.1.isMaximal
        letI := Ideal.Quotient.field P.1.asIdeal
        ∃ s : (𝓞 F ⧸ P.1.asIdeal)ˣ, Res (Ideal.Quotient.mk P.1.asIdeal)
          (nrm γ ((1 + l ^ c) ^ (e + 1)) α ^ l ^ (2 * e + 2 + (2 * e + 3) * (c + (2 * e + 3))) *
            (nrm γ ((1 + l ^ c) ^ (e + 1)) α' ^ l ^ (2 * e + 2 + (2 * e + 3) * (c + (2 * e + 3))))⁻¹) (s ^ l ^ ν) := by
    rintro ⟨P, hPb, hPs⟩
    letI := P.isMaximal
    letI := Ideal.Quotient.field P.asIdeal
    haveI : Finite (𝓞 F ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
    have hlP : Ideal.Quotient.mk P.asIdeal (l : 𝓞 F) ≠ 0 := fun h =>
      hPb (Ideal.mul_mem_right _ _ (Ideal.Quotient.eq_zero_iff_mem.1 h))
    have hbP : ∀ α, Ideal.Quotient.mk P.asIdeal (b α) ≠ 0 := fun α h =>
      hPb (Ideal.mem_of_dvd _ ((Finset.dvd_prod_of_mem b (Finset.mem_univ α)).mul_left _)
        (Ideal.Quotient.eq_zero_iff_mem.1 h))
    have hz := prim_map (Ideal.Quotient.mk P.asIdeal) l ν hl.out (hlay.c_pos.trans hlay.c_le) hlP ζ hlay.prim
    obtain ⟨v, hv⟩ := exists_index (𝓞 F ⧸ P.asIdeal)ˣ (l ^ ν) (by rw [hz.eq_orderOf]; exact orderOf_dvd_natCard _)
    obtain ⟨θ, hθ, hθv⟩ := hT _ (l ^ ν) e _ hz v
    refine ⟨_, hP _ _ _ θ hθ (𝓞 L) ((Ideal.Quotient.mk P.asIdeal).comp (algebraMap (𝓞 L) (𝓞 F))), ?_⟩
    intro α α' hαα
    obtain ⟨u, hu, hu1⟩ := hval α _ _ hPs (hbP α) _ v θ hθ hθv
    obtain ⟨u', hu', hu1'⟩ := hval α' _ _ hPs (hbP α') _ v θ hθ hθv
    simp only [LinearMap.comp_apply] at hαα
    rw [hu1, hu1'] at hαα
    obtain ⟨x, hx⟩ := pe_dvd l c ν (2 * e + 3) (e + 1) hl.out hlay.c_pos hc (by omega)
    obtain ⟨s, hs⟩ := hv (u ^ l ^ (2 * e + 2 + (2 * e + 3) * (c + (2 * e + 3))) *
        (u' ^ l ^ (2 * e + 2 + (2 * e + 3) * (c + (2 * e + 3))))⁻¹) (by
      rw [map_mul, map_inv, map_pow, map_pow, mul_inv_eq_one]
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_pow]
      simp only [nsmul_eq_mul, Nat.cast_pow] at hαα ⊢
      rw [pow_add, hx]
      linear_combination x * hαα)
    exact ⟨s, hs ▸ res_mul (res_pow hu _) (res_inv (res_pow hu' _))⟩
  choose Φ hΦ hsep using main
  let f : S → (I → ZMod (l ^ ν)) := fun α => l ^ (2 * e + 2) • (LinearMap.pi fun i => Φ i (N α)) (y α)
  have hf : Function.Injective f := by
    intro α α' h
    obtain ⟨δ, hδ⟩ := hD L F l ν hl.out ζ hlay.prim _ _ hb0 fun P _ hPb hPs =>
      hsep ⟨P, hPb, hPs⟩ α α' (congrFun h ⟨P, hPb, hPs⟩)
    exact Subtype.ext (hinj _ α.2 _ α'.2 ⟨δ, (mul_inv_eq_iff_eq_mul.1 hδ).trans (mul_comm _ _)⟩)
  have hcard := hU L hL (2 * e + 2) ⟨e + 1, by ring⟩ hr l ν (I → ZMod (l ^ ν)) _ (isPrimFam_pi Φ hΦ)
    (Finset.univ.image f) (by
      intro s hs
      obtain ⟨α, -, rfl⟩ := Finset.mem_image.1 hs
      exact ⟨N α, y α, hy α, rfl⟩)
  rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_coe,
    show 2 * (2 * e + 2 + 1) + 4 = 4 * e + 10 by ring] at hcard
  exact hcard

end LateralTheory.Q.SFewOfCut

end
