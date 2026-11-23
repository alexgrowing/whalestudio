import Formalism.LocalToGlobal.Columns.CardFilterNeighboursEqPaths

noncomputable section

namespace Formalism.L2.Col

open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Module

section Count

variable {E : Type} [Field E] [NumberField E] [StarRing E] (Q : HeightOneSpectrum (𝓞 E))

theorem one_lt_card_residue : 1 < Nat.card (𝓞 E ⧸ Q.asIdeal) := by
  have h1 : Ideal.absNorm Q.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact Q.isPrime.ne_top
  have h0 : Ideal.absNorm Q.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact Q.ne_bot
  have hc : Nat.card (𝓞 E ⧸ Q.asIdeal) = Ideal.absNorm Q.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  omega

theorem card_eq_card_quotient_pow_of_ideal_smul_eq_zero {M : Type} [AddCommGroup M] [Module (𝓞 E) M] [Finite M]
    (hM : ∀ p ∈ Q.asIdeal, ∀ x : M, p • x = 0) : ∃ m, Nat.card M = Nat.card (𝓞 E ⧸ Q.asIdeal) ^ m := by
  haveI : Q.asIdeal.IsMaximal := Q.isMaximal
  letI : Field (𝓞 E ⧸ Q.asIdeal) := Ideal.Quotient.field Q.asIdeal
  have htor : Module.IsTorsionBySet (𝓞 E) M (Q.asIdeal : Set (𝓞 E)) := by
    intro x a
    exact hM a.1 a.2 x
  letI : Module (𝓞 E ⧸ Q.asIdeal) M := htor.module
  haveI : Module.Finite (𝓞 E ⧸ Q.asIdeal) M := Module.Finite.of_finite
  refine ⟨Module.finrank (𝓞 E ⧸ Q.asIdeal) M, ?_⟩
  rw [Nat.card_congr (Module.finBasis (𝓞 E ⧸ Q.asIdeal) M).equivFun.toEquiv, Nat.card_fun,
    Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin]

theorem card_submodules_complement {U : Type} [AddCommGroup U] [Module (𝓞 E) U] [Finite U]
    (hU : ∀ p ∈ Q.asIdeal, ∀ x : U, p • x = 0) {a b : ℕ}
    (hab : Nat.card U = Nat.card (𝓞 E ⧸ Q.asIdeal) ^ (a + b)) :
    Nat.card {W : Submodule (𝓞 E) U // Nat.card W = Nat.card (𝓞 E ⧸ Q.asIdeal) ^ a} =
      Nat.card {W : Submodule (𝓞 E) U // Nat.card W = Nat.card (𝓞 E ⧸ Q.asIdeal) ^ b} := by
  have := Q.isMaximal
  let _ : Field (𝓞 E ⧸ Q.asIdeal) := Ideal.Quotient.field Q.asIdeal
  have : Finite (𝓞 E ⧸ Q.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ Q.ne_bot
  have hq : 1 < Nat.card (𝓞 E ⧸ Q.asIdeal) := Finite.one_lt_card
  have ht : Module.IsTorsionBySet (𝓞 E) U (Q.asIdeal : Set (𝓞 E)) := fun x p => hU p.1 p.2 x
  let _ : Module (𝓞 E ⧸ Q.asIdeal) U := ht.module
  have : IsScalarTower (𝓞 E) (𝓞 E ⧸ Q.asIdeal) U := ht.isScalarTower
  have : FiniteDimensional (𝓞 E ⧸ Q.asIdeal) U := Module.Finite.of_finite
  let _ : Fintype (𝓞 E ⧸ Q.asIdeal) := Fintype.ofFinite _
  let eS : Submodule (𝓞 E ⧸ Q.asIdeal) U ≃ Submodule (𝓞 E) U :=
    { toFun := fun W => W.restrictScalars (𝓞 E)
      invFun := fun W => wmpToK Q W
      left_inv := fun W => Submodule.ext fun x => Iff.rfl
      right_inv := fun W => Submodule.ext fun x => Iff.rfl }
  have hcardW : ∀ W : Submodule (𝓞 E ⧸ Q.asIdeal) U,
      Nat.card W = Nat.card (𝓞 E ⧸ Q.asIdeal) ^ finrank (𝓞 E ⧸ Q.asIdeal) W := by
    intro W
    let _ : Fintype W := Fintype.ofFinite W
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Module.card_eq_pow_finrank
  have hfin : finrank (𝓞 E ⧸ Q.asIdeal) U = a + b := by
    have h1 : Nat.card U = Nat.card (𝓞 E ⧸ Q.asIdeal) ^ finrank (𝓞 E ⧸ Q.asIdeal) U := by
      let _ : Fintype U := Fintype.ofFinite U
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
      exact Module.card_eq_pow_finrank
    rw [h1] at hab
    exact Nat.pow_right_injective hq hab
  have hc : ∀ m, Nat.card {W : Submodule (𝓞 E) U // Nat.card W = Nat.card (𝓞 E ⧸ Q.asIdeal) ^ m} =
      Nat.card {W : Submodule (𝓞 E ⧸ Q.asIdeal) U // finrank (𝓞 E ⧸ Q.asIdeal) W = m} := by
    intro m
    refine Nat.card_congr (eS.symm.subtypeEquiv fun W => ?_)
    change Nat.card W = _ ↔ finrank (𝓞 E ⧸ Q.asIdeal) (wmpToK Q W) = m
    rw [← card_wmpToK (P := Q) W, hcardW]
    exact ⟨fun h => Nat.pow_right_injective hq h, fun h => by rw [h]⟩
  rw [hc a, hc b, card_subspaces_finrank, ← card_subspaces_cofinrank]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun W => ?_)
  have := Submodule.finrank_quotient_add_finrank W
  rw [hfin] at this
  omega

theorem card_comap_mkQ {M : Type} [AddCommGroup M] [Module (𝓞 E) M] (p : Submodule (𝓞 E) M)
    (W : Submodule (𝓞 E) (M ⧸ p)) : Nat.card (W.comap p.mkQ) = Nat.card p * Nat.card W := by
  set K := W.comap p.mkQ with hK
  have hpK : p ≤ K := by
    intro x hx
    rw [hK, Submodule.mem_comap, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero p).mpr hx]
    exact W.zero_mem
  let f : K →ₗ[𝓞 E] W := p.mkQ.restrict (p := K) (q := W) (by intro x hx; exact hx)
  have hf : Function.Surjective f := by
    rintro ⟨w, hw⟩
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective p w
    exact ⟨⟨m, hw⟩, rfl⟩
  have hker : LinearMap.ker f = p.comap K.subtype := by
    ext ⟨x, hx⟩
    rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply,
      ← Submodule.Quotient.mk_eq_zero p (x := x)]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.ker f),
    Nat.card_congr (f.quotKerEquivOfSurjective hf).toEquiv, hker,
    Nat.card_congr (Submodule.comapSubtypeEquivOfLe hpK).toEquiv]

def submoduleChainSet (X : Type) [AddCommGroup X] [Module (𝓞 E) X] (i j : ℕ) : Set (Submodule (𝓞 E) X) :=
  {Y | Q.asIdeal • (⊤ : Submodule (𝓞 E) X) ≤ Y ∧ Q.asIdeal • Y = ⊥ ∧
    Nat.card (X ⧸ Y) = Nat.card (𝓞 E ⧸ Q.asIdeal) ^ i ∧ Nat.card Y = Nat.card (𝓞 E ⧸ Q.asIdeal) ^ j}

theorem card_submodulePairs_symm_of {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Finite X] {i j : ℕ}
    (hY : (submoduleChainSet Q X i j).Nonempty) : Nat.card (submoduleChainSet Q X i j) = Nat.card (submoduleChainSet Q X j i) := by
  classical
  obtain ⟨Y₀, h1, h2, h3, h4⟩ := hY
  have hq := one_lt_card_residue Q
  have hq0 : 0 < Nat.card (𝓞 E ⧸ Q.asIdeal) := by omega
  have hX : Nat.card X = Nat.card (𝓞 E ⧸ Q.asIdeal) ^ (i + j) := by
    rw [Submodule.card_eq_card_quotient_mul_card Y₀, h4, h3, pow_add, mul_comm]

  have hsq : ∀ p ∈ Q.asIdeal, ∀ p' ∈ Q.asIdeal, ∀ x : X, p • p' • x = 0 := by
    intro p hp p' hp' x
    have hx : p' • x ∈ Y₀ := h1 (Submodule.smul_mem_smul hp' Submodule.mem_top)
    have h5 : p • (p' • x) ∈ Q.asIdeal • Y₀ := Submodule.smul_mem_smul hp hx
    rw [h2] at h5
    exact (Submodule.mem_bot _).1 h5
  obtain ⟨a, ha, c, hcQ, hc⟩ := wmp_exists_unif Q
  obtain ⟨s, r, hr, hsr⟩ := Q.isMaximal.exists_inv hcQ
  have key : ∀ p ∈ Q.asIdeal, ∃ t : 𝓞 E, ∀ x : X, p • x = (s * t) • (a • x) := by
    intro p hp
    obtain ⟨t, ht⟩ := hc p hp
    refine ⟨t, fun x => ?_⟩
    calc p • x = ((s * c + r) * p) • x := by rw [hsr, one_mul]
      _ = (s * (c * p)) • x + r • p • x := by rw [add_mul, add_smul, mul_assoc, mul_smul r p x]
      _ = (s * t) • (a • x) := by
        rw [hsq r hr p hp x, add_zero, ht, ← mul_smul]
        congr 1
        ring
  let φ : X →ₗ[𝓞 E] X := a • LinearMap.id
  have hφ : ∀ x, φ x = a • x := fun x => rfl
  set K := LinearMap.ker φ with hK
  set R := Q.asIdeal • (⊤ : Submodule (𝓞 E) X) with hR
  have hRrange : R = LinearMap.range φ := by
    refine le_antisymm (Submodule.smul_le.2 fun p hp x _ => ?_) ?_
    · obtain ⟨t, ht⟩ := key p hp
      exact ⟨(s * t) • x, by rw [hφ, ht, smul_comm]⟩
    · rintro _ ⟨x, rfl⟩
      exact Submodule.smul_mem_smul ha Submodule.mem_top
  have hkill : ∀ Y : Submodule (𝓞 E) X, Q.asIdeal • Y = ⊥ ↔ Y ≤ K := by
    intro Y
    constructor
    · intro h y hy
      have h5 : a • y ∈ Q.asIdeal • Y := Submodule.smul_mem_smul ha hy
      rw [h] at h5
      exact LinearMap.mem_ker.2 ((Submodule.mem_bot _).1 h5)
    · intro h
      rw [eq_bot_iff, Submodule.smul_le]
      intro p hp y hy
      obtain ⟨t, ht⟩ := key p hp
      have h0 : a • y = 0 := LinearMap.mem_ker.1 (h hy)
      rw [ht, h0, smul_zero]
      exact Submodule.zero_mem _
  have hRK : R ≤ K := by
    intro y hy
    rw [hRrange] at hy
    obtain ⟨x, rfl⟩ := hy
    exact LinearMap.mem_ker.2 (hsq a ha a ha x)
  have hXKR : Nat.card X = Nat.card K * Nat.card R := by
    rw [Submodule.card_eq_card_quotient_mul_card K, Nat.card_congr φ.quotKerEquivRange.toEquiv, ← hRrange]
  set R' := R.comap K.subtype with hR'
  have hR'card : Nat.card R' = Nat.card R := Nat.card_congr (Submodule.comapSubtypeEquivOfLe hRK).toEquiv
  have : Finite (K ⧸ R') := Finite.of_surjective _ (Submodule.mkQ_surjective R')
  have hUkill : ∀ p ∈ Q.asIdeal, ∀ u : K ⧸ R', p • u = 0 := by
    intro p hp u
    induction u using Submodule.Quotient.induction_on with
    | _ y =>
      rw [← Submodule.Quotient.mk_smul]
      have h5 : p • (y : X) ∈ Q.asIdeal • K := Submodule.smul_mem_smul hp y.2
      rw [(hkill K).2 le_rfl] at h5
      have h6 : p • y = 0 := Subtype.ext ((Submodule.mem_bot _).1 h5)
      rw [h6, Submodule.Quotient.mk_zero]
  have hRkill : ∀ p ∈ Q.asIdeal, ∀ x : R, p • x = 0 := by
    intro p hp x
    have h5 : p • (x : X) ∈ Q.asIdeal • R := Submodule.smul_mem_smul hp x.2
    rw [(hkill R).2 hRK] at h5
    exact Subtype.ext ((Submodule.mem_bot _).1 h5)
  obtain ⟨γ, hγ⟩ := card_eq_card_quotient_pow_of_ideal_smul_eq_zero Q hRkill
  obtain ⟨u, hu⟩ := card_eq_card_quotient_pow_of_ideal_smul_eq_zero Q hUkill
  have hKcard : Nat.card K = Nat.card R * Nat.card (K ⧸ R') := by
    rw [Submodule.card_eq_card_quotient_mul_card R', hR'card]
  have hsum : i + j = 2 * γ + u := by
    have e : Nat.card (𝓞 E ⧸ Q.asIdeal) ^ (i + j) = Nat.card (𝓞 E ⧸ Q.asIdeal) ^ (2 * γ + u) := by
      rw [← hX, hXKR, hKcard, hγ, hu, ← pow_add, ← pow_add]
      congr 1
      ring
    exact Nat.pow_right_injective hq e

  let F : Submodule (𝓞 E) (K ⧸ R') → Submodule (𝓞 E) X := fun W => (W.comap R'.mkQ).map K.subtype
  let G : Submodule (𝓞 E) X → Submodule (𝓞 E) (K ⧸ R') := fun Y => (Y.comap K.subtype).map R'.mkQ
  have hFcard : ∀ W, Nat.card (F W) = Nat.card R * Nat.card W := by
    intro W
    rw [Nat.card_congr (Submodule.equivMapOfInjective K.subtype K.injective_subtype (W.comap R'.mkQ)).symm.toEquiv,
      card_comap_mkQ, hR'card]
  have hFR : ∀ W, R ≤ F W := by
    intro W x hx
    refine ⟨⟨x, hRK hx⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero R').2 hx]
    exact W.zero_mem
  have hFK : ∀ W, F W ≤ K := fun W => Submodule.map_subtype_le _ _
  have hGF : ∀ W, G (F W) = W := by
    intro W
    change Submodule.map R'.mkQ (Submodule.comap K.subtype (Submodule.map K.subtype (W.comap R'.mkQ))) = W
    rw [Submodule.comap_map_eq_of_injective K.injective_subtype,
      Submodule.map_comap_eq_of_surjective (Submodule.mkQ_surjective R')]
  have hFG : ∀ Y, R ≤ Y → Y ≤ K → F (G Y) = Y := by
    intro Y hRY hYK
    change Submodule.map K.subtype (Submodule.comap R'.mkQ (Submodule.map R'.mkQ (Y.comap K.subtype))) = Y
    rw [Submodule.comap_map_mkQ, sup_eq_right.2 (Submodule.comap_mono hRY), Submodule.map_comap_subtype,
      inf_eq_right.2 hYK]

  have hcount : ∀ i' j', i' + j' = i + j → Nat.card (submoduleChainSet Q X i' j') =
      Nat.card {W : Submodule (𝓞 E) (K ⧸ R') //
        Nat.card R * Nat.card W = Nat.card (𝓞 E ⧸ Q.asIdeal) ^ j'} := by
    intro i' j' hij
    refine Nat.card_congr
      { toFun := fun Y => ⟨G Y.1, ?_⟩
        invFun := fun W => ⟨F W.1, ?_⟩
        left_inv := fun Y => Subtype.ext (hFG Y.1 Y.2.1 ((hkill Y.1).1 Y.2.2.1))
        right_inv := fun W => Subtype.ext (hGF W.1) }
    · rw [← hFcard, hFG Y.1 Y.2.1 ((hkill Y.1).1 Y.2.2.1)]
      exact Y.2.2.2.2
    · refine ⟨hFR W.1, (hkill _).2 (hFK W.1), ?_, by rw [hFcard]; exact W.2⟩
      have e := Submodule.card_eq_card_quotient_mul_card (F W.1)
      rw [hX, ← hij, hFcard, W.2, pow_add, mul_comm] at e
      exact Nat.eq_of_mul_eq_mul_left (pow_pos hq0 _) e.symm

  have hW₀ := hFcard (G Y₀)
  rw [hFG Y₀ h1 ((hkill Y₀).1 h2), h4, hγ] at hW₀
  have hγj : γ ≤ j := by
    by_contra hlt
    have : Nat.card (𝓞 E ⧸ Q.asIdeal) ^ j < Nat.card (𝓞 E ⧸ Q.asIdeal) ^ γ :=
      Nat.pow_lt_pow_right hq (by omega)
    have hpos : 0 < Nat.card (G Y₀) := Nat.card_pos
    nlinarith
  have hWle : Nat.card (G Y₀) ≤ Nat.card (K ⧸ R') := Nat.card_le_card_of_injective _ Subtype.val_injective
  have hγi : γ ≤ i := by
    have e1 : Nat.card (𝓞 E ⧸ Q.asIdeal) ^ j = Nat.card (𝓞 E ⧸ Q.asIdeal) ^ γ * Nat.card (𝓞 E ⧸ Q.asIdeal) ^ (j - γ) := by
      rw [← pow_add, Nat.add_sub_cancel' hγj]
    rw [e1] at hW₀
    have e2 := Nat.eq_of_mul_eq_mul_left (pow_pos hq0 γ) hW₀
    rw [← e2, hu] at hWle
    have := (Nat.pow_le_pow_iff_right hq).1 hWle
    omega
  rw [hcount i j rfl, hcount j i (add_comm j i), hγ]
  have conv : ∀ m, γ ≤ m → Nat.card {W : Submodule (𝓞 E) (K ⧸ R') //
      Nat.card (𝓞 E ⧸ Q.asIdeal) ^ γ * Nat.card W = Nat.card (𝓞 E ⧸ Q.asIdeal) ^ m} =
      Nat.card {W : Submodule (𝓞 E) (K ⧸ R') // Nat.card W = Nat.card (𝓞 E ⧸ Q.asIdeal) ^ (m - γ)} := by
    intro m hm
    refine Nat.card_congr (Equiv.subtypeEquivRight fun W => ?_)
    rw [show Nat.card (𝓞 E ⧸ Q.asIdeal) ^ m = Nat.card (𝓞 E ⧸ Q.asIdeal) ^ γ * Nat.card (𝓞 E ⧸ Q.asIdeal) ^ (m - γ) by
      rw [← pow_add, Nat.add_sub_cancel' hm]]
    exact ⟨fun h => Nat.eq_of_mul_eq_mul_left (pow_pos hq0 γ) h, fun h => by rw [h]⟩
  rw [conv j hγj, conv i hγi]
  exact card_submodules_complement Q hUkill (by rw [hu]; congr 1; omega)

theorem card_submodulePairs_symm (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Finite X] (i j : ℕ) :
    Nat.card (submoduleChainSet Q X i j) = Nat.card (submoduleChainSet Q X j i) := by
  by_cases h1 : (submoduleChainSet Q X i j).Nonempty
  · exact card_submodulePairs_symm_of Q h1
  by_cases h2 : (submoduleChainSet Q X j i).Nonempty
  · exact (card_submodulePairs_symm_of Q h2).symm
  rw [Set.not_nonempty_iff_eq_empty] at h1 h2
  rw [h1, h2]

end Count

section Paths

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem inf_toAddSubgroup {R V : Type} [Ring R] [AddCommGroup V] [Module R V] (p q : Submodule R V) :
    (p ⊓ q).toAddSubgroup = p.toAddSubgroup ⊓ q.toAddSubgroup := rfl

open Classical in

theorem pathCount_eq_card_middle (P Q : HeightOneSpectrum (𝓞 E)) (i j : ℕ) (d f : DecoSet E n ST SG) :
    decorationPathCount P.asIdeal Q.asIdeal i j d f =
      Nat.card {e : DecoSet E n ST SG // e ∈ d.heckeSet P.asIdeal i ∧ f ∈ e.heckeSet Q.asIdeal j} := by
  have hP : P.asIdeal ≠ ⊥ := P.ne_bot
  have hP' := conjIdeal_ne_bot hP
  have hQ : Q.asIdeal ≠ ⊥ := Q.ne_bot
  have hQ' := conjIdeal_ne_bot hQ
  unfold decorationPathCount
  rw [← Nat.card_eq_finsetCard]
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro e
  simp only [Finset.mem_filter, DecoSet.mem_heckeNb hP hP', DecoSet.mem_heckeNb hQ hQ']

theorem split_inf_le {P : HeightOneSpectrum (𝓞 E)} (hne : conjPrime₂ P ≠ P) {N M e : Submodule (𝓞 E) (Sp E n)}
    (h1 : P.asIdeal • M ≤ e) (h2 : (conjPrime₂ P).asIdeal • N ≤ e) : M ⊓ N ≤ e := by
  have hne' : P.asIdeal ≠ (conjPrime₂ P).asIdeal := fun h => hne (HeightOneSpectrum.ext h.symm)
  have htop := Ideal.IsMaximal.coprime_of_ne P.isMaximal (conjPrime₂ P).isMaximal hne'
  have h1mem : (1 : 𝓞 E) ∈ P.asIdeal ⊔ (conjPrime₂ P).asIdeal := by rw [htop]; trivial
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp h1mem
  intro x hx
  have hx' : x = a • x + b • x := by rw [← add_smul, hab, one_smul]
  rw [hx']
  exact e.add_mem (h1 (Submodule.smul_mem_smul ha hx.1)) (h2 (Submodule.smul_mem_smul hb hx.2))

theorem split_sup_inf_eq {P : HeightOneSpectrum (𝓞 E)} (hne : conjPrime₂ P ≠ P) {N M e : Submodule (𝓞 E) (Sp E n)}
    (h1 : P.asIdeal • e ≤ N) (h2 : (conjPrime₂ P).asIdeal • e ≤ M) : (e ⊓ N) ⊔ (M ⊓ e) = e := by
  have hne' : P.asIdeal ≠ (conjPrime₂ P).asIdeal := fun h => hne (HeightOneSpectrum.ext h.symm)
  have htop := Ideal.IsMaximal.coprime_of_ne P.isMaximal (conjPrime₂ P).isMaximal hne'
  have h1mem : (1 : 𝓞 E) ∈ P.asIdeal ⊔ (conjPrime₂ P).asIdeal := by rw [htop]; trivial
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp h1mem
  refine le_antisymm (sup_le inf_le_left inf_le_right) ?_
  intro x hx
  have hx' : x = a • x + b • x := by rw [← add_smul, hab, one_smul]
  rw [hx']
  exact Submodule.add_mem_sup ⟨e.smul_mem a hx, h1 (Submodule.smul_mem_smul ha hx)⟩
    ⟨h2 (Submodule.smul_mem_smul hb hx), e.smul_mem b hx⟩

theorem relIndex_of_sup_eq {G : Type} [AddCommGroup G] {M e N : AddSubgroup G} (h : (e ⊓ N) ⊔ (M ⊓ e) = e) :
    M.relIndex e = (M ⊓ N).relIndex (e ⊓ N) := by
  have key : (M ⊓ e).relIndex ((e ⊓ N) ⊔ (M ⊓ e)) = (M ⊓ e).relIndex (e ⊓ N) :=
    AddSubgroup.relIndex_sup_right (e ⊓ N) (M ⊓ e)
  rw [h] at key
  rw [← AddSubgroup.inf_relIndex_right M e, key, ← AddSubgroup.inf_relIndex_right (M ⊓ e) (e ⊓ N),
    ← AddSubgroup.inf_relIndex_right (M ⊓ N) (e ⊓ N)]
  congr 1
  ext x
  simp only [AddSubgroup.mem_inf]
  tauto

theorem card_quotient_relIndex {C B N : Submodule (𝓞 E) (Sp E n)} (hCB : C ≤ B) :
    Nat.card ((N ⧸ C.comap N.subtype) ⧸ (B.comap N.subtype).map (C.comap N.subtype).mkQ) =
      B.toAddSubgroup.relIndex N.toAddSubgroup ∧
    Nat.card ((B.comap N.subtype).map (C.comap N.subtype).mkQ) * B.toAddSubgroup.relIndex N.toAddSubgroup =
      C.toAddSubgroup.relIndex N.toAddSubgroup := by
  have hC'B' : C.comap N.subtype ≤ B.comap N.subtype := Submodule.comap_mono hCB
  have hidx : ∀ A : Submodule (𝓞 E) (Sp E n),
      Nat.card (N ⧸ A.comap N.subtype) = A.toAddSubgroup.relIndex N.toAddSubgroup := by
    intro A
    rw [← Submodule.cardQuot_apply]
    rfl
  have h1 : Nat.card ((N ⧸ C.comap N.subtype) ⧸ (B.comap N.subtype).map (C.comap N.subtype).mkQ) =
      B.toAddSubgroup.relIndex N.toAddSubgroup := by
    rw [Nat.card_congr (Submodule.quotientQuotientEquivQuotient _ _ hC'B').toEquiv, hidx]
  refine ⟨h1, ?_⟩
  rw [← h1, ← hidx C,
    Submodule.card_eq_card_quotient_mul_card ((B.comap N.subtype).map (C.comap N.subtype).mkQ)]

theorem card_of_equiv_fin {A : Type} [AddCommGroup A] [Module (𝓞 E) A] {Q : Ideal (𝓞 E)} {i : ℕ}
    (h : Nonempty (A ≃ₗ[𝓞 E] (Fin i → 𝓞 E ⧸ Q))) : Nat.card A = Nat.card (𝓞 E ⧸ Q) ^ i := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin i), Fintype.card_fin]

theorem ideal_sq_smul_le {P : HeightOneSpectrum (𝓞 E)} {N M B : Submodule (𝓞 E) (Sp E n)}
    (hPM : ∀ p ∈ P.asIdeal, ∀ p' ∈ P.asIdeal, ∀ x ∈ M, p • p' • x ∈ N) (hB : M ⊓ N ≤ B) :
    (P.asIdeal * P.asIdeal) • M ≤ B := by
  have hMN : (P.asIdeal * P.asIdeal) • M ≤ M ⊓ N := by
    refine le_inf Submodule.smul_le_right ?_
    rw [Submodule.mul_smul, Submodule.smul_le]
    intro a ha y hy
    refine Submodule.smul_induction_on (p := fun y => a • y ∈ N) hy ?_ ?_
    · intro r hr x hx
      exact hPM a ha r hr x hx
    · intro x y hx hy
      simp only [smul_add]
      exact N.add_mem hx hy
  exact le_trans hMN hB

theorem card_paths_eq_submodulePairs (P : HeightOneSpectrum (𝓞 E)) (hne : conjPrime₂ P ≠ P)
    (hST : ∀ R : ST, R.1 ≠ P ∧ R.1 ≠ conjPrime₂ P) (hSG : ∀ w : SG, w.1 ≠ P ∧ w.1 ≠ conjPrime₂ P)
    (d f : DecoSet E n ST SG) (hf : f.1.f = d.1.f) (hb : f.1.be = d.1.be)
    (hPM : ∀ p ∈ P.asIdeal, ∀ p' ∈ P.asIdeal, ∀ x ∈ f.1.N, p • p' • x ∈ d.1.N) (i j : ℕ) :
    Nat.card {e : DecoSet E n ST SG // e ∈ d.heckeSet P.asIdeal i ∧ f ∈ e.heckeSet P.asIdeal j} =
      Nat.card (submoduleChainSet (conjPrime₂ P) (d.1.N ⧸ (f.1.N ⊓ d.1.N).comap d.1.N.subtype) i j) := by
  classical
  set N := d.1.N with hNdef
  set M := f.1.N with hMdef
  set C' := (M ⊓ N).comap N.subtype with hC'
  have hq0 : 0 < Nat.card (𝓞 E ⧸ (conjPrime₂ P).asIdeal) := by have := one_lt_card_residue (conjPrime₂ P); omega

  have hmem : ∀ e : {e : DecoSet E n ST SG // e ∈ d.heckeSet P.asIdeal i ∧ f ∈ e.heckeSet P.asIdeal j},
      ((e.1.1.N ⊓ N).comap N.subtype).map C'.mkQ ∈ submoduleChainSet (conjPrime₂ P) (N ⧸ C') i j := by
    rintro ⟨e, ⟨hn1, -, -⟩, ⟨hn2, -, -⟩⟩
    obtain ⟨i11, i12, ⟨i13⟩⟩ := (isHeckeNbr_iff P i _ _).1 hn1
    obtain ⟨i21, i22, ⟨i23⟩⟩ := (isHeckeNbr_iff P j _ _).1 hn2
    have hCB : M ⊓ N ≤ e.1.N ⊓ N := le_inf (split_inf_le hne i21 i12) inf_le_right
    obtain ⟨c1, c2⟩ := card_quotient_relIndex (N := N) hCB
    have hBN : (e.1.N ⊓ N).toAddSubgroup.relIndex N.toAddSubgroup = Nat.card (𝓞 E ⧸ (conjPrime₂ P).asIdeal) ^ i := by
      rw [← wmp_card_quot]
      exact card_of_equiv_fin ⟨i13⟩
    refine ⟨?_, ?_, by rw [c1, hBN], ?_⟩
    · rw [Submodule.smul_le]
      intro p hp y _
      induction y using Submodule.Quotient.induction_on with
      | _ x =>
        rw [← Submodule.Quotient.mk_smul]
        exact Submodule.mem_map_of_mem (f := C'.mkQ)
          (show p • x ∈ (e.1.N ⊓ N).comap N.subtype from ⟨i12 (Submodule.smul_mem_smul hp x.2), N.smul_mem p x.2⟩)
    · rw [eq_bot_iff, Submodule.smul_le]
      intro p hp y hy
      obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hy
      rw [Submodule.mem_bot, Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact ⟨i22 (Submodule.smul_mem_smul hp hx.1), N.smul_mem p x.2⟩
    · have hglue := split_sup_inf_eq hne i11 i22
      have hg : (e.1.N.toAddSubgroup ⊓ N.toAddSubgroup) ⊔ (M.toAddSubgroup ⊓ e.1.N.toAddSubgroup) = e.1.N.toAddSubgroup := by
        rw [← inf_toAddSubgroup, ← inf_toAddSubgroup, ← Submodule.sup_toAddSubgroup, hglue]
      have hj : M.toAddSubgroup.relIndex e.1.N.toAddSubgroup = Nat.card (𝓞 E ⧸ (conjPrime₂ P).asIdeal) ^ j := by
        rw [← AddSubgroup.inf_relIndex_right, ← inf_toAddSubgroup, ← wmp_card_quot]
        exact card_of_equiv_fin ⟨i23⟩
      have hmul := AddSubgroup.relIndex_mul_relIndex (H := (M ⊓ N).toAddSubgroup) (K := (e.1.N ⊓ N).toAddSubgroup)
        (L := N.toAddSubgroup) (fun x hx => hCB hx) (fun x hx => hx.2)
      rw [inf_toAddSubgroup M N, inf_toAddSubgroup e.1.N N, ← relIndex_of_sup_eq hg, hj,
        ← inf_toAddSubgroup e.1.N N, hBN, ← inf_toAddSubgroup M N] at hmul
      rw [hBN, ← hmul] at c2
      exact Nat.eq_of_mul_eq_mul_right (pow_pos hq0 i) c2
  let Φ : {e : DecoSet E n ST SG // e ∈ d.heckeSet P.asIdeal i ∧ f ∈ e.heckeSet P.asIdeal j} →
      submoduleChainSet (conjPrime₂ P) (N ⧸ C') i j := fun e => ⟨_, hmem e⟩
  refine Nat.card_eq_of_bijective Φ ⟨?_, ?_⟩
  ·
    rintro ⟨e₁, ⟨hn1, hf1, hb1⟩, h1⟩ ⟨e₂, ⟨hn2, hf2, hb2⟩, h2⟩ h
    have h' := congrArg (fun Y : submoduleChainSet (conjPrime₂ P) (N ⧸ C') i j => (Y.1.comap C'.mkQ).map N.subtype) h
    have hC1 : C' ≤ (e₁.1.N ⊓ N).comap N.subtype :=
      Submodule.comap_mono (le_inf (split_inf_le hne ((isHeckeNbr_iff P j _ _).1 h1.1).1
        ((isHeckeNbr_iff P i _ _).1 hn1).2.1) inf_le_right)
    have hC2 : C' ≤ (e₂.1.N ⊓ N).comap N.subtype :=
      Submodule.comap_mono (le_inf (split_inf_le hne ((isHeckeNbr_iff P j _ _).1 h2.1).1
        ((isHeckeNbr_iff P i _ _).1 hn2).2.1) inf_le_right)
    simp only [Φ, Submodule.comap_map_mkQ, sup_eq_right.2 hC1, sup_eq_right.2 hC2, Submodule.map_comap_subtype] at h'
    have hB : e₁.1.N ⊓ N = e₂.1.N ⊓ N := by
      rw [inf_eq_right.2 (inf_le_right : e₁.1.N ⊓ N ≤ N), inf_eq_right.2 (inf_le_right : e₂.1.N ⊓ N ≤ N)] at h'
      exact h'
    have g₁ := hn1.eq_glue d.2.lat d.2.uni e₁.2.uni P hne
    have g₂ := hn2.eq_glue d.2.lat d.2.uni e₂.2.uni P hne
    exact Subtype.ext (Subtype.ext (Deco.ext (by rw [g₁, g₂, hB]) (hf1.trans hf2.symm) (hb1.trans hb2.symm)))
  ·
    rintro ⟨Y, hY1, hY2, hY3, hY4⟩
    set B' := Y.comap C'.mkQ with hB'
    set B := B'.map N.subtype with hBdef
    have hYB : B'.map C'.mkQ = Y := Submodule.map_comap_eq_of_surjective (Submodule.mkQ_surjective C') Y
    have hC'B' : C' ≤ B' := fun x hx => by
      rw [hB', Submodule.mem_comap, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero C').2 hx]
      exact Y.zero_mem
    have hB'eq : B.comap N.subtype = B' := Submodule.comap_map_eq_of_injective N.injective_subtype B'
    have hCB : M ⊓ N ≤ B := fun x hx => ⟨⟨x, hx.2⟩, hC'B' hx, rfl⟩
    have hBN : B ≤ N := Submodule.map_subtype_le _ _

    have hkillB : ∀ p ∈ (conjPrime₂ P).asIdeal, ∀ z : N ⧸ B', p • z = 0 := by
      intro p hp z
      induction z using Submodule.Quotient.induction_on with
      | _ x =>
        rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, hB', Submodule.mem_comap, map_smul]
        exact hY1 (Submodule.smul_mem_smul hp Submodule.mem_top)
    have hcardB : Nat.card (N ⧸ B') = Nat.card (𝓞 E ⧸ (conjPrime₂ P).asIdeal) ^ i := by
      rw [← Nat.card_congr (Submodule.quotientQuotientEquivQuotient C' B' hC'B').toEquiv, hYB]
      exact hY3
    obtain ⟨ψ⟩ := wmp_quot_equiv_of_card (conjPrime₂ P) (N ⧸ B') hkillB hcardB
    let φ : N →ₗ[𝓞 E] (Fin i → 𝓞 E ⧸ (conjPrime₂ P).asIdeal) := (ψ : (N ⧸ B') →ₗ[𝓞 E] _) ∘ₗ B'.mkQ
    have hφ : Function.Surjective φ := ψ.surjective.comp (Submodule.mkQ_surjective B')
    have hkφ : LinearMap.ker φ = B' := by
      rw [LinearMap.ker_comp, LinearEquiv.ker, Submodule.comap_bot, Submodule.ker_mkQ]
    obtain ⟨N', hl, hu, hnb, hsame, hinf⟩ := exists_heckeNbr_ker d.2.lat d.2.uni P hne φ hφ
    rw [hkφ] at hinf

    have hglue := hnb.eq_glue d.2.lat d.2.uni hu P hne
    rw [hinf] at hglue
    obtain ⟨n11, n12, -⟩ := (isHeckeNbr_iff P i _ _).1 hnb

    have hPbB : (conjPrime₂ P).asIdeal • B ≤ M := by
      rw [Submodule.smul_le]
      intro p hp x hx
      obtain ⟨x', hx', rfl⟩ := Submodule.mem_map.1 hx
      have h5 : p • C'.mkQ x' ∈ (conjPrime₂ P).asIdeal • Y := Submodule.smul_mem_smul hp hx'
      rw [hY2, Submodule.mem_bot, ← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h5
      exact h5.1
    have hsq : (P.asIdeal * P.asIdeal) • M ≤ B := ideal_sq_smul_le hPM hCB
    have hPbar : (conjPrime₂ P).asIdeal • N' ≤ M := by
      rw [hglue, Submodule.smul_sup]
      refine sup_le hPbB ?_
      rw [Submodule.smul_le]
      intro t ht z hz
      refine Submodule.smul_induction_on (p := fun z => t • z ∈ M) hz (fun r hr u hu' => ?_) (fun a b ha hb => ?_)
      · rw [smul_smul]
        refine conj_smul_dual_mem f.2.uni hsq ?_ hu'
        rw [map_mul]
        exact Ideal.mul_mem_mul ht hr
      · rw [smul_add]; exact M.add_mem ha hb
    have hPM' : P.asIdeal • M ≤ N' := by
      rw [Submodule.smul_le]
      intro p hp x hx
      refine conj_smul_dual_mem hu hPbar ?_ ?_
      · rw [mem_conjP, cO_cO]
        exact hp
      · rw [show dual (hStd E n) M = M from f.2.uni]
        exact hx

    have hkill' : ∀ p ∈ (conjPrime₂ P).asIdeal, ∀ z : N' ⧸ (M ⊓ N').comap N'.subtype, p • z = 0 := by
      intro p hp z
      induction z using Submodule.Quotient.induction_on with
      | _ y =>
        rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
        exact ⟨hPbar (Submodule.smul_mem_smul hp y.2), N'.smul_mem p y.2⟩
    have hcard' : Nat.card (N' ⧸ (M ⊓ N').comap N'.subtype) = Nat.card (𝓞 E ⧸ (conjPrime₂ P).asIdeal) ^ j := by
      obtain ⟨c1, c2⟩ := card_quotient_relIndex (N := N) hCB
      have hBNi : B.toAddSubgroup.relIndex N.toAddSubgroup = Nat.card (𝓞 E ⧸ (conjPrime₂ P).asIdeal) ^ i := by
        rw [← wmp_card_quot, hB'eq]
        exact hcardB
      have hYc : Nat.card ((B.comap N.subtype).map C'.mkQ) = Nat.card (𝓞 E ⧸ (conjPrime₂ P).asIdeal) ^ j := by
        rw [hB'eq, hYB]
        exact hY4
      have hmul := AddSubgroup.relIndex_mul_relIndex (H := (M ⊓ N).toAddSubgroup) (K := B.toAddSubgroup)
        (L := N.toAddSubgroup) (fun x hx => hCB hx) (fun x hx => hBN hx)
      rw [hYc, hBNi] at c2
      rw [hBNi, ← c2] at hmul
      have hMB : (M ⊓ N).toAddSubgroup.relIndex B.toAddSubgroup = Nat.card (𝓞 E ⧸ (conjPrime₂ P).asIdeal) ^ j :=
        Nat.eq_of_mul_eq_mul_right (pow_pos hq0 i) hmul
      have hglue2 := split_sup_inf_eq hne n11 hPbar
      have hg : (N'.toAddSubgroup ⊓ N.toAddSubgroup) ⊔ (M.toAddSubgroup ⊓ N'.toAddSubgroup) = N'.toAddSubgroup := by
        rw [← inf_toAddSubgroup, ← inf_toAddSubgroup, ← Submodule.sup_toAddSubgroup, hglue2]
      rw [wmp_card_quot, inf_toAddSubgroup, AddSubgroup.inf_relIndex_right, relIndex_of_sup_eq hg,
        ← inf_toAddSubgroup, ← inf_toAddSubgroup, hinf]
      exact hMB
    obtain ⟨ψ'⟩ := wmp_quot_equiv_of_card (conjPrime₂ P) _ hkill' hcard'
    let e : DecoSet E n ST SG := ⟨{ N := N', f := d.1.f, be := d.1.be },
      d.2.replN hl hu (fun R => hsame R.1 (hST R).1 (hST R).2) (fun w => hsame w.1 (hSG w).1 (hSG w).2)⟩
    have he1 : e ∈ d.heckeSet P.asIdeal i := ⟨hnb, rfl, rfl⟩
    have he2 : f ∈ e.heckeSet P.asIdeal j := ⟨(isHeckeNbr_iff P j _ _).2 ⟨hPM', hPbar, ⟨ψ'⟩⟩, hf, hb⟩
    refine ⟨⟨e, he1, he2⟩, Subtype.ext ?_⟩
    change ((N' ⊓ N).comap N.subtype).map C'.mkQ = Y
    rw [hinf, hB'eq, hYB]

theorem pathCount_symm_same_prime (P : HeightOneSpectrum (𝓞 E)) (hne : conjPrime₂ P ≠ P)
    (hST : ∀ R : ST, R.1 ≠ P ∧ R.1 ≠ conjPrime₂ P) (hSG : ∀ w : SG, w.1 ≠ P ∧ w.1 ≠ conjPrime₂ P) (i j : ℕ)
    (d f : DecoSet E n ST SG) :
    decorationPathCount P.asIdeal P.asIdeal i j d f = decorationPathCount P.asIdeal P.asIdeal j i d f := by
  rw [pathCount_eq_card_middle P P i j d f, pathCount_eq_card_middle P P j i d f]
  by_cases hc : f.1.f = d.1.f ∧ f.1.be = d.1.be ∧
      (∀ p ∈ P.asIdeal, ∀ p' ∈ P.asIdeal, ∀ x ∈ f.1.N, p • p' • x ∈ d.1.N)
  · obtain ⟨hf, hb, hPM⟩ := hc
    rw [card_paths_eq_submodulePairs P hne hST hSG d f hf hb hPM i j,
      card_paths_eq_submodulePairs P hne hST hSG d f hf hb hPM j i]
    by_cases hfin : Finite (d.1.N ⧸ (f.1.N ⊓ d.1.N).comap d.1.N.subtype)
    · rw [card_submodulePairs_symm]
    · have hq := one_lt_card_residue (conjPrime₂ P)
      have hT : ∀ k l, Nat.card (submoduleChainSet (conjPrime₂ P) (d.1.N ⧸ (f.1.N ⊓ d.1.N).comap d.1.N.subtype) k l) = 0 := by
        intro k l
        rw [Nat.card_eq_zero]
        left
        refine ⟨fun Y => hfin ?_⟩
        obtain ⟨Y, hY⟩ := Y
        obtain ⟨_, _, hXY, hY'⟩ := hY
        apply Nat.finite_of_card_ne_zero
        rw [Submodule.card_eq_card_quotient_mul_card Y, hXY, hY']
        exact Nat.mul_ne_zero (pow_ne_zero _ (by omega)) (pow_ne_zero _ (by omega))
      rw [hT, hT]
  · have h0 : ∀ k l, Nat.card {e : DecoSet E n ST SG //
        e ∈ d.heckeSet P.asIdeal k ∧ f ∈ e.heckeSet P.asIdeal l} = 0 := by
      intro k l
      rw [Nat.card_eq_zero]
      left
      refine ⟨fun x => ?_⟩
      obtain ⟨e, he1, he2⟩ := x
      simp only [DecoSet.heckeSet, Set.mem_setOf_eq] at he1 he2
      apply hc
      refine ⟨he2.2.1.trans he1.2.1, he2.2.2.trans he1.2.2, ?_⟩
      intro p hp p' hp' x hx
      exact he1.1.1 (Submodule.smul_mem_smul hp (he2.1.1 (Submodule.smul_mem_smul hp' hx)))
    rw [h0, h0]

end Paths

end Formalism.L2.Col
