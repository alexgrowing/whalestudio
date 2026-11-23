import Development.WeilBound.CoreStatements.VolumeEquality.DegPushFibA
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PIntNumSymm

noncomputable section

namespace SheetDecomposition

namespace Fib

variable {Ψ : Type} {p q : ℕ} {K : Type}

def entPair : Ent (rk Ψ p q) → PairIx Ψ p q
  | ⟨.inl τ, ⟨l, m⟩, h⟩ => (τ, ⟨(Fin.castAdd q m, Fin.castAdd q l), h, by
      have h1 : (l : ℕ) < p := l.2
      have h2 : (m : ℕ) < p := m.2
      exact iff_of_true h2 h1⟩)
  | ⟨.inr τ, ⟨l, m⟩, h⟩ => (τ, ⟨(Fin.natAdd p m, Fin.natAdd p l), by
      have h' : (m : ℕ) < l := h
      exact ⟨show p + (m : ℕ) < p + l by omega, iff_of_false (show ¬ p + (m : ℕ) < p by omega)
        (show ¬ p + (l : ℕ) < p by omega)⟩⟩)

theorem entPair_bij : Function.Bijective (entPair : Ent (rk Ψ p q) → PairIx Ψ p q) := by
  constructor
  · rintro ⟨s, ⟨l, m⟩, h⟩ ⟨s', ⟨l', m'⟩, h'⟩ he
    rcases s with τ | τ <;> rcases s' with τ' | τ'
    · simp only [entPair, Prod.mk.injEq, Subtype.mk.injEq] at he
      obtain ⟨rfl, h1, h2⟩ := he
      have e1' := congrArg Fin.val h1
      have e2' := congrArg Fin.val h2
      change (m : ℕ) = (m' : ℕ) at e1'
      change (l : ℕ) = (l' : ℕ) at e2'
      have e1 : m = m' := Fin.ext e1'
      have e2 : l = l' := Fin.ext e2'
      subst e1 e2
      rfl
    · simp only [entPair, Prod.mk.injEq, Subtype.mk.injEq] at he
      obtain ⟨rfl, h1, h2⟩ := he
      have e : (m : ℕ) = p + (m' : ℕ) := congrArg Fin.val h1
      have hm : (m : ℕ) < p := m.2
      omega
    · simp only [entPair, Prod.mk.injEq, Subtype.mk.injEq] at he
      obtain ⟨rfl, h1, h2⟩ := he
      have e : p + (m : ℕ) = (m' : ℕ) := congrArg Fin.val h1
      have hm : (m' : ℕ) < p := m'.2
      omega
    · simp only [entPair, Prod.mk.injEq, Subtype.mk.injEq] at he
      obtain ⟨rfl, h1, h2⟩ := he
      have e1' : p + (m : ℕ) = p + (m' : ℕ) := congrArg Fin.val h1
      have e2' : p + (l : ℕ) = p + (l' : ℕ) := congrArg Fin.val h2
      have e1 : m = m' := Fin.ext (by omega)
      have e2 : l = l' := Fin.ext (by omega)
      subst e1 e2
      rfl
  · rintro ⟨τ, ⟨a, b⟩, hab, hiff⟩
    by_cases hb : (b : ℕ) < p
    · have ha : (a : ℕ) < p := hiff.2 hb
      refine ⟨⟨Sum.inl τ, ⟨(⟨b, hb⟩, ⟨a, ha⟩), hab⟩⟩, ?_⟩
      simp only [entPair]
      congr 1
    · have ha : ¬ (a : ℕ) < p := fun h => hb (hiff.1 h)
      have hlt : (a : ℕ) < b := hab
      have hb' : (b : ℕ) - p < q := by omega
      have ha' : (a : ℕ) - p < q := by omega
      refine ⟨⟨Sum.inr τ, ⟨(⟨b - p, hb'⟩, ⟨a - p, ha'⟩), show (a : ℕ) - p < b - p by omega⟩⟩, ?_⟩
      simp only [entPair]
      congr 1
      apply Subtype.ext
      simp only [Prod.mk.injEq, Fin.ext_iff, Fin.natAdd]
      omega

def dif {n : ℕ} (st : Fin n → K → ℤ) (m : Fin n) : K → ℤ :=
  st m - if h : 0 < (m : ℕ) then st ⟨m - 1, by omega⟩ else 0

theorem dif_sum {n : ℕ} (g : Fin n → K → ℤ) (m : Fin n) : dif (fun m => ∑ m' ∈ Finset.Iic m, g m') m = g m := by
  unfold dif
  beta_reduce
  rw [Finset.Iic_eq_cons_Iio m, Finset.sum_cons]
  split_ifs with h
  · have e : Finset.Iio m = Finset.Iic (⟨(m : ℕ) - 1, by omega⟩ : Fin n) := by
      ext x
      simp only [Finset.mem_Iio, Finset.mem_Iic, Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val]
      omega
    rw [e]
    abel
  · have e : Finset.Iio m = ∅ := by
      ext x
      simp only [Finset.mem_Iio, Finset.notMem_empty, iff_false, not_lt, Fin.le_iff_val_le_val]
      omega
    rw [e, Finset.sum_empty]
    simp

def rootOf (st : ∀ s, Fin (rk Ψ p q s) → K → ℤ) (t : Ψ × Fin (p + q)) : K → ℤ :=
  if h : (t.2 : ℕ) < p then dif (st (.inl t.1)) ⟨t.2, h⟩
  else -dif (st (.inr t.1)) ⟨p + q - 1 - t.2, by have := t.2.2; show _ < q; omega⟩

theorem rootOf_step (x : Ψ × Fin (p + q) → K → ℤ) (t : Ψ × Fin (p + q)) : rootOf (stepDeg x) t = x t := by
  obtain ⟨τ, j⟩ := t
  unfold rootOf
  split_ifs with h
  · have e := dif_sum (grDeg x (Sum.inl τ)) ⟨(j : ℕ), h⟩
    change dif (fun m => ∑ m' ∈ Finset.Iic m, grDeg x (Sum.inl τ) m') ⟨(j : ℕ), h⟩ = x (τ, j)
    rw [e]
    rfl
  · have hj := j.2
    have h' : ¬ (j : ℕ) < p := h
    have e := dif_sum (grDeg x (Sum.inr τ)) ⟨p + q - 1 - (j : ℕ), by show _ < q; omega⟩
    change -dif (fun m => ∑ m' ∈ Finset.Iic m, grDeg x (Sum.inr τ) m') ⟨p + q - 1 - (j : ℕ), _⟩ = x (τ, j)
    rw [e]
    simp only [grDeg, neg_neg]
    congr 2
    apply Fin.ext
    simp only
    omega

section

variable {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω] [Fintype K] {ι : K → Type} [∀ b, Fintype (ι b)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ b, Fintype (ι' b)] {y : (Σ b, ι b) → Ω} {y' : (Σ b, ι' b) → Ω}

private theorem sup_valuation_ne_zero_of_exists_ne_zero {L : Type} [Field L] {J : Type} [Fintype J] {κ : J → Type} [∀ b, Fintype (κ b)]
    (O : ValuationSubring L) (z : (Σ b, κ b) → L) (hz : ∀ b, ∃ i, z ⟨b, i⟩ ≠ 0) (b : J) :
    (Finset.univ.sup fun i : κ b => O.valuation (z ⟨b, i⟩)) ≠ 0 := by
  obtain ⟨i, hi⟩ := hz b
  have hv : O.valuation (z ⟨b, i⟩) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    exact hi
  intro h0
  have hle : O.valuation (z ⟨b, i⟩) ≤ Finset.univ.sup fun i : κ b => O.valuation (z ⟨b, i⟩) :=
    Finset.le_sup (f := fun i : κ b => O.valuation (z ⟨b, i⟩)) (Finset.mem_univ i)
  rw [h0] at hle
  exact hv (le_antisymm hle zero_le')

private theorem vdeg_sub' {L : Type} [Field L] {J : Type} [Fintype J] {κ : J → Type} [∀ b, Fintype (κ b)]
    (O : ValuationSubring L) (z : (Σ b, κ b) → L) (hz : ∀ b, ∃ i, z ⟨b, i⟩ ≠ 0) (a c : J → ℤ) :
    vdeg O z (a - c) = vdeg O z a / vdeg O z c := by
  unfold vdeg
  rw [← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [Pi.sub_apply, zpow_sub₀ (sup_valuation_ne_zero_of_exists_ne_zero O z hz b)]

private theorem vdeg_ne_zero' {L : Type} [Field L] {J : Type} [Fintype J] {κ : J → Type} [∀ b, Fintype (κ b)]
    (O : ValuationSubring L) (z : (Σ b, κ b) → L) (hz : ∀ b, ∃ i, z ⟨b, i⟩ ≠ 0) (a : J → ℤ) :
    vdeg O z a ≠ 0 := by
  unfold vdeg
  rw [Finset.prod_ne_zero_iff]
  intro b _
  exact zpow_ne_zero _ (sup_valuation_ne_zero_of_exists_ne_zero O z hz b)

theorem valEq_dif (hy : ∀ b, ∃ i, y ⟨b, i⟩ ≠ 0) (hy' : ∀ b, ∃ i, y' ⟨b, i⟩ ≠ 0) {n : ℕ} {st : Fin n → K → ℤ}
    {st' : Fin n → K' → ℤ} (h : ∀ m, ValEq k y (st m) y' (st' m)) (m : Fin n) : ValEq k y (dif st m) y' (dif st' m) := by
  unfold dif
  split_ifs with hm
  · obtain ⟨ρ₁, hρ₁, h₁⟩ := h m
    obtain ⟨ρ₂, hρ₂, h₂⟩ := h ⟨(m : ℕ) - 1, by omega⟩
    refine ⟨ρ₁ / ρ₂, div_ne_zero hρ₁ hρ₂, fun O hO => ?_⟩
    rw [vdeg_sub' O y hy, vdeg_sub' O y' hy', h₁ O hO, h₂ O hO, map_div₀]
    have hv : O.valuation ρ₂ ≠ 0 := by
      rw [Valuation.ne_zero_iff]
      exact hρ₂
    have hw := vdeg_ne_zero' O y' hy' (st' ⟨(m : ℕ) - 1, by omega⟩)
    field_simp
  · simpa using h m

private theorem vdeg_neg' {L : Type} [Field L] {J : Type} [Fintype J] {κ : J → Type} [∀ b, Fintype (κ b)]
    (O : ValuationSubring L) (z : (Σ b, κ b) → L) (a : J → ℤ) :
    vdeg O z (-a) = (vdeg O z a)⁻¹ := by
  unfold vdeg
  rw [← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [Pi.neg_apply, zpow_neg]

theorem valEq_root (hy : ∀ b, ∃ i, y ⟨b, i⟩ ≠ 0) (hy' : ∀ b, ∃ i, y' ⟨b, i⟩ ≠ 0) {st : ∀ s, Fin (rk Ψ p q s) → K → ℤ}
    {st' : ∀ s, Fin (rk Ψ p q s) → K' → ℤ} (h : ∀ s m, ValEq k y (st s m) y' (st' s m)) (t : Ψ × Fin (p + q)) :
    ValEq k y (rootOf st t) y' (rootOf st' t) := by
  unfold rootOf
  split_ifs with ht
  · exact valEq_dif hy hy' (h _) _
  · obtain ⟨ρ, hρ, hh⟩ := valEq_dif hy hy' (h (Sum.inr t.1)) ⟨p + q - 1 - (t.2 : ℕ), by have := t.2.2; show _ < q; omega⟩
    refine ⟨ρ⁻¹, inv_ne_zero hρ, fun O hO => ?_⟩
    rw [vdeg_neg', vdeg_neg', hh O hO, map_inv₀, mul_inv]

end

def uConst (Ψ : Type) [Fintype Ψ] (p q : ℕ) : ℤ :=
  uNum (rk Ψ p q) fun j => fibDeg (rootOf fun s m => plDeg ⟨s, m⟩) ((Finite.equivFin (PairIx Ψ p q)).symm j)

private theorem valEq_sub {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω] {K : Type} [Fintype K]
    {ι : K → Type} [∀ b, Fintype (ι b)] {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ b, Fintype (ι' b)]
    {y : (Σ b, ι b) → Ω} {y' : (Σ b, ι' b) → Ω}
    (hy : ∀ b, ∃ i, y ⟨b, i⟩ ≠ 0) (hy' : ∀ b, ∃ i, y' ⟨b, i⟩ ≠ 0) {a c : K → ℤ} {a' c' : K' → ℤ}
    (ha : ValEq k y a y' a') (hc : ValEq k y c y' c') : ValEq k y (a - c) y' (a' - c') := by
  obtain ⟨ρ₁, hρ₁, h₁⟩ := ha
  obtain ⟨ρ₂, hρ₂, h₂⟩ := hc
  refine ⟨ρ₁ / ρ₂, div_ne_zero hρ₁ hρ₂, fun O hO => ?_⟩
  rw [vdeg_sub' O y hy, vdeg_sub' O y' hy', h₁ O hO, h₂ O hO, map_div₀]
  have hv : O.valuation ρ₂ ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    exact hρ₂
  have hw := vdeg_ne_zero' O y' hy' c'
  field_simp

theorem num_eq (hN : NumEq) [Fintype Ψ] (k : Type) [Field k] [CharZero k] (Ω : Type) [Field Ω] [Algebra k Ω] [Fintype K]
    (ι : K → Type) [∀ b, Fintype (ι b)] (y : (Σ b, ι b) → Ω) (u : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (rk Ψ p q s)) Ω)
    (d r : ℕ) (x : Ψ × Fin (p + q) → K → ℤ) (e : Fin r ≃ PairIx Ψ p q) (hu : IsGenU k u d) (hy : IsPt k y r)
    (hv : ∀ s m, ValEq k y (stepDeg x s m) (plPt u) (plDeg ⟨s, m⟩)) :
    num k y (fun j => fibDeg x (e j)) = d * uConst Ψ p q := by
  classical
  have hne := plPt_ne u hu.1 hu.2.1
  have hfd : FiniteDimensional (fnField k (plPt u)) Ω := by
    rw [fnField_plPt u hu.1 hu.2.1]
    exact Module.finite_of_finrank_pos (by rw [hu.2.2.2.2]; exact hu.2.2.2.1)
  have hcard : Nat.card (Ent (rk Ψ p q)) = r := by
    rw [Nat.card_eq_of_bijective _ entPair_bij, Nat.card_congr e.symm, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hpt' : IsPt k (plPt u) r := ⟨hne, hfd, by rw [trdeg_eq u hu, hcard]⟩
  have hval : ∀ j, ValEq k y (fibDeg x (e j)) (plPt u) (fibDeg (rootOf fun s m => plDeg ⟨s, m⟩) (e j)) := by
    intro j
    unfold fibDeg
    apply valEq_sub hy.1 hne
    · rw [← rootOf_step x]
      exact valEq_root hy.1 hne hv _
    · rw [← rootOf_step x]
      exact valEq_root hy.1 hne hv _
  rw [hN k Ω K ι _ _ y (plPt u) r _ _ hy hpt' hval]
  unfold num
  rw [fnField_plPt u hu.1 hu.2.1, hu.2.2.2.2, inum_plPt u hu]
  unfold uConst
  congr 1
  have hN' : Nat.card (PairIx Ψ p q) = r := by
    rw [Nat.card_congr e.symm, Nat.card_eq_fintype_card, Fintype.card_fin]
  unfold uNum
  set g : PairIx Ψ p q → (Σ s, Fin (rk Ψ p q s)) → ℤ := fibDeg (rootOf fun s m => plDeg ⟨s, m⟩) with hg
  clear_value g
  revert e
  rw [← hN']
  intro e hval
  have := GroundTheory.Heights₂.Heights.FieldNumbers.IntNumSymm.proof ℚ (Σ s, Fin (rk Ψ p q s)) (PlIx (rk Ψ p q))
    (RingHom.ker (MvPolynomial.aeval (genCone (rk Ψ p q)))) _ (fun j => g ((Finite.equivFin (PairIx Ψ p q)).symm j))
    (e.trans (Finite.equivFin (PairIx Ψ p q)))
  convert this using 2
  funext j
  simp

variable {Ψ' : Type} {Ω : Type}

def reU (ε : Ψ' → Ψ) (u : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (rk Ψ p q s)) Ω) :
    ∀ s, Matrix (Fin (rk Ψ' p q s)) (Fin (rk Ψ' p q s)) Ω
  | .inl τ => u (.inl (ε τ))
  | .inr τ => u (.inr (ε τ))

def reEnt (ε : Ψ' → Ψ) : Ent (rk Ψ' p q) → Ent (rk Ψ p q)
  | ⟨.inl τ, x⟩ => ⟨.inl (ε τ), x⟩
  | ⟨.inr τ, x⟩ => ⟨.inr (ε τ), x⟩

theorem isGenU_reU {k : Type} [Field k] [Field Ω] [Algebra k Ω] (ε : Ψ' ≃ Ψ)
    (u : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (rk Ψ p q s)) Ω) {d : ℕ} (h : IsGenU k u d) : IsGenU k (reU ε u) d := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨?_, ?_, ?_, h4, ?_⟩
  · rintro (τ | τ) m
    · exact h1 (Sum.inl (ε τ)) m
    · exact h1 (Sum.inr (ε τ)) m
  · rintro (τ | τ) l m hlm
    · exact h2 (Sum.inl (ε τ)) l m hlm
    · exact h2 (Sum.inr (ε τ)) l m hlm
  · have e : (fun q : Ent (rk Ψ' p q) => reU ε u q.1 q.2.1.1 q.2.1.2) =
        (fun q : Ent (rk Ψ p q) => u q.1 q.2.1.1 q.2.1.2) ∘ reEnt ε := by
      funext ⟨s, x⟩
      rcases s with τ | τ <;> rfl
    rw [e]
    refine h3.comp _ ?_
    rintro ⟨s, x⟩ ⟨s', x'⟩ he
    rcases s with τ | τ <;> rcases s' with τ' | τ'
    · obtain ⟨hs, hx⟩ := Sigma.mk.inj_iff.1 he
      have ht : τ = τ' := ε.injective (Sum.inl.inj hs)
      subst ht
      have hx' : x = x' := eq_of_heq hx
      subst hx'
      rfl
    · obtain ⟨hs, _⟩ := Sigma.mk.inj_iff.1 he
      exact absurd hs Sum.inl_ne_inr
    · obtain ⟨hs, _⟩ := Sigma.mk.inj_iff.1 he
      exact absurd hs Sum.inr_ne_inl
    · obtain ⟨hs, hx⟩ := Sigma.mk.inj_iff.1 he
      have ht : τ = τ' := ε.injective (Sum.inr.inj hs)
      subst ht
      have hx' : x = x' := eq_of_heq hx
      subst hx'
      rfl
  · have e : (Set.range fun q : (s : Ψ' ⊕ Ψ') × Fin (rk Ψ' p q s) × Fin (rk Ψ' p q s) => reU ε u q.1 q.2.1 q.2.2) =
        Set.range fun q : (s : Ψ ⊕ Ψ) × Fin (rk Ψ p q s) × Fin (rk Ψ p q s) => u q.1 q.2.1 q.2.2 := by
      ext z
      constructor
      · rintro ⟨⟨s, l, m⟩, rfl⟩
        rcases s with τ | τ
        · exact ⟨⟨Sum.inl (ε τ), l, m⟩, rfl⟩
        · exact ⟨⟨Sum.inr (ε τ), l, m⟩, rfl⟩
      · rintro ⟨⟨s, l, m⟩, rfl⟩
        rcases s with τ | τ
        · exact ⟨⟨Sum.inl (ε.symm τ), l, m⟩, congrArg (fun X => u (Sum.inl X) l m) (ε.apply_symm_apply τ)⟩
        · exact ⟨⟨Sum.inr (ε.symm τ), l, m⟩, congrArg (fun X => u (Sum.inr X) l m) (ε.apply_symm_apply τ)⟩
    rw [e]
    exact h5

end Fib

open Fib

theorem trdegU : TrdegU := by
  intro Ψ _ p q k _ Ω _ _ u d h
  rw [trdeg_eq u h, Nat.card_eq_of_bijective _ entPair_bij, Nat.card_eq_fintype_card]

theorem fibNum : NumEq → FibNum := by
  intro hN
  refine ⟨fun n p q => uConst (Fin n) p q, ?_⟩
  intro Ψ _ p q k _ _ Ω _ _ K _ ι _ y u d r x e hu hy hv
  show _ = (d : ℤ) * uConst (Fin (Fintype.card Ψ)) p q
  let ε : Fin (Fintype.card Ψ) ≃ Ψ := (Fintype.equivFin Ψ).symm
  let x' : Fin (Fintype.card Ψ) × Fin (p + q) → K → ℤ := fun t => x (ε t.1, t.2)
  let e' : Fin r ≃ PairIx (Fin (Fintype.card Ψ)) p q :=
    e.trans (Equiv.prodCongr ε (Equiv.refl _)).symm
  have hu' := isGenU_reU ε u hu
  have hv' : ∀ s m, ValEq k y (stepDeg x' s m) (plPt (reU ε u)) (plDeg ⟨s, m⟩) := by
    rintro (τ | τ) m
    · obtain ⟨ρ, hρ, h⟩ := hv (Sum.inl (ε τ)) m
      refine ⟨ρ, hρ, fun O hO => ?_⟩
      have := h O hO
      rw [vdeg_plDeg] at this ⊢
      exact this
    · obtain ⟨ρ, hρ, h⟩ := hv (Sum.inr (ε τ)) m
      refine ⟨ρ, hρ, fun O hO => ?_⟩
      have := h O hO
      rw [vdeg_plDeg] at this ⊢
      exact this
  have h1 := num_eq hN k Ω ι y (reU ε u) d r x' e' hu' hy hv'
  rw [← h1]
  congr 1
  funext j
  simp [e', x', fibDeg]

end SheetDecomposition
