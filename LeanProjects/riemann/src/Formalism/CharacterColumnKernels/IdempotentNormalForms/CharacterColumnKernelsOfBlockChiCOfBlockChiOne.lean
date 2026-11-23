import Formalism.CharacterColumnKernels.CharacterColumnKernelEqualityForm
import Formalism.CharacterColumnKernels.IdempotentNormalForms.GlobalColumn
import Formalism.CharacterColumnKernels.IdempotentNormalForms.BlockRhoFull
import Formalism.CharacterColumnKernels.IdempotentNormalForms.BlockChiOneFullOf

open Finset Classical

noncomputable section

namespace Formalism.NG

lemma sum_range_ite_le_add_sum_Ioo (t : ℕ) (a : ℕ∞) (Sha : ℕ → ℕ∞) :
    ∑ i ∈ range t, (if i + 1 = 1 then a else Sha (i + 1 - 1)) ≤ a + ∑ e ∈ Ioo 0 t, Sha e := by
  have hsub : range t ⊆ insert 0 (Ioo 0 t) := by
    intro i hi
    rw [mem_range] at hi
    rcases Nat.eq_zero_or_pos i with h | h
    · exact mem_insert.2 (Or.inl h)
    · exact mem_insert.2 (Or.inr (mem_Ioo.2 ⟨h, hi⟩))
  have h0 : (0 : ℕ) ∉ Ioo 0 t := by simp
  calc ∑ i ∈ range t, (if i + 1 = 1 then a else Sha (i + 1 - 1))
      ≤ ∑ i ∈ insert 0 (Ioo 0 t), (if i + 1 = 1 then a else Sha (i + 1 - 1)) :=
        sum_le_sum_of_subset hsub
    _ = a + ∑ e ∈ Ioo 0 t, Sha e := by
        rw [sum_insert h0]
        congr 1
        refine sum_congr rfl fun e he => ?_
        have hne : e + 1 ≠ 1 := by
          have := (mem_Ioo.1 he).1
          omega
        rw [if_neg hne, Nat.add_sub_cancel]

lemma collectAlt (t : ℕ) (ht : 1 ≤ t) (L : Fin (t + 1) → ℕ∞) (S : Finset (Fin (t + 1))) (v : ℕ∞)
    (what₂ cols qs : Finset ℕ) (lenRow vζ h0 : ℕ → ℕ∞) (e' j deg : ℕ → ℕ) (Sha : ℕ → ℕ∞)
    (eO vδ s vhE N H0 : ℕ∞) (cB : ℕ)
    (hG : v ≤ ∑ k ∈ S, L k)
    (hL0 : L 0 ≤ ∑ w ∈ what₂, lenRow w + ∑ w ∈ cols, ((j w : ℕ∞) * (eO * (e' w : ℕ∞) + vδ) + h0 w) +
      s + 4 * N * ((cols.card : ℕ∞) + 1) * vδ)
    (hL1 : L ⟨1, by omega⟩ ≤ vhE + ∑ w ∈ cols, (eO * (e' w : ℕ∞) + 2 * vδ) +
      eO * (cB : ℕ∞) * ∑ w ∈ what₂, ((deg w : ℕ∞) + 2) + 4 * ((cols.card : ℕ∞) + 1) * vδ +
      ∑ w ∈ qs, vζ w)
    (hLc : ∀ c : Fin (t + 1), 2 ≤ (c : ℕ) → L c ≤ Sha ((c : ℕ) - 1) +
      eO * (cB : ℕ∞) * ∑ w ∈ what₂, ((deg w : ℕ∞) + 2) + 4 * ((cols.card : ℕ∞) + 1) * vδ +
      (cols.card : ℕ∞) * H0 + ∑ w ∈ qs, vζ w) :
    v ≤ ∑ w ∈ what₂, lenRow w +
        ∑ w ∈ cols, (eO * (e' w : ℕ∞) + (j w : ℕ∞) * (eO * (e' w : ℕ∞) + vδ) + 2 * vδ + h0 w) + s +
        ∑ e ∈ Finset.Ioo 0 t, Sha e + vhE +
        (t : ℕ∞) * eO * (cB : ℕ∞) * ∑ w ∈ what₂, ((deg w : ℕ∞) + 2) +
        4 * (N + t) * ((cols.card : ℕ∞) + 1) * vδ +
        (t : ℕ∞) * (cols.card : ℕ∞) * H0 + (t : ℕ∞) * ∑ w ∈ qs, vζ w := by
  set C1 : ℕ∞ := ∑ w ∈ cols, (eO * (e' w : ℕ∞) + 2 * vδ) with hC1
  set A0 : ℕ∞ := ∑ w ∈ what₂, lenRow w +
    ∑ w ∈ cols, ((j w : ℕ∞) * (eO * (e' w : ℕ∞) + vδ) + h0 w) + s with hA0
  set B : ℕ∞ := eO * (cB : ℕ∞) * ∑ w ∈ what₂, ((deg w : ℕ∞) + 2) +
    4 * ((cols.card : ℕ∞) + 1) * vδ + (cols.card : ℕ∞) * H0 + ∑ w ∈ qs, vζ w with hB
  have hsucc : ∀ i : Fin t, L i.succ ≤
      (if (i : ℕ) + 1 = 1 then vhE + C1 else Sha ((i : ℕ) + 1 - 1)) + B := by
    intro i
    by_cases hi : (i : ℕ) = 0
    · have hs : i.succ = ⟨1, by omega⟩ := Fin.ext (by simp [hi])
      rw [if_pos (by omega), hs]
      refine (hL1.trans ?_)
      rw [hB]
      calc vhE + C1 + eO * (cB : ℕ∞) * ∑ w ∈ what₂, ((deg w : ℕ∞) + 2) +
            4 * ((cols.card : ℕ∞) + 1) * vδ + ∑ w ∈ qs, vζ w
          ≤ vhE + C1 + eO * (cB : ℕ∞) * ∑ w ∈ what₂, ((deg w : ℕ∞) + 2) +
            4 * ((cols.card : ℕ∞) + 1) * vδ + ∑ w ∈ qs, vζ w + (cols.card : ℕ∞) * H0 := le_self_add
        _ = _ := by ring
    · rw [if_neg (by omega)]
      have h2 : 2 ≤ ((i.succ : Fin (t + 1)) : ℕ) := by simp [Fin.val_succ]; omega
      refine (hLc i.succ h2).trans_eq ?_
      rw [hB, Fin.val_succ]
      ring
  have hsumite : ∑ i : Fin t, (if (i : ℕ) + 1 = 1 then vhE + C1 else Sha ((i : ℕ) + 1 - 1)) ≤
      (vhE + C1) + ∑ e ∈ Ioo 0 t, Sha e := by
    rw [Fin.sum_univ_eq_sum_range (fun i => if i + 1 = 1 then vhE + C1 else Sha (i + 1 - 1)) t]
    exact sum_range_ite_le_add_sum_Ioo t (vhE + C1) Sha
  have hcol : ∑ w ∈ cols,
      (eO * (e' w : ℕ∞) + (j w : ℕ∞) * (eO * (e' w : ℕ∞) + vδ) + 2 * vδ + h0 w) =
      ∑ w ∈ cols, ((j w : ℕ∞) * (eO * (e' w : ℕ∞) + vδ) + h0 w) + C1 := by
    rw [hC1, ← sum_add_distrib]
    exact sum_congr rfl fun w _ => by ring
  rw [hcol]
  calc v ≤ ∑ k ∈ S, L k := hG
    _ ≤ ∑ k : Fin (t + 1), L k := sum_le_sum_of_subset (subset_univ _)
    _ = L 0 + ∑ i : Fin t, L i.succ := Fin.sum_univ_succ L
    _ ≤ (A0 + 4 * N * ((cols.card : ℕ∞) + 1) * vδ) +
          ∑ i : Fin t, ((if (i : ℕ) + 1 = 1 then vhE + C1 else Sha ((i : ℕ) + 1 - 1)) + B) :=
        add_le_add hL0 (sum_le_sum fun i _ => hsucc i)
    _ = (A0 + 4 * N * ((cols.card : ℕ∞) + 1) * vδ) +
          (∑ i : Fin t, (if (i : ℕ) + 1 = 1 then vhE + C1 else Sha ((i : ℕ) + 1 - 1)) +
            (t : ℕ∞) * B) := by
        rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ (A0 + 4 * N * ((cols.card : ℕ∞) + 1) * vδ) +
          (((vhE + C1) + ∑ e ∈ Ioo 0 t, Sha e) + (t : ℕ∞) * B) := by
        gcongr
    _ = _ := by
        rw [hA0, hB]
        ring

set_option maxHeartbeats 4000000 in

theorem blockRhoLat : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A T' G : Type) [Ring A] [CommRing T'] [Algebra T' A] [Group G] (d : Type) [Fintype d] [DecidableEq d]
    (ρ : A →+* Matrix d d O) [SMulCommClass A O (LatQ O d ρ)]
    [Module T' (LatQ O d ρ)] [IsScalarTower T' A (LatQ O d ρ)]
    (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') (δO : O) (ι : Type) [Fintype ι] [DecidableEq ι]
    (ι' : Type) [DecidableEq ι'] (colIdx : ι → ι'), Function.Injective colIdx →
    ∀ (D : ι' → Subgroup G) (j e' : ι' → ℕ) (Kc : ∀ l, Fin (j (colIdx l)) → G → A)
      (k0 : ι → G → A) (ℓ : ℕ) (sE : Finset G) (tE : G → T'),
    E = ∑ g ∈ sE, tE g • r g → E * E = δ • E →
    (∀ m : LatQ O d ρ, E • m = 0) →
    (∀ l g, ∃ a : A, k0 l g = a * E) →
    (∀ m : LatQ O d ρ, δ • m = δO • m) →
    (∀ m : LatQ O d ρ, (∑ g ∈ sE, tE g * ((χ g : T'ˣ) : T')) • m = δO • m) →
    Nonempty (↥(LinearMap.range (DistribSMul.toLinearMap O (LatQ O d ρ) e₁)) ≃ₗ[O] KO O) →
    (∀ l (s : Fin (j (colIdx l)) → (LatQ O d ρ)),
      (∀ a, s a ∈ LinearMap.range (DistribSMul.toLinearMap O (LatQ O d ρ) e₁)) →
      (fun g : D (colIdx l) => ∑ a, Kc l a g • s a) ∈
        LinearMap.range (colDO (O := O) r χ (D (colIdx l))) →
      ∀ a, ((ℓ : O) ^ e' (colIdx l)) • s a = 0) →
    let ρM := uRep O (M := LatQ O d ρ) r χ
    let Ψ := colPsi (O := O) (M := LatQ O d ρ) r χ E e₁ δ (fun l => D (colIdx l))
      (fun l => j (colIdx l)) Kc k0
    ∀ (what₂ : Finset ι') (F : ∀ w, Submodule O (H1z (resRep ρM (D w)))) (lenRow : ι' → ℕ∞)
      (Q : Submodule O (H1z ρM)) (s : ℕ∞),
    let cols : Finset ι' := univ.image colIdx
    let eO : ℕ∞ := Module.length O (O ⧸ Ideal.span {(ℓ : O)})
    let vδ : ℕ∞ := IsDiscreteValuationRing.addVal O δO
    let N : ℕ∞ := Fintype.card d
    let h0 : ι' → ℕ∞ := fun w => Module.length O (LinearMap.ker (colDO (O := O) (M := LatQ O d ρ) r χ (D w)))
    (∀ w ∈ what₂, ∃ B : Submodule O (H1z (resRep ρM (D w))), F w ≤ B ∧
      Module.length O (B ⧸ (F w).comap B.subtype) ≤ lenRow w ∧
      ∀ h, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ B) →
    (∀ w ∈ cols, ∀ h, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ F w) →
    (∀ h, Submodule.mkQ _ (Ψ h) ∈ Q) →
    Module.length O ↥(Q ⊓ ⨅ w ∈ what₂ ∪ cols, (F w).comap (resH1 ρM (D w))) ≤ s →
    Module.length O (ColNNJ r χ E e₁ δ (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0 →ₗ[A]
        (LatQ O d ρ)) ≤
      ∑ w ∈ what₂, lenRow w + ∑ w ∈ cols, ((j w : ℕ∞) * (eO * (e' w : ℕ∞) + vδ) + h0 w) + s +
        4 * N * ((cols.card : ℕ∞) + 1) * vδ := by
  intro O _ _ _ A T' G _ _ _ _ d _ _ ρ _ _ _
  letI : Module A (d → KO O) := (inferInstance : Module A (LatQ O d ρ))
  letI : SMulCommClass A O (d → KO O) := (inferInstance : SMulCommClass A O (LatQ O d ρ))
  letI : Module T' (d → KO O) := (inferInstance : Module T' (LatQ O d ρ))
  letI : IsScalarTower T' A (d → KO O) := (inferInstance : IsScalarTower T' A (LatQ O d ρ))
  exact blockRhoFull O A T' G d

set_option maxHeartbeats 4000000 in

theorem blockChiCLat (hC : StatBlockChiCFull.{0, 0, 0, 0, 0, 0}) : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A T' G : Type) [Ring A] [CommRing T'] [Algebra T' A] [Group G] (d : Type) [Fintype d] [DecidableEq d]
    (ρ : A →+* Matrix d d O) [SMulCommClass A O (LatQ O d ρ)]
    [Module T' (LatQ O d ρ)] [IsScalarTower T' A (LatQ O d ρ)]
    (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') (δO : O) (ι : Type) [Fintype ι] [DecidableEq ι]
    (ι' : Type) [DecidableEq ι'] (colIdx : ι → ι'), Function.Injective colIdx →
    ∀ (D : ι' → Subgroup G) (j : ι' → ℕ) (Kc : ∀ l, Fin (j (colIdx l)) → G → A)
      (k0 : ι → G → A) (ℓ cB : ℕ) (sE : Finset G) (tE : G → T'),
    Fintype.card d = 1 →
    E = ∑ g ∈ sE, tE g • r g → E * E = δ • E →
    (∀ m : LatQ O d ρ, e₁ • m = 0) → (∀ m : LatQ O d ρ, E • m = 0) →
    (∀ l g, ∃ a : A, k0 l g = a * E) →
    (∀ m : LatQ O d ρ, δ • m = δO • m) →
    (∀ m : LatQ O d ρ, (∑ g ∈ sE, tE g * ((χ g : T'ˣ) : T')) • m = δO • m) →
    let ρM := uRep O (M := LatQ O d ρ) r χ
    let Ψ := colPsi (O := O) (M := LatQ O d ρ) r χ E e₁ δ (fun l => D (colIdx l))
      (fun l => j (colIdx l)) Kc k0
    ∀ (lrows qs : Finset ι') (F : ∀ w, Submodule O (H1z (resRep ρM (D w)))) (deg : ι' → ℕ)
      (vζ : ι' → ℕ∞) (Q : Submodule O (H1z ρM)) (Sha H0 : ℕ∞),
    let cols : Finset ι' := univ.image colIdx
    let eO : ℕ∞ := Module.length O (O ⧸ Ideal.span {(ℓ : O)})
    let vδ : ℕ∞ := IsDiscreteValuationRing.addVal O δO
    (∀ w ∈ cols, Module.length O (LinearMap.ker (colDO (O := O) (M := LatQ O d ρ) r χ (D w))) ≤ H0) →
    (∀ w ∈ lrows, ∃ B : Submodule O (H1z (resRep ρM (D w))), F w ≤ B ∧
      Module.length O (B ⧸ (F w).comap B.subtype) ≤ eO * (cB : ℕ∞) * ((deg w : ℕ∞) + 2) ∧
      ∀ h, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ B) →
    (∀ w ∈ qs, ∃ B : Submodule O (H1z (resRep ρM (D w))), F w ≤ B ∧
      Module.length O (B ⧸ (F w).comap B.subtype) ≤ vζ w ∧
      ∀ h, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ B) →
    (∀ w ∈ cols, ∀ h, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ F w) →
    (∀ h, Submodule.mkQ _ (Ψ h) ∈ Q) →
    Module.length O ↥(Q ⊓ ⨅ w ∈ lrows ∪ qs ∪ cols, (F w).comap (resH1 ρM (D w))) ≤ Sha →
    Module.length O (ColNNJ r χ E e₁ δ (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0 →ₗ[A]
        (LatQ O d ρ)) ≤
      Sha + eO * (cB : ℕ∞) * ∑ w ∈ lrows, ((deg w : ℕ∞) + 2) + 4 * ((cols.card : ℕ∞) + 1) * vδ +
        (cols.card : ℕ∞) * H0 + ∑ w ∈ qs, vζ w := by
  intro O _ _ _ A T' G _ _ _ _ d _ _ ρ _ _ _
  letI : Module A (d → KO O) := (inferInstance : Module A (LatQ O d ρ))
  letI : SMulCommClass A O (d → KO O) := (inferInstance : SMulCommClass A O (LatQ O d ρ))
  letI : Module T' (d → KO O) := (inferInstance : Module T' (LatQ O d ρ))
  letI : IsScalarTower T' A (d → KO O) := (inferInstance : IsScalarTower T' A (LatQ O d ρ))
  exact hC O A T' G d

set_option maxHeartbeats 4000000 in

theorem blockChiOneLat (hOne : StatBlockChiOneFull.{0, 0, 0, 0, 0, 0}) : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A T' G : Type) [Ring A] [CommRing T'] [Algebra T' A] [Group G] (d : Type) [Fintype d] [DecidableEq d]
    (ρ : A →+* Matrix d d O) [SMulCommClass A O (LatQ O d ρ)]
    [Module T' (LatQ O d ρ)] [IsScalarTower T' A (LatQ O d ρ)]
    (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') (δO : O) (ι : Type) [Fintype ι] [DecidableEq ι]
    (ι' : Type) [DecidableEq ι'] (colIdx : ι → ι'), Function.Injective colIdx →
    ∀ (D : ι' → Subgroup G) (j e' : ι' → ℕ) (Kc : ∀ l, Fin (j (colIdx l)) → G → A)
      (k0 : ι → G → A) (ℓ cB : ℕ),
    Fintype.card d = 1 →
    (∀ g (m : LatQ O d ρ), uElt r χ g • m = m) →
    (∀ m : LatQ O d ρ, e₁ • m = 0) → (∀ m : LatQ O d ρ, E • m = δO • m) →
    (∀ m : LatQ O d ρ, δ • m = δO • m) →
    (∀ l, ∃ g ∈ D (colIdx l), ∃ c : O, IsUnit c ∧
      ∀ m : LatQ O d ρ, k0 l g • m = ((ℓ : O) ^ e' (colIdx l) * δO * c) • m) →
    let ρM := uRep O (M := LatQ O d ρ) r χ
    let Ψ := colPsi (O := O) (M := LatQ O d ρ) r χ E e₁ δ (fun l => D (colIdx l))
      (fun l => j (colIdx l)) Kc k0
    ∀ (lrows qs : Finset ι') (F : ∀ w, Submodule O (H1z (resRep ρM (D w)))) (deg : ι' → ℕ)
      (vζ : ι' → ℕ∞) (Q : Submodule O (H1z ρM)) (vhE : ℕ∞),
    let cols : Finset ι' := univ.image colIdx
    let eO : ℕ∞ := Module.length O (O ⧸ Ideal.span {(ℓ : O)})
    let vδ : ℕ∞ := IsDiscreteValuationRing.addVal O δO
    (∀ w ∈ lrows, ∃ B : Submodule O (H1z (resRep ρM (D w))), F w ≤ B ∧
      Module.length O (B ⧸ (F w).comap B.subtype) ≤ eO * (cB : ℕ∞) * ((deg w : ℕ∞) + 2) ∧
      ∀ h, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ B) →
    (∀ w ∈ qs, ∃ B : Submodule O (H1z (resRep ρM (D w))), F w ≤ B ∧
      Module.length O (B ⧸ (F w).comap B.subtype) ≤ vζ w ∧
      ∀ h, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ B) →
    (∀ w ∈ cols, ∀ h, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ F w) →
    (∀ h, Submodule.mkQ _ (Ψ h) ∈ Q) →
    Module.length O ↥(Q ⊓ ⨅ w ∈ lrows ∪ qs ∪ cols, (F w).comap (resH1 ρM (D w))) ≤ vhE →
    Module.length O (ColNNJ r χ E e₁ δ (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0 →ₗ[A]
        (LatQ O d ρ)) ≤
      vhE + ∑ w ∈ cols, (eO * (e' w : ℕ∞) + 2 * vδ) +
        eO * (cB : ℕ∞) * ∑ w ∈ lrows, ((deg w : ℕ∞) + 2) + 4 * ((cols.card : ℕ∞) + 1) * vδ +
        ∑ w ∈ qs, vζ w := by
  intro O _ _ _ A T' G _ _ _ _ d _ _ ρ _ _ _
  letI : Module A (d → KO O) := (inferInstance : Module A (LatQ O d ρ))
  letI : SMulCommClass A O (d → KO O) := (inferInstance : SMulCommClass A O (LatQ O d ρ))
  letI : Module T' (d → KO O) := (inferInstance : Module T' (LatQ O d ρ))
  letI : IsScalarTower T' A (d → KO O) := (inferInstance : IsScalarTower T' A (LatQ O d ρ))
  exact hOne O A T' G d

theorem character_column_kernels_of_block_chi_c_of_block_chi_one (hC : StatBlockChiCFull.{0, 0, 0, 0, 0, 0})
    (hOne : StatBlockChiOneFull.{0, 0, 0, 0, 0, 0}) : characterColumnKernelEqualityForm := by
  intro O _ _ _ X X' T T' Z p q b hspan hinj d _ _ R' _ hdet Tc _ _ _ _ G _ r χ E e₁ δ ι _ _
    colIdx hinjc D j e' Kc k0 hEE he₁ hpt g₀ n hn π' ρπ hρπ t ht bl hbl ρk hρk hblk _ _ _ hcard
    hcard1 sE tE δO ℓ cB what₂ qs lenRow deg vζ s vhE H0 Sha hE hk0 NNc cols eO vδ N h0
    hE0 hδ0 hτ0 he₁iso hlift hb0 hbc hb1
  have hEE' : E * E = δ • E := by rw [Algebra.smul_def]; exact hEE

  have hG : vcc T Z (p π') ≤ ∑ k ∈ univ.image bl, Module.length O (NNc →ₗ[R'] blockRestrictedRepresentationType bl ρk k) :=
    globalColumn O X X' T T' Z p q b hspan hinj d R' hdet Tc G r χ E e₁ δ ι
      (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0 hEE he₁ hpt g₀ n hn π' ρπ hρπ
      (Fin (t + 1)) bl hbl ρk hρk hblk hcard

  have hL0 : Module.length O (NNc →ₗ[R'] blockRestrictedRepresentationType bl ρk 0) ≤
      ∑ w ∈ what₂, lenRow w + ∑ w ∈ cols, ((j w : ℕ∞) * (eO * (e' w : ℕ∞) + vδ) + h0 w) + s +
        4 * N * ((cols.card : ℕ∞) + 1) * vδ := by
    obtain ⟨F, Q, h1, h2, h3, h4⟩ := hb0
    exact blockRhoLat O R' Tc G {a // bl a = 0} (ρk 0).toRingHom r χ E e₁ δ δO ι ℕ colIdx hinjc
      D j e' Kc k0 ℓ sE tE hE hEE' hE0 hk0 hδ0 hτ0 he₁iso hlift what₂ F lenRow Q s h1 h2 h3 h4

  have hlt : 1 < t + 1 := by omega
  have hL1 : Module.length O (NNc →ₗ[R'] blockRestrictedRepresentationType bl ρk ⟨1, hlt⟩) ≤
      vhE + ∑ w ∈ cols, (eO * (e' w : ℕ∞) + 2 * vδ) +
        eO * (cB : ℕ∞) * ∑ w ∈ what₂, ((deg w : ℕ∞) + 2) + 4 * ((cols.card : ℕ∞) + 1) * vδ +
        ∑ w ∈ qs, vζ w := by
    obtain ⟨hu, he10, hEδ, hδ1, hk1, F, Q, h1, h2, h3, h4, h5⟩ := hb1
    have hc1 : Fintype.card {a // bl a = ⟨1, hlt⟩} = 1 :=
      hcard1 ⟨1, hlt⟩ (fun h => by simpa using congrArg Fin.val h)
    exact blockChiOneLat hOne O R' Tc G {a // bl a = ⟨1, hlt⟩} (ρk ⟨1, hlt⟩).toRingHom
      r χ E e₁ δ δO ι ℕ colIdx hinjc D j e' Kc k0 ℓ cB hc1 hu he10 hEδ hδ1 hk1 what₂ qs F deg vζ Q
      vhE h1 h2 h3 h4 h5

  have hLc : ∀ c : Fin (t + 1), 2 ≤ (c : ℕ) → Module.length O (NNc →ₗ[R'] blockRestrictedRepresentationType bl ρk c) ≤
      Sha ((c : ℕ) - 1) + eO * (cB : ℕ∞) * ∑ w ∈ what₂, ((deg w : ℕ∞) + 2) +
        4 * ((cols.card : ℕ∞) + 1) * vδ + (cols.card : ℕ∞) * H0 + ∑ w ∈ qs, vζ w := by
    intro c hc
    obtain ⟨he10, hEc, hδc, hτc, hH0, F, Q, h1, h2, h3, h4, h5⟩ := hbc c hc
    have hcc : Fintype.card {a // bl a = c} = 1 :=
      hcard1 c (fun h => by rw [h] at hc; simp at hc)
    exact blockChiCLat hC O R' Tc G {a // bl a = c} (ρk c).toRingHom r χ E e₁ δ δO ι ℕ colIdx
      hinjc D j Kc k0 ℓ cB sE tE hcc hE hEE' he10 hEc hk0 hδc hτc what₂ qs F deg vζ Q
      (Sha ((c : ℕ) - 1)) H0 hH0 h1 h2 h3 h4 h5
  exact collectAlt t ht (fun k => Module.length O (NNc →ₗ[R'] blockRestrictedRepresentationType bl ρk k)) (univ.image bl)
    (vcc T Z (p π')) what₂ cols qs lenRow vζ h0 e' j deg Sha eO vδ s vhE N H0 cB hG hL0 hL1 hLc

theorem n5 : characterColumnKernelEqualityForm := character_column_kernels_of_block_chi_c_of_block_chi_one blockChiCFull blockChiOneFull

end Formalism.NG
