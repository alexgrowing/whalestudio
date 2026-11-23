import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesKillsAvg
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesLabelMulOfConstituent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCuspidalListHarishChandraPairingNeZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterPairingHarishChandraCuspidalMackey
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetCharacterIrreducibleLabel

open GlobalTheory.GLq GlobalTheory.MirAvg Polynomial

noncomputable section

namespace GlobalTheory.GLq.DetRoot

open scoped Classical

variable {g : ℕ} [Fact g.Prime]

theorem ip_list_sum_left {G : Type} [Group G] [Fintype G] (L : List (G → ℂ)) (B : G → ℂ) :
    ip L.sum B = (L.map fun ρ => ip ρ B).sum := by
  induction L with
  | nil => simp [ip]
  | cons ρ L ih =>
    rw [List.sum_cons, List.map_cons, List.sum_cons, ← ih]
    unfold ip
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]

theorem list_nat_sum {G : Type} [Group G] [Fintype G] (L : List (G → ℂ)) (hL : ∀ ρ ∈ L, IsIrr ρ) (B : G → ℂ)
    (hB : IsChar B) : ∃ N : ℕ, (L.map fun ρ => ip ρ B).sum = N ∧ ∀ ρ ∈ L, ip ρ B ≠ 0 → N ≠ 0 := by
  induction L with
  | nil => exact ⟨0, by simp, by simp⟩
  | cons ρ L ih =>
    obtain ⟨N, hN, hN0⟩ := ih (fun σ hσ => hL σ (List.mem_cons_of_mem _ hσ))
    obtain ⟨k, hk⟩ := GlobalTheory.GLq.LabelMul.ip_nat (hL ρ List.mem_cons_self) hB
    refine ⟨k + N, by simp [hN, hk], ?_⟩
    intro σ hσ h0
    rcases List.mem_cons.1 hσ with rfl | hσ
    · rw [hk] at h0
      have : k ≠ 0 := by exact_mod_cast h0
      omega
    · have := hN0 σ hσ h0
      omega

theorem ip_ne_zero_of_common {G : Type} [Group G] [Fintype G] {ψ A B : G → ℂ} (hψ : IsIrr ψ) (hA : IsChar A)
    (hB : IsChar B) (hψA : ip ψ A ≠ 0) (hψB : ip ψ B ≠ 0) : ip A B ≠ 0 := by
  obtain ⟨L, hL, rfl⟩ := (GlobalTheory.T.character_decomposition_and_classFunction_expansion G A).1 hA
  rw [GlobalTheory.GLq.LabelMul.ip_sum_eq_count hψ L hL] at hψA
  have hm : ψ ∈ L := List.count_pos_iff.1 (Nat.pos_of_ne_zero (by exact_mod_cast hψA))
  obtain ⟨N, hN, hN0⟩ := list_nat_sum L hL B hB
  rw [ip_list_sum_left, hN]
  exact_mod_cast hN0 ψ hm hψB

theorem ip_add_ne_zero {G : Type} [Group G] [Fintype G] {ψ X Y : G → ℂ} (hψ : IsIrr ψ) (hX : IsChar X)
    (hY : IsChar Y) (h : ip ψ X ≠ 0) : ip ψ (X + Y) ≠ 0 := by
  rw [GlobalTheory.GLq.LabelMul.ip_add_right]
  obtain ⟨k, hk⟩ := GlobalTheory.GLq.LabelMul.ip_nat hψ hX
  obtain ⟨l, hl⟩ := GlobalTheory.GLq.LabelMul.ip_nat hψ hY
  rw [hk] at h
  have hk0 : k ≠ 0 := by exact_mod_cast h
  rw [hk, hl]
  exact_mod_cast (show k + l ≠ 0 by omega)

theorem isChar_hcL_cusp (K : List (Pc g)) (hK : ∀ p ∈ K, IsCusp p.2) (m : ℕ) (hm : degL K = m) :
    IsChar (hcL K m) :=
  (GlobalTheory.T.harishChandraProductList_isCharacter_and_perm_invariant g K K m hm.symm (fun p hp => GlobalTheory.GLq.IpCuspProd.isChar_of_isCusp (hK p hp))).1

theorem ip_hc_left (m : ℕ) (ψ : Gn g (m + 1) → ℂ) (hψ : IsIrr ψ) (σ : Gn g m → ℂ) (hσ : IsIrr σ)
    (β : Gn g 1 → ℂ) (hβ : IsChar β) (K : List (Pc g)) (hK : ∀ p ∈ K, IsCusp p.2) (hd : degL K = m)
    (hσK : ip σ (hcL K m) ≠ 0) (h : ip ψ (hc m 1 σ β (m + 1)) ≠ 0) : ip ψ (hc m 1 (hcL K m) β (m + 1)) ≠ 0 := by
  obtain ⟨R, hR, he⟩ := GlobalTheory.GLq.LabelMul.exists_add_of_ip_ne_zero hσ (isChar_hcL_cusp K hK m hd) hσK
  rw [he, GlobalTheory.GLq.LabelMul.hc_add_left]
  have hc := (GlobalTheory.T.harishChandra_induction_character_restriction_decomp g m 1 (m + 1) rfl).1
  exact ip_add_ne_zero hψ (hc σ β (GlobalTheory.GLq.LabelMul.isChar_of_isIrr hσ) hβ) (hc R β hR hβ) h

theorem ip_hc_right (m : ℕ) (ψ : Gn g (m + 1) → ℂ) (hψ : IsIrr ψ) (σ : Gn g m → ℂ) (hσ : IsIrr σ)
    (β : Gn g 1 → ℂ) (hβ : IsChar β) (K : List (Pc g)) (hK : ∀ p ∈ K, IsCusp p.2) (hd : degL K = m)
    (hσK : ip σ (hcL K m) ≠ 0) (h : ip ψ (hc 1 m β σ (m + 1)) ≠ 0) : ip ψ (hc 1 m β (hcL K m) (m + 1)) ≠ 0 := by
  obtain ⟨R, hR, he⟩ := GlobalTheory.GLq.LabelMul.exists_add_of_ip_ne_zero hσ (isChar_hcL_cusp K hK m hd) hσK
  rw [he, GlobalTheory.GLq.LabelMul.hc_add_right]
  have hc := (GlobalTheory.T.harishChandra_induction_character_restriction_decomp g 1 m (m + 1) (by omega)).1
  exact ip_add_ne_zero hψ (hc β σ hβ (GlobalTheory.GLq.LabelMul.isChar_of_isIrr hσ)) (hc β R hβ hR) h

theorem eq_of_isCuspOf_det (L : LabelDatum g) (θ : (ZMod g)ˣ →* ℂˣ) (c : ZMod g) (h : GlobalTheory.GLp.IsCharLab L θ c)
    (P : (ZMod g)[X])
    (hP : IsCuspOf L P (fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ))) : P = X - C c := by
  obtain ⟨⟨hm, -, h0, hdeg⟩, -, hf⟩ := hP
  have hPe : P = X - C (-P.coeff 0) := by
    rw [map_neg, sub_neg_eq_add]; exact hm.eq_X_add_C hdeg
  have hc'0 : -P.coeff 0 ≠ 0 := neg_ne_zero.2 h0
  obtain ⟨u, hu⟩ := GlobalTheory.GLq.LabelDet.gen_one_mem L
  let y : Gn g 1 := Units.map (Matrix.scalar (Fin 1) : ZMod g →+* Mt g 1).toMonoidHom u
  have hy00 : (y : Mt g 1) 0 0 = u := by simp [y]
  have hcp : (y : Mt g 1).charpoly = X - C ((y : Mt g 1) 0 0) := by
    simp [Matrix.charpoly, Matrix.det_fin_one]
  have hx : algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) (-P.coeff 0) ∈ Formalism.CyclotomicNorms.rootsBar P := by
    rw [hPe]; simp [Formalism.CyclotomicNorms.rootsBar]
  have hz : L.gen 1 ∈ Formalism.CyclotomicNorms.rootsBar (y : Mt g 1).charpoly := by
    rw [hcp, hy00, ← hu]; simp [Formalism.CyclotomicNorms.rootsBar]
  have hirr : Irreducible (y : Mt g 1).charpoly := by rw [hcp]; exact irreducible_X_sub_C _
  have key := hf _ hx y hirr _ hz
  have hxp : (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) (-P.coeff 0)) ^ (g ^ 1 - 1) = 1 := by
    rw [← map_pow, pow_one, ZMod.pow_card_sub_one_eq_one hc'0, map_one]
  have hth := GlobalTheory.GLq.LabelDet.theta_gen_pow L hxp 1
  rw [pow_one, pow_one] at hth
  have hdet : Matrix.GeneralLinearGroup.det y = u := by ext; simp [y, Matrix.det_fin_one]
  simp only [hdet, Nat.sub_self, pow_zero, one_mul, Finset.sum_range_one, pow_one, hth] at key
  rw [h.2 u hu] at key
  have := L.teich_inj _ _ ((_root_.map_ne_zero _).2 h.1) ((_root_.map_ne_zero _).2 hc'0) key
  rw [hPe, (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)).injective this]

end GlobalTheory.GLq.DetRoot

namespace GlobalTheory.GLq.DetRoot

open scoped Classical

theorem root_of_hc_det : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g) (n : ℕ) (ψ : Gn g (n + 1) → ℂ) (f : (ZMod g)[X]),
    IsIrr ψ → HasLabel L ψ f → ∀ (σ : Gn g n → ℂ), IsIrr σ → ∀ (θ : (ZMod g)ˣ →* ℂˣ) (c : ZMod g),
    GlobalTheory.GLp.IsCharLab L θ c →
    (ip ψ (hc n 1 σ (fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) (n + 1)) ≠ 0 → f.IsRoot c) ∧
    (ip ψ (hc 1 n (fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) σ (n + 1)) ≠ 0 → f.IsRoot c) := by
  intro g _ L n ψ f hψ hL σ hσ θ c hlab
  obtain ⟨Q, hQ, hQd, rfl, hQi⟩ := hL
  obtain ⟨K, hK, hKd, hKi⟩ := GlobalTheory.GLq.SuppCusp.exists_cusp_list g n σ hσ
  subst hKd
  have hβI : IsIrr (fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) :=
    GlobalTheory.GLq.LabelDet.isIrr_hom (θ.comp Matrix.GeneralLinearGroup.det)
  have hβC := GlobalTheory.GLq.LabelMul.isChar_of_isIrr hβI
  have hβcusp : IsCusp (fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) :=
    ⟨one_pos, hβI, fun a h1 h2 => by omega⟩
  have hQc : ∀ p ∈ Q.map Prod.snd, IsCusp p.2 := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    exact (hQ q hq).2.1
  have hA := isChar_hcL_cusp _ hQc _ hQd

  have fin : ∀ K' : List (Pc g), (Q.map Prod.snd).Perm K' →
      (⟨1, fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)⟩ : Pc g) ∈ K' →
      ((Q.map Prod.fst).prod).IsRoot c := by
    intro K' hp hm
    obtain ⟨⟨P, s⟩, hq, hs⟩ := List.mem_map.1 (hp.mem_iff.2 hm)
    dsimp only at hs
    subst hs
    have hP := eq_of_isCuspOf_det L θ c hlab P (hQ _ hq)
    have hdvd : P ∣ (Q.map Prod.fst).prod := List.dvd_prod (List.mem_map.2 ⟨_, hq, rfl⟩)
    exact Polynomial.IsRoot.dvd (by rw [hP]; exact root_X_sub_C.2 rfl) hdvd
  have hbc : ∀ p ∈ [(⟨1, fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)⟩ : Pc g)], IsCusp p.2 := by
    intro p hp
    rw [List.mem_singleton] at hp
    subst hp
    exact hβcusp
  have hKc := fun p hp => GlobalTheory.GLq.IpCuspProd.isChar_of_isCusp (hK p hp)
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h2 := ip_hc_left _ ψ hψ σ hσ _ hβC K hK rfl hKi h
    have e2 : hc (degL K) 1 (hcL K (degL K))
        (hcL [(⟨1, fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)⟩ : Pc g)] 1) (degL K + 1) =
        hcL (K ++ [(⟨1, fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)⟩ : Pc g)]) (degL K + 1) :=
      (GlobalTheory.GLq.LabelMul.hcL_append K _ hKc (fun p hp => GlobalTheory.GLq.IpCuspProd.isChar_of_isCusp (hbc p hp))
        (degL K + 1) (by simp [degL])).symm
    rw [GlobalTheory.GLq.IpCuspProd.hcL_single 1 _ (GlobalTheory.GLq.IpCuspProd.isClass_of_isChar hβC)] at e2
    rw [e2] at h2
    have hKd' : degL (K ++ [(⟨1, fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)⟩ : Pc g)]) =
        degL K + 1 := by simp [degL]
    have hB := isChar_hcL_cusp _ (fun p hp => by
      rcases List.mem_append.1 hp with hp | hp
      · exact hK p hp
      · exact hbc p hp) _ hKd'
    have hAB := ip_ne_zero_of_common hψ hA hB hQi h2
    refine fin (K ++ [(⟨1, fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)⟩ : Pc g)]) ?_
      (List.mem_append.2 (Or.inr (List.mem_singleton.2 rfl)))
    by_contra hn
    exact hAB ((GlobalTheory.GLq.IpCuspProd.ip_hcL_cusp g _ _ _ hQd hKd' hQc (fun p hp => by
      rcases List.mem_append.1 hp with hp | hp
      · exact hK p hp
      · exact hbc p hp)).1 hn)
  · have h2 := ip_hc_right _ ψ hψ σ hσ _ hβC K hK rfl hKi h
    have e2 : hc 1 (degL K) (fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) (hcL K (degL K))
        (degL K + 1) =
        hcL ((⟨1, fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)⟩ : Pc g) :: K) (degL K + 1) :=
      (hcL_cons (⟨1, fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)⟩ : Pc g) K (degL K + 1)).symm
    rw [e2] at h2
    have hKd' : degL ((⟨1, fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)⟩ : Pc g) :: K) =
        degL K + 1 := by simp [degL]; omega
    have hKc' : ∀ p ∈ (⟨1, fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)⟩ : Pc g) :: K,
        IsCusp p.2 := by
      intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact hβcusp
      · exact hK p hp
    have hB := isChar_hcL_cusp _ hKc' _ hKd'
    have hAB := ip_ne_zero_of_common hψ hA hB hQi h2
    refine fin ((⟨1, fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)⟩ : Pc g) :: K) ?_
      List.mem_cons_self
    by_contra hn
    exact hAB ((GlobalTheory.GLq.IpCuspProd.ip_hcL_cusp g _ _ _ hQd hKd' hQc hKc').1 hn)

end GlobalTheory.GLq.DetRoot
