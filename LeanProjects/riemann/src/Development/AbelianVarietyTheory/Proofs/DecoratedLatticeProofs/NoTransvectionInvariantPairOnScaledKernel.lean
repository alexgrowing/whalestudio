import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneAtOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
open IsLocalRing

noncomputable section
namespace GlobalTheory.LatPair

theorem no_pair_on_scaled_kernel : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (i : n) (P : GlobalTheory.LatPair.Pair k n) (c : k), 3 ≤ Fintype.card n → c ≠ 0 → (∀ x : n → k, x ∈ P.lat ↔ (∀ j, c⁻¹ * x j ∈ 𝒪[k]) ∧ ∃ s : 𝒪[k], s ∈ IsLocalRing.maximalIdeal 𝒪[k] ∧ (s : k) = c⁻¹ * x i) → (∀ (x : n → k) (a : 𝓀[k]), P.HasVal x a → ∀ (b d : n) (t : 𝒪[k]), b ≠ d → (b ≠ i ∨ t ∈ IsLocalRing.maximalIdeal 𝒪[k]) → P.HasVal (x + Pi.single b ((t : k) * x d)) a) → False := by
  intro k _ _ _ _ n _ _ i P c hn hc hlat hcl
  have hmem : ∀ b, b ≠ i → Pi.single b c ∈ P.lat := by
    intro b hb
    rw [hlat]
    refine ⟨fun j => ?_, ⟨0, zero_mem _, ?_⟩⟩
    · by_cases h : j = b
      · subst h; simp [hc]
      · rw [Pi.single_eq_of_ne h]; simp
    · rw [Pi.single_eq_of_ne (Ne.symm hb)]; simp
  have hzero : ∀ a, a ≠ i → P.HasVal (Pi.single a c) 0 := by
    intro a ha
    obtain ⟨d, hda, hdi⟩ : ∃ d, d ≠ a ∧ d ≠ i := by
      by_contra h
      push_neg at h
      have hsub : (Finset.univ : Finset n) ⊆ {a, i} := fun d _ => by
        by_cases hd : d = a
        · simp [hd]
        · simp [h d hd]
      have h1 := Finset.card_le_card hsub
      have h2 : ({a, i} : Finset n).card ≤ 2 := Finset.card_le_two
      rw [Finset.card_univ] at h1
      omega
    obtain ⟨v, hv⟩ := (Pair.mem_lat_iff (P := P)).1 (hmem d hdi)
    obtain ⟨w, hw⟩ := (Pair.mem_lat_iff (P := P)).1 (hmem a ha)
    have h1 := hcl _ _ hv a d 1 (Ne.symm hda) (Or.inl ha)
    have hx : (Pi.single d c + Pi.single a (((1 : 𝒪[k]) : k) * (Pi.single d c : n → k) d) : n → k) = Pi.single d c + Pi.single a c := by
      simp
    rw [hx] at h1
    have h3 := h1.unique (hv.add hw)
    have hw0 : w = 0 := by linear_combination -h3
    exact hw0 ▸ hw
  obtain ⟨a, ha⟩ : ∃ a, a ≠ i := by
    by_contra h
    push_neg at h
    have : Fintype.card n ≤ 1 := Fintype.card_le_one_iff.2 (fun x y => (h x).trans (h y).symm)
    omega
  have hzi : ∀ t : 𝒪[k], t ∈ IsLocalRing.maximalIdeal 𝒪[k] → P.HasVal (Pi.single i ((t : k) * c)) 0 := by
    intro t ht
    have h1 := hcl _ _ (hzero a ha) i a t (Ne.symm ha) (Or.inr ht)
    rw [Pi.single_eq_same] at h1
    simpa using h1.sub (hzero a ha)
  apply P.fn_ne
  ext ⟨x, hx⟩
  obtain ⟨hxj, s, hs, hsx⟩ := (hlat x).1 hx
  have hsing : ∀ b, P.HasVal (Pi.single b (x b)) 0 := by
    intro b
    by_cases hb : b = i
    · subst hb
      have he : (s : k) * c = x b := by rw [hsx]; field_simp
      simpa [he] using hzi s hs
    · have h := (hzero b hb).smul ⟨c⁻¹ * x b, hxj b⟩
      have he : (⟨c⁻¹ * x b, hxj b⟩ : 𝒪[k]) • (Pi.single b c : n → k) = Pi.single b (x b) := by
        rw [← Pi.single_smul']; congr 1; change (c⁻¹ * x b) * c = x b; field_simp
      simpa [he] using h
  have hsum : P.HasVal (∑ b, Pi.single b (x b)) 0 :=
    Finset.sum_induction _ (fun y => P.HasVal y 0) (fun _ _ h h' => by simpa using h.add h')
      ⟨P.lat.zero_mem, map_zero P.fn⟩ (fun b _ => hsing b)
  rw [Finset.univ_sum_single] at hsum
  rw [LinearMap.zero_apply]
  exact hsum.2

end GlobalTheory.LatPair
