import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBaryStageStart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfToRealRel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStarSubdivisionInvariantPolyhedralFanStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MarkedFormIndicatorZeroOneBarycentresPolyFanStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolyFanFaceCutByIntLinearFormIsCellStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntLinearFormCuttingSubcellStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarrierDimLeOfAddCellGeneratorsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionBarycentreCellNextStageStatement

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

noncomputable section

namespace GlobalTheory.PolFan

section Helpers

variable {X : Type} [AddCommGroup X]

theorem inRCone_append_left {b a : ℕ} (v : Fin b → LinearMap.BilinForm ℤ X) (u : Fin a → LinearMap.BilinForm ℤ X)
    {β : LinearMap.BilinForm ℤ X} (h : InRCone v β) : InRCone (Fin.append v u) β :=
  inRCone_trans (fun k => by simpa using inRCone_self (Fin.append v u) (Fin.castAdd a k)) h

theorem inRCone_cons_of {n m : ℕ} (β₀ : LinearMap.BilinForm ℤ X) {F : Fin m → LinearMap.BilinForm ℤ X}
    {β : LinearMap.BilinForm ℤ X} (h : InRCone F β) : InRCone (Fin.cons β₀ F : Fin (m + 1) → _) β :=
  inRCone_trans (fun k => by simpa using inRCone_self (Fin.cons β₀ F : Fin (m + 1) → _) k.succ) h

theorem inRCone_cons_mono {n m : ℕ} (β₀ : LinearMap.BilinForm ℤ X) {F : Fin m → LinearMap.BilinForm ℤ X}
    {δ : Fin n → LinearMap.BilinForm ℤ X} (h : ∀ k, InRCone F (δ k)) :
    ∀ k, InRCone (Fin.cons β₀ F : Fin (m + 1) → _) ((Fin.cons β₀ δ : Fin (n + 1) → _) k) := by
  intro k
  refine Fin.cases ?_ (fun k => ?_) k
  · simpa using inRCone_self (Fin.cons β₀ F : Fin (m + 1) → _) 0
  · simpa using inRCone_cons_of (n := n) β₀ (h k)

theorem inRCone_comp_of {m m' : ℕ} {G : Fin m → LinearMap.BilinForm ℤ X} (s : Fin m' ↪ Fin m) {c : Fin m → ℝ}
    (hc : ∀ j, 0 ≤ c j) {β : LinearMap.BilinForm ℤ X} (hβ : toReal β = ∑ j, c j • toReal (G j))
    (h0 : ∀ j, j ∉ Set.range s → c j = 0) : InRCone (fun l => G (s l)) β := by
  refine ⟨fun l => c (s l), fun l => hc _, ?_⟩
  rw [hβ]
  symm
  exact Fintype.sum_of_injective s s.injective _ _ (fun j hj => by rw [h0 j hj, zero_smul]) fun l => rfl

theorem coeff_eq_zero_of_apply {m : ℕ} {G : Fin m → LinearMap.BilinForm ℤ X} {c : Fin m → ℝ} (hc : ∀ j, 0 ≤ c j)
    {β : LinearMap.BilinForm ℤ X} (hβ : toReal β = ∑ j, c j • toReal (G j)) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ)
    (hG : ∀ j, 0 ≤ h (G j)) (h0 : h β = 0) (j : Fin m) (hj : h (G j) ≠ 0) : c j = 0 := by
  have e := apply_eq_of_toReal_eq hβ h
  rw [h0, Int.cast_zero] at e
  have hnn : ∀ j ∈ Finset.univ, 0 ≤ c j * (h (G j) : ℝ) := fun j _ => mul_nonneg (hc j) (by exact_mod_cast hG j)
  have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 e.symm j (Finset.mem_univ _)
  exact (mul_eq_zero.1 this).resolve_right (by exact_mod_cast hj)

theorem exists_faceCut {m : ℕ} (G : Fin m → LinearMap.BilinForm ℤ X) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ)
    (hG : ∀ j, 0 ≤ h (G j)) : ∃ (m' : ℕ) (s : Fin m' ↪ Fin m), IsFaceCut G s h := by
  classical
  let S := Finset.univ.filter fun j => h (G j) = 0
  refine ⟨S.card, (S.orderEmbOfFin rfl).toEmbedding, hG, fun j => ?_⟩
  have : Set.range (S.orderEmbOfFin rfl).toEmbedding = (S : Set (Fin m)) := by
    simp [Finset.range_orderEmbOfFin]
  rw [this]
  simp [S]

end Helpers

section Reduce

variable {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
  [Module.Finite O X]

theorem reduce_of_not_mem {m n : ℕ} {G : Fin m → LinearMap.BilinForm ℤ X} {γ : Fin n → LinearMap.BilinForm ℤ X}
    (hG : IsCell bar φ G) (hγ : IsCell bar φ γ) (hcov : ∀ k, InRCone G (γ k)) {β₀ : LinearMap.BilinForm ℤ X}
    (hb : β₀ ∈ balForms bar X) (hp : ∀ y, 0 ≤ β₀ y y) (hin : InRCone G β₀) (hnin : ¬ InRCone γ β₀) :
    ∃ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut G s h ∧ 0 < h β₀ ∧
      ∀ k, InRCone (fun l => G (s l)) (γ k) := by
  obtain ⟨h, hh1, hh2, hh3⟩ := GlobalTheory.T.exists_intLinearForm_cutting_subcell O bar φ X m n G γ hG hγ hcov
  obtain ⟨m', s, hs⟩ := exists_faceCut G h hh1
  refine ⟨m', s, h, hs, ?_, fun k => ?_⟩
  · rcases (hin.apply_nonneg h hh1).eq_or_lt with e | e
    · exact (hnin (hh3 β₀ hb hp hin e.symm)).elim
    · exact e
  · obtain ⟨c, hc, e⟩ := hcov k
    exact inRCone_comp_of s hc e fun j hj =>
      coeff_eq_zero_of_apply hc e h hh1 (hh2 k) j fun h0 => hj ((hs.2 j).1 h0)

theorem reduce_of_mem {m n n' : ℕ} {G : Fin m → LinearMap.BilinForm ℤ X} {δ : Fin n → LinearMap.BilinForm ℤ X}
    (hG : IsCell bar φ G) (hδ : IsCell bar φ δ) (hcov : ∀ k, InRCone G (δ k)) {β₀ : LinearMap.BilinForm ℤ X}
    (hin : InRCone δ β₀) {s : Fin n' ↪ Fin n} {h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ} (hcut : IsFaceCut δ s h)
    (hpos : 0 < h β₀) :
    ∃ (m' : ℕ) (s' : Fin m' ↪ Fin m) (h' : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut G s' h' ∧ 0 < h' β₀ ∧
      ∀ k, InRCone (fun l => G (s' l)) (δ (s k)) := by
  obtain ⟨h₁, hh1, hh2, hh3⟩ := GlobalTheory.T.exists_intLinearForm_cutting_subcell O bar φ X m n G δ hG hδ hcov
  set K : ℤ := 1 + ∑ j, |h (G j)| with hK
  have hKj : ∀ j, |h (G j)| < K := fun j => by
    have := Finset.single_le_sum (f := fun j => |h (G j)|) (fun j _ => abs_nonneg _) (Finset.mem_univ j)
    linarith
  let h' : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ := K • h₁ + h
  have hv : ∀ β, h' β = K * h₁ β + h β := fun β => rfl
  have hnn : ∀ j, 0 ≤ h' (G j) := fun j => by
    rw [hv]
    rcases (hh1 j).eq_or_lt with e | e
    · rw [← e, mul_zero, zero_add]
      exact (hh3 _ (hG.mem j) (hG.nonneg j) (inRCone_self G j) e.symm).apply_nonneg h hcut.1
    · have h1 : 1 ≤ h₁ (G j) := e
      have := hKj j
      have h2 : -K < h (G j) := by have := neg_abs_le (h (G j)); linarith
      have hK0 : 0 < K := lt_of_le_of_lt (abs_nonneg _) (hKj j)
      have h3 : K ≤ K * h₁ (G j) := le_mul_of_one_le_right hK0.le h1
      linarith
  obtain ⟨m', s', hs'⟩ := exists_faceCut G h' hnn
  have hz : ∀ β, InRCone δ β → h₁ β = 0 := fun β hβ => by
    obtain ⟨c, _, e⟩ := hβ
    have := apply_eq_of_toReal_eq e h₁
    simp only [hh2, Int.cast_zero, mul_zero, Finset.sum_const_zero] at this
    exact_mod_cast this
  refine ⟨m', s', h', hs', by rw [hv, hz β₀ hin, mul_zero, zero_add]; exact hpos, fun k => ?_⟩
  obtain ⟨c, hc, e⟩ := hcov (s k)
  have h0 : h' (δ (s k)) = 0 := by
    rw [hv, hz _ (inRCone_self δ _), mul_zero, zero_add]
    exact (hcut.2 _).2 ⟨k, rfl⟩
  exact inRCone_comp_of s' hc e fun j hj => coeff_eq_zero_of_apply hc e h' hnn h0 j fun h0 => hj ((hs'.2 j).1 h0)

end Reduce

theorem baryStep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ lab φ : InvFun (𝓞 E)) (i : ℕ), (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) → IsPolyFan H.bar q ψ → IsTwInv H ψ → IsTwInv H lab → IsCarrierDim H.bar q ψ lab → IsTwInv H φ → IsBaryStage H.bar q ψ lab φ (i + 1) → ∃ φ' : InvFun (𝓞 E), IsTwInv H φ' ∧ IsBaryStage H.bar q ψ lab φ' i := by
  intro E _ _ _ H q ψ lab φ i hdom hψ hψt hlt hcar hφt hst
  obtain ⟨w, hwt, hw⟩ := GlobalTheory.T.markedFormIndicator_zeroOne_barycentres_polyFan E H q ψ lab i hdom hψ hψt hlt hcar
  obtain ⟨hφp, hφs, hφc⟩ := hst
  have hcen : IsCentreSet H.bar q φ w := by
    intro X _ _ _ _ hX
    obtain ⟨h1, h2, h3, h4, -⟩ := hw X hX
    refine ⟨h1, h2, fun m γ hγ β hβ hp β' hβ' hp' hw1 hw2 hc hc' => ?_⟩
    obtain ⟨b, a, v, u, -, hv, hcov, -, -, hvl, hoff, -⟩ := hφc X hX m γ hγ
    have inv : ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 1 → InRCone γ β → InRCone v β := by
      intro β hβ hp hw1 hc
      by_contra hn
      have := hoff β hβ hp (inRCone_trans hcov hc) hn
      rw [h3 β hβ hp hw1] at this
      exact lt_irrefl _ this
    exact h4 b v hv hvl β hβ hp β' hβ' hp' hw1 hw2 (inv β hβ hp hw1 hc) (inv β' hβ' hp' hw2 hc')
  obtain ⟨φ', hp', ht', hsub, hs1, hs2, hs3⟩ := GlobalTheory.T.exists_starSubdivision_invariant_polyhedral_fan E H q φ w hdom hφp hφt hwt hcen
  refine ⟨φ', ht', hp', hsub.trans hφs, fun X _ _ _ _ hX n γ' hγ' => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := hw X hX
  have hnat : ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → ∃ n : ℕ, lab.evalZ β = n :=
    fun β hβ hp => ⟨_, hcar X hX β hβ hp⟩
  have core : ∀ (b a : ℕ) (v : Fin b → LinearMap.BilinForm ℤ X) (u : Fin a → LinearMap.BilinForm ℤ X),
      IsCell H.bar φ (Fin.append v u) → IsCell H.bar ψ v → Function.Injective (fun j => lab.evalZ (u j)) →
      (∀ j, ((i + 1 : ℕ) : ℝ) < lab.evalZ (u j)) →
      (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone v β → lab.evalZ β ≤ ((i + 1 : ℕ) : ℝ)) →
      (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone (Fin.append v u) β → ¬ InRCone v β →
        ((i + 1 : ℕ) : ℝ) < lab.evalZ β) →
      (∀ (d : Fin b → ℤ) (c : Fin a → ℤ), ∑ j, c j • u j = ∑ k, d k • v k → c = 0) →
      ∀ β₀ ∈ balForms H.bar X, (∀ y, 0 ≤ β₀ y y) → w.evalZ β₀ = 1 → InRCone (Fin.append v u) β₀ →
      ∀ (m' : ℕ) (s : Fin m' ↪ Fin (b + a)) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ),
        IsFaceCut (Fin.append v u) s h → 0 < h β₀ →
      ∃ (b' a' : ℕ) (v' : Fin b' → LinearMap.BilinForm ℤ X) (u' : Fin a' → LinearMap.BilinForm ℤ X),
        IsCell H.bar φ' (Fin.append v' u') ∧ IsCell H.bar ψ v' ∧
        (∀ k, InRCone (Fin.append v' u') ((Fin.cons β₀ fun j => Fin.append v u (s j) : Fin (m' + 1) → _) k)) ∧
        Function.Injective (fun j => lab.evalZ (u' j)) ∧ (∀ j, (i : ℝ) < lab.evalZ (u' j)) ∧
        (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone v' β → lab.evalZ β ≤ i) ∧
        (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone (Fin.append v' u') β → ¬ InRCone v' β →
          (i : ℝ) < lab.evalZ β) ∧
        ∀ (d : Fin b' → ℤ) (c : Fin a' → ℤ), ∑ j, c j • u' j = ∑ k, d k • v' k → c = 0 := by
    intro b a v u hγ hv hinj hlu hvl hoff hind β₀ hb0 hp0 hw0 hin0
    exact GlobalTheory.T.starSubdivision_barycentre_cell_next_stage (𝓞 E) H.bar ψ lab φ' w i X b a v u hv hinj hlu hvl hoff hind hnat
      (fun m' s h hh => GlobalTheory.T.polyFan_face_cut_by_intLinearForm_isCell E H q ψ hψ X hX (hdom X) b v hv m' s h hh) h5
      (fun β hβ hp β' hβ' hp' hw1 hw2 hc hc' => (hcen X hX).2.2 _ _ hγ β hβ hp β' hβ' hp' hw1 hw2 hc hc')
      (fun β₀ hb0 hp0 β hβ hp hin c₀ c hc₀ hc e =>
        GlobalTheory.T.carrierDim_le_of_add_cell_generators (𝓞 E) H.bar q ψ lab hcar X hX b v hv β₀ hb0 hp0 β hβ hp hin c₀ c hc₀ hc e)
      β₀ hb0 hp0 hw0 (h3 β₀ hb0 hp0 hw0) hin0
      (fun m' s h hh hpos => hs2 X hX _ _ hγ β₀ hb0 hp0 hw0 hin0 m' s h hh hpos)
  rcases hs3 X hX n γ' hγ' with ⟨m, γ, hγ, hno, hcov'⟩ | ⟨m, δ, β₀, m', s, h, hδ, hb0, hp0, hw0, hin0, hcut, hpos, hcov'⟩
  · obtain ⟨b, a, v, u, hG, hv, hcov, hinj, hlu, hvl, hoff, hind⟩ := hφc X hX m γ hγ
    by_cases hc : ∃ β₀ ∈ balForms H.bar X, (∀ y, 0 ≤ β₀ y y) ∧ w.evalZ β₀ = 1 ∧ InRCone (Fin.append v u) β₀
    · obtain ⟨β₀, hb0, hp0, hw0, hin0⟩ := hc
      have hnin : ¬ InRCone γ β₀ := fun hh => by
        have := hno β₀ hb0 hp0 hh
        rw [hw0] at this
        exact one_ne_zero this
      obtain ⟨m', s, h, hcut, hpos, hsub'⟩ := reduce_of_not_mem hG hγ hcov hb0 hp0 hin0 hnin
      obtain ⟨b', a', v', u', r1, r2, r3, r4, r5, r6, r7, r8⟩ :=
        core b a v u hG hv hinj hlu hvl hoff hind β₀ hb0 hp0 hw0 hin0 m' s h hcut hpos
      exact ⟨b', a', v', u', r1, r2, fun j => inRCone_trans r3 (inRCone_cons_of (n := 0) β₀
        (inRCone_trans hsub' (hcov' j))), r4, r5, r6, r7, r8⟩
    · push_neg at hc
      have hw0 : ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone (Fin.append v u) β → w.evalZ β = 0 :=
        fun β hβ hp hin => (h1 β hβ hp).resolve_right fun e => hc β hβ hp e hin
      refine ⟨b, a, v, u, hs1 X hX _ _ hG hw0, hv, fun j => inRCone_trans hcov (hcov' j), hinj,
        fun j => ?_, fun β hβ hp hin => ?_, fun β hβ hp hin hn => ?_, hind⟩
      · have := hlu j; push_cast at this ⊢; linarith
      · obtain ⟨k, hk⟩ := hnat β hβ hp
        have hle := hvl β hβ hp hin
        rw [hk] at hle ⊢
        have hle' : k ≤ i + 1 := by exact_mod_cast hle
        rcases hle'.lt_or_eq with hl | hl
        · exact_mod_cast Nat.lt_succ_iff.1 hl
        · obtain ⟨β₁, hb1, hp1, hw1, hin1⟩ := h5 b v hv β hβ hp hin (by rw [hk, hl])
          exact absurd (inRCone_append_left v u hin1) (hc β₁ hb1 hp1 hw1)
      · have := hoff β hβ hp hin hn; push_cast at this ⊢; linarith
  · obtain ⟨b, a, v, u, hG, hv, hcov, hinj, hlu, hvl, hoff, hind⟩ := hφc X hX m δ hδ
    obtain ⟨m'', s', h', hcut', hpos', hsub'⟩ := reduce_of_mem hG hδ hcov hin0 hcut hpos
    obtain ⟨b', a', v', u', r1, r2, r3, r4, r5, r6, r7, r8⟩ :=
      core b a v u hG hv hinj hlu hvl hoff hind β₀ hb0 hp0 hw0 (inRCone_trans hcov hin0) m'' s' h' hcut' hpos'
    exact ⟨b', a', v', u', r1, r2, fun j => inRCone_trans r3 (inRCone_trans (inRCone_cons_mono β₀ hsub') (hcov' j)),
      r4, r5, r6, r7, r8⟩

end GlobalTheory.PolFan
