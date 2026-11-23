import Formalism.WachLatticeTwists.HodgeTateChains.XiAdicFiltrationData
import Formalism.WachLatticeTwists.HodgeTateChains.HodgeTateFiltrations.Imports

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic

theorem twistKill : StatTwistKill := by
  intro ℓ _ u s hs h2 hu j hj E T ⟨hI1, hI2⟩ hT4 hT3 y
  obtain ⟨hne, hval⟩ := Formalism.WindowSums.valuation_zpow_sub_one ℓ u s hs h2 hu j hj
  obtain ⟨a, x, hax⟩ := (hI1 ((ℓ : ℤ_[ℓ]) • y)).1 (by rw [map_smul]; exact hT4 _)
  obtain ⟨c, hu'⟩ : ∃ c : ℤ_[ℓ]ˣ, (((u ^ j : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1)
      = (c : ℤ_[ℓ]) * (ℓ : ℤ_[ℓ]) ^ (s + padicValInt ℓ j) := by
    have h := PadicInt.unitCoeff_spec hne
    rw [hval] at h
    exact ⟨_, h⟩
  have h4 : T.infm (((ℓ : ℤ_[ℓ]) ^ (s + padicValInt ℓ j)) • a) + T.infX (((ℓ : ℤ_[ℓ]) ^ (s + padicValInt ℓ j)) • x) = 0 := by
    apply (hI2 _ _).2
    constructor
    · refine ⟨((c⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • a, ?_⟩
      have h5 : ∀ (t : ℤ_[ℓ]) (v : T.Wm), t • v - v = (t - 1) • v := by
        intro t v; rw [sub_smul, one_smul]
      rw [h5, smul_smul]
      conv_rhs => rw [hu', mul_right_comm, Units.mul_inv, one_mul]
    · obtain ⟨x'', hx''⟩ := hT3 x
      refine ⟨((ℓ : ℤ_[ℓ]) ^ (s + padicValInt ℓ j - 1)) • x'', ?_⟩
      rw [map_smul, ← smul_sub, ← hx'', smul_smul, ← pow_succ, Nat.sub_add_cancel (by omega)]
  have h6 : 1 + s + padicValInt ℓ j = (s + padicValInt ℓ j) + 1 := by ring
  rw [h6, pow_succ, mul_smul, hax, smul_add, ← map_smul, ← map_smul]
  exact h4

theorem kill3 : StatKill3 := by
  intro ℓ _ u s hs h2 hu e K ⟨h0, hex, htw⟩ x
  refine killSum ℓ (fun k => K.H k) (fun k => K.Gr k) K.f K.p
    (fun k => 1 + s + padicValNat ℓ (e - k)) e h0 hex (fun k hk y => ?_) x
  obtain ⟨hI, hT4, hT3⟩ := htw k hk
  have h := twistKill ℓ u s hs h2 hu ((k : ℤ) - e) (by omega) (K.Gr k) (K.tw k) hI hT4 hT3 y
  have hv : padicValInt ℓ ((k : ℤ) - e) = padicValNat ℓ (e - k) := by
    unfold padicValInt
    congr 1
    omega
  rw [hv] at h
  exact h

theorem free3 : StatFree3 := by
  intro ℓ _ N G HB T b La0 ⟨hI1, hI2⟩ hT4 hT3 htf hlog x
  obtain ⟨a, y, hay⟩ := (hI1 ((ℓ : ℤ_[ℓ]) • x)).1 (by rw [map_smul]; exact hT4 _)
  obtain ⟨y', hy'⟩ := hT3 y
  have h1 : T.infX ((ℓ : ℤ_[ℓ]) • y) = 0 := by
    have := (hI2 0 ((ℓ : ℤ_[ℓ]) • y)).2 ⟨⟨0, by simp⟩, y', hy'⟩
    rw [map_zero, zero_add] at this
    exact this
  have h2 : b (T.infX y) = 0 := htf _ (by rw [← map_smul, ← map_smul, h1, map_zero])
  have h3 : (ℓ : ℤ_[ℓ]) • b x = b (T.infm a) := by rw [← map_smul, hay, map_add, h2, add_zero]
  rw [add_comm, pow_succ, mul_smul, h3]
  exact hlog a

theorem tbFull : StatTBFull := by
  intro ℓ _ u w s m e d hs h2 hsm hu hw U D L K T φ ψ hd hP hLES hT5 hCR hK hTI hT4 hT3 htf hlog
    hC hL hdR hH2 hR hCor
  have hℓ : ℓ.Prime := Fact.out
  have hLL := ll ℓ w m (by omega) (fun h => le_trans (h2 h) hsm) hw U 0 (e + 1) (ℓ ^ (m - s)) L
    (pow_ne_zero _ hℓ.ne_zero) hP hLES hT5 hCR
  have hcast : (0 : ℤ) + ((e + 1 : ℕ) : ℤ) = (e : ℤ) + 1 := by push_cast; ring
  rw [hcast] at hLL
  have hLL' : TorsKilled ℓ D.HYL (cLL ℓ m U 0 ((e : ℤ) + 1) (ℓ ^ (m - s))) := fun x ⟨k, hk⟩ =>
    φ.injective (by
      rw [map_smul, map_zero]
      exact hLL _ ⟨k, by rw [← map_smul, hk, map_zero]⟩)
  have hK3 : D.Kill3 s e := fun x =>
    ψ.injective (by rw [map_smul, map_zero]; exact kill3 ℓ u s hs h2 hu e K hK _)
  have hF3 : D.Free3 s e := fun x => by
    have h := free3 ℓ (s + ceilE ℓ e) D.HGe D.HB T (D.bW ∘ₗ D.gE) D.La0 hTI hT4 hT3 htf hlog x
    rw [← add_assoc] at h
    exact h
  exact tb ℓ s m e d U D hd hC hL hdR hLL' hH2 hK3 hF3 hR hCor

end Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic
