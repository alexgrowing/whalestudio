import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.PolygonSlopeSum
import Formalism.HarderNarasimhan.StatementCor

open Module Submodule

namespace Formalism.HN

theorem imageStep : ImageStep := by
  intro R ι W F _ _ _ _ _ _ V E _ _ _ _ _ ρ ρ' L M s φ C θ hL hM hC
  refine iSup₂_le fun i hi => ?_
  by_cases h0 : φ i = 0
  · simp [h0]
  · have hLi : L i ≠ ⊥ := by
      intro hb
      apply h0
      refine LinearMap.ext fun x => ?_
      have : x = 0 := Subtype.ext ((Submodule.eq_bot_iff _).1 hb x x.2)
      simp [this]
    have hN0 : (LinearMap.range (φ i)).map M.subtype ≠ ⊥ := by
      intro hb
      apply h0
      refine LinearMap.ext fun x => Subtype.ext ?_
      have hx : ((φ i x : M) : W) ∈ (LinearMap.range (φ i)).map M.subtype :=
        ⟨φ i x, ⟨x, rfl⟩, rfl⟩
      rw [hb, Submodule.mem_bot] at hx
      simp [hx]
    have hθ : θ ≤ muMin ρ' ((LinearMap.range (φ i)).map M.subtype) :=
      ((hC i hi).2.2 hLi).trans ((slopeIneq R (V i) W (E i) F (ρ i) ρ' (L i) M (hL i hi) hM (φ i)
        (C i) (hC i hi).1 (hC i hi).2.1).1 h0).1
    exact (hnStep_spec R W F ρ' M hM θ).2.2.1 _ (Submodule.map_subtype_le _ _) hN0 hθ

theorem hnCor : HNCor := by
  intro R V E _ _ _ _ _ _ ρ L hL
  have mono : ∀ N : Submodule R V, N ≤ L → N ≠ ⊥ → muMax ρ N ≤ muMax ρ L := by
    intro N hN hN0
    have hL0 : L ≠ ⊥ := fun h => hN0 (le_bot_iff.1 (h ▸ hN))
    have hNL := hnSum_isLat_mono ρ hL hN
    refine ((muChar R V E ρ N hNL hN0).1 (muMax ρ L)).2 fun N' hN' => ?_
    exact ((muChar R V E ρ L hL hL0).1 (muMax ρ L)).1 le_rfl N' (hN'.trans hN)
  refine ⟨?_, ?_, ?_, ?_, mono, ?_⟩
  · intro a b hab
    unfold hnStep
    exact sSup_le_sSup fun N ⟨h1, h2, h3⟩ => ⟨h1, h2, hab.trans h3⟩
  · intro hL0 θ
    constructor
    · intro h
      have h2 := (hnStep_spec R V E ρ L hL θ).2.1
      rw [h] at h2
      exact h2 hL0
    · intro hθ
      exact le_antisymm (hnStep_spec R V E ρ L hL θ).1.1
        ((hnStep_spec R V E ρ L hL θ).2.2.1 L le_rfl hL0 hθ)
  · intro θ hθ
    by_contra hne
    have sp := hnStep_spec R V E ρ L hL θ
    have h2 := sp.2.1 hne
    have hNL := hnSum_isLat_mono ρ hL sp.1.1
    have mc := muChar R V E ρ _ hNL hne
    have := mono _ sp.1.1 hne
    linarith [mc.2.2.2.1, mc.2.2.2.2]
  · intro t
    have h := (hnSlopes R V E ρ L hL).2.1 t
    have h2 := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin (rk ρ L)))) (p := fun j => slopeList ρ L j < t)
    simp only [not_lt, Finset.card_univ, Fintype.card_fin] at h2
    omega
  · intro N θ hN hN0 hθ
    have sp := hnStep_spec R V E ρ L hL θ
    rw [(hnSlopes R V E ρ L hL).2.1 θ]
    have := hL.2
    have hS := hnSum_isLat_mono ρ hL sp.1.1
    have := hS.2
    exact Formalism.F.att_rk_le (hnSum_zl_mono ρ (sp.2.2.1 N hN hN0 hθ))

end Formalism.HN
