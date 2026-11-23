import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.CcDualWtAnti

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.LatticeSystems Formalism.GradedWeylDivisibility

section

variable {p n' : ℕ} {R : RS p n'} {m : ℕ}

theorem cc_elem (X : Fin n' → Fin (m + 1) → ℤ) (e : Edge R.W R.Qq (m + 1))
    (G : Fin n' → Matrix (Fin (m + 1)) (Fin (m + 1)) R.Kf)
    (hs : (fun s : Fin n' => extO R.O R.ι R.σ s.val e.src) = famD R.O G 1)
    (hle : (fun s : Fin n' => LeAt p R.ι R.σ R.w s.val e) = famD R.O G (algebraMap R.O R.Kf R.w))
    (x : Vsp R.Kf X) (h1 : ((1 : R.Kf) ^ Ar 1 X) • x ∈ toV X (Hten R.O X (famD R.O G 1)))
    (hw : ((algebraMap R.O R.Kf R.w) ^ Ar 1 X) • x ∈ toV X (Hten R.O X (famD R.O G (algebraMap R.O R.Kf R.w)))) :
    x ∈ HL (O := R.O) R.ι R.σ X e.src ∧ x ∈ Re p R.ι R.σ R.w 1 X e := by
  constructor
  · show x ∈ toV X (Hten R.O X (fun s : Fin n' => extO R.O R.ι R.σ s.val e.src))
    rw [hs]
    rwa [one_zpow, one_smul] at h1
  · refine (cc_mem_scale (zpow_ne_zero _ R.w_ne)).2 ?_
    rw [zpow_neg, inv_inv]
    show _ ∈ toV X (Hten R.O X (fun s : Fin n' => LeAt p R.ι R.σ R.w s.val e))
    rw [hle]
    exact hw

end

theorem restCloudMaps_of (h : RestCloudLat) (hIncl : DualHeightInclusion) : RestCloudMaps := by
  classical
  intro p n' R mm hmm TT a ccl aw bw lam0 A B hBase hDom hzero hAB h8 e he
  obtain ⟨mH, mU, abelian₂, hint, hel⟩ :=
    h p n' R mm hmm TT a ccl aw bw lam0 A B hBase hDom hzero hAB h8 _ _ _ _ _ rfl rfl rfl rfl rfl
  obtain ⟨G, hG, hs, hle, ht⟩ := cc_edge R e he
  obtain ⟨nb, z0, s, s', ka, hnb, hka, h24, hmem⟩ := hel G hG
  have hw : algebraMap R.O R.Kf R.w ≠ 0 := R.w_ne
  have hIH : IntB R mH := fun M hM => (hint M hM).1
  have hIU : IntB R mU := fun M hM => (hint M hM).2.1
  have hIL : IntB R abelian₂ := fun M hM => (hint M hM).2.2

  obtain ⟨hlo1, hlo2⟩ := cc_lo TT ccl aw bw lam0 A B hBase hzero hAB
  obtain ⟨hlo1', hlo2'⟩ := cc_dualW TT _ _ hlo1 hlo2
  have hze1 : ∀ s ∈ TT, flatW (mm + 1) (fun _ : TT => 2 * ccl) (fun _ : TT => 2 * ccl) s 0 = ((2 * ccl : ℕ) : ℤ) ∧
      flatW (mm + 1) (fun _ : TT => 2 * ccl) (fun _ : TT => 2 * ccl) s (Fin.last (mm + 1)) = -((2 * ccl : ℕ) : ℤ) :=
    fun s hs => ⟨cc_flat_zero _ _ _ s hs, cc_flat_last _ _ _ s hs⟩
  obtain ⟨aze, -⟩ := cc_Ar_of TT _ _ hze1 (fun s hs => cc_flat_off _ _ _ s hs)
  obtain ⟨alo, -⟩ := cc_Ar_of TT _ _ hlo1 hlo2
  obtain ⟨alo', elo'⟩ := cc_Ar_of TT _ _ hlo1' hlo2'
  have aHp : Ar 1 (flatW (mm + 1) (fun s => A s + 2 * ccl) (fun s => B s + 2 * ccl)) =
      Ar 1 (flatW (mm + 1) A B) + Ar 1 (flatW (mm + 1) (fun _ : TT => 2 * ccl) (fun _ : TT => 2 * ccl)) := by
    rw [← cc_Ar_add, ← cc_flat_add]
  have alam : Ar 1 lam0 = Ar 1 (flatW (mm + 1) A B) + Ar 1 (lam0 - flatW (mm + 1) A B) := by
    rw [← cc_Ar_add, add_sub_cancel]
  have aL : Ar 1 (flatW (mm + 1) (fun s => A s + 2 * ccl) (fun s => B s + 2 * ccl)) =
      Ar 1 lam0 + Ar 1 (dualW (lam0 - flatW (mm + 1) A B)) := by
    rw [aHp, alam, aze, alo, alo']
    push_cast
    ring
  have hdlo : IsDominant (lam0 - flatW (mm + 1) A B) := cc_lo_dom TT ccl aw bw lam0 A B hBase hDom hzero hAB
  have hdlo' : IsDominant (dualW (lam0 - flatW (mm + 1) A B)) := fun s => cc_dualWt_anti _ (hdlo s)

  obtain ⟨z1, sb1, sa1, -⟩ := hmem 1 one_ne_zero
  obtain ⟨zw, sbw, saw, isow⟩ := hmem _ hw
  obtain ⟨-, -, sap, -⟩ := hmem _ (mul_ne_zero hw hw)
  obtain ⟨hz1, hz2⟩ := cc_elem _ e G hs hle z0 z1 zw
  refine ⟨nb, mH.flip z0, fun b => mU.flip (s b), fun a' => abelian₂.flip (s' a'), ka, hnb, hka, ?_, ?_, ?_⟩
  · intro a' b F
    exact h24 a' b F
  · intro F
    constructor
    · intro hF
      have h1 := (cc_mem_scale (zpow_ne_zero _ hw)).1 hF
      rw [zpow_neg, inv_inv] at h1
      have h2 : mH ((algebraMap R.O R.Kf R.w ^ Ar 1 (flatW (mm + 1) A B)) • F)
          ((algebraMap R.O R.Kf R.w ^ Ar 1 (flatW (mm + 1) (fun _ : TT => 2 * ccl) (fun _ : TT => 2 * ccl))) • z0) =
          (algebraMap R.O R.Kf R.w ^ Ar 1 (flatW (mm + 1) (fun s => A s + 2 * ccl) (fun s => B s + 2 * ccl))) •
            mH.flip z0 F := by
        rw [map_smul, map_smul, LinearMap.smul_apply, smul_smul, ← zpow_add₀ hw, aHp, LinearMap.flip_apply,
          add_comm (Ar 1 (flatW (mm + 1) A B))]
      have h3 := isow ((algebraMap R.O R.Kf R.w ^ Ar 1 (flatW (mm + 1) A B)) • F) (by
        rw [h2, ← hle]
        exact h1)
      refine (cc_mem_scale (zpow_ne_zero _ hw)).2 ?_
      rw [zpow_neg, inv_inv]
      show _ ∈ toV _ (Hten R.O _ (fun s : Fin n' => LeAt p R.ι R.σ R.w s.val e))
      rw [hle]
      exact h3
    · intro hF
      exact cc_Re hIH aHp e he F hF z0 hz2
  · intro t c₂ hc
    refine ⟨?_, ?_, ?_⟩
    · intro F hF
      exact cc_CCL hIncl hIH aHp (flattened_weight_dominant _ _ _) e he z0 hz1 hz2 t c₂ F hF
    · intro b F hF
      obtain ⟨hb1, hb2⟩ := cc_elem _ e G hs hle (s b) (sb1 b) (sbw b)
      exact cc_CCL hIncl hIU alam hdlo e he (s b) hb1 hb2 t c₂ F hF
    · intro a' g hg
      obtain ⟨-, ha2⟩ := cc_elem _ e G hs hle (s' a') (sa1 a') (saw a')
      have ha3 : ((algebraMap R.O R.Kf R.w * algebraMap R.O R.Kf R.w) ^ Ar 1 (dualW (lam0 - flatW (mm + 1) A B))) • s' a' ∈
          HL (O := R.O) R.ι R.σ (dualW (lam0 - flatW (mm + 1) A B)) e.tgt := by
        show _ ∈ toV _ (Hten R.O _ (fun s : Fin n' => extO R.O R.ι R.σ s.val e.tgt))
        rw [ht]
        exact sap a'
      have h5 := cc_CCL' hIL aL hdlo' (by rw [elo', alo']) (TT.card * ccl) (by rw [alo']; push_cast; ring) e he (s' a')
        ha3 ha2 t c₂ (by rw [← mul_assoc]; exact hc) g hg
      rw [← mul_assoc] at h5
      exact h5

end Formalism.MainNotions.flipOneThree.Pf

end
