import Formalism.WachLatticeTwists.HodgeTateChains.InvariantsCohomologyData
import Formalism.WachLatticeTwists.HodgeTateChains.HodgeTateFiltrations.InverseOperatorFromInjectivity

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic

open Polynomial

theorem piece : StatPiece := by
  intro ℓ _ w m hm h2 hw U i A P ⟨hS, ⟨hIR1, hIR2⟩, hT4, ⟨_, hT3⟩, htf, hHT⟩ y ⟨k, hk⟩
  have hkill : aeval P.gm ((X - 1) * Rpoly ℓ w U i) = 0 := by
    obtain ⟨q, hq⟩ := (htpoly ℓ w U i).1
    rw [hq, map_mul, hHT, zero_mul]
  have h1 : P.res ((ℓ : ℤ_[ℓ]) • P.lam y) = 0 := by rw [map_smul]; exact hT4 _
  obtain ⟨a, x, hax⟩ := (hIR1 _).1 h1
  have h3 : P.infm (((ℓ : ℤ_[ℓ]) ^ k) • a) + P.infX (((ℓ : ℤ_[ℓ]) ^ k) • x) = 0 := by
    rw [map_smul, map_smul, ← smul_add, ← hax, smul_comm, ← map_smul, hk, map_zero, smul_zero]
  obtain ⟨⟨a', ha'⟩, _⟩ := (hIR2 _ _).1 h3
  obtain ⟨a'', ha''⟩ := eigen ℓ w m hm h2 hw U i P.Wm P.gm htf hkill k a a' ha'
  obtain ⟨x'', hx''⟩ := hT3 x
  have h4 : P.infm (((ℓ : ℤ_[ℓ]) ^ (max 1 (rI ℓ m U i))) • a) + P.infX (((ℓ : ℤ_[ℓ]) ^ (max 1 (rI ℓ m U i))) • x) = 0 := by
    apply (hIR2 _ _).2
    constructor
    · refine ⟨((ℓ : ℤ_[ℓ]) ^ (max 1 (rI ℓ m U i) - rI ℓ m U i)) • a'', ?_⟩
      rw [map_smul, ← smul_sub, ← ha'', smul_smul, ← pow_add, Nat.sub_add_cancel (le_max_right _ _)]
    · refine ⟨((ℓ : ℤ_[ℓ]) ^ (max 1 (rI ℓ m U i) - 1)) • x'', ?_⟩
      rw [map_smul, ← smul_sub, ← hx'', smul_smul, ← pow_succ, Nat.sub_add_cancel (le_max_left _ _)]
  have h5 : ((ℓ : ℤ_[ℓ]) ^ (max 1 (rI ℓ m U i) + 1)) • P.lam y = 0 := by
    rw [pow_succ, mul_smul, hax, smul_add, ← map_smul, ← map_smul]; exact h4
  have h6 := congrArg P.io h5
  rw [map_smul, hS, map_zero, smul_smul, ← pow_succ] at h6
  have h7 : 2 + max 1 (rI ℓ m U i) = max 1 (rI ℓ m U i) + 1 + 1 := by ring
  rw [h7]; exact h6

theorem ll : StatLL := by
  intro ℓ _ w m hm h2 hw U a n d D hd hP ⟨h0, hex⟩ hT5 hcr
  have hGr : ∀ k, TorsKilled ℓ (D.Gr k) (2 + max 1 (rI ℓ m U (a + k))) :=
    fun k => piece ℓ w m hm h2 hw U (a + k) (D.Gr k) (D.piece k) (hP k)
  have hm' := devSum ℓ (fun k => D.Hm k) (fun k => D.Gr k) D.f D.p _ h0 hex hT5 hGr n
  rw [← reindex] at hm'
  exact cores ℓ D.HK (D.Hm n) D.res D.cor d _ hd hcr hm'

theorem h0 : InvariantsKilledByPower := by
  intro ℓ _ w m hm h2 hw U h0U hne D hP hUn hFl hLES ⟨hInv1, hInv2⟩ x
  have hA := piece ℓ w m hm h2 hw U 0 D.A D.piece hP
  have hr : rI ℓ m U 0 = ∑ u ∈ U, (m + padicValInt ℓ u) := by
    unfold rI; rw [Finset.erase_eq_of_notMem h0U]; simp
  have hr1 : 1 ≤ rI ℓ m U 0 := by
    rw [hr]
    obtain ⟨u, hu⟩ := hne
    calc 1 ≤ m + padicValInt ℓ u := by omega
      _ ≤ _ := Finset.single_le_sum (f := fun u => m + padicValInt ℓ u) (fun _ _ => Nat.zero_le _) hu
  have hc : 2 + max 1 (rI ℓ m U 0) = c0 ℓ m U := by unfold c0; rw [max_eq_right hr1, hr]
  rw [hc] at hA
  obtain ⟨_, _, _, ⟨hT3inj, _⟩, htf, hHT⟩ := hP
  have hW0 : ∀ z : D.H0WeightInvariants, z = 0 := fun z =>
    hInv1 z (eigenInj ℓ w m hm h2 hw U 0 h0U D.piece.Wm D.piece.gm htf hHT _ (hInv2 z).1)
      (hT3inj _ (hInv2 z).2)
  obtain ⟨r, hr'⟩ := hUn x
  let x' : Submodule.torsionBy ℤ_[ℓ] D.M ((ℓ : ℤ_[ℓ]) ^ r) :=
    ⟨x, by rw [Submodule.mem_torsionBy_iff]; exact hr'⟩
  have hx0 : ((ℓ : ℤ_[ℓ]) ^ r) • x' = 0 := Subtype.ext hr'
  have h1 : ((ℓ : ℤ_[ℓ]) ^ c0 ℓ m U) • D.dl r (D.emb r x') = 0 :=
    hA _ ⟨r, by rw [← map_smul, ← map_smul, hx0, map_zero, map_zero]⟩
  have h2' : D.dl r (D.emb r (((ℓ : ℤ_[ℓ]) ^ c0 ℓ m U) • x')) = 0 := by rw [map_smul, map_smul]; exact h1
  obtain ⟨z, hz⟩ := (hLES r _).1 h2'
  rw [hW0 z, map_zero] at hz
  have h3 : ((ℓ : ℤ_[ℓ]) ^ c0 ℓ m U) • x' = 0 := hFl r (by rw [← hz, map_zero])
  exact congrArg Subtype.val h3

theorem tb : StatTB := by
  intro ℓ _ s m e d U D hd ⟨c1, c2, c3, c4, c5, c6, c7⟩ ⟨e1, e2, e3⟩ hdR hLL hH2 hK3 hF3 hR ⟨hcr, hcf⟩
  have hℓ : ℓ.Prime := Fact.out
  have hle := (cTBTable ℓ hℓ s m e (padicValNat ℓ d) U).2
  generalize cTB ℓ s m e (padicValNat ℓ d) U = N at hle ⊢
  generalize cLL ℓ m U 0 ((e : ℤ) + 1) (ℓ ^ (m - s)) = c at hle hLL
  unfold TBData.tateDualityKillsH2 at hH2
  generalize s + padicValNat ℓ (e + 1) = t at hle hH2
  obtain ⟨z, hz⟩ := (e1 (((ℓ : ℤ_[ℓ]) ^ t) • D.f1 D.y)).1 (by rw [map_smul]; exact hH2 _)
  have h1 : ((ℓ : ℤ_[ℓ]) ^ c) • D.iY D.y = 0 := hLL _ hdR
  have h2 : D.qL (((ℓ : ℤ_[ℓ]) ^ c) • D.iZ z) = 0 := by
    rw [map_smul, c2, hz, map_smul, c1, smul_comm, ← map_smul, h1, map_zero, smul_zero]
  obtain ⟨w, hw⟩ := (e2 _).1 h2
  have h3 : D.bW w = ((ℓ : ℤ_[ℓ]) ^ c) • D.ex (D.jZ z) := by rw [← c4, hw, map_smul, c3]
  obtain ⟨x, hx⟩ := (e3 (((ℓ : ℤ_[ℓ]) ^ cPrime ℓ s e) • w)).1 (by rw [map_smul]; exact hK3 _)
  have h4 : ((ℓ : ℤ_[ℓ]) ^ (cPrime ℓ s e + 1 + s + ceilE ℓ e)) • D.bW w ∈ D.La0 := by
    have h := hF3 x
    rw [hx, map_smul, smul_smul, ← pow_add] at h
    have hexp : cPrime ℓ s e + 1 + s + ceilE ℓ e = 1 + s + ceilE ℓ e + cPrime ℓ s e := by ring
    rw [hexp]; exact h
  obtain ⟨z1, hz1⟩ := hR (D.bW w) _ (aTB ℓ s e) h4 ((aCount ℓ hℓ s e).2.1).symm
  have h5 : D.ex (((ℓ : ℤ_[ℓ]) ^ (aTB ℓ s e + c)) • D.jZ z - D.jW z1) = 0 := by
    rw [map_sub, map_smul, ← hz1, h3, smul_smul, ← pow_add, sub_self]
  have h6 := hcf _ h5
  have h6' : D.pr (((ℓ : ℤ_[ℓ]) ^ (aTB ℓ s e + c)) • D.jZ z - D.jW z1)
      = ((ℓ : ℤ_[ℓ]) ^ (aTB ℓ s e + c + t)) • D.res D.yK := by
    rw [map_sub, c5, sub_zero, map_smul, ← c6, hz, map_smul, ← c7, smul_smul, ← pow_add]
  rw [h6', map_smul, hcr, smul_comm] at h6
  have h8 := index_smul_mem D.HfK d hd _ h6
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hle
  have h9 : ((ℓ : ℤ_[ℓ]) ^ N) • D.yK
      = ((ℓ : ℤ_[ℓ]) ^ j) • (((ℓ : ℤ_[ℓ]) ^ padicValNat ℓ d) • (((ℓ : ℤ_[ℓ]) ^ (aTB ℓ s e + c + t)) • D.yK)) := by
    rw [smul_smul, smul_smul, ← pow_add, ← pow_add, hj]
    congr 2
    ring
  rw [h9]
  exact D.HfK.smul_mem _ h8

end Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic
