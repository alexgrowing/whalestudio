import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NonzeroLocusSecMonoConst
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformLiftingOfSectionsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelativelyAmpleConsecutiveVeryAmpleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VeryAmpleTensorPowerSectionsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VeryAmpleUnionSectionsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalSectionsCompatibleSystemStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LineBundleRootFromRelationsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelativelyAmpleTwistDifferenceStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullbackTwistIsoDifferenceStatement

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier
open GlobalTheory.CompanionTheory.FormalAlg

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.FormalAlg

theorem exists_compatible {R : Type} [CommRing R] (I : Ideal R) {Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))}
    {β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left} {N : ∀ e, LB (Y e).left}
    {v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))} {D : ℤ}
    (step : ∀ (e : ℕ) (σ : LB.Sec (pw (N e) D)), ∃ σ' : LB.Sec (pw (N (e + 1)) D),
      SecMaps (pullPow (v e) D) σ (secPull σ' (β e)))
    {τ : Type} (a₀ : τ → LB.Sec (pw (N 0) D)) :
    ∃ a : ∀ e, τ → LB.Sec (pw (N e) D), a 0 = a₀ ∧
      ∀ e i, SecMaps (pullPow (v e) D) (a e i) (secPull (a (e + 1) i) (β e)) := by
  choose L hL using step
  exact ⟨fun e i => Nat.rec (motive := fun e => LB.Sec (pw (N e) D)) (a₀ i) (fun e x => L e x) e,
    rfl, fun e i => hL e _⟩

theorem tower_sections : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → (∀ e, IsProper (Y e).hom) → ∀ (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))), (∀ e, (N e).IsLB ∧ (v e).IsGen) → RelAmple (Y 0) (N 0) → ∃ (n p q : ℕ) (a : ∀ e, Fin (p + 1) → LB.Sec (pw (N e) (n : ℤ))) (c : ∀ e, Fin (q + 1) → LB.Sec (pw (N e) ((n : ℤ) + 1))), 1 ≤ n ∧ VeryAmpleBy (Y 0).hom (pw (N 0) (n : ℤ)) (a 0) ∧ VeryAmpleBy (Y 0).hom (pw (N 0) ((n : ℤ) + 1)) (c 0) ∧ (∀ e i, SecMaps (pullPow (v e) (n : ℤ)) (a e i) (secPull (a (e + 1) i) (β e))) ∧ (∀ e i, SecMaps (pullPow (v e) ((n : ℤ) + 1)) (c e i) (secPull (c (e + 1) i) (β e))) := by
  intro R _ _ I Y β hβ hP N v hN hA
  obtain ⟨d, hd, m₁, s, m₂, s', hs, hs'⟩ := GlobalTheory.T.relatively_ample_consecutive_very_ample (R ⧸ I ^ (0 + 1)) (Y 0) (N 0) (hN 0).1 hA
  obtain ⟨t₁, ht₁⟩ := GlobalTheory.T.formal_line_bundle_very_ample_system R I Y β hβ hP N v hN d hd m₁ s hs
  obtain ⟨t₂, ht₂⟩ := GlobalTheory.T.formal_line_bundle_very_ample_system R I Y β hβ hP N v hN (d + 1) (by omega) m₂ s' hs'
  set k := max t₁ t₂ with hk
  set t := 1 + (d + 1) * k with ht
  set t' := 1 + d * k with ht'
  have hkt : k ≤ t := by nlinarith
  have hkt' : k ≤ t' := by nlinarith
  have h1 : t₁ ≤ t := (le_max_left _ _).trans hkt
  have h2 : t₂ ≤ t' := (le_max_right _ _).trans hkt'
  have e₁ : ((d * t : ℕ) : ℤ) = (d : ℤ) * (t : ℕ) := by push_cast; ring
  have e₂ : ((d * t : ℕ) : ℤ) + 1 = ((d + 1 : ℕ) : ℤ) * (t' : ℕ) := by
    simp only [ht, ht']; push_cast; ring
  have hc₁ : 0 < Fintype.card (Fin t → Fin (m₁ + 1)) := Fintype.card_pos
  have hc₂ : 0 < Fintype.card (Fin t' → Fin (m₂ + 1)) := Fintype.card_pos
  obtain ⟨p, hp⟩ : ∃ p, Fintype.card (Fin t → Fin (m₁ + 1)) = p + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hc₁).symm⟩
  obtain ⟨q, hq⟩ : ∃ q, Fintype.card (Fin t' → Fin (m₂ + 1)) = q + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hc₂).symm⟩
  let E₁ : Fin (p + 1) ≃ (Fin t → Fin (m₁ + 1)) := (Fintype.equivFinOfCardEq hp).symm
  let E₂ : Fin (q + 1) ≃ (Fin t' → Fin (m₂ + 1)) := (Fintype.equivFinOfCardEq hq).symm
  have ht1 : 1 ≤ t := by omega
  have ht1' : 1 ≤ t' := by omega
  have va := GlobalTheory.T.very_ample_tensor_power_sections _ (Y 0).hom (N 0) _ _ t e₁.symm m₁ s (hN 0).1 ht1 hs p E₁
  have vc := GlobalTheory.T.very_ample_tensor_power_sections _ (Y 0).hom (N 0) _ _ t' e₂.symm m₂ s' (hN 0).1 ht1' hs' q E₂
  obtain ⟨a, ha0, ha⟩ := exists_compatible I (v := v) (ht₁ t h1 _ e₁) (fun j => secMono e₁.symm s (E₁ j))
  obtain ⟨c, hc0, hc⟩ := exists_compatible I (v := v) (ht₂ t' h2 _ e₂) (fun j => secMono e₂.symm s' (E₂ j))
  refine ⟨d * t, p, q, a, c, Nat.mul_pos hd ht1, ?_, ?_, ha, hc⟩
  · rw [ha0]; exact va
  · rw [hc0]; exact vc

theorem schemes_of_closedProj : GEClosedProj → GlobalTheory.Published.FormalAlgebraisation.Schemes := by
  intro hGE R _ _ I hI Y β hβ hP N hN hv hA
  choose v hvg using hv
  have hNv : ∀ e, (N e).IsLB ∧ (v e).IsGen := fun e => ⟨hN e, hvg e⟩
  obtain ⟨n, p, q, a, c, hn, ha0, hc0, hca, hcc⟩ := tower_sections R I Y β hβ hP N v hNv hA
  set D : ℤ := (n : ℤ) * ((n + 1 : ℕ) : ℤ) with hD
  have h1 : (n : ℤ) * ((n + 1 : ℕ) : ℤ) = D := rfl
  have h2 : ((n : ℤ) + 1) * ((n : ℕ) : ℤ) = D := by rw [hD]; push_cast; ring
  have hcard : ∀ (k r : ℕ), ∃ m, Fintype.card (Fin k → Fin (r + 1)) = m + 1 := fun k r =>
    ⟨_, (Nat.succ_pred_eq_of_pos (Fintype.card_pos (α := Fin k → Fin (r + 1)))).symm⟩
  obtain ⟨m₁, hm₁⟩ := hcard (n + 1) p
  obtain ⟨m₂, hm₂⟩ := hcard n q
  let E₁ : Fin (m₁ + 1) ≃ (Fin (n + 1) → Fin (p + 1)) := (Fintype.equivFinOfCardEq hm₁).symm
  let E₂ : Fin (m₂ + 1) ≃ (Fin n → Fin (q + 1)) := (Fintype.equivFinOfCardEq hm₂).symm
  let m := m₁ + 1 + m₂
  let E : Fin (m + 1) ≃ Fin (m₁ + 1) ⊕ Fin (m₂ + 1) :=
    (finCongr (by omega)).trans finSumFinEquiv.symm
  let z : ∀ e, Fin (m + 1) → LB.Sec (pw (N e) D) := fun e j =>
    Sum.elim (fun i => secMono h1 (a e) (E₁ i)) (fun i => secMono h2 (c e) (E₂ i)) (E j)
  have hz1 : ∀ e w, z e (E.symm (Sum.inl (E₁.symm w))) = secMono h1 (a e) w := fun e w => by
    simp [z]
  have hz2 : ∀ e w, z e (E.symm (Sum.inr (E₂.symm w))) = secMono h2 (c e) w := fun e w => by
    simp [z]
  have hva : VeryAmpleBy (Y 0).hom (pw (N 0) D) (z 0) := by
    have x1 := GlobalTheory.T.very_ample_tensor_power_sections _ (Y 0).hom (N 0) _ _ (n + 1) h1 p (a 0) (hN 0) (by omega) ha0 m₁ E₁
    have x2 := GlobalTheory.T.very_ample_tensor_power_sections _ (Y 0).hom (N 0) _ _ n h2 q (c 0) (hN 0) hn hc0 m₂ E₂
    exact GlobalTheory.T.very_ample_union_sections _ (Y 0).hom _ (isLB_pw (hN 0) D) m₁ m₂ m _ _ E x1 x2
  have hzc : ∀ e j, SecMaps (pullPow (v e) D) (z e j) (secPull (z (e + 1) j) (β e)) := fun e j => by
    simp only [z]
    rcases E j with i | i
    · exact secMaps_secMono (v e) h1 (a e) (a (e + 1)) (hca e) _
    · exact secMaps_secMono (v e) h2 (c e) (c (e + 1)) (hcc e) _
  obtain ⟨X, Q, ζ, b, ω, hQ, hX, hXa, hb, hbc, hω, hωz, hquad, hcov⟩ :=
    GlobalTheory.T.formal_sections_compatible_system hGE R I hI Y β hβ (fun e => pw (N e) D) (fun e => pullPow (v e) D)
      (fun e => ⟨isLB_pw (hN e) D, pullPow_isGen _ _ (hvg e)⟩) m z hzc hva
  let ia : (Fin (n + 1) → Fin (p + 1)) → Fin (m + 1) := fun w => E.symm (Sum.inl (E₁.symm w))
  let ic : (Fin n → Fin (q + 1)) → Fin (m + 1) := fun w => E.symm (Sum.inr (E₂.symm w))
  have hA' : ⨆ i : Fin (p + 1), nonzeroLocus (ζ (ia fun _ => i)) = ⊤ := by
    have := hcov (Set.range fun i : Fin (p + 1) => ia fun _ => i) (by
      rw [iSup_range, ← ha0.1]
      refine iSup_congr fun i => ?_
      rw [hz1, nonzeroLocus_secMono_const h1 _ _ (by omega)])
    rwa [iSup_range] at this
  have hC' : ⨆ i : Fin (q + 1), nonzeroLocus (ζ (ic fun _ => i)) = ⊤ := by
    have := hcov (Set.range fun i : Fin (q + 1) => ic fun _ => i) (by
      rw [iSup_range, ← hc0.1]
      refine iSup_congr fun i => ?_
      rw [hz2, nonzeroLocus_secMono_const h2 _ _ hn])
    rwa [iSup_range] at this
  obtain ⟨A, ωA, hAL, hωA, hAc⟩ := GlobalTheory.T.line_bundle_root_from_relations X.left Q hQ (n + 1) (by omega) (Fin (p + 1)) (fun w => ζ (ia w))
    (fun w₁ w₂ w₃ w₄ hw c' => hquad _ _ _ _ (fun e c'' => by
      simp only [ia, hz1]; exact secMono_mul h1 (a e) w₁ w₂ w₃ w₄ hw c'') c') hA'
  obtain ⟨C, ωC, hCL, hωC, hCc⟩ := GlobalTheory.T.line_bundle_root_from_relations X.left Q hQ n hn (Fin (q + 1)) (fun w => ζ (ic w))
    (fun w₁ w₂ w₃ w₄ hw c' => hquad _ _ _ _ (fun e c'' => by
      simp only [ic, hz2]; exact secMono_mul h2 (c e) w₁ w₂ w₃ w₄ hw c'') c') hC'
  refine ⟨X, tw C A (-1), b, hX, isLB_tw hCL hAL _,
    GlobalTheory.T.relatively_ample_twist_difference R X Q m ζ hQ hXa A C n hn hAL hCL ⟨ωA, hωA⟩ ⟨ωC, hωC⟩, hb, hbc, fun e => ?_⟩
  refine GlobalTheory.T.pullback_twist_iso_difference (b e) A C (N e) n hAL hCL (hN e) ?_ ?_
  · refine hAc _ (b e) (N e) n D h1 (a e) (ω e) (hN e) (hω e) fun w => ?_
    have := hωz e (ia w)
    simp only [ia, hz1] at this
    exact this
  · refine hCc _ (b e) (N e) ((n : ℤ) + 1) D h2 (c e) (ω e) (hN e) (hω e) fun w => ?_
    have := hωz e (ic w)
    simp only [ic, hz2] at this
    exact this

end GlobalTheory.CompanionTheory.FormalAlg
