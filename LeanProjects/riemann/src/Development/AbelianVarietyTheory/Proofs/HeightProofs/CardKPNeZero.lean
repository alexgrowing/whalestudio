import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResCharConj
import Formalism.LocalToGlobal.Divisibility.DefGroup
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Plug.TwistLevels

open Formalism.L2.Host

theorem not_unrAt_mul {L : Type} [Field L] [NumberField L] {d ψ : HChar L} {v : HeightOneSpectrum (𝓞 L)}
    (hd : d.UnrAt v) (hψ : ¬ ψ.UnrAt v) : ¬ (d * ψ).UnrAt v := by
  intro h
  apply hψ
  intro x hx
  have := h x hx
  rw [HChar.loc_mul, hd x hx, one_mul] at this
  exact this

theorem unrAt_mul {L : Type} [Field L] [NumberField L] {d ψ : HChar L} {v : HeightOneSpectrum (𝓞 L)}
    (hd : d.UnrAt v) (hψ : ψ.UnrAt v) : (d * ψ).UnrAt v := by
  intro x hx
  rw [HChar.loc_mul, hd x hx, hψ x hx, one_mul]

theorem card_residueField_ne_zero {L : Type} [Field L] [NumberField L] (Q : HeightOneSpectrum (𝓞 L)) : Nat.card (kP Q) ≠ 0 := by
  have h : Nat.card (kP Q) = Ideal.absNorm Q.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [h, Ne, Ideal.absNorm_eq_zero_iff]
  exact Q.ne_bot

def ramSet (P : Pre) (Ξ : Set (HChar P.host.E)) : Set (HeightOneSpectrum (𝓞 P.host.E)) :=
  {Q | ((P.host.pde * P.host.pde' : ℕ) : 𝓞 P.host.E) ∈ Q.asIdeal ∨ ∃ χ ∈ Ξ, ¬ χ.UnrAt Q}

theorem not_unrAt_xiTw (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : B.places.Pl) (Q : HeightOneSpectrum (𝓞 B.host.E))
    (hQ : Q ∈ T.Q w) (hn : ((B.host.pde * B.host.pde' : ℕ) : 𝓞 B.host.E) ∉ Q.asIdeal) : ¬ (T.xiTw f w).UnrAt Q := by
  have h1 : ((B.host.pde : ℕ) : 𝓞 B.host.E) ∉ Q.asIdeal := fun h =>
    hn (by rw [Nat.cast_mul]; exact Q.asIdeal.mul_mem_right _ h)
  have h2 : ((B.host.pde' : ℕ) : 𝓞 B.host.E) ∉ Q.asIdeal := fun h =>
    hn (by rw [Nat.cast_mul]; exact Q.asIdeal.mul_mem_left _ h)
  have hψ : ¬ (T.psi w).UnrAt Q := fun h => ((T.psi_is w).ram Q).1 h hQ
  unfold TwDat.xiTw
  split_ifs
  · exact not_unrAt_mul (f.isDel'.unr Q h2) hψ
  · exact not_unrAt_mul (f.isDel.unr Q h1) hψ

theorem ram_finite (B : Base) (f : Fr B.toPre) (T : TwDat B) (χ : HChar B.host.E) (hχ : χ ∈ T.set f) :
    {Q : HeightOneSpectrum (𝓞 B.host.E) | ¬ χ.UnrAt Q}.Finite := by
  have hpde : B.host.pde * B.host.pde' ≠ 0 :=
    mul_ne_zero (B.toPre.level_prime _ B.host.pde_level.1).ne_zero (B.toPre.level_prime _ B.host.pde_level.2).ne_zero
  have hZ := GlobalTheory.Mem.Top.TwFin.finite_mem (K := B.host.E) hpde
  have h1 : ∀ Q : HeightOneSpectrum (𝓞 B.host.E), ((B.host.pde * B.host.pde' : ℕ) : 𝓞 B.host.E) ∉ Q.asIdeal →
      ((B.host.pde : ℕ) : 𝓞 B.host.E) ∉ Q.asIdeal := fun Q hn h =>
    hn (by rw [Nat.cast_mul]; exact Q.asIdeal.mul_mem_right _ h)
  have h2 : ∀ Q : HeightOneSpectrum (𝓞 B.host.E), ((B.host.pde * B.host.pde' : ℕ) : 𝓞 B.host.E) ∉ Q.asIdeal →
      ((B.host.pde' : ℕ) : 𝓞 B.host.E) ∉ Q.asIdeal := fun Q hn h =>
    hn (by rw [Nat.cast_mul]; exact Q.asIdeal.mul_mem_left _ h)
  rcases hχ with hχ | ⟨w, rfl⟩
  · rcases hχ with rfl | rfl | rfl
    · exact Set.finite_empty.subset fun Q hQ => hQ fun _ _ => rfl
    · refine hZ.subset fun Q hQ => ?_
      by_contra hn
      exact hQ (f.isDel.unr Q (h1 Q hn))
    · refine hZ.subset fun Q hQ => ?_
      by_contra hn
      exact hQ (f.isDel'.unr Q (h2 Q hn))
  · refine (hZ.union (T.Q w).finite_toSet).subset fun Q hQ => ?_
    by_contra hc
    simp only [Set.mem_union, Finset.mem_coe, not_or] at hc
    have hψ : (T.psi w).UnrAt Q := ((T.psi_is w).ram Q).2 hc.2
    apply hQ
    unfold TwDat.xiTw
    split_ifs
    · exact unrAt_mul (f.isDel'.unr Q (h2 Q hc.1)) hψ
    · exact unrAt_mul (f.isDel.unr Q (h1 Q hc.1)) hψ

open Classical in

theorem levels_bounded : ∀ (P : Pre) (f : Fr P) (Ξ : Set (Formalism.L2.Host.HChar P.host.E)), ∃ Ms : Finset ℕ, (∀ M ∈ Ms, M ≠ 0) ∧
    ∀ (B : Base) (hB : B.toPre = P) (T : TwDat B), HEq (T.set (hB ▸ f)) Ξ → ∀ (w : B.places.Pl)
      (S : Finset (HeightOneSpectrum (𝓞 B.host.E))),
      (∀ Q ∈ S, ((B.host.pde * B.host.pde' : ℕ) : 𝓞 B.host.E) ∈ Q.asIdeal ∨ Q ∈ T.Q w) →
      B.host.g 0 * B.host.g 1 * ∏ q ∈ S.image (fun Q => Nat.card (kP Q)), q ∈ Ms := by
  intro P f Ξ
  by_cases hA : (ramSet P Ξ).Finite
  · refine ⟨hA.toFinset.powerset.image
      (fun S => P.host.g 0 * P.host.g 1 * ∏ q ∈ S.image (fun Q => Nat.card (kP Q)), q), ?_, ?_⟩
    · intro M hM
      obtain ⟨S, -, rfl⟩ := Finset.mem_image.1 hM
      refine mul_ne_zero (mul_ne_zero (P.host.g_prime 0).ne_zero (P.host.g_prime 1).ne_zero) ?_
      rw [Finset.prod_ne_zero_iff]
      intro q hq
      obtain ⟨Q, -, rfl⟩ := Finset.mem_image.1 hq
      exact card_residueField_ne_zero Q
    · intro B hB T hT w S hS
      subst hB
      have hT' : T.set f = Ξ := eq_of_heq hT
      refine Finset.mem_image.2 ⟨S, Finset.mem_powerset.2 fun Q hQ => hA.mem_toFinset.2 ?_, rfl⟩
      rcases hS Q hQ with h | h
      · exact Or.inl h
      · by_cases hn : ((B.host.pde * B.host.pde' : ℕ) : 𝓞 B.host.E) ∈ Q.asIdeal
        · exact Or.inl hn
        · refine Or.inr ⟨T.xiTw f w, ?_, not_unrAt_xiTw B f T w Q h hn⟩
          rw [← hT']
          exact Set.mem_union_right _ ⟨w, rfl⟩
  · refine ⟨∅, by simp, ?_⟩
    intro B hB T hT w S hS
    subst hB
    exfalso
    apply hA
    have hT' : T.set f = Ξ := eq_of_heq hT
    have hpde : B.host.pde * B.host.pde' ≠ 0 :=
      mul_ne_zero (B.toPre.level_prime _ B.host.pde_level.1).ne_zero (B.toPre.level_prime _ B.host.pde_level.2).ne_zero
    have hfin := (GlobalTheory.Mem.Top.TwFin.tw_fin B f T).1
    refine ((GlobalTheory.Mem.Top.TwFin.finite_mem (K := B.host.E) hpde).union
      (hfin.biUnion fun χ hχ => ram_finite B f T χ hχ)).subset ?_
    rintro Q (h | ⟨χ, hχ, hr⟩)
    · exact Or.inl h
    · refine Or.inr (Set.mem_biUnion (x := χ) ?_ hr)
      rw [hT']
      exact hχ

end GlobalTheory.Plug.TwistLevels
