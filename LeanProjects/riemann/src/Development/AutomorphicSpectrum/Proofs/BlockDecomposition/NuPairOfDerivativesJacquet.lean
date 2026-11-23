import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.SegmentDerivatives.DerivSub
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.ProdIrrFiniteLength
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothIterPhi
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassInvolutive
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassTwistNeg
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FineJacquetSegmentInduction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityOfEquiv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandKazhdanContragredient
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalLanglandsOfIrreducibleAdmissible
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairingTwistedDeterminantSubquotient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NontrivialTwJacquetOfSurjective

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir Zc

namespace GlobalTheory.CompanionTheory.BZNuPairAsm

section Lemmas

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem dualCl_degree (x : IrrGL k) : (dualCl x).1 = x.1 := by
  unfold dualCl
  split <;> rfl

theorem dual_shift (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (s q : IrrGL k) (j : ℕ) (h : q = (dualCl s).nu (j : ℂ)) :
    dualCl (q.nu (-(((j : ℂ) + 1) / 2))) = (s.nu (-(((j : ℂ) + 1) / 2))).nu 1 := by
  subst h
  rw [GlobalTheory.CompanionTheory.ZcDual.dualCl_nu hA, GlobalTheory.CompanionTheory.ZcDual.dualCl_nu hA, GlobalTheory.CompanionTheory.Zcore.dualCl_dualCl hA,
    IrrGL.nu_nu, IrrGL.nu_nu]
  congr 1
  ring

theorem nontrivial_of_irreducible {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (hi : ρ.IsIrreducible) : Nontrivial V := by
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  apply hi.bot_ne_top
  ext v
  simp [Subsingleton.elim v 0]

theorem continuous_inv (ψ : AddChar k Circle) (hc : Continuous ψ) : Continuous (ψ⁻¹ : AddChar k Circle) := by
  have e : (⇑(ψ⁻¹ : AddChar k Circle)) = fun a => ψ (-a) := by
    funext a
    exact AddChar.inv_apply ψ a
  rw [e]
  exact hc.comp continuous_neg

theorem jm_swap (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hJT : JmTheta k) {N : ℕ} {V : Type} [AddCommGroup V]
    [Module ℂ V] (ω : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth ω) (hi : ω.IsIrreducible)
    (a b c : IrrGL k) (hc : dualCl a = c) (hd : ∑ i, (![a, b] i).1 = N) (h : 1 ≤ jm ![a, b] hd (contra ω)) :
    ∃ hd' : ∑ i, (![dualCl b, c] i).1 = N, 1 ≤ jm ![dualCl b, c] hd' ω := by
  have hfl : HasFiniteLength ω := hasFiniteLength_of_isIrreducible hi
  have hd2 : ∑ i, (![dualCl b, dualCl a] i).1 = N := by
    simpa [Fin.sum_univ_two, dualCl_degree, add_comm] using hd
  have key := hJT N V ω hs hfl a b hd hd2
  have e := GlobalTheory.CompanionTheory.ThetaW.comp_thetaW_equiv_contra (GlobalTheory.CompanionTheory.GKLocalProof.gkLocal hA) N ω hs hi
  rw [GlobalTheory.CompanionTheory.JacquetCongr.jm_congr_of_equiv ![a, b] hd _ _ e] at key
  subst hc
  exact ⟨hd2, key ▸ h⟩

end Lemmas

theorem nuPair : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    GlobalTheory.Published.IrreducibleAdmissibleGL → GlobalTheory.BZSeg.DerivJac k → GlobalTheory.BZSeg.JmTheta k → GlobalTheory.BZSeg.DerivSub k →
    GlobalTheory.BZSeg.NuPair k := by
  intro k _ _ _ _ hA hDJ hJT hDS N V _ _ ω hs hi hng
  obtain ⟨ψ, hc, h1⟩ := GlobalTheory.LocGL.exists_continuous_addChar_ne_one k
  have hn : Nontrivial V := nontrivial_of_irreducible ω hi
  have hg : ¬ IsGenericFor ψ ω := fun h => hng ((isGeneric_iff_isGenericFor hc h1 ω).2 h)
  obtain ⟨m, hm0, hmN, hnt, hlow⟩ := GlobalTheory.CompanionTheory.BZCuspPair.exists_highest ψ hc h1 N ω hs hn hg
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, N = n + 1 + j + 1 := ⟨N - n - 2, by omega⟩
  have hfl : HasFiniteLength ω := hasFiniteLength_of_isIrreducible hi
  have hD := GlobalTheory.CompanionTheory.BZCuspPair.deriv_nontrivial ψ n j ω hnt
  obtain ⟨S, f, hf⟩ := hDS ψ n j V ω hs hfl hD
  have hsq : IsSubquotient S.ρ (GlobalTheory.BZMir.deriv k ψ j ω) := IsSubquotient.of_injective f hf
  obtain ⟨β, hdβ, hβ, hjm⟩ := hDJ ψ hc h1 n j V ω hs hfl S hsq
  have hv := GlobalTheory.CompanionTheory.BZCuspPair.phi_vanish ψ hc h1 n j ω hs hlow
  have hs' : IsSmooth (contra ω) := isSmooth_contra _
  have hi' : (contra ω).IsIrreducible := GlobalTheory.CompanionTheory.ZcDual.isIrreducible_contra hA ω hs hi
  have hfl' : HasFiniteLength (contra ω) := hasFiniteLength_of_isIrreducible hi'
  let B : V →ₗ[ℂ] smoothPart ω.dual →ₗ[ℂ] ℂ := ((smoothPart ω.dual).subtype).flip
  have hB : ∀ g v v', B (ω g v) (contra ω g v') = B v v' := by
    intro g v v'
    change (ω.dual g (v' : Module.Dual ℂ V)) (ω g v) = (v' : Module.Dual ℂ V) v
    rw [Representation.dual_apply]
    show (v' : Module.Dual ℂ V) (ω g⁻¹ (ω g v)) = (v' : Module.Dual ℂ V) v
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hBn : ∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0 := by
    intro v hv0
    obtain ⟨l, hl⟩ := GlobalTheory.ContraRefl.exists_smooth_form_ne hs
      (fun U a => GlobalTheory.ThetaLiftGL.compactOpen_basis k (n + 1 + j + 1) U a) hv0
    exact ⟨l, hl⟩
  obtain ⟨B', hB', hB'n⟩ := GlobalTheory.CompanionTheory.BZCuspPair.pair_deriv ψ hc h1 n j ω (contra ω) hs hs' B hB hBn hv
  have hint : ∀ g w, f (S.ρ g w) = GlobalTheory.BZMir.deriv k ψ j ω g (f w) := fun g w =>
    Representation.IntertwiningMap.isIntertwining _ _ f g w
  have hSn : Nontrivial S.V := nontrivial_of_irreducible S.ρ S.irr
  obtain ⟨Q, hQ, hQeq⟩ := GlobalTheory.CompanionTheory.DualQuot.exists_subquotient_dual_nu k (n + 1) j _ S
    (GlobalTheory.BZMir.deriv k ψ⁻¹ j (contra ω)) (GlobalTheory.CompanionTheory.BZCuspPair.isSmooth_deriv ψ⁻¹ j hs')
    (B'.comp f.toLinearMap)
    (by
      intro g w w'
      change B' (f (S.ρ g w)) _ = _ * B' (f w) w'
      rw [hint]
      exact hB' g (f w) w')
    (by
      intro h0
      obtain ⟨w, hw⟩ := exists_ne (0 : S.V)
      have hfw : f w ≠ 0 := fun e => hw (hf (e.trans (map_zero f).symm))
      obtain ⟨w', hw'⟩ := hB'n (f w) hfw
      apply hw'
      have := LinearMap.congr_fun (LinearMap.congr_fun h0 w) w'
      exact this)
  obtain ⟨β₂, hd₂, hβ₂, hjm₂⟩ := hDJ ψ⁻¹ (continuous_inv ψ hc) (inv_ne_one.mpr h1) n j _ (contra ω) hs' hfl' Q hQ
  obtain ⟨hd₃, hjm₃⟩ := jm_swap hA hJT ω hs hi _ β₂ _ rfl hd₂ hjm₂
  have hshift := dual_shift hA (IrrGL.of S.ρ S.smooth S.irr) (IrrGL.of Q.ρ Q.smooth Q.irr) j hQeq
  have hd' : ∑ a, (![dualCl β₂, ((IrrGL.of S.ρ S.smooth S.irr).nu (-(((j : ℂ) + 1) / 2))).nu 1] a).1 =
      n + 1 + j + 1 := by
    rw [← hshift]
    exact hd₃
  refine ⟨(IrrGL.of S.ρ S.smooth S.irr).nu (-(((j : ℂ) + 1) / 2)), β, dualCl β₂, hdβ, hd', ?_, ?_, ?_, hjm, ?_⟩
  · rw [IrrGL.nu_fst]
    exact Nat.succ_pos n
  · rw [hβ]
    exact Nat.succ_pos j
  · rw [dualCl_degree, hβ₂, hβ]
  · rw [← GlobalTheory.CompanionTheory.SegFine.jm_congr (by rw [hshift]) hd₃ hd' ω]
    exact hjm₃

end GlobalTheory.CompanionTheory.BZNuPairAsm

end
