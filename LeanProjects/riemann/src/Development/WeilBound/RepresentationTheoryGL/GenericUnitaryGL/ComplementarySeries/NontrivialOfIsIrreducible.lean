import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.Complementary
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothIterPhi
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassInvolutive
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassTwistNeg
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityOfEquiv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsSocleOfOrderFree
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalLanglandsOfIrreducibleAdmissibleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsIrrRepInjectiveStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairingTwistedDeterminantSubquotientStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NontrivialTwJacquetOfSurjective
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import CompanionTheory.AutomorphicTheory.HeckeStandardModules.EqZeroOfCompAt

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir Zc

namespace PositivityTheory.RgGu.NR

namespace NuP

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem nontrivial_of_irr {G : Type} [Group G] [TopologicalSpace G] (τ : IrrRep G) : Nontrivial τ.V := by
  have hi := τ.irr
  by_contra hs
  rw [not_nontrivial_iff_subsingleton] at hs
  apply (bot_ne_top : (⊥ : Subrepresentation τ.ρ) ≠ ⊤)
  apply Subrepresentation.ext
  ext x
  rw [Subsingleton.elim x 0]
  exact ⟨fun _ => zero_mem _, fun _ => zero_mem _⟩

theorem nontrivial_of_isIrreducible {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ G V} (hi : π.IsIrreducible) : Nontrivial V := by
  by_contra hs
  rw [not_nontrivial_iff_subsingleton] at hs
  apply (bot_ne_top : (⊥ : Subrepresentation π) ≠ ⊤)
  apply Subrepresentation.ext
  ext x
  rw [Subsingleton.elim x 0]
  exact ⟨fun _ => zero_mem _, fun _ => zero_mem _⟩

theorem continuous_inv_addChar (ψ : AddChar k Circle) (hc : Continuous ψ) : Continuous (ψ⁻¹ : AddChar k Circle) := by
  have : (⇑(ψ⁻¹ : AddChar k Circle)) = fun a => ψ (-a) := funext fun a => AddChar.inv_apply ψ a
  rw [this]
  exact hc.comp continuous_neg

theorem dualCl_fst (x : IrrGL k) : (dualCl x).1 = x.1 := by
  unfold dualCl
  split <;> rfl

end NuP

set_option maxHeartbeats 4000000 in
open NuP in
theorem nuPair_of (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (h1 : GlobalTheory.BZSeg.DerivJac k) (h2 : GlobalTheory.BZSeg.JmTheta k) (h3 : DerFin k) : GlobalTheory.BZSeg.NuPair k := by
  intro N V _ _ ω hs hi hng
  have hA := GlobalTheory.CompanionTheory.BZCuspPair.irrAdm
  obtain ⟨ψ, hc, hψ⟩ := exists_continuous_addChar_ne_one k
  have hg : ¬ IsGenericFor ψ ω := fun h => hng ⟨ψ, hc, hψ, h⟩
  have hnt : Nontrivial V := nontrivial_of_isIrreducible hi
  obtain ⟨n, hn0, hnN, hnt2, hlow⟩ := GlobalTheory.CompanionTheory.BZCuspPair.exists_highest ψ hc hψ N ω hs hnt hg
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, N = n + 1 + j + 1 := ⟨N - (n + 1) - 1, by omega⟩
  have hc' := continuous_inv_addChar ψ hc
  have hψ' : ψ⁻¹ ≠ 1 := inv_ne_one.2 hψ
  let B : V →ₗ[ℂ] smoothPart ω.dual →ₗ[ℂ] ℂ := LinearMap.flip (smoothPart ω.dual).subtype
  have hBa : ∀ a b, B a b = (b : Module.Dual ℂ V) a := fun _ _ => rfl
  have hB : ∀ g a b, B (ω g a) (contra ω g b) = B a b := by
    intro g a b
    simp only [hBa, contra_apply]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hnd : ∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0 := fun v hv =>
    GlobalTheory.ContraRefl.exists_smooth_form_ne hs (GlobalTheory.SqIntUnit.compactOpen_basis k _) hv
  obtain ⟨B', hB', hn'⟩ := GlobalTheory.CompanionTheory.BZCuspPair.pair_deriv ψ hc hψ n j ω (contra ω) hs (isSmooth_contra _) B hB hnd
    (GlobalTheory.CompanionTheory.BZCuspPair.phi_vanish ψ hc hψ n j ω hs hlow)
  have hD := GlobalTheory.CompanionTheory.BZCuspPair.deriv_nontrivial ψ n j ω hnt2
  have hfl := h3 ψ hc hψ (n + 1) j V ω hs hi
  obtain ⟨S, f, hf⟩ := GlobalTheory.T.exists_injective_irreducible_subrepresentation k (n + 1) _ _ _ _ (GlobalTheory.CompanionTheory.BZCuspPair.isSmooth_deriv ψ j hs) hD
    (IsSubquotient.refl _) hfl
  have := nontrivial_of_irr S
  obtain ⟨w₀, hw₀⟩ := exists_ne (0 : S.V)
  have hw1 : f w₀ ≠ 0 := fun h => hw₀ (hf (by rw [h, map_zero]))
  obtain ⟨w', hw'⟩ := hn' (f w₀) hw1
  obtain ⟨Q, hQ, hQcl⟩ := GlobalTheory.T.pairing_twisted_determinant_subquotient k (n + 1) j _ S (GlobalTheory.BZMir.deriv k ψ⁻¹ j (contra ω))
    (GlobalTheory.CompanionTheory.BZCuspPair.isSmooth_deriv ψ⁻¹ j (isSmooth_contra _)) (B'.comp f.toLinearMap)
    (fun g w v => by
      have := hB' g (f w) v
      simpa [f.isIntertwining] using this)
    (fun h0 => hw' (by simpa using LinearMap.congr_fun (LinearMap.congr_fun h0 w₀) w'))
  have hflω : HasFiniteLength ω := hasFiniteLength_of_isIrreducible hi
  obtain ⟨β, hd1, hβ, hj1⟩ := h1 ψ hc hψ n j V ω hs hflω S (IsSubquotient.of_injective f hf)
  have hic : (contra ω).IsIrreducible := GlobalTheory.CompanionTheory.ZcDual.isIrreducible_contra hA ω hs hi
  obtain ⟨β'', hd2, hβ'', hj2⟩ := h1 ψ⁻¹ hc' hψ' n j _ (contra ω) (isSmooth_contra _)
    (hasFiniteLength_of_isIrreducible hic) Q hQ

  have hGK : Zc.Cos.GKLocal k := GlobalTheory.T.local_langlands_of_irreducible_admissible hA
  have hsθ : IsSmooth ((ω.comp (Zc.Cos.thetaW k (n + 1 + j + 1))).comp (Zc.Cos.thetaW k (n + 1 + j + 1))) := by
    rw [GlobalTheory.CompanionTheory.LSocle.comp_thetaW_thetaW]
    exact hs
  have hiθ : Representation.IsIrreducible
      ((ω.comp (Zc.Cos.thetaW k (n + 1 + j + 1))).comp (Zc.Cos.thetaW k (n + 1 + j + 1))) := by
    rw [GlobalTheory.CompanionTheory.LSocle.comp_thetaW_thetaW]
    exact hi
  have E := GlobalTheory.CompanionTheory.LSocle.equiv_contra_comp_thetaW hGK (ω.comp (Zc.Cos.thetaW k (n + 1 + j + 1))) hsθ hiθ
  rw [GlobalTheory.CompanionTheory.LSocle.comp_thetaW_thetaW] at E
  have hj3 : 1 ≤ jm ![(IrrGL.of Q.ρ Q.smooth Q.irr).nu (-(((j : ℂ) + 1) / 2)), β''] hd2
      (ω.comp (Zc.Cos.thetaW k (n + 1 + j + 1))) := by
    rw [GlobalTheory.CompanionTheory.JacquetCongr.jm_congr_of_equiv _ hd2 _ _ E]
    exact hj2
  set α : IrrGL k := (IrrGL.of S.ρ S.smooth S.irr).nu (-(((j : ℂ) + 1) / 2)) with hα
  set Q' : IrrGL k := (IrrGL.of Q.ρ Q.smooth Q.irr).nu (-(((j : ℂ) + 1) / 2)) with hQ'
  have hsum2 : ∀ (x y : IrrGL k), ∑ a, (![x, y] a).1 = x.1 + y.1 := fun x y => by
    simp [Fin.sum_univ_two]
  have hd3 : ∑ i, (![dualCl β'', dualCl Q'] i).1 = n + 1 + j + 1 := by
    rw [hsum2, dualCl_fst, dualCl_fst]
    rw [hsum2] at hd2
    omega
  have hj4 := hj3
  rw [h2 _ V ω hs hflω Q' β'' hd2 hd3] at hj4

  have hcls : dualCl Q' = α.nu 1 := by
    rw [hQ', hQcl, hα, IrrGL.nu_nu, IrrGL.nu_nu, GlobalTheory.CompanionTheory.ZcDual.dualCl_nu hA, GlobalTheory.CompanionTheory.Zcore.dualCl_dualCl hA]
    congr 1
    ring
  have key : ∀ u : IrrGL k, u = α.nu 1 → ∀ hdu : ∑ i, (![dualCl β'', u] i).1 = n + 1 + j + 1,
      1 ≤ jm ![dualCl β'', u] hdu ω → ∃ hd' : ∑ a, (![dualCl β'', α.nu 1] a).1 = n + 1 + j + 1,
        1 ≤ jm ![dualCl β'', α.nu 1] hd' ω := by
    rintro u rfl hdu h
    exact ⟨hdu, h⟩
  obtain ⟨hd', hj5⟩ := key _ hcls hd3 hj4
  have hβ''1 : β''.1 = j + 1 := hβ''
  refine ⟨α, β, dualCl β'', hd1, hd', ?_, ?_, ?_, hj1, hj5⟩
  · show 0 < (IrrGL.of S.ρ S.smooth S.irr).1
    show 0 < n + 1
    omega
  · omega
  · rw [dualCl_fst, hβ''1, hβ]

end PositivityTheory.RgGu.NR
