import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KatoTwistedClassNormCompatibleCyclotomic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KmapComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SCls
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.InvApi
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.GalAct
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.RepSlD
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.ValCast
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.OrbitSum
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.CoeffSlD
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KmapSubMemOfASet

open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

private theorem pol_cont {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ)
    [Fact l.Prime] (w n : ℕ) (t : X.Fn l) (ht : PolMod X l w n t) :
    ∃ E : Finset Ω, ∀ s : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E, s x = x) → CgF X l n (X.galB l s t) t := by
  obtain ⟨c, hc, htc⟩ := ht
  choose f _ hf using hc
  choose Ec hEc using fun i => GlobalTheory.KZ.GalCont.fix_fin X (f i : X.K)
  obtain ⟨Ez, hEz⟩ := GlobalTheory.KZ.GalCont.cyc_sub_one_mem (Ω := Ω) l n
  obtain ⟨-, -, -, -, hmap, -⟩ := sCls Ω ε X l n
  obtain ⟨-, -, -, -, hsm, -⟩ := sApi Ω ε X l n
  refine ⟨Ez ∪ Finset.univ.biUnion Ec, fun s hs u => ?_⟩
  have hχ := hEz s fun x hx => hs x (Finset.mem_union_left _ hx)
  rw [idl, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hχ
  have hk : ∀ i, AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l (X.gal s) (c i)) =
      AdicCompletion.eval (idl l) (X.Kl l) n (c i) := by
    intro i
    have h1 := hmap (X.gal s) _ _ (hf i)
    have h2 : Units.map (X.gal s : X.K →* X.K) (f i) = f i :=
      Units.ext (hEc i s fun x hx => hs x (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hx⟩)))
    rw [h2] at h1
    exact (show _ = _ from h1).trans (show _ = _ from hf i).symm
  have hgal : X.galB l s t u =
      X.kmap l (X.gal s) (t ![u 0, (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) * u 1]) := rfl
  rw [hgal, htc, htc, map_sum, ← Finset.sum_sub_distrib, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [map_smul, map_sub, map_smul, hk, ← map_smul, ← map_sub]
  refine hsm _ _ _ ?_
  rw [← mul_sub]
  refine Dvd.dvd.mul_left (Dvd.dvd.trans ?_ (sub_dvd_pow_sub_pow _ _ _)) _
  rw [← sub_one_mul]
  exact hχ.mul_right _

theorem UpperTheory.V.Z.Kato.Nb.sTopCocG :
    UpperTheory.V.Z.Kato.Nb.STopCocG := by
  intro Ω _ _ _ ε X l _ n N M₀ M w _ _ _ g hL hW x y hxy u hu z β hβ hz
  obtain ⟨hE, hadd, -, -, -, -, hgal, -, -, hmul, -⟩ := sApi Ω ε X l n
  obtain ⟨-, iadd, -, icg, -⟩ := sInvApi Ω ε X l N w n
  obtain ⟨m1, m2, -⟩ := sXiMul Ω ε X l n N M₀ M w g hL x y hxy (fun z => z = 1)
  obtain ⟨-, -, -, -, -, -, -, hcy⟩ := sSlD Ω ε X N (NeZero.pos N)
  refine ⟨fun σ hσ => ?_, fun σ hσ τ hτ => ?_, ?_⟩
  · exact icg _ _ (hz σ hσ) (iadd _ _ (sXiInv Ω ε X l n N M₀ M w g hL hW x y hxy _ _ (hu.eqv σ))
      (iadd _ _ (sGalAct Ω ε X l N w n (NeZero.pos N) σ β hβ).1 hβ).2).1
  · have h0 := m2 (u σ) 0
    rw [Nat.cast_zero, zero_smul] at h0
    have h1 := m1 (u (σ * τ)) (u σ) (tw X (l ^ n) M₀ σ (u τ)) (fun x y => u σ x y ^ 0) fun x y h => by
      simpa using hu.coc σ τ x y h
    have h2 := sXiTw Ω ε X l n N M₀ M w g hL x y (fun z => z = 1) (u τ) σ
    rw [(hcy M σ).2.2.2.1.1 hσ] at h2
    simp only [mul_one] at h2
    have h3 := hE.trans h1 (hadd _ _ _ _ (hE.refl _) (hadd _ _ _ _ h2 h0).2).1
    have h4 := hE.trans (hz _ (mul_mem hσ hτ)) (hadd _ _ _ _ h3 (hE.refl _)).1
    have h5 := (hadd _ _ _ _ (hz σ hσ) (hgal σ _ _ (hz τ hτ))).1
    refine hE.trans h4 (hE.symm ?_)
    convert h5 using 1
    rw [hmul, map_add, map_sub]
    abel
  · obtain ⟨T, hT⟩ := hu.loc
    obtain ⟨⟨t, ht, hβt⟩, -⟩ := hβ
    obtain ⟨E, hEt⟩ := pol_cont X l w n t ht
    refine ⟨T ∪ E, fun σ hσ τ hτ h => ?_⟩
    have h1 := m1 (u σ) (u τ) (u τ) (u τ) fun x y hh => by
      simpa using hT σ τ (fun a ha => h a (Finset.mem_union_left _ ha)) x y hh
    rw [sub_self, add_zero] at h1
    have h2 := hEt (τ⁻¹ * σ) fun a ha => by
      rw [AlgEquiv.mul_apply, h a (Finset.mem_union_right _ ha), ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
    have h3 := hgal τ _ _ (hE.trans (hgal _ _ _ hβt) (hE.trans h2 (hE.symm hβt)))
    rw [← hmul, mul_inv_cancel_left] at h3
    exact hE.trans (hz σ hσ) (hE.trans (hadd _ _ _ _ h1 (hadd _ _ _ _ h3 (hE.refl β)).2).1 (hE.symm (hz τ hτ)))
