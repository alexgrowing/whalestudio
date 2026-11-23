import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KatoTwistedClassNormCompatibleCyclotomic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KmapComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SCls
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.CndIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.InvApi
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.MemGamIff

open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

attribute [local instance] algMdl

section
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

private theorem trM_add (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N M w : ℕ) [NeZero M] (g : SL(2, ℤ)) (a b : X.Khat l) :
    trM X l N M w g (a + b) = trM X l N M w g a + trM X l N M w g b := by
  unfold trM
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [← map_add]
  congr 1
  funext u
  simp [smul_add]

private theorem trM_sub (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N M w : ℕ) [NeZero M] (g : SL(2, ℤ)) (a b : X.Khat l) :
    trM X l N M w g (a - b) = trM X l N M w g a - trM X l N M w g b := by
  rw [eq_sub_iff_add_eq, ← trM_add, sub_add_cancel]

private theorem trM_cg [IsAlgClosure ℚ Ω] (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n N M w : ℕ) [NeZero M] (g : SL(2, ℤ))
    (a b : X.Khat l) (h : AdicCompletion.eval (idl l) (X.Kl l) n (a - b) = 0) :
    CgF X l n (trM X l N M w g a) (trM X l N M w g b) := by
  obtain ⟨-, -, -, hsum, -, hact, -⟩ := sApi Ω ε X l n
  refine hsum _ _ _ _ fun γ _ => hact _ _ _ fun u => ?_
  rw [← smul_sub, map_smul, h, smul_zero]

end

theorem UpperTheory.V.Z.Kato.Nb.sTopRel :
    UpperTheory.V.Z.Kato.Nb.STopRel := by
  intro Ω _ _ _ ε X l _ n N M₀ M w _ _ _ g hL hW c d ws hws hLv x y hxy x' y' hx hy
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  obtain ⟨a, ha, hinv, hs⟩ := hws.top n N M₀ M hLv hN hM (hL.eq ▸ dvd_rfl) (hL.eq ▸ hL.dl.mul_left N) x y hxy x' y' hx hy
  obtain ⟨hI, hG⟩ := sTrM Ω ε X l n N M₀ M w g hL hW a ha fun γ hγ => by
    obtain ⟨k, hk⟩ := hinv γ hγ
    exact ⟨k, by simpa [slU] using congrArg Units.val hk⟩
  obtain ⟨h0, hadd, -⟩ := sInvApi Ω ε X l N w n
  obtain ⟨heq, hpm, -⟩ := sApi Ω ε X l n
  obtain ⟨hcls, hmul, -, hcg, -⟩ := sCls Ω ε X l n
  refine ⟨0 - trM X l N M w g (clsK X l n (a : X.K)), (hadd _ _ h0 hI).2, fun σ hσ => ?_⟩
  obtain ⟨h, hh⟩ := hs σ hσ
  have hW0 : wGen X M l n (slD X N (siegel X c x')) (slD X N (siegel X d y')) σ ≠ 0 :=
    fun e => TopW.topW_ne_zero _ (Subtype.ext e)
  have h1 := sXiOne Ω ε X l n N M₀ M w g hL x y hxy (ws n M₀ σ) ((hws.coc n M₀ hLv).eqv σ)
  have h2 := hcg _ _ _ _ (hcls (slU X (toGQ !![(N : ℤ), 0; 0, 1]) (ws n M₀ σ x y)))
    (hmul _ _ _ _ (hcls (Units.mk0 _ hW0)) (hmul _ _ _ _ (hcls (galU X σ a)) (hcls a)).2).1
    ⟨h, Units.ext (by
      rw [Units.val_mul, Units.val_mul, Units.val_div_eq_div_val, Units.val_pow_eq_pow_val]
      exact hh)⟩
  have h3 := trM_cg X l n N M w g _ _ h2
  rw [trM_add, trM_sub] at h3
  have h4 := heq.trans (heq.symm h3) h1
  have h5 := (hpm _ _ _ _ h4 (hpm _ _ _ _ (heq.symm (hG σ hσ)) (heq.refl (trM X l N M w g (clsK X l n (a : X.K))))).2).2
  convert h5 using 1
  · exact (add_sub_cancel_right _ _).symm
  · rw [map_sub, map_zero]; abel
