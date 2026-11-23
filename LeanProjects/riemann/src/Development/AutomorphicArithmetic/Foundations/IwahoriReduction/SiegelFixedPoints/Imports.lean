import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.IsThBIff
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamOfLSmulIff
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamFROfIsLamF
import Development.AbelianVarietyTheory.Definitions.Foundations.ActWBOfInvariant
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalBActCommGamma0CapGamma0LevelShimuraReciprocitStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiamondCommutesHeckeU
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.ExistsSeries
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.Actcls

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

theorem UpperTheory.Kd.L.twist :
    ∀ (l : ℕ) [Fact l.Prime] (N : ℕ) [NeZero N] (w : ℕ), Odd w → ∃ (c₁ : ℕ) (κ : ℚ), κ ≠ 0 ∧ ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [CharZero Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)), Par l N c d gm → (∀ r₀, gm r₀ ∈ CongruenceSubgroup.Gamma1 N) → ∀ (A : ValuationSubring Ω), ((l : ℕ) : Ω) ∈ A.nonunits → ∀ (x : ZMod N) (m n c₀ : ℕ), 1 ≤ m → m ≤ n → ∀ bB : (Ω ≃ₐ[ℚ] Ω) → X.Fn l, (∀ σ ∈ fixMu Ω (topMu l n m N), LiftB X l N w n c₀ (clsBmu X l n m N x c d (w + 2) gm σ) (bB σ)) → ∀ (y : (ZMod (l ^ m))ˣ) (δ : (ZMod N)ˣ), ∃ g : HahnSeries ℚ Ω, (∀ r, g.coeff r ∈ A) ∧ ∀ s, Stab A s → (∀ a ∈ A, A.valuation (s a - a) < 1) → s (zt ε l m) = zt ε l m → ∀ φ : HahnSeries ℚ Ω, IsThB X A N l n (X.diam N l (δ : ZMod N).val (GlobalTheory.KA.push (redM l n m (N * N)) (bTop X l n m N bB) s y)) φ → ∀ tt : ZMod (l ^ n), IsLamG ε l n m s tt → ∀ (β : ℕ) (t : ℤ), (β : ZMod (l ^ m)) = (y : ZMod (l ^ m)) → (β : ZMod N) = 1 → (l : ℤ) ^ m * t ≡ 1 [ZMOD N] → ∀ i : ℕ, CgA A l n ((l : Ω) ^ c₁ * φ.coeff (i : ℚ)) ((l : Ω) ^ c₁ * ((l : Ω) ^ c₀ * (κ : Ω) * (tt.val : Ω) * (l : Ω) ^ m * toQ (l ^ m) (pieceT N l m m (w + 2) (1 : DirichletCharacter Ω (l ^ m)) (c : ℤ) (d : ℤ) ((x.val : ℤ) * t * (((δ⁻¹ : (ZMod N)ˣ) : ZMod N).val : ℤ), 0) (t * (((δ⁻¹ : (ZMod N)ˣ) : ZMod N).val : ℤ), 0) (eOm ε (1 / ((N : ℚ) * (l : ℚ) ^ m)) ^ β) ((unitSet l m).filter fun γ => (γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ m))).det = 1)) i) + (s (g.coeff (i : ℚ)) - g.coeff (i : ℚ))) := by
  intro l _ N _ w hw
  obtain ⟨c₁, κ, hκ, H⟩ := UpperTheory.Kd.L.law l N w hw
  refine ⟨c₁, κ, hκ, ?_⟩
  intro Ω _ _ _ _ ε X c d gm hP hG1 A hA x m n c₀ hm hmn bB hB y δ
  have hl : l.Prime := Fact.out
  have hl0 : l ≠ 0 := hl.ne_zero
  have hcopδ : ((δ : ZMod N).val).Coprime N := ZMod.val_coe_unit_coprime δ
  have hD : IsDiam N l (δ : ZMod N).val (sgD N l (δ : ZMod N).val) :=
    DiamU.isDiam_sgD_of_coprime' hl0 hcopδ
  obtain ⟨hP', hL⟩ := actcls ε X l N c d gm hP _ hD.1
  obtain ⟨g, hgA, hg⟩ := H ε X c d (fun r => gm r * sgD N l (δ : ZMod N).val) hP' A hA x m n c₀ hm hmn
    (fun σ => X.act l ((sgD N l (δ : ZMod N).val : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (bB σ))
    (fun σ hσ => hL x w m n c₀ hw hm σ (bB σ) (hB σ hσ)) y
  refine ⟨g, hgA, ?_⟩
  intro s hs1 hs2 hs3 φ hφ tt htt β t hβy hβ1 hlt i
  have key := hg s hs1 hs2 hs3 φ ?_ tt htt β t (((δ⁻¹ : (ZMod N)ˣ) : ZMod N).val : ℤ) ?_ hβy hβ1 hlt i
  · rw [show ((x.val : ℤ) * t * (((δ⁻¹ : (ZMod N)ˣ) : ZMod N).val : ℤ))
        = (x.val : ℤ) * (((δ⁻¹ : (ZMod N)ˣ) : ZMod N).val : ℤ) * t by ring,
      show t * (((δ⁻¹ : (ZMod N)ˣ) : ZMod N).val : ℤ) = (((δ⁻¹ : (ZMod N)ˣ) : ZMod N).val : ℤ) * t by ring]
    exact key
  · have hNM : NeZero (topM l n m (N * N)) :=
      ⟨by unfold topM; exact mul_ne_zero (pow_ne_zero _ hl0) (mul_ne_zero (NeZero.ne N) (NeZero.ne N))⟩
    have hcop : N.Coprime l := (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hl).mpr hP.cop))
    obtain ⟨ψ, hψ1, hψ2⟩ := X.j_hol
    have hpush : GlobalTheory.KA.push (redM l n m (N * N))
        (bTop X l n m N (fun σ => X.act l ((sgD N l (δ : ZMod N).val : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (bB σ))) s y
        = X.diam N l (δ : ZMod N).val (GlobalTheory.KA.push (redM l n m (N * N)) (bTop X l n m N bB) s y) := by
      simp only [GlobalTheory.KA.push, Tower.diam, map_sum]
      refine Finset.sum_congr rfl fun y' _ => ?_
      simp only [bTop]
      exact GlobalTheory.T.galB_act_comm_gamma0CapGamma0Level_shimuraReciprocity ε X ε.injective ⟨ψ, hψ2, hψ1⟩ N l w hP.odd hP.five hcop hw _ hD.1 _ _
        (hB _ (shArg_mem_fixMu _ s y')).1
    rw [hpush]
    exact hφ
  · have h1 := (CongruenceSubgroup.Gamma1_mem N (gm 1)).mp (hG1 1)
    have h2 := CongruenceSubgroup.Gamma0_mem.mp hD.1.1
    have h3 := hD.2
    have hdet := congrArg (fun z : ℤ => (z : ZMod N)) (Matrix.SpecialLinearGroup.det_coe (sgD N l (δ : ZMod N).val))
    simp only [Matrix.det_fin_two] at hdet
    unfold GlobalTheory.KZ.en at h3 ⊢
    push_cast at hdet h3 ⊢
    rw [ZMod.natCast_zmod_val] at h3
    rw [ZMod.natCast_zmod_val, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    push_cast
    rw [h1.1, h2, mul_zero, add_zero, one_mul]
    rw [h2, mul_zero, sub_zero, h3] at hdet
    exact (Units.eq_inv_of_mul_eq_one_right hdet).symm
