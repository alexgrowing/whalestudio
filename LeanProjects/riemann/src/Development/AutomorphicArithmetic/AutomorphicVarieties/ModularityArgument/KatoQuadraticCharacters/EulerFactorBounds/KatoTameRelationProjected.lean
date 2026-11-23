import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SPushPsi
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KmapComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.InvApi
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.DiamEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.CoeffSlD
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.CohApi
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SCycZ
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.BarMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KatoNormRelationTwistTower
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KatoNormRelationLevelTower
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KatoNormRelationTamePrime
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.LiftOk
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SRel0
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.LiftPush
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SN2rho
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SInteg
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.InvCg
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.FrobeniusConjugateInertia
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.InvMemO
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.PushPsi
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SymEx
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.MlTRedCoe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormLeOneOfIsIntegral

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KA UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Nb
open scoped Matrix MatrixGroups Classical

private theorem nsum {l : ℕ} [Fact l.Prime] {ι : Type} (S : Finset ι) (f : ι → Qbar l) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ i ∈ S, ‖f i‖ ≤ C) : ‖∑ i ∈ S, f i‖ ≤ C :=
  IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC h

private theorem cv_wsum {l : ℕ} [Fact l.Prime] {ι : Type} [Fintype ι] (n : ℕ) (cw : ι → Qbar l) (hc : ∀ x, ‖cw x‖ ≤ 1)
    (a b : ι → Fin 2 → Qbar l) (h : ∀ x, Cv n (a x) (b x)) : Cv n (∑ x, cw x • a x) (∑ x, cw x • b x) := by
  intro i
  unfold Cg
  rw [Finset.sum_apply, Finset.sum_apply, ← Finset.sum_sub_distrib]
  refine nsum _ _ _ (norm_nonneg _) fun x _ => ?_
  rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, ← mul_sub, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hc x)).trans (h x i)

private theorem coh_sum {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime]
    (N w n : ℕ) (hN : 0 < N) (A : Type) [CommGroup A] (κ : (Ω ≃ₐ[ℚ] Ω) → A) {ι : Type} (S : Finset ι)
    (z z' : ι → (Ω ≃ₐ[ℚ] Ω) → A → X.Fn l) (h : ∀ i, CohB X l N w n κ (z i) (z' i)) :
    CohB X l N w n κ (∑ i ∈ S, z i) (∑ i ∈ S, z' i) := by
  obtain ⟨h1, -, h3, -⟩ := sCohApi Ω ε X l N w n hN A κ
  induction S using Finset.induction_on with
  | empty => simpa using h1.refl _
  | insert i S hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi]; exact (h3 _ _ _ _ (h i) ih).1

theorem UpperTheory.V.Z.Kato.Nb.kato_tame_relation_projected :
    UpperTheory.V.Z.Kato.Nb.KatoTameRelationProjected := by
  intro l _ Ω _ _ _ ι e gN A W ε X pr N _ cw c d gm ψ cf S hNf hmat hgm hlN hl2 he hcw hj hadm c₀ Y hY
  obtain ⟨hadm3, hcwO⟩ := hadm
  obtain ⟨x₀, hx₀⟩ := hcw
  have hA0 := hadm3 x₀ hx₀
  have hlp : l.Prime := Fact.out
  obtain ⟨c₁, hc₁⟩ := mlTOf symEx sApi sInvApi sBStab sSlD sCohApi sCycZ sTopT kato_normRelation_twistTower kato_normRelation_levelTower l Ω ε X N e hlN hl2 he
  have hm := fun x : {x // cw x ≠ 0} => sN2rho l Ω ι e gN A W ε X pr N x.1 c d gm ψ cf (hadm3 x.1 x.2) he hmat
  choose m hm using hm
  have hInt := sInteg l Ω ι e gN A W ε X pr N x₀ c d gm ψ cf hA0 he hmat
  obtain ⟨Yx, hYx, hYsum⟩ := hY
  obtain ⟨S', hSS', hS'⟩ := sEuler l Ω ι e gN A W ε X pr N x₀ c d gm ψ cf hA0 he hlN S hNf hmat
  refine ⟨Finset.univ.sup m + c₁, S', fun w hw => hNf.unr w (fun h => hw (hSS' h)), ?_⟩
  intro n hn w hw hdiv ψw hK hsurj
  obtain ⟨hpP, hpcop, a, δ, ha, hδ, hhec, hfrob⟩ := hS' w hw
  haveI : NeZero (normV w) := ⟨hpP.ne_zero⟩
  have hpl : (normV w).Coprime l := Nat.Coprime.coprime_dvd_right ⟨N * c * d, by ring⟩ hpcop
  have hplN : (normV w).Coprime (l * N) := Nat.Coprime.coprime_dvd_right ⟨c * d, by ring⟩ hpcop
  have hY' := fun x : {x // cw x ≠ 0} => hc₁ (c₀ + c₁) (by omega) ι gN A W pr x.1 c d gm ψ cf (hadm3 x.1 x.2)
    (normV w) hpP hpcop
  choose Y' hY'Z hY'coc hY'push hY'cont hY'O using hY'
  have hEC := sEulCg l Ω ι e gN A W ε X pr N x₀ c d gm ψ cf hA0 he (normV w) n hpP hn hdiv a δ ha hδ
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  obtain ⟨hc1, hd1, hcc, hdc, -, -, -, -, -, -, hgN, -⟩ := hA0
  have hLaws : ∃ ws, Laws X l c d ws :=
    symEx Ω ε X l c d hlp hc1 hd1 (Nat.Coprime.coprime_dvd_right ⟨l * N, by ring⟩ hcc)
      (Nat.Coprime.coprime_dvd_right ⟨l * N, by ring⟩ hdc)
  have hodd : Odd (2 * e - 1) := ⟨e - 1, by omega⟩
  have hLW := sLiftOk Ω ε X l N (2 * e - 1) hl2 hlN hodd
  have hHyp : ∀ r₀, Hyp l N c d (gm r₀) := fun r₀ => ⟨hl2, hlN, hc1, hd1, hcc, hdc, hgN r₀⟩
  have hkey := fun (x : {x // cw x ≠ 0}) (r : ℕ) =>
    hm x (normV w) hpP hplN a δ ha hδ hhec c₀ c₁ r r (Yx x.1 r) (Y' x r) _ _
      (sRel0 l Ω ι e gN A W ε X pr N x.1 c d gm ψ cf (hadm3 x.1 x.2) he c₀ (Yx x.1) (hYx x.1) r r)
      (sRelT l Ω ι e gN A W ε X pr N x.1 c d gm ψ cf (hadm3 x.1 x.2) he (normV w) hpl (c₀ + c₁) (Y' x) (hY'Z x) r r)
      (by
        clear hc₁ hm hY'Z hY'coc hY'push hY'cont hY'O hYx hYsum hS' hInt hEC hadm3 hmat hNf hgm hj hfrob hhec
        have h := coh_sum X l N (2 * e - 1) r hN0 _ (fun s => ((cycMod ℚ Ω l r) s)⁻¹) Finset.univ _ _
          (fun r₀ => kato_norm_relation_tame_prime Ω ε X l N (normV w) x.1 c d (2 * e - 1) (gm r₀) (hHyp r₀) hpP hpcop hLaws hLW r r)
        convert h using 1
        all_goals try rfl
        all_goals funext s y
        all_goals simp [Finset.sum_apply, Finset.smul_sum, map_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib]
        all_goals exact Finset.sum_comm)
  choose bN hbN hCvN using hkey
  have hO1 : ∀ z ∈ cf.O, ‖z‖ ≤ 1 := fun z hz => GlobalTheory.CoefCoord.norm_le_one cf ⟨z, hz⟩
  have hlO : ((l : ℕ) : Qbar l) ∈ cf.O := natCast_mem cf.O l
  have hldvd : l ∣ normV w - 1 := dvd_trans (dvd_pow_self l (by omega : n ≠ 0)) hdiv
  have hsp := fun (x : {x // cw x ≠ 0}) (r : ℕ) =>
    sSpec l Ω ι e gN A W ε X pr N x.1 c d gm ψ cf (hadm3 x.1 x.2) he hmat (normV w) r hpP hldvd a δ
      (((l : ℕ) : Qbar l) ^ (m x + c₁)) (hO1 a ha) (hO1 δ hδ) (hO1 _ (pow_mem hlO _)) (Yx x.1 r)
      (fun s y => ((l : ℕ) : Qbar l) ^ (m x) • ∑ t, Y' x r s (t, y)) (bN x r)
      ((sInteg l Ω ι e gN A W ε X pr N x.1 c d gm ψ cf (hadm3 x.1 x.2) he hmat).2.2.2.2.2.2 c₀ (Yx x.1) (hYx x.1) r)
      (hbN x r) (fun s y => by
        have h := hCvN x r s y
        rw [mul_comm, ← smul_smul] at h
        exact h)
  choose b' hb'O hb'Cv using hsp
  set M := Finset.univ.sup m with hM
  have hmM : ∀ x, m x ≤ M := fun x => Finset.le_sup (Finset.mem_univ x)
  obtain ⟨Yt, hYt⟩ : ∃ Yt : (r : ℕ) → (Ω ≃ₐ[ℚ] Ω) → (ZMod (normV w))ˣ × (ZMod (l ^ r))ˣ → Fin 2 → Qbar l,
      ∀ r s y, Yt r s y = ∑ x, (cw x.1 * ((l : ℕ) : Qbar l) ^ M) • Y' x r s y :=
    ⟨fun r s y => _, fun r s y => rfl⟩
  have hcoc : ∀ r s s' y, Yt r (s * s') y = Yt r s y + rhoK W e ψ s *ᵥ Yt r s' (y * cycT l r (normV w) s) := by
    intro r s s' y
    simp only [hYt, hY'coc, smul_add, Finset.sum_add_distrib, Matrix.mulVec_sum, Matrix.mulVec_smul]
  have hpush : ∀ r, Yt r = push (Prod.map id (redL l r)) (Yt (r + 1)) := by
    intro r
    funext s y
    simp only [push, hYt]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hY'push x r]
    simp only [push, Finset.smul_sum]
  have hcont : ∀ r y i, Continuous fun s => Yt r s y i := by
    intro r y i
    simp only [hYt, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact continuous_finset_sum _ fun x _ => continuous_const.mul (hY'cont x r y i)
  have hmem : ∀ r s u i, Yt r s u i ∈ cf.O := by
    intro r s u i
    rw [hYt, Finset.sum_apply]
    refine Subalgebra.sum_mem _ fun x _ => ?_
    rw [Pi.smul_apply, smul_eq_mul]
    exact Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (hcwO x.1) (pow_mem hlO _)) (hY'O x r s u i)
  obtain ⟨Yw, hYw1, hYw2, hYw3, hYw4, hYw5⟩ :=
    sPushPsi l Ω cf (rhoK W e ψ) (normV w) n ψw hK Yt hcoc hpush hcont hmem
  have hsub : ∀ f : ZMod N → (Fin 2 → Qbar l), ∑ x, cw x • f x = ∑ x : {x // cw x ≠ 0}, cw x.1 • f x.1 := by
    intro f
    rw [← Finset.sum_filter_of_ne (p := fun x => cw x ≠ 0) (fun x _ h hc => h (by simp [hc]))]
    exact Finset.sum_subtype _ (fun x => by simp) _
  refine ⟨Yw, eul l e (normV w) a δ, 1, fun r => ∑ x, (cw x.1 * ((l : ℕ) : Qbar l) ^ (M - m x)) • b' x r,
    hYw1, hYw2, hYw3, hYw4, hEC.1, by simp, ?_, ?_, ?_⟩
  · intro r i
    beta_reduce
    rw [Finset.sum_apply]
    refine Subalgebra.sum_mem _ fun x _ => ?_
    rw [Pi.smul_apply, smul_eq_mul]
    exact Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (hcwO x.1) (pow_mem hlO _)) (hb'O x r i)
  · intro r s i
    have hcv := cv_wsum r (fun x => cw x.1 * ((l : ℕ) : Qbar l) ^ (M - m x))
      (fun x => by
        rw [norm_mul, norm_pow]
        exact mul_le_one₀ (hO1 _ (hcwO x.1)) (by positivity) (pow_le_one₀ (norm_nonneg _) (hO1 _ hlO)))
      _ _ (fun x => hb'Cv x r s)
    have hL : ∀ η : (ZMod (l ^ r))ˣ → Qbar l, (∑ a, spec η (fun s x => Yw r s (a, x)) s) =
        ∑ x, (cw x.1 * ((l : ℕ) : Qbar l) ^ (M - m x)) •
          spec η (fun s y => ((l : ℕ) : Qbar l) ^ (m x) • ∑ t, Y' x r s (t, y)) s := by
      intro η
      simp only [spec]
      calc ∑ a, ∑ y, η y • Yw r s (a, y) = ∑ y, η y • ∑ a, Yw r s (a, y) := by
            rw [Finset.sum_comm]
            simp only [Finset.smul_sum]
        _ = ∑ y, η y • ∑ t, Yt r s (t, y) := by simp only [hYw5]
        _ = _ := by
            simp only [hYt, Finset.smul_sum, smul_smul]
            refine (Finset.sum_congr rfl fun y _ => Finset.sum_comm).trans (Finset.sum_comm.trans ?_)
            refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
              Finset.sum_congr rfl fun t _ => ?_
            have hp : ((l : ℕ) : Qbar l) ^ M = ((l : ℕ) : Qbar l) ^ (M - m x) * ((l : ℕ) : Qbar l) ^ (m x) := by
              rw [← pow_add, Nat.sub_add_cancel (hmM x)]
            rw [hp]
            congr 1
            ring
    have hR : ∀ η : (ZMod (l ^ r))ˣ → Qbar l,
        eul l e (normV w) a δ • ((l : ℕ) : Qbar l) ^ (M + c₁) • spec η (Y r) s +
          (mat W s *ᵥ (∑ x, (cw x.1 * ((l : ℕ) : Qbar l) ^ (M - m x)) • b' x r) -
            ∑ x, (cw x.1 * ((l : ℕ) : Qbar l) ^ (M - m x)) • b' x r) =
        ∑ x, (cw x.1 * ((l : ℕ) : Qbar l) ^ (M - m x)) •
          (eul l e (normV w) a δ • ((l : ℕ) : Qbar l) ^ (m x + c₁) • spec η (Yx x.1 r) s +
            (mat W s *ᵥ b' x r - b' x r)) := by
      intro η
      simp only [smul_add, Finset.sum_add_distrib]
      congr 1
      · simp only [spec, hYsum, hsub, Finset.smul_sum, smul_smul]
        refine Finset.sum_comm.trans (Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_)
        have hp : ((l : ℕ) : Qbar l) ^ (M + c₁) =
            ((l : ℕ) : Qbar l) ^ (M - m x) * ((l : ℕ) : Qbar l) ^ (m x + c₁) := by
          rw [← pow_add]
          congr 1
          have := hmM x
          omega
        rw [hp]
        congr 1
        ring
      · simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, smul_sub, Finset.sum_sub_distrib]
    beta_reduce
    rw [hL, hR]
    exact hcv i
  · intro B σ hB hF
    obtain ⟨he1, htr, hdet⟩ := hfrob B σ hB hF
    exact hEC.2 σ hInt.2.1 he1 htr hdet
