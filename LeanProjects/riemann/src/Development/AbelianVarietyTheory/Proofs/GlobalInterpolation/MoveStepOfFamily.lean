import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.BelowFiniteNonempty
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemMulLatIff

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.ThetaMove

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

theorem moveLaw_at (X : Fields) (Pr : Primes X) (R : Ranks) (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S)
    (cst : LocCst X (rowSG Pr sel mu)) (u : Pr.Word)
    (D : D7) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)
    (hX : X.Ok) (hPr : Pr.Ok) (hCh : Ch.FromHecke W s.σ₀) (hsel : IsSel X sel) (hT : Pr.T u ∈ S) (hg : ∀ k, Pr.g k ∈ S)
    (hs : s.Ok) (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hχ : TaylorLogMetric.IsChi D χ)
    (hcop : ∀ P ∈ Sall sel mu u, Nat.Coprime (Ideal.absNorm cc) (Ideal.absNorm P.asIdeal))
    (hEq : B.EqP χ) (hLat : B.LatAll) (hTh : ∀ a b, Even a → Even b → B.ThZeroMem a b)
    (i : ℕ) (hi : i < R.m) (b : ℕ) (hb : b = R.N (i + 1)) (lam' : X.Tau → DomWeight b)
    (N₁ N₂ : Submodule (𝓞 X.E) (Sp X.E (R.N i))) (N₁' N₂' : Submodule (𝓞 X.E) (Sp X.E b))
    (fr : Frs X.E (R.N i) (rowSG Pr sel mu)) (fr' : Frs X.E b (rowSG Pr sel mu)) (Ξ : HomE X.E (R.N i) b → X.K)
    (h₁ : IsSdLat N₁) (h₂ : IsSdLat N₂) (h₁' : IsSdLat N₁') (h₂' : IsSdLat N₂')
    (ag : AgreeOff (Pr.T u) N₁ N₂) (ag' : AgreeOff (Pr.T u) N₁' N₂')
    (b₁ : InBox (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N₁ N₁' Ξ)
    (b₂ : InBox (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N₂ N₂' Ξ)
    (j₁ : JetsIn (ambOf s B χ cD) (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) (W.lamTrue u i) (nuLast W u i) N₁ N₁')
    (j₂ : JetsIn (ambOf s B χ cD) (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) (W.lamTrue u i) (nuLast W u i) N₂ N₂') :
    kerOf (stepT W Ch sel mu cst (ambOf s B χ cD) u i lam') (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N₁ fr N₁' fr' Ξ =
      moveScal Ch mu u i N₁ N₂ N₁' N₂' •
        kerOf (stepT W Ch sel mu cst (ambOf s B χ cD) u i lam') (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N₂ fr N₂' fr' Ξ := by
  classical
  have ea : Even (R.N i) := even_N R i
  have eb : Even b := hb ▸ even_N R (i + 1)
  have hA := GlobalTheory.ThetaMove.SeamMoves.moves_ambOf X D s cc δ B χ cD (R.N i) b hX hs hcc hχ hEq hLat
    (hTh _ _ ea eb) ea eb
  have bad := GlobalTheory.ThetaMove.BadPrimes.bad_primes X Pr sel S mu u hX hPr hsel hT hg
  have hU : (ambOf s B χ cD).AAUnit (Sall sel mu u) := fun P hP =>
    GlobalTheory.PeriodIdealUnit.locP_AA_eq_one X D s cc δ B χ cD P (bad P hP).2.1 (bad P hP).2.2.1 (hcop P hP)
  set A := ambOf s B χ cD with hAdef
  set Sa := Sall sel mu u with hSa
  have hq : 0 < ∏ P : rowSG Pr sel mu, Formalism.L2.Col.qOf P.1 :=
    Finset.prod_pos fun P _ => Nat.pos_of_ne_zero fun h => P.1.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have hTpos : 0 < Pr.T u := (hPr.T_prime u).pos
  have hcA : 0 < cAof sel mu cst := pow_pos hq _
  have hcB : 0 < cBof sel mu cst u := Nat.mul_pos hTpos (pow_pos hq _)
  have hoff : ∀ Q : HeightOneSpectrum (𝓞 X.E), Q ∉ Sa → conjPrime₂ Q ∉ Sa → ((Pr.T u : ℕ) : 𝓞 X.E) ∉ Q.asIdeal := by
    intro Q h h' hQ
    rw [← hPr.piT_norm u] at hQ
    rcases Q.isPrime.mem_or_mem hQ with h1 | h1
    · exact h (Finset.mem_union_left _ ((mem_divs (hPr.piT_ne_zero u) Q).2 h1))
    · exact h' (Finset.mem_union_left _ ((mem_divs (hPr.piT_ne_zero u) _).2 ((mem_conjP Q _).2 h1)))
  have hord : ∀ {n : ℕ} {M M' : Submodule (𝓞 X.E) (Sp X.E n)} {P : HeightOneSpectrum (𝓞 X.E)},
      localization₂ P.asIdeal M = localization₂ P.asIdeal M' → ordDet P M = ordDet P M' := fun h => by
    unfold ordDet frameAt
    rw [h]
  let ex : HeightOneSpectrum (𝓞 X.E) → ℤ := fun P =>
    ((b / 2 : ℕ) : ℤ) * idxExp P N₁ N₂ - ((R.N i / 2 : ℕ) : ℤ) * idxExp P N₁' N₂'
  have hTR : (0 : ℝ) < (Pr.T u : ℝ) := by exact_mod_cast hTpos
  have hρ2 : (∏ P ∈ Pr.vT u, (Pr.T u : ℝ) ^ ex P) ^ 2 =
      ∏ P ∈ Sa, ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ (volExp P N₂ N₂' - volExp P N₁ N₁') := by
    rw [← Finset.prod_pow, ← Finset.prod_subset (s₁ := Pr.vT u) (s₂ := Sa) Finset.subset_union_left]
    · refine Finset.prod_congr rfl fun P hP => ?_
      rw [hPr.vT_norm u P hP, ← zpow_natCast, ← zpow_mul]
      congr 1
      obtain ⟨a', ha'⟩ := ea
      obtain ⟨b', hb'⟩ := eb
      have e1 : R.N i / 2 = a' := by omega
      have e2 : b / 2 = b' := by omega
      have e3 : (R.N i : ℤ) = 2 * a' := by omega
      have e4 : (b : ℤ) = 2 * b' := by omega
      simp only [ex, volExp, idxExp, e1, e2, e3, e4]
      push_cast
      ring
    · intro P hP hP'
      have h1 : ((Pr.T u : ℕ) : 𝓞 X.E) ∉ P.asIdeal := fun h => hP' ((bad P hP).2.2.2.1 h)
      rw [volExp, volExp, hord (ag P h1), hord (ag' P h1), sub_self, zpow_zero]
  have box : ∀ {N : Submodule (𝓞 X.E) (Sp X.E (R.N i))} {N' : Submodule (𝓞 X.E) (Sp X.E b)},
      InBox Sa (cAof sel mu cst) (cBof sel mu cst u) N N' Ξ →
      InBox Sa (cAof sel mu cst) (cBof sel mu cst u) N N' fun x => A.σ₀ (Ξ x) := fun h =>
    ⟨fun x hx => h.1 x fun h0 => hx (by simp [h0]), fun x y hy => by simp only [h.2 x y hy]⟩
  have hcore := core hA (fun P hP => (bad P hP).1) hU h₁ h₂ h₁' h₂' (fun Q h h' => ag Q (hoff Q h h'))
    (fun Q h h' => ag' Q (hoff Q h h')) hcA hcB (box b₁) (box b₂) (Finset.prod_pos fun P _ => zpow_pos hTR _) hρ2
  have f₁ := GlobalTheory.finite_divLat_quot_mulLat_homAt X.E _ _ Sa N₁ N₁' _ _ h₁.1 h₁'.1 hcA hcB
  have f₂ := GlobalTheory.finite_divLat_quot_mulLat_homAt X.E _ _ Sa N₂ N₂' _ _ h₂.1 h₂'.1 hcA hcB
  have := @Fintype.ofFinite _ f₁
  have := @Fintype.ofFinite _ f₂
  have hj := GlobalTheory.jetOp_identity_of_entire X (R.N i) b A.σ₀ A.cD (W.lamTrue u i) lam' (nuLast W u i) _ _ _ _ _ _ (A.chiF _ _ N₁ N₁')⁻¹ (A.chiF _ _ N₂ N₂')⁻¹
    (∏ P ∈ Pr.vT u, (Pr.T u : X.K) ^ ex P)
    (fun q => analytic_thInd (S := Sa) hA h₁ h₁' (cBof sel mu cst u)
      (Function.surjInv (Submodule.Quotient.mk_surjective _) q : ↥(divLat (cAof sel mu cst) (homAt Sa N₁ N₁'))))
    (fun q => analytic_thInd (S := Sa) hA h₂ h₂' (cBof sel mu cst u)
      (Function.surjInv (Submodule.Quotient.mk_surjective _) q : ↥(divLat (cAof sel mu cst) (homAt Sa N₂ N₂'))))
    (fun q m hm => j₁ _ (Subtype.prop _) m hm) (fun q m hm => j₂ _ (Subtype.prop _) m hm)
    (fun z => by
      have h1 := hcore z
      unfold latSum at h1
      rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype] at h1
      refine h1.trans ?_
      congr 1
      simp)
  have hmU := mUof_conj W Ch sel mu u s.σ₀ hX hPr hCh hsel hT hg i hi
  have m₁ := GlobalTheory.MuOffMove.muOff_move X Pr sel S mu u _ _ N₁ N₂ hX hPr hsel hT hg hmU h₁ h₂ ag
  have m₂ := GlobalTheory.MuOffMove.muOff_move X Pr sel S mu u _ _ N₁' N₂' hX hPr hsel hT hg hmU h₁' h₂' ag'
  unfold stepT
  rw [kerOf_eq, kerOf_eq]
  refine (congrArg _ hj).trans ?_
  rw [smul_smul, smul_smul]
  congr 1
  have hsc : moveScal Ch mu u i N₁ N₂ N₁' N₂' =
      (∏ P ∈ Pr.vT u, ((mUof Ch mu i P ^ (-idxExp P N₁ N₂) : X.Kˣ) : X.K)) *
        (∏ P ∈ Pr.vT u, ((mUof Ch mu i P ^ (-idxExp P N₁' N₂') : X.Kˣ) : X.K))⁻¹ * ∏ P ∈ Pr.vT u, (Pr.T u : X.K) ^ ex P := by
    rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun P _ => ?_
    rw [locScal, ← Units.val_inv_eq_inv_val, ← Units.val_mul, ← zpow_neg, ← zpow_add]
    congr 3
    ring
  rw [hsc, muInvDet, muInvDet, muInvDet, muInvDet, m₁, m₂]
  simp only [mul_inv]
  ring

open GlobalTheory.KerT in

theorem moveStep_of_family : ∀ (Z : Dat) (H : D7) (s : Seam H Z.X) (cc : Ideal (𝓞 H.host.K)) (δ : ℂ) (B : Base H cc δ)
    (χ : TaylorLogMetric.IdE H → ℂ) (cD : H.what₂.Tau → ℂ) (sel : HeightOneSpectrum (𝓞 Z.X.F) → HeightOneSpectrum (𝓞 Z.X.E)) (S : Set ℕ)
    (mu : Tup Z.X.F Z.X.E Z.X.K S) (cst : LocCst Z.X (rowSG Z.Pr sel mu)) (u : Z.Pr.Word) (i : ℕ), i < Z.R.m →
    Hyp Z s cc δ χ cD sel S mu cst u → B.EqP χ → B.LatAll → (∀ a b, Even a → Even b → B.ThZeroMem a b) →
    GlobalTheory.KerT.JetsAll Z.W sel mu cst (ambOf s B χ cD) u i (i + 1) →
    MoveStep Z.W Z.Ch sel mu cst (ambOf s B χ cD) u i (i + 1) := by
  intro Z H s cc δ B χ cD sel S mu cst u i hi h hEq hLat hTh hJ N₁ N₂ N₁' N₂' fr fr' Ξ h₁ h₂ h₁' h₂' ag ag' b₁ b₂
  obtain ⟨hs, hσ, hcc, -, hχ, -⟩ := h.ana
  exact moveLaw_at Z.X Z.Pr Z.R Z.W Z.Ch sel S mu cst u H s cc δ B χ cD h.ok.fields h.ok.primes (hσ ▸ h.ok.hecke) h.isSel h.T_mem
    h.g_mem hs hcc hχ h.cop hEq hLat hTh i hi _ rfl _ N₁ N₂ N₁' N₂' fr fr' Ξ h₁ h₂ h₁' h₂' ag ag' b₁ b₂ (hJ _ _ h₁ h₁') (hJ _ _ h₂ h₂')

end GlobalTheory.ThetaMove
