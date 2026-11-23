import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
import Formalism.LocalToGlobal.Columns.TiedValLatG
import Formalism.LocalToGlobal.Columns.CoefModB
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClassSumPairingOfIsFormsOf
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClassSumPairingFormsLat

noncomputable section

namespace GlobalTheory.PairAtClass

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2 Matrix

section

variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι]
  (emb : ι → E →+* K) (σ : K →+* ℂ) {R : Ranks} {I : ChainIn E K ι R} (Q : PerIn I) (hQ : Q.Ok)

theorem petersson_single_left (g w : Q.S'.Cl → GlobalTheory.Mem.Col2.Fr emb σ (R.N R.m - 1) → ℂ) (c : Q.S'.Cl) [DecidableEq Q.S'.Cl] :
    Q.ipP emb σ hQ (fun c' => if c' = c then g c' else 0) w = Q.wt c * ipVal emb σ Q.sgT (g c) (w c) := by
  letI := Q.clFin hQ
  simp only [PerIn.ipP, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  refine (Finset.sum_eq_single c (fun b _ hb => ?_) (fun h => absurd (Finset.mem_univ c) h)).trans ?_
  · simp [hb]
  · simp

theorem petersson_single_right (g w : Q.S'.Cl → GlobalTheory.Mem.Col2.Fr emb σ (R.N R.m - 1) → ℂ) (c : Q.S'.Cl) [DecidableEq Q.S'.Cl] :
    Q.ipP emb σ hQ g (fun c' => if c' = c then w c' else 0) = Q.wt c * ipVal emb σ Q.sgT (g c) (w c) := by
  letI := Q.clFin hQ
  simp only [PerIn.ipP, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  refine (Finset.sum_eq_single c (fun b _ hb => ?_) (fun h => absurd (Finset.mem_univ c) h)).trans ?_
  · simp [hb]
  · simp

theorem period_single (hI : I.Ok) (hc : ι → HCParam R) (G : Q.Mt emb σ)
    (w : Q.S'.Cl → GlobalTheory.Mem.Col2.Fr emb σ (R.N R.m - 1) → ℂ) (c : Q.S'.Cl) [DecidableEq Q.S'.Cl] :
    (Q.per emb σ hI hQ hc).period (fun c' => if c' = c then w c' else 0) G =
      Q.wt c * pairB Q.sgT (polOf (Gr emb σ (R.N R.m - 1)) (shiftOf Q.sgT) (fr0 emb σ (R.N R.m - 1)) (w c))
        (Q.rd emb σ G c) := by
  letI := Q.clFin hQ
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  refine (Finset.sum_eq_single c (fun b _ hb => ?_) (fun h => absurd (Finset.mem_univ c) h)).trans ?_
  · simp [hb]
  · simp

end

theorem pair_integral : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] (emb : ι → E →+* K) (σ : K →+* ℂ) {R : Ranks} {I : ChainIn E K ι R} (Q : PerIn I) (hI : I.Ok) (hQ : Q.Ok) (hc : ι → HCParam R) (hF : (Q.S'.fam emb Q.sgT).Ok) (G : Q.Mt emb σ) (g : Q.S'.Cl → GlobalTheory.Mem.Col2.Fr emb σ (R.N R.m - 1) → ℂ), (∀ w, (Q.per emb σ hI hQ hc).period w G = Q.ipP emb σ hQ g w) → ∀ (c : Q.S'.Cl) [DecidableEq Q.S'.Cl] (y : Formalism.L2.DIV.VV K Q.sgT), y ∈ nabAt emb Q.sgT (Q.S'.Lsh c.1 (Q.S'.rep c)) → Q.rd emb σ G c = MvPolynomial.map σ y.1 → ∀ x ∈ (Q.S'.hlat emb Q.sgT hF).L, ∃ a : 𝓞 K, σ (a : K) = ((Nat.card (Q.S'.Stab c) : ℕ) : ℂ) * Q.ipP emb σ hQ (fun c' => if c' = c then g c' else 0) (fun c' => if c' = c then Q.S'.embF emb σ Q.sgT hF x c' else 0) := by
  intro E K ι _ _ _ _ _ _ _ emb σ R I Q hI hQ hc hF G g hP c _ y hy hG x hx
  have hfin := hQ.step.fin_stab c.1 (Q.S'.rep c)
  have hne : ((Nat.card (Q.S'.Stab c) : ℕ) : ℂ) ≠ 0 := by
    haveI := hfin
    exact_mod_cast Nat.card_pos.ne'
  have hint := ((GlobalTheory.PeriodClassSum.pairBDual E K ι _ emb Q.sgT _ (hQ.step.lsh_lat c.1 (Q.S'.rep c)) (x.1 c)).1.1
    (hx c)) y hy
  obtain ⟨a, ha⟩ := hint
  refine ⟨a, ?_⟩
  have e12 : Q.ipP emb σ hQ (fun c' => if c' = c then g c' else 0)
      (fun c' => if c' = c then Q.S'.embF emb σ Q.sgT hF x c' else 0) =
      Q.ipP emb σ hQ g (fun c' => if c' = c then Q.S'.embF emb σ Q.sgT hF x c' else 0) := by
    rw [petersson_single_left, petersson_single_right]
    simp
  rw [e12, ← hP, period_single, hG]
  show _ = _ * (Q.wt c * pairB Q.sgT (polOf (Gr emb σ (R.N R.m - 1)) (shiftOf Q.sgT) (fr0 emb σ (R.N R.m - 1))
    (evV emb (1 : Matrix (Fin (R.N R.m - 1)) (Fin (R.N R.m - 1)) E) Q.sgT σ (x.1 c))) (MvPolynomial.map σ y.1))
  rw [GlobalTheory.PeriodOnStep.polOf_evV, ← GlobalTheory.PeriodOnStep.map_pairB, ← pairBK_apply, PerIn.wt, ← mul_assoc,
    mul_inv_cancel₀ hne, one_mul]
  rw [← ha, LinearMap.toSpanSingleton_apply, Algebra.smul_def, mul_one]

end GlobalTheory.PairAtClass
