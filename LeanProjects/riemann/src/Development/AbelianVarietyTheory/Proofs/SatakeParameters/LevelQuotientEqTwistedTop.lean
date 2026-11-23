import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.XiAtPenultimateEqXiCpl1
import Formalism.LocalToGlobal.Columns.KOneCharacterTrivialNearOne
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.Columns.ChainTwTopQ
import Formalism.LocalToGlobal.Columns.DiagUnitMemAndNormalizesKOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhiTopTargetTwist
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlockExtMemTwistedK1Statement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrincipalCongruenceLeTwistedK1Statement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedK1BlockDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowTypeCharacterBlockSumOneEqStatement

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2 GlobalTheory.TopStep

namespace GlobalTheory.TopLevQ

section Gen

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K]

theorem lamQB_prinCong (P : HeightOneSpectrum (𝓞 E)) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {N : ℕ} (r c : ℕ) (hc : 0 < c)
    (k : GLint E N P) (hk : k ∈ prinCong N P c) : LocE.lamQB ξ r N k.1.toLinearMap = 1 := by
  have h1 := redGL_of_prinCong hc hk
  refine twLamQB_red_one P ξ le_rfl k.1 fun s t _ _ _ _ => ⟨glint_entry k s t, ?_⟩
  have h2 := congrArg (fun M : GL (Fin N) (𝓞 E ⧸ P.asIdeal) => (M : Matrix (Fin N) (Fin N) (𝓞 E ⧸ P.asIdeal)) s t) h1
  simp only [redGL_val, Units.val_one, Matrix.one_apply] at h2
  exact h2

theorem levI_ext {N : ℕ} {P : HeightOneSpectrum (𝓞 E)} {A B : LevI E K N P} (e : A.H = B.H)
    (e' : ∀ k (h1 : k ∈ A.H) (h2 : k ∈ B.H), A.lam ⟨k, h1⟩ = B.lam ⟨k, h2⟩) : A = B := by
  obtain ⟨H, lam⟩ := A
  obtain ⟨H', lam'⟩ := B
  obtain rfl : H = H' := e
  obtain rfl : lam = lam' := MonoidHom.ext fun a => e' a.1 a.2 a.2
  rfl

theorem level_congruence_eq_twisted_k1 (P : HeightOneSpectrum (𝓞 E)) (hu : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)
    {N n : ℕ} (hN : N = n + 1) (r b c : ℕ) (hn : n = r + b) :
    levCong hN P c ⟨HQ (𝓞 E ⧸ P.asIdeal) n r b, (lamQ ξ n r b)⁻¹⟩ = kOneLevel P N r (c + 1) ξ := by
  set l : Lev (𝓞 E ⧸ P.asIdeal) K n := ⟨HQ (𝓞 E ⧸ P.asIdeal) n r b, (lamQ ξ n r b)⁻¹⟩
  have hH : (levCong hN P c l).H = twK1H P N r (c + 1) := by
    refine le_antisymm (sup_le ?_ (GlobalTheory.T.principal_congruence_le_twisted_k1 P r (c + 1) c.succ_pos)) fun g hg => ?_
    · rintro _ ⟨j, hj, rfl⟩
      exact GlobalTheory.T.block_ext_mem_twisted_k1 P hu hN r b (c + 1) hn j hj
    · obtain ⟨j, hj, hb⟩ := GlobalTheory.T.twisted_k1_block_decomposition P hN r b c hn g hg
      exact (mem_levCong hN c l g).2 ⟨j, hj, hb⟩
  refine levI_ext hH fun k h1 h2 => ?_
  obtain ⟨j, hj, hb⟩ := (mem_levCong hN c l k).1 h1
  rw [levCong_lam hN c l h1 hj hb]
  apply Units.ext
  have hjK : extI hN P j ∈ twK1H P N r (c + 1) := GlobalTheory.T.block_ext_mem_twisted_k1 P hu hN r b (c + 1) hn j hj
  have hbK : (extI hN P j)⁻¹ * k ∈ twK1H P N r (c + 1) := GlobalTheory.T.principal_congruence_le_twisted_k1 P r (c + 1) c.succ_pos hb
  have hk : (⟨k, h2⟩ : twK1H P N r (c + 1)) = ⟨_, hjK⟩ * ⟨_, hbK⟩ := Subtype.ext (mul_inv_cancel_left _ _).symm
  show _ = ((kOneCharacter P N r (c + 1) ξ).toHomUnits ⟨k, h2⟩ : K)
  rw [MonoidHom.coe_toHomUnits, hk, map_mul]
  show _ = LocE.lamQB ξ r N (extI hN P j).1.toLinearMap * LocE.lamQB ξ r N ((extI hN P j)⁻¹ * k).1.toLinearMap
  rw [lamQB_prinCong P ξ r (c + 1) c.succ_pos _ hb, mul_one, extI_val, GlobalTheory.T.rowTypeCharacter_blockSumOne_eq P ξ hN r (by omega) j.1,
    GlobalTheory.TopLaw.lamQB_eq_red ξ hn j hj]
  rfl

end Gen

section Top

theorem levQTop_eq_twTt : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S), X.Ok → Pr.Ok → IsSel X sel → (∀ i, Pr.g i ∈ S) → (∀ v, Pr.T v ∈ S) → levQTop R sel mu (4 * R.m) = twTt (R := R) sel mu R.m := by
  intro X Pr R _ sel S mu hX hPr hsel _ _
  funext Q
  have hu : ((qOf Q.1 : ℕ) : 𝓞 X.E) ∉ Q.1.asIdeal ^ 2 :=
    (GlobalTheory.ColPeriod.levelPrimes X Pr sel S mu hX hPr hsel ⟨Q.1, by classical exact Finset.mem_union_right _ Q.2⟩).1.2
  exact level_congruence_eq_twisted_k1 Q.1 hu _ (N_m_succ R) R.r (R.m * R.t) (4 * R.m) (rank_X'_eq R)

end Top
end GlobalTheory.TopLevQ
