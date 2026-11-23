import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BlockSplitAll
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsobaricDiscreteSelfDualStrongMultiplicityOne
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightRegularOfExt
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SSAscent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalInvariantsMatchSemisimpleStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RootsCharpolySmulMatrix
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PowFinrankEqZeroOfIsNilpotent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightRegularDefinite
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolyFactorizationSemisimpleStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.H0WeightPartNoInvariantsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.H0TateDualNoInvariantsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

namespace GlobalTheory.LocalInvEta

open GlobalTheory.LocalInv GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts Matrix

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

def LocalGlobalEta : Prop := ∀ (i : N.Loc) (a : ℕ), 1 ≤ a → ∀ (π : A.CG a) (s : ℝ),
  A.csd (A.tw π A.etaT) → A.ralg (A.tw π A.etaT) → (∃ m : ℤ, s = (m : ℝ) + 1 / 2) →
  ∀ ρ : G H.E N.Om →* GL (Fin a) (N.O i), Cont N i ρ →
    IsSSRep (mapRep (algebraMap (N.O i) (Kf N i)) ρ) → Matches N A i ρ π (s + (1 - (a : ℝ)) / 2) →
    ∀ w, wd N A i ρ w = A.lpTw (A.locG π w) (s + (1 - (a : ℝ)) / 2) ∧
      (w ∈ placesOver H.E (N.l i) → DeRham N A i ρ w)

theorem not_subOrQuot (eig : Eig N A) (hT : GlobalTheory.IndefiniteRowSideFullHecke.TemperedRepresentations.Tempered N A) (hLG : LocalGlobalEta N A)
    (hL : EigLaws N A eig) (hA : EigAway N A eig) (hAb : EigAbove N A eig) (hS : TemperedSizes N A eig)
    (hη : EtaType N A) (hW : WeightRegular N A) (i : N.Loc) (x : N.X i) (π : A.CG R.r)
    (hx : HasParamX N A i x [⟨R.r, π, 1⟩]) (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i))
    (hρ : IsRankPart N i x ρ) (w : PlE H) (j : ℕ) :
    ¬ SubOrQuot N i ρ (N.chi i 1 * eps N i ^ j) w := by
  intro hs
  obtain ⟨P, hP, hB⟩ := hx
  obtain ⟨σ, hσ⟩ : ∃ σ, FrobLift N w σ := exists_isFrob (N.plOm.2 w)
  obtain ⟨r, hr⟩ := r_odd R
  obtain ⟨t, ht⟩ := R.t_odd
  have hrt := r_add_le R
  have a1 := part_alg N A hη hW i P _ hB ⟨R.r, A.tw π A.etaTinv, 1⟩ (by simp [twistIso]) (r_odd R) odd_one
  have a2 := part_alg N A hη hW i P _ hB ⟨1, A.tw (A.muC i) A.etaTinv, R.t⟩ (by simp [twistIso, muPart])
    odd_one R.t_odd
  have x1 : (1 - (R.nV : ℝ)) / 2 = -(R.t : ℝ) / 2 + (1 - (R.r : ℝ)) / 2 := by
    rw [Ranks.nV]; push_cast; ring
  have l1 := hLG i R.r (r_odd R).pos (A.tw π A.etaTinv) (-(R.t : ℝ) / 2) a1.1 a1.2
    ⟨-(t : ℤ) - 1, by rw [ht]; push_cast; ring⟩
    ρ hρ.1 hρ.2.1 (x1 ▸ matches_rho N A i x π P hP hB ρ hρ) w
  have hc : Cont N i (charRep N i (N.chi i 1 * eps N i ^ j)) := by
    refine charRep_cont N i _ ?_
    refine ((N.chi_cont i 1).mul ((eps_cont N i).pow j)).congr fun g => ?_
    simp
  have x2 : ((R.t : ℝ) - 1) / 2 + (1 - (R.nV : ℝ)) / 2 + j =
      (-(R.r : ℝ) / 2 + j) + (1 - ((1 : ℕ) : ℝ)) / 2 := by
    rw [Ranks.nV]; push_cast; ring
  have l2 := hLG i 1 le_rfl (A.tw (A.muC i) A.etaTinv) (-(R.r : ℝ) / 2 + j) a2.1 a2.2
    ⟨(j : ℤ) - r - 1, by rw [hr]; push_cast; ring⟩
    _ hc (charRep_ss N i _) (x2 ▸ matches_chi N A i j) w
  obtain ⟨c1, c2, c3⟩ := hL w σ hσ
  obtain ⟨m, hm⟩ := Multiset.card_eq_one.mp
    ((c1 (A.locG (A.tw (A.muC i) A.etaTinv) w)).trans (A.locG_dim _ w))
  obtain ⟨c, hcc⟩ := Multiset.card_eq_one.mp ((c1 (A.locG A.etaT w)).trans (A.locG_dim _ w))
  have hmem := eig_mem N A eig hA hAb i ρ _ hρ.1 hc w l1.2 l2.2 hs σ hσ _
    (by rw [l2.1, c2, hm, Multiset.map_singleton])
  rw [l1.1, c2] at hmem
  obtain ⟨α, hα, he⟩ := Multiset.mem_map.mp hmem
  have s1 := (hS w σ hσ _ (hT _ (r_odd R).pos _ a1.1 a1.2 w) (α * c) (by
    rw [A.locG_tw, c3 _ _ c (A.locG_dim _ w) hcc]
    exact Multiset.mem_map_of_mem _ hα)).2
  have s2 := (hS w σ hσ _ (hT _ le_rfl _ a2.1 a2.2 w) (m * c) (by
    rw [A.locG_tw, c3 _ _ c (A.locG_dim _ w) hcc, hm]
    simp)).1
  rw [A.locG_dim] at s1 s2
  have hq := one_lt_normV w
  have hq0 : (0 : ℝ) < ((normV w : ℕ) : ℝ) := lt_trans one_pos hq
  have s2' : 1 ≤ ‖m * c‖ := by simpa using s2
  have hn : ‖α * c‖ * ((normV w : ℕ) : ℝ) ^ (-(R.t : ℝ) / 2 + (1 - (R.r : ℝ)) / 2) =
      ‖m * c‖ * ((normV w : ℕ) : ℝ) ^ ((-(R.r : ℝ) / 2 + j) + (1 - ((1 : ℕ) : ℝ)) / 2) := by
    rw [← norm_cpow w, ← norm_cpow w, ← norm_mul, ← norm_mul]
    congr 1
    linear_combination c * he
  have hle : ((normV w : ℕ) : ℝ) ^ ((-(R.r : ℝ) / 2 + j) + (1 - ((1 : ℕ) : ℝ)) / 2) ≤
      ((normV w : ℕ) : ℝ) ^ (((R.r : ℝ) - 1) / 2 + (-(R.t : ℝ) / 2 + (1 - (R.r : ℝ)) / 2)) := by
    rw [Real.rpow_add hq0 (((R.r : ℝ) - 1) / 2)]
    calc _ ≤ ‖m * c‖ * ((normV w : ℕ) : ℝ) ^ ((-(R.r : ℝ) / 2 + j) + (1 - ((1 : ℕ) : ℝ)) / 2) :=
          le_mul_of_one_le_left (Real.rpow_nonneg hq0.le _) s2'
      _ = _ := hn.symm
      _ ≤ _ := mul_le_mul_of_nonneg_right s1 (Real.rpow_nonneg hq0.le _)
  rw [Real.rpow_le_rpow_left_iff hq] at hle
  have h1 : (R.r : ℝ) + 5 ≤ R.t := by exact_mod_cast hrt
  have h2 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  push_cast at hle
  linarith

theorem noLocalInv_cusp (eig : Eig N A) (hT : GlobalTheory.IndefiniteRowSideFullHecke.TemperedRepresentations.Tempered N A) (hLG : LocalGlobalEta N A)
    (hL : EigLaws N A eig) (hA : EigAway N A eig) (hAb : EigAbove N A eig) (hS : TemperedSizes N A eig)
    (hη : EtaType N A) (hW : WeightRegular N A) (i : N.Loc) (x : N.X i) (hx : IsCuspPoint N A i x)
    (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) (hρ : IsRankPart N i x ρ) : NoLocalInv N i ρ := by
  obtain ⟨-, Sig, hx, π, rfl⟩ := hx
  intro w
  have key := not_subOrQuot N A eig hT hLG hL hA hAb hS hη hW i x π hx ρ hρ w
  constructor
  · intro v hv
    by_contra h0
    refine key 0 ⟨v, h0, Or.inl fun g hg => ?_⟩
    rw [matK_eq, Matrix.smul_mulVec, hv g hg]
    simp
  · intro v hv
    by_contra h0
    refine key 1 ⟨v, h0, Or.inr fun g hg => ?_⟩
    have h1 : Matrix.vecMul v (matT N i ρ g)ᵀ = v := by
      rw [Matrix.vecMul_transpose]; exact hv g hg
    have h2 : Matrix.vecMul v (matW N i ρ g) =
        algebraMap (N.O i) (Kf N i) ((eps N i g : (N.O i)ˣ) : N.O i) • v := by
      conv_lhs => rw [← h1]
      rw [Matrix.vecMul_vecMul, matT_transpose_mul_matW, Matrix.vecMul_smul, Matrix.vecMul_one]
    rw [matK_eq, Matrix.vecMul_smul, h2, smul_smul]
    simp

theorem etaType_of_tie (D : D7) (h : Formalism.MainNotions.SumRepresentations.tie0 D) : EtaType D.nd D.naut := by
  obtain ⟨-, ⟨⟨h1, -⟩, h2, -⟩, -⟩ := h
  refine ⟨h1, fun τ z hz => ?_⟩
  rcases (h2 τ).1 with e | e <;> rw [e, Multiset.mem_singleton] at hz <;> subst hz
  · exact ⟨0, by simp⟩
  · exact ⟨-1, by push_cast; ring⟩

end GlobalTheory.LocalInvEta

theorem GlobalTheory.LocalInvEta.noLocalInvariants_everywhere : ∀ (D : D7) (T : WDTie D.nd D.naut), Formalism.MainNotions.SumRepresentations.tie0 D → Formalism.MainNotions.SumRepresentations.adm2 D → Formalism.MainNotions.SumRepresentations.adm5 D → Formalism.MainNotions.SumRepresentations.adm7 D → MuInt D.nd D.naut → GlobalTheory.LocalInv.GoodCuspidal D.nd D.naut → GlobalTheory.LocalInv.EigAway D.nd D.naut T.eig → GlobalTheory.LocalInv.EigAbove D.nd D.naut T.eig → Formalism.MainNotions.SumRepresentations.CuspidalGaloisUnramified D := by
  intro D T htie h2 h5 h7 _ hG hA hAb i r hr x hx ρ hss hchar w
  have hcusp : GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts.IsCuspPoint D.nd D.naut i x := by
    rcases hx with ⟨hz, Sig, h1, h2⟩ | h
    · exact ⟨hz, Sig, h1, hG i x Sig h1 h2⟩
    · exact h
  have hcont := GlobalTheory.T.charpoly_factorization_semisimple D h5 i x (r x) (hr x) ρ hss hchar
  have hrank : GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts.IsRankPart D.nd i x ρ :=
    ⟨hcont, hss, fun w hw B σ hB hσ => by rw [← hchar σ]; exact (hr x).2.2 w hw B σ hB hσ⟩
  have hLG : GlobalTheory.LocalInvEta.LocalGlobalEta D.nd D.naut := GlobalTheory.T.local_invariants_match_semisimple D htie h2 h5
  have hT : GlobalTheory.IndefiniteRowSideFullHecke.TemperedRepresentations.Tempered D.nd D.naut := fun a ha π hc hra => h7 a π ha hc hra
  have hno := GlobalTheory.LocalInvEta.noLocalInv_cusp D.nd D.naut T.eig hT hLG
    (GlobalTheory.RowTie.eigLaws_of_wdTie _ _ _ _ _ T) hA hAb (GlobalTheory.LocalInv.temperedSizes_of_tie _ _ _ _ _ T)
    (GlobalTheory.LocalInvEta.etaType_of_tie D htie) (GlobalTheory.LocalInv.weightRegular_definite D) i x hcusp ρ hrank w
  exact ⟨GlobalTheory.T.H0_weight_part_no_invariants _ _ _ _ i ρ _ hno.1, GlobalTheory.T.H0_coefRep_T2_subtype_eq_bot_of_noInv_matT _ _ _ _ i ρ _ hno.2⟩
