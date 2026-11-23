import Mathlib
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NatCastMemOfPrimeDvdAbsNorm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralAwayFromMovedLocalDatumStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnipotentLevelNilpotent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntOfHomAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepDatumBoundedAtTypePrime

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical

namespace GlobalTheory.KerTie

theorem intOff_pow' {S : Finset ℕ} {z : ℂ} (h : IntOff S z) (n : ℕ) : IntOff S (z ^ n) := by
  induction n with
  | zero => simpa using IntOff.one
  | succ n ih => rw [pow_succ]; exact ih.mul h

theorem intOff_prod' {S : Finset ℕ} {κ : Type} (s : Finset κ) (f : κ → ℂ) (h : ∀ k ∈ s, IntOff S (f k)) :
    IntOff S (∏ k ∈ s, f k) :=
  Finset.prod_induction _ (IntOff S) (fun _ _ ha hb => ha.mul hb) IntOff.one h

theorem intAt_chArg_of_omPhi {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
    {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
    {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}
    (hL : L.Ok Ch sel mu cst G m2) {i : ℕ} (hi : i < m2) (al : L.β i) (be : L.β (i + 1)) (P : rowSG Pr sel mu)
    {y : HomE X.E (R.N i + cOf R i) (R.N (i + 1) + cOf R (i + 1))}
    (h0 : omPhi Ch sel mu cst i P (L.h i al P) (L.h (i + 1) be P) y ≠ 0) :
    IntAt P.1 ((qOf P.1 : X.E) ^ cst.D P * -Loc.chArg y) := by
  have hm := hL.hm
  by_cases hP : P.1 ∈ Pr.vGs
  · have h1 := (GlobalTheory.Mem.Col2.BddG.omPhi_bdd_type Ch sel mu cst i P (by omega) hP _ _ (hL.stabG i al P hP)
      (hL.stabG (i + 1) be P hP)).2 y h0
    rw [hL.depthG P hP, pow_one, mul_neg]
    exact GlobalTheory.TopStep.intAt_neg h1
  · have h1 := right_ne_zero_of_mul h0
    rw [PhiAt, if_neg hP] at h1
    have hb := hL.boundQ i al P hP
    have hb' := hL.boundQ (i + 1) be P hP
    have hD := hL.depthQ' P hP
    simp only [lamYat, hP, if_false, GlobalTheory.GO.ChRoot.mem_lamY_zero] at hb hb'
    have hint : IntAt P.1 ((qOf P.1 : X.E) ^ (i + 1) * Loc.chArg y) := by
      refine GlobalTheory.ColPeriod.EntQ.intAt_chArg _ y fun v hv => ?_
      have h2 := (hb' _ (GlobalTheory.ColPeriod.EntQ.int_of_PhiQ (GlobalTheory.ColPeriod.EntQ.k_le_N R _) (GlobalTheory.ColPeriod.EntQ.k_le_N R _) h1 (hb v hv).1)).2
      have h3 : (L.h i al P) ((L.h i al P)⁻¹ v) = v := LinearEquiv.apply_symm_apply _ v
      simpa [h3] using h2
    obtain ⟨d, hd⟩ : ∃ d, cst.D P = d + (i + 1) := ⟨cst.D P - (i + 1), by omega⟩
    rw [hd, pow_add, mul_neg, mul_assoc]
    exact GlobalTheory.TopStep.intAt_neg ((GlobalTheory.TopStep.intAt_pow (GlobalTheory.TopStep.intAt_nat _) _).mul hint)

theorem intOff_xiEntry : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), (∀ j, ∃ e, Formalism.L2.Col.IsMu0 t.Ch t.seam.σ₀ e j (t.glob.mu0 j)) → (∀ (j : Fin D.R.m) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 t.X.E)), (∀ i, ((t.Pr.g i : ℕ) : 𝓞 t.X.E) ∉ v.asIdeal) → t.seam.σ₀ (t.Ch.muVal j v : t.X.K) = (((t.glob.mu0 j).val v : ℂˣ) : ℂ)) → ∀ u μ, (∀ k, D.host.g k ∉ Y.Qp μ) → ∀ (i : ℕ), i < t.m2 → ∀ al be p p' x, IntOff (t.O u μ).S (t.seam.σ₀ (XiEntry (u := t.word u) t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) i al be p p' x)) := by
  intro D L hT Gi Gl K Y cX ex t hmu hval u μ hg i hi al be p p' x
  have hL := t.idx_ok μ
  have hm := hL.hm
  unfold XiEntry
  rw [map_mul, map_prod]
  refine IntOff.mul ?_ (intOff_prod' _ _ fun P _ => ?_)
  · unfold phiT
    split_ifs
    · simpa using IntOff.one
    · simpa using IntOff.zero
  · have hq := GlobalTheory.KerTie.sNum_qOf_rowSG D L hT Gi Gl K Y cX ex t u μ P
    have hst : P.1 ∈ t.Pr.vGs → (t.idx μ).h i al P ∈ stabL t.X.E _ (lamYat (Pr := t.Pr) i P.1) ∧
        (t.idx μ).h (i + 1) be P ∈ stabL t.X.E _ (lamYat (Pr := t.Pr) (i + 1) P.1) :=
      fun hP => ⟨hL.stabG i al P hP, hL.stabG (i + 1) be P hP⟩

    have hom : ∀ y, IntOff (t.O u μ).S (t.seam.σ₀ (omPhi t.Ch t.sel (t.tup μ) (t.cst μ) i P
        ((t.idx μ).h i al P) ((t.idx μ).h (i + 1) be P) y)) := fun y =>
      GlobalTheory.T.integralAwayFrom_moved_localDatum D L hT Gi Gl K Y cX ex t hmu hval u μ hg i (by omega) P _ _ hst y
    unfold XiAt E1at Loc.E1
    rw [map_mul, map_mul, map_sum]
    refine IntOff.mul (GlobalTheory.UnipVol.intOff_volN_Cbe D L hT Gi Gl K Y cX ex t u μ i P _) (IntOff.mul ?_ (IntOff.sum _ _ fun s _ => ?_))
    · rw [map_pow, map_inv₀, map_pow, map_natCast, ← inv_pow]
      exact intOff_pow' (intOff_pow' (IntOff.inv_nat hq) _) _
    · generalize Loc.xx1 _ s = y
      by_cases h0 : omPhi t.Ch t.sel (t.tup μ) (t.cst μ) i P ((t.idx μ).h i al P) ((t.idx μ).h (i + 1) be P) y = 0
      · rw [h0, zero_mul, map_zero]
        exact IntOff.zero
      · rw [map_mul]
        refine (hom _).mul (IntOff.of_pow (n := qOf P.1 ^ (t.cst μ).D P) (pow_pos (GlobalTheory.GO.ChRoot.qOf_pos _) _) ?_)
        rw [← map_pow, GlobalTheory.GO.ChRoot.psi_root hL.cst_ok P _ (intAt_chArg_of_omPhi hL hi al be P h0), map_one]

end GlobalTheory.KerTie
