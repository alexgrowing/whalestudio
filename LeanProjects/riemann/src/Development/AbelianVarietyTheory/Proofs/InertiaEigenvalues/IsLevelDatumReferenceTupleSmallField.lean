import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRatScalarMulIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsScaleOfChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjFunBaseRoot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGoodCoverGalois
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConjugateFormsThetaLiftEqThetaSeriesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HolomorphicSectionsSpanRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassSumsSpanCuspFormsBaseTupleSecondFieldStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemOfForallRingEquivFixed
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicCuspSectionsLeSpanAlgebraicCuspForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KapTopLastPosRun
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EasyInputs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartConjMem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentSumSelfDualFramesBoundStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjointFrameMatrixIntegralOfConjugateHalfStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ExportSeries Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels GlobalTheory.ConjTwist
open Formalism.L2.Host (embLL0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.RefDatumLev

variable {D : D7}

theorem q_base_empty {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (hL : R.toLevCh.Is A.μ0) :
    R.Q A.μ0 = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun PP hPP => ?_
  have h := (hL.Q_ram A.μ0 PP).2 (Or.inl hPP)
  rw [hL.xi_base] at h
  exact h fun x _ => rfl

open Classical in
theorem isIdemSum_conjPl {e : AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (h : IsIdemSum e P) :
    IsIdemSum (cA D e) (P.image Formalism.L2.DIV.conjPl) := by
  classical
  obtain ⟨⟨es, hes, he⟩, hc⟩ := h
  refine ⟨⟨fun Q => cA D (es (Formalism.L2.DIV.conjPl Q)), ?_, ?_⟩, ?_⟩
  · intro Q hQ
    obtain ⟨PP, hPP, rfl⟩ := Finset.mem_image.1 hQ
    show Formalism.L2.NTheta.IsIdemAt (cA D (es (Formalism.L2.DIV.conjPl (Formalism.L2.DIV.conjPl PP)))) (Formalism.L2.DIV.conjPl PP)
    rw [Formalism.L2.DIV.conjPl_conjPl]
    exact GlobalTheory.MovedIdem.isIdemAt_conj (hes PP hPP) fun x => Iff.rfl
  · rw [Finset.sum_image (fun a _ b _ (hab : Formalism.L2.DIV.conjPl a = Formalism.L2.DIV.conjPl b) => by
      rw [← Formalism.L2.DIV.conjPl_conjPl a, hab, Formalism.L2.DIV.conjPl_conjPl b])]
    simp only [Formalism.L2.DIV.conjPl_conjPl]
    rw [he, map_sum]
  · rw [GlobalTheory.MovedIdem.cA_cA, mul_comm]; exact hc

theorem frMapAdj_add' (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (x y : WO S T) :
    frMapAdj S T βS βT (x + y) = frMapAdj S T βS βT x + frMapAdj S T βS βT y := by
  unfold frMapAdj
  rw [Matrix.map_add (cA D) (fun a b => (cA D).map_add a b), Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul,
    Matrix.map_add (toEAf D) (fun a b => (toEAf D).map_add a b), Matrix.mul_add, Matrix.add_mul]

theorem frMapAdj_nsmul' (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (k : ℕ) (x : WO S T) :
    frMapAdj S T βS βT (k • x) = k • frMapAdj S T βS βT x := by
  induction k with
  | zero =>
    rw [zero_smul, zero_smul]
    unfold frMapAdj
    rw [Matrix.map_zero (cA D) (cA D).map_zero, Matrix.transpose_zero, Matrix.mul_zero, Matrix.zero_mul,
      Matrix.map_zero (toEAf D) (toEAf D).map_zero, Matrix.mul_zero, Matrix.zero_mul]
  | succ n ih => rw [succ_nsmul, succ_nsmul, frMapAdj_add', ih]

theorem natM_mem_Mb (T : CoreJ D) : ((T.Q.l.M : ℕ) : 𝓞 D.host.E) ∈ T.Q.l.Mb := by
  have hle : T.Q.l.Mb * T.Q.l.Mb.map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) ≤ T.Q.l.Mb := Ideal.mul_le_left
  rw [T.Q.l.prod] at hle
  exact hle (Ideal.mem_span_singleton_self _)

theorem isIntM_add_nsmul_iff {b a : ℕ} {N N' : Matrix (Fin b) (Fin a) (EAf D)} (hN' : IsIntM N') (k : ℕ) :
    IsIntM (N + k • N') ↔ IsIntM N := by
  constructor
  · intro h i j
    have := sub_mem (h i j) (nsmul_mem (hN' i j) k)
    rwa [Matrix.add_apply, Matrix.smul_apply, add_sub_cancel_right] at this
  · intro h i j
    rw [Matrix.add_apply, Matrix.smul_apply]
    exact add_mem (h i j) (nsmul_mem (hN' i j) k)

theorem redM_add_nsmul (PP : Formalism.L2.DIV.Pl D.host.E) {b a : ℕ} {N N' : Matrix (Fin b) (Fin a) (EAf D)} (hN : IsIntM N)
    (hN' : IsIntM N') (k : ℕ) (hk : ((k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) : redM PP (N + k • N') = redM PP N := by
  have hk0 : ((k : ℕ) : Formalism.L2.DIV.kP PP) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk PP.asIdeal)]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hk
  ext i j
  have h1 : (N + k • N') i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := (isIntM_add_nsmul_iff hN' _).2 hN i j
  unfold redM
  rw [dif_pos h1, dif_pos (hN i j)]
  have h2 : (⟨(N + k • N') i j, h1⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) =
      ⟨N i j, hN i j⟩ + ((k : ℕ) : Formalism.L2.Herm.intAf D.host.F D.host.E) * ⟨N' i j, hN' i j⟩ := by
    apply Subtype.ext
    simp [Matrix.add_apply, Matrix.smul_apply, nsmul_eq_mul]
  rw [h2, map_add, map_mul, map_natCast, hk0, zero_mul, add_zero]

theorem omegaK_congr {a b : ℕ} (Pg : Finset (Formalism.L2.DIV.Pl D.host.E))
    {y y' : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin b) (Fin a) (Formalism.L2.DIV.kP PP)}
    (h : ∀ PP ∈ Pg, y PP = y' PP) : omegaK Pg y = omegaK Pg y' := by
  unfold omegaK
  have : (∀ PP ∈ Pg, LowZero a (y PP) ∧ topL a (y PP) = 1) ↔ (∀ PP ∈ Pg, LowZero a (y' PP) ∧ topL a (y' PP) = 1) :=
    ⟨fun hy PP hPP => h PP hPP ▸ hy PP hPP, fun hy PP hPP => (h PP hPP).symm ▸ hy PP hPP⟩
  by_cases hc : ∀ PP ∈ Pg, LowZero a (y PP) ∧ topL a (y PP) = 1
  · rw [if_pos hc, if_pos (this.1 hc)]
  · rw [if_neg hc, if_neg (fun h' => hc (this.2 h'))]

theorem omegaK_mem {a b : ℕ} (Pg : Finset (Formalism.L2.DIV.Pl D.host.E))
    (y : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin b) (Fin a) (Formalism.L2.DIV.kP PP)) (k : Subfield ℂ) :
    omegaK Pg y ∈ k := by
  unfold omegaK
  split_ifs
  exacts [k.one_mem, k.zero_mem]

theorem omegaQ_empty {a b : ℕ} (r : ℕ) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (k : ℤ)
    (y : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin b) (Fin a) (Formalism.L2.DIV.kP PP)) : omegaQ ∅ r ξ k y = 1 := by
  unfold omegaQ
  rw [dif_pos (fun PP h => absurd h (Finset.notMem_empty PP))]
  simp

theorem isLevDatum_ref : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m), GlobalTheory.NT.RayField → ∀ (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T.Q.c.F) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (F : Face D A3.A) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (O : ∀ j, OMDat T.toCore Rl.toRealDat j Unit (fun _ => A3.A.μ0)), LawsJ T → GlobalTheory.Hk3.Core Rl.toRealDat F → Nonempty (FWTie T Rl.toRealDat κ v₀) → TieIn T Rl.toRealDat κ v₀ → IoExt Rl.toRealDat → QGuard Rl.toRealDat → IsGalois ℚ D.LL0 → Formalism.L2.Host.ValLL0 D Rl.C → RayIn D (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') (embLL0 D).fieldRange → (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange) → ∀ (j : Fin D.R.m) (hV : T.V ((j : ℕ) + 1) T.σ₀ = Wc D j), OMPins T Rl.toRealDat κ v₀ O j → GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T Rl.toRealDat j T.σ₀ hV → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.IsLevDatum Rl.toRealDat.ψ (Vc D j) (Wc D j) (Rl.toRealDat.ΛV j) (Rl.toRealDat.ΛW j) T.Q.l.M (embLL0 D).fieldRange (Rl.toRealDat.vacP j) (Rl.toRealDat.vP j A3.A.μ0) := by
  intro D Γ _ _ Pl0 I0 T0 A3 hRF T _ Rl cG S YS F κ v₀ O hT hcore hfw hti hio hQ hgal hval hray hroots j hV hpins hfp
  classical
  have hQ0 : Rl.toRealDat.Q A3.A.μ0 = ∅ := q_base_empty Rl.toRealDat hcore.lev
  obtain ⟨-, e, he, hth⟩ := hcore.thP.vP j A3.A.μ0
  rw [hQ0, Finset.union_empty] at he
  simp only [hQ0, omegaQ_empty, mul_one] at hth
  obtain ⟨cV, hbV⟩ := hcore.lev.βV j
  obtain ⟨cW, hbW⟩ := hcore.lev.βW j
  have hsV := GlobalTheory.Mem.EasyInputs.selfDualOK D _ _ _ _ hbV
  have hsW := GlobalTheory.Mem.EasyInputs.selfDualOK D _ _ _ _ hbW
  have hfV := hbV.1
  have hfW := hbW.1
  have hhalf := (hpins.2.tuple ()).half
  have hP2 : ∀ PP ∈ Rl.toRealDat.Pg,
      ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal :=
    fun PP hPP => hhalf.2.2 PP (Or.inl hPP)
  have hMPg : ∀ PP ∈ Rl.toRealDat.Pg, ((T.Q.l.M : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    intro PP hPP
    have h1 : ((T.Q.l.M : ℕ) : 𝓞 D.host.E) ∈ T.Q.l.Mb := natM_mem_Mb T
    have h2 : T.Q.l.Mb ≤ PP.asIdeal := by
      rw [hhalf.1]
      exact Ideal.prod_le_inf.trans (Finset.inf_le hPP)
    exact h2 h1
  refine ⟨Rl.toRealDat.Pg.image Formalism.L2.DIV.conjPl, cA D e, _, isIdemSum_conjPl he, ?_, ?_, ?_, ?_, hth⟩
  · intro PP hPP
    obtain ⟨P0, hP0, rfl⟩ := Finset.mem_image.1 hPP
    show Formalism.L2.DIV.starOHom ((T.Q.l.M : ℕ) : 𝓞 D.host.E) ∈ P0.asIdeal
    rw [map_natCast]
    exact hMPg P0 hP0
  · intro t ht
    by_cases hc : IsHalf (cA D e) t ∧ IsIntM (frMapAdj (Vc D j) (Wc D j) (Rl.toRealDat.βV j) (Rl.toRealDat.βW j) t)
    · exact ⟨GlobalTheory.T.idempotent_sum_self_dual_frames_bound D _ _ _ _ _ _ hsV hsW hfV hfW _ e he hP2 t hc.1 hc.2, hc.1⟩
    · exact absurd (if_neg hc) ht
  · intro u hu hue t
    have hN' := GlobalTheory.T.adjointFrameMatrix_integral_of_conjugate_half D _ _ _ _ _ _ hsV hsW hfV hfW _ e he hP2 u hu hue
    have hfr : frMapAdj (Vc D j) (Wc D j) (Rl.toRealDat.βV j) (Rl.toRealDat.βW j) (t + T.Q.l.M • u) =
        frMapAdj (Vc D j) (Wc D j) (Rl.toRealDat.βV j) (Rl.toRealDat.βW j) t +
          T.Q.l.M • frMapAdj (Vc D j) (Wc D j) (Rl.toRealDat.βV j) (Rl.toRealDat.βW j) u := by
      rw [frMapAdj_add', frMapAdj_nsmul']
    have hKu : IsHalf (cA D e) (T.Q.l.M • u) := fun a b => by
      rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, hue a b]
    have hhalf' : IsHalf (cA D e) (t + T.Q.l.M • u) ↔ IsHalf (cA D e) t := by
      constructor
      · intro h a b
        have := h a b
        rw [Matrix.add_apply, mul_add, hKu a b] at this
        exact add_right_cancel this
      · intro h a b
        rw [Matrix.add_apply, mul_add, h a b, hKu a b]
    show (if _ then _ else _) = (if _ then _ else _)
    rw [hfr]
    by_cases hc : IsHalf (cA D e) t ∧ IsIntM (frMapAdj (Vc D j) (Wc D j) (Rl.toRealDat.βV j) (Rl.toRealDat.βW j) t)
    · rw [if_pos ⟨hhalf'.2 hc.1, (isIntM_add_nsmul_iff hN' _).2 hc.2⟩, if_pos hc]
      exact omegaK_congr _ fun PP hPP => redM_add_nsmul PP hc.2 hN' _ (hMPg PP hPP)
    · rw [if_neg, if_neg hc]
      intro h'
      exact hc ⟨hhalf'.1 h'.1, (isIntM_add_nsmul_iff hN' _).1 h'.2⟩
  · intro t
    show (if _ then _ else _) ∈ _
    split_ifs
    · exact omegaK_mem _ _ _
    · exact Subfield.zero_mem _

end GlobalTheory.RefDatumLev
