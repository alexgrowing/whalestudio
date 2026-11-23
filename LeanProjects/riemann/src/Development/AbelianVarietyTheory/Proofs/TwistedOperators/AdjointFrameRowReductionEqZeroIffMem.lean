import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LamHomApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ShiftedTensorLatticePartMemLiftGroupPoints
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeStrongApproxOpenCompact
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IsLatticeVacuumIffSignedRationalFixed
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinPartIdemSumMulInvMem
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OffIdempotentFinitePointMemCompletedTensorLatticStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.LiftDat.RowKer

open GlobalTheory.LiftLevel

variable {D : D7}

theorem row_mat {S T : HSp D} (hS : S.gram = 1) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (a e : AE D) (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) :
    adjA S T βS βT a (partAt (cA D e) (finW S T y)) = Matrix.of fun i j => rowAdj T βT a e (y i) 0 j := by
  have hb : βS.val * (βS⁻¹).val = 1 := by
    rw [← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one]
  have hg : (S.gram⁻¹).map (incA D) = 1 := by rw [hS, inv_one, Matrix.map_one _ (map_zero _) (map_one _)]
  unfold adjA frMapAdj rowAdj
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hb, Matrix.one_mul, hg, Matrix.one_mul]
  ext i j
  simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Matrix.of_apply,
    partAt, finW, smul_eq_mul, Fin.sum_univ_one, map_sum]

theorem rowRed_zero (T : HSp D) (βT : GL (Fin T.rank) (EAf D)) (a e : AE D) (PP : Formalism.L2.DIV.Pl D.host.E) :
    rowRed T βT a e PP 0 = 0 := by
  funext j
  have h0 : rowAdj T βT a e 0 = 0 := by
    unfold rowAdj; ext i k; simp [Matrix.mul_apply, Matrix.smul_apply]
  have h1 : ∀ h, Formalism.L2.DIV.resS D.host.F PP (⟨0, h⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = 0 :=
    fun _ => map_zero _
  simp [rowRed, redM, h0, h1]

theorem full_std (n : ℕ) : (stdL D.host.E n).FG ∧
    Submodule.span D.host.E (stdL D.host.E n : Set (Fin n → D.host.E)) = ⊤ := by
  refine ⟨Submodule.fg_span (Set.finite_range _), ?_⟩
  rw [eq_top_iff, ← (Pi.basisFun D.host.E (Fin n)).span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨a, rfl⟩
  exact Submodule.subset_span ⟨a, by simp⟩

theorem full_smul {r : ℕ} (I : Ideal (𝓞 D.host.E)) (hI : I ≠ ⊥) (L : Lt D.host.E r) (hL : L.FG)
    (hLs : Submodule.span D.host.E (L : Set (Fin r → D.host.E)) = ⊤) :
    (I • L).FG ∧ Submodule.span D.host.E ((I • L : Lt D.host.E r) : Set (Fin r → D.host.E)) = ⊤ := by
  refine ⟨hL.smul (IsNoetherian.noetherian I), ?_⟩
  obtain ⟨t, ht, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  have htE : (t : D.host.E) ≠ 0 := fun h => ht0 (RingOfIntegers.ext (h.trans rfl))
  rw [eq_top_iff, ← hLs, Submodule.span_le]
  intro u hu
  have hu' : (t : D.host.E) • u ∈ Submodule.span D.host.E ((I • L : Lt D.host.E r) : Set (Fin r → D.host.E)) :=
    Submodule.subset_span (Submodule.smul_mem_smul ht hu)
  have := Submodule.smul_mem _ ((t : D.host.E)⁻¹) hu'
  rwa [smul_smul, inv_mul_cancel₀ htE, one_smul] at this

end GlobalTheory.LiftDat.RowKer

namespace GlobalTheory.LiftDat.RowKer

open GlobalTheory.LiftLevel

theorem rowRed_eq_zero_iff : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∀ (a : AE D) (k₀ : GA D S), (∃ b : AE D, a * b = e) → GlobalTheory.LiftLevel.IsMover S T βS βT e a k₀ → GlobalTheory.LiftLevel.IsGen C βS βT Pg Q e a → GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊤ → GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊥ → IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (conjI (GlobalTheory.LiftLevel.liftI Pg Q)) → IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (Ideal.span {2}) → ∀ v ∈ C.X.Λ, ((∀ PP ∈ Pg ∪ Q, GlobalTheory.LiftDat.rowRed T βT a e PP v = 0) ↔ v ∈ GlobalTheory.LiftLevel.liftI Pg Q • C.X.Λ) := by
  intro D S T C hn ΛT _ _ βS βT _ _ Pg Q ξ _ _ e he a k₀ _ _ hgen h1 h2 h3 _ v hv
  rcases Nat.eq_zero_or_pos T.rank with h0 | hpos
  · haveI : IsEmpty (Fin T.rank) := by rw [h0]; infer_instance
    have hv0 : v = 0 := funext fun j => isEmptyElim j
    constructor
    · intro _; rw [hv0]; exact zero_mem _
    · intro _ PP _; funext j; exact isEmptyElim j
  let i0 : Fin S.rank := ⟨0, lt_of_lt_of_le hpos hn⟩
  let y : Matrix (Fin S.rank) (Fin T.rank) D.host.E := Matrix.of fun i => if i = i0 then v else 0
  have hyrow : ∀ i, y i = if i = i0 then v else 0 := fun i => rfl
  have hy0 : y i0 = v := by rw [hyrow, if_pos rfl]
  have hy : ∀ L : Lt D.host.E T.rank, v ∈ L → y ∈ tens (stdL D.host.E S.rank) L := fun L hvL =>
    (GlobalTheory.SW.TensLat.mem_tens_stdL L y).2 fun k => by
      rw [hyrow]
      split_ifs
      · exact hvL
      · exact zero_mem _
  have hAo : ∀ L : Lt D.host.E T.rank, ∀ o : 𝓞 D.host.E, ∀ z ∈ tens (stdL D.host.E S.rank) L,
      (o : D.host.E) • z ∈ tens (stdL D.host.E S.rank) L :=
    fun L o z hz => smul_mem_tens o (fun u hu => Submodule.smul_mem _ o hu) hz
  have hee : e * e = e := GlobalTheory.PlaceVec.idemSum_mul_self he
  have hce : finPart D (cA D e) ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by
      rw [← map_mul, ← map_mul, hee])
  have hfinW : ∀ (L : Lt D.host.E T.rank) (z : Matrix (Fin S.rank) (Fin T.rank) D.host.E),
      z ∈ tens (stdL D.host.E S.rank) L → finW S T z ∈ hatA S T (tens (stdL D.host.E S.rank) L) := fun L z hz => by
    rw [GlobalTheory.Ker.SignVac.finW_eq]; exact GlobalTheory.Ker.SignVac.finTens_mem (GlobalTheory.LatVac.one_mem_intAf _) hz
  have hxL : ∀ L : Lt D.host.E T.rank, v ∈ L →
      partAt (cA D e) (finW S T y) ∈ hatA S T (tens (stdL D.host.E S.rank) L) := fun L hvL => by
    have : partAt (cA D e) (finW S T y) = cA D e • finW S T y := by ext i j; rfl
    rw [this]; exact smul_mem_hatA_of_int (hAo L) hce (hfinW L y (hy L hvL))
  have hhalf : IsHalf (cA D e) (partAt (cA D e) (finW S T y)) := fun i j => by
    simp only [partAt, Matrix.map_apply, ← mul_assoc, ← map_mul, hee]
  obtain ⟨hc1, hc2⟩ := hgen _ hhalf
  have hred : ∀ PP, redM PP (adjA S T βS βT a (partAt (cA D e) (finW S T y))) =
      fun i j => rowRed T βT a e PP (y i) j := by
    intro PP; rw [row_mat C.m.gS βS βT a e y]; rfl
  constructor
  · intro hR
    have hint := hc1.2 (hxL _ hv)
    have hall : ∀ PP ∈ Pg ∪ Q, redM PP (adjA S T βS βT a (partAt (cA D e) (finW S T y))) = 0 := by
      intro PP hPP
      rw [hred]
      funext i j
      rw [hyrow]
      split_ifs
      · exact congrFun (hR PP hPP) j
      · exact congrFun (rowRed_zero T βT a e PP) j
    have hxI := hc2.1 ⟨hint, hall⟩

    have hm : liftI Pg Q ⊔ conjI (liftI Pg Q) = ⊤ := Ideal.isCoprime_iff_sup_eq.1 h3
    have h1' : (1 : 𝓞 D.host.E) ∈ liftI Pg Q ⊔ conjI (liftI Pg Q) := by rw [hm]; exact Submodule.mem_top
    obtain ⟨t, ht, c, hc, htc⟩ := Submodule.mem_sup.1 h1'
    have hcP : ∀ PP ∈ Pg ∪ Q, conjI (liftI Pg Q) ≤ PP.asIdeal := by
      intro PP hPP x hx
      have h2' := mem_of_mem_conjI hx
      rw [liftI] at h2'
      have h3' : stO x ∈ conjI PP.asIdeal := Finset.inf_le (f := fun PP : Formalism.L2.DIV.Pl D.host.E => conjI PP.asIdeal)
        hPP (Ideal.prod_le_inf h2')
      have h4' := mem_of_mem_conjI h3'
      have h5' : stO (stO x) = x := RingOfIntegers.ext (star_star _)
      rwa [h5'] at h4'
    have htP : ∀ PP ∈ Pg ∪ Q, t ∉ PP.asIdeal := by
      intro PP hPP htm
      have h6 : (1 : 𝓞 D.host.E) ∈ PP.asIdeal := htc ▸ add_mem htm (hcP PP hPP hc)
      exact PP.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h6)
    have hPQ : (Pg ∪ Q).Nonempty := by
      by_contra hne
      rw [Finset.not_nonempty_iff_eq_empty] at hne
      apply h1
      rw [liftI, hne, Finset.prod_empty, Ideal.one_eq_top]
    have ht0 : (t : D.host.E) ≠ 0 := by
      obtain ⟨PP, hPP⟩ := hPQ
      intro h
      apply htP PP hPP
      have : t = 0 := RingOfIntegers.ext (h.trans rfl)
      rw [this]; exact zero_mem _
    have htL : ∀ u ∈ C.X.Λ, t • u ∈ liftI Pg Q • C.X.Λ := fun u hu => Submodule.smul_mem_smul ht hu
    have hty : (t : D.host.E) • y ∈ tens (stdL D.host.E S.rank) (liftI Pg Q • C.X.Λ) := smul_mem_tens t htL (hy _ hv)
    have hz1 : finPart D (e * incA D ((t : D.host.E))⁻¹) ∈ intAE D :=
      GlobalTheory.IdemSumInt.finPart_idemSum_mul_inv_mem D e (Pg ∪ Q) he t htP
    have e1 : partAt e (finW S T y) = (e * incA D ((t : D.host.E))⁻¹) • finW S T ((t : D.host.E) • y) := by
      have e2 : finW S T ((t : D.host.E) • y) =
          (pairA D.host.F 0 1 ⊗ₜ[D.host.F] (t : D.host.E) : AE D) • finW S T y := by
        rw [GlobalTheory.Ker.SignVac.finW_eq, GlobalTheory.Ker.SignVac.finW_eq, GlobalTheory.LatVac.tmul_smul_finTens, one_mul,
          Matrix.transpose_smul]
      have e3 : finW S T y = (pairA D.host.F 0 1 ⊗ₜ[D.host.F] (1 : D.host.E) : AE D) • finW S T y := by
        rw [GlobalTheory.Ker.SignVac.finW_eq, GlobalTheory.LatVac.tmul_smul_finTens, one_mul, one_smul]
      rw [e2, smul_smul, mul_assoc]
      have e4 : incA D ((t : D.host.E))⁻¹ * (pairA D.host.F 0 1 ⊗ₜ[D.host.F] (t : D.host.E) : AE D) =
          pairA D.host.F 0 1 ⊗ₜ[D.host.F] (1 : D.host.E) := by
        change ((1 : AF D.host.F) ⊗ₜ[D.host.F] ((t : D.host.E))⁻¹) * _ = _
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, inv_mul_cancel₀ ht0]
      rw [e4, mul_smul, ← e3]
      ext i j; rfl
    have hpe : partAt e (finW S T y) ∈ hatA S T (tens (stdL D.host.E S.rank) (liftI Pg Q • C.X.Λ)) := by
      rw [e1]; exact smul_mem_hatA_of_int (hAo _) hz1 (hfinW _ _ hty)

    have hpo := GlobalTheory.T.offIdempotent_finitePoint_mem_completedTensorLattice D S T Pg Q e he C.X.Λ y (hy _ hv)
    have hsum : finW S T y = partAt (cA D e) (finW S T y) + partAt e (finW S T y) +
        partAt (1 - e - cA D e) (finW S T y) := by
      ext i j; simp only [partAt, Matrix.add_apply, Matrix.map_apply]; ring
    have hfI : finW S T y ∈ hatA S T (tens (stdL D.host.E S.rank) (liftI Pg Q • C.X.Λ)) := by
      rw [hsum]; exact add_mem (add_mem hxI hpe) hpo
    have hyI := ((GlobalTheory.Ker.HatLat.hatA_tens D S T C (stdL D.host.E S.rank) (liftI Pg Q • C.X.Λ) (full_std _)
      (full_smul _ h2 C.X.Λ C.X.Λ_fg C.X.Λ_span)).2.1 y).1 hfI
    have := (GlobalTheory.SW.TensLat.mem_tens_stdL _ y).1 hyI i0
    rwa [hy0] at this
  · intro hvI PP hPP
    have h6 := (hc2.2 (hxL _ hvI)).2 PP hPP
    rw [hred] at h6
    funext j
    have h7 := congrFun (congrFun h6 i0) j
    rw [hy0] at h7
    exact h7

end GlobalTheory.LiftDat.RowKer
