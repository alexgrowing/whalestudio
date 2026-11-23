import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ComplEquivEvW
import Development.AutomorphicArithmetic.DivisorFrames.MemIntAdelesAndIdealIffSplitEmbeddings
import Development.AutomorphicArithmetic.DivisorFrames.UnitCharIdempotentSumEqProdUnitInd
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels ComplexConjugate
open GlobalTheory.FunObj GlobalTheory.StdFrames GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.SplitTie
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open Classical in
private theorem stdB_eq {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ν : kˣ →* ℂˣ) (ϖ : kˣ) (c a a' : ℕ) (Y : Matrix (Fin a') (Fin (a + a')) k) :
    GlobalTheory.StdPairCone.stdB ν ϖ c a a' Y =
      if (∀ i j, Y i (Fin.natAdd a j) ∈ 𝒪[k]) ∧ ∀ i j, Y i (Fin.castAdd a' j) ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c) then
        GlobalTheory.StdPairCone.unitInd ν (GlobalTheory.StdPairCone.blk₂ Y).det else 0 := by
  unfold GlobalTheory.StdPairCone.stdB GlobalTheory.StdPairCone.unitInd
  split_ifs with h1 h2 h3 h4 h5
  · rfl
  · exact absurd ⟨h1.1, h1.2.1.2⟩ h3
  · exact absurd ⟨h1.2.1.1, h1.2.2⟩ h2
  · exact absurd ⟨h5.1, ⟨h4.1, h5.2⟩, h4.2⟩ h1
  · rfl
  · rfl

private theorem cA_invol {D : D7} (z : AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero]
  | tmul a x => exact congrArg (fun y : D.host.E => a ⊗ₜ[D.host.F] y) (star_star x)
  | add a b ha hb => rw [RingHom.map_add, RingHom.map_add, ha, hb]

private theorem half_alg {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (e : R) (x : S) {m n : ℕ}
    (P : Matrix (Fin m) (Fin m) S) (G : Matrix (Fin m) (Fin m) R) (M : Matrix (Fin m) (Fin n) R)
    (H : Matrix (Fin n) (Fin n) R) (Q : Matrix (Fin n) (Fin n) S) (h : e • M = M) (i : Fin m) (j : Fin n) :
    f e * (x • (P * (G * M * H).map f * Q)) i j = (x • (P * (G * M * H).map f * Q)) i j := by
  have h1 : f e • (G * M * H).map f = (G * M * H).map f := by
    conv_rhs => rw [← h, Matrix.mul_smul, Matrix.smul_mul]
    ext i j
    exact (RingHom.map_mul f e _).symm
  have h2 : f e • (x • (P * (G * M * H).map f * Q)) = x • (P * (G * M * H).map f * Q) := by
    rw [smul_comm, ← Matrix.smul_mul (f e), ← Matrix.mul_smul P (f e), h1]
  exact congrFun (congrFun h2 i) j

private theorem dualCoord_half {D : D7} (ε : AE D) (A' WW : HSp D) (βA' : GL (Fin A'.rank) (Lev.EAf D))
    (βW : GL (Fin WW.rank) (Lev.EAf D)) (y : WO A' WW) (hy : IsHalf (cA D ε) y) (i : Fin A'.rank) (j : Fin WW.rank) :
    toEAf D ε * GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord A' WW βA' βW y i j = GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord A' WW βA' βW y i j := by
  refine half_alg (toEAf D) ε _ _ _ _ _ _ ?_ i j
  ext i j
  have := congrArg (cA D) (hy j i)
  rw [RingHom.map_mul, cA_invol] at this
  exact this

private theorem cball_sub {F : Type} [Field F] [NumberField F] (v : Pl F) (c : ℕ) (x : Fv F v)
    (hx : x ∈ GlobalTheory.SplitWeil.cball (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v ^ c)) : x ∈ 𝒪[Fv F v] := by
  have h : valuation (Fv F v) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v : Fv F v) = uniformizer (Fv F v) :=
    (GlobalTheory.SplitFlip.exists_isUnif (k := Fv F v)).choose_spec
  rw [Valuation.mem_integer_iff]
  refine le_trans (show valuation (Fv F v) x ≤ valuation (Fv F v) ((GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v ^ c : (Fv F v)ˣ) : Fv F v)
    from hx) ?_
  rw [Units.val_pow_eq_pow_val, map_pow, h]
  exact pow_le_one₀ zero_le' uniformizer_lt_one.le

open Classical in
private theorem core (D : D7) (ε : AE D) (Pw : Finset (Pl D.host.E)) (hε : IsIdemSum ε Pw) (ι : Type) [Fintype ι]
    (pl : ι → Pl D.host.F) (τ : ∀ i, D.host.E →ₐ[D.host.F] Fv D.host.F (pl i))
    (hP : ∀ w, w ∈ Pw ↔ ∃ i, splitPrime (τ i) = w) (hinj : Function.Injective (fun i => splitPrime (τ i)))
    (c : Pl D.host.E → ℕ) (ν : (AE D)ˣ →* Circle) (a k d : ℕ) (hk : a + k = d)
    (Y : Matrix (Fin k) (Fin d) (Lev.EAf D)) (hY : ∀ i j, toEAf D ε * Y i j = Y i j) :
    (if IsIntM Y ∧ ∀ i j, j.1 < a → GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId (∏ w ∈ Pw, w.asIdeal ^ c w) (Y i j) then
      GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.unitChar ν ε (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.rightBlock a Y) else 0) =
      ∏ i, GlobalTheory.StdPairCone.stdB (chrW ν (τ i)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt (pl i)) (c (splitPrime (τ i))) a k
        ((Y.map (GlobalTheory.BotMatch.evW (τ i))).submatrix id (finCongr hk)) := by
  subst hk
  have hI := fun i j => UpperTheory.mem_intAdeles_and_ideal_iff_splitEmbeddings D ε Pw hε ι pl τ hP hinj c (Y i j) (hY i j)
  have hb : ∀ l, GlobalTheory.StdPairCone.blk₂ ((Y.map (GlobalTheory.BotMatch.evW (τ l))).submatrix id (finCongr rfl)) =
      (GlobalTheory.BotMatch.evW (τ l)).mapMatrix (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.rightBlock a Y) := fun l => by
    funext i j
    have h : a + j.1 < a + k := by omega
    show _ = GlobalTheory.BotMatch.evW (τ l) (if h : a + j.1 < a + k then Y i ⟨a + j.1, h⟩ else 0)
    rw [dif_pos h]
    rfl
  simp only [stdB_eq, hb, ← RingHom.map_det]
  by_cases h : IsIntM Y ∧ ∀ i j, j.1 < a → GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId (∏ w ∈ Pw, w.asIdeal ^ c w) (Y i j)
  · rw [if_pos h, UpperTheory.unitChar_idempotentSum_eq_prod_unitInd D ε Pw hε ι pl τ hP hinj ν k]
    · refine Finset.prod_congr rfl fun l _ => (if_pos ⟨fun i j => ?_, fun i j => ?_⟩).symm
      · exact (hI i _).1.1 (h.1 i _) l
      · exact (hI i _).2.1 (h.2 i (Fin.castAdd k j) j.2) l
    · intro l
      rw [RingHom.map_det, ← hb, Matrix.det_apply']
      refine sum_mem fun σ _ => mul_mem (intCast_mem _ _) (prod_mem fun i _ => ?_)
      exact (hI _ _).1.1 (h.1 _ _) l
  · rw [if_neg h]
    symm
    by_contra hne
    have hall : ∀ l, (∀ i j, GlobalTheory.BotMatch.evW (τ l) (Y i (Fin.natAdd a j)) ∈ 𝒪[Fv D.host.F (pl l)]) ∧
        ∀ i j, GlobalTheory.BotMatch.evW (τ l) (Y i (Fin.castAdd k j)) ∈
          GlobalTheory.SplitWeil.cball (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt (pl l) ^ c (splitPrime (τ l))) := fun l => by
      by_contra hl
      exact hne (Finset.prod_eq_zero (Finset.mem_univ l) (if_neg hl))
    refine h ⟨fun i j => (hI i j).1.2 fun l => ?_, fun i j hj => (hI i j).2.2 fun l => (hall l).2 i ⟨j.1, hj⟩⟩
    induction j using Fin.addCases with
    | left j => exact cball_sub _ _ _ ((hall l).2 i j)
    | right j => exact (hall l).1 i j

theorem UpperTheory.stdSectionSecond_eq_prod_local :
    ∀ (D : D7) (ε : AE D) (Pw : Finset (Pl D.host.E)), IsIdemSum ε Pw → ∀ (ι : Type) [Fintype ι] (pl : ι → Pl D.host.F)
        (τ : ∀ i, D.host.E →ₐ[D.host.F] Fv D.host.F (pl i)), (∀ w, w ∈ Pw ↔ ∃ i, splitPrime (τ i) = w) →
        Function.Injective (fun i => splitPrime (τ i)) → ∀ (c : Pl D.host.E → ℕ) (ν : (AE D)ˣ →* Circle) (a : ℕ) (A' WW : HSp D) (βA' : GL (Fin A'.rank) (Lev.EAf D))
          (βW : GL (Fin WW.rank) (Lev.EAf D)) (hk : a + A'.rank = WW.rank) (y : WO A' WW), IsHalf (cA D ε) y →
          GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd ν ε (∏ w ∈ Pw, w.asIdeal ^ c w) a A' WW βA' βW y =
            ∏ i, GlobalTheory.StdPairCone.stdB (chrW ν (τ i)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt (pl i)) (c (splitPrime (τ i))) a A'.rank
              (((GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord A' WW βA' βW y).map (GlobalTheory.BotMatch.evW (τ i))).submatrix id (finCongr hk)) := by
  intro D ε Pw hε ι _ pl τ hP hinj c ν a A' WW βA' βW hk y hy
  classical
  rw [← core D ε Pw hε ι pl τ hP hinj c ν a A'.rank WW.rank hk _ (dualCoord_half ε A' WW βA' βW y hy)]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd
  simp only [hy, true_and]
