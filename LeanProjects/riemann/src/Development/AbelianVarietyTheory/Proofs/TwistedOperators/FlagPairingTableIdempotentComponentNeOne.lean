import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairTable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

noncomputable section

namespace GlobalTheory.SeeConjRead.RevTab

open Classical Formalism.L2.SG.HidaSetting

theorem pairTable_of {M A : Type} [Ring A] (p : M → M → A) (Z sm : A → Prop) (hZ : ∀ c, Z c → sm c)
    (hadd : ∀ a b, sm a → sm b → sm (a + b)) {ρ k : ℕ} (e f : Fin ρ → M) (b b' : Fin k → M) (z : M) (u : A)
    (hu : sm (u - 1))
    (t1 : ∀ a c, Z (p (f a) (e c) - if a = c then 1 else 0)) (t2 : ∀ a j, Z (p (f a) (b j))) (t3 : ∀ a, Z (p (f a) z))
    (t4 : ∀ a c, Z (p (f a) (f c)))
    (t5 : ∀ i a, Z (p (b' i) (e a))) (t6 : ∀ i j, Z (p (b' i) (b j) - if i = j then u else 0)) (t7 : ∀ i, Z (p (b' i) z))
    (t8 : ∀ i a, Z (p (b' i) (f a)))
    (t9 : ∀ a, Z (p z (e a))) (t10 : ∀ j, Z (p z (b j))) (t11 : Z (p z z + 1)) (t12 : ∀ a, Z (p z (f a)))
    (t13 : ∀ a c, Z (p (e a) (e c))) (t14 : ∀ a j, Z (p (e a) (b j))) (t15 : ∀ a, Z (p (e a) z))
    (t16 : ∀ a c, Z (p (e a) (f c) - if a = c then 1 else 0)) :
    PairTable p sm e f b b' z := by
  refine ⟨fun a c => hZ _ (t1 a c), fun a j => hZ _ (t2 a j), fun a => hZ _ (t3 a), fun a c => hZ _ (t4 a c),
    fun i a => hZ _ (t5 i a), fun i j => ?_, fun i => hZ _ (t7 i), fun i a => hZ _ (t8 i a),
    fun a => hZ _ (t9 a), fun j => hZ _ (t10 j), hZ _ t11, fun a => hZ _ (t12 a),
    fun a c => hZ _ (t13 a c), fun a j => hZ _ (t14 a j), fun a => hZ _ (t15 a), fun a c => hZ _ (t16 a c)⟩
  have h := hZ _ (t6 i j)
  by_cases hij : i = j
  · simp only [hij, if_true] at h ⊢
    have := hadd _ _ h hu
    rwa [show p (b' j) (b j) - u + (u - 1) = p (b' j) (b j) - 1 by abel] at this
  · simpa only [hij, if_false] using h

variable {D : D7}

theorem smallAt_add {PP : Pl D.host.E} {a b : EAf D} (ha : SmallAt PP a) (hb : SmallAt PP b) : SmallAt PP (a + b) := by
  unfold SmallAt at *
  rw [RingHom.map_add]
  exact Valuation.map_add_lt _ ha hb

theorem smallAt_of_mul {PP : Pl D.host.E} {g : ℕ} (hg : (g : 𝓞 D.host.E) ∈ PP.asIdeal) {t : EAf D}
    (ht : t ∈ GlobalTheory.StdFrames.OA D) : SmallAt PP ((g : EAf D) * t) := by
  unfold SmallAt
  have hv : Valued.v (g : PP.adicCompletion D.host.E) < 1 := by
    have := (PP.valuation_lt_one_iff_mem (K := D.host.E) (g : 𝓞 D.host.E)).2 hg
    rw [← Formalism.UG.P.levelaf_valued_algebraMap] at this
    simpa using this
  rw [RingHom.map_mul, map_natCast, Valuation.map_mul]
  have h1 := (GlobalTheory.AdIsom.mem_OA t).1 ht PP
  calc Valued.v (g : PP.adicCompletion D.host.E) * Valued.v (GlobalTheory.StdFrames.cpt PP t)
      ≤ Valued.v (g : PP.adicCompletion D.host.E) * 1 := mul_le_mul_of_nonneg_left h1 zero_le'
    _ = Valued.v (g : PP.adicCompletion D.host.E) := mul_one _
    _ < 1 := hv

end GlobalTheory.SeeConjRead.RevTab

namespace GlobalTheory.SeeConjRead.RevTab

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf
open scoped TensorProduct

section Cong

variable {I : Formalism.MainNotions.S.AutInst} {g : ℕ}

theorem zmod_swap {x y : VA I} {d : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F} (h : ZMod' I g (hA I x y - d)) :
    ZMod' I g (hA I y x - sigA I d) := by
  have := unitaryCongruence.Z_sig I g h
  rwa [map_sub, ← unitaryCongruence.hA_symm] at this

theorem zmod_swap0 {x y : VA I} (h : ZMod' I g (hA I x y)) : ZMod' I g (hA I y x) := by
  have := unitaryCongruence.Z_sig I g h
  rwa [← unitaryCongruence.hA_symm] at this

theorem zmod_swap_delta {ρ : ℕ} {x y : VA I} {a c : Fin ρ} (h : ZMod' I g (hA I x y - if c = a then 1 else 0)) :
    ZMod' I g (hA I y x - if a = c then 1 else 0) := by
  have := zmod_swap h
  by_cases hac : a = c
  · subst hac
    simpa using this
  · simpa [hac, Ne.symm hac] using this

theorem zmod_diag {k : ℕ} {bw bwd : Fin k → VA I} {ew : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F}
    (hD : ∀ i j, ZMod' I g (hA I (bwd i) (bw j) - if i = j then ew else 0)) (i j : Fin k) :
    ZMod' I g (hA I (bw (Fin.rev i)) (bwd (Fin.rev j)) - if i = j then sigA I ew else 0) := by
  have := zmod_swap (hD (Fin.rev j) (Fin.rev i))
  by_cases hij : i = j
  · subst hij
    simpa using this
  · have h2 : ¬ Fin.rev j = Fin.rev i := fun h => hij (Fin.rev_injective h).symm
    simpa [hij, h2] using this

end Cong

variable {D : D7}

theorem smallAt_sg_sub_one {PP : Pl D.host.E} {g : ℕ} (hg : (g : 𝓞 D.host.E) ∈ PP.asIdeal) {ew : EAf D}
    (hc0 : ∃ t ∈ GlobalTheory.StdFrames.OA D, 1 - ew - GlobalTheory.StdFrames.sg D ew = (g : EAf D) * t) (hid : ew * ew = ew)
    (hne : GlobalTheory.StdFrames.cpt PP ew ≠ 1) : SmallAt PP (GlobalTheory.StdFrames.sg D ew - 1) := by
  have h0 : GlobalTheory.StdFrames.cpt PP ew = 0 := by
    have h1 := congrArg (GlobalTheory.StdFrames.cpt PP) hid
    rw [map_mul] at h1
    have h2 : GlobalTheory.StdFrames.cpt PP ew * (GlobalTheory.StdFrames.cpt PP ew - 1) = 0 := by rw [mul_sub, h1, mul_one, sub_self]
    rcases mul_eq_zero.1 h2 with h | h
    · exact h
    · exact absurd (sub_eq_zero.1 h) hne
  obtain ⟨t, ht, hc⟩ := hc0
  have hs := smallAt_of_mul hg ht
  rw [← hc] at hs
  have e1 : GlobalTheory.StdFrames.sg D ew - 1 = -(1 - ew - GlobalTheory.StdFrames.sg D ew) - ew := by ring
  unfold SmallAt at *
  rw [e1, map_sub, map_neg, h0, sub_zero, Valuation.map_neg]
  exact hs

end GlobalTheory.SeeConjRead.RevTab

namespace GlobalTheory.SeeConjRead

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf RevTab

theorem pairTable_rev : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (PP : Pl D.host.E), ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → GlobalTheory.StdFrames.cpt PP (ewT X h) ≠ 1 → PairTable (hY D) (SmallAt PP) (e0T X h) (f0T X h) (fun i => bwdT X h (Fin.rev i)) (fun i => bwT X h (Fin.rev i)) (z0T X h) := by
  intro D X h PP hg hne
  have hc0 : ZMod' X.B.I X.B.g (1 - X.ew - sigA X.B.I X.ew) := by
    have hz := X.vectorsInLattice.2.1
    have h2 : ZMod' X.B.I X.B.g (hA X.B.I X.z0 ((1 - X.ew - sigA X.B.I X.ew) • X.z0)) :=
      unitaryCongruence.mL_Qs X.B.I X.B.g hz (X.ew_full _ hz)
    rw [unitaryCongruence.hA_smul_right] at h2
    have hint : (1 - X.ew - sigA X.B.I X.ew) ∈ Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E :=
      sub_mem (sub_mem (one_mem _) X.ew_int) (unitaryCongruence.sigA_mem _ X.ew_int)
    have h4 := unitaryCongruence.Z_sub X.B.I X.B.g (unitaryCongruence.Z_smul X.B.I X.B.g hint X.formsAtZero.1) h2
    rwa [show (1 - X.ew - sigA X.B.I X.ew) * (hA X.B.I X.z0 X.z0 + 1) -
      (1 - X.ew - sigA X.B.I X.ew) * hA X.B.I X.z0 X.z0 = 1 - X.ew - sigA X.B.I X.ew by ring] at h4
  have hG := X.gramIntegral
  have hZ := X.formsAtZero
  have hW := X.weightVectorsIntegral
  have hD := X.bw_dual
  have hgq := X.g_eq
  have hid := X.ew_idem
  obtain ⟨⟨I⟩⟩ := X
  dsimp only at h hc0 hG hZ hW hD hgq hid hne ⊢
  subst h
  subst hgq
  refine pairTable_of (hY D) (ZMod' (Formalism.L2.SG.InstExistsPf.instOf D) (D.host.g 0 * D.host.g 1)) (SmallAt PP)
    (fun c ⟨t, ht, hc⟩ => hc ▸ smallAt_of_mul hg ht) (fun a b => smallAt_add) _ _ _ _ _ _
    (smallAt_sg_sub_one hg hc0 hid hne)
    (fun a c => zmod_swap_delta (hG c a).2.2) (fun a j => ((hW (Fin.rev j)).2.2 a).2.2.2) (fun a => (hZ.2 a).2)
    (fun a c => (hG a c).2.1)
    (fun i a => zmod_swap0 ((hW (Fin.rev i)).2.2 a).1) (fun i j => zmod_diag hD i j)
    (fun i => zmod_swap0 (hW (Fin.rev i)).1) (fun i a => zmod_swap0 ((hW (Fin.rev i)).2.2 a).2.1)
    (fun a => zmod_swap0 (hZ.2 a).1) (fun j => (hW (Fin.rev j)).2.1) hZ.1 (fun a => zmod_swap0 (hZ.2 a).2)
    (fun a c => (hG a c).1) (fun a j => ((hW (Fin.rev j)).2.2 a).2.2.1) (fun a => (hZ.2 a).1)
    (fun a c => (hG a c).2.2)

end GlobalTheory.SeeConjRead
