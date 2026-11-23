import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.IdeleNormEmbeddingNegOneReal

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder
open UpperTheory.ConvolutionTheory.RankTwoDescent

namespace UpperTheory.ConvolutionTheory.RankTwoDescent.Nz

variable {E : Type} [Field E] [NumberField E]

def FinOne (h : GL (Fin 2) (A E)) : Prop := ∀ i j, (h.val i j).2 = ((1 : Matrix (Fin 2) (Fin 2) (A E)) i j).2

def InfOneG (m : GL (Fin 2) (A E)) : Prop := ∀ i j, (m.val i j).1 = ((1 : Matrix (Fin 2) (Fin 2) (A E)) i j).1

theorem comm_of {h m : GL (Fin 2) (A E)} (hf : FinOne h) (hi : InfOneG m) : m * h = h * m := by
  let f1 : A E →+* InfiniteAdeleRing E := RingHom.fst (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E)
  let f2 : A E →+* FiniteAdeleRing (𝓞 E) E := RingHom.snd (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E)
  have hm : f1.mapMatrix m.val = 1 := by
    rw [← map_one f1.mapMatrix]
    exact Matrix.ext fun i j => hi i j
  have hh : f2.mapMatrix h.val = 1 := by
    rw [← map_one f2.mapMatrix]
    exact Matrix.ext fun i j => hf i j
  have e1 : f1.mapMatrix (m * h).val = f1.mapMatrix (h * m).val := by
    rw [Units.val_mul, Units.val_mul, map_mul, map_mul, hm, one_mul, mul_one]
  have e2 : f2.mapMatrix (m * h).val = f2.mapMatrix (h * m).val := by
    rw [Units.val_mul, Units.val_mul, map_mul, map_mul, hh, one_mul, mul_one]
  exact Units.ext (Matrix.ext fun i j => Prod.ext (congrFun (congrFun e1 i) j) (congrFun (congrFun e2 i) j))

theorem hU_fin (D : Dat ℚ E) (u : ℝ) : (D.mkE 0 (bI u)).2 = 0 := by
  change (AdeleBaseChange.adeleMap ℚ E 0).2 + (AdeleBaseChange.adeleMap ℚ E (bI u)).2 * (rt D.θ : A E).2 = 0
  have h : (AdeleBaseChange.adeleMap ℚ E (bI u)).2 = 0 := by
    change AdeleBaseChange.finiteAdeleMap ℚ E (bI u).2 = 0
    rw [bI_snd, map_zero]
  rw [h, map_zero, zero_mul]
  exact add_zero _

theorem finOne_hU (D : Dat ℚ E) (u : ℝ) : FinOne (hU D u) := by
  intro i j
  have h := hU_fin D u
  fin_cases i <;> fin_cases j <;> simp [hU, nE, h]

theorem infOne_em {k : GL (Fin 2) (A ℚ)} (h : ∀ i j, (k.val i j).1 = ((1 : Matrix (Fin 2) (Fin 2) (A ℚ)) i j).1) :
    InfOneG (em E k) := by
  intro i j
  have e : ((em E k).val i j) = AdeleBaseChange.adeleMap ℚ E (k.val i j) := rfl
  have e2 : (AdeleBaseChange.adeleMap ℚ E (k.val i j)).1 = (AdeleBaseChange.adeleMap ℚ E ((1 : Matrix (Fin 2) (Fin 2) (A ℚ)) i j)).1 := by
    rw [AdeleBaseChange.adeleMap_apply, AdeleBaseChange.adeleMap_apply, h]
  rw [e, e2]
  fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply]

variable [IsTotallyComplex E]

theorem exists_X (D : Dat ℚ E) (u : ℝ) : ∃ X, infGL E 2 X = hU D u := by
  set z := D.mkE 0 (bI u) with hz
  have hz2 : z.2 = 0 := hU_fin D u
  have hs : sInf E (GlobalTheory.CuspRep.pInf E z) = z := Prod.ext ((infEq E).apply_symm_apply _) hz2.symm
  refine ⟨⟨!![1, GlobalTheory.CuspRep.pInf E z; 0, 1], !![1, -GlobalTheory.CuspRep.pInf E z; 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩, Units.ext ?_⟩
  ext i j
  change (1 : Matrix (Fin 2) (Fin 2) (A E)) i j - sInf E ((1 : Matrix (Fin 2) (Fin 2) (Cinf E)) i j) + sInf E (!![1, GlobalTheory.CuspRep.pInf E z; 0, 1] i j) = _
  fin_cases i <;> fin_cases j <;> simp [hU, nE, ← hz, hs]

theorem Tr_translate {P : CuspSub E 2} {φ : GL (Fin 2) (A E) → ℂ} (h : φ ∈ Tr P) (x : GL (Fin 2) (A E)) :
    (fun g => φ (g * x)) ∈ Tr P := by
  unfold Tr at h ⊢
  induction h using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨f', hf', y, rfl⟩ := hf
    exact Submodule.subset_span ⟨f', hf', x * y, by funext g; simp [mul_assoc]⟩
  | zero => exact Submodule.zero_mem _
  | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
  | smul c a _ ha => exact Submodule.smul_mem _ c ha

theorem Gd_translate {D : Dat ℚ E} {P : CuspSub E 2} {L N : ℕ} {φ : GL (Fin 2) (A E) → ℂ} (hG : Gd D P L N φ) (u : ℝ) :
    Gd D P L N (fun g => φ (g * hU D u)) := by
  obtain ⟨X, hX⟩ := exists_X D u
  have hc : ∀ k, finGL E 2 k * hU D u = hU D u * finGL E 2 k := by
    intro k
    rw [← hX, infGL_comm]
  refine ⟨hG.pos, hG.dvd, hG.same, Tr_translate hG.mem _, hG.pl, ?_, ?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨h1, B, hB, hE⟩ := hG.fix w hw
    refine ⟨?_, B, hB, ?_⟩
    · intro g k hk
      have e : H.lc w k = finGL E 2 (locGL E 2 w k) := rfl
      change φ (g * H.lc w k * hU D u) = φ (g * hU D u)
      rw [e, mul_assoc, hc, ← mul_assoc, ← e]
      exact h1 _ k hk
    · intro g
      have e : (fun y => φ (g * finGL E 2 (locGL E 2 w y) * hU D u)) = fun y => φ (g * hU D u * finGL E 2 (locGL E 2 w y)) := by
        funext y
        rw [mul_assoc, hc, ← mul_assoc]
      change UpperTheory.V.Af.Smo.Eig w B fun y => φ (g * finGL E 2 (locGL E 2 w y) * hU D u)
      rw [e]
      exact hE (g * hU D u)
  · intro k hk g
    change φ (g * em E k * hU D u) = φ (g * hU D u)
    rw [mul_assoc, comm_of (finOne_hU D u) (infOne_em hk.1), ← mul_assoc]
    exact hG.lev k hk _
  · intro y x hne v hv
    rw [Wo_right, ← hX, mul_assoc, ← map_mul] at hne
    exact hG.supp y _ hne v hv
  · intro t ht hd y x
    rw [Wo_right, Wo_right, ← hX, mul_assoc, mul_assoc, ← map_mul]
    exact hG.tor t ht hd y _

end UpperTheory.ConvolutionTheory.RankTwoDescent.Nz
