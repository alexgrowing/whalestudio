import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
open scoped ContDiff

noncomputable section
namespace GlobalTheory.LineDerWord

noncomputable def nd : (k : ℕ) → ((Fin k → ℝ) → ℂ) → ℂ
  | 0, h => h Fin.elim0
  | k + 1, h => deriv (fun s : ℝ => nd k (fun s' => h (Fin.cons s s'))) 0

theorem two_le : minSmoothness ℝ 2 ≤ (∞ : WithTop ℕ∞) := by
  rw [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 le_top

theorem contDiff_cons (k : ℕ) {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] :
    ContDiff ℝ ∞ (fun p : (Fin k → ℝ) × (ℝ × Y) => (Fin.cons p.2.1 p.1 : Fin (k+1) → ℝ)) := by
  refine contDiff_pi.2 fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cons_zero]; fun_prop
  · simp only [Fin.cons_succ]; exact (contDiff_apply ℝ ℝ j).comp contDiff_fst

theorem hasDerivAt_fst {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] (G : ℝ × Y → ℂ)
    (hG : ContDiff ℝ ∞ G) (s : ℝ) (y : Y) :
    HasDerivAt (fun s' : ℝ => G (s', y)) (fderiv ℝ G (s, y) (1, 0)) s := by
  have h1 : HasDerivAt (fun s' : ℝ => (s', y)) ((1 : ℝ), (0 : Y)) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s y)
  exact ((hG.differentiable (by simp)) (s, y)).hasFDerivAt.comp_hasDerivAt s h1

theorem smooth_nd : ∀ (k : ℕ) {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (H : (Fin k → ℝ) → Y → ℂ), ContDiff ℝ ∞ (fun p : (Fin k → ℝ) × Y => H p.1 p.2) →
    ContDiff ℝ ∞ (fun y => nd k (fun s => H s y))
  | 0, Y, _, _, H, hH => by
      simp only [nd]
      exact hH.comp (contDiff_const.prodMk contDiff_id)
  | k + 1, Y, _, _, H, hH => by
      let G : ℝ × Y → ℂ := fun p => nd k (fun s' => H (Fin.cons p.1 s') p.2)
      have hG : ContDiff ℝ ∞ G := by
        have := smooth_nd k (Y := ℝ × Y) (fun s' p => H (Fin.cons p.1 s') p.2)
          (hH.comp ((contDiff_cons k).prodMk (contDiff_snd.comp contDiff_snd)))
        exact this
      have e : (fun y => nd (k+1) (fun s => H s y)) = fun y => fderiv ℝ G ((0:ℝ), y) (1, 0) := by
        funext y
        exact (hasDerivAt_fst G hG 0 y).deriv
      rw [e]
      have hd : ContDiff ℝ ∞ (fderiv ℝ G) := (contDiff_infty_iff_fderiv.1 hG).2
      exact (hd.comp (contDiff_const.prodMk contDiff_id)).clm_apply contDiff_const

end GlobalTheory.LineDerWord

namespace GlobalTheory.LineDerWord

theorem hasDerivAt_snd (G : ℝ × ℝ → ℂ) (hG : ContDiff ℝ ∞ G) (s t : ℝ) :
    HasDerivAt (fun t' : ℝ => G (s, t')) (fderiv ℝ G (s, t) (0, 1)) t := by
  have h1 : HasDerivAt (fun t' : ℝ => (s, t')) ((0 : ℝ), (1 : ℝ)) t :=
    (hasDerivAt_const t s).prodMk (hasDerivAt_id t)
  exact ((hG.differentiable (by simp)) (s, t)).hasFDerivAt.comp_hasDerivAt t h1

theorem swap (G : ℝ × ℝ → ℂ) (hG : ContDiff ℝ ∞ G) (t₀ : ℝ) :
    HasDerivAt (fun t => deriv (fun s => G (s, t)) 0)
      (deriv (fun s => deriv (fun t' => G (s, t')) t₀) 0) t₀ := by
  have e1 : (fun t => deriv (fun s => G (s, t)) 0) = fun t => fderiv ℝ G (0, t) (1, 0) := by
    funext t; exact (hasDerivAt_fst G hG 0 t).deriv
  have e2 : (fun s => deriv (fun t' => G (s, t')) t₀) = fun s => fderiv ℝ G (s, t₀) (0, 1) := by
    funext s; exact (hasDerivAt_snd G hG s t₀).deriv
  rw [e1, e2]
  have hd : ContDiff ℝ ∞ (fderiv ℝ G) := (contDiff_infty_iff_fderiv.1 hG).2
  have hdd : Differentiable ℝ (fderiv ℝ G) := hd.differentiable (by simp)
  have ha : HasDerivAt (fun t : ℝ => fderiv ℝ G (0, t)) (fderiv ℝ (fderiv ℝ G) (0, t₀) (0, 1)) t₀ :=
    (hdd (0, t₀)).hasFDerivAt.comp_hasDerivAt t₀ ((hasDerivAt_const t₀ (0:ℝ)).prodMk (hasDerivAt_id t₀))
  have hb : HasDerivAt (fun s : ℝ => fderiv ℝ G (s, t₀)) (fderiv ℝ (fderiv ℝ G) (0, t₀) (1, 0)) 0 :=
    (hdd (0, t₀)).hasFDerivAt.comp_hasDerivAt 0 ((hasDerivAt_id (0:ℝ)).prodMk (hasDerivAt_const (0:ℝ) t₀))
  have ha' := (ContinuousLinearMap.apply ℝ ℂ ((1:ℝ), (0:ℝ))).hasFDerivAt.comp_hasDerivAt t₀ ha
  have hb' := (ContinuousLinearMap.apply ℝ ℂ ((0:ℝ), (1:ℝ))).hasFDerivAt.comp_hasDerivAt 0 hb
  have hsym : IsSymmSndFDerivAt ℝ G (0, t₀) := hG.contDiffAt.isSymmSndFDerivAt two_le
  simp only [Function.comp_def, ContinuousLinearMap.apply_apply] at ha' hb'
  rw [hb'.deriv, hsym]
  exact ha'

theorem hasDerivAt_nd : ∀ (k : ℕ) (H : (Fin k → ℝ) → ℝ → ℂ),
    ContDiff ℝ ∞ (fun p : (Fin k → ℝ) × ℝ => H p.1 p.2) → ∀ t₀ : ℝ,
    HasDerivAt (fun t => nd k (fun s => H s t)) (nd k (fun s => deriv (H s) t₀)) t₀
  | 0, H, hH, t₀ => by
      simp only [nd]
      have : ContDiff ℝ ∞ (H Fin.elim0) := hH.comp (contDiff_const.prodMk contDiff_id)
      exact ((this.differentiable (by simp)) t₀).hasDerivAt
  | k + 1, H, hH, t₀ => by
      let G : ℝ × ℝ → ℂ := fun p => nd k (fun s' => H (Fin.cons p.1 s') p.2)
      have hG : ContDiff ℝ ∞ G :=
        smooth_nd k (Y := ℝ × ℝ) (fun s' p => H (Fin.cons p.1 s') p.2)
          (hH.comp ((contDiff_cons k).prodMk (contDiff_snd.comp contDiff_snd)))
      have hs := swap G hG t₀
      have e : ∀ s : ℝ, deriv (fun t' => G (s, t')) t₀ = nd k (fun s' => deriv (H (Fin.cons s s')) t₀) := by
        intro s
        refine (hasDerivAt_nd k (fun s' t => H (Fin.cons s s') t) ?_ t₀).deriv
        have hc : ContDiff ℝ ∞ (fun q : (Fin k → ℝ) × ℝ => ((Fin.cons s q.1 : Fin (k+1) → ℝ), q.2)) := by
          refine ContDiff.prodMk ?_ contDiff_snd
          refine contDiff_pi.2 fun i => ?_
          refine Fin.cases ?_ (fun j => ?_) i
          · simp only [Fin.cons_zero]; exact contDiff_const
          · simp only [Fin.cons_succ]; exact (contDiff_apply ℝ ℝ j).comp contDiff_fst
        exact hH.comp hc
      simp only [e] at hs
      exact hs

end GlobalTheory.LineDerWord

namespace GlobalTheory.LineDerWord

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem foldr_lineDer_eq_nd (φ : GAd σ J → ℂ) : ∀ (l : List (ℝ → GAd σ J)) (g : GAd σ J),
    l.foldr lineDer φ g = nd l.length (fun s => φ (g * (List.ofFn fun i => l.get i (s i)).prod))
  | [], g => by simp [nd]
  | β :: l, g => by
      simp only [List.foldr_cons, lineDer, List.length_cons, nd]
      congr 1
      funext t
      rw [foldr_lineDer_eq_nd φ l (g * β t)]
      congr 1
      funext s'
      simp [List.ofFn_succ, mul_assoc]
      rfl

end GlobalTheory.LineDerWord

namespace GlobalTheory.LineDerWord

theorem contDiff_snoc (k : ℕ) :
    ContDiff ℝ ∞ (fun p : (Fin k → ℝ) × ℝ => (Fin.snoc p.1 p.2 : Fin (k+1) → ℝ)) := by
  refine contDiff_pi.2 fun i => ?_
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last]; exact contDiff_snd
  · simp only [Fin.snoc_castSucc]; exact (contDiff_apply ℝ ℝ j).comp contDiff_fst

theorem hasDerivAt_foldr_lineDer_translate : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (f : GAd σ J → ℂ), IsSm σ J f →
    ∀ l : List (ℝ → GAd σ J), (∀ β ∈ l, IsRealLine σ J β) → ∀ γ : ℝ → GAd σ J, IsRealLine σ J γ → ∀ g,
      HasDerivAt (fun t : ℝ => l.foldr lineDer (fun x => f (x * γ t)) g) (l.foldr lineDer (lineDer γ f) g) 0 := by
  intro F E _ _ _ _ _ σ n J f hf l hl γ hγ g
  have e1 : (fun t : ℝ => l.foldr lineDer (fun x => f (x * γ t)) g) =
      fun t => nd l.length (fun s => f (g * (List.ofFn fun i => l.get i (s i)).prod * γ t)) := by
    funext t; rw [foldr_lineDer_eq_nd]
  have e2 : l.foldr lineDer (lineDer γ f) g =
      nd l.length (fun s => deriv (fun t => f (g * (List.ofFn fun i => l.get i (s i)).prod * γ t)) 0) := by
    rw [foldr_lineDer_eq_nd]; rfl
  rw [e1, e2]
  refine hasDerivAt_nd l.length (fun s t => f (g * (List.ofFn fun i => l.get i (s i)).prod * γ t)) ?_ 0
  let β : Fin (l.length + 1) → ℝ → GAd σ J := Fin.snoc (α := fun _ => ℝ → GAd σ J) (fun i => l.get i) γ
  have hβ : ∀ i, IsRealLine σ J (β i) := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [β, Fin.snoc_last]; exact hγ
    · simp only [β, Fin.snoc_castSucc]; exact hl _ (List.get_mem l j)
  have hs := (hf (l.length + 1) β hβ g).comp (contDiff_snoc l.length)
  convert hs using 2 with p
  simp only [Function.comp_apply]
  rw [List.ofFn_succ']
  simp only [β, Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append, List.prod_append, List.prod_singleton, mul_assoc]

end GlobalTheory.LineDerWord
