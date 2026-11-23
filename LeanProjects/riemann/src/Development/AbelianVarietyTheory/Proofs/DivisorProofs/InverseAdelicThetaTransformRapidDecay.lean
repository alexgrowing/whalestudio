import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoMulInvOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrandPeriodic

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical

noncomputable section
namespace GlobalTheory.InvDecay

variable {F : Type} [Field F] [NumberField F]

abbrev eM (F : Type) [Field F] [NumberField F] := InfiniteAdeleRing.ringEquiv_mixedSpace F

theorem ext_symm (y : mixedEmbedding.mixedSpace F) (w : InfinitePlace F) :
    InfinitePlace.Completion.extensionEmbedding w ((eM F).symm y w) =
      if h : w.IsReal then (y.1 ⟨w, h⟩ : ℂ) else y.2 ⟨w, InfinitePlace.not_isReal_iff_isComplex.1 h⟩ := by
  split_ifs with h
  · rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply h]
    exact congrArg _ (congrFun (congrArg Prod.fst ((eM F).apply_symm_apply y)) ⟨w, h⟩)
  · have := congrFun (congrArg Prod.snd ((eM F).apply_symm_apply y)) ⟨w, InfinitePlace.not_isReal_iff_isComplex.1 h⟩
    rw [← this]
    rfl

theorem re_eq (a : Ainf F) (w : InfinitePlace F) (h : w.IsReal) : re a w = (eM F a).1 ⟨w, h⟩ := by
  rw [re, ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply h, Complex.ofReal_re]
  rfl

theorem continuous_eMsymm : Continuous (eM F).symm := by
  refine continuous_pi fun v => ?_
  rcases v.isReal_or_isComplex with hv | hv
  · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]
    refine ((continuous_apply (⟨v, hv⟩ : {w : InfinitePlace F // w.IsReal})).comp continuous_fst).congr fun y => ?_
    exact (congrFun (congrArg Prod.fst ((eM F).apply_symm_apply y)) ⟨v, hv⟩).symm
  · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]
    refine ((continuous_apply (⟨v, hv⟩ : {w : InfinitePlace F // w.IsComplex})).comp continuous_snd).congr fun y => ?_
    exact (congrFun (congrArg Prod.snd ((eM F).apply_symm_apply y)) ⟨v, hv⟩).symm

theorem embR_add' {N : ℕ} (a b : Fin N → mixedEmbedding.mixedSpace F) : embR (a + b) = embR a + embR b := by
  funext i
  simp only [embR, Pi.add_apply, map_add, pairA]
  exact Prod.ext rfl (add_zero 0).symm

theorem fstA_add_embR {N : ℕ} (x : Fin N → AF F) (t : Fin N → mixedEmbedding.mixedSpace F) (l : Fin N) :
    fstA F ((x + embR t) l) = fstA F (x l) + (eM F).symm (t l) := by
  rw [Pi.add_apply, map_add]; rfl

theorem dot_embR_single {N : ℕ} (z : Fin N → AF F) (l : Fin N) (y : mixedEmbedding.mixedSpace F) :
    z ⬝ᵥ embR (Pi.single l y) = pairA F (fstA F (z l) * (eM F).symm y) 0 := by
  have : embR (Pi.single l y) = Pi.single l (pairA F ((eM F).symm y) 0) := by
    funext i
    by_cases h : i = l
    · subst h; simp [embR]
    · rw [Pi.single_eq_of_ne h]
      show pairA F ((eM F).symm ((Pi.single l y : Fin N → mixedEmbedding.mixedSpace F) i)) 0 = 0
      rw [Pi.single_eq_of_ne h, map_zero]; rfl
  rw [this, dotProduct_single]
  exact Prod.ext rfl (mul_zero _)

theorem mul_apply' (a b : Ainf F) (w : InfinitePlace F) : (a * b) w = a w * b w := rfl

def yv (w₀ : {w : InfinitePlace F // w.IsReal}) (s : ℝ) : mixedEmbedding.mixedSpace F := (Pi.single w₀ s, 0)

def rc (w₀ : {w : InfinitePlace F // w.IsReal}) (a : Ainf F) : ℝ := (eM F a).1 w₀

theorem phase {ψ : AddChar (AF F) ℂ} {lam : InfinitePlace F → ℝ} (hL : IsLam ψ lam) {N : ℕ}
    (z : Fin N → AF F) (l : Fin N) (w₀ : {w : InfinitePlace F // w.IsReal}) (s : ℝ) :
    ψ (z ⬝ᵥ embR (Pi.single l (yv w₀ s))) =
      Complex.exp ((((2 * Real.pi * (lam w₀.1 * rc w₀ (fstA F (z l)))) : ℝ) * Complex.I) * (s : ℂ)) := by
  rw [dot_embR_single]
  show psiInf F ψ _ = _
  rw [hL.2]
  congr 1
  have hs : (∑ w, lam w * re (fstA F (z l) * (eM F).symm (yv w₀ s)) w) =
      lam w₀.1 * (rc w₀ (fstA F (z l)) * s) := by
    rw [Finset.sum_eq_single w₀.1]
    · congr 1
      rw [re, mul_apply', map_mul, ext_symm, dif_pos w₀.2, Complex.re_mul_ofReal, rc]
      have := re_eq (fstA F (z l)) w₀.1 w₀.2
      rw [re] at this
      rw [this]
      simp [yv]
    · intro w _ hw
      rw [re, mul_apply', map_mul, ext_symm]
      split_ifs with h
      · have : (⟨w, h⟩ : {w : InfinitePlace F // w.IsReal}) ≠ w₀ := fun e => hw (congrArg Subtype.val e)
        simp [yv, Pi.single_eq_of_ne this]
      · simp [yv]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hs]
  push_cast
  ring

end GlobalTheory.InvDecay

namespace GlobalTheory.InvDecay
variable {F : Type} [Field F] [NumberField F]

theorem yv_add (w₀ : {w : InfinitePlace F // w.IsReal}) (a b : ℝ) : yv w₀ (a + b) = yv w₀ a + yv w₀ b := by
  simp only [yv, Pi.single_add, Prod.mk_add_mk, add_zero]

def lineM {N : ℕ} (l : Fin N) (w₀ : {w : InfinitePlace F // w.IsReal}) : ℝ →+ (Fin N → AF F) × (Fin N → AF F) :=
  AddMonoidHom.mk' (fun s => ((0 : Fin N → AF F), embR (Pi.single l (yv w₀ s)))) (by
    intro a b
    rw [yv_add, Pi.single_add, embR_add']
    exact Prod.ext (add_zero 0).symm rfl)

theorem isRealLine_lineM {N : ℕ} (l : Fin N) (w₀ : {w : InfinitePlace F // w.IsReal}) :
    IsRealLine (lineM (F := F) l w₀) := by
  refine ⟨?_, fun t => ⟨?_, ?_⟩⟩
  · refine continuous_const.prodMk (continuous_pi fun i => ?_)
    show Continuous fun s : ℝ => pairA F ((eM F).symm ((Pi.single l (yv w₀ s) : Fin N → mixedEmbedding.mixedSpace F) i)) 0
    by_cases h : i = l
    · subst h
      simp only [Pi.single_eq_same]
      have hc : Continuous fun s : ℝ => yv (F := F) w₀ s := by
        refine Continuous.prodMk (continuous_pi fun j => ?_) continuous_const
        by_cases hj : j = w₀
        · subst hj; simp only [Pi.single_eq_same]; exact continuous_id'
        · simpa [Pi.single_eq_of_ne hj] using continuous_const
      exact (continuous_eMsymm.comp hc).prodMk continuous_const
    · simp only [Pi.single_eq_of_ne h]
      exact continuous_const
  · funext i; show sndA F (0 : AF F) = 0; exact map_zero _
  · funext i; rfl

theorem norm_le_sum (hF : IsTotallyReal F) {N : ℕ} (t : Fin N → mixedEmbedding.mixedSpace F) :
    ‖t‖ ≤ ∑ l, ∑ w : {w : InfinitePlace F // w.IsReal}, |(t l).1 w| := by
  haveI : IsEmpty {w : InfinitePlace F // w.IsComplex} :=
    ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.2 w.2 (hF.isReal w.1)⟩
  refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)).2
    fun l => ?_
  refine le_trans ?_ (Finset.single_le_sum (f := fun l => ∑ w : {w : InfinitePlace F // w.IsReal}, |(t l).1 w|)
    (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ l))
  rw [Prod.norm_def, show (t l).2 = 0 from Subsingleton.elim _ _, norm_zero]
  refine max_le ((pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)).2 fun w => ?_)
    (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (f := fun w => |(t l).1 w|) (fun _ _ => abs_nonneg _) (Finset.mem_univ w)

end GlobalTheory.InvDecay

namespace GlobalTheory.InvDecay
variable {F : Type} [Field F] [NumberField F]

theorem invV_bdd {N : ℕ} [Invertible (2 : AF F)] {ψ : AddChar (AF F) ℂ} (hψ : ∀ x, ‖ψ x‖ = 1) {ν : Measure (AF F)}
    {𝓓 : Set (Fin N → AF F)} (h1 : muV N ν 𝓓 = 1) {f : VA F N → ℂ} {C : ℝ} (hC : ∀ w, ‖f w‖ ≤ C)
    (z : Fin N → AF F) : ‖invV ψ ν 𝓓 f z‖ ≤ C := by
  have := norm_setIntegral_le_of_norm_le_const (μ := muV N ν) (s := 𝓓)
    (f := fun y => f (z, y) * ψ (-(⅟(2 : AF F) * (z ⬝ᵥ y)))) (C := C) (by rw [h1]; exact ENNReal.one_lt_top)
    (fun y _ => by rw [norm_mul, hψ, mul_one]; exact hC _)
  rw [Measure.real, h1, ENNReal.toReal_one, mul_one] at this
  exact this

theorem invV_deriv {N : ℕ} [Invertible (2 : AF F)] {ψ : AddChar (AF F) ℂ} {lam : InfinitePlace F → ℝ}
    {ν : Measure (AF F)} (hL : IsLam ψ lam) (hν : IsCov1 ν) {𝓓 : Set (Fin N → AF F)}
    (hD : IsAddFundamentalDomain (ratSub F N) 𝓓 (muV N ν)) {f f' : VA F N → ℂ} (hf : QuasiV ψ f)
    (l : Fin N) (w₀ : {w : InfinitePlace F // w.IsReal}) (z : Fin N → AF F)
    (hd : HasDerivAt (fun t : ℝ => invV ψ ν 𝓓 (heisV ψ (lineM l w₀ t) f) z) (invV ψ ν 𝓓 f' z) 0) :
    invV ψ ν 𝓓 f' z =
      (((2 * Real.pi * (lam w₀.1 * rc w₀ (fstA F (z l)))) : ℝ) * Complex.I) * invV ψ ν 𝓓 f z := by
  set c : ℂ := (((2 * Real.pi * (lam w₀.1 * rc w₀ (fstA F (z l)))) : ℝ) * Complex.I)
  have he : (fun t : ℝ => invV ψ ν 𝓓 (heisV ψ (lineM l w₀ t) f) z) =
      fun t : ℝ => Complex.exp (c * (t : ℂ)) * invV ψ ν 𝓓 f z := by
    funext t
    show invV ψ ν 𝓓 (heisV ψ (0, embR (Pi.single l (yv w₀ t))) f) z = _
    rw [invV_heisV_snd hν hD hf, phase hL]
  rw [he] at hd
  have h2 : HasDerivAt (fun t : ℝ => Complex.exp (c * (t : ℂ)) * invV ψ ν 𝓓 f z)
      (Complex.exp (c * ((0 : ℝ) : ℂ)) * (c * 1) * invV ψ ν 𝓓 f z) 0 :=
    (((hasDerivAt_id (0 : ℝ)).ofReal_comp.const_mul c).cexp).mul_const _
  rw [hd.unique h2]
  simp

theorem norm_invV_deriv {N : ℕ} [Invertible (2 : AF F)] {ψ : AddChar (AF F) ℂ} {lam : InfinitePlace F → ℝ}
    {ν : Measure (AF F)} {𝓓 : Set (Fin N → AF F)} {f f' : VA F N → ℂ}
    (l : Fin N) (w₀ : {w : InfinitePlace F // w.IsReal}) (z : Fin N → AF F)
    (h : invV ψ ν 𝓓 f' z =
      (((2 * Real.pi * (lam w₀.1 * rc w₀ (fstA F (z l)))) : ℝ) * Complex.I) * invV ψ ν 𝓓 f z) :
    ‖invV ψ ν 𝓓 f' z‖ = 2 * Real.pi * |lam w₀.1| * |rc w₀ (fstA F (z l))| * ‖invV ψ ν 𝓓 f z‖ := by
  rw [h, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < 2), abs_of_pos Real.pi_pos, abs_mul]
  ring

end GlobalTheory.InvDecay

namespace GlobalTheory.InvDecay

theorem invV_decay : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ)
    (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)), Ctx ψ lam ν (half F N) →
    ∀ 𝓓 : Set (Fin N → AF F), IsAddFundamentalDomain (ratSub F N) 𝓓 (muV N ν) → muV N ν 𝓓 = 1 →
    ∀ 𝒱 : Set (VA F N → ℂ), (∀ f ∈ 𝒱, QuasiV ψ f ∧ ∃ C : ℝ, ∀ w, ‖f w‖ ≤ C) →
    (∀ f ∈ 𝒱, ∀ M : ℝ →+ VA F N, IsRealLine M → ∃ f' ∈ 𝒱, ∀ x,
      HasDerivAt (fun t : ℝ => invV ψ ν 𝓓 (heisV ψ (M t) f) x) (invV ψ ν 𝓓 f' x) 0) →
    ∀ f ∈ 𝒱, ∀ (x : Fin N → AF F) (k : ℕ), ∃ C : ℝ,
      ∀ t : Fin N → mixedEmbedding.mixedSpace F, ‖t‖ ^ k * ‖invV ψ ν 𝓓 f (x + embR t)‖ ≤ C := by
  intro F _ _ N _ ψ lam ν hC 𝓓 hD h1 𝒱 hV hder
  obtain ⟨hTR, hchar, hL, hcov, -⟩ := hC
  have key : ∀ f ∈ 𝒱, ∀ (l : Fin N) (w₀ : {w : InfinitePlace F // w.IsReal}), ∃ f' ∈ 𝒱, ∀ z,
      invV ψ ν 𝓓 f' z =
        (((2 * Real.pi * (lam w₀.1 * rc w₀ (fstA F (z l)))) : ℝ) * Complex.I) * invV ψ ν 𝓓 f z := by
    intro f hf l w₀
    obtain ⟨f', hf', hd⟩ := hder f hf (lineM l w₀) (isRealLine_lineM l w₀)
    exact ⟨f', hf', fun z => invV_deriv hL hcov hD (hV f hf).1 l w₀ z (hd z)⟩
  have main : ∀ k : ℕ, ∀ f ∈ 𝒱, ∀ x : Fin N → AF F, ∃ C : ℝ,
      ∀ t : Fin N → mixedEmbedding.mixedSpace F, ‖t‖ ^ k * ‖invV ψ ν 𝓓 f (x + embR t)‖ ≤ C := by
    intro k
    induction k with
    | zero =>
      intro f hf x
      obtain ⟨-, C, hCf⟩ := hV f hf
      exact ⟨C, fun t => by rw [pow_zero, one_mul]; exact invV_bdd hchar.2.1 h1 hCf _⟩
    | succ k ih =>
      intro f hf x
      choose f' hf' hrel using key f hf
      choose C' hC' using fun (p : Fin N × {w : InfinitePlace F // w.IsReal}) => ih (f' p.1 p.2) (hf' p.1 p.2) x
      obtain ⟨C₀, hC₀⟩ := ih f hf x
      refine ⟨∑ l, ∑ w₀ : {w : InfinitePlace F // w.IsReal},
        (C' (l, w₀) / (2 * Real.pi * |lam w₀.1|) + |rc w₀ (fstA F (x l))| * C₀), fun t => ?_⟩
      set g := ‖invV ψ ν 𝓓 f (x + embR t)‖ with hgdef
      have hg : 0 ≤ g := norm_nonneg _
      have term : ∀ l w₀, |(t l).1 w₀| * (‖t‖ ^ k * g) ≤
          C' (l, w₀) / (2 * Real.pi * |lam w₀.1|) + |rc w₀ (fstA F (x l))| * C₀ := by
        intro l w₀
        have hn := norm_invV_deriv l w₀ (x + embR t) (hrel l w₀ (x + embR t))
        have hrc : rc w₀ (fstA F ((x + embR t) l)) = rc w₀ (fstA F (x l)) + (t l).1 w₀ := by
          rw [fstA_add_embR, rc, rc, map_add, RingEquiv.apply_symm_apply]; rfl
        rw [hrc, ← hgdef] at hn
        have ha : 0 < 2 * Real.pi * |lam w₀.1| := by
          have := hL.1 w₀.1
          positivity
        have hb := hC' (l, w₀) t
        simp only at hb
        rw [hn] at hb
        have htri : |(t l).1 w₀| ≤ |rc w₀ (fstA F (x l)) + (t l).1 w₀| + |rc w₀ (fstA F (x l))| := by
          have := abs_sub (rc w₀ (fstA F (x l)) + (t l).1 w₀) (rc w₀ (fstA F (x l)))
          simpa using this
        have hP : 0 ≤ ‖t‖ ^ k * g := by positivity
        calc |(t l).1 w₀| * (‖t‖ ^ k * g)
            ≤ (|rc w₀ (fstA F (x l)) + (t l).1 w₀| + |rc w₀ (fstA F (x l))|) * (‖t‖ ^ k * g) :=
              mul_le_mul_of_nonneg_right htri hP
          _ = |rc w₀ (fstA F (x l)) + (t l).1 w₀| * (‖t‖ ^ k * g) +
                |rc w₀ (fstA F (x l))| * (‖t‖ ^ k * g) := by ring
          _ ≤ _ := by
            refine add_le_add ((le_div_iff₀ ha).2 ?_) (mul_le_mul_of_nonneg_left (hC₀ t) (abs_nonneg _))
            calc |rc w₀ (fstA F (x l)) + (t l).1 w₀| * (‖t‖ ^ k * g) * (2 * Real.pi * |lam w₀.1|)
                = ‖t‖ ^ k * (2 * Real.pi * |lam w₀.1| * |rc w₀ (fstA F (x l)) + (t l).1 w₀| * g) := by ring
              _ ≤ C' (l, w₀) := hb
      calc ‖t‖ ^ (k + 1) * g = ‖t‖ * (‖t‖ ^ k * g) := by ring
        _ ≤ (∑ l, ∑ w₀ : {w : InfinitePlace F // w.IsReal}, |(t l).1 w₀|) * (‖t‖ ^ k * g) :=
            mul_le_mul_of_nonneg_right (norm_le_sum hTR t) (by positivity)
        _ = ∑ l, ∑ w₀ : {w : InfinitePlace F // w.IsReal}, |(t l).1 w₀| * (‖t‖ ^ k * g) := by
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun l _ => Finset.sum_mul _ _ _
        _ ≤ _ := Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun w₀ _ => term l w₀
  exact fun f hf x k => main k f hf x

end GlobalTheory.InvDecay

end
