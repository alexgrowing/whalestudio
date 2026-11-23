import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBBStmt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
import Formalism.HermitianCurvature.HermitianCurvatureProofs.JointInstanceTheoremA
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PeriodLatticeFactsSplitOfGeneral
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PoissonJointFirstReduction

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.PBB

open Finset Filter Topology NumberField MeasureTheory
open scoped ComplexConjugate

noncomputable section
open Classical

theorem blockPSD_pull {α X : Type} [DecidableEq α] (Y : Finset X) (f : X → α) (a w b : α → α → ℂ)
    (h : KB.BlockPSD (Y.image f) (Y.image f) a w b) :
    KB.BlockPSD Y Y (fun p q => a (f p) (f q)) (fun p q => w (f p) (f q)) (fun p q => b (f p) (f q)) := by
  unfold KB.BlockPSD at h ⊢
  have := Formalism.FourierDecayAlt.P.JCx1.decay.psd_pull _ _ h (Y.disjSum Y) (Sum.map f f) (by
    intro x hx
    rcases x with p | p
    · rw [Finset.inl_mem_disjSum] at hx
      rw [Sum.map_inl, Finset.inl_mem_disjSum]
      exact Finset.mem_image_of_mem f hx
    · rw [Finset.inr_mem_disjSum] at hx
      rw [Sum.map_inr, Finset.inr_mem_disjSum]
      exact Finset.mem_image_of_mem f hx)
  refine (congrArg (TB.PSDOn (Y.disjSum Y)) ?_).mp this
  funext x y
  rcases x with p | p <;> rcases y with q | q <;> rfl

theorem block_schur {X ι : Type} [Fintype ι] (Y : Finset X) (κ : X → X → ℂ) (hκ : TB.PSDOn Y κ)
    (a w b : ι → X → X → ℂ) (hB : ∀ v, KB.BlockPSD Y Y (a v) (w v) (b v)) :
    ‖∑ p ∈ Y, ∑ q ∈ Y, κ p q * ∏ v, w v p q‖ ≤
      ((∑ p ∈ Y, ∑ q ∈ Y, κ p q * ∏ v, a v p q).re + (∑ p ∈ Y, ∑ q ∈ Y, κ p q * ∏ v, b v p q).re) / 2 := by
  let el : X ⊕ X → X := Sum.elim id id
  have hK : TB.PSDOn (Y.disjSum Y) (fun x y => κ (el x) (el y)) :=
    Formalism.FourierDecayAlt.P.JCx1.decay.psd_pull Y κ hκ (Y.disjSum Y) el (by
      intro x hx
      rcases x with p | p
      · rw [Finset.inl_mem_disjSum] at hx; exact hx
      · rw [Finset.inr_mem_disjSum] at hx; exact hx)
  have hB2 : ∀ v, ∃ K : X ⊕ X → X ⊕ X → ℂ, TB.PSDOn (Y.disjSum Y) K ∧
      ∀ p q, K (.inl p) (.inl q) = a v p q ∧ K (.inl p) (.inr q) = w v p q ∧ K (.inr p) (.inr q) = b v p q :=
    fun v => ⟨_, hB v, fun p q => ⟨rfl, rfl, rfl⟩⟩
  choose K hKp hKv using hB2
  let M : Option ι → X ⊕ X → X ⊕ X → ℂ := fun o => match o with
    | none => fun x y => κ (el x) (el y)
    | some v => K v
  have hM : ∀ o, TB.PSDOn (Y.disjSum Y) (M o) := by
    intro o
    rcases o with _ | v
    · exact hK
    · exact hKp v
  have hP := Formalism.FourierDecayAlt.P.schur_product (X ⊕ X) (Option ι) (Y.disjSum Y) M hM
  have h2 := Formalism.FourierDecayAlt.P.JCx1.decay.psd_compress (Y.disjSum Y) (fun x y => ∏ o, M o x y) hP
    (fun _ : Fin 2 => Y) (fun j => if j = 0 then Sum.inl else Sum.inr) (by
      intro j h hh
      fin_cases j
      · simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte]; rw [Finset.inl_mem_disjSum]; exact hh
      · simp only [Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte]; rw [Finset.inr_mem_disjSum]; exact hh)
  obtain ⟨hcs, hA, hB'⟩ := Formalism.FourierDecayAlt.P.JCx1.decay.psd_two_cs _ h2
  simp only [Matrix.of_apply, Fintype.prod_option, Fin.isValue, one_ne_zero, ↓reduceIte, M, el, Sum.elim_inl,
    Sum.elim_inr, id, hKv] at hcs hA hB'
  set W := ∑ p ∈ Y, ∑ q ∈ Y, κ p q * ∏ v, w v p q
  set A := (∑ p ∈ Y, ∑ q ∈ Y, κ p q * ∏ v, a v p q).re
  set B := (∑ p ∈ Y, ∑ q ∈ Y, κ p q * ∏ v, b v p q).re
  have hW : ‖W‖ ^ 2 ≤ A * B := hcs
  have hA0 : 0 ≤ A := hA
  have hB0 : 0 ≤ B := hB'
  have hn := norm_nonneg W
  nlinarith [sq_nonneg (A - B), sq_nonneg (‖W‖ - (A + B) / 2)]

section words

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

theorem len_le_cnt (S : C.HidaSetting E Wp Wq) (w : S.W) (v : Fin S.f) : (w.1 v).length ≤ S.base.cnt w :=
  Finset.le_sup (f := fun u => (w.1 u).length) (Finset.mem_univ v)

theorem admissible_word_mem_bounded_letter_lists (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (a : List C.Letter) (ha : D.AdmAt S v a) :
    a ∈ C.listsUpTo (S.pts v) S.Ntop := by
  obtain ⟨w, rfl⟩ := ha
  have hlen : (w.1 v).length ≤ S.Ntop := le_trans (len_le_cnt S w v) w.2.2
  simp only [C.listsUpTo, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image, Fintype.mem_piFinset]
  refine ⟨(w.1 v).length, by omega, (w.1 v).get, fun j => ?_, List.ofFn_get _⟩
  simp only [Finset.mem_product, Finset.mem_univ, true_and, List.get_eq_getElem]
  have h1 := w.2.1.1 v j j.2
  have hnode : (if ((w.1 v)[j.1]).1 then ((w.1 v)[j.1]).2 else ((w.1 v)[j.1]).2 - 1) ∈ S.nodes v := by
    simp only [C.HidaSetting.nodes, Finset.mem_union, Finset.mem_biUnion, Finset.mem_range] at h1 ⊢
    rcases h1 with h | h
    · exact Or.inl ⟨_, by omega, h⟩
    · exact Or.inr h
  simp only [C.HidaSetting.pts, Finset.mem_union, Finset.mem_image]
  split_ifs at hnode with hb
  · exact Or.inl hnode
  · exact Or.inr ⟨_, hnode, by ring⟩

theorem admissible_length_of_places (S : C.HidaSetting E Wp Wq) (p : C.Word S.f) (hp : ∀ v, D.AdmAt S v (p v)) (n : ℕ)
    (hn : n ≤ S.Ntop) (hl : ∀ v, (p v).length ≤ n) : S.AdmN p := by
  refine ⟨⟨fun v => ?_, fun v => ?_⟩, ?_⟩
  · obtain ⟨u, hu⟩ := hp v
    rw [← hu]
    exact u.2.1.1 v
  · obtain ⟨u, hu⟩ := hp v
    rw [← hu]
    exact u.2.1.2 v
  · exact le_trans (Finset.sup_le fun v _ => hl v) hn

theorem mem_Wb (S : C.HidaSetting E Wp Wq) (n : ℕ) (w' : S.W)
    (hm : ∀ v, D.AdmAt S v (w'.1 v) ∧ (w'.1 v).length ≤ n) : w' ∈ S.base.Wb n := by
  simp only [TB.Data.Wb, Finset.mem_filter]
  refine ⟨?_, ?_⟩
  · show w' ∈ (C.wall S.pts S.Ntop).subtype S.AdmN
    rw [Finset.mem_subtype]
    simp only [C.wall, Fintype.mem_piFinset]
    exact fun v => admissible_word_mem_bounded_letter_lists S v _ (hm v).1
  · show C.Word.cnt w'.1 ≤ n
    exact Finset.sup_le fun v _ => (hm v).2

theorem prod_sum_words (S : C.HidaSetting E Wp Wq) (n : ℕ) (hn : n ≤ S.Ntop)
    (U : Fin S.f → Finset (List C.Letter)) (θ : Fin S.f → List C.Letter → ℝ)
    (hU : ∀ v, KB.LocProb S v n (U v) (θ v)) (G : Fin S.f → List C.Letter → ℂ) :
    ∑ w' ∈ S.base.Wb n, ((∏ v, θ v (w'.1 v) : ℝ) : ℂ) * ∏ v, G v (w'.1 v) =
      ∏ v, ∑ a ∈ U v, (θ v a : ℂ) * G v a := by
  rw [Finset.prod_univ_sum]
  have hsub : Fintype.piFinset U ⊆ (S.base.Wb n).map (Function.Embedding.subtype _) := by
    intro p hp
    rw [Fintype.mem_piFinset] at hp
    have hadm : S.AdmN p :=
      admissible_length_of_places S p (fun v => ((hU v).2 _ (hp v)).1) n hn (fun v => ((hU v).2 _ (hp v)).2)
    refine Finset.mem_map.mpr ⟨⟨p, hadm⟩, mem_Wb S n ⟨p, hadm⟩ fun v => (hU v).2 _ (hp v), rfl⟩
  have hzero : ∀ p ∈ (S.base.Wb n).map (Function.Embedding.subtype _), p ∉ Fintype.piFinset U →
      ∏ v, (θ v (p v) : ℂ) * G v (p v) = 0 := by
    intro p _ hp
    rw [Fintype.mem_piFinset] at hp
    push Not at hp
    obtain ⟨v, hv⟩ := hp
    exact Finset.prod_eq_zero (Finset.mem_univ v) (by rw [(hU v).1.2.1 _ hv]; simp)
  rw [Finset.sum_subset hsub hzero, Finset.sum_map]
  refine Finset.sum_congr rfl fun w' _ => ?_
  simp only [Function.Embedding.coe_subtype]
  push_cast
  rw [Finset.prod_mul_distrib]

theorem isProb_prod (S : C.HidaSetting E Wp Wq) (n : ℕ) (hn : n ≤ S.Ntop)
    (U : Fin S.f → Finset (List C.Letter)) (θ : Fin S.f → List C.Letter → ℝ)
    (hU : ∀ v, KB.LocProb S v n (U v) (θ v)) :
    TB.IsProb (S.base.Wb n) (fun w' : S.W => ∏ v, θ v (w'.1 v)) := by
  refine ⟨fun w' => Finset.prod_nonneg fun v _ => (hU v).1.1 _, fun w' hw' => ?_, ?_⟩
  · by_contra hne
    apply hw'
    refine mem_Wb S n w' fun v => (hU v).2 _ ?_
    by_contra hv
    exact hne (Finset.prod_eq_zero (Finset.mem_univ v) ((hU v).1.2.1 _ hv))
  · have h := prod_sum_words S n hn U θ hU (fun _ _ => 1)
    simp only [Finset.prod_const_one, mul_one] at h
    have h1 : ∀ v, ∑ a ∈ U v, (θ v a : ℂ) = 1 := fun v => by exact_mod_cast (hU v).1.2.2
    simp only [h1, Finset.prod_const_one] at h
    exact_mod_cast h

theorem locProb_single (S : C.HidaSetting E Wp Wq) (w : S.W) (v : Fin S.f) (n : ℕ) (hn : S.base.cnt w ≤ n) :
    KB.LocProb S v n {w.1 v} (fun a => if a = w.1 v then 1 else 0) := by
  refine ⟨⟨fun a => by dsimp only; split_ifs <;> norm_num, fun a ha => ?_, by simp⟩, fun a ha => ?_⟩
  · rw [Finset.mem_singleton] at ha
    simp [ha]
  · rw [Finset.mem_singleton] at ha
    subst ha
    exact ⟨⟨w, rfl⟩, le_trans (len_le_cnt S w v) hn⟩

end words

section wave

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

theorem prod_univ_ite {ι R : Type} [Fintype ι] [CommMonoid R] (A : Finset ι) (g : ι → R) :
    ∏ v, (if v ∈ A then g v else 1) = ∏ v ∈ A, g v := by
  rw [← Finset.prod_filter]
  congr 1
  ext v
  simp

theorem rhs_eval (S : C.HidaSetting E Wp Wq) (ε : ℝ) (i : ℕ) (hi : i - 1 ≤ S.G.r + 1) (Y : Finset (TB.Pt E))
    (κ : TB.Pt E → TB.Pt E → ℂ) (n : ℕ) (hn : n ≤ S.Ntop) (U : Fin S.f → Finset (List C.Letter))
    (θ : Fin S.f → List C.Letter → ℝ) (hU : ∀ v, KB.LocProb S v n (U v) (θ v)) (s : Fin S.f → ℝ) :
    (∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, ((s v : ℂ) * ∑ a ∈ U v, (θ v a : ℂ) *
        KB.gN S v ε (i - 1) a (C.loc (S.σ v) h) (C.loc (S.σ v) h'))).re =
      (∏ v, s v) * ∑ w' ∈ S.base.Wb n, (∏ v, θ v (w'.1 v)) * S.base.N0 ε (i - 1) w' Y κ := by
  have e1 : ∀ h h' : TB.Pt E, ∏ v, ((s v : ℂ) * ∑ a ∈ U v, (θ v a : ℂ) *
        KB.gN S v ε (i - 1) a (C.loc (S.σ v) h) (C.loc (S.σ v) h')) =
      ((∏ v, s v : ℝ) : ℂ) * ∑ w' ∈ S.base.Wb n, ((∏ v, θ v (w'.1 v) : ℝ) : ℂ) *
        (S.gram ε (i - 1) w'.1 h h' / (C.Word.size S.P w'.1 : ℂ)) := by
    intro h h'
    rw [Finset.prod_mul_distrib,
      ← prod_sum_words S n hn U θ hU (fun v a => KB.gN S v ε (i - 1) a (C.loc (S.σ v) h) (C.loc (S.σ v) h'))]
    push_cast
    congr 1
    refine Finset.sum_congr rfl fun w' _ => ?_
    congr 1
    simp only [KB.gN, C.HidaSetting.gram, if_pos hi, Finset.prod_div_distrib]
    congr 1
    simp only [C.Word.size, C.HidaSetting.sizeAt, Complex.ofReal_prod]
  have e2 : ∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, ((s v : ℂ) * ∑ a ∈ U v, (θ v a : ℂ) *
        KB.gN S v ε (i - 1) a (C.loc (S.σ v) h) (C.loc (S.σ v) h')) =
      ((∏ v, s v : ℝ) : ℂ) * ∑ w' ∈ S.base.Wb n, ((∏ v, θ v (w'.1 v) : ℝ) : ℂ) *
        ((∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * S.gram ε (i - 1) w'.1 h h') / (C.Word.size S.P w'.1 : ℂ)) := by
    rw [Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun h' _ => by rw [e1 h h']]
    simp only [Finset.mul_sum, Finset.sum_div]
    rw [Finset.sum_congr rfl (fun h _ => Finset.sum_comm), Finset.sum_comm]
    refine Finset.sum_congr rfl fun w' _ => Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun h' _ => ?_
    ring
  rw [e2, Complex.re_ofReal_mul, Complex.re_sum]
  congr 1
  refine Finset.sum_congr rfl fun w' _ => ?_
  rw [Complex.re_ofReal_mul, Complex.div_ofReal_re]
  rfl

theorem waveV_core (S : C.HidaSetting E Wp Wq) (X : ℕ → Fin S.f → ℝ) (hW : ∀ v, KB.WaveLoc S v fun i => X i v)
    (ε : ℝ) (hε : 0 < ε) (i : ℕ) (hi1 : 1 ≤ i) (hi2 : i ≤ S.G.r + 1) (w : S.W)
    (hcnt : S.base.cnt w + C.Kst ≤ S.Ntop) :
    ∃ θ : Finset (Fin S.f) → S.W → ℝ, (∀ A, TB.IsProb (S.base.Wb (S.base.cnt w + C.Kst)) (θ A)) ∧
      ∀ Y : Finset (TB.Pt E), (∀ h ∈ Y, TB.level h = i - 1) → ∀ κ, TB.PSDOn Y κ →
        ∀ (L : Fin S.f → ℂ) (A : Finset (Fin S.f)),
          (∏ v ∈ A, ‖L v‖ ^ C.Kst) * ‖KB.NhatV S ε i w Y κ L‖ ≤
            (∏ v ∈ A, X i v ^ C.Kst) *
              ∑ w' ∈ S.base.Wb (S.base.cnt w + C.Kst), θ A w' * S.base.N0 ε (i - 1) w' Y κ := by
  have hlen : ∀ v, (w.1 v).length + C.Kst ≤ S.Ntop := fun v => by have := len_le_cnt S w v; omega
  have H := fun v => hW v i hi1 hi2 (w.1 v) ⟨w, rfl⟩ (hlen v)
  choose Up θp Um θm hUp hUm hblk using H
  have hwid : ∀ v, (w.1 v).length + C.Kst ≤ S.base.cnt w + C.Kst := fun v => by
    have := len_le_cnt S w v; omega
  have hUp' : ∀ v, KB.LocProb S v (S.base.cnt w + C.Kst) (Up v) (θp v) := fun v =>
    ⟨(hUp v).1, fun a ha => ⟨((hUp v).2 a ha).1, le_trans ((hUp v).2 a ha).2 (hwid v)⟩⟩
  have hUm' : ∀ v, KB.LocProb S v (S.base.cnt w + C.Kst) (Um v) (θm v) := fun v =>
    ⟨(hUm v).1, fun a ha => ⟨((hUm v).2 a ha).1, le_trans ((hUm v).2 a ha).2 (hwid v)⟩⟩
  let U : Bool → Finset (Fin S.f) → Fin S.f → Finset (List C.Letter) := fun sg A v =>
    if v ∈ A then (if sg then Up v else Um v) else {w.1 v}
  let th : Bool → Finset (Fin S.f) → Fin S.f → List C.Letter → ℝ := fun sg A v =>
    if v ∈ A then (if sg then θp v else θm v) else fun a => if a = w.1 v then 1 else 0
  have hU : ∀ sg A v, KB.LocProb S v (S.base.cnt w + C.Kst) (U sg A v) (th sg A v) := by
    intro sg A v
    by_cases hv : v ∈ A
    · cases sg
      · simp only [U, th, hv, if_true, Bool.false_eq_true, if_false]; exact hUm' v
      · simp only [U, th, hv, if_true]; exact hUp' v
    · simp only [U, th, hv, if_false]; exact locProb_single S w v _ (by omega)
  have hP : ∀ sg A, TB.IsProb (S.base.Wb (S.base.cnt w + C.Kst)) (fun w' : S.W => ∏ v, th sg A v (w'.1 v)) :=
    fun sg A => isProb_prod S _ hcnt (U sg A) (th sg A) (hU sg A)
  refine ⟨fun A w' => ((∏ v, th true A v (w'.1 v)) + ∏ v, th false A v (w'.1 v)) / 2, fun A => ?_, ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hP true A
    obtain ⟨g1, g2, g3⟩ := hP false A
    refine ⟨fun a => by have := h1 a; have := g1 a; dsimp only; positivity, fun a ha => ?_, ?_⟩
    · simp only [h2 a ha, g2 a ha]; norm_num
    · rw [← Finset.sum_div, Finset.sum_add_distrib, h3, g3]; norm_num
  intro Y hY κ hκ L A
  have hYv : ∀ v, ∀ h ∈ Y.image (C.loc (S.σ v)), D.ptSize h = i - 1 := by
    intro v h hh
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hh
    rw [Formalism.FourierDecayAlt.P.JCx1.needs.ptSize_loc]
    exact hY p hp
  let sc : Fin S.f → ℝ := fun v => if v ∈ A then X i v ^ C.Kst else 1
  let aK : Bool → Fin S.f → C.LPt → C.LPt → ℂ := fun sg v p q =>
    (sc v : ℂ) * ∑ a ∈ U sg A v, (th sg A v a : ℂ) * KB.gN S v ε (i - 1) a p q
  have haK : ∀ sg v, (aK sg v) = if v ∈ A then (fun p q => ((X i v ^ C.Kst : ℝ) : ℂ) *
      KB.mix S v ε (i - 1) (if sg then Up v else Um v) (if sg then θp v else θm v) p q)
      else KB.gN S v ε (i - 1) (w.1 v) := by
    intro sg v
    funext p q
    by_cases hv : v ∈ A
    · cases sg <;> simp [aK, sc, U, th, hv, KB.mix]
    · simp [aK, sc, U, th, hv]
  have hc : ∀ v, ∃ c : ℂ, ‖c‖ = (if v ∈ A then ‖L v‖ ^ C.Kst else 1) ∧
      KB.BlockPSD (Y.image (C.loc (S.σ v))) (Y.image (C.loc (S.σ v))) (aK true v)
        (fun p q => c * KB.hatB S v ε i 1 (w.1 v) (L v) p q) (aK false v) := by
    intro v
    by_cases hv : v ∈ A
    · obtain ⟨-, u, hu, hB⟩ := hblk v ε hε (L v) (Y.image (C.loc (S.σ v))) (hYv v)
      refine ⟨u * L v ^ C.Kst, by simp [hv, hu, norm_pow], ?_⟩
      rw [haK true v, haK false v]
      simp only [hv, if_true, Bool.false_eq_true, if_false]
      exact hB
    · obtain ⟨hB0, -⟩ := hblk v ε hε (L v) (Y.image (C.loc (S.σ v))) (hYv v)
      refine ⟨1, by simp [hv], ?_⟩
      rw [haK true v, haK false v]
      simp only [hv, if_false, one_mul]
      exact hB0
  choose c hcn hcB using hc
  have hS := block_schur Y κ hκ (fun v p q => aK true v (C.loc (S.σ v) p) (C.loc (S.σ v) q))
    (fun v p q => c v * KB.hatB S v ε i 1 (w.1 v) (L v) (C.loc (S.σ v) p) (C.loc (S.σ v) q))
    (fun v p q => aK false v (C.loc (S.σ v) p) (C.loc (S.σ v) q))
    (fun v => blockPSD_pull Y (C.loc (S.σ v)) _ _ _ (hcB v))
  have hL : ∑ p ∈ Y, ∑ q ∈ Y, κ p q * ∏ v, (c v * KB.hatB S v ε i 1 (w.1 v) (L v) (C.loc (S.σ v) p)
      (C.loc (S.σ v) q)) = (∏ v, c v) * KB.NhatV S ε i w Y κ L := by
    simp only [KB.NhatV, Finset.prod_mul_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    ring
  have hcp : ‖∏ v, c v‖ = ∏ v ∈ A, ‖L v‖ ^ C.Kst := by
    rw [norm_prod, Finset.prod_congr rfl (fun v _ => hcn v)]
    convert prod_univ_ite (R := ℝ) A (fun v => ‖L v‖ ^ C.Kst) using 3
  have hi : i - 1 ≤ S.G.r + 1 := by omega
  have hR : ∀ sg, (∑ p ∈ Y, ∑ q ∈ Y, κ p q * ∏ v, aK sg v (C.loc (S.σ v) p) (C.loc (S.σ v) q)).re =
      (∏ v ∈ A, X i v ^ C.Kst) * ∑ w' ∈ S.base.Wb (S.base.cnt w + C.Kst),
        (∏ v, th sg A v (w'.1 v)) * S.base.N0 ε (i - 1) w' Y κ := by
    intro sg
    rw [rhs_eval S ε i hi Y κ _ hcnt (U sg A) (th sg A) (hU sg A) sc]
    congr 1
    convert prod_univ_ite (R := ℝ) A (fun v => X i v ^ C.Kst) using 3
  try dsimp only at hS
  rw [hL, norm_mul, hcp, hR true, hR false] at hS
  refine hS.trans (le_of_eq ?_)
  rw [← mul_add, mul_div_assoc, ← Finset.sum_add_distrib, Finset.sum_div]
  congr 1
  refine Finset.sum_congr rfl fun w' _ => ?_
  ring

end wave

section nhat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

theorem norm_psiL (S : C.HidaSetting E Wp Wq) (l c : ℂ) : ‖KB.psiL S l c‖ = 1 := by
  unfold KB.psiL
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (((2 * (l * c).re / (S.g : ℝ) : ℝ)) : ℂ) =
      ((2 * Real.pi * (2 * (l * c).re / (S.g : ℝ)) : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem continuous_psiL (S : C.HidaSetting E Wp Wq) (l : ℂ) : Continuous fun c => KB.psiL S l c := by
  unfold KB.psiL
  fun_prop

theorem psiInf_eq_prod (S : C.HidaSetting E Wp Wq) (l : E) (c : J.CV E) :
    S.psiInf l c = ∏ v, KB.psiL S (S.σ v l) (c (S.pl v)) := by
  unfold C.HidaSetting.psiInf KB.psiL
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.sum_div, Finset.mul_sum]

theorem prod_dlB (S : C.HidaSetting E Wp Wq) (hg : 0 < S.g) (hU : S6.Unram E) (i : ℕ) :
    ∏ _v : Fin S.f, KB.dlB S i 1 = ZLattice.covolume (J.eLat E (S6.perLat E S.g (S6.nuBlock S.G.r i 1) 1) 1) := by
  rw [Formalism.FourierDecayAlt.P.unipotent_dual_lattice_covolume E hU S.g _ 1 hg]
  have hf : S.f = S6.deg E := by
    have h1 := (Formalism.FourierDecayAlt.P.degreeFacts_statement E).2.1
    have h2 : Fintype.card (Fin S.f) = Fintype.card (InfinitePlace E) := Fintype.card_congr S.pl
    rw [Fintype.card_fin] at h2
    omega
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, hf]
  unfold KB.dlB D.deG
  have hrd := Formalism.FourierDecayAlt.P.Jx4.rd_pos E
  have hg' : (0 : ℝ) < (S.g : ℝ) := by exact_mod_cast hg
  have e : S6.rd E ^ (2 * S6.nuBlock (S.G.r : ℤ) (i : ℤ) (1 : ℤ)) / (2 / (S6.rd E * (S.g : ℝ) ^ 3)) =
      S6.rd E ^ (2 * S6.nuBlock (S.G.r : ℤ) (i : ℤ) (1 : ℤ)) * (S6.rd E / 2) * (S.g : ℝ) ^ 3 := by
    field_simp
  rw [Nat.cast_one, e, mul_pow, mul_pow, ← zpow_natCast, ← zpow_mul, ← pow_mul]

theorem nhat_eq_nhatV (S : C.HidaSetting E Wp Wq) (hg : 0 < S.g) (hU : S6.Unram E) (hInt : KB.IntAll S)
    (ε : ℝ) (hε : 0 < ε) (i : ℕ) (hi1 : 1 ≤ i) (hi2 : i ≤ S.G.r + 1) (w : S.W) (Y : Finset (TB.Pt E))
    (hY : ∀ h ∈ Y, TB.level h = i - 1) (κ : TB.Pt E → TB.Pt E → ℂ) (l : E) :
    S.Nhat ε i w.1 Y κ l = KB.NhatV S ε i w Y κ (fun v => S.σ v l) := by
  have H : ∀ (v : Fin S.f) (h h' : Y), ∃ φ : ℂ → ℂ, Continuous φ ∧
      (∀ c : ℂ, c ≠ 0 → φ c = S.gramLoc v ε i (w.1 v) (C.loc (S.σ v) h ++ [(1, c)])
        (C.loc (S.σ v) h' ++ [(1, c)])) ∧
      (∃ Cφ : ℝ, ∀ c : ℂ, ‖φ c‖ ≤ Cφ * ((1 + ‖c‖) ^ 3)⁻¹) ∧
      ∫ c : ℂ, φ c = (KB.dlB S i 1 : ℂ) * S.gramLoc v ε (i - 1) (w.1 v) (C.loc (S.σ v) h)
        (C.loc (S.σ v) h') := by
    intro v h h'
    exact hInt v ε hε i hi1 hi2 w _ _ (by rw [Formalism.FourierDecayAlt.P.JCx1.needs.ptSize_loc]; exact hY h h.2)
      (by rw [Formalism.FourierDecayAlt.P.JCx1.needs.ptSize_loc]; exact hY h' h'.2)
  choose φ hφc hφe hφb hφi using H
  choose Cφ hCφ using hφb
  set ψ : Fin S.f → ℂ → ℂ := fun v c => KB.psiL S (S.σ v l) c with hψ
  set sz : ℂ := (C.Word.size S.P w.1 : ℂ) with hsz
  set Φ : (Fin S.f → ℂ) → ℂ := fun y =>
    (∑ h : Y, ∑ h' : Y, κ h h' * ∏ v, (φ v h h' (y v) * ψ v (y v))) / sz with hΦ
  have hint1 : ∀ v (h h' : Y), Integrable (fun c => φ v h h' c * ψ v c) := fun v h h' =>
    Formalism.FourierDecayAlt.P.JCx1.needs.integrable_of_decay ((hφc v h h').mul (continuous_psiL S _)) (Cφ := Cφ v h h')
      (fun c => by rw [norm_mul, norm_psiL, mul_one]; exact hCφ v h h' c)
  have hΦc : Continuous Φ := by
    apply Continuous.div_const
    exact continuous_finsetSum _ fun h _ => continuous_finsetSum _ fun h' _ =>
      continuous_const.mul (continuous_finsetProd _ fun v _ =>
        ((hφc v h h').mul (continuous_psiL S _)).comp (continuous_apply v))
  have hN1 : ∀ c : J.CV E, (∀ v, c (S.pl v) ≠ 0) →
      S.N1 ε i w.1 Y κ c * S.psiInf l c = Φ (Formalism.FourierDecayAlt.P.JCx1.needs.Qm S c) := by
    intro c hc
    simp only [C.HidaSetting.N1, hΦ, Formalism.FourierDecayAlt.P.JCx1.needs.Qm_apply, psiInf_eq_prod, Finset.prod_mul_distrib]
    rw [div_mul_eq_mul_div, Finset.sum_mul, ← Finset.sum_coe_sort Y]
    congr 1
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Finset.sum_mul, ← Finset.sum_coe_sort Y]
    refine Finset.sum_congr rfl fun h' _ => ?_
    rw [mul_assoc]
    congr 2
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [hφe v h h' _ (hc v)]
  have hae : (fun c => S.N1 ε i w.1 Y κ c * S.psiInf l c) =ᵐ[volume]
      fun c => Φ (Formalism.FourierDecayAlt.P.JCx1.needs.Qm S c) := by
    have hnull : volume (Formalism.FourierDecayAlt.P.JCx1.needs.Qm S ⁻¹' (⋃ v, {y : Fin S.f → ℂ | y v = 0})) = 0 := by
      rw [(Formalism.FourierDecayAlt.P.JCx1.needs.Qm_mp S).measure_preimage (MeasurableSet.iUnion fun v =>
        measurableSet_eq_fun (measurable_pi_apply v) measurable_const).nullMeasurableSet]
      exact measure_iUnion_null fun v => Measure.pi_hyperplane _ v 0
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with c hc
    apply hN1 c
    intro v hv
    exact hc (Set.mem_preimage.mpr (Set.mem_iUnion.mpr ⟨v, by simp [Formalism.FourierDecayAlt.P.JCx1.needs.Qm_apply, hv]⟩))
  have hmap : ∫ c, Φ (Formalism.FourierDecayAlt.P.JCx1.needs.Qm S c) = ∫ y, Φ y := by
    conv_rhs => rw [← (Formalism.FourierDecayAlt.P.JCx1.needs.Qm_mp S).map_eq]
    rw [integral_map (Formalism.FourierDecayAlt.P.JCx1.needs.Qm_mp S).measurable.aemeasurable hΦc.aestronglyMeasurable]
  have hint : ∀ (h h' : Y), Integrable (fun y : Fin S.f → ℂ => ∏ v, (φ v h h' (y v) * ψ v (y v))) :=
    fun h h' => Integrable.fintype_prod (f := fun v c => φ v h h' c * ψ v c) (fun v => hint1 v h h')
  have hΦi : ∫ y, Φ y = (∑ h : Y, ∑ h' : Y, κ h h' * ∏ v, ∫ c, φ v h h' c * ψ v c) / sz := by
    simp only [hΦ]
    rw [integral_div, integral_finsetSum _ fun h _ =>
      integrable_finsetSum _ fun h' _ => (hint h h').const_mul _]
    congr 1
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [integral_finsetSum _ fun h' _ => (hint h h').const_mul _]
    refine Finset.sum_congr rfl fun h' _ => ?_
    rw [integral_const_mul, integral_fintype_prod_volume_eq_prod (f := fun v c => φ v h h' c * ψ v c)]
  have hne : ∀ᵐ c : ℂ, c ∉ ({0} : Set ℂ) := measure_eq_zero_iff_ae_notMem.mp (measure_singleton 0)
  have hB1 : ∀ v (h h' : Y), KB.hatB S v ε i 1 (w.1 v) (S.σ v l) (C.loc (S.σ v) h) (C.loc (S.σ v) h') =
      (KB.dlB S i 1 : ℂ)⁻¹ * ((∫ c, φ v h h' c * ψ v c) / (S.sizeAt v (w.1 v) : ℂ)) := by
    intro v h h'
    unfold KB.hatB KB.gN
    rw [show i + 1 - 1 = i by omega, ← integral_div]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hne] with c hc
    rw [hφe v h h' c (by simpa using hc)]
    simp only [hψ]
    ring
  have hcv := prod_dlB S hg hU i
  have hrd := Formalism.FourierDecayAlt.P.Jx4.rd_pos E
  have hdl0 : KB.dlB S i 1 ≠ 0 := by
    unfold KB.dlB D.deG
    have hg' : (0 : ℝ) < (S.g : ℝ) := by exact_mod_cast hg
    positivity
  have eR : KB.NhatV S ε i w Y κ (fun v => S.σ v l) = ∑ h : Y, ∑ h' : Y, κ h h' *
      ∏ v, ((KB.dlB S i 1 : ℂ)⁻¹ * ((∫ c, φ v h h' c * ψ v c) / (S.sizeAt v (w.1 v) : ℂ))) := by
    unfold KB.NhatV
    rw [← Finset.sum_coe_sort Y]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [← Finset.sum_coe_sort Y]
    refine Finset.sum_congr rfl fun h' _ => ?_
    simp only [hB1]
  unfold C.HidaSetting.Nhat
  rw [eR, integral_congr_ae hae, hmap, hΦi, ← hcv, Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_congr rfl fun h' _ => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_div_distrib, Finset.prod_inv_distrib, Complex.ofReal_prod]
  have hsz' : ∏ v, (S.sizeAt v (w.1 v) : ℂ) = sz := by
    simp only [hsz, C.Word.size, C.HidaSetting.sizeAt, Complex.ofReal_prod]
  rw [hsz']
  ring

end nhat

end

end Formalism.FourierDecayAlt.P.PBB

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt

theorem plane_wave_bound : Formalism.FourierDecayAlt.KB.WaveV :=
  fun _ _ _ _ _ _ _ _ _ _ S X hW ε hε i hi1 hi2 w _ hcnt => PBB.waveV_core S X hW ε hε i hi1 hi2 w hcnt

theorem plane_wave_bound_of_local_bounds : Formalism.FourierDecayAlt.KB.WaveOfLoc := by
  intro E _ _ _ Wp Wq _ _ _ _ S X hg1 hg2 hU _hG hInt _hX hW ε hε i hi1 hi2 w _hw hcnt
  obtain ⟨θ, hθ, hb⟩ := PBB.waveV_core S X hW ε hε i hi1 hi2 w hcnt
  refine ⟨θ, hθ, fun Y hY κ hκ l _ _ A => ?_⟩
  have hg : 0 < S.g := Nat.mul_pos hg1 hg2
  rw [PBB.nhat_eq_nhatV S hg hU hInt ε hε i hi1 hi2 w Y hY κ l]
  have := hb Y hY κ hκ (fun v => S.σ v l) A
  simp only [Formalism.FourierDecayAlt.P.JCx1.norm_σ] at this
  exact this

end Formalism.FourierDecayAlt.P
