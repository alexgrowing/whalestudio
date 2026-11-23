import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdmissibleWordMemBoundedLetterLists

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.PBB

open Finset Filter Topology NumberField MeasureTheory
open scoped ComplexConjugate

noncomputable section
open Classical

theorem psd_congr {α : Type} (F : Finset α) (k1 k2 : α → α → ℂ) (h : ∀ x ∈ F, ∀ y ∈ F, k1 x y = k2 x y)
    (hk : TB.PSDOn F k1) : TB.PSDOn F k2 := by
  unfold TB.PSDOn at hk ⊢
  convert hk using 1
  ext x y
  exact (h x.1 x.2 y.1 y.2).symm

theorem block_schur2 {X ι : Type} [Fintype ι] (Y : Finset X) (κa κw κb : X → X → ℂ)
    (hκ : KB.BlockPSD Y Y κa κw κb) (a w b : ι → X → X → ℂ) (hB : ∀ v, KB.BlockPSD Y Y (a v) (w v) (b v)) :
    ‖∑ p ∈ Y, ∑ q ∈ Y, κw p q * ∏ v, w v p q‖ ≤
      ((∑ p ∈ Y, ∑ q ∈ Y, κa p q * ∏ v, a v p q).re + (∑ p ∈ Y, ∑ q ∈ Y, κb p q * ∏ v, b v p q).re) / 2 := by
  let A' : Option ι → X → X → ℂ := fun o => match o with | none => κa | some v => a v
  let W' : Option ι → X → X → ℂ := fun o => match o with | none => κw | some v => w v
  let B' : Option ι → X → X → ℂ := fun o => match o with | none => κb | some v => b v
  have hB2 : ∀ o : Option ι, ∃ K : X ⊕ X → X ⊕ X → ℂ, TB.PSDOn (Y.disjSum Y) K ∧
      ∀ p q, K (.inl p) (.inl q) = A' o p q ∧ K (.inl p) (.inr q) = W' o p q ∧ K (.inr p) (.inr q) = B' o p q := by
    intro o
    rcases o with _ | v
    · exact ⟨_, hκ, fun p q => ⟨rfl, rfl, rfl⟩⟩
    · exact ⟨_, hB v, fun p q => ⟨rfl, rfl, rfl⟩⟩
  choose K hKp hKv using hB2
  have hP := Formalism.FourierDecayAlt.P.schur_product (X ⊕ X) (Option ι) (Y.disjSum Y) K hKp
  have h2 := Formalism.FourierDecayAlt.P.JCx1.decay.psd_compress (Y.disjSum Y) (fun x y => ∏ o, K o x y) hP
    (fun _ : Fin 2 => Y) (fun j => if j = 0 then Sum.inl else Sum.inr) (by
      intro j h hh
      fin_cases j
      · simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte]; rw [Finset.inl_mem_disjSum]; exact hh
      · simp only [Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte]; rw [Finset.inr_mem_disjSum]; exact hh)
  obtain ⟨hcs, hA, hB'⟩ := Formalism.FourierDecayAlt.P.JCx1.decay.psd_two_cs _ h2
  simp only [Matrix.of_apply, Fintype.prod_option, Fin.isValue, one_ne_zero, ↓reduceIte, hKv, A', W', B']
    at hcs hA hB'
  set Wn := ∑ p ∈ Y, ∑ q ∈ Y, κw p q * ∏ v, w v p q
  set A := (∑ p ∈ Y, ∑ q ∈ Y, κa p q * ∏ v, a v p q).re
  set B := (∑ p ∈ Y, ∑ q ∈ Y, κb p q * ∏ v, b v p q).re
  have hW : ‖Wn‖ ^ 2 ≤ A * B := hcs
  have hA0 : 0 ≤ A := hA
  have hB0 : 0 ≤ B := hB'
  have hn := norm_nonneg Wn
  nlinarith [sq_nonneg (A - B), sq_nonneg (‖Wn‖ - (A + B) / 2)]

section lift

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

theorem sizeAt_nonneg (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (a : List C.Letter) : 0 ≤ S.sizeAt v a := by
  unfold C.HidaSetting.sizeAt
  exact List.prod_nonneg fun x hx => by
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
    exact abs_nonneg _

theorem gN_psd (S : C.HidaSetting E Wp Wq) (hpos : C.ThmPPos S) (v : Fin S.f) (ε : ℝ) (hε : 0 < ε) (j : ℕ)
    (hj : j ≤ S.G.r + 1) (w : S.W) (Z : Finset C.LPt) : TB.PSDOn Z (KB.gN S v ε j (w.1 v)) := by
  have h0 := hpos v ε hε j hj w Z
  have h1 := Formalism.FourierDecayAlt.P.diagonal_scaling C.LPt Z _ (fun _ => (√(S.sizeAt v (w.1 v)))⁻¹) h0
  refine psd_congr Z _ _ (fun x _ y _ => ?_) h1
  unfold KB.gN
  have hs := sizeAt_nonneg S v (w.1 v)
  have e : (((√(S.sizeAt v (w.1 v)))⁻¹ : ℝ) : ℂ) * (((√(S.sizeAt v (w.1 v)))⁻¹ : ℝ) : ℂ) =
      ((S.sizeAt v (w.1 v) : ℝ) : ℂ)⁻¹ := by
    rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt hs, Complex.ofReal_inv]
  rw [e, div_eq_mul_inv, mul_comm]

theorem lift_block0 (S : C.HidaSetting E Wp Wq) (hpos : C.ThmPPos S) (v : Fin S.f) (ε : ℝ) (hε : 0 < ε) (j : ℕ)
    (hj : j ≤ S.G.r + 1) (w : S.W) (Y : Finset (TB.Pt E)) (P P' : TB.Pt E → C.LPt) :
    KB.BlockPSD Y Y (fun p q => KB.gN S v ε j (w.1 v) (P p) (P q))
      (fun p q => KB.gN S v ε j (w.1 v) (P p) (P' q)) (fun p q => KB.gN S v ε j (w.1 v) (P' p) (P' q)) := by
  let G : TB.Pt E ⊕ TB.Pt E → C.LPt := Sum.elim P P'
  have hZ := gN_psd S hpos v ε hε j hj w ((Y.disjSum Y).image G)
  have hpull := Formalism.FourierDecayAlt.P.JCx1.decay.psd_pull _ _ hZ (Y.disjSum Y) G
    (fun x hx => Finset.mem_image_of_mem G hx)
  unfold KB.BlockPSD
  refine psd_congr _ _ _ (fun x hx y hy => ?_) hpull
  rcases x with p | p <;> rcases y with q | q
  · rfl
  · rfl
  · have hp : G (.inr p) ∈ (Y.disjSum Y).image G := Finset.mem_image_of_mem G hx
    have hq : G (.inl q) ∈ (Y.disjSum Y).image G := Finset.mem_image_of_mem G hy
    have := hZ.1.apply (⟨G (.inr p), hp⟩ : (Y.disjSum Y).image G) (⟨G (.inl q), hq⟩ : (Y.disjSum Y).image G)
    simp only [Matrix.of_apply] at this
    exact this.symm
  · rfl

theorem rhs_eval2 (S : C.HidaSetting E Wp Wq) (ε : ℝ) (j : ℕ) (Y : Finset (TB.Pt E))
    (κ : TB.Pt E → TB.Pt E → ℂ) (n : ℕ) (hn : n ≤ S.Ntop) (U : Fin S.f → Finset (List C.Letter))
    (θ : Fin S.f → List C.Letter → ℝ) (hU : ∀ v, KB.LocProb S v n (U v) (θ v)) (s : Fin S.f → ℝ)
    (P P' : Fin S.f → TB.Pt E → C.LPt) :
    (∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, ((s v : ℂ) * ∑ a ∈ U v, (θ v a : ℂ) *
        KB.gN S v ε j a (P v h) (P' v h'))).re =
      (∏ v, s v) * ∑ w' ∈ S.base.Wb n, (∏ v, θ v (w'.1 v)) *
        ((∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, S.gramLoc v ε j (w'.1 v) (P v h) (P' v h')) /
          (C.Word.size S.P w'.1 : ℂ)).re := by
  have e1 : ∀ h h' : TB.Pt E, ∏ v, ((s v : ℂ) * ∑ a ∈ U v, (θ v a : ℂ) * KB.gN S v ε j a (P v h) (P' v h')) =
      ((∏ v, s v : ℝ) : ℂ) * ∑ w' ∈ S.base.Wb n, ((∏ v, θ v (w'.1 v) : ℝ) : ℂ) *
        ((∏ v, S.gramLoc v ε j (w'.1 v) (P v h) (P' v h')) / (C.Word.size S.P w'.1 : ℂ)) := by
    intro h h'
    rw [Finset.prod_mul_distrib,
      ← prod_sum_words S n hn U θ hU (fun v a => KB.gN S v ε j a (P v h) (P' v h'))]
    push_cast
    congr 1
    refine Finset.sum_congr rfl fun w' _ => ?_
    congr 1
    simp only [KB.gN, Finset.prod_div_distrib]
    congr 1
    simp only [C.Word.size, C.HidaSetting.sizeAt, Complex.ofReal_prod]
  have e2 : ∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, ((s v : ℂ) * ∑ a ∈ U v, (θ v a : ℂ) *
        KB.gN S v ε j a (P v h) (P' v h')) =
      ((∏ v, s v : ℝ) : ℂ) * ∑ w' ∈ S.base.Wb n, ((∏ v, θ v (w'.1 v) : ℝ) : ℂ) *
        ((∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, S.gramLoc v ε j (w'.1 v) (P v h) (P' v h')) /
          (C.Word.size S.P w'.1 : ℂ)) := by
    rw [Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun h' _ => by rw [e1 h h']]
    simp only [Finset.mul_sum, Finset.sum_div]
    rw [Finset.sum_congr rfl (fun h _ => Finset.sum_comm), Finset.sum_comm]
    refine Finset.sum_congr rfl fun w' _ => Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun h' _ => ?_
    ring
  rw [e2, Complex.re_ofReal_mul, Complex.re_sum]
  congr 1
  refine Finset.sum_congr rfl fun w' _ => ?_
  rw [Complex.re_ofReal_mul]

theorem pair_sum {ι : Type} (s : Finset ι) (p q a b : ι → ℝ) (hp : ∑ x ∈ s, p x = 1) (hq : ∑ x ∈ s, q x = 1) :
    ∑ x ∈ s, ∑ y ∈ s, p x * q y * ((a x + b y) / 2) = ((∑ x ∈ s, p x * a x) + ∑ y ∈ s, q y * b y) / 2 := by
  calc ∑ x ∈ s, ∑ y ∈ s, p x * q y * ((a x + b y) / 2) =
        (∑ x ∈ s, ∑ y ∈ s, (p x * a x) * q y + ∑ x ∈ s, ∑ y ∈ s, p x * (q y * b y)) / 2 := by
        rw [← Finset.sum_add_distrib, Finset.sum_div]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [← Finset.sum_add_distrib, Finset.sum_div]
        refine Finset.sum_congr rfl fun y _ => ?_
        ring
    _ = _ := by rw [← Finset.sum_mul_sum, ← Finset.sum_mul_sum, hq, hp]; ring

theorem liftV_core (S : C.HidaSetting E Wp Wq) (Λ : ℕ → ℕ → Fin S.f → ℝ) (hpos : C.ThmPPos S)
    (hL : ∀ v, KB.LiftLoc S v fun b s => Λ b s v) (ε : ℝ) (hε : 0 < ε) (i s : ℕ) (hs1 : 1 ≤ s) (hsi : s ≤ i)
    (hir : i ≤ S.G.r) (w : S.W) (hcnt : S.base.cnt w + C.Kst ≤ S.Ntop) :
    ∃ θ : Finset (Fin S.f) → S.W × S.W → ℝ,
      (∀ A, TB.IsProb (S.base.Wb (S.base.cnt w + C.Kst) ×ˢ S.base.Wb (S.base.cnt w + C.Kst)) (θ A)) ∧
      ∀ (Y : Finset (TB.Pt E)) (κa κw κb : TB.Pt E → TB.Pt E → ℂ),
        (∀ h ∈ Y, TB.level h = i - s) → KB.BlockPSD Y Y κa κw κb →
        ∀ (t t' : Fin S.f → ℂ), (∀ v, t v ≠ 0) → (∀ v, t' v ≠ 0) → ∀ A : Finset (Fin S.f),
          (∏ v ∈ A, ‖(t v)⁻¹ - (t' v)⁻¹‖ ^ C.Kst) * ‖KB.NstV S ε i s w Y κw t t'‖ ≤
            (∏ v ∈ A, Λ (i - s + 1) s v ^ C.Kst) *
              ∑ x ∈ S.base.Wb (S.base.cnt w + C.Kst) ×ˢ S.base.Wb (S.base.cnt w + C.Kst), θ A x *
                (((KB.NstV S ε i s x.1 Y κa t t).re + (KB.NstV S ε i s x.2 Y κb t' t').re) / 2) := by
  have hlen : ∀ v, (w.1 v).length + C.Kst ≤ S.Ntop := fun v => by have := len_le_cnt S w v; omega
  have H := fun v => hL v (i - s + 1) s (by omega) hs1 (by omega) (w.1 v) ⟨w, rfl⟩ (hlen v)
  have hbi : i - s + 1 + s - 1 = i := by omega
  have hb1 : i - s + 1 - 1 = i - s := by omega
  simp only [hbi, hb1] at H
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
  refine ⟨fun A x => (∏ v, th true A v (x.1.1 v)) * ∏ v, th false A v (x.2.1 v), fun A => ?_, ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hP true A
    obtain ⟨g1, g2, g3⟩ := hP false A
    refine ⟨fun x => mul_nonneg (h1 _) (g1 _), fun x hx => ?_, ?_⟩
    · rw [Finset.mem_product, not_and_or] at hx
      rcases hx with hx | hx
      · simp only [h2 _ hx, zero_mul]
      · simp only [g2 _ hx, mul_zero]
    · rw [Finset.sum_product]
      dsimp only at h3 g3 ⊢
      rw [← Finset.sum_mul_sum, h3, g3, one_mul]
  intro Y κa κw κb hY hκ t t' ht ht' A
  have hYv : ∀ v, ∀ h ∈ Y.image (C.loc (S.σ v)), D.ptSize h = i - s := by
    intro v h hh
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hh
    rw [Formalism.FourierDecayAlt.P.JCx1.needs.ptSize_loc]
    exact hY p hp
  let Pt : Fin S.f → TB.Pt E → C.LPt := fun v h => C.loc (S.σ v) h ++ [(s, t v)]
  let Pt' : Fin S.f → TB.Pt E → C.LPt := fun v h => C.loc (S.σ v) h ++ [(s, t' v)]
  let sc : Fin S.f → ℝ := fun v => if v ∈ A then Λ (i - s + 1) s v ^ C.Kst else 1
  let aK : Bool → Fin S.f → C.LPt → C.LPt → ℂ := fun sg v p q =>
    (sc v : ℂ) * ∑ a ∈ U sg A v, (th sg A v a : ℂ) * KB.gN S v ε i a p q
  have haK : ∀ sg v, (aK sg v) = if v ∈ A then (fun p q => ((Λ (i - s + 1) s v ^ C.Kst : ℝ) : ℂ) *
      KB.mix S v ε i (if sg then Up v else Um v) (if sg then θp v else θm v) p q)
      else KB.gN S v ε i (w.1 v) := by
    intro sg v
    funext p q
    by_cases hv : v ∈ A
    · cases sg <;> simp [aK, sc, U, th, hv, KB.mix]
    · simp [aK, sc, U, th, hv]
  have hc : ∀ v, ∃ c : ℂ, ‖c‖ = (if v ∈ A then ‖(t v)⁻¹ - (t' v)⁻¹‖ ^ C.Kst else 1) ∧
      KB.BlockPSD Y Y (fun p q => aK true v (Pt v p) (Pt v q))
        (fun p q => c * KB.gN S v ε i (w.1 v) (Pt v p) (Pt' v q)) (fun p q => aK false v (Pt' v p) (Pt' v q)) := by
    intro v
    by_cases hv : v ∈ A
    · obtain ⟨u, hu, hB⟩ := hblk v ε hε (t v) (t' v) (Y.image (C.loc (S.σ v))) (ht v) (ht' v) (hYv v)
      have hB' := blockPSD_pull Y (C.loc (S.σ v)) _ _ _ hB
      refine ⟨u * ((t v)⁻¹ - (t' v)⁻¹) ^ C.Kst, by simp [hv, hu, norm_pow], ?_⟩
      rw [haK true v, haK false v]
      simp only [hv, if_true, Bool.false_eq_true, if_false]
      exact hB'
    · refine ⟨1, by simp [hv], ?_⟩
      rw [haK true v, haK false v]
      simp only [hv, if_false, one_mul]
      exact lift_block0 S hpos v ε hε i (by omega) w Y (Pt v) (Pt' v)
  choose c hcn hcB using hc
  have hS := block_schur2 Y κa κw κb hκ (fun v p q => aK true v (Pt v p) (Pt v q))
    (fun v p q => c v * KB.gN S v ε i (w.1 v) (Pt v p) (Pt' v q))
    (fun v p q => aK false v (Pt' v p) (Pt' v q)) hcB
  have hsz' : ∏ v, (S.sizeAt v (w.1 v) : ℂ) = (C.Word.size S.P w.1 : ℂ) := by
    simp only [C.Word.size, C.HidaSetting.sizeAt, Complex.ofReal_prod]
  have hLh : ∑ p ∈ Y, ∑ q ∈ Y, κw p q * ∏ v, (c v * KB.gN S v ε i (w.1 v) (Pt v p) (Pt' v q)) =
      (∏ v, c v) * KB.NstV S ε i s w Y κw t t' := by
    unfold KB.NstV KB.gN
    simp only [Finset.prod_mul_distrib, Finset.prod_div_distrib, hsz']
    rw [Finset.sum_div, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_div, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    ring
  have hcp : ‖∏ v, c v‖ = ∏ v ∈ A, ‖(t v)⁻¹ - (t' v)⁻¹‖ ^ C.Kst := by
    rw [norm_prod, Finset.prod_congr rfl (fun v _ => hcn v)]
    convert prod_univ_ite (R := ℝ) A (fun v => ‖(t v)⁻¹ - (t' v)⁻¹‖ ^ C.Kst) using 3
  have hR : ∀ (sg : Bool) (κ : TB.Pt E → TB.Pt E → ℂ) (P : Fin S.f → TB.Pt E → C.LPt),
      (∑ p ∈ Y, ∑ q ∈ Y, κ p q * ∏ v, aK sg v (P v p) (P v q)).re =
      (∏ v ∈ A, Λ (i - s + 1) s v ^ C.Kst) * ∑ w' ∈ S.base.Wb (S.base.cnt w + C.Kst),
        (∏ v, th sg A v (w'.1 v)) *
          ((∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, S.gramLoc v ε i (w'.1 v) (P v h) (P v h')) /
            (C.Word.size S.P w'.1 : ℂ)).re := by
    intro sg κ P
    rw [rhs_eval2 S ε i Y κ _ hcnt (U sg A) (th sg A) (hU sg A) sc P P]
    congr 1
    convert prod_univ_ite (R := ℝ) A (fun v => Λ (i - s + 1) s v ^ C.Kst) using 3
  try dsimp only at hS
  rw [hLh, norm_mul, hcp, hR true κa Pt, hR false κb Pt'] at hS
  refine hS.trans (le_of_eq ?_)
  rw [Finset.sum_product]
  have hps := pair_sum (S.base.Wb (S.base.cnt w + C.Kst)) (fun x => ∏ v, th true A v (x.1 v))
    (fun y => ∏ v, th false A v (y.1 v)) (fun x => (KB.NstV S ε i s x Y κa t t).re)
    (fun y => (KB.NstV S ε i s y Y κb t' t').re) (hP true A).2.2 (hP false A).2.2
  dsimp only at hps ⊢
  rw [hps, ← mul_add, mul_div_assoc]
  rfl

end lift

end

end Formalism.FourierDecayAlt.P.PBB

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt

theorem lift_bound_below_top_all_places : Formalism.FourierDecayAlt.KB.LiftV :=
  fun _ _ _ _ _ _ _ _ _ _ S Λ hpos hL ε hε i s hs1 hsi hir w _ hcnt =>
    PBB.liftV_core S Λ hpos hL ε hε i s hs1 hsi hir w hcnt

end Formalism.FourierDecayAlt.P
