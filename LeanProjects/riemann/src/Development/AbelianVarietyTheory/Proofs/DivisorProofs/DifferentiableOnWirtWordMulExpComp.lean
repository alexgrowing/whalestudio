import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableRisingS
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors

noncomputable section

namespace GlobalTheory.WirtChain

open Complex

variable {Φ I : Type} [Fintype Φ] [Fintype I]

theorem contDiffOn_wirt' {V : Set (Φ → ℂ)} (hV : IsOpen V) {g : (Φ → ℂ) → ℂ} (hg : ContDiffOn ℝ ∞ g V)
    (τ : Φ) (bar : Bool) : ContDiffOn ℝ ∞ (wirt τ bar g) V := by
  have hd := ((contDiffOn_infty_iff_fderiv_of_isOpen hV).1 hg).2
  unfold wirt
  exact ((hd.clm_apply contDiffOn_const).add (contDiffOn_const.mul (hd.clm_apply contDiffOn_const))).div_const 2

theorem contDiffOn_wirtWord' {V : Set (Φ → ℂ)} (hV : IsOpen V) {g : (Φ → ℂ) → ℂ} (hg : ContDiffOn ℝ ∞ g V)
    (w : List (Φ × Bool)) : ContDiffOn ℝ ∞ (wirtWord w g) V := by
  induction w with
  | nil => simpa [wirtWord_nil] using hg
  | cons a w ih => rw [wirtWord_cons]; exact contDiffOn_wirt' hV ih _ _

open Classical in
theorem fderiv_eq_sum_wirt' (h : (Φ → ℂ) → ℂ) (y u : Φ → ℂ) :
    fderiv ℝ h y u = ∑ τ, (u τ * wirt τ false h y + (starRingEnd ℂ) (u τ) * wirt τ true h y) := by
  have hu : u = ∑ τ, ((u τ).re • (Pi.single τ (1:ℂ) : Φ → ℂ) + (u τ).im • (Pi.single τ I : Φ → ℂ)) := by
    ext τ'
    simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_ite, smul_zero]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq]
    simp [Complex.re_add_im]
  conv_lhs => rw [hu]
  rw [map_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [map_add, map_smul, map_smul]
  simp only [wirt, Bool.false_eq_true, if_false, if_true, real_smul]
  set A := fderiv ℝ h y (Pi.single τ 1)
  set B := fderiv ℝ h y (Pi.single τ I)
  have hc : (starRingEnd ℂ) (u τ) = (u τ).re - (u τ).im * I := by
    apply Complex.ext <;> simp
  have hu' : u τ = (u τ).re + (u τ).im * I := (Complex.re_add_im _).symm
  have key : ∀ (a c : ℝ) (A B : ℂ), (a:ℂ) * A + (c:ℂ) * B =
      ((a:ℂ) + (c:ℂ) * I) * ((A + -I * B) / 2) + ((a:ℂ) - (c:ℂ) * I) * ((A + I * B) / 2) := by
    intro a c A B
    ring_nf
    rw [I_sq]
    ring
  have := key (u τ).re (u τ).im A B
  rw [← hu', ← hc] at this
  linear_combination this

section Rep

variable (U : Set (I → ℂ)) (G : ℂ → (Φ → ℂ) → ℂ) (t : (I → ℂ) → Φ → ℂ) (l : (I → ℂ) → ℂ)

inductive ExpSum : (ℂ → (I → ℂ) → ℂ) → Prop
  | zero : ExpSum fun _ _ => 0
  | term (n : ℕ) (β : (I → ℂ) → ℂ) (w : List (Φ × Bool)) : ContDiffOn ℝ ∞ β U →
      ExpSum fun σ z => σ ^ n * β z * Complex.exp (-σ * l z) * wirtWord w (G σ) (t z)
  | add {F₁ F₂ : ℂ → (I → ℂ) → ℂ} : ExpSum F₁ → ExpSum F₂ → ExpSum fun σ z => F₁ σ z + F₂ σ z

variable {U G t l}

theorem ExpSum.const_mul {F : ℂ → (I → ℂ) → ℂ} (hF : ExpSum U G t l F) (c : ℂ) :
    ExpSum U G t l fun σ z => c * F σ z := by
  induction hF with
  | zero => simpa using ExpSum.zero (U := U) (G := G) (t := t) (l := l)
  | term n β w hβ =>
    have h := ExpSum.term (U := U) (G := G) (t := t) (l := l) n (fun z => c * β z) w (contDiffOn_const.mul hβ)
    convert h using 2
    ring_nf
  | add _ _ h₁ h₂ =>
    have h := ExpSum.add h₁ h₂
    convert h using 2
    ring_nf

theorem ExpSum.sum {α : Type} (s : Finset α) (F : α → ℂ → (I → ℂ) → ℂ) (hF : ∀ a ∈ s, ExpSum U G t l (F a)) :
    ExpSum U G t l fun σ z => ∑ a ∈ s, F a σ z := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ExpSum.zero (U := U) (G := G) (t := t) (l := l)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact ExpSum.add (hF a (Finset.mem_insert_self a s)) (ih fun b hb => hF b (Finset.mem_insert_of_mem hb))

theorem ExpSum.holo {D : Set ℂ} {V : Set (Φ → ℂ)} (hmaps : Set.MapsTo t U V)
    (hGh : ∀ w : List (Φ × Bool), ∀ y ∈ V, DifferentiableOn ℂ (fun σ => wirtWord w (G σ) y) D)
    {F : ℂ → (I → ℂ) → ℂ} (hF : ExpSum U G t l F) {z : I → ℂ} (hz : z ∈ U) :
    DifferentiableOn ℂ (fun σ => F σ z) D := by
  induction hF with
  | zero => exact differentiableOn_const _
  | term n β w hβ =>
    exact (((differentiableOn_id.pow n).mul (differentiableOn_const _)).mul
      ((differentiableOn_id.neg.mul_const (l z)).cexp)).mul (hGh w (t z) (hmaps hz))
  | add _ _ h₁ h₂ => exact h₁.add h₂

theorem ExpSum.smooth {D : Set ℂ} {V : Set (Φ → ℂ)} (hV : IsOpen V) (hmaps : Set.MapsTo t U V)
    (ht : ContDiffOn ℝ ∞ t U) (hl : ContDiffOn ℝ ∞ l U)
    (hGs : ∀ σ ∈ D, ContDiffOn ℝ ∞ (G σ) V)
    {F : ℂ → (I → ℂ) → ℂ} (hF : ExpSum U G t l F) {σ : ℂ} (hσ : σ ∈ D) :
    ContDiffOn ℝ ∞ (F σ) U := by
  induction hF with
  | zero => exact contDiffOn_const
  | term n β w hβ =>
    exact ((contDiffOn_const.mul hβ).mul (contDiffOn_const.mul hl).cexp).mul
      ((contDiffOn_wirtWord' hV (hGs σ hσ) w).comp ht hmaps)
  | add _ _ h₁ h₂ => exact h₁.add h₂

end Rep

section Deriv

variable {U : Set (I → ℂ)} {G : ℂ → (Φ → ℂ) → ℂ} {t : (I → ℂ) → Φ → ℂ} {l : (I → ℂ) → ℂ}

theorem ExpSum.deriv {D : Set ℂ} {V : Set (Φ → ℂ)} (hU : IsOpen U) (hV : IsOpen V) (hmaps : Set.MapsTo t U V)
    (ht : ContDiffOn ℝ ∞ t U) (hl : ContDiffOn ℝ ∞ l U)
    (hGs : ∀ σ ∈ D, ContDiffOn ℝ ∞ (G σ) V)
    {F : ℂ → (I → ℂ) → ℂ} (hF : ExpSum U G t l F) (v : I → ℂ) :
    ∃ F', ExpSum U G t l F' ∧ ∀ σ ∈ D, ∀ z ∈ U, fderiv ℝ (F σ) z v = F' σ z := by
  have hdt := ((contDiffOn_infty_iff_fderiv_of_isOpen hU).1 ht).2
  have hdl := ((contDiffOn_infty_iff_fderiv_of_isOpen hU).1 hl).2
  have hdtv : ContDiffOn ℝ ∞ (fun z => fderiv ℝ t z v) U := hdt.clm_apply contDiffOn_const
  have hdlv : ContDiffOn ℝ ∞ (fun z => fderiv ℝ l z v) U := hdl.clm_apply contDiffOn_const
  induction hF with
  | zero => exact ⟨fun _ _ => 0, ExpSum.zero, fun σ _ z _ => by simp⟩
  | @add F₁ F₂ h₁ h₂ ih₁ ih₂ =>
    obtain ⟨F₁', h₁', e₁⟩ := ih₁
    obtain ⟨F₂', h₂', e₂⟩ := ih₂
    refine ⟨fun σ z => F₁' σ z + F₂' σ z, ExpSum.add h₁' h₂', fun σ hσ z hz => ?_⟩
    have d₁ := ((h₁.smooth hV hmaps ht hl hGs hσ).differentiableOn (by simp)).differentiableAt (hU.mem_nhds hz)
    have d₂ := ((h₂.smooth hV hmaps ht hl hGs hσ).differentiableOn (by simp)).differentiableAt (hU.mem_nhds hz)
    show fderiv ℝ (fun y => F₁ σ y + F₂ σ y) z v = F₁' σ z + F₂' σ z
    have hsum : HasFDerivAt (fun y => F₁ σ y + F₂ σ y) _ z := d₁.hasFDerivAt.add d₂.hasFDerivAt
    rw [hsum.fderiv, ContinuousLinearMap.add_apply, e₁ σ hσ z hz, e₂ σ hσ z hz]
  | term n β w hβ =>
    have hdb := ((contDiffOn_infty_iff_fderiv_of_isOpen hU).1 hβ).2
    have hdbv : ContDiffOn ℝ ∞ (fun z => fderiv ℝ β z v) U := hdb.clm_apply contDiffOn_const
    refine ⟨fun σ z => (σ ^ n * fderiv ℝ β z v * Complex.exp (-σ * l z) * wirtWord w (G σ) (t z) +
        σ ^ (n + 1) * (-(β z * fderiv ℝ l z v)) * Complex.exp (-σ * l z) * wirtWord w (G σ) (t z)) +
        ∑ τ : Φ, (σ ^ n * (β z * fderiv ℝ t z v τ) * Complex.exp (-σ * l z) * wirtWord ((τ, false) :: w) (G σ) (t z) +
          σ ^ n * (β z * (starRingEnd ℂ) (fderiv ℝ t z v τ)) * Complex.exp (-σ * l z) *
            wirtWord ((τ, true) :: w) (G σ) (t z)), ?_, ?_⟩
    · refine ExpSum.add (ExpSum.add (ExpSum.term n _ w hdbv) (ExpSum.term (n + 1) _ w (hβ.mul hdlv).neg))
        (ExpSum.sum Finset.univ _ fun τ _ => ExpSum.add (ExpSum.term n _ _ (hβ.mul (contDiffOn_pi.1 hdtv τ)))
          (ExpSum.term n _ _ (hβ.mul ?_)))
      have := Complex.conjCLE.contDiff.comp_contDiffOn (contDiffOn_pi.1 hdtv τ)
      simpa [Function.comp_def] using this
    · intro σ hσ z hz
      have hzn := hU.mem_nhds hz
      set W := wirtWord w (G σ) with hWdef
      have hWs : ContDiffOn ℝ ∞ W V := contDiffOn_wirtWord' hV (hGs σ hσ) w
      have hb' : HasFDerivAt β (fderiv ℝ β z) z :=
        ((hβ.differentiableOn (by simp)).differentiableAt hzn).hasFDerivAt
      have hl' : HasFDerivAt l (fderiv ℝ l z) z :=
        ((hl.differentiableOn (by simp)).differentiableAt hzn).hasFDerivAt
      have ht' : HasFDerivAt t (fderiv ℝ t z) z :=
        ((ht.differentiableOn (by simp)).differentiableAt hzn).hasFDerivAt
      have hW' : HasFDerivAt W (fderiv ℝ W (t z)) (t z) :=
        ((hWs.differentiableOn (by simp)).differentiableAt (hV.mem_nhds (hmaps hz))).hasFDerivAt
      have hE := (hl'.const_mul (-σ)).cexp
      have hWt := hW'.comp z ht'
      have hall := ((hb'.const_mul (σ ^ n)).mul hE).mul hWt
      have hall' : HasFDerivAt (fun y => σ ^ n * β y * Complex.exp (-σ * l y) * W (t y)) _ z := hall
      rw [hall'.fderiv]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
        ContinuousLinearMap.comp_apply, Function.comp_apply, Pi.mul_apply]
      rw [fderiv_eq_sum_wirt' W (t z) (fderiv ℝ t z v)]
      simp only [wirtWord_cons]
      rw [← hWdef]
      have hs : ∀ τ : Φ, σ ^ n * β z * Complex.exp (-σ * l z) * (fderiv ℝ t z v τ * wirt τ false W (t z) +
          (starRingEnd ℂ) (fderiv ℝ t z v τ) * wirt τ true W (t z)) =
          σ ^ n * (β z * fderiv ℝ t z v τ) * Complex.exp (-σ * l z) * wirt τ false W (t z) +
          σ ^ n * (β z * (starRingEnd ℂ) (fderiv ℝ t z v τ)) * Complex.exp (-σ * l z) * wirt τ true W (t z) :=
        fun τ => by ring
      rw [Finset.mul_sum]
      simp only [hs]
      ring

end Deriv

open Classical in

theorem differentiableOn_wirtWord_mul_exp_comp : ∀ (Φ I : Type) [Fintype Φ] [Fintype I] (U : Set (I → ℂ)) (V : Set (Φ → ℂ)) (D : Set ℂ) (G : ℂ → (Φ → ℂ) → ℂ) (t : (I → ℂ) → Φ → ℂ) (b l : (I → ℂ) → ℂ), IsOpen U → IsOpen V → Set.MapsTo t U V → ContDiffOn ℝ ∞ t U → ContDiffOn ℝ ∞ b U → ContDiffOn ℝ ∞ l U → (∀ σ ∈ D, ContDiffOn ℝ ∞ (G σ) V) → (∀ w : List (Φ × Bool), ∀ y ∈ V, DifferentiableOn ℂ (fun σ => wirtWord w (G σ) y) D) → ∀ w : List (I × Bool), ∀ z ∈ U, DifferentiableOn ℂ (fun σ => wirtWord w (fun z' => b z' * Complex.exp (-σ * l z') * G σ (t z')) z) D := by
  intro Φ I _ _ U V D G t b l hU hV hmaps ht hb hl hGs hGh w z hz
  have key : ∀ w : List (I × Bool), ∃ F, ExpSum U G t l F ∧ ∀ σ ∈ D,
      Set.EqOn (wirtWord w (fun z' => b z' * Complex.exp (-σ * l z') * G σ (t z'))) (F σ) U := by
    intro w
    induction w with
    | nil =>
      refine ⟨_, ExpSum.term 0 b [] hb, fun σ _ z _ => ?_⟩
      simp [wirtWord_nil]
    | cons a w ih =>
      obtain ⟨F, hF, hEq⟩ := ih
      obtain ⟨F₁, hF₁, hd₁⟩ := hF.deriv hU hV hmaps ht hl hGs (Pi.single a.1 1)
      obtain ⟨F₂, hF₂, hd₂⟩ := hF.deriv hU hV hmaps ht hl hGs (Pi.single a.1 Complex.I)
      refine ⟨fun σ z => (1 / 2 : ℂ) * (F₁ σ z + (if a.2 then Complex.I else -Complex.I) * F₂ σ z),
        (ExpSum.add hF₁ (hF₂.const_mul _)).const_mul _, fun σ hσ z hz => ?_⟩
      have hev : wirtWord w (fun z' => b z' * Complex.exp (-σ * l z') * G σ (t z')) =ᶠ[nhds z] F σ :=
        Filter.eventually_of_mem (hU.mem_nhds hz) fun y hy => hEq σ hσ hy
      rw [wirtWord_cons]
      simp only [wirt]
      rw [hev.fderiv_eq, hd₁ σ hσ z hz, hd₂ σ hσ z hz]
      ring
  obtain ⟨F, hF, hEq⟩ := key w
  exact (hF.holo hmaps hGh hz).congr fun σ hσ => hEq σ hσ hz

end GlobalTheory.WirtChain
