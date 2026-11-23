import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
import Formalism.LocalToGlobal.Columns.ChainTw
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ResiduesOfCompletionAtPrimeWithUniformizer
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompletionChainLatticeEntriesAgree

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

noncomputable section
namespace GlobalTheory.TwBridge.PhiProof
open GlobalTheory.SymBridge

section Core
variable {E K k : Type} [Field E] [NumberField E] [Field K]
  [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def lPos {κ l : ℕ} : Fin κ ⊕ Fin l → ℕ := Sum.elim (fun i => i.val) (fun i => κ + i.val)

theorem zPos_inl {κ l τ j : ℕ} (a : Fin κ ⊕ Fin l) :
    zPos (κ := κ) (τ := τ) (l := l) (j := j) (Sum.inl a) = lPos a := by
  rcases a with i | i <;> rfl

theorem lPos_lt {κ l : ℕ} (a : Fin κ ⊕ Fin l) : lPos a < κ + l := by
  rcases a with i | i <;> simp [lPos] <;> omega

theorem le_zPos_inr {κ l τ j : ℕ} (p : Fin j × Fin τ) :
    κ + l ≤ zPos (κ := κ) (τ := τ) (l := l) (j := j) (Sum.inr p) := by
  simp only [zPos]; omega

def enum (κ l τ j : ℕ) : Ix (Fin κ ⊕ Fin l) (Fin τ) j ≃ Fin (κ + l + j * τ) :=
  (Equiv.sumCongr finSumFinEquiv finProdFinEquiv).trans finSumFinEquiv

theorem enum_val {κ l τ j : ℕ} (a : Ix (Fin κ ⊕ Fin l) (Fin τ) j) : ((enum κ l τ j a : Fin _) : ℕ) = zPos a := by
  rcases a with (i | i) | ⟨i, u⟩ <;> simp [enum, zPos, finProdFinEquiv] <;> ring

theorem zPos_lt {κ l τ j : ℕ} (a : Ix (Fin κ ⊕ Fin l) (Fin τ) j) : zPos a < κ + l + j * τ := by
  rw [← enum_val]; exact Fin.isLt _

theorem exists_zPos {κ l τ j p : ℕ} (hp : p < κ + l + j * τ) : ∃ a : Ix (Fin κ ⊕ Fin l) (Fin τ) j, zPos a = p :=
  ⟨(enum κ l τ j).symm ⟨p, hp⟩, by rw [← enum_val, Equiv.apply_symm_apply]⟩

theorem det_lPos (ι : E →+* k) (κ l : ℕ) (M : ℕ → ℕ → E) :
    (Matrix.of fun a b : Fin κ ⊕ Fin l => ι (M (lPos a) (lPos b))).det =
      ι (Matrix.of fun s t : Fin (κ + l) => M s.1 t.1).det := by
  have hT : (Matrix.of fun a b : Fin κ ⊕ Fin l => ι (M (lPos a) (lPos b))) =
      ((Matrix.of fun s t : Fin (κ + l) => M s.1 t.1).map ι).submatrix finSumFinEquiv finSumFinEquiv := by
    ext (a | a) (b | b) <;> simp [lPos]
  rw [hT, Matrix.det_submatrix_equiv_self, RingHom.map_det]; rfl

theorem mem_KO_iff (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k) (ϖ : kˣ) (hC : IsCompl P q ι ϖ)
    (hU : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ) (κ l : ℕ) (M : ℕ → ℕ → E) :
    (∃ g ∈ KO k (Fin κ ⊕ Fin l), g.val = Matrix.of fun a b => ι (M (lPos a) (lPos b))) ↔
      (∀ p p', p < κ + l → p' < κ + l → IntAt P (M p p')) ∧
        IsUnit (redP P (Matrix.det (Matrix.of fun s t : Fin (κ + l) => M s.1 t.1))) := by
  let e : Fin κ ⊕ Fin l ≃ Fin (κ + l) := finSumFinEquiv
  have he : ∀ a, ((e a : Fin _) : ℕ) = lPos a := by rintro (i | i) <;> simp [e, lPos]
  let A : Matrix (Fin (κ + l)) (Fin (κ + l)) E := Matrix.of fun s t => M s.1 t.1
  let T : Matrix (Fin κ ⊕ Fin l) (Fin κ ⊕ Fin l) k := Matrix.of fun a b => ι (M (lPos a) (lPos b))
  have hdet : T.det = ι A.det := det_lPos ι κ l M
  have hint : ∀ x : k, valuation k x = 1 → x ∈ 𝒪[k] := fun x hx =>
    (Valuation.mem_integer_iff (valuation k) x).2 hx.le
  change (∃ g ∈ KO k (Fin κ ⊕ Fin l), g.val = T) ↔ _
  constructor
  · rintro ⟨g, hg, hgv⟩
    have hI := intM_of_mem_KO hg
    rw [hgv] at hI
    refine ⟨fun p p' hp hp' => ?_, ?_⟩
    · have h := hI (e.symm ⟨p, hp⟩) (e.symm ⟨p', hp'⟩)
      simp only [T, Matrix.of_apply] at h
      rw [← he, ← he, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
      exact (hC.int _).1 h
    · have hv := valuation_det_of_mem_KO hg
      rw [Matrix.GeneralLinearGroup.val_det_apply, hgv, hdet] at hv
      exact (ComplRes.v_eq_one_iff_red hC hU ((hC.int _).1 (hint _ hv))).1 hv
  · rintro ⟨hent, hunit⟩
    have hTint : ∀ a b, T a b ∈ 𝒪[k] := fun a b =>
      (hC.int _).2 (hent _ _ (he a ▸ (e a).2) (he b ▸ (e b).2))
    let B : Matrix (Fin κ ⊕ Fin l) (Fin κ ⊕ Fin l) 𝒪[k] := Matrix.of fun a b => ⟨T a b, hTint a b⟩
    have hB : B.map (algebraMap 𝒪[k] k) = T := by ext a b; rfl
    have hBdet : algebraMap 𝒪[k] k B.det = ι A.det := by
      rw [RingHom.map_det]; change (B.map (algebraMap 𝒪[k] k)).det = _; rw [hB, hdet]
    have hAint : IntAt P A.det := (hC.int _).1 (hBdet ▸ (B.det).2)
    have hv : valuation k (ι A.det) = 1 := (ComplRes.v_eq_one_iff_red hC hU hAint).2 hunit
    have hBu : IsUnit B.det :=
      (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.2 (by rw [hBdet]; exact hv)
    refine ⟨Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) (B.nonsingInvUnit hBu), ⟨_, rfl⟩, ?_⟩
    ext a b
    rw [Matrix.GeneralLinearGroup.map_apply]
    rfl

theorem core (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k) (ϖ : kˣ) (σ₀ : K →+* ℂ)
    (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (δ : kˣ →* ℂˣ) (hC : IsCompl P q ι ϖ) (hU : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ)
    (hδ : ∀ a (u : kˣ), IntAt P a → IsUnit (redP P a) → (u : k) = ι a → (δ u : ℂ) = (σ₀ (LocE.unitV ξ a))⁻¹)
    {κ l τ j j' r b a : ℕ} (hr : r = κ + l) (hb : b = κ + l + j * τ) (ha : a = κ + l + j' * τ) (M : ℕ → ℕ → E)
    (Y : Matrix (Ix (Fin κ ⊕ Fin l) (Fin τ) j) (Ix (Fin κ ⊕ Fin l) (Fin τ) j') k)
    (hY : ∀ x y, Y x y = ι (M (zPos x) (zPos y))) :
    (((∀ p p', p < b → p' < a → IntAt P (M p p')) ∧
        (∀ p p', r ≤ p → p < b → p' < r → IntAt P (M p p' / (q : E)))) →
      parPhi δ Y = σ₀ (LocE.unitV ξ (Matrix.det (Matrix.of fun s t : Fin r => M s.1 t.1)))) ∧
    (¬ ((∀ p p', p < b → p' < a → IntAt P (M p p')) ∧
        (∀ p p', r ≤ p → p < b → p' < r → IntAt P (M p p' / (q : E)))) → parPhi δ Y = 0) := by
  subst hr hb ha
  have h11 : Y.toBlocks₁₁ = Matrix.of fun x y : Fin κ ⊕ Fin l => ι (M (lPos x) (lPos y)) := by
    ext x y; simp only [toBlocks₁₁, of_apply, hY, zPos_inl]
  have key : ((∃ g ∈ KO k (Fin κ ⊕ Fin l), g.val = Y.toBlocks₁₁) ∧ MaxM Y.toBlocks₂₁ ∧ IntM Y.toBlocks₁₂ ∧
      IntM Y.toBlocks₂₂) ↔
      (((∀ p p', p < κ + l + j * τ → p' < κ + l + j' * τ → IntAt P (M p p')) ∧
        (∀ p p', κ + l ≤ p → p < κ + l + j * τ → p' < κ + l → IntAt P (M p p' / (q : E)))) ∧
        IsUnit (redP P (Matrix.det (Matrix.of fun s t : Fin (κ + l) => M s.1 t.1)))) := by
    rw [h11, mem_KO_iff P q ι ϖ hC hU]
    constructor
    · rintro ⟨⟨hI11, hu⟩, h21, h12, h22⟩
      have hB11 : IntM Y.toBlocks₁₁ := by
        rw [h11]; intro x y
        exact (hC.int _).2 (hI11 _ _ (lPos_lt x) (lPos_lt y))
      have hIY : IntM Y := by
        rw [← fromBlocks_toBlocks Y]; exact intM_fromBlocks.2 ⟨hB11, h12, h21.intM, h22⟩
      refine ⟨⟨fun p p' hp hp' => ?_, fun p p' hp1 hp2 hp' => ?_⟩, hu⟩
      · obtain ⟨x, rfl⟩ := exists_zPos hp
        obtain ⟨y, rfl⟩ := exists_zPos hp'
        have := hIY x y
        rw [hY] at this
        exact (hC.int _).1 this
      · obtain ⟨x, rfl⟩ := exists_zPos hp2
        obtain ⟨y, rfl⟩ := exists_zPos (j := j') (by nlinarith : p' < κ + l + j' * τ)
        rcases x with x0 | x1
        · rw [zPos_inl] at hp1; exact absurd hp1 (not_le.2 (lPos_lt x0))
        rcases y with y0 | y1
        · have := h21 x1 y0
          simp only [toBlocks₂₁, of_apply, hY] at this
          exact (ComplRes.v_div_q hC hU _).1 this
        · exact absurd hp' (not_lt.2 (le_zPos_inr y1))
    · rintro ⟨⟨h1, h2⟩, hu⟩
      have hIY : ∀ x y, Y x y ∈ 𝒪[k] := fun x y => by
        rw [hY]; exact (hC.int _).2 (h1 _ _ (zPos_lt x) (zPos_lt y))
      refine ⟨⟨fun p p' hp hp' => h1 p p' (by omega) (by omega), hu⟩, fun x y => ?_, fun x y => hIY _ _,
        fun x y => hIY _ _⟩
      show valuation k (Y (Sum.inr x) (Sum.inl y)) < 1
      rw [hY]
      refine (ComplRes.v_div_q hC hU _).2 (h2 _ _ (le_zPos_inr x) (zPos_lt _) ?_)
      rw [zPos_inl]; exact lPos_lt y
  constructor
  · intro hc
    by_cases hu : IsUnit (redP P (Matrix.det (Matrix.of fun s t : Fin (κ + l) => M s.1 t.1)))
    · obtain ⟨⟨g, hg, hgv⟩, h21, h12, h22⟩ := key.2 ⟨hc, hu⟩
      rw [parPhi_of_mem δ hg hgv h21 h12 h22]
      have hdet : ((Matrix.GeneralLinearGroup.det g : kˣ) : k) =
          ι (Matrix.det (Matrix.of fun s t : Fin (κ + l) => M s.1 t.1)) := by
        rw [Matrix.GeneralLinearGroup.val_det_apply, hgv, h11, det_lPos]
      have hv := valuation_det_of_mem_KO hg
      rw [Matrix.GeneralLinearGroup.val_det_apply, hgv, h11, det_lPos] at hv
      have hint : IntAt P (Matrix.det (Matrix.of fun s t : Fin (κ + l) => M s.1 t.1)) :=
        (hC.int _).1 ((Valuation.mem_integer_iff _ _).2 hv.le)
      rw [Units.val_inv_eq_inv_val, hδ _ _ hint hu hdet, inv_inv]
    · have h0 : LocE.unitV ξ (Matrix.det (Matrix.of fun s t : Fin (κ + l) => M s.1 t.1)) = 0 := by
        unfold LocE.unitV; rw [dif_neg hu]
      rw [h0, map_zero]
      by_contra hne
      exact hu (key.1 ((parPhi_ne_zero_iff δ).1 hne)).2
  · intro hc
    by_contra hne
    exact hc (key.1 ((parPhi_ne_zero_iff δ).1 hne)).1

end Core

theorem plain_coords {k : Type} [Field k] {ι ι' n n' : Type*} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    {c c' : ℕ} (ord : ι ≃ n ⊕ Fin c) (ord' : ι' ≃ n' ⊕ Fin c') (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin c') k) (a : ι) (b : ι') :
    (plainFrame ord).coords (plainFrame ord') x a b = x (ord a) (ord' b) := by
  simp [LatFrame.coords, plainFrame]

theorem refl_coords {k : Type} [Field k] {ι n' : Type*} [Fintype ι] [DecidableEq ι] [Fintype n'] [DecidableEq n']
    {ι' : Type*} {c' : ℕ} (ord' : ι' ≃ n' ⊕ Fin c') (x : Matrix ι (n' ⊕ Fin c') k) (a : ι) (b : ι') :
    (LatFrame.refl k ι).coords (plainFrame ord') x a b = x a (ord' b) := by
  simp [LatFrame.coords, LatFrame.refl, plainFrame]

theorem scE_zero (n l : ℕ) : LocE.scE n 0 l = 0 := by
  unfold LocE.scE; split_ifs <;> simp

theorem fIdx_zero (κ n v : ℕ) : LocE.fIdx κ 0 n v = v := by
  unfold LocE.fIdx; split_ifs <;> omega

section Main
variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S₀ : Set ℕ}
  (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu)
  {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k)
  (s : ℕ) (W : TwData k)

theorem phi_steps (hA : AtTwist (R := R) sel mu cst σ₀ P ι s W) (j c : ℕ) (h : j + c = s)
    (e' : XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1) ≃ Fin (R.N j + cOf R j))
    (e : XIx (Fin R.k) (Fin R.t) (j + 1) ⊕ Fin c ≃ Fin (R.N (j + 1) + cOf R (j + 1)))
    (he' : IsOrdY e') (he : IsOrdY e) (x : HomE X.E (R.N j + cOf R j) (R.N (j + 1) + cOf R (j + 1))) :
    (W.T s R).Phi j c h (toLoc ι e e' x) = σ₀ (PhiAt Ch mu cst.sharp j P.1 x) := by
  have hm := hA.steps
  have hPhi : PhiAt Ch mu cst.sharp j P.1 x = LocE.PhiQ (qOf P.1) (resChar (mu : Chr X.F X.E X.K) P.1) R.k R.r
      (cOf R j) (R.N j) (cOf R (j + 1)) (R.N (j + 1)) x := by
    unfold PhiAt; rw [if_neg hA.nmem]
  have hT : (W.T s R).Phi j c h (toLoc ι e e' x) = parPhi W.δ
      ((plainFrame (stdOrd (Fin R.k) (Fin R.t) (l := s + 1) (j + 1) c (by omega))).coords
        (plainFrame (stdOrd (Fin R.k) (Fin R.t) (l := s + 1) j (c + 1) (by omega))) (toLoc ι e e' x)) := rfl
  have hc1 : c = cOf R (j + 1) := by simp only [cOf]; omega
  have hc2 : c + 1 = cOf R j := by simp only [cOf]; omega
  have hY : ∀ a b, (plainFrame (stdOrd (Fin R.k) (Fin R.t) (l := s + 1) (j + 1) c (by omega))).coords
      (plainFrame (stdOrd (Fin R.k) (Fin R.t) (l := s + 1) j (c + 1) (by omega))) (toLoc ι e e' x) a b =
      ι (LocE.entB (qOf P.1) R.k (cOf R j) (R.N j) (cOf R (j + 1)) (R.N (j + 1)) 0 0 x (zPos a) (zPos b)) := by
    intro a b
    have ha1 : (e (stdOrd (Fin R.k) (Fin R.t) (l := s + 1) (j + 1) c (by omega) a)).val =
        LocE.fIdx R.k (cOf R (j + 1)) (R.N (j + 1)) (zPos a) :=
      (EntryBases.stdOrd_place (l := s + 1) (by omega) rfl e he a).1.trans (by rw [← hc1]; rfl)
    have hb1 : (e' (stdOrd (Fin R.k) (Fin R.t) (l := s + 1) j (c + 1) (by omega) b)).val =
        LocE.fIdx R.k (cOf R j) (R.N j) (zPos b) :=
      (EntryBases.stdOrd_place (l := s + 1) (by omega) rfl e' he' b).1.trans (by rw [← hc2]; rfl)
    rw [plain_coords]
    simp only [toLoc, LocE.entB, scE_zero, sub_self, zpow_zero, mul_one]
    rw [← ha1, ← hb1, EntryBases.eN_val, EntryBases.atN_val]
  have hr : R.r = R.k + (s + 1) := by simp only [Ranks.r]; omega
  have hb : R.N (j + 1) + cOf R (j + 1) = R.k + (s + 1) + (j + 1) * R.t := by
    simp only [Ranks.N, cOf, add_mul, mul_add, one_mul, mul_one]; omega
  have ha : R.N j + cOf R j = R.k + (s + 1) + j * R.t := by
    simp only [Ranks.N, cOf, mul_add, mul_one]; omega
  have hcore := core P.1 (qOf P.1) ι W.ϖ σ₀ (resChar (mu : Chr X.F X.E X.K) P.1) W.δ hA.compl W.unif hA.del hr hb ha
    (fun p p' => LocE.entB (qOf P.1) R.k (cOf R j) (R.N j) (cOf R (j + 1)) (R.N (j + 1)) 0 0 x p p') _ hY
  rw [hT, hPhi]
  unfold LocE.PhiQ
  split_ifs with hc
  · exact hcore.1 hc
  · rw [map_zero]; exact hcore.2 hc

theorem phi_top (hA : AtTwist (R := R) sel mu cst σ₀ P ι s W)
    (e' : XIx (Fin R.k) (Fin R.t) (s + 1) ⊕ Fin 0 ≃ Fin (R.N (s + 1) + cOf R (s + 1)))
    (e : Ix (Fin R.k ⊕ Fin (s + 1)) (Fin R.t) (s + 2) ≃ Fin (R.N R.m - 1 + 0)) (he' : IsOrdY e') (he : IsOrd zPos e)
    (x : HomE X.E (R.N (s + 1) + cOf R (s + 1)) (R.N R.m - 1 + 0)) :
    (W.T s R).PhiTop (toLoc ι e e' x) = σ₀ (PhiTop Ch mu cst.sharp s P.1 x) := by
  have hm := hA.steps
  have hPhi : PhiTop Ch mu cst.sharp s P.1 x = LocE.PhiQ (qOf P.1) (resChar (mu : Chr X.F X.E X.K) P.1) R.k R.r
      (cOf R (s + 1)) (R.N (s + 1)) 0 (R.N R.m - 1) x := by
    unfold PhiTop; rw [if_neg hA.nmem]
  have hT : (W.T s R).PhiTop (toLoc ι e e' x) = parPhi W.δ
      ((LatFrame.refl k (Ix (Fin R.k ⊕ Fin (s + 1)) (Fin R.t) (s + 2))).coords
        (plainFrame (stdOrd (Fin R.k) (Fin R.t) (l := s + 1) (s + 1) 0 rfl)) (toLoc ι e e' x)) := rfl
  have hc2 : 0 = cOf R (s + 1) := by simp only [cOf]; omega
  have hY : ∀ a b, (LatFrame.refl k (Ix (Fin R.k ⊕ Fin (s + 1)) (Fin R.t) (s + 2))).coords
      (plainFrame (stdOrd (Fin R.k) (Fin R.t) (l := s + 1) (s + 1) 0 rfl)) (toLoc ι e e' x) a b =
      ι (LocE.entB (qOf P.1) R.k (cOf R (s + 1)) (R.N (s + 1)) 0 (R.N R.m - 1) 0 0 x (zPos a) (zPos b)) := by
    intro a b
    have ha1 : (e a).val = LocE.fIdx R.k 0 (R.N R.m - 1) (zPos a) := by rw [fIdx_zero]; exact he a
    have hb1 : (e' (stdOrd (Fin R.k) (Fin R.t) (l := s + 1) (s + 1) 0 rfl b)).val =
        LocE.fIdx R.k (cOf R (s + 1)) (R.N (s + 1)) (zPos b) :=
      (EntryBases.stdOrd_place (κ := R.k) (τ := R.t) (j := s + 1) (c := 0) (l := s + 1) rfl rfl e' he' b).1.trans (by rw [← hc2]; rfl)
    rw [refl_coords]
    simp only [toLoc, LocE.entB, scE_zero, sub_self, zpow_zero, mul_one]
    rw [← ha1, ← hb1, EntryBases.eN_val, EntryBases.atN_val]
  have hr : R.r = R.k + (s + 1) := by simp only [Ranks.r]; omega
  have hb : R.N R.m - 1 + 0 = R.k + (s + 1) + (s + 2) * R.t := by
    simp only [Ranks.N, hm, add_mul, mul_add, one_mul, mul_one]; omega
  have ha : R.N (s + 1) + cOf R (s + 1) = R.k + (s + 1) + (s + 1) * R.t := by
    simp only [Ranks.N, cOf, mul_add, mul_one]; omega
  have hcore := core P.1 (qOf P.1) ι W.ϖ σ₀ (resChar (mu : Chr X.F X.E X.K) P.1) W.δ hA.compl W.unif hA.del hr hb ha
    (fun p p' => LocE.entB (qOf P.1) R.k (cOf R (s + 1)) (R.N (s + 1)) 0 (R.N R.m - 1) 0 0 x p p') _ hY
  rw [hT, hPhi]
  unfold LocE.PhiQ
  split_ifs with hc
  · exact hcore.1 hc
  · rw [map_zero]; exact hcore.2 hc

end Main

theorem phiAgree_of_atTwist : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → PhiAgree Ch sel mu cst σ₀ P ι s W := by
  intro X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s W _ _ ν _ _ hA
  exact ⟨fun j c h e' e he' he x => phi_steps Ch sel mu cst σ₀ P ι s W hA j c h e' e he' he x,
    fun e' e he' he x => phi_top Ch sel mu cst σ₀ P ι s W hA e' e he' he x⟩

end GlobalTheory.TwBridge.PhiProof
