import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockDiagonalMinorVanishing
import ReciprocityTheory.SemistableReduction.SemiContractA
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.SchurCalc

variable {N : ℕ}

theorem minorIJ_eq_submatrix {k m : ℕ} (X : Matrix (Fin N) (Fin N) ℂ) (I J : Finset (Fin N))
    (g g' : Fin k ⊕ Fin m → Fin N) (hI : I.card = k + m) (hJ : J.card = k + m)
    (hg : ∀ x, g x ∈ I) (hg' : ∀ x, g' x ∈ J)
    (sg : StrictMono (g ∘ finSumFinEquiv.symm)) (sg' : StrictMono (g' ∘ finSumFinEquiv.symm)) :
    minorIJ X I J = (X.submatrix g g').det := by
  rw [MinorCalc.minorIJ_eq_det X I J (k + m) hI hJ,
    ← Finset.orderEmbOfFin_unique hI (f := g ∘ finSumFinEquiv.symm) (fun x => hg _) sg,
    ← Finset.orderEmbOfFin_unique hJ (f := g' ∘ finSumFinEquiv.symm) (fun x => hg' _) sg',
    ← Matrix.det_submatrix_equiv_self finSumFinEquiv.symm (X.submatrix g g')]
  rfl

theorem strictMono_elim {k m : ℕ} (e : Fin k → Fin N) (c : Fin m → Fin N) (he : StrictMono e)
    (hc : StrictMono c) (hec : ∀ x y, e x < c y) :
    StrictMono (Sum.elim e c ∘ finSumFinEquiv.symm) := by
  intro x y hxy
  induction x using Fin.addCases with
  | left x =>
    induction y using Fin.addCases with
    | left y =>
      simp only [Function.comp, finSumFinEquiv_symm_apply_castAdd, Sum.elim_inl]
      exact he (Fin.lt_def.2 (by simpa only [Fin.lt_def, Fin.val_castAdd] using hxy))
    | right y =>
      simp only [Function.comp, finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
        Sum.elim_inl, Sum.elim_inr]
      exact hec x y
  | right x =>
    induction y using Fin.addCases with
    | left y =>
      exfalso
      simp only [Fin.lt_def, Fin.val_natAdd, Fin.val_castAdd] at hxy
      have := y.2
      omega
    | right y =>
      simp only [Function.comp, finSumFinEquiv_symm_apply_natAdd, Sum.elim_inr]
      exact hc (Fin.lt_def.2 (by
        have h' := Fin.lt_def.1 hxy
        simp only [Fin.val_natAdd] at h'
        omega))

theorem det_compress {k : ℕ} {m : Type} [Fintype m] [DecidableEq m]
    (A : Matrix (Fin k) (Fin k) ℂ) (hA : IsUnit A.det)
    (B : Matrix (Fin k) (Fin 2) ℂ) (Cc : Matrix (Fin 2) (Fin k) ℂ) (D : Matrix (Fin 2) (Fin 2) ℂ)
    (w' w : Matrix (Fin 2) m ℂ) :
    ((fromBlocks (1 : Matrix (Fin k) (Fin k) ℂ) 0 0 w')ᴴ * fromBlocks A B Cc D *
      fromBlocks (1 : Matrix (Fin k) (Fin k) ℂ) 0 0 w).det =
      A.det * (w'ᴴ * (D - Cc * A⁻¹ * B) * w).det := by
  letI := Matrix.invertibleOfIsUnitDet A hA
  rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
  simp only [conjTranspose_one, conjTranspose_zero, Matrix.one_mul, Matrix.zero_mul, Matrix.mul_zero,
    add_zero, zero_add, Matrix.mul_one]
  rw [det_fromBlocks₁₁, invOf_eq_nonsing_inv]
  congr 2
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]

theorem submatrix_compress {α β : Type} [Fintype β] (H U U' : Matrix (Fin N) (Fin N) ℂ) (g : β → Fin N)
    (f f' : α → Fin N) (R R' : Matrix β α ℂ)
    (hU : ∀ y l, U l (f y) = ∑ z, if l = g z then R z y else 0)
    (hU' : ∀ y l, U' l (f' y) = ∑ z, if l = g z then R' z y else 0) :
    (Uᴴ * H * U').submatrix f f' = Rᴴ * H.submatrix g g * R' := by
  let E : Matrix (Fin N) β ℂ := Matrix.of fun l z => if l = g z then 1 else 0
  have h1 : U.submatrix id f = E * R := by
    ext l y
    simp [E, Matrix.mul_apply, hU]
  have h2 : U'.submatrix id f' = E * R' := by
    ext l y
    simp [E, Matrix.mul_apply, hU']
  have h3 : (Uᴴ * H * U').submatrix f f' = (U.submatrix id f)ᴴ * H * U'.submatrix id f' := by
    ext x y
    simp [Matrix.mul_apply]
  have h4 : Eᴴ * H * E = H.submatrix g g := by
    ext z z'
    simp [E, Matrix.mul_apply, conjTranspose_apply]
  rw [h3, h1, h2, conjTranspose_mul, ← h4]
  simp only [Matrix.mul_assoc]

theorem minor_pos {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.PosDef) (I : Finset (Fin N)) : 0 < minorIJ H I I := by
  rw [MinorCalc.minorIJ_eq_det H I I _ rfl rfl]
  exact (hH.submatrix (I.orderEmbOfFin rfl).injective).det_pos

def schurPlane (H : Matrix (Fin N) (Fin N) ℂ) (C : Finset (Fin N)) (ca cb : Fin N) : Matrix (Fin 2) (Fin 2) ℂ :=
  H.submatrix ![ca, cb] ![ca, cb] -
    H.submatrix ![ca, cb] (C.orderEmbOfFin rfl) * (H.submatrix (C.orderEmbOfFin rfl) (C.orderEmbOfFin rfl))⁻¹ *
      H.submatrix (C.orderEmbOfFin rfl) ![ca, cb]

theorem schurPlane_posDef {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.PosDef) (C : Finset (Fin N)) {ca cb : Fin N}
    (hC : ∀ c ∈ C, c < ca) (hab : ca < cb) : (schurPlane H C ca cb).PosDef := by
  have hinj : Function.Injective (Sum.elim (C.orderEmbOfFin rfl) ![ca, cb]) := by
    have hc : ∀ x, C.orderEmbOfFin rfl x < ca := fun x => hC _ (Finset.orderEmbOfFin_mem _ _ _)
    rintro (x | x) (y | y) h
    · simpa using h
    · exfalso
      fin_cases y
      · exact (hc x).ne h
      · exact ((hc x).trans hab).ne h
    · exfalso
      fin_cases x
      · exact (hc y).ne h.symm
      · exact ((hc y).trans hab).ne h.symm
    · fin_cases x <;> fin_cases y
      · rfl
      · exact absurd h hab.ne
      · exact absurd h hab.ne'
      · rfl
  have hM := hH.submatrix hinj
  have hA := hH.submatrix (C.orderEmbOfFin rfl).injective
  have e : H.submatrix (Sum.elim (C.orderEmbOfFin rfl) ![ca, cb]) (Sum.elim (C.orderEmbOfFin rfl) ![ca, cb]) =
      fromBlocks (H.submatrix (C.orderEmbOfFin rfl) (C.orderEmbOfFin rfl))
        (H.submatrix (C.orderEmbOfFin rfl) ![ca, cb]) (H.submatrix (C.orderEmbOfFin rfl) ![ca, cb])ᴴ
        (H.submatrix ![ca, cb] ![ca, cb]) := by
    ext (x | x) (y | y)
    · rfl
    · rfl
    · simp only [submatrix_apply, Sum.elim_inr, Sum.elim_inl, fromBlocks_apply₂₁, conjTranspose_apply]
      exact (hH.1.apply _ _).symm
    · rfl
  rw [e] at hM
  have := ReciprocityTheory.MultiplicativeHeights.sc_schur_posDef _ _ hA hM
  have e2 : (H.submatrix (C.orderEmbOfFin rfl) ![ca, cb])ᴴ = H.submatrix ![ca, cb] (C.orderEmbOfFin rfl) := by
    ext x y
    simp only [submatrix_apply, conjTranspose_apply]
    exact hH.1.apply _ _
  rw [e2] at this
  exact this

theorem minor_block (H U U' : Matrix (Fin N) (Fin N) ℂ) (C : Finset (Fin N)) (ca cb : Fin N) {m : ℕ}
    (hA : IsUnit (H.submatrix (C.orderEmbOfFin rfl) (C.orderEmbOfFin rfl)).det)
    (c c' : Fin m → Fin N) (I J : Finset (Fin N)) (hI : I.card = C.card + m) (hJ : J.card = C.card + m)
    (hCI : ∀ x ∈ C, x ∈ I) (hCJ : ∀ x ∈ C, x ∈ J) (hcI : ∀ y, c y ∈ I) (hcJ : ∀ y, c' y ∈ J)
    (sc : StrictMono c) (sc' : StrictMono c') (hc : ∀ x ∈ C, ∀ y, x < c y) (hc' : ∀ x ∈ C, ∀ y, x < c' y)
    (w w' : Matrix (Fin 2) (Fin m) ℂ)
    (hUe : ∀ x ∈ C, ∀ l, U l x = if l = x then 1 else 0) (hUe' : ∀ x ∈ C, ∀ l, U' l x = if l = x then 1 else 0)
    (hUc : ∀ y l, U l (c y) = (if l = ca then w 0 y else 0) + if l = cb then w 1 y else 0)
    (hUc' : ∀ y l, U' l (c' y) = (if l = ca then w' 0 y else 0) + if l = cb then w' 1 y else 0) :
    minorIJ (Uᴴ * H * U') I J =
      (H.submatrix (C.orderEmbOfFin rfl) (C.orderEmbOfFin rfl)).det * (wᴴ * schurPlane H C ca cb * w').det := by
  have mem : ∀ x, C.orderEmbOfFin rfl x ∈ C := fun x => Finset.orderEmbOfFin_mem _ _ _
  have key : ∀ (V : Matrix (Fin N) (Fin N) ℂ) (d : Fin m → Fin N) (v : Matrix (Fin 2) (Fin m) ℂ),
      (∀ x ∈ C, ∀ l, V l x = if l = x then 1 else 0) →
      (∀ y l, V l (d y) = (if l = ca then v 0 y else 0) + if l = cb then v 1 y else 0) →
      ∀ y l, V l (Sum.elim (C.orderEmbOfFin rfl) d y) =
        ∑ z, if l = Sum.elim (C.orderEmbOfFin rfl) ![ca, cb] z then
          (fromBlocks (1 : Matrix (Fin C.card) (Fin C.card) ℂ) 0 0 v) z y else 0 := by
    intro V d v h1 h2 y l
    have b11 : ∀ a x, (fromBlocks (1 : Matrix (Fin C.card) (Fin C.card) ℂ) 0 0 v) (Sum.inl a) (Sum.inl x) =
        if a = x then (1 : ℂ) else 0 := fun a x => by rw [fromBlocks_apply₁₁, Matrix.one_apply]
    have b12 : ∀ a x, (fromBlocks (1 : Matrix (Fin C.card) (Fin C.card) ℂ) 0 0 v) (Sum.inl a) (Sum.inr x) =
        (0 : ℂ) := fun a x => rfl
    have b21 : ∀ a x, (fromBlocks (1 : Matrix (Fin C.card) (Fin C.card) ℂ) 0 0 v) (Sum.inr a) (Sum.inl x) =
        (0 : ℂ) := fun a x => rfl
    have b22 : ∀ a x, (fromBlocks (1 : Matrix (Fin C.card) (Fin C.card) ℂ) 0 0 v) (Sum.inr a) (Sum.inr x) =
        v a x := fun a x => rfl
    rcases y with x | y
    · simp only [Sum.elim_inl, Sum.elim_inr, Fintype.sum_sum_type, b11, b21, ite_self, Finset.sum_const_zero,
        add_zero, Fin.sum_univ_two]
      rw [h1 _ (mem x), Finset.sum_eq_single x]
      · simp
      · intro b _ hb
        simp [hb]
      · simp
    · simp only [Sum.elim_inr, Sum.elim_inl, Fintype.sum_sum_type, b12, b22, ite_self, Finset.sum_const_zero,
        zero_add, Fin.sum_univ_two]
      rw [h2]
      rfl
  rw [minorIJ_eq_submatrix _ I J (Sum.elim (C.orderEmbOfFin rfl) c) (Sum.elim (C.orderEmbOfFin rfl) c') hI hJ
      (by rintro (x | x); exacts [hCI _ (mem x), hcI x]) (by rintro (x | x); exacts [hCJ _ (mem x), hcJ x])
      (strictMono_elim _ _ (C.orderEmbOfFin rfl).strictMono sc fun x y => hc _ (mem x) y)
      (strictMono_elim _ _ (C.orderEmbOfFin rfl).strictMono sc' fun x y => hc' _ (mem x) y),
    submatrix_compress H U U' (Sum.elim (C.orderEmbOfFin rfl) ![ca, cb]) _ _ _ _ (key U c w hUe hUc)
      (key U' c' w' hUe' hUc')]
  have e : H.submatrix (Sum.elim (C.orderEmbOfFin rfl) ![ca, cb]) (Sum.elim (C.orderEmbOfFin rfl) ![ca, cb]) =
      fromBlocks (H.submatrix (C.orderEmbOfFin rfl) (C.orderEmbOfFin rfl))
        (H.submatrix (C.orderEmbOfFin rfl) ![ca, cb]) (H.submatrix ![ca, cb] (C.orderEmbOfFin rfl))
        (H.submatrix ![ca, cb] ![ca, cb]) := by
    ext (x | x) (y | y) <;> rfl
  rw [e]
  exact det_compress _ hA _ _ _ _ _

theorem elem_apply (ca cb : Fin N) (t : ℂ) (l y : Fin N) :
    (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) l y =
      (if l = y then 1 else 0) + if cb = l ∧ ca = y then t else 0 := by
  rw [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]

def selCol (r : Fin 2) : Matrix (Fin 2) (Fin 1) ℂ := Matrix.of fun x _ => if x = r then 1 else 0

theorem det_sel (S : Matrix (Fin 2) (Fin 2) ℂ) (r s : Fin 2) : ((selCol r)ᴴ * S * selCol s).det = S r s := by
  rw [det_fin_one]
  fin_cases r <;> fin_cases s <;> simp [Matrix.mul_apply, selCol, Fin.sum_univ_two, conjTranspose_apply]

def lineCol (t : ℂ) : Matrix (Fin 2) (Fin 1) ℂ := Matrix.of fun x _ => ![1, t] x

theorem det_line (S : Matrix (Fin 2) (Fin 2) ℂ) (t : ℂ) :
    ((lineCol t)ᴴ * S * lineCol t).det = herm2 S ![1, t] ![1, t] := by
  rw [det_fin_one]
  simp [Matrix.mul_apply, lineCol, Fin.sum_univ_two, conjTranspose_apply, herm2, dotProduct, mulVec]
  ring

theorem det_plane (S : Matrix (Fin 2) (Fin 2) ℂ) (t : ℂ) :
    ((!![1, 0; t, 1] : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * S * !![1, 0; t, 1]).det = S.det := by
  rw [det_mul, det_mul, det_conjTranspose, det_fin_two_of]
  simp

theorem core (H : Matrix (Fin N) (Fin N) ℂ) (hH : H.PosDef) (C : Finset (Fin N)) (ca cb : Fin N)
    (hC : ∀ c ∈ C, c < ca) (hab : ca < cb) :
    (∀ r s : Fin 2, schurPlane H C ca cb r s = minorIJ H (insert (![ca, cb] r) C) (insert (![ca, cb] s) C) /
      minorIJ H C C) ∧
    ∀ t : ℂ,
      minorIJ ((1 + Matrix.single cb ca t)ᴴ * H * (1 + Matrix.single cb ca t)) C C = minorIJ H C C ∧
      minorIJ ((1 + Matrix.single cb ca t)ᴴ * H * (1 + Matrix.single cb ca t)) (insert ca C) (insert ca C) =
        minorIJ H C C * herm2 (schurPlane H C ca cb) ![1, t] ![1, t] ∧
      minorIJ ((1 + Matrix.single cb ca t)ᴴ * H * (1 + Matrix.single cb ca t)) (insert cb (insert ca C))
        (insert cb (insert ca C)) = minorIJ H C C * (schurPlane H C ca cb).det := by
  have hpos : 0 < (H.submatrix (C.orderEmbOfFin rfl) (C.orderEmbOfFin rfl)).det :=
    (hH.submatrix (C.orderEmbOfFin rfl).injective).det_pos
  have hA : IsUnit (H.submatrix (C.orderEmbOfFin rfl) (C.orderEmbOfFin rfl)).det := hpos.ne'.isUnit
  have hmin : minorIJ H C C = (H.submatrix (C.orderEmbOfFin rfl) (C.orderEmbOfFin rfl)).det :=
    MinorCalc.minorIJ_eq_det H C C _ rfl rfl
  have hcb : ∀ c ∈ C, c < cb := fun c hc => (hC c hc).trans hab
  have hcr : ∀ r : Fin 2, ∀ c ∈ C, c < ![ca, cb] r := fun r c hc => by
    fin_cases r
    · exact hC c hc
    · exact hcb c hc
  have hnot : ∀ r : Fin 2, ![ca, cb] r ∉ C := fun r h => lt_irrefl _ (hcr r _ h)
  have hcard : ∀ r : Fin 2, (insert (![ca, cb] r) C).card = C.card + 1 := fun r =>
    Finset.card_insert_of_notMem (hnot r)
  have hca : ca ∉ C := hnot 0
  have hcb' : cb ∉ insert ca C := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨hab.ne', hnot 1⟩
  constructor
  · intro r s
    have h := minor_block H 1 1 C ca cb hA (fun _ : Fin 1 => ![ca, cb] r) (fun _ => ![ca, cb] s)
      (insert (![ca, cb] r) C) (insert (![ca, cb] s) C) (hcard r) (hcard s)
      (fun x hx => Finset.mem_insert_of_mem hx) (fun x hx => Finset.mem_insert_of_mem hx)
      (fun _ => Finset.mem_insert_self _ _) (fun _ => Finset.mem_insert_self _ _)
      (Subsingleton.strictMono _) (Subsingleton.strictMono _) (fun x hx _ => hcr r x hx)
      (fun x hx _ => hcr s x hx) (selCol r) (selCol s)
      (fun x _ l => Matrix.one_apply) (fun x _ l => Matrix.one_apply)
      (fun _ l => by fin_cases r <;> (simp [selCol, Matrix.one_apply] <;> congr))
      (fun _ l => by fin_cases s <;> (simp [selCol, Matrix.one_apply] <;> congr))
    rw [det_sel] at h
    simp only [conjTranspose_one, Matrix.one_mul, Matrix.mul_one] at h
    rw [h, hmin, mul_div_cancel_left₀ _ hpos.ne']
  · intro t
    have hE : ∀ x ∈ C, ∀ l, (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) l x = if l = x then 1 else 0 :=
      fun x hx l => by
        have : ca ≠ x := fun e => hca (e ▸ hx)
        rw [elem_apply]
        simp [this]
    have hc0 : ∀ l, (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) l ca =
        (if l = ca then 1 else 0) + if l = cb then t else 0 := fun l => by
      rw [elem_apply]
      simp [eq_comm]
    have hc1 : ∀ l, (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) l cb = if l = cb then 1 else 0 := fun l => by
      rw [elem_apply]
      simp [hab.ne]
    refine ⟨?_, ?_, ?_⟩
    · have h := minor_block H _ _ C ca cb hA (m := 0) Fin.elim0 Fin.elim0 C C rfl rfl (fun _ h => h) (fun _ h => h)
        (fun y => y.elim0) (fun y => y.elim0) (fun y => y.elim0) (fun y => y.elim0)
        (fun _ _ y => y.elim0) (fun _ _ y => y.elim0) 0 0 hE hE (fun y => y.elim0) (fun y => y.elim0)
      rw [h, hmin, Matrix.det_isEmpty (n := Fin 0), mul_one]
    · have h := minor_block H _ _ C ca cb hA (fun _ : Fin 1 => ca) (fun _ => ca) (insert ca C) (insert ca C)
        (hcard 0) (hcard 0) (fun x hx => Finset.mem_insert_of_mem hx) (fun x hx => Finset.mem_insert_of_mem hx)
        (fun _ => Finset.mem_insert_self _ _) (fun _ => Finset.mem_insert_self _ _)
        (Subsingleton.strictMono _) (Subsingleton.strictMono _) (fun x hx _ => hC x hx) (fun x hx _ => hC x hx)
        (lineCol t) (lineCol t) hE hE (fun _ l => by rw [hc0]; simp [lineCol])
        (fun _ l => by rw [hc0]; simp [lineCol])
      rw [h, hmin, det_line]
    · have hcard2 : (insert cb (insert ca C)).card = C.card + 2 := by
        rw [Finset.card_insert_of_notMem hcb', Finset.card_insert_of_notMem hca]
      have hm : StrictMono ![ca, cb] := by
        intro x y hxy
        fin_cases x <;> fin_cases y
        · exact absurd hxy (lt_irrefl _)
        · exact hab
        · exact absurd hxy (by decide)
        · exact absurd hxy (lt_irrefl _)
      have hin : ∀ y, ![ca, cb] y ∈ insert cb (insert ca C) := fun y => by
        fin_cases y <;> simp
      have hu : ∀ y l, (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) l (![ca, cb] y) =
          (if l = ca then (!![1, 0; t, 1] : Matrix (Fin 2) (Fin 2) ℂ) 0 y else 0) +
            if l = cb then (!![1, 0; t, 1] : Matrix (Fin 2) (Fin 2) ℂ) 1 y else 0 := fun y l => by
        fin_cases y
        · simpa using hc0 l
        · simpa using hc1 l
      have h := minor_block H _ _ C ca cb hA ![ca, cb] ![ca, cb] (insert cb (insert ca C)) (insert cb (insert ca C))
        hcard2 hcard2 (fun x hx => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx))
        (fun x hx => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx)) hin hin hm hm
        (fun x hx y => hcr y x hx) (fun x hx y => hcr y x hx) !![1, 0; t, 1] !![1, 0; t, 1] hE hE hu hu
      rw [h, hmin, det_plane]

theorem minor_empty (X : Matrix (Fin N) (Fin N) ℂ) : minorIJ X ∅ ∅ = 1 := by
  rw [MinorCalc.minorIJ_eq_det X ∅ ∅ 0 rfl rfl, Matrix.det_isEmpty]

theorem minor_conjTranspose (h : Matrix (Fin N) (Fin N) ℂ) (I : Finset (Fin N)) :
    minorIJ hᴴ I I = star (minorIJ h I I) := by
  rw [MinorCalc.minorIJ_eq_det hᴴ I I _ rfl rfl, MinorCalc.minorIJ_eq_det h I I _ rfl rfl,
    ← det_conjTranspose, conjTranspose_submatrix]

theorem minor_gram {G h : Matrix (Fin N) (Fin N) ℂ} {I : Finset (Fin N)} (hG : ∀ k c, c ∈ I → k ∉ I → G k c = 0)
    (hh : ∀ k c, c ∈ I → k ∉ I → h k c = 0) :
    minorIJ (hᴴ * G * h) I I = star (minorIJ h I I) * minorIJ G I I * minorIJ h I I := by
  rw [MinorCalc.minorIJ_mul_of_support _ h I I hh, MinorCalc.minorIJ_mul_of_support _ G I I hG,
    minor_conjTranspose]

theorem re_mul_of_pos {z : ℂ} (hz : 0 < z) (w : ℂ) : (z * w).re = z.re * w.re := by
  have him : z.im = 0 := by
    have := (Complex.pos_iff.mp hz).2
    linarith
  rw [Complex.mul_re, him, zero_mul, sub_zero]

theorem re_pos {z : ℂ} (hz : 0 < z) : 0 < z.re := (Complex.pos_iff.mp hz).1

theorem log_gram {p m : ℂ} (hp : 0 < p) (hq : 0 < star m * p * m) :
    (1 / 2) * Real.log p.re + Real.log ‖m‖ = (1 / 2) * Real.log (star m * p * m).re := by
  have hm : m ≠ 0 := by
    rintro rfl
    simp at hq
  have e : star m * p * m = ((‖m‖ ^ 2 : ℝ) : ℂ) * p := by
    have e0 : star m * m = ((‖m‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      exact Complex.conj_mul' m
    rw [← e0]
    ring
  have hn : ‖m‖ ≠ 0 := norm_ne_zero_iff.2 hm
  rw [e, Complex.re_ofReal_mul, Real.log_mul (pow_ne_zero 2 hn) (re_pos hp).ne', Real.log_pow]
  push_cast
  ring

theorem sum_xi (T : Fin N → ℝ) (a b : Fin N) (hb : (b : ℕ) = a + 1) (T0 : ℝ)
    (h0 : ∀ i : Fin N, (i : ℕ) + 1 = a → T i = T0) (hz : (a : ℕ) = 0 → T0 = 0) :
    ∑ i : Fin N, (xiCoef () a ((), i) : ℝ) * T i = T0 + T b - 2 * T a := by
  have e : ∀ i : Fin N, (xiCoef () a ((), i) : ℝ) * T i =
      (if (i : ℕ) + 1 = a then T0 else 0) + (if i = b then T b else 0) - (if i = a then 2 * T a else 0) := by
    intro i
    have e1 : ((i : ℕ) = a + 1) ↔ i = b := by rw [Fin.ext_iff, hb]
    have hcoef : (xiCoef () a ((), i) : ℝ) =
        (if (i : ℕ) + 1 = a then 1 else 0) + (if i = b then 1 else 0) - (if i = a then 2 else 0) := by
      simp only [xiCoef, if_true, e1]
      push_cast
      rfl
    rw [hcoef]
    by_cases c1 : (i : ℕ) + 1 = a
    · have n2 : i ≠ b := fun e => by
        have := congrArg Fin.val e
        omega
      have n3 : i ≠ a := fun e => by
        have := congrArg Fin.val e
        omega
      simp [c1, n2, n3, h0 i c1]
    · by_cases c2 : i = b
      · have n3 : i ≠ a := fun e => by
          have := congrArg Fin.val e
          have := congrArg Fin.val c2
          omega
        simp only [if_neg c1, if_pos c2, if_neg n3]
        rw [c2]
        ring
      · by_cases c3 : i = a
        · simp only [if_neg c1, if_neg c2, if_pos c3]
          rw [c3]
          ring
        · simp only [if_neg c1, if_neg c2, if_neg c3]
          ring
  simp only [e, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  congr 2
  by_cases ha : (a : ℕ) = 0
  · rw [hz ha]
    simp
  · rw [Finset.sum_eq_single (⟨(a : ℕ) - 1, by have := a.2; omega⟩ : Fin N)]
    · rw [if_pos (by simp; omega)]
    · intro i _ hi
      rw [if_neg]
      intro h
      exact hi (Fin.ext (by simp; omega))
    · simp

theorem steps {N j : ℕ} {a b ca cb : Fin N} (hj : j ≤ N) (hb : (b : ℕ) = a + 1)
    (hcase : (b : ℕ) < j ∨ j ≤ (a : ℕ)) (hca : (ca : ℕ) = lastCol N j a) (hcb : (cb : ℕ) = ca + 1) :
    ∃ lo : ℕ, (∀ c : Fin N, c ∈ stepCols N j a ↔ lo ≤ c ∧ (c : ℕ) ≤ ca) ∧
      (∀ c : Fin N, c ∈ stepCols N j b ↔ lo ≤ c ∧ (c : ℕ) ≤ cb) ∧
      (∀ i : Fin N, (i : ℕ) + 1 = a → (i : ℕ) + 1 ≠ j → ∀ c : Fin N, c ∈ stepCols N j i ↔ lo ≤ c ∧ (c : ℕ) < ca) ∧
      ((a : ℕ) = 0 ∨ (a : ℕ) = j → (ca : ℕ) = lo) ∧ lo ≤ ca := by
  have h1 := a.2
  have h2 := b.2
  have h3 := cb.2
  unfold lastCol at hca
  rcases hcase with h | h
  · rw [if_pos (by omega)] at hca
    refine ⟨N - j, fun c => ?_, fun c => ?_, fun i hi hij c => ?_, fun _ => ?_, by omega⟩
    · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [if_pos (by omega)]
      omega
    · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [if_pos (by omega)]
      omega
    · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [if_pos (by omega)]
      omega
    · omega
  · rw [if_neg (by omega)] at hca
    refine ⟨0, fun c => ?_, fun c => ?_, fun i hi hij c => ?_, fun _ => ?_, by omega⟩
    · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [if_neg (by omega)]
      omega
    · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [if_neg (by omega)]
      omega
    · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [if_neg (by omega)]
      omega
    · omega

end GlobalTheory.CompanionTheory.Ar.PB.SchurCalc

namespace GlobalTheory.CompanionTheory.Ar.PB

open SchurCalc in

theorem norm_three_steps : ∀ (N j : ℕ) (a b ca cb : Fin N) (G h : Matrix (Fin N) (Fin N) ℂ), j ≤ N → (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → IsBlockDiag j G → G.PosDef → IsBlockDiag j h → h.det ≠ 0 → ∃ G₂ : Matrix (Fin 2) (Fin 2) ℂ, G₂.PosDef ∧ (∀ r s : Fin 2, G₂ r s = minorIJ (hᴴ * G * h) (insert (![ca, cb] r) ((stepCols N j a).erase ca)) (insert (![ca, cb] s) ((stepCols N j a).erase ca)) / minorIJ (hᴴ * G * h) ((stepCols N j a).erase ca) ((stepCols N j a).erase ca)) ∧ ∀ t : ℂ, (∑ i : Fin N, (xiCoef () a ((), i) : ℝ) * (blockPot j i G (h * (1 + Matrix.single cb ca t)) + if IsProperStep N j i then 0 else Real.log ‖if (i : ℕ) + 1 = j then (if (a : ℕ) < j then minorIJ h (wIdx N j) (wIdx N j) else 1) else minorIJ h (omIdx N j) (omIdx N j)‖)) = xiPot G₂ t := by
  intro N j a b ca cb G h hj hb hcase hca hcb hG hGp hh hdet
  have ha2 := a.2
  have hb2 := b.2
  obtain ⟨lo, m1, m2, m3, m4, m5⟩ := steps hj hb hcase hca hcb
  obtain ⟨C, hCdef⟩ : ∃ C, C = (stepCols N j a).erase ca := ⟨_, rfl⟩
  rw [← hCdef]
  have hCm : ∀ c : Fin N, c ∈ C ↔ lo ≤ c ∧ (c : ℕ) < ca := fun c => by
    rw [hCdef, Finset.mem_erase, m1, Ne, Fin.ext_iff]
    omega
  have hSa : stepCols N j a = insert ca C := by
    rw [hCdef]
    exact (Finset.insert_erase ((m1 ca).2 ⟨m5, le_rfl⟩)).symm
  have hSb : stepCols N j b = insert cb (insert ca C) := by
    ext c
    rw [m2, Finset.mem_insert, Finset.mem_insert, hCm, Fin.ext_iff, Fin.ext_iff]
    omega
  have hC : ∀ c ∈ C, c < ca := fun c hc => Fin.lt_def.2 ((hCm c).1 hc).2
  have hab : ca < cb := Fin.lt_def.2 (by omega)
  obtain ⟨H, hHdef⟩ : ∃ H, H = hᴴ * G * h := ⟨_, rfl⟩
  rw [← hHdef]
  have hH : H.PosDef := by
    rw [hHdef]
    exact hGp.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det h).2 hdet.isUnit))
  obtain ⟨e1, e2⟩ := core H hH C ca cb hC hab
  have hS := schurPlane_posDef hH C hC hab
  refine ⟨schurPlane H C ca cb, hS, e1, fun t => ?_⟩
  obtain ⟨f0, f1, f2⟩ := e2 t
  obtain ⟨-, -, z2⟩ := e2 0
  have hU : (h * (1 + Matrix.single cb ca t))ᴴ * G * (h * (1 + Matrix.single cb ca t)) =
      (1 + Matrix.single cb ca t)ᴴ * H * (1 + Matrix.single cb ca t) := by
    rw [hHdef]
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  have z2' : minorIJ H (insert cb (insert ca C)) (insert cb (insert ca C)) = minorIJ H C C * (schurPlane H C ca cb).det := by
    simpa using z2
  have D0pos : 0 < minorIJ H C C := minor_pos hH C
  have hdS : 0 < (schurPlane H C ca cb).det := hS.det_pos
  have hherm : 0 < herm2 (schurPlane H C ca cb) ![1, t] ![1, t] :=
    hS.dotProduct_mulVec_pos (fun e => by simpa using congrFun e 0)
  obtain ⟨g, hgdef⟩ : ∃ g : ℂ, g = if j ≤ (a : ℕ) then minorIJ G (wIdx N j) (wIdx N j) else 1 := ⟨_, rfl⟩
  have hmw : 0 < minorIJ G (wIdx N j) (wIdx N j) := minor_pos hGp _
  have hmo : 0 < minorIJ G (omIdx N j) (omIdx N j) := minor_pos hGp _
  have gpos : 0 < g := by
    rw [hgdef]
    split_ifs
    · exact hmw
    · exact one_pos
  have hdf : ∀ i : Fin N, (j ≤ (i : ℕ) + 1 ↔ j ≤ (a : ℕ)) → (i : ℕ) + 1 ≠ N → detFac j i G = g := fun i h1 h2 => by
    unfold detFac
    rw [if_neg h2, mul_one, hgdef]
    simp only [h1]
  let T : Fin N → ℝ := fun i => blockPot j i G (h * (1 + Matrix.single cb ca t)) + if IsProperStep N j i then 0 else
    Real.log ‖if (i : ℕ) + 1 = j then (if (a : ℕ) < j then minorIJ h (wIdx N j) (wIdx N j) else 1)
      else minorIJ h (omIdx N j) (omIdx N j)‖
  have hprop : ∀ i : Fin N, IsProperStep N j i → detFac j i G = g →
      T i = (1 / 2) * Real.log g.re + (1 / 2) * Real.log
        (minorIJ ((1 + Matrix.single cb ca t)ᴴ * H * (1 + Matrix.single cb ca t)) (stepCols N j i) (stepCols N j i)).re := by
    intro i hp hd
    show blockPot j i G (h * (1 + Matrix.single cb ca t)) + _ = _
    rw [if_pos hp, add_zero]
    unfold blockPot
    rw [if_pos hp, hd, hU]
  have Ta : T a = (1 / 2) * Real.log g.re + (1 / 2) * Real.log (minorIJ H C C * herm2 (schurPlane H C ca cb) ![1, t] ![1, t]).re := by
    have hp : IsProperStep N j a := ⟨by omega, by omega⟩
    rw [hprop a hp (hdf a (by omega) hp.2), hSa, f1]
  have Tb : T b = (1 / 2) * Real.log g.re + (1 / 2) * Real.log (minorIJ H C C * (schurPlane H C ca cb).det).re := by
    by_cases hp : IsProperStep N j b
    · rw [hprop b hp (hdf b (by have := hp.1; omega) hp.2), hSb, f2]
    · show blockPot j b G (h * (1 + Matrix.single cb ca t)) + _ = _
      rw [if_neg hp]
      unfold blockPot
      rw [if_neg hp, add_zero, ← z2', ← hSb]
      rcases hcase with hW | hO
      · have hbj : (b : ℕ) + 1 = j := by
          by_contra hne
          exact hp ⟨hne, by omega⟩
        have hSw : stepCols N j b = wIdx N j := by
          ext c
          have := c.2
          simp only [stepCols, wIdx, Finset.mem_filter, Finset.mem_univ, true_and]
          rw [if_pos (by omega)]
          omega
        have hg1 : g = 1 := by
          rw [hgdef, if_neg (by omega)]
        have hd : detFac j b G = minorIJ G (wIdx N j) (wIdx N j) := by
          unfold detFac
          rw [if_pos (by omega)]
          split_ifs with hbN
          · have : omIdx N j = ∅ := by
              ext c
              simp [omIdx]
              omega
            rw [this, minor_empty, mul_one]
          · rw [mul_one]
        have hq := minor_pos hH (wIdx N j)
        rw [hHdef, minor_gram (MinorCalc.support_wIdx hG) (MinorCalc.support_wIdx hh)] at hq
        rw [if_pos hbj, if_pos (by omega), hd, hSw, hHdef, minor_gram (MinorCalc.support_wIdx hG)
          (MinorCalc.support_wIdx hh), log_gram hmw hq, hg1]
        simp
      · have hbN : (b : ℕ) + 1 = N := by
          by_contra hne
          exact hp ⟨by omega, hne⟩
        have hSo : stepCols N j b = omIdx N j := by
          ext c
          have := c.2
          simp only [stepCols, omIdx, Finset.mem_filter, Finset.mem_univ, true_and]
          rw [if_neg (by omega)]
          omega
        have hg1 : g = minorIJ G (wIdx N j) (wIdx N j) := by
          rw [hgdef, if_pos hO]
        have hd : detFac j b G = minorIJ G (wIdx N j) (wIdx N j) * minorIJ G (omIdx N j) (omIdx N j) := by
          unfold detFac
          rw [if_pos (by omega), if_pos hbN]
        have hq := minor_pos hH (omIdx N j)
        rw [hHdef, minor_gram (MinorCalc.support_omIdx hG) (MinorCalc.support_omIdx hh)] at hq
        rw [if_neg (by omega), hd, hSo, hHdef, minor_gram (MinorCalc.support_omIdx hG)
          (MinorCalc.support_omIdx hh), hg1, re_mul_of_pos hmw, Real.log_mul (re_pos hmw).ne' (re_pos hmo).ne',
          ← log_gram hmo hq]
        ring
  have hz1 : (a : ℕ) = 0 ∨ (a : ℕ) = j → minorIJ H C C = 1 := fun hh' => by
    have : C = ∅ := by
      ext c
      rw [hCm]
      have := m4 hh'
      simp
      omega
    rw [this, minor_empty]
  refine (sum_xi T a b hb ((1 / 2) * Real.log g.re + (1 / 2) * Real.log (minorIJ H C C).re) ?_ ?_).trans ?_
  · intro i hi
    by_cases hp : IsProperStep N j i
    · have hC' : stepCols N j i = C := by
        ext c
        rw [m3 i hi hp.1, hCm]
      rw [hprop i hp (hdf i (by omega) hp.2), hC', f0]
    · have hij : (i : ℕ) + 1 = j := by
        by_contra hne
        exact hp ⟨hne, by omega⟩
      show blockPot j i G (h * (1 + Matrix.single cb ca t)) + _ = _
      rw [if_neg hp, if_pos hij, if_neg (by omega)]
      unfold blockPot
      rw [if_neg hp, hdf i (by omega) (by omega), hz1 (Or.inr (by omega))]
      simp
  · intro h0
    have hg1 : g = 1 := by
      rw [hgdef]
      split_ifs with hjo
      · have : wIdx N j = ∅ := by
          ext c
          have := c.2
          simp [wIdx]
          omega
        rw [this, minor_empty]
      · rfl
    rw [hg1, hz1 (Or.inl h0)]
    simp
  · rw [Ta, Tb, re_mul_of_pos D0pos, re_mul_of_pos D0pos, Real.log_mul (re_pos D0pos).ne' (re_pos hdS).ne',
      Real.log_mul (re_pos D0pos).ne' (re_pos hherm).ne']
    unfold xiPot
    ring

end GlobalTheory.CompanionTheory.Ar.PB
