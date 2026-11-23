import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompGvec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CauchyBinetPluckerAndCellCoordinates
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.MulConjTransposeEqOneOfOrthonormal

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv plE)
open GlobalTheory.ProjSpace (pt)

namespace GlobalTheory.GrCl.CellLin

variable {R : Type} [CommRing R] {m a k b N : ℕ}

def pmat (hk : k ≤ m) (w : GPm m a b) : Matrix (Fin k) (Fin m) (MvPolynomial (GVar m a k b) R) :=
  fun l i => gcell MvPolynomial.X (w.1⁻¹ i) (Fin.castLE hk l)

theorem gvec_apply (hk : k ≤ m) (c : Fin m → Fin (N + 1) → R) (w : GPm m a b) (l : Fin k) (r : Fin (N + 1)) :
    gvec (fun l => (MvPolynomial.C : R →+* MvPolynomial (GVar m a k b) R) ∘ c l) w
        (MvPolynomial.X : GVar m a k b → MvPolynomial (GVar m a k b) R) (Fin.castLE hk l) r =
      ∑ i, pmat hk w l i * MvPolynomial.C (c i r) := by
  simp only [gvec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply, pmat]
  refine ((Equiv.sum_comp w.1 fun i =>
    gcell MvPolynomial.X (w.1⁻¹ i) (Fin.castLE hk l) * MvPolynomial.C (c i r)).symm.trans ?_).symm
  simp

theorem gxi_eq (hk : k ≤ m) (c : Fin m → Fin (N + 1) → R) (w : GPm m a b) (q : Fin (plN N k + 1)) :
    gxi a b hk c w q = ∑ S : Set.powersetCard (Fin m) k, ((pmat hk w).submatrix id (subsetEnum S)).det *
      MvPolynomial.C (plk c (subsetEnum S) q) := by
  let B : Matrix (Fin m) (Fin k) (MvPolynomial (GVar m a k b) R) :=
    Matrix.of fun i l' => MvPolynomial.C (c i (plE N k q l'))
  have h : (Matrix.of fun l l' => gvec (fun l => (MvPolynomial.C : R →+* MvPolynomial (GVar m a k b) R) ∘ c l) w
        (MvPolynomial.X : GVar m a k b → MvPolynomial (GVar m a k b) R) (Fin.castLE hk l) (plE N k q l')) =
      (pmat (R := R) hk w * B : Matrix (Fin k) (Fin k) (MvPolynomial (GVar m a k b) R)) := by
    ext1 l l'
    rw [Matrix.mul_apply, Matrix.of_apply, gvec_apply]
    rfl
  unfold gxi plk
  rw [h, det_mul_eq_sum_minors]
  refine Finset.sum_congr rfl fun S _ => ?_
  congr 1
  rw [RingHom.map_det]
  congr 1

theorem sum_gell (hk : k ≤ m) {D c : Fin m → Fin (N + 1) → R} (h : LeftInv D c) (w v : GPm m a b) :
    ∑ q, MvPolynomial.C (gell a b hk D v q) * gxi a b hk c w q =
      ((pmat hk w).submatrix id (v.1 ∘ Fin.castLE hk)).det := by
  have h1 : ∀ q, (MvPolynomial.C : R →+* MvPolynomial (GVar m a k b) R) (gell a b hk D v q) =
      lform (fun i => (MvPolynomial.C : R →+* MvPolynomial (GVar m a k b) R) ∘ D i) (v.1 ∘ Fin.castLE hk) q := by
    intro q
    simp [gell, lform, map_prod]
  simp only [h1, gxi]
  rw [GlobalTheory.FlagEmb.CauchyBinet.lform_plk]
  congr 1
  ext1 l l'
  simp only [Matrix.of_apply, Matrix.submatrix_apply, id, gvec_apply, Function.comp_apply]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  have h2 : ∀ i, ∑ r, (MvPolynomial.C : R →+* MvPolynomial (GVar m a k b) R) (D (v.1 (Fin.castLE hk l')) r) *
      (pmat hk w l i * MvPolynomial.C (c i r)) = pmat hk w l i *
        MvPolynomial.C (∑ r, D (v.1 (Fin.castLE hk l')) r * c i r) := by
    intro i
    simp only [map_sum, map_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    ring
  simp only [h2, h _ _]
  rw [Finset.sum_eq_single (v.1 (Fin.castLE hk l'))]
  · simp
  · intro i _ hi
    rw [if_neg (Ne.symm hi)]
    simp
  · simp

theorem exists_perm (hk : k ≤ m) (hkb : k ≤ b) (hak : a ≤ k) (f : Fin k → Fin m) (hf : Function.Injective f)
    (h1 : ∀ l : Fin k, (l : ℕ) < a → (f l : ℕ) = l) (h2 : ∀ l, (f l : ℕ) < b) :
    ∃ v : GPm m a b, ∀ l, v.1 (Fin.castLE hk l) = f l := by
  classical
  let p : Fin m → Prop := fun i => (i : ℕ) < k ∨ b ≤ (i : ℕ)
  let g : {i // p i} → Fin m := fun i => if h : (i.1 : ℕ) < k then f ⟨i.1, h⟩ else i.1
  have hg : Function.Injective g := by
    rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
    simp only [g] at hij
    split_ifs at hij with h3 h4 h4
    · have := hf hij
      simp only [Fin.mk.injEq] at this
      exact Subtype.ext (Fin.ext this)
    · have h5 := h2 ⟨i, h3⟩
      rw [hij] at h5
      have := hj.resolve_left h4
      omega
    · have h5 := h2 ⟨j, h4⟩
      rw [← hij] at h5
      have := hi.resolve_left h3
      omega
    · exact Subtype.ext hij
  let e : {i // p i} ≃ {y // y ∈ Set.range g} := Equiv.ofInjective g hg
  have hv : ∀ i (hi : p i), e.extendSubtype i = g ⟨i, hi⟩ := fun i hi => by
    rw [Equiv.extendSubtype_apply_of_mem e i hi]
    rfl
  refine ⟨⟨e.extendSubtype, fun i hi => ?_⟩, fun l => ?_⟩
  · rcases hi with hi | hi
    · have hik : (i : ℕ) < k := by omega
      rw [hv i (Or.inl hik)]
      simp only [g, dif_pos hik]
      exact Fin.ext (h1 ⟨i, hik⟩ hi)
    · have hik : ¬ (i : ℕ) < k := by omega
      rw [hv i (Or.inr hi)]
      simp only [g, dif_neg hik]
  · have hl : ((Fin.castLE hk l : Fin m) : ℕ) < k := l.2
    change e.extendSubtype (Fin.castLE hk l) = f l
    rw [hv _ (Or.inl hl)]
    simp only [g, dif_pos hl]
    rfl

theorem enum_init (hk : k ≤ m) (hak : a ≤ k) (f : Fin k → Fin m) (hf : StrictMono f)
    (h : ∀ i : Fin m, (i : ℕ) < a → i ∈ Set.range f) (n : ℕ) : ∀ (hn : n < k), n < a → (f ⟨n, hn⟩ : ℕ) = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hna
    obtain ⟨l', hl'⟩ := h ⟨n, by omega⟩ hna
    have h1 : ¬ (l' : ℕ) < n := fun hlt => by
      have := ih l' hlt l'.2 (by omega)
      have h3 : f ⟨l', l'.2⟩ = f l' := rfl
      rw [h3, hl'] at this
      simp only at this
      omega
    rcases Nat.lt_or_ge n l' with h2 | h2
    · have h3 : f ⟨n, hn⟩ < f l' := hf (by simpa [Fin.lt_def] using h2)
      rw [hl'] at h3
      have h4 : (f ⟨n, hn⟩ : ℕ) < n := h3
      have h5 := hf.injective (Fin.ext (ih _ h4 (by omega) (by omega)))
      simp only [Fin.mk.injEq] at h5
      omega
    · have : (⟨n, hn⟩ : Fin k) = l' := Fin.ext (by simp; omega)
      rw [this, hl']

theorem det_eq_zero_of_lt (hk : k ≤ m) (hak : a ≤ k) (w : GPm m a b) (f : Fin k → Fin m) (i : Fin m) (hi : (i : ℕ) < a)
    (hf : i ∉ Set.range f) : ((pmat (R := R) hk w).submatrix id f).det = 0 := by
  refine Matrix.det_eq_zero_of_row_eq_zero ⟨i, by omega⟩ fun l' => ?_
  simp only [Matrix.submatrix_apply, id, pmat, gcell]
  rw [dif_neg (fun h => by have := h.1; simp at this; omega), if_neg]
  intro he
  apply hf
  refine ⟨l', ?_⟩
  have h1 : Fin.castLE hk (⟨i, by omega⟩ : Fin k) = i := rfl
  rw [h1, Equiv.Perm.inv_eq_iff_eq, w.2 i (Or.inl hi)] at he
  exact he

theorem det_eq_zero_of_ge (hk : k ≤ m) (hkb : k ≤ b) (w : GPm m a b) (f : Fin k → Fin m) (l' : Fin k)
    (hi : b ≤ (f l' : ℕ)) : ((pmat (R := R) hk w).submatrix id f).det = 0 := by
  refine Matrix.det_eq_zero_of_column_eq_zero l' fun l => ?_
  have h1 : w.1⁻¹ (f l') = f l' := by
    rw [Equiv.Perm.inv_eq_iff_eq, w.2 _ (Or.inr hi)]
  simp only [Matrix.submatrix_apply, id, pmat, gcell, h1]
  rw [dif_neg (fun h => by have := h.2.2.2; omega), if_neg]
  intro he
  have h2 := congrArg Fin.val he
  have h3 := l.2
  simp only [Fin.val_castLE] at h2
  omega

theorem main : ∀ (R : Type) [CommRing R] (m a k b N : ℕ) (hk : k ≤ m) (D c : Fin m → Fin (N + 1) → R), a ≤ k → k ≤ b → LeftInv D c → ∀ q, ∃ (T : Type) (_ : Fintype T) (jj : T → GPm m a b) (e : T → R), ∀ w' : GPm m a b, gxi a b hk c w' q = ∑ t, (MvPolynomial.C : R →+* MvPolynomial (GVar m a k b) R) (e t) * ∑ q', (MvPolynomial.C : R →+* MvPolynomial (GVar m a k b) R) (gell a b hk D (jj t) q') * gxi a b hk c w' q' := by
  intro R _ m a k b N hk D c hak hkb h q
  classical
  let admitted : Set.powersetCard (Fin m) k → Prop := fun S =>
    (∀ i : Fin m, (i : ℕ) < a → i ∈ Set.range (subsetEnum S)) ∧ ∀ l, (subsetEnum S l).val < b
  have hex : ∀ S : {S // admitted S}, ∃ v : GPm m a b, ∀ l, v.1 (Fin.castLE hk l) = subsetEnum S.1 l := fun S =>
    exists_perm hk hkb hak _ (subsetEnum_injective S.1)
      (fun l hl => enum_init hk hak _ (S.1.1.orderEmbOfFin S.1.2).strictMono S.2.1 l l.2 hl) S.2.2
  choose jj hjj using hex
  refine ⟨{S // admitted S}, inferInstance, jj, fun S => plk c (subsetEnum S.1) q, fun w => ?_⟩
  have h1 : ∀ S, (jj S).1 ∘ Fin.castLE hk = subsetEnum S.1 := fun S => funext (hjj S)
  simp only [sum_gell hk h, h1]
  rw [gxi_eq, ← Finset.sum_subtype (Finset.univ.filter admitted) (by simp)
    (fun S => MvPolynomial.C (plk c (subsetEnum S) q) * ((pmat hk w).submatrix id (subsetEnum S)).det),
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun S _ => ?_
  split_ifs with hS
  · exact mul_comm _ _
  · rw [not_and_or] at hS
    rcases hS with hS | hS
    · push Not at hS
      obtain ⟨i, hi, hf⟩ := hS
      rw [det_eq_zero_of_lt hk hak w _ i hi hf, zero_mul]
    · push Not at hS
      obtain ⟨l, hl⟩ := hS
      rw [det_eq_zero_of_ge hk hkb w _ l hl, zero_mul]

end GlobalTheory.GrCl.CellLin
