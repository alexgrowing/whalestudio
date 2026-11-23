import Formalism.AdmissibleDesigns.NonemptyPl

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Formalism.BasicNotions Classical

namespace Formalism.MainNotions.N.K

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.MainNotions Formalism.MainNotions.N

section Arith

def qU (e : ℕ) (x : ℕ∞) : ℚ := (x.toNat : ℚ) / e

theorem qU_mono {e : ℕ} {x y : ℕ∞} (h : x ≤ y) (hy : y ≠ ⊤) : qU e x ≤ qU e y := by
  unfold qU
  have h1 : x.toNat ≤ y.toNat := ENat.toNat_le_toNat h hy
  have h2 : (x.toNat : ℚ) ≤ y.toNat := by exact_mod_cast h1
  gcongr

theorem qU_eO_mul {e : ℕ} (he : e ≠ 0) (x : ℕ∞) : qU e ((e : ℕ∞) * x) = (x.toNat : ℚ) := by
  induction x using ENat.recTopCoe with
  | top =>
    rw [ENat.mul_top (by exact_mod_cast he)]
    simp only [qU, ENat.toNat_top, Nat.cast_zero, zero_div]
  | coe n =>
    have he0 : (e : ℚ) ≠ 0 := by exact_mod_cast he
    rw [← Nat.cast_mul]
    simp only [qU, ENat.toNat_natCast]
    push_cast
    first | (field_simp; ring) | field_simp

theorem inequality_of_finite_terms (e : ℕ) (he : e ≠ 0) (eO : ℕ∞) (heO : eO = e) (lhs : ℕ∞) (what₂ cols qs : Finset ℕ)
    (rowLen h0d z : ℕ → ℕ∞) (e' j deg : ℕ → ℕ) (vδ s H0 : ℕ∞) (Sha : ℕ → ℕ∞) (hE t cB Nn : ℕ)
    (hR : ∀ w ∈ what₂, rowLen w ≠ ⊤) (hH : ∀ w ∈ cols, h0d w ≠ ⊤) (hv : vδ ≠ ⊤) (hs : s ≠ ⊤)
    (hSha : ∀ k ∈ Finset.Ioo 0 t, Sha k ≠ ⊤) (hH0 : H0 ≠ ⊤) (hz : ∀ w ∈ qs, z w ≠ ⊤)
    (hd : lhs ≤
      ∑ w ∈ what₂, rowLen w +
        ∑ w ∈ cols, (eO * (e' w : ℕ∞) + (j w : ℕ∞) * (eO * (e' w : ℕ∞) + vδ) + 2 * vδ + h0d w) + s +
        ∑ k ∈ Finset.Ioo 0 t, Sha k + eO * (hE : ℕ∞) +
        (t : ℕ∞) * eO * (cB : ℕ∞) * ∑ w ∈ what₂, ((deg w : ℕ∞) + 2) +
        4 * ((Nn : ℕ∞) + t) * ((cols.card : ℕ∞) + 1) * vδ +
        (t : ℕ∞) * (cols.card : ℕ∞) * H0 + (t : ℕ∞) * ∑ w ∈ qs, z w) :
    qU e lhs ≤
      ∑ w ∈ what₂, qU e (rowLen w) +
        ∑ w ∈ cols, ((e' w : ℚ) + (j w : ℚ) * ((e' w : ℚ) + qU e vδ) + 2 * qU e vδ + qU e (h0d w)) +
        qU e s + ∑ k ∈ Finset.Ioo 0 t, qU e (Sha k) + (hE : ℚ) +
        (t : ℚ) * (∑ w ∈ what₂, ((deg w : ℚ) + 2) * (cB : ℚ)) +
        4 * ((Nn : ℚ) + t) * ((cols.card : ℚ) + 1) * qU e vδ +
        (t : ℚ) * (cols.card : ℚ) * qU e H0 + (t : ℚ) * ∑ w ∈ qs, qU e (z w) := by
  subst heO
  obtain ⟨v, rfl⟩ := ENat.ne_top_iff_exists.mp hv
  obtain ⟨sn, rfl⟩ := ENat.ne_top_iff_exists.mp hs
  obtain ⟨h0n, rfl⟩ := ENat.ne_top_iff_exists.mp hH0
  have h1 : ∑ w ∈ what₂, rowLen w = ((∑ w ∈ what₂, (rowLen w).toNat : ℕ) : ℕ∞) := by
    rw [Nat.cast_sum]; exact Finset.sum_congr rfl fun w hw => (ENat.natCast_toNat (hR w hw)).symm
  have h2 : ∑ w ∈ cols, ((e : ℕ∞) * (e' w : ℕ∞) + (j w : ℕ∞) * ((e : ℕ∞) * (e' w : ℕ∞) + (v : ℕ∞)) +
      2 * (v : ℕ∞) + h0d w) =
      ((∑ w ∈ cols, (e * e' w + j w * (e * e' w + v) + 2 * v + (h0d w).toNat) : ℕ) : ℕ∞) := by
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [← ENat.natCast_toNat (hH w hw)]
    simp only [ENat.toNat_natCast]
    push_cast; ring
  have h3 : ∑ k ∈ Finset.Ioo 0 t, Sha k = ((∑ k ∈ Finset.Ioo 0 t, (Sha k).toNat : ℕ) : ℕ∞) := by
    rw [Nat.cast_sum]; exact Finset.sum_congr rfl fun k hk => (ENat.natCast_toNat (hSha k hk)).symm
  have h4 : ∑ w ∈ qs, z w = ((∑ w ∈ qs, (z w).toNat : ℕ) : ℕ∞) := by
    rw [Nat.cast_sum]; exact Finset.sum_congr rfl fun w hw => (ENat.natCast_toNat (hz w hw)).symm
  have h5 : ∑ w ∈ what₂, ((deg w : ℕ∞) + 2) = ((∑ w ∈ what₂, (deg w + 2) : ℕ) : ℕ∞) := by
    push_cast; rfl
  rw [h1, h2, h3, h4, h5] at hd
  norm_cast at hd
  have hl : lhs ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top _) hd
  obtain ⟨L, rfl⟩ := ENat.ne_top_iff_exists.mp hl
  have hL := (ENat.natCast_le_natCast).mp hd
  have hq := (Nat.cast_le (α := ℚ)).mpr hL
  have heq : (e : ℚ) ≠ 0 := by exact_mod_cast he
  have hs1 : ∑ w ∈ what₂, qU e (rowLen w) = ((∑ w ∈ what₂, (rowLen w).toNat : ℕ) : ℚ) / e := by
    rw [Nat.cast_sum, Finset.sum_div]; rfl
  have hs2 : ∑ w ∈ cols, ((e' w : ℚ) + (j w : ℚ) * ((e' w : ℚ) + qU e (v : ℕ∞)) + 2 * qU e (v : ℕ∞) +
      qU e (h0d w)) =
      ((∑ w ∈ cols, (e * e' w + j w * (e * e' w + v) + 2 * v + (h0d w).toNat) : ℕ) : ℚ) / e := by
    rw [Nat.cast_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp only [qU, ENat.toNat_natCast]
    push_cast
    field_simp
    try ring
  have hs3 : ∑ k ∈ Finset.Ioo 0 t, qU e (Sha k) = ((∑ k ∈ Finset.Ioo 0 t, (Sha k).toNat : ℕ) : ℚ) / e := by
    rw [Nat.cast_sum, Finset.sum_div]; rfl
  have hs4 : ∑ w ∈ qs, qU e (z w) = ((∑ w ∈ qs, (z w).toNat : ℕ) : ℚ) / e := by
    rw [Nat.cast_sum, Finset.sum_div]; rfl
  have hs5 : ∑ w ∈ what₂, ((deg w : ℚ) + 2) * (cB : ℚ) = ((∑ w ∈ what₂, (deg w + 2) : ℕ) : ℚ) * cB := by
    rw [Nat.cast_sum, Finset.sum_mul]; push_cast; rfl
  rw [hs1, hs2, hs3, hs4, hs5]
  simp only [qU, ENat.toNat_natCast]
  rw [div_le_iff₀ (by positivity)]
  refine hq.trans (le_of_eq ?_)
  push_cast
  field_simp
  try ring

end Arith

section Rec

variable {D : D7} (i : D.nd.Loc) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (dc : TruncatedSeriesCountingIdentities.Decl D i)

open Formalism.MainNotions.N.Glob Formalism.BasicNotions.Loc

def eON : ℕ∞ := Module.length (D.nd.O i) (D.nd.O i ⧸ Ideal.span {((D.nd.l i : ℕ) : D.nd.O i)})

def jN (n : ℕ) : ℕ :=
  if h : plOf i dc n ∈ placesOver D.host.E (D.nd.l i) then Br.jW D.loc D.nbr i (plOf i dc n) h ρ π else 0

def e'N (e' : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (n : ℕ) : ℕ := e' (plOf i dc n)

def sN : ℕ∞ := Module.length (D.nd.O i) ↥(Br.selPi D.loc D.nbr i ρ π)

def ShaN (e : ℕ) : ℕ∞ := eON i * Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ)

def twistInvariantsLength (w : HeightOneSpectrum (𝓞 D.host.E)) : ℕ∞ :=
  Module.length (D.nd.O i) ↥(Representation.invariants ((Br.WKO i ρ π).comp (decS D.nd w)))

def invLen (w : HeightOneSpectrum (𝓞 D.host.E)) (e : ℕ) : ℕ∞ :=
  Module.length (D.nd.O i) ↥(Representation.invariants ((KOtw D.nd i (e : ℤ)).comp (decS D.nd w)))

def invariantsLengthSup : ℕ∞ := (dc.col ×ˢ Finset.Ioo 0 D.R.t).sup fun p => invLen i p.1 p.2

def zetaN (n : ℕ) : D.nd.O i := D.nd.zeta i (plOf i dc n)

def LeTwistInvariantsAtColumns (h0d : ℕ → ℕ∞) : Prop := ∀ n ∈ colsN i dc, h0d n ≤ twistInvariantsLength i ρ π (plOf i dc n)

def TieRow (rowLen : ℕ → ℕ∞) (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ) : Prop :=
  ∀ n ∈ rowsN i dc, rowLen n ≠ ⊤ ∧ ((rowLen n).toNat : ℚ) ≤ ((eON i).toNat : ℚ) * lenRow (plOf i dc n)

def FiniteTwistInvariants : Prop := ∀ w ∈ dc.col, twistInvariantsLength i ρ π w < ⊤

def FiniteCharacterInvariants : Prop := ∀ w ∈ dc.col, ∀ e ∈ Finset.Ioo 0 D.R.t, invLen i w e < ⊤

def ZetaNe : Prop := ∀ v ∈ D.nd.Q i, D.nd.zeta i v ≠ 1

end Rec

section Sel

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Finset

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {A T' G : Type} [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A] [Group G] [TopologicalSpace G]

def selRho (M : Type) [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M]
    (r : G →* A) (χ : G →* T'ˣ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (colIdx : ι → ℕ) (D : ℕ → Subgroup G) (what₂ : Finset ℕ)
    (F : ∀ w, Submodule O (H1z (resRep (uRep O (M := M) r χ) (D w))))
    {Vo : Type} (Io : Vo → Subgroup G) : Submodule O (H1z (uRep O (M := M) r χ)) :=
  (lcH1 (uRep O (M := M) r χ) ⊓ ⨅ v, unrH1 (uRep O (M := M) r χ) (Io v)) ⊓
    ⨅ w ∈ what₂ ∪ univ.image colIdx, (F w).comap (resH1 (uRep O (M := M) r χ) (D w))

def selChi (M : Type) [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M]
    (r : G →* A) (χ : G →* T'ˣ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (colIdx : ι → ℕ) (D : ℕ → Subgroup G) (what₂ qs : Finset ℕ)
    (F : ∀ w, Submodule O (H1z (resRep (uRep O (M := M) r χ) (D w))))
    {Vo VS : Type} (Io : Vo → Subgroup G) (IS : VS → Subgroup G) : Submodule O (H1z (uRep O (M := M) r χ)) :=
  (lcH1 (uRep O (M := M) r χ) ⊓ (⨅ v, unrH1 (uRep O (M := M) r χ) (Io v)) ⊓
      ⨅ v, unrH1 (uRep O (M := M) r χ) (IS v)) ⊓
    ⨅ w ∈ what₂ ∪ qs ∪ univ.image colIdx, (F w).comap (resH1 (uRep O (M := M) r χ) (D w))

def InjTie {H H' : Type} [AddCommGroup H] [Module O H] [AddCommGroup H'] [Module O H']
    (S : Submodule O H) (S' : Submodule O H') : Prop :=
  ∃ f : ↥S →ₗ[O] ↥S', Function.Injective f

theorem length_le_of_injTie {H H' : Type} [AddCommGroup H] [Module O H] [AddCommGroup H'] [Module O H']
    {S : Submodule O H} {S' : Submodule O H'} (h : InjTie S S') :
    Module.length O ↥S ≤ Module.length O ↥S' := by
  obtain ⟨f, hf⟩ := h
  exact Module.length_le_of_injective f hf

end Sel

section SelRec

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology

variable {D : D7} (i : D.nd.Loc) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  {A T' G : Type} [Ring A] [Algebra (D.nd.O i) A] [CommRing T'] [Algebra T' A] [Group G] [TopologicalSpace G]

def TieSel1 (M : Type) [AddCommGroup M] [Module A M] [Module (D.nd.O i) M] [SMulCommClass A (D.nd.O i) M]
    (r : G →* A) (χ : G →* T'ˣ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (colIdx : ι → ℕ) (Dw : ℕ → Subgroup G) (what₂ : Finset ℕ)
    (F : ∀ w, Submodule (D.nd.O i) (H1z (resRep (uRep (D.nd.O i) (M := M) r χ) (Dw w))))
    {Vo : Type} (Io : Vo → Subgroup G) : Prop :=
  InjTie (selRho M r χ colIdx Dw what₂ F Io) (Br.selPi D.loc D.nbr i ρ π)

theorem selRho_le_sN (M : Type) [AddCommGroup M] [Module A M] [Module (D.nd.O i) M]
    [SMulCommClass A (D.nd.O i) M]
    (r : G →* A) (χ : G →* T'ˣ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (colIdx : ι → ℕ) (Dw : ℕ → Subgroup G) (what₂ : Finset ℕ)
    (F : ∀ w, Submodule (D.nd.O i) (H1z (resRep (uRep (D.nd.O i) (M := M) r χ) (Dw w))))
    {Vo : Type} (Io : Vo → Subgroup G) (h : TieSel1 i ρ π M r χ colIdx Dw what₂ F Io) :
    Module.length (D.nd.O i) ↥(selRho M r χ colIdx Dw what₂ F Io) ≤ sN i ρ π := length_le_of_injTie h

def TieSel2 (M : Type) [AddCommGroup M] [Module A M] [Module (D.nd.O i) M] [SMulCommClass A (D.nd.O i) M]
    (r : G →* A) (χ : G →* T'ˣ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (colIdx : ι → ℕ) (Dw : ℕ → Subgroup G) (what₂ qs : Finset ℕ)
    (F : ∀ w, Submodule (D.nd.O i) (H1z (resRep (uRep (D.nd.O i) (M := M) r χ) (Dw w))))
    {Vo VS : Type} (Io : Vo → Subgroup G) (IS : VS → Subgroup G) (c : ℕ) : Prop :=
  Module.length (D.nd.O i) ↥(selChi M r χ colIdx Dw what₂ qs F Io IS) ≤ ShaN i (c - 1)

end SelRec

section N9Rec

variable {D : D7} (i : D.nd.Loc) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (dc : TruncatedSeriesCountingIdentities.Decl D i)

open Formalism.MainNotions.N.Glob Formalism.BasicNotions.Loc

theorem eON_eq : ∃ e : ℕ, e ≠ 0 ∧ eON i = e := by
  obtain ⟨e, he0, he⟩ := Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.exists_eO D.nd i
  exact ⟨e, he0, by unfold eON; rw [Formalism.NG.IdempotentNormalFormsLenFacts.length_quot_span, he]⟩

theorem lenUnit_eq_qU (M : Type) [AddCommGroup M] [Module (D.nd.O i) M] :
    lenUnit (O := D.nd.O i) (D.nd.l i) M = qU (eON i).toNat (Module.length (D.nd.O i) M) := rfl

theorem row_mem_plSet {v : HeightOneSpectrum (𝓞 D.host.E)} (h : v ∈ dc.row) : v ∈ plSet i dc := by
  unfold plSet
  exact Finset.mem_union_left _ (Finset.mem_union_left _ h)

theorem col_mem_plSet {v : HeightOneSpectrum (𝓞 D.host.E)} (h : v ∈ dc.col) : v ∈ plSet i dc := by
  unfold plSet
  exact Finset.mem_union_left _ (Finset.mem_union_right _ h)

theorem q_mem_plSet {v : HeightOneSpectrum (𝓞 D.host.E)} (h : v ∈ D.nd.Q i) : v ∈ plSet i dc := by
  unfold plSet
  exact Finset.mem_union_right _ h

theorem sum_rowsN {β : Type} [AddCommMonoid β] (f : ℕ → β) :
    ∑ n ∈ rowsN i dc, f n = ∑ v ∈ dc.row, f (idx i dc v) := by
  unfold rowsN
  exact Finset.sum_image (by
    intro x hx y hy hxy
    exact idx_inj i dc (row_mem_plSet i dc hx) (row_mem_plSet i dc hy) hxy)

theorem sum_qsN {β : Type} [AddCommMonoid β] (f : ℕ → β) :
    ∑ n ∈ qsN i dc, f n = ∑ v ∈ D.nd.Q i, f (idx i dc v) := by
  unfold qsN
  exact Finset.sum_image (by
    intro x hx y hy hxy
    exact idx_inj i dc (q_mem_plSet i dc hx) (q_mem_plSet i dc hy) hxy)

private theorem image_colIdx_eq_image_idx : Finset.univ.image (colIdx i dc) = dc.col.image (idx i dc) := by
  unfold colIdx
  ext n
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨l, rfl⟩
    exact ⟨l.1, l.2, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨⟨v, hv⟩, rfl⟩

theorem sum_cols {β : Type} [AddCommMonoid β] (f : ℕ → β) :
    ∑ n ∈ Finset.univ.image (colIdx i dc), f n = ∑ v ∈ dc.col, f (idx i dc v) := by
  rw [image_colIdx_eq_image_idx i dc]
  exact Finset.sum_image (by
    intro x hx y hy hxy
    exact idx_inj i dc (col_mem_plSet i dc hx) (col_mem_plSet i dc hy) hxy)

theorem card_cols : (Finset.univ.image (colIdx i dc)).card = dc.col.card := by
  rw [image_colIdx_eq_image_idx i dc]
  exact Finset.card_image_of_injOn (by
    intro x hx y hy hxy
    exact idx_inj i dc (col_mem_plSet i dc hx) (col_mem_plSet i dc hy) hxy)

theorem cols_eq : Finset.univ.image (colIdx i dc) = colsN i dc := by
  unfold colsN
  exact image_colIdx_eq_image_idx i dc

theorem plOf_mem_col {n : ℕ} (hn : n ∈ colsN i dc) : plOf i dc n ∈ dc.col := by
  unfold colsN at hn
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hn
  rw [plOf_idx i dc (col_mem_plSet i dc hv)]
  exact hv

theorem le_H0N {x : ℕ∞} {n : ℕ} (hn : n ∈ colsN i dc) {k : ℕ} (hk : k ∈ Finset.Ioo 0 D.R.t)
    (h : x ≤ invLen i (plOf i dc n) k) : x ≤ invariantsLengthSup i dc := by
  refine h.trans ?_
  unfold invariantsLengthSup
  have hm : (plOf i dc n, k) ∈ dc.col ×ˢ Finset.Ioo 0 D.R.t :=
    Finset.mem_product.2 ⟨plOf_mem_col i dc hn, hk⟩
  have h2 := Finset.le_sup (f := fun p : HeightOneSpectrum (𝓞 D.host.E) × ℕ => invLen i p.1 p.2) hm
  exact h2

theorem invariants_length_sup_ne_top (hF : FiniteCharacterInvariants i dc) : invariantsLengthSup i dc ≠ ⊤ := by
  rw [← lt_top_iff_ne_top]
  unfold invariantsLengthSup
  rw [Finset.sup_lt_iff (bot_lt_top : (⊥ : ℕ∞) < ⊤)]
  rintro ⟨w, k⟩ hp
  rw [Finset.mem_product] at hp
  exact hF w hp.1 k hp.2

theorem qU_H0N_le : qU (eON i).toNat (invariantsLengthSup i dc) ≤ h0 D.nd i dc.col := by
  unfold Formalism.MainNotions.N.h0
  rcases (dc.col ×ˢ Finset.Ioo 0 D.R.t).eq_empty_or_nonempty with hs | hs
  · unfold invariantsLengthSup
    rw [hs]
    simp [qU]
  · obtain ⟨p, hp, hpeq⟩ := Finset.exists_mem_eq_sup _ hs (fun p => invLen i p.1 p.2)
    have hH : invariantsLengthSup i dc = invLen i p.1 p.2 := by
      unfold invariantsLengthSup
      exact hpeq
    rw [hH]
    have hm : qU (eON i).toNat (invLen i p.1 p.2) ∈ Finset.image (fun p => lenUnit (D.nd.l i)
        ↥(Representation.invariants (MonoidHom.comp (KOtw D.nd i ↑p.2) (decS D.nd p.1))))
        (dc.col ×ˢ Finset.Ioo 0 D.R.t) := Finset.mem_image.2 ⟨p, hp, rfl⟩
    obtain ⟨m, hmax⟩ := Finset.max_of_mem hm
    rw [hmax, WithBot.unbotD_coe]
    exact Finset.le_max_of_eq hm hmax

theorem vcc_eq_qU : D.nd.vcc i π =
    qU (eON i).toNat (Module.length (D.nd.O i) (D.nd.O i ⧸ ccAt (D.nd.T i) (D.nd.Z i) π)) := rfl

theorem sPi_eq_qU : Br.sPi D.loc D.nbr i ρ π = qU (eON i).toNat (sN i ρ π) := rfl

theorem twist_invariants_unit_change (w : HeightOneSpectrum (𝓞 D.host.E)) :
    Br.h0W i w ρ π = qU (eON i).toNat (twistInvariantsLength i ρ π w) := rfl

theorem qU_ShaN {k : ℕ} (hk : k ∈ Finset.Ioo 0 D.R.t)
    (hf : Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (k : ℤ) < ⊤) :
    qU (eON i).toNat (ShaN i k) = D.what₂.shaLen (D.nd.l i) k := by
  obtain ⟨e, he0, he⟩ := eON_eq i
  unfold ShaN
  rw [he, ENat.toNat_natCast, qU_eO_mul he0]
  obtain ⟨hk0, hkt⟩ := Finset.mem_Ioo.mp hk
  rw [D.nd.sha_eq (D.nd.l i) k hk0 hkt _ (ENat.natCast_toNat hf.ne).symm]

theorem lenUnit_zeta (v : HeightOneSpectrum (𝓞 D.host.E)) :
    lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {D.nd.zeta i v - 1}) =
      qU (eON i).toNat (IsDiscreteValuationRing.addVal (D.nd.O i) (D.nd.zeta i v - 1)) := by
  rw [lenUnit_eq_qU, Formalism.NG.IdempotentNormalFormsLenFacts.length_quot_span]

theorem zeta_ne_top (hz : ZetaNe i) {v : HeightOneSpectrum (𝓞 D.host.E)} (hv : v ∈ D.nd.Q i) :
    IsDiscreteValuationRing.addVal (D.nd.O i) (D.nd.zeta i v - 1) ≠ ⊤ := by
  rw [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
  exact sub_ne_zero.mpr (hz v hv)

theorem card_first_block : Fintype.card {a // RepresentationBoundsCohomology.blk D.R a = 0} = D.R.r :=
  (Fintype.card_congr (Formalism.MainNotions.N.RepresentationBoundsCohomology.blockZeroEquiv D.R.r D.R.t).symm).trans (Fintype.card_fin _)

end N9Rec

section N9Main

variable {D : D7} (i : D.nd.Loc) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (dc : TruncatedSeriesCountingIdentities.Decl D i)

open Formalism.MainNotions.N.Glob Formalism.BasicNotions.Loc

theorem qU_vdel {vδ : ℕ∞}
    (hvδ : vδ = eON i * ((∑ k ∈ Finset.Ioo 0 D.R.t, (D.nd.s0 i + padicValNat (D.nd.l i) k) : ℕ) : ℕ∞)) :
    qU (eON i).toNat vδ = D.nd.vdel i := by
  unfold Formalism.BasicNotions.NData.vdel
  obtain ⟨e, he, hE⟩ := eON_eq i
  rw [hvδ, hE, ENat.toNat_natCast, qU_eO_mul he, ENat.toNat_natCast]
  push_cast
  first | rfl | simp [Finset.sum_add_distrib] | ring

theorem selmer_length_inequality (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ) (e' : HeightOneSpectrum (𝓞 D.host.E) → ℕ)
    (cB : ℕ) (rowLen h0d : ℕ → ℕ∞) (vδ : ℕ∞) (Nn : ℕ)
    (hvδ : vδ = eON i * ((∑ k ∈ Finset.Ioo 0 D.R.t, (D.nd.s0 i + padicValNat (D.nd.l i) k) : ℕ) : ℕ∞))
    (hN : Nn = D.R.r)
    (hd : Module.length (D.nd.O i) (D.nd.O i ⧸ ccAt (D.nd.T i) (D.nd.Z i) π) ≤
      ∑ w ∈ rowsN i dc, rowLen w +
        ∑ w ∈ Finset.univ.image (colIdx i dc), (eON i * (e'N i dc e' w : ℕ∞) +
          (jN i ρ π dc w : ℕ∞) * (eON i * (e'N i dc e' w : ℕ∞) + vδ) + 2 * vδ + h0d w) + sN i ρ π +
        ∑ e ∈ Finset.Ioo 0 D.R.t, ShaN i e +
        eON i * (padicValNat (D.nd.l i) (classNumber D.host.E) : ℕ∞) +
        (D.R.t : ℕ∞) * eON i * (cB : ℕ∞) * ∑ w ∈ rowsN i dc, ((ReciprocityTheory.Gal.locDeg (plOf i dc w) : ℕ∞) + 2) +
        4 * ((Nn : ℕ∞) + D.R.t) * (((Finset.univ.image (colIdx i dc)).card : ℕ∞) + 1) * vδ +
        (D.R.t : ℕ∞) * ((Finset.univ.image (colIdx i dc)).card : ℕ∞) * invariantsLengthSup i dc +
        (D.R.t : ℕ∞) * ∑ w ∈ qsN i dc, IsDiscreteValuationRing.addVal (D.nd.O i) (zetaN i dc w - 1))
    (hT4 : TieRow i dc rowLen lenRow) (hT3 : LeTwistInvariantsAtColumns i ρ π dc h0d) (hF1 : FiniteTwistInvariants i ρ π dc)
    (hF2 : FiniteCharacterInvariants i dc) (hz : ZetaNe i) (hs : Br.sFin D.loc D.nbr i ρ π)
    (hsha : ∀ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) < ⊤) :
    D.nd.vcc i π ≤
      (∑ w ∈ dc.row ∪ dc.col, TruncatedSeriesCountingIdentities.lenW i ρ π dc lenRow e' w) + Br.sPi D.loc D.nbr i ρ π +
      (∑ e ∈ Finset.Ioo 0 D.R.t, D.what₂.shaLen (D.nd.l i) e) +
      (padicValNat (D.nd.l i) (Formalism.MainNotions.N.hE D.host) : ℚ) +
      (D.R.t : ℚ) * (∑ w ∈ dc.row, ((Formalism.MainNotions.N.locDeg D.host.E w : ℚ) + 2) * (cB : ℚ)) +
      4 * (D.R.nV : ℚ) * ((dc.col.card : ℚ) + 1) * D.nd.vdel i +
      (D.R.t : ℚ) * (dc.col.card : ℚ) * h0 D.nd i dc.col +
      (D.R.t : ℚ) * (∑ v ∈ D.nd.Q i, lenUnit (O := D.nd.O i) (D.nd.l i)
        (D.nd.O i ⧸ Ideal.span {D.nd.zeta i v - 1})) := by
  obtain ⟨e, he0, he⟩ := eON_eq i
  have hEt : (eON i).toNat = e := by rw [he, ENat.toNat_natCast]
  have hEpos : (0 : ℚ) < ((eON i).toNat : ℚ) := by rw [hEt]; exact_mod_cast Nat.pos_of_ne_zero he0

  have hR : ∀ w ∈ rowsN i dc, rowLen w ≠ ⊤ := fun w hw => (hT4 w hw).1
  have hH : ∀ w ∈ Finset.univ.image (colIdx i dc), h0d w ≠ ⊤ := by
    intro n hn
    rw [cols_eq] at hn
    exact ne_top_of_le_ne_top (hF1 _ (plOf_mem_col i dc hn)).ne (hT3 n hn)
  have hv : vδ ≠ ⊤ := by rw [hvδ, he, ← Nat.cast_mul]; exact ENat.natCast_ne_top _
  have hs' : sN i ρ π ≠ ⊤ := (show sN i ρ π < ⊤ from hs).ne
  have hSha : ∀ k ∈ Finset.Ioo 0 D.R.t, ShaN i k ≠ ⊤ := by
    intro k hk
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (hsha k hk).ne
    unfold ShaN
    rw [← hm, he, ← Nat.cast_mul]
    exact ENat.natCast_ne_top _
  have hz' : ∀ n ∈ qsN i dc, IsDiscreteValuationRing.addVal (D.nd.O i) (zetaN i dc n - 1) ≠ ⊤ := by
    intro n hn
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hn
    unfold zetaN
    rw [plOf_idx i dc (q_mem_plSet i dc hv)]
    exact zeta_ne_top i hz hv
  have key := inequality_of_finite_terms e he0 (eON i) he _ (rowsN i dc) (Finset.univ.image (colIdx i dc)) (qsN i dc) rowLen h0d
    (fun w => IsDiscreteValuationRing.addVal (D.nd.O i) (zetaN i dc w - 1)) (e'N i dc e') (jN i ρ π dc)
    (fun w => ReciprocityTheory.Gal.locDeg (plOf i dc w)) vδ (sN i ρ π) (invariantsLengthSup i dc) (ShaN i)
    (padicValNat (D.nd.l i) (classNumber D.host.E)) D.R.t cB Nn hR hH hv hs' hSha (invariants_length_sup_ne_top i dc hF2) hz' hd
  rw [← hEt] at key
  rw [vcc_eq_qU]

  have hvd := qU_vdel i hvδ
  have A0 : ∑ w ∈ dc.row ∪ dc.col, TruncatedSeriesCountingIdentities.lenW i ρ π dc lenRow e' w =
      ∑ w ∈ dc.row, lenRow w + ∑ w ∈ dc.col, TruncatedSeriesCountingIdentities.lenW i ρ π dc lenRow e' w := by
    rw [Finset.sum_union dc.disj]
    congr 1
    refine Finset.sum_congr rfl fun w hw => ?_
    unfold TruncatedSeriesCountingIdentities.lenW
    rw [dif_neg (Finset.disjoint_left.mp dc.disj hw)]
  have A1 : ∑ n ∈ rowsN i dc, qU (eON i).toNat (rowLen n) ≤ ∑ w ∈ dc.row, lenRow w := by
    rw [sum_rowsN]
    refine Finset.sum_le_sum fun v hv => ?_
    have hn : idx i dc v ∈ rowsN i dc := Finset.mem_image_of_mem _ hv
    have h2 := (hT4 _ hn).2
    rw [plOf_idx i dc (row_mem_plSet i dc hv)] at h2
    unfold qU
    rw [div_le_iff₀ hEpos]
    linarith
  have A2 : ∑ w ∈ Finset.univ.image (colIdx i dc),
      ((e'N i dc e' w : ℚ) + (jN i ρ π dc w : ℚ) * ((e'N i dc e' w : ℚ) + qU (eON i).toNat vδ) +
        2 * qU (eON i).toNat vδ + qU (eON i).toNat (h0d w)) ≤
      ∑ w ∈ dc.col, TruncatedSeriesCountingIdentities.lenW i ρ π dc lenRow e' w := by
    rw [sum_cols]
    refine Finset.sum_le_sum fun v hv => ?_
    have hpo := plOf_idx i dc (col_mem_plSet i dc hv)
    have hw : v ∈ placesOver D.host.E (D.nd.l i) := (dc.cover v).1 (Or.inr hv)
    have hjw : ∀ u (hu : u = v) (h : u ∈ placesOver D.host.E (D.nd.l i)),
        Br.jW D.loc D.nbr i u h ρ π = Br.jW D.loc D.nbr i v hw ρ π := by
      rintro u rfl h; rfl
    have hj : jN i ρ π dc (idx i dc v) = Br.jW D.loc D.nbr i v hw ρ π := by
      unfold jN
      rw [dif_pos (by rw [hpo]; exact hw)]
      exact hjw _ hpo _
    have he' : e'N i dc e' (idx i dc v) = e' v := by unfold e'N; rw [hpo]
    have hn : idx i dc v ∈ colsN i dc := Finset.mem_image_of_mem _ hv
    have hh : qU (eON i).toNat (h0d (idx i dc v)) ≤ Br.h0W i v ρ π := by
      rw [twist_invariants_unit_change]
      have h3 := hT3 _ hn
      rw [hpo] at h3
      exact qU_mono h3 (hF1 v hv).ne
    unfold TruncatedSeriesCountingIdentities.lenW
    rw [dif_pos hv]
    unfold Br.lenCol
    rw [hj, he', hvd]
    linarith
  have A3 : qU (eON i).toNat (sN i ρ π) = Br.sPi D.loc D.nbr i ρ π := (sPi_eq_qU i ρ π).symm
  have A4 : ∑ k ∈ Finset.Ioo 0 D.R.t, qU (eON i).toNat (ShaN i k) =
      ∑ k ∈ Finset.Ioo 0 D.R.t, D.what₂.shaLen (D.nd.l i) k :=
    Finset.sum_congr rfl fun k hk => qU_ShaN i hk (hsha k hk)
  have A5 : ((padicValNat (D.nd.l i) (classNumber D.host.E) : ℕ) : ℚ) =
      (padicValNat (D.nd.l i) (Formalism.MainNotions.N.hE D.host) : ℚ) := rfl
  have A6 : ∑ n ∈ rowsN i dc, ((ReciprocityTheory.Gal.locDeg (plOf i dc n) : ℚ) + 2) * (cB : ℚ) =
      ∑ w ∈ dc.row, ((Formalism.MainNotions.N.locDeg D.host.E w : ℚ) + 2) * (cB : ℚ) := by
    rw [sum_rowsN]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [plOf_idx i dc (row_mem_plSet i dc hv)]
    rfl
  have A7 : 4 * ((Nn : ℚ) + D.R.t) * (((Finset.univ.image (colIdx i dc)).card : ℕ) + 1 : ℚ) *
      qU (eON i).toNat vδ = 4 * (D.R.nV : ℚ) * ((dc.col.card : ℚ) + 1) * D.nd.vdel i := by
    rw [card_cols, hvd, hN]
    unfold Ranks.nV
    push_cast
    ring
  have A8 : (D.R.t : ℚ) * (((Finset.univ.image (colIdx i dc)).card : ℕ) : ℚ) * qU (eON i).toNat (invariantsLengthSup i dc) ≤
      (D.R.t : ℚ) * (dc.col.card : ℚ) * h0 D.nd i dc.col := by
    rw [card_cols]
    exact mul_le_mul_of_nonneg_left (qU_H0N_le i dc) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have A9 : ∑ n ∈ qsN i dc, qU (eON i).toNat (IsDiscreteValuationRing.addVal (D.nd.O i) (zetaN i dc n - 1)) =
      ∑ v ∈ D.nd.Q i, lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {D.nd.zeta i v - 1}) := by
    rw [sum_qsN]
    refine Finset.sum_congr rfl fun v hv => ?_
    unfold zetaN
    rw [plOf_idx i dc (q_mem_plSet i dc hv), lenUnit_zeta]
  rw [A3, A4, A5, A6, A7, A9] at key
  rw [A0]
  linarith

end N9Main

section N9Cor

variable {D : D7} (i : D.nd.Loc) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (dc : TruncatedSeriesCountingIdentities.Decl D i)

open Formalism.MainNotions.N.Glob Formalism.BasicNotions.Loc

def SelmerLengthInequality (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ) (e' : HeightOneSpectrum (𝓞 D.host.E) → ℕ)
    (cB : ℕ) : Prop :=
  ∃ (rowLen h0d : ℕ → ℕ∞) (vδ : ℕ∞) (Nn : ℕ),
    vδ = eON i * ((∑ k ∈ Finset.Ioo 0 D.R.t, (D.nd.s0 i + padicValNat (D.nd.l i) k) : ℕ) : ℕ∞) ∧
    Nn = D.R.r ∧
    Module.length (D.nd.O i) (D.nd.O i ⧸ ccAt (D.nd.T i) (D.nd.Z i) π) ≤
      ∑ w ∈ rowsN i dc, rowLen w +
        ∑ w ∈ Finset.univ.image (colIdx i dc), (eON i * (e'N i dc e' w : ℕ∞) +
          (jN i ρ π dc w : ℕ∞) * (eON i * (e'N i dc e' w : ℕ∞) + vδ) + 2 * vδ + h0d w) + sN i ρ π +
        ∑ e ∈ Finset.Ioo 0 D.R.t, ShaN i e +
        eON i * (padicValNat (D.nd.l i) (classNumber D.host.E) : ℕ∞) +
        (D.R.t : ℕ∞) * eON i * (cB : ℕ∞) * ∑ w ∈ rowsN i dc, ((ReciprocityTheory.Gal.locDeg (plOf i dc w) : ℕ∞) + 2) +
        4 * ((Nn : ℕ∞) + D.R.t) * (((Finset.univ.image (colIdx i dc)).card : ℕ∞) + 1) * vδ +
        (D.R.t : ℕ∞) * ((Finset.univ.image (colIdx i dc)).card : ℕ∞) * invariantsLengthSup i dc +
        (D.R.t : ℕ∞) * ∑ w ∈ qsN i dc, IsDiscreteValuationRing.addVal (D.nd.O i) (zetaN i dc w - 1) ∧
    TieRow i dc rowLen lenRow ∧ LeTwistInvariantsAtColumns i ρ π dc h0d

theorem theorem_of_display_inequality (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ)
    (e' : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ)
    (hD : D.nd.l i ≠ D.host.g 0 → D.nd.l i ≠ D.host.g 1 → π ∈ D.nd.Z i → Br.sFin D.loc D.nbr i ρ π →
      (∀ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) < ⊤) →
      SelmerLengthInequality i ρ π dc lenRow e' cB)
    (hF1 : FiniteTwistInvariants i ρ π dc) (hF2 : FiniteCharacterInvariants i dc) (hz : ZetaNe i) :
    TruncatedSeriesCountingIdentities.GlobalLatticeIndexTheorem i ρ π dc lenRow e' cB := by
  unfold TruncatedSeriesCountingIdentities.GlobalLatticeIndexTheorem
  intro h0 h1 hZ hs hsha
  obtain ⟨rowLen, h0d, vδ, Nn, hvδ, hN, hd, hT4, hT3⟩ := hD h0 h1 hZ hs hsha
  exact selmer_length_inequality i ρ π dc lenRow e' cB rowLen h0d vδ Nn hvδ hN hd hT4 hT3 hF1 hF2 hz hs hsha

theorem zeta_ne_one_of_g5_extra (h : TruncatedSeriesCountingIdentities.TameGeneratorConditions i) : ZetaNe i := by
  unfold ZetaNe TruncatedSeriesCountingIdentities.TameGeneratorConditions at *
  intro v hv
  have h2 := h v (Or.inr hv)
  tauto

theorem theorem_of_display (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ)
    (e' : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ)
    (hD : D.nd.l i ≠ D.host.g 0 → D.nd.l i ≠ D.host.g 1 → π ∈ D.nd.Z i → Br.sFin D.loc D.nbr i ρ π →
      (∀ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) < ⊤) →
      SelmerLengthInequality i ρ π dc lenRow e' cB)
    (hF1 : FiniteTwistInvariants i ρ π dc) (hF2 : FiniteCharacterInvariants i dc) (h5x : TruncatedSeriesCountingIdentities.TameGeneratorConditions i) :
    TruncatedSeriesCountingIdentities.GlobalLatticeIndexTheorem i ρ π dc lenRow e' cB := theorem_of_display_inequality i ρ π dc lenRow e' cB hD hF1 hF2 (zeta_ne_one_of_g5_extra i h5x)

end N9Cor

end Formalism.MainNotions.N.K

end
