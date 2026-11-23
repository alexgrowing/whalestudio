import Mathlib
import Formalism.LocalToGlobal.Divisibility.HeckeCSDICommTrRep
import Development.AbelianVarietyTheory.Definitions.Divisors.FactorBounds
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Matrix
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.RowLevIndex

section Gen

variable {κ : Type} [CommRing κ]

theorem firstDiagonalBlock_of_diagonal_embedding {n r : ℕ} (h : r ≤ n) (bl : List ℕ) (p : GL (Fin r) κ) (M : GL (Fin n) κ)
    (hM : M ∈ blockUT n κ r bl) (e : M = diagEmb κ h p) : blk0 n κ h bl ⟨M, hM⟩ = p := by
  subst e
  apply Units.ext
  ext i j
  rw [blockZero_val]
  show (diagEmb κ h p : Matrix (Fin n) (Fin n) κ) (Fin.castLE h i) (Fin.castLE h j) = _
  rw [diagEmb_val, diagMat_of_lt _ (show (Fin.castLE h i).val < r from i.2) (show (Fin.castLE h j).val < r from j.2)]
  rfl

theorem HK_le_HPar {n r : ℕ} (h : r ≤ n) (bl : List ℕ) (H₀ : Subgroup (GL (Fin r) κ)) :
    HK n κ r bl ≤ HPar n κ h bl H₀ := by
  rw [HK_eq_HPar h bl]
  intro M hM
  obtain ⟨hb, h0⟩ := mem_HPar.mp hM
  exact mem_HPar.mpr ⟨hb, by rw [Subgroup.mem_bot] at h0; rw [h0]; exact H₀.one_mem⟩

theorem mem_HK_iff {n r : ℕ} (h : r ≤ n) (bl : List ℕ) (M : GL (Fin n) κ) (hM : M ∈ blockUT n κ r bl) :
    M ∈ HK n κ r bl ↔ blk0 n κ h bl ⟨M, hM⟩ = 1 := by
  rw [HK_eq_HPar h bl, mem_HPar]
  constructor
  · rintro ⟨_, h0⟩
    exact (Subgroup.mem_bot).mp h0
  · intro h0
    exact ⟨hM, (Subgroup.mem_bot).mpr h0⟩

end Gen

section Rows

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Formalism.L2.Col.Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

open Classical in

abbrev inL (v : Pr.vGs) : rowSG Pr sel mu := ⟨v.1, Finset.mem_union_left _ v.2⟩

theorem rowTy_inL (P : LevFam X.E X.K R.r Pr.vGs) (v : Pr.vGs) :
    rowTy Ch sel mu P (inL sel mu v) = rowTyG Ch P v := LevFam.glue_of_mem _ _ _ v.2

theorem rowTyKK_inL (v : Pr.vGs) :
    rowTyKK Ch sel mu (inL sel mu v) = rowTyK Ch v := LevFam.glue_of_mem _ _ _ v.2

theorem rowTy_H_of_not (P : LevFam X.E X.K R.r Pr.vGs) (w : rowSG Pr sel mu) (hw : w.1 ∉ Pr.vGs) :
    (rowTy Ch sel mu P w).H = (rowTyKK Ch sel mu w).H := by
  unfold rowTy rowTyKK
  rw [LevFam.glue_of_not _ _ _ hw, LevFam.glue_of_not _ _ _ hw]

theorem memP (P : LevFam X.E X.K R.r Pr.vGs) (x : ↥(rowTy Ch sel mu P).inv.grp) (v : Pr.vGs) :
    x.1 (inL sel mu v) ∈ HPar (R.N R.m - 1) (𝓞 X.E ⧸ v.1.asIdeal) (r_le_X' R) (List.replicate R.m R.t) (P v).H := by
  have h := x.2 (inL sel mu v) (Set.mem_univ _)
  change x.1 (inL sel mu v) ∈ (rowTy Ch sel mu P (inL sel mu v)).H at h
  rw [rowTy_inL] at h
  exact h

theorem grp_le (P : LevFam X.E X.K R.r Pr.vGs) :
    (rowTyKK Ch sel mu).inv.grp ≤ (rowTy Ch sel mu P).inv.grp := by
  intro x hx w _
  have h := hx w (Set.mem_univ _)
  change x w ∈ (rowTyKK Ch sel mu w).H at h
  change x w ∈ (rowTy Ch sel mu P w).H
  by_cases hw : w.1 ∈ Pr.vGs
  · have e1 := rowTyKK_inL Ch sel mu ⟨w.1, hw⟩
    have e2 := rowTy_inL Ch sel mu P ⟨w.1, hw⟩
    change rowTyKK Ch sel mu w = _ at e1
    change rowTy Ch sel mu P w = _ at e2
    rw [e1] at h
    rw [e2]
    exact GlobalTheory.RowLevIndex.HK_le_HPar _ _ _ h
  · rw [rowTy_H_of_not Ch sel mu P w hw]
    exact h

def blkMap (P : LevFam X.E X.K R.r Pr.vGs) : FormG (rowTy Ch sel mu P).inv →* GLG X.E R.r Pr.vGs where
  toFun x v := blk0 (R.N R.m - 1) (𝓞 X.E ⧸ v.1.asIdeal) (r_le_X' R) (List.replicate R.m R.t)
    ⟨x.2.1 (inL sel mu v), HPar_le _ _ _ (memP Ch sel mu P x.2 v)⟩
  map_one' := by
    funext v
    exact map_one (blk0 (R.N R.m - 1) (𝓞 X.E ⧸ v.1.asIdeal) (r_le_X' R) (List.replicate R.m R.t))
  map_mul' a b := by
    funext v
    exact map_mul (blk0 (R.N R.m - 1) (𝓞 X.E ⧸ v.1.asIdeal) (r_le_X' R) (List.replicate R.m R.t))
      ⟨a.2.1 (inL sel mu v), HPar_le _ _ _ (memP Ch sel mu P a.2 v)⟩ ⟨b.2.1 (inL sel mu v), HPar_le _ _ _ (memP Ch sel mu P b.2 v)⟩

end Rows

section Rows2

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (P : LevFam X.E X.K R.r Pr.vGs)

def incl : FormG (rowTyKK Ch sel mu).inv →* FormG (rowTy Ch sel mu P).inv :=
  MonoidHom.prodMap (MonoidHom.id _) (Subgroup.inclusion (grp_le Ch sel mu P))

theorem incl_injective : Function.Injective (incl Ch sel mu P) := by
  intro a b e
  have e1 := congrArg Prod.fst e
  have e2 := congrArg (fun x => (x.2 : GLG X.E (R.N R.m - 1) (rowSG Pr sel mu))) e
  exact Prod.ext e1 (Subtype.ext e2)

theorem range_incl : (incl Ch sel mu P).range = (blkMap Ch sel mu P).ker := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    rw [MonoidHom.mem_ker]
    funext v
    have h := y.2.2 (inL sel mu v) (Set.mem_univ _)
    change y.2.1 (inL sel mu v) ∈ (rowTyKK Ch sel mu (inL sel mu v)).H at h
    rw [rowTyKK_inL] at h
    exact (GlobalTheory.RowLevIndex.mem_HK_iff (r_le_X' R) _ _ _).mp h
  · intro hx
    rw [MonoidHom.mem_ker] at hx
    have hmem : x.2.1 ∈ (rowTyKK Ch sel mu).inv.grp := by
      intro w _
      change x.2.1 w ∈ (rowTyKK Ch sel mu w).H
      by_cases hw : w.1 ∈ Pr.vGs
      · have e1 := rowTyKK_inL Ch sel mu ⟨w.1, hw⟩
        change rowTyKK Ch sel mu w = _ at e1
        rw [e1]
        exact (GlobalTheory.RowLevIndex.mem_HK_iff (r_le_X' R) _ _ (HPar_le _ _ _ (memP Ch sel mu P x.2 ⟨w.1, hw⟩))).mpr
          (congrFun hx ⟨w.1, hw⟩)
      · rw [← rowTy_H_of_not Ch sel mu P w hw]
        exact x.2.2 w (Set.mem_univ _)
    exact ⟨(x.1, ⟨x.2.1, hmem⟩), rfl⟩

open Classical in
theorem range_blkMap : (blkMap Ch sel mu P).range = P.grp := by
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    intro v _
    obtain ⟨_, h0⟩ := mem_HPar.mp (memP Ch sel mu P x.2 v)
    exact h0
  · intro hp
    let h : GLG X.E (R.N R.m - 1) (rowSG Pr sel mu) := fun w =>
      if hw : w.1 ∈ Pr.vGs then diagEmb _ (r_le_X' R) (p ⟨w.1, hw⟩) else 1
    have hmem : h ∈ (rowTy Ch sel mu P).inv.grp := by
      intro w _
      change h w ∈ (rowTy Ch sel mu P w).H
      by_cases hw : w.1 ∈ Pr.vGs
      · have e2 := rowTy_inL Ch sel mu P ⟨w.1, hw⟩
        change rowTy Ch sel mu P w = _ at e2
        rw [e2]
        have hh : h w = diagEmb _ (r_le_X' R) (p ⟨w.1, hw⟩) := dif_pos hw
        rw [hh]
        exact mem_HPar.mpr ⟨diagEmb_mem_blockUT _ _ _, by
          rw [GlobalTheory.RowLevIndex.firstDiagonalBlock_of_diagonal_embedding _ _ (p ⟨w.1, hw⟩) _ _ rfl]; exact hp ⟨w.1, hw⟩ (Set.mem_univ _)⟩
      · have hh : h w = 1 := dif_neg hw
        rw [hh]
        exact Subgroup.one_mem _
    refine ⟨((1 : UF X.E (R.N R.m - 1)), ⟨h, hmem⟩), ?_⟩
    funext v
    exact GlobalTheory.RowLevIndex.firstDiagonalBlock_of_diagonal_embedding _ _ (p v) _ _ (dif_pos v.2)

end Rows2

theorem index_eq : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (W : Formalism.L2.Col.Wts X Pr.Word R) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (P : LevFam X.E X.K R.r Pr.vGs), ∃ ι : (mtildeKGSD W Ch sel mu).G →* (mtildeGSD W Ch sel mu P).G, Function.Injective ι ∧ (∀ (a : (mtildeKGSD W Ch sel mu).G) (d : (mtildeKGSD W Ch sel mu).D), ι a • d = a • d) ∧ ι.range.index = Nat.card P.grp := by
  intro X Pr R W Ch sel S mu P
  refine ⟨incl Ch sel mu P, incl_injective Ch sel mu P, fun a d => rfl, ?_⟩
  rw [range_incl, Subgroup.index_ker, range_blkMap]

end GlobalTheory.RowLevIndex
