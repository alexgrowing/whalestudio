import Formalism.LocalToGlobal.Columns.RecLevel
import Formalism.LocalToGlobal.Columns.LevGCount
import Formalism.LocalToGlobal.Columns.RowFormsLemmas

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV (Pl kP St redAt redFn)

section Mem

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG : Finset (Pl E)) (H : Subgroup (GLG E n SG))

theorem mem_mirabolicLevel_iff_local {x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} :
    x ∈ J0 hc n ST ↔ x ∈ UAd hc n ∧ x ∈ St (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ∧ ∀ P ∈ ST, x ∈ mirAt (F := F) n P := by
  simp only [J0, Subgroup.mem_inf, Subgroup.mem_iInf, and_assoc]

theorem rld_redG_apply (k : J0 hc n ST) (w : SG) :
    redG hc n ST SG k w = redFn (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) w.1 (k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
  rw [Formalism.L2.DIV.redFn, Formalism.L2.DIV.extendOne_of_mem _ (congruence_subgroup_le_stabilizer hc n ST k.2)]
  rfl

theorem mem_levU_iff {x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} :
    x ∈ levU hc n ST SG H ↔ x ∈ UAd hc n ∧ x ∈ St (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ∧
      (∀ P ∈ ST, x ∈ mirAt (F := F) n P) ∧
      (fun w : SG => redFn (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) w.1 x) ∈ H := by
  rw [mem_levU]
  constructor
  · rintro ⟨hJ, hH⟩
    obtain ⟨h1, h2, h3⟩ := (mem_mirabolicLevel_iff_local hc n ST).1 hJ
    refine ⟨h1, h2, h3, ?_⟩
    have e : (fun w : SG => redFn (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) w.1 x) = redG hc n ST SG ⟨x, hJ⟩ :=
      funext fun w => (rld_redG_apply hc n ST SG ⟨x, hJ⟩ w).symm
    rw [e]
    exact hH
  · rintro ⟨h1, h2, h3, hH⟩
    have hJ := (mem_mirabolicLevel_iff_local hc n ST).2 ⟨h1, h2, h3⟩
    refine ⟨hJ, ?_⟩
    have e : redG hc n ST SG ⟨x, hJ⟩ = fun w : SG => redFn (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) w.1 x :=
      funext fun w => rld_redG_apply hc n ST SG ⟨x, hJ⟩ w
    rw [e]
    exact hH

theorem levU_eq_inf : levU hc n ST SG H = levU hc n ∅ SG H ⊓ ⨅ P ∈ ST, mirAt (F := F) n P := by
  ext x
  rw [Subgroup.mem_inf, mem_levU_iff, mem_levU_iff]
  simp only [Subgroup.mem_iInf]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨h1, h2, fun P hP => by simp at hP, h4⟩, h3⟩
  · rintro ⟨⟨h1, h2, -, h4⟩, h3⟩
    exact ⟨h1, h2, h3, h4⟩

theorem levRed_apply (x : levU hc n ST SG H) (w : SG) :
    (levRed hc n ST SG H x : GLG E n SG) w =
      redFn (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) w.1 (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :=
  rld_redG_apply hc n ST SG (Subgroup.inclusion (unipotentLevel_le_mirabolicLevel hc n ST SG H) x) w

end Mem

section Fin

variable {κ : Type} [CommRing κ] {n r : ℕ}

theorem rld_coarse_eq {t s : ℕ} (ht : 0 < t) (hn : n = r + s * t) :
    (fun i : Fin n => coarse r (List.replicate s t) i.val) = Formalism.L2.DIV.blkOf r t := by
  funext i
  simp only [coarse, blkIdx, Formalism.L2.DIV.blkOf]
  split_ifs with hi
  · rfl
  · rw [blkIdx_replicate ht s (i.val - r) (by have := i.isLt; omega)]

theorem rld_blockUT_eq {t s : ℕ} (ht : 0 < t) (hn : n = r + s * t) :
    blockUT n κ r (List.replicate s t) = Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t) := by
  ext M
  show (M : Matrix (Fin n) (Fin n) κ).BlockTriangular (fun i => coarse r (List.replicate s t) i.val) ↔
    (M : Matrix (Fin n) (Fin n) κ).BlockTriangular (Formalism.L2.DIV.blkOf r t)
  rw [rld_coarse_eq ht hn]

theorem blockZero_eq_restrictedBlock (h : r ≤ n) (bl : List ℕ) {M : GL (Fin n) κ} (hM : M ∈ blockUT n κ r bl)
    (hM' : M ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r)) : blk0 n κ h bl ⟨M, hM⟩ = Formalism.L2.DIV.upperLeftBlock h M := by
  rw [Formalism.L2.DIV.upperLeftBlock, Formalism.L2.DIV.extendOne_of_mem _ hM']
  apply Units.ext
  rfl

private theorem mem_blockTri_blk2_of_mem_blockTri_blkOf {t : ℕ} {M : GL (Fin n) κ}
    (hM : M ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t)) : M ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r) := by
  have hM2 : (M : Matrix (Fin n) (Fin n) κ).BlockTriangular (Formalism.L2.DIV.blkOf r t) := hM
  show (M : Matrix (Fin n) (Fin n) κ).BlockTriangular (Formalism.L2.DIV.blk2 r)
  intro i j hij
  apply hM2
  simp only [Formalism.L2.DIV.blk2, Formalism.L2.DIV.blkOf] at hij ⊢
  split_ifs at hij ⊢ <;> first | omega | exact Nat.succ_pos _

theorem mem_HPar_iff (h : r ≤ n) {t s : ℕ} (ht : 0 < t) (hn : n = r + s * t) (H₀ : Subgroup (GL (Fin r) κ)) {M : GL (Fin n) κ} :
    M ∈ HPar n κ h (List.replicate s t) H₀ ↔
      M ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t) ∧ Formalism.L2.DIV.upperLeftBlock h M ∈ H₀ := by
  rw [mem_HPar]
  constructor
  · rintro ⟨hM, h0⟩
    have hM' : M ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t) := by
      rw [← rld_blockUT_eq ht hn]
      exact hM
    refine ⟨hM', ?_⟩
    rw [← blockZero_eq_restrictedBlock h _ hM (mem_blockTri_blk2_of_mem_blockTri_blkOf hM')]
    exact h0
  · rintro ⟨hM', h0⟩
    have hM : M ∈ blockUT n κ r (List.replicate s t) := by
      rw [rld_blockUT_eq ht hn]
      exact hM'
    refine ⟨hM, ?_⟩
    rw [blockZero_eq_restrictedBlock h _ hM (mem_blockTri_blk2_of_mem_blockTri_blkOf hM')]
    exact h0

theorem rld_blkDet_eq {t s : ℕ} (ht : 0 < t) (hn : n = r + s * t) (c : ℕ) {M : GL (Fin n) κ}
    (hM : M ∈ blockUT n κ r (List.replicate s t)) :
    blkDet n κ (coarse r (List.replicate s t)) c ⟨M, hM⟩ = Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf r t) c M := by
  have hM' : M ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t) := by
    rw [← rld_blockUT_eq ht hn]
    exact hM
  rw [Formalism.L2.DIV.dBlk, Formalism.L2.DIV.extendOne_of_mem _ hM']
  apply Units.ext
  have key : ∀ b : Fin n → ℕ, b = Formalism.L2.DIV.blkOf r t →
      ((M : Matrix (Fin n) (Fin n) κ).toSquareBlock b c).det = ((M : Matrix (Fin n) (Fin n) κ).submatrix
        (Subtype.val : {a : Fin n // Formalism.L2.DIV.blkOf r t a = c} → Fin n) Subtype.val).det := by
    rintro b rfl
    rfl
  exact key _ (rld_coarse_eq ht hn)

end Fin

section Cmp

variable {F E K : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K]
variable (hc : Formalism.BasicNotions.CMData F E) {n r : ℕ} [NeZero n] (h : r ≤ n) {t s : ℕ} (ht : 0 < t) (hn : n = r + s * t)
  {SG : Finset (Pl E)} (P : LevFam E K r SG) (χ : ∀ w : SG, ℕ → (𝓞 E ⧸ w.1.asIdeal)ˣ →* Kˣ)

include ht hn in

theorem levU_parFam_eq_lev :
    levU hc n ∅ SG (parFam h t s P χ).grp =
      Formalism.L2.DIV.lev hc (1 : Matrix (Fin n) (Fin n) E) (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (parDat h t s P χ) := by
  ext x
  rw [mem_levU_iff, Formalism.L2.DIV.mem_lev]
  simp only [Formalism.L2.DIV.parLev, Subgroup.mem_inf, Subgroup.mem_iInf, Formalism.L2.DIV.mem_parah, LevFam.grp,
    Subgroup.mem_pi, Set.mem_univ, true_implies, parFam, mem_HPar_iff h ht hn, parDat,
    Formalism.L2.DIV.LevelP.ofLocal, Formalism.L2.DIV.rTup]
  constructor
  · rintro ⟨h1, h2, -, h4⟩
    exact ⟨⟨⟨⟨h1, h2⟩, fun PP hP => ⟨h2, (h4 ⟨PP, hP⟩).1⟩⟩, fun _ hP => by simp at hP⟩, fun w _ => (h4 w).2⟩
  · rintro ⟨⟨⟨⟨h1, h2⟩, h3⟩, -⟩, h4⟩
    exact ⟨h1, h2, fun _ hP => by simp at hP, fun w => ⟨(h3 w.1 w.2).2, h4 w (Set.mem_univ w)⟩⟩

include ht hn in

theorem levU_parFam_eq_lev_inf (ST : Finset (Pl E)) :
    levU hc n ST SG (parFam h t s P χ).grp =
      Formalism.L2.DIV.lev hc (1 : Matrix (Fin n) (Fin n) E) (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (parDat h t s P χ) ⊓
        ⨅ Q ∈ ST, mirAt (F := F) n Q := by
  rw [levU_eq_inf, levU_parFam_eq_lev hc h ht hn P χ]

omit [StarRing E] in
theorem rld_ofLocal_chi (Hl : ∀ PP : SG, Subgroup (GL (Fin r) (kP PP.1))) (cl : ∀ PP : SG, Hl PP →* Kˣ)
    (y : (Subgroup.pi Set.univ Hl : Subgroup (Formalism.L2.DIV.G0 SG r))) :
    (Formalism.L2.DIV.LevelP.ofLocal Hl cl).chi y = ∏ PP : SG, cl PP ⟨y.1 PP, y.2 PP (Set.mem_univ PP)⟩ := by
  show (∏ PP : SG, (cl PP).comp (Formalism.L2.DIV.LevelP.prj Hl PP)) y = _
  rw [MonoidHom.finset_prod_apply]
  rfl

omit [StarRing E] in
theorem rld_parDat_cg (c : ℕ) (w : SG) : (parDat h t s P χ).cg (c + 1) w.1 = χ w c := by
  simp only [parDat, dif_pos w.2, Nat.add_sub_cancel, Subtype.coe_eta]

include ht hn in

theorem levChr_parFam_eq_levChar (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (h1 : x ∈ levU hc n ∅ SG (parFam h t s P χ).grp)
    (h2 : x ∈ Formalism.L2.DIV.lev hc (1 : Matrix (Fin n) (Fin n) E) (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (parDat h t s P χ)) :
    levChr (parFam h t s P χ).chr ⟨x, h1⟩ = Formalism.L2.DIV.levChar hc 1 1 (parDat h t s P χ) ⟨x, h2⟩ := by
  have e1 : (levRed hc n ∅ SG (parFam h t s P χ).grp ⟨x, h1⟩ : GLG E n SG) = fun w : SG =>
      redFn (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) w.1 x :=
    funext (levRed_apply hc n ∅ SG _ ⟨x, h1⟩)
  have hx := e1 ▸ (levRed hc n ∅ SG (parFam h t s P χ).grp ⟨x, h1⟩).2
  have k1 : levRed hc n ∅ SG (parFam h t s P χ).grp ⟨x, h1⟩ = ⟨_, hx⟩ := Subtype.ext e1
  have hw : ∀ w : SG, redFn (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) w.1 x ∈
      HPar n (𝓞 E ⧸ w.1.asIdeal) h (List.replicate s t) (P w).H :=
    fun w => (Subgroup.mem_pi _).mp hx w (Set.mem_univ w)
  have hw' := fun w : SG => (mem_HPar_iff h ht hn (P w).H).1 (hw w)
  have eL : levChr (parFam h t s P χ).chr ⟨x, h1⟩ =
      ∏ w : SG, ((P w).lam ⟨Formalism.L2.DIV.upperLeftBlock h (redFn (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) w.1 x), (hw' w).2⟩ *
        ∏ c ∈ Finset.range s, χ w c (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf r t) (c + 1)
          (redFn (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) w.1 x))) := by
    simp only [levChr, MonoidHom.comp_apply]
    rw [k1]
    unfold LevFam.chr piChar
    erw [MonoidHom.finset_prod_apply]
    refine Finset.prod_congr rfl fun w _ => ?_
    show (P w).lam (HPar0 h (List.replicate s t) (P w).H ⟨_, hw w⟩) *
      detChar (χ w) n r (List.replicate s t) ⟨_, HPar_le h _ _ (hw w)⟩ = _
    congr 1
    · congr 1
      apply Subtype.ext
      exact blockZero_eq_restrictedBlock h _ _ (mem_blockTri_blk2_of_mem_blockTri_blkOf (hw' w).1)
    · rw [detChar, MonoidHom.finset_prod_apply, List.length_replicate]
      refine Finset.prod_congr rfl fun c _ => ?_
      rw [MonoidHom.comp_apply, rld_blkDet_eq ht hn]
  have hD := (Formalism.L2.DIV.mem_lev.mp h2).2
  have eR : Formalism.L2.DIV.levChar hc 1 1 (parDat h t s P χ) ⟨x, h2⟩ =
      (∏ w : SG, (P w).lam ⟨Formalism.L2.DIV.upperLeftBlock h (redFn (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) w.1 x), (hw' w).2⟩) *
        ∏ w : SG, ∏ c ∈ Finset.range s, χ w c (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf r t) (c + 1)
          (redFn (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) w.1 x)) := by
    rw [Formalism.L2.DIV.levChar_apply, Formalism.L2.DIV.levFn, Formalism.L2.DIV.extendOne_of_mem _ hD]
    rw [show (parDat h t s P χ).P.chi ⟨_, hD⟩ = _ from
      rld_ofLocal_chi (fun w => (P w).H) (fun w => (P w).lam) ⟨_, hD⟩]
    simp only [parDat, Finset.prod_empty, mul_one]
    congr 1
    rw [← Finset.prod_coe_sort SG]
    refine Finset.prod_congr rfl fun w _ => Finset.prod_congr rfl fun c _ => ?_
    simp only [dif_pos w.2, Nat.add_sub_cancel, Subtype.coe_eta]
  rw [eL, eR, Finset.prod_mul_distrib]

end Cmp

section FinCol

variable {κ K : Type} [CommRing κ] [Field K] {n r : ℕ}

end FinCol

section Cols

open Formalism.BasicNotions (Ranks)

variable {X : Fields} {Pr : Primes X} {R : Ranks} (hc : Formalism.BasicNotions.CMData X.F X.E) (Ch : Chars X Pr R.m)

theorem t_pos (R : Ranks) : 0 < R.t := by
  exact R.t_odd.pos

end Cols

section SharpFin

variable {κ K : Type} [CommRing κ] [Field K]

end SharpFin

section Sharp

open Formalism.BasicNotions (Ranks)

variable {X : Fields} {Pr : Primes X} {R : Ranks} (hc : Formalism.BasicNotions.CMData X.F X.E) (Ch : Chars X Pr R.m)

theorem colLevS_of_lt {j : ℕ} (hj : j + 1 < R.m) : colLevS Ch j = colLev Ch j := by
  funext w
  simp only [colLevS, if_pos hj]

theorem colLevS_top_H {j : ℕ} (hj : R.m ≤ j) (w : Pr.vGs) :
    (colLevS Ch j w).H = HXmsharp (𝓞 X.E ⧸ w.1.asIdeal) (R.N j) R.k R.r R.t R.m := by
  simp only [colLevS, if_neg (show ¬ j + 1 < R.m by omega), if_neg (show ¬ j + 1 = R.m by omega)]

end Sharp

end Formalism.L2.Col
