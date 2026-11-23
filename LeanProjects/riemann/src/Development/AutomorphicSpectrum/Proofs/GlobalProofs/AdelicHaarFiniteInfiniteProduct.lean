import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsUnitOfComm

namespace GlobalTheory.CompanionTheory.LeviGen
open GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart

theorem ind_block_eq {A : Type} [CommRing A] {r : ℕ} (T : Finset (Fin r)) (k : Fin r) :
    (ind (block T k) : Fin r → A) = ind {i | i ≤ k} - ind {i | i ≤ k} * ind (upTo (T.filter (· < k))) := by
  classical
  funext i
  have e : i ∈ block T k ↔ i ∈ {i | i ≤ k} ∧ ¬ i ∈ upTo (T.filter (· < k)) := by
    simp only [block, upTo, Set.mem_setOf_eq, Finset.mem_filter]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      rintro ⟨t, ⟨ht, htk⟩, hit⟩
      exact absurd (h2 t ht htk) (not_lt.2 hit)
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun t ht htk => lt_of_not_ge fun hit => h2 ⟨t, ⟨ht, htk⟩, hit⟩⟩
  simp only [Pi.sub_apply, Pi.mul_apply, ind_apply, e]
  split_ifs <;> simp_all

theorem ind_upTo_insert {A : Type} [CommRing A] {r : ℕ} (S : Finset (Fin r)) (a : Fin r) :
    (ind (upTo (insert a S)) : Fin r → A) = ind {i | i ≤ a} + ind (upTo S) - ind {i | i ≤ a} * ind (upTo S) := by
  classical
  funext i
  have e : i ∈ upTo (insert a S) ↔ i ∈ {i | i ≤ a} ∨ i ∈ upTo S := by
    simp only [upTo, Set.mem_setOf_eq, Finset.mem_insert]
    constructor
    · rintro ⟨k, hk | hk, hik⟩
      · exact Or.inl (hk ▸ hik)
      · exact Or.inr ⟨k, hk, hik⟩
    · rintro (h | ⟨k, hk, hik⟩)
      · exact ⟨a, Or.inl rfl, h⟩
      · exact ⟨k, Or.inr hk, hik⟩
  simp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply, ind_apply, e]
  split_ifs <;> simp_all

theorem sum_ind_block {A : Type} [CommRing A] {r : ℕ} (T : Finset (Fin r)) :
    ∑ k ∈ T, (ind (block T k) : Fin r → A) = ind (upTo T) := by
  classical
  funext i
  rw [Finset.sum_apply]
  by_cases hi : i ∈ upTo T
  · have hne : (T.filter (i ≤ ·)).Nonempty := by
      obtain ⟨k, hk, hik⟩ := hi
      exact ⟨k, Finset.mem_filter.2 ⟨hk, hik⟩⟩
    set k0 := (T.filter (i ≤ ·)).min' hne
    have hk0 : k0 ∈ T.filter (i ≤ ·) := Finset.min'_mem _ hne
    have hk0T : k0 ∈ T := (Finset.mem_filter.1 hk0).1
    have hik0 : i ≤ k0 := (Finset.mem_filter.1 hk0).2
    have hmin : ∀ t ∈ T, i ≤ t → k0 ≤ t := fun t ht hit => Finset.min'_le _ _ (Finset.mem_filter.2 ⟨ht, hit⟩)
    have hb : ∀ k ∈ T, (i ∈ block T k ↔ k = k0) := by
      intro k hk
      constructor
      · rintro ⟨h1, h2⟩
        refine le_antisymm ?_ (hmin k hk h1)
        by_contra hlt
        exact absurd (h2 k0 hk0T (lt_of_not_ge hlt)) (not_lt.2 hik0)
      · rintro rfl
        exact ⟨hik0, fun t ht htk => lt_of_not_ge fun hit => absurd (hmin t ht hit) (not_le.2 htk)⟩
    rw [Finset.sum_eq_single_of_mem k0 hk0T, ind_apply, ind_apply, if_pos ((hb k0 hk0T).2 rfl), if_pos hi]
    intro k hk hkk
    rw [ind_apply, if_neg fun h => hkk ((hb k hk).1 h)]
  · rw [ind_apply, if_neg hi]
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [ind_apply, if_neg fun h => hi ⟨k, hk, h.1⟩]

theorem ind_block_mul_ind_block {A : Type} [CommRing A] {r : ℕ} (T : Finset (Fin r)) {k l : Fin r} (hk : k ∈ T) (hl : l ∈ T) (hkl : k ≠ l) :
    (ind (block T k) : Fin r → A) * ind (block T l) = 0 := by
  classical
  funext i
  simp only [Pi.mul_apply, Pi.zero_apply, ind_apply]
  by_cases h1 : i ∈ block T k
  · by_cases h2 : i ∈ block T l
    · exfalso
      rcases lt_or_gt_of_ne hkl with h | h
      · exact absurd (h2.2 k hk h) (not_lt.2 h1.1)
      · exact absurd (h1.2 l hl h) (not_lt.2 h2.1)
    · rw [if_neg h2, mul_zero]
  · rw [if_neg h1, zero_mul]

theorem prX_ind_le {A : Type} [CommRing A] (s : A →+* A) {n r : ℕ} (J : Matrix (Fin n) (Fin n) A) (Z W : Matrix (Fin n) (Fin r) A)
    (k : Fin r) : prX s J Z W (ind {i | i ≤ k}) =
      Z.submatrix id (Fin.castLE k.2) * Formalism.UG.cT s (W.submatrix id (Fin.castLE k.2)) * J := by
  classical
  rw [prX]
  congr 1
  ext a b
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.submatrix_apply, id, Formalism.UG.cT, Matrix.transpose_apply,
    Matrix.map_apply, Matrix.of_apply]
  have e : (Finset.univ : Finset (Fin (k.val + 1))).image (Fin.castLE k.2) = Finset.univ.filter (· ≤ k) := by
    ext c
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨j, rfl⟩
      exact Fin.le_iff_val_le_val.2 (Nat.lt_succ_iff.1 j.2)
    · intro hc
      exact ⟨⟨c.val, Nat.lt_succ_of_le (Fin.le_iff_val_le_val.1 hc)⟩, rfl⟩
  rw [← Finset.sum_image (s := Finset.univ) (g := Fin.castLE k.2) (f := fun c => Z a c * s (W b c))
    (fun x _ y _ h => Fin.castLE_injective _ h), e, Finset.sum_filter]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [ind_apply]
  split_ifs with h <;> simp_all
end GlobalTheory.CompanionTheory.LeviGen

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
open Formalism.UG (cT)

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.LeviGen

open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

section Gen

variable {A : Type} [CommRing A] {s : A →+* A} {n r : ℕ} {J : Matrix (Fin n) (Fin n) A}
  {X Y : Matrix (Fin n) (Fin r) A}

theorem prj_add (d e : Fin r → A) : prj s J X Y (d + e) = prj s J X Y d + prj s J X Y e := by
  rw [prj, prj, prj, prX_add, prY_add]; abel

theorem prj_zero : prj s J X Y 0 = 0 := by rw [prj, prX_zero, prY_zero, add_zero]

theorem onPart_zero (G : Matrix (Fin n) (Fin n) A) : onPart 0 G = 1 := by simp [onPart]

theorem cT_sub_mul {m : ℕ} (Z W : Matrix (Fin n) (Fin r) A) (f : Fin m → Fin r) :
    cT s (W.submatrix id f) * J * Z.submatrix id f = (cT s W * J * Z).submatrix f f := by
  ext i j; simp [Matrix.mul_apply, cT]

theorem prX_mulVec_eq_zero {Z W : Matrix (Fin n) (Fin r) A} {I : Set (Fin r)} {y : Fin n → A}
    (hy : ∀ i ∈ I, ((cT s W * J) *ᵥ y) i = 0) : prX s J Z W (ind I) *ᵥ y = 0 := by
  classical
  have : diagonal (ind I) *ᵥ ((cT s W * J) *ᵥ y) = 0 := by
    funext i
    rw [mulVec_diagonal, ind_apply]
    by_cases hi : i ∈ I
    · rw [hy i hi, mul_zero]; rfl
    · rw [if_neg hi, zero_mul]; rfl
  rw [prX, Matrix.mul_assoc (Z * diagonal _), ← mulVec_mulVec, ← mulVec_mulVec, this, mulVec_zero]

theorem mulVec_col {m : ℕ} (M : Matrix (Fin n) (Fin n) A) (N : Matrix (Fin n) (Fin m) A) (i : Fin m) :
    M *ᵥ Nᵀ i = (M * N)ᵀ i := by
  funext a; simp [Matrix.mul_apply, mulVec, dotProduct]

end Gen

end GlobalTheory.CompanionTheory.LeviGen

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
open Formalism.UG (cT)

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.LeviGen

open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n r : ℕ}
  {J : Matrix (Fin n) (Fin n) E} {X Y : Matrix (Fin n) (Fin r) E}

theorem sigR_sigR (h : IsCMExt F E σ) (a : AF F ⊗[F] E) : sigR (AF F) σ (sigR (AF F) σ a) = a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul x e => simp [sigR, GlobalTheory.SiegelSet.sigma_sigma h]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

theorem cT_adMat {a b : ℕ} (Z : Matrix (Fin a) (Fin b) E) :
    cT (sigR (AF F) σ) (adMat F Z) = adMat F (cT (σ : E →+* E) Z) := rfl

theorem adMat_mul {a b c : ℕ} (M : Matrix (Fin a) (Fin b) E) (N : Matrix (Fin b) (Fin c) E) :
    adMat F (M * N) = adMat F M * adMat F N := Matrix.map_mul

theorem adMat_zero {a b : ℕ} : adMat F (0 : Matrix (Fin a) (Fin b) E) = 0 := by ext; simp [adMat]

theorem adMat_one {a : ℕ} : adMat F (1 : Matrix (Fin a) (Fin a) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)

theorem mat_mul_inv (g : GAd σ J) : (matHom _ σ J g).1 * (matHom _ σ J g⁻¹).1 = 1 := by
  rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]

theorem mat_inv_mul (g : GAd σ J) : (matHom _ σ J g⁻¹).1 * (matHom _ σ J g).1 = 1 := by
  rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]

theorem mat_unitary (g : GAd σ J) :
    cT (sigR (AF F) σ) (matHom _ σ J g).1 * adMat F J * (matHom _ σ J g).1 = adMat F J := g.2

def mkPt (M N : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) (h1 : M * N = 1) (h2 : N * M = 1)
    (hu : cT (sigR (AF F) σ) M * adMat F J * M = adMat F J) : GAd σ J := ⟨⟨M, N, h1, h2⟩, hu⟩

theorem exists_onPart (g : GAd σ J) {Q : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)} (hQ : Q * Q = Q)
    (hQJ : cT (sigR (AF F) σ) Q * adMat F J = adMat F J * Q)
    (hc : (matHom _ σ J g).1 * Q = Q * (matHom _ σ J g).1) :
    ∃ m : GAd σ J, (matHom _ σ J m).1 = onPart Q (matHom _ σ J g).1 ∧
      (matHom _ σ J m⁻¹).1 = onPart Q (matHom _ σ J g⁻¹).1 :=
  ⟨mkPt _ _ (onPart_inv hQ hc (mat_mul_inv g) (mat_inv_mul g))
    (onPart_inv hQ (comm_inv hc (mat_mul_inv g) (mat_inv_mul g)) (mat_inv_mul g) (mat_mul_inv g))
    (onPart_unitary hQ hQJ hc (mat_unitary g) (mat_mul_inv g) (mat_inv_mul g)), rfl, rfl⟩

variable (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y)
include h hJ hW

theorem adFrame : cT (sigR (AF F) σ) (adMat F X) * adMat F J * adMat F X = 0 ∧
    cT (sigR (AF F) σ) (adMat F Y) * adMat F J * adMat F Y = 0 ∧
    cT (sigR (AF F) σ) (adMat F X) * adMat F J * adMat F Y = 1 ∧
    cT (sigR (AF F) σ) (adMat F Y) * adMat F J * adMat F X = 1 ∧
    cT (sigR (AF F) σ) (adMat F J) = adMat F J := by
  simp only [cT_adMat, ← adMat_mul, hW.xx, hW.yy, hW.xy, yx h hJ hW, adMat_zero, adMat_one]
  refine ⟨trivial, trivial, trivial, trivial, congrArg _ (Matrix.ext fun i j => hJ.1 i j)⟩

end Adelic

end GlobalTheory.CompanionTheory.LeviGen

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
open Formalism.UG (cT)

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.LeviGen

open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

section Levi

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n r : ℕ}
  {J : Matrix (Fin n) (Fin n) E} {X Y : Matrix (Fin n) (Fin r) E}
  (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y)
include h hJ hW

theorem isComm_of_mem_levi {T : Finset (Fin r)} {g : GAd σ J} (hg : g ∈ levi σ J X Y T) {j : Fin r} (hj : j ∈ T) :
    IsComm (sigR (AF F) σ) (adMat F J) (adMat F X) (adMat F Y) (matHom _ σ J g).1 (ind {i | i ≤ j}) := by
  obtain ⟨fxx, fyy, fxy, fyx, fJ⟩ := adFrame h hJ hW
  have hm := Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hg j) hj
  obtain ⟨⟨B, -, eB⟩, ⟨C, -, eC⟩⟩ := Subgroup.mem_inf.1 hm
  have inj := Fin.castLE_injective j.2
  have h1 : cT (sigR (AF F) σ) ((adMat F Y).submatrix id (Fin.castLE j.2)) * adMat F J *
      (adMat F X).submatrix id (Fin.castLE j.2) = 1 := by rw [cT_sub_mul, fyx, Matrix.submatrix_one _ inj]
  have h2 : cT (sigR (AF F) σ) ((adMat F X).submatrix id (Fin.castLE j.2)) * adMat F J *
      (adMat F Y).submatrix id (Fin.castLE j.2) = 1 := by rw [cT_sub_mul, fxy, Matrix.submatrix_one _ inj]
  refine ⟨?_, ?_⟩
  · rw [prX_ind_le]
    exact comm_of_frame h1 (mat_unitary g) (mat_mul_inv g) (mat_inv_mul g) eB eC
  · change _ * prX _ _ (adMat F Y) (adMat F X) _ = prX _ _ (adMat F Y) (adMat F X) _ * _
    rw [prX_ind_le]
    exact comm_of_frame h2 (mat_unitary g) (mat_mul_inv g) (mat_inv_mul g) eC eB

theorem mem_levi_of_isComm {T : Finset (Fin r)} {m : GAd σ J}
    (hm : ∀ j ∈ T, IsComm (sigR (AF F) σ) (adMat F J) (adMat F X) (adMat F Y) (matHom _ σ J m).1 (ind {i | i ≤ j}))
    (hm' : ∀ j ∈ T, IsComm (sigR (AF F) σ) (adMat F J) (adMat F X) (adMat F Y) (matHom _ σ J m⁻¹).1 (ind {i | i ≤ j})) :
    m ∈ levi σ J X Y T := by
  obtain ⟨fxx, fyy, fxy, fyx, fJ⟩ := adFrame h hJ hW
  refine Subgroup.mem_iInf.2 fun j => Subgroup.mem_iInf.2 fun hj => Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · have inj := Fin.castLE_injective j.2
    have h1 : cT (sigR (AF F) σ) ((adMat F Y).submatrix id (Fin.castLE j.2)) * adMat F J *
        (adMat F X).submatrix id (Fin.castLE j.2) = 1 := by rw [cT_sub_mul, fyx, Matrix.submatrix_one _ inj]
    have c1 := (hm j hj).1
    have c2 := (hm' j hj).1
    rw [prX_ind_le] at c1 c2
    obtain ⟨B, eB⟩ := exists_unit_of_comm h1 (mat_mul_inv m) c1 c2
    exact ⟨B, Subgroup.mem_top _, eB⟩
  · have inj := Fin.castLE_injective j.2
    have h2 : cT (sigR (AF F) σ) ((adMat F X).submatrix id (Fin.castLE j.2)) * adMat F J *
        (adMat F Y).submatrix id (Fin.castLE j.2) = 1 := by rw [cT_sub_mul, fxy, Matrix.submatrix_one _ inj]
    have c1 : _ * prX _ _ (adMat F Y) (adMat F X) _ = prX _ _ (adMat F Y) (adMat F X) _ * _ := (hm j hj).2
    have c2 : _ * prX _ _ (adMat F Y) (adMat F X) _ = prX _ _ (adMat F Y) (adMat F X) _ * _ := (hm' j hj).2
    rw [prX_ind_le] at c1 c2
    obtain ⟨B, eB⟩ := exists_unit_of_comm h2 (mat_mul_inv m) c1 c2
    exact ⟨B, Subgroup.mem_top _, eB⟩

theorem isComm_upTo {T : Finset (Fin r)} {g : GAd σ J} (hg : g ∈ levi σ J X Y T) {S : Finset (Fin r)} (hS : S ⊆ T) :
    IsComm (sigR (AF F) σ) (adMat F J) (adMat F X) (adMat F Y) (matHom _ σ J g).1 (ind (upTo S)) := by
  obtain ⟨fxx, fyy, fxy, fyx, fJ⟩ := adFrame h hJ hW
  induction S using Finset.induction_on with
  | empty =>
    have e : upTo (∅ : Finset (Fin r)) = ∅ := by ext; simp [upTo]
    rw [e, ind_empty]; exact isComm_zero
  | insert a S _ ih =>
    have ha := isComm_of_mem_levi h hJ hW hg (hS (Finset.mem_insert_self a S))
    have hS' := ih ((Finset.subset_insert a S).trans hS)
    rw [ind_upTo_insert]
    exact (ha.add hS').sub (ha.mul fxy fyx hS')

theorem isComm_block {T : Finset (Fin r)} {g : GAd σ J} (hg : g ∈ levi σ J X Y T) {k : Fin r} (hk : k ∈ T) :
    IsComm (sigR (AF F) σ) (adMat F J) (adMat F X) (adMat F Y) (matHom _ σ J g).1 (ind (block T k)) := by
  obtain ⟨fxx, fyy, fxy, fyx, fJ⟩ := adFrame h hJ hW
  have hk' := isComm_of_mem_levi h hJ hW hg hk
  rw [ind_block_eq]
  exact hk'.sub (hk'.mul fxy fyx (isComm_upTo h hJ hW hg (Finset.filter_subset _ T)))

end Levi

end GlobalTheory.CompanionTheory.LeviGen

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
open Formalism.UG (cT)

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.LeviGen

open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

section Parts

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n r : ℕ}
  {J : Matrix (Fin n) (Fin n) E} {X Y : Matrix (Fin n) (Fin r) E}
  (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y)
include h hJ hW

theorem exists_glPart {T : Finset (Fin r)} {g : GAd σ J} (hg : g ∈ levi σ J X Y T) {k : Fin r} (hk : k ∈ T) :
    ∃ m ∈ glPart σ J X Y T k, (matHom _ σ J m).1 =
      onPart (prj (sigR (AF F) σ) (adMat F J) (adMat F X) (adMat F Y) (ind (block T k))) (matHom _ σ J g).1 := by
  obtain ⟨fxx, fyy, fxy, fyx, fJ⟩ := adFrame h hJ hW
  set P := prj (sigR (AF F) σ) (adMat F J) (adMat F X) (adMat F Y) (ind (block T k))
  have hP : P * P = P := by rw [prj_mul_prj fxx fyy fxy fyx, ind_mul_self]
  have hPJ : cT (sigR (AF F) σ) P * adMat F J = adMat F J * P := cT_prj_mul (sigR_sigR h) fJ (map_ind _ _)
  obtain ⟨m, e1, e2⟩ := exists_onPart g hP hPJ (isComm_block h hJ hW hg hk).comm_prj
  refine ⟨m, Subgroup.mem_inf.2 ⟨?_, fun y hy => ?_⟩, e1⟩
  · refine mem_levi_of_isComm h hJ hW (fun j hj => ?_) (fun j hj => ?_)
    · rw [e1]; exact isComm_onPart fxx fyy fxy fyx (isComm_of_mem_levi h hJ hW hg hj)
    · rw [e2]; exact isComm_onPart fxx fyy fxy fyx (isComm_of_mem_levi h hJ hW (inv_mem hg) hj)
  · obtain ⟨hy1, hy2⟩ := Submodule.mem_inf.1 hy
    have z1 : prX (sigR (AF F) σ) (adMat F J) (adMat F X) (adMat F Y) (ind (block T k)) *ᵥ y = 0 :=
      prX_mulVec_eq_zero fun i hi => by
        have := LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hy2 i) hi)
        rw [cT_adMat, ← adMat_mul]; exact this
    have z2 : prX (sigR (AF F) σ) (adMat F J) (adMat F Y) (adMat F X) (ind (block T k)) *ᵥ y = 0 :=
      prX_mulVec_eq_zero fun i hi => by
        have := LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hy1 i) hi)
        rw [cT_adMat, ← adMat_mul]; exact this
    have z : P *ᵥ y = 0 := by
      simp only [P, prj, add_mulVec]; rw [z1]; exact (zero_add _).trans z2
    rw [e1, onPart, add_mulVec, sub_mulVec, one_mulVec, z, ← mulVec_mulVec, z, mulVec_zero, sub_zero, add_zero]

theorem exists_uPart {T : Finset (Fin r)} {g : GAd σ J} (hg : g ∈ levi σ J X Y T) :
    ∃ m ∈ uPart σ J X Y T, (matHom _ σ J m).1 =
      onPart (1 - prj (sigR (AF F) σ) (adMat F J) (adMat F X) (adMat F Y) (ind (upTo T))) (matHom _ σ J g).1 := by
  obtain ⟨fxx, fyy, fxy, fyx, fJ⟩ := adFrame h hJ hW
  set P := prj (sigR (AF F) σ) (adMat F J) (adMat F X) (adMat F Y) (ind (upTo T))
  have hP : P * P = P := by rw [prj_mul_prj fxx fyy fxy fyx, ind_mul_self]
  have hPJ : cT (sigR (AF F) σ) P * adMat F J = adMat F J * P := cT_prj_mul (sigR_sigR h) fJ (map_ind _ _)
  have hc : (matHom _ σ J g).1 * P = P * (matHom _ σ J g).1 := (isComm_upTo h hJ hW hg subset_rfl).comm_prj
  have hQ : (1 - P) * (1 - P) = 1 - P := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hP, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul]; abel
  have hQJ : cT (sigR (AF F) σ) (1 - P) * adMat F J = adMat F J * (1 - P) := by
    rw [cT_sub', Formalism.UG.cT_one, Matrix.sub_mul, hPJ, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one]
  have hcQ : (matHom _ σ J g).1 * (1 - P) = (1 - P) * (matHom _ σ J g).1 := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hc, Matrix.mul_one, Matrix.one_mul]
  obtain ⟨m, e1, -⟩ := exists_onPart g hQ hQJ hcQ
  refine ⟨m, fun y hy => ?_, e1⟩
  have hcol : ∀ (C : Matrix (Fin n) (Fin r) E), P * adMat F C = adMat F C * diagonal (ind (upTo T)) →
      colSpan F C (upTo T) ≤ LinearMap.ker (1 - P).mulVecLin := fun C hC => by
    classical
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, hi, rfl⟩
    change (1 - P) *ᵥ (adMat F C)ᵀ i = 0
    rw [mulVec_col, Matrix.sub_mul, Matrix.one_mul, hC]
    funext a
    rw [Matrix.transpose_apply, Matrix.sub_apply]
    erw [Matrix.mul_diagonal]
    rw [ind_apply, if_pos hi, mul_one, sub_self]
    rfl
  have hX : P * adMat F X = adMat F X * diagonal (ind (upTo T)) := by
    simp only [P, prj, Matrix.add_mul, prX_mul_X fyx, prY_mul_X fxx, add_zero]
    rfl
  have hY : P * adMat F Y = adMat F Y * diagonal (ind (upTo T)) := by
    simp only [P, prj, Matrix.add_mul, prX_mul_Y fyy, prY_mul_Y fxy, zero_add]
    rfl
  have z : (1 - P) *ᵥ y = 0 := LinearMap.mem_ker.1 (sup_le (hcol X hX) (hcol Y hY) hy)
  rw [e1, onPart, add_mulVec, sub_mulVec, one_mulVec, z, ← mulVec_mulVec, z, mulVec_zero, sub_zero, add_zero]

end Parts

end GlobalTheory.CompanionTheory.LeviGen

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
open Formalism.UG (cT)

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.LeviGen

open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n r : ℕ}
  {J : Matrix (Fin n) (Fin n) E} {X Y : Matrix (Fin n) (Fin r) E}

section Var

variable (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y)
include h hJ hW

theorem isComm_sum {T : Finset (Fin r)} {g : GAd σ J} (hg : g ∈ levi σ J X Y T) {S : Finset (Fin r)} (hS : S ⊆ T) :
    IsComm (sigR (AF F) σ) (adMat F J) (adMat F X) (adMat F Y) (matHom _ σ J g).1 (∑ k ∈ S, ind (block T k)) := by
  induction S using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact isComm_zero
  | insert a S ha ih =>
    rw [Finset.sum_insert ha]
    exact (isComm_block h hJ hW hg (hS (Finset.mem_insert_self a S))).add (ih ((Finset.subset_insert a S).trans hS))

theorem exists_sum {T : Finset (Fin r)} {g : GAd σ J} (hg : g ∈ levi σ J X Y T) {S : Finset (Fin r)} (hS : S ⊆ T) :
    ∃ m ∈ ⨆ i, part σ J X Y T i, (matHom _ σ J m).1 =
      onPart (prj (sigR (AF F) σ) (adMat F J) (adMat F X) (adMat F Y) (∑ k ∈ S, ind (block T k))) (matHom _ σ J g).1 := by
  obtain ⟨fxx, fyy, fxy, fyx, fJ⟩ := adFrame h hJ hW
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨1, one_mem _, ?_⟩
    rw [Finset.sum_empty, prj_zero, onPart_zero, map_one, Units.val_one]
  | insert a S ha ih =>
    have haT := hS (Finset.mem_insert_self a S)
    have hST := (Finset.subset_insert a S).trans hS
    obtain ⟨m, hm, em⟩ := ih hST
    obtain ⟨ma, hma, ema⟩ := exists_glPart h hJ hW hg haT
    have hle : part σ J X Y T (some (⟨a, haT⟩ : {k // k ∈ T})) ≤ ⨆ i, part σ J X Y T i := le_iSup _ _
    refine ⟨ma * m, mul_mem (hle hma) hm, ?_⟩
    have h0 := prj_mul_prj (s := sigR (AF F) σ) (J := adMat F J) fxx fyy fxy fyx (ind (block T a)) (∑ k ∈ S, ind (block T k))
    have hz : (ind (block T a) : Fin r → AF F ⊗[F] E) * ∑ k ∈ S, ind (block T k) = 0 := by
      rw [Finset.mul_sum]; exact Finset.sum_eq_zero fun k hk => ind_block_mul_ind_block T haT (hST hk) (fun e => ha (e ▸ hk))
    rw [hz, prj_zero] at h0
    rw [map_mul, Units.val_mul, ema, em, onPart_add h0 (isComm_sum h hJ hW hg hST).comm_prj, ← prj_add,
      Finset.sum_insert ha]

end Var

theorem levi_eq_iSup_part : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ)
    (X Y : Matrix (Fin n) (Fin r) E), GlobalTheory.SiegelSet.IsWittFrame σ J X Y → ∀ T : Finset (Fin r),
    levi σ J X Y T = ⨆ i, part σ J X Y T i := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW T
  obtain ⟨fxx, fyy, fxy, fyx, fJ⟩ := adFrame h hJ hW
  refine le_antisymm (fun g hg => ?_) (iSup_le fun i => ?_)
  · obtain ⟨mT, hmT, emT⟩ := exists_sum h hJ hW hg (subset_refl T)
    obtain ⟨mW, hmW, emW⟩ := exists_uPart h hJ hW hg
    rw [sum_ind_block] at emT
    set P := prj (sigR (AF F) σ) (adMat F J) (adMat F X) (adMat F Y) (ind (upTo T)) with hPdef
    have hP : P * P = P := by rw [hPdef, prj_mul_prj fxx fyy fxy fyx, ind_mul_self]
    have hc : (matHom _ σ J g).1 * P = P * (matHom _ σ J g).1 := (isComm_upTo h hJ hW hg subset_rfl).comm_prj
    have h0 : (1 - P) * P = 0 := by rw [Matrix.sub_mul, hP, Matrix.one_mul, sub_self]
    have e : (matHom _ σ J (mW * mT)).1 = (matHom _ σ J g).1 := by
      rw [map_mul, Units.val_mul, emW, emT, onPart_add h0 hc, sub_add_cancel, onPart_one_left]
    have : mW * mT = g := Subtype.ext (Units.ext e)
    rw [← this]
    exact mul_mem (Subgroup.mem_iSup_of_mem none hmW) hmT
  · cases i with
    | none =>
      intro m hm
      have key : ∀ (C : Matrix (Fin n) (Fin r) E) (k : Fin r), k ∈ T →
          (∀ y ∈ colSpan F C (upTo T), (matHom _ σ J m).1 *ᵥ y = y) → m ∈ frameStab σ J (initCols C k) ⊤ := by
        intro C k hk hC
        refine ⟨1, Subgroup.mem_top _, ?_⟩
        rw [Units.val_one, Matrix.mul_one]
        refine Matrix.transpose_injective (funext fun j => ?_)
        rw [← mulVec_col]
        exact hC _ (Submodule.subset_span ⟨Fin.castLE k.2 j, ⟨k, hk, Fin.le_iff_val_le_val.2 (Nat.lt_succ_iff.1 j.2)⟩, rfl⟩)
      refine Subgroup.mem_iInf.2 fun k => Subgroup.mem_iInf.2 fun hk => Subgroup.mem_inf.2
        ⟨key X k hk fun y hy => hm y (Submodule.mem_sup_left hy),
          key Y k hk fun y hy => hm y (Submodule.mem_sup_right hy)⟩
    | some k => exact inf_le_left

end Main

end GlobalTheory.CompanionTheory.LeviGen
