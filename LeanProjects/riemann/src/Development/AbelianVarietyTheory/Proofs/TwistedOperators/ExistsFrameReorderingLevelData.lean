import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeConjReord

open Matrix Formalism.L2.Herm

section Perm

variable {n : ℕ}

theorem sum_perm_one (R : Type) [CommRing R] (f : Equiv.Perm (Fin n)) (i j : Fin n) :
    (∑ k, if f k = j then (if i = f k then (1 : R) else 0) else 0) = if i = j then 1 else 0 := by
  rw [Equiv.sum_comp f (fun m => if m = j then (if i = m then (1 : R) else 0) else 0)]
  simp

def pmat (R : Type) [CommRing R] (f : Equiv.Perm (Fin n)) : GL (Fin n) R where
  val := (1 : Matrix (Fin n) (Fin n) R).submatrix id f
  inv := (1 : Matrix (Fin n) (Fin n) R).submatrix id f.symm
  val_inv := by
    ext i j
    simpa [Matrix.mul_apply, Matrix.one_apply, Equiv.eq_symm_apply] using sum_perm_one R f i j
  inv_val := by
    ext i j
    simpa [Matrix.mul_apply, Matrix.one_apply, Equiv.eq_symm_apply] using sum_perm_one R f.symm i j

theorem pmat_inv (R : Type) [CommRing R] (f : Equiv.Perm (Fin n)) : (pmat R f)⁻¹ = pmat R f.symm := by
  ext i j
  rfl

theorem conj_pmat (R : Type) [CommRing R] (f : Equiv.Perm (Fin n)) (g : GL (Fin n) R) (a b : Fin n) :
    (((pmat R f)⁻¹ * g * pmat R f : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) a b = (g : Matrix (Fin n) (Fin n) R) (f a) (f b) := by
  rw [pmat_inv, Units.val_mul, Units.val_mul]
  show ((1 : Matrix (Fin n) (Fin n) R).submatrix id f.symm * (g : Matrix (Fin n) (Fin n) R) *
    (1 : Matrix (Fin n) (Fin n) R).submatrix id f) a b = _
  simp [Matrix.mul_apply, Matrix.one_apply, Equiv.eq_symm_apply]

theorem bc_pmat {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (f : Equiv.Perm (Fin n)) :
    Formalism.UG.bc φ (pmat R f) = pmat S f := by
  apply Units.ext
  ext i j
  simp only [Formalism.UG.bc, pmat] at *
  by_cases h : i = f j <;> simp [Matrix.one_apply, h]

theorem pmat_mulVec (R : Type) [CommRing R] (f : Equiv.Perm (Fin n)) (v : Fin n → R) :
    ((pmat R f.symm : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) *ᵥ v = fun i => v (f i) := by
  funext i
  show ((1 : Matrix (Fin n) (Fin n) R).submatrix id f.symm *ᵥ v) i = v (f i)
  simp [Matrix.mulVec, dotProduct, Matrix.one_apply, Equiv.eq_symm_apply]

end Perm

section Frame

open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem frGL_mul_int (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (σ y : GL (Fin n) (intAf F E)) :
    frGL (β * intGL F E n σ) y = frGL β (σ * y * σ⁻¹) := by
  show β * intGL F E n σ * intGL F E n y * (β * intGL F E n σ)⁻¹ = β * intGL F E n (σ * y * σ⁻¹) * β⁻¹
  rw [map_mul, map_mul, map_inv]
  group

theorem St_mul_int (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (σ : GL (Fin n) (intAf F E)) :
    St (β * intGL F E n σ) = St β := by
  ext x
  simp only [St, MonoidHom.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨σ * y * σ⁻¹, (frGL_mul_int β σ y).symm⟩
  · rintro ⟨y, rfl⟩
    refine ⟨σ⁻¹ * y * σ, ?_⟩
    rw [frGL_mul_int]
    congr 1
    group

theorem redFn_mul_int (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (σ : GL (Fin n) (intAf F E)) (PP : Pl E)
    (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
    redFn (β * intGL F E n σ) PP x = (Formalism.UG.bc (resS F PP) σ)⁻¹ * redFn β PP x * Formalism.UG.bc (resS F PP) σ := by
  by_cases hx : x ∈ St β
  · obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hx
    have hy : frGL β y = frGL (β * intGL F E n σ) (σ⁻¹ * y * σ) := by
      rw [frGL_mul_int]
      congr 1
      group
    rw [redFn_frGL β PP y, hy, redFn_frGL]
    simp only [map_mul, map_inv]
  · have hx' : x ∉ St (β * intGL F E n σ) := by rwa [St_mul_int]
    simp [redFn, ext1, hx, hx']

theorem isFrame_mul_pmat {β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)} (h : IsFrame β Λ)
    (f : Equiv.Perm (Fin n)) : IsFrame (β * intGL F E n (pmat _ f)) Λ := by
  unfold Formalism.L2.DIV.IsFrame at h ⊢
  intro x
  have e : (((β * intGL F E n (pmat _ f))⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
      Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ x =
      fun i => (((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
        Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ x) (f i) := by
    rw [_root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec, ← map_inv (intGL F E n) (pmat _ f), pmat_inv]
    unfold intGL
    rw [bc_pmat, pmat_mulVec]
  rw [h x, e]
  exact ⟨fun hx i => hx (f i), fun hx i => by simpa using hx (f.symm i)⟩

end Frame

section Level

variable {D : D7}

theorem rankBlock_val_eq_submatrix_of_le_rank {κ : Type} [CommRing κ] {n r : ℕ} (hr : r ≤ n) (hn : n ≤ r) (M : GL (Fin n) κ) :
    ((upperLeftBlock hr M : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) =
      (M : Matrix (Fin n) (Fin n) κ).submatrix (Fin.castLE hr) (Fin.castLE hr) := by
  apply upper_block_val_submatrix
  rw [mem_blockTri]
  intro i j hij
  have hi : i.val < r := lt_of_lt_of_le i.isLt hn
  simp [blk2, hi] at hij

theorem blockTri_all {κ : Type} [CommRing κ] {n r : ℕ} (t : ℕ) (hn : n ≤ r) (M : GL (Fin n) κ) :
    M ∈ blockTri (blkOf r t) := by
  rw [mem_blockTri]
  intro i j hij
  have hi : i.val < r := lt_of_lt_of_le i.isLt hn
  simp [blkOf, hi] at hij

def fperm {n r : ℕ} (hr : r ≤ n) (hn : n ≤ r) (π : Equiv.Perm (Fin r)) : Equiv.Perm (Fin n) :=
  ((finCongr (le_antisymm hr hn)).symm.trans π.symm).trans (finCongr (le_antisymm hr hn))

theorem fperm_castLE {n r : ℕ} (hr : r ≤ n) (hn : n ≤ r) (π : Equiv.Perm (Fin r)) (a : Fin r) :
    fperm hr hn π (Fin.castLE hr (π a)) = Fin.castLE hr a := by
  have h1 : (finCongr (le_antisymm hr hn)).symm (Fin.castLE hr (π a)) = π a := Fin.ext (by simp)
  simp only [fperm, Equiv.trans_apply, h1, Equiv.symm_apply_apply]
  exact Fin.ext (by simp)

theorem reord_rTup {n : ℕ} (L : LevDat D.host.E ℂ n) (hn : n ≤ L.r) (β : GL (Fin n) (EAf D))
    (π : Equiv.Perm (Fin L.r)) (x : GL (Fin n) (EAf D)) :
    reord π (rTup (β * intGL _ _ n (pmat _ (fperm L.hr hn π))) L x) = rTup β L x := by
  funext PP
  apply Units.ext
  ext a b
  show (upperLeftBlock L.hr (redFn (β * intGL _ _ n (pmat _ (fperm L.hr hn π))) PP.1 x)).1 (π a) (π b) =
    (upperLeftBlock L.hr (redFn β PP.1 x)).1 a b
  rw [rankBlock_val_eq_submatrix_of_le_rank L.hr hn, rankBlock_val_eq_submatrix_of_le_rank L.hr hn, redFn_mul_int, bc_pmat]
  simp only [Matrix.submatrix_apply]
  rw [conj_pmat, fperm_castLE, fperm_castLE]

theorem rank_zeroth_component_eq : (Yc D 0).rank ≤ D.R.r := by
  have h := D.sp.Y_rank 0 (Nat.zero_le _)
  show (D.sp.Y (min 0 D.R.m)).rank ≤ D.R.r
  rw [Nat.zero_min, h]
  show D.R.r + 0 * D.R.t ≤ D.R.r
  simp

end Level

section Main

variable {D : D7}

def r0 {T : Type} (Lc : LevCh D T) (β : GL (Fin (Yc D 0).rank) (EAf D)) (x : GL (Fin (Yc D 0).rank) (EAf D)) :
    G0 Lc.Pg D.R.r :=
  fun PP => upperLeftBlock (r_le_Y 0) (redFn β PP.1 x)

theorem mem_levelSubgroup_principalDatum_iff {T : Type} (Lc : LevCh D T) (P : LevelP Lc.Pg D.R.r ℂ) (β : GL (Fin (Yc D 0).rank) (EAf D))
    (κ : GA D (Yc D 0)) :
    κ ∈ levS (Yc D 0) β (Lc.dat0 P) ↔
      (κ ∈ GfC (Yc D 0) ∧ finE (Yc D 0) κ ∈ UA D.sp.cm (Yc D 0).gram ∧ finE (Yc D 0) κ ∈ St β) ∧
        r0 Lc β (finE (Yc D 0) κ) ∈ P.H := by
  have hP : (Lc.dat0 P).P = P := by simp [LevCh.dat0, datY]
  have hblk : ∀ PP ∈ (Lc.dat0 P).Pg,
      redFn β PP (finE (Yc D 0) κ) ∈ blockTri (blkOf (Lc.dat0 P).r (Lc.dat0 P).t) :=
    fun PP _ => blockTri_all _ (rank_zeroth_component_eq (D := D)) _
  have hQ : ∀ PP ∈ (Lc.dat0 P).Q, redFn β PP (finE (Yc D 0) κ) ∈ blockTri (blk2 (Lc.dat0 P).r) := by
    intro PP h
    simp [LevCh.dat0, datY] at h
  rw [Formalism.IndefR.Links.levS, Formalism.IndefR.Lev.levG, SetLike.mem_coe, Formalism.IndefR.Lev.mem_levA, Formalism.L2.DIV.mem_lev,
    Formalism.L2.DIV.mem_parLev, hP]
  exact ⟨fun ⟨h1, ⟨h2, h3, _, _⟩, h4⟩ => ⟨⟨h1, h2, h3⟩, h4⟩,
    fun ⟨⟨h1, h2, h3⟩, h4⟩ => ⟨h1, ⟨h2, h3, hblk, hQ⟩, h4⟩⟩

theorem principalRowLevelCharacter_trivial {T : Type} (Lc : LevCh D T) (P : LevelP Lc.Pg D.R.r ℂ) (β : GL (Fin (Yc D 0).rank) (EAf D))
    (κ : GA D (Yc D 0)) :
    levChi (Yc D 0) β (Lc.dat0 P) κ = ((ext1 P.H P.chi (r0 Lc β (finE (Yc D 0) κ)) : ℂˣ) : ℂ) := by
  have hs : (Lc.dat0 P).s = 0 := rfl
  have hQ : (Lc.dat0 P).Q = ∅ := rfl
  have hP : (Lc.dat0 P).P = P := by simp [LevCh.dat0, datY]
  rw [Formalism.IndefR.Lev.levChi, levFn, hs, hQ, hP]
  simp only [Finset.range_zero, Finset.prod_empty, Finset.prod_const_one, mul_one]
  rfl

theorem level_eq_of_reord {T : Type} (Lc : LevCh D T) (P P' : LevelP Lc.Pg D.R.r ℂ) (π : Equiv.Perm (Fin D.R.r))
    (hH : ∀ g, g ∈ P.H ↔ reord π g ∈ P'.H) (hchi : ∀ g hg hg', P.chi ⟨g, hg⟩ = P'.chi ⟨reord π g, hg'⟩)
    (β₂ β₃ : GL (Fin (Yc D 0).rank) (EAf D)) (hSt : St β₂ = St β₃)
    (hkey : ∀ x, reord π (r0 Lc β₂ x) = r0 Lc β₃ x) (κ : GA D (Yc D 0)) :
    (κ ∈ levS (Yc D 0) β₂ (Lc.dat0 P) ↔ κ ∈ levS (Yc D 0) β₃ (Lc.dat0 P')) ∧
      levChi (Yc D 0) β₂ (Lc.dat0 P) κ = levChi (Yc D 0) β₃ (Lc.dat0 P') κ := by
  refine ⟨?_, ?_⟩
  · rw [mem_levelSubgroup_principalDatum_iff, mem_levelSubgroup_principalDatum_iff, hSt, hH, hkey]
  · rw [principalRowLevelCharacter_trivial, principalRowLevelCharacter_trivial]
    by_cases hg : r0 Lc β₂ (finE (Yc D 0) κ) ∈ P.H
    · have hg' : r0 Lc β₃ (finE (Yc D 0) κ) ∈ P'.H := by
        rw [← hkey]
        exact (hH _).1 hg
      have e : (⟨reord π (r0 Lc β₂ (finE (Yc D 0) κ)), (hH _).1 hg⟩ : P'.H) = ⟨r0 Lc β₃ (finE (Yc D 0) κ), hg'⟩ :=
        Subtype.ext (hkey _)
      rw [extendOne_of_mem _ hg, extendOne_of_mem _ hg', hchi _ hg ((hH _).1 hg), e]
    · have hg' : r0 Lc β₃ (finE (Yc D 0) κ) ∉ P'.H := by
        rw [← hkey]
        exact fun h => hg ((hH _).2 h)
      unfold ext1
      rw [dif_neg hg, dif_neg hg']

end Main

theorem exists_frame_reord : ∀ {D : D7} {T : Type} (Lc : LevCh D T) (P P' : LevelP Lc.Pg D.R.r ℂ) (π : Equiv.Perm (Fin D.R.r)), (∀ g, g ∈ P.H ↔ reord π g ∈ P'.H) → (∀ g hg hg', P.chi ⟨g, hg⟩ = P'.chi ⟨reord π g, hg'⟩) → ∀ β₃ : GL (Fin (Yc D 0).rank) (EAf D), IsFrame β₃ (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → ∃ β₂ : GL (Fin (Yc D 0).rank) (EAf D), IsFrame β₂ (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) ∧ ∀ κ : GA D (Yc D 0), (κ ∈ levS (Yc D 0) β₂ (Lc.dat0 P) ↔ κ ∈ levS (Yc D 0) β₃ (Lc.dat0 P')) ∧ levChi (Yc D 0) β₂ (Lc.dat0 P) κ = levChi (Yc D 0) β₃ (Lc.dat0 P') κ := by
  intro D T Lc P P' π hH hchi β₃ hβ
  exact ⟨β₃ * intGL _ _ _ (pmat _ (fperm (Lc.dat0 P).hr (rank_zeroth_component_eq (D := D)) π)), isFrame_mul_pmat hβ _,
    fun κ => level_eq_of_reord Lc P P' π hH hchi _ β₃ (St_mul_int _ _)
      (fun x => reord_rTup (Lc.dat0 P) (rank_zeroth_component_eq (D := D)) β₃ π x) κ⟩

end GlobalTheory.SeeConjReord
