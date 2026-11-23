import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AdaptSelf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormGeometrySummary

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.DegAsm.AdaptInv
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} in
theorem _root_.GlobalTheory.DegAsm.AdaptInv.xa_mono (F : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r) {a b : ℕ} (h : a ≤ b) : F.Xa a ≤ F.Xa b :=
  _root_.Formalism.HermitianLatticeCounting.P.Xa_mono F h

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} in
theorem _root_.GlobalTheory.DegAsm.AdaptInv.e_mem_xa (F : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r) (b : Fin r) {a : ℕ} (h : b.val < a) :
    F.e b.castSucc ∈ F.Xa a :=
  _root_.Formalism.HermitianLatticeCounting.P.e_mem_Xa F b h

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} in
private theorem Xa_eq_span_e_castSucc (F : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r) (n : ℕ) :
    F.Xa n = Submodule.span K ((fun b : Fin r => F.e b.castSucc) '' {b | b.val < n}) := rfl

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} in
private theorem sameGr_e_sub_mem_Xa {F G : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r} (h : _root_.GlobalTheory.DegAsm.SameGr F G)
    (a : Fin (r + 1)) : G.e a - F.e a ∈ F.Xa a := by
  unfold _root_.GlobalTheory.DegAsm.SameGr at h
  exact h a

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} in
theorem _root_.GlobalTheory.DegAsm.AdaptInv.xa_eq {F G : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r} (h : _root_.GlobalTheory.DegAsm.SameGr F G) (n : ℕ) :
    G.Xa n = F.Xa n := by
  have key : ∀ n, F.Xa n ≤ G.Xa n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rw [Xa_eq_span_e_castSucc F n, Submodule.span_le]
      rintro _ ⟨b, hb, rfl⟩
      have hd := sameGr_e_sub_mem_Xa h b.castSucc
      simp only [Fin.coe_castSucc] at hd
      have h1 : G.e b.castSucc ∈ G.Xa n := _root_.Formalism.HermitianLatticeCounting.P.e_mem_Xa G b hb
      have h2 : G.e b.castSucc - F.e b.castSucc ∈ G.Xa n := _root_.Formalism.HermitianLatticeCounting.P.Xa_mono G (le_of_lt hb) (ih b hb hd)
      have h3 := Submodule.sub_mem _ h1 h2
      simpa using h3
  refine le_antisymm ?_ (key n)
  rw [Xa_eq_span_e_castSucc G n, Submodule.span_le]
  rintro _ ⟨b, hb, rfl⟩
  have hd := sameGr_e_sub_mem_Xa h b.castSucc
  simp only [Fin.coe_castSucc] at hd
  have h1 : F.e b.castSucc ∈ F.Xa n := _root_.Formalism.HermitianLatticeCounting.P.e_mem_Xa F b hb
  have h2 : G.e b.castSucc - F.e b.castSucc ∈ F.Xa n := _root_.Formalism.HermitianLatticeCounting.P.Xa_mono F (le_of_lt hb) hd
  have h3 := Submodule.add_mem _ h1 h2
  simpa using h3

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} in
theorem _root_.GlobalTheory.DegAsm.AdaptInv.sameGr_symm {F G : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r} (h : _root_.GlobalTheory.DegAsm.SameGr F G) :
    _root_.GlobalTheory.DegAsm.SameGr G F := by
  unfold _root_.GlobalTheory.DegAsm.SameGr
  intro a
  rw [_root_.GlobalTheory.DegAsm.AdaptInv.xa_eq h]
  have hd := Submodule.neg_mem _ (sameGr_e_sub_mem_Xa h a)
  rwa [neg_sub] at hd

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} in
theorem _root_.GlobalTheory.DegAsm.AdaptInv.x_eq {F G : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r} (h : _root_.GlobalTheory.DegAsm.SameGr F G) :
    G.X = F.X := by
  unfold _root_.Formalism.HermitianLatticeCounting.S6.FlagD.X
  exact _root_.GlobalTheory.DegAsm.AdaptInv.xa_eq h r

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} in
private theorem sameGr_z_sub_mem_X {F G : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r}
    (h : _root_.GlobalTheory.DegAsm.SameGr F G) : G.z - F.z ∈ F.X := by
  have hd := sameGr_e_sub_mem_Xa h (Fin.last r)
  simp only [Fin.val_last] at hd
  exact hd

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} in
private theorem sameGr_V0_le {F G F' G' : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r}
    (h : _root_.GlobalTheory.DegAsm.SameGr F G) (h' : _root_.GlobalTheory.DegAsm.SameGr F' G') :
    _root_.Formalism.HermitianLatticeCounting.S6.V0 G G' ≤ _root_.Formalism.HermitianLatticeCounting.S6.V0 F F' := by
  show G.X ⊔ G'.X ⊔ Submodule.span K {G.z, G'.z} ≤ _
  rw [_root_.GlobalTheory.DegAsm.AdaptInv.x_eq h, _root_.GlobalTheory.DegAsm.AdaptInv.x_eq h']
  refine sup_le (sup_le (_root_.Formalism.HermitianLatticeCounting.P.isotropicSpan_le_jointSpan_left F F') (_root_.Formalism.HermitianLatticeCounting.P.isotropicSpan_le_jointSpan_right F F')) ?_
  rw [Submodule.span_le]
  rintro v (rfl | rfl)
  · have h3 := Submodule.add_mem _ (_root_.Formalism.HermitianLatticeCounting.P.lastVector_mem_jointSpan_left F F')
      (_root_.Formalism.HermitianLatticeCounting.P.isotropicSpan_le_jointSpan_left F F' (sameGr_z_sub_mem_X h))
    simpa using h3
  · have h3 := Submodule.add_mem _ (_root_.Formalism.HermitianLatticeCounting.P.lastVector_mem_jointSpan_right F F')
      (_root_.Formalism.HermitianLatticeCounting.P.isotropicSpan_le_jointSpan_right F F' (sameGr_z_sub_mem_X h'))
    simpa using h3

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} in
theorem _root_.GlobalTheory.DegAsm.AdaptInv.sitesCommonSpace_v0_eq_Vp {F G F' G' : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r} (h : _root_.GlobalTheory.DegAsm.SameGr F G) (h' : _root_.GlobalTheory.DegAsm.SameGr F' G') : _root_.Formalism.HermitianLatticeCounting.S6.V0 G G' = _root_.Formalism.HermitianLatticeCounting.S6.V0 F F' :=
  le_antisymm (sameGr_V0_le h h')
    (sameGr_V0_le (_root_.GlobalTheory.DegAsm.AdaptInv.sameGr_symm h) (_root_.GlobalTheory.DegAsm.AdaptInv.sameGr_symm h'))

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} in
private theorem det_of_eq_of_sub_mem_span_lt {l : ℕ} (u u' w : Fin l → V)
    (h : ∀ a, u' a - u a ∈ Submodule.span K (u '' {c | c < a})) :
    (Matrix.of fun a b => H.B (u' a) (w b)).det = (Matrix.of fun a b => H.B (u a) (w b)).det := by
  choose L hLsupp hL using fun a => (Finsupp.mem_span_image_iff_linearCombination K).1 (h a)
  set M : Matrix (Fin l) (Fin l) K := 1 + Matrix.of fun a c => L a c with hM
  have hrow : ∀ a, u' a = ∑ c, M a c • u c := by
    intro a
    have h1 := hL a
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)] at h1
    simp only [hM, Matrix.add_apply, Matrix.one_apply, Matrix.of_apply, add_smul,
      Finset.sum_add_distrib, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ,
      if_true, h1]
    abel
  have hmat : (Matrix.of fun a b => H.B (u' a) (w b)) = M * Matrix.of fun a b => H.B (u a) (w b) := by
    ext a b
    rw [Matrix.of_apply, hrow a, _root_.Formalism.HermitianLatticeCounting.P.B_sum_left, Matrix.mul_apply]
    simp only [Matrix.of_apply]
  have hdet : M.det = 1 := by
    rw [Matrix.det_of_lowerTriangular]
    · refine Finset.prod_eq_one fun a _ => ?_
      have h0 : L a a = 0 := (Finsupp.mem_supported' K (L a)).1 (hLsupp a) a (by simp)
      simp [hM, h0]
    · intro i j hij
      have hij' : i < j := hij
      have h0 : L i j = 0 :=
        (Finsupp.mem_supported' K (L i)).1 (hLsupp i) j (by simpa using hij'.le)
      simp [hM, h0, Matrix.one_apply_ne hij'.ne]
  rw [hmat, Matrix.det_mul, hdet, one_mul]

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} in
private theorem sameGr_Dl_left_eq {F G : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r} (h : _root_.GlobalTheory.DegAsm.SameGr F G)
    (F' : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r) (l : ℕ) (hl : l ≤ r + 1) : _root_.Formalism.HermitianLatticeCounting.S6.Dl G F' l hl = _root_.Formalism.HermitianLatticeCounting.S6.Dl F F' l hl := by
  rw [_root_.Formalism.HermitianLatticeCounting.P.Dl_eq, _root_.Formalism.HermitianLatticeCounting.P.Dl_eq]
  apply det_of_eq_of_sub_mem_span_lt (fun a => F.e (Fin.castLE hl a))
    (fun a => G.e (Fin.castLE hl a))
  intro a
  have hd := sameGr_e_sub_mem_Xa h (Fin.castLE hl a)
  simp only [Fin.coe_castLE] at hd
  refine (show F.Xa a ≤ _ from ?_) hd
  rw [Xa_eq_span_e_castSucc F, Submodule.span_le]
  rintro _ ⟨b, hb, rfl⟩
  apply Submodule.subset_span
  refine ⟨⟨b.val, by have := a.isLt; simp only [Set.mem_setOf_eq] at hb; omega⟩, ?_, ?_⟩
  · simp only [Set.mem_setOf_eq] at hb ⊢
    exact Fin.mk_lt_of_lt_val hb
  · simp only
    congr 1

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} in
theorem _root_.GlobalTheory.DegAsm.AdaptInv.dl_eq {F G F' G' : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r} (h : _root_.GlobalTheory.DegAsm.SameGr F G) (h' : _root_.GlobalTheory.DegAsm.SameGr F' G') (l : ℕ) (hl : l ≤ r + 1) :
    _root_.Formalism.HermitianLatticeCounting.S6.Dl G G' l hl = _root_.Formalism.HermitianLatticeCounting.S6.Dl F F' l hl := by
  calc _root_.Formalism.HermitianLatticeCounting.S6.Dl G G' l hl = _root_.Formalism.HermitianLatticeCounting.S6.Dl F G' l hl := sameGr_Dl_left_eq h G' l hl
    _ = star (_root_.Formalism.HermitianLatticeCounting.S6.Dl G' F l hl) := _root_.Formalism.HermitianLatticeCounting.P.Dl_swap G' F l hl
    _ = star (_root_.Formalism.HermitianLatticeCounting.S6.Dl F' F l hl) := by rw [sameGr_Dl_left_eq h' F l hl]
    _ = _root_.Formalism.HermitianLatticeCounting.S6.Dl F F' l hl := (_root_.Formalism.HermitianLatticeCounting.P.Dl_swap F' F l hl).symm

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} in
theorem _root_.GlobalTheory.DegAsm.AdaptInv.inN_of {F G : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r} (h : _root_.GlobalTheory.DegAsm.SameGr F G) (s : V →ₗ[K] V) (hs : F.InN s) : G.InN s := by
  unfold _root_.Formalism.HermitianLatticeCounting.S6.FlagD.InN at hs ⊢
  obtain ⟨hiso, hbij, hflag, hperp⟩ := hs
  refine ⟨hiso, hbij, ?_, ?_⟩
  · have hXa : ∀ n, ∀ x ∈ F.Xa n, s x - x ∈ F.Xa n := by
      intro n x hx
      have hle : Submodule.span K ((fun b : Fin r => F.e b.castSucc) '' {b | b.val < n}) ≤
          (F.Xa n).comap (s - LinearMap.id) := by
        rw [Submodule.span_le]
        rintro _ ⟨b, hb, rfl⟩
        simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.sub_apply, LinearMap.id_apply]
        exact _root_.Formalism.HermitianLatticeCounting.P.Xa_mono F (le_of_lt hb) (hflag b)
      have h3 := hle (by rwa [← Xa_eq_span_e_castSucc])
      simpa using h3
    intro a
    rw [_root_.GlobalTheory.DegAsm.AdaptInv.xa_eq h]
    have hd := sameGr_e_sub_mem_Xa h a.castSucc
    simp only [Fin.coe_castSucc] at hd
    have h3 := Submodule.add_mem _ (hflag a) (hXa a _ hd)
    convert h3 using 1
    rw [map_sub]
    abel
  · intro y hy
    rw [_root_.GlobalTheory.DegAsm.AdaptInv.x_eq h]
    apply hperp
    intro a
    have hmem : F.e a.castSucc ∈ G.X := by
      rw [_root_.GlobalTheory.DegAsm.AdaptInv.x_eq h]
      exact _root_.Formalism.HermitianLatticeCounting.P.e_mem_X F a
    exact _root_.Formalism.HermitianLatticeCounting.P.perp_X G hy _ hmem

variable {R : Type} [CommRing R] [Algebra R K] [Module R V] [IsScalarTower R K V]

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} in
variable {R : Type} [CommRing R] [Algebra R K] [Module R V] [IsScalarTower R K V] in
theorem _root_.GlobalTheory.DegAsm.AdaptInv.lead_eq {F G : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r}
    (h : _root_.GlobalTheory.DegAsm.SameGr F G) (Λ : Submodule R V) (a : Fin (r + 1)) :
    _root_.GlobalTheory.HermLat.lead G Λ a = _root_.GlobalTheory.HermLat.lead F Λ a := by
  unfold _root_.GlobalTheory.HermLat.lead
  rw [_root_.GlobalTheory.DegAsm.AdaptInv.xa_eq h]
  ext t
  simp only [Submodule.mem_comap, LinearMap.coe_restrictScalars, LinearMap.toSpanSingleton_apply]
  have hd : t • (G.e a - F.e a) ∈ Λ ⊔ _root_.GlobalTheory.HermLat.rs R (F.Xa a) := by
    apply Submodule.mem_sup_right
    unfold _root_.GlobalTheory.HermLat.rs
    rw [Submodule.restrictScalars_mem]
    exact Submodule.smul_mem _ t (sameGr_e_sub_mem_Xa h a)
  have h3 : t • G.e a = t • F.e a + t • (G.e a - F.e a) := by
    rw [smul_sub]
    abel
  rw [h3, Submodule.add_mem_iff_left _ hd]

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} in
variable {R : Type} [CommRing R] [Algebra R K] [Module R V] [IsScalarTower R K V] in
private theorem sameGr_sub_smul_e_mem_Xa_iff {F G : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r}
    (h : _root_.GlobalTheory.DegAsm.SameGr F G) (a : Fin (r + 1)) (t : K) (x : V) :
    x - t • G.e a ∈ G.Xa a ↔ x - t • F.e a ∈ F.Xa a := by
  rw [_root_.GlobalTheory.DegAsm.AdaptInv.xa_eq h]
  have hd := sameGr_e_sub_mem_Xa h a
  have h3 : x - t • G.e a = (x - t • F.e a) - t • (G.e a - F.e a) := by
    rw [smul_sub]
    abel
  rw [h3, Submodule.sub_mem_iff_left _ (Submodule.smul_mem _ t hd)]

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} in
variable {R : Type} [CommRing R] [Algebra R K] [Module R V] [IsScalarTower R K V] in
theorem _root_.GlobalTheory.DegAsm.AdaptInv.isAdm_iff {F G F' G' : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r} (h : _root_.GlobalTheory.DegAsm.SameGr F G) (h' : _root_.GlobalTheory.DegAsm.SameGr F' G') (Λ : Submodule R V) (g : R) :
    _root_.GlobalTheory.HermLat.IsAdm G G' Λ g ↔ _root_.GlobalTheory.HermLat.IsAdm F F' Λ g := by
  unfold _root_.GlobalTheory.HermLat.IsAdm
  simp only [sameGr_sub_smul_e_mem_Xa_iff h, sameGr_sub_smul_e_mem_Xa_iff h']

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} in
variable {R : Type} [CommRing R] [Algebra R K] [Module R V] [IsScalarTower R K V] in
theorem _root_.GlobalTheory.DegAsm.AdaptInv.isFramed_iff {F G F' G' : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r} (h : _root_.GlobalTheory.DegAsm.SameGr F G) (h' : _root_.GlobalTheory.DegAsm.SameGr F' G') (Λ : Submodule R V)
    (aa : Fin r → Submodule R K) : _root_.GlobalTheory.HermLat.IsFramed G G' Λ aa ↔ _root_.GlobalTheory.HermLat.IsFramed F F' Λ aa := by
  unfold _root_.GlobalTheory.HermLat.IsFramed _root_.GlobalTheory.HermLat.IsFrame
  simp only [_root_.GlobalTheory.DegAsm.AdaptInv.lead_eq h, _root_.GlobalTheory.DegAsm.AdaptInv.lead_eq h']

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} in
variable {R : Type} [CommRing R] [Algebra R K] [Module R V] [IsScalarTower R K V] in
theorem _root_.GlobalTheory.DegAsm.AdaptInv.latL_eq {F G F' G' : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r} (h : _root_.GlobalTheory.DegAsm.SameGr F G) (h' : _root_.GlobalTheory.DegAsm.SameGr F' G') (Λ : Submodule R V) :
    _root_.GlobalTheory.HermLat.latL G G' Λ = _root_.GlobalTheory.HermLat.latL F F' Λ := by
  unfold _root_.GlobalTheory.HermLat.latL _root_.GlobalTheory.HermLat.uPerp
  rw [_root_.GlobalTheory.DegAsm.AdaptInv.x_eq h, _root_.GlobalTheory.DegAsm.AdaptInv.x_eq h']

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} in
variable {R : Type} [CommRing R] [Algebra R K] [Module R V] [IsScalarTower R K V] in
theorem _root_.GlobalTheory.DegAsm.AdaptInv.flagFramesSameGraded_definitePartLattice_eq {F G F' G' : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r} (h : _root_.GlobalTheory.DegAsm.SameGr F G) (h' : _root_.GlobalTheory.DegAsm.SameGr F' G') (Λ : Submodule R V) :
    _root_.GlobalTheory.HermLat.flagPairDefinitePartLattice G G' Λ = _root_.GlobalTheory.HermLat.flagPairDefinitePartLattice F F' Λ := by
  unfold _root_.GlobalTheory.HermLat.flagPairDefinitePartLattice _root_.GlobalTheory.HermLat.wSp
  rw [_root_.GlobalTheory.DegAsm.AdaptInv.latL_eq h h',
    _root_.GlobalTheory.DegAsm.AdaptInv.sitesCommonSpace_v0_eq_Vp h h']

open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} in
variable {R : Type} [CommRing R] [Algebra R K] [Module R V] [IsScalarTower R K V] in
theorem _root_.GlobalTheory.DegAsm.AdaptInv.iotaGraph_eq {F G F' G' : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r} (h : _root_.GlobalTheory.DegAsm.SameGr F G) (h' : _root_.GlobalTheory.DegAsm.SameGr F' G') (Λ : Submodule R V) (g : R) :
    _root_.GlobalTheory.HermLat.iotaGraph G G' Λ g = _root_.GlobalTheory.HermLat.iotaGraph F F' Λ g := by
  unfold _root_.GlobalTheory.HermLat.iotaGraph
  rw [_root_.GlobalTheory.DegAsm.AdaptInv.flagFramesSameGraded_definitePartLattice_eq h h', _root_.GlobalTheory.DegAsm.AdaptInv.flagFramesSameGraded_definitePartLattice_eq h' h,
    _root_.GlobalTheory.DegAsm.AdaptInv.x_eq h, _root_.GlobalTheory.DegAsm.AdaptInv.x_eq h']

end GlobalTheory.DegAsm.AdaptInv

namespace GlobalTheory.DegAsm
open AdaptInv

open NumberField in
open scoped Pointwise ENNReal Classical in
private theorem NF_j_eq_sub_finrank_II {K V : Type} [Field K] [NumberField K]
    [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ}
    (N : _root_.GlobalTheory.DegCnt.NF H r) :
    N.j = r - Module.finrank K (_root_.Formalism.HermitianLatticeCounting.S6.II N.F N.F') := by
  have hj : N.j ≤ r := N.j_le
  have hdet : _root_.Formalism.HermitianLatticeCounting.S6.Dl N.F N.F' N.j
      (by omega) ≠ 0 := _root_.GlobalTheory.DegCnt.NFGeom.Dl_ne N
  have hsup : N.F.X = N.F.Xa N.j ⊔
      _root_.Formalism.HermitianLatticeCounting.S6.II N.F N.F' := by
    apply _root_.Formalism.HermitianLatticeCounting.P.X_eq_of_levels N.F N.j _ (by unfold _root_.Formalism.HermitianLatticeCounting.S6.II; exact inf_le_left)
    intro a ha
    exact ⟨_, _root_.GlobalTheory.DegCnt.NFGeom.e_mem_II N a ha, 1, _root_.Formalism.HermitianLatticeCounting.P.e_level N.F a⟩
  have hinf : _root_.Formalism.HermitianLatticeCounting.S6.II N.F N.F' ⊓
      N.F.Xa N.j = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxI, hxa⟩
    have hx' : x ∈ N.F'.X := by
      unfold _root_.Formalism.HermitianLatticeCounting.S6.II at hxI
      exact hxI.2
    exact (Submodule.mem_bot K).2
      (_root_.Formalism.HermitianLatticeCounting.P.Dl_injL N.F N.F' hj hdet hxa fun u hu =>
        _root_.Formalism.HermitianLatticeCounting.P.X_iso N.F' hx' (_root_.Formalism.HermitianLatticeCounting.P.Xa_le_X N.F' _ hu))
  rw [_root_.Formalism.HermitianLatticeCounting.P.finrank_compl N.F hj _ hsup hinf]
  omega

open NumberField in
open scoped Pointwise ENNReal Classical in
private theorem NF_Dl_eq_zero_of_j_lt {K V : Type} [Field K] [NumberField K]
    [StarRing K] [AddCommGroup V] [Module K V] {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ}
    (N : _root_.GlobalTheory.DegCnt.NF H r) (l : ℕ) (hl : l ≤ r + 1) (hjl : N.j < l)
    (hlr : l ≤ r) : _root_.Formalism.HermitianLatticeCounting.S6.Dl N.F N.F' l hl = 0 := by
  rw [_root_.Formalism.HermitianLatticeCounting.P.Dl_eq]
  apply Matrix.det_eq_zero_of_row_eq_zero ⟨N.j, hjl⟩
  intro b
  simp only [Matrix.of_apply]
  have hmem : N.F.e (⟨N.j, by omega⟩ : Fin r).castSucc ∈
      _root_.Formalism.HermitianLatticeCounting.S6.II N.F N.F' :=
    _root_.GlobalTheory.DegCnt.NFGeom.e_mem_II N ⟨N.j, by omega⟩ le_rfl
  have hX : N.F.e (Fin.castLE hl ⟨N.j, hjl⟩) ∈
      N.F'.X := by
    have h1 : Fin.castLE hl ⟨N.j, hjl⟩ =
        (⟨N.j, by omega⟩ : Fin r).castSucc := by
      ext
      simp
    rw [h1]
    unfold _root_.Formalism.HermitianLatticeCounting.S6.II at hmem
    exact hmem.2
  have hb : N.F'.e (Fin.castLE hl b) ∈ N.F'.X := by
    have h1 : Fin.castLE hl b = (⟨b.val, by have := b.isLt; omega⟩ : Fin r).castSucc := by
      ext
      simp
    rw [h1]
    exact _root_.Formalism.HermitianLatticeCounting.P.e_mem_X N.F' _
  exact _root_.Formalism.HermitianLatticeCounting.P.X_iso N.F' hX hb

open NumberField in
open scoped Pointwise ENNReal Classical in

theorem _root_.GlobalTheory.DegAsm.adapt_invariants : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V), _root_.Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), ∀ (F F' : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r) (𝔡 : Ideal (𝓞 K)) (N : _root_.GlobalTheory.DegCnt.NF H r), _root_.GlobalTheory.DegAsm.Adapt F F' 𝔡 N → (∀ a : ℕ, N.F.Xa a = F.Xa a ∧ N.F'.Xa a = F'.Xa a) ∧ N.F.X = F.X ∧ N.F'.X = F'.X ∧ _root_.Formalism.HermitianLatticeCounting.S6.V0 N.F N.F' = _root_.Formalism.HermitianLatticeCounting.S6.V0 F F' ∧ N.j = r - Module.finrank K (_root_.Formalism.HermitianLatticeCounting.S6.II F F') ∧ (∀ (l : ℕ) (hl : l ≤ r + 1), _root_.Formalism.HermitianLatticeCounting.S6.Dl N.F N.F' l hl = _root_.Formalism.HermitianLatticeCounting.S6.Dl F F' l hl) ∧ (∀ (l : ℕ) (hl : l ≤ r + 1), N.j < l → l ≤ r → _root_.Formalism.HermitianLatticeCounting.S6.Dl F F' l hl = 0) ∧ (∀ s : V →ₗ[K] V, (N.F.InN s ↔ F.InN s) ∧ (N.F'.InN s ↔ F'.InN s)) ∧ ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), (N.IsTerm g Λ ↔ _root_.GlobalTheory.HermLat.IsFramed F F' Λ N.aa ∧ _root_.GlobalTheory.HermLat.IsAdm F F' Λ (g : 𝓞 K)) ∧ _root_.GlobalTheory.HermLat.latL N.F N.F' Λ = _root_.GlobalTheory.HermLat.latL F F' Λ ∧ _root_.GlobalTheory.HermLat.latL N.F' N.F Λ = _root_.GlobalTheory.HermLat.latL F' F Λ ∧ _root_.GlobalTheory.HermLat.flagPairDefinitePartLattice N.F N.F' Λ = _root_.GlobalTheory.HermLat.flagPairDefinitePartLattice F F' Λ ∧ _root_.GlobalTheory.HermLat.flagPairDefinitePartLattice N.F' N.F Λ = _root_.GlobalTheory.HermLat.flagPairDefinitePartLattice F' F Λ ∧ _root_.GlobalTheory.HermLat.iotaGraph N.F N.F' Λ (g : 𝓞 K) = _root_.GlobalTheory.HermLat.iotaGraph F F' Λ (g : 𝓞 K) := by
  intro K V _ _ _ _ _ _ _ _ H _ r F F' 𝔡 N hN
  unfold _root_.GlobalTheory.DegAsm.Adapt at hN
  obtain ⟨-, h, h'⟩ := hN
  have hI : _root_.Formalism.HermitianLatticeCounting.S6.II N.F N.F' = _root_.Formalism.HermitianLatticeCounting.S6.II F F' := by
    unfold _root_.Formalism.HermitianLatticeCounting.S6.II
    rw [_root_.GlobalTheory.DegAsm.AdaptInv.x_eq h, _root_.GlobalTheory.DegAsm.AdaptInv.x_eq h']
  refine ⟨fun a => ⟨_root_.GlobalTheory.DegAsm.AdaptInv.xa_eq h a, _root_.GlobalTheory.DegAsm.AdaptInv.xa_eq h' a⟩,
    _root_.GlobalTheory.DegAsm.AdaptInv.x_eq h, _root_.GlobalTheory.DegAsm.AdaptInv.x_eq h',
    _root_.GlobalTheory.DegAsm.AdaptInv.sitesCommonSpace_v0_eq_Vp h h', ?_,
    fun l hl => _root_.GlobalTheory.DegAsm.AdaptInv.dl_eq h h' l hl, ?_,
    fun s => ⟨⟨_root_.GlobalTheory.DegAsm.AdaptInv.inN_of (_root_.GlobalTheory.DegAsm.AdaptInv.sameGr_symm h) s,
      _root_.GlobalTheory.DegAsm.AdaptInv.inN_of h s⟩,
      ⟨_root_.GlobalTheory.DegAsm.AdaptInv.inN_of (_root_.GlobalTheory.DegAsm.AdaptInv.sameGr_symm h') s,
      _root_.GlobalTheory.DegAsm.AdaptInv.inN_of h' s⟩⟩,
    fun g Λ => ⟨?_, _root_.GlobalTheory.DegAsm.AdaptInv.latL_eq h h' Λ,
      _root_.GlobalTheory.DegAsm.AdaptInv.latL_eq h' h Λ,
      _root_.GlobalTheory.DegAsm.AdaptInv.flagFramesSameGraded_definitePartLattice_eq h h' Λ,
      _root_.GlobalTheory.DegAsm.AdaptInv.flagFramesSameGraded_definitePartLattice_eq h' h Λ,
      _root_.GlobalTheory.DegAsm.AdaptInv.iotaGraph_eq h h' Λ _⟩⟩
  · rw [← hI]
    exact NF_j_eq_sub_finrank_II N
  · intro l hl hjl hlr
    rw [← _root_.GlobalTheory.DegAsm.AdaptInv.dl_eq h h' l hl]
    exact NF_Dl_eq_zero_of_j_lt N l hl hjl hlr
  · unfold _root_.GlobalTheory.DegCnt.NF.IsTerm
    rw [_root_.GlobalTheory.DegAsm.AdaptInv.isFramed_iff h h',
      _root_.GlobalTheory.DegAsm.AdaptInv.isAdm_iff h h']

end GlobalTheory.DegAsm
