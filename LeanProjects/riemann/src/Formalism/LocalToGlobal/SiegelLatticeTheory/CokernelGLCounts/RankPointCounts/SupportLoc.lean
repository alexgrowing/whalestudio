import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.SupportG

noncomputable section

namespace Formalism.L2.SG.Pf

open Matrix NumberField IsDedekindDomain Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups ValuativeRel
open scoped BigOperators

section Fit

variable {R : Type*} [CommRing R]

theorem exists_mul_eq_of_range_le {ι : Type*} [Fintype ι] [DecidableEq ι] (M N : Matrix ι ι R)
    (h : LinearMap.range N.mulVecLin ≤ LinearMap.range M.mulVecLin) : ∃ G : Matrix ι ι R, M * G = N := by
  classical
  have hv : ∀ j : ι, ∃ v : ι → R, M.mulVecLin v = N.mulVecLin (Pi.single j 1) := fun j =>
    h (LinearMap.mem_range_self _ _)
  choose v hv using hv
  refine ⟨Matrix.of fun i j => v j i, ?_⟩
  ext i j
  have hij := congrFun (hv j) i
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec_single_one] at hij
  rw [Matrix.mul_apply]
  convert hij using 1
  · simp [Matrix.mulVec, dotProduct]
  · simp

theorem det_assoc_of_range_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (M N : Matrix ι ι R)
    (h : LinearMap.range N.mulVecLin = LinearMap.range M.mulVecLin) (hM : ∀ x, M.det * x = 0 → x = 0) :
    ∃ u : Rˣ, N.det = M.det * u := by
  obtain ⟨G, hG⟩ := exists_mul_eq_of_range_le M N h.le
  obtain ⟨H, hH⟩ := exists_mul_eq_of_range_le N M h.ge
  have hGH : G * H = 1 := by
    have h1 : M * (G * H) = M * 1 := by rw [← Matrix.mul_assoc, hG, hH, Matrix.mul_one]
    have h2 : (M.adjugate * M) * (G * H) = (M.adjugate * M) * 1 := by
      rw [Matrix.mul_assoc, h1, ← Matrix.mul_assoc]
    rw [Matrix.adjugate_mul] at h2
    ext i j
    have h3 := congrFun (congrFun h2 i) j
    simp only [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_one, Matrix.smul_apply, smul_eq_mul] at h3
    have h4 : M.det * ((G * H) i j - (1 : Matrix ι ι R) i j) = 0 := by rw [mul_sub, h3, sub_self]
    exact sub_eq_zero.mp (hM _ h4)
  have hu : IsUnit G.det := by
    have h5 := congrArg Matrix.det hGH
    rw [Matrix.det_mul, Matrix.det_one] at h5
    exact ⟨⟨G.det, H.det, h5, by rw [mul_comm]; exact h5⟩, rfl⟩
  exact ⟨hu.unit, by rw [IsUnit.unit_spec, ← hG, Matrix.det_mul]⟩

theorem det_assoc_of_cok {n : Type*} [Fintype n] [DecidableEq n] (Z Z' : Matrix n n R)
    (φ : ((n → R) ⧸ LinearMap.range Z.mulVecLin) ≃ₗ[R] ((n → R) ⧸ LinearMap.range Z'.mulVecLin))
    (hZ : ∀ x, Z.det * x = 0 → x = 0) : ∃ u : Rˣ, Z'.det = Z.det * u := by
  obtain ⟨A, hA⟩ := Module.projective_lifting_property (Submodule.mkQ (LinearMap.range Z'.mulVecLin))
    ((φ : _ →ₗ[R] _) ∘ₗ Submodule.mkQ (LinearMap.range Z.mulVecLin)) (Submodule.mkQ_surjective _)
  have hA' : ∀ v, Submodule.mkQ (LinearMap.range Z'.mulVecLin) (LinearMap.toMatrix' A *ᵥ v) =
      φ (Submodule.mkQ (LinearMap.range Z.mulVecLin) v) := by
    intro v
    rw [LinearMap.toMatrix'_mulVec]
    exact LinearMap.congr_fun hA v
  obtain ⟨B, hB⟩ := Module.projective_lifting_property (Submodule.mkQ (LinearMap.range Z.mulVecLin))
    ((φ.symm : _ →ₗ[R] _) ∘ₗ Submodule.mkQ (LinearMap.range Z'.mulVecLin)) (Submodule.mkQ_surjective _)
  have hB' : ∀ v, Submodule.mkQ (LinearMap.range Z.mulVecLin) (LinearMap.toMatrix' B *ᵥ v) =
      φ.symm (Submodule.mkQ (LinearMap.range Z'.mulVecLin) v) := by
    intro v
    rw [LinearMap.toMatrix'_mulVec]
    exact LinearMap.congr_fun hB v
  set a := LinearMap.toMatrix' A
  set b := LinearMap.toMatrix' B
  let M1 : Matrix (n ⊕ n) (n ⊕ n) R := fromBlocks 1 0 (-a) Z'
  let M2 : Matrix (n ⊕ n) (n ⊕ n) R := fromBlocks Z (-b) 0 1
  have c1 : ∀ u : n ⊕ n → R, u ∈ LinearMap.range M1.mulVecLin ↔
      Submodule.mkQ (LinearMap.range Z'.mulVecLin) (a *ᵥ (u ∘ Sum.inl) + u ∘ Sum.inr) = 0 := by
    intro u
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨y ∘ Sum.inr, ?_⟩
      simp only [Matrix.mulVecLin_apply, M1, Matrix.fromBlocks_mulVec]
      funext i
      simp [Matrix.neg_mulVec]
    · rintro ⟨y, hy⟩
      refine ⟨Sum.elim (u ∘ Sum.inl) y, ?_⟩
      simp only [Matrix.mulVecLin_apply] at hy ⊢
      simp only [M1, Matrix.fromBlocks_mulVec]
      funext i
      rcases i with i | i
      · simp
      · simp only [Sum.elim_inr, Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.one_mulVec, Matrix.zero_mulVec,
          add_zero, Matrix.neg_mulVec, hy]
        simp
  have c2 : ∀ u : n ⊕ n → R, u ∈ LinearMap.range M2.mulVecLin ↔
      Submodule.mkQ (LinearMap.range Z.mulVecLin) (u ∘ Sum.inl + b *ᵥ (u ∘ Sum.inr)) = 0 := by
    intro u
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨y ∘ Sum.inl, ?_⟩
      simp only [Matrix.mulVecLin_apply, M2, Matrix.fromBlocks_mulVec]
      funext i
      simp [Matrix.neg_mulVec]
    · rintro ⟨y, hy⟩
      refine ⟨Sum.elim y (u ∘ Sum.inr), ?_⟩
      simp only [Matrix.mulVecLin_apply] at hy ⊢
      simp only [M2, Matrix.fromBlocks_mulVec]
      funext i
      rcases i with i | i
      · simp only [Sum.elim_inl, Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.neg_mulVec, hy]
        simp
      · simp
  have key : LinearMap.range M1.mulVecLin = LinearMap.range M2.mulVecLin := by
    ext u
    rw [c1, c2, map_add, hA', ← φ.apply_symm_apply (Submodule.mkQ _ (u ∘ Sum.inr)), ← hB', ← map_add, ← map_add,
      LinearEquiv.map_eq_zero_iff]
  have d1 : M1.det = Z'.det := by simp [M1, Matrix.det_fromBlocks_zero₁₂]
  have d2 : M2.det = Z.det := by simp [M2]
  obtain ⟨u, hu⟩ := det_assoc_of_range_eq M2 M1 key (by rw [d2]; exact hZ)
  exact ⟨u, by rw [← d1, hu, d2]⟩

end Fit

section Pts

variable {K S : Type} [Zero K] [CommRing S]

theorem ptEntryL_eq (L : List (Sˣ × ℕ+)) : ∀ i j : ℕ,
    Formalism.MainNotions.S.Loc.ptEntryL L i j = ptEntry (L.map fun b => ((b.1 : S), (b.2 : ℕ))) i j := by
  induction L with
  | nil => intro i j; simp [Formalism.MainNotions.S.Loc.ptEntryL, ptEntry]
  | cons b L ih =>
    intro i j
    obtain ⟨t, s⟩ := b
    simp only [Formalism.MainNotions.S.Loc.ptEntryL, List.map_cons, ptEntry, ih]

theorem modBlocks_map {A : Type} (f : ℕ → ℕ → A → S) : ∀ (l : List (A × ℕ)) (a : ℕ) (L : List (Sˣ × ℕ+)),
    modBlocks f a l = some L → L.map (fun b => ((b.1 : S), (b.2 : ℕ))) = mapBlocks f a l
  | [], a, L, h => by
    simp only [modBlocks, Option.some.injEq] at h
    subst h; rfl
  | (t, s) :: l, a, L, h => by
    simp only [modBlocks] at h
    split_ifs at h with hu
    obtain ⟨L1, hL1, rfl⟩ := Option.map_eq_some_iff.1 h
    simp only [List.map_cons, mapBlocks, modBlocks_map f l (a + s) L1 hL1]
    rfl

theorem mapBlocks_snd {A B : Type} (f : ℕ → ℕ → A → B) : ∀ (l : List (A × ℕ)) (a : ℕ),
    (mapBlocks f a l).map Prod.snd = l.map Prod.snd
  | [], _ => rfl
  | (t, s) :: l, a => by simp [mapBlocks, mapBlocks_snd f l (a + s)]

theorem mapBlocks_append {A B : Type} (f : ℕ → ℕ → A → B) : ∀ (l0 l1 : List (A × ℕ)) (a : ℕ),
    mapBlocks f a (l0 ++ l1) = mapBlocks f a l0 ++ mapBlocks f (a + (l0.map Prod.snd).sum) l1
  | [], l1, a => by simp [mapBlocks]
  | (t, s) :: l0, l1, a => by
    simp only [List.cons_append, mapBlocks, mapBlocks_append f l0 l1 (a + s), List.map_cons, List.sum_cons, add_assoc]

theorem ptEntry_append_ge {L : Type} [Zero L] : ∀ (l0 l1 : List (L × ℕ)) (i j : ℕ), (l0.map Prod.snd).sum ≤ i →
    ptEntry (l0 ++ l1) i j = if (l0.map Prod.snd).sum ≤ j then
      ptEntry l1 (i - (l0.map Prod.snd).sum) (j - (l0.map Prod.snd).sum) else 0
  | [], l1, i, j, _ => by simp
  | (t, s) :: l0, l1, i, j, hi => by
    simp only [List.map_cons, List.sum_cons] at hi ⊢
    simp only [List.cons_append, ptEntry]
    rw [if_neg (by omega)]
    by_cases h2 : s ≤ j
    · rw [if_pos ⟨by omega, h2⟩, ptEntry_append_ge l0 l1 (i - s) (j - s) (by omega)]
      by_cases h3 : s + (l0.map Prod.snd).sum ≤ j
      · rw [if_pos (by omega), if_pos h3, Nat.sub_sub, Nat.sub_sub]
      · rw [if_neg (by omega), if_neg h3]
    · rw [if_neg (fun h => h2 h.2), if_neg (by omega)]

end Pts

section Scale

variable {K S : Type} [Field K] [CommRing S]

theorem ptEntry_scale (ι : K →+* S) (g : ℕ → ℕ → K → S) (ρ : ℕ → S) (κ : S) (r : ℕ)
    (H : ∀ a s t x y, 1 ≤ a → a - 1 ≤ x → a - 1 ≤ y → x + y + 1 = 2 * (a - 1) + s → x ≤ r → y ≤ r →
      ¬ (x = r ∧ y = r) → g a s t = ρ x * ρ y * κ * ι t) :
    ∀ (l : List (K × ℕ)) (a i j : ℕ), 1 ≤ a → a - 1 + i ≤ r → a - 1 + j ≤ r → ¬ (a - 1 + i = r ∧ a - 1 + j = r) →
      ptEntry (mapBlocks g a l) i j = ρ (a - 1 + i) * ρ (a - 1 + j) * κ * ι (ptEntry l i j)
  | [], a, i, j, _, _, _, _ => by simp [mapBlocks, ptEntry]
  | (t, s) :: l, a, i, j, ha, hi, hj, hn => by
    simp only [mapBlocks, ptEntry]
    by_cases h1 : i < s ∧ j < s
    · rw [if_pos h1, if_pos h1]
      by_cases h2 : i + j + 1 = s
      · rw [if_pos h2, if_pos h2]
        exact H a s t _ _ ha (by omega) (by omega) (by omega) hi hj hn
      · rw [if_neg h2, if_neg h2]; simp
    · rw [if_neg h1, if_neg h1]
      by_cases h2 : s ≤ i ∧ s ≤ j
      · rw [if_pos h2, if_pos h2, ptEntry_scale ι g ρ κ r H l (a + s) (i - s) (j - s) (by omega) (by omega) (by omega)
          (by omega)]
        have e1 : a + s - 1 + (i - s) = a - 1 + i := by omega
        have e2 : a + s - 1 + (j - s) = a - 1 + j := by omega
        rw [e1, e2]
      · rw [if_neg h2, if_neg h2]; simp

theorem det_scaled {n : ℕ} (ι : K →+* S) (ρ : Fin n → S) (κ : S) (P : Matrix (Fin n) (Fin n) K) :
    (Matrix.of fun x y => ρ x * ρ y * κ * ι (P x y)).det = (∏ x, ρ x) ^ 2 * κ ^ n * ι P.det := by
  have h : (Matrix.of fun x y => ρ x * ρ y * κ * ι (P x y)) =
      Matrix.diagonal ρ * (κ • (P.map ι)) * Matrix.diagonal ρ := by
    ext x y
    simp only [Matrix.of_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply,
      Matrix.map_apply, smul_eq_mul]
    ring
  have hm : (P.map ι).det = ι P.det := by rw [RingHom.map_det, RingHom.mapMatrix_apply]
  rw [h, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_smul, hm, Fintype.card_fin]
  ring

theorem det_corner {n : ℕ} (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) S)
    (h : ∀ x y, ¬ (x = Fin.last n ∧ y = Fin.last n) → A x y = B x y) :
    A.det = B.det + (A (Fin.last n) (Fin.last n) - B (Fin.last n) (Fin.last n)) *
      (B.submatrix Fin.castSucc Fin.castSucc).det := by
  obtain ⟨c, hc⟩ : ∃ c, c = A (Fin.last n) (Fin.last n) - B (Fin.last n) (Fin.last n) := ⟨_, rfl⟩
  rw [← hc]
  have hA : A = B.updateRow (Fin.last n)
      (B (Fin.last n) + c • (Pi.single (Fin.last n) (1 : S) : Fin (n + 1) → S)) := by
    ext x y
    by_cases hx : x = Fin.last n
    · subst hx
      by_cases hy : y = Fin.last n
      · subst hy
        simp [hc]
      · simp [Matrix.updateRow_apply, Pi.single_apply, hy, h _ y (fun hh => hy hh.2)]
    · simp [Matrix.updateRow_apply, hx, h x y (fun hh => hx hh.1)]
  rw [hA, Matrix.det_updateRow_add, Matrix.updateRow_eq_self, Matrix.det_updateRow_smul]
  congr 2
  rw [Matrix.det_succ_row _ (Fin.last n), Finset.sum_eq_single (Fin.last n)]
  · rw [Matrix.updateRow_self, Pi.single_eq_same, Matrix.submatrix_updateRow_succAbove,
      Fin.succAbove_last, Fin.val_last, Even.neg_one_pow (⟨n, rfl⟩ : Even (n + n))]
    ring
  · intro j _ hj
    rw [Matrix.updateRow_self, Pi.single_eq_of_ne hj]
    ring
  · intro hn
    exact absurd (Finset.mem_univ _) hn

end Scale

section LocLemmas

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem kk_ne (Mo : Loc.Model F E) {m : ℕ} (a b : Loc.Pt E (m + 1)) (h : Mo.Kk (m + 1) a b ≠ 0) :
    ∃ c, Mo.BB a c ≠ 0 ∧ Mo.BB b c ≠ 0 := by
  rw [Loc.Model.Kk_succ] at h
  by_contra hc
  push_neg at hc
  apply h
  have e : (fun c => Mo.BB a c * (starRingEnd ℂ) (Mo.BB b c) / (Mo.nAut c : ℂ)) = fun _ => 0 := by
    funext c
    by_cases h1 : Mo.BB a c = 0
    · simp [h1]
    · simp [hc c h1]
  rw [e, tsum_zero]

theorem det_uLow {n : ℕ} (x : Loc.IL n → E) : (Loc.uLow x).det = 1 := by
  have hlt : Matrix.BlockTriangular (Loc.uLow x) OrderDual.toDual := by
    intro i j hij
    have hij' : i < j := hij
    simp only [Loc.uLow]
    rw [if_neg (ne_of_lt hij'), dif_neg (lt_asymm hij')]
  rw [Matrix.det_of_lowerTriangular _ hlt]
  simp [Loc.uLow]

theorem det_uUp {n : ℕ} (w : Loc.Pt E n) (y : Loc.IN w → E) : (Loc.uUp w y).det = 1 := by
  have hut : Matrix.BlockTriangular (Loc.uUp w y) id := by
    intro i j hij
    have hij' : j < i := hij
    simp only [Loc.uUp]
    rw [if_neg (ne_of_gt hij'), dif_neg (fun h => lt_asymm hij' h.1)]
  rw [Matrix.det_of_upperTriangular hut]
  simp [Loc.uUp]

theorem bb_ne (Mo : Loc.Model F E) {m : ℕ} (w : Loc.Pt E (m + 1)) (c : Mo.Cls m) (h : Mo.BB w c ≠ 0) :
    ∃ ZZ : Mo.Mat (m + 1), (ZZ.Z.map Mo.R.subtype).det = w.mat.det ∧ Nonempty (Mo.Iso ZZ (Quotient.out c)) := by
  obtain ⟨xy, hxy⟩ : ∃ xy, Mo.bbIntegrand w c xy ≠ 0 := by
    by_contra hc
    push_neg at hc
    apply h
    unfold Loc.Model.BB
    simp [hc]
  unfold Loc.Model.bbIntegrand at hxy
  dsimp only at hxy
  split_ifs at hxy with hZ
  · have h1 := left_ne_zero_of_mul hxy
    rw [Nat.cast_ne_zero] at h1
    unfold Loc.Model.nIso at h1
    refine ⟨_, ?_, (Nat.card_ne_zero.1 h1).1⟩
    show (Loc.uLow xy.1 * w.mat * Loc.uUp w xy.2).det = w.mat.det
    rw [Matrix.det_mul, Matrix.det_mul, det_uLow, det_uUp, one_mul, mul_one]
  · exact absurd rfl hxy

theorem modK_mul_unit (Mo : Loc.Model F E) (x : E) (u : (Mo.R)ˣ) : Mo.modK (x * ((u : Mo.R) : E)) = Mo.modK x := by
  unfold Loc.Model.modK
  congr 2
  ext z
  simp only [Set.mem_image, SetLike.mem_coe]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨((u : Mo.R) : E) * y, Mo.R.mul_mem (u : Mo.R).2 hy, by ring⟩
  · rintro ⟨y, hy, rfl⟩
    refine ⟨(((u⁻¹ : (Mo.R)ˣ) : Mo.R) : E) * y, Mo.R.mul_mem (((u⁻¹ : (Mo.R)ˣ) : Mo.R)).2 hy, ?_⟩
    have e : ((u : Mo.R) : E) * (((u⁻¹ : (Mo.R)ˣ) : Mo.R) : E) = 1 := by
      rw [← MulMemClass.coe_mul, Units.mul_inv]; rfl
    calc x * ((u : Mo.R) : E) * ((((u⁻¹ : (Mo.R)ˣ) : Mo.R) : E) * y)
        = x * (((u : Mo.R) : E) * (((u⁻¹ : (Mo.R)ˣ) : Mo.R) : E)) * y := by ring
      _ = x * y := by rw [e, mul_one]

theorem det_assoc_pts (Mo : Loc.Model F E) {m : ℕ} (a b : Loc.Pt E (m + 1)) (h : Mo.Kk (m + 1) a b ≠ 0) :
    IsUnit a.mat.det ∧ ∃ u : (Mo.R)ˣ, b.mat.det = a.mat.det * ((u : Mo.R) : E) := by
  obtain ⟨c, hc1, hc2⟩ := kk_ne Mo a b h
  obtain ⟨Z1, hZ1, i1⟩ := bb_ne Mo a c hc1
  obtain ⟨Z2, hZ2, i2⟩ := bb_ne Mo b c hc2
  have hreg : ∀ x, Z1.Z.det * x = 0 → x = 0 := by
    intro x hx
    have e := congrArg Mo.R.subtype hx
    rw [map_mul, RingHom.map_det, map_zero] at e
    have e2 := (Z1.unit.mul_right_eq_zero).1 e
    exact Subtype.val_injective (e2.trans (map_zero Mo.R.subtype).symm)
  obtain ⟨u, hu⟩ := det_assoc_of_cok Z1.Z Z2.Z ((Classical.choice i1).1.trans (Classical.choice i2).1.symm) hreg
  refine ⟨hZ1 ▸ Z1.unit, u, ?_⟩
  have e := congrArg Mo.R.subtype hu
  rw [map_mul, RingHom.map_det, RingHom.map_det] at e
  rw [← hZ1, ← hZ2]
  exact e

end LocLemmas

section Spec

variable {D : Formalism.BasicNotions.D7}

def tw (p : PlF D) (n : ℕ) : (D.s.atP p).Ep :=
  match (D.s.atP p).split with
  | some sg => sg.e.symm (1, (-1) ^ n)
  | none => 1

theorem twist_eq (p : PlF D) (s : ℕ) (x : (D.s.atP p).Ep) : twist p s x = tw p s * x := by
  unfold twist tw
  rcases hs : (D.s.atP p).split with _ | sg
  · simp
  · apply sg.e.injective
    ext <;> simp [map_mul]

theorem tw_add (p : PlF D) (m n : ℕ) : tw p (m + n) = tw p m * tw p n := by
  unfold tw
  rcases hs : (D.s.atP p).split with _ | sg
  · simp
  · simp only
    rw [← map_mul, Prod.mk_mul_mk, one_mul, pow_add]

theorem tw_mul_self (p : PlF D) (n : ℕ) : tw p n * tw p n = 1 := by
  unfold tw
  rcases hs : (D.s.atP p).split with _ | sg
  · simp
  · simp only
    rw [← map_mul, Prod.mk_mul_mk, one_mul, ← mul_pow, neg_one_mul, neg_neg, one_pow]
    exact map_one _

def cB (δ : ∀ p, (D.s.atP p).Fp) (p : PlF D) : (D.s.atP p).Ep :=
  algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) * (D.s.atP p).ιE (uP p : D.host.E)

def rho (δ : ∀ p, (D.s.atP p).Fp) (p : PlF D) (x : ℕ) : (D.s.atP p).Ep :=
  Ring.inverse (cB δ p) ^ (D.R.rS - x) * tw p x

def kap (p : PlF D) : (D.s.atP p).Ep := tw p 1 * Ring.inverse (qE p)

theorem blkTop_eq (δ : ∀ p, (D.s.atP p).Fp) (T T' : ℕ) (p : PlF D) :
    ∀ a s t x y, 1 ≤ a → a - 1 ≤ x → a - 1 ≤ y → x + y + 1 = 2 * (a - 1) + s → x ≤ D.R.rS → y ≤ D.R.rS →
      ¬ (x = D.R.rS ∧ y = D.R.rS) → blkTop δ T T' p a s t = rho δ p x * rho δ p y * kap p * (D.s.atP p).ιE t := by
  intro a s t x y ha hx hy hxy hxr hyr hn
  have hc : ¬ (a + s - 1 = D.R.rS + 1 ∧ s = 1) := by
    rintro ⟨h1, h2⟩
    apply hn
    constructor <;> omega
  unfold blkTop
  rw [if_neg hc]
  unfold blkMod
  rw [if_neg hc, sub_zero]
  unfold tMod
  rw [twist_eq]
  have hν : nu D.R.rS a (a + s - 1) = (D.R.rS - x) + (D.R.rS - y) := by
    unfold nu
    omega
  have htw : tw p x * tw p y * tw p 1 = tw p s := by
    rw [← tw_add, ← tw_add]
    have e : x + y + 1 = a - 1 + (a - 1) + s := by omega
    rw [e, tw_add, tw_add, tw_mul_self, one_mul]
  rw [hν, ← Ring.inverse_pow, pow_add, ← htw]
  simp only [rho, kap, cB]
  ring

theorem modPt_blocks (δ : ∀ p, (D.s.atP p).Fp) (T T' : ℕ) (p : PlF D) {n : ℕ} (w : Point D.host.E n)
    (a : Loc.Pt (D.s.atP p).Ep n) (ha : modPt δ T T' p w = some a) :
    a.blocks.map (fun b => ((b.1 : (D.s.atP p).Ep), (b.2 : ℕ))) = mapBlocks (blkTop δ T T' p) 1 w.1 := by
  unfold modPt at ha
  cases hm : modBlocks (blkTop δ T T' p) 1 w.1 with
  | none => rw [hm] at ha; simp at ha
  | some l =>
    rw [hm] at ha
    simp only at ha
    split_ifs at ha with hsz
    simp only [Option.some.injEq] at ha
    subst ha
    exact modBlocks_map (blkTop δ T T' p) w.1 1 l hm

theorem amat_eq (δ : ∀ p, (D.s.atP p).Fp) (T T' : ℕ) (p : PlF D) (w : Point D.host.E (D.R.rS + 1))
    (a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1)) (ha : modPt δ T T' p w = some a) (x y : Fin (D.R.rS + 1))
    (hn : ¬ (x = Fin.last D.R.rS ∧ y = Fin.last D.R.rS)) :
    a.mat x y = rho δ p x * rho δ p y * kap p * (D.s.atP p).ιE (ptMat w x y) := by
  have hx := x.isLt
  have hy := y.isLt
  have h1 := ptEntry_scale (D.s.atP p).ιE (blkTop δ T T' p) (rho δ p) (kap p) D.R.rS
    (blkTop_eq δ T T' p) w.1 1 x y le_rfl (by omega) (by omega)
    (fun h => hn ⟨Fin.ext (by simp only [Fin.val_last]; omega), Fin.ext (by simp only [Fin.val_last]; omega)⟩)
  show Formalism.MainNotions.S.Loc.ptEntryL a.blocks x y = _
  rw [ptEntryL_eq, modPt_blocks δ T T' p w a ha, h1]
  simp [ptMat]

theorem dmin_top (w : Point D.host.E (D.R.rS + 1)) : Dmin w (D.R.rS + 1) = (ptMat w).det := by
  unfold Dmin
  rw [dif_pos le_rfl]
  rfl

theorem dmin_r (w : Point D.host.E (D.R.rS + 1)) :
    Dmin w D.R.rS = ((ptMat w).submatrix Fin.castSucc Fin.castSucc).det := by
  unfold Dmin
  rw [dif_pos (Nat.le_succ _)]
  rfl

theorem det_amat (δ : ∀ p, (D.s.atP p).Fp) (T T' : ℕ) (p : PlF D) (w : Point D.host.E (D.R.rS + 1))
    (a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1)) (ha : modPt δ T T' p w = some a) :
    a.mat.det = ((∏ x : Fin (D.R.rS + 1), rho δ p x) ^ 2 * kap p ^ (D.R.rS + 1)) *
        (D.s.atP p).ιE (Dmin w (D.R.rS + 1)) +
      (a.mat (Fin.last _) (Fin.last _) - rho δ p D.R.rS * rho δ p D.R.rS * kap p *
        (D.s.atP p).ιE (ptMat w (Fin.last _) (Fin.last _))) *
      (((∏ x : Fin D.R.rS, rho δ p x) ^ 2 * kap p ^ D.R.rS) * (D.s.atP p).ιE (Dmin w D.R.rS)) := by
  set B : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep :=
    Matrix.of fun x y => rho δ p x * rho δ p y * kap p * (D.s.atP p).ιE (ptMat w x y) with hBdef
  have hc := det_corner a.mat B (fun x y hxy => by rw [amat_eq δ T T' p w a ha x y hxy]; rfl)
  have hBd : B.det = ((∏ x : Fin (D.R.rS + 1), rho δ p x) ^ 2 * kap p ^ (D.R.rS + 1)) *
      (D.s.atP p).ιE (Dmin w (D.R.rS + 1)) := by
    rw [hBdef, det_scaled, dmin_top]
  have hm : B.submatrix Fin.castSucc Fin.castSucc = Matrix.of fun x y : Fin D.R.rS =>
      rho δ p x * rho δ p y * kap p *
        (D.s.atP p).ιE (((ptMat w).submatrix Fin.castSucc Fin.castSucc) x y) := by
    ext x y
    simp [hBdef]
  have hBm : (B.submatrix Fin.castSucc Fin.castSucc).det =
      ((∏ x : Fin D.R.rS, rho δ p x) ^ 2 * kap p ^ D.R.rS) * (D.s.atP p).ιE (Dmin w D.R.rS) := by
    rw [hm, det_scaled, dmin_r]
  have hBl : B (Fin.last _) (Fin.last _) = rho δ p D.R.rS * rho δ p D.R.rS * kap p *
      (D.s.atP p).ιE (ptMat w (Fin.last _) (Fin.last _)) := by
    simp [hBdef]
  rw [hc, hBd, hBm, hBl]

theorem last_one (w : Point D.host.E (D.R.rS + 1)) (hD : Dmin w D.R.rS ≠ 0) :
    ∃ l0 t, w.1 = l0 ++ [(t, 1)] ∧ (l0.map Prod.snd).sum = D.R.rS := by
  have hne : w.1 ≠ [] := by
    intro h
    have := w.2.2
    rw [h] at this
    simp at this
  obtain ⟨l0, b, hb⟩ : ∃ l0 b, w.1 = l0 ++ [b] := ⟨w.1.dropLast, w.1.getLast hne, (List.dropLast_append_getLast hne).symm⟩
  obtain ⟨t, s⟩ := b
  have hmem := w.2.1 (t, s) (by rw [hb]; simp)
  have hsum : (l0.map Prod.snd).sum + s = D.R.rS + 1 := by
    have := w.2.2
    rw [hb] at this
    simpa using this
  by_cases hs : s = 1
  · subst hs
    exact ⟨l0, t, hb, by omega⟩
  · exfalso
    apply hD
    rw [dmin_r]
    apply Matrix.det_eq_zero_of_row_eq_zero ⟨(l0.map Prod.snd).sum, by have := hmem.2; omega⟩
    intro j
    show ptEntry w.1 (l0.map Prod.snd).sum j.val = 0
    rw [hb, ptEntry_append_ge _ _ _ _ le_rfl]
    split_ifs with hj
    · have := j.isLt
      have := hmem.2
      simp only [ptEntry, Nat.sub_self]
      rw [if_pos ⟨by omega, by omega⟩, if_neg (by omega)]
    · rfl

theorem ptMat_last (w : Point D.host.E (D.R.rS + 1)) (l0 : List (D.host.E × ℕ)) (t : D.host.E)
    (hb : w.1 = l0 ++ [(t, 1)]) (hs : (l0.map Prod.snd).sum = D.R.rS) :
    ptMat w (Fin.last _) (Fin.last _) = t := by
  show ptEntry w.1 (Fin.last D.R.rS).val (Fin.last D.R.rS).val = t
  rw [hb, Fin.val_last, ptEntry_append_ge l0 [(t, 1)] D.R.rS D.R.rS (by omega), if_pos (by omega), hs,
    Nat.sub_self]
  simp [ptEntry]

theorem dmin_snoc (w : Point D.host.E (D.R.rS + 1)) (l0 : List (D.host.E × ℕ)) (t : D.host.E)
    (hb : w.1 = l0 ++ [(t, 1)]) (hs : (l0.map Prod.snd).sum = D.R.rS) :
    Dmin w (D.R.rS + 1) = Dmin w D.R.rS * t := by
  rw [dmin_top, dmin_r]
  have hrow : ∀ j : Fin (D.R.rS + 1), j ≠ Fin.last _ → ptMat w (Fin.last _) j = 0 := by
    intro j hj
    show ptEntry w.1 _ _ = 0
    rw [hb, Fin.val_last, ptEntry_append_ge l0 [(t, 1)] _ _ (by omega), if_neg]
    intro hle
    apply hj
    ext
    simp only [Fin.val_last]
    have := j.isLt
    omega
  let B : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E :=
    Matrix.of fun x y => if x = Fin.last _ ∧ y = Fin.last _ then 0 else ptMat w x y
  have hB0 : B.det = 0 := Matrix.det_eq_zero_of_row_eq_zero (Fin.last _) (fun j => by
    by_cases hj : j = Fin.last _
    · simp [B, hj]
    · simp [B, hj, hrow j hj])
  have hc := det_corner (ptMat w) B (fun x y hxy => by
    simp only [B, Matrix.of_apply]
    rw [if_neg hxy])
  have hsub : B.submatrix Fin.castSucc Fin.castSucc = (ptMat w).submatrix Fin.castSucc Fin.castSucc := by
    ext x y
    simp [B, Fin.castSucc_ne_last]
  have hBl : B (Fin.last _) (Fin.last _) = 0 := by simp [B]
  rw [hc, hB0, hsub, ptMat_last w l0 t hb hs, hBl]
  ring

theorem amat_last (δ : ∀ p, (D.s.atP p).Fp) (T T' : ℕ) (p : PlF D) (w : Point D.host.E (D.R.rS + 1))
    (a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1)) (ha : modPt δ T T' p w = some a) (l0 : List (D.host.E × ℕ))
    (t : D.host.E) (hb : w.1 = l0 ++ [(t, 1)]) (hs : (l0.map Prod.snd).sum = D.R.rS) :
    a.mat (Fin.last _) (Fin.last _) = blkTop δ T T' p (D.R.rS + 1) 1 t := by
  show Formalism.MainNotions.S.Loc.ptEntryL a.blocks (Fin.last D.R.rS).val (Fin.last D.R.rS).val = _
  rw [ptEntryL_eq, modPt_blocks δ T T' p w a ha, hb, mapBlocks_append, Fin.val_last,
    ptEntry_append_ge _ _ _ _ (by rw [mapBlocks_snd]; omega), if_pos (by rw [mapBlocks_snd]; omega),
    mapBlocks_snd, hs, Nat.sub_self]
  simp [mapBlocks, ptEntry, Nat.add_comm 1 D.R.rS]

theorem zeta_snoc (w : Point D.host.E (D.R.rS + 1)) (h0 : Dmin w D.R.rS ≠ 0) (l0 : List (D.host.E × ℕ))
    (t : D.host.E) (hb : w.1 = l0 ++ [(t, 1)]) (hs : (l0.map Prod.snd).sum = D.R.rS) : zetaOf w = t := by
  unfold zetaOf
  rw [dmin_snoc w l0 t hb hs, mul_div_cancel_left₀ t h0]

end Spec

theorem localSupport_holds (D : Formalism.BasicNotions.D7) : Formalism.L2.SG.SupportG.SupportLoc D := by
  intro δ M p _hA T T' w w' hk hK
  have hl : locK M δ T T' p (D.R.rS + 1) w w' ≠ 0 := by
    intro h0
    apply hK
    unfold KtopP
    rw [h0, mul_zero, zero_mul]
  unfold locK at hl
  split at hl
  · rename_i a b ha hb
    obtain ⟨haU, u, hdet⟩ := det_assoc_pts (M p) a b hl
    have ea := det_amat δ T T' p w a ha
    have eb := det_amat δ T T' p w' b hb
    by_cases h0 : Dmin w D.R.rS = 0
    · have h0' : Dmin w' D.R.rS = 0 := by
        unfold kind at hk
        rw [if_pos h0] at hk
        by_contra hne
        rw [if_neg hne] at hk
        exact absurd hk (by simp)
      rw [h0, map_zero, mul_zero, mul_zero, add_zero] at ea
      rw [h0', map_zero, mul_zero, mul_zero, add_zero] at eb
      have hL : IsUnit ((∏ x : Fin (D.R.rS + 1), rho δ p x) ^ 2 * kap p ^ (D.R.rS + 1)) :=
        isUnit_of_mul_isUnit_left (ea ▸ haU)
      have hX : (D.s.atP p).ιE (Dmin w' (D.R.rS + 1)) =
          (D.s.atP p).ιE (Dmin w (D.R.rS + 1)) * (((u : (M p).R)) : (D.s.atP p).Ep) := by
        apply hL.mul_left_cancel
        rw [← eb, hdet, ea]
        ring
      refine ⟨?_, by rw [h0, h0']⟩
      rw [hX, modK_mul_unit]
    · have h0' : Dmin w' D.R.rS ≠ 0 := by
        unfold kind at hk
        rw [if_neg h0] at hk
        intro hne
        rw [if_pos hne] at hk
        exact absurd hk (by simp)
      have hz : zetaOf w = zetaOf w' := by
        unfold kind at hk
        rw [if_neg h0, if_neg h0'] at hk
        exact Option.some.inj hk
      obtain ⟨l0, t, hb0, hs0⟩ := last_one w h0
      obtain ⟨l0', t', hb0', hs0'⟩ := last_one w' h0'
      have htt : t' = t := by
        rw [← zeta_snoc w h0 l0 t hb0 hs0, ← zeta_snoc w' h0' l0' t' hb0' hs0', hz]
      subst htt
      have hL1 : (∏ x : Fin (D.R.rS + 1), rho δ p x) ^ 2 * kap p ^ (D.R.rS + 1) =
          ((∏ x : Fin D.R.rS, rho δ p x) ^ 2 * kap p ^ D.R.rS) * (rho δ p D.R.rS * rho δ p D.R.rS * kap p) := by
        rw [Fin.prod_univ_castSucc]
        simp only [Fin.val_castSucc, Fin.val_last]
        ring
      rw [amat_last δ T T' p w a ha l0 t' hb0 hs0, ptMat_last w l0 t' hb0 hs0, dmin_snoc w l0 t' hb0 hs0, hL1,
        map_mul] at ea
      rw [amat_last δ T T' p w' b hb l0' t' hb0' hs0', ptMat_last w' l0' t' hb0' hs0', dmin_snoc w' l0' t' hb0' hs0',
        hL1, map_mul] at eb
      have ea' : a.mat.det = (((∏ x : Fin D.R.rS, rho δ p x) ^ 2 * kap p ^ D.R.rS) * blkTop δ T T' p (D.R.rS + 1) 1 t') *
          (D.s.atP p).ιE (Dmin w D.R.rS) := by rw [ea]; ring
      have eb' : b.mat.det = (((∏ x : Fin D.R.rS, rho δ p x) ^ 2 * kap p ^ D.R.rS) * blkTop δ T T' p (D.R.rS + 1) 1 t') *
          (D.s.atP p).ιE (Dmin w' D.R.rS) := by rw [eb]; ring
      have hL : IsUnit (((∏ x : Fin D.R.rS, rho δ p x) ^ 2 * kap p ^ D.R.rS) * blkTop δ T T' p (D.R.rS + 1) 1 t') :=
        isUnit_of_mul_isUnit_left (ea' ▸ haU)
      have hY : (D.s.atP p).ιE (Dmin w' D.R.rS) =
          (D.s.atP p).ιE (Dmin w D.R.rS) * (((u : (M p).R)) : (D.s.atP p).Ep) := by
        apply hL.mul_left_cancel
        rw [← eb', hdet, ea']
        ring
      refine ⟨?_, by rw [hY, modK_mul_unit]⟩
      rw [dmin_snoc w l0 t' hb0 hs0, dmin_snoc w' l0' t' hb0' hs0', map_mul, map_mul, hY]
      rw [show (D.s.atP p).ιE (Dmin w D.R.rS) * (((u : (M p).R)) : (D.s.atP p).Ep) * (D.s.atP p).ιE t' =
        (D.s.atP p).ιE (Dmin w D.R.rS) * (D.s.atP p).ιE t' * (((u : (M p).R)) : (D.s.atP p).Ep) by ring,
        modK_mul_unit]
  · exact absurd rfl hl

end Formalism.L2.SG.Pf
