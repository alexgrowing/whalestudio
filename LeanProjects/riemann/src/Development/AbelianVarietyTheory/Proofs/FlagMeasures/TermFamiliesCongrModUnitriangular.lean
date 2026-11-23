import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
open Formalism.MainNotions.S

namespace GlobalTheory.SlocCong

theorem stab_of_flag {E : Type} [CommRing E] {V : Type} [AddCommGroup V] [Module E V] {n : ℕ}
    (f : Fin n → V) (g : V →ₗ[E] V)
    (hg : ∀ a, g (f a) - f a ∈ Submodule.span E (f '' {c | c < a})) (a : Fin n) :
    ∀ v ∈ Submodule.span E (f '' {c | c < a}), g v ∈ Submodule.span E (f '' {c | c < a}) := by
  intro v hv
  have : Submodule.span E (f '' {c | c < a}) ≤ (Submodule.span E (f '' {c | c < a})).comap g := by
    rw [Submodule.span_le]
    rintro _ ⟨c, hc, rfl⟩
    have h1 : Submodule.span E (f '' {c' | c' < c}) ≤ Submodule.span E (f '' {c | c < a}) :=
      Submodule.span_mono (Set.image_mono fun c' (hc' : c' < c) => (show c' < a from lt_trans hc' hc))
    have h2 : f c ∈ Submodule.span E (f '' {c | c < a}) := Submodule.subset_span ⟨c, hc, rfl⟩
    have := Submodule.add_mem _ (h1 (hg c)) h2
    simpa using this
  exact this hv

theorem exists_unitri {R : Type} [CommRing R] {n : ℕ} (W W' : Matrix (Fin n) (Fin n) R)
    (hW : ∀ a b, b < a → W a b = 0) (hW' : ∀ a b, b < a → W' a b = 0) (hd : ∀ a, W' a a = W a a)
    (hu : ∀ a, IsUnit (W a a)) :
    ∃ ξ : Matrix (Fin n) (Fin n) R, (∀ a b, b < a → ξ a b = 0) ∧ (∀ a, ξ a a = 1) ∧ W * ξ = W' := by
  have hbt : W.BlockTriangular id := fun i j h => hW i j h
  have hbt' : W'.BlockTriangular id := fun i j h => hW' i j h
  have hdet : IsUnit W.det := by
    rw [Matrix.det_of_upperTriangular hbt]
    exact IsUnit.prod_univ_iff.2 hu
  haveI := W.invertibleOfIsUnitDet hdet
  have hinv : W⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hbt
  have diag : ∀ P Q : Matrix (Fin n) (Fin n) R, P.BlockTriangular id → Q.BlockTriangular id →
      ∀ a, (P * Q) a a = P a a * Q a a := by
    intro P Q hP hQ a
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_single a (fun c _ hc => ?_) (by simp)
    rcases lt_or_gt_of_ne hc with h | h
    · rw [hP h, zero_mul]
    · rw [hQ h, mul_zero]
  refine ⟨W⁻¹ * W', fun a b h => (hinv.mul hbt') h, fun a => ?_, ?_⟩
  · rw [diag _ _ hinv hbt', hd, ← diag _ _ hinv hbt, Matrix.nonsing_inv_mul _ hdet, Matrix.one_apply_eq]
  · rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mul]

end GlobalTheory.SlocCong

namespace GlobalTheory.SlocCong

theorem flag_of_mem_N {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E} {V : Type} [AddCommGroup V]
    [Module E V] {H : Loc.HermSp M V} {r : ℕ} (Fr : LocNG.FrameD H r) (g : V ≃ₗ[E] V) (hg : g ∈ Fr.N)
    (a : Fin (r + 1)) : g (Fr.f a) - Fr.f a ∈ Submodule.span E (Fr.f '' {c | c < a}) := by
  classical
  have fmem : ∀ c a : Fin (r + 1), c < a → Fr.f c ∈ Submodule.span E (Fr.f '' {c | c < a}) :=
    fun c a h => Submodule.subset_span ⟨c, h, rfl⟩
  have Smono : ∀ a b : Fin (r + 1), a ≤ b →
      Submodule.span E (Fr.f '' {c | c < a}) ≤ Submodule.span E (Fr.f '' {c | c < b}) :=
    fun a b h => Submodule.span_mono (Set.image_mono fun c (hc : c < a) => (show c < b from lt_of_lt_of_le hc h))
  let Q : (V ≃ₗ[E] V) → Prop := fun g => ∀ a, g (Fr.f a) - Fr.f a ∈ Submodule.span E (Fr.f '' {c | c < a})
  suffices hQ : Q g from hQ a
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨-, hflag, hperp⟩ := hg
    intro a
    rcases Fin.eq_castSucc_or_eq_last a with ⟨i, rfl⟩ | rfl
    · have hv : Fr.f i.castSucc ∈ Fr.Fj (i.val + 1) :=
        Submodule.subset_span ⟨i, by simp, rfl⟩
      have := hflag (i.val + 1) (by omega) _ hv
      simp only [Nat.add_sub_cancel] at this
      refine (Submodule.span_le.2 ?_) this
      rintro _ ⟨b, hb, rfl⟩
      exact fmem b.castSucc i.castSucc (Fin.castSucc_lt_castSucc_iff.2 (Fin.lt_def.2 hb))
    · have hz : Fr.f (Fin.last r) ∈ H.perp (H.X Fr.f) := by
        intro x hx
        have h0 : H.h x (Fr.f (Fin.last r)) = 0 := by
          induction hx using Submodule.span_induction with
          | mem x hx =>
            obtain ⟨b, rfl⟩ := hx
            exact Fr.h_iso _ _ (Or.inl (Fin.castSucc_ne_last b))
          | zero => exact H.h_zero_left _
          | add x y _ _ hx hy => rw [H.h_add_left, hx, hy, add_zero]
          | smul c x _ hx => rw [H.h_smul_left, hx, mul_zero]
        rw [H.h_herm, h0, map_zero]
      have := hperp _ hz
      refine (Submodule.span_le.2 ?_) this
      rintro _ ⟨b, rfl⟩
      exact fmem b.castSucc (Fin.last r) (Fin.castSucc_lt_last b)
  | one => intro a; simp
  | mul g h _ _ hg hh =>
    intro a
    have := Submodule.add_mem _
      (stab_of_flag Fr.f (g : V →ₗ[E] V) hg a _ (hh a)) (hg a)
    convert this using 1
    simp only [LinearEquiv.coe_coe, map_sub, LinearEquiv.mul_apply]
    abel
  | inv g _ hg =>
    intro a
    induction a using WellFoundedLT.induction with
    | _ a ih =>
      have hst : ∀ v ∈ Submodule.span E (Fr.f '' {c | c < a}),
          g⁻¹ v ∈ Submodule.span E (Fr.f '' {c | c < a}) := by
        intro v hv
        have : Submodule.span E (Fr.f '' {c | c < a}) ≤
            (Submodule.span E (Fr.f '' {c | c < a})).comap (g⁻¹ : V ≃ₗ[E] V).toLinearMap := by
          rw [Submodule.span_le]
          rintro _ ⟨c, hc, rfl⟩
          have := Submodule.add_mem _ (Smono c a (le_of_lt hc) (ih c hc)) (fmem c a hc)
          simpa using this
        exact this hv
      have := Submodule.neg_mem _ (hst _ (hg a))
      convert this using 1
      simp [map_sub]
end GlobalTheory.SlocCong

namespace GlobalTheory.SlocCong

theorem coords_of_flag {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E} {V : Type} [AddCommGroup V]
    [Module E V] {H : Loc.HermSp M V} {r : ℕ} (Fr : LocNG.FrameD H r) (L : Submodule M.L.O (H.Wb Fr.f))
    (g : V ≃ₗ[E] V) (hg : ∀ a, g (Fr.f a) - Fr.f a ∈ Submodule.span E (Fr.f '' {c | c < a}))
    (y : Fin (r + 1) → V) (B : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hB : ∀ a b, b < a → B a b = 0) (hBO : ∀ a, B a a ∈ M.L.O)
    (hy : ∀ b, y b = ∑ a, B a b • Fr.f a) (hyL : ∀ b, g (y b) ∈ Fr.LamStd L) :
    ∃ W : Matrix (Fin (r + 1)) (Fin (r + 1)) E, (∀ a b, b < a → W a b = 0) ∧ (∀ a, W a a = B a a) ∧
      (∀ a b, W a b ∈ M.L.O) ∧ ∀ b, g (y b) = ∑ c, W c b • Fr.f c := by
  classical
  have hLam : ∀ v ∈ Fr.LamStd L, ∀ i, H.h v (Fr.es i) ∈ M.L.O := by
    intro v hv i
    induction hv using Submodule.span_induction with
    | mem x hx => exact hx.1 i
    | zero => rw [H.h_zero_left]; exact M.L.O.zero_mem
    | add x y _ _ hx hy => rw [H.h_add_left]; exact M.L.O.add_mem hx hy
    | smul a x _ hx =>
      rw [show a • x = (a : E) • x from rfl, H.h_smul_left]
      exact M.L.O.mul_mem a.2 hx
  have hsum : ∀ (w : V) (c : Fin (r + 1) → E),
      H.h (∑ a, c a • Fr.f a) w = ∑ a, c a * H.h (Fr.f a) w := by
    intro w c
    let φ : V →ₗ[E] E :=
      { toFun := fun v => H.h v w
        map_add' := fun x y => H.h_add_left x y w
        map_smul' := fun a x => by simp [H.h_smul_left] }
    rw [show H.h (∑ a, c a • Fr.f a) w = φ (∑ a, c a • Fr.f a) from rfl, map_sum]
    simp [φ, H.h_smul_left]
  have hex : ∀ b, ∃ l : Fin (r + 1) →₀ E, (∀ c, ¬ c < b → l c = 0) ∧
      g (y b) = B b b • Fr.f b + ∑ c, l c • Fr.f c := by
    intro b
    have hmem : g (y b) - B b b • Fr.f b ∈ Submodule.span E (Fr.f '' {c | c < b}) := by
      have e1 : g (y b) - B b b • Fr.f b =
          ∑ a, (B a b • g (Fr.f a) - if a = b then B b b • Fr.f b else 0) := by
        rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' Finset.univ b, if_pos (Finset.mem_univ _), hy b]
        simp [map_sum, map_smul]
      rw [e1]
      refine Submodule.sum_mem _ fun a _ => ?_
      rcases lt_trichotomy a b with h | rfl | h
      · rw [if_neg (ne_of_lt h), sub_zero]
        refine Submodule.smul_mem _ _ ?_
        exact stab_of_flag Fr.f (g : V →ₗ[E] V) hg b _ (Submodule.subset_span ⟨a, h, rfl⟩)
      · rw [if_pos rfl, ← smul_sub]
        exact Submodule.smul_mem _ _ (hg a)
      · rw [hB a b h, if_neg (ne_of_gt h), zero_smul, sub_zero]
        exact Submodule.zero_mem _
    obtain ⟨l, hl, hlc⟩ := (Finsupp.mem_span_image_iff_linearCombination E).1 hmem
    refine ⟨l, fun c hc => ?_, ?_⟩
    · by_contra hne
      exact hc (hl (Finsupp.mem_support_iff.2 hne))
    · rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)] at hlc
      rw [hlc]; abel
  choose l hl0 hlsum using hex
  refine ⟨Matrix.of fun c b => l b c + if c = b then B b b else 0, ?_, ?_, ?_, ?_⟩
  · intro a b h
    simp [hl0 b a (not_lt.2 (le_of_lt h)), ne_of_gt h]
  · intro a
    simp [hl0 a a (lt_irrefl a)]
  · have hcoord : ∀ b, ∀ c, c ≠ Fin.last r → l b c + (if c = b then B b b else 0) ∈ M.L.O := by
      intro b c hc
      obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.2 hc
      have hv := hLam _ (hyL b) i
      have eqv : g (y b) = ∑ c, (l b c + if c = b then B b b else 0) • Fr.f c := by
        simp only [add_smul, Finset.sum_add_distrib, ite_smul, zero_smul, Finset.sum_ite_eq',
          Finset.mem_univ, if_true]
        rw [hlsum b]; abel
      rw [eqv, hsum] at hv
      rw [Finset.sum_eq_single i.castSucc] at hv
      · rw [Fr.h_es i i, if_pos rfl, mul_one] at hv
        exact hv
      · intro c _ hc'
        rcases Fin.eq_castSucc_or_eq_last c with ⟨j, rfl⟩ | rfl
        · rw [Fr.h_es j i, if_neg (show j ≠ i from fun h => hc' (h ▸ rfl)), mul_zero]
        · rw [H.h_herm, Fr.h_sz, map_zero, mul_zero]
      · simp
    intro c b
    by_cases hc : c = Fin.last r
    · subst hc
      simp only [Matrix.of_apply]
      rw [hl0 b (Fin.last r) (not_lt.2 (Fin.le_last b))]
      split_ifs with h
      · subst h; simpa using hBO (Fin.last r)
      · simpa using M.L.O.zero_mem
    · exact hcoord b c hc
  · intro b
    simp only [Matrix.of_apply, add_smul, Finset.sum_add_distrib, ite_smul, zero_smul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    rw [hlsum b]; abel
end GlobalTheory.SlocCong

namespace GlobalTheory

theorem loc_cong_unitri : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) {r : ℕ} (P : LocNG.FPair H r) (d : LocNG.Datum P) (τ : Loc.Term V M r) (sg : Loc.SplitG M.L), M.split = some sg → LocNG.IsTermOver P d τ → ∀ (y x : Fin (r + 1) → V) (B B' : Matrix (Fin (r + 1)) (Fin (r + 1)) E), (∀ a b, b < a → B a b = 0) → (∀ a b, b < a → B' a b = 0) → (∀ a, B' a a = B a a) → (∀ a, B a a ∈ M.L.O ∧ ∃ t ∈ M.L.O, t * B a a = 1) → (∀ b, y b = ∑ a, B a b • P.A.f a) → (∀ b, x b = ∑ a, B' a b • P.B.f a) → (∀ a, y a ∈ τ.abelian₂) → (∀ b, x b ∈ τ.abelian₂) → ∃ ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) E, (∀ a b, ξ a b ∈ M.L.O) ∧ (∀ a b, b < a → ξ a b = 0) ∧ (∀ a, ξ a a = 1) ∧ ∀ b, x b - ∑ a, ξ a b • y a ∈ H.smulLat (algebraMap F E (sg.q : F)) τ.abelian₂ := by
  intro F _ _ _ E _ _ _ _ M V _ _ H r P d τ sg hsg hτ y x B B' hB hB' hd hu hy hx hyL hxL
  obtain ⟨-, -, ⟨n, hn, hf, hL⟩, ⟨n', hn', hf', hL'⟩, hadm⟩ := hτ
  have hyL' : ∀ b, n⁻¹ (y b) ∈ P.A.LamStd d.L := by
    intro b
    have := hyL b
    rw [hL] at this
    obtain ⟨u, hu, hu'⟩ := Submodule.mem_map.1 this
    have : n⁻¹ (y b) = u := by
      rw [← hu']; simp
    rw [this]; exact hu
  have hxL' : ∀ b, n'⁻¹ (x b) ∈ P.B.LamStd d.L' := by
    intro b
    have := hxL b
    rw [hL'] at this
    obtain ⟨u, hu, hu'⟩ := Submodule.mem_map.1 this
    have : n'⁻¹ (x b) = u := by
      rw [← hu']; simp
    rw [this]; exact hu
  obtain ⟨W, hWt, hWd, hWO, hWy⟩ := SlocCong.coords_of_flag P.A d.L n⁻¹
    (SlocCong.flag_of_mem_N P.A n⁻¹ (inv_mem hn)) y B hB (fun a => (hu a).1) hy hyL'
  obtain ⟨W', hWt', hWd', hWO', hWx⟩ := SlocCong.coords_of_flag P.B d.L' n'⁻¹
    (SlocCong.flag_of_mem_N P.B n'⁻¹ (inv_mem hn')) x B' hB' (fun a => hd a ▸ (hu a).1) hx hxL'
  have hy2 : ∀ a, y a = ∑ c, W c a • τ.f c := by
    intro a
    have := congrArg n (hWy a)
    simp only [map_sum, map_smul] at this
    rw [hf]
    simpa using this
  have hx2 : ∀ b, x b = ∑ c, W' c b • τ.f' c := by
    intro b
    have := congrArg n' (hWx b)
    simp only [map_sum, map_smul] at this
    rw [hf']
    simpa using this
  let WO : Matrix (Fin (r + 1)) (Fin (r + 1)) M.L.O := Matrix.of fun a b => ⟨W a b, hWO a b⟩
  let WO' : Matrix (Fin (r + 1)) (Fin (r + 1)) M.L.O := Matrix.of fun a b => ⟨W' a b, hWO' a b⟩
  have hunit : ∀ a, IsUnit (WO a a) := by
    intro a
    obtain ⟨t, ht, ht1⟩ := (hu a).2
    refine isUnit_iff_exists_inv.2 ⟨⟨t, ht⟩, ?_⟩
    apply Subtype.ext
    simp [WO, hWd, mul_comm, ht1]
  obtain ⟨ξO, hξt, hξd, hξ⟩ := SlocCong.exists_unitri WO WO'
    (fun a b h => Subtype.ext (by simp [WO, hWt a b h]))
    (fun a b h => Subtype.ext (by simp [WO', hWt' a b h]))
    (fun a => Subtype.ext (by simp [WO, WO', hWd, hWd', hd]))
    hunit
  have hWξ : ∀ c b, W' c b = ∑ a, W c a * (ξO a b : E) := by
    intro c b
    have := congrArg (fun m => ((m c b : M.L.O) : E)) hξ
    simp [Matrix.mul_apply, WO, WO'] at this
    exact this.symm
  refine ⟨fun a b => (ξO a b : E), fun a b => (ξO a b).2, fun a b h => by simp [hξt a b h],
    fun a => by simp [hξd a], fun b => ?_⟩
  have hadm' := (hadm sg hsg).1
  have key : x b - ∑ a, (ξO a b : E) • y a = ∑ c, W' c b • (τ.f' c - τ.f c) := by
    simp only [hy2, Finset.smul_sum, smul_smul, smul_sub, Finset.sum_sub_distrib, hx2 b]
    rw [Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hWξ c b, Finset.sum_smul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mul_comm]
  rw [key]
  refine Submodule.sum_mem _ fun c _ => ?_
  have := Submodule.smul_mem _ (⟨W' c b, hWO' c b⟩ : M.L.O) (hadm' c)
  exact this

end GlobalTheory
