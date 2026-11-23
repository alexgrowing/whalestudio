import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsAdaptedEmpty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockEmb
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousAdelicUnitaryEmbedding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormBlockEmbLeftInvariant
import Development.AutomorphicSpectrum.Definitions.TwistedFlags.WittDecompositionZeroSectionEmbedEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmDataIsCMExtAndGramIsHermND
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.ComplFrame

theorem middle_core {K : Type} [Field K] {n r a d : ℕ} (hd : a + d + a = n)
    (C Ci : Matrix (Fin n) (Fin n) K) (hCi : Ci * C = 1)
    (M : Matrix (Fin n) (Fin r) K) (L : Matrix (Fin r) (Fin n) K) (hL : L * M = 1)
    (hout : ∀ (b : Fin n) (j : Fin r), (b.val < a ∨ n ≤ b.val + a) → (Ci * M) b j = 0)
    (P : Matrix (Fin r) (Fin d) K)
    (hP : ∀ (i : Fin n) (t : Fin d), (M * P) i t = C i ⟨a + t.val, by omega⟩) :
    ∃ hdim : a + r + a = n, ∃ B Bi : Matrix (Fin r) (Fin r) K, B * Bi = 1 ∧
      ∀ (i : Fin n) (j : Fin r), M i j = ∑ t : Fin r, C i (⟨a + t.val, by omega⟩ : Fin n) * B t j := by
  have hCC : C * Ci = 1 := by
    first
      | exact mul_eq_one_comm.mp hCi
      | exact Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _) hCi
  obtain ⟨Cm, hCm⟩ : ∃ Cm : Matrix (Fin n) (Fin d) K, ∀ i t, Cm i t = C i ⟨a + t.val, by omega⟩ :=
    ⟨fun i t => C i ⟨a + t.val, by omega⟩, fun _ _ => rfl⟩
  obtain ⟨Cb, hCb⟩ : ∃ Cb : Matrix (Fin d) (Fin n) K, ∀ t i, Cb t i = Ci ⟨a + t.val, by omega⟩ i :=
    ⟨fun t i => Ci ⟨a + t.val, by omega⟩ i, fun _ _ => rfl⟩
  obtain ⟨B', hB'⟩ : ∃ B' : Matrix (Fin d) (Fin r) K, ∀ t j, B' t j = (Ci * M) ⟨a + t.val, by omega⟩ j :=
    ⟨fun t j => (Ci * M) ⟨a + t.val, by omega⟩ j, fun _ _ => rfl⟩
  have hM : M = Cm * B' := by
    ext i j
    have e1 : M i j = ∑ b : Fin n, C i b * (Ci * M) b j := by
      rw [← Matrix.mul_apply, ← Matrix.mul_assoc, hCC, Matrix.one_mul]
    rw [e1, Matrix.mul_apply]
    symm
    refine Finset.sum_of_injOn (fun t : Fin d => (⟨a + t.val, by omega⟩ : Fin n)) ?_ ?_ ?_ ?_
    · intro t _ t' _ h
      have h' := congrArg Fin.val h
      exact Fin.ext (by simpa using h')
    · intro t _
      simp
    · intro b _ hb
      have hbo : b.val < a ∨ n ≤ b.val + a := by
        by_contra hc
        push Not at hc
        apply hb
        refine ⟨⟨b.val - a, by omega⟩, by simp, Fin.ext ?_⟩
        show a + (b.val - a) = b.val
        omega
      simp [hout b j hbo]
    · intro t _
      simp only [hCm, hB']
  have hMP : M * P = Cm := by
    ext i t
    rw [hP, hCm]
  have hCbm : Cb * Cm = 1 := by
    ext s t
    rw [Matrix.mul_apply]
    simp only [hCb, hCm]
    rw [← Matrix.mul_apply, hCi, Matrix.one_apply, Matrix.one_apply]
    simp [Fin.ext_iff]
  have h1 : P * B' = 1 := by
    calc P * B' = (L * M) * (P * B') := by rw [hL, Matrix.one_mul]
      _ = L * ((M * P) * B') := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hMP, ← hM, hL]
  have h2 : B' * P = 1 := by
    calc B' * P = (Cb * Cm) * (B' * P) := by rw [hCbm, Matrix.one_mul]
      _ = Cb * ((Cm * B') * P) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [← hM, hMP, hCbm]
  have hrd : r = d := by
    apply le_antisymm
    · have h := Matrix.rank_mul_le_left P B'
      rw [h1, Matrix.rank_one, Fintype.card_fin] at h
      exact h.trans (Matrix.rank_le_width P)
    · have h := Matrix.rank_mul_le_left B' P
      rw [h2, Matrix.rank_one, Fintype.card_fin] at h
      exact h.trans (Matrix.rank_le_width B')
  subst hrd
  refine ⟨hd, B', P, h2, fun i j => ?_⟩
  rw [hM, Matrix.mul_apply]
  simp only [hCm]

section Pair

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n m : ℕ} {J : Matrix (Fin n) (Fin n) E} {X Y : Matrix (Fin n) (Fin m) E} {C : GL (Fin n) E}

theorem mulVec_col {p q : Type} [Fintype q] {R : Type} [CommRing R] (A : Matrix p q R) {s : Type} (Z : Matrix q s R) (j : s)
    (l : p) : (A *ᵥ fun k => Z k j) l = (A * Z) l j := rfl

theorem pairY (hW : GlobalTheory.SiegelSet.IsWittFrame σ J X Y) (hyx : Formalism.UG.cT (σ : E →+* E) Y * J * X = 1)
    (hC : GlobalTheory.BlockForms.IsAdapted σ J X Y C) (l : Fin m) (b : Fin n) :
    ((Formalism.UG.cT (σ : E →+* E) Y * J) *ᵥ fun k => C.1 k b) l = if b.val = l.val then 1 else 0 := by
  obtain ⟨-, yy, -, -⟩ := hW
  obtain ⟨hle, colX, columnBlock, -, perpY⟩ := hC
  have hl := l.isLt
  have hb := b.isLt
  by_cases h1 : b.val < m
  · have hcol : (fun k => C.1 k b) = fun k => X k ⟨b.val, h1⟩ :=
      funext fun k => colX b ⟨b.val, h1⟩ rfl k
    rw [hcol, mulVec_col, hyx, Matrix.one_apply]
    by_cases h : b.val = l.val
    · rw [if_pos h, if_pos (Fin.ext h.symm)]
    · rw [if_neg h, if_neg (fun h' => h (congrArg Fin.val h').symm)]
  · by_cases h2 : b.val + m < n
    · rw [perpY b (by omega) h2, if_neg (by omega)]
      rfl
    · have hj : n - 1 - b.val < m := by omega
      have hcol : (fun k => C.1 k b) = fun k => Y k ⟨n - 1 - b.val, hj⟩ :=
        funext fun k => columnBlock b ⟨n - 1 - b.val, hj⟩ (by show b.val + (n - 1 - b.val) + 1 = n; omega) k
      rw [hcol, mulVec_col, yy, if_neg (by omega)]
      rfl

theorem pairX (hW : GlobalTheory.SiegelSet.IsWittFrame σ J X Y)
    (hC : GlobalTheory.BlockForms.IsAdapted σ J X Y C) (l : Fin m) (b : Fin n) :
    ((Formalism.UG.cT (σ : E →+* E) X * J) *ᵥ fun k => C.1 k b) l = if b.val + l.val + 1 = n then 1 else 0 := by
  obtain ⟨xx, -, xy, -⟩ := hW
  obtain ⟨hle, colX, columnBlock, perpX, -⟩ := hC
  have hl := l.isLt
  have hb := b.isLt
  by_cases h1 : b.val < m
  · have hcol : (fun k => C.1 k b) = fun k => X k ⟨b.val, h1⟩ :=
      funext fun k => colX b ⟨b.val, h1⟩ rfl k
    rw [hcol, mulVec_col, xx, if_neg (by omega)]
    rfl
  · by_cases h2 : b.val + m < n
    · rw [perpX b (by omega) h2, if_neg (by omega)]
      rfl
    · have hj : n - 1 - b.val < m := by omega
      have hcol : (fun k => C.1 k b) = fun k => Y k ⟨n - 1 - b.val, hj⟩ :=
        funext fun k => columnBlock b ⟨n - 1 - b.val, hj⟩ (by show b.val + (n - 1 - b.val) + 1 = n; omega) k
      rw [hcol, mulVec_col, xy, Matrix.one_apply]
      by_cases h : b.val + l.val + 1 = n
      · rw [if_pos h, if_pos (Fin.ext (by show l.val = n - 1 - b.val; omega))]
      · rw [if_neg h, if_neg (fun h' => h (by have := congrArg Fin.val h'; simp at this; omega))]

end Pair

section Main

variable {D : D7}

theorem pair_vec (V : HSp D) {p : ℕ} (U : Matrix (Fin V.rank) (Fin p) D.host.E) (w : Fin V.rank → D.host.E) (i : Fin p) :
    ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) U * V.gram) *ᵥ w) i =
      V.hT (V.frame.equivFun.symm fun k => U k i) (V.frame.equivFun.symm w) := by
  have hsig : ∀ x : D.host.E, (D.sp.cm.sig : D.host.E →+* D.host.E) x = starRingEnd D.host.E x :=
    fun _ => rfl
  simp only [Module.Basis.equivFun_symm_apply, map_sum, LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ₂,
    LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Matrix.mulVec,
    dotProduct, Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, hsig,
    Formalism.BasicNotions.HSpace.gram, Finset.mul_sum, Finset.sum_mul, RingHom.id_apply]
  first
    | (refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_; ring)
    | (rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_; ring)

theorem pair_frame (V V' : HSp D) (ι : V'.V →ₗ[D.host.E] V.V) {p : ℕ} (U : Matrix (Fin V.rank) (Fin p) D.host.E) (i : Fin p)
    (j : Fin V'.rank) :
    (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) U * V.gram * frameMat V V' ι) i j =
      V.hT (V.frame.equivFun.symm fun k => U k i) (ι (V'.frame j)) := by
  have h := pair_vec V U (fun l => V.frame.repr (ι (V'.frame j)) l) i
  have he : V.frame.equivFun.symm (fun l => V.frame.repr (ι (V'.frame j)) l) = ι (V'.frame j) :=
    V.frame.equivFun.symm_apply_apply (ι (V'.frame j))
  rw [he] at h
  rw [← h, Matrix.mul_apply]
  simp only [Matrix.mulVec, dotProduct, Formalism.L2.Theta.frameMat, LinearMap.toMatrix_apply]

private theorem cT_mul_global {A : Type} [CommRing A] (σ : A →+* A) {l q s : Type} [Fintype q]
    (M : Matrix l q A) (N : Matrix q s A) :
    Formalism.UG.cT σ (M * N) = Formalism.UG.cT σ N * Formalism.UG.cT σ M := by
  simp only [Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_mul]

private theorem cT_cT_of_involutive_global {A : Type} [CommRing A] (σ : A →+* A) (hσ : ∀ x, σ (σ x) = x) {l q : Type}
    (M : Matrix l q A) : Formalism.UG.cT σ (Formalism.UG.cT σ M) = M := by
  ext i j
  simp [Formalism.UG.cT, hσ]

private theorem cT_one_global {A : Type} [CommRing A] (σ : A →+* A) {q : Type} [DecidableEq q] :
    Formalism.UG.cT σ (1 : Matrix q q A) = 1 := by
  simp [Formalism.UG.cT, Matrix.map_one]

theorem frame_cols : ∀ (D : D7) (V V' : HSp D) (ι : V'.V →ₗ[D.host.E] V.V), HSpace.IsIsomEmb V' V ι →
    ∀ (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y →
    ∀ T : Finset (Fin m), (∀ v : V.V, v ∈ LinearMap.range ι ↔ ∀ i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T, V.hT (V.frame.equivFun.symm fun j => X j i) v = 0 ∧ V.hT (V.frame.equivFun.symm fun j => Y j i) v = 0) →
    ∀ C : GL (Fin V.rank) D.host.E, GlobalTheory.BlockForms.IsAdapted D.sp.cm.sig V.gram X Y C →
    ∀ a : ℕ, a ≤ m → (∀ i : Fin m, i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T ↔ i.val < a) →
    ∃ hdim : a + V'.rank + a = V.rank, ∃ B Bi : Matrix (Fin V'.rank) (Fin V'.rank) D.host.E, B * Bi = 1 ∧
      (∀ (i : Fin V.rank) (j : Fin V'.rank), frameMat V V' ι i j = ∑ r : Fin V'.rank, C.1 i (⟨a + r.val, by omega⟩ : Fin V.rank) * B r j) ∧
      ∀ b : Fin V.rank, (b.val < a ∨ V.rank ≤ b.val + a) →
        (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat V V' ι) * V.gram) *ᵥ (fun k => C.1 k b) = 0 := by
  intro D V V' ι hiso m X Y hW T hTr C hC a ham hup
  have hsig : ∀ x : D.host.E, (D.sp.cm.sig : D.host.E →+* D.host.E) x = starRingEnd D.host.E x :=
    fun _ => rfl
  have hinvol : ∀ x : D.host.E, (D.sp.cm.sig : D.host.E →+* D.host.E)
      ((D.sp.cm.sig : D.host.E →+* D.host.E) x) = x := fun x => by simp [hsig]
  have hle : 2 * m ≤ V.rank := hC.le
  have hherm : ∀ x y : V.V, V.hT y x = starRingEnd D.host.E (V.hT x y) := by
    intro x y
    have hs := V.herm
    first
      | exact (hs x y).symm
      | exact (hs.eq x y).symm
  have hG : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram = V.gram := by
    ext k l
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, hsig, Formalism.BasicNotions.HSpace.gram]
    exact (hherm _ _).symm
  have hyx : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Y * V.gram * X = 1 := by
    have h := congrArg (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E)) hW.xy
    rw [cT_mul_global, cT_mul_global, cT_cT_of_involutive_global _ hinvol, hG, cT_one_global, ← Matrix.mul_assoc] at h
    exact h
  have hperp : ∀ v ∈ LinearMap.range ι, ∀ i : Fin m, i.val < a →
      V.hT (V.frame.equivFun.symm fun j => X j i) v = 0 ∧
        V.hT (V.frame.equivFun.symm fun j => Y j i) v = 0 :=
    fun v hv i hi => (hTr v).1 hv i ((hup i).2 hi)
  have hmid : ∀ b : Fin V.rank, a ≤ b.val → b.val + a < V.rank →
      V.frame.equivFun.symm (fun k => C.1 k b) ∈ LinearMap.range ι := by
    intro b hb1 hb2
    refine (hTr _).2 fun i hi => ?_
    have hi' := (hup i).1 hi
    constructor
    · rw [← pair_vec V X (fun k => C.1 k b) i, pairX hW hC i b, if_neg (by omega)]
    · rw [← pair_vec V Y (fun k => C.1 k b) i, pairY hW hyx hC i b, if_neg (by omega)]
  have hw : ∀ t : Fin (V.rank - a - a), ∃ w : V'.V,
      ι w = V.frame.equivFun.symm (fun k => C.1 k ⟨a + t.val, by omega⟩) := fun t =>
    LinearMap.mem_range.mp (hmid _ (Nat.le_add_right _ _) (by show a + t.val + a < V.rank; omega))
  choose w hw using hw
  obtain ⟨P, hPdef⟩ : ∃ P : Matrix (Fin V'.rank) (Fin (V.rank - a - a)) D.host.E,
      ∀ k t, P k t = V'.frame.repr (w t) k := ⟨fun k t => V'.frame.repr (w t) k, fun _ _ => rfl⟩
  have hP : ∀ (i : Fin V.rank) (t : Fin (V.rank - a - a)),
      (Formalism.L2.Theta.frameMat V V' ι * P) i t = C.1 i ⟨a + t.val, by omega⟩ := by
    intro i t
    calc (Formalism.L2.Theta.frameMat V V' ι * P) i t
        = (LinearMap.toMatrix V'.frame V.frame ι *ᵥ ⇑(V'.frame.repr (w t))) i := by
          simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, hPdef, Formalism.L2.Theta.frameMat]
      _ = V.frame.repr (ι (w t)) i :=
          congrFun (LinearMap.toMatrix_mulVec_repr V'.frame V.frame ι (w t)) i
      _ = C.1 i ⟨a + t.val, by omega⟩ := by
          rw [hw t]
          exact congrFun (V.frame.equivFun.apply_symm_apply _) i
  have hinj : Function.Injective ι := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    apply V'.nondeg.1 x
    intro y
    rw [← hiso x y, hx, map_zero, LinearMap.zero_apply]
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective ι (LinearMap.ker_eq_bot.mpr hinj)
  have hL : LinearMap.toMatrix V.frame V'.frame g * Formalism.L2.Theta.frameMat V V' ι = 1 := by
    show LinearMap.toMatrix V.frame V'.frame g * LinearMap.toMatrix V'.frame V.frame ι = 1
    rw [← LinearMap.toMatrix_comp, hg, LinearMap.toMatrix_id]
  have key : ∀ (A : Matrix (Fin m) (Fin V.rank) D.host.E) (l : Fin m) (c0 : Fin V.rank),
      (∀ c, (A *ᵥ fun k => C.1 k c) l = if c = c0 then 1 else 0) →
      ∀ j, (A * Formalism.L2.Theta.frameMat V V' ι) l j =
        ((↑C⁻¹ : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * Formalism.L2.Theta.frameMat V V' ι) c0 j := by
    intro A l c0 hA j
    have hM' : Formalism.L2.Theta.frameMat V V' ι =
        C.1 * ((↑C⁻¹ : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * Formalism.L2.Theta.frameMat V V' ι) := by
      rw [← Matrix.mul_assoc, C.mul_inv, Matrix.one_mul]
    conv_lhs => rw [hM']
    rw [← Matrix.mul_assoc, Matrix.mul_apply, Finset.sum_eq_single c0]
    · rw [← mulVec_col, hA, if_pos rfl, one_mul]
    · intro c _ hc
      rw [← mulVec_col, hA, if_neg hc, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ c0) h
  have hout : ∀ (b : Fin V.rank) (j : Fin V'.rank), (b.val < a ∨ V.rank ≤ b.val + a) →
      ((↑C⁻¹ : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * Formalism.L2.Theta.frameMat V V' ι) b j = 0 := by
    intro b j hb
    have hbl := b.isLt
    rcases hb with hb | hb
    · have hlm : b.val < m := by omega
      rw [← key (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Y * V.gram) ⟨b.val, hlm⟩ b ?_ j]
      · rw [pair_frame]
        exact (hperp _ (LinearMap.mem_range_self ι _) ⟨b.val, hlm⟩ hb).2
      · intro c
        rw [pairY hW hyx hC _ c]
        exact if_congr ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩ rfl rfl
    · have hlm : V.rank - 1 - b.val < m := by omega
      rw [← key (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X * V.gram) ⟨V.rank - 1 - b.val, hlm⟩ b ?_ j]
      · rw [pair_frame]
        exact (hperp _ (LinearMap.mem_range_self ι _) ⟨V.rank - 1 - b.val, hlm⟩ (by show V.rank - 1 - b.val < a; omega)).1
      · intro c
        have hcl := c.isLt
        rw [pairX hW hC _ c]
        refine if_congr ⟨fun h => Fin.ext ?_, fun h => ?_⟩ rfl rfl
        · have h' : c.val + (V.rank - 1 - b.val) + 1 = V.rank := h
          omega
        · subst h
          show c.val + (V.rank - 1 - c.val) + 1 = V.rank
          omega
  obtain ⟨hdim, B, Bi, hBB, hcols⟩ := middle_core (n := V.rank) (r := V'.rank) (a := a)
    (d := V.rank - a - a) (by omega) C.1 (↑C⁻¹) C.inv_mul (Formalism.L2.Theta.frameMat V V' ι)
    (LinearMap.toMatrix V.frame V'.frame g) hL hout P hP
  refine ⟨hdim, B, Bi, hBB, hcols, fun b hb => ?_⟩
  funext j
  rw [pair_vec V (Formalism.L2.Theta.frameMat V V' ι) (fun k => C.1 k b) j]
  have hcolj : (fun k => Formalism.L2.Theta.frameMat V V' ι k j) = ⇑(V.frame.repr (ι (V'.frame j))) := by
    funext k
    simp only [Formalism.L2.Theta.frameMat, LinearMap.toMatrix_apply]
  have hvj : V.frame.equivFun.symm (fun k => Formalism.L2.Theta.frameMat V V' ι k j) = ι (V'.frame j) := by
    rw [hcolj]
    exact V.frame.equivFun.symm_apply_apply _
  rw [hvj, hherm, Pi.zero_apply]
  have hbl := b.isLt
  rcases hb with hb | hb
  · have hlm : b.val < m := by omega
    have hcol : (fun k => C.1 k b) = fun k => X k ⟨b.val, hlm⟩ :=
      funext fun k => hC.colX b ⟨b.val, hlm⟩ rfl k
    rw [hcol, (hperp _ (LinearMap.mem_range_self ι _) ⟨b.val, hlm⟩ hb).1, map_zero]
  · have hlm : V.rank - 1 - b.val < m := by omega
    have hcol : (fun k => C.1 k b) = fun k => Y k ⟨V.rank - 1 - b.val, hlm⟩ :=
      funext fun k => hC.columnBlock b ⟨V.rank - 1 - b.val, hlm⟩
        (by show b.val + (V.rank - 1 - b.val) + 1 = V.rank; omega) k
    rw [hcol, (hperp _ (LinearMap.mem_range_self ι _) ⟨V.rank - 1 - b.val, hlm⟩
      (by show V.rank - 1 - b.val < a; omega)).2, map_zero]

end Main

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.ComplFrame
end
