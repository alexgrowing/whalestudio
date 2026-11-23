import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc Topology Filter Matrix

namespace GlobalTheory.CompanionTheory.ExpandN

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem nhdsNE_zero_neBot : (𝓝[≠] (0 : k)).NeBot := by
  letI := IsTopologicalAddGroup.rightUniformSpace k
  haveI := isUniformAddGroup_of_addCommGroup (G := k)
  letI : (Valued.v (R := k)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  open scoped Valued in
  exact NormedField.nhdsNE_neBot (0 : k)

theorem exists_one_add_smul_mem_unipRad {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
    [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
    (e : (Σ a, m a) ≃ n) {u : GL n k} (hu : u ∈ unipRad k e) (c : k) :
    ∃ v : GL n k, (v : Matrix n n k) = 1 + c • ((u : Matrix n n k) - 1) ∧ v ∈ unipRad k e := by
  obtain ⟨hP, hD⟩ := mem_unipRad.1 hu
  have hsame : ∀ i j, blk e i = blk e j → (u : Matrix n n k) i j = (1 : Matrix n n k) i j := by
    intro i j hij
    obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective j
    obtain rfl : a = b := by simpa using hij
    rw [hD a i j, Matrix.one_apply, Matrix.one_apply]
    simp
  set M : Matrix n n k := 1 + c • ((u : Matrix n n k) - 1) with hM
  have hMsame : ∀ i j, blk e i = blk e j → M i j = (1 : Matrix n n k) i j := by
    intro i j hij
    simp [hM, hsame i j hij]
  have hT : M.BlockTriangular (blk e) := by
    intro i j hij
    have hne : i ≠ j := by
      rintro rfl
      exact lt_irrefl _ hij
    have h0 : (u : Matrix n n k) i j = 0 := mem_parab.1 hP i j hij
    simp [hM, h0, Matrix.one_apply_ne hne]
  have hdet : M.det = 1 := by
    rw [hT.det_fintype]
    refine Finset.prod_eq_one fun a _ => ?_
    have : M.toSquareBlock (blk e) a = 1 := by
      ext ⟨i, hi⟩ ⟨j, hj⟩
      rw [Matrix.toSquareBlock_def]
      simp only [Matrix.of_apply]
      rw [hMsame i j (hi.trans hj.symm), Matrix.one_apply, Matrix.one_apply]
      simp
    rw [this, Matrix.det_one]
  obtain ⟨v, hv⟩ : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).2 (by simp [hdet])
  refine ⟨v, hv, mem_unipRad.2 ⟨mem_parab.2 fun i j hij => ?_, fun a i j => ?_⟩⟩
  · rw [hv]; exact hT hij
  · rw [hv, hMsame _ _ (by simp), Matrix.one_apply, Matrix.one_apply]
    simp

theorem val_conj_one_add_smul {n : Type} [Fintype n] [DecidableEq n] (G u v : GL n k) (c : k)
    (hv : (v : Matrix n n k) = 1 + c • ((u : Matrix n n k) - 1)) :
    ((G * v * G⁻¹ : GL n k) : Matrix n n k) =
      1 + c • (((G * u * G⁻¹ : GL n k) : Matrix n n k) - 1) := by
  have h1 : (G : Matrix n n k) * ((G⁻¹ : GL n k) : Matrix n n k) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  simp only [Units.val_mul, hv, mul_add, add_mul, mul_sub, sub_mul, mul_one,
    Matrix.mul_smul, Matrix.smul_mul, h1]

theorem exists_pow_conj_mem_KN : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N h : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N)
    (J : Subgroup (GL (Fin N) k)), IsOpen (J : Set (GL (Fin N) k)) →
    IsCompact (J : Set (GL (Fin N) k)) → HasIwahoriFact k N J d hd → (∀ a, 0 < d a) →
    ∀ t : Levi k (Bl d), IsStrictlyDominant k N J d hd t →
    ∀ n ∈ unipRad k (stdBlocks d hd), ∃ r : ℕ,
      leviEmb k (stdBlocks d hd) t ^ r * n * (leviEmb k (stdBlocks d hd) t ^ r)⁻¹ ∈ KN k N J d hd := by
  intro k _ _ _ _ N h d hd J hJo _ _ _ t ht n hn
  obtain ⟨O, hO, hOJ⟩ := (GlobalTheory.SplitFlip.isEmbedding_val_GL (k := k) (n := Fin N)).isInducing.isOpen_iff.1 hJo
  have memJ : ∀ x : GL (Fin N) k, x ∈ J ↔ (x : Matrix (Fin N) (Fin N) k) ∈ O := by
    intro x
    have : x ∈ (J : Set (GL (Fin N) k)) ↔ x ∈ (fun g : GL (Fin N) k => g.val) ⁻¹' O := by rw [hOJ]
    exact this
  have h1O : (1 : Matrix (Fin N) (Fin N) k) ∈ O := by
    simpa using (memJ 1).1 J.one_mem
  set X : Matrix (Fin N) (Fin N) k := (n : Matrix (Fin N) (Fin N) k) - 1 with hX
  haveI := nhdsNE_zero_neBot (k := k)
  have hcont : Continuous fun c : k => (1 : Matrix (Fin N) (Fin N) k) + c • X :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hev : ∀ᶠ c in 𝓝[≠] (0 : k), (1 : Matrix (Fin N) (Fin N) k) + c • X ∈ O := by
    have : ∀ᶠ c in 𝓝 (0 : k), (1 : Matrix (Fin N) (Fin N) k) + c • X ∈ O :=
      hcont.continuousAt.eventually_mem (hO.mem_nhds (by simpa using h1O))
    exact this.filter_mono nhdsWithin_le_nhds
  obtain ⟨c, hcO, hc0⟩ := (hev.and self_mem_nhdsWithin).exists
  have hc0' : c ≠ 0 := hc0
  obtain ⟨v, hv, hvN⟩ := exists_one_add_smul_mem_unipRad (stdBlocks d hd) hn c
  have hvJ : v ∈ J := (memJ v).2 (by rw [hv]; exact hcO)
  let U : Set (GL (Fin N) k) := (fun g : GL (Fin N) k =>
    (1 : Matrix (Fin N) (Fin N) k) + c⁻¹ • ((g : Matrix (Fin N) (Fin N) k) - 1)) ⁻¹' O
  have hU : IsOpen U := by
    refine hO.preimage ?_
    have hs : Continuous fun g : GL (Fin N) k => (g : Matrix (Fin N) (Fin N) k) - 1 :=
      Units.continuous_val.sub continuous_const
    exact continuous_const.add (hs.const_smul c⁻¹)
  have h1U : (1 : GL (Fin N) k) ∈ U := by
    show (1 : Matrix (Fin N) (Fin N) k) + c⁻¹ • (((1 : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) - 1) ∈ O
    simpa using h1O
  obtain ⟨j, hj⟩ := ht.2 U hU h1U
  refine ⟨j, ?_⟩
  set G := leviEmb k (stdBlocks d hd) t ^ j with hG
  have hGn : G ∈ Subgroup.normalizer (unipRad k (stdBlocks d hd) : Set (GL (Fin N) k)) :=
    pow_mem (leviEmb_mem_normalizer k (stdBlocks d hd) t) j
  have hmem := hj v (Subgroup.mem_inf.2 ⟨hvJ, hvN⟩)
  have hval := val_conj_one_add_smul G n v c hv
  refine Subgroup.mem_inf.2 ⟨(memJ _).2 ?_, (Subgroup.mem_normalizer_iff.1 hGn n).1 hn⟩
  have hmem' : (1 : Matrix (Fin N) (Fin N) k) +
      c⁻¹ • (((G * v * G⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) - 1) ∈ O := hmem
  rw [hval] at hmem'
  simpa [smul_smul, inv_mul_cancel₀ hc0'] using hmem'

end GlobalTheory.CompanionTheory.ExpandN
