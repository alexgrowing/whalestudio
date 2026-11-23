import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigCongr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsColumnCharacterEigenSubmoduleNeBotStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviWhittakerColumnCharacterEigenVecMulNeBotStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockTriVecMulEqSinglePredStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCommOfIrreducibleMultiplicityLeOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankCommonFixedLeOneOfCommutingHeckeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhittakerSpaceDimFiniteGLLeOneStatement

noncomputable section

namespace GlobalTheory.BlockDecompositionExistence

open GlobalTheory.FinGL GlobalTheory.FinGL.LeviWh Formalism.L2.DIV Module

section Exist

variable {F : Type} [Field F] {r : ℕ}

theorem edgeSum_split (b : Fin r → ℕ) (k : Fin r) (p : blockTri (κ := F) b) (hp : p ∈ colSet F b k.val) :
    edgeSum (blkEdge b) (p : GL (Fin r) F) =
      (∑ i, if blkEdge b i k then ((p : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i k else 0) +
        edgeSum (fun i j => blkEdge b i j ∧ k < j) (p : GL (Fin r) F) := by
  unfold edgeSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : (if blkEdge b i k then ((p : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i k else 0) =
      ∑ j, if j = k then (if blkEdge b i j then ((p : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j else 0) else 0 := by
    simp
  rw [h1, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases he : blkEdge b i j
  · rcases lt_trichotomy j k with h | h | h
    · have hij : i ≠ j := by
        intro e; have := he.1; rw [e] at this; omega
      have h0 := hp.2 i j h
      rw [Matrix.one_apply_ne hij] at h0
      simp [he, h0]
    · simp [he, h]
    · simp [he, h, h.ne']
  · simp [he]

theorem step [Fintype F] (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) {V : Type} [AddCommGroup V] [Module ℂ V]
    (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V) (hσ : IsCuspDatum b σ) (k : Fin r)
    (h : eig σ (colSet F b (k.val + 1)) (fun p => ψ (edgeSum (blkEdge b) (p : GL (Fin r) F))) ≠ ⊥) :
    eig σ (colSet F b k.val) (fun p => ψ (edgeSum (blkEdge b) (p : GL (Fin r) F))) ≠ ⊥ := by
  obtain ⟨l, hl, hne⟩ := GlobalTheory.T.exists_columnCharacter_eigenSubmodule_ne_bot F ψ hψ r V b σ hσ.mono hσ.infl k h
  by_cases hl0 : l = 0
  · subst hl0
    by_cases hk : ∃ i, blkEdge b i k
    · exfalso
      obtain ⟨i, hi1, hi2⟩ := hk
      apply hne
      rw [eq_bot_iff]
      intro y hy
      rw [mem_eig] at hy
      rw [Submodule.mem_bot]
      refine hσ.cusp (Finset.univ.filter fun a => a < k) ⟨i, k, hi2, ?_, by simp⟩ y fun u hu => ?_
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        show i.val < k.val
        omega
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
        have hu' : ∀ i j : Fin r, ¬ (i < k ∧ ¬ j < k) →
            ((u : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j = (1 : Matrix (Fin r) (Fin r) F) i j := by
          intro i j hij
          by_contra hc
          exact hij (hu i j hc).2
        have hmem : u ∈ colSet F b k.val := by
          refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, fun i j hj => hu' i j fun hh => hh.2 hj⟩
          · have hij' : j < i := hij
            rw [hu' i j fun hh => hh.2 (hij'.trans hh.1), Matrix.one_apply_ne hij'.ne']
          · rw [hu' i i fun hh => hh.2 hh.1, Matrix.one_apply_eq]
        rw [hy u hmem]
        have : edgeSum (fun i j => blkEdge b i j ∧ k < j) (u : GL (Fin r) F) = 0 := by
          refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
          split_ifs with hh
          · have h1 := hh.1.1
            have h2 : k.val < j.val := hh.2
            rw [hu' i j fun h3 => by have : i.val < k.val := h3.1; omega, Matrix.one_apply_ne]
            intro e; rw [e] at h1; omega
          · rfl
        simp [colChar, this]
    · rw [eig_congr σ _ _ (colChar ψ b k 0)]
      · exact hne
      · intro p hp
        rw [edgeSum_split b k p hp]
        have : ∀ i, ¬ blkEdge b i k := fun i hi => hk ⟨i, hi⟩
        simp [colChar, this]
  · obtain ⟨i, hi⟩ := Function.ne_iff.1 hl0
    obtain ⟨hik, hbi⟩ := hl i hi
    have hik' : i.val < k.val := hik
    let k' : Fin r := ⟨k.val - 1, by omega⟩
    have hk' : k'.val + 1 = k.val := by show k.val - 1 + 1 = k.val; omega
    have hbk : b k' = b k := by
      apply le_antisymm
      · exact hσ.mono (show k'.val ≤ k.val by omega)
      · rw [← hbi]; exact hσ.mono (show i.val ≤ k'.val by omega)
    obtain ⟨g, hg1, hg2⟩ := GlobalTheory.T.exists_blockTri_vecMul_eq_single_pred F r b hσ.mono k k' hk' l hl0 hl
    have h2 := GlobalTheory.T.leviWhittakerColumnCharacter_eigen_vecMul_ne_bot F ψ r V b σ k l g hg1 hne
    rw [hg2] at h2
    rw [eig_congr σ _ _ (colChar ψ b k (Pi.single k' 1))]
    · exact h2
    · intro p hp
      rw [edgeSum_split b k p hp]
      unfold colChar
      congr 2
      refine Finset.sum_congr rfl fun a _ => ?_
      by_cases ha : a = k'
      · subst ha
        have : blkEdge b k' k := ⟨hk'.symm, hbk⟩
        simp [this]
      · have : ¬ blkEdge b a k := fun hh => ha (Fin.ext (by have := hh.1; omega))
        simp [this, ha]

theorem eig_ne_bot [Fintype F] (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) {V : Type} [AddCommGroup V] [Module ℂ V]
    (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V) (hσ : IsCuspDatum b σ) :
    eig σ {p : blockTri (κ := F) b | (p : GL (Fin r) F) ∈ unip F r} (fun p => ψ (edgeSum (blkEdge b) (p : GL (Fin r) F))) ≠ ⊥ := by
  have key : ∀ k, k ≤ r →
      eig σ (colSet F b k) (fun p => ψ (edgeSum (blkEdge b) (p : GL (Fin r) F))) ≠ ⊥ := by
    intro k hk
    induction hk using Nat.decreasingInduction with
    | of_succ k hk ih => exact step ψ hψ b σ hσ ⟨k, hk⟩ ih
    | self =>
      have hirr := hσ.irr
      have hV : (⊤ : Submodule ℂ V) ≠ ⊥ := by
        intro h
        have : (⊤ : Subrepresentation σ) = ⊥ := Subrepresentation.toSubmodule_injective h
        exact top_ne_bot this
      intro h
      apply hV
      rw [← h, eq_comm, eq_top_iff]
      intro v _
      rw [mem_eig]
      intro p hp
      have hp1 : p = 1 := by
        ext i j
        simpa using hp.2 i j j.2
      subst hp1
      have : edgeSum (blkEdge b) (1 : GL (Fin r) F) = 0 := by
        refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
        split_ifs with hh
        · have h1 := hh.1
          rw [Units.val_one, Matrix.one_apply_ne]
          intro e; rw [e] at h1; omega
        · rfl
      simp [this]
  have h0 : colSet F b 0 = {p : blockTri (κ := F) b | (p : GL (Fin r) F) ∈ unip F r} := by
    ext p; simp [colSet]
  rw [← h0]
  exact key 0 (Nat.zero_le r)

end Exist

section Unique

variable {F : Type} [Field F] {r : ℕ}

theorem exists_blocks (b : Fin r → ℕ) (hb : Monotone b) :
    ∃ (ι : Type) (_ : Fintype ι) (n : ι → ℕ) (E : (Σ c, Fin (n c)) ≃ Fin r),
      (∀ x y, b (E x) = b (E y) ↔ x.1 = y.1) ∧ (∀ c (i j : Fin (n c)), E ⟨c, i⟩ < E ⟨c, j⟩ ↔ i < j) ∧
      ∀ c (i j : Fin (n c)), (E ⟨c, j⟩).val = (E ⟨c, i⟩).val + 1 ↔ j.val = i.val + 1 := by
  classical
  let T : ℕ → Finset (Fin r) := fun c => Finset.univ.filter fun a => b a = c
  let f : ∀ c, Fin (T c).card ↪o Fin r := fun c => (T c).orderEmbOfFin rfl
  have hf : ∀ c i, b (f c i) = c := fun c i => by
    exact (Finset.mem_filter.1 ((T c).orderEmbOfFin_mem rfl i)).2
  have hs : ∀ c a, b a = c → ∃ i, f c i = a := fun c a ha => by
    have : a ∈ Set.range (f c) := by
      rw [Finset.range_orderEmbOfFin]; simp [T, ha]
    exact this
  let E0 : (Σ c : ↥(Finset.univ.image b), Fin (T c).card) → Fin r := fun x => f x.1 x.2
  have hE : Function.Bijective E0 := by
    constructor
    · rintro ⟨⟨c, hc⟩, i⟩ ⟨⟨c', hc'⟩, j⟩ h
      have h' : f c i = f c' j := h
      have e : c = c' := by rw [← hf c i, h', hf]
      subst e
      rw [(f c).injective h']
    · intro a
      obtain ⟨i, hi⟩ := hs (b a) a rfl
      exact ⟨⟨⟨b a, by simp⟩, i⟩, hi⟩
  refine ⟨↥(Finset.univ.image b), inferInstance, fun c => (T c).card, Equiv.ofBijective E0 hE, ?_, ?_, ?_⟩
  · intro x y
    show b (f x.1 x.2) = b (f y.1 y.2) ↔ _
    rw [hf, hf, Subtype.ext_iff]
  · intro c i j
    exact (f c).lt_iff_lt
  · intro c i j
    show (f c j).val = (f c i).val + 1 ↔ _
    constructor
    · intro h
      have h1 : i < j := (f c).lt_iff_lt.1 (show (f c i).val < (f c j).val by omega)
      have h1' : i.val < j.val := h1
      by_contra hc
      have h2 : i.val + 1 < j.val := by omega
      let m : Fin (T c).card := ⟨i.val + 1, h2.trans j.2⟩
      have h3 : (f c i).val < (f c m).val := (f c).lt_iff_lt.2 (show i.val < i.val + 1 by omega)
      have h4 : (f c m).val < (f c j).val := (f c).lt_iff_lt.2 (show i.val + 1 < j.val from h2)
      omega
    · intro h
      have h1 : (f c i).val < (f c j).val := (f c).lt_iff_lt.2 (show i.val < j.val by omega)
      by_contra hc
      have h2 : (f c i).val + 1 < (f c j).val := by omega
      let m : Fin r := ⟨(f c i).val + 1, h2.trans (f c j).2⟩
      have hm : b m = c := by
        apply le_antisymm
        · rw [← hf c j]; exact hb (show (f c i).val + 1 ≤ (f c j).val by omega)
        · conv_lhs => rw [← hf c i]
          exact hb (show (f c i).val ≤ (f c i).val + 1 by omega)
      obtain ⟨l, hl⟩ := hs c m hm
      have h3 : i.val < l.val := (f c).lt_iff_lt.1 (by rw [hl]; show (f c i).val < (f c i).val + 1; omega)
      have h4 : l.val < j.val := (f c).lt_iff_lt.1 (by rw [hl]; exact h2)
      omega

theorem exists_diag (b : Fin r → ℕ) {ι : Type} [Fintype ι] {n : ι → ℕ} (E : (Σ c, Fin (n c)) ≃ Fin r)
    (hE : ∀ x y, b (E x) = b (E y) ↔ x.1 = y.1) :
    ∃ D : (∀ c, GL (Fin (n c)) F) →* blockTri (κ := F) b,
      (∀ x c i j, ((D x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) (E ⟨c, i⟩) (E ⟨c, j⟩) =
        (x c : Matrix (Fin (n c)) (Fin (n c)) F) i j) ∧
      ∀ x c c' i j, c ≠ c' → ((D x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) (E ⟨c, i⟩) (E ⟨c', j⟩) = 0 := by
  classical
  let G : (∀ c, GL (Fin (n c)) F) →* (∀ c, Matrix (Fin (n c)) (Fin (n c)) F) :=
    Pi.monoidHom fun c => (Units.coeHom _).comp (Pi.evalMonoidHom (fun c => GL (Fin (n c)) F) c)
  let M : (∀ c, Matrix (Fin (n c)) (Fin (n c)) F) →* Matrix (Fin r) (Fin r) F :=
    ((Matrix.reindexAlgEquiv F F E).toRingEquiv.toRingHom.comp
      (Matrix.blockDiagonal'RingHom (fun c => Fin (n c)) F)).toMonoidHom
  let D0 : (∀ c, GL (Fin (n c)) F) →* GL (Fin r) F := (M.comp G).toHomUnits
  have hD : ∀ x u v, (D0 x : Matrix (Fin r) (Fin r) F) (E u) (E v) =
      Matrix.blockDiagonal' (fun c => (x c : Matrix (Fin (n c)) (Fin (n c)) F)) u v := by
    intro x u v
    show Matrix.blockDiagonal' (fun c => (x c : Matrix (Fin (n c)) (Fin (n c)) F)) (E.symm (E u)) (E.symm (E v)) = _
    simp
  have h2 : ∀ x c c' i j, c ≠ c' → (D0 x : Matrix (Fin r) (Fin r) F) (E ⟨c, i⟩) (E ⟨c', j⟩) = 0 := by
    intro x c c' i j h
    rw [hD, Matrix.blockDiagonal'_apply_ne _ _ _ h]
  refine ⟨D0.codRestrict _ fun x => ?_, fun x c i j => ?_, h2⟩
  · rw [mem_blockTri]
    intro i j hij
    obtain ⟨⟨c, i⟩, rfl⟩ := E.surjective i
    obtain ⟨⟨c', j⟩, rfl⟩ := E.surjective j
    exact h2 x c c' i j fun e => hij.ne' ((hE _ _).2 e)
  · exact (hD x _ _).trans (Matrix.blockDiagonal'_apply_eq _ _ _ _)

theorem exists_proj (b : Fin r → ℕ) {ι : Type} {n : ι → ℕ} (E : (Σ c, Fin (n c)) ≃ Fin r)
    (hE : ∀ x y, b (E x) = b (E y) ↔ x.1 = y.1) :
    ∃ B : blockTri (κ := F) b →* (∀ c, GL (Fin (n c)) F),
      ∀ p c i j, (B p c : Matrix (Fin (n c)) (Fin (n c)) F) i j =
        ((p : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) (E ⟨c, i⟩) (E ⟨c, j⟩) := by
  have hinj : ∀ c, Function.Injective fun i : Fin (n c) => E ⟨c, i⟩ := fun c i j h => by
    simpa using h
  let B0 : ∀ c, blockTri (κ := F) b →* Matrix (Fin (n c)) (Fin (n c)) F := fun c =>
    { toFun := fun p => ((p : GL (Fin r) F) : Matrix (Fin r) (Fin r) F).submatrix
        (fun i : Fin (n c) => E ⟨c, i⟩) (fun i : Fin (n c) => E ⟨c, i⟩)
      map_one' := Matrix.submatrix_one _ (hinj c)
      map_mul' := by
        intro x y
        show ((x.1 * y.1 : GL (Fin r) F) : Matrix (Fin r) (Fin r) F).submatrix _ _ = _
        rw [Units.val_mul]
        refine submatrix_mul_of_zero _ (hinj c) _ _ fun i j l hl => ?_
        obtain ⟨⟨c', l⟩, rfl⟩ := E.surjective l
        have hc : c' ≠ c := by
          rintro rfl
          exact hl ⟨l, rfl⟩
        have hl' : b (E ⟨c', l⟩) ≠ b (E ⟨c, i⟩) := fun h => hc ((hE _ _).1 h)
        have hij : b (E ⟨c, j⟩) = b (E ⟨c, i⟩) := (hE _ _).2 rfl
        rcases lt_or_gt_of_ne hl' with h | h
        · rw [mem_blockTri.1 x.2 _ _ h, zero_mul]
        · rw [mem_blockTri.1 y.2 _ _ (hij ▸ h), mul_zero] }
  exact ⟨Pi.monoidHom fun c => (B0 c).toHomUnits, fun p c i j => rfl⟩

theorem finrank_le_one [Fintype F] (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V) (hσ : IsCuspDatum b σ) :
    leviWh ψ b σ ≤ 1 := by
  classical
  obtain ⟨ι, _, n, E, hE, hlt, hsucc⟩ := exists_blocks b hσ.mono
  obtain ⟨D, hD1, hD2⟩ := exists_diag (F := F) b E hE
  obtain ⟨B, hB⟩ := exists_proj (F := F) b E hE
  have hBD : ∀ x, B (D x) = x := by
    intro x
    ext c i j
    rw [hB, hD1]
  have hker : ∀ p, B p = 1 → σ p = 1 := by
    intro p hp
    refine hσ.infl p fun i j hij => ?_
    obtain ⟨⟨c, i⟩, rfl⟩ := E.surjective i
    obtain ⟨⟨c', j⟩, rfl⟩ := E.surjective j
    have e : c = c' := (hE _ _).1 hij
    subst e
    rw [← hB, hp]
    simp [Matrix.one_apply]
  have hfac : ∀ p, σ p = σ (D (B p)) := by
    intro p
    have : σ (p * (D (B p))⁻¹) = 1 := hker _ (by rw [map_mul, map_inv, hBD, mul_inv_cancel])
    calc σ p = σ (p * (D (B p))⁻¹ * D (B p)) := by rw [inv_mul_cancel_right]
      _ = σ (D (B p)) := by rw [map_mul, this, one_mul]
  let a : ∀ c, Representation ℂ (GL (Fin (n c)) F) V := fun c =>
    (σ.comp D).comp (MonoidHom.mulSingle (fun c => GL (Fin (n c)) F) c)
  have ha : ∀ c g, a c g = σ (D (Pi.mulSingle c g)) := fun c g => rfl
  have hcomm : ∀ c c', c ≠ c' → ∀ g h, Commute (a c g) (a c' h) := by
    intro c c' hc g h
    rw [ha, ha]
    exact ((Pi.mulSingle_commute (f := fun c => GL (Fin (n c)) F) hc g h).map D).map σ
  have hex := fun c => GlobalTheory.T.hecke_comm_of_irreducible_multiplicity_le_one (GL (Fin (n c)) F) (unip F (n c)) (fun g => ψ (edgeSum supEdge g))
    (fun x hx y hy => by
      have := congrArg Multiplicative.toAdd ((supHom F (n c)).map_mul ⟨x, hx⟩ ⟨y, hy⟩)
      have h' : edgeSum supEdge (x * y) = edgeSum supEdge x + edgeSum supEdge y := this
      simp only [h', AddChar.map_add_eq_mul])
    (by
      have := congrArg Multiplicative.toAdd ((supHom F (n c)).map_one)
      have h' : edgeSum supEdge (1 : GL (Fin (n c)) F) = 0 := this
      simp only [h', AddChar.map_zero_eq_one])
    (fun W _ _ _ τ hτ => GlobalTheory.T.whittakerSpaceDimFiniteGL_le_one F ψ hψ (n c) W τ hτ) V (a c)
  choose e he1 he2 he3 he4 using hex
  have hea : ∀ c c', c ≠ c' → ∀ g, Commute (e c) (a c' g) := fun c c' hc g =>
    (he3 c _ fun h => hcomm c' c hc.symm g h).symm
  refine GlobalTheory.T.finrank_commonFixed_le_one_of_commuting_hecke ι (fun c => GL (Fin (n c)) F) V a e he1 hea
    (fun c c' hc => he3 c' _ (hea c c' hc)) hcomm he4 ?_ _ ?_
  · intro Y hY
    have h1 : ∀ x : ∀ c, GL (Fin (n c)) F, ∀ v ∈ Y, σ (D x) v ∈ Y := by
      intro x
      rw [← Finset.noncommProd_mulSingle x]
      refine Finset.noncommProd_induction _ _ _ (fun x => ∀ v ∈ Y, σ (D x) v ∈ Y) ?_ ?_ ?_
      · intro x y hx hy v hv; rw [map_mul, map_mul]; exact hx _ (hy v hv)
      · intro v hv; simpa using hv
      · intro c _; exact hY c _
    let Z : Subrepresentation σ := ⟨Y, fun p v hv => by rw [hfac]; exact h1 _ v hv⟩
    have hirr := hσ.irr
    rcases eq_bot_or_eq_top Z with h | h
    · exact Or.inl (congrArg Subrepresentation.toSubmodule h)
    · exact Or.inr (congrArg Subrepresentation.toSubmodule h)
  · intro v hv c
    apply he2
    rw [mem_eig] at hv ⊢
    intro u hu
    have hu' : u ∈ unip F (n c) := hu
    have hent : ∀ c' (i j : Fin (n c')), c' ≠ c →
        ((D (Pi.mulSingle c u) : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) (E ⟨c', i⟩) (E ⟨c', j⟩) =
          (1 : Matrix (Fin (n c')) (Fin (n c')) F) i j := by
      intro c' i j hc
      rw [hD1, Pi.mulSingle_eq_of_ne hc, Units.val_one]
    have hent' : ∀ (i j : Fin (n c)),
        ((D (Pi.mulSingle c u) : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) (E ⟨c, i⟩) (E ⟨c, j⟩) =
          (u : Matrix (Fin (n c)) (Fin (n c)) F) i j := by
      intro i j
      rw [hD1, Pi.mulSingle_eq_same]
    have hmem : (D (Pi.mulSingle c u) : GL (Fin r) F) ∈ unip F r := by
      refine ⟨mem_blockTri.2 fun i j hij => ?_, fun i => ?_⟩
      · obtain ⟨⟨c1, i⟩, rfl⟩ := E.surjective i
        obtain ⟨⟨c2, j⟩, rfl⟩ := E.surjective j
        by_cases h12 : c1 = c2
        · subst h12
          have hji : j < i := (hlt _ _ _).1 hij
          by_cases hc : c1 = c
          · subst hc
            rw [hent', unip_lower hu' hji]
          · rw [hent _ _ _ hc, Matrix.one_apply_ne hji.ne']
        · exact hD2 _ _ _ _ _ h12
      · obtain ⟨⟨c1, i⟩, rfl⟩ := E.surjective i
        by_cases hc : c1 = c
        · subst hc
          rw [hent', unip_diag hu']
        · rw [hent _ _ _ hc, Matrix.one_apply_eq]
    rw [ha, hv _ hmem]
    congr 2
    unfold edgeSum
    rw [← E.sum_comp, Fintype.sum_sigma, Finset.sum_eq_single c]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [← E.sum_comp, Fintype.sum_sigma, Finset.sum_eq_single c]
      · refine Finset.sum_congr rfl fun j _ => ?_
        rw [hent']
        refine if_congr ?_ rfl rfl
        unfold blkEdge supEdge
        rw [hsucc, hE]
        simp
      · intro c' _ hc
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [hD2 _ _ _ _ _ hc.symm, ite_self]
      · simp
    · intro c' _ hc
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
      obtain ⟨⟨c2, j⟩, rfl⟩ := E.surjective j
      split_ifs with hh
      · have e2 : c' = c2 := (hE _ _).1 hh.2
        subst e2
        have := (hsucc _ _ _).1 hh.1
        rw [hent _ _ _ hc, Matrix.one_apply_ne]
        intro e3; rw [e3] at this; omega
      · rfl
    · simp

end Unique

theorem leviWh_eq_one (F : Type) [Field F] [Fintype F] (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (r : ℕ) (V : Type)
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (b : Fin r → ℕ)
    (σ : Representation ℂ (blockTri (κ := F) b) V) (hσ : IsCuspDatum b σ) : leviWh ψ b σ = 1 := by
  refine le_antisymm (finrank_le_one ψ hψ b σ hσ) ?_
  exact Submodule.one_le_finrank_iff.2 (eig_ne_bot ψ hψ b σ hσ)

end GlobalTheory.BlockDecompositionExistence
