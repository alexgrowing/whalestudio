import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUnitOfSumEqOne
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NormalizedMinorExtendsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsPermNormalizedMinorsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LuDecompositionOfMinorsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AlgebraicIndependentOfAdjoinStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalizationClosureSmoothStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalizationClosureEqualStatement

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell

theorem exists_cell {F : Type} [Field F] (O : Subring F) [IsLocalRing O] {n r : ℕ}
    (A : Matrix (Fin n) (Fin r) F) (N : Matrix (Fin r) (Fin n) F) (hA : ∀ a b, A a b ∈ O)
    (hN : ∀ a b, N a b ∈ O) (hNA : N * A = 1) (Y : Matrix (Fin r) (Fin r) F)
    (hs : ∀ i : Fin r, ∃ J, NormAt O (A * Y) ((i : ℕ) + 1) i.2 J) :
    ∃ w : Equiv.Perm (Fin r), ∀ (k : ℕ) (hk : k ≤ r), NormAt O Y k hk (w ∘ Fin.castLE hk) := by
  refine GlobalTheory.T.exists_perm_normalized_minors O Y (fun k hk I' I => GlobalTheory.T.normalized_minor_extends O Y k hk I' I) fun k hk => ?_
  cases k with
  | zero => exact ⟨Fin.elim0, normAt_zero O Y _⟩
  | succ k =>
    obtain ⟨J, hJ⟩ := hs ⟨k, hk⟩
    exact exists_normAt O A N hA hN hNA Y _ hk J hJ

theorem big_cell_smooth : ∀ (Ω : Type) [Field Ω] (S : Type) [Fintype S] (r n : S → ℕ) (R : Subring Ω) (O : Subring (GenField Ω r)) [IsLocalRing O] (T : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω) (M : ∀ s, Matrix (Fin (n s)) (Fin (r s)) Ω) (N : ∀ s, Matrix (Fin (r s)) (Fin (n s)) Ω) (J : (q : Σ s, Fin (r s)) → Fin ((q.2 : ℕ) + 1) → Fin (n q.1)), (∀ a ∈ R, algebraMap Ω (GenField Ω r) a ∈ O) → (∀ s, (T s).det ≠ 0) → (∀ s j l, M s j l ∈ R) → (∀ s l j, N s l j ∈ R) → (∀ s, N s * M s = 1) → (∀ q, stepMinor (flagB M T q.1) q.2 (J q) ≠ 0) → (∀ (q : Σ s, Fin (r s)) (J' : Fin ((q.2 : ℕ) + 1) → Fin (n q.1)), stepMinor (flagB M T q.1) q.2 J' / stepMinor (flagB M T q.1) q.2 (J q) ∈ O) → ∃ t ∈ ratioRing R (flagB M T) J, t ≠ 0 ∧ t ∈ O ∧ t⁻¹ ∈ O ∧ ∃ h : ∀ a ∈ R, algebraMap Ω (GenField Ω r) a ∈ locSub (ratioRing R (flagB M T) J) t, (((algebraMap Ω (GenField Ω r)).comp R.subtype).codRestrict (locSub (ratioRing R (flagB M T) J) t) (fun a => h a a.2)).Smooth := by
  intro Ω _ S _ r n R O _ T M N J hRO hT hM hN hNM hJ0 hJr
  classical
  haveI : Finite (GenIx r) := by unfold GenIx; infer_instance
  set i := algebraMap Ω (GenField Ω r) with hi
  set A := ratioRing R (flagB M T) J with hAdef
  let Y : ∀ s, Matrix (Fin (r s)) (Fin (r s)) (GenField Ω r) := fun s => (T s).map i * genU Ω r s
  let Am : ∀ s, Matrix (Fin (n s)) (Fin (r s)) (GenField Ω r) := fun s => (M s).map i
  let Nm : ∀ s, Matrix (Fin (r s)) (Fin (n s)) (GenField Ω r) := fun s => (N s).map i
  have hB : ∀ s, flagB M T s = Am s * Y s := fun s => by
    show (M s * T s).map i * genU Ω r s = (M s).map i * ((T s).map i * genU Ω r s)
    rw [Matrix.map_mul, Matrix.mul_assoc]
  have hNA : ∀ s, Nm s * Am s = 1 := fun s => by
    show (N s).map i * (M s).map i = 1
    rw [← Matrix.map_mul, hNM, Matrix.map_one _ (map_zero _) (map_one _)]
  have hYN : ∀ s, Nm s * flagB M T s = Y s := fun s => by
    rw [hB, ← Matrix.mul_assoc, hNA, Matrix.one_mul]
  have hAmO : ∀ s a b, Am s a b ∈ O := fun s a b => hRO _ (hM _ _ _)
  have hNmO : ∀ s a b, Nm s a b ∈ O := fun s a b => hRO _ (hN _ _ _)

  have hw : ∀ s, ∃ w : Equiv.Perm (Fin (r s)), ∀ (k : ℕ) (hk : k ≤ r s),
      NormAt O (Y s) k hk (w ∘ Fin.castLE hk) := fun s =>
    exists_cell O (Am s) (Nm s) (hAmO s) (hNmO s) (hNA s) (Y s) fun i' => by
      refine ⟨J ⟨s, i'⟩, ?_⟩
      rw [← hB]
      exact ⟨hJ0 ⟨s, i'⟩, hJr ⟨s, i'⟩⟩
  choose w hw using hw
  have hlu := fun s => GlobalTheory.T.lu_decomposition_of_minors ((Y s).submatrix (w s) id) fun k hk => (hw s k hk).1
  choose C V hC hV0 hV1 hCV using hlu

  let v : GenIx r → GenField Ω r := fun q => V q.1 q.2.1.1 q.2.1.2
  set B := Subring.closure (((R.map i : Subring _) : Set (GenField Ω r)) ∪ Set.range v) with hBdef
  have hRB : ∀ a ∈ R, i a ∈ B := fun a ha =>
    Subring.subset_closure (Or.inl ⟨a, ha, rfl⟩)
  have hRA : ∀ a ∈ R, i a ∈ A := fun a ha =>
    Subring.subset_closure (Or.inl ⟨a, ha, rfl⟩)
  have hVB : ∀ s l k, V s l k ∈ B := fun s l k => by
    rcases lt_trichotomy l k with h | h | h
    · rw [hV0 s l k h]; exact B.zero_mem
    · rw [h, hV1]; exact B.one_mem
    · exact Subring.subset_closure (Or.inr ⟨⟨s, ⟨(l, k), h⟩⟩, rfl⟩)

  let y0 : (q : Σ s, Fin (r s)) → GenField Ω r := fun q =>
    kMinor (Y q.1) ((q.2 : ℕ) + 1) q.2.2 (w q.1 ∘ Fin.castLE q.2.2)
  have hy0 : ∀ q, y0 q ≠ 0 := fun q => (hw q.1 _ q.2.2).1
  have hrat : ∀ (s : S) (k : ℕ) (hk : k ≤ r s) (I : Fin k → Fin (r s)),
      kMinor (Y s) k hk (w s ∘ I) / kMinor (Y s) k hk (w s ∘ Fin.castLE hk) = kMinor (V s) k hk I :=
    fun s k hk I => ratio_eq_kMinor ((Y s).submatrix (w s) id) (C s) (V s) (hC s) (hV0 s) (hV1 s) (hCV s) k hk I
      (hw s k hk).1
  have hyB : ∀ (q : Σ s, Fin (r s)) I, kMinor (Y q.1) ((q.2 : ℕ) + 1) q.2.2 I / y0 q ∈ B := fun q I => by
    have e : I = w q.1 ∘ ((w q.1).symm ∘ I) := by
      ext a; simp
    rw [e]
    show kMinor (Y q.1) _ q.2.2 _ / kMinor (Y q.1) _ q.2.2 _ ∈ B
    rw [hrat]
    exact kMinor_mem B _ (hVB q.1) _ _ _
  have hPB : ∀ (q : Σ s, Fin (r s)) J', stepMinor (flagB M T q.1) q.2 J' / y0 q ∈ B := fun q J' => by
    rw [hB, stepMinor_eq_kMinor]
    exact kMinor_mul_div_mem B (Am q.1) (Y q.1) _ q.2.2 _ (fun a b => hRB _ (hM _ _ _)) (hyB q) J'
  have hPA : ∀ (q : Σ s, Fin (r s)) J', stepMinor (flagB M T q.1) q.2 J' / stepMinor (flagB M T q.1) q.2 (J q) ∈ A :=
    fun q J' => Subring.subset_closure (Or.inr ⟨q, J', rfl⟩)
  have hyA : ∀ (q : Σ s, Fin (r s)) I, kMinor (Y q.1) ((q.2 : ℕ) + 1) q.2.2 I /
      stepMinor (flagB M T q.1) q.2 (J q) ∈ A := fun q I => by
    rw [← hYN q.1]
    exact kMinor_mul_div_mem A (Nm q.1) (flagB M T q.1) _ q.2.2 _ (fun a b => hRA _ (hN _ _ _)) (hPA q) I
  have hAO : A ≤ O := by
    refine Subring.closure_le.2 ?_
    rintro a (⟨b, hb, rfl⟩ | ⟨q, J', rfl⟩)
    · exact hRO b hb
    · exact hJr q J'

  let tq : (Σ s, Fin (r s)) → GenField Ω r := fun q => y0 q / stepMinor (flagB M T q.1) q.2 (J q)
  have htq0 : ∀ q, tq q ≠ 0 := fun q => div_ne_zero (hy0 q) (hJ0 q)
  have htqA : ∀ q, tq q ∈ A := fun q => hyA q _
  have htqB : ∀ q, (tq q)⁻¹ ∈ B := fun q => by
    show (y0 q / _)⁻¹ ∈ B
    rw [inv_div]
    exact hPB q _
  have htqO : ∀ q, (tq q)⁻¹ ∈ O := fun q => by
    show (y0 q / _)⁻¹ ∈ O
    rw [inv_div, hB, stepMinor_eq_kMinor]
    exact kMinor_mul_div_mem O (Am q.1) (Y q.1) _ q.2.2 _ (hAmO q.1) (hw q.1 _ q.2.2).2 _
  have hAB : A ≤ Subring.closure ((B : Set (GenField Ω r)) ∪ Set.range tq) := by
    refine Subring.closure_le.2 ?_
    rintro a (⟨b, hb, rfl⟩ | ⟨q, J', rfl⟩)
    · exact Subring.subset_closure (Or.inl (hRB b hb))
    · have e : stepMinor (flagB M T q.1) q.2 J' / stepMinor (flagB M T q.1) q.2 (J q) =
          (stepMinor (flagB M T q.1) q.2 J' / y0 q) * tq q := by
        show _ = _ * (y0 q / _)
        have := hy0 q
        have := hJ0 q
        field_simp
      rw [SetLike.mem_coe, e]
      exact mul_mem (Subring.subset_closure (Or.inl (hPB q J'))) (Subring.subset_closure (Or.inr ⟨q, rfl⟩))
  have hBA : B ≤ Subring.closure ((A : Set (GenField Ω r)) ∪ Set.range fun q => (tq q)⁻¹) := by
    refine Subring.closure_le.2 ?_
    rintro a (⟨b, hb, rfl⟩ | ⟨q, rfl⟩)
    · exact Subring.subset_closure (Or.inl (hRA b hb))
    · obtain ⟨s, ⟨⟨l, k⟩, hlk⟩⟩ := q
      have hlk' : k < l := hlk
      have e1 : V s l k = kMinor (Y s) ((k : ℕ) + 1) k.2 (w s ∘ lastRow k l) / y0 ⟨s, k⟩ := by
        rw [← kMinor_lower_lastRow (V s) (hV0 s) (hV1 s) k l hlk', ← hrat]
      have e2 : V s l k = (kMinor (Y s) ((k : ℕ) + 1) k.2 (w s ∘ lastRow k l) /
          stepMinor (flagB M T s) k (J ⟨s, k⟩)) * (tq ⟨s, k⟩)⁻¹ := by
        rw [e1]
        show _ = _ * (y0 ⟨s, k⟩ / _)⁻¹
        have := hy0 ⟨s, k⟩
        have := hJ0 ⟨s, k⟩
        field_simp
      show V s l k ∈ _
      rw [e2]
      exact mul_mem (Subring.subset_closure (Or.inl (hyA ⟨s, k⟩ _))) (Subring.subset_closure (Or.inr ⟨_, rfl⟩))

  have hv : AlgebraicIndependent Ω v := by
    refine GlobalTheory.T.algebraic_independent_of_adjoin _ v (genU_indep Ω r) fun q => ?_
    rw [← genU_gen]
    have hmem : ∀ s l k, V s l k ∈ IntermediateField.adjoin Ω (Set.range v) := fun s l k => by
      rcases lt_trichotomy l k with h | h | h
      · rw [hV0 s l k h]; exact zero_mem _
      · rw [h, hV1]; exact one_mem _
      · exact IntermediateField.subset_adjoin _ _ ⟨⟨s, ⟨(l, k), h⟩⟩, rfl⟩
    refine entries_mem _ ((T q.1).submatrix (w q.1) id) ?_ (genU Ω r q.1) (C q.1) (V q.1)
      (genU_zero Ω r q.1) (genU_one Ω r q.1) (hC q.1) (hV0 q.1) (hV1 q.1) ?_ (hmem q.1) _ _ q.2.2
    · rw [Matrix.det_permute]
      exact mul_ne_zero (by rcases Int.units_eq_one_or (Equiv.Perm.sign (w q.1)) with h | h <;> simp [h]) (hT _)
    · rw [← hCV q.1]
      congr 1

  have hL := GlobalTheory.T.localization_closure_equal A B tq htq0 htqA htqB hAB hBA
  have htA : (∏ q, tq q) ∈ A := A.prod_mem fun q _ => htqA q
  have hinv : (∏ q, tq q)⁻¹ = ∏ q, (tq q)⁻¹ := (Finset.prod_inv_distrib _).symm
  refine ⟨∏ q, tq q, htA, Finset.prod_ne_zero_iff.2 fun q _ => htq0 q, hAO htA, ?_, ?_⟩
  · rw [hinv]
    exact O.prod_mem fun q _ => htqO q
  have hR : ∀ a ∈ R, i a ∈ locSub A (∏ q, tq q) := fun a ha => le_locSub _ _ (hRA a ha)
  refine ⟨hR, ?_⟩
  have gen : ∀ (L : Subring (GenField Ω r)), L = locSub B (∏ q, tq q)⁻¹ → ∀ h : ∀ a ∈ R, i a ∈ L,
      ((i.comp R.subtype).codRestrict L (fun a => h a a.2)).Smooth := by
    rintro _ rfl h
    refine GlobalTheory.T.localization_closure_smooth R v hv _ ?_ (inv_ne_zero (Finset.prod_ne_zero_iff.2 fun q _ => htq0 q)) h
    rw [hinv]
    exact B.prod_mem fun q _ => htqB q
  exact gen _ hL hR

end GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell
