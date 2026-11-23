import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CentralExponentBoundOver
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsingletonJacquetOfPerm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivDetCharacterOfIrreducibleRankLeOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JordanHolderMultiplicityNormalizedBorelJacquetUn

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

theorem UpperTheory.jacquet_borel_nontrivial_of_blocks_le_one :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (r : ℕ) (d : Fin r → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin N), (∀ a, d a ≤ 1) → Nontrivial (Jacquet π (unipRad k e)) →
    Nontrivial (Jacquet π (unipB k (Fin N))) := by
  intro k _ _ _ _ N V _ _ π r d e hd hR
  have hinj : Function.Injective (blk e) := by
    intro i j hij
    apply e.symm.injective
    simp only [GlobalTheory.SmGL.blk] at hij
    revert hij
    generalize e.symm i = p
    generalize e.symm j = q
    intro hij
    obtain ⟨a, x⟩ := p
    obtain ⟨b, y⟩ := q
    simp only at hij
    subst hij
    have hxy : x = y := by
      have h1 := x.isLt
      have h2 := y.isLt
      have h3 := hd a
      ext
      omega
    rw [hxy]
  set S : Finset (Fin r) := Finset.univ.image (blk e) with hSdef
  have hS : S.card = N := by
    rw [hSdef, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  let f : Fin N → Fin N := fun i =>
    (S.orderIsoOfFin hS).symm ⟨blk e i, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  have hflt : ∀ i j, blk e i < blk e j → f i < f j := by
    intro i j h
    simp only [f, OrderIso.lt_iff_lt]
    exact h
  have hfinj : Function.Injective f := by
    intro i j h
    apply hinj
    have := (S.orderIsoOfFin hS).symm.injective h
    simpa using this
  let σ : Fin N ≃ Fin N := Equiv.ofBijective f ⟨hfinj, Finite.injective_iff_surjective.mp hfinj⟩
  have hσ : ∀ i j, blk e i < blk e j → σ i < σ j := hflt
  have h1 : σ.toPEquiv.toMatrix * σ.symm.toPEquiv.toMatrix = (1 : Matrix (Fin N) (Fin N) k) := by
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.self_trans_symm, Equiv.toPEquiv_refl,
      PEquiv.toMatrix_refl]
  have h2 : σ.symm.toPEquiv.toMatrix * σ.toPEquiv.toMatrix = (1 : Matrix (Fin N) (Fin N) k) := by
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.symm_trans_self, Equiv.toPEquiv_refl,
      PEquiv.toMatrix_refl]
  let hh : GL (Fin N) k := ⟨σ.toPEquiv.toMatrix, σ.symm.toPEquiv.toMatrix, h1, h2⟩
  have hent : ∀ (g : GL (Fin N) k) (i j : Fin N),
      ((hh * g * hh⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j = (g : Matrix (Fin N) (Fin N) k) (σ i) (σ j) := by
    intro g i j
    have hv : ((hh * g * hh⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k)
        = σ.toPEquiv.toMatrix * (g : Matrix (Fin N) (Fin N) k) * σ.symm.toPEquiv.toMatrix := rfl
    rw [hv, PEquiv.mul_toMatrix_apply, ← Equiv.toPEquiv_symm, Equiv.symm_symm, Equiv.toPEquiv_apply]
    simp only [Matrix.mul_assoc]
    rw [PEquiv.toMatrix_mul_apply, Equiv.toPEquiv_apply]
  have memR : ∀ n : unipB k (Fin N), hh * (n : GL (Fin N) k) * hh⁻¹ ∈ unipRad k e := by
    intro n
    have hn := (mem_unipB k).mp n.2
    rw [mem_unipRad, mem_parab]
    refine ⟨?_, ?_⟩
    · intro i j hij
      rw [hent]
      exact hn.1 _ _ (hσ _ _ hij)
    · intro a x y
      have hxy : x = y := by
        have h1 := x.isLt
        have h2 := y.isLt
        have h3 := hd a
        ext
        omega
      subst hxy
      rw [hent, hn.2, Matrix.one_apply_eq]
  rw [← not_subsingleton_iff_nontrivial] at hR ⊢
  intro hB
  apply hR
  change Subsingleton (V ⧸ GlobalTheory.PRep.twKer π _ 1) at hB
  change Subsingleton (V ⧸ GlobalTheory.PRep.twKer π _ 1)
  rw [Submodule.Quotient.subsingleton_iff] at hB ⊢
  have key : GlobalTheory.PRep.twKer π (unipB k (Fin N)) 1 ≤
      (GlobalTheory.PRep.twKer π (unipRad k e) 1).comap (π hh) := by
    unfold GlobalTheory.PRep.twKer
    rw [Submodule.span_le]
    rintro w ⟨n, v, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, MonoidHom.one_apply, Units.val_one, one_smul, map_sub]
    apply Submodule.subset_span
    refine ⟨⟨hh * (n : GL (Fin N) k) * hh⁻¹, memR n⟩, π hh v, ?_⟩
    simp only [MonoidHom.one_apply, Units.val_one, one_smul, map_mul, Module.End.mul_apply]
    rw [← Module.End.mul_apply (π hh⁻¹), ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [eq_top_iff]
  intro v _
  have hv : v = π hh (π hh⁻¹ v) := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  rw [hv]
  exact key (hB ▸ Submodule.mem_top)
