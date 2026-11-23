import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenFns
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactUnipotentInCompactSubgroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacquetModuleMapInjectiveOfInjective
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Rodier.LowerOpen

theorem inv_conj_apply {k : Type} [Field k] {N : ℕ} (w : Equiv.Perm (Fin N)) (x : GL (Fin N) k)
    (p q : Fin N) :
    (((GroundTheory.Automorphic.permGL k w)⁻¹ * x * GroundTheory.Automorphic.permGL k w : GL (Fin N) k) :
      Matrix (Fin N) (Fin N) k) p q = (x : Matrix (Fin N) (Fin N) k) (w p) (w q) := by
  have h1 : (((GroundTheory.Automorphic.permGL k w)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) =
      w.permMatrix k := by
    rw [← map_inv]
    show ((w⁻¹)⁻¹).permMatrix k = w.permMatrix k
    rw [inv_inv]
  have h2 : ((GroundTheory.Automorphic.permGL k w : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) =
      (w⁻¹).permMatrix k := rfl
  rw [Units.val_mul, Units.val_mul, h1, h2, Equiv.Perm.permMatrix, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  simp [Equiv.Perm.inv_def]

theorem lt_of_blk_lt {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) {p q : Fin N}
    (hb : blk (stdBlocks d hd) (wOpen d hd q) < blk (stdBlocks d hd) (wOpen d hd p)) : p < q := by
  by_contra hpq
  have h1 := Tuple.monotone_sort (GlobalTheory.CompanionTheory.Rodier.wKey d hd) (not_lt.mp hpq)
  simp only [Function.comp_apply, GlobalTheory.CompanionTheory.Rodier.wKey] at h1
  have hb' : blk (stdBlocks d hd) (Tuple.sort (GlobalTheory.CompanionTheory.Rodier.wKey d hd) q) <
      blk (stdBlocks d hd) (Tuple.sort (GlobalTheory.CompanionTheory.Rodier.wKey d hd) p) := hb
  rw [Prod.Lex.toLex_le_toLex] at h1
  rcases h1 with h | ⟨h, -⟩
  · exact lt_asymm hb' (OrderDual.toDual_lt_toDual.mp h)
  · exact (ne_of_lt hb') (OrderDual.toDual.injective h)

theorem lower_entries {k : Type} [Field k] {h N : ℕ} {d : Fin h → ℕ} {hd : ∑ a, d a = N}
    {x : GL (Fin N) k} (hx : x ∈ unipRadLower k (stdBlocks d hd)) (i j : Fin N) :
    (blk (stdBlocks d hd) i < blk (stdBlocks d hd) j → (x : Matrix (Fin N) (Fin N) k) i j = 0) ∧
      (blk (stdBlocks d hd) i = blk (stdBlocks d hd) j →
        (x : Matrix (Fin N) (Fin N) k) i j = (1 : Matrix (Fin N) (Fin N) k) i j) := by
  obtain ⟨hpl, hdiag⟩ := (GlobalTheory.SmGL.mem_unipRadLower k).mp hx
  rw [GlobalTheory.SmGL.mem_parabLower_iff] at hpl
  obtain ⟨⟨a, i'⟩, rfl⟩ := (stdBlocks d hd).surjective i
  obtain ⟨⟨b, j'⟩, rfl⟩ := (stdBlocks d hd).surjective j
  rw [GlobalTheory.SmGL.blk_apply, GlobalTheory.SmGL.blk_apply]
  refine ⟨fun hab => hpl a b i' j' hab, fun hab => ?_⟩
  subst hab
  rw [hdiag a i' j', Matrix.one_apply, Matrix.one_apply]
  simp [(stdBlocks d hd).apply_eq_iff_eq]

theorem parab_inf_lower {k : Type} [Field k] {h N : ℕ} {d : Fin h → ℕ} {hd : ∑ a, d a = N}
    {x : GL (Fin N) k} (hp : x ∈ parab k (stdBlocks d hd))
    (hx : x ∈ unipRadLower k (stdBlocks d hd)) : x = 1 := by
  ext i j
  rcases lt_trichotomy (blk (stdBlocks d hd) i) (blk (stdBlocks d hd) j) with hlt | heq | hgt
  · have hij : i ≠ j := by
      rintro rfl
      exact lt_irrefl _ hlt
    rw [(lower_entries hx i j).1 hlt]
    simp [Matrix.one_apply, hij]
  · rw [(lower_entries hx i j).2 heq]
    simp
  · have hij : i ≠ j := by
      rintro rfl
      exact lt_irrefl _ hgt
    rw [GlobalTheory.SmGL.mem_parab.mp hp i j hgt]
    simp [Matrix.one_apply, hij]

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N)

variable {k d hd} in

theorem mem_unipU_iff {u : GL (Fin N) k} :
    u ∈ unipU k d hd ↔ u ∈ unipB k (Fin N) ∧
      pm k (wOpen d hd) * u * (pm k (wOpen d hd))⁻¹ ∈ unipRadLower k (stdBlocks d hd) := by
  rw [GlobalTheory.CompanionTheory.Rodier.unipU, Subgroup.mem_inf, Subgroup.mem_comap]
  rfl

theorem inv_conj_mem_unipU {x : GL (Fin N) k} (hx : x ∈ unipRadLower k (stdBlocks d hd)) :
    (pm k (wOpen d hd))⁻¹ * x * pm k (wOpen d hd) ∈ unipU k d hd := by
  rw [mem_unipU_iff]
  refine ⟨?_, ?_⟩
  · rw [GlobalTheory.SmGL.mem_unipB]
    have hent : ∀ p q, (((pm k (wOpen d hd))⁻¹ * x * pm k (wOpen d hd) : GL (Fin N) k) :
        Matrix (Fin N) (Fin N) k) p q = (x : Matrix (Fin N) (Fin N) k) (wOpen d hd p) (wOpen d hd q) :=
      fun p q => inv_conj_apply (wOpen d hd) x p q
    refine ⟨fun i j hji => ?_, fun i => ?_⟩
    · rw [hent]
      rcases lt_trichotomy (blk (stdBlocks d hd) (wOpen d hd i)) (blk (stdBlocks d hd) (wOpen d hd j))
        with hlt | heq | hgt
      · exact (lower_entries hx _ _).1 hlt
      · rw [(lower_entries hx _ _).2 heq, Matrix.one_apply, if_neg]
        intro h
        exact hji.ne' ((wOpen d hd).injective h)
      · exact absurd (lt_of_blk_lt d hd hgt) (not_lt.mpr hji.le)
    · rw [hent, (lower_entries hx _ _).2 rfl]
      simp
  · have he : pm k (wOpen d hd) * ((pm k (wOpen d hd))⁻¹ * x * pm k (wOpen d hd)) *
        (pm k (wOpen d hd))⁻¹ = x := by group
    rw [he]
    exact hx

theorem eq_of_mul_eq {p u u' : GL (Fin N) k} (hp : p ∈ parab k (stdBlocks d hd))
    (hu : u ∈ unipU k d hd) (hu' : u' ∈ unipU k d hd)
    (e : p * pm k (wOpen d hd) * u = pm k (wOpen d hd) * u') : u = u' := by
  have hv : u' * u⁻¹ ∈ unipU k d hd := (unipU k d hd).mul_mem hu' ((unipU k d hd).inv_mem hu)
  have hlow := (mem_unipU_iff.mp hv).2
  have hpeq : pm k (wOpen d hd) * (u' * u⁻¹) * (pm k (wOpen d hd))⁻¹ = p := by
    calc pm k (wOpen d hd) * (u' * u⁻¹) * (pm k (wOpen d hd))⁻¹
        = (pm k (wOpen d hd) * u') * u⁻¹ * (pm k (wOpen d hd))⁻¹ := by group
      _ = (p * pm k (wOpen d hd) * u) * u⁻¹ * (pm k (wOpen d hd))⁻¹ := by rw [e]
      _ = p := by group
  rw [hpeq] at hlow
  have h1 := parab_inf_lower hp hlow
  rw [h1] at e
  simpa using e

theorem isClosed_unipU : IsClosed (unipU k d hd : Set (GL (Fin N) k)) := by
  have hent : ∀ (i j : Fin N) (c : k),
      IsClosed {g : GL (Fin N) k | (g : Matrix (Fin N) (Fin N) k) i j = c} :=
    fun i j c => isClosed_eq (Units.continuous_val.matrix_elem i j) continuous_const
  have hB : IsClosed (unipB k (Fin N) : Set (GL (Fin N) k)) := by
    have hs : (unipB k (Fin N) : Set (GL (Fin N) k)) =
        (⋂ i, ⋂ j, ⋂ (_ : j < i), {g : GL (Fin N) k | (g : Matrix (Fin N) (Fin N) k) i j = 0}) ∩
          ⋂ i, {g : GL (Fin N) k | (g : Matrix (Fin N) (Fin N) k) i i = 1} := by
      ext g
      simp [GlobalTheory.SmGL.mem_unipB]
    rw [hs]
    exact (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => hent i j 0).inter
      (isClosed_iInter fun i => hent i i 1)
  have hL : IsClosed (unipRadLower k (stdBlocks d hd) : Set (GL (Fin N) k)) := by
    have hs : (unipRadLower k (stdBlocks d hd) : Set (GL (Fin N) k)) =
        (⋂ a, ⋂ b, ⋂ i, ⋂ j, ⋂ (_ : a < b), {g : GL (Fin N) k |
          (g : Matrix (Fin N) (Fin N) k) (stdBlocks d hd ⟨a, i⟩) (stdBlocks d hd ⟨b, j⟩) = 0}) ∩
          ⋂ a, ⋂ i, ⋂ j, {g : GL (Fin N) k |
            (g : Matrix (Fin N) (Fin N) k) (stdBlocks d hd ⟨a, i⟩) (stdBlocks d hd ⟨a, j⟩) =
              (1 : Matrix (Fin (d a)) (Fin (d a)) k) i j} := by
      ext g
      simp [GlobalTheory.SmGL.mem_unipRadLower, GlobalTheory.SmGL.mem_parabLower_iff]
    rw [hs]
    exact (isClosed_iInter fun a => isClosed_iInter fun b => isClosed_iInter fun i =>
      isClosed_iInter fun j => isClosed_iInter fun _ => hent _ _ _).inter
      (isClosed_iInter fun a => isClosed_iInter fun i => isClosed_iInter fun j => hent _ _ _)
  have hc : Continuous fun u : GL (Fin N) k => pm k (wOpen d hd) * u * (pm k (wOpen d hd))⁻¹ :=
    (continuous_const.mul continuous_id).mul continuous_const
  have hs : (unipU k d hd : Set (GL (Fin N) k)) =
      (unipB k (Fin N) : Set (GL (Fin N) k)) ∩
        (fun u : GL (Fin N) k => pm k (wOpen d hd) * u * (pm k (wOpen d hd))⁻¹) ⁻¹'
          (unipRadLower k (stdBlocks d hd) : Set (GL (Fin N) k)) := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_preimage, SetLike.mem_coe]
    exact mem_unipU_iff
  rw [hs]
  exact hB.inter (hL.preimage hc)

end GlobalTheory.CompanionTheory.Rodier.LowerOpen

namespace GlobalTheory.CompanionTheory.Rodier

theorem unipU_open_cell : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N), (∀ x ∈ unipRadLower k (stdBlocks d hd), (pm k (wOpen d hd))⁻¹ * x * pm k (wOpen d hd) ∈ unipU k d hd) ∧ (∀ p ∈ parab k (stdBlocks d hd), ∀ u ∈ unipU k d hd, ∀ u' ∈ unipU k d hd, p * pm k (wOpen d hd) * u = pm k (wOpen d hd) * u' → u = u') ∧ IsClosed (unipU k d hd : Set (GL (Fin N) k)) := by
  intro k _ _ _ _ h N d hd
  exact ⟨fun x hx => LowerOpen.inv_conj_mem_unipU k d hd hx,
    fun p hp u hu u' hu' e => LowerOpen.eq_of_mul_eq k d hd hp hu hu' e,
    LowerOpen.isClosed_unipU k d hd⟩

end GlobalTheory.CompanionTheory.Rodier
