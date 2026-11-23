import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.RestrictedCharpolys.FiniteCharpoly
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.RestrictedCharpolys.FibVanPull
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.LocalContinuity.LocalDescentHolds
import GroundTheory.AutomorphicForms.ContragredientTranspose.MatrixSimilarity

noncomputable section

open Matrix Polynomial Set

namespace PositivityTheory.RgUd.TP.Desc.Restr.Ppull2

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc PositivityTheory.RgUd.TP.Desc.Restr

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isClosed_charpoly_eq {N : ℕ} (c : k[X]) : IsClosed {A : Matrix (Fin N) (Fin N) k | A.charpoly = c} := by
  have hc : ∀ (i : ℕ) (A : Matrix (Fin N) (Fin N) k), A.charpoly.coeff i =
      MvPolynomial.eval (fun p : Fin N × Fin N => A p.1 p.2)
        (MvPolynomial.map (Int.castRingHom k) ((Matrix.charpoly.univ ℤ (Fin N)).coeff i)) := by
    intro i A
    have h := Matrix.charpoly.univ_map_eval₂Hom (Fin N) (Int.castRingHom k) (fun p : Fin N × Fin N => A p.1 p.2)
    have hA : Matrix.of (Function.curry (fun p : Fin N × Fin N => A p.1 p.2)) = A := by
      ext a b
      rfl
    rw [hA] at h
    rw [← h, Polynomial.coeff_map, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq_eval_map]
  have hset : {A : Matrix (Fin N) (Fin N) k | A.charpoly = c} = ⋂ i : ℕ, {A | A.charpoly.coeff i = c.coeff i} := by
    ext A
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    exact ⟨fun h i => by rw [h], fun h => Polynomial.ext h⟩
  rw [hset]
  refine isClosed_iInter fun i => ?_
  simp only [hc]
  exact isClosed_eq ((MvPolynomial.continuous_eval _).comp
    (continuous_pi fun p => continuous_id.matrix_elem p.1 p.2)) continuous_const

theorem conj_mem_Bz {n : ℕ} {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {g : GL (Fin n) k} (hg : g ∈ Gz Z)
    {x : Matrix (Fin n) (Fin n) k} (hx : x ∈ Bz Z) : g.val * x * g⁻¹.val ∈ Bz Z := by
  have hg' : ∀ a ∈ Z, a * g.val = g.val * a := hg
  have hx' : ∀ a ∈ Z, a * x = x * a := hx
  show ∀ a ∈ Z, a * (g.val * x * g⁻¹.val) = g.val * x * g⁻¹.val * a
  intro a ha
  have hi : a * g⁻¹.val = g⁻¹.val * a := by
    have e := congrArg (fun m => g⁻¹.val * m * g⁻¹.val) (hg' a ha)
    simp only [mul_assoc, Units.mul_inv, mul_one, Units.inv_mul_cancel_left] at e
    exact e.symm
  calc a * (g.val * x * g⁻¹.val) = a * g.val * x * g⁻¹.val := by simp only [mul_assoc]
    _ = g.val * (a * x) * g⁻¹.val := by rw [hg' a ha]; simp only [mul_assoc]
    _ = g.val * x * (a * g⁻¹.val) := by rw [hx' a ha]; simp only [mul_assoc]
    _ = g.val * x * g⁻¹.val * a := by rw [hi]; simp only [mul_assoc]

theorem pullPieces : PullPieces k := by
  unfold PullPieces
  intro n N q Z Z' φ e hZ hD χ
  have hBz : ∀ {m : ℕ} (S : Subalgebra k (Matrix (Fin m) (Fin m) k)), IsClosed (Bz S) := by
    intro m S
    have hS : Bz S = ⋂ a ∈ S, {x : Matrix (Fin m) (Fin m) k | a * x = x * a} := by
      ext x
      simp only [Set.mem_iInter]
      rfl
    rw [hS]
    exact isClosed_biInter fun a _ =>
      isClosed_eq (continuous_const.matrix_mul continuous_id) (continuous_id.matrix_mul continuous_const)
  obtain ⟨P, hP0, hP⟩ : ∃ P : k[X], P ≠ 0 ∧
      ∀ x : Matrix (Fin n) (Fin n) k, x.charpoly = χ → aeval (φ x) P = 0 := by
    by_cases hχ : χ = 0
    · exact ⟨1, one_ne_zero, fun x hx => absurd (hx.trans hχ) (Matrix.charpoly_monic x).ne_zero⟩
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN
      refine ⟨1, one_ne_zero, fun x _ => ?_⟩
      ext i j
      exact i.elim0
    · obtain ⟨hq, -⟩ := Ppull2A.choose_zero hD hN
      refine ⟨expand k q χ, ?_, fun x hx => Ppull2A.aeval_expand hD hN χ x (hx ▸ Matrix.aeval_self_charpoly x)⟩
      rwa [Ne, Polynomial.expand_eq_zero (by omega)]
  obtain ⟨l, hnd, hl⟩ := Ppull2A.finite_charpoly N P hP0
  refine ⟨l, fun h => ?_⟩
  choose M F' hP' hG' using h
  unfold IsPieces at hP'
  let L : Fin l.length → k[X] := fun j => l[j.val]'j.isLt
  have hLm : ∀ j, L j ∈ l := fun j => List.getElem_mem j.isLt
  let mj : Fin l.length → ℕ := fun j => M (L j) (hLm j)
  let G : (Σ j : Fin l.length, Fin (mj j)) → Set (Matrix (Fin n) (Fin n) k) := fun s =>
    {x | x ∈ Bz Z ∧ x.charpoly = χ ∧ (φ x).charpoly = L s.1 ∧ φ x ∈ F' (L s.1) (hLm s.1) s.2}
  have memG : ∀ s x, x ∈ G s ↔ (x ∈ Bz Z ∧ x.charpoly = χ ∧ (φ x).charpoly = L s.1 ∧
      φ x ∈ F' (L s.1) (hLm s.1) s.2) := fun _ _ => Iff.rfl
  have hGc : ∀ s, IsClosed (G s) ∧ G s ⊆ Bz Z ∧
      ∀ g ∈ Gz Z, ∀ x ∈ G s, (g : Matrix (Fin n) (Fin n) k) * x * ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) ∈ G s := by
    rintro ⟨j, i⟩
    refine ⟨?_, fun x hx => ((memG _ x).1 hx).1, ?_⟩
    · exact (hBz Z).inter ((isClosed_charpoly_eq χ).inter
        (((isClosed_charpoly_eq _).preimage hD.emb.continuous).inter
          (((hP' _ _).1 i).1.preimage hD.emb.continuous)))
    · intro g hg x hx
      obtain ⟨hxB, hxc, hxφc, hxF⟩ := (memG _ x).1 hx
      let g' : GL (Fin N) k := Units.map (φ : Matrix (Fin n) (Fin n) k →* Matrix (Fin N) (Fin N) k) g
      have hg' : g' ∈ Gz Z' := (hD.gz g').2 ⟨g, hg, rfl⟩
      have hφ : φ (g.val * x * g⁻¹.val) = g'.val * φ x * g'⁻¹.val := by
        rw [map_mul, map_mul]
        rfl
      refine (memG _ _).2 ⟨conj_mem_Bz hg hxB, ?_, ?_, ?_⟩
      · rw [Matrix.coe_units_inv, Matrix.charpoly_units_conj]
        exact hxc
      · show (φ (g.val * x * g⁻¹.val)).charpoly = _
        rw [hφ, Matrix.coe_units_inv, Matrix.charpoly_units_conj]
        exact hxφc
      · show φ (g.val * x * g⁻¹.val) ∈ _
        rw [hφ]
        exact ((hP' _ _).1 i).2.2 g' hg' _ hxF
  have hGd : ∀ s s', s ≠ s' → Disjoint (G s) (G s') := by
    rintro ⟨j, i⟩ ⟨j', i'⟩ hne
    rw [Set.disjoint_left]
    intro x hx1 hx2
    obtain ⟨-, -, hc1, hF1⟩ := (memG _ x).1 hx1
    obtain ⟨-, -, hc2, hF2⟩ := (memG _ x).1 hx2
    by_cases hj : j = j'
    · subst hj
      have hi : i ≠ i' := fun h => hne (by rw [h])
      exact Set.disjoint_left.1 ((hP' _ _).2.1 i i' hi) hF1 hF2
    · apply hj
      have hL : L j = L j' := hc1.symm.trans hc2
      exact Fin.ext ((List.Nodup.getElem_inj_iff hnd).1 hL)
  have hGcov : ∀ x ∈ Bz Z, x.charpoly = χ → ∃ s, x ∈ G s := by
    intro x hx hc
    obtain ⟨j0, hj0, hj0e⟩ := List.getElem_of_mem (hl (φ x) (hP x hc))
    let j : Fin l.length := ⟨j0, hj0⟩
    have hxB' : φ x ∈ Bz Z' := by
      rw [hD.cen]
      exact ⟨x, hx, rfl⟩
    obtain ⟨i, hi⟩ := (hP' (L j) (hLm j)).2.2 (φ x) hxB' hj0e.symm
    exact ⟨⟨j, i⟩, (memG _ x).2 ⟨hx, hc, hj0e.symm, hi⟩⟩
  have hGg : ∀ s, Good Z (G s) := by
    rintro ⟨j, i⟩
    have hg := hG' (L j) (hLm j) i
    unfold Good at hg ⊢
    rcases hg with ⟨c', hc', hnil⟩ | ⟨N', S, hS, hmu, hV⟩
    · have hcc : c' ∈ φ '' (Z : Set (Matrix (Fin n) (Fin n) k)) := by
        rw [← hD.carrier]
        exact hc'
      obtain ⟨c, hc, rfl⟩ := hcc
      refine Or.inl ⟨c, hc, fun x hx => ?_⟩
      obtain ⟨m, hm⟩ := hnil (φ x) ((memG _ x).1 hx).2.2.2
      exact ⟨m, hD.inj (by rw [map_pow, map_sub, hm, map_zero])⟩
    · refine Or.inr ⟨N', S, hS, by rw [← hD.mu]; exact hmu, fun hv =>
        Ppull2B.fibVan_pull hD _ _ (fun x hx => ((memG _ x).1 hx).2.2.2) (hV hv)⟩
  refine ⟨∑ j, mj j, fun t => G (finSigmaFinEquiv.symm t), ?_, fun t => hGg _⟩
  unfold IsPieces
  refine ⟨fun t => hGc _, fun t t' htt => hGd _ _ (fun h => htt (finSigmaFinEquiv.symm.injective h)), ?_⟩
  intro x hx hc
  obtain ⟨s, hs⟩ := hGcov x hx hc
  exact ⟨finSigmaFinEquiv s, by simpa using hs⟩

end PositivityTheory.RgUd.TP.Desc.Restr.Ppull2
