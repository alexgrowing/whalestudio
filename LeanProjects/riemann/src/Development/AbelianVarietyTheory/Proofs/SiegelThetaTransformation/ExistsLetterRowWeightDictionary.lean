import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RelabelEmbeddingsGoodBijectiveConjCompat
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaLetterEquivConjugate
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PushLettersIntCastOfIsHomogeneous
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PointwiseNormCanonicalThetaEqSqThetaConstant
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsSymplecticCoordinatesAdapted
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnChartAsm

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.Letters

theorem rename_place_mem {R : Type} [CommRing R] {T T' κ : Type} [Fintype κ] {p q : ℕ} (f : T ≃ T')
    {c : T → Fin p → ℕ} {c' : T → Fin q → ℕ} {d : T' → Fin p → ℕ} {d' : T' → Fin q → ℕ}
    (h : ∀ t, d (f t) = c t) (h' : ∀ t, d' (f t) = c' t) {P : Harm.Poly R T p q κ}
    (hP : P ∈ Harm.rowHighest R c c') :
    MvPolynomial.rename (f.prodCongr (Equiv.refl ((Fin p ⊕ Fin q) × κ))) P ∈ Harm.rowHighest R d d' := by
  obtain ⟨h₁, h₂, h₃⟩ := Harm.mem_rowHighest_iff_rowAdd.1 hP
  set F := f.prodCongr (Equiv.refl ((Fin p ⊕ Fin q) × κ)) with hF
  have hFa (t : T) (v : (Fin p ⊕ Fin q) × κ) : F (t, v) = (f t, v) := rfl
  refine Harm.mem_rowHighest_iff_rowAdd.2 ⟨fun t a b => ?_, fun t ρ => ?_, fun t ρ ρ' hρ s => ?_⟩ <;>
    obtain ⟨t, rfl⟩ := f.surjective t
  · have := congrArg (MvPolynomial.rename F) (h₁ t a b)
    rw [map_zero, Harm.laplacian_apply, map_sum] at this
    rw [Harm.laplacian_apply, ← this]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Harm.xVar, Harm.yVar, ← hFa, ← hFa, MvPolynomial.pderiv_rename F.injective,
      MvPolynomial.pderiv_rename F.injective]
  · rw [Harm.isWeightedHomogeneous_rename_iff F.injective, h, h']
    convert h₂ t ρ using 1
    funext ⟨t', ρ', k⟩
    simp [hFa, Harm.rowInd_apply]
  · conv_rhs => rw [← h₃ t ρ ρ' hρ s]
    refine DFunLike.congr_fun (?_ : (Harm.rowAdd (f t) ρ ρ' (s : R)).comp (MvPolynomial.rename F) =
      (MvPolynomial.rename F).comp (Harm.rowAdd t ρ ρ' (s : R))) P
    refine MvPolynomial.algHom_ext fun ⟨t', ρ'', k⟩ => ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, MvPolynomial.rename_X, hFa, Harm.rowAdd_X, Harm.rowAdd_X]
    simp only [f.injective.eq_iff]
    split_ifs <;> simp [hFa]

theorem rename_place_mem_iff {R : Type} [CommRing R] {T T' κ : Type} [Fintype κ] {p q : ℕ} (f : T ≃ T')
    {c : T → Fin p → ℕ} {c' : T → Fin q → ℕ} {d : T' → Fin p → ℕ} {d' : T' → Fin q → ℕ}
    (h : ∀ t, d (f t) = c t) (h' : ∀ t, d' (f t) = c' t) {P : Harm.Poly R T p q κ} :
    MvPolynomial.rename (f.prodCongr (Equiv.refl ((Fin p ⊕ Fin q) × κ))) P ∈ Harm.rowHighest R d d' ↔
      P ∈ Harm.rowHighest R c c' := by
  refine ⟨fun hP => ?_, rename_place_mem f h h'⟩
  have := rename_place_mem f.symm (d := c) (d' := c') (fun t => by rw [← h, f.apply_symm_apply])
    (fun t => by rw [← h', f.apply_symm_apply]) hP
  rw [MvPolynomial.rename_rename] at this
  convert this
  rw [show (f.symm.prodCongr (Equiv.refl ((Fin p ⊕ Fin q) × κ))) ∘
    (f.prodCongr (Equiv.refl ((Fin p ⊕ Fin q) × κ))) = id from
      (f.prodCongr (Equiv.refl ((Fin p ⊕ Fin q) × κ))).symm_comp_self, MvPolynomial.rename_id_apply]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ}

theorem exists_isSympl (X : Data E r) (hL : SelfD X X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) :
    ∃ bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ, IsSympl X bas := by
  obtain ⟨h1, h2, h3⟩ := ThetaHol.finrank_lattice X
  have hg : g = X.Ψ.card * r := by simpa using Fintype.card_congr idx
  have hκ : X.κ0 / 2 ≠ 0 := by rcases X.κ0_xi with h | h <;> rw [h] <;> simp [X.ξ0_ne]
  have hlat : ReciprocityTheory.MultiplicativeHeights.IsLattice X.Λ := ⟨X.Λ_fg, X.Λ_span⟩
  obtain ⟨B, hB⟩ : ∃ B : LinearMap.BilinForm ℚ (Fin r → E), ∀ u v, EF X u v = B u v :=
    ⟨_, TensLat.EF_eq_bilin X⟩
  choose k hk using fun u v : X.Λ => (hL.2 u).1 u.2 v v.2
  have hk' (u v : X.Λ) : (k u v : ℚ) = B u v := (hk u v).symm.trans (hB _ _)
  let β : LinearMap.BilinForm ℤ X.Λ := LinearMap.mk₂ ℤ k
    (fun x x' y => by apply Int.cast_injective (α := ℚ); simp [hk'])
    (fun m x y => by apply Int.cast_injective (α := ℚ); simp [hk', -zsmul_eq_mul, map_zsmul]; simp)
    (fun x y y' => by apply Int.cast_injective (α := ℚ); simp [hk'])
    (fun m x y => by apply Int.cast_injective (α := ℚ); simp [hk', -zsmul_eq_mul, map_zsmul]; simp)
  have hβ (u v : X.Λ) : (β u v : ℚ) = EF X u v := (hk u v).symm
  have halt : β.IsAlt := fun x => by
    have := TensLat.EF_swap X x x
    apply Int.cast_injective (α := ℚ)
    rw [hβ, Int.cast_zero]
    linarith
  have hbij : Function.Bijective β := by
    constructor
    · intro x x' h
      refine Subtype.ext (eq_of_EFf_eq hκ X.Gm_det hlat fun y hy => ?_)
      exact (hβ x ⟨y, hy⟩).symm.trans (h ▸ hβ x' ⟨y, hy⟩)
    · intro φ
      obtain ⟨x, hx, hφ⟩ := exists_traceFormDual_eq hκ X.Gm_det hlat φ.toAddMonoidHom
      refine ⟨⟨x, (hL.2 x).2 hx⟩, LinearMap.ext fun y => Int.cast_injective (α := ℚ) ?_⟩
      exact (hβ _ _).trans (hφ y).symm
  obtain ⟨g', bas, S, hs, -, hr⟩ := exists_symplectic_coordinates_adapted halt hbij (I := ⊥)
    (fun m x hm hx => by simpa [hm] using hx) (by simp) (Or.inr rfl)
  obtain rfl : g' = g := by omega
  exact ⟨bas, fun a b => by rw [← hβ, hs]; simp⟩

end GlobalTheory.Dict.Letters

open GlobalTheory.Dict.Letters GlobalTheory.Harm in

theorem GlobalTheory.Dict.exists_dic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (c : Coeff l) (σ : c.F →+* ℂ) (r g n : ℕ) (X : Data E r) (a : (E →+* ℂ) × ℕ → ℕ) (e : Fin g ≃ Lt1 Dw), GoodEmb c σ → r = Dw.p + Dw.q → X.p0 = Dw.q → (∀ τ : E →+* ℂ, τ ∈ X.Ψ ↔ τ (H.rt : E) = H.rt0) → SelfD X X.Λ → Dom a n → ∃ Dc : Dic Dw c σ X g Dw.p n a, Dc.e = e ∧ (LastPos Dw a → 0 < Dw.p → ∃ τ, ∃ i : Fin Dw.p, i.val + 1 = Dw.p ∧ 1 ≤ Dc.k τ i) := by
  intro E _ _ _ H Dw l c σ r g n X a e hσ hr hp0 hΨ hL hD
  obtain ⟨hbij, hrt, hcj, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  have hr' : X.p0 + Dw.p = r := by omega
  have i1 := ComplexEmbedding.involutive_conjugate E
  have i2 : ∀ τ, ¬ InPsi H τ ↔ InPsi H (ComplexEmbedding.conjugate τ) := not_mem_hostType_iff H
  have i3 : ∀ τ, InPsi H τ → Dw.mult τ = Dw.p := fun _ => mult_of_mem Dw
  have i4 : ∀ τ, InPsi H τ → Dw.mult (ComplexEmbedding.conjugate τ) = X.p0 := fun _ h =>
    (mult_conjEmb_of_mem Dw h).trans hp0.symm
  let f : {τ // InPsi H τ} ≃ X.Ψ := (Equiv.ofBijective _ hbij).subtypeEquiv fun τ =>
    ((hΨ _).trans (hrt τ)).symm
  have hf (t : {τ // InPsi H τ}) : (f t).1 = relab c σ t.1 := rfl
  let ρ : Lt1 Dw ≃ X.Ψ × (Fin Dw.p ⊕ Fin X.p0) :=
    (halfRowEquiv i1 i2 i3 i4).trans (f.prodCongr (Equiv.refl _))
  let idx : Fin g ≃ X.Ψ × Fin r := e.trans (ρ.trans (rowOf X hr'))
  have hidx (j) : (∃ t : {τ // InPsi H τ}, ∃ i : Fin Dw.p, (e j).1 = t.1 ∧ ((e j).2 : ℕ) = i ∧
      idx j = (f t, rowIdx hr' (Sum.inl i))) ∨
      ∃ t : {τ // InPsi H τ}, ∃ i : Fin X.p0, (e j).1 = ComplexEmbedding.conjugate t.1 ∧ ((e j).2 : ℕ) = i ∧
        idx j = (f t, rowIdx hr' (Sum.inr i)) := by
    obtain ⟨⟨t, i | i⟩, h⟩ := (halfRowEquiv i1 i2 i3 i4).symm.surjective (e j)
    · refine Or.inl ⟨t, i, by rw [← h]; rfl, by rw [← h]; rfl, ?_⟩
      simp only [idx, ρ, Equiv.trans_apply, ← h, Equiv.apply_symm_apply]
      rfl
    · refine Or.inr ⟨t, i, by rw [← h]; rfl, by rw [← h]; rfl, ?_⟩
      simp only [idx, ρ, Equiv.trans_apply, ← h, Equiv.apply_symm_apply]
      rfl
  obtain ⟨bas, hbas⟩ := exists_isSympl X hL idx
  let k₀ : {τ // InPsi H τ} → Fin Dw.p → ℕ := fun t => diffOf fun i => a (t.1, i)
  let k₀' : {τ // InPsi H τ} → Fin X.p0 → ℕ := fun t => diffOf fun i => a (ComplexEmbedding.conjugate t.1, i)
  have hx (t) : partOf (k₀ t) = fun i : Fin Dw.p => a (t.1, i) :=
    partOf_diffOf fun i j h => hD.1 _ h
  have hy (t) : partOf (k₀' t) = fun i : Fin X.p0 => a (ComplexEmbedding.conjugate t.1, i) :=
    partOf_diffOf fun i j h => hD.1 _ h
  let eL : LtN Dw n ≃ Harm.Var X.Ψ Dw.p X.p0 (Fin n) :=
    (typeLetterEquiv i1 i2 i3 i4 n).trans (f.prodCongr (Equiv.refl _))
  have hmem (P : MvPolynomial (LtN Dw n) c.F) :
      P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) ↔
        MvPolynomial.rename eL P ∈ rowHighest c.F (k₀ ∘ f.symm) (k₀' ∘ f.symm) := by
    rw [Equiv.coe_trans, ← MvPolynomial.rename_rename,
      rename_place_mem_iff f (c := k₀) (c' := k₀') (fun t => by simp) (fun t => by simp)]
    simp only [mem_HHa_iff_rename i1 i2 i3 i4, mem_rowHighest_iff_rowAdd, hx, hy]
  have hinv (τ) : Function.invFun (relab c σ) (relab c σ τ) = τ := Function.leftInverse_invFun hbij.1 τ
  refine ⟨⟨hr', bas, idx, hbas, e, eL, k₀ ∘ f.symm, k₀' ∘ f.symm, fun x v j => ?_, fun j => ?_,
    fun ℓ => ?_, ?_, fun P hP => ?_, ?_⟩, rfl, fun hpos hp => ?_⟩
  · rcases hidx j with ⟨t, i, h1, h2, h3⟩ | ⟨t, i, h1, h2, h3⟩
    · have hi := i.isLt
      rw [pv, Function.comp_apply, h3, h2, h1, per_of_le _ _ _ _ (by simp), perFr,
        dif_pos (show relab c σ t.1 ∈ X.Ψ from (f t).2), dif_pos (by omega)]
      rfl
    · have hi := i.isLt
      have h4 : relab c σ (ComplexEmbedding.conjugate t.1) = ComplexEmbedding.conjugate (f t).1 := hcj t.1
      rw [pv, Function.comp_apply, h3, h2, h1, per_of_lt _ _ _ _ (by rw [rowIdx_inr]; omega), h4]
      have h5 : rowIdx hr' (Sum.inr i) = ⟨X.p0 - 1 - i, by omega⟩ := Fin.ext (rowIdx_inr hr' i)
      rw [h5]
      generalize f t = u
      obtain ⟨τ, hτ⟩ := u
      obtain ⟨τ, rfl⟩ := i1.surjective τ
      rw [show ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ from i1 τ, perFr,
        dif_neg (fun h => (X.cmType τ).1 h hτ), dif_pos (show conjEmb τ ∈ X.Ψ from hτ), dif_pos (by omega)]
      rfl
  · rcases hidx j with ⟨t, i, h1, h2, h3⟩ | ⟨t, i, h1, h2, h3⟩
    · rw [h3, h1]
      exact rowType_rowOf_inl X hr' (f t) i
    · rw [h3, h1]
      exact (rowType_rowOf_inr X hr' (f t) i).trans (hcj t.1).symm
  · have : idx.symm (rowOf X hr' ((eL ℓ).1, (eL ℓ).2.1)) = e.symm ⟨ℓ.1, ℓ.2.1⟩ := by
      rw [Equiv.symm_apply_eq]
      simp only [idx, Equiv.trans_apply, Equiv.apply_symm_apply]
      rfl
    rw [letterDir, this]
    rfl
  · funext τ j
    obtain ⟨t, rfl⟩ := f.surjective τ
    obtain ⟨i | i, rfl⟩ := (rowIdx hr').surjective j
    · rw [wtOf_inl, wtX, if_pos (by simp), hf, hinv, Function.comp_apply, f.symm_apply_apply, hx]
      simp
    · have hi := i.isLt
      rw [wtOf_inr, wtX, if_neg (by rw [rowIdx_inr]; omega), hf, ← hcj, hinv, Function.comp_apply,
        f.symm_apply_apply, hy, rowIdx_inr, show X.p0 - 1 - (X.p0 - 1 - i) = i by omega]
      rfl
  · rw [← MvPolynomial.map_rename]
    exact map_mem_rowHighest _ ((hmem P).1 hP)
  · letI := σ.toAlgebra
    rw [← span_map_rowHighest c.F ℂ]
    refine Submodule.span_mono ?_
    rintro _ ⟨Q, hQ, rfl⟩
    obtain ⟨P, rfl⟩ := MvPolynomial.rename_surjective _ eL.surjective Q
    exact ⟨P, (hmem P).2 hQ, (MvPolynomial.map_rename _ _ _).symm⟩
  · obtain ⟨t⟩ : Nonempty {τ // InPsi H τ} := by
      obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
      by_cases h : InPsi H τ
      · exact ⟨⟨τ, h⟩⟩
      · exact ⟨⟨_, (i2 τ).1 h⟩⟩
    refine ⟨f t, ⟨Dw.p - 1, by omega⟩, by simp only; omega, ?_⟩
    have := hpos t.1 t.2 (by rw [i3 _ t.2]; exact hp)
    rw [i3 _ t.2] at this
    simp only [Function.comp_apply, Equiv.symm_apply_apply, k₀, diffOf]
    rw [dif_neg (by omega)]
    exact this
