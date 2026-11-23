import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GgNone

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.CoordExist

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

noncomputable def linL (H : HermSp M V) (y : V) : V →ₗ[E] E where
  toFun x := H.h x y
  map_add' a b := H.h_add_left a b y
  map_smul' a x := H.h_smul_left a x y

lemma h_sum_left (H : HermSp M V) {n : ℕ} (c : Fin n → E) (b : Fin n → V) (y : V) :
    H.h (∑ i, c i • b i) y = ∑ i, c i * H.h (b i) y := by
  show linL H y (∑ i, c i • b i) = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul]
  rfl

lemma hf_eq (H : HermSp M V) {n : ℕ} (b : Fin n → V) (c d : Fin n → E) :
    hf M.L (Matrix.of fun i j => H.h (b i) (b j)) c d = H.h (∑ i, c i • b i) (∑ j, d j • b j) := by

  have hr : ∀ (x : V) (d : Fin n → E), H.h x (∑ j, d j • b j) = ∑ j, M.L.cj (d j) * H.h x (b j) := by
    intro x d
    rw [H.h_herm, h_sum_left, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, ← H.h_herm]
  rw [h_sum_left]
  unfold GlobalTheory.HL.hf
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hr, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.of_apply]
  ring

lemma hf_basis (H : HermSp M V) {n : ℕ} (b : Module.Basis (Fin n) E V) (x y : V) :
    hf M.L (Matrix.of fun i j => H.h (b i) (b j)) (b.equivFun x) (b.equivFun y) = H.h x y := by
  rw [hf_eq, b.sum_equivFun, b.sum_equivFun]

lemma nontriv (L : LocE F E) : Nontrivial E := Module.nontrivial_of_finrank_pos (R := F) (by rw [L.rank]; norm_num)

lemma hermND (H : HermSp M V) {n : ℕ} (b : Module.Basis (Fin n) E V) :
    IsHermND M.L (Matrix.of fun i j => H.h (b i) (b j)) := by
  refine ⟨?_, ?_⟩
  · unfold GlobalTheory.HL.IsHerm GlobalTheory.HL.cT
    ext i j
    exact (H.h_herm (b j) (b i)).symm
  · have := M.L.free
    have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [M.L.rank]; norm_num)
    set G : Matrix (Fin n) (Fin n) E := Matrix.of fun i j => H.h (b i) (b j) with hGdef
    have hvec : ∀ (v : Fin n → E) j, (Matrix.vecMul v G) j = H.h (∑ i, v i • b i) (b j) := by
      intro v j
      rw [h_sum_left]
      simp only [Matrix.vecMul, dotProduct, hGdef, Matrix.of_apply]
    have hright : ∀ x y : V, H.h x y = ∑ j, M.L.cj (b.repr y j) * H.h x (b j) := by
      intro x y
      conv_lhs => rw [← b.sum_repr y]
      rw [H.h_herm, h_sum_left, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, ← H.h_herm]

    have hinj : Function.Injective (Matrix.vecMulLinear G) := by
      intro v v' hvv
      have hvv' : Matrix.vecMul v G = Matrix.vecMul v' G := hvv
      have hd : ∀ j, (Matrix.vecMul (v - v') G) j = 0 := by
        intro j
        rw [Matrix.sub_vecMul, hvv', sub_self]
        rfl
      have hx : ∑ i, (v - v') i • b i = 0 := by
        apply H.nondeg
        intro y
        rw [hright]
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [← hvec, hd, mul_zero]
      have h0 := Fintype.linearIndependent_iff.mp b.linearIndependent (v - v') hx
      funext i
      exact sub_eq_zero.mp (h0 i)

    have hsurj : Function.Surjective (Matrix.vecMulLinear G) := by
      have h2 : Function.Injective ((Matrix.vecMulLinear G).restrictScalars F) := hinj
      exact LinearMap.injective_iff_surjective.mp h2
    exact (Matrix.isUnit_iff_isUnit_det G).mp (Matrix.vecMul_surjective_iff_isUnit.mp hsurj)

lemma not_field (L : LocE F E) (g : SplitG L) : ¬ IsField E := by
  intro hE
  have hx : g.e.symm (1, 0) ≠ 0 := by
    intro h0
    have h1 := congrArg g.e h0
    simp at h1
  obtain ⟨x', hx'⟩ := hE.mul_inv_cancel hx
  have hxy : g.e.symm (1, 0) * g.e.symm (0, 1) = 0 := by
    rw [← map_mul]
    simp
  have hy : g.e.symm (0, 1) = 0 := by
    calc g.e.symm (0, 1) = (x' * g.e.symm (1, 0)) * g.e.symm (0, 1) := by
          rw [mul_comm x', hx', one_mul]
      _ = 0 := by rw [mul_assoc, hxy, mul_zero]
  have h1 := congrArg g.e hy
  simp at h1

lemma gram_eq {H : HermSp M V} {r : ℕ} (A : LocNG.FrameD H r) (a b : Fin (r + 1)) :
    H.h (A.f a) (A.f b) = if a = Fin.last r ∧ b = Fin.last r then -algebraMap F E A.T else 0 := by
  split_ifs with hab
  · rw [hab.1, hab.2]
    exact A.h_zz
  · exact A.h_iso a b (not_and_or.mp hab)

lemma dual_eq {H : HermSp M V} {r : ℕ} (A : LocNG.FrameD H r) (a : Fin (r + 1)) (j : Fin r) :
    H.h (A.f a) (A.es j) = if a = j.castSucc then 1 else 0 := by
  induction a using Fin.lastCases with
  | last =>
    rw [if_neg (Fin.castSucc_lt_last j).ne', H.h_herm, A.h_sz, map_zero]
  | cast i =>
    rw [A.h_es i j]
    simp only [Fin.castSucc_inj]

lemma unit_of {T : F} (hT : T ∈ 𝒪[F]) (u : 𝒪[F]) (h : (u : F) * T = 1) :
    ∃ v : (𝒪[F])ˣ, ((v : 𝒪[F]) : F) = T := by
  refine ⟨⟨⟨T, hT⟩, u, ?_, ?_⟩, rfl⟩
  · apply Subtype.ext
    show T * (u : F) = 1
    rw [mul_comm]
    exact h
  · apply Subtype.ext
    show (u : F) * T = 1
    exact h

end

theorem exists_coord : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → ∃ S : Frames M.L r k, Nonempty (Coord P S) := by
  intro F _ _ _ E _ _ _ _ M hOK V _ _ H r k P hrank hrel
  have := hOK.loc
  have : Nontrivial E := nontriv M.L
  have := H.free
  have := H.fin
  unfold LocNG.FPair.RelG LocNG.FPair.IsPoint LocNG.FPair.NormsOK at hrel
  obtain ⟨-, -, hG, -, -, ⟨w, hw⟩, hAT, hA0, hBT, hB0, hsp⟩ := hrel

  obtain ⟨ϖ, hϖ, hϖs⟩ : ∃ ϖ : 𝒪[F], Irreducible ϖ ∧ ∀ g, M.split = some g → ϖ = g.q := by
    cases hs : M.split with
    | none =>
      obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
      exact ⟨ϖ, hϖ, fun g hg => by cases hg⟩
    | some g =>
      exact ⟨g.q, g.q_irr, fun g' hg => by cases hg; rfl⟩
  let bs : Module.Basis (Fin (k + 2 * r + 1)) E V := Module.finBasisOfFinrankEq E V hrank
  have hZ : (Matrix.of fun a c => hf M.L (Matrix.of fun i j => H.h (bs i) (bs j))
      (bs.equivFun (P.B.f c)) (bs.equivFun (P.A.f a))) = H.Zhat P.A.f P.B.f := by
    ext a c
    simp only [Matrix.of_apply, hf_basis]
    rfl
  have hD1 : lead (H.Zhat P.A.f P.B.f) (Fin.last (r + 1)) = H.Dl P.A.f P.B.f (r + 1) := by
    unfold GlobalTheory.HL.lead HermSp.Dl
    rw [dif_pos le_rfl]
  have hD0 : lead (H.Zhat P.A.f P.B.f) (Fin.last r).castSucc = H.Dl P.A.f P.B.f r := by
    unfold GlobalTheory.HL.lead HermSp.Dl
    rw [dif_pos (Nat.le_succ r)]
  have hG' := hG
  unfold LocNG.FPair.Gv HermSp.Gdet HermSp.normE at hG'
  rw [← hD1, ← hD0, ← hZ] at hG'
  let S : Frames M.L r k :=
    { ϖ := ϖ
      ϖ_irr := hϖ
      Hm := Matrix.of fun i j => H.h (bs i) (bs j)
      herm := hermND H bs
      T := Units.mk0 P.A.T hA0
      T' := Units.mk0 P.B.T hB0
      f := fun a => bs.equivFun (P.A.f a)
      f' := fun a => bs.equivFun (P.B.f a)
      es := fun j => bs.equivFun (P.A.es j)
      es' := fun j => bs.equivFun (P.B.es j)
      gram := fun a c => by
        rw [hf_basis, gram_eq]
        rfl
      gram' := fun a c => by
        rw [hf_basis, gram_eq]
        rfl
      dual := fun a j => by rw [hf_basis, dual_eq]
      dual' := fun a j => by rw [hf_basis, dual_eq]
      iso := fun i j => by rw [hf_basis, P.A.h_ss]
      iso' := fun i j => by rw [hf_basis, P.B.h_ss]
      w := w
      relevant := fun a c => by
        rw [hf_basis, ← hw a c]
        have hsq : ((-1 : E) ^ (r - (c : ℕ))) * (-1) ^ (r - (c : ℕ)) = 1 := by
          rw [← mul_pow]
          simp
        show H.h (P.B.f c) (P.A.f a) =
          (-1) ^ (r - (c : ℕ)) * H.h (P.B.f c) (P.A.f a) * (-1) ^ (r - (c : ℕ))
        linear_combination (-(H.h (P.B.f c) (P.A.f a))) * hsq
      G_ne := hG'
      gg := M.split.isSome
      gg_ok := by
        intro hgg
        obtain ⟨g, hg⟩ := Option.isSome_iff_exists.mp hgg
        obtain ⟨⟨u, v, hu, hv⟩, -⟩ := hsp g hg
        exact ⟨not_field M.L g, unit_of hAT u hu, unit_of hBT v hv⟩ }
  refine ⟨S, ⟨{ e := bs.equivFun
                h_eq := fun x y => hf_basis H bs x y
                f_eq := fun a => rfl
                f'_eq := fun a => rfl
                es_eq := fun a => rfl
                es'_eq := fun a => rfl
                T_eq := rfl
                T'_eq := rfl
                gg_none := fun h => ?_
                gg_some := fun g hg => ⟨?_, hϖs g hg⟩ }⟩⟩
  · show M.split.isSome = false
    rw [h]
    rfl
  · show M.split.isSome = true
    rw [hg]
    rfl

end GlobalTheory.HL.CoordExist
