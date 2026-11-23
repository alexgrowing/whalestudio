import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SCuIsom
import Development.AbelianVarietyTheory.Definitions.Foundations.AuxiliaryFrameNormalizedSpaces
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIrreducible

noncomputable section

namespace GlobalTheory.Mem.SStageInhab

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem

theorem ncard_primesOver_eq (E : Type) [Field E] [NumberField E] (l : ℕ) (hl : l.Prime) :
    ((Ideal.span {(l : ℤ)}).primesOver (𝓞 E)).ncard = (placesOver E l).ncard := by
  symm
  apply Set.ncard_congr (fun v _ => v.asIdeal)
  · intro v hv
    refine ⟨v.isPrime, ⟨?_⟩⟩
    have hm : (Ideal.span {(l : ℤ)}).IsMaximal :=
      Ideal.IsPrime.isMaximal ((Ideal.span_singleton_prime (by exact_mod_cast hl.ne_zero)).2 (Nat.prime_iff_prime_int.1 hl)) (by simpa using hl.ne_zero)
    refine hm.eq_of_le (Ideal.IsPrime.ne_top (Ideal.IsPrime.under ℤ v.asIdeal)) ?_
    rw [Ideal.span_singleton_le_iff_mem]
    simpa [Ideal.under, placesOver] using hv
  · intro a b _ _ h; exact HeightOneSpectrum.ext h
  · rintro P ⟨hP, hP'⟩
    have hmem : ((l:ℕ) : 𝓞 E) ∈ P := by
      have : (l:ℤ) ∈ P.under ℤ := by rw [← hP'.over]; exact Ideal.mem_span_singleton_self _
      simpa [Ideal.under] using this
    refine ⟨⟨P, hP, ?_⟩, hmem, rfl⟩
    rintro rfl
    exact hl.ne_zero (by simpa using hmem)

theorem conjF_ne_id (B : Base) : B.toPre.conjF ≠ AlgHom.id _ _ := by
  letI := B.host.cmStar
  intro h
  have h2 := B.sp.cm.deg2
  have hs : Function.Surjective (algebraMap B.host.F B.host.E) := fun a => by
    have : B.toPre.conjF a = a := by rw [h]; rfl
    exact (B.sp.cm.fixed a).1 this
  have : Module.finrank B.host.F B.host.E = 1 := by
    rw [← Algebra.finrank_eq_one_iff_bijective_algebraMap.symm] ; exact ⟨(algebraMap B.host.F B.host.E).injective, hs⟩
  omega

theorem exists_locAt_split_iff (B : Base) (h2 : Module.finrank B.host.F B.host.E = 2) (hne : B.toPre.conjF ≠ AlgHom.id _ _) (p) :
    ∃ L : Formalism.MainNotions.S.Loc.LocAt B.host.F B.host.E B.toPre.conjF p, (L.split.isSome ↔
    Formalism.MainNotions.S.Loc.resChar p ∈ ({B.host.g 0, B.host.g 1} : Finset ℕ)) := by
  obtain ⟨L, hL⟩ := GlobalTheory.LocalData.exists_locAt _ _ B.toPre.conjF h2 p
  by_cases h : Formalism.MainNotions.S.Loc.resChar p ∈ ({B.host.g 0, B.host.g 1} : Finset ℕ)
  · obtain ⟨S⟩ := GlobalTheory.LocSplit.nonempty_splitAt _ _ _ h2 hne p L (by
      rw [ncard_primesOver_eq _ _ L.ellPrime.out]
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with h | h <;> rw [h] <;> exact B.toPre.g_split _)
    exact ⟨{L with split := some S}, by simp [h]⟩
  · exact ⟨L, by simp [hL, h]⟩

theorem nonempty_conj_embedding (EE : Type) [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] (d D : ℕ) (h : d ≤ D)
    (b : OrthonormalBasis (Fin d) ℂ EE) : Nonempty (EE →ₗᵢ⋆[ℂ] EuclideanSpace ℂ (Fin D)) := by
  let e := EuclideanSpace.basisFun (Fin D) ℂ
  have ho : Orthonormal ℂ (fun i : Fin d => e (Fin.castLE h i)) := e.orthonormal.comp _ (Fin.castLE_injective h)
  let f : EE →ₛₗ[starRingEnd ℂ] EuclideanSpace ℂ (Fin D) :=
    { toFun := fun x => ∑ i, (inner ℂ x (b i)) • e (Fin.castLE h i)
      map_add' := by intro x y; simp [inner_add_left, add_smul, Finset.sum_add_distrib]
      map_smul' := by intro c x; simp [Finset.smul_sum, smul_smul, mul_comm] }
  refine ⟨⟨f, fun x => ?_⟩⟩
  have h1 : inner ℂ (f x) (f x) = ∑ i, (starRingEnd ℂ) (inner ℂ x (b i)) * inner ℂ x (b i) :=
    ho.inner_sum _ _ _
  have h2 := b.sum_inner_mul_inner x x
  have h3 : inner ℂ (f x) (f x) = inner ℂ x x := by
    rw [h1, ← h2]; refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_conj_symm, mul_comm]
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h3
  have h4 : ‖f x‖^2 = ‖x‖^2 := by exact_mod_cast h3
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h4

theorem exists_innerProductSpace (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ip : V → V → ℂ)
    (hs : ∀ x y, (starRingEnd ℂ) (ip y x) = ip x y) (hp : ∀ x, x ≠ 0 → 0 < (ip x x).re)
    (ha : ∀ x y z, ip (x+y) z = ip x z + ip y z) (hm : ∀ x y (r:ℂ), ip (r • x) y = (starRingEnd ℂ) r * ip x y) :
    ∃ (U : Type) (_ : NormedAddCommGroup U) (_ : InnerProductSpace ℂ U) (_ : FiniteDimensional ℂ U) (e : U ≃ₗ[ℂ] V),
      ∀ x y, inner ℂ x y = ip (e x) (e y) := by
  let c : InnerProductSpace.Core ℂ V :=
    { inner := ip, conj_inner_symm := hs
      re_inner_nonneg := fun x => by
        by_cases h : x = 0
        · have := hm x x 0; subst h; simp at this; simp [this]
        · exact (hp x h).le
      add_left := ha, smul_left := hm
      definite := fun x h => by by_contra h'; have := hp x h'; rw [h] at this; simp at this }
  letI n : NormedAddCommGroup V := c.toNormedAddCommGroup
  letI i : InnerProductSpace ℂ V := InnerProductSpace.ofCore c.toCore
  exact ⟨V, n, i, inferInstance, LinearEquiv.refl _ _, fun x y => rfl⟩

theorem exists_sStage (B : Base) (C : Cols B) (W : RowsRest B C)
    (Del : ℚ) (hD : 0 < Del)
    (gap : ∀ w τ (l : ℕ) (h : l + 1 < B.R.k - 1), (B.hcW w τ).v ⟨l, by omega⟩ - (B.hcW w τ).v ⟨l + 1, h⟩ = 4 * Del)
    (letter : B.Word → Fin (B.R.k - 2) → Bool) (hinj : Function.Injective letter)
    (hu : ∀ w τ (l : ℕ) (h : l < B.R.k - 2), (B.hcW w τ).u ⟨l + 1, by omega⟩ =
      (B.hcW w τ).v ⟨l, by omega⟩ - 1 / 2 - (if letter w ⟨l, h⟩ then Del else 0))
    (hs : ∀ u, ∀ x ∈ (C.mem u).A.Mu0, ∀ y ∈ (C.mem u).A.Mu0, (starRingEnd ℂ) ((C.fm u).ipC 0 y x) = (C.fm u).ipC 0 x y)
    (hp : ∀ u, ∀ x ∈ (C.mem u).A.Mu0, x ≠ 0 → 0 < ((C.fm u).ipC 0 x x).re)
    (hDD : W.Drows ≤ W.Dall) :
    ∃ S : SStage B C W, S.s.Del = Del ∧ S.s.letter = letter ∧ (∀ u u', Nonempty (S.s.Term u u')) ∧
      ∀ u u', Nonempty (S.s.Pair u u') := by
  have hloc := by
    letI := B.host.cmStar
    exact exists_locAt_split_iff B B.sp.cm.deg2 (conjF_ne_id B)
  choose L hL using hloc
  let pt : Formalism.MainNotions.S.Point B.host.E (B.R.rS + 1) := ⟨[(1, B.R.rS + 1)], by simp, by simp⟩
  have hU := fun u => by
    haveI := (C.mem u).A.Mu0_fd
    exact exists_innerProductSpace (C.mem u).A.Mu0 (fun x y => (C.fm u).ipC 0 x.1 y.1) (fun x y => hs u _ x.2 _ y.2)
      (fun x hx => hp u _ x.2 (fun h => hx (Subtype.ext h)))
      (fun x y z => by simp [MemberForms.ipC, mul_add, Finset.sum_add_distrib])
      (fun x y r => by simp [MemberForms.ipC, Finset.mul_sum, mul_left_comm])
  choose U n i f e he using hU
  obtain ⟨sE⟩ := nonempty_conj_embedding W.EE _ _ hDD W.onb
  let s : Formalism.MainNotions.S.Draft.SData B.R B.host.F B.host.E B.toPre.conjF B.Word (Tau B.R) B.hcW :=
    { cdScale := fun _ _ => 1, cdScale_pos := fun _ _ => one_pos, Del := Del, Del_pos := hD, cloud_gap := gap
      letter := letter, letter_inj := hinj, u_letter := hu, HH := EuclideanSpace ℂ (Fin W.Dall)
      Cu := U, cuN := n, cuI := i, cuF := f, Pu := fun _ => 0, volN := fun _ => 1, volH := fun _ => 1
      volN_pos := fun _ => one_pos, volH_pos := fun _ => one_pos, Term := fun _ _ => Unit
      aTerm := fun _ _ _ => 0, isId := fun _ => True, inS := fun _ => True, relevant := fun _ => True
      FeqF := fun _ => True, Gterm := fun _ => 0, atP := L, PlF := HeightOneSpectrum (𝓞 B.host.F)
      BBne := fun _ _ => False, generic := fun _ => False, Pair := fun _ _ => Unit
      pfst := fun _ => (), psnd := fun _ => (), s0 := fun _ => 0, scalarPair := fun _ => True
      pval := fun _ => 0, ptOf := fun _ => pt, cTerm := fun _ => 1, massPair := fun _ => 1
      meanCount := fun _ _ _ => 0 }
  exact ⟨{ dsig := fun _ => 1, dsig_pos := fun _ => one_pos, s := s, s_split := hL, s_HH := by simp [s]
           s_Cu := e, s_PlF := Equiv.refl _, s_Cu_isom := he, sEE := sE },
    rfl, rfl, fun _ _ => ⟨()⟩, fun _ _ => ⟨()⟩⟩

theorem nonempty_sStage (B : Base) (C : Cols B) (W : RowsRest B C)
    (Del : ℚ) (hD : 0 < Del)
    (gap : ∀ w τ (l : ℕ) (h : l + 1 < B.R.k - 1), (B.hcW w τ).v ⟨l, by omega⟩ - (B.hcW w τ).v ⟨l + 1, h⟩ = 4 * Del)
    (letter : B.Word → Fin (B.R.k - 2) → Bool) (hinj : Function.Injective letter)
    (hu : ∀ w τ (l : ℕ) (h : l < B.R.k - 2), (B.hcW w τ).u ⟨l + 1, by omega⟩ =
      (B.hcW w τ).v ⟨l, by omega⟩ - 1 / 2 - (if letter w ⟨l, h⟩ then Del else 0))
    (hs : ∀ u, ∀ x ∈ (C.mem u).A.Mu0, ∀ y ∈ (C.mem u).A.Mu0, (starRingEnd ℂ) ((C.fm u).ipC 0 y x) = (C.fm u).ipC 0 x y)
    (hp : ∀ u, ∀ x ∈ (C.mem u).A.Mu0, x ≠ 0 → 0 < ((C.fm u).ipC 0 x x).re)
    (hDD : W.Drows ≤ W.Dall) : Nonempty (SStage B C W) :=
  (exists_sStage B C W Del hD gap letter hinj hu hs hp hDD).elim fun S _ => ⟨S⟩

end GlobalTheory.Mem.SStageInhab

end
