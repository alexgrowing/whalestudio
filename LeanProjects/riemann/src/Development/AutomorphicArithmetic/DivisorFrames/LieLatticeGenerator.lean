import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepIdeal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricFrameEqRiemannFormAtInteriorPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IoOfLeOneIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiFibrationLieLatticeFullStatement
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LieRead

private theorem mem_letters' {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (Dw : Datum H) (x : Letter Dw) : x ∈ letters Dw := by
  obtain ⟨τ, i⟩ := x
  obtain ⟨a, rfl⟩ := (Fintype.equivFin (E →+* ℂ)).symm.surjective τ
  unfold letters
  exact List.mem_flatMap.2 ⟨a, List.mem_finRange _, List.mem_map.2 ⟨i, List.mem_finRange _, rfl⟩⟩

private theorem nodup_letters' {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (Dw : Datum H) : (letters Dw).Nodup := by
  unfold letters
  rw [List.nodup_flatMap]
  refine ⟨fun a _ => (List.nodup_finRange _).map fun i j h => ?_, ?_⟩
  · exact eq_of_heq (Sigma.mk.inj_iff.1 h).2
  · refine (List.nodup_finRange _).imp ?_
    intro a b hab
    simp only [Function.onFun]
    intro x hx hy
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    obtain ⟨j, -, h⟩ := List.mem_map.1 hy
    exact hab ((Fintype.equivFin (E →+* ℂ)).symm.injective (congrArg Sigma.fst h)).symm

private theorem mem_span_single' {K : Type} [Field K] {g : ℕ} (S : Set (Fin g)) (T : Set (Fin g → K))
    (hT : ∀ v, v ∈ T ↔ ∃ k ∈ S, v = Pi.single k 1) (v : Fin g → K) :
    v ∈ Submodule.span K T ↔ ∀ k, k ∉ S → v k = 0 := by
  classical
  constructor
  · intro hv k hk
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, hj, rfl⟩ := (hT x).1 hx
      exact Pi.single_eq_of_ne (show k ≠ j from fun h => hk (by rw [h]; exact hj)) _
    | zero => rfl
    | add x y _ _ hx hy => simp [hx, hy]
    | smul a x _ hx => simp [hx]
  · intro h
    rw [pi_eq_sum_univ' v]
    refine Submodule.sum_mem _ fun k _ => ?_
    by_cases hk : k ∈ S
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ((hT _).2 ⟨k, hk, rfl⟩))
    · rw [h k hk, zero_smul]; exact Submodule.zero_mem _

private theorem exists_mul_mem' {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (L : Submodule (𝓞 K) V) (v : V)
    (hv : v ∈ Submodule.span K (L : Set V)) : ∃ d : 𝓞 K, d ≠ 0 ∧ d • v ∈ L := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d, hd, hx⟩ := hx
    obtain ⟨e, he, hy⟩ := hy
    refine ⟨d * e, mul_ne_zero hd he, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact L.smul_mem _ hx
    · rw [mul_smul]; exact L.smul_mem _ hy
  | smul a x _ hx =>
    obtain ⟨d, hd, hx⟩ := hx
    obtain ⟨⟨e, he⟩, b, hb⟩ := IsLocalization.exists_integer_multiple (nonZeroDivisors (𝓞 K)) a
    refine ⟨e * d, mul_ne_zero (nonZeroDivisors.ne_zero he) hd, ?_⟩
    have : (e * d) • a • x = b • d • x := by
      rw [mul_comm, mul_smul, ← smul_assoc e a x, show e • a = algebraMap _ K b from hb.symm, algebraMap_smul, smul_comm]
    rw [this]
    exact L.smul_mem _ hx

theorem UpperTheory.lie_lattice_generator :
    ∀ (D : D7) (O : Setup D) (K : Type) [Field K] [NumberField K] (F : SemiFib K) (τ : D.host.E →+* ℂ) (i : ℕ) (hi : i < O.S.Dw.mult τ), F.P₀.g = (letters O.S.Dw).length → ∃ q : Fin F.P₀.g, (letters O.S.Dw)[(q : ℕ)]? = some ⟨τ, ⟨i, hi⟩⟩ ∧ stepVec O F τ i = Pi.single q 1 ∧ (stepIdeal O F τ i).FG ∧ (∃ v ∈ F.lieLat, (∀ k : Fin F.P₀.g, k ∉ {k : Fin F.P₀.g | ∃ x : Letter O.S.Dw, x.1 = τ ∧ (x.2 : ℕ) < i + 1 ∧ (letters O.S.Dw)[(k : ℕ)]? = some x} → v k = 0) ∧ v q ≠ 0) ∧ (stepIdeal O F τ i : Set K) = {b : K | ∃ v ∈ F.lieLat, (∀ k : Fin F.P₀.g, k ∉ {k : Fin F.P₀.g | ∃ x : Letter O.S.Dw, x.1 = τ ∧ (x.2 : ℕ) < i + 1 ∧ (letters O.S.Dw)[(k : ℕ)]? = some x} → v k = 0) ∧ b = v q} := by
  classical
  intro D O K _ _ F τ i hi hg
  obtain ⟨n, hn, hq⟩ := List.getElem_of_mem (mem_letters' O.S.Dw ⟨τ, ⟨i, hi⟩⟩)
  let q : Fin F.P₀.g := ⟨n, hg ▸ hn⟩
  have hq' : (letters O.S.Dw)[(q : ℕ)]? = some ⟨τ, ⟨i, hi⟩⟩ := List.getElem?_eq_some_iff.2 ⟨hn, hq⟩
  have hvec : stepVec O F τ i = Pi.single q 1 := by
    funext p
    unfold stepVec
    by_cases hp : p = q
    · subst hp
      rw [if_pos ⟨_, rfl, rfl, hq'⟩, Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne hp, if_neg]
      rintro ⟨⟨τ', j, hj⟩, h1, h2, h3⟩
      dsimp only at h1 h2
      subst h1 h2
      obtain ⟨hp', h4⟩ := List.getElem?_eq_some_iff.1 h3
      exact hp (Fin.ext ((List.Nodup.getElem_inj_iff (nodup_letters' O.S.Dw)).1 (h4.trans hq.symm)))
  have hcoef : ∀ v, stepCoef O F τ i v = v q := by
    intro v
    simp [stepCoef, hvec, Pi.single_apply]
  have hfull := (GlobalTheory.T.semi_fibration_lie_lattice_full K F).1
  have hlat : ∀ v, v ∈ stepLat O F τ (i + 1) ↔ v ∈ F.lieLat ∧ ∀ k : Fin F.P₀.g, k ∉ {k : Fin F.P₀.g | ∃ x : Letter O.S.Dw, x.1 = τ ∧ (x.2 : ℕ) < i + 1 ∧ (letters O.S.Dw)[(k : ℕ)]? = some x} → v k = 0 := by
    intro v
    rw [stepLat, Submodule.mem_inf, Submodule.restrictScalars_mem]
    refine and_congr Iff.rfl (mem_span_single' _ _ (fun w => ?_) v)
    constructor
    · rintro ⟨k, x, a, b, c, d⟩
      exact ⟨k, ⟨x, a, b, c⟩, d⟩
    · rintro ⟨k, ⟨x, a, b, c⟩, d⟩
      exact ⟨k, x, a, b, c, d⟩
  refine ⟨q, hq', hvec, ?_, ?_, ?_⟩
  · refine Submodule.FG.map _ ?_
    exact Submodule.FG.of_le hfull.1 inf_le_left
  · obtain ⟨d, hd, hv⟩ := exists_mul_mem' F.lieLat (Pi.single q 1) (by rw [hfull.2]; trivial)
    refine ⟨_, hv, fun k hk => ?_, ?_⟩
    · have : k ≠ q := by
        rintro rfl
        exact hk ⟨_, rfl, Nat.lt_succ_self _, hq'⟩
      simp [Pi.single_eq_of_ne this]
    · simpa using hd
  · ext b
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v, ((hlat v).1 hv).1, ((hlat v).1 hv).2, hcoef v⟩
    · rintro ⟨v, h1, h2, rfl⟩
      exact ⟨v, (hlat v).2 ⟨h1, h2⟩, hcoef v⟩
