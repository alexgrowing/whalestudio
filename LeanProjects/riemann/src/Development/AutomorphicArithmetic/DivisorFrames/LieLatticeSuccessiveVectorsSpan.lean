import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatDegreeStatementOfDegreeTheorem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCoord
import Development.AbelianVarietyTheory.Definitions.Divisors.VolMeasureOfAdd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepIdeal
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.FlatDegreeCompare

section
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad

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

end

open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LieRead in
theorem UpperTheory.lie_lattice_successive_vectors_span :
    ∀ (D : D7) (O : GlobalTheory.Mean4O.Setup D) (K : Type) [Field K] [NumberField K] (F : GlobalTheory.LieHt.SemiFib K), F.P₀.g = (GlobalTheory.ShFam.Pad.letters O.S.Dw).length → GlobalTheory.LieHt.Full F.lieLat → ∀ ρ : D.host.E →+* ℂ, LinearIndependent K (fun i : Fin (O.S.Dw.mult ρ) => GlobalTheory.LieRead.stepVec O F ρ i) ∧ GlobalTheory.LieRead.stepLat O F ρ (O.S.Dw.mult ρ) = F.lieLat ⊓ (Submodule.span K (Set.range fun i : Fin (O.S.Dw.mult ρ) => GlobalTheory.LieRead.stepVec O F ρ i)).restrictScalars (𝓞 K) ∧ (GlobalTheory.LieRead.stepLat O F ρ (O.S.Dw.mult ρ)).FG ∧ Submodule.span K (Set.range fun i : Fin (O.S.Dw.mult ρ) => GlobalTheory.LieRead.stepVec O F ρ i) = Submodule.span K (GlobalTheory.LieRead.stepLat O F ρ (O.S.Dw.mult ρ) : Set (Fin F.P₀.g → K)) := by
  classical
  intro D O K _ _ F hg hfull ρ
  have key : ∀ i : Fin (O.S.Dw.mult ρ), ∃ q : Fin F.P₀.g,
      (letters O.S.Dw)[(q : ℕ)]? = some ⟨ρ, i⟩ ∧ stepVec O F ρ i = Pi.single q 1 := by
    intro i
    obtain ⟨n, hn, hq⟩ := List.getElem_of_mem (mem_letters' O.S.Dw ⟨ρ, i⟩)
    let q : Fin F.P₀.g := ⟨n, hg ▸ hn⟩
    have hq' : (letters O.S.Dw)[(q : ℕ)]? = some ⟨ρ, i⟩ := List.getElem?_eq_some_iff.2 ⟨hn, hq⟩
    refine ⟨q, hq', ?_⟩
    funext p
    unfold stepVec
    by_cases hp : p = q
    · subst hp
      rw [if_pos ⟨_, rfl, rfl, hq'⟩, Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne hp, if_neg]
      rintro ⟨⟨τ', j⟩, h1, h2, h3⟩
      dsimp only at h1 h2
      subst h1
      obtain rfl : j = i := Fin.ext h2
      obtain ⟨hp', h4⟩ := List.getElem?_eq_some_iff.1 h3
      exact hp (Fin.ext ((List.Nodup.getElem_inj_iff (nodup_letters' O.S.Dw)).1 (h4.trans hq.symm)))
  choose q hq hvec using key
  have hinj : Function.Injective q := by
    intro i j h
    have h1 := hq i
    rw [h, hq j] at h1
    exact (eq_of_heq (Sigma.mk.inj_iff.1 (Option.some.inj h1)).2).symm
  have hset : {v : Fin F.P₀.g → K | ∃ (i : Fin F.P₀.g) (x : Letter O.S.Dw), x.1 = ρ ∧ (x.2 : ℕ) < O.S.Dw.mult ρ ∧
      (letters O.S.Dw)[(i : ℕ)]? = some x ∧ v = Pi.single i 1}
      = Set.range fun i : Fin (O.S.Dw.mult ρ) => stepVec O F ρ i := by
    ext v
    constructor
    · rintro ⟨k, ⟨τ', j⟩, h1, -, h3, rfl⟩
      dsimp only at h1
      subst h1
      refine ⟨j, ?_⟩
      obtain ⟨hk', h4⟩ := List.getElem?_eq_some_iff.1 h3
      obtain ⟨hj', h5⟩ := List.getElem?_eq_some_iff.1 (hq j)
      have : q j = k := Fin.ext ((List.Nodup.getElem_inj_iff (nodup_letters' O.S.Dw)).1 (h5.trans h4.symm))
      simp only [hvec, this]
    · rintro ⟨i, rfl⟩
      exact ⟨q i, ⟨ρ, i⟩, rfl, i.2, hq i, hvec i⟩
  have hlat : stepLat O F ρ (O.S.Dw.mult ρ) = F.lieLat ⊓ (Submodule.span K
      (Set.range fun i : Fin (O.S.Dw.mult ρ) => stepVec O F ρ i)).restrictScalars (𝓞 K) := by
    rw [stepLat, hset]
  refine ⟨?_, hlat, ?_, ?_⟩
  · have h := (Pi.basisFun K (Fin F.P₀.g)).linearIndependent.comp q hinj
    convert h using 1
    funext i
    simp [hvec]
  · exact Submodule.FG.of_le hfull.1 inf_le_left
  · apply le_antisymm
    · intro v hv
      obtain ⟨d, hd, hdv⟩ := exists_mul_mem' F.lieLat v (by rw [hfull.2]; trivial)
      have hm : d • v ∈ stepLat O F ρ (O.S.Dw.mult ρ) := by
        rw [hlat]
        exact ⟨hdv, Submodule.smul_mem ((Submodule.span K
          (Set.range fun i : Fin (O.S.Dw.mult ρ) => stepVec O F ρ i)).restrictScalars (𝓞 K)) d hv⟩
      have hd' : (algebraMap (𝓞 K) K d) ≠ 0 := by simpa using hd
      have : v = (algebraMap (𝓞 K) K d)⁻¹ • d • v := by
        rw [← algebraMap_smul K d v, smul_smul, inv_mul_cancel₀ hd', one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span hm)
    · rw [Submodule.span_le, hlat]
      exact fun v hv => hv.2
