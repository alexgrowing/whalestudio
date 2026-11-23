import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.FinMax
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.FinCompl
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.CofinalCompl
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.IdemLift

open IsLocalRing

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.maxIdem :
    ∀ (Λ T : Type) [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] [CommRing T] [Algebra Λ T] [Module.Finite Λ T] (m : Ideal T), m.IsMaximal → ∃ e : T, IsIdempotentElem e ∧ e ∉ m ∧ ∀ m' : Ideal T, m'.IsMaximal → m' ≠ m → e ∈ m' := by
  intro Λ T _ _ _ _ _ _ _ m hm
  classical
  obtain ⟨hfin, -, n, h1, h2⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.finMax Λ T
  set I' := Ideal.map (algebraMap Λ T) (maximalIdeal Λ) with hI'
  have key : ∀ (k : ℕ) (y : T), y ∈ ((maximalIdeal Λ) ^ k • (⊤ : Submodule Λ T)) ↔
      y ∈ (I' ^ k • (⊤ : Submodule T T)) := by
    intro k y
    rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, Ideal.map_pow, Ideal.smul_eq_mul,
      Ideal.mul_top]
  haveI hΛ : IsAdicComplete (maximalIdeal Λ) T := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.finCompl Λ T (maximalIdeal Λ)
  have hT : IsAdicComplete I' T :=
    { haus' := fun y hy => IsHausdorff.haus' (I := maximalIdeal Λ) y fun k =>
        SModEq.sub_mem.mpr ((key k _).mpr (SModEq.sub_mem.mp (hy k)))
      prec' := fun f hf => by
        obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := maximalIdeal Λ) f fun hmn =>
          SModEq.sub_mem.mpr ((key _ _).mpr (SModEq.sub_mem.mp (hf hmn)))
        exact ⟨L, fun k => SModEq.sub_mem.mpr ((key k _).mp (SModEq.sub_mem.mp (hL k)))⟩ }
  haveI hJ : IsAdicComplete (⊥ : Ideal T).jacobson T :=
    UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.cofinalCompl T T I' _ n h1 h2 hT
  haveI := hfin
  haveI := Fintype.ofFinite (MaximalSpectrum T)
  set s := Finset.univ.filter (fun p : MaximalSpectrum T => p.asIdeal ≠ m) with hs
  set m'' := s.inf (fun p => p.asIdeal) with hm''
  have hnot : ¬ m'' ≤ m := by
    intro h
    obtain ⟨p, hp, hpm⟩ := (Ideal.IsPrime.inf_le' hm.isPrime).mp h
    exact (Finset.mem_filter.mp hp).2 (p.isMaximal.eq_of_le hm.ne_top hpm)
  have htop : m ⊔ m'' = ⊤ :=
    hm.out.2 _ (lt_of_le_of_ne le_sup_left fun h => hnot (h ▸ le_sup_right))
  have h1mem : (1 : T) ∈ m ⊔ m'' := htop ▸ Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp h1mem
  have hbp : ∀ p : Ideal T, p.IsMaximal → p ≠ m → b ∈ p := by
    intro p hp hpm
    have hle : m'' ≤ p :=
      Finset.inf_le (f := fun p : MaximalSpectrum T => p.asIdeal) (b := ⟨p, hp⟩) (by simp [s, hpm])
    exact hle hb
  have memJ : ∀ y : T, (∀ p : Ideal T, p.IsMaximal → y ∈ p) → y ∈ (⊥ : Ideal T).jacobson :=
    fun y hy => Ideal.mem_sInf.mpr fun p hp => hy p hp.2
  have hJm : ∀ y : T, y ∈ (⊥ : Ideal T).jacobson → ∀ p : Ideal T, p.IsMaximal → y ∈ p :=
    fun y hy p hp => Ideal.mem_sInf.mp hy ⟨bot_le, hp⟩
  have hxx : b * b - b ∈ (⊥ : Ideal T).jacobson := by
    have e1 : b * b - b = -(b * a) := by
      have ha' : a = 1 - b := by rw [← hab]; ring
      rw [ha']
      ring
    rw [e1]
    refine memJ _ fun p hp => p.neg_mem ?_
    by_cases hpm : p = m
    · rw [hpm]
      exact m.mul_mem_left _ ha
    · exact p.mul_mem_right _ (hbp p hp hpm)
  obtain ⟨e, he, hex⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.idemLift T _ b hxx
  refine ⟨e, he, fun hem => ?_, fun p hp hpm => ?_⟩
  · apply hm.ne_top
    rw [Ideal.eq_top_iff_one]
    have h3 : e - b ∈ m := hJm _ hex m hm
    have h4 : (1 : T) = e - (e - b) + a := by rw [← hab]; ring
    rw [h4]
    exact m.add_mem (m.sub_mem hem h3) ha
  · have h3 : e - b ∈ p := hJm _ hex p hp
    have h4 : e = (e - b) + b := by ring
    rw [h4]
    exact p.add_mem h3 (hbp p hp hpm)
