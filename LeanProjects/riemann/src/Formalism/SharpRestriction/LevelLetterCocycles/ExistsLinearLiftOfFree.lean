import Formalism.SharpRestriction.LevelLetterCocycles.InvariantLetterIdempotentOfFixed

noncomputable section

open Classical

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.Step2T

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open Formalism.MainNotions.CrystallineLiftingInputs (DL InPN pullJ fMX TCase)
open Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.Step2L

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem basis_induction {R M ι : Type} [CommRing R] [AddCommGroup M] [Module R M] (b : Module.Basis ι R M)
    (P : M → Prop) (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y))
    (hsmul : ∀ (a : R) x, P x → P (a • x)) (hb : ∀ k, P (b k)) : ∀ x, P x := by
  intro x
  have hx : x ∈ Submodule.span R (Set.range b) := by rw [b.span_eq]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨k, rfl⟩ := hy; exact hb k
  | zero => exact h0
  | add y z _ _ hy hz => exact hadd y z hy hz
  | smul a y _ hy => exact hsmul a y hy

variable (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem exists_linear_lift_of_free [NeZero n] [IsDomain O] [IsPrincipalIdealRing O] (hZ : TTool2Z W)
    (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (hp : 11 ≤ PD.p) {M η σ : ℕ} (hTC : TCase PD.p 1 M η σ)
    (hc : IsCrys PD T.ρ) (c : ZMod n) {FF : Type} [AddCommGroup FF] [Module O FF]
    [Module.Free O FF] [Module.Finite O FF] (F₁ : Submodule O FF) (ζL : FF →ₗ[O] W.DD T)
    (hζ : ∀ f, DL W T c (ζL f) ∧ InPN W T 1 (ζL f)) :
    ∃ tL : ↥F₁ →ₗ[O] W.DD T, ∀ f : ↥F₁, tL f ∈ pullJ W T c 1 ∧ DL W T (c + 1) (tL f) ∧
      (∃ p ∈ pullJ W T c 1, ((PD.p : ℕ) : O) ^ σ • W.φD T (ζL f) - (W.γ T (tL f) - tL f) =
        fMX W M η • p) ∧
      ∃ t', IsTrZ W T c 1 M η σ (ζL f) t' ∧ ∃ p ∈ pullJ W T c 1, tL f - t' = fMX W M η • p := by
  obtain ⟨Zex, Zpr, Zlin, -⟩ := hZ hA hp 1 M η σ hTC T hc c
  simp only [pow_one, Nat.cast_one] at Zpr
  let bF := Module.Free.chooseBasis O FF
  obtain ⟨r, b1⟩ := Submodule.basisOfPid bF F₁
  let tch : FF → W.DD T := fun f => Classical.epsilon (fun t => IsTrZ W T c 1 M η σ (ζL f) t)
  have htch : ∀ f, IsTrZ W T c 1 M η σ (ζL f) (tch f) := fun f =>
    Classical.epsilon_spec (Zex _ (hζ f).1 (hζ f).2)
  let tL : ↥F₁ →ₗ[O] W.DD T := b1.constr O (fun k => tch (b1 k : FF))
  refine ⟨tL, ?_⟩

  have hz0 : ∀ t, IsTrZ W T c 1 M η σ 0 t → ∃ p ∈ pullJ W T c 1, t = fMX W M η • p := by
    intro t ht
    have hd0 := invariantLetter_zero W T c
    have hp0 := uniformizerLattice_zero W T (k := 1)
    obtain ⟨p, hp, e⟩ := Zlin 0 0 0 0 t t t hd0 hp0 hd0 hp0 ht ht (by simpa using ht)
    exact ⟨p, hp, by simpa using e⟩
  refine basis_induction b1 _ ?_ ?_ ?_ ?_
  · obtain ⟨t0, ht0⟩ := Zex 0 (invariantLetter_zero W T c) (uniformizerLattice_zero W T 1)
    obtain ⟨p0, hp0, e0⟩ := hz0 t0 (by simpa using ht0)
    refine ⟨by simp, by simpa using invariantLetter_zero W T (c + 1), ⟨0, Submodule.zero_mem _, by simp⟩,
      t0, by simpa using ht0, -p0, Submodule.neg_mem _ hp0, ?_⟩
    simp [e0]
  · rintro x y ⟨hx1, hx2, ⟨px, hpx, ex⟩, tx, htx, qx, hqx, fx⟩ ⟨hy1, hy2, ⟨py, hpy, ey⟩, ty, hty, qy, hqy, fy⟩
    have hsum : ζL (x : FF) + ζL (y : FF) = ζL ((x + y : ↥F₁) : FF) := by
      rw [Submodule.coe_add, map_add]
    obtain ⟨txy, htxy⟩ := Zex (ζL ((x + y : ↥F₁) : FF)) (hζ _).1 (hζ _).2
    obtain ⟨r1, hr1, e1⟩ := Zlin 1 1 _ _ tx ty txy (hζ x).1 (hζ x).2 (hζ y).1 (hζ y).2 htx hty
      (by rw [one_smul, one_smul, hsum]; exact htxy)
    refine ⟨by rw [map_add]; exact Submodule.add_mem _ hx1 hy1,
      by rw [map_add]; exact Formalism.MainNotions.RamifiedCoefficientChains.S9.dl_add W T hx2 hy2,
      ⟨px + py, Submodule.add_mem _ hpx hpy, ?_⟩, txy, htxy, qx + qy - r1,
      Submodule.sub_mem _ (Submodule.add_mem _ hqx hqy) hr1, ?_⟩
    · rw [smul_add, ← ex, ← ey, Submodule.coe_add, map_add ζL, map_add (W.φD T), smul_add,
        map_add tL, map_add (W.γ T)]
      abel
    · rw [smul_sub, smul_add, ← fx, ← fy, ← e1, map_add tL, one_smul, one_smul]
      abel
  · rintro a x ⟨hx1, hx2, ⟨px, hpx, ex⟩, tx, htx, qx, hqx, fx⟩
    have hsm : a • ζL (x : FF) = ζL ((a • x : ↥F₁) : FF) := by
      rw [Submodule.coe_smul, map_smul]
    obtain ⟨tax, htax⟩ := Zex (ζL ((a • x : ↥F₁) : FF)) (hζ _).1 (hζ _).2
    obtain ⟨r1, hr1, e1⟩ := Zlin a 0 _ _ tx tx tax (hζ x).1 (hζ x).2 (hζ x).1 (hζ x).2 htx htx
      (by rw [zero_smul, add_zero, hsm]; exact htax)
    refine ⟨by rw [map_smul]; exact Submodule.smul_of_tower_mem _ a hx1,
      by rw [map_smul]; exact Formalism.MainNotions.RamifiedCoefficientChains.S9.dl_smul W T a hx2,
      ⟨a • px, Submodule.smul_of_tower_mem _ a hpx, ?_⟩, tax, htax, a • qx - r1,
      Submodule.sub_mem _ (Submodule.smul_of_tower_mem _ a hqx) hr1, ?_⟩
    · rw [smul_comm (fMX W M η) a px, ← ex]
      simp only [map_smul, Submodule.coe_smul, smul_sub]
      rw [smul_comm]
    · rw [smul_sub, smul_comm (fMX W M η) a qx, ← fx, ← e1]
      simp only [map_smul, zero_smul, add_zero, smul_sub]
      abel
  · intro k
    have hk : tL (b1 k) = tch (b1 k : FF) := by simp [tL]
    obtain ⟨h1, h2, h3⟩ := Zpr _ _ (hζ _).1 (hζ _).2 (htch (b1 k : FF))
    refine ⟨by rw [hk]; exact h2, by rw [hk]; exact h1, by rw [hk]; exact h3, tch (b1 k : FF),
      htch _, 0, Submodule.zero_mem _, by rw [hk, sub_self, smul_zero]⟩

end Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.Step2T

end
