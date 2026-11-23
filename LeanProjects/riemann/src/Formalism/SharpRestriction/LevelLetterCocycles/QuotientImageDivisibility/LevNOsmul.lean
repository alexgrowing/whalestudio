import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.MemOfExp
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.PchainDN
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.NDlCoords

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries Formalism.MainNotions.N.Pv.LocalLengthBound.Ser TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

section Fam

variable (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem levN_osmul (c : ZMod n) (ζ : LL) (o : O) (x : ↥(W.N T)) :
    W.levN T c ζ (o • x) = algebraMap O LL o • W.levN T c ζ x := by
  obtain ⟨m, hm⟩ := W.levN_supp T c ζ x
  have e : (o • x : ↥(W.N T)) = (algebraMap O (LetA O n) o) • x := by
    ext; simp [algebraMap_smul]
  rw [e]
  have := funext fun k => W.levN_smul T c ζ (algebraMap O (LetA O n) o) x k
  rw [this]
  change smulS _ _ = _
  have hC : (algebraMap O (PowerSeries LL) o) = PowerSeries.C (algebraMap O LL o) := by
    first
    | exact PowerSeries.algebraMap_apply' o
    | exact PowerSeries.algebraMap_apply o
    | simp [PowerSeries.algebraMap_apply']
    | simp [PowerSeries.algebraMap_apply]
  rw [AlgHom.commutes, hC, smulS_C hm]

theorem fam_exp [IsDomain O] {A : Type} [AddCommGroup A] [Module O A] (hs : W.s = 1)
    (c : ZMod n) (ζ₀ : LL)
    (hLv : ∀ (x : ↥(W.N T)) (k : ℤ), W.levN T c ζ₀ x k ∈ Formalism.MainNotions.WachCoordinates.FilLev W T c 0 (-k))
    (χ : LL) (hχ0 : χ ≠ 0) (hχ : ∀ i : ℤ, i ≠ 0 → χ ^ i ≠ 1)
    (hγN : ∀ (x : W.DD T) (hx : x ∈ W.N T) (hγx : W.γ T x ∈ W.N T) (k : ℤ),
      W.levN T c ζ₀ ⟨W.γ T x, hγx⟩ k = χ ^ k • W.levN T c ζ₀ ⟨x, hx⟩ k)
    (hγA : ∀ f : LetA O n, W.lev c ζ₀ (W.γA W.gam f) = PowerSeries.rescale χ (W.lev c ζ₀ f))
    (u₀ : PowerSeries LL) (hu₀ : W.lev c ζ₀ W.q = X * u₀) (hu0 : constantCoeff u₀ ≠ 0)
    (K : ℕ) (w : A →ₗ[O] W.DD T) (hK : ∀ f, W.Q ^ K • w f ∈ W.N T)
    (hγw : ∀ f, W.γ T (w f) - w f ∈ W.N T) :
    ∃ dd : A → ℤ → T.V ⊗[Qp] BdR, (∀ f, ∃ m, LB m (dd f)) ∧
      (∀ f, W.levN T c ζ₀ ⟨W.Q ^ K • w f, hK f⟩ = smulS ((X * u₀) ^ K) (dd f)) ∧
      (∀ f (i : ℤ), i ≠ 0 → dd f i ∈ Formalism.MainNotions.WachCoordinates.FilLev W T c 0 (-i)) ∧
      (∀ f g, dd (f + g) = dd f + dd g) ∧ (∀ (o : O) f, dd (o • f) = algebraMap O LL o • dd f) := by
  have ex : ∀ f, ∃ d : ℤ → T.V ⊗[Qp] BdR, (∃ m, LB m d) ∧
      W.levN T c ζ₀ ⟨W.Q ^ K • w f, hK f⟩ = smulS ((X * u₀) ^ K) d ∧
      ∀ i : ℤ, (χ ^ i - 1) • d i ∈ Formalism.MainNotions.WachCoordinates.FilLev W T c 0 (-i) :=
    fun f => gamma_levels_expansion W T hs c ζ₀ hLv χ hχ0 hγN hγA u₀ hu₀ hu0 (hK f) (hγw f)
  choose dd hdLB hde hdγ using ex
  have hanti := Formalism.MainNotions.UnusedSlot80.LevR.filLev_anti W T c 0
  refine ⟨dd, hdLB, hde, fun f i hi => ?_, fun f g => ?_, fun o f => ?_⟩
  · have h := Formalism.KernelCokernelLengths.exists_fixed_add_of_sub_mem LL (T.V ⊗[Qp] BdR) (fun a => Formalism.MainNotions.WachCoordinates.FilLev W T c 0 a)
      hanti χ hχ 0 0 (dd f) (fun j h1 h2 => by omega) (hdγ f)
    exact h.1 i hi
  · obtain ⟨m1, h1⟩ := hdLB (f + g)
    obtain ⟨m2, h2⟩ := hdLB f
    obtain ⟨m3, h3⟩ := hdLB g
    have e1 : (⟨W.Q ^ K • w (f + g), hK (f + g)⟩ : ↥(W.N T)) =
        ⟨W.Q ^ K • w f, hK f⟩ + ⟨W.Q ^ K • w g, hK g⟩ := Subtype.ext (by simp [smul_add])
    have e2 := hde (f + g)
    rw [e1, map_add, hde f, hde g, ← smulS_add (LB_mono h2 (min_le_left m2 m3))
      (LB_mono h3 (min_le_right m2 m3))] at e2
    exact div_unique (m := min m1 (min m2 m3)) (LB_mono h1 (min_le_left _ _))
      (LB_mono (LB_add (LB_mono h2 (min_le_left m2 m3)) (LB_mono h3 (min_le_right m2 m3)))
        (min_le_right _ _)) u₀ hu0 K e2.symm
  · obtain ⟨m1, h1⟩ := hdLB (o • f)
    obtain ⟨m2, h2⟩ := hdLB f
    have e1 : (⟨W.Q ^ K • w (o • f), hK (o • f)⟩ : ↥(W.N T)) = o • ⟨W.Q ^ K • w f, hK f⟩ :=
      Subtype.ext (by simp [osmul_comm W T])
    have e2 := hde (o • f)
    rw [e1, levN_osmul W T c ζ₀ o, hde f, ← smulS_smul h2] at e2
    exact div_unique (m := min m1 m2) (LB_mono h1 (min_le_left _ _))
      (LB_mono (LB_smul h2 _) (min_le_right _ _)) u₀ hu0 K e2.symm

end Fam

end Formalism.MainNotions.N.Pv.LocalLengthBound
