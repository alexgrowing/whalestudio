import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.NormsFree
import Formalism.LocalToGlobal.ProjectiveLattices.RegPFree
import Formalism.LocalToGlobal.ProjectiveLattices.RegQFree
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.LiftLaSpec
import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapsClosed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSimilitudeOfAutModLevelIdeal
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointBaseChangeUniqueReflIff
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelMoveModuliUniqueUniversalTripleStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueFramedPointMoveUniversalTripleStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointMoveCalculusStatement

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

namespace GlobalTheory.LevelActionLaws

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {D : Datum H}
  {l : Level H}

attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

theorem exists_levAut (hpq : 1 ≤ D.p + D.q) (Xo : Moduli D l) (g : Sim D)
    (hν : (l.A : ℤ) ∣ g.ν l.A - 1) : ∃ ρ : Xo.X ≅ Xo.X, Xo.LevAut g ρ := by
  have hsim := exists_obj_twist_by_similitude SimAlg.sim_group
  have hred : IsReduced Xo.X := by
    haveI := Xo.smooth
    exact (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ Xo.s
      (SmoothOfRelativeDimension.smooth D.dim _)).1
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  obtain ⟨i, hi⟩ := (ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ Xo.univ Xo.univ).1
  obtain ⟨g', hg'⟩ := (SimAlg.sim_group E H D hpq).2.2.2 g
  have hν' : (l.A : ℤ) ∣ g'.ν l.A - 1 := by
    have h₁ := (hg' l.A l.A_pos).2
    have : g'.ν l.A - 1 = (g.ν l.A * g'.ν l.A - 1) - (g.ν l.A - 1) * g'.ν l.A := by ring
    rw [this]
    exact dvd_sub h₁ (hν.mul_right _)
  obtain ⟨o₁, m₁, a₁, b₁⟩ := hsim E H D l _ _ _ _ Xo.univ g hpq hν
  obtain ⟨o₂, m₂, a₂, b₂⟩ := hsim E H D l _ _ _ _ Xo.univ g' hpq hν'
  obtain ⟨f, hf⟩ := Moduli.LevelAction.exists_twists Xo g hred i.toSABMap hi o₁ m₁ a₁ b₁
  obtain ⟨f', hf'⟩ := Moduli.LevelAction.exists_twists Xo g' hred i.toSABMap hi o₂ m₂ a₂ b₂
  exact ⟨⟨f, f', Moduli.LevelAction.comp_eq_id_of_twists Xo hred i hf hf' (fun a => ((hg' _ hM).1 a).2)
      (fun a => ((hg' _ l.A_pos).1 a).2),
    Moduli.LevelAction.comp_eq_id_of_twists Xo hred i hf' hf (fun a => ((hg' _ hM).1 a).1)
      (fun a => ((hg' _ l.A_pos).1 a).1)⟩, hf⟩

theorem eta_congr (Xo : Moduli D l) {a b : D.La} (h : a - b ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La)) :
    Xo.univ.eta a = Xo.univ.eta b := by
  have e : a = (a - b) + b := by abel
  rw [e, Xo.univ.eta_add, Xo.univ.eta_ker _ h, one_mul]

theorem etaA_congr (Xo : Moduli D l) {a b : D.La} (h : D.ModN l.A (a - b)) :
    Xo.univ.etaA a = Xo.univ.etaA b := by
  obtain ⟨x, hx⟩ := h
  have e : a = (a - b) + b := by abel
  rw [e, Xo.univ.etaA_add, hx, Xo.univ.etaA_ker, one_mul]

theorem exists_sim (hpq : 1 ≤ D.p + D.q) (hA : l.A.Coprime l.M) (γ : LaMod D l ≃ₗ[𝓞 E] LaMod D l) :
    ∃ g : Sim D, (∀ a, g.f l.M a - liftLa γ a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La)) ∧
      (∀ a, D.ModN l.A (g.f l.A a - a)) ∧ (l.A : ℤ) ∣ g.ν l.A - 1 := by
  refine GlobalTheory.exists_sim_of_aut_mod E H D l l.A (liftLa γ) hpq l.A_pos hA fun x hx => ?_
  have h := liftLa_spec γ x
  rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).2 hx] at h
  have h2 := γ.map_eq_zero_iff.1 h.symm
  exact (Submodule.Quotient.mk_eq_zero _).1 h2

theorem exists_move (hpq : 1 ≤ D.p + D.q) (hA : l.A.Coprime l.M) (Xo : Moduli D l)
    (γ : LaMod D l ≃ₗ[𝓞 E] LaMod D l) :
    ∃ (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ), IsIso ρ ∧
      IsLevMove ρ ν (liftLa γ) LinearMap.id := by
  obtain ⟨g, h1, h2, h3⟩ := exists_sim hpq hA γ
  obtain ⟨ρ, hs, ν, hM, hAA⟩ := exists_levAut hpq Xo g h3
  refine ⟨ρ.hom, ν, inferInstance, hs, fun a => ?_, fun a => ?_⟩
  · rw [← eta_congr Xo (h1 a)]; exact hM a
  · have e := hAA a
    rw [etaA_congr Xo (h2 a)] at e
    exact e

theorem move_unique (hpq : 1 ≤ D.p + D.q) (hA : l.A.Coprime l.M) (Xo : Moduli D l) (c : Coeff l)
    (γ : LaMod D l ≃ₗ[𝓞 E] LaMod D l) {ρ ρ' : Xo.X ⟶ Xo.X} {ν : SABMap Xo.univ.t Xo.univ.t ρ}
    {ν' : SABMap Xo.univ.t Xo.univ.t ρ'} (i : IsIso ρ) (i' : IsIso ρ')
    (h : IsLevMove ρ ν (liftLa γ) LinearMap.id) (h' : IsLevMove ρ' ν' (liftLa γ) LinearMap.id) :
    ρ = ρ' ∧ ν.φ = ν'.φ :=
  GlobalTheory.T.levelMove_moduli_unique_universalTriple E H D l Xo c ρ ρ' ν ν' _ _ _ _ hpq (fun a => by simp) (fun a => ⟨0, by simp⟩) i i' h h'
    (exists_sim hpq hA γ)

theorem frMove_transfer (hpq : 1 ≤ D.p + D.q) (hA : l.A.Coprime l.M) (Xo : Moduli D l) (c : Coeff l)
    (γ : LaMod D l ≃ₗ[𝓞 E] LaMod D l) {ρ : Xo.X ⟶ Xo.X} {ν : SABMap Xo.univ.t Xo.univ.t ρ} (i : IsIso ρ)
    (h : IsLevMove ρ ν (liftLa γ) LinearMap.id) {S : Type} [CommRing S] [Algebra c.F S] {y y' : FrPt Xo c S}
    (hy : levR (liftLa γ, LinearMap.id) y y') : FrMove ρ ν y y' := by
  obtain ⟨ρ', ν', i', h', hm⟩ := hy
  obtain ⟨rfl, e⟩ := move_unique hpq hA Xo c γ i i' h h'
  obtain ⟨⟨w, hw⟩, hu⟩ := GlobalTheory.T.existsUnique_framedPoint_move_universalTriple E H D l Xo c ρ ν h.1 S y
  rwa [← hu w y' ν' e.symm hw hm]

theorem liftLa_one_sub (a : D.La) :
    liftLa (1 : LaMod D l ≃ₗ[𝓞 E] LaMod D l) a - a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) := by
  rw [← Submodule.Quotient.eq]
  exact liftLa_spec 1 a

theorem liftLa_mul_sub (γ δ : LaMod D l ≃ₗ[𝓞 E] LaMod D l) (a : D.La) :
    liftLa (γ * δ) a - liftLa γ (liftLa δ a) ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) := by
  rw [← Submodule.Quotient.eq]
  have h1 := liftLa_spec (γ * δ) a
  have h2 := liftLa_spec γ (liftLa δ a)
  rw [liftLa_spec δ a] at h2
  exact h1.trans h2.symm

theorem levLaws : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → ∀ l₁ : Level H, l.A.Coprime l.M → LevLaws Xo c l₁ := by
  intro E _ _ _ H Dw l Xo c hpq l₁ hA
  obtain ⟨⟨ι, hι, hone⟩, hmul, hnb⟩ := GlobalTheory.T.framedPointMove_calculus E H Dw l Xo c
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g S _ _ y
    obtain ⟨ρ, ν, i, h⟩ := exists_move hpq hA Xo g.1
    obtain ⟨y', hy'⟩ := (GlobalTheory.T.existsUnique_framedPoint_move_universalTriple E H Dw l Xo c ρ ν h.1 S y).1
    exact ⟨y', ρ, ν, i, h, hy'⟩
  · intro g S _ _ y y' y'' h' h''
    obtain ⟨ρ, ν, i, h, hm⟩ := h'
    have hm' := frMove_transfer hpq hA Xo c g.1 i h h''
    obtain rfl := (GlobalTheory.T.existsUnique_framedPoint_move_universalTriple E H Dw l Xo c ρ ν h.1 S y).2 y' y'' ν rfl hm hm'
    exact (GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c S S (AlgHom.id c.F S) y').2.1
  · intro S _ _ y
    refine ⟨𝟙 _, ι, inferInstance, ⟨Category.id_comp _, fun a => ?_, fun a => ?_⟩, hone S y⟩
    · rw [hι, Category.comp_id, Category.id_comp]
      exact congrArg _ (eta_congr Xo (liftLa_one_sub a))
    · rw [hι, Category.comp_id, Category.id_comp]
      rfl
  · intro g g' S _ _ y y' y'' h h'
    obtain ⟨ρ, ν, i, h, hm⟩ := h
    obtain ⟨ρ', ν', i', h', hm'⟩ := h'
    obtain ⟨μ, hμ, hc⟩ := hmul ρ ρ' ν ν'
    refine ⟨ρ ≫ ρ', μ, inferInstance, ⟨?_, fun a => ?_, fun a => ?_⟩, hc S y y' y'' hm hm'⟩
    · rw [Category.assoc, h'.1, h.1]
    · have e : Xo.univ.eta ((levG (g * g')).1 a) = Xo.univ.eta ((levG g).1 ((levG g').1 a)) :=
        eta_congr Xo (liftLa_mul_sub g.1 g'.1 a)
      rw [e, hμ, ← Category.assoc, h.2.1, Category.assoc, h'.2.1, Category.assoc]
    · have e : (levG (g * g')).2 a = (levG g).2 ((levG g').2 a) := rfl
      rw [e, hμ, ← Category.assoc, h.2.2, Category.assoc, h'.2.2, Category.assoc]
  · intro g S T _ _ _ _ φ y y' z z' hyz hy hz
    obtain ⟨ρ, ν, i, h, hm⟩ := hy
    exact (hnb ρ ν).1 S T φ y y' z z' hyz hm (frMove_transfer hpq hA Xo c g.1 i h hz)
  · intro g S _ _ t y y' z z' hyz hy hz
    obtain ⟨ρ, ν, i, h, hm⟩ := hy
    exact (hnb ρ ν).2 S t y y' z z' hyz hm (frMove_transfer hpq hA Xo c g.1 i h hz)

end GlobalTheory.LevelActionLaws
