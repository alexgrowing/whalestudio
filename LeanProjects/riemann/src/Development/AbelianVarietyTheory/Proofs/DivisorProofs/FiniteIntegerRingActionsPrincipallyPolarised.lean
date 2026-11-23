import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaPointDeterminesAndEndDeterminedTorsion
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsStarNormLEOfIsCMField
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.FiniteFibrePoints
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin.FinAct

theorem finite_oActs : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K]
    [IsAlgClosed K] [CharZero K] (P : PolAV (Sp K)), letI := H.starRing;
    Set.Finite {act : 𝓞 E → (P.A ⟶ P.A) | ∃ ρ : P.OAct (𝓞 E), ∀ a, ρ.act a = act a} := by
  intro E _ _ _ H K _ _ _ P
  letI := H.starRing
  have h₂ := GlobalTheory.thetaPtDetermines_and_endDeterminedOnTorsion.2
  choose cn hcn using GlobalTheory.exists_starNormLE_of_isCMField E (fun a => H.bar_eq a)
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℤ (𝓞 E)).FG)
  set g := P.g
  set M := 4 ^ g * g.factorial * (2 * s.sup cn) + 1 with hM
  have hM1 : 1 ≤ M := Nat.le_add_left _ _
  have key : ∀ c, c ≤ s.sup cn → 4 ^ g * g.factorial * (2 * c) < M ^ 2 := fun c hc =>
    calc 4 ^ g * g.factorial * (2 * c) ≤ 4 ^ g * g.factorial * (2 * s.sup cn) := by gcongr
      _ < M := Nat.lt_succ_self _
      _ ≤ M ^ 2 := Nat.le_self_pow two_ne_zero _
  have hK : (M : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  let T := {x : baseOver (Sp K) ⟶ P.A // x ^ M = 1}
  haveI : Finite T := GlobalTheory.AbTorsionFinite.finite_torsion K P.A P.isAb M hM1
  classical
  let F : (𝓞 E → (P.A ⟶ P.A)) → (s → T → Option T) := fun act a x =>
    if h : (x.1 ≫ act a) ^ M = 1 then some ⟨_, h⟩ else none
  refine Set.Finite.of_finite_image (f := F) (Set.toFinite _) ?_
  rintro act₁ ⟨ρ₁, h₁⟩ act₂ ⟨ρ₂, h₂'⟩ hF
  have tor : ∀ (ρ : P.OAct (𝓞 E)) (a : 𝓞 E) (x : T), (x.1 ≫ ρ.act a) ^ M = 1 := fun ρ a x => by
    have := ρ.hom a
    have e := map_pow (IsMonHom.monoidHom (ρ.act a) (baseOver (Sp K))) x.1 M
    rw [x.2, map_one] at e
    exact e.symm
  have onS : ∀ a ∈ s, ρ₁.act a = ρ₂.act a := fun a ha => by
    have := h₂ g (cn a) M (key _ (Finset.le_sup ha)) K hK P P rfl rfl (Iso.refl _)
      (ThetaPtDet.isPolIso_refl P) (𝓞 E) ρ₁ ρ₂ a (hcn a) fun y hy => by
        have e := congrFun (congrFun hF ⟨a, ha⟩) ⟨y, hy⟩
        simp only [F, h₁, h₂'] at e
        rw [dif_pos (h₁ a ▸ tor ρ₁ a ⟨y, hy⟩), dif_pos (h₂' a ▸ tor ρ₂ a ⟨y, hy⟩)] at e
        have e' := congrArg Subtype.val (Option.some_injective _ e)
        simp only [Iso.refl_hom, Category.comp_id, Category.id_comp, h₁, h₂']
        exact e'
    simpa only [Iso.refl_hom, Category.comp_id, Category.id_comp] using this
  have add₁ : ∀ a b, ρ₁.act (a + b) = ρ₁.act a * ρ₁.act b := ρ₁.map_add
  have add₂ : ∀ a b, ρ₂.act (a + b) = ρ₂.act a * ρ₂.act b := ρ₂.map_add
  let f₁ : 𝓞 E →+ Additive (P.A ⟶ P.A) := AddMonoidHom.mk' (fun a => Additive.ofMul (ρ₁.act a))
    fun a b => by rw [add₁]; rfl
  let f₂ : 𝓞 E →+ Additive (P.A ⟶ P.A) := AddMonoidHom.mk' (fun a => Additive.ofMul (ρ₂.act a))
    fun a b => by rw [add₂]; rfl
  have hf : f₁ = f₂ := AddMonoidHom.eq_of_eqOn_dense (s := (s : Set (𝓞 E)))
    (by rw [← Submodule.span_int_eq_addSubgroupClosure, hs]; rfl) fun a ha =>
      congrArg Additive.ofMul (onS a ha)
  funext a
  rw [← h₁, ← h₂']
  exact Additive.ofMul.injective (DFunLike.congr_fun hf a)

end GlobalTheory.UMin.FinAct
