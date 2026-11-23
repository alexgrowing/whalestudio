import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.FamUnif
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointHol
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodClassInjectiveOfRichChartsStatement

set_option autoImplicit false

noncomputable section

open TopologicalSpace Filter Topology
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.AnPer.MaxCharts

variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ}
  {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V}

def Alg (u : Unif F s σ) (W : Opens (Tot I g)) : Prop :=
  ∃ x : Sp (Hol W) ⟶ X, (∀ h : ∀ p ∈ W, p.1 ∈ F.V,
      x ≫ s = spMap ((Hol.comap Prod.fst (fun _ _ ↦ analyticAt_fst) h).toRingHom.comp σ)) ∧
    ∀ (p : Tot I g) (hp : p ∈ W), spMap (Hol.ev p hp).toRingHom ≫ x = u.E p

theorem alg_of_ev (u : Unif F s σ) (W : Opens (Tot I g)) (x : Sp (Hol W) ⟶ X)
    (hx : ∀ (p : Tot I g) (hp : p ∈ W), spMap (Hol.ev p hp).toRingHom ≫ x = u.E p) : Alg u W := by
  refine ⟨x, fun h ↦ ?_, hx⟩
  refine point_hol_ext _ W (Sp B) (⊤_ Scheme.{0}) (terminal.from _) _ _ (terminal.hom_ext _ _) fun p hp ↦ ?_
  have e := hx p hp
  change spMap (Hol.ev p hp).toRingHom ≫ _ = spMap (Hol.ev p hp).toRingHom ≫ _
  rw [← Category.assoc, e, u.w p (h p hp), ← Cris.spMap_comp]
  rfl

theorem alg_mono (u : Unif F s σ) {W W' : Opens (Tot I g)} (h : W' ≤ W) (a : Alg u W) : Alg u W' := by
  obtain ⟨x, -, hx⟩ := a
  refine alg_of_ev u W' (spMap (Hol.comap id analyticOnNhd_id (fun p hp ↦ h hp)).toRingHom ≫ x) fun p hp ↦ ?_
  rw [← Category.assoc, ← Cris.spMap_comp, ← hx p (h hp)]
  rfl

@[reducible] def charts (u : Unif F s σ) : Charts F := Charts.std F (Alg u)

def real [IsSeparated s] (u : Unif F s σ) : Real (charts u) s σ where
  x k := k.2.2.choose
  w k := k.2.2.choose_spec.1 k.2.1
  compat {l k k'} h := by
    refine point_hol_ext _ k'.1 X _ s _ _ ?_ fun p hp ↦ ?_
    · rw [Category.assoc, k.2.2.choose_spec.1 k.2.1, k'.2.2.choose_spec.1 k'.2.1, ← Cris.spMap_comp]
      exact congrArg spMap (RingHom.ext fun b ↦ Charts.sh_cst (K := charts u) h (σ b))
    · change spMap (Hol.ev p hp).toRingHom ≫ _ = spMap (Hol.ev p hp).toRingHom ≫ _
      rw [k'.2.2.choose_spec.2 p hp, ← Category.assoc, ← Cris.spMap_comp, ← u.per l p (k'.2.1 p hp),
        ← k.2.2.choose_spec.2 _ (h p hp)]
      rfl

theorem isFor [IsSeparated s] (u : Unif F s σ) : (real u).IsFor u := fun k ↦ k.2.2.choose_spec.2

theorem rich (u : Unif F s σ) : (charts u).Rich := by
  constructor
  · intro p hp
    obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := u.E p (default : PrimeSpectrum ℂ))
      (U := ⊤) trivial
    let W : Opens (Tot I g) := ⟨{q | q.1 ∈ F.V ∧ ⊤ ≤ u.E q ⁻¹ᵁ U}, (u.hol U 0).1⟩
    have hol : IsHolTo (W : Set (Tot I g)) u.E := fun U' f ↦ ⟨by
      have e : {q | q ∈ (W : Set (Tot I g)) ∧ ⊤ ≤ u.E q ⁻¹ᵁ U'} =
          (W : Set (Tot I g)) ∩ {q | q.1 ∈ F.V ∧ ⊤ ≤ u.E q ⁻¹ᵁ U'} :=
        Set.ext fun q ↦ ⟨fun h ↦ ⟨h.1, h.1.1, h.2⟩, fun h ↦ ⟨h.1, h.2.2⟩⟩
      exact e ▸ W.isOpen.inter (u.hol U' f).1,
      (u.hol U' f).2.mono fun q h ↦ ⟨h.1.1, h.2⟩⟩
    obtain ⟨x, -, hx⟩ := exists_point_hol _ W X u.E U hU hol fun q hq ↦ hq.2
    refine ⟨⟨W, fun q hq ↦ hq.1, alg_of_ev u W x hx⟩, hp, fun y _ ↦ ?_⟩
    obtain rfl : y = (default : PrimeSpectrum ℂ) := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
    exact hpU
  · intro l k₁ k₂ p h₁ h₂
    have ho : IsOpen ((k₁.1 : Set (Tot I g)) ∩ F.shift l ⁻¹' (k₂.1 : Set (Tot I g))) :=
      (F.shift_analytic l k₁.2.1).continuousOn.isOpen_inter_preimage k₁.1.isOpen k₂.1.isOpen
    refine ⟨⟨⟨_, ho⟩, fun q hq ↦ k₁.2.1 q hq.1, alg_mono u (fun q hq ↦ hq.1) k₁.2.2⟩, ⟨h₁, h₂⟩,
      fun q hq ↦ ?_, fun q hq ↦ hq.2⟩
    rw [F.shift_zero]
    exact hq.1

end GlobalTheory.AnPer.MaxCharts

namespace GlobalTheory.AnPer

theorem period_unique : PUniq := by
  intro I _ g Λ _ F B _ X s _ σ u c per per' h h'
  exact GlobalTheory.T.periodClass_injective_of_rich_charts (MaxCharts.charts u) (MaxCharts.rich u) per per'
    ((h _ _ (MaxCharts.isFor u)).symm.trans (h' _ _ (MaxCharts.isFor u)))

end GlobalTheory.AnPer
