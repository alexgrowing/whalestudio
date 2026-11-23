import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatLineGenerator
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CardComapMulFinsumEqFinsumFibres
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AddJFintype
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericCoordsDescendSubfield
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapStalkMap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagStep

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagStep

theorem mem_of_mem_iSup_of_indep {Ω W I : Type} [Field Ω] [AddCommGroup W] [Module Ω W] (A : Subring Ω)
    {F : I → Submodule Ω W} (hF : iSupIndep F) {P : I → Submodule A W}
    (hP : ∀ t, P t ≤ (F t).restrictScalars A) (s : I) {x : W} (hx : x ∈ ⨆ t, P t) (hxs : x ∈ F s) : x ∈ P s := by
  classical
  have hsplit : (⨆ t, P t) ≤ P s ⊔ ⨆ (t) (_ : t ≠ s), P t := iSup_le fun t => by
    by_cases e : t = s
    · subst e
      exact le_sup_left
    · exact le_sup_of_le_right (le_iSup₂_of_le t e le_rfl)
  obtain ⟨a, ha, d, hd, rfl⟩ := Submodule.mem_sup.1 (hsplit hx)
  have hd2 : d ∈ ⨆ (t) (_ : t ≠ s), F t := by
    have hle : (⨆ (t) (_ : t ≠ s), P t) ≤ (⨆ (t) (_ : t ≠ s), F t).restrictScalars A :=
      iSup₂_le fun t e v hv => (le_iSup₂_of_le t e le_rfl : F t ≤ ⨆ (t) (_ : t ≠ s), F t) (hP t hv)
    exact hle hd
  have hd3 : d ∈ F s := by
    have h := sub_mem hxs (show a ∈ F s from hP s ha)
    simpa using h
  have h0 : d = 0 := Submodule.disjoint_def.1 (hF s) d hd3 hd2
  rw [h0, add_zero]
  exact ha

theorem eigLat_isFlagVBOn_of_pull_char0 : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Tor.Level H) (c : Coeff l)
    (X X' : Scheme.{0}) (t : SAB H X) (t' : SAB H X') (f : X' ⟶ X) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [CharZero Ω₀]
    [CharZero Ω] [Algebra Ω₀ Ω] (ξ : Spec (CommRingCat.of Ω₀) ⟶ X) (ξ' : Spec (CommRingCat.of Ω) ⟶ X')
    (cst : c.F →+* Ω₀) (V V' : Type) [AddCommGroup V] [Module Ω₀ V] [AddCommGroup V'] [Module Ω V']
    (M : LieModel t.G ξ V) (M' : LieModel t'.G ξ' V') (ρ : 𝓞 E →+* Module.End Ω₀ V) (ρ' : 𝓞 E →+* Module.End Ω V')
    (L : CMType H ⊕ CMType H → Lat ξ V) (j : V →+ V') (r : CMType H ⊕ CMType H → ℕ)
    (b : ∀ s, Fin (r s) → V'),
    IsCptGen ξ → IsCptGen ξ' → GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f (algebraMap Ω₀ Ω) →
    M.IsActOf t.act.act ρ → M'.IsActOf t'.act.act ρ' →
    (∀ q : Cpt ξ, (∀ r : ℕ, r.Prime → ¬ InFibre ξ r q) → IsIntegrallyClosed (regAt ξ q)) →
    (∀ q : Cpt ξ', (∀ r : ℕ, r.Prime → ¬ InFibre ξ' r q) → IsIntegrallyClosed (regAt ξ' q)) →
    (∀ s (q : Cpt ξ), (∀ r : ℕ, r.Prime → ¬ InFibre ξ r q) → L s q = M.eigLat ρ (cst.comp (labelEmb c s)) q) →
    M'.lat = M.lat.pull ξ' f j →
    (∀ s, ∀ e ∈ eigSp ρ (cst.comp (labelEmb c s)),
      j e ∈ eigSp ρ' (((algebraMap Ω₀ Ω).comp cst).comp (labelEmb c s))) →
    (∀ s, ((L s).pull ξ' f j).IsFlagVBOn Set.univ (b s)) →
    ∀ s, (M'.eigLat ρ' (((algebraMap Ω₀ Ω).comp cst).comp (labelEmb c s))).IsFlagVBOn
      {q | ∀ r : ℕ, r.Prime → ¬ InFibre ξ' r q} (b s) := by
  intro E _ _ _ H l c X X' t t' f Ω₀ Ω _ _ _ _ _ ξ ξ' cst V V' _ _ _ _ M M' ρ ρ' L j r b hg hg' hd hact hact' hint hint'
    hL hlat hj hfl
  have key : ∀ s (q : Cpt ξ'), (∀ r : ℕ, r.Prime → ¬ InFibre ξ' r q) →
      (M'.eigLat ρ' (((algebraMap Ω₀ Ω).comp cst).comp (labelEmb c s))) q = ((L s).pull ξ' f j) q := by
    intro s q hq
    obtain ⟨h, -, h2⟩ := RegAtDom.regAt_dominates X Ω₀ ξ X' Ω ξ' f (algebraMap Ω₀ Ω) hd q
    have hp : ∀ r : ℕ, r.Prime → ¬ InFibre ξ r ⟨f q.1, h⟩ := fun r hr hn =>
      hn (h2 hg' _ (natCast_mem _ r) (by rw [map_natCast]; exact not_not.1 (hq r hr)))
    have hsum := (SatModel.lat_eq_iSup_of_char0 c t ξ hg cst M ρ hact hint).2 _ hp
    have hind := (SatModel.lat_eq_iSup_of_char0 c t' ξ' hg' ((algebraMap Ω₀ Ω).comp cst) M' ρ' hact' hint').1
    have hle : ∀ u, ((L u).pull ξ' f j) q ≤ M'.lat q ⊓
        (eigSp ρ' (((algebraMap Ω₀ Ω).comp cst).comp (labelEmb c u))).restrictScalars (regAt ξ' q) := by
      intro u
      refine Submodule.span_le.2 ?_
      rintro _ ⟨h', e, he, rfl⟩
      have he' : e ∈ M.lat.inter (eigSp ρ (cst.comp (labelEmb c u))) ⟨f q.1, h⟩ := by
        have h3 := hL u ⟨f q.1, h⟩ hp
        have h4 : e ∈ L u ⟨f q.1, h⟩ := he
        rw [h3] at h4
        exact h4
      refine ⟨?_, hj u e he'.2⟩
      show j e ∈ M'.lat q
      rw [hlat]
      exact Submodule.subset_span ⟨h, e, he'.1, rfl⟩
    have hall : M'.lat q ≤ ⨆ u, ((L u).pull ξ' f j) q := by
      rw [hlat]
      refine Submodule.span_le.2 ?_
      rintro _ ⟨h', e, he, rfl⟩
      have he1 : e ∈ ⨆ u, M.lat.inter (eigSp ρ (cst.comp (labelEmb c u))) ⟨f q.1, h⟩ := by
        rw [← hsum]
        exact he
      refine Submodule.iSup_induction _ (motive := fun e => j e ∈ ⨆ u, ((L u).pull ξ' f j) q) he1
        (fun u e he => ?_) ?_ (fun x y hx hy => ?_)
      · refine Submodule.mem_iSup_of_mem u (Submodule.subset_span ⟨h, e, ?_, rfl⟩)
        have h3 := hL u ⟨f q.1, h⟩ hp
        rw [h3]
        exact he
      · simp only [map_zero]
        exact zero_mem _
      · simp only [map_add]
        exact add_mem hx hy
    refine le_antisymm ?_ (hle s)
    rintro x ⟨hx1, hx2⟩
    exact mem_of_mem_iSup_of_indep (regAt ξ' q) hind (fun u => (hle u).trans inf_le_right) s (hall hx1) hx2
  intro s p hp
  obtain ⟨U, hU, b', hb, hf⟩ := hfl s p trivial
  refine ⟨U, hU, b', hb, fun q hq hqU => ?_⟩
  obtain ⟨h1, h2⟩ := hf q trivial hqU
  exact ⟨h1, (key s q hq).trans h2⟩

end GlobalTheory.CompanionTheory.Ar.FlagStep
