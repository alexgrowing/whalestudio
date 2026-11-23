import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EpsZeroCompOfIsTanAtG
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsCommonModOfIsDiag

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.LocM.MapComp
open GlobalTheory.LocM.CommonMod

namespace GlobalTheory.LocM.StepMono

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem inStep_comp {Z' Z B : Mdl Y i₀} {f : Z'.X ⟶ Z.X} {g : Z.X ⟶ B.X} (hf : IsMap Z' Z f) (hg : IsMap Z B g)
    {σ : E →+* ℂ} {r : ℕ} {k : Type} [Field k] {w : Sp k ⟶ Z'.X} {v : Sp (DualNumber k) ⟶ B.t.G.left}
    (h : InStep Z' B σ r w v) : InStep Z B σ r (w ≫ f) v := by
  obtain ⟨τ, mu, u, i, t, fu, hi, hv⟩ := h
  obtain ⟨τ₁, mu₁, u₁, t₁, e₁, fu₁, fu₁'⟩ := hf.2 k w (range_subset_opn Z' fu)
  have f₂ := flagAt_push hf.1.2.2 mu₁ e₁ fu₁ fu fu₁'
  obtain ⟨τ₂, mu₂, -, t₂, -⟩ := hg.2 k (w ≫ f) (range_subset_opn Z f₂)
  obtain ⟨mu', hmu'⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ mu₂ mu₁
  have t' := isTrans_comp hg.1.1 hf.1.1 t₂ t₁ mu' hmu'
  obtain ⟨-, hmu⟩ := TransUniq.trans_unique E H Dw Xo p W Y _ _ _ _ mu mu' (hg.1.2.1.trans hf.1.2.1) t t'
  obtain ⟨a, φ, ha, gu, -⟩ := fu
  obtain ⟨y, hy, -⟩ := exists_lift_chart Z' ha
  refine ⟨τ₂, mu₂, _, i, t₂, f₂, hi, hv.trans ?_⟩
  rw [hmu k y _ _ _ (by rw [hy]; exact (gu.1 σ i).1.1), hmu', Category.assoc]

theorem tanEv_congr {X : Scheme.{0}} (t : SAB H X) {k : Type} [CommRing k] {x x' : Sp k ⟶ X} (e : x = x')
    {v : Sp (DualNumber k) ⟶ t.G.left} (hv : IsTanAtG t x v) {V : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ V) :
    ∃ (hv' : IsTanAtG t x' v) (h' : ⊤ ≤ x' ⁻¹ᵁ V), ∀ s, tanEv t hv h s = tanEv t hv' h' s := by
  subst e
  exact ⟨hv, h, fun _ => rfl⟩

theorem map_entry {R S T : Type} [CommRing R] [CommRing S] [CommRing T] {n : ℕ} (ψ : R →+* S) (φ : S →+* T)
    (a : GL (Fin n) R) (j l : Fin n) : φ (Matrix.GeneralLinearGroup.map ψ a j l) = φ.comp ψ (a j l) := rfl

theorem holds_of_isMap (t : Step Y i₀) {Z Z' : Mdl Y i₀} {f : Z'.X ⟶ Z.X} (hf : IsMap Z' Z f) (h : t.Holds Z) :
    t.Holds Z' := by
  obtain ⟨hk, g, hg, H₀⟩ := h
  refine ⟨hf.1.2.2 _ hk, f ≫ g, isMap_comp hf hg, fun x => ?_⟩
  obtain ⟨U, hU, V, n, m, a, hx, hUV, hm, H₁⟩ := H₀ (f x)
  obtain ⟨_, ⟨U', hU', rfl⟩, hx', hle⟩ := Z'.X.isBasis_affineOpens.exists_subset_of_mem_open
    (show x ∈ ((f ⁻¹ᵁ U : Z'.X.Opens) : Set Z'.X) from hx) (f ⁻¹ᵁ U).2
  have e : U' ≤ f ⁻¹ᵁ U := hle
  refine ⟨U', hU', V, n, m, Matrix.GeneralLinearGroup.map (f.appLE U U' e).hom a, hx',
    e.trans (f.preimage_mono hUV), hm, fun k _ φ v hv hh hs j hj => ?_⟩
  have ep : (spMap φ ≫ hU'.fromSpec) ≫ f = spMap (φ.comp (f.appLE U U' e).hom) ≫ hU.fromSpec := by
    rw [← sp_comp, Category.assoc, Category.assoc]
    exact congrArg (spMap φ ≫ ·) (IsAffineOpen.SpecMap_appLE_fromSpec f hU hU' e).symm
  have eq : (spMap φ ≫ hU'.fromSpec) ≫ f ≫ g = (spMap (φ.comp (f.appLE U U' e).hom) ≫ hU.fromSpec) ≫ g := by
    rw [← ep]
    simp only [Category.assoc]
  have hs' := inStep_comp hf hg hs
  rw [ep] at hs'
  obtain ⟨hv', hh', he⟩ := tanEv_congr t.B.t eq hv hh
  exact (Finset.sum_congr rfl fun l _ => congrArg₂ (· * ·) (map_entry _ φ a j l) (he _)).trans
    (H₁ k _ v hv' hh' hs' j hj)

theorem holds_mono : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p), ∀ (t : Step Y i₀) (Z Z' : Mdl Y i₀), (∃ f, IsMap Z' Z f) → t.Holds Z → t.Holds Z' :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ t _ _ ⟨_, hf⟩ h => holds_of_isMap t hf h

end GlobalTheory.LocM.StepMono
