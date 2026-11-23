import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAdmissibleAffineModelDividingTuple
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsBundleOnAdmissibleModel
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.BaseFactsOfIsEE
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsThetaSystemGenusOneStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyAbelianSchemeProjectiveClosure
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyClosureExtensionAbelianScheme
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGeometricTestMapClassicalPoint
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH.ClosureExample

theorem exists_adm (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) :
    ∃ (M : RatModel o Ω) (U₀ : M.Z.Opens), S.admitted M U₀ := by
  obtain ⟨s, hs⟩ := S.fg
  obtain ⟨x₀, hx₀⟩ := S.th_ne
  let t₀ : Option s → Ω := fun j => j.elim 1 Subtype.val
  have htop : Subfield.closure (Set.range (algebraMap o Ω) ∪
      {x | ∃ i j : S.Gam × Option s, x = S.th j.1 * t₀ j.2 / (S.th i.1 * t₀ i.2)}) = ⊤ := by
    set F := Subfield.closure (Set.range (algebraMap o Ω) ∪
      {x | ∃ i j : S.Gam × Option s, x = S.th j.1 * t₀ j.2 / (S.th i.1 * t₀ i.2)}) with hF
    have hR : ∀ a ∈ S.R, a ∈ F := by
      intro a ha
      rw [← hs] at ha
      induction ha using Algebra.adjoin_induction with
      | mem x hx =>
        refine Subfield.subset_closure (Or.inr ⟨(x₀, none), (x₀, some ⟨x, hx⟩), ?_⟩)
        simp only [t₀, Option.elim]
        field_simp
      | algebraMap r => exact Subfield.subset_closure (Or.inl ⟨r, rfl⟩)
      | add x y _ _ hx hy => exact add_mem hx hy
      | mul x y _ _ hx hy => exact mul_mem hx hy
    refine top_unique fun x _ => ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := S.frac x
    exact div_mem (hR a ha) (hR b hb)
  obtain ⟨M, U₀, h, -⟩ := GlobalTheory.ZH.exists_admissible_affine_model_dividing_tuple o Ω S (Option s) t₀ ⟨none, one_ne_zero⟩ (by
    rw [htop]
    exact Module.Finite.of_surjective (Algebra.linearMap (⊤ : Subfield Ω) Ω) fun x => ⟨⟨x, trivial⟩, rfl⟩)
  exact ⟨M, U₀, h⟩

theorem exists_clos_ext_tMap : GlobalTheory.UT.LL → ∃ (o Ω : Type) (_ : CommRing o) (_ : Field Ω) (_ : Algebra o Ω) (_ : ArithBase o Ω) (S : ThetaSys o Ω) (ρ : S.Real), S.g = 1 ∧ S.Big ∧ (S.HasTests → ρ.HasGeo → ∃ (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE ∧ ∃ Q : Clos ρ M U₀ EE, Nonempty Q.Ext ∧ ∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (t : ρ.GeoTest p y₀) (c : Q.Fac y t.u), Nonempty (Q.TMap t c)) := by
  intro hL
  obtain ⟨o, Ω, _, _, _, _, S, hg, hbig, ⟨ρ⟩⟩ := GlobalTheory.T.exists_theta_system_genus_one hL.1 hL.2.1
  refine ⟨o, Ω, _, _, _, ‹_›, S, ρ, hg, hbig, fun hT hG => ?_⟩
  obtain ⟨M, U₀, hA⟩ := exists_adm o Ω S
  obtain ⟨EE, hE, -⟩ := GlobalTheory.ZH.exists_isEE_of_adm o Ω S M U₀ hT hA
  have hB := GlobalTheory.ZH.baseFacts_of_isEE o Ω S M U₀ EE hT hA.1 hE
  obtain ⟨Q⟩ := GlobalTheory.ZH.nonempty_clos hL o Ω S ρ M U₀ EE hB
  obtain ⟨h1, h2⟩ := GlobalTheory.ZH.exists_geoTest_tMap_and_centre hL o Ω S ρ M U₀ EE hB Q hbig hG
  have := hB.jac
  obtain ⟨z, -, hz⟩ := nonempty_inter_closedPoints (X := M.Z) (Z := Set.univ) ⟨genericPoint M.Z, trivial⟩
    isClosed_univ.isLocallyClosed
  obtain ⟨p, hp, y, hy⟩ := h2 z hz
  obtain ⟨y₀, t, c, hc⟩ := h1 p y hy.2
  exact ⟨M, U₀, EE, hB, Q, GlobalTheory.ZH.ClosureLifting.nonempty_ext hL o Ω S ρ M U₀ EE hB Q, p, hp, y, y₀, t, c, hc⟩

end GlobalTheory.ZH.ClosureExample
