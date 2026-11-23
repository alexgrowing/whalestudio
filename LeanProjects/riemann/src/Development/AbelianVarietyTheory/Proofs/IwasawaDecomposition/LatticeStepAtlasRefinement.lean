import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompGvec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeStepHoldsPullbackStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarrierMatrixTransferStatement

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)

namespace GlobalTheory.GrCl

theorem locMaps_of_grel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (t : Step Y i₀) (Z : Mdl Y i₀) (g : Z.X ⟶ t.B.X) (D : LCrd (Y Z.i) Z.π), IsMap Z t.B g → IsLat t Z g D → ∀ (A : Atlas (Y Z.i) Z.π Z.ty) (X' : Scheme.{0}) (f : X' ⟶ Z.X) (q : X' ⟶ PSpace (Z.i.c.V W) (plN D.N t.k)) (ty' : (E →+* ℂ) → Finset ℕ) (A' : Atlas (Y Z.i) (f ≫ Z.π) ty'), (∀ (K : Type) [Field K] (w : Sp K ⟶ Z.X) (u : Vecs Dw (Y Z.i).t K), A.FlagAt w u ↔ Z.FlagAt w u) → GRel D A t.σ t.le f q A' → q ≫ PSpace.str _ _ = f ≫ Z.π ≫ (Y Z.i).s → Lifts (Z.π ≫ (Y Z.i).s) f q → ∀ (Z₁ : Mdl Y i₀) (g₀ : Z₁.X ⟶ Z.X), IsMap Z₁ Z g₀ → t.Holds Z₁ → LocMaps Z₁ A' := by
  intro E _ _ _ H Dw Xo p W Y i₀ hp hpW t Z g D hg hL A X' f q ty' A' hA hR hq hLift Z₁ g₀ hg₀ hH K _ w hw
  obtain ⟨τ, mu, u, hT, hπ, hZ₁, hZ⟩ := ((isMap_iff _ _ _).1 hg₀).2 K w hw
  have hAZ : A.FlagAt (w ≫ g₀) (fun σ j => u σ j ≫ mu.φ) := (hA K _ _).2 hZ
  obtain ⟨y, hyπ, hA'y⟩ := Atlas.FlagAt.exists_point hAZ A'
  have htan : ∀ σ i, IsTanAtG (Y Z.i).t ((y ≫ f) ≫ Z.π) (u σ i ≫ mu.φ) := by
    obtain ⟨a, φ, -, hf, -⟩ := id hA'y
    rw [Category.assoc]
    exact fun σ i => (hf.1 σ i).1
  obtain ⟨U, hU⟩ := exists_up htan
  have hR' := (hR K y U).1 (hU ▸ hA'y)
  have hyf : y ≫ f = w ≫ g₀ := Atlas.FlagAt.point_eq (hU ▸ hR'.1) hAZ (by rw [Category.assoc, hyπ])
  refine ⟨y, ⟨τ, mu, u, hT, hyπ.trans hπ, hZ₁, hA'y⟩, ?_⟩
  intro R _ _ _ _ _ _ z hz
  obtain ⟨α, hα₀⟩ := D.C.cover ((z ≫ g₀) (IsLocalRing.closedPoint R))
  have hα : ⊤ ≤ (z ≫ g₀) ⁻¹ᵁ D.C.B α :=
    ((IsLocalRing.closed_point_mem_iff (U := (z ≫ g₀) ⁻¹ᵁ D.C.B α)).1 hα₀).ge
  have hyz : y ≫ f = spMap (algebraMap R K) ≫ z ≫ g₀ := by rw [hyf, ← hz, Category.assoc]
  have hy : ⊤ ≤ (y ≫ f) ⁻¹ᵁ D.C.B α := by
    rw [hyz]
    exact GlobalTheory.FlagMod.le_preimage_map (z ≫ g₀) hα le_top
  obtain ⟨n', a, a', h₁, h₂, hann⟩ := GlobalTheory.T.lattice_step_holds_pullback E H Dw Xo p W Y i₀ hp hpW t Z g D hg hL Z₁ g₀ hg₀ hH R K z α hα
  obtain ⟨y₀, hy₀, hyq⟩ := GlobalTheory.T.carrier_matrix_transfer _ Z.X X' (Z.π ≫ (Y Z.i).s) D.C D.N t.k D.Em f q hq R K (z ≫ g₀) α hα n' a a' y hy _
    h₁ h₂ hyz (hR'.2 α hy) fun l j hj =>
      hann τ mu u hT (hz ▸ hZ₁) (y ≫ f) hyz hy (U t.σ (Fin.castLE t.le l)) (Fin.castLE t.le l) l.2
        (congrFun (congrFun hU t.σ) (Fin.castLE t.le l)) j hj
  exact hLift R K (z ≫ g₀) y₀ y hy₀ hyz hyq

end GlobalTheory.GrCl
