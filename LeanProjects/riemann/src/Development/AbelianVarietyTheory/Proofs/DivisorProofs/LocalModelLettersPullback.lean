import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPreChain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorsionCharExtendsDivisibleLevel
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.GroupBplus (AffOp)
open GlobalTheory.RingChain (RChain)
open GlobalTheory.ChainPts.PullHT (pullA)
open scoped TensorProduct
open GlobalTheory.ChainPts

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.ChainPts.PtDesc

open GlobalTheory.VB (IsFrame IsVB)
open GlobalTheory.ChainPts.PullHT

theorem exists_affOp_frame {X : Scheme.{0}} {F : X.Modules} {r : ℕ} (hF : IsVB F r) (x : X) :
    ∃ (U : AffOp X) (e : Fin r → Γ(F, U.1)), x ∈ U.1 ∧ IsFrame e := by
  obtain ⟨V, e, hx, he⟩ := hF x
  obtain ⟨U, hU, hxU, hUV⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hx
  exact ⟨⟨U, hU, ⟨⟨x, hxU⟩⟩⟩, _, hxU, he.res hUV⟩

theorem mem_intO_of_isIntegral (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] (x : C)
    (hx : IsIntegral (intO C) x) : x ∈ intO C := by
  haveI := GlobalTheory.TorsCharExt.intO_valuationRing C
  haveI := GlobalTheory.TorsCharExt.intO_isFractionRing C
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp hx
  exact y.2

theorem valF_coef_pull {k : Type} [Field k] {T X X' : Scheme.{0}} (w : Sp k ⟶ X') (g : X' ⟶ X) (h : X ⟶ T) {F : X.Modules}
    [F.IsQuasicoherent] {r : ℕ} (d : Bool) {V : X.Opens} {A : T.Opens} {e : Fin r → Γ(F, V)} {s : Fin r → Γ(F, h ⁻¹ᵁ A)}
    (he : IsFrame e) (hs : IsFrame s) (l i : Fin r) :
    valF w _ (coef d (isFrame_pullS g le_rfl he) (isFrame_pullS g (Scheme.Hom.comp_preimage g h A).le hs) l i) =
      valF (w ≫ g) _ (coef d he hs l i) := by
  rw [coef_pullS g d le_rfl (Scheme.Hom.comp_preimage g h _).le he hs l i]
  exact valF_appLE w g (U := V ⊓ h ⁻¹ᵁ A) (U' := g ⁻¹ᵁ V ⊓ (g ≫ h) ⁻¹ᵁ A) _
    (by rw [Scheme.Hom.comp_preimage]; exact le_rfl) _

theorem valF_appTop {k : Type} [Field k] {X X' : Scheme.{0}} (w : Sp k ⟶ X') (g : X' ⟶ X) (c : Γ(X, ⊤)) :
    valF w ⊤ (g.appTop c) = valF (w ≫ g) ⊤ c := by
  rw [← valF_appLE w g (U := ⊤) (U' := ⊤) le_rfl le_rfl c]
  congr 1
  first | (erw [Scheme.Hom.appLE_eq_app]; done) | (erw [Scheme.Hom.appLE_eq_app]; rfl) | done

theorem ptJ_ptR_of_kerMatch : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} [Fact p.Prime] {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p} (Z : GlobalTheory.LocM.Mdl Y i₀) {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {B : GlobalTheory.Vert.Model O} (h : B.X ⟶ Z.X) {r : ℕ} (x x' : Fin r → Letter Dw) (Lie Om : AM B (𝓞 E)) (sL : ∀ a : Fin Z.m, Fin r → Γ(Lie.V, h ⁻¹ᵁ (Z.U a).1)) (hL : ∀ a, GlobalTheory.VB.IsFrame (sL a)) (sO : ∀ a : Fin Z.m, Fin r → Γ(Om.V, h ⁻¹ᵁ (Z.U a).1)) (hO : ∀ a, GlobalTheory.VB.IsFrame (sO a)) (n o : ℕ) (π : Γ(B.X, ⊤)) (γ : ℕ → Γ(B.X, ⊤)) (C : ChainsBp p n o Lie Om π γ) (X' : Scheme.{0}) (f : X' ⟶ B.X) (Q₁ Q₂ : X'.Modules) (j' : (Scheme.Modules.pullback f).obj Lie.V ⟶ Q₁) (ρ' : (Scheme.Modules.pullback f).obj Om.V ⟶ Q₂) (hL' : ∀ a, GlobalTheory.VB.IsFrame (pullS f sL a)) (hO' : ∀ a, GlobalTheory.VB.IsFrame (pullS f sO a)), GlobalTheory.VB.IsVB Lie.V r → GlobalTheory.VB.IsVB Om.V r → SysPt Z h x x' hL hO C → KerMatch C f j' ρ' → PtJ Z (f ≫ h) x hL' (f.appTop π) j' ∧ PtR Z (f ≫ h) x' hO' ρ' := by
  intro E _ _ _ H Dw Xo p _ W Y i₀ Z O _ _ _ B h r x x' Lie Om sL hL sO hO n o π γ C X' f Q₁ Q₂ j' ρ' hL' hO' vbL vbO hSys hKer
  haveI := vbL.isQuasicoherent
  haveI := vbO.isQuasicoherent
  have hp : ∀ y : Z.Pt, (p : ↥y.C.S) ≠ 0 := fun y => Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  refine ⟨fun y w hw a φ hφ => ?_, fun y w hw a φ hφ => ?_⟩
  · haveI := GlobalTheory.TorsCharExt.intO_valuationRing ↥y.C.S
    obtain ⟨U, e, hx, he⟩ := exists_affOp_frame vbL (f (w (IsLocalRing.closedPoint _)))
    have hU : ⊤ ≤ w ⁻¹ᵁ f ⁻¹ᵁ U.1 := top_le_of_closedPoint w _ hx
    obtain ⟨ψ, hψ, hJ, -⟩ := hKer ↥y.C.S (intO ↥y.C.S) (mem_intO_of_isIntegral _) (hp y) w U hU
    have hS := (hSys y U ψ (by rw [hψ, Category.assoc]; exact hw) a φ hφ).1 e he
    rw [hψ, ← hJ] at hS
    refine ⟨f ⁻¹ᵁ U.1, _, isFrame_pullS f le_rfl he, hU, fun cf v hv => (hS cf v hv).trans ?_⟩
    have hc := valF_coef_pull (spMap (intO ↥y.C.S).subtype ≫ w) f h false he (hL a)
    simp only [← Category.assoc, ← hc, valF_appTop]
  · haveI := GlobalTheory.TorsCharExt.intO_valuationRing ↥y.C.S
    obtain ⟨U, e, hx, he⟩ := exists_affOp_frame vbO (f (w (IsLocalRing.closedPoint _)))
    have hU : ⊤ ≤ w ⁻¹ᵁ f ⁻¹ᵁ U.1 := top_le_of_closedPoint w _ hx
    obtain ⟨ψ, hψ, -, hR⟩ := hKer ↥y.C.S (intO ↥y.C.S) (mem_intO_of_isIntegral _) (hp y) w U hU
    have hS := (hSys y U ψ (by rw [hψ, Category.assoc]; exact hw) a φ hφ).2 e he
    rw [hψ, ← hR] at hS
    refine ⟨f ⁻¹ᵁ U.1, _, isFrame_pullS f le_rfl he, hU, fun cf v hv => (hS cf v hv).trans ?_⟩
    have hc := valF_coef_pull (spMap (intO ↥y.C.S).subtype ≫ w) f h true he (hO a)
    simp only [← Category.assoc, ← hc]

end GlobalTheory.ChainPts.PtDesc

end
