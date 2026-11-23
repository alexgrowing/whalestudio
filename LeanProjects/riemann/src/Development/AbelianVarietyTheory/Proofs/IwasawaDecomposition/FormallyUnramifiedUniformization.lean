import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormallyUnramifiedEtaleCompletion
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteRootsOfBimul
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.ChartCharRank

open GlobalTheory.CharRank

theorem projective_and_finrank_le_min : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ Y.X)
    (t : SAB H (Sp R)) (mξ : SABMap t Y.t ξ) (P : PELUnif (maximalIdeal R) t),
    IsCN R → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom →
    ((residue R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified → P.TorsionIso →
    ∀ y : Sp (FractionRing R) ⟶ Xo.XF c, y ≫ Y.j = jK R ≫ ξ →
    Module.Projective (𝓞 E) P.D.toPre.X ∧ Module.finrank (𝓞 E) P.D.toPre.X ≤ min D.p D.q := by
  intro E _ _ _ H D l Xo c Y R _ _ _ ξ t m P hCN _ _ _ y hy
  haveI : Module.Projective (𝓞 E) P.D.toPre.X := GlobalTheory.Forms.projective_of_int (𝓞 E) P.D.toPre.X
  refine ⟨inferInstance, ?_⟩
  obtain ⟨hNoeth, -, -, hChar⟩ := hCN
  haveI := hNoeth
  haveI := hChar
  let K := AlgebraicClosure (FractionRing R)
  let f : R →+* K := (algebraMap (FractionRing R) K).comp (algebraMap R (FractionRing R))
  have hf : Function.Injective f :=
    (algebraMap (FractionRing R) K).injective.comp (IsFractionRing.injective R (FractionRing R))
  haveI : CharZero K := ⟨fun a b h => Nat.cast_injective (R := R) (hf (by simpa using h))⟩
  have hy' : y ≫ Y.jQ ≫ pullback.fst _ _ = jK R ≫ ξ := hy
  let x' : Sp K ⟶ Xo.XF c := spMap (algebraMap (FractionRing R) K) ≫ y
  have hx : x' ≫ Y.jQ ≫ pullback.fst _ _ = spMap f ≫ ξ := by
    rw [← DomFine.spMap_comp', Category.assoc, hy']
    rfl
  obtain ⟨β₀, hβ₀⟩ := Spec.map_surjective
    (x' ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s)
  have hβ : x' ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s = spMap β₀.hom :=
    hβ₀.symm
  have hdet := (Y.oF.geom K x' β₀.hom hβ).1
  have hr : (β₀.hom (baseKA l).ρ) ^ 2 = -(H.d : K) := by
    rw [← map_pow, (baseKA l).ρ_sq, map_neg, map_natCast]
  have bound : ∀ (τ : 𝓞 E →+* K) (N : ℕ), LieMult Y.oF.t.act x' τ N →
      Module.finrank (𝓞 E) P.D.toPre.X ≤ N := by
    intro τ N hN
    have h₅ := (GlobalTheory.lieMult_iff_of_isGrpPullback Y.m.cart Y.oF.t.act Y.t.act Y.m.act x' τ N).1 hN
    rw [hx] at h₅
    have h₆ := (GlobalTheory.lieMult_iff_of_isGrpPullback m.cart t.act Y.t.act m.act (spMap f) τ N).2 h₅
    obtain ⟨n, -, hn⟩ := lieMult_unif_loc H R t P K f hf τ N h₆
    omega
  obtain ⟨τ₁, τ₂, h₁, h₂⟩ := exists_chars H K _ hr
  exact le_min (bound τ₁ _ ((hdet τ₁).1 h₁)) (bound τ₂ _ ((hdet τ₂).2 h₂))

end GlobalTheory.ChartCharRank
