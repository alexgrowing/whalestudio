import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecializationMapCompUniversalSection
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsTangentOfUniqueIntegralLift
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GrNormPush
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GrNormPosOfBasis
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.GalCarry
open Formalism.MainNotions.DIV.Cons (intO)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.GalCarry.LnPushProof

attribute [local instance] Over.cartesianMonoidalCategory

section Twist

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X) (σ : 𝓞 E ≃+* 𝓞 E) (hσ : σ H.w0 = H.w0)

theorem dlogDvd_twist {O : Type} [CommRing O] (x : Sp O ⟶ X) (p m : ℕ) (v : Sp (DualNumber O) ⟶ t.G.left) :
    DlogDvd (GlobalTheory.FiniteStable.twist σ hσ t) x p m v ↔ DlogDvd t x p m v :=
  ⟨fun h n c g hg => h n ⟨c.χ, c.mul, c.nat⟩ g hg, fun h n c g hg => h n ⟨c.χ, c.mul, c.nat⟩ g hg⟩

variable {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]

theorem lat_twist (p : ℕ) (x : Sp C ⟶ X) (b : Bool) :
    lat (GlobalTheory.FiniteStable.twist σ hσ t) p x b = lat t p x b := by
  cases b
  · rfl
  · ext v
    exact exists_congr fun xO => and_congr_right fun _ => exists_congr fun m => exists_congr fun vO =>
      and_congr_right fun _ => and_congr_right fun _ => dlogDvd_twist t σ hσ xO p m vO

theorem grNorm_twist (x : Sp C ⟶ X) (Λ : Set (Sp (DualNumber C) ⟶ t.G.left)) {m : ℕ}
    (u : Fin m → (Sp (DualNumber C) ⟶ t.G.left)) (i : Fin m) :
    grNorm (GlobalTheory.FiniteStable.twist σ hσ t) x Λ u i = grNorm t x Λ u i := rfl

theorem grNorm_cast (x : Sp C ⟶ X) (Λ : Set (Sp (DualNumber C) ⟶ t.G.left)) {m n : ℕ} (h : m = n)
    (v : Fin n → (Sp (DualNumber C) ⟶ t.G.left)) (k : ℕ) (hk : k < n) (hk' : k < m) :
    grNorm t x Λ (fun i => v (Fin.cast h i)) ⟨k, hk'⟩ = grNorm t x Λ v ⟨k, hk⟩ := by
  subst h
  rfl

end Twist

theorem lnPush : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F))
    (T : Tw Z), T.LnPush := by
  intro E _ _ _ H Dw l Xo c Z T p _ b x u u' hu hu' τ k
  obtain ⟨xO, hxO, -⟩ := GlobalTheory.ShFam.Pad.Guard.existsUnique_ext Z x
  have huniq : ∀ y : Sp ↥(intO ℂ_[p]) ⟶ Z.X, spMap (intO ℂ_[p]).subtype ≫ y =
      spMap (intO ℂ_[p]).subtype ≫ xO ≫ T.ρ.hom → y = xO ≫ T.ρ.hom := fun y hy =>
    (GlobalTheory.ShFam.Pad.Guard.existsUnique_ext Z (x ≫ T.ρ.hom)).unique (hy.trans (by rw [← Category.assoc, hxO]))
      (by rw [← Category.assoc, hxO])
  have hΛ : ∀ v, IsTanAtG Z.t x v → (v ∈ lat Z.t p x b ↔
      v ≫ T.sab.φ ∈ lat (GlobalTheory.FiniteStable.twist T.σ T.w0 Z.t) p (x ≫ T.ρ.hom) b) := by
    intro v hv
    subst hxO
    rw [Category.assoc]
    exact GlobalTheory.ShFam.LatPush.lat_push E H Z.X Z.X _ Z.t T.ρ.hom T.sab ℂ_[p] p b xO huniq v hv
  have key : ∀ (h : k < Dw.mult τ) (h' : k < Dw.mult (T.emb τ)),
      grNorm Z.t x (lat Z.t p x b) (u (T.emb τ)) ⟨k, h'⟩ =
        grNorm Z.t (x ≫ T.ρ.hom) (lat Z.t p (x ≫ T.ρ.hom) b) (u' τ) ⟨k, h⟩ := by
    intro h h'
    rw [GlobalTheory.ShFam.Pad.Pull.grNorm_push T.sab rfl hΛ (fun i => hu _ i), lat_twist, grNorm_twist,
      funext (hu' τ)]
    exact (grNorm_cast Z.t _ _ (T.mult_emb τ) (fun i => u (T.emb τ) i ≫ T.mu.cm.F) k h' h).symm
  simp only [lnStep]
  rw [T.emb_rt τ]
  by_cases hk : k < Dw.mult τ
  · have hk' : k < Dw.mult (T.emb τ) := T.mult_emb τ ▸ hk
    rw [dif_pos hk', dif_pos hk, key hk hk']
  · have hk' : ¬ k < Dw.mult (T.emb τ) := T.mult_emb τ ▸ hk
    rw [dif_neg hk', dif_neg hk]

end GlobalTheory.ShFam.GalCarry.LnPushProof
