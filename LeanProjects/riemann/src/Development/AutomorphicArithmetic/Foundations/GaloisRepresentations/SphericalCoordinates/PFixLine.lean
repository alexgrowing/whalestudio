import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogResolutionFubiniStudyPositive

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem herm_pos_toV_mulVec_of_pos {p : ℕ} [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ)
    (y : LKCx.grp G β) (z : Fin G.n → ℂ) (hz : 0 < (star z ⬝ᵥ LKCx.herm G v β *ᵥ z).re) :
    0 < (star (↑(LKCx.toV G v β y) *ᵥ z) ⬝ᵥ LKCx.herm G v β *ᵥ (↑(LKCx.toV G v β y) *ᵥ z)).re := by
  have hM : (↑(LKCx.toV G v β y) : Matrix (Fin G.n) (Fin G.n) ℂ) = G.psi v ↑(↑y : G.Cˣ × ℚˣ).1 := rfl
  have hs := GlobalTheory.ArchBound.herm_sim G β y v
  have hpos : (0 : ℝ) < ((↑(↑y : G.Cˣ × ℚˣ).2 : ℚ) : ℝ) := by exact_mod_cast y.2.2
  rw [hM, Matrix.star_mulVec, Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    ← Matrix.mul_assoc, hs, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul]
  exact mul_pos hpos hz

private theorem actY_actY_inv {p : ℕ} [Fact p.Prime] {D : UPel.HT.Datum p} {G : HTGroup p} (L : Link D G)
    {β : G.Cˣ} (a : LKCx.grp G β) (w : VQ D) : actY L a (actY L a⁻¹ w) = w := by
  show L.rep _ (L.rep _ w) = w
  rw [← Module.End.mul_apply, ← map_mul]
  have h1 : ((↑(↑a : G.Cˣ × ℚˣ).1 : G.C) * ↑(↑a⁻¹ : G.Cˣ × ℚˣ).1) = 1 := by
    rw [← Units.val_mul, ← Prod.fst_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, Prod.fst_one,
      Units.val_one]
  rw [h1, map_one, Module.End.one_apply]

theorem UpperTheory.Gal.W2.fixLine_of :
    UpperTheory.Gal.W2.ActY → UpperTheory.Gal.W2.FixLine := by
  intro hA p _ D G L v t₀ ρ β RD Q z hQ hrel y
  have hz0 : z.1 ≠ 0 := by
    intro h0
    have h1 := z.2
    rw [h0] at h1
    simp at h1
  have hinvmul : ∀ (y' : LKCx.grp G β) (x : Fin G.n → ℂ),
      (LKCx.toV G v β y'⁻¹).val *ᵥ ((LKCx.toV G v β y').val *ᵥ x) = x := by
    intro y' x
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one,
      Matrix.one_mulVec]
  have hne : ∀ (y' : LKCx.grp G β) (c : ℂ), (LKCx.toV G v β y').val *ᵥ z.1 = c • z.1 → c ≠ 0 := by
    rintro y' c hc rfl
    rw [zero_smul] at hc
    apply hz0
    rw [← hinvmul y' z.1, hc, Matrix.mulVec_zero]
  have inv : ∀ y' : LKCx.grp G β, LKCx.FixL G v β y' z.1 → LKCx.FixL G v β y'⁻¹ z.1 := by
    rintro y' ⟨c, hc⟩
    have hc0 := hne y' c hc
    have h1 : z.1 = c • ((LKCx.toV G v β y'⁻¹).val *ᵥ z.1) := by
      rw [← Matrix.mulVec_smul, ← hc, hinvmul]
    refine ⟨c⁻¹, ?_⟩
    calc (LKCx.toV G v β y'⁻¹).val *ᵥ z.1
        = c⁻¹ • (c • ((LKCx.toV G v β y'⁻¹).val *ᵥ z.1)) := by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
      _ = c⁻¹ • z.1 := by rw [← h1]
  let zi : LKCx.PosV G v β := ⟨(LKCx.toV G v β y⁻¹).val *ᵥ z.1, herm_pos_toV_mulVec_of_pos G v β y⁻¹ z.1 z.2⟩
  let Q₂ : VQ D →+ Fin D.g → ℂ := Q.comp (actY L y).toAddMonoidHom
  have hQ₂ : ∀ w, Q₂ w = Q (actY L y w) := fun w => rfl
  have hback : ∀ w, Q₂ (actY L y⁻¹ w) = Q w := by
    intro w
    rw [hQ₂, actY_actY_inv]
  have hper : IsPerQ L β ρ Q₂ := (hA p D G L β y⁻¹).2.2.1 ρ Q Q₂ hQ hback
  have hrel₂ : RD.rel Q₂ zi.1 := RD.equiv y⁻¹ Q Q₂ z.1 hback hrel
  have key := RD.uniq Q Q₂ z zi hQ hper hrel hrel₂
  refine ⟨⟨fun hF => ?_, fun ⟨H, hH⟩ => ?_⟩, inv y⟩
  · obtain ⟨c, hc⟩ := inv y hF
    obtain ⟨h, hh⟩ := key.mpr ⟨c, hne _ c hc, hc⟩
    refine ⟨LinearMap.toMatrix' (h : (Fin D.g → ℂ) →ₗ[ℂ] Fin D.g → ℂ), fun w => ?_⟩
    rw [LinearMap.toMatrix'_mulVec, ← hQ₂, hh w]
    rfl
  · have hsurj : Function.Surjective (Matrix.toLin' H) := by
      rw [← LinearMap.range_eq_top]
      have hle : Submodule.span ℝ (Set.range ⇑Q) ≤ (LinearMap.range (Matrix.toLin' H)).restrictScalars ℝ := by
        rw [Submodule.span_le]
        rintro _ ⟨w, rfl⟩
        refine ⟨Q (actY L y⁻¹ w), ?_⟩
        rw [Matrix.toLin'_apply, ← hH, actY_actY_inv]
      rw [hQ.2.1] at hle
      exact eq_top_iff.mpr (fun x _ => hle (Submodule.mem_top : x ∈ (⊤ : Submodule ℝ (Fin D.g → ℂ))))
    have hinj := LinearMap.injective_iff_surjective.mpr hsurj
    obtain ⟨c, hc0, hc⟩ := key.mp ⟨LinearEquiv.ofBijective (Matrix.toLin' H) ⟨hinj, hsurj⟩, fun w => by
      show Q₂ w = Matrix.toLin' H (Q w)
      rw [Matrix.toLin'_apply, hQ₂, hH]⟩
    have h2 := inv y⁻¹ ⟨c, hc⟩
    rwa [inv_inv] at h2
