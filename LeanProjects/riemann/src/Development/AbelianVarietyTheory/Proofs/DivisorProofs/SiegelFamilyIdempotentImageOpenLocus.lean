import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverCompImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenLocusIdempotentImageSiegelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrincipalSiegelAdjointActionPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelPullbackWithActionCancellationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentImageRelationOfPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelPullbackOfIdempotentImagesAndActionPullbacStatement

noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.SiegelTor GlobalTheory.EndLoc

theorem idemImage_locus : ∀ (h h' M d : ℕ) (O : Type) [Ring O] (bar : O → O) (e : O) (jl : (Fin h ⊕ Fin h → ℤ) →+ (Fin h' ⊕ Fin h' → ℤ)) (n : ℕ) (o : Fin n → O) (κ : Fin n → (Fin h' ⊕ Fin h' → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (S' : Scheme.{0}) [IsLocallyNoetherian S'] (t : S' ⟶ Sp (cycAway M)) (z : SiegPre h' M (zetaAway M) t) (act : O → (z.A ⟶ z.A)), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → z.Principal → IsRAct z.A act → Adj z.A z.P bar act → e * e = e → ∃ (Y : Scheme.{0}) (j : Y ⟶ S') (c : SiegPre h M (zetaAway M) (j ≫ t)), IsImmersion j ∧ QuasiCompact j ∧ SiegKerBy c d ∧ IsUnit ((d : ℕ) : Γ(Y, ⊤)) ∧ (∀ (T : Scheme.{0}) (t' : T ⟶ Sp (cycAway M)) (y : T ⟶ Y) (c' : SiegPre h M (zetaAway M) t'), y ≫ j ≫ t = t' → SiegPB c' c y → ∃ (w : SiegPre h' M (zetaAway M) t') (actw : O → (w.A ⟶ w.A)), w.Principal ∧ IsRAct w.A actw ∧ Adj w.A w.P bar actw ∧ ActPB w actw z act (y ≫ j) ∧ ZRel e jl o κ c' w actw) ∧ ∀ (T : Scheme.{0}) (t' : T ⟶ Sp (cycAway M)) (g : T ⟶ S') (c' : SiegPre h M (zetaAway M) t'), g ≫ t = t' → IsUnit ((d : ℕ) : Γ(T, ⊤)) → SiegKerBy c' d → (∃ (w : SiegPre h' M (zetaAway M) t') (actw : O → (w.A ⟶ w.A)), ActPB w actw z act g ∧ ZRel e jl o κ c' w actw) → ∃! y : T ⟶ Y, y ≫ j = g ∧ SiegPB c' c y := by
  intro h h' M d O _ bar e jl n o κ S' _ t z act hh hM hodd hd hcop hpr hra hadj hee
  obtain ⟨U, c, wU, actU, hker, hunit, hwp, hwr, hwa, hwpb, hrel, hrange⟩ :=
    GlobalTheory.T.exists_open_locus_idempotent_image_siegel h h' M d O bar e jl n o κ S' t z act hh hM hodd hd hcop hpr hra hadj hee
  refine ⟨U.toScheme, U.ι, c, inferInstance, inferInstance, hker, hunit, ?_, ?_⟩
  · intro T t' y c' hyt hc'
    obtain ⟨w₂, act₂, hp₂, hr₂, ha₂, hpb₂⟩ :=
      GlobalTheory.T.exists_principal_siegel_adjoint_action_pullback h' M (cycAway M) (zetaAway M) O bar U.toScheme T (U.ι ≫ t) t' y wU actU hyt hwp hwr hwa
    exact ⟨w₂, act₂, hp₂, hr₂, ha₂, hpb₂.trans hwpb,
      GlobalTheory.T.idempotent_image_relation_of_pullback h h' M (cycAway M) (zetaAway M) O e jl n o κ U.toScheme T (U.ι ≫ t) t' y c wU actU c' w₂ act₂ hpb₂ hc' hrel⟩
  · intro T t' g c' hgt hdu hc' hex
    subst hgt
    have hr : Set.range g.base ⊆ (U : Set S') := hrange T g c' hdu hc' hex
    let y : T ⟶ U.toScheme := IsOpenImmersion.lift U.ι g (by rw [Scheme.Opens.range_ι]; exact hr)
    have hy : y ≫ U.ι = g := IsOpenImmersion.lift_fac _ _ _
    obtain ⟨w', actw', hpb', hrel'⟩ := hex
    refine ⟨y, ⟨hy, ?_⟩, ?_⟩
    · have hpb'' : ActPB w' actw' z act (y ≫ U.ι) := by rw [hy]; exact hpb'
      exact GlobalTheory.T.siegel_pullback_of_idempotent_images_and_action_pullback h h' M (cycAway M) (zetaAway M) O e jl n o κ U.toScheme T (U.ι ≫ t) (g ≫ t) y c wU actU c' w' actw'
        (GlobalTheory.T.siegel_pullback_with_action_cancellation h' M (cycAway M) (zetaAway M) O S' U.toScheme T t (U.ι ≫ t) (g ≫ t) z act U.ι y wU actU w' actw' hwpb hpb'')
        hrel hrel'
    · rintro y' ⟨hy', -⟩
      exact (cancel_mono U.ι).1 (hy'.trans hy.symm)

end GlobalTheory.UPel.HT
