import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinOfIsPull
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SectionPowerCalculusGeometricFibre
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsBasisRecombinationInvertibleMatrixTrait

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LN GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorRef

open GlobalTheory.FramePull in

theorem linA_of_dominant {S : Scheme.{0}} {G : Over S} [Flat G.hom] {L : LB G.left} (hL : L.IsLB) {N : ℕ}
    {T T' B : Over S} (u : T' ⟶ T) [IsSchemeTheoreticallyDominant u.left] [QuasiCompact u.left] (h : T ⟶ B) {n : ℕ}
    (b : Fin n → LB.Sec (LPow G L (N : ℤ) B)) (c : Fin n → Γ(T.left, ⊤)) (a : Γ(T.left, ⊤))
    (s : LB.Sec (LPow G L (N : ℤ) T)) (s' : LB.Sec (LPow G L (N : ℤ) T')) (hs : IsPull u s s')
    (H : LinA G L N (u ≫ h) b (fun i => u.left.appTop.hom (c i)) (u.left.appTop.hom a) s') :
    LinA G L N h b c a s := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.Recombine.exists_lin hL h b c
  obtain ⟨τ, hτ⟩ := GlobalTheory.Recombine.exists_lin hL (𝟙 T) (fun _ : Fin 1 => s) (fun _ => a)
  have : Flat (fst T G).left := inferInstanceAs (Flat (pullback.fst T.hom G.hom))
  have : IsSchemeTheoreticallyDominant (u ▷ G).left :=
    IsSchemeTheoreticallyDominant.of_isPullback (whisker_isPullback u).flip
  have : QuasiCompact (u ▷ G).left := MorphismProperty.of_isPullback (whisker_isPullback u).flip inferInstance
  have hg : ∀ (y : (T' ⊗ G).left) (x : Γ(T.left, ⊤)),
      gs ((u ▷ G).left ≫ (fst T G).left) y ⊤ x = gs (fst T' G).left y ⊤ (u.left.appTop.hom x) := fun y x => by
    rw [← Over.comp_left, whiskerRight_fst, Over.comp_left]
    exact (gs_pull _ u.left y ⊤ trivial _).symm
  have e : τ = σ := sec_ext_of_inj (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => (N : ℤ)) hL (u ▷ G).left
    (u ▷ G).left.app_injective fun y J hJ => by
      have a₁ := (lin_iff _ _ _ _).1 hτ _ (u ▷ G).left y J hJ
      have a₂ := (lin_iff _ _ _ _).1 hσ _ (u ▷ G).left y J hJ
      have a₃ := H y J hJ
      have a₄ := hs _ (𝟙 _) y J hJ
      rw [Category.id_comp] at a₄
      rw [Fin.sum_univ_one, id_whiskerRight, Over.id_left, Category.comp_id, hg, ← a₄] at a₁
      refine a₁.trans (a₃.trans (Eq.trans ?_ a₂.symm))
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hg, comp_whiskerRight, Over.comp_left]
  subst e
  intro z J hJ
  have a₁ := hτ z J hJ
  rw [Fin.sum_univ_one, id_whiskerRight, Over.id_left] at a₁
  exact a₁.symm.trans (hσ z J hJ)

theorem linA_of_fractionRing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R]
    (t : SAB H (Sp R)) (N n : ℕ) (b : Fin n → LB.Sec (LPow t.G t.PP.L (N : ℤ) (Over.mk (𝟙 (Sp R)))))
    (W : Type) [CommRing W] [IsDomain W] (φ : R →+* W) (c : Fin n → W) (a : W)
    (s : LB.Sec (LPow t.G t.PP.L (N : ℤ) (Over.mk (spMap φ))))
    (s' : LB.Sec (LPow t.G t.PP.L (N : ℤ) (Over.mk (spMap ((algebraMap W (FractionRing W)).comp φ))))),
    Lin t.G t.PP.L N (jC φ (algebraMap W (FractionRing W))) (fun _ : Fin 1 => s) (fun _ => 1) s' →
    LinA t.G t.PP.L N (toBase ((algebraMap W (FractionRing W)).comp φ)) b
      (fun i => GlobalTheory.OneBasis.fnR (algebraMap W (FractionRing W) (c i))) (GlobalTheory.OneBasis.fnR (algebraMap W (FractionRing W) a)) s' →
    LinA t.G t.PP.L N (toBase φ) b (fun i => GlobalTheory.OneBasis.fnR (c i)) (GlobalTheory.OneBasis.fnR a) s := by
  intro E _ _ _ H R _ t N n b W _ _ φ c a s s' h₁ h₂
  have := t.semi.smooth
  have : IsDominant (jK W) := DVR.isDominant_jK
  have : IsSchemeTheoreticallyDominant (jC φ (algebraMap W (FractionRing W))).left :=
    IsSchemeTheoreticallyDominant.of_isDominant (jK W)
  have : QuasiCompact (jC φ (algebraMap W (FractionRing W))).left := inferInstanceAs (QuasiCompact (jK W))
  have e : ∀ x : W, (jC φ (algebraMap W (FractionRing W))).left.appTop.hom (GlobalTheory.OneBasis.fnR x) =
      GlobalTheory.OneBasis.fnR (algebraMap W (FractionRing W) x) := fun x => GlobalTheory.OneBasis.Calc.appTop_fnR _ x
  refine linA_of_dominant t.PP.isLB (jC φ (algebraMap W (FractionRing W))) (toBase φ) b _ _ s s'
    (GlobalTheory.FramePull.isPull_of_lin h₁) ?_
  rw [jC_toBase]
  simp only [e]
  exact h₂

end GlobalTheory.TorRef
