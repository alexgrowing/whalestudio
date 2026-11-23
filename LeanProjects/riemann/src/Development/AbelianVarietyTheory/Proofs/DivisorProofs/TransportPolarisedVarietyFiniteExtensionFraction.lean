import Mathlib
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordBundlePullbackGrpPullback
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem transport_extLam : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∀ PP : LB (G2 G).left, ExtLam G (A.L.pull gen.hom.left) PP → ∀ (K' : Type) [Field K'] (io : FractionRing R →+* K') (A₁ : PolAV (Sp K')) (α₁ : A₁.A.left ⟶ A.A.left) (α₁₂ : (G2 A₁.A).left ⟶ (G2 A.A).left), IsGrpPullback A₁.A A.A (spMap io) α₁ → Geo.Tor.IsSquare α₁ α₁₂ → LBIso (abelian₂ A₁.A A₁.L) ((abelian₂ A.A A.L).pull α₁₂) → ∀ (R₂ : Type) [CommRing R₂] [IsDomain R₂] [IsLocalRing R₂] (ρ : R →+* R₂) (i : K' ≃+* FractionRing R₂), Function.Injective ρ → (∀ r, i (io (algebraMap R _ r)) = algebraMap R₂ _ (ρ r)) → ∀ (G₂ : Over (Sp R₂)) [GrpObj G₂] [IsCommMonObj G₂] (β : G₂.left ⟶ G.left) (β₂ : (G2 G₂).left ⟶ (G2 G).left), IsGrpPullback G₂ G (spMap ρ) β → Geo.Tor.IsSquare β β₂ → ∃ (A₂ : PolAV (Sp (FractionRing R₂))) (gen₂ : ((Over.pullback (jK R₂)).obj G₂) ≅ A₂.A) (q : A₂.A.left ⟶ A₁.A.left), IsMonHom gen₂.hom ∧ ExtLam G₂ (A₂.L.pull gen₂.hom.left) (PP.pull β₂) ∧ IsGrpPullback A₂.A A₁.A (spMap i.toRingHom) q ∧ LBIso A₂.L (A₁.L.pull q) ∧ gen₂.inv.left ≫ pullback.fst G₂.hom (jK R₂) ≫ β = q ≫ α₁ ≫ gen.inv.left ≫ pullback.fst G.hom (jK R) := by
  intro R _ _ _ G _ _ A gen hgen PP hExt K' _ io A₁ α₁ α₁₂ hα hsqα hΛ R₂ _ _ _ ρ i hρ hi G₂ _ _ β β₂ hβ hsqβ
  haveI := hgen
  have : IsCommMonObj ((Over.pullback (jK R)).obj G) := Functor.isCommMonObj_obj
  have : IsCommMonObj ((Over.pullback (jK R₂)).obj G₂) := Functor.isCommMonObj_obj
  obtain ⟨A₂, q, pq, -, mq, t, ht⟩ := GlobalTheory.polBaseChange_holds _ _ (spMap i.toRingHom) A₁
  have hq : IsGrpPullback A₂.A A₁.A (spMap i.toRingHom) q := ⟨pq, fun T x y x₀ y₀ hx hy => by
    have e₁ : x₀ = Out.toBase pq.w x := Over.OverMorphism.ext hx
    have e₂ : y₀ = Out.toBase pq.w y := Over.OverMorphism.ext hy
    rw [e₁, e₂, ← mq]; rfl⟩
  have hLq : LBIso A₂.L (A₁.L.pull q) := LBIso.symm ⟨t, ht⟩
  have hsq : jK R₂ ≫ spMap ρ = spMap i.toRingHom ≫ spMap io ≫ jK R := by
    simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    simp [hi]
  haveI : IsMonHom gen.symm.hom := by show IsMonHom gen.inv; infer_instance
  have hgi : IsGrpPullback A.A ((Over.pullback (jK R)).obj G) (𝟙 _) gen.inv.left := isGrpPullback_of_iso gen.symm
  have gG : IsGrpPullback A.A G (jK R) (gen.inv.left ≫ pullback.fst G.hom (jK R)) :=
    (hgi.comp (isGrpPullback_pullback G (jK R))).congr (Category.id_comp _) rfl
  have gA : IsGrpPullback A₂.A G (spMap i.toRingHom ≫ spMap io ≫ jK R)
      (q ≫ α₁ ≫ gen.inv.left ≫ pullback.fst G.hom (jK R)) := hq.comp (hα.comp gG)
  have g₂ : IsGrpPullback ((Over.pullback (jK R₂)).obj G₂) G (spMap i.toRingHom ≫ spMap io ≫ jK R)
      (pullback.fst G₂.hom (jK R₂) ≫ β) :=
    ((isGrpPullback_pullback G₂ (jK R₂)).comp hβ).congr hsq rfl
  obtain ⟨e, he, hee⟩ := grpPullback_iso g₂ gA
  haveI := he
  have hei : e.inv.left ≫ e.hom.left = 𝟙 _ := by rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have hgh : gen.inv.left ≫ gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have h5 : e.inv.left ≫ pullback.fst G₂.hom (jK R₂) ≫ β = q ≫ α₁ ≫ gen.inv.left ≫ pullback.fst G.hom (jK R) := by
    rw [← hee, ← Category.assoc, hei, Category.id_comp]
  refine ⟨A₂, e, q, he, ⟨pull_isLB hExt.1 β₂, fun κ₂ hκ₂ => ?_⟩, hq, hLq, h5⟩

  obtain ⟨g₂m, hg₂, -⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ G ((Over.pullback (jK R)).obj G) _
    (isGrpPullback_pullback G (jK R))
  obtain ⟨γ₁, hsqγ, Ha⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ ((Over.pullback (jK R)).obj G) A.A _ hgi
  obtain ⟨q₂, hsqq, Hc⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ A₁.A A₂.A _ hq
  obtain ⟨e₂, hsqe, Hd⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ A₂.A ((Over.pullback (jK R₂)).obj G₂) _
    (isGrpPullback_of_iso e)
  have hLK := pull_isLB A.isLB gen.hom.left
  have i₀ : LBIso A.L ((A.L.pull gen.hom.left).pull gen.inv.left) :=
    LBIso.chartPull (chartPullUnpull A.L (𝟙 _) rfl)
      (chartPullLinComb A.L gen.hom.left (fun _ => gen.inv.left) (fun _ => 𝟙 _) _ (𝟙 _)
        (fun _ => by rw [hgh, Category.id_comp]))
      (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB A.isLB (𝟙 _)))
  have Ha' := Ha _ _ _ PP g₂m hLK A.isLB hExt.1 i₀ (hExt.2 g₂m hg₂)
  have Hb : LBIso (abelian₂ A₁.A A₁.L) (PP.pull (α₁₂ ≫ γ₁ ≫ g₂m)) :=
    LBIso.trans (DVR.linComb_isLB _ A₁.isLB _ _) (pull_isLB (DVR.linComb_isLB _ A.isLB _ _) _)
      (pull_isLB hExt.1 _) hΛ
      (LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ α₁₂ α₁₂ rfl)
        (chartPullSame PP (fun _ => α₁₂ ≫ γ₁ ≫ g₂m) (fun _ => γ₁ ≫ g₂m) _ α₁₂ fun _ => rfl) Ha')
  have Hc' := Hc _ _ _ PP _ A₁.isLB A₂.isLB hExt.1 hLq Hb
  have Hd' := Hd _ _ _ PP _ A₂.isLB (pull_isLB A₂.isLB _) hExt.1
    (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB A₂.isLB _)) Hc'
  have E : e₂ ≫ q₂ ≫ α₁₂ ≫ γ₁ ≫ g₂m = κ₂ ≫ β₂ := by
    apply pullback.hom_ext
    · show (e₂ ≫ q₂ ≫ α₁₂ ≫ γ₁ ≫ g₂m) ≫ (fst G G).left = (κ₂ ≫ β₂) ≫ (fst G G).left
      simp only [Category.assoc, hg₂.1, reassoc_of% hsqγ.1, reassoc_of% hsqα.1, reassoc_of% hsqq.1,
        reassoc_of% hsqe.1, hsqβ.1, reassoc_of% hκ₂.1, hee]
    · show (e₂ ≫ q₂ ≫ α₁₂ ≫ γ₁ ≫ g₂m) ≫ (snd G G).left = (κ₂ ≫ β₂) ≫ (snd G G).left
      simp only [Category.assoc, hg₂.2, reassoc_of% hsqγ.2, reassoc_of% hsqα.2, reassoc_of% hsqq.2,
        reassoc_of% hsqe.2, hsqβ.2, reassoc_of% hκ₂.2, hee]
  exact LBIso.trans (DVR.linComb_isLB _ (pull_isLB A₂.isLB _) _ _) (pull_isLB hExt.1 _)
    (pull_isLB (pull_isLB hExt.1 β₂) κ₂) Hd'
    (LBIso.chartPull (chartPullSame PP _ (fun _ => β₂) _ κ₂ fun _ => E) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ κ₂ κ₂ rfl)
      (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hExt.1 β₂)))

end GlobalTheory.Mum
