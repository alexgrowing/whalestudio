import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SameTwistOfOneField
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

theorem GlobalTheory.HeckeLocN.exists_twRing_of_large : ∀ (D : D7) (C : NChoice D) (F : TwFrameC D) (low : Finset ℕ) (E0 : PlEmb D.what₂), TwistFrameLowIndexCompatibility D F low → ChoiceC D C → ∀ w : D.what₂.places.Pl, ∃ F0 : Loc.FinExt (D.what₂.places.resChar w), ∀ (X : CoefIn D.what₂) (j : ℕ), X.E = E0 → F0.1 ≤ (X.Kx j w).1 → ∃ f : D.ntw.O0 (C.twI w) →+* OcC X j w, TwAlgAt C X j w f ∧ TwRdAt C X j w f ∧ (TwistedAt D w → ∀ (x : D.LL0) (y : D.ntw.O0 (C.twI w)), algebraMap (D.ntw.O0 (C.twI w)) (FractionRing (D.ntw.O0 (C.twI w))) y = (if C.sd w then D.ntw.emb0 (C.twI w) else D.ntw.emb0b (C.twI w)) x → ecC X j w (x : D.what₂.LL) = algebraMap (OcC X j w) (FractionRing (OcC X j w)) (f y)) := by
  intro D C F low E0 hT hC w
  obtain ⟨φ, hR, hn, ⟨K, hKf, hK⟩, halg⟩ :=
    GlobalTheory.HeightCounting.SameTw.exists_reads D C F hT w (D.what₂.places.resChar w) (C.twI_l w) (E0.emb w) (E0.emb_w w)
  refine ⟨⟨K, hKf⟩, ?_⟩
  intro X j hXE hle
  let g : D.ntw.O0 (C.twI w) →+* ↥(X.Kx j w).1 := φ.codRestrict (X.Kx j w).1 (fun y => hle (hK y))
  let f : D.ntw.O0 (C.twI w) →+* OcC X j w :=
    g.codRestrict (Loc.OL (X.Kx j w)) (fun y => (Formalism.BasicNotions.Examples₂.LB.mem_OL (X.Kx j w) (g y)).2 (hn y))
  have hf : ∀ y, iqC X j w (algebraMap (OcC X j w) (FractionRing (OcC X j w)) (f y)) = φ y := fun y => by
    rw [iqC_alg]; rfl
  have e1 : (iqC X j w).comp (ecC X j w) = E0.emb w := by
    ext x; rw [RingHom.comp_apply, iqC_ec, hXE]
  have e2 : (iqC X j w).comp ((algebraMap (OcC X j w) (FractionRing (OcC X j w))).comp f) = φ := by
    ext y; exact hf y
  have hRd : GlobalTheory.HeightCounting.SameTw.Reads D C w (ecC X j w) ((algebraMap (OcC X j w) (FractionRing (OcC X j w))).comp f) :=
    GlobalTheory.HeightCounting.SameTw.Reads.of_comp (iqC X j w) (by rw [e1, e2]; exact hR)
  refine ⟨f, ?_, hRd, fun hw x y hy => GlobalTheory.HeightCounting.SameTw.Reads.emb hC hw hRd x y hy⟩
  intro z z' hz
  apply Subtype.val_injective
  apply Subtype.val_injective
  change φ _ = _
  rw [halg z z' hz]
  rfl
