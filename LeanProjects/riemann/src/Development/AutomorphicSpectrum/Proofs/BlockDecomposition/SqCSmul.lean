import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalisationLadders.CriterionTruncation
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Coords
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiltrationCriticalComparisonMapStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensTransfer
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EtaNat
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClsCongr
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.LocBC

variable {R R' : Type} [CommRing R] [CommRing R'] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
  {Φ : PDF R C} {Φ' : PDF R' C'} {σ : R →+* R'} (m : SMor Φ Φ' σ)

theorem sqC_add {c c' c'' : R'} (hc : c'' = c + c') {a b : IdF Φ.A} {a' b' : IdF Φ'.A}
    (ha : m.LeC c a a') (hb : m.LeC c b b') (ha' : m.LeC c' a a') (hb' : m.LeC c' b b')
    (ha'' : m.LeC c'' a a') (hb'' : m.LeC c'' b b') (T : C') (x : sqM a b (m.G.obj T)) :
    (m.sqC c'' ha'' hb'').τ T x = (m.sqC c ha hb).τ T x + (m.sqC c' ha' hb').τ T x := by
  subst hc
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine Subtype.ext ?_
  change Ideal.Quotient.mk _ (algebraMap R' _ (c + c') * m.ρ T y) =
    Ideal.Quotient.mk _ (algebraMap R' _ c * m.ρ T y) + Ideal.Quotient.mk _ (algebraMap R' _ c' * m.ρ T y)
  rw [map_add, add_mul, map_add]

theorem sqC_smul {c c' : R'} (r : R) (hc : c' = σ r * c) {a b : IdF Φ.A} {a' b' : IdF Φ'.A}
    (ha : m.LeC c a a') (hb : m.LeC c b b') (ha' : m.LeC c' a a') (hb' : m.LeC c' b b') (T : C')
    (x : sqM a b (m.G.obj T)) :
    (m.sqC c' ha' hb').τ T x = (m.sqC c ha hb).τ T (r • x) := by
  subst hc
  rw [LinearMap.map_smulₛₗ]
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine Subtype.ext ?_
  change Ideal.Quotient.mk _ (algebraMap R' _ (σ r * c) * m.ρ T y) =
    σ r • Ideal.Quotient.mk _ (algebraMap R' _ c * m.ρ T y)
  have h : ∀ z : Φ'.A.obj T, Ideal.Quotient.mk (b'.S T) (algebraMap R' _ (σ r) * z) = σ r • Ideal.Quotient.mk (b'.S T) z :=
    fun z => by rw [← Algebra.smul_def]; rfl
  rw [← h, ← mul_assoc, ← map_mul]

section Pts

variable {d : ℕ} (E : Frame Φ d) (E' : Frame Φ' d) (e : E.D ⟶ m.G.obj E'.D)

theorem mPt_add {c c' c'' : R'} (hc : c'' = c + c') {a b : IdF Φ.A} {a' b' : IdF Φ'.A}
    (ha : m.LeC c a a') (hb : m.LeC c b b') (ha' : m.LeC c' a a') (hb' : m.LeC c' b b')
    (ha'' : m.LeC c'' a a') (hb'' : m.LeC c'' b b') (j : ℕ) (x : CH.H (Pt.U E ⋙ sq a b) j) :
    (mPt m E E' e c'' ha'' hb'').pull j x = (mPt m E E' e c ha hb).pull j x + (mPt m E E' e c' ha' hb').pull j x := by
  obtain ⟨f, hf, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (CH.cx _) j).1 x
  have h1 := CrystallineSemistableComparison.CechClassBoundaries.cyc (mPt m E E' e c'' ha'' hb'').hom f hf
  have h2 := CrystallineSemistableComparison.CechClassBoundaries.cyc (mPt m E E' e c ha hb).hom f hf
  have h3 := CrystallineSemistableComparison.CechClassBoundaries.cyc (mPt m E E' e c' ha' hb').hom f hf
  change (mPt m E E' e c'' ha'' hb'').hom.mapH j _ = (mPt m E E' e c ha hb).hom.mapH j _ + (mPt m E E' e c' ha' hb').hom.mapH j _
  rw [CrystallineSemistableComparison.P.mapH_cls _ j f hf h1, CrystallineSemistableComparison.P.mapH_cls _ j f hf h2, CrystallineSemistableComparison.P.mapH_cls _ j f hf h3,
    ← (CrystallineSemistableComparison.P.cls_surj _ j).2.2.2.1 _ _ h2 h3 (by rw [map_add, h2, h3, add_zero])]
  exact cls_congr (funext fun s => sqC_add m hc ha hb ha' hb' ha'' hb'' _ _) _ _

theorem mPt_smul {c c' : R'} (r : R) (hc : c' = σ r * c) {a b : IdF Φ.A} {a' b' : IdF Φ'.A}
    (ha : m.LeC c a a') (hb : m.LeC c b b') (ha' : m.LeC c' a a') (hb' : m.LeC c' b b')
    (j : ℕ) (x : CH.H (Pt.U E ⋙ sq a b) j) :
    (mPt m E E' e c' ha' hb').pull j x = (mPt m E E' e c ha hb).pull j (r • x) := by
  obtain ⟨f, hf, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (CH.cx _) j).1 x
  have h0 : CH.d _ j (r • f) = 0 := by rw [map_smul]; exact (show r • CH.d _ j f = 0 by rw [show CH.d _ j f = 0 from hf, smul_zero])
  have h1 := CrystallineSemistableComparison.CechClassBoundaries.cyc (mPt m E E' e c' ha' hb').hom f hf
  have h2 := CrystallineSemistableComparison.CechClassBoundaries.cyc (mPt m E E' e c ha hb).hom (r • f) h0
  rw [← (CrystallineSemistableComparison.P.cls_surj _ j).2.2.2.2 r f hf h0]
  change (mPt m E E' e c' ha' hb').hom.mapH j _ = (mPt m E E' e c ha hb).hom.mapH j _
  rw [CrystallineSemistableComparison.P.mapH_cls _ j f hf h1, CrystallineSemistableComparison.P.mapH_cls _ j _ h0 h2]
  exact cls_congr (funext fun s => sqC_smul m r hc ha hb ha' hb' _ _) _ _

theorem pull_U (c : R') {a b : IdF Φ.A} {a' b' : IdF Φ'.A} (ha : m.LeC c a a') (hb : m.LeC c b b') (j : ℕ)
    (x : CH.H (sq a b) j) :
    (mPt m E E' e c ha hb).pull j ((CH.Mor.restrict (sq a b) (Pt.U E)).pull j x) =
      (CH.Mor.restrict (sq a' b') (Pt.U E')).pull j ((m.sqC c ha hb).pull j x) := by
  obtain ⟨f, hf, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (CH.cx _) j).1 x
  rfl

end Pts

section HAdd

variable {R'' : Type} [CommRing R''] [Algebra R R''] {Ψ : PDF R'' C'} (p : SMor Φ Ψ (algebraMap R R''))
  {d : ℕ} (E : Frame Φ d) (E' : Frame Ψ d) (e : E.D ⟶ p.G.obj E'.D)

theorem hadd_Pt {N : Type} [AddCommGroup N] [Module R N] (ν : N →ₗ[R] R'') {a b : IdF Φ.A} {a' b' : IdF Ψ.A}
    (ha : ∀ n, p.LeC (ν n) a a') (hb : ∀ n, p.LeC (ν n) b b') (j : ℕ) :
    ∃ F : N ⊗[R] CH.H (Pt.U E ⋙ sq a b) j →+ CH.H (Pt.U E' ⋙ sq a' b') j,
      ∀ n x, F (n ⊗ₜ x) = (mPt p E E' e (ν n) (ha n) (hb n)).pull j x := by
  let f : N →+ (CH.H (Pt.U E ⋙ sq a b) j →+ CH.H (Pt.U E' ⋙ sq a' b') j) :=
    AddMonoidHom.mk' (fun n => ((mPt p E E' e (ν n) (ha n) (hb n)).pull j).toAddMonoidHom) (fun n n' => AddMonoidHom.ext fun x =>
      mPt_add p E E' e (map_add ν n n') (ha n) (hb n) (ha n') (hb n') (ha _) (hb _) j x)
  refine ⟨TensorProduct.liftAddHom f fun r n x => ?_, fun n x => ?_⟩
  · exact mPt_smul p E E' e r (by rw [map_smul, Algebra.smul_def]) (ha n) (hb n) (ha _) (hb _) j x
  · exact TensorProduct.liftAddHom_tmul _ _ _ _

end HAdd

end GlobalTheory.CompanionTheory.LocBC
