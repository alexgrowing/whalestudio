import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepLevelContainsDeepCongruenceAtBadPrimeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DeepElementConjRationalAtBadPrimeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RepresentativeImagePointOfLiftStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT.LevGe

theorem exists_put : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F)) (κ : GL (Fin n) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))), κ ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) → ∃ x ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F), (∀ v', v' ≠ v → bc (prV (E := E) v') x = 1) ∧ bc (prV (E := E) v) x = bc (prV (E := E) v) κ := by
  intro F E _ _ _ _ _ σ n J v κ hκ
  classical
  refine ⟨Formalism.UG.P.afsplitU v (bc (prV (E := E) v) κ) 1,
    Formalism.UG.P.afsplitU_mem v σ J _ 1 (Formalism.UG.P.afsplit_bc_mem σ J v κ hκ) (one_mem _), fun w hw => ?_, ?_⟩
  · apply Units.ext
    rw [Formalism.UG.P.afsplit_coe_bc_prV, Formalism.UG.P.afsplitU_coe, Formalism.UG.P.afsplitC_prV_ne v w hw, Units.val_one, Units.val_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  · exact Formalism.UG.P.afsplit_right1 v _ 1

set_option maxHeartbeats 800000 in

theorem mem_uloc : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : Charts I l Z u a i hi bad chOf) (k : Ch → GA B (B.R.N i)), ReadsAt I l Z K k → ∀ (c : (I.stp u a i).Cl) (fb : SBof I a → GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E), FrNear I l Z a (k (chOf c)) fb → ∀ (P : SBof I a) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) → ∀ κ ∈ UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), ∀ g ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1, GlobalTheory.TwU.InFrame (i := i) (sm I l Z) fb (I.cst a).D P κ g → (∀ g' ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1, CongE P.1 ((I.cst a).D P) g g' → ∃ κ' : (I.stp u a i).G c.1, Keeps I κ' ((I.stp u a i).rep c) ∧ LiftsInv I κ' P g' ∧ ∀ P', P' ≠ P → LiftsInv I κ' P' 1) → bc (prV (E := (I.rec7 l Z).host.E) v) κ ∈ (K (chOf c)).lev.Uloc v := by
  intro B X I hOk hPins l Z u a i hi bad Ch chOf K k hR c fb hfb P v hv κ hκ g hg hF hL
  obtain ⟨N, hN⟩ := GlobalTheory.T.stepLevel_contains_deep_congruence_at_bad_prime I hOk hPins l Z a (B.T u) i hi bad (K (chOf c)).lev P v hv
  obtain ⟨x, hx, hxoff, hxv⟩ := exists_put _ _ v κ hκ
  obtain ⟨kk, hkk⟩ : ∃ kk : GL (Fin ((I.rec7 l Z).R.N i)) (TensorProduct (I.rec7 l Z).host.F (I.rec7 l Z).host.E (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)), kk = k (chOf c) := ⟨_, rfl⟩
  obtain ⟨z, hz, hzoff, hzN, g', hg', hgg', hpt⟩ := GlobalTheory.T.deepElement_conj_rational_at_badPrime I hOk hPins l Z a i hi kk fb (hkk ▸ hfb) P v hv κ hκ g hg hF x hx hxv N
  obtain ⟨κ', hK, hLP, hLo⟩ := hL g' hg' hgg'
  have hxz : x * z ∈ UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F) := mul_mem hx hz
  have hxzoff : ∀ v', v' ≠ v → bc (prV (E := (I.rec7 l Z).host.E) v') (x * z) = 1 := fun v' hv' => by
    rw [map_mul, hxoff v' hv', hzoff v' hv', mul_one]
  have hpt' : ∀ r s, adAt (I.rec7 l Z).host.F (GlobalTheory.TwU.seamP (sm I l Z) P.1) ((kk⁻¹ * (x * z) * kk).1 r s) = algebraMap (I.rec7 l Z).host.E ((GlobalTheory.TwU.seamP (sm I l Z) P.1).adicCompletion (I.rec7 l Z).host.E) ((GlobalTheory.TwU.seamGL (sm I l Z) g').1 r s) := hpt
  have hq := GlobalTheory.T.representative_image_point_of_lift I hOk hPins l Z u a i hi bad Ch chOf K k hR c kk hkk P v hv (x * z) hxz hxzoff g' hg' hpt' κ' hK hLP hLo
  subst hkk
  have hxzU : x * z ∈ (K (chOf c)).lev.U := (hR.lev c (x * z) _ hq).2 ⟨κ', hK.1, rfl, hK.2⟩
  have hzU : z ∈ (K (chOf c)).lev.U := hN z hz hzoff hzN
  have hxU : x ∈ (K (chOf c)).lev.U := by
    have := mul_mem hxzU (inv_mem hzU)
    rwa [mul_inv_cancel_right] at this
  have := (((K (chOf c)).lev.U_eq x).1 hxU).2 v
  rwa [hxv] at this

end GlobalTheory.Mem.Col2.AdT.LevGe

end
