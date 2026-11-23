import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DecayNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawTypeASchwartzTripleIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawTypeASchwartzTripleSecondStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawTypeASchwartzTripleThirdStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.PureBound

theorem size_inf {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (x : AE F E) :
    GlobalTheory.IdeleDecay.size F E ((pairA F 1 0 : AF F) • x) = GlobalTheory.IdeleDecay.size F E x := by
  unfold GlobalTheory.IdeleDecay.size GlobalTheory.IdeleDecay.coord
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearEquiv.map_smul, Pi.smul_apply, smul_eq_mul]
  have h1 : ∀ z : AF F, (pairA F 1 0 * z).1 = z.1 := fun z => one_mul z.1
  unfold evI
  rw [h1]

theorem norm_ev_shiftA_pure_le : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ g ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → FiniteAdeleRing (𝓞 F) F), ∀ S : Set (SInf F (Fin (b + 2) × Fin (b + 2 + a'))),
      IsCompact S → ∃ m : ℕ, 0 < m ∧ ∀ N : ℕ, ∃ C : ℝ, ∀ f ∈ S, ∀ (l : (AE F E)ˣ) (y : Fin b × Fin (b + a') → AF F),
        ‖e (G.M.co.rho B.ψ (shiftA H H' l) (pureA F f g)) y‖ ≤ C * GlobalTheory.IdeleDecay.decay F E N m l := by
  intro hKP F E _ _ _ _ _ σ B b a' G G₁ H H' hC e he X om om' om₁ om₁' hT hT₁ g hg S hS
  obtain ⟨m, hm, hA⟩ := GlobalTheory.T.seesaw_type_a_schwartz_triple_identity hKP F E σ B b a' G G₁ H H' hC e he X om om' om₁ om₁' hT hT₁ g hg
  refine ⟨m, hm, fun N => ?_⟩
  obtain ⟨r, gs, hgs, hB⟩ := GlobalTheory.T.seesaw_type_a_schwartz_triple_second hKP F E σ B b a' G G₁ H H' hC e he X om om' om₁ om₁' hT hT₁ g hg m hm
  choose C hCb using fun j : Fin r => GlobalTheory.T.seesaw_type_a_schwartz_triple_third hKP F E σ B b a' G G₁ H H' hC e he X om om' om₁ om₁' hT hT₁ (gs j) (hgs j) S hS N
  refine ⟨∑ j, |C j|, fun f hf l y => ?_⟩
  unfold GlobalTheory.IdeleDecay.decay
  split_ifs with hl
  · obtain ⟨j, hj⟩ := hB l hl
    rw [hj f]
    have hid : (pairA F 1 0 : AF F) • ((pairA F 1 0 : AF F) • l.1) = (pairA F 1 0 : AF F) • l.1 := by
      rw [smul_smul]
      congr 1
      show ((1 : Ainf F) * 1, (0 : Af F) * 0) = ((1 : Ainf F), (0 : Af F))
      simp
    have h1 := hCb j f hf _ hid y
    rw [size_inf] at h1
    refine h1.trans (mul_le_mul_of_nonneg_right ((le_abs_self _).trans ?_) ?_)
    · exact Finset.single_le_sum (f := fun j => |C j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    · exact inv_nonneg.mpr (pow_nonneg (add_nonneg zero_le_one (GlobalTheory.IdeleDecay.size_nonneg _)) _)
  · rw [hA l hl f y, norm_zero, mul_zero]

end GlobalTheory.PureBound
