import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedCharacterAtUniformizerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterOfIdeleClassStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeValueNotFiniteOrderStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPrimeDegreeOneStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

namespace GlobalTheory.NuGood

theorem not_root_of_unity : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ v, X.Good v → (∀ (t : E →ₐ[F] Fv F v) (k : ℤ), k ≠ 0 → chrW X.ν t (unifAt v) ^ k ≠ 1) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' h v hv t k hk hpow
  have hW : splitPrime t ∉ above E (X.T : Set (Pl F)) := by
    intro hmem
    exact hv.1 (by simpa [above, splitPrime_under] using hmem)
  have hunr : UnrAt X.ν (splitPrime t) := by
    rw [Chars.ν, div_eq_mul_inv]
    exact (h.chars.unrα _ hW).mul (h.chars.unrβ _ hW).inv
  rw [GlobalTheory.T.unramified_character_at_uniformizer F E X.ν v t hunr] at hpow
  have hHecke : IsHecke F E X.ν := by
    refine ⟨?_, fun x => ?_⟩
    · exact (h.chars.heckeα.1.div' h.chars.heckeβ.1 :)
    · rw [Chars.ν, MonoidHom.div_apply, h.chars.heckeα.2 x, h.chars.heckeβ.2 x, div_one]
  obtain ⟨H, hloc, hinf⟩ := GlobalTheory.T.hecke_character_of_idele_class F E σ h.base.cm X.ν hHecke
  have hexp : HasExp B.emb X.ν (fun w => B.mα w - B.mβ w) := by
    intro z hz
    have h1 := h.chars.expα z hz
    have h2 := h.chars.expβ z hz
    show (((X.α z / X.β z : Circle)) : ℂ) = _
    rw [Circle.coe_div, h1, h2, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun w _ => ?_
    have hne : piInf (B.emb w) z ≠ 0 := (z.isUnit.map (piInf (B.emb w))).ne_zero
    have hne' : piInf (B.emb w) z / (‖piInf (B.emb w) z‖ : ℂ) ≠ 0 :=
      div_ne_zero hne (by exact_mod_cast (norm_ne_zero_iff.2 hne))
    rw [zpow_sub₀ hne']
  have hval : val X.ν (splitPrime t) = H.val (splitPrime t) := (hloc _ _).symm
  obtain ⟨p, hp, hN, hsq⟩ := GlobalTheory.T.split_prime_degree_one F E (splitPrime t) (by rw [splitPrime_under]; exact hv.2)
  refine GlobalTheory.T.hecke_value_not_finite_order F E σ h.base.cm h.base.galois B.emb H _ (hinf _ _ hexp) (fun w => ?_) p hp _ hN hsq ?_
  · have := h.geo.kappa w
    omega
  · rw [← hval]
    exact isOfFinOrder_iff_zpow_eq_one.2 ⟨k, hk, hpow⟩

end GlobalTheory.NuGood
