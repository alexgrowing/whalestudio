import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCharEqValZpow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateGroupPointsInjectiveMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateTorsionPointCompatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateCurvePointAdditionCompatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticMapUniformizationLineStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLineOneParameterHomomorphismStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentCoprimeAtGoodPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneHermitianIdealCoprimeLtStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneSkewIdealCoprimeLtStatement

noncomputable section
namespace GlobalTheory.UnrEuler
open NumberField IsDedekindDomain GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped nonZeroDivisors
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem glob (σ : E →ₐ[F] E) (B : Base F E) {b a' : ℕ} (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b)
    (H' : Plane E (b + 2 + a') (b + a')) (hC : CfgA B G G₁ H H') (X : Chars F E) (om : Rep σ G.V G.W)
    (om' : Rep σ G.V' G.W) (hX : IsTriple B G X om om') :
    Converges (above E (X.T : Set (Pl F))) (charFam X.ν) (((b + 2 - a') / 2 : ℕ) : ℂ) ∧
    HasProd (fun v : {v : Pl F // v ∉ (X.T : Set (Pl F))} =>
        unrFac X.ν (idA σ H.𝔟 H'.𝔟) (((b + 2 - a') / 2 : ℕ) : ℂ) v.1)
      (((idealVal X.ν H.𝔟 * idealVal X.ν H'.𝔟 : ℂˣ) : ℂ) * (nrm (idA σ H.𝔟 H'.𝔟) : ℂ) ^ (-((((b + 2 - a') / 2 : ℕ) : ℂ))) *
        charL X.ν (X.S₀ : Set (Pl F)) (((b + 2 - a') / 2 : ℕ) : ℂ)) := by
  set s : ℂ := (((b + 2 - a') / 2 : ℕ) : ℂ) with hs_def
  have hs : 1 < s.re := by
    have h1 := hX.geo.eBig
    have h2 : 1 < (b + 2 - a') / 2 := by omega
    rw [hs_def, Complex.natCast_re]
    exact_mod_cast h2
  have hTP : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ∈ (X.T : Set (Pl F)) → w.under (𝓞 F) ∈ B.P :=
    fun w hw => hX.chars.sub hw
  obtain ⟨h𝔟0, h𝔟⟩ := GlobalTheory.T.adapted_plane_hermitian_ideal_coprime_lt σ B H G.V G₁.V 0 (b + 1) _ _ hX.base hX.geo.hV hC.hH (by omega) (by omega)
  obtain ⟨h𝔠0, h𝔠⟩ := GlobalTheory.T.adapted_plane_skew_ideal_coprime_lt σ B H' G.W G₁.W 0 (b + 1) _ _ hX.base hX.geo.hW hC.hH' (by omega) (by omega)
  have hd := GlobalTheory.T.different_coprime_at_good_places σ B hX.base
  have hc0 := conjI_ne_zero σ h𝔠0
  have hbc : H.𝔟 * (conjI σ H'.𝔟)⁻¹ ≠ 0 := mul_ne_zero h𝔟0 (inv_ne_zero hc0)
  have h𝔞0 : idA σ H.𝔟 H'.𝔟 ≠ 0 := mul_ne_zero hbc (inv_ne_zero diffE_ne_zero)
  have hcount : ∀ w, FractionalIdeal.count E w (idA σ H.𝔟 H'.𝔟) =
      FractionalIdeal.count E w H.𝔟 - FractionalIdeal.count E w (conjI σ H'.𝔟) - FractionalIdeal.count E w (diffE E) := by
    intro w
    rw [idA, FractionalIdeal.count_mul E w hbc (inv_ne_zero diffE_ne_zero), FractionalIdeal.count_mul E w h𝔟0 (inv_ne_zero hc0),
      FractionalIdeal.count_inv, FractionalIdeal.count_inv]
    ring
  have hT : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ∈ (X.T : Set (Pl F)) →
      FractionalIdeal.count E w (idA σ H.𝔟 H'.𝔟) = 0 := by
    intro w hw
    obtain ⟨w', hw', hcw⟩ := GlobalTheory.T.count_conj_ideal_eq_count σ H'.𝔟 h𝔠0 w
    rw [hcount, hcw, h𝔟 _ (hTP w hw) w rfl, (h𝔠 _ (hTP w hw) w' hw'), hd _ (hTP w hw) w rfl]
    simp
  have hunr : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ∉ (X.T : Set (Pl F)) → UnrAt X.ν w := by
    intro w hw
    rw [Chars.ν, div_eq_mul_inv]
    exact (hX.chars.unrα w hw).mul (hX.chars.unrβ w hw).inv
  have htriv := nu_triv B X hX.chars hX.geo.even
  have hconj := GlobalTheory.T.idealVal_conj_inv σ hX.base.cm X.ν htriv H'.𝔟 h𝔠0
    (fun w hw => hunr w fun hwT => hw (h𝔠 _ (hTP w hwT) w rfl))
  have hdiff := GlobalTheory.T.idealVal_different_eq_one hX.base.unram X.ν htriv
    (fun w hw => hunr w fun hwT => hw (hd _ (hTP w hwT) w rfl))
  have hval : idealVal X.ν (idA σ H.𝔟 H'.𝔟) = idealVal X.ν H.𝔟 * idealVal X.ν H'.𝔟 := by
    rw [idA, idealVal_mul _ hbc (inv_ne_zero diffE_ne_zero), idealVal_mul _ h𝔟0 (inv_ne_zero hc0), idealVal_inv,
      idealVal_inv, hconj, hdiff, inv_inv, inv_one, mul_one]
  have hA := GlobalTheory.T.hecke_l_function_ideal_euler_product X.ν (X.T : Set (Pl F)) (idA σ H.𝔟 H'.𝔟) h𝔞0 hT s
  have hL := GlobalTheory.T.hecke_l_function_euler_product_convergent X.ν (X.T : Set (Pl F)) (X.S₀ : Set (Pl F))
    (by intro v hv; unfold Chars.T; classical exact Finset.mem_union_left _ hv) (fun w hw _ => hX.chars.ram w hw) s hs
  refine ⟨hL.1, ?_⟩
  have := hA.mul hL.2
  rw [hval] at this
  exact this

end GlobalTheory.UnrEuler
