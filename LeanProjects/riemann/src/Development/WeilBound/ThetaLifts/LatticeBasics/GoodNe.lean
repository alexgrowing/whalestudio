import Mathlib
import Development.WeilBound.ThetaLifts.LatticeBasics.PairsStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceSplitOrInert
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedCharacterAtUniformizer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterOfIdeleClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeValueNotFiniteOrder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPrimeDegreeOne

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {B : Base F E}
  {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

theorem isHecke_nu (h : IsTriple B G X om om') : IsHecke F E X.ν :=
  ⟨(h.chars.heckeα.1.div' h.chars.heckeβ.1 :), fun x => by
    rw [Chars.ν, MonoidHom.div_apply, h.chars.heckeα.2 x, h.chars.heckeβ.2 x, div_one]⟩

theorem hasExp_nu (h : IsTriple B G X om om') : HasExp B.emb X.ν (fun w => B.mα w - B.mβ w) := by
  intro z hz
  show (((X.α z / X.β z : Circle)) : ℂ) = _
  rw [Circle.coe_div, h.chars.expα z hz, h.chars.expβ z hz, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  have hne : piInf (B.emb w) z ≠ 0 := (z.isUnit.map (piInf (B.emb w))).ne_zero
  rw [zpow_sub₀ (div_ne_zero hne (by exact_mod_cast (norm_ne_zero_iff.2 hne)))]

theorem nonempty_emb_of_splitsFully (hB : B.IsGood σ) {v : Pl F} (hv : SplitsFully E v) : Nonempty (E →ₐ[F] Fv F v) := by
  refine (GlobalTheory.KFinLoc.split_or_inert F E σ B hB v).resolve_right ?_
  rintro ⟨w, hw⟩
  have hw' : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = w.asIdeal := hw
  have hu : w.under (𝓞 F) = v := (HeightOneSpectrum.ext (v.isMaximal.eq_of_le (w.under (𝓞 F)).isPrime.ne_top
    (Ideal.map_le_iff_le_comap.1 hw'.le))).symm
  obtain ⟨p, hp, hN, -⟩ := GlobalTheory.SplitFullyNorm.exists_prime_absNorm_eq_of_splitsFully F E w (hu ▸ hv)
  rw [← hw', Ideal.absNorm_algebraMap, ← Algebra.IsAlgebraic.finrank_of_isFractionRing (𝓞 F) F (𝓞 E) E, hB.cm.2.2.1] at hN
  exact Nat.Prime.not_prime_pow le_rfl (hN ▸ hp)

theorem nu_pow_ne_one (h : IsTriple B G X om om') {v : Pl F} (hv : X.Good v) (t : E →ₐ[F] Fv F v) {k : ℤ} (hk : k ≠ 0) :
    chrW X.ν t (unifAt v) ^ k ≠ 1 := by
  intro hpow
  have hW : splitPrime t ∉ above E (X.T : Set (Pl F)) := fun hmem => hv.1 (by simpa [above, splitPrime_under] using hmem)
  have hunr : UnrAt X.ν (splitPrime t) := by
    rw [Chars.ν, div_eq_mul_inv]
    exact (h.chars.unrα _ hW).mul (h.chars.unrβ _ hW).inv
  rw [GlobalTheory.ChrWUnif.chrW_unifAt F E X.ν v t hunr] at hpow
  obtain ⟨H, hloc, hinf⟩ := GlobalTheory.HeckeBridge.exists_hchar F E σ h.base.cm X.ν (isHecke_nu h)
  have hval : val X.ν (splitPrime t) = H.val (splitPrime t) := (hloc _ _).symm
  obtain ⟨p, hp, hN, hsq⟩ := GlobalTheory.SplitFullyNorm.exists_prime_absNorm_eq_of_splitsFully F E (splitPrime t)
    (by rw [splitPrime_under]; exact hv.2)
  refine GlobalTheory.CMSplitValue.not_isOfFinOrder_val F E σ h.base.cm h.base.galois B.emb H _ (hinf _ _ (hasExp_nu h))
    (fun w => ?_) p hp _ hN hsq ?_
  · have := h.geo.kappa w
    omega
  · rw [← hval]
    exact isOfFinOrder_iff_zpow_eq_one.2 ⟨k, hk, hpow⟩

theorem goodNe : GoodNe := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h _ hv =>
  ⟨nonempty_emb_of_splitsFully h.base hv.2, fun t e => nu_pow_ne_one h hv t one_ne_zero (by rw [e, zpow_one])⟩

end GlobalTheory.ThK.Dbl

end
