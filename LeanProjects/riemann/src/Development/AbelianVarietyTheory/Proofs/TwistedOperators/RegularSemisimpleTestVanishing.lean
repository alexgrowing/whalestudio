import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointRadical
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotientMeasureFibrationStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeightedOrbitalIntegralTypeTestVanishStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviIdempotentSplittingStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCyclicOfFiniteQuotient
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp

noncomputable section

namespace GlobalTheory.TypesFactor

section Split

variable {ι : Type} [DecidableEq ι] (i : ι) (G : ι → Type) [∀ j, Group (G j)] [∀ j, TopologicalSpace (G j)]

def splitEquiv : (∀ j, G j) ≃ₜ* G i × ∀ j : {j // j ≠ i}, G j :=
  { Homeomorph.piSplitAt i G with map_mul' := fun _ _ => rfl }

variable {i G}

theorem splitEquiv_apply (x : ∀ j, G j) : splitEquiv i G x = (x i, fun j : {j // j ≠ i} => x j) := rfl

theorem splitEquiv_symm_self (a : G i) (b : ∀ j : {j // j ≠ i}, G j) : (splitEquiv i G).symm (a, b) i = a :=
  congrArg Prod.fst ((splitEquiv i G).apply_symm_apply (a, b))

theorem splitEquiv_symm_ne (a : G i) (b : ∀ j : {j // j ≠ i}, G j) (j : {j // j ≠ i}) :
    (splitEquiv i G).symm (a, b) j = b j :=
  congrFun (congrArg Prod.snd ((splitEquiv i G).apply_symm_apply (a, b))) j

theorem splitEquiv_symm_one (a : G i) : (splitEquiv i G).symm (a, 1) = Pi.mulSingle i a := by
  apply (splitEquiv i G).injective
  rw [ContinuousMulEquiv.apply_symm_apply, splitEquiv_apply]
  exact Prod.ext (Pi.mulSingle_eq_same i a).symm (funext fun j => (Pi.mulSingle_eq_of_ne j.2 a).symm)

theorem splitEquiv_symm_mem_cent (g : ∀ j, G j) (a : G i) (b : ∀ j : {j // j ≠ i}, G j) :
    (splitEquiv i G).symm (a, b) ∈ cent g ↔ a ∈ cent (g i) ∧ b ∈ cent (fun j : {j // j ≠ i} => g j) := by
  simp only [mem_cent]
  rw [← (splitEquiv i G).injective.eq_iff, map_mul, map_mul, ContinuousMulEquiv.apply_symm_apply, splitEquiv_apply]
  exact Prod.ext_iff

end Split

theorem mem_cent_pi {ι : Type} {G : ι → Type} [∀ j, Group (G j)] {g x : ∀ j, G j} :
    x ∈ cent g ↔ ∀ j, x j ∈ cent (g j) :=
  ⟨fun h j => mem_cent.2 (congrFun (mem_cent.1 h) j), fun h => mem_cent.2 (funext fun j => mem_cent.1 (h j))⟩

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
  (J : Matrix (Fin n) (Fin n) E)

theorem embAt_mem_cent {S : Finset (HeightOneSpectrum (𝓞 F))} {g : GAd σ J} {x : ∀ v : S, GLoc σ J v}
    (hx : x ∈ cent (projAt σ J S g)) : embAt σ J S x ∈ cent g := by
  have hm := mem_atPts.1 (embAt_mem σ J S x)
  refine mem_cent.2 (GAd_ext σ J (fun w => ?_) fun v => ?_)
  · simp only [map_mul, mem_finPts_iff_forall.1 hm.1 w, one_mul, mul_one]
  · by_cases hv : v ∈ S
    · have h := congrFun (mem_cent.1 hx) ⟨v, hv⟩
      rw [map_mul, map_mul, show proj σ J v (embAt σ J S x) = x ⟨v, hv⟩ from proj_embAt σ J S x ⟨v, hv⟩]
      exact h
    · simp only [map_mul, hm.2 v hv, one_mul, mul_one]

theorem isMulCommutative_cent_projAt (S : Finset (HeightOneSpectrum (𝓞 F))) {γ : GRat σ J} (hγ : IsRegSS γ.1.1) :
    IsMulCommutative (cent (projAt σ J S (ratEmb σ J γ))) :=
  ⟨⟨fun a b => Subtype.ext (funext fun v => by
    have hc := isMulCommutative_cent_HA (isRegSS_proj_ratEmb hγ v)
    exact congrArg Subtype.val (hc.1.1 ⟨a.1 v, mem_cent_pi.1 a.2 v⟩ ⟨b.1 v, mem_cent_pi.1 b.2 v⟩))⟩⟩

theorem leftInv_integrand (S : Finset (HeightOneSpectrum (𝓞 F))) {g : GAd σ J} (ff : ∀ v, GLoc σ J v → ℂ)
    {C : GAd σ J → ℂ} (hCi : LeftInv (cent g) C) :
    LeftInv (cent (projAt σ J S g)) fun x => C (embAt σ J S x) * ∏ v : S, ff v ((x v)⁻¹ * proj σ J v g * x v) := by
  intro t ht x
  simp only [map_mul, Pi.mul_apply]
  rw [hCi _ (embAt_mem_cent σ J ht)]
  congr 1
  refine Finset.prod_congr rfl fun v _ => congrArg (ff v) ?_
  have hc : t v * proj σ J v g = proj σ J v g * t v := mem_cent.1 (mem_cent_pi.1 ht v)
  have e : (t v * x v)⁻¹ * proj σ J v g * (t v * x v) = (x v)⁻¹ * ((t v)⁻¹ * (proj σ J v g * t v)) * x v := by group
  rw [e, ← hc, inv_mul_cancel_left]

theorem integrable_integrand (h : IsCMExt F E σ) (hJ : IsHermND σ J) (S : Finset (HeightOneSpectrum (𝓞 F)))
    {γ : GRat σ J} (hγ : IsRegSS γ.1.1) (ff : ∀ v, GLoc σ J v → ℂ) (hc : ∀ v : S, Continuous (ff v))
    (hs : ∀ v : S, HasCompactSupport (ff v)) {C : GAd σ J → ℂ} (hC : Continuous C)
    (hCi : LeftInv (cent (ratEmb σ J γ)) C) (dg : Measure (∀ v : S, GLoc σ J v)) [dg.IsHaarMeasure]
    (dt : Measure (cent (projAt σ J S (ratEmb σ J γ)))) [dt.IsHaarMeasure] :
    Integrable (descend (cent (projAt σ J S (ratEmb σ J γ)))
      fun x => C (embAt σ J S x) * ∏ v : S, ff v ((x v)⁻¹ * proj σ J v (ratEmb σ J γ) * x v))
      (quotMeas _ dt dg) := by
  haveI : LocallyCompactSpace (∀ v : S, GLoc σ J v) := Pi.locallyCompactSpace_of_finite
  haveI := isMulRightInvariant_cent (isMulCommutative_cent_projAt σ J S hγ) dt
  have hp : ∀ v : S, IsProperOrbit (cent (proj σ J v (ratEmb σ J γ))) (proj σ J v (ratEmb σ J γ)) :=
    fun v => isProperOrbit_GLoc h hJ (isRegSS_proj_ratEmb hγ v)
  choose K hK hK' using fun v : S => hp v _ (hs v).isCompact
  refine integrable_descend (isClosed_cent _) (leftInv_integrand σ J S ff hCi)
    ((hC.comp (continuous_embAt σ J S)).mul (continuous_finset_prod _ fun v _ =>
      (hc v).comp ((((continuous_apply v).inv).mul continuous_const).mul (continuous_apply v))))
    (isCompact_univ_pi hK) fun x hx => ?_
  have h1 : ∀ v : S, (x v)⁻¹ * proj σ J v (ratEmb σ J γ) * x v ∈ tsupport (ff v) := fun v =>
    subset_tsupport _ (Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul hx) v (Finset.mem_univ _))
  choose t ht ht' using fun v => hK' v (x v) (h1 v)
  exact ⟨t, mem_cent_pi.2 ht, fun v _ => ht' v⟩

end Gen

end GlobalTheory.TypesFactor

namespace GlobalTheory.TypesFactor
section Gen2
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
  (J : Matrix (Fin n) (Fin n) E)

def splitAt (S : Finset (HeightOneSpectrum (𝓞 F))) [DecidableEq S] (v₀ : S) :
    GLoc σ J v₀ × (∀ j : {j : S // j ≠ v₀}, GLoc σ J j) ≃ₜ* ∀ v : S, GLoc σ J v :=
  (splitEquiv v₀ fun v : S => GLoc σ J v).symm

variable {σ J}

theorem splitAt_self {S : Finset (HeightOneSpectrum (𝓞 F))} [DecidableEq S] {v₀ : S} (a : GLoc σ J v₀)
    (b : ∀ j : {j : S // j ≠ v₀}, GLoc σ J j) : splitAt σ J S v₀ (a, b) v₀ = a :=
  splitEquiv_symm_self (G := fun v : S => GLoc σ J v) a b

theorem splitAt_ne {S : Finset (HeightOneSpectrum (𝓞 F))} [DecidableEq S] {v₀ : S} (a : GLoc σ J v₀)
    (b : ∀ j : {j : S // j ≠ v₀}, GLoc σ J j) (j : {j : S // j ≠ v₀}) : splitAt σ J S v₀ (a, b) j = b j :=
  splitEquiv_symm_ne (G := fun v : S => GLoc σ J v) a b j

theorem splitAt_one {S : Finset (HeightOneSpectrum (𝓞 F))} [DecidableEq S] {v₀ : S} (a : GLoc σ J v₀) :
    splitAt σ J S v₀ (a, 1) = Pi.mulSingle v₀ a :=
  splitEquiv_symm_one (G := fun v : S => GLoc σ J v) a

theorem splitAt_mem_cent {S : Finset (HeightOneSpectrum (𝓞 F))} [DecidableEq S] {v₀ : S} (g : ∀ v : S, GLoc σ J v)
    (a : GLoc σ J v₀) (b : ∀ j : {j : S // j ≠ v₀}, GLoc σ J j) :
    splitAt σ J S v₀ (a, b) ∈ cent g ↔ a ∈ cent (g v₀) ∧ b ∈ cent (fun j : {j : S // j ≠ v₀} => g j) :=
  splitEquiv_symm_mem_cent (G := fun v : S => GLoc σ J v) g a b

end Gen2
end GlobalTheory.TypesFactor

namespace GlobalTheory.TypesFactor
section Gen3
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E}

theorem quotInt_const_mul {H : Type} [Group H] [MeasurableSpace H] (T : Subgroup H) (dt : Measure T) (dh : Measure H)
    (c : ℂ) (f : H → ℂ) : quotInt T dt dh (fun x => c * f x) = c * quotInt T dt dh f := by
  simp only [quotInt, GlobalTheory.AutomorphicL2Unitary.descend]
  exact integral_const_mul _ _

theorem hasQuotInt_integrand_zero (h : IsCMExt F E σ) (hJ : IsHermND σ J) (S : Finset (HeightOneSpectrum (𝓞 F)))
    [DecidableEq S] (v₀ : S) {γ : GRat σ J} (hγ : IsRegSS γ.1.1) (ff : ∀ v, GLoc σ J v → ℂ)
    (hc : ∀ v : S, Continuous (ff v)) (hs : ∀ v : S, HasCompactSupport (ff v)) (μ : Measure (GLoc σ J v₀))
    [μ.IsHaarMeasure] {C : GAd σ J → ℂ} (hC : Continuous C) (hCi : LeftInv (cent (ratEmb σ J γ)) C)
    (P : GLoc σ J v₀ → Prop) (hCP : ∀ g, P g → ∀ y, C (emb σ J v₀ g * y) = C y)
    (hloc : ∀ bf : GLoc σ J v₀ → ℂ, Continuous bf → LeftInv (cent (proj σ J v₀ (ratEmb σ J γ))) bf →
      (∀ g, P g → ∀ x, bf (g * x) = bf x) → ∀ (ds : Measure (cent (proj σ J v₀ (ratEmb σ J γ)))) [ds.IsHaarMeasure],
      quotInt (cent (proj σ J v₀ (ratEmb σ J γ))) ds μ
        (fun a => bf a * ff v₀ (a⁻¹ * proj σ J v₀ (ratEmb σ J γ) * a)) = 0)
    (dg : Measure (∀ v : S, GLoc σ J v)) [dg.IsHaarMeasure]
    (dt : Measure (cent (projAt σ J S (ratEmb σ J γ)))) [dt.IsHaarMeasure] :
    HasQuotInt (cent (projAt σ J S (ratEmb σ J γ))) dt dg
      (fun x => C (embAt σ J S x) * ∏ v : S, ff v ((x v)⁻¹ * proj σ J v (ratEmb σ J γ) * x v)) 0 := by
  have hint := integrable_integrand σ J h hJ S hγ ff hc hs hC hCi dg dt
  refine ⟨hint, ?_⟩
  haveI : LocallyCompactSpace (∀ v : S, GLoc σ J v) := Pi.locallyCompactSpace_of_finite
  haveI : LocallyCompactSpace (∀ j : {j : S // j ≠ v₀}, GLoc σ J j) := Pi.locallyCompactSpace_of_finite
  haveI : LocallyCompactSpace (cent (proj σ J v₀ (ratEmb σ J γ))) := (isClosed_cent _).locallyCompactSpace
  refine GlobalTheory.T.quotient_measure_fibration (GLoc σ J v₀) (∀ j : {j : S // j ≠ v₀}, GLoc σ J j) (∀ v : S, GLoc σ J v) (splitAt σ J S v₀)
    (cent (proj σ J v₀ (ratEmb σ J γ))) (cent (fun j : {j : S // j ≠ v₀} => proj σ J j (ratEmb σ J γ))) (cent (projAt σ J S (ratEmb σ J γ)))
    (fun a b => splitAt_mem_cent (projAt σ J S (ratEmb σ J γ)) a b) (isClosed_cent _) (isMulCommutative_cent_projAt σ J S hγ)
    dg dt μ Measure.haar _ (leftInv_integrand σ J S ff hCi) hint fun b => ?_
  set e := splitAt σ J S v₀
  have hsplit : (fun a => C (embAt σ J S (e (a, b))) *
      ∏ v : S, ff v ((e (a, b) v)⁻¹ * proj σ J v (ratEmb σ J γ) * e (a, b) v)) =
      fun a => (∏ j : {j : S // j ≠ v₀}, ff j ((b j)⁻¹ * proj σ J j (ratEmb σ J γ) * b j)) *
        (C (embAt σ J S (e (a, b))) * ff v₀ (a⁻¹ * proj σ J v₀ (ratEmb σ J γ) * a)) := by
    funext a
    rw [Fintype.prod_eq_mul_prod_subtype_ne _ v₀]
    simp only [e, splitAt_self, splitAt_ne]
    ring
  have hmul : ∀ a a' : GLoc σ J v₀, e (a * a', b) = e (a, 1) * e (a', b) := fun a a' => by
    rw [← map_mul, Prod.mk_mul_mk, one_mul]
  refine (congrArg _ hsplit).trans ((quotInt_const_mul _ _ _ _ _).trans ?_)
  rw [hloc (fun a => C (embAt σ J S (e (a, b))))
    (hC.comp ((continuous_embAt σ J S).comp (e.continuous.comp (continuous_id.prodMk continuous_const))))
    (fun t ht a => by
      change C (embAt σ J S (e (t * a, b))) = C (embAt σ J S (e (a, b)))
      rw [hmul, map_mul, hCi _ (embAt_mem_cent σ J ((splitAt_mem_cent (projAt σ J S (ratEmb σ J γ)) t 1).2 ⟨ht, one_mem _⟩))])
    (fun g hg x => by
      change C (embAt σ J S (e (g * x, b))) = C (embAt σ J S (e (x, b)))
      rw [hmul, map_mul, show e (g, 1) = Pi.mulSingle v₀ g from splitAt_one g, embAt_mulSingle]
      exact hCP g hg _) Measure.haar, mul_zero]

end Gen3
end GlobalTheory.TypesFactor

namespace GlobalTheory.TypesFactor

theorem typesFactor_vanish : GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.TypeConstTermVanish → ∀ (D : D7) (V : HSp D) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), IsTestFin T U μf ff → (∀ v, (μf v).IsHaarMeasure) → GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.HypH (k := fun v : T.S => ResF v.1) T.τ → ∀ (Φ : WittFrame V) (u : SV (wittIndex V)) (γ : GF V), u ≠ 0 → IsRegSS γ.1.1 → rat V γ ∈ Φ.levi D.sp.cm (AF D.host.F) {u} → ∀ C : GA D V → ℂ, Continuous C → LeftInv (cent (rat V γ)) C → (∀ hW : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.IsIsotropic V (Φ.sub u), LeftInv (NA (IsoFlag.single hW)) C) → ∀ (dg : Measure (∀ v : T.S, GLoc D.sp.cm.sig V.gram v)) [dg.IsHaarMeasure] (dt : Measure (cent (projAt D.sp.cm.sig V.gram T.S (rat V γ)))) [dt.IsHaarMeasure], HasQuotInt (cent (projAt D.sp.cm.sig V.gram T.S (rat V γ))) dt dg (fun x => C (embAt D.sp.cm.sig V.gram T.S x) * ∏ v : T.S, ff v ((x v)⁻¹ * proj D.sp.cm.sig V.gram v (rat V γ) * x v)) 0 := by
  intro hTC D V T U μf ff hff hHaar hH Φ u γ hu hγ hlevi C hC hCi hCN dg _ dt _
  classical
  obtain ⟨ε, hW, hε2, hεpos, hεlt, hεγ, hεN⟩ := GlobalTheory.T.levi_idempotent_splitting D V Φ u hu
  obtain ⟨v₀, hv₀⟩ := hH ε.rank hεpos hεlt
  have hfin := hff.isFinFamily.1
  exact hasQuotInt_integrand_zero (isCMExt_host D) (isHermND_gram V) T.S v₀ hγ ff
    (fun v => (hfin v).1.continuous) (fun v => (hfin v).2) (μf v₀) hC hCi
    (fun g => ε.map (T.frame v₀).emb * ((splitHom D.sp.cm.sig V.gram (T.frame v₀).emb g).1 - 1) *
      (1 - ε.map (T.frame v₀).emb) = (splitHom D.sp.cm.sig V.gram (T.frame v₀).emb g).1 - 1)
    (fun g hg y => hCN hW _ (hεN v₀ (T.frame v₀).emb g hg) y)
    (fun bf hbc hbi hbn ds _ => (GlobalTheory.T.weightedOrbitalIntegral_typeTest_vanish hTC D V T U μf ff hff v₀ (hHaar v₀) γ ε hγ hε2 (hεγ γ hlevi) hεpos hεlt
      hv₀ bf hbc hbi hbn ds).2) dg dt

end GlobalTheory.TypesFactor
