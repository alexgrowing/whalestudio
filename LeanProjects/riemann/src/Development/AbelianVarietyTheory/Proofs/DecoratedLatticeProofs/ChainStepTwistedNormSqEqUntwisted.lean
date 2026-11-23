import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaChainStepVectorLocalPureTensor
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PureTensorInnerProductEqFinprodLocalInnerProduct
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitIdempotentPrimeProjectionCorrespondence
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DegreeOnePrimeReductionSplitPlaceDictionary
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormSqThetaLocalDatumAtTwistPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeIdealIsUnitSplitPlaceStatement
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.StepExactNS
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl IsBase onHalf phiQ rdQ)

open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (ipO Place IsBaseOff)

noncomputable section

namespace GlobalTheory.TwistNorm

theorem level_trivial_eq_ofLocal {E : Type} [Field E] [NumberField E] (Pg : Finset (Pl E)) (r : ℕ) :
    LevelP.triv Pg r ℂ = LevelP.ofLocal (fun _ => ⊥) (fun _ => 1) := by
  have hH : (Subgroup.pi Set.univ fun PP : ↥Pg => (⊥ : Subgroup (GL (Fin r) (kP PP.1)))) = ⊥ := by
    ext g
    simp [Subgroup.mem_pi, funext_iff]
  haveI : Subsingleton (↥(⊥ : Subgroup (G0 Pg r)) →* ℂˣ) :=
    ⟨fun f g => MonoidHom.ext fun y => by rw [Subsingleton.elim y 1, map_one, map_one]⟩
  unfold LevelP.triv LevelP.ofLocal
  congr 1
  · exact hH.symm
  · exact Subsingleton.helim (congrArg (fun H : Subgroup (G0 Pg r) => (↥H →* ℂˣ)) hH.symm) _ _

theorem norm_sq_eq_inner_product {D : D7} {S T : HSp D} (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) (g : WO S T → ℂ) :
    ((nrm2 μ 𝓕 g : ℝ) : ℂ) = ipO μ 𝓕 g g := by
  unfold nrm2 ipO
  rw [← integral_complex_ofReal]
  congr 1
  funext w
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem chainStep_twisted_normSq_eq_untwisted_mul_localFactors : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (f₀ : WO S T → ℂ) (m : Measure (WO S T)) (X : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) m X → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (r t j t' : ℕ) (hr : r ≤ S.rank), S.rank + t' = T.rank → ∀ (Pg Q : Finset (Pl D.host.E)), Disjoint Pg Q → (∀ PP ∈ Q, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (χj ξ ξ' : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (f f' : WO S T → ℂ), IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT (Lev.datY S.rank r t j hr Pg Q (LevelP.triv _ _ _) χ ξ Lev.Frm.B) χj Q ξ f₀ f → IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT (Lev.datY S.rank r t j hr Pg ∅ (LevelP.triv _ _ _) χ ξ' Lev.Frm.B) χj ∅ ξ' f₀ f' → nrm2 m X f = nrm2 m X f' * ∏ PP ∈ Q, (zinv PP 0 r * ((Ideal.absNorm PP.asIdeal : ℝ) ^ (r * (T.rank - r)))⁻¹) := by
  classical
  intro D ψ θ S T sS sT ΛS ΛT βS βT f₀ m X hB hC hFS hFT r t j t' hr ht Pg Q hdisj hQ2 χ χj ξ ξ' f f' hf hf'
  have hP : (Lev.datY S.rank r t j hr Pg Q (LevelP.triv _ _ _) χ ξ Lev.Frm.B).P =
      LevelP.ofLocal (Pg := Pg) (r := r) (LL := ℂ) (fun _ => ⊥) (fun _ => 1) := by
    show (if Lev.Frm.B = Lev.Frm.B then LevelP.triv Pg r ℂ else (LevelP.triv Pg r ℂ).conj) = _
    rw [if_pos rfl]
    exact level_trivial_eq_ofLocal Pg r
  have hP' : (Lev.datY S.rank r t j hr Pg ∅ (LevelP.triv _ _ _) χ ξ' Lev.Frm.B).P =
      LevelP.ofLocal (Pg := Pg) (r := r) (LL := ℂ) (fun _ => ⊥) (fun _ => 1) := by
    show (if Lev.Frm.B = Lev.Frm.B then LevelP.triv Pg r ℂ else (LevelP.triv Pg r ℂ).conj) = _
    rw [if_pos rfl]
    exact level_trivial_eq_ofLocal Pg r
  obtain ⟨⟨x, hx⟩, hall⟩ := GlobalTheory.StepVec.stepVecLocal D ψ θ S T sS sT ΛS ΛT βS βT _ χj Q ξ f₀ f m X t' ht _ _ hP hB hC
    hFS hFT hdisj hf
  have hall' := (GlobalTheory.StepVec.stepVecLocal D ψ θ S T sS sT ΛS ΛT βS βT _ χj ∅ ξ' f₀ f' m X t' ht _ _ hP' hB hC hFS hFT
    (Finset.disjoint_empty_right _) hf').2
  obtain ⟨hvac, e, ⟨⟨es, hes, rfl⟩, hce⟩, -⟩ := hf
  have hes' : ∀ PP ∈ Pg ∪ Q, Formalism.L2.NTheta.IsIdemAt (es PP) PP := hes
  have hce' : (∑ PP ∈ Pg ∪ Q, es PP) * cA D (∑ PP ∈ Pg ∪ Q, es PP) = 0 := hce
  have hsum := GlobalTheory.SplitIdemDict.idem_dictionary D
  choose vA φA hφA hprA using fun i : ↥(Pg ∪ Q) => hsum.1 (es i.1) i.1 (hes' i.1 i.2)
  have hunder : ∀ i : ↥(Pg ∪ Q), (i.1).asIdeal.under (𝓞 D.host.F) = (vA i).asIdeal := fun i =>
    (hsum.2 _ _ _ (hprA i)).1
  have hcross := GlobalTheory.PlaceDatum.cross_eq_zero (R := AE D) GlobalTheory.PlaceDatum.isUnit_natCast (cA D) es (Pg ∪ Q)
    (fun i hi => (hes' i hi).1.1) hce'
  have hinj : Function.Injective vA := by
    intro i j hij
    have h1 := (hφA i).2.1
    have h2 := (hφA j).2.1
    rw [hij] at h1
    have h3 := GlobalTheory.PlaceDatum.idempotent_eq_of_orthogonal_decomp (hes' i.1 i.2).1.1 (hes' i.1 i.2).1.2.1 (hes' j.1 j.2).1.1
      (hes' j.1 j.2).1.2.1 (h1.trans h2.symm) (hcross _ i.2 _ j.2) (hcross _ j.2 _ i.2)
    exact Subtype.ext (GlobalTheory.StepVec.prime_eq_of_idem (hes' i.1 i.2) (h3 ▸ hes' j.1 j.2))

  obtain ⟨x', hx'l, hx'r⟩ : ∃ x' : Place D → WO S T → ℂ, (∀ τ, x' (.inr τ) = f₀) ∧
      ∀ v, x' (.inl v) = if ∃ PP ∈ Pg, PP.asIdeal.under (𝓞 D.host.F) = v.asIdeal then x (.inl v) else f₀ :=
    ⟨Sum.elim (fun v => if ∃ PP ∈ Pg, PP.asIdeal.under (𝓞 D.host.F) = v.asIdeal then x (.inl v) else f₀) fun _ => f₀,
      fun _ => rfl, fun _ => rfl⟩
  have hpure' := hall' x' ⟨⟨hx'l, fun v hv => by
      rw [hx'r, if_neg]
      rintro ⟨PP, h1, h2⟩
      exact hv PP (Finset.mem_union_left _ h1) h2⟩,
    fun v φ e' he' mu => ⟨fun PP hpp hmu J lam hJ => by
      have h := (hx.2 v φ e' he' mu).1 PP hpp hmu J lam hJ
      rw [hx'r, if_pos ⟨PP.1, PP.2, (hsum.2 v φ PP.1 hpp).1⟩]
      exact h, fun PP hq => by simp at hq⟩⟩
  have hpure := hall x hx
  obtain ⟨hfin, hxx⟩ := GlobalTheory.PlaceTensor.PureScalar.ip_pure_eq_finprod D ψ θ S T sS sT ΛS ΛT f₀ m X hB hC x x f f
    hpure hpure
  obtain ⟨-, hxx'⟩ := GlobalTheory.PlaceTensor.PureScalar.ip_pure_eq_finprod D ψ θ S T sS sT ΛS ΛT f₀ m X hB hC x' x' f' f'
    hpure' hpure'
  have h0 : ipO m X f₀ f₀ = 1 := by
    rw [← norm_sq_eq_inner_product, hvac.2.norm.2 (m, X) hC]
    simp

  let iq : ↥Q → ↥(Pg ∪ Q) := fun i => ⟨i.1, Finset.mem_union_right _ i.2⟩
  let U : Finset (Place D) := Q.attach.image fun i => (Sum.inl (vA (iq i)) : Place D)
  have hnotPg : ∀ i : ↥Q, ¬ ∃ PP ∈ Pg, PP.asIdeal.under (𝓞 D.host.F) = (vA (iq i)).asIdeal := by
    rintro i ⟨PP, hPP, hu⟩
    have h1 : vA ⟨PP, Finset.mem_union_left _ hPP⟩ = vA (iq i) := HeightOneSpectrum.ext ((hunder _).symm.trans hu)
    have h2 : PP = i.1 := congrArg Subtype.val (hinj h1)
    exact Finset.disjoint_left.1 hdisj hPP (by rw [h2]; exact i.2)
  have hpt : ∀ p, ipO m X (x p) (x p) =
      ipO m X (x' p) (x' p) * (if p ∈ U then ipO m X (x p) (x p) else 1) := by
    intro p
    by_cases hp : p ∈ U
    · rw [if_pos hp]
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hp
      rw [hx'r, if_neg (hnotPg i), h0, one_mul]
    · rw [if_neg hp, mul_one]
      rcases p with v | τ
      · rw [hx'r]
        by_cases hv : ∃ PP ∈ Pg, PP.asIdeal.under (𝓞 D.host.F) = v.asIdeal
        · rw [if_pos hv]
        · rw [if_neg hv]
          have hxv : x (.inl v) = f₀ := hx.1.2 v fun PP hPP hu => by
            rcases Finset.mem_union.1 hPP with h | h
            · exact hv ⟨PP, h, hu⟩
            · exact hp (Finset.mem_image.2 ⟨⟨PP, h⟩, Finset.mem_attach _ _,
                congrArg Sum.inl (HeightOneSpectrum.ext ((hunder _).symm.trans hu))⟩)
          rw [hxv]
      · rw [hx'l, hx.1.1 τ]
  let s0 : Finset (Place D) := hfin.toFinset ∪ U
  have hA : ∏ᶠ p, ipO m X (x p) (x p) = ∏ p ∈ s0, ipO m X (x p) (x p) :=
    finprod_eq_prod_of_mulSupport_subset _ fun p hp => Finset.mem_union_left _ (hfin.mem_toFinset.2 hp)
  have hA' : ∏ᶠ p, ipO m X (x' p) (x' p) = ∏ p ∈ s0, ipO m X (x' p) (x' p) := by
    refine finprod_eq_prod_of_mulSupport_subset _ fun p hp => ?_
    by_cases hU : p ∈ U
    · exact Finset.mem_union_right _ hU
    · refine Finset.mem_union_left _ (hfin.mem_toFinset.2 ?_)
      have h := hpt p
      rw [if_neg hU, mul_one] at h
      rw [Function.mem_mulSupport] at hp ⊢
      rwa [h]
  have hsplit : ∏ p ∈ s0, ipO m X (x p) (x p) =
      (∏ p ∈ s0, ipO m X (x' p) (x' p)) * ∏ p ∈ U, ipO m X (x p) (x p) := by
    rw [Finset.prod_congr rfl fun p _ => hpt p, Finset.prod_mul_distrib, Finset.prod_ite_mem,
      Finset.inter_eq_right.2 Finset.subset_union_right]
  have hU : ∏ p ∈ U, ipO m X (x p) (x p) = ∏ i ∈ Q.attach, ipO m X (x (.inl (vA (iq i)))) (x (.inl (vA (iq i)))) := by
    refine Finset.prod_image fun i _ j _ h => ?_
    have h1 := hinj (Sum.inl_injective h)
    have h2 : (iq i).1 = (iq j).1 := congrArg Subtype.val h1
    exact Subtype.ext h2
  have hloc : ∀ i : ↥Q, ipO m X (x (.inl (vA (iq i)))) (x (.inl (vA (iq i)))) =
      ((zinv i.1 0 r * ((Ideal.absNorm i.1.asIdeal : ℝ) ^ (r * (T.rank - r)))⁻¹ : ℝ) : ℂ) := by
    intro i
    obtain ⟨mu, hmu⟩ := (GlobalTheory.PlaceRed.red_dict D (vA (iq i)) (φA (iq i)) i.1 (hprA (iq i))).2 (ξ i.1)⁻¹
    have hθ := (hx.2 (vA (iq i)) (φA (iq i)) (es i.1) (hφA (iq i)) mu).2 i.1 i.2 (hprA (iq i)) hmu
    rw [← norm_sq_eq_inner_product, GlobalTheory.T.normSq_thetaLocalDatum_at_twistPlace D ψ θ S T sS sT ΛS ΛT βS βT f₀ m X hB hC hFS hFT i.1 (vA (iq i)) (φA (iq i)) (es i.1)
      (hφA (iq i)) (hprA (iq i)) (GlobalTheory.T.homLatticeIdeal_isUnit_splitPlace D i.1 (hQ2 i.1 i.2) (vA (iq i)) (φA (iq i)) (hprA (iq i))) r hr (by omega)
      (ξ i.1)⁻¹ mu hmu _ hθ]
  apply Complex.ofReal_injective
  rw [Complex.ofReal_mul, Complex.ofReal_prod, norm_sq_eq_inner_product, norm_sq_eq_inner_product, hxx, hxx', hA, hA', hsplit, hU,
    Finset.prod_congr rfl fun i _ => hloc i,
    Finset.prod_attach Q fun PP => ((zinv PP 0 r * ((Ideal.absNorm PP.asIdeal : ℝ) ^ (r * (T.rank - r)))⁻¹ : ℝ) : ℂ)]

end GlobalTheory.TwistNorm
