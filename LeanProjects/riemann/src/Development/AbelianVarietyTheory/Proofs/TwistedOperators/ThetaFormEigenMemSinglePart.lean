import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ConjScalarThm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingsExistRow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAdjoinSplitHeckeGeneratorsDualsSphericalStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalHeckeConjPlaceEqDualLabelStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVectorStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelOperatorsAtPrimeOffLevelDatum
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightCocharacterEqOfGoodPlaces

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjScalar.OnePart

open GlobalTheory.Hk3 GlobalTheory.Hk3.LabDet

theorem adjoin_scalar {M : Type} [AddCommGroup M] [Module ℂ M] (s : Set (Module.End ℂ M)) (S : M → Prop)
    (h : ∀ x ∈ s, ∃ l : ℂ, ∀ u, S u → x u = l • u) :
    ∀ a ∈ Algebra.adjoin ℂ s, ∃ l : ℂ, ∀ u, S u → a u = l • u := by
  intro a ha
  induction ha using Algebra.adjoin_induction with
  | mem x hx => exact h x hx
  | algebraMap r =>
    refine ⟨r, fun u _ => ?_⟩
    simp [Module.algebraMap_end_apply]
  | add x y _ _ hx hy =>
    obtain ⟨l, hl⟩ := hx
    obtain ⟨m, hm⟩ := hy
    exact ⟨l + m, fun u hu => by rw [LinearMap.add_apply, hl u hu, hm u hu, add_smul]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨l, hl⟩ := hx
    obtain ⟨m, hm⟩ := hy
    exact ⟨m * l, fun u hu => by rw [Module.End.mul_apply, hm u hu, map_smul, hl u hu, smul_smul]⟩

variable {D : D7}

theorem scalar_of_split {V : HSp D} {M : Type} [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (P : Pl D.host.E)
    (hP : Formalism.DivisionValues.conjPl P ≠ P) (S : M → Prop) (fu : ∀ u, S u → ∀ k ∈ hyp V P, π k u = u) (a b : List ℤ → ℂ)
    (ha : ∀ u, S u → ∀ k, k ≤ V.rank →
      opOf π P (Finsupp.single (splitLab V.rank k) 1) u = a (splitLab V.rank k) • u)
    (hb : ∀ u, S u → ∀ k, k ≤ V.rank →
      opOf π (Formalism.DivisionValues.conjPl P) (Finsupp.single (splitLab V.rank k) 1) u = b (splitLab V.rank k) • u) (d : List ℤ) :
    ∃ l : ℂ, ∀ u, S u → opOf π P (Finsupp.single d 1) u = l • u := by
  obtain ⟨z, hz, hzu⟩ := GlobalTheory.T.exists_adjoin_splitHeckeGenerators_duals_spherical V P hP M π d
  have gen : ∀ x ∈ {x : Module.End ℂ M | ∃ k, k ≤ V.rank ∧ (x = opOf π P (Finsupp.single (splitLab V.rank k) 1) ∨
      x = opOf π P (Finsupp.single (dualLab (splitLab V.rank k)) 1))}, ∃ l : ℂ, ∀ u, S u → x u = l • u := by
    rintro x ⟨k, hk, rfl | rfl⟩
    · exact ⟨a (splitLab V.rank k), fun u hu => ha u hu k hk⟩
    · refine ⟨b (splitLab V.rank k), fun u hu => ?_⟩
      have hc := (GlobalTheory.T.sphericalHecke_conjPlace_eq_dualLabel V P).2.2 (Finsupp.single (splitLab V.rank k) 1) M π u (fu u hu)
      rw [GlobalTheory.Hk3.dualC, Finsupp.mapDomain_single] at hc
      rw [← hc]
      exact hb u hu k hk
  obtain ⟨l, hl⟩ := adjoin_scalar _ S gen z hz
  exact ⟨l, fun u hu => by rw [← hzu u (fu u hu), hl u hu]⟩

theorem postOn_hk_single {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (P : Pl D.host.E) (d : List ℤ) (U : MMap M) :
    postOn M (hk V P (Finsupp.single d 1)) U = opOf (rRep M) P (Finsupp.single d 1) U := by
  unfold rRep
  simp only [hk, opOf, Finsupp.sum_single_index, one_smul, zero_smul]
  ext v g
  simp [postOn, heckeLin, rLin, LinearMap.compMultilinearMap_apply, Finset.sum_apply]

private theorem star_algebraMap_eq (c : D.host.F) : star (algebraMap D.host.F D.host.E c) = algebraMap D.host.F D.host.E c := by
  have hm : (algebraMap D.host.F D.host.E c) ∈ NumberField.maximalRealSubfield D.host.E :=
    NumberField.IsTotallyReal.le_maximalRealSubfield D.host.F c.2
  exact (NumberField.IsCMField.complexConj_eq_self_iff _ _).mpr hm

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem good_conj (R : RealDat D A Ks) (t : T0) (P : Pl D.host.E) (hP : Good R t P) : Good R t (Formalism.DivisionValues.conjPl P) := by
  intro PP hPP
  obtain ⟨h1, h2⟩ := hP PP hPP
  rw [GlobalTheory.GoodPrimes.isConjPl_iff] at h2 ⊢
  refine ⟨fun e => h2 ?_, fun e => h1 ?_⟩
  · rw [e, Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl]
  · have e' := congrArg Formalism.DivisionValues.conjPl e
    rw [Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl, Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl] at e'
    exact e'.symm

theorem good_of_offS (R : RealDat D A Ks) (hL : R.toLevCh.Is A.μ0) (P : Pl D.host.E)
    (h : OffS D (GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.badF R) P) : Good R A.μ0 P := by
  classical
  intro PP hPP
  have hPg : PP ∈ R.Pg := by
    rcases hPP with h1 | h1
    · exact h1
    · rw [GlobalTheory.LiftLower.Q_base hL] at h1
      simp at h1
  obtain ⟨x, hx, hy⟩ := h (PP.under (𝓞 D.host.F)) (Finset.mem_image_of_mem _ hPg)
  have hx' : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x ∈ PP.asIdeal := hx
  have hcoe : ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x : 𝓞 D.host.E) : D.host.E) =
      algebraMap D.host.F D.host.E (x : D.host.F) := by
    first
    | rfl
    | (rw [← IsScalarTower.algebraMap_apply (𝓞 D.host.F) (𝓞 D.host.E) D.host.E,
          IsScalarTower.algebraMap_apply (𝓞 D.host.F) D.host.F D.host.E]; rfl)
  have hnot := hy _ hcoe
  refine ⟨fun e => hnot (by rw [← e]; exact hx'), fun hc => ?_⟩
  obtain ⟨c', hc'P, hc'eq⟩ := hc _ hx'
  exact hy c' (by rw [hc'eq, hcoe, star_algebraMap_eq]) hc'P

private theorem primeIdem_and_sphOp_of_isHeckeOpFull {V : HSp D} {J : Set (GA D V)} {χ : GA D V → ℂ}
    {Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))} {P : Pl D.host.E} {d : List ℤ} {Rp : Finset (GA D V)}
    (h : Hecke₂ V J χ Sb P d Rp) :
    (∃ e f, IsPrimeIdem P e f ∧ OffS D Sb P ∧ (∀ g, SuppF V f g → (g ∈ J ↔ g ∈ KsphC V ∅)) ∧
      (∀ g ∈ J, SuppF V f g → χ g = 1)) ∧ SphOp V P d Rp := by
  unfold Hecke₂ at h
  obtain ⟨e, f, ϖ, α, hS, hPf, h1, h2, h3, hJ, hχ, hα, hd, hR, hc⟩ := h
  refine ⟨⟨e, f, hPf, hS, hJ, hχ⟩, ?_⟩
  have hset : {k | k ∈ J ∧ SuppF V f k} = {k | k ∈ KsphC V ∅ ∧ SuppF V f k} := by
    ext k
    exact ⟨fun hk => ⟨(hJ k hk.2).1 hk.1, hk.2⟩, fun hk => ⟨(hJ k hk.2).2 hk.1, hk.2⟩⟩
  unfold SphOp Hecke₂
  refine ⟨e, f, ϖ, α, GlobalTheory.LevOp.offS_empty, hPf, h1, h2, h3, fun _ _ => Iff.rfl, fun _ _ _ => rfl, hα, hd, hR, ?_⟩
  rw [← hset]
  exact hc

private theorem mult_map_mul_right_eq_of_chi_eq_one {θ} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {J : Set (GA D V)}
    {χ : GA D V → ℂ} {U : MMap M} (hU : U ∈ Mult θ M J χ) (k : GA D V) (hk : k ∈ J) (hχ : χ k = 1) :
    ∀ v g, U v (g * k) = U v g := by
  induction hU using Submodule.span_induction with
  | mem T hT =>
    intro v g
    rw [hT.lev v k hk g, hχ, one_mul]
  | zero => intro v g; rfl
  | add T T' _ _ h1 h2 =>
    intro v g
    simp only [MultilinearMap.add_apply, Pi.add_apply, h1 v g, h2 v g]
  | smul c T _ h1 =>
    intro v g
    simp only [MultilinearMap.smul_apply, Pi.smul_apply, h1 v g]

theorem mem_one_part : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.models_HW → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (b : Pl D.host.E → List ℤ → ℂ), ∃ ev, ∀ w : (R.HW i σ).H, (∀ P d, GlobalTheory.Hk3.Good R A.μ0 P → GlobalTheory.ConjScalar.RelLab (Wc D i) P d → postOn (R.MW i σ) (GlobalTheory.Hk3.hk (Wc D i) P (Finsupp.single d 1)) ((R.HW i σ).e w) = b P d • (R.HW i σ).e w) → w ∈ GlobalTheory.LiftLower.partH R i σ ev := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hL hM i σ b
  classical
  obtain ⟨Sw, hSw⟩ : ∃ Sw : MMap (R.MW i σ) → Prop, ∀ u, Sw u ↔ ∃ w : (R.HW i σ).H,
      (∀ P d, GlobalTheory.Hk3.Good R A.μ0 P → GlobalTheory.ConjScalar.RelLab (Wc D i) P d →
        postOn (R.MW i σ) (GlobalTheory.Hk3.hk (Wc D i) P (Finsupp.single d 1)) ((R.HW i σ).e w) = b P d • (R.HW i σ).e w) ∧
      u = (R.HW i σ).e w := ⟨_, fun _ => Iff.rfl⟩
  refine ⟨fun P d => if h : ∃ l : ℂ, ∀ u, Sw u → opOf (rRep (R.MW i σ)) P (Finsupp.single d 1) u = l • u
    then h.choose else 0, ?_⟩
  intro w hw
  have hW : ∀ w' : (R.HW i σ).H, (R.HW i σ).e w' ∈ R.Wall i σ := by
    intro w'
    rw [← (hM i σ).2.1]
    exact LinearMap.mem_range_self _ w'
  simp only [GlobalTheory.LiftLower.partH, Submodule.mem_comap, partFull, Submodule.mem_inf, Submodule.mem_iInf,
    LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
  refine ⟨hW w, ?_⟩
  intro P d Rp hfull
  obtain ⟨⟨e, f, hPf, hS, hJ, hχ⟩, hsph⟩ := primeIdem_and_sphOp_of_isHeckeOpFull hfull
  have hG : GlobalTheory.Hk3.Good R A.μ0 P := good_of_offS R hL P hS
  have hfix : ∀ w' : (R.HW i σ).H, ∀ k ∈ hyp (Wc D i) P,
      rRep (R.MW i σ) k ((R.HW i σ).e w') = (R.HW i σ).e w' := by
    intro w' k hk
    obtain ⟨hk1, hk2⟩ := (GlobalTheory.LevOp.mem_hyp hPf).1 hk
    have hkJ := (hJ k hk2).2 hk1
    have hinv := mult_map_mul_right_eq_of_chi_eq_one (hW w') k hkJ (hχ k hkJ hk2)
    unfold rRep
    ext v g
    simp [postOn, rLin, LinearMap.compMultilinearMap_apply, hinv]
  have hSfix : ∀ u, Sw u → ∀ k ∈ hyp (Wc D i) P, rRep (R.MW i σ) k u = u := by
    intro u hu k hk
    obtain ⟨w', -, rfl⟩ := (hSw u).1 hu
    exact hfix w' k hk
  have hex : ∃ l : ℂ, ∀ u, Sw u → opOf (rRep (R.MW i σ)) P (Finsupp.single d 1) u = l • u := by
    by_cases hc : Formalism.DivisionValues.conjPl P = P
    · refine ⟨b P d, fun u hu => ?_⟩
      obtain ⟨w', hw', rfl⟩ := (hSw u).1 hu
      rw [← postOn_hk_single]
      exact hw' P d hG (Or.inr ⟨hc, Rp, hsph⟩)
    · refine scalar_of_split (rRep (R.MW i σ)) P hc Sw hSfix (b P) (b (Formalism.DivisionValues.conjPl P)) ?_ ?_ d
      · intro u hu k hk
        obtain ⟨w', hw', rfl⟩ := (hSw u).1 hu
        rw [← postOn_hk_single]
        exact hw' P _ hG (Or.inl ⟨hc, k, hk, rfl⟩)
      · intro u hu k hk
        obtain ⟨w', hw', rfl⟩ := (hSw u).1 hu
        rw [← postOn_hk_single]
        refine hw' (Formalism.DivisionValues.conjPl P) _ (good_conj R A.μ0 P hG) (Or.inl ⟨?_, k, hk, rfl⟩)
        rw [Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl]
        exact fun h => hc h.symm
  have hsum : heckeOn (R.MW i σ) Rp ((R.HW i σ).e w) = ∑ γ ∈ Rp, rRep (R.MW i σ) γ ((R.HW i σ).e w) := by
    unfold rRep
    ext v g
    simp [heckeOn, postOn, heckeLin, rLin, LinearMap.compMultilinearMap_apply]
  rw [hsum, ((GlobalTheory.T.spherical_label_operators_on_hyperspecial_fixed_vectors (Wc D i) P).1 d Rp hsph).2 _ (rRep (R.MW i σ)) _ (hfix w), dif_pos hex]
  exact hex.choose_spec _ ((hSw _).2 ⟨w, hw, rfl⟩)

end GlobalTheory.ConjScalar.OnePart

end
