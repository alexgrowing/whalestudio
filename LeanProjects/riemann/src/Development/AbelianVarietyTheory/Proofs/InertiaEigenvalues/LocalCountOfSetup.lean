import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.H1MapSubgroup
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteContinuousCocyclesLocalGaloisRep
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NatCastPowNeZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalGaloisRepInvariantsFromFractionRing
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinrankDdRFinsum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationLtOneIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPlaceEmb
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisEmbeddingCount
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCongOfCongOnFixed
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralNormLe

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published

namespace GlobalTheory.LocalConditionCount

theorem norm_lt_one_iff_mem {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] {v : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω} (hA : IsPlaceOver A v)
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (x : 𝓞 E) :
    ‖Bw.j (algebraMap E Ω (x : E))‖ < 1 ↔ x ∈ v.asIdeal :=
  _root_.GlobalTheory.NonPowerRoot.norm_lt_one_iff hA Bw x

section Algebra

theorem card_span {O Λ K G ι : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing Λ] [Algebra O Λ]
    [AddCommGroup K] [Module Λ K] (hK : ∀ a ∈ IsLocalRing.maximalIdeal O, ∀ b : K, algebraMap O Λ a • b = 0)
    (Z : Submodule O (G → ι → O)) [Module.Finite O Z] (hZ : ∀ (c : O) z, c ≠ 0 → c • z ∈ Z → z ∈ Z) :
    Nat.card (Submodule.span Λ {f : G → ι → K | ∃ y ∈ Z, ∃ b : K, ∀ g a, f g a = algebraMap O Λ (y g a) • b}) =
      Nat.card K ^ Module.finrank O Z := by
  letI : Module O K := Module.compHom K (algebraMap O Λ)
  have hs : ∀ (a : O) (b : K), a • b = algebraMap O Λ a • b := fun _ _ => rfl
  let β := Module.finBasis O Z
  let Φ : (Fin (Module.finrank O Z) → K) →ₗ[Λ] (G → ι → K) :=
    { toFun := fun b g a => ∑ i, algebraMap O Λ ((β i).1 g a) • b i
      map_add' := fun b b' => by funext g a; simp [Finset.sum_add_distrib]
      map_smul' := fun c b => by funext g a; simp [Finset.smul_sum, smul_comm c] }
  have hΦ : ∀ b g a, Φ b g a = ∑ i, ((β i).1 g a) • b i := fun _ _ _ => rfl
  have hr : Submodule.span Λ {f : G → ι → K | ∃ y ∈ Z, ∃ b : K, ∀ g a, f g a = algebraMap O Λ (y g a) • b} =
      LinearMap.range Φ := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro f ⟨y, hy, b, hf⟩
      refine ⟨fun i => β.repr ⟨y, hy⟩ i • b, funext fun g => funext fun a => ?_⟩
      have := congrFun (congrFun (congrArg Subtype.val (β.sum_repr ⟨y, hy⟩)) g) a
      simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul] at this
      rw [hΦ, hf, ← hs, ← this, Finset.sum_smul]
      exact Finset.sum_congr rfl fun i _ => by rw [smul_smul, mul_comm]
    · rintro _ ⟨b, rfl⟩
      have : Φ b = ∑ i, fun g a => algebraMap O Λ ((β i).1 g a) • b i := by
        funext g a
        simp only [Finset.sum_apply]
        rfl
      rw [this]
      exact Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨_, (β i).2, b i, fun _ _ => rfl⟩
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro b hb
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
    have hT : Module.IsTorsionBySet O K (IsLocalRing.maximalIdeal O) := fun b a => hK a.1 a.2 b
    letI : Module (IsLocalRing.ResidueField O) K := hT.module
    have hs' : ∀ (a : O) (b : K), IsLocalRing.residue O a • b = a • b := fun _ _ => rfl
    funext i
    refine (Module.forall_dual_apply_eq_zero_iff (IsLocalRing.ResidueField O) (b i)).1 fun φ => ?_
    choose c hc using fun j => IsLocalRing.residue_surjective (φ (b j))
    have h1 : ∀ g a, ∃ y, (∑ j, c j • β j : Z).1 g a = ϖ * y := fun g a => by
      have h2 := congrArg φ ((hΦ b g a).symm.trans (congrFun (congrFun hb g) a))
      simp only [map_sum, ← hs', map_smul, ← hc, smul_eq_mul, Pi.zero_apply, map_zero, ← map_mul] at h2
      rw [← map_sum, IsLocalRing.residue_eq_zero_iff, hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at h2
      obtain ⟨y, hy⟩ := h2
      exact ⟨y, by simpa [mul_comm] using hy⟩
    choose y hy using h1
    have h3 : (∑ j, c j • β j : Z).1 = ϖ • y := funext fun g => funext fun a => hy g a
    have hyZ : y ∈ Z := hZ ϖ y hϖ.ne_zero (h3 ▸ (∑ j, c j • β j : Z).2)
    have h4 : (∑ j, c j • β j : Z) = ϖ • ⟨y, hyZ⟩ := Subtype.ext h3
    have h5 := congrArg (fun z => β.repr z i) h4
    simp only [Module.Basis.repr_sum_self, map_smul, Finsupp.smul_apply, smul_eq_mul] at h5
    rw [← hc, h5, IsLocalRing.residue_eq_zero_iff]
    exact Ideal.mul_mem_right _ _ hϖ.not_isUnit
  rw [hr, ← Nat.card_congr (LinearEquiv.ofInjective Φ hinj).toEquiv, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin _),
    Fintype.card_fin]

theorem finite_and_finrank {O L G H ι : Type} [CommRing O] [IsDomain O] [IsNoetherianRing O] [Field L] [Algebra O L]
    [IsFractionRing O L] (e : G ≃ H) (W : Submodule L (H → ι → L)) [FiniteDimensional L W]
    (Z : Submodule O (G → ι → O)) (hZ : ∀ y, y ∈ Z ↔ (fun h a => algebraMap O L (y (e.symm h) a)) ∈ W)
    (hW : ∀ w ∈ W, ∃ d : O, d ≠ 0 ∧ ∃ f : H → ι → O, ∀ h a, algebraMap O L (f h a) = algebraMap O L d * w h a) :
    Module.Finite O Z ∧ Module.finrank O Z = Module.finrank L W := by
  classical
  have hinj := IsFractionRing.injective O L
  let φ : Z →ₗ[O] W :=
    { toFun := fun y => ⟨_, (hZ y).1 y.2⟩
      map_add' := fun a b => Subtype.ext (by funext g j; simp)
      map_smul' := fun c a => Subtype.ext (by funext g j; simp [Algebra.smul_def]) }
  have hφ : ∀ (y : Z) h a, (φ y).1 h a = algebraMap O L (y.1 (e.symm h) a) := fun _ _ _ => rfl
  have hφi : Function.Injective φ := fun y y' h => Subtype.ext (funext fun g => funext fun a => hinj (by
    have := congrFun (congrFun (congrArg Subtype.val h) (e g)) a
    rwa [hφ, hφ, e.symm_apply_apply] at this))
  constructor
  · let F : Finset (H × ι) → Submodule L W := fun s =>
      { carrier := {w | ∀ p ∈ s, w.1 p.1 p.2 = 0}
        zero_mem' := fun _ _ => rfl
        add_mem' := fun {a b} ha hb p hp => by simp [ha p hp, hb p hp]
        smul_mem' := fun c a ha p hp => by simp [ha p hp] }
    obtain ⟨_, ⟨s, rfl⟩, hs⟩ := (wellFounded_lt (α := Submodule L W)).has_min (Set.range F) ⟨_, ∅, rfl⟩
    have h0 : ∀ w ∈ F s, w = 0 := fun w hw => Subtype.ext (funext fun h => funext fun a => by
      have h1 : F (insert (h, a) s) ≤ F s := fun w hw p hp => hw p (Finset.mem_insert_of_mem hp)
      have h2 := h1.eq_of_not_lt (hs _ ⟨_, rfl⟩)
      exact (h2.ge hw) (h, a) (Finset.mem_insert_self _ _))
    let ev : Z →ₗ[O] (s → O) :=
      { toFun := fun y p => y.1 (e.symm p.1.1) p.1.2
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    refine Module.Finite.of_injective ev ((injective_iff_map_eq_zero _).2 fun y hy => hφi ?_)
    rw [map_zero]
    refine h0 _ fun p hp => ?_
    have : y.1 (e.symm p.1) p.2 = 0 := congrFun hy ⟨p, hp⟩
    rw [hφ, this, map_zero]
  · haveI : IsLocalizedModule (nonZeroDivisors O) φ := by
      refine ⟨fun s => ?_, fun y => ?_, fun {x y} h => ⟨1, by rw [hφi h]⟩⟩
      · have hs : algebraMap O L s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
        rw [Module.End.isUnit_iff]
        refine ⟨fun a b h => ?_, fun a => ⟨(algebraMap O L s)⁻¹ • a, ?_⟩⟩
        · simp only [Module.algebraMap_end_apply] at h
          rw [← algebraMap_smul L, ← algebraMap_smul L (s : O) b] at h
          exact smul_right_injective _ hs h
        · rw [Module.algebraMap_end_apply, ← algebraMap_smul L, smul_inv_smul₀ hs]
      · obtain ⟨d, hd, f, hf⟩ := hW y.1 y.2
        have e0 : (fun h a => algebraMap O L (f (e (e.symm h)) a)) = algebraMap O L d • y.1 := by
          funext h a
          rw [e.apply_symm_apply, hf]
          rfl
        refine ⟨(⟨fun g => f (e g), (hZ _).2 (e0 ▸ W.smul_mem _ y.2)⟩, ⟨d, mem_nonZeroDivisors_of_ne_zero hd⟩), ?_⟩
        refine Subtype.ext (Eq.trans ?_ e0.symm)
        exact (algebraMap_smul L d y.1).symm
    rw [← IsLocalizedModule.finrank_eq (nonZeroDivisors O) φ le_rfl, Module.finrank, Module.finrank,
      IsLocalization.rank_eq L (nonZeroDivisors O) le_rfl]

theorem card_subquotient {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (B S Z : Submodule R M)
    (h1 : B ≤ S) (h2 : S ≤ Z) :
    Nat.card S = Nat.card B * Nat.card ((S.comap Z.subtype).map (B.comap Z.subtype).mkQ) := by
  let f : S →ₗ[R] Z ⧸ B.comap Z.subtype := (B.comap Z.subtype).mkQ.comp (Submodule.inclusion h2)
  have hk : LinearMap.ker f = B.comap S.subtype := by
    ext x
    exact Submodule.Quotient.mk_eq_zero _
  have hr : LinearMap.range f = (S.comap Z.subtype).map (B.comap Z.subtype).mkQ := by
    rw [LinearMap.range_comp, Submodule.range_inclusion]
  rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.ker f), Nat.card_congr f.quotKerEquivRange.toEquiv, hr, hk,
    Nat.card_congr (Submodule.comapSubtypeEquivOfLe h1).toEquiv]

theorem finrank_eq_add_quotient {L V M : Type} [Field L] [AddCommGroup V] [Module L V] [AddCommGroup M] [Module L M]
    (f : V →ₗ[L] M) (hf : Function.Injective f) (W : Submodule L M) [FiniteDimensional L W] (h : LinearMap.range f ≤ W) :
    Module.finrank L W = Module.finrank L V + Module.finrank L (W ⧸ (LinearMap.range f).comap W.subtype) := by
  rw [← Submodule.finrank_quotient_add_finrank ((LinearMap.range f).comap W.subtype),
    (Submodule.comapSubtypeEquivOfLe h).finrank_eq, LinearMap.finrank_range_of_inj hf, add_comm]

end Algebra

section Local

open Formalism.BasicNotions.Loc

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [IsDomain O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω Gw O)

theorem isFractionRing_LL : letI := Bw.toLL.toAlgebra; IsFractionRing O ↥Bw.LL.1 := by
  letI := Bw.toLL.toAlgebra
  haveI : FaithfulSMul O ↥Bw.LL.1 :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (GlobalTheory.EmbInj.toLL_inj Bw)
  refine IsFractionRing.of_field O _ fun x => ?_
  obtain ⟨n, d, hd, hf⟩ := GlobalTheory.EmbInj.exists_frac Bw x
  refine ⟨n, d, ?_⟩
  have hd' : Bw.toLL d ≠ 0 := (map_ne_zero_iff _ (GlobalTheory.EmbInj.toLL_inj Bw)).2 hd
  change x = Bw.toLL _ / Bw.toLL _
  rw [← hf, mul_div_cancel_left₀ _ hd']

omit [IsDomain O] in
theorem B1_le_Z1f (P : LocPrime l) {m : ℕ} (T : ↥Gw →* GL (Fin m) O)
    (hT : Continuous fun g => ((T g : GL (Fin m) O) : Matrix (Fin m) (Fin m) O)) :
    Formalism.WeaklyAdmissibleFiltrations.B1 (Bw.rep T) ≤ Formalism.WeaklyAdmissibleFiltrations.finiteCocycles (P.PD Bw.Kw) (Bw.rep T) := by
  rintro _ ⟨x, rfl⟩
  have h : ∀ g, Formalism.WeaklyAdmissibleFiltrations.cob (Bw.rep T) x g = Bw.rep T g x - x := fun _ => rfl
  haveI : IsTopologicalRing ↥Bw.LL.1 := (GlobalTheory.LocalIntegers.good_integers l Bw.LL).1.2.2.2.1
  refine ⟨⟨(GlobalTheory.BKDimNoInv.rep_continuous Bw T hT x).sub continuous_const, fun g k => ?_⟩, x ⊗ₜ 1, fun g => ?_⟩
  · simp only [h, map_mul, Module.End.mul_apply, map_sub]
    abel
  · simp [h, Formalism.WeaklyAdmissibleFiltrations.actVB, TensorProduct.sub_tmul]

set_option maxHeartbeats 1600000 in

theorem card_local [IsDiscreteValuationRing O] [IsTopologicalRing O] (hO : IsAdic (IsLocalRing.maximalIdeal O))
    (hfin : Formalism.GaloisCohomology.LocalFinitenessK) (P : LocPrime l) {m : ℕ} (T : ↥Gw →* GL (Fin m) O)
    (hT : Continuous fun g => ((T g : GL (Fin m) O) : Matrix (Fin m) (Fin m) O))
    (h0 : Formalism.WeaklyAdmissibleFiltrations.H0V (Bw.rep T) = ⊥) {Λ K : Type} [CommRing Λ] [Algebra O Λ] [AddCommGroup K] [Module Λ K] [Finite K]
    [TopologicalSpace K] [DiscreteTopology K]
    (hK : ∀ a ∈ IsLocalRing.maximalIdeal O, ∀ b : K, algebraMap O Λ a • b = 0)
    (ρ : Representation Λ ↥Gw (Fin m → K))
    (hρ : ∀ g x a, ρ g x a = ∑ b, algebraMap O Λ ((T g : Matrix (Fin m) (Fin m) O) a b) • x b) :
    Nat.card (Submodule.span Λ {x : H1 ρ | ∃ (z : Z1 ρ) (c : ↥(GK Bw.Kw) → Fin m → ↥Bw.LL.1) (y : ↥Gw → Fin m → O) (b : K),
      c ∈ Formalism.WeaklyAdmissibleFiltrations.finiteCocycles (P.PD Bw.Kw) (Bw.rep T) ∧ (∀ g a, c (Bw.e g) a = Bw.toLL (y g a)) ∧
      (∀ g a, (z : ↥Gw → Fin m → K) g a = algebraMap O Λ (y g a) • b) ∧ x = Submodule.Quotient.mk z}) =
    Nat.card (H0 ρ) * Nat.card K ^ Module.finrank ↥Bw.LL.1 (Formalism.WeaklyAdmissibleFiltrations.FiniteCohomology (P.PD Bw.Kw) (Bw.rep T)) := by
  classical
  letI := Bw.toLL.toAlgebra
  haveI := isFractionRing_LL Bw
  haveI := GlobalTheory.BlochKatoIntegralScalars.compactSpace_GK Bw.Kw
  have hinj := GlobalTheory.EmbInj.toLL_inj Bw
  set W := Formalism.WeaklyAdmissibleFiltrations.finiteCocycles (P.PD Bw.Kw) (Bw.rep T) with hWdef
  haveI := GlobalTheory.LocalH1Finiteness.finite_continuous_cocycles_localGaloisRep Bw hfin T hT
  haveI : FiniteDimensional ↥Bw.LL.1 W :=
    Submodule.finiteDimensional_of_le (S₂ := Formalism.WeaklyAdmissibleFiltrations.continuousCocycles (Bw.rep T)) fun c hc => hc.1
  have hsm : ∀ (c : O) (y : ↥Gw → Fin m → O), (fun h a => Bw.toLL ((c • y) (Bw.e.symm h) a)) =
      Bw.toLL c • fun h a => Bw.toLL (y (Bw.e.symm h) a) := fun c y => by funext h a; simp
  let Z : Submodule O (↥Gw → Fin m → O) :=
    { carrier := {y | (fun h a => Bw.toLL (y (Bw.e.symm h) a)) ∈ W}
      zero_mem' := by
        simp only [Set.mem_ofPred_eq, Pi.zero_apply, map_zero]
        exact W.zero_mem
      add_mem' := fun {a b} ha hb => by
        have := W.add_mem ha hb
        simp only [Set.mem_ofPred_eq, Pi.add_apply, map_add]
        exact this
      smul_mem' := fun c y hy => by
        rw [Set.mem_ofPred_eq, hsm]
        exact W.smul_mem _ hy }
  have hZ : ∀ y, y ∈ Z ↔ (fun h a => Bw.toLL (y (Bw.e.symm h) a)) ∈ W := fun _ => Iff.rfl
  obtain ⟨hZf, hZr⟩ := finite_and_finrank Bw.e.toEquiv W Z hZ fun w hw => by
    obtain ⟨d, hd, f, -, hf⟩ := GlobalTheory.BlochKatoRank.exists_integral Bw w hw.1.1
    exact ⟨d, hd, f, hf⟩
  have hcard := card_span hK Z fun c z hc hz => by
    rw [hZ, hsm] at hz
    exact (W.smul_mem_iff ((map_ne_zero_iff _ hinj).2 hc)).1 hz
  have hBW := B1_le_Z1f Bw P T hT
  have hcob : Function.Injective (Formalism.WeaklyAdmissibleFiltrations.cob (Bw.rep T)) := (injective_iff_map_eq_zero _).2 fun x hx => by
    have : x ∈ Formalism.WeaklyAdmissibleFiltrations.H0V (Bw.rep T) := (Submodule.mem_iInf _).2 fun g => congrFun hx g
    rwa [h0] at this
  have hdim : Module.finrank ↥Bw.LL.1 W = m + Module.finrank ↥Bw.LL.1 (Formalism.WeaklyAdmissibleFiltrations.FiniteCohomology (P.PD Bw.Kw) (Bw.rep T)) := by
    have := finrank_eq_add_quotient _ hcob W hBW
    rw [Module.finrank_fin_fun] at this
    exact this
  set S : Set (↥Gw → Fin m → K) := {f | ∃ y ∈ Z, ∃ b : K, ∀ g a, f g a = algebraMap O Λ (y g a) • b} with hS
  have hb : ∀ b : K, Continuous fun o : O => algebraMap O Λ o • b := fun b => by
    let μ : O →+ K := ⟨⟨fun o => algebraMap O Λ o • b, by simp⟩, fun _ _ => by simp [add_smul]⟩
    refine continuous_of_continuousAt_zero μ ?_
    rw [ContinuousAt, map_zero, nhds_discrete K, Filter.tendsto_pure]
    have ho : IsOpen ((IsLocalRing.maximalIdeal O ^ 1 : Ideal O) : Set O) := (isAdic_iff.1 hO).1 1
    rw [pow_one] at ho
    filter_upwards [ho.mem_nhds (zero_mem _)] with o ho
    exact hK o ho b
  have hSZ : ∀ f ∈ S, f ∈ Z1 ρ := by
    rintro f ⟨y, hy, b, hf⟩
    have hy' := ((hZ y).1 hy).1
    constructor
    · refine continuous_pi fun a => ?_
      simp only [hf]
      refine (hb b).comp ?_
      have h1 : Continuous fun g => Bw.toLL (y (Bw.e.symm (Bw.e g)) a) :=
        ((continuous_apply a).comp hy'.1).comp Bw.e_cont
      simp only [MulEquiv.symm_apply_apply] at h1
      have h2 : Continuous fun g => Bw.eO (y g a) := h1.subtype_mk fun g => (Bw.eO (y g a)).2
      exact (Bw.eO_symm_cont.comp h2).congr fun g => Bw.eO.symm_apply_apply _
    · intro g h
      funext a
      have h1 := congrFun (hy'.2 (Bw.e g) (Bw.e h)) a
      simp only [← map_mul, MulEquiv.symm_apply_apply, Pi.add_apply, GlobalTheory.LocalH1Finiteness.rep_apply, ← map_sum,
        ← map_add] at h1
      simp only [Pi.add_apply, hρ, hf, hinj h1, map_add, map_sum, map_mul, add_smul, Finset.sum_smul, mul_smul]
  have hBS : B1 ρ ≤ Submodule.span Λ S := by
    rintro _ ⟨x, rfl⟩
    rw [← Finset.univ_sum_single x, map_sum]
    refine Submodule.sum_mem _ fun j _ => Submodule.subset_span
      ⟨fun g a => (T g : Matrix (Fin m) (Fin m) O) a j - (Pi.single j 1 : Fin m → O) a, ?_, x j, fun g a => ?_⟩
    · rw [hZ]
      refine hBW ⟨Pi.single j 1, funext fun h => funext fun a => ?_⟩
      change Bw.rep T h (Pi.single j 1) a - (Pi.single j 1 : Fin m → ↥Bw.LL.1) a = _
      rw [GlobalTheory.LocalH1Finiteness.rep_apply]
      simp [Pi.single_apply, apply_ite Bw.toLL]
    · rw [amitsur_d0_apply, Pi.sub_apply, hρ]
      simp [Pi.single_apply, apply_ite (algebraMap O Λ), sub_smul, ite_smul]
  have hspan : Submodule.span Λ {x : H1 ρ | ∃ (z : Z1 ρ) (c : ↥(GK Bw.Kw) → Fin m → ↥Bw.LL.1) (y : ↥Gw → Fin m → O) (b : K),
      c ∈ W ∧ (∀ g a, c (Bw.e g) a = Bw.toLL (y g a)) ∧
      (∀ g a, (z : ↥Gw → Fin m → K) g a = algebraMap O Λ (y g a) • b) ∧ x = Submodule.Quotient.mk z} =
      ((Submodule.span Λ S).comap (Z1 ρ).subtype).map ((B1 ρ).comap (Z1 ρ).subtype).mkQ := by
    have e1 : Submodule.span Λ S = (Submodule.span Λ ((Z1 ρ).subtype ⁻¹' S)).map (Z1 ρ).subtype := by
      rw [Submodule.map_span, Set.image_preimage_eq_of_subset fun f hf => ⟨⟨f, hSZ f hf⟩, rfl⟩]
    rw [e1, Submodule.comap_map_eq_of_injective (Z1 ρ).subtype_injective, Submodule.map_span]
    congr 1
    ext x
    constructor
    · rintro ⟨z, c, y, b, hc, hy, hz, rfl⟩
      refine ⟨z, ⟨y, ?_, b, hz⟩, rfl⟩
      rw [hZ]
      simp only [← hy, MulEquiv.apply_symm_apply]
      exact hc
    · rintro ⟨z, ⟨y, hy, b, hz⟩, rfl⟩
      exact ⟨z, _, y, b, (hZ y).1 hy, fun g a => by rw [MulEquiv.symm_apply_apply], hz, rfl⟩
  have h1 := card_subquotient (B1 ρ) (Submodule.span Λ S) (Z1 ρ) hBS (Submodule.span_le.2 hSZ)
  have hk : LinearMap.ker (d0 ρ) = H0 ρ := by
    ext x
    simp [mem_riemannRochSpace_iff_regularAt_everywhere, funext_iff (f := d0 ρ x), sub_eq_zero]
  have h2 : Nat.card K ^ m = Nat.card (H0 ρ) * Nat.card (B1 ρ) := by
    rw [← hk, B1, ← Nat.card_congr (d0 ρ).quotKerEquivRange.toEquiv, ← Submodule.card_eq_card_quotient_mul_card,
      Nat.card_fun, Nat.card_eq_fintype_card (α := Fin m), Fintype.card_fin]
  have h3 : Nat.card (B1 ρ) ≠ 0 := fun h => by
    rw [h, mul_zero] at h2
    exact pow_ne_zero m Nat.card_pos.ne' h2
  rw [hcard, hZr, hdim, pow_add, h2, ← hspan] at h1
  apply mul_left_cancel₀ h3
  rw [← h1]
  ring

end Local

section Global

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (bkP : BKPh X) (i : X.Tw)

abbrev Emb : Type := Σ u : placesOver D.host.E (X.l i), EmbV bkP i u.1 u.2

def fracEquiv (v : PlE D.host) (hv : v ∈ placesOver D.host.E (X.l i)) :
    FractionRing (X.O0 i) ≃+* ↥(bkP.br i v hv).LL.1 :=
  letI := (bkP.br i v hv).toLL.toAlgebra
  haveI := isFractionRing_LL (bkP.br i v hv)
  IsFractionRing.ringEquivOfRingEquiv (RingEquiv.refl (X.O0 i))

theorem fracEquiv_alg (v : PlE D.host) (hv : v ∈ placesOver D.host.E (X.l i)) (a : X.O0 i) :
    fracEquiv bkP i v hv (algebraMap _ _ a) = (bkP.br i v hv).toLL a := by
  letI := (bkP.br i v hv).toLL.toAlgebra
  haveI := isFractionRing_LL (bkP.br i v hv)
  exact IsFractionRing.ringEquivOfRingEquiv_algebraMap (RingEquiv.refl (X.O0 i)) a

def embOf (x : Emb bkP i) : D.host.E →+* FractionRing (X.O0 i) :=
  ((fracEquiv bkP i x.1.1 x.1.2).symm.toRingHom.comp (AlgHom.toRingHom x.2)).comp
    (((bkP.br i x.1.1 x.1.2).j.comp (algebraMap D.host.E N.Om)).codRestrict
      (bkP.br i x.1.1 x.1.2).Kw.1 (bkP.br i x.1.1 x.1.2).j_E)

theorem fracEquiv_embOf (x : Emb bkP i) (e : D.host.E) :
    fracEquiv bkP i x.1.1 x.1.2 (embOf bkP i x e) = x.2 (cE bkP i x.1.1 x.1.2 e) :=
  (fracEquiv bkP i x.1.1 x.1.2).apply_symm_apply _

theorem isFrac_iff (x : Emb bkP i) (e : D.host.E) (n d : X.O0 i) :
    IsFrac bkP i x.1.1 x.1.2 (x.2 (cE bkP i x.1.1 x.1.2 e)) n d ↔
      d ≠ 0 ∧ algebraMap _ (FractionRing (X.O0 i)) d * embOf bkP i x e = algebraMap _ _ n := by
  unfold IsFrac
  refine and_congr_right fun _ => ?_
  rw [← (fracEquiv bkP i x.1.1 x.1.2).injective.eq_iff, map_mul, fracEquiv_alg, fracEquiv_alg, fracEquiv_embOf]

theorem norm_toLL_lt_one_iff (v : PlE D.host) (hv : v ∈ placesOver D.host.E (X.l i)) (n : X.O0 i) :
    ‖(((bkP.br i v hv).toLL n : ↥(bkP.br i v hv).LL.1) : PadicAlgCl (X.l i))‖ < 1 ↔ ¬ IsUnit n := by
  refine (GlobalTheory.EmbThroughCompletion.not_isUnit_iff _ ((bkP.br i v hv).eO n)).symm.trans ?_
  rw [MulEquiv.isUnit_map]

theorem mem_iff_not_isUnit (x : Emb bkP i) (e : 𝓞 D.host.E) (n : X.O0 i)
    (h : algebraMap _ _ n = embOf bkP i x e) : e ∈ x.1.1.asIdeal ↔ ¬ IsUnit n := by
  rw [← norm_toLL_lt_one_iff bkP i x.1.1 x.1.2, ← fracEquiv_alg, h, fracEquiv_embOf, GlobalTheory.EmbInj.norm_algHom]
  exact (norm_lt_one_iff_mem (N.plOm.2 x.1.1) (bkP.br i x.1.1 x.1.2) e).symm

theorem exists_int (φ : D.host.E →+* FractionRing (X.O0 i)) (x : 𝓞 D.host.E) :
    ∃ y : X.O0 i, algebraMap (X.O0 i) (FractionRing (X.O0 i)) y = φ (x : D.host.E) :=
  IsIntegrallyClosed.algebraMap_eq_of_integral
    (x.isIntegral_coe.map_of_comp_eq (Int.castRingHom (X.O0 i)) φ (RingHom.ext_int _ _))

theorem l_mem_maximalIdeal : ((X.l i : ℕ) : X.O0 i) ∈ IsLocalRing.maximalIdeal (X.O0 i) := fun hu =>
  X.O_l i (by simpa using hu.map (algebraMap (X.O0 i) (X.O i)))

theorem embOf_bijective : Function.Bijective (embOf bkP i) := by
  constructor
  · rintro ⟨⟨v, hv⟩, τ⟩ ⟨⟨v', hv'⟩, τ'⟩ h
    obtain rfl : v = v' := by
      apply HeightOneSpectrum.ext
      ext e
      obtain ⟨n, hn⟩ := exists_int i (embOf bkP i ⟨⟨v, hv⟩, τ⟩) e
      exact (mem_iff_not_isUnit bkP i _ e n hn).trans (mem_iff_not_isUnit bkP i ⟨⟨v', hv'⟩, τ'⟩ e n (h ▸ hn)).symm
    obtain rfl : τ = τ' := GlobalTheory.EmbInj.algHom_ext (bkP.br i v hv) τ τ' fun e =>
      (fracEquiv_embOf bkP i ⟨⟨v, hv⟩, τ⟩ e).symm.trans (by rw [h]; exact fracEquiv_embOf bkP i ⟨⟨v, hv⟩, τ'⟩ e)
    rfl
  · intro φ
    choose f hf using exists_int i φ
    have hinj := IsFractionRing.injective (X.O0 i) (FractionRing (X.O0 i))
    let ψ : 𝓞 D.host.E →+* X.O0 i :=
      { toFun := f
        map_one' := hinj (by simp [hf])
        map_mul' := fun x y => hinj (by simp [hf])
        map_zero' := hinj (by simp [hf])
        map_add' := fun x y => hinj (by simp [hf]) }
    have hl : ((X.l i : ℕ) : 𝓞 D.host.E) ∈ (IsLocalRing.maximalIdeal (X.O0 i)).comap ψ := by
      rw [Ideal.mem_comap, map_natCast]
      exact l_mem_maximalIdeal i
    let v : HeightOneSpectrum (𝓞 D.host.E) :=
      ⟨(IsLocalRing.maximalIdeal (X.O0 i)).comap ψ, inferInstance, fun h => by
        rw [h, Ideal.mem_bot] at hl
        exact (Fact.out : (X.l i).Prime).ne_zero (by exact_mod_cast hl)⟩
    have hv : v ∈ placesOver D.host.E (X.l i) := hl
    let Bw := bkP.br i v hv
    obtain ⟨g, hg⟩ := GlobalTheory.EmbThroughCompletion.exists_conj (Bw.j.comp (algebraMap D.host.E N.Om))
      (Bw.LL.1.val.toRingHom.comp ((fracEquiv bkP i v hv).toRingHom.comp φ))
      (GlobalTheory.EmbThroughCompletion.norm_lt_one_iff v _ _ (norm_lt_one_iff_mem (N.plOm.2 v) Bw) fun x => by
        change ‖((fracEquiv bkP i v hv (φ x) : ↥Bw.LL.1) : PadicAlgCl (X.l i))‖ < 1 ↔ _
        rw [← hf, fracEquiv_alg, norm_toLL_lt_one_iff]
        rfl)
    let σ : Bw.Kw.1 →ₐ[ℚ_[X.l i]] PadicAlgCl (X.l i) :=
      (g : PadicAlgCl (X.l i) →ₐ[ℚ_[X.l i]] PadicAlgCl (X.l i)).comp Bw.Kw.1.val
    refine ⟨⟨⟨v, hv⟩, σ.codRestrict Bw.LL.1.toSubalgebra (Bw.LL_split σ)⟩, RingHom.ext fun e => ?_⟩
    apply (fracEquiv bkP i v hv).injective
    exact (fracEquiv_embOf bkP i ⟨⟨v, hv⟩, _⟩ e).trans (Subtype.ext (hg e))

theorem exists_conj : ∃ σ : Emb bkP i ≃ Emb bkP i, ∀ x : Emb bkP i,
    IsConjEmb bkP i x.1.1 (σ x).1.1 x.1.2 (σ x).1.2 x.2 (σ x).2 := by
  let Φ := Equiv.ofBijective _ (embOf_bijective bkP i)
  let c : (D.host.E →+* FractionRing (X.O0 i)) ≃ (D.host.E →+* FractionRing (X.O0 i)) :=
    { toFun := fun φ => φ.comp (D.host.conj : D.host.E →+* D.host.E)
      invFun := fun φ => φ.comp (D.host.conj.symm : D.host.E →+* D.host.E)
      left_inv := fun φ => by ext x; simp
      right_inv := fun φ => by ext x; simp }
  refine ⟨Φ.trans (c.trans Φ.symm), fun x e n d => ?_⟩
  rw [isFrac_iff, isFrac_iff]
  have : embOf bkP i ((Φ.trans (c.trans Φ.symm)) x) = c (Φ x) := Φ.apply_symm_apply _
  rw [this]
  rfl

theorem card_emb : Nat.card (Emb bkP i) = 2 * D.R.f := by
  haveI : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  rw [Nat.card_congr (Equiv.ofBijective _ (embOf_bijective bkP i)), GlobalTheory.Proof.GaloisEmbeddingCount.card_ringHom_of_isGalois D.host.E _
    ((X.emb0 i).comp (D.embE.codRestrict D.LL0 D.hostField_le_fixedField)),
    D.host.finrank_cmField, Formalism.BasicNotions.Ranks.f, Formalism.BasicNotions.Ranks.n]
  ring

variable (s : X.Sig i)

theorem continuous_Tgl : Continuous fun g => ((Tgl i s g : GL (Fin D.R.r) (X.O0 i)) :
    Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)) := by
  simp only [Tgl_coe, Tmat, ← map_inv]
  exact ((X.twistCharacterFamily_continuous i _ _).comp continuous_inv).smul (X.rhoS_cont i s)

def h1fDim (u : placesOver D.host.E (X.l i)) : ℕ :=
  Module.finrank ↥(bkP.br i u.1 u.2).LL.1 (Formalism.WeaklyAdmissibleFiltrations.FiniteCohomology (PDv bkP i u.1 u.2) (repV bkP i u.1 u.2 (Tgl i s)))

theorem noInv (h : IsotypicValuationAtRing bkP i s) (v : PlE D.host) (x : Fin D.R.r → FractionRing (X.O0 i))
    (hx : ∀ g : ↥(DecV N v), ((((Tgl i s).comp (DecV N v).subtype g : GL (Fin D.R.r) (X.O0 i)) :
      Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)).map (algebraMap (X.O0 i) (FractionRing (X.O0 i)))).mulVec x = x) : x = 0 :=
  h.2.2.1 v _ (N.plOm.2 v) x fun g hg => by rw [← Tgl_coe]; exact hx ⟨g, hg⟩

theorem h1fDim_eq (h : GalHyp bkP i s) (u : placesOver D.host.E (X.l i)) [Fintype (EmbV bkP i u.1 u.2)] :
    (h1fDim bkP i s u : ℤ) =
      ∑ τ, ((dimD bkP i u.1 u.2 (Tgl i s) τ : ℤ) - dimFil0 bkP i u.1 u.2 (Tgl i s) τ) := by
  have hdR := (h.1.2.1 u.1 u.2 (Tgl i s) (Or.inr rfl)).1
  have h1 := GlobalTheory.BKDimNoInv.finrank_h1f_no_invariants (bkP.br i u.1 u.2) (D.loc (X.l i)) ((Tgl i s).comp (DecV N u.1).subtype)
    ((continuous_Tgl i s).comp continuous_subtype_val) (h.2.2.2.2.2.1 _ _).2.1 hdR (noInv bkP i s h.1 u.1)
  obtain ⟨h2, h3⟩ := GlobalTheory.DeRhamSplit.finrank_DdR_local (D.loc (X.l i)) _ _ (bkP.br i u.1 u.2).LL_split
    (lt_of_lt_of_le (by norm_num) h.2.2.2.2.2.2) _ hdR 0
  have h2' := (congrArg (Nat.cast : ℕ → ℤ) (h2.trans (finsum_eq_sum_of_fintype _))).trans (Nat.cast_sum _ _)
  have h3' := (congrArg (Nat.cast : ℕ → ℤ) (h3.trans (finsum_eq_sum_of_fintype _))).trans (Nat.cast_sum _ _)
  refine h1.trans ((congrArg₂ (· - ·) h2' h3').trans ?_)
  exact (Finset.sum_sub_distrib _ _).symm

theorem sum_h1fDim (h : GalHyp bkP i s) [Fintype (placesOver D.host.E (X.l i))] :
    ∑ u, h1fDim bkP i s u = D.R.f * D.R.r := by
  classical
  have hcard := card_emb bkP i
  have hf : 2 * D.R.f ≠ 0 := by unfold Ranks.f Ranks.n; positivity
  haveI : Finite (Emb bkP i) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hf)
  haveI : ∀ u : placesOver D.host.E (X.l i), Finite (EmbV bkP i u.1 u.2) := fun u =>
    Finite.of_injective (fun τ => (⟨u, τ⟩ : Emb bkP i))
      (sigma_mk_injective (β := fun u : placesOver D.host.E (X.l i) => EmbV bkP i u.1 u.2))
  letI : ∀ u : placesOver D.host.E (X.l i), Fintype (EmbV bkP i u.1 u.2) := fun u => Fintype.ofFinite _
  obtain ⟨σ, hσ⟩ := exists_conj bkP i
  let d : Emb bkP i → ℤ := fun x =>
    (dimD bkP i x.1.1 x.1.2 (Tgl i s) x.2 : ℤ) - dimFil0 bkP i x.1.1 x.1.2 (Tgl i s) x.2
  have hpair : ∀ x, d x + d (σ x) = D.R.r := fun x => by
    have := h.1.2.2.2.2 _ _ _ _ _ _ (hσ x)
    simp only [d]
    omega
  have h1 : ∑ x, (d x + d (σ x)) = ∑ _x : Emb bkP i, (D.R.r : ℤ) := Finset.sum_congr rfl fun x _ => hpair x
  rw [Finset.sum_add_distrib, Equiv.sum_comp σ d, Finset.sum_const, Finset.card_univ,
    ← Nat.card_eq_fintype_card, hcard, nsmul_eq_mul] at h1
  have h2 : ((∑ u, h1fDim bkP i s u : ℕ) : ℤ) = ∑ x, d x := by
    rw [Fintype.sum_sigma, Nat.cast_sum]
    exact Finset.sum_congr rfl fun u _ => h1fDim_eq bkP i s h u
  have : ((∑ u, h1fDim bkP i s u : ℕ) : ℤ) = (D.R.f * D.R.r : ℕ) := by
    rw [h2]
    push_cast at h1 ⊢
    linarith
  exact_mod_cast this

end Global

theorem locCount : LocalFiniteness → LocalTateDuality → LocalEulerChar → Gen.ArchimedeanSignatureMatching → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i) (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [Algebra (X.O0 i) Λ] (κ : GE N →* Λˣ) (Q : Finset (PlE D.host)), Setup bkP i s κ Q → LocCount bkP i s κ := by
  intro _ _ _ h4 D N X bkP i s Λ _ _ _ κ Q ⟨hG, hloc, hfin, _, _, hκ, _⟩ K _ _ _ _ hK
  classical
  obtain ⟨I, hI, ⟨eK⟩⟩ := isSimpleModule_iff_quot_maximal.1 hK
  obtain rfl := IsLocalRing.eq_maximalIdeal hI
  have hkill : ∀ a ∈ IsLocalRing.maximalIdeal (X.O0 i), ∀ b : K, algebraMap (X.O0 i) Λ a • b = 0 := fun a ha b => by
    apply eK.injective
    obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (eK b)
    rw [map_smul, map_zero, ← hc]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mul_mem_right c _ (map_nonunit _ a ha))
  haveI := X.twistBaseCoefficientRing_residueField_finite i
  haveI : Finite (IsLocalRing.ResidueField Λ) := IsLocalRing.ResidueField.finite_of_finite (R := X.O0 i) inferInstance
  haveI : Finite K := Finite.of_injective (β := IsLocalRing.ResidueField Λ) eK eK.injective
  haveI : Finite (placesOver D.host.E (X.l i)) := ((X.S0 i).finite_toSet.subset (X.twistExcludedPlaces_contains_residueChar i)).to_subtype
  letI : Fintype (placesOver D.host.E (X.l i)) := Fintype.ofFinite _
  rw [← finprod_set_coe_eq_finprod_mem, ← finprod_set_coe_eq_finprod_mem, finprod_eq_prod_of_fintype,
    finprod_eq_prod_of_fintype, ← sum_h1fDim bkP i s hG, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun u _ => ?_
  rw [bkOn, dif_pos u.2]
  refine card_local (bkP.br i u.1 u.2) (X.twistBaseCoefficientRing_isAdic i) h4.2.2.2.1 (D.loc (X.l i)) ((Tgl i s).comp (DecV N u.1).subtype)
    ((continuous_Tgl i s).comp continuous_subtype_val)
    (GlobalTheory.BKDimNoInv.localGaloisRep_invariants_from_fractionRing _ _ (noInv bkP i s hG.1 u.1)) hkill _ fun g x a => ?_
  have := hκ u.1 u.2 _ (N.plOm.2 u.1) g.1 g.2
  change ((κ g.1 : Λˣ) : Λ) • (_ : K) = _
  rw [this, Units.val_one, one_smul]
  rfl

end GlobalTheory.LocalConditionCount
