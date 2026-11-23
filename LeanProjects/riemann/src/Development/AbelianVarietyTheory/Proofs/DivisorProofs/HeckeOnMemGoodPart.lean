import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RePosOfIsMultIP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMultMapRightTranslateFiniteAdelicNormalizerStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsDCOfMemDoubleCoset
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotentsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAntiStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlacesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAntiInvolutionOfCharsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryUnimodularExistsFundamentalDomainStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleCosetSumFundamentalDomainStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicativeInnerProductModelStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Links Formalism.IndefR.Bridge Formalism.IndefR.Datum
open scoped InnerProductSpace

namespace GlobalTheory.HeckeModel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Group

variable {G : Type} [Group G]

theorem sum_eq_of_isDC {J : Subgroup G} {x x' : G} {A A' : Finset G} {F : G → ℂ} (hA : IsDC J x A) (hA' : IsDC J x' A')
    (hx : ∃ k₁ k₂ : J, x' = (k₁ : G) * x * k₂) (hF : ∀ k ∈ J, ∀ h, F (h * k) = F h) (h : G) :
    ∑ a ∈ A, F (h * a) = ∑ a ∈ A', F (h * a) :=
  congrFun (GlobalTheory.HkB.dcOp_eq_and_level J ⊤ 1 x x' A A' F
    (fun k hk => ⟨k, hk, 1, J.one_mem, trivial, (mul_one k).symm, fun l _ => Commute.one_left l⟩)
    (fun _ _ => rfl) (fun _ _ => trivial) (fun _ _ => trivial) hA hA' hx
    (fun k h => by simpa using hF k k.2 h)).1 h

theorem sum_inv_of_isDC {J : Subgroup G} {x : G} {A : Finset G} {F : G → ℂ} (hA : IsDC J x A)
    (hF : ∀ k ∈ J, ∀ h, F (h * k) = F h) (k : G) (hk : k ∈ J) (h : G) :
    ∑ a ∈ A, F (h * k * a) = ∑ a ∈ A, F (h * a) := by
  have := (GlobalTheory.HkB.dcOp_eq_and_level J ⊤ 1 x x A A F
    (fun k hk => ⟨k, hk, 1, J.one_mem, trivial, (mul_one k).symm, fun l _ => Commute.one_left l⟩)
    (fun _ _ => rfl) (fun _ _ => trivial) (fun _ _ => trivial) hA hA ⟨1, 1, by simp⟩
    (fun k h => by simpa using hF k k.2 h)).2 ⟨k, hk⟩ h
  simpa [dcOp] using this

theorem mem_of_isDC {K L : Subgroup G} (hKL : K ≤ L) {x : G} (hx : x ∈ L) {A : Finset G} (hA : IsDC K x A) :
    ∀ a ∈ A, a ∈ L := by
  intro a ha
  obtain ⟨k₁, k₂, rfl⟩ := hA.1 a ha
  exact L.mul_mem (L.mul_mem (hKL k₁.2) hx) (hKL k₂.2)

structure Splits (J K L : Subgroup G) : Prop where
  le : K ≤ L
  mem : ∀ g ∈ L, g ∈ J ↔ g ∈ K
  dec : ∀ k ∈ J, ∃ k₁ ∈ K, ∃ k₂ ∈ J, k = k₁ * k₂ ∧ ∀ l ∈ L, Commute k₂ l

theorem Splits.le' {J K L : Subgroup G} (hs : Splits J K L) : K ≤ J := fun g hg => (hs.mem g (hs.le hg)).2 hg

theorem Splits.isDC {J K L : Subgroup G} (hs : Splits J K L) {x : G} (hx : x ∈ L) {A : Finset G} (hA : IsDC K x A) :
    IsDC J x A := by
  have hAL := mem_of_isDC hs.le hx hA
  refine ⟨fun a ha => ?_, ?_⟩
  · obtain ⟨k₁, k₂, rfl⟩ := hA.1 a ha
    exact ⟨⟨k₁, hs.le' k₁.2⟩, ⟨k₂, hs.le' k₂.2⟩, rfl⟩
  · rintro g ⟨k₁, k₂, rfl⟩
    obtain ⟨a₁, ha₁, b₁, hb₁, e₁, c₁⟩ := hs.dec k₁ k₁.2
    obtain ⟨a, ⟨ha, hak⟩, -⟩ := hA.2 (a₁ * x) ⟨⟨a₁, ha₁⟩, 1, by simp⟩
    have hmem : a⁻¹ * (k₁ * x * k₂) ∈ J := by
      have : a⁻¹ * ((k₁ : G) * x * k₂) = a⁻¹ * (a₁ * x) * (b₁ * k₂) := by
        rw [e₁, mul_assoc a₁ b₁ x, (c₁ x hx).eq]; group
      rw [this]
      exact J.mul_mem (hs.le' hak) (J.mul_mem hb₁ k₂.2)
    refine ⟨a, ⟨ha, hmem⟩, ?_⟩
    rintro a' ⟨ha', hmem'⟩
    have h1 : a⁻¹ * a' ∈ J := by
      have : a⁻¹ * a' = (a⁻¹ * ((k₁ : G) * x * k₂)) * (a'⁻¹ * (k₁ * x * k₂))⁻¹ := by group
      rw [this]; exact J.mul_mem hmem (J.inv_mem hmem')
    have h2 : a⁻¹ * a' ∈ K := (hs.mem _ (L.mul_mem (L.inv_mem (hAL a ha)) (hAL a' ha'))).1 h1
    exact (hA.2 a' (hA.1 a' ha')).unique ⟨ha', by simp [K.one_mem]⟩ ⟨ha, h2⟩

theorem Splits.sum_transl {J K L : Subgroup G} (hs : Splits J K L) {x : G} (hx : x ∈ L) {A : Finset G}
    (hA : IsDC K x A) {F : G → ℂ} (hF : ∀ k ∈ K, ∀ h, F (h * k) = F h) {κ : G} (hκ : κ ∈ J) (h : G) :
    ∑ a ∈ A, F (h * κ * a) = ∑ a ∈ A, F (h * a * κ) := by
  have hAL := mem_of_isDC hs.le hx hA
  obtain ⟨a₁, ha₁, b₁, -, rfl, c₁⟩ := hs.dec κ hκ
  have e1 : a₁ * b₁ = b₁ * a₁ := (c₁ a₁ (hs.le ha₁)).eq.symm
  rw [e1, ← mul_assoc, sum_inv_of_isDC hA hF a₁ ha₁]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [← mul_assoc, hF a₁ ha₁, mul_assoc, (c₁ a (hAL a ha)).eq, mul_assoc]

end Group

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

structure OffAt (β : GL (Fin V.rank) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) (K large₂ : Subgroup (GA D V)) : Prop where
  splits : Splits (levG V β L) K large₂
  chi : ∀ k ∈ K, levChi V β L k = 1

theorem inv_of_mem_mult {θ : InfFam D} {M : DSModel V S} {β : GL (Fin V.rank) (Lev.EAf D)}
    {L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank} {K large₂ : Subgroup (GA D V)} (hL : OffAt β L K large₂) {T : MMap M}
    (hT : T ∈ Mult θ M (levS V β L) (levChi V β L)) (v : M.Vec) : ∀ k ∈ K, ∀ h, T v (h * k) = T v h := by
  intro k hk h
  rw [((GlobalTheory.MultMem.mem_mult_iff D θ V S M _ _ T).1 hT).lev v k (hL.splits.le' hk) h, hL.chi k hk, one_mul]

theorem heckeOn_mem_mult {θ : InfFam D} {M : DSModel V S} {β : GL (Fin V.rank) (Lev.EAf D)}
    {L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank} {K large₂ : Subgroup (GA D V)} (hL : OffAt β L K large₂) (hf : large₂ ≤ GfC V)
    {x : GA D V} (hx : x ∈ large₂) {A : Finset (GA D V)} (hA : IsDC K x A) {T : MMap M}
    (hT : T ∈ Mult θ M (levS V β L) (levChi V β L)) : heckeOn M A T ∈ Mult θ M (levS V β L) (levChi V β L) := by
  classical
  have hAL := mem_of_isDC hL.splits.le hx hA
  have hT' := (GlobalTheory.MultMem.mem_mult_iff D θ V S M _ _ T).1 hT
  have h0 : IsMultMap θ M ∅ (levChi V β L) T := ⟨hT'.aut, hT'.cusp, fun _ _ hk => absurd hk (Set.notMem_empty _), hT'.equiv, hT'.cont⟩
  have hex : ∀ a : GA D V, ∃ T' : MMap M, a ∈ A → IsMultMap θ M ∅ (levChi V β L) T' ∧ ∀ v, T' v = rTr V a (T v) := by
    intro a
    by_cases ha : a ∈ A
    · obtain ⟨T', h⟩ := GlobalTheory.T.isMultMap_rightTranslate_finiteAdelic_normalizer θ M ∅ (levChi V β L) a (hf (hAL a ha))
        (fun k hk => absurd hk (Set.notMem_empty _)) T h0
      exact ⟨T', fun _ => h⟩
    · exact ⟨0, fun h => absurd h ha⟩
  choose Ta hTa using hex
  have e : heckeOn M A T = ∑ a ∈ A, Ta a := by
    ext v g
    rw [MultilinearMap.sum_apply, Finset.sum_apply]
    exact Finset.sum_congr rfl fun a ha => (congrFun ((hTa a ha).2 v) g).symm
  have h1 : IsMultMap θ M ∅ (levChi V β L) (heckeOn M A T) := by
    rw [← GlobalTheory.MultMem.mem_mult_iff, e]
    exact Submodule.sum_mem _ fun a ha => Submodule.subset_span (hTa a ha).1
  refine Submodule.subset_span ⟨h1.aut, h1.cusp, fun v k hk g => ?_, h1.equiv, h1.cont⟩
  show ∑ a ∈ A, T v (g * k * a) = levChi V β L k * ∑ a ∈ A, T v (g * a)
  rw [hL.splits.sum_transl hx hA (inv_of_mem_mult hL hT v) hk, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => hT'.lev v k hk _

theorem heckeLin_actL {β : GL (Fin V.rank) (Lev.EAf D)} {L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank} {K large₂ : Subgroup (GA D V)}
    (hL : OffAt β (flagL L) K large₂) {x : GA D V} (hx : x ∈ large₂) {A : Finset (GA D V)} (hA : IsDC K x A)
    {F : GA D V → ℂ} (hF : ∀ k ∈ K, ∀ h, F (h * k) = F h) (g0 : Formalism.L2.DIV.G0 L.Pg L.r) :
    actL V β L g0 (heckeLin V A F) = heckeLin V A (actL V β L g0 F) := by
  funext h
  show actG0 V β L g0 (heckeLin V A F) h = ∑ a ∈ A, actG0 V β L g0 F (h * a)
  unfold actG0
  by_cases hk : ∃ κ, IsLevelLift V β L g0 κ
  · simp only [dif_pos hk]
    have hκ : hk.choose ∈ levG V β (flagL L) := ⟨hk.choose_spec.1, hk.choose_spec.2.1, Subgroup.mem_top _⟩
    rw [heckeLin_apply, hL.splits.sum_transl hx hA hF hκ, Finset.mul_sum]
  · simp [dif_neg hk]

theorem heckeOn_mem_goodPart {θ : InfFam D} {M : DSModel V S} {β : GL (Fin V.rank) (Lev.EAf D)}
    {L L' : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank} {K large₂ : Subgroup (GA D V)} (hL : OffAt β (flagL L) K large₂)
    (hL' : OffAt β L' K large₂) (hf : large₂ ≤ GfC V) {G : Type} [Group G] [Fintype G] (eG : G ≃* Formalism.L2.DIV.G0 L.Pg L.r) (c : G → ℂ)
    {x : GA D V} (hx : x ∈ large₂) {A : Finset (GA D V)} (hA : IsDC K x A) {T : MMap M}
    (hT : T ∈ goodPart θ M (levS V β L') (levChi V β L') (gaL V β L eG c)) :
    heckeOn M A T ∈ goodPart θ M (levS V β L') (levChi V β L') (gaL V β L eG c) := by
  rw [mem_goodPart] at hT ⊢
  refine ⟨heckeOn_mem_mult hL' hf hx hA hT.1, fun v => ?_⟩
  show gaL V β L eG c (heckeLin V A (T v)) = heckeLin V A (T v)
  conv_rhs => rw [← hT.2 v]
  simp only [gaL, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
  exact Finset.sum_congr rfl fun g _ => by rw [heckeLin_actL hL hx hA (inv_of_mem_mult hL' hT.1 v)]

theorem offAt_of_place {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {N : ℕ}
    (hβ : IsBaseFrame V β Λ N) {P : HeightOneSpectrum (𝓞 D.host.E)} {e : Formalism.L2.Theta.AE D} (he : IsIdemAt e P)
    (hN : ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) {L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank}
    (hL : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ IsConjPl PP P) {K large₂ : Subgroup (GA D V)}
    (hLg : ∀ g, g ∈ large₂ ↔ SuppAt e V g) (hK : ∀ g, g ∈ K ↔ g ∈ locPart V (KsphC V ∅) e) : OffAt β L K large₂ := by
  have hp : IsPrimeIdem P e (e + cA D e) := Or.inl ⟨he, rfl⟩
  obtain ⟨h1, h2, h3⟩ := (GlobalTheory.T.level_hyperspecial_trivialCharacter_splits_off_places V β Λ N L hβ).2 P e _ hp hN hL
  obtain ⟨hf, hcf, -⟩ := (GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 P e _ hp
  have hc := ((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).1 _ hf hcf).2.2
  refine ⟨⟨fun g hg => (hLg g).2 ((hK g).1 hg).2, fun g hg => ?_, fun k hk => ?_⟩, fun k hk => ?_⟩
  · rw [h1 g ((hLg g).1 hg), hK]
    exact ⟨fun h => ⟨h, (hLg g).1 hg⟩, fun h => h.1⟩
  · obtain ⟨k₁, hk₁, k₂, hk₂, s₁, s₂, rfl⟩ := h3 k hk
    refine ⟨k₁, (hK _).2 ⟨(h1 _ s₁).1 hk₁, s₁⟩, k₂, hk₂, rfl, fun l hl => ?_⟩
    exact (hc (1 - (e + cA D e)) l k₂ (by rw [mul_sub, mul_one, hf, sub_self]) ((hLg l).1 hl) s₂).symm
  · have := (hK k).1 hk
    exact h2 k ((h1 k this.2).2 this.1) this.2

theorem isDC_of_isCosetRep {K : Subgroup (GA D V)} {K' : Set (GA D V)} (hK : ∀ g, g ∈ K ↔ g ∈ K') {x : GA D V}
    {A : Finset (GA D V)} (hA : IsCosetRep V K' x A) : IsDC K x A := by
  refine ⟨fun a ha => ?_, ?_⟩
  · obtain ⟨-, k₁, h₁, k₂, h₂, rfl⟩ := hA.1 a ha
    exact ⟨⟨k₁, (hK _).2 h₁⟩, ⟨k₂, (hK _).2 h₂⟩, rfl⟩
  · rintro g ⟨k₁, k₂, rfl⟩
    have := hA.2 _ ⟨k₁, (hK _).1 k₁.2, k₂, (hK _).1 k₂.2, rfl⟩
    simpa only [hK] using this

theorem comm_card_of_place {P : HeightOneSpectrum (𝓞 D.host.E)} {e : Formalism.L2.Theta.AE D} (he : IsIdemAt e P)
    {K large₂ : Subgroup (GA D V)} (hLg : ∀ g, g ∈ large₂ ↔ SuppAt e V g) (hK : ∀ g, g ∈ K ↔ g ∈ locPart V (KsphC V ∅) e)
    {x y : GA D V} (hx : x ∈ large₂) (hy : y ∈ large₂) {A B A' : Finset (GA D V)} (hA : IsDC K x A) (hB : IsDC K y B)
    (hA' : IsDC K x⁻¹ A') {F : GA D V → ℂ} (hF : ∀ k ∈ K, ∀ h, F (h * k) = F h) :
    heckeLin V A (heckeLin V B F) = heckeLin V B (heckeLin V A F) ∧ A.card = A'.card := by
  have hle : K ≤ large₂ := fun g hg => (hLg g).2 ((hK g).1 hg).2
  obtain ⟨τ, t1, t2, t3, t4, t5⟩ := (GlobalTheory.T.involution_spherical_hecke_anti V P e he).1
  refine GlobalTheory.T.exists_anti_involution_of_chars K large₂ 1 x y A B A' F
    (fun k hk => ⟨k, hk, 1, K.one_mem, hle hk, (mul_one k).symm, fun l _ => Commute.one_left l⟩) (fun _ _ => rfl)
    ⟨τ, fun g hg => (hLg _).2 (t1 g ((hLg g).1 hg)), fun a ha b hb => t2 a b ((hLg _).1 ha) ((hLg _).1 hb),
      fun a ha => t3 a ((hLg _).1 ha), fun k hk => (hK _).2 ⟨t4 k ((hK k).1 hk.1), t1 k ((hLg k).1 hk.2)⟩, fun g hg => ?_⟩
    (mem_of_isDC hle hx hA) (mem_of_isDC hle hy hB) (mem_of_isDC hle (large₂.inv_mem hx) hA') hA hB hA'
    (fun k h => by simpa using hF k k.2 h)
  obtain ⟨a, ha, b, hb, h⟩ := t5 g ((hLg g).1 hg)
  exact ⟨a, ⟨(hK a).2 ha, (hLg a).2 ha.2⟩, b, ⟨(hK b).2 hb, (hLg b).2 hb.2⟩, h⟩

theorem exists_lift {X : Type} [AddCommGroup X] [Module ℂ X] (HM : HMod X) (hinj : Function.Injective HM.e)
    (T : X →ₗ[ℂ] X) (hT : ∀ x, T (HM.e x) ∈ LinearMap.range HM.e) :
    ∃ φ : Module.End ℂ HM.H, ∀ x, HM.e (φ x) = T (HM.e x) := by
  refine ⟨(LinearEquiv.ofInjective HM.e hinj).symm.toLinearMap ∘ₗ (T ∘ₗ HM.e).codRestrict _ hT, fun x => ?_⟩
  have := congrArg Subtype.val ((LinearEquiv.ofInjective HM.e hinj).apply_symm_apply ((T ∘ₗ HM.e).codRestrict _ hT x))
  exact this

theorem adjoint_eq_of_isDC {θ : InfFam D} {M : DSModel V S} {J : Set (GA D V)} {χ : GA D V → ℂ} {μ : Measure (GA D V)}
    {𝓕 : Set (GA D V)} (hμ : μ.IsHaarMeasure) (hF : IsFundamentalDomain (GQ V) 𝓕 μ) {HM : HMod (MMap M)}
    {U : Submodule ℂ (MMap M)} (hM : HM.Is U (ipM M μ 𝓕)) (hU : U ≤ Mult θ M J χ) {K : Subgroup (GA D V)}
    (hinv : ∀ T ∈ U, ∀ v, ∀ k ∈ K, ∀ h, T v (h * k) = T v h) {x : GA D V} {A A' : Finset (GA D V)}
    (hA : IsDC K x A) (hA' : IsDC K x⁻¹ A') (hc : A.card = A'.card) {φ φ' : Module.End ℂ HM.H}
    (hφ : ∀ z, HM.e (φ z) = heckeOn M A (HM.e z)) (hφ' : ∀ z, HM.e (φ' z) = heckeOn M A' (HM.e z)) :
    LinearMap.adjoint φ = φ' := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  have : Countable (GQ V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig V.gram
  have := (GlobalTheory.T.adelicUnitary_unimodular_exists_fundamentalDomain D V μ hμ).1
  have hmem : ∀ z, HM.e z ∈ U := fun z => hM.2.1 ▸ LinearMap.mem_range_self _ z
  have hS := GlobalTheory.T.multiplicative_inner_product_model M μ 𝓕 HM U hM
  symm
  rw [LinearMap.eq_adjoint_iff]
  intro y z
  rw [← inner_conj_symm, ← inner_conj_symm y]
  congr 1
  by_cases hsm : ∀ τ, M.sm τ ≠ ⊥
  · obtain ⟨v, hv⟩ := GlobalTheory.SchurConst.exists_vec M hsm
    apply mul_right_cancel₀ hv
    rw [← (hS z (φ' y) v v).2, ← (hS (φ z) y v v).2, hφ, hφ']
    have hz := GlobalTheory.SchurConst.left_cont_of_mem θ M J χ _ (hU (hmem z)) v
    have hy := GlobalTheory.SchurConst.left_cont_of_mem θ M J χ _ (hU (hmem y)) v
    refine (GlobalTheory.T.double_coset_sum_fundamental_domain μ (GQ V) K 𝓕 x A A' (HM.e z v) (HM.e y v) hF (fun a ha => ?_) (fun a ha => ?_) hc hz.1 hy.1 hz.2 hy.2
      (hinv _ (hmem z) v) (hinv _ (hmem y) v) (hS z z v v).1 (hS y y v v).1).symm
    · obtain ⟨k₁, k₂, h⟩ := hA.1 a ha
      exact ⟨k₁, k₁.2, k₂, k₂.2, h⟩
    · obtain ⟨k₁, k₂, h⟩ := hA'.1 a ha
      exact ⟨k₁, k₁.2, k₂, k₂.2, h⟩
  · push Not at hsm
    obtain ⟨τ, hτ⟩ := hsm
    have h0 : y = 0 := by
      apply hM.1
      rw [map_zero]
      ext v g
      have : v τ = 0 := Subtype.ext ((Submodule.eq_bot_iff _).1 hτ _ (v τ).2)
      rw [(HM.e y).map_coord_zero τ this]
      rfl
    simp [h0]

theorem exists_heckeOps {θ : InfFam D} {M : DSModel V S} {β : GL (Fin V.rank) (Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {N : ℕ} (hβ : IsBaseFrame V β Λ N)
    {L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank} (hχ : ∀ k ∈ levG V β L, levChi V β L k = 1)
    {G : Type} [Group G] [Fintype G] (eG : G ≃* Formalism.L2.DIV.G0 L.Pg L.r) (c : G → ℂ)
    {μ : Measure (GA D V)} {𝓕 : Set (GA D V)} (hμ : μ.IsHaarMeasure) (hF : IsFundamentalDomain (GQ V) 𝓕 μ)
    {HM : HMod (MMap M)} (hM : HM.Is (goodPart θ M (levS V β L) (levChi V β L) (gaL V β L eG c)) (ipM M μ 𝓕))
    {I : Type} (pl : I → HeightOneSpectrum (𝓞 D.host.E)) (hs : ∀ i, ∃ e, IsIdemAt e (pl i))
    (hN : ∀ i, ((N : ℕ) : 𝓞 D.host.E) ∉ (pl i).asIdeal)
    (hoff : ∀ i PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ pl i ∧ ¬ IsConjPl PP (pl i)) :
    ∃ φ : I × ℕ → Module.End ℂ HM.H, (∀ a b, Commute (φ a) (φ b)) ∧ (∀ a, Commute (φ a) (LinearMap.adjoint (φ a))) ∧
      (∀ (P : Formalism.L2.DIV.LevelP L.Pg L.r ℂ) a,
        ((goodPart θ M (levS V β (withP L P)) (levChi V β (withP L P)) (gaL V β L eG c)).comap HM.e).map (φ a) ≤
          (goodPart θ M (levS V β (withP L P)) (levChi V β (withP L P)) (gaL V β L eG c)).comap HM.e) ∧
      ∀ i k, k ≤ V.rank → (∃ α A, IsHeckeAt V (pl i) k α ∧ IsDC (levG V β L) α⁻¹ A) ∧
        ∀ α A, IsHeckeAt V (pl i) k α → IsDC (levG V β L) α⁻¹ A → ∀ z, HM.e (φ (i, k) z) = heckeOn M A (HM.e z) := by
  choose e he using hs
  have hp : ∀ i, IsPrimeIdem (pl i) (e i) (e i + cA D (e i)) := fun i => Or.inl ⟨he i, rfl⟩
  have hq := fun i => (GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 (pl i) (e i) _ (hp i)
  have hLg : ∀ i, ∃ large₂ : Subgroup (GA D V), ∀ g, g ∈ large₂ ↔ SuppAt (e i) V g :=
    fun i => ((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).1 _ (hq i).1 (hq i).2.1).1
  choose large₂ hLg using hLg
  have hfin : ∀ i, large₂ i ≤ GfC V := fun i g hg => (hq i).2.2.1 g ((hLg i g).1 hg)
  let K : I → Subgroup (GA D V) := fun i => levG V β L ⊓ large₂ i
  have hK : ∀ i g, g ∈ K i ↔ g ∈ locPart V (KsphC V ∅) (e i) := by
    intro i g
    have h1 := ((GlobalTheory.T.level_hyperspecial_trivialCharacter_splits_off_places V β Λ N L hβ).2 (pl i) (e i) _ (hp i) (hN i) (hoff i)).1 g
    exact ⟨fun h => ⟨(h1 ((hLg i g).1 h.2)).1 h.1, (hLg i g).1 h.2⟩, fun h => ⟨(h1 h.2).2 h.1, (hLg i g).2 h.2⟩⟩
  have hoL : ∀ i, OffAt β L (K i) (large₂ i) := fun i => offAt_of_place hβ (he i) (hN i) (hoff i) (hLg i) (hK i)
  have hoP : ∀ i P, OffAt β (withP L P) (K i) (large₂ i) :=
    fun i P => offAt_of_place (L := withP L P) hβ (he i) (hN i) (hoff i) (hLg i) (hK i)
  have hrep : ∀ i, ∀ x ∈ large₂ i, ∃ A, IsDC (K i) x A := by
    intro i x hx
    obtain ⟨A, -, hA⟩ := (GlobalTheory.T.involution_spherical_hecke_anti V (pl i) (e i) (he i)).2.1 x ((hLg i x).1 hx)
    exact ⟨A, isDC_of_isCosetRep (hK i) hA⟩
  have hα : ∀ a : I × ℕ, ∃ α ∈ large₂ a.1, a.2 ≤ V.rank → ∃ ϖ : 𝓞 D.host.E, ϖ ∈ (pl a.1).asIdeal ∧ ϖ ∉ (pl a.1).asIdeal ^ 2 ∧
      IsHeckeElt V (e a.1) (ϖ : D.host.E) a.2 α := by
    rintro ⟨i, k⟩
    by_cases hk : k ≤ V.rank
    · obtain ⟨ϖ, h1, h2⟩ := Ideal.exists_mem_pow_notMem_pow_succ (pl i).asIdeal (pl i).ne_bot (pl i).isPrime.ne_top 1
      rw [pow_one] at h1
      obtain ⟨α, hα⟩ := ((GlobalTheory.T.involution_spherical_hecke_anti V (pl i) (e i) (he i)).2.2 ϖ h1 h2).1 k hk
      exact ⟨α, (hLg i α).2 hα.2.1, fun _ => ⟨ϖ, h1, h2, hα⟩⟩
    · exact ⟨1, (large₂ i).one_mem, fun h => absurd h hk⟩
  choose α hαL hα using hα
  choose A hA using fun a : I × ℕ => hrep a.1 (α a)⁻¹ ((large₂ a.1).inv_mem (hαL a))
  choose A' hA' using fun a : I × ℕ => hrep a.1 (α a)⁻¹⁻¹ ((large₂ a.1).inv_mem ((large₂ a.1).inv_mem (hαL a)))
  have hmem : ∀ z, HM.e z ∈ goodPart θ M (levS V β L) (levChi V β L) (gaL V β L eG c) :=
    fun z => hM.2.1 ▸ LinearMap.mem_range_self _ z
  have hinv : ∀ i, ∀ T ∈ goodPart θ M (levS V β L) (levChi V β L) (gaL V β L eG c), ∀ v, ∀ k ∈ K i, ∀ h,
      T v (h * k) = T v h := fun i T hT v => inv_of_mem_mult (hoL i) (goodPart_le _ _ _ _ _ hT) v
  have hlift : ∀ i, ∀ x ∈ large₂ i, ∀ B, IsDC (K i) x B → ∃ φ : Module.End ℂ HM.H, ∀ z, HM.e (φ z) = heckeOn M B (HM.e z) :=
    fun i x hx B hB => exists_lift HM hM.1 _ fun z => by
      rw [hM.2.1]
      exact heckeOn_mem_goodPart (hoP i _) (hoL i) (hfin i) eG c hx hB (hmem z)
  choose φ hφ using fun a : I × ℕ => hlift a.1 _ ((large₂ a.1).inv_mem (hαL a)) _ (hA a)
  choose φ' hφ' using fun a : I × ℕ => hlift a.1 _ ((large₂ a.1).inv_mem ((large₂ a.1).inv_mem (hαL a))) _ (hA' a)
  have hcomm : ∀ (ψ ψ' : Module.End ℂ HM.H) (B B' : Finset (GA D V)), (∀ z, HM.e (ψ z) = heckeOn M B (HM.e z)) →
      (∀ z, HM.e (ψ' z) = heckeOn M B' (HM.e z)) →
      (∀ z v, heckeLin V B (heckeLin V B' (HM.e z v)) = heckeLin V B' (heckeLin V B (HM.e z v))) → Commute ψ ψ' := by
    intro ψ ψ' B B' h h' hc
    ext z
    apply hM.1
    rw [Module.End.mul_apply, Module.End.mul_apply, h, h', h', h]
    ext v : 1
    exact hc z v
  refine ⟨φ, fun a b => hcomm _ _ _ _ (hφ a) (hφ b) fun z v => ?_, fun a => ?_, fun P a => ?_, fun i k hk => ⟨?_, ?_⟩⟩
  · rcases (hq a.1).2.2.2.2 (pl b.1) (e b.1) _ (hp b.1) with h0 | ⟨h1, -⟩
    · have hc := ((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).1 _ (hq a.1).1 (hq a.1).2.1).2.2 (e b.1 + cA D (e b.1))
      funext h
      simp only [heckeLin_apply]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun y hy => Finset.sum_congr rfl fun x hx => ?_
      have := hc x y h0 ((hLg _ x).1 (mem_of_isDC (hoL a.1).splits.le ((large₂ a.1).inv_mem (hαL a)) (hA a) x hx))
        ((hLg _ y).1 (mem_of_isDC (hoL b.1).splits.le ((large₂ b.1).inv_mem (hαL b)) (hA b) y hy))
      rw [mul_assoc, this.eq, mul_assoc]
    · have hLL : large₂ b.1 = large₂ a.1 := by
        ext g
        rw [hLg, hLg, SuppAt, SuppAt, h1]
      have hKK : K b.1 = K a.1 := by simp only [K, hLL]
      exact (comm_card_of_place (he a.1) (hLg a.1) (hK a.1) ((large₂ a.1).inv_mem (hαL a)) ((large₂ a.1).inv_mem (hLL ▸ hαL b))
        (hA a) (hKK ▸ hA b) (hA' a) (hinv a.1 _ (hmem z) v)).1
  · have hc := (comm_card_of_place (F := 0) (he a.1) (hLg a.1) (hK a.1) ((large₂ a.1).inv_mem (hαL a)) ((large₂ a.1).inv_mem (hαL a))
        (hA a) (hA a) (hA' a) (fun _ _ _ => rfl)).2
    rw [adjoint_eq_of_isDC hμ hF hM (goodPart_le _ _ _ _ _) (hinv a.1) (hA a) (hA' a) hc (hφ a) (hφ' a)]
    exact hcomm _ _ _ _ (hφ a) (hφ' a) fun z v => (comm_card_of_place (he a.1) (hLg a.1) (hK a.1) ((large₂ a.1).inv_mem (hαL a))
      ((large₂ a.1).inv_mem ((large₂ a.1).inv_mem (hαL a))) (hA a) (hA' a) (hA' a) (hinv a.1 _ (hmem z) v)).1
  · rintro _ ⟨z, hz, rfl⟩
    rw [Submodule.mem_comap, hφ]
    exact heckeOn_mem_goodPart (hoP a.1 _) (hoP a.1 P) (hfin a.1) eG c ((large₂ a.1).inv_mem (hαL a)) (hA a) hz
  · obtain ⟨ϖ, h1, h2, h3⟩ := hα (i, k) hk
    exact ⟨α (i, k), A (i, k), ⟨e i, ϖ, he i, h1, h2, h3⟩, (hoL i).splits.isDC ((large₂ i).inv_mem (hαL (i, k))) (hA (i, k))⟩
  · rintro α' B ⟨e', ϖ', he', h1', h2', h3'⟩ hB z
    obtain ⟨ϖ, h1, h2, h3⟩ := hα (i, k) hk
    obtain ⟨rfl, -⟩ := (hq i).2.2.2.1 e' _ (Or.inl ⟨he', rfl⟩)
    obtain ⟨a, ha, b, hb, rfl⟩ := (((GlobalTheory.T.involution_spherical_hecke_anti V (pl i) (e i) (he i)).2.2 ϖ h1 h2).2 k _ h3).2 ϖ' α' h1' h2' h3'
    rw [hφ]
    ext v h
    refine sum_eq_of_isDC ((hoL i).splits.isDC ((large₂ i).inv_mem (hαL (i, k))) (hA (i, k))) hB
      ⟨⟨b, ((hK i b).2 hb).1⟩⁻¹, ⟨a, ((hK i a).2 ha).1⟩⁻¹, by simp [mul_assoc]⟩ (fun k hk h => ?_) h
    rw [((GlobalTheory.MultMem.mem_mult_iff D θ V S M _ _ _).1 (goodPart_le _ _ _ _ _ (hmem z))).lev v k hk h, hχ k hk, one_mul]

end GlobalTheory.HeckeModel
