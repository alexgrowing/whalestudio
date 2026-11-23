import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsDCOfMemDoubleCoset
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicInnerDoubleCosetOpAdjoint
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ReprMemOfBasisRational
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DcOpCommOfCommute
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DivisorsAtInvDualLabelAndStabilizerMul
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVectorStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalHeckeCombinationsCommuteFixedVectorsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalHeckeConjPlaceEqDualLabelStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DefiniteOps

open GlobalTheory.SplitHeckeAdj GlobalTheory.IdemSupport

section Abstract

variable {H G : Type} [Group H] [Group G]

def rtr (φ : H →* G) (W : Type) [AddCommGroup W] [Module ℂ W] : H →* Module.End ℂ (G → W) where
  toFun γ := LinearMap.funLeft ℂ W fun h => h * φ γ
  map_one' := by ext F h; simp [LinearMap.funLeft]
  map_mul' a b := by ext F h; simp [LinearMap.funLeft, mul_assoc]

theorem rtr_apply (φ : H →* G) {W : Type} [AddCommGroup W] [Module ℂ W] (γ : H) (F : G → W) (h : G) :
    rtr φ W γ F h = F (h * φ γ) := rfl

theorem isDC_image [DecidableEq G] (φ : H →* G) (J : Subgroup G) (L : Subgroup H) (K : Set H)
    (hK : ∀ g, g ∈ K ↔ g ∈ L ∧ φ g ∈ J)
    (hsp : ∀ k ∈ J, ∃ k₁ ∈ J, ∃ k₂ ∈ J, k₁ ∈ L.map φ ∧ k = k₁ * k₂ ∧ ∀ l ∈ L.map φ, Commute k₂ l)
    (α : H) (hα : α ∈ L) (R : Finset H) (hR : ∀ γ ∈ R, γ ∈ L)
    (h1 : ∀ γ ∈ R, ∃ k₁ ∈ K, ∃ k₂ ∈ K, γ = k₁ * α * k₂)
    (h2 : ∀ x, (∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * α * k₂) → ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ K) :
    Bridge.IsDC J (φ α) (R.image φ) := by
  constructor
  · intro a ha
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨k₁, a₁, k₂, a₂, rfl⟩ := h1 γ hγ
    exact ⟨⟨φ k₁, ((hK _).1 a₁).2⟩, ⟨φ k₂, ((hK _).1 a₂).2⟩, by simp⟩
  · rintro g ⟨k₁, k₂, rfl⟩
    obtain ⟨_, a₁, b₁, hb₁, ⟨u₁, hu₁, rfl⟩, e₁, c₁⟩ := hsp k₁ k₁.2
    obtain ⟨_, a₂, b₂, hb₂, ⟨u₂, hu₂, rfl⟩, e₂, -⟩ := hsp k₂ k₂.2
    have hy : u₁ * α * u₂ ∈ L := L.mul_mem (L.mul_mem hu₁ hα) hu₂
    have e : (k₁ : G) * φ α * k₂ = φ (u₁ * α * u₂) * (b₁ * b₂) := by
      have c := (c₁ (φ (α * u₂)) ⟨_, L.mul_mem hα hu₂, rfl⟩).eq
      rw [e₁, e₂, mul_assoc u₁, map_mul φ u₁, mul_assoc (φ u₁) (φ (α * u₂)), ← mul_assoc (φ (α * u₂)), ← c, map_mul]
      simp only [mul_assoc]
    have key : ∀ γ ∈ R, ((φ γ)⁻¹ * ((k₁ : G) * φ α * k₂) ∈ J ↔ γ⁻¹ * (u₁ * α * u₂) ∈ K) := by
      intro γ hγ
      rw [e, ← mul_assoc, J.mul_mem_cancel_right (J.mul_mem hb₁ hb₂), hK, map_mul φ γ⁻¹, map_inv]
      exact ⟨fun h => ⟨L.mul_mem (L.inv_mem (hR γ hγ)) hy, h⟩, fun h => h.2⟩
    obtain ⟨γ, ⟨hγ, hγ'⟩, hu⟩ := h2 _ ⟨u₁, (hK _).2 ⟨hu₁, a₁⟩, u₂, (hK _).2 ⟨hu₂, a₂⟩, rfl⟩
    refine ⟨φ γ, ⟨Finset.mem_image_of_mem _ hγ, (key γ hγ).2 hγ'⟩, ?_⟩
    rintro _ ⟨ha, ha'⟩
    obtain ⟨γ', hγ₁, rfl⟩ := Finset.mem_image.1 ha
    rw [hu γ' ⟨hγ₁, (key γ' hγ₁).1 ha'⟩]

theorem rep_change (K : Subgroup H) (Ks : Set H) (hK : ∀ g, g ∈ Ks ↔ g ∈ K) (α g : H) (R : Finset H)
    (h1 : ∀ γ ∈ R, ∃ k₁ ∈ Ks, ∃ k₂ ∈ Ks, γ = k₁ * g * k₂)
    (h2 : ∀ x, (∃ k₁ ∈ Ks, ∃ k₂ ∈ Ks, x = k₁ * α * k₂) → ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ Ks) :
    ∀ x, (∃ k₁ ∈ Ks, ∃ k₂ ∈ Ks, x = k₁ * g * k₂) → ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ Ks := by
  obtain ⟨γ, ⟨hγ, hγ'⟩, -⟩ := h2 α ⟨1, (hK _).2 K.one_mem, 1, (hK _).2 K.one_mem, by simp⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := h1 γ hγ
  rintro x ⟨k₁, a₁, k₂, a₂, rfl⟩
  rw [hK] at ha hb a₁ a₂ hγ'
  refine h2 _ ⟨k₁ * a⁻¹, (hK _).2 (K.mul_mem a₁ (K.inv_mem ha)), ((a * g * b)⁻¹ * α)⁻¹ * b⁻¹ * k₂,
    (hK _).2 (K.mul_mem (K.mul_mem (K.inv_mem hγ') (K.inv_mem hb)) a₂), by group⟩

theorem dcOp_image [DecidableEq G] (φ : H →* G) {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (R : Finset H)
    (hi : ∀ g ∈ R, ∀ g' ∈ R, φ g = φ g' → g = g') (F : G → W) :
    Bridge.dcOp (R.image φ) F = ∑ γ ∈ R, rtr φ W γ F := by
  funext h
  rw [Bridge.dcOp, Finset.sum_image hi, Finset.sum_apply]
  rfl

theorem dcOp_mem {Γ W : Type} [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (ι : Γ →* G)
    (ρ : Γ →* Module.End ℂ W) (J L : Subgroup G) (χ : J →* ℂˣ) (x : G) (A : Finset G)
    (hsp : ∀ k ∈ J, ∃ k₁ ∈ J, ∃ k₂ ∈ J, k₁ ∈ L ∧ k = k₁ * k₂ ∧ ∀ l ∈ L, Commute k₂ l)
    (hχ : ∀ k : J, (k : G) ∈ L → χ k = 1) (hA : ∀ a ∈ A, a ∈ L) (hx : Bridge.IsDC J x A)
    (F : G → W) (hF : F ∈ Bridge.AdForms ι ρ J χ) : Bridge.dcOp A F ∈ Bridge.AdForms ι ρ J χ := by
  intro γ h k
  have h1 : ∀ (k : J) (h : G), F (h * k) = (χ k : ℂ) • F h := fun k h => by simpa using hF 1 h k
  have h2 : ∀ h, F (ι γ * h) = ρ γ (F h) := fun h => by simpa using hF γ h 1
  rw [(GlobalTheory.HkB.dcOp_eq_and_level J L χ x x A A F hsp hχ hA hA hx hx ⟨1, 1, by simp⟩ h1).2 k]
  simp only [Bridge.dcOp, map_sum, mul_assoc, h2]

theorem exists_lift {X : Type} [AddCommGroup X] [Module ℂ X] (M : HMod X) (U : Submodule ℂ X) (ip : X → X → ℂ)
    (hM : M.Is U ip) (S : Module.End ℂ X) (hS : ∀ F ∈ U, S F ∈ U) :
    ∃ s : Module.End ℂ M.H, ∀ x, M.e (s x) = S (M.e x) := by
  have h : ∀ x, (S ∘ₗ M.e) x ∈ LinearMap.range M.e := fun x => by
    rw [hM.2.1]; exact hS _ (hM.2.1 ▸ LinearMap.mem_range_self _ x)
  refine ⟨(LinearEquiv.ofInjective M.e hM.1).symm.toLinearMap ∘ₗ LinearMap.codRestrict _ (S ∘ₗ M.e) h, fun x => ?_⟩
  exact LinearEquiv.ofInjective_symm_apply M.e (h := hM.1) _

theorem right_inv {Γ W : Type} [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (φ : H →* G) (ι : Γ →* G)
    (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) (F : G → W) (hF : F ∈ Bridge.AdForms ι ρ J χ) (k : H)
    (hk : φ k ∈ J) (h1 : χ ⟨φ k, hk⟩ = 1) : rtr φ W k F = F := by
  funext h
  have := hF 1 h ⟨φ k, hk⟩
  rw [h1, map_one, map_one, one_mul, Module.End.one_apply, Units.val_one, one_smul] at this
  exact this

theorem zero_mem_adj {Γ W I : Type} [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Fintype I] (ι : Γ →* G)
    (J : Subgroup G) (y : I → G) (U : Submodule ℂ (G → W)) (S S' : Module.End ℂ (G → W)) (hS : S = 0) (hS' : S' = 0)
    (F : G → W) : S F ∈ U ∧ ∀ F' ∈ U, Bridge.adInner ι J y (S F) F' = Bridge.adInner ι J y F (S' F') := by
  subst hS hS'
  refine ⟨U.zero_mem, fun F' _ => ?_⟩
  simp only [Bridge.adInner, LinearMap.zero_apply, Pi.zero_apply, inner_zero_left, inner_zero_right]

theorem mem_adj_congr {X : Type} (U : X → Prop) (ip : X → X → ℂ) {F a b : X} {S S' : X → X} (e : a = b)
    (e' : ∀ F', U F' → S F' = S' F') (hb : U b) (h : ∀ F', U F' → ip b F' = ip F (S' F')) :
    U a ∧ ∀ F', U F' → ip a F' = ip F (S F') := by
  subst e
  exact ⟨hb, fun F' hF' => (e' F' hF').symm ▸ h F' hF'⟩

theorem exists_normalFam {D : D7} {X : Type} [AddCommGroup X] [Module ℂ X] (M : HMod X) (U : Submodule ℂ X) (ip : X → X → ℂ)
    (hM : M.Is U ip) (ok : Pl D.host.E → Prop) (O : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ X)
    (O0 : ∀ P, O P 0 = 0) (Oa : ∀ P c c', O P (c + c') = O P c + O P c')
    (Os : ∀ P d z, O P (Finsupp.single d z) = z • O P (Finsupp.single d 1))
    (Oc : ∀ P P', ok P → ∀ c c', ∀ F ∈ U, O P c (O P' c' F) = O P' c' (O P c F))
    (Om : ∀ P, ok P → ∀ d, ∀ F ∈ U, O P (Finsupp.single d 1) F ∈ U ∧
      ∀ F' ∈ U, ip (O P (Finsupp.single d 1) F) F' = ip F (O P (Finsupp.single (dualLab d) 1) F')) :
    ∃ h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ M.H,
      (∀ P, ok P → ∀ c x, M.e (h P c x) = O P c (M.e x)) ∧ NormalFam ok h := by
  have hmem : ∀ x, M.e x ∈ U := fun x => hM.2.1 ▸ LinearMap.mem_range_self _ x
  have hex : ∀ P c, ∃ s : Module.End ℂ M.H, ok P → ∀ x, M.e (s x) = O P c (M.e x) := by
    intro P c
    by_cases hP : ok P
    swap
    · exact ⟨0, fun h => absurd h hP⟩
    refine (exists_lift M _ _ hM (O P c) ?_).imp fun s hs _ => hs
    intro F hF
    induction c using Finsupp.induction_linear with
    | zero => rw [O0]; exact Submodule.zero_mem _
    | add c c' h h' => rw [Oa]; exact Submodule.add_mem _ h h'
    | single d z =>
      rw [Os]
      exact Submodule.smul_mem _ z (Om P hP d F hF).1
  choose h hh using hex
  refine ⟨h, fun P hP c x => hh P c hP x, fun P P' hP hP' c c' => ?_, fun P hP c => ?_⟩
  · refine LinearMap.ext fun x => hM.1 ?_
    rw [Module.End.mul_apply, Module.End.mul_apply, hh P c hP, hh P' c' hP', hh P' c' hP', hh P c hP]
    exact Oc P P' hP c c' _ (hmem x)
  · have h0 : h P 0 = 0 := LinearMap.ext fun x => hM.1 (by
      rw [hh P _ hP, O0, LinearMap.zero_apply, LinearMap.zero_apply, map_zero])
    have ha : ∀ c c', h P (c + c') = h P c + h P c' := fun c c' => LinearMap.ext fun x => hM.1 (by
      rw [LinearMap.add_apply, map_add, hh P _ hP, hh P _ hP, hh P _ hP, Oa, LinearMap.add_apply])
    have hs : ∀ d z, h P (Finsupp.single d z) = z • h P (Finsupp.single d 1) := fun d z => LinearMap.ext fun x => hM.1 (by
      rw [LinearMap.smul_apply, map_smul, hh P _ hP, hh P _ hP, Os, LinearMap.smul_apply])
    induction c using Finsupp.induction_linear with
    | zero => rw [Finsupp.mapRange_zero, dualC, Finsupp.mapDomain_zero, h0, map_zero]
    | add c c' e e' =>
      rw [Finsupp.mapRange_add (star_add), dualC, Finsupp.mapDomain_add, ha, ha, map_add, e, e']
      rfl
    | single d z =>
      rw [Finsupp.mapRange_single, dualC, Finsupp.mapDomain_single, hs d, hs (dualLab d), map_smulₛₗ]
      congr 1
      symm
      rw [LinearMap.eq_adjoint_iff]
      intro x x'
      rw [← inner_conj_symm, ← inner_conj_symm x, hM.2.2, hM.2.2, hh P _ hP, hh P _ hP,
        (Om P hP d _ (hmem x')).2 _ (hmem x)]

end Abstract

variable {D : D7}

theorem opOf_add {V : HSp D} {M : Type} [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (P : Pl D.host.E)
    (c c' : List ℤ →₀ ℂ) : opOf π P (c + c') = opOf π P c + opOf π P c' :=
  Finsupp.sum_add_index' (fun _ => zero_smul _ _) fun _ _ _ => add_smul _ _ _

theorem opOf_zero {V : HSp D} {M : Type} [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (P : Pl D.host.E) :
    opOf π P 0 = 0 := Finsupp.sum_zero_index

theorem opOf_single {V : HSp D} {M : Type} [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (P : Pl D.host.E)
    (d : List ℤ) (z : ℂ) : opOf π P (Finsupp.single d z) = z • ∑ γ ∈ rep V P d, π γ :=
  Finsupp.sum_single_index (zero_smul _ _)

theorem hkF_eq (V : HSp D) {W : Type} [AddCommGroup W] [Module ℂ W] (P : Pl D.host.E) (c : List ℤ →₀ ℂ)
    (F : Bridge.Gf V → W) : hkF V P c F = opOf (rtr (fin V) W) P c F := by
  funext h
  simp only [hkF, opOf, Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply, rtr_apply]

theorem rep_spec {V : HSp D} {P : Pl D.host.E} {d : List ℤ} (h : IsLab V P d) : SphOp V P d (rep V P d) := by
  unfold Hk3.rep
  rw [dif_pos h]
  exact h.choose_spec

theorem rep_empty {V : HSp D} {P : Pl D.host.E} {d : List ℤ} (h : ¬ IsLab V P d) : rep V P d = ∅ := by
  unfold Hk3.rep
  rw [dif_neg h]

theorem opOf_nonlab {V : HSp D} {M : Type} [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) {P : Pl D.host.E}
    {d : List ℤ} (h : ¬ IsLab V P d) : opOf π P (Finsupp.single d 1) = 0 := by
  rw [opOf_single, rep_empty h, Finset.sum_empty, smul_zero]

theorem supp_of_sphOp {V : HSp D} {P : Pl D.host.E} {d : List ℤ} {R : Finset (GA D V)} {e f : AE D}
    (hP : IsPrimeIdem P e f) (h : SphOp V P d R) : ∀ γ ∈ R, SuppF V f γ := by
  obtain ⟨e', f', ϖ, α, -, h1, -, -, -, -, -, -, -, h2, -⟩ := h
  obtain ⟨rfl, rfl⟩ := ((supported_group_and_prime_idempotents V).2.2.1 P e f hP).2.2.2.1 e' f' h1
  exact h2

theorem supp_rep {V : HSp D} {P : Pl D.host.E} (d : List ℤ) {e f : AE D} (hP : IsPrimeIdem P e f) :
    ∀ γ ∈ rep V P d, SuppF V f γ := by
  by_cases h : IsLab V P d
  · exact supp_of_sphOp hP (rep_spec h)
  · rw [rep_empty h]; simp

theorem mem_hyp {V : HSp D} {P : Pl D.host.E} {e f : AE D} (hP : IsPrimeIdem P e f) (k : GA D V) :
    k ∈ hyp V P ↔ k ∈ KsphC V ∅ ∧ SuppF V f k := by
  refine ⟨fun ⟨h, e', f', h1, h2⟩ => ?_, fun h => ⟨h.1, e, f, hP, h.2⟩⟩
  obtain ⟨rfl, rfl⟩ := ((supported_group_and_prime_idempotents V).2.2.1 P e f hP).2.2.2.1 e' f' h1
  exact ⟨h, h2⟩

theorem opOf_comm {V : HSp D} {M : Type} [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (P P' : Pl D.host.E)
    (c c' : List ℤ →₀ ℂ) (u : M) (hu : ∀ k ∈ hyp V P, π k u = u) :
    opOf π P c (opOf π P' c' u) = opOf π P' c' (opOf π P c u) := by
  obtain ⟨e, f, hP⟩ := (supported_group_and_prime_idempotents V).2.1 P
  obtain ⟨e', f', hP'⟩ := (supported_group_and_prime_idempotents V).2.1 P'
  rcases ((supported_group_and_prime_idempotents V).2.2.1 P e f hP).2.2.2.2 P' e' f' hP' with h | ⟨-, h | h⟩
  · have : Commute (opOf π P c) (opOf π P' c') := by
      refine Commute.sum_left _ _ _ fun d _ => Commute.sum_right _ _ _ fun d' _ => ?_
      refine Commute.smul_left (Commute.smul_right ?_ _) _
      refine Commute.sum_left _ _ _ fun γ hγ => Commute.sum_right _ _ _ fun γ' hγ' => ?_
      exact (commute_of_suppF V h (supp_rep d hP γ hγ) (supp_rep d' hP' γ' hγ')).map π
    exact LinearMap.congr_fun this.eq u
  · rw [h]; exact GlobalTheory.T.sphericalHeckeCombinations_commute_fixedVectors V P c c' M π u hu
  · rw [eq_conj_of_isConjPl h, (GlobalTheory.T.sphericalHecke_conjPlace_eq_dualLabel V P).2.2 c' M π u hu,
      (GlobalTheory.T.sphericalHecke_conjPlace_eq_dualLabel V P).2.2 c' M π _ ((GlobalTheory.T.spherical_label_operators_on_hyperspecial_fixed_vectors V P).2.1 c M π u hu)]
    exact GlobalTheory.T.sphericalHeckeCombinations_commute_fixedVectors V P c _ M π u hu

theorem pairwise_dualLab {d : List ℤ} (h : d.Pairwise fun a b => b ≤ a) : (dualLab d).Pairwise fun a b => b ≤ a := by
  unfold dualLab
  rw [List.pairwise_reverse, List.pairwise_map]
  exact h.imp fun h => neg_le_neg h

theorem exists_sphOp_pair {V : HSp D} {P : Pl D.host.E} {d : List ℤ} {e f : AE D} (hP : IsPrimeIdem P e f)
    (K : Subgroup (GA D V)) (hK : ∀ g, g ∈ hyp V P ↔ g ∈ K) (h : IsLab V P d) :
    ∃ α R', SuppF V f α ∧ IsCosetRep V {k | k ∈ KsphC V ∅ ∧ SuppF V f k} α (Hk3.rep V P d) ∧ SphOp V P (dualLab d) R' ∧
      IsCosetRep V {k | k ∈ KsphC V ∅ ∧ SuppF V f k} α⁻¹ R' := by
  have hu := ((supported_group_and_prime_idempotents V).2.2.1 P e f hP).2.2.2.1
  have hK' : ∀ g, g ∈ {k | k ∈ KsphC V ∅ ∧ SuppF V f k} ↔ g ∈ K := fun g => (mem_hyp hP g).symm.trans (hK g)
  obtain ⟨e', f', ϖ, α, h0, h1, h2, h3, h4, h5, h6, h7, h8, -, h10⟩ := rep_spec h
  obtain ⟨he, hf⟩ := hu e' f' h1
  rw [hf] at h5 h6 h7 h10
  rw [he] at h8
  obtain ⟨d', l1, -, l2⟩ := (GlobalTheory.T.spherical_label_operators_on_hyperspecial_fixed_vectors V P).2.2.2.2 e f α hP h7
  have l3 := rep_spec (((GlobalTheory.T.spherical_label_operators_on_hyperspecial_fixed_vectors V P).2.2.2.1 d').1.1 l1)
  have l4 := supp_of_sphOp hP l3
  obtain ⟨e'', f'', -, α', -, g1, -, -, -, -, -, -, -, -, g2⟩ := l3
  rw [(hu e'' f'' g1).2] at g2
  have l5 : ∀ γ ∈ Hk3.rep V P (dualLab d'), ∃ k₁ ∈ {k | k ∈ KsphC V ∅ ∧ SuppF V f k},
      ∃ k₂ ∈ {k | k ∈ KsphC V ∅ ∧ SuppF V f k}, γ = k₁ * α⁻¹ * k₂ := fun γ hγ => by
    obtain ⟨k₁, a₁, k₂, a₂, hh⟩ := l2 γ hγ
    exact ⟨k₁, (mem_hyp hP _).1 a₁, k₂, (mem_hyp hP _).1 a₂, hh⟩
  have l6 : IsCosetRep V {k | k ∈ KsphC V ∅ ∧ SuppF V f k} α⁻¹ (Hk3.rep V P (dualLab d')) :=
    ⟨fun γ hγ => ⟨(g2.1 γ hγ).1, l5 γ hγ⟩, rep_change K _ hK' α' α⁻¹ _ l5 g2.2⟩
  have hee : e * e = e := by
    obtain ⟨Φ, hΦ⟩ := exists_comp D
    exact delta_idem hΦ (of_isPrimeIdem hΦ hP).1
  have hϖ : (ϖ : D.host.E) ≠ 0 := fun h0 => h3 (by
    rw [show ϖ = 0 from RingOfIntegers.ext h0]; exact Ideal.zero_mem _)
  exact ⟨α, _, h7, h10, ⟨e, f, ϖ, α⁻¹, h0, hP, h2, h3, pairwise_dualLab h4, h5, h6, (suppGroup V f).inv_mem h7,
    (GlobalTheory.DivDual.divAt_inv_and_mul V e ϖ d α hee hϖ h8).1, l4, l6⟩, l6⟩

section Level

variable (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
  (L : LevDat D.host.E ℂ V.rank) (hβ : IsBaseFrame V β Λ 1) (P : Pl D.host.E)
  (hoff : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P)

include hβ hoff

theorem local_level {e f : AE D} (hP : IsPrimeIdem P e f) :
    (∀ k ∈ (levEnv V β L).J, ∃ k₁ ∈ (levEnv V β L).J, ∃ k₂ ∈ (levEnv V β L).J,
        k₁ ∈ (suppGroup V f).map (fin V) ∧ k = k₁ * k₂ ∧ ∀ l ∈ (suppGroup V f).map (fin V), Commute k₂ l) ∧
      (∀ k : (levEnv V β L).J, (k : Bridge.Gf V) ∈ (suppGroup V f).map (fin V) → (levEnv V β L).χ k = 1) ∧
      ∀ g, g ∈ {k | k ∈ KsphC V ∅ ∧ SuppF V f k} ↔ g ∈ suppGroup V f ∧ fin V g ∈ (levEnv V β L).J := by
  have h01 := (supported_group_and_prime_idempotents V).2.2.1 P e f hP
  have hff := h01.1
  have hN := h01.2.2.1
  have h1 : ((1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    rw [Nat.cast_one]; exact (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top
  have h03 := (GlobalTheory.LevSplit.lev_split V β Λ 1 (flag1L L) hβ).2 P e f hP h1 hoff
  have hK := h03.1
  have hχ := h03.2.1
  have hsp := h03.2.2
  refine ⟨fun k hk => ?_, ?_, fun g => ?_⟩
  · obtain ⟨g, hg, rfl⟩ := fin_lift V k
    obtain ⟨k₁, h₁, k₂, h₂, s₁, s₂, rfl⟩ := hsp g ((mem_J V β L hg).1 hk)
    refine ⟨fin V k₁, (mem_J V β L h₁.1).2 h₁, fin V k₂, (mem_J V β L h₂.1).2 h₂, ⟨k₁, s₁, rfl⟩, map_mul _ _ _, ?_⟩
    rintro _ ⟨l, hl, rfl⟩
    exact (commute_of_suppF V (idem_mul_one_sub f hff) hl s₂).symm.map (fin V)
  · rintro ⟨k, hk⟩ ⟨g, hg, hgk⟩
    obtain rfl : fin V g = k := hgk
    exact Units.ext ((chi_eq V β L hk).trans (hχ g ((mem_J V β L (hN g hg)).1 hk) hg))
  · exact ⟨fun h => ⟨h.2, (mem_J V β L (hN g h.2)).2 ((hK g h.2).2 h.1)⟩,
      fun h => ⟨(hK g h.1).1 ((mem_J V β L (hN g h.1)).1 h.2), h.1⟩⟩

variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (ρ : GQ V →* Module.End ℂ W)

theorem fixed_of_mem (F : Bridge.Gf V → W) (hF : F ∈ Bridge.AdForms (Bridge.ratF V) ρ (levEnv V β L).J (levEnv V β L).χ) :
    ∀ k ∈ hyp V P, rtr (fin V) W k F = F := by
  intro k hk
  refine ((supported_group_and_prime_idempotents V).2.1 P).elim fun e he => he.elim fun f hP => ?_
  have h0 := local_level V β Λ L hβ P hoff hP
  have h4 := (h0.2.2 k).1 ((mem_hyp hP k).1 hk)
  exact right_inv (fin V) _ ρ _ _ F hF k h4.2 (h0.2.1 ⟨fin V k, h4.2⟩ (Subgroup.mem_map_of_mem _ h4.1))

theorem single_mem_adj (hρ : ∀ γ u u', inner ℂ (ρ γ u) (ρ γ u') = inner ℂ u u') {I : Type} [Fintype I] (y : I → Bridge.Gf V)
    (hy : Bridge.IsReps (Bridge.ratF V) (levEnv V β L).J y)
    (hfin : ∀ i, Finite (Bridge.stab (Bridge.ratF V) (levEnv V β L).J (y i))) (d : List ℤ)
    (F : Bridge.Gf V → W) (hF : F ∈ Bridge.AdForms (Bridge.ratF V) ρ (levEnv V β L).J (levEnv V β L).χ) :
    opOf (rtr (fin V) W) P (Finsupp.single d 1) F ∈ Bridge.AdForms (Bridge.ratF V) ρ (levEnv V β L).J (levEnv V β L).χ ∧
      ∀ F' ∈ Bridge.AdForms (Bridge.ratF V) ρ (levEnv V β L).J (levEnv V β L).χ,
        Bridge.adInner (Bridge.ratF V) (levEnv V β L).J y (opOf (rtr (fin V) W) P (Finsupp.single d 1) F) F' =
          Bridge.adInner (Bridge.ratF V) (levEnv V β L).J y F (opOf (rtr (fin V) W) P (Finsupp.single (dualLab d) 1) F') := by
  classical
  by_cases hd : IsLab V P d
  swap
  · have hd' : ¬ IsLab V P (dualLab d) := fun h => hd (((GlobalTheory.T.spherical_label_operators_on_hyperspecial_fixed_vectors V P).2.2.2.1 d).1.2 h)
    exact zero_mem_adj _ _ y _ _ _ (opOf_nonlab _ hd) (opOf_nonlab _ hd') F
  refine ((supported_group_and_prime_idempotents V).2.1 P).elim fun e he => he.elim fun f hP => ?_
  have h0 := local_level V β Λ L hβ P hoff hP
  have h1 := h0.1
  have h2 := h0.2.1
  have h3 := h0.2.2
  have hN := ((supported_group_and_prime_idempotents V).2.2.1 P e f hP).2.2.1
  refine (exists_sphOp_pair hP (suppGroup V f ⊓ (levEnv V β L).J.comap (fin V))
    (fun g => (mem_hyp hP g).trans (h3 g)) hd).elim fun α hα => hα.elim fun R' a0 => ?_
  have a1 := a0.1
  have a2 := a0.2.1
  have a3 := a0.2.2.1
  have a4 := a0.2.2.2
  have s1 := supp_rep (V := V) d hP
  have s2 := supp_of_sphOp hP a3
  have d1 := isDC_image (fin V) _ (suppGroup V f) _ h3 h1 α a1 _ s1 (fun γ hγ => (a2.1 γ hγ).2) a2.2
  have d2 := isDC_image (fin V) _ (suppGroup V f) _ h3 h1 α⁻¹ ((suppGroup V f).inv_mem a1) _ s2
    (fun γ hγ => (a4.1 γ hγ).2) a4.2
  rw [MonoidHom.map_inv] at d2
  have m : ∀ R : Finset (GA D V), (∀ γ ∈ R, SuppF V f γ) → ∀ a ∈ R.image (fin V), a ∈ (suppGroup V f).map (fin V) := by
    intro R hR a ha
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.1 ha
    exact ⟨γ, hR γ hγ, rfl⟩
  have i : ∀ R : Finset (GA D V), (∀ γ ∈ R, SuppF V f γ) → ∀ g ∈ R, ∀ g' ∈ R, fin V g = fin V g' → g = g' :=
    fun R hR g hg g' hg' => fin_inj V (hN _ (hR g hg)) (hN _ (hR g' hg'))
  have e1 : opOf (rtr (fin V) W) P (Finsupp.single d 1) F = Bridge.dcOp ((Hk3.rep V P d).image (fin V)) F :=
    (((GlobalTheory.T.spherical_label_operators_on_hyperspecial_fixed_vectors V P).1 _ _ (rep_spec hd)).2 _ _ F (fixed_of_mem V β Λ L hβ P hoff ρ F hF)).symm.trans
      (dcOp_image _ _ (i _ s1) F).symm
  have e2 : ∀ F' ∈ Bridge.AdForms (Bridge.ratF V) ρ (levEnv V β L).J (levEnv V β L).χ,
      opOf (rtr (fin V) W) P (Finsupp.single (dualLab d) 1) F' = Bridge.dcOp (R'.image (fin V)) F' := fun F' hF' =>
    (((GlobalTheory.T.spherical_label_operators_on_hyperspecial_fixed_vectors V P).1 _ R' a3).2 _ _ F' (fixed_of_mem V β Λ L hβ P hoff ρ F' hF')).symm.trans
      (dcOp_image _ _ (i _ s2) F').symm
  exact mem_adj_congr (· ∈ Bridge.AdForms (Bridge.ratF V) ρ (levEnv V β L).J (levEnv V β L).χ)
    (Bridge.adInner (Bridge.ratF V) (levEnv V β L).J y) e1 e2 (dcOp_mem _ ρ _ _ _ _ _ h1 h2 (m _ s1) d1 F hF)
    (GlobalTheory.adInner_dcOp_adjoint (Bridge.ratF V) ρ _ _ _ y _ _ _ hρ (norm_chi V β Λ L hβ) hy hfin h1 h2 (m _ s1) (m _ s2)
      d1 d2 F hF)

end Level

theorem opOf_single_smul {V : HSp D} {M : Type} [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M)
    (P : Pl D.host.E) (d : List ℤ) (z : ℂ) : opOf π P (Finsupp.single d z) = z • opOf π P (Finsupp.single d 1) := by
  rw [opOf_single, opOf_single, one_smul]

theorem side (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (L : LevDat D.host.E ℂ V.rank) (hβ : IsSDFrame V β Λ 1) (ok : Pl D.host.E → Prop)
    (hok : ∀ P, ok P → ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P)
    {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (ρ : GQ V →* Module.End ℂ W)
    (hρ : ∀ γ u u', inner ℂ (ρ γ u) (ρ γ u') = inner ℂ u u') {I : Type} [Fintype I] (y : I → Bridge.Gf V)
    (hy : Bridge.IsReps (Bridge.ratF V) (levEnv V β L).J y)
    (hfin : ∀ i, Finite (Bridge.stab (Bridge.ratF V) (levEnv V β L).J (y i))) (M : HMod (Bridge.Gf V → W))
    (hM : M.Is (Bridge.AdForms (Bridge.ratF V) ρ (levEnv V β L).J (levEnv V β L).χ)
      (Bridge.adInner (Bridge.ratF V) (levEnv V β L).J y)) :
    ∃ h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ M.H,
      (∀ P, ok P → ∀ c x, M.e (h P c x) = hkF V P c (M.e x)) ∧ NormalFam ok h := by
  refine hβ.elim fun n hn => ?_
  have hn' : IsBaseFrame V β Λ 1 := (one_pow n : (1 : ℕ) ^ n = 1) ▸ hn
  refine (exists_normalFam M _ _ hM ok (opOf (rtr (fin V) W)) (opOf_zero _) (opOf_add _) (opOf_single_smul _)
    (fun P P' hP c c' F hF => opOf_comm _ P P' c c' F (fixed_of_mem V β Λ L hn' P (hok P hP) ρ F hF))
    (fun P hP d F hF => single_mem_adj V β Λ L hn' P (hok P hP) ρ hρ y hy hfin d F hF)).imp fun h hh => ?_
  exact ⟨fun P hP c x => (hh.1 P hP c x).trans (hkF_eq V P c _).symm, hh.2⟩

theorem definite_ops : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (_F : Face D A), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → (∀ t, ∃ h, IsOpsX R t h ∧ NormalFam (Good R t) h) ∧ ∀ i t, ∃ h, IsOpsV R i t h ∧ NormalFam (Good R t) h := by
  intro D G _ _ Pl0 T A Ks _ _ _ R _ hL _ hM
  refine ⟨fun t => ?_, fun i t => ?_⟩
  · exact side D.sp.X' R.βX R.ΛX (R.datXt t) hL.βX (Good R t) (fun _ h => h) R.cX.coef.ρ (fun γ => hM.cX.2.1 γ)
      (R.B.R t).pres.y (R.B.R t).pres.reps (fun c => Finite.of_equiv _ ((R.B.R t).pres.stabI c).toEquiv) (R.HX t) (hM.HX t)
  · exact side (Vc D i) (R.βV i) (R.ΛV i) (R.datVt i t) (hL.βV i) (Good R t) (fun _ h => h) (R.cV i).coef.ρ
      (fun γ => (hM.cV i).2.1 γ) (R.B.L i t).pres.y (R.B.L i t).pres.reps
      (fun c => Finite.of_equiv _ ((R.B.L i t).pres.stabI c).toEquiv) (R.HV i t) (hM.HV i t)

end GlobalTheory.DefiniteOps

end
