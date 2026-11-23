import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.Columns.HeckeSp
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsDCOfMemDoubleCoset
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAntiInvolutionOfChars
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegrableOnFundamentalDomainMulRight
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotentsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAntiStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPlaceHeckeDoubleCosetsInverseRepsLabelStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DivisorsAtInvDualLabelAndStabilizerMulStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsHyperspecialDoubleCosetOfElementaryDivisorStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ElementaryDivisorsInvHeckeElementSplitPlaceStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SphericalOps

section Generic

variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H]
  [BorelSpace H] {μ : Measure H} [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
  {Γ : Subgroup H} [Countable Γ] {𝓕 : Set H}

theorem memLp_translate (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) {F : H → ℂ} (hc : Continuous F)
    (hl : ∀ γ ∈ Γ, ∀ h, F (γ * h) = F h) (hi : IntegrableOn (fun h => star (F h) * F h) 𝓕 μ) (y : H) :
    MemLp (fun h => F (h * y)) 2 (μ.restrict 𝓕) := by
  have h1 := GlobalTheory.integrableOn_fundamentalDomain_mul_right h𝓕 y (fun h => star (F h) * F h)
    (fun γ hγ h => by simp only [hl γ hγ]) hi
  have hm : AEStronglyMeasurable (fun h => F (h * y)) (μ.restrict 𝓕) :=
    (hc.comp (continuous_mul_right y)).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hm]
  refine h1.norm.congr (Filter.Eventually.of_forall fun h => ?_)
  simp [sq]

theorem integral_adjoint (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (K : Subgroup H) (x : H) (A A' : Finset H)
    {F F' : H → ℂ} (hc : Continuous F) (hc' : Continuous F')
    (hl : ∀ γ ∈ Γ, ∀ h, F (γ * h) = F h) (hl' : ∀ γ ∈ Γ, ∀ h, F' (γ * h) = F' h)
    (hr : ∀ k ∈ K, ∀ h, F (h * k) = F h) (hr' : ∀ k ∈ K, ∀ h, F' (h * k) = F' h)
    (hi : IntegrableOn (fun h => star (F h) * F h) 𝓕 μ) (hi' : IntegrableOn (fun h => star (F' h) * F' h) 𝓕 μ)
    (hA : ∀ a ∈ A, ∃ k₁ ∈ K, ∃ k₂ ∈ K, a = k₁ * x * k₂) (hA' : ∀ a ∈ A', ∃ k₁ ∈ K, ∃ k₂ ∈ K, a = k₁ * x⁻¹ * k₂)
    (hcard : A.card = A'.card) :
    ∫ h in 𝓕, star (∑ a ∈ A, F (h * a)) * F' h ∂μ = ∫ h in 𝓕, star (F h) * ∑ a ∈ A', F' (h * a) ∂μ := by
  have hint : ∀ y y', IntegrableOn (fun h => star (F (h * y)) * F' (h * y')) 𝓕 μ := fun y y' =>
    ((memLp_translate h𝓕 hc hl hi y).star).integrable_mul (memLp_translate h𝓕 hc' hl' hi' y')
  have hu : ∀ γ ∈ Γ, ∀ h, (fun h => star (F (h * x)) * F' h) (γ * h) = (fun h => star (F (h * x)) * F' h) h := by
    intro γ hγ h
    simp only [hl' γ hγ, mul_assoc, hl γ hγ]
  have h1 : ∀ a ∈ A, ∫ h in 𝓕, star (F (h * a)) * F' h ∂μ = ∫ h in 𝓕, star (F (h * x)) * F' h ∂μ := by
    intro a ha
    obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := hA a ha
    refine Eq.trans ?_ (GlobalTheory.setIntegral_fundamentalDomain_mul_right h𝓕 k₁ (fun h => star (F (h * x)) * F' h) hu)
    congr 1
    funext h
    rw [hr' k₁ hk₁, ← mul_assoc, hr k₂ hk₂, ← mul_assoc]
  have h2 : ∀ a ∈ A', ∫ h in 𝓕, star (F h) * F' (h * a) ∂μ = ∫ h in 𝓕, star (F (h * x)) * F' h ∂μ := by
    intro a ha
    obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := hA' a ha
    refine Eq.trans ?_
      (GlobalTheory.setIntegral_fundamentalDomain_mul_right h𝓕 (k₁ * x⁻¹) (fun h => star (F (h * x)) * F' h) hu)
    congr 1
    funext h
    have : h * (k₁ * x⁻¹) * x = h * k₁ := by group
    simp only [this]
    rw [hr k₁ hk₁, ← mul_assoc, hr' k₂ hk₂]
  simp_rw [star_sum, Finset.sum_mul, Finset.mul_sum]
  rw [integral_finset_sum _ fun a _ => by simpa [IntegrableOn] using hint a 1,
    integral_finset_sum _ fun a _ => by simpa [IntegrableOn] using hint 1 a,
    Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_const, Finset.sum_const, hcard]

end Generic

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}
  {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}

section Translate

open GlobalTheory.PointAtPlaceHom

theorem Rder_rTr {k : GA D V} (hk : k ∈ GfC V) (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (φ : GA D V → ℂ) : Rder θ V τ X (rTr V k φ) = rTr V k (Rder θ V τ X φ) := by
  funext g
  unfold Rder rTr
  congr 1
  funext t
  rw [mul_assoc, mul_assoc, oneP, comm_of_mem V (atTau_mem V τ _) hk]

theorem foldr_rTr {α : Type} (k : GA D V) (F : α → (GA D V → ℂ) → (GA D V → ℂ)) (l : List α)
    (h : ∀ a ∈ l, ∀ φ, F a (rTr V k φ) = rTr V k (F a φ)) (φ : GA D V → ℂ) :
    l.foldr F (rTr V k φ) = rTr V k (l.foldr F φ) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.foldr_cons, List.foldr_cons, ih fun b hb => h b (List.mem_cons_of_mem _ hb), h a List.mem_cons_self]

theorem gelf_rTr {k : GA D V} (hk : k ∈ GfC V) (τ : D.what₂.Tau) (n : ℕ) (φ : GA D V → ℂ) :
    gelf θ V τ n (rTr V k φ) = rTr V k (gelf θ V τ n φ) := by
  unfold gelf
  rw [Finset.sum_congr rfl fun idx _ => foldr_rTr k _ _ (fun a ha ψ => ?_) φ]
  · funext g
    simp only [rTr, Finset.sum_apply]
  · obtain ⟨b, rfl⟩ := List.mem_ofFn.1 ha
    unfold RderC
    rw [Rder_rTr hk, Rder_rTr hk]
    rfl

theorem isAutFunSm_rTr {k : GA D V} (hk : k ∈ GfC V) {φ : GA D V → ℂ} (h : IsAutFunSm θ V φ) :
    IsAutFunSm θ V (rTr V k φ) := by
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  refine { left := fun γ hγ g => ?_, level := ?_, cont := h.cont.comp (continuous_mul_right k),
           smooth := fun n τs Xs hX g => ?_, zfin := ?_, growth := ?_ }
  · unfold rTr
    rw [mul_assoc, h.left γ hγ]
  · obtain ⟨U, hU, e⟩ := h.level
    refine ⟨U.comap (MulAut.conj k⁻¹).toMonoidHom, hU.preimage ?_, fun u hu hf g => ?_⟩
    · show Continuous fun u : GA D V => k⁻¹ * u * k⁻¹⁻¹
      fun_prop
    · have hu' : k⁻¹ * u * k⁻¹⁻¹ ∈ U := hu
      have := e _ hu' (mul_mem (mul_mem (inv_mem hk) hf) (inv_mem (inv_mem hk))) (g * k)
      unfold rTr
      rw [← this]
      congr 1
      group
  · have := h.smooth n τs Xs hX (g * k)
    convert this using 2 with t
    unfold rTr
    rw [mul_assoc, mul_assoc, comm_of_mem V (list_prod_mem fun a ha => ?_) hk]
    obtain ⟨b, rfl⟩ := List.mem_ofFn.1 ha
    exact atTau_mem V _ _
  · obtain ⟨W, hW, m, s⟩ := h.zfin
    refine ⟨W.map (heckeLin V {k}), inferInstance, ⟨φ, m, ?_⟩, ?_⟩
    · funext g
      simp [heckeLin_apply, rTr]
    · rintro τ n _ ⟨f, hf, rfl⟩
      have e : ∀ f, heckeLin V {k} f = rTr V k f := fun f => by
        funext g
        simp [heckeLin_apply, rTr]
      exact ⟨_, s τ n f hf, by rw [e, e, gelf_rTr hk]⟩
  · obtain ⟨N, hN⟩ := h.growth
    refine ⟨N, fun l hl x => ?_⟩
    obtain ⟨C, hC⟩ := hN l hl (x * k)
    refine ⟨C, fun g hg => ?_⟩
    rw [foldr_rTr k _ l (fun a _ ψ => Rder_rTr hk _ _ ψ) φ]
    unfold rTr
    rw [mul_assoc, comm_of_mem V hg hk, ← mul_assoc]
    exact hC g hg

variable {M : DSModel V S} {J : Set (GA D V)} {χ : GA D V → ℂ}

theorem isMultMap_single {T : MMap M} (h : IsMultMap θ M J χ T) {k : GA D V} (hk : k ∈ GfC V) :
    IsMultMap θ M ∅ χ (heckeOn M {k} T) := by
  have e : ∀ v, heckeOn M {k} T v = rTr V k (T v) := fun v => by
    funext g
    simp [heckeOn, postOn_apply, heckeLin_apply, rTr]
  refine ⟨fun v => ?_, fun v => ?_, fun v k hk => hk.elim, fun τ g hg v w hw => ?_, fun τ v x => ?_⟩
  · rw [e]
    exact isAutFunSm_rTr hk (h.aut v)
  · rw [e]
    intro r C hC μ 𝓕 hμ h𝓕 g
    simp only [rTr, mul_assoc]
    exact h.cusp v r C hC μ 𝓕 hμ h𝓕 (g * k)
  · rw [e, e, h.equiv τ g hg v w hw]
    funext x
    unfold rTr
    rw [mul_assoc, mul_assoc, comm_of_mem V (atTau_mem V τ g) hk]
  · obtain ⟨ℓ, s, e'⟩ := h.cont τ v (x * k)
    exact ⟨ℓ, s, fun w => by rw [e, e']; rfl⟩

theorem isMultMap_heckeOn {T : MMap M} (h : IsMultMap θ M J χ T) {R : Finset (GA D V)} (hR : ∀ k ∈ R, k ∈ GfC V)
    (hl : ∀ v, ∀ k ∈ J, ∀ g, heckeLin V R (T v) (g * k) = χ k * heckeLin V R (T v) g) :
    IsMultMap θ M J χ (heckeOn M R T) := by
  have e : heckeOn M R T = ∑ k ∈ R, heckeOn M {k} T := by
    ext v g
    simp [heckeOn, postOn_apply, heckeLin_apply, MultilinearMap.sum_apply]
  have h0 : IsMultMap θ M ∅ χ (heckeOn M R T) := by
    rw [← GlobalTheory.MultMem.mem_mult_iff, e]
    exact sum_mem fun k hk => (GlobalTheory.MultMem.mem_mult_iff ..).2 (isMultMap_single h (hR k hk))
  exact ⟨h0.aut, h0.cusp, hl, h0.equiv, h0.cont⟩

end Translate

section Local

open Formalism.IndefR.Bridge

variable {J L : Subgroup (GA D V)} {P : HeightOneSpectrum (𝓞 D.host.E)} {e f : Formalism.L2.Theta.AE D}

def RealUnif (P : HeightOneSpectrum (𝓞 D.host.E)) : Prop :=
  ∃ x : 𝓞 D.host.F, ∃ y : 𝓞 D.host.E, (y : D.host.E) = algebraMap D.host.F D.host.E (x : D.host.F) ∧
    y ∈ P.asIdeal ∧ y ∉ P.asIdeal ^ 2

theorem exists_loc (h : IsPrimeIdem P e f) : ∃ L : Subgroup (GA D V), ∀ g, g ∈ L ↔ SuppF V f g :=
  have h1 := (GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 P e f h
  ((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).1 f h1.1 h1.2.1).1

theorem isDC_of_rep (hL : ∀ g, g ∈ L ↔ SuppF V f g) {α : GA D V} {R : Finset (GA D V)}
    (h : IsCosetRep V {k | k ∈ (J : Set (GA D V)) ∧ SuppF V f k} α R) : IsDC (J ⊓ L) α R := by
  refine ⟨fun a ha => ?_, fun g ⟨k₁, k₂, e⟩ => ?_⟩
  · obtain ⟨-, k₁, h₁, k₂, h₂, e⟩ := h.1 a ha
    exact ⟨⟨k₁, h₁.1, (hL _).2 h₁.2⟩, ⟨k₂, h₂.1, (hL _).2 h₂.2⟩, e⟩
  · obtain ⟨a, ha, hu⟩ := h.2 g ⟨k₁, ⟨k₁.2.1, (hL _).1 k₁.2.2⟩, k₂, ⟨k₂.2.1, (hL _).1 k₂.2.2⟩, e⟩
    exact ⟨a, ⟨ha.1, ha.2.1, (hL _).2 ha.2.2⟩, fun b hb => hu b ⟨hb.1, hb.2.1, (hL _).1 hb.2.2⟩⟩

theorem split_triv : ∀ k ∈ J ⊓ L, ∃ k₁ ∈ J ⊓ L, ∃ k₂ ∈ J ⊓ L, k₁ ∈ L ∧ k = k₁ * k₂ ∧ ∀ l ∈ L, Commute k₂ l :=
  fun k hk => ⟨k, hk, 1, one_mem _, hk.2, (mul_one k).symm, fun l _ => Commute.one_left l⟩

theorem local_data (hu : RealUnif P) (h : IsPrimeIdem P e f) (hL : ∀ g, g ∈ L ↔ SuppF V f g)
    (hJ : ∀ g, SuppF V f g → (g ∈ (J : Set (GA D V)) ↔ g ∈ KsphC V ∅)) :
    (∃ ι : GA D V → GA D V, (∀ g ∈ L, ι g ∈ L) ∧ (∀ x ∈ L, ∀ y ∈ L, ι (x * y) = ι y * ι x) ∧
      (∀ x ∈ L, ι (ι x) = x) ∧ (∀ k ∈ (J ⊓ L) ⊓ L, ι k ∈ J ⊓ L) ∧
      ∀ g ∈ L, ∃ a ∈ (J ⊓ L) ⊓ L, ∃ b ∈ (J ⊓ L) ⊓ L, ι g = a * g * b) ∧
    (∀ g, SuppF V f g → ∃ R : Finset (GA D V), (∀ γ ∈ R, SuppF V f γ) ∧
      IsCosetRep V {k | k ∈ (J : Set (GA D V)) ∧ SuppF V f k} g R) ∧
    ∀ (ϖ ϖ' : 𝓞 D.host.E) (d : List ℤ) (g g' : GA D V), ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → ϖ' ∈ P.asIdeal →
      ϖ' ∉ P.asIdeal ^ 2 → d.Pairwise (fun a b => b ≤ a) → SuppF V f g → SuppF V f g' →
      DivAt V e (ϖ : D.host.E) d g → DivAt V e (ϖ' : D.host.E) d g' →
      ∃ k₁ k₂ : (J ⊓ L : Subgroup (GA D V)), g' = (k₁ : GA D V) * g * k₂ := by
  have hK : {k | k ∈ (J : Set (GA D V)) ∧ SuppF V f k} = {k | k ∈ KsphC V ∅ ∧ SuppF V f k} :=
    Set.ext fun k => and_congr_left fun hk => hJ k hk
  have m1 : ∀ {a}, a ∈ KsphC V ∅ → SuppF V f a → a ∈ J ⊓ L := fun h1 h2 => ⟨(hJ _ h2).2 h1, (hL _).2 h2⟩
  have m2 : ∀ {a}, a ∈ KsphC V ∅ → SuppF V f a → a ∈ (J ⊓ L) ⊓ L := fun h1 h2 => ⟨m1 h1 h2, (hL _).2 h2⟩
  rw [hK]
  rcases id h with ⟨hs, rfl⟩ | ⟨rfl, -⟩
  · obtain ⟨⟨ι, i1, i2, i3, i4, i5⟩, hR, -⟩ := GlobalTheory.T.involution_spherical_hecke_anti V P e hs
    refine ⟨⟨ι, fun g hg => (hL _).2 (i1 g ((hL _).1 hg)), fun x hx y hy => i2 x y ((hL _).1 hx) ((hL _).1 hy),
      fun x hx => i3 x ((hL _).1 hx), fun k hk => ?_, fun g hg => ?_⟩, hR, ?_⟩
    · have := (hL _).1 hk.2
      exact m1 (i4 k ⟨(hJ k this).1 hk.1.1, this⟩) (i1 k this)
    · obtain ⟨a, ha, b, hb, e⟩ := i5 g ((hL _).1 hg)
      exact ⟨a, m2 ha.1 ha.2, b, m2 hb.1 hb.2, e⟩
    · intro ϖ ϖ' d g g' h1 h2 h3 h4 _ h5 h6 h7 h8
      obtain ⟨a, ha, b, hb, e⟩ := GlobalTheory.T.exists_hyperspecial_doubleCoset_of_elementaryDivisors V P e ϖ ϖ' d g g' hs h1 h2 h3 h4 h5 h6 h7 h8
      exact ⟨⟨a, m1 ha.1 ha.2⟩, ⟨b, m1 hb.1 hb.2⟩, e⟩
  · have key := GlobalTheory.T.inert_place_hecke_double_cosets_inverse_reps_label V P f h hu
    refine ⟨⟨fun g => g⁻¹, fun g hg => inv_mem hg, fun x _ y _ => mul_inv_rev x y, fun x _ => inv_inv x,
      fun k hk => inv_mem hk.1, fun g hg => ?_⟩, fun g hg => (key g hg).2.1, ?_⟩
    · obtain ⟨a, b, ha, ha', hb, hb', e⟩ := (key g ((hL _).1 hg)).1
      exact ⟨a, m2 ha ha', b, m2 hb hb', e⟩
    · intro ϖ ϖ' d g g' h1 h2 h3 h4 h5 h6 h7 h8 h9
      obtain ⟨a, b, ha, ha', hb, hb', e⟩ := (key g h6).2.2 ϖ ϖ' d g' h1 h2 h3 h4 h5 h7 h8 h9
      exact ⟨⟨a, m1 ha ha'⟩, ⟨b, m1 hb hb'⟩, e⟩

variable {χ : GA D V → ℂ}

theorem inv_loc (hL : ∀ g, g ∈ L ↔ SuppF V f g) (hχ : ∀ g ∈ (J : Set (GA D V)), SuppF V f g → χ g = 1)
    {F : GA D V → ℂ} (hF : ∀ k ∈ (J : Set (GA D V)), ∀ g, F (g * k) = χ k * F g) :
    ∀ (k : (J ⊓ L : Subgroup (GA D V))) (h : GA D V),
      F (h * k) = (((1 : (J ⊓ L : Subgroup (GA D V)) →* ℂˣ) k : ℂˣ) : ℂ) • F h := fun k h => by
  rw [hF k k.2.1, hχ k k.2.1 ((hL _).1 k.2.2)]
  simp

variable {Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))}

theorem labelUnique (hu : ∀ P : HeightOneSpectrum (𝓞 D.host.E), RealUnif P) :
    LabelUnique (J : Set (GA D V)) χ Sb := by
  rintro P d R R' ⟨e, f, ϖ, α, -, hP, h1, h2, hd, hJ, hχ, hα, hD, hR, hc⟩
    ⟨e', f', ϖ', α', -, hP', h1', h2', -, -, -, hα', hD', hR', hc'⟩ F hF
  obtain ⟨rfl, rfl⟩ := ((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 P e f hP).2.2.2.1 e' f' hP'
  obtain ⟨L, hL⟩ := exists_loc (V := V) hP
  exact (GlobalTheory.HkB.dcOp_eq_and_level (J ⊓ L) L 1 α α' R R' F split_triv (fun _ _ => rfl)
    (fun a ha => (hL _).2 (hR a ha)) (fun a ha => (hL _).2 (hR' a ha)) (isDC_of_rep hL hc) (isDC_of_rep hL hc')
    ((local_data (hu P) hP hL hJ).2.2 ϖ ϖ' d α α' h1 h2 h1' h2' hd hα hα' hD hD') (inv_loc hL hχ hF)).1

theorem splitLab_pairwise (n k : ℕ) : (splitLab n k).Pairwise fun a b => b ≤ a := by
  unfold splitLab
  rw [List.pairwise_append]
  refine ⟨by simp, by simp, fun a ha b hb => ?_⟩
  rw [List.eq_of_mem_replicate ha, List.eq_of_mem_replicate hb]
  norm_num

theorem splitDict : SplitDict (J : Set (GA D V)) χ Sb := by
  rintro P k R ⟨e, ϖ, α, hS, he, h1, h2, hk, hJ, hχ, hα, hR, hc⟩
  have hP : IsPrimeIdem P e (e + cA D e) := Or.inl ⟨he, rfl⟩
  obtain ⟨L, hL⟩ := exists_loc (V := V) hP
  exact ⟨e, e + cA D e, ϖ, α⁻¹, hS, hP, h1, h2, splitLab_pairwise _ _, hJ, hχ,
    (hL _).1 (inv_mem ((hL _).2 hα.2.1)), GlobalTheory.T.elementary_divisors_inv_hecke_element_split_place V P e ϖ k α he h1 h2 hk hα, hR, hc⟩

theorem level_heckeLin {d : List ℤ} {R : Finset (GA D V)}
    (hm : ∀ k ∈ J, ∀ k' ∈ J, χ (k * k') = χ k * χ k')
    (hs : ∀ e f, OffS D Sb P → IsPrimeIdem P e f → ∀ k ∈ J, ∃ k₁ ∈ J, ∃ k₂ ∈ J,
      SuppF V f k₁ ∧ SuppF V (1 - f) k₂ ∧ k = k₁ * k₂)
    (h : Hecke₂ V (J : Set (GA D V)) χ Sb P d R) {F : GA D V → ℂ}
    (hF : ∀ k ∈ (J : Set (GA D V)), ∀ g, F (g * k) = χ k * F g) :
    ∀ k ∈ (J : Set (GA D V)), ∀ g, heckeLin V R F (g * k) = χ k * heckeLin V R F g := by
  obtain ⟨e, f, ϖ, α, hS, hP, -, -, -, -, hχ, -, -, hR, hc⟩ := h
  obtain ⟨L, hL⟩ := exists_loc (V := V) hP
  have h0 := (GlobalTheory.HkB.dcOp_eq_and_level (J ⊓ L) L 1 α α R R F split_triv (fun _ _ => rfl)
    (fun a ha => (hL _).2 (hR a ha)) (fun a ha => (hL _).2 (hR a ha)) (isDC_of_rep hL hc) (isDC_of_rep hL hc)
    ⟨1, 1, by simp⟩ (inv_loc hL hχ hF)).2
  intro k hk g
  obtain ⟨k₁, hk₁, k₂, hk₂, s₁, s₂, rfl⟩ := hs e f hS hP k hk
  have h1 := (GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 P e f hP
  have hc : ∀ a ∈ R, Commute a k₂ := fun a ha =>
    ((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).1 f h1.1 h1.2.1).2.2 (1 - f) a k₂ (by rw [mul_sub, mul_one, h1.1, sub_self]) (hR a ha) s₂
  have h2 : heckeLin V R F (g * k₁) = heckeLin V R F g := by
    show dcOp R F (g * k₁) = dcOp R F g
    simpa using h0 ⟨k₁, hk₁, (hL _).2 s₁⟩ g
  rw [hm k₁ hk₁ k₂ hk₂, hχ k₁ hk₁ s₁, one_mul, ← h2, heckeLin_apply, heckeLin_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [← hF k₂ hk₂, ← mul_assoc, mul_assoc _ k₂, ← (hc a ha).eq, mul_assoc _ a]

theorem comm_heckeLin (hu : RealUnif P) {P' : HeightOneSpectrum (𝓞 D.host.E)} {d d' : List ℤ}
    {R R' : Finset (GA D V)} (h : Hecke₂ V (J : Set (GA D V)) χ Sb P d R)
    (h' : Hecke₂ V (J : Set (GA D V)) χ Sb P' d' R') {F : GA D V → ℂ}
    (hF : ∀ k ∈ (J : Set (GA D V)), ∀ g, F (g * k) = χ k * F g) :
    heckeLin V R (heckeLin V R' F) = heckeLin V R' (heckeLin V R F) := by
  obtain ⟨e, f, ϖ, α, hS, hP, -, -, -, hJ, hχ, hα, -, hR, hc⟩ := h
  obtain ⟨e', f', ϖ', α', -, hP', -, -, -, -, -, hα', -, hR', hc'⟩ := h'
  have h1 := (GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 P e f hP
  rcases h1.2.2.2.2 P' e' f' hP' with h0 | ⟨rfl, -⟩
  · funext g
    simp only [heckeLin_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b hb => Finset.sum_congr rfl fun a ha => ?_
    rw [mul_assoc, mul_assoc, (((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).1 f h1.1 h1.2.1).2.2 f' a b h0 (hR a ha) (hR' b hb)).eq]
  · obtain ⟨L, hL⟩ := exists_loc (V := V) hP
    obtain ⟨hι, hrep, -⟩ := local_data hu hP hL hJ
    obtain ⟨A', hA', hc''⟩ := hrep α⁻¹ ((hL _).1 (inv_mem ((hL _).2 hα)))
    exact (GlobalTheory.DoubleCosetComm.dcOp_comm_and_card (J ⊓ L) L 1 α α' R R' A' F split_triv (fun _ _ => rfl) hι
      (fun a ha => (hL _).2 (hR a ha)) (fun a ha => (hL _).2 (hR' a ha)) (fun a ha => (hL _).2 (hA' a ha))
      (isDC_of_rep hL hc) (isDC_of_rep hL hc') (isDC_of_rep hL hc'') (inv_loc hL hχ hF)).1

theorem dualLab_pairwise {d : List ℤ} (h : d.Pairwise fun a b => b ≤ a) :
    (dualLab d).Pairwise fun a b => b ≤ a := by
  unfold dualLab
  rw [List.pairwise_reverse, List.pairwise_map]
  exact h.imp fun h => neg_le_neg h

theorem idem_of_isPrimeIdem (h : IsPrimeIdem P e f) (V : HSp D) : e * e = e := by
  rcases id h with ⟨hs, -⟩ | ⟨rfl, -⟩
  · exact hs.1.1
  · exact ((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 P f f h).1

theorem exists_dual (hu : RealUnif P) {d : List ℤ} {R : Finset (GA D V)}
    (h : Hecke₂ V (J : Set (GA D V)) χ Sb P d R) :
    ∃ R', Hecke₂ V (J : Set (GA D V)) χ Sb P (dualLab d) R' ∧ R.card = R'.card ∧
      ∃ (K : Subgroup (GA D V)) (x : GA D V), (∀ k ∈ K, k ∈ J ∧ χ k = 1) ∧
        (∀ a ∈ R, ∃ k₁ ∈ K, ∃ k₂ ∈ K, a = k₁ * x * k₂) ∧ ∀ a ∈ R', ∃ k₁ ∈ K, ∃ k₂ ∈ K, a = k₁ * x⁻¹ * k₂ := by
  obtain ⟨e, f, ϖ, α, hS, hP, h1, h2, hd, hJ, hχ, hα, hD, hR, hc⟩ := h
  obtain ⟨L, hL⟩ := exists_loc (V := V) hP
  obtain ⟨hι, hrep, -⟩ := local_data hu hP hL hJ
  have hα' := (hL _).1 (inv_mem ((hL _).2 hα))
  obtain ⟨R', hR', hc'⟩ := hrep α⁻¹ hα'
  have h0 : (ϖ : D.host.E) ≠ 0 := fun h0 => h2 (by
    rw [show ϖ = 0 from RingOfIntegers.coe_eq_zero_iff.1 h0]
    exact zero_mem _)
  refine ⟨R', ⟨e, f, ϖ, α⁻¹, hS, hP, h1, h2, dualLab_pairwise hd, hJ, hχ, hα',
    (GlobalTheory.T.divisorsAt_inv_dualLabel_and_stabilizer_mul V e ϖ d α (idem_of_isPrimeIdem hP V) h0 hD).1, hR', hc'⟩, ?_, J ⊓ L, α,
    fun k hk => ⟨hk.1, hχ k hk.1 ((hL _).1 hk.2)⟩, fun a ha => ?_, fun a ha => ?_⟩
  · exact (GlobalTheory.DoubleCosetComm.dcOp_comm_and_card (W := ℂ) (J ⊓ L) L 1 α α R R R' 0 split_triv (fun _ _ => rfl) hι
      (fun a ha => (hL _).2 (hR a ha)) (fun a ha => (hL _).2 (hR a ha)) (fun a ha => (hL _).2 (hR' a ha))
      (isDC_of_rep hL hc) (isDC_of_rep hL hc) (isDC_of_rep hL hc') (fun _ _ => by simp)).2
  · obtain ⟨k₁, k₂, e⟩ := (isDC_of_rep hL hc).1 a ha
    exact ⟨k₁, k₁.2, k₂, k₂.2, e⟩
  · obtain ⟨k₁, k₂, e⟩ := (isDC_of_rep hL hc').1 a ha
    exact ⟨k₁, k₁.2, k₂, k₂.2, e⟩

end Local

theorem spherical_ops : ∀ {D : D7} (V : HSp D) {S : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) (J : Subgroup (GA D V)) (χ : GA D V → ℂ) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))), (∀ (P : HeightOneSpectrum (𝓞 D.host.E)), ∃ x : 𝓞 D.host.F, ∃ y : 𝓞 D.host.E, (y : D.host.E) = algebraMap D.host.F D.host.E (x : D.host.F) ∧ y ∈ P.asIdeal ∧ y ∉ P.asIdeal ^ 2) → IsInfFam θ → (∀ k ∈ J, ∀ k' ∈ J, χ (k * k') = χ k * χ k') → (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) e f, OffS D Sb P → IsPrimeIdem P e f → ∀ k ∈ J, ∃ k₁ ∈ J, ∃ k₂ ∈ J, SuppF V f k₁ ∧ SuppF V (1 - f) k₂ ∧ k = k₁ * k₂) → LabelUnique (J : Set (GA D V)) χ Sb ∧ SplitDict (J : Set (GA D V)) χ Sb ∧ ∀ P d R, Hecke₂ V (J : Set (GA D V)) χ Sb P d R → (∀ T ∈ Mult θ M (J : Set (GA D V)) χ, heckeOn M R T ∈ Mult θ M (J : Set (GA D V)) χ) ∧ (∀ P' d' R', Hecke₂ V (J : Set (GA D V)) χ Sb P' d' R' → ∀ T ∈ Mult θ M (J : Set (GA D V)) χ, heckeOn M R (heckeOn M R' T) = heckeOn M R' (heckeOn M R T)) ∧ ∃ R', Hecke₂ V (J : Set (GA D V)) χ Sb P (dualLab d) R' ∧ ∀ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), μ.IsHaarMeasure → μ.IsMulRightInvariant → IsFundamentalDomain (GQ V) 𝓕 μ → SchurMult θ M (J : Set (GA D V)) χ μ 𝓕 → ∀ T ∈ Mult θ M (J : Set (GA D V)) χ, ∀ T' ∈ Mult θ M (J : Set (GA D V)) χ, ∀ c, IsMultIP M μ 𝓕 (heckeOn M R T) T' c ↔ IsMultIP M μ 𝓕 T (heckeOn M R' T') c := by
  intro D V S θ M J χ Sb hu hθ hm hs
  have keep : ∀ P d R, Hecke₂ V (J : Set (GA D V)) χ Sb P d R →
      ∀ T ∈ Mult θ M (J : Set (GA D V)) χ, heckeOn M R T ∈ Mult θ M (J : Set (GA D V)) χ := by
    intro P d R h T hT
    rw [GlobalTheory.MultMem.mem_mult_iff] at hT ⊢
    refine isMultMap_heckeOn hT (fun k hk => ?_) fun v => level_heckeLin hm (hs P) h (hT.lev v)
    obtain ⟨_, _, _, _, -, -, -, -, -, -, -, -, -, -, hc⟩ := h
    exact (hc.1 k hk).1
  refine ⟨labelUnique hu, splitDict, fun P d R h => ⟨keep P d R h, fun P' d' R' h' T hT => ?_, ?_⟩⟩
  · rw [GlobalTheory.MultMem.mem_mult_iff] at hT
    ext1 v
    exact comm_heckeLin (hu P) h h' (hT.lev v)
  · obtain ⟨R', h', hcard, K, x, hK, hR, hR'⟩ := exists_dual (hu P) h
    refine ⟨R', h', fun μ 𝓕 hμ hr h𝓕 hS T hT T' hT' c => ?_⟩
    haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
    haveI : BorelSpace (GA D V) := ⟨rfl⟩
    haveI : Countable (GQ V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig V.gram
    have hS' := hS hθ hμ h𝓕
    obtain ⟨c₁, h₁⟩ := hS' _ (keep P d R h T hT) _ hT'
    obtain ⟨c₂, h₂⟩ := hS' _ hT _ (keep P _ R' h' T' hT')
    obtain ⟨c₃, h₃⟩ := hS' _ hT _ hT
    obtain ⟨c₄, h₄⟩ := hS' _ hT' _ hT'
    rw [GlobalTheory.MultMem.mem_mult_iff] at hT hT'
    have key : ∀ v v' : M.Vec, ∫ g in 𝓕, star (heckeOn M R T v g) * T' v' g ∂μ =
        ∫ g in 𝓕, star (T v g) * heckeOn M R' T' v' g ∂μ := fun v v' =>
      integral_adjoint h𝓕 K x R R' (hT.aut v).cont (hT'.aut v').cont (hT.aut v).left (hT'.aut v').left
        (fun k hk g => by rw [hT.lev v k (hK k hk).1, (hK k hk).2, one_mul])
        (fun k hk g => by rw [hT'.lev v' k (hK k hk).1, (hK k hk).2, one_mul])
        (h₃ v v).1 (h₄ v' v').1 hR hR' hcard
    exact ⟨fun H v v' => ⟨(h₂ v v').1, (key v v').symm.trans (H v v').2⟩,
      fun H v v' => ⟨(h₁ v v').1, (key v v').trans (H v v').2⟩⟩

end GlobalTheory.SphericalOps
