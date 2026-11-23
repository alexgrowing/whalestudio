import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToQMemMaximalIdealIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinOrdLeOrdAdd
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.EqZeroOfForallLTensorEqZero
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GraphLocal.MaxGen

theorem ringHom_eq_of_trBasis {F κ D ι : Type} [Field F] [Field κ] [CharZero κ] [Algebra F κ]
    [CommRing D] [IsLocalRing D] {z : ι → κ} (hz : IsTranscendenceBasis F z) (α β : κ →+* D)
    (hc : ∀ a, α (algebraMap F κ a) = β (algebraMap F κ a)) (hzz : ∀ i, α (z i) = β (z i))
    (hm : ∀ x, ¬ IsUnit (α x - β x)) : α = β := by
  let F₀ := IntermediateField.adjoin F (Set.range z)
  haveI : Algebra.IsAlgebraic F₀ κ := hz.isAlgebraic_field
  have hle : F₀ ≤ (RingHom.eqLocusField α β).toIntermediateField hc := by
    refine IntermediateField.adjoin_le_iff.2 ?_
    rintro _ ⟨i, rfl⟩
    exact hzz i
  have hcomp : α.comp (algebraMap F₀ κ) = β.comp (algebraMap F₀ κ) :=
    RingHom.ext fun a => hle a.2
  ext x
  have hsep : (minpoly F₀ x).Separable := Algebra.IsSeparable.isSeparable F₀ x
  have ev : ∀ (γ : κ →+* D) (f : Polynomial F₀),
      (f.map (γ.comp (algebraMap F₀ κ))).eval (γ x) = γ (Polynomial.aeval x f) := by
    intro γ f
    rw [Polynomial.eval_map, Polynomial.aeval_def, Polynomial.hom_eval₂]
  refine IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub
    (f := (minpoly F₀ x).map (α.comp (algebraMap F₀ κ))) ?_ ?_ (hm x) ?_
  · rw [ev, minpoly.aeval, map_zero]
  · rw [hcomp, ev, minpoly.aeval, map_zero]
  · rw [Polynomial.derivative_map, ev]
    exact (IsUnit.mk0 _ (hsep.aeval_derivative_ne_zero (minpoly.aeval F₀ x))).map α

theorem exists_extension {R κ k' : Type} [CommRing R] [Field κ] [Field k'] (π : R →+* κ)
    (r : R →+* k') (hker : ∀ a, π a = 0 ↔ r a = 0)
    (hfr : ∀ f : κ, ∃ a b : R, π b ≠ 0 ∧ f * π b = π a) :
    ∃ ι : κ →+* k', ∀ a, ι (π a) = r a := by
  letI : Algebra (R ⧸ RingHom.ker π) κ := (RingHom.kerLift π).toAlgebra
  haveI : FaithfulSMul (R ⧸ RingHom.ker π) κ :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.kerLift_injective π)
  haveI : IsFractionRing (R ⧸ RingHom.ker π) κ := by
    refine IsFractionRing.of_field _ _ fun f => ?_
    obtain ⟨a, b, hb, e⟩ := hfr f
    exact ⟨Ideal.Quotient.mk _ a, Ideal.Quotient.mk _ b, (eq_div_iff hb).2 e⟩
  let g : R ⧸ RingHom.ker π →+* k' := Ideal.Quotient.lift _ r fun a ha => (hker a).1 ha
  have hg : Function.Injective g := by
    refine (injective_iff_map_eq_zero g).2 fun a ha => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact Ideal.Quotient.eq_zero_iff_mem.2 ((hker a).2 ha)
  exact ⟨IsFractionRing.lift hg, fun a => IsFractionRing.lift_algebraMap hg (Ideal.Quotient.mk _ a)⟩

theorem exists_mul_mem_radical {R : Type} [CommRing R] {I p : Ideal R} (hp : p ∈ I.minimalPrimes)
    {x : R} (hx : x ∈ p) : ∃ s, s ∉ p ∧ x * s ∈ I.radical := by
  haveI := hp.isPrime
  have h := IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes
    (A := Localization.AtPrime p) p I hp
  obtain ⟨n, hn⟩ : algebraMap R (Localization.AtPrime p) x ∈
      (I.map (algebraMap R (Localization.AtPrime p))).radical :=
    h ▸ Ideal.mem_map_of_mem _ hx
  rw [IsLocalization.mem_map_algebraMap_iff (M := p.primeCompl)] at hn
  obtain ⟨⟨a, b⟩, hn⟩ := hn
  rw [← map_pow, ← map_mul, IsLocalization.eq_iff_exists p.primeCompl] at hn
  obtain ⟨t, ht⟩ := hn
  refine ⟨t * b, (t * b).2, n + 1, ?_⟩
  simp only at ht
  have : (x * (t.1 * b.1)) ^ (n + 1) = (t.1 ^ n * b.1 ^ n * x * t.1) * a := by
    rw [mul_assoc, ← ht]; ring
  rw [this]
  exact I.mul_mem_left _ a.2

variable {K κ' : Type} [Field K] [Field κ'] [Algebra ℂ K] [Algebra ℂ κ']

variable (κ') in

def inl (E : Place (algebraMap ℂ K)) : E.ring →+* tens (κ' := κ') (placeAlg E) where
  toFun e := ⟨(e : K) ⊗ₜ 1, tmul_mem e.2 1⟩
  map_one' := rfl
  map_mul' _ _ := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' _ _ := Subtype.ext (by simp [TensorProduct.add_tmul])

def inr (E : Place (algebraMap ℂ K)) : κ' →+* tens (κ' := κ') (placeAlg E) where
  toFun b := ⟨(1 : K) ⊗ₜ b, tmul_mem (one_mem (placeAlg E)) b⟩
  map_one' := rfl
  map_mul' _ _ := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' _ _ := Subtype.ext (by simp [TensorProduct.tmul_add])

theorem inl_const (E : Place (algebraMap ℂ K)) (a : ℂ) :
    inl κ' E (E.const a) = inr E (algebraMap ℂ κ' a) := by
  refine Subtype.ext ?_
  change algebraMap ℂ K a ⊗ₜ[ℂ] (1 : κ') = (1 : K) ⊗ₜ[ℂ] algebraMap ℂ κ' a
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

theorem tensEquiv_tmul (E : Place (algebraMap ℂ K)) (e : placeAlg E) (b : κ') :
    tensEquiv (placeAlg E) (e ⊗ₜ b) = inl κ' E ⟨e.1, e.2⟩ * inr E b := by
  refine Subtype.ext ?_
  change (e : K) ⊗ₜ[ℂ] b = ((e : K) ⊗ₜ[ℂ] (1 : κ')) * ((1 : K) ⊗ₜ[ℂ] b)
  simp

theorem tens_ringHom_ext (E : Place (algebraMap ℂ K)) {T : Type} [CommRing T]
    {f g : tens (κ' := κ') (placeAlg E) →+* T} (h₁ : ∀ e, f (inl κ' E e) = g (inl κ' E e))
    (h₂ : ∀ b, f (inr E b) = g (inr E b)) : f = g := by
  refine RingHom.ext fun w => ?_
  obtain ⟨w, rfl⟩ := (tensEquiv (placeAlg E)).surjective w
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul e b => rw [tensEquiv_tmul, map_mul, map_mul, h₁, h₂]
  | add u v hu hv => simp only [map_add, hu, hv]

theorem exists_tens_lift (E : Place (algebraMap ℂ K)) {T : Type} [CommRing T] (u : E.ring →+* T)
    (v : κ' →+* T) (h : ∀ a, u (E.const a) = v (algebraMap ℂ κ' a)) :
    ∃ θ : tens (κ' := κ') (placeAlg E) →+* T,
      (∀ e, θ (inl κ' E e) = u e) ∧ ∀ b, θ (inr E b) = v b := by
  letI : Algebra ℂ T := (v.comp (algebraMap ℂ κ')).toAlgebra
  let u' : placeAlg E →ₐ[ℂ] T :=
    { toFun := fun e => u ⟨e.1, e.2⟩
      map_one' := map_one u
      map_mul' := fun a b => map_mul u ⟨a.1, a.2⟩ ⟨b.1, b.2⟩
      map_zero' := map_zero u
      map_add' := fun a b => map_add u ⟨a.1, a.2⟩ ⟨b.1, b.2⟩
      commutes' := h }
  let v' : κ' →ₐ[ℂ] T := { v with commutes' := fun _ => rfl }
  let θ := (Algebra.TensorProduct.productMap u' v').comp
    (tensEquiv (κ' := κ') (placeAlg E)).symm.toAlgHom
  have hθ : ∀ (e : E.ring) (b : κ'), θ (inl κ' E e * inr E b) = u e * v b := fun e b => by
    have := tensEquiv_tmul E ⟨e.1, e.2⟩ b
    change Algebra.TensorProduct.productMap u' v' ((tensEquiv (placeAlg E)).symm _) = _
    erw [← this]
    rw [AlgEquiv.symm_apply_apply, Algebra.TensorProduct.productMap_apply_tmul]
    rfl
  refine ⟨θ.toRingHom, fun e => ?_, fun b => ?_⟩
  · simpa using hθ e 1
  · simpa using hθ 1 b

theorem ord_pos_iff (E : Place (algebraMap ℂ K)) (e : E.ring) (he : (e : K) ≠ 0) :
    0 < E.ord e ↔ e ∈ IsLocalRing.maximalIdeal E.ring := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  refine ⟨fun h hu => h.ne' (E.ord_eq_zero hu), fun h => ?_⟩
  refine lt_of_le_of_ne ((E.ord_nonneg_iff he).2 e.2) fun h0 => h ?_
  exact IsUnit.of_mul_eq_one ⟨_, ((E.ord_eq_zero_iff he).1 h0.symm).2⟩
    (Subtype.ext (mul_inv_cancel₀ he))

variable {κ : Type} [Field κ] [Algebra ℂ κ]

theorem map_eq_zero_of_gens {k : ℕ} (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ')
    (E : Place (algebraMap ℂ K)) (hER : E.Contains R) (t : E.ring) (zR : Fin k → R)
    (𝔭 : Ideal (tens (κ' := κ') (placeAlg E)))
    (hπc : ∀ a (h : algebraMap ℂ K a ∈ R), π ⟨algebraMap ℂ K a, h⟩ = algebraMap ℂ κ a)
    (hRc : ∀ a, algebraMap ℂ K a ∈ R) (hfr : ∀ f : κ, ∃ a b : R, π b ≠ 0 ∧ f * π b = π a)
    (hker : ∀ r : R, (r : K) ≠ 0 → (π r = 0 ↔ 0 < E.ord r)) (ht : Irreducible t)
    (hz : IsTranscendenceBasis ℂ fun i => π (zR i))
    (h𝔭 : 𝔭 ∈ (graphIdeal E R π ρ).minimalPrimes)
    {D : Type} [CommRing D] [IsLocalRing D] (μ : tens (κ' := κ') (placeAlg E) →+* D)
    (hμ : ∀ b, IsUnit (μ b) ↔ b ∉ 𝔭) (hg : ∀ i, μ (gens E R π ρ hER t zR i) = 0) :
    ∀ b ∈ 𝔭, μ b = 0 := by
  haveI : CharZero κ := charZero_of_injective_algebraMap (algebraMap ℂ κ).injective
  let j : R →+* E.ring := R.subtype.codRestrict E.ring fun r => hER r r.2
  obtain ⟨ι, hι⟩ := exists_extension π ((IsLocalRing.residue E.ring).comp j) (fun a => by
    by_cases ha : (a : K) = 0
    · obtain rfl : a = 0 := Subtype.ext ha
      simp
    · rw [hker a ha, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff]
      exact ord_pos_iff E (j a) ha) hfr
  have hmax : IsLocalRing.maximalIdeal E.ring = Ideal.span {t} := ht.maximalIdeal_eq
  let φ : IsLocalRing.ResidueField E.ring →+* D :=
    Ideal.Quotient.lift _ (μ.comp (inl κ' E)) fun a ha => by
      rw [hmax, Ideal.mem_span_singleton] at ha
      obtain ⟨c, rfl⟩ := ha
      have h0 : μ (inl κ' E t) = 0 := hg 0
      rw [map_mul, RingHom.comp_apply, h0, zero_mul]
  have hφ : ∀ e, φ (IsLocalRing.residue E.ring e) = μ (inl κ' E e) := fun _ => rfl
  let ψ : κ' →+* D := μ.comp (inr E)
  let α : κ →+* D := φ.comp ι
  let β : κ →+* D := ψ.comp ρ.toRingHom
  have hαβ : ∀ a : R, α (π a) - β (π a) = μ (inl κ' E (j a) - inr E (ρ (π a))) := fun a => by
    rw [map_sub, ← hφ]
    exact congrArg (fun y => φ y - β (π a)) (hι a)
  have hmR : ∀ a : R, α (π a) - β (π a) ∈ IsLocalRing.maximalIdeal D := fun a => by
    rw [hαβ, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hμ, not_not]
    exact h𝔭.1.2 (Ideal.subset_span (Or.inr ⟨a, rfl⟩))
  have hιc : ∀ a, ι (algebraMap ℂ κ a) = IsLocalRing.residue E.ring (E.const a) := fun a => by
    rw [← hπc a (hRc a), hι]
    rfl
  have heq : α = β := by
    refine ringHom_eq_of_trBasis hz α β (fun a => ?_) (fun i => ?_) (fun x => ?_)
    · change φ (ι _) = μ (inr E (ρ _))
      rw [hιc, hφ, inl_const, AlgHom.commutes]
    · rw [← sub_eq_zero, hαβ]
      exact hg i.succ
    · obtain ⟨a, b, hb, e⟩ := hfr x
      intro hu
      have hu' : IsUnit ((α x - β x) * α (π b)) := hu.mul ((IsUnit.mk0 _ hb).map α)
      have e' : (α x - β x) * α (π b) =
          (α (π a) - β (π a)) - β x * (α (π b) - β (π b)) := by
        rw [← e, map_mul, map_mul]
        ring
      rw [e'] at hu'
      exact (sub_mem (hmR a) (Ideal.mul_mem_left _ _ (hmR b))) hu'
  letI : Algebra κ (IsLocalRing.ResidueField E.ring) := ι.toAlgebra
  letI : Algebra κ κ' := ρ.toRingHom.toAlgebra
  letI : Algebra κ D := α.toAlgebra
  haveI : IsReduced (IsLocalRing.ResidueField E.ring ⊗[κ] κ') :=
    GlobalTheory.ReducedAlg.isReduced_field_tensor _ _
  let φ' : IsLocalRing.ResidueField E.ring →ₐ[κ] D := { φ with commutes' := fun _ => rfl }
  let ψ' : κ' →ₐ[κ] D := { ψ with commutes' := fun x => (RingHom.congr_fun heq x).symm }
  let χ := Algebra.TensorProduct.productMap φ' ψ'
  let u : IsLocalRing.ResidueField E.ring →ₐ[κ] IsLocalRing.ResidueField E.ring ⊗[κ] κ' :=
    Algebra.TensorProduct.includeLeft
  let v : κ' →ₐ[κ] IsLocalRing.ResidueField E.ring ⊗[κ] κ' := Algebra.TensorProduct.includeRight
  have huv : ∀ x, u (ι x) = v (ρ x) := fun x => (u.commutes x).trans (v.commutes x).symm
  obtain ⟨θ, hθ₁, hθ₂⟩ := exists_tens_lift E (u.toRingHom.comp (IsLocalRing.residue E.ring))
    v.toRingHom fun a => by
      change u (IsLocalRing.residue E.ring (E.const a)) = v _
      rw [← hιc, huv, AlgHom.commutes]
  have hχ : χ.toRingHom.comp θ = μ := by
    refine tens_ringHom_ext E (fun e => ?_) (fun b => ?_)
    · rw [RingHom.comp_apply, hθ₁, ← hφ]
      exact Algebra.TensorProduct.productMap_left_apply φ' ψ' _
    · rw [RingHom.comp_apply, hθ₂]
      exact Algebra.TensorProduct.productMap_right_apply φ' ψ' _
  have hI : graphIdeal E R π ρ ≤ RingHom.ker θ := by
    refine Ideal.span_le.2 ?_
    rintro b (⟨e, he, hb⟩ | ⟨a, hb⟩)
    · have he0 : e ≠ 0 := by
        rintro rfl
        simp [Place.ord] at he
      have hmem : e ∈ E.ring := (E.ord_nonneg_iff he0).1 he.le
      obtain rfl : b = inl κ' E ⟨e, hmem⟩ := Subtype.ext hb
      change θ _ = 0
      rw [hθ₁, RingHom.comp_apply,
        (IsLocalRing.residue_eq_zero_iff _).2 ((ord_pos_iff E ⟨e, hmem⟩ he0).1 he), map_zero]
    · obtain rfl : b = inl κ' E (j a) - inr E (ρ (π a)) := Subtype.ext hb
      change θ _ = 0
      rw [map_sub, hθ₁, hθ₂, sub_eq_zero]
      exact (congrArg u (hι a).symm).trans (huv _)
  intro b hb
  obtain ⟨s, hs, n, hn⟩ := exists_mul_mem_radical h𝔭 hb
  have h1 : θ (b * s) = 0 := IsNilpotent.eq_zero ⟨n, by rw [← map_pow]; exact hI hn⟩
  have h2 : μ b * μ s = 0 := by
    rw [← map_mul, ← hχ, RingHom.comp_apply, h1, map_zero]
  exact ((hμ s).2 hs).mul_left_eq_zero.1 h2

theorem maximalIdeal_locAt_eq_span : ∀ {K κ κ' L : Type} [Field K] [Field κ] [Field κ'] [Field L] [Algebra ℂ K] [Algebra ℂ κ] [Algebra ℂ κ']
    [Algebra (K ⊗[ℂ] κ') L] [IsFractionRing (K ⊗[ℂ] κ') L]
    (k : ℕ) (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ') (E : Place (algebraMap ℂ K))
    (hER : E.Contains R) (t : E.ring) (zR : Fin k → R)
    (𝔭 : Ideal (tens (κ' := κ') (placeAlg E))) [𝔭.IsPrime],
  (∃ O' : Subring κ', IsLocModel (algebraMap ℂ κ') O') →
  (∀ a (h : algebraMap ℂ K a ∈ R), π ⟨algebraMap ℂ K a, h⟩ = algebraMap ℂ κ a) →
  (∀ a, algebraMap ℂ K a ∈ R) → (∀ f : κ, ∃ a b : R, π b ≠ 0 ∧ f * π b = π a) →
  (∀ r : R, (r : K) ≠ 0 → (π r = 0 ↔ 0 < E.ord r)) →
  Irreducible t → TrBasis (algebraMap ℂ κ) (fun i => π (zR i)) →
  𝔭 ∈ (graphIdeal E R π ρ).minimalPrimes →
  letI := isLocalRing_locAt (L := L) 𝔭 (IsFractionRing.injective (K ⊗[ℂ] κ') L)
  IsLocalRing.maximalIdeal (locAt (L := L) 𝔭) =
    Ideal.span (Set.range fun i => toQ 𝔭 (gens E R π ρ hER t zR i)) := by
  intro K κ κ' L _ _ _ _ _ iκ _ _ _ k R π ρ E hER t zR 𝔭 _ _ hπc hRc hfr hker ht hz h𝔭
  have hinj := IsFractionRing.injective (K ⊗[ℂ] κ') L
  letI := isLocalRing_locAt (L := L) 𝔭 hinj
  have hz' : IsTranscendenceBasis ℂ fun i => π (zR i) := by
    have e : (algebraMap ℂ κ).toAlgebra = iκ := Algebra.algebra_ext _ _ fun _ => rfl
    unfold TrBasis at hz
    rw [e] at hz
    exact hz
  set J : Ideal (locAt (L := L) 𝔭) :=
    Ideal.span (Set.range fun i => toQ 𝔭 (gens E R π ρ hER t zR i)) with hJ
  have hle : J ≤ IsLocalRing.maximalIdeal (locAt (L := L) 𝔭) := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    refine (toQ_mem_maximalIdeal_iff 𝔭 hinj).2 (h𝔭.1.2 (Ideal.subset_span ?_))
    refine Fin.cases ?_ (fun i => ?_) i
    · exact Or.inl ⟨t, by rw [E.ord_irreducible ht]; exact one_pos, rfl⟩
    · exact Or.inr ⟨zR i, rfl⟩
  have hne : J ≠ ⊤ := fun h => (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.1 (h ▸ hle))
  haveI : Nontrivial (locAt (L := L) 𝔭 ⧸ J) := Ideal.Quotient.nontrivial_iff.2 hne
  haveI : IsLocalRing (locAt (L := L) 𝔭 ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  haveI : IsLocalHom (Ideal.Quotient.mk J) :=
    IsLocalHom.of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  have key := map_eq_zero_of_gens R π ρ E hER t zR 𝔭 hπc hRc hfr hker ht hz' h𝔭
    ((Ideal.Quotient.mk J).comp (toQ 𝔭))
    (fun b => (isUnit_map_iff (Ideal.Quotient.mk J) _).trans (isUnit_toQ_iff 𝔭 hinj))
    (fun i => Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨i, rfl⟩))
  refine le_antisymm (fun x hx => ?_) hle
  obtain ⟨a, s, hs, e⟩ := exists_mul_toQ 𝔭 x
  have ha : a ∈ 𝔭 := (toQ_mem_maximalIdeal_iff 𝔭 hinj).1 (e ▸ Ideal.mul_mem_right _ _ hx)
  have haJ : toQ (L := L) 𝔭 a ∈ J := Ideal.Quotient.eq_zero_iff_mem.1 (key a ha)
  rw [← e] at haJ
  exact (Ideal.mul_unit_mem_iff_mem J (isUnit_toQ 𝔭 hinj hs)).1 haJ

end GlobalTheory.GraphLocal.MaxGen
