import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.NormsFree
import Formalism.LocalToGlobal.ProjectiveLattices.RegPFree
import Formalism.LocalToGlobal.ProjectiveLattices.RegQFree
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.LiftLaSpec
import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliSchemeLevelMapsHeckePointsStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModuliConsequenceOfAbelianSchemeLaws
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFormEqOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CompEqIdOfTwists
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TypeFnPeriodExistModuliNonempty
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelOfSplitAndLevelCoeffExist
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsIntegralRatZetaOfCoeff
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PointsDetectFrobeniusSectionsStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDeltaDatumHigherLevel
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HalvesFreeAndAdjoint
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsEquivariantFunOnSpanningFamilies
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DetEqOneOfTrivialOnHalf
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIdempotentSectionFamily
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelAutomorphismPeriodFamilyStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsComplexFrobeniusPointsStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DetOneReductionOfDetOneStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DetCharacterReductionInvariantStatement

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

namespace GlobalTheory.CharacterFunction

theorem exists_weight {ι A : Type} [Finite ι] [CommGroup A] (R : ι → ι → A → Prop)
    (tr : ∀ i j m a b, R i j a → R j m b → R i m (a * b)) (loop : ∀ i a, R i i a → a = 1)
    (hf : ∀ i j a, R i j a → ∃ f : ι → ι, Function.Surjective f ∧ f i = j ∧ ∀ x, R x (f x) a)
    (N : ℕ) (hN : ∀ i j a, R i j a → a ^ N = 1) :
    ∃ v : ι → A, (∀ i, v i ^ N = 1) ∧ ∀ i j a, R i j a → v j = a * v i := by
  have sy : ∀ i j a, R i j a → R j i a⁻¹ := by
    intro i j a h
    obtain ⟨f, hs, rfl, hx⟩ := hf i j a h
    have hi : Function.Injective f := Finite.injective_iff_surjective.2 hs
    obtain ⟨N, hN, hp⟩ := Function.mem_periodicPts.1 (hi.mem_periodicPts i)
    have it : ∀ m x, R x (f^[m + 1] x) (a ^ (m + 1)) := by
      intro m
      induction m with
      | zero => intro x; simpa using hx x
      | succ m ih =>
        intro x
        rw [Function.iterate_succ_apply', pow_succ]
        exact tr _ _ _ _ _ (ih x) (hx _)
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    have h2 : f^[2 * M + 1] (f i) = i := by
      rw [← Function.iterate_succ_apply]
      have := (hp.mul_const 2).eq
      rwa [show (M + 1) * 2 = (2 * M + 1).succ by simp only [Nat.succ_eq_add_one]; ring] at this
    have h3 := it (2 * M) (f i)
    rw [h2] at h3
    rwa [← eq_inv_of_mul_eq_one_right (loop _ _ (tr _ _ _ _ _ h h3))]
  let R' : ι → ι → A → Prop := fun i j a => (i = j ∧ a = 1) ∨ R i j a
  have sy' : ∀ i j a, R' i j a → R' j i a⁻¹ := by
    rintro i j a (⟨rfl, rfl⟩ | h)
    · exact Or.inl ⟨rfl, inv_one⟩
    · exact Or.inr (sy _ _ _ h)
  have tr' : ∀ i j m a b, R' i j a → R' j m b → R' i m (a * b) := by
    rintro i j m a b (⟨rfl, rfl⟩ | h) h'
    · rwa [one_mul]
    · rcases h' with ⟨rfl, rfl⟩ | h'
      · rw [mul_one]; exact Or.inr h
      · exact Or.inr (tr _ _ _ _ _ h h')
  have loop' : ∀ i a, R' i i a → a = 1 := by
    rintro i a (⟨-, h⟩ | h)
    · exact h
    · exact loop _ _ h
  let s : Setoid ι := ⟨fun i j => ∃ a, R' i j a, fun i => ⟨1, Or.inl ⟨rfl, rfl⟩⟩,
    fun ⟨a, h⟩ => ⟨_, sy' _ _ _ h⟩, fun ⟨a, h⟩ ⟨b, h'⟩ => ⟨_, tr' _ _ _ _ _ h h'⟩⟩
  have hv : ∀ i, ∃ a, R' (Quotient.mk s i).out i a := fun i => Quotient.mk_out (s := s) i
  choose v hv using hv
  refine ⟨v, fun i => (hv i).elim (fun h => by rw [h.2, one_pow]) (hN _ _ _), fun i j a h => ?_⟩
  have e : Quotient.mk s i = Quotient.mk s j := Quotient.sound ⟨a, Or.inr h⟩
  have h1 := hv j
  rw [← e] at h1
  have h2 := loop' _ _ (tr' _ _ _ _ _ (tr' _ _ _ _ _ (hv i) (Or.inr h)) (sy' _ _ _ h1))
  rw [mul_inv_eq_one] at h2
  rw [← h2, mul_comm]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

theorem levAut_mul {l : Level H} {Xo : Moduli Dw l} {g g' : Sim Dw} {ρ ρ' : Xo.X ≅ Xo.X} (h : Xo.LevAut g ρ)
    (h' : Xo.LevAut g' ρ') : Xo.LevAut (SimAlg.mul g g') (ρ ≪≫ ρ') := by
  obtain ⟨hs, ν, a, b⟩ := h
  obtain ⟨hs', ν', a', b'⟩ := h'
  obtain ⟨n, hn⟩ := Moduli.LevelAction.exists_comp_sabMap ν ν' (h := (ρ ≪≫ ρ').hom) rfl
  refine ⟨by rw [Iso.trans_hom, Category.assoc, hs', hs], n, fun x => ?_, fun x => ?_⟩
  · rw [hn, Iso.trans_hom, Category.assoc, ← a', ← Category.assoc, ← Category.assoc, ← a]; rfl
  · rw [hn, Iso.trans_hom, Category.assoc, ← b', ← Category.assoc, ← Category.assoc, ← b]; rfl

theorem natCast_mem_half {l l₂ : Level H} {pd : ℕ} {I : Ideal (𝓞 E)} (hM : l₂.M = l.M * pd)
    (hMb : l₂.Mb = l.Mb * I) : (pd : 𝓞 E) ∈ I := by
  have hM0 : l.M ≠ 0 := by have := l.three_le; omega
  have hp : I * I.map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {(pd : 𝓞 E)} := by
    have h2 := l₂.prod
    rw [hMb, hM, Ideal.map_mul, mul_mul_mul_comm, l.prod, Nat.cast_mul,
      ← Ideal.span_singleton_mul_span_singleton] at h2
    refine mul_left_cancel₀ ?_ h2
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hM0
  have : Ideal.span {(pd : 𝓞 E)} ≤ I := hp ▸ Ideal.mul_le_left
  exact this (Ideal.subset_span rfl)

theorem nsmul_mem_smul_top {R L : Type} [CommRing R] [AddCommGroup L] [Module R L] {I : Ideal R} {N : ℕ}
    (h : (N : R) ∈ I) (x : L) : N • x ∈ (I • ⊤ : Submodule R L) := by
  rw [← Nat.cast_smul_eq_nsmul R]
  exact Submodule.smul_mem_smul h trivial

theorem four_le_card {R : Type} [CommRing R] [Finite R] {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (h : (p : R) = 0)
    (𝔪 : Ideal R) (hm : 𝔪.IsMaximal) : 4 ≤ Nat.card (R ⧸ 𝔪) := by
  letI : Field (R ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  haveI : Finite (R ⧸ 𝔪) := Finite.of_surjective _ Ideal.Quotient.mk_surjective
  have h0 : (p : R ⧸ 𝔪) = 0 := by rw [← map_natCast (Ideal.Quotient.mk 𝔪), h, map_zero]
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP (R ⧸ 𝔪) p := (CharP.charP_iff_prime_eq_zero hp).2 h0
  have := Nat.card_le_card_of_injective _ (ZMod.castHom (dvd_refl p) (R ⧸ 𝔪)).injective
  rw [Nat.card_zmod] at this
  omega

theorem char_eq_one {l l₂ : Level H} {pd : ℕ} {I : Ideal (𝓞 E)} (hp : pd.Prime) (h5 : 5 ≤ pd) (hM : l₂.M = l.M * pd)
    (hA : l₂.A = 1) (hMb : l₂.Mb = l.Mb * I) {A : Type} [CommGroup A]
    (ψ : ((Dw.La ⧸ (I • ⊤ : Submodule (𝓞 E) Dw.La)) ≃ₗ[𝓞 E] (Dw.La ⧸ (I • ⊤ : Submodule (𝓞 E) Dw.La))) →* A)
    (D' : Datum H) (t : Dw.La →ₗ[𝓞 E] D'.La) (tinj : ∀ a, (∃ b, t a = l₂.M' • b) → ∃ b, a = l₂.M' • b)
    (tsurj : ∀ b, ∃ a e, b = t a + l₂.M' • e) (g : Sim Dw)
    (hg : ∀ a, g.f l.M a - a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La))
    (k : (Dw.La ⧸ (I • ⊤ : Submodule (𝓞 E) Dw.La)) ≃ₗ[𝓞 E] (Dw.La ⧸ (I • ⊤ : Submodule (𝓞 E) Dw.La)))
    (hk : ∀ a, Submodule.Quotient.mk (g.f l₂.M a) = k (Submodule.Quotient.mk a))
    (γ : D'.La ≃ₗ[𝓞 E] D'.La) (hγ : ∀ a b, D'.EF (γ a) (γ b) = D'.EF a b)
    (h : ∀ a, γ (t (g.f l₂.M a)) - t a ∈ l₂.Mb • (⊤ : Submodule (𝓞 E) D'.La)) : ψ k = 1 := by
  have hM' : l₂.M' = l.M * pd := by rw [Level.M', hA, Nat.lcm_one_right, hM]
  have hpI : (pd : 𝓞 E) ∈ I := natCast_mem_half hM hMb
  have hMI : ((l₂.M' : ℕ) : 𝓞 E) ∈ I := by rw [hM', Nat.cast_mul]; exact I.mul_mem_left _ hpI
  have hMl : (l.M : 𝓞 E) ∈ l.Mb := by
    have : Ideal.span {(l.M : 𝓞 E)} ≤ l.Mb := l.prod ▸ Ideal.mul_le_left
    exact this (Ideal.subset_span rfl)
  have hMl' : ((l₂.M' : ℕ) : 𝓞 E) ∈ l.Mb := by rw [hM', Nat.cast_mul]; exact l.Mb.mul_mem_right _ hMl
  have hmap : ∀ (J : Ideal (𝓞 E)) {L L' : Type} [AddCommGroup L] [Module (𝓞 E) L] [AddCommGroup L'] [Module (𝓞 E) L']
      (f : L →ₗ[𝓞 E] L') (x : L), x ∈ (J • ⊤ : Submodule (𝓞 E) L) → f x ∈ (J • ⊤ : Submodule (𝓞 E) L') := by
    intro J L L' _ _ _ _ f x hx
    have := Submodule.mem_map_of_mem (f := f) hx
    rw [Submodule.map_smul''] at this
    exact Submodule.smul_mono le_rfl le_top this
  have hlow : ∀ b, γ b - b ∈ l.Mb • (⊤ : Submodule (𝓞 E) D'.La) := by
    intro b
    obtain ⟨a, e, rfl⟩ := tsurj b
    obtain ⟨w, hw⟩ := g.tower l.M pd (by have := l.three_le; omega) hp.pos a
    rw [← hM] at hw
    have h1 : g.f l₂.M a - a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) := by
      have := add_mem (hw ▸ nsmul_mem_smul_top hMl w) (hg a)
      rwa [sub_add_sub_cancel] at this
    have h2 := hmap _ (γ : D'.La →ₗ[𝓞 E] D'.La) _ (hmap _ t _ h1)
    have h3 : γ (t (g.f l₂.M a)) - t a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D'.La) :=
      Submodule.smul_mono (hMb ▸ Ideal.mul_le_left) le_rfl (h a)
    have h4 := add_mem (sub_mem h3 h2) (nsmul_mem_smul_top hMl' (γ e - e))
    convert h4 using 1
    simp only [map_add, map_sub, map_nsmul, LinearEquiv.coe_coe, smul_sub]
    abel
  have hdet := HalfLevelDet.det_eq_one_of_trivial_on_half E H D' l γ hγ (fun a ha => by
    have : γ a - a ∈ (Ideal.span {(l.M : 𝓞 E)} • ⊤ : Submodule (𝓞 E) D'.La) := by
      refine Submodule.smul_induction_on ha (fun c hc b _ => ?_) (fun u v hu hv => ?_)
      · rw [map_smul, ← smul_sub, ← l.prod, mul_comm, Submodule.mul_smul]
        exact Submodule.smul_mem_smul hc (hlow b)
      · rw [map_add, add_sub_add_comm]; exact add_mem hu hv
    rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at this
    obtain ⟨e, -, he⟩ := this
    exact ⟨e, by rw [← Nat.cast_smul_eq_nsmul (𝓞 E), he]; abel⟩)
  have hI0 : I ≠ ⊥ := fun e => hp.ne_zero (by rw [e, Ideal.mem_bot] at hpI; exact_mod_cast hpI)
  haveI : Finite (𝓞 E ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot _ hI0
  haveI := D'.fin
  haveI := D'.proj
  have hsurj : ∀ b, ∃ a, b - t a ∈ (I • ⊤ : Submodule (𝓞 E) D'.La) := fun b => by
    obtain ⟨a, e, rfl⟩ := tsurj b
    exact ⟨a, by rw [add_sub_cancel_left]; exact nsmul_mem_smul_top hMI e⟩
  refine GlobalTheory.T.det_character_reduction_invariant (𝓞 E) Dw.La D'.La I A ψ t (γ : D'.La →ₗ[𝓞 E] D'.La) k
    (four_le_card hp h5 (by rw [← map_natCast (Ideal.Quotient.mk I)]; exact Ideal.Quotient.eq_zero_iff_mem.2 hpI))
    hsurj (fun a ha => ?_) (GlobalTheory.T.det_one_reduction_of_det_one (𝓞 E) E D'.La I _ hdet)
    (fun a => ⟨_, hk a, Submodule.smul_mono (hMb ▸ Ideal.mul_le_right) le_rfl (h a)⟩)
  have key : ∀ b ∈ (I • ⊤ : Submodule (𝓞 E) D'.La), ∃ a' ∈ (I • ⊤ : Submodule (𝓞 E) Dw.La), ∃ e,
      b = t a' + l₂.M' • e := by
    intro b hb
    refine Submodule.smul_induction_on hb (fun c hc b _ => ?_) ?_
    · obtain ⟨a, e, rfl⟩ := tsurj b
      exact ⟨c • a, Submodule.smul_mem_smul hc trivial, c • e, by rw [smul_add, map_smul, smul_comm c l₂.M']⟩
    · rintro _ _ ⟨u, hu, e, rfl⟩ ⟨v, hv, e', rfl⟩
      exact ⟨u + v, add_mem hu hv, e + e', by rw [map_add, smul_add]; abel⟩
  obtain ⟨a', ha', e, he⟩ := key _ ha
  obtain ⟨b, hb⟩ := tinj (a - a') ⟨e, by rw [map_sub, he, add_sub_cancel_left]⟩
  have := add_mem (hb ▸ nsmul_mem_smul_top hMI b) ha'
  rwa [sub_add_cancel] at this

theorem exists_component_weight {l l₂ : Level H} {pd : ℕ} {I : Ideal (𝓞 E)} (hr : 1 ≤ Dw.p + Dw.q) (hp : pd.Prime)
    (h5 : 5 ≤ pd) (hM : l₂.M = l.M * pd) (hA : l₂.A = 1) (hMb : l₂.Mb = l.Mb * I) {A : Type} [CommGroup A]
    (ψ : ((Dw.La ⧸ (I • ⊤ : Submodule (𝓞 E) Dw.La)) ≃ₗ[𝓞 E] (Dw.La ⧸ (I • ⊤ : Submodule (𝓞 E) Dw.La))) →* A)
    (Xo : Moduli Dw l₂) (c : Coeff l₂) {g₀ : ℕ} {ty : Fin g₀ → (E →+* ℂ)} (hty : IsTypeFn H Dw.p Dw.q ty)
    (F : FamilyUnif Xo (KA l₂).val.toRingHom ty) (N : ℕ) (hN : ∀ k, ψ k ^ N = 1) :
    ∃ v : Fin F.n → A, (∀ i, v i ^ N = 1) ∧ ∀ k (g : Sim Dw) (ρ : Xo.X ≅ Xo.X),
      (∀ a, g.f l.M a - a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) → Xo.LevAut g ρ →
      (∀ a, Submodule.Quotient.mk (g.f l₂.M a) = k (Submodule.Quotient.mk a)) →
      ∀ i j P P', IsPeriod (F.Di i) ty P → IsPeriod (F.Di j) ty P' → F.u i P ≫ ρ.hom = F.u j P' →
        v j = ψ k * v i := by
  have hper : ∀ i, ∃ P, IsPeriod (F.Di i) ty P := fun i =>
    ((PeriodExists.typeFn_period_exist E H (F.Di i)).2.1 g₀ ty (by rw [(F.sig i).1, (F.sig i).2]; exact hty)).2
  let R : Fin F.n → Fin F.n → A → Prop := fun i j a => ∃ (k : _) (g : Sim Dw) (ρ : Xo.X ≅ Xo.X),
    (∀ a, g.f l.M a - a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) ∧ Xo.LevAut g ρ ∧
    (∀ a, Submodule.Quotient.mk (g.f l₂.M a) = k (Submodule.Quotient.mk a)) ∧ a = ψ k ∧
    ∀ P, IsPeriod (F.Di i) ty P → ∃ P', IsPeriod (F.Di j) ty P' ∧ F.u i P ≫ ρ.hom = F.u j P'
  suffices key : ∃ v : Fin F.n → A, (∀ i, v i ^ N = 1) ∧ ∀ i j a, R i j a → v j = a * v i by
    obtain ⟨v, hv₀, hv⟩ := key
    refine ⟨v, hv₀, fun k g ρ hg hρ hk i j P P' hP hP' e => hv i j _ ⟨k, g, ρ, hg, hρ, hk, rfl, ?_⟩⟩
    obtain ⟨j', hj'⟩ := (GlobalTheory.T.level_automorphism_period_family E H Dw l₂ Xo c hr hA g₀ ty F g ρ hty hρ).1 i
    obtain ⟨Q, hQ, e'⟩ := hj' P hP
    obtain rfl := F.disj _ _ _ _ hQ hP' (e'.symm.trans e)
    exact hj'
  refine exists_weight R ?_ ?_ ?_ N (by rintro i j _ ⟨k, -, -, -, -, -, rfl, -⟩; exact hN k)
  · rintro i j m _ _ ⟨k, g, ρ, hg, hρ, hk, rfl, h⟩ ⟨k', g', ρ', hg', hρ', hk', rfl, h'⟩
    refine ⟨k * k', SimAlg.mul g g', ρ ≪≫ ρ', fun a => ?_, levAut_mul hρ hρ', fun a => ?_, (map_mul ψ _ _).symm,
      fun P hP => ?_⟩
    · have := add_mem (hg (g'.f l.M a)) (hg' a)
      rwa [sub_add_sub_cancel] at this
    · rw [LinearEquiv.mul_apply, ← hk', ← hk]; rfl
    · obtain ⟨P', hP', e⟩ := h P hP
      obtain ⟨P'', hP'', e'⟩ := h' P' hP'
      exact ⟨P'', hP'', by rw [Iso.trans_hom, ← Category.assoc, e, e']⟩
  · rintro i _ ⟨k, g, ρ, hg, hρ, hk, rfl, h⟩
    obtain ⟨P, hP⟩ := hper i
    obtain ⟨P', hP', e⟩ := h P hP
    obtain ⟨γ, hγ, hγ'⟩ := (GlobalTheory.T.level_automorphism_period_family E H Dw l₂ Xo c hr hA g₀ ty F g ρ hty hρ).2 i P P' hP hP' e
    exact char_eq_one hp h5 hM hA hMb ψ (F.Di i) (F.t i) (fun a => (F.t_inj i a).1) (F.t_surj i) g hg k hk γ hγ hγ'
  · rintro i j _ ⟨k, g, ρ, hg, hρ, hk, rfl, h⟩
    choose f hf using (GlobalTheory.T.level_automorphism_period_family E H Dw l₂ Xo c hr hA g₀ ty F g ρ hty hρ).1
    refine ⟨f, fun m => ?_, ?_, fun x => ⟨k, g, ρ, hg, hρ, hk, rfl, hf x⟩⟩
    · obtain ⟨Q, hQ⟩ := hper m
      have hs : ρ.inv ≫ Xo.s = Xo.s := by rw [Iso.inv_comp_eq, hρ.1]
      obtain ⟨x, P, hP, e⟩ := F.onto (F.u m Q ≫ ρ.inv) (by rw [Category.assoc, hs, F.over_σ m Q hQ])
      obtain ⟨P', hP', e'⟩ := hf x P hP
      rw [e, Category.assoc, Iso.inv_hom_id, Category.comp_id] at e'
      exact ⟨x, (F.disj _ _ _ _ hQ hP' e').symm⟩
    · obtain ⟨P, hP⟩ := hper i
      obtain ⟨P', hP', e⟩ := h P hP
      obtain ⟨P'', hP'', e'⟩ := hf i P hP
      exact F.disj _ _ _ _ hP'' hP' (e'.symm.trans e)

theorem isLev_psiTie {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} (d : DeltaDat Xo c n) (hd : d.IsLev)
    (ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ) {g₀ : ℕ} {ty : Fin g₀ → (E →+* ℂ)}
    (F : FamilyUnif d.Xo₂ (KA d.l₂).val.toRingHom ty) (χ : Fin F.n → Rul d.Xo₂ d.c₂)
    (hχ : ∀ i, χ i ∈ sec d.Xo₂ d.c₂ 0 0)
    (hval : ∀ i (y : FrPt d.Xo₂ d.c₂ (CAt d.c₂.F.val.toRingHom)) (i' : Fin F.n) P, IsPeriod (F.Di i') ty P →
      y.x = F.u i' P → evR d.Xo₂ d.c₂ (χ i) y = if i' = i then 1 else 0)
    (v : Fin F.n → c.Fˣ) (N : ℕ) (hN : ∀ i, v i ^ N = 1)
    (hv : ∀ k (g : Sim Dw) (ρ : d.Xo₂.X ≅ d.Xo₂.X),
      (∀ a, g.f l.M a - a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) → d.Xo₂.LevAut g ρ →
      (∀ a, Submodule.Quotient.mk (g.f d.l₂.M a) = k (Submodule.Quotient.mk a)) →
      ∀ i j P P', IsPeriod (F.Di i) ty P → IsPeriod (F.Di j) ty P' → F.u i P ≫ ρ.hom = F.u j P' →
        v j = ψ k * v i) :
    ∃ f : Rul d.Xo₂ d.c₂, DeltaDat.IsLev { d with cδ := f } ∧ DeltaDat.PsiTie { d with cδ := f } ψ ∧ f ^ N = 1 := by
  let f : Rul d.Xo₂ d.c₂ := ∑ i, d.eF (v i : c.F) • χ i
  have hf : f ∈ sec d.Xo₂ d.c₂ 0 0 := Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hχ i)
  have hev : ∀ (y : FrPt d.Xo₂ d.c₂ (CAt d.c₂.F.val.toRingHom)) (i : Fin F.n) P, IsPeriod (F.Di i) ty P →
      y.x = F.u i P → evR d.Xo₂ d.c₂ f y = algebraMap d.c₂.F _ (d.eF (v i : c.F)) := by
    intro y i P hP e
    have h1 : evR d.Xo₂ d.c₂ f y = ∑ j, d.eF (v j : c.F) • evR d.Xo₂ d.c₂ (χ j) y := by
      change evalL (K := d.c₂.F) (fun S _ _ => FrPt d.Xo₂ d.c₂ S) (fun φ y z => FrMap φ y z) y f = _
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => map_smul _ _ _
    rw [h1, Finset.sum_eq_single i]
    · rw [hval i y i P hP e, if_pos rfl, Algebra.smul_def, mul_one]
    · intro j _ hj
      rw [hval j y i P hP e, if_neg (Ne.symm hj), smul_zero]
    · simp
  have hon : ∀ y : FrPt d.Xo₂ d.c₂ (CAt d.c₂.F.val.toRingHom), ∃ i P, IsPeriod (F.Di i) ty P ∧ F.u i P = y.x :=
    fun y => F.onto y.x y.x_over
  haveI : IsDomain (CAt d.c₂.F.val.toRingHom) := inferInstanceAs (IsDomain ℂ)
  have hne : ∀ i, algebraMap d.c₂.F (CAt d.c₂.F.val.toRingHom) (d.eF (v i : c.F)) ≠ 0 := fun i h =>
    (v i).ne_zero (d.eF.injective ((algebraMap d.c₂.F (CAt d.c₂.F.val.toRingHom)).injective (by
      rw [h, map_zero, map_zero])))
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, -, -⟩ := hd
  refine ⟨f, ⟨h1, h2, h3, h4, h5, h6, h7, hf, fun k _ _ _ y h0 => ?_⟩, fun k g ρ hg _ hρ hk K _ _ _ y y' e => ?_, ?_⟩
  · obtain ⟨z, -, -, hz, -⟩ := GlobalTheory.T.exists_complex_frobenius_points E H Dw d.l₂ d.Xo₂ d.c₂ k y y
    obtain ⟨i, P, hP, e⟩ := hon z
    have := hz f hf h0
    rw [hev z i P hP e.symm] at this
    exact hne i this
  · obtain ⟨z, z', hρz, -, hz⟩ := GlobalTheory.T.exists_complex_frobenius_points E H Dw d.l₂ d.Xo₂ d.c₂ K y y'
    obtain ⟨i, P, hP, e₁⟩ := hon z
    obtain ⟨j, P', hP', e₂⟩ := hon z'
    refine hz f hf _ ?_
    rw [hev z i P hP e₁.symm, hev z' j P' hP' e₂.symm,
      hv k g ρ hg.2.1 hρ hk i j P P' hP hP' (by rw [e₁, e₂]; exact (hρz _ e).symm), Units.val_mul, map_mul, map_mul]
    rfl
  · have hone : (1 : Rul d.Xo₂ d.c₂) ∈ sec d.Xo₂ d.c₂ 0 0 := by
      refine ⟨fun p q φ y z _ => by simp, fun p t y y' _ => ?_⟩
      have : wchar (ex Dw 0 0) t = 1 := by
        unfold wchar
        refine Finset.prod_eq_one fun i _ => ?_
        cases i <;> simp [ex]
      simp [this]
    have hpow : ∀ m : ℕ, f ^ m ∈ sec d.Xo₂ d.c₂ 0 0 := by
      intro m
      induction m with
      | zero => rw [pow_zero]; exact hone
      | succ m ih => rw [pow_succ]; simpa using sec_mul d.Xo₂ d.c₂ 0 0 0 0 ih hf
    have hs := Submodule.sub_mem _ (hpow N) hone
    refine sub_eq_zero.1 (GlobalTheory.T.points_detect_frobenius_sections E H Dw d.l₂ d.Xo₂ d.c₂ 0 0 _ hs fun K _ _ _ y => ?_)
    obtain ⟨z₀, z, -, -, hz⟩ := GlobalTheory.T.exists_complex_frobenius_points E H Dw d.l₂ d.Xo₂ d.c₂ K y y
    obtain ⟨i, P, hP, e⟩ := hon z
    have e₀ := hev z i P hP e.symm
    have hmul : ∀ a b : Rul d.Xo₂ d.c₂, evR d.Xo₂ d.c₂ (a * b) z = evR d.Xo₂ d.c₂ a z * evR d.Xo₂ d.c₂ b z :=
      fun a b => evalAt_mul _ _ a b z
    have e₁ : evR d.Xo₂ d.c₂ 1 z = 1 := by
      have := hmul f 1
      rw [mul_one, e₀] at this
      exact (mul_eq_left₀ (hne i)).1 this.symm
    have e₂ : ∀ m : ℕ, evR d.Xo₂ d.c₂ (f ^ m) z = evR d.Xo₂ d.c₂ f z ^ m := by
      intro m
      induction m with
      | zero => rw [pow_zero, pow_zero, e₁]
      | succ m ih => rw [pow_succ, pow_succ, hmul, ih]
    have e₃ : evR d.Xo₂ d.c₂ (f ^ N - 1) z = evR d.Xo₂ d.c₂ (f ^ N) z - evR d.Xo₂ d.c₂ 1 z :=
      map_sub (evalL (K := d.c₂.F) (fun S _ _ => FrPt d.Xo₂ d.c₂ S) (fun φ y z => FrMap φ y z) z) _ _
    have := hz _ hs 0 (by
      rw [e₃, e₂, e₀, e₁, ← map_pow, ← map_pow, ← Units.val_pow_eq_pow_val, hN, Units.val_one, map_one, map_one,
        map_zero, zero_mul, sub_self])
    rwa [map_zero, zero_mul] at this

theorem exists_char_subfield {G : Type} [Group G] (ψ₀ : G →* ℂˣ) (F : IntermediateField ℚ ℂ)
    (h : ∀ k, ((ψ₀ k : ℂˣ) : ℂ) ∈ F) : ∃ ψ : G →* Fˣ, ∀ k, (((ψ k : Fˣ) : F) : ℂ) = (ψ₀ k : ℂˣ) :=
  ⟨MonoidHom.toHomUnits
    { toFun := fun k => (⟨(ψ₀ k : ℂˣ), h k⟩ : F)
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp) }, fun _ => rfl⟩

end GlobalTheory.CharacterFunction
