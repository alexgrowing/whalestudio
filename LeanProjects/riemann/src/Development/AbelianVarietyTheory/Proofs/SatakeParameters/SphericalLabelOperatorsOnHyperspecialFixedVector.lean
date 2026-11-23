import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Formalism.LocalToGlobal.ProjectiveLattices.UnramBridgeHolds
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPlaceHeckeDoubleCosetsInverseRepsLabel
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DivisorsAtInvDualLabelAndStabilizerMul
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCompletedLatticeBasisAtPrime
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompletedLatticeIntegralityFacts
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsHyperspecialDoubleCosetOfElementaryDivisor
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHeckeOpFullDualLab

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SphLabelOps

section Abstract

theorem dv_of_cartan {R K : Type} [CommRing R] [CommRing K] {n : ℕ} {Λ : (Fin n → R) → Prop} {O : R → Prop}
    {OK : Subring K} {ε : R} (φ : R →+* K) (s : K → R) (hs : ∀ t, φ (s t) = t) (hε : φ ε = 1)
    (hφ : ∀ x y, φ x = φ y → ε * x = ε * y) (hO : ∀ x, O x → φ x ∈ OK) (hO' : ∀ t ∈ OK, O (s t))
    {A B : Matrix (Fin n) (Fin n) R} {u : Fin n → R}
    (h1 : ∀ z : Fin n → R, (∀ i, O (z i)) → Λ (ε • B *ᵥ z))
    (h2 : ∀ y, Λ y → ∃ z : Fin n → R, (∀ i, O (z i)) ∧ ε • y = ε • B *ᵥ z)
    {k₁ k₂ : GL (Fin n) K} (i1 : ∀ i j, k₁.1 i j ∈ OK) (i1' : ∀ i j, (k₁⁻¹).1 i j ∈ OK)
    (i2 : ∀ i j, k₂.1 i j ∈ OK) (i2' : ∀ i j, (k₂⁻¹).1 i j ∈ OK)
    (h : A.map φ * B.map φ = B.map φ * (k₁.1 * Matrix.diagonal (fun i => φ (u i)) * k₂.1)) :
    GlobalTheory.DivDual.Dv Λ O ε u A := by
  have key : ∀ x y : Fin n → R, φ ∘ x = φ ∘ y → ε • x = ε • y := fun x y e =>
    funext fun i => hφ _ _ (congrFun e i)
  have key' : ∀ x y : Fin n → R, ε • x = ε • y → φ ∘ x = φ ∘ y := fun x y e => funext fun i => by
    have := congrArg φ (congrFun e i)
    simpa [hε] using this
  have mv : ∀ (M : Matrix (Fin n) (Fin n) R) x, φ ∘ (M *ᵥ x) = M.map φ *ᵥ (φ ∘ x) := fun M x =>
    funext fun i => RingHom.map_mulVec φ M x i
  have ss : ∀ w : Fin n → K, φ ∘ (s ∘ w) = w := fun w => funext fun i => hs _
  have int : ∀ (k : Matrix (Fin n) (Fin n) K) (z : Fin n → R), (∀ i j, k i j ∈ OK) → (∀ i, O (z i)) →
      ∀ i, O ((s ∘ (k *ᵥ (φ ∘ z))) i) := fun k z hk hz i =>
    hO' _ (OK.sum_mem (t := Finset.univ) fun j _ => mul_mem (hk i j) (hO _ (hz j)))
  have hB : (B * k₁.1.map s).map φ = B.map φ * k₁.1 := by
    rw [Matrix.map_mul]
    congr 1
    exact Matrix.ext fun i j => hs _
  have hu : ∀ z : Fin n → R, φ ∘ (fun i => u i * z i) = Matrix.diagonal (fun i => φ (u i)) *ᵥ (φ ∘ z) :=
    fun z => funext fun i => by simp [Matrix.mulVec_diagonal]
  refine ⟨B * k₁.1.map s, fun z hz => ?_, fun y hy => ?_, fun y hy => ?_, fun z hz => ?_⟩
  · rw [key _ (B *ᵥ (s ∘ (k₁.1 *ᵥ (φ ∘ z)))) (by rw [mv, mv, ss, hB, Matrix.mulVec_mulVec])]
    exact h1 _ (int _ z i1 hz)
  · obtain ⟨z, hz, e⟩ := h2 y hy
    refine ⟨_, int _ z i1' hz, key _ _ ?_⟩
    rw [key' _ _ e, mv, mv, ss, hB, Matrix.mulVec_mulVec, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  · obtain ⟨z, hz, e⟩ := h2 y hy
    refine ⟨_, int _ z i2 hz, key _ _ ?_⟩
    rw [mv, key' _ _ e, mv, mv, hu, ss, hB]
    simp only [Matrix.mulVec_mulVec, h, Matrix.mul_assoc]
  · refine ⟨_, h1 _ (int _ z i2' hz), key _ _ ?_⟩
    have e : φ ∘ (ε • B *ᵥ (s ∘ ((k₂⁻¹).1 *ᵥ (φ ∘ z)))) = φ ∘ (B *ᵥ (s ∘ ((k₂⁻¹).1 *ᵥ (φ ∘ z)))) :=
      funext fun i => by simp [hε]
    rw [mv, e, mv, mv, hu, ss, hB]
    simp only [Matrix.mulVec_mulVec]
    rw [← Matrix.mul_assoc, h]
    simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

variable {G : Type} [Group G]

def Reps (K : Subgroup G) (g : G) (R : Finset G) : Prop :=
  (∀ γ ∈ R, ∃ k₁ ∈ K, ∃ k₂ ∈ K, γ = k₁ * g * k₂) ∧
    ∀ x : G, (∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * g * k₂) → ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ K

theorem Reps.of_dc {K : Subgroup G} {g a b : G} {R : Finset G} (ha : a ∈ K) (hb : b ∈ K)
    (h : Reps K (a * g * b) R) : Reps K g R := by
  refine ⟨fun γ hγ => ?_, ?_⟩
  · obtain ⟨k₁, h₁, k₂, h₂, rfl⟩ := h.1 γ hγ
    exact ⟨_, mul_mem h₁ ha, _, mul_mem hb h₂, by group⟩
  · rintro _ ⟨k₁, h₁, k₂, h₂, rfl⟩
    exact h.2 _ ⟨_, mul_mem h₁ (inv_mem ha), _, mul_mem (inv_mem hb) h₂, by group⟩

theorem Reps.sum_eq {K : Subgroup G} {g k : G} {R R' : Finset G} (h : Reps K g R) (h' : Reps K g R') (hk : k ∈ K)
    {M : Type} [AddCommMonoid M] (F : G → M) (hF : ∀ x, ∀ l ∈ K, F (x * l) = F x) :
    ∑ γ ∈ R, F (k * γ) = ∑ γ ∈ R', F γ := by
  have mv : ∀ {l x : G}, l ∈ K → (∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * g * k₂) →
      ∃ k₁ ∈ K, ∃ k₂ ∈ K, l * x = k₁ * g * k₂ := by
    rintro l _ hl ⟨k₁, h₁, k₂, h₂, rfl⟩
    exact ⟨_, mul_mem hl h₁, _, h₂, by group⟩
  have ex := fun γ (hγ : γ ∈ R) => h'.2 _ (mv hk (h.1 γ hγ))
  refine Finset.sum_bij (fun γ hγ => (ex γ hγ).choose) (fun γ hγ => (ex γ hγ).choose_spec.1.1) ?_ ?_ ?_
  · intro a ha b hb e
    have e1 := (ex a ha).choose_spec.1.2
    have e2 := (ex b hb).choose_spec.1.2
    rw [e] at e1
    refine (h.2 b (h.1 b hb)).unique ⟨ha, ?_⟩ ⟨hb, by rw [inv_mul_cancel]; exact one_mem _⟩
    have := mul_mem (inv_mem e1) e2
    convert this using 1
    group
  · intro δ hδ
    obtain ⟨γ, ⟨hγ, e⟩, -⟩ := h.2 _ (mv (inv_mem hk) (h'.1 δ hδ))
    refine ⟨γ, hγ, ((ex γ hγ).choose_spec.2 δ ⟨hδ, ?_⟩).symm⟩
    have := inv_mem e
    convert this using 1
    group
  · intro γ hγ
    have := hF (ex γ hγ).choose _ (ex γ hγ).choose_spec.1.2
    rwa [mul_inv_cancel_left] at this

theorem Reps.card_eq {K : Subgroup G} {g : G} {R R' : Finset G} (h : Reps K g R) (h' : Reps K g R') :
    R.card = R'.card := by
  simpa using h.sum_eq h' (one_mem K) (fun _ => (1 : ℕ)) fun _ _ _ => rfl

end Abstract

section Divisors

open Formalism.L2.NTheta GlobalTheory.IdemSupport GlobalTheory.LatLocBasis

variable {D : D7} {P : HeightOneSpectrum (𝓞 D.host.E)} {e f : Formalism.L2.Theta.AE D}

theorem tie_of_isPrimeIdem (h : IsPrimeIdem P e f) : Comparison₂ P e := by
  rcases h with ⟨h, -⟩ | ⟨-, -, h⟩
  · exact h.2
  · exact h

theorem idem_mul_loc_mem (h : Comparison₂ P e) {t : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F} (ht : t ∈ Formalism.MainNotions.StandardLattice.intAf D.host.F)
    (c : locRing P) : finPart D e * (t ⊗ₜ[D.host.F] (c : D.host.E)) ∈ intAE D := by
  obtain ⟨a, s, hs, hc⟩ := c.2
  have hs0 : s ≠ 0 := fun h0 => hs (h0 ▸ P.asIdeal.zero_mem)
  have h1 : finPart D (e * incA D ((s : D.host.E)⁻¹)) ∈ intAE D := by
    by_contra hn
    exact hs ((h s hs0).2 hn)
  have h2 : (t ⊗ₜ[D.host.F] (a : D.host.E)) ∈ intAE D := AddSubgroup.subset_closure ⟨t, ht, a, rfl⟩
  have h3 := mul_mem_int D h1 h2
  have h4 : finPart D (incA D ((s : D.host.E)⁻¹)) =
    (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] ((s : D.host.E)⁻¹) := rfl
  rw [RingHom.map_mul, h4, mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_comm _ (a : D.host.E)] at h3
  rw [hc]
  exact h3

theorem idem_mul_span_mem (V : HSp D) (he : e * e = e) (h : Comparison₂ P e) {x : Fin V.rank → D.host.E}
    (hx : x ∈ Submodule.span (locRing P) (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E))) :
    (fun a => finPart D e * ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] x a)) ∈ LamHat V := by
  have hee : finPart D e * finPart D e = finPart D e := by rw [← RingHom.map_mul, he]
  induction hx using Submodule.span_induction with
  | mem x hx =>
    refine GlobalTheory.LatDual.smul_mem_lamHat V _ (GlobalTheory.SplitPlace.idem_mem he) _ ?_
    rw [GlobalTheory.LatDual.lamHat_eq_hat]
    exact AddSubgroup.subset_closure ⟨1, fun v => one_mem _, x, hx, rfl⟩
  | zero =>
    simp only [Pi.zero_apply, TensorProduct.tmul_zero, mul_zero]
    exact zero_mem _
  | add u w _ _ hu hw =>
    simp only [Pi.add_apply, TensorProduct.tmul_add, mul_add]
    exact add_mem hu hw
  | smul c u _ hu =>
    have := GlobalTheory.LatDual.smul_mem_lamHat V _ (idem_mul_loc_mem h (one_mem_intAf _) c) _ hu
    convert this using 2 with a
    rw [mul_mul_mul_comm, hee, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rfl

set_option maxHeartbeats 1000000 in

theorem exists_basis (V : HSp D) (he : e * e = e) (h : Comparison₂ P e) :
    ∃ B : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E),
      (∀ z, IntVec z → (fun a => finPart D e * B.mulVec z a) ∈ LamHat V) ∧
      ∀ y ∈ LamHat V, ∃ z, IntVec z ∧ (fun a => finPart D e * y a) = fun a => finPart D e * B.mulVec z a := by
  have hee : finPart D e * finPart D e = finPart D e := by rw [← RingHom.map_mul, he]
  obtain ⟨-, -, hfg, hspan, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  obtain ⟨b, hb, hc⟩ := exists_gens P (GlobalTheory.Member.latC V) hfg hspan
  refine ⟨Matrix.of fun a i => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] b i a, fun z hz => ?_, fun y hy => ?_⟩
  · have := sum_mem (S := LamHat V) (t := Finset.univ) fun i _ =>
      GlobalTheory.LatDual.smul_mem_lamHat V _ (hz i) _ (idem_mul_span_mem V he h (hb i))
    convert this using 1
    funext a
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  · rw [GlobalTheory.LatDual.lamHat_eq_hat] at hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨t, ht, x, hx, rfl⟩ := hy
      obtain ⟨c, hc⟩ := hc x hx
      refine ⟨fun i => finPart D e * (t ⊗ₜ[D.host.F] (c i : D.host.E)), fun i => idem_mul_loc_mem h ht _, ?_⟩
      funext a
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.mul_sum]
      rw [hc a, TensorProduct.tmul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_left_comm _ (finPart D e), ← mul_assoc, hee, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
        mul_comm (b i a)]
    | zero => exact ⟨0, fun _ => zero_mem _, by rw [Matrix.mulVec_zero]⟩
    | add u w _ _ hu hw =>
      obtain ⟨z, hz, hu⟩ := hu
      obtain ⟨z', hz', hw⟩ := hw
      refine ⟨z + z', fun i => add_mem (hz i) (hz' i), funext fun a => ?_⟩
      rw [Matrix.mulVec_add, Pi.add_apply, Pi.add_apply, mul_add, mul_add, congrFun hu a, congrFun hw a]
    | neg u _ hu =>
      obtain ⟨z, hz, hu⟩ := hu
      refine ⟨-z, fun i => neg_mem (hz i), funext fun a => ?_⟩
      rw [Matrix.mulVec_neg, Pi.neg_apply, Pi.neg_apply, mul_neg, mul_neg, congrFun hu a]

set_option maxHeartbeats 800000 in

theorem exists_component (he : e * e = e) (h : Comparison₂ P e) :
    ∃ (φ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E →+* P.adicCompletion D.host.E)
      (s : P.adicCompletion D.host.E → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E),
      (∀ t, φ (s t) = t) ∧ φ (finPart D e) = 1 ∧ (∀ x y, φ x = φ y → finPart D e * x = finPart D e * y) ∧
      (∀ x ∈ intAE D, φ x ∈ Formalism.UG.Ov D.host.E P) ∧ (∀ t ∈ Formalism.UG.Ov D.host.E P, s t ∈ intAE D) ∧
      ∀ x : D.host.E, φ (finPart D (incA D x)) = algebraMap D.host.E _ x := by
  classical
  obtain ⟨ι, i1, i2, -⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  have hee : finPart D e * finPart D e = finPart D e := by rw [← RingHom.map_mul, he]
  have ev : ∀ a b Q, ι (a * b) Q = ι a Q * ι b Q := fun a b Q => by rw [map_mul]; rfl
  have inc : ∀ (x : D.host.E) Q, ι (finPart D (incA D x)) Q = algebraMap D.host.E _ x := fun x Q =>
    congrArg (fun z : FiniteAdeleRing (𝓞 D.host.E) D.host.E => z Q) (i1 x)
  have one : ∀ Q, ι (finPart D e) Q ≠ 0 → ι (finPart D e) Q = 1 := fun Q h0 =>
    mul_left_cancel₀ h0 (by rw [← ev, hee, mul_one])
  have nint : ∀ x : 𝓞 D.host.E, x ≠ 0 → (x ∈ P.asIdeal ↔ ∃ Q, ι (finPart D e) Q ≠ 0 ∧ x ∈ Q.asIdeal) := by
    intro x hx
    rw [h x hx, i2, not_forall]
    refine exists_congr fun Q => ?_
    rw [RingHom.map_mul, ev, inc]
    by_cases h0 : ι (finPart D e) Q = 0
    · rw [h0, zero_mul, map_zero]
      exact iff_of_false (fun h => h zero_le_one) (fun h => h.1 rfl)
    · rw [one Q h0, one_mul]
      exact ((inv_mem_iff Q hx).not.trans not_not).trans (and_iff_right one_ne_zero).symm
  have h1 : ∀ Q, ι (finPart D e) Q ≠ 0 → Q = P := fun Q hQ => eq_of_le fun x hx => by
    by_cases hx0 : x = 0
    · rw [hx0]; exact zero_mem _
    · exact (nint x hx0).2 ⟨Q, hQ, hx⟩
  have h2 : ι (finPart D e) P = 1 := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
    obtain ⟨Q, hQ, -⟩ := (nint x hx0).1 hx
    obtain rfl := h1 Q hQ
    exact one _ hQ
  have s1 : ∀ t, singleV D.host.E P t P = t := fun t =>
    Pi.single_eq_same (M := fun w : HeightOneSpectrum (𝓞 D.host.E) => w.adicCompletion D.host.E) P t
  have s2 : ∀ t Q, Q ≠ P → singleV D.host.E P t Q = 0 := fun t Q hQ =>
    Pi.single_eq_of_ne (M := fun w : HeightOneSpectrum (𝓞 D.host.E) => w.adicCompletion D.host.E) hQ t
  refine ⟨(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.E P).toRingHom.comp ι.toRingHom, fun t => ι.symm (singleV D.host.E P t),
    fun t => ?_, h2, fun x y hxy => ι.injective (FiniteAdeleRing.ext _ fun Q => ?_), fun x hx => (i2 x).1 hx P,
    fun t ht => (i2 _).2 fun Q => ?_, fun x => inc x P⟩
  · show ι (ι.symm _) P = t
    rw [ι.apply_symm_apply, s1]
  · rw [ev, ev]
    by_cases h0 : ι (finPart D e) Q = 0
    · rw [h0, zero_mul, zero_mul]
    · obtain rfl := h1 Q h0
      have : ι x Q = ι y Q := hxy
      rw [this]
  · rw [ι.apply_symm_apply]
    by_cases hQ : Q = P
    · subst hQ
      rw [s1]; exact ht
    · rw [s2 t Q hQ, map_zero]; exact zero_le_one

theorem exists_divAt (V : HSp D) (he : e * e = e) (h : Comparison₂ P e) {ϖ : 𝓞 D.host.E} (h1 : ϖ ∈ P.asIdeal)
    (h2 : ϖ ∉ P.asIdeal ^ 2) (g : GA D V) :
    ∃ d : List ℤ, d.Pairwise (fun a b => b ≤ a) ∧ DivAt V e (ϖ : D.host.E) d g := by
  obtain ⟨φ, s, hs, hε, hφ, hO, hO', hinc⟩ := exists_component he h
  obtain ⟨B, b1, b2⟩ := exists_basis V he h
  have hee : finPart D e * finPart D e = finPart D e := by rw [← RingHom.map_mul, he]
  obtain ⟨C, c1, c2⟩ := (GlobalTheory.LatIntFacts.int_facts V).2.2 _ B hee fun y hy => (b2 y hy).imp fun _ h => h.2
  have mp : ∀ X Y : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E),
      finPart D e • (X * Y) = finPart D e • (1 : Matrix (Fin V.rank) (Fin V.rank) _) → X.map φ * Y.map φ = 1 := by
    intro X Y hXY
    rw [← Matrix.map_mul, ← Matrix.map_one φ (map_zero φ) (map_one φ)]
    refine Matrix.ext fun i j => ?_
    have := congrArg φ (congrFun (congrFun hXY i) j)
    rwa [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, map_mul, hε, one_mul,
      one_mul] at this
  let b : GL (Fin V.rank) (P.adicCompletion D.host.E) := ⟨B.map φ, C.map φ, mp _ _ c1, mp _ _ c2⟩
  let a : GL (Fin V.rank) (P.adicCompletion D.host.E) := Formalism.UG.bc φ (finHom V g)
  have hv : Formalism.UG.IsUnifV D.host.E P (algebraMap D.host.E _ (ϖ : D.host.E)) :=
    (P.valuedAdicCompletion_eq_valuation' (ϖ : D.host.E)).trans
      ((P.valuation_of_algebraMap ϖ).trans (GlobalTheory.LatIntFacts.intValuation_uniformiser P h1 h2))
  obtain ⟨d, hd, k₁, hk₁, k₂, hk₂, hk⟩ := Formalism.UG.Final.CartanDecomp D.host.E P V.rank _
    (Formalism.UG.P.cartan_unif_lt_one D.host.E P _ hv).le hv (b⁻¹ * a * b)
  refine ⟨List.ofFn d, List.pairwise_ofFn.2 fun i j hij => hd hij.le, (GlobalTheory.DivDual.divAt_iff V e _ _ g).2
    ⟨List.length_ofFn, dv_of_cartan φ s hs hε hφ hO hO' (B := B) b1 b2
      (Formalism.UG.P.cartan_entries_of_mem _ _ hk₁) (Formalism.UG.P.cartan_entries_of_mem _ _ (inv_mem hk₁))
      (Formalism.UG.P.cartan_entries_of_mem _ _ hk₂) (Formalism.UG.P.cartan_entries_of_mem _ _ (inv_mem hk₂)) ?_⟩⟩
  have e1 : (Matrix.diagonal fun i : Fin V.rank =>
      φ (finPart D (incA D ((ϖ : D.host.E) ^ ((List.ofFn d).getD i.1 0))))) =
      Formalism.UG.diagPow D.host.E P (algebraMap D.host.E _ (ϖ : D.host.E)) d := by
    unfold Formalism.UG.diagPow
    congr 1
    funext i
    rw [hinc, map_zpow₀]
    simp
  rw [e1, ← hk]
  show a.1 * b.1 = b.1 * _
  rw [← Units.val_mul, ← Units.val_mul]
  congr 1
  group

theorem divAt_one (V : HSp D) (he : e * e = e) (h : Comparison₂ P e) (ϖ : D.host.E) :
    DivAt V e ϖ (List.replicate V.rank 0) 1 := by
  obtain ⟨B, b1, b2⟩ := exists_basis V he h
  have hee : finPart D e * finPart D e = finPart D e := by rw [← RingHom.map_mul, he]
  have e1 : ∀ z : Fin V.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E,
      (fun i : Fin V.rank => finPart D (incA D (ϖ ^ ((List.replicate V.rank (0 : ℤ)).getD i.1 0))) * z i) = z :=
    fun z => funext fun i => by
      rw [List.getD_replicate _ i.2, zpow_zero, map_one, map_one, one_mul]
  have e2 : finMat D.sp.cm.sig V.gram (1 : GA D V) = 1 := GlobalTheory.SplitPlace.fm_one V
  refine ⟨List.length_replicate, B, b1, b2, fun y hy => ?_, fun z hz => ⟨_, b1 z hz, ?_⟩⟩
  · simp only [e1, e2, Matrix.one_mulVec]
    exact b2 y hy
  · simp only [e1, e2, Matrix.one_mulVec, ← mul_assoc, hee]

end Divisors

section Labels

open Formalism.L2.NTheta GlobalTheory.IdemSupport

variable {D : D7} {V : HSp D} {P : HeightOneSpectrum (𝓞 D.host.E)} {e f : Formalism.L2.Theta.AE D}

theorem exists_real_unif (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E)) :
    ∃ x : 𝓞 D.host.F, ∃ y : 𝓞 D.host.E, (y : D.host.E) = algebraMap D.host.F D.host.E (x : D.host.F) ∧
      y ∈ P.asIdeal ∧ y ∉ P.asIdeal ^ 2 := by
  have hu : Algebra.Unramified (𝓞 D.host.F) (𝓞 D.host.E) := by
    haveI := D.host.isCMField_hostE
    exact GlobalTheory.PlaceComp.unramified (E := D.host.E) D.sp.cm
  haveI := P.isPrime
  haveI : Algebra.IsUnramifiedAt (𝓞 D.host.F) P.asIdeal :=
    Algebra.unramified_iff_forall.1 hu ⟨P.asIdeal, P.isPrime⟩
  have hle : (P.asIdeal.under (𝓞 D.host.F)).map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) ≤ P.asIdeal :=
    Ideal.map_comap_le
  have h1 : Ideal.ramificationIdx' (P.asIdeal.under (𝓞 D.host.F)) P.asIdeal = 1 := by
    letI := Localization.AtPrime.algebraOfLiesOver (P.asIdeal.under (𝓞 D.host.F)) P.asIdeal
    exact (Ideal.IsDedekindDomain.ramificationIdx'_eq_one_iff P.ne_bot hle).2
      ((Algebra.isUnramifiedAt_iff_map_eq (𝓞 D.host.F) (P.asIdeal.under (𝓞 D.host.F)) P.asIdeal).1 ‹_›).2
  have h2 : ¬ (P.asIdeal.under (𝓞 D.host.F)).map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) ≤ P.asIdeal ^ 2 :=
    fun h => (Ideal.ramificationIdx'_ne_one_iff hle).2 h h1
  rw [Ideal.map_le_iff_le_comap, SetLike.not_le_iff_exists] at h2
  obtain ⟨x, hx, hx2⟩ := h2
  exact ⟨x, algebraMap _ _ x, rfl, hx, hx2⟩

noncomputable abbrev stabG (V : HSp D) : Subgroup (GA D V) :=
  GlobalTheory.AdelicU.levelOff D.sp.cm.sig V.gram (GlobalTheory.AdelicU.frameLat V) ∅

theorem mem_stabG (k : GA D V) : k ∈ stabG V ↔ k ∈ KsphC V ∅ := by
  rw [GlobalTheory.AdelicU.KsphC_eq]; rfl

theorem hyp_eq (h : IsPrimeIdem P e f) : hyp V P = {k | k ∈ KsphC V ∅ ∧ SuppF V f k} := by
  refine Set.ext fun k => and_congr_right fun _ => ⟨?_, fun hk => ⟨e, f, h, hk⟩⟩
  rintro ⟨e', f', h', hk⟩
  obtain ⟨-, rfl⟩ := ((supported_group_and_prime_idempotents V).2.2.1 P e f h).2.2.2.1 e' f' h'
  exact hk

theorem exists_hyp (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) :
    ∃ K : Subgroup (GA D V), hyp V P = K := by
  obtain ⟨e, f, h⟩ := (supported_group_and_prime_idempotents V).2.1 P
  have h0 := (supported_group_and_prime_idempotents V).2.2.1 P e f h
  obtain ⟨L, hL⟩ := ((supported_group_and_prime_idempotents V).1 f h0.1 h0.2.1).1
  exact ⟨stabG V ⊓ L, (hyp_eq h).trans (Set.ext fun k => and_congr (mem_stabG k).symm (hL k).symm)⟩

variable {K : Subgroup (GA D V)} {ϖ : 𝓞 D.host.E} {d : List ℤ} {g : GA D V}

theorem isLab_of_divAt (h : IsPrimeIdem P e f) (h1 : ϖ ∈ P.asIdeal) (h2 : ϖ ∉ P.asIdeal ^ 2)
    (hd : d.Pairwise fun a b => b ≤ a) (hg : SuppF V f g) (hD : DivAt V e (ϖ : D.host.E) d g) : IsLab V P d := by
  obtain ⟨R, r1, r2⟩ : ∃ R : Finset (GA D V), (∀ γ ∈ R, SuppF V f γ) ∧
      IsCosetRep V {k | k ∈ KsphC V ∅ ∧ SuppF V f k} g R := by
    rcases id h with ⟨hs, rfl⟩ | ⟨rfl, -⟩
    · exact (GlobalTheory.SplitPlace.split_local V P e hs).2.1 g hg
    · exact (GlobalTheory.InertDoubleCoset.inert_double_cosets V P f h (exists_real_unif D P) g hg).2.1
  exact ⟨R, e, f, ϖ, g, fun v hv => absurd hv (Finset.notMem_empty v), h, h1, h2, hd, fun _ _ => Iff.rfl,
    fun _ _ _ => rfl, hg, hD, r1, r2⟩

theorem reps_of_sphOp (hK : hyp V P = K) (h : IsPrimeIdem P e f) (h1 : ϖ ∈ P.asIdeal) (h2 : ϖ ∉ P.asIdeal ^ 2)
    (hg : SuppF V f g) (hD : DivAt V e (ϖ : D.host.E) d g) {R : Finset (GA D V)} (hR : SphOp V P d R) :
    Reps K g R := by
  obtain ⟨e', f', ϖ', α, -, h', h1', h2', hd, -, -, hα, hD', -, hc⟩ := hR
  obtain ⟨rfl, rfl⟩ := ((supported_group_and_prime_idempotents V).2.2.1 P e f h).2.2.2.1 e' f' h'
  have hK' := (hyp_eq h).symm.trans hK
  rw [hK'] at hc
  obtain ⟨a, ha, b, hb, rfl⟩ : ∃ a ∈ {k | k ∈ KsphC V ∅ ∧ SuppF V f' k},
      ∃ b ∈ {k | k ∈ KsphC V ∅ ∧ SuppF V f' k}, α = a * g * b := by
    rcases id h with ⟨hs, rfl⟩ | ⟨rfl, -⟩
    · exact GlobalTheory.SplitLabel.split_label V P e' ϖ ϖ' d g α hs h1 h2 h1' h2' hg hα hD hD'
    · obtain ⟨a, b, ha, ha', hb, hb', e⟩ :=
        (GlobalTheory.InertDoubleCoset.inert_double_cosets V P f' h (exists_real_unif D P) g hg).2.2 ϖ ϖ' d α h1 h2 h1' h2'
          hd hα hD hD'
      exact ⟨a, ⟨ha, ha'⟩, b, ⟨hb, hb'⟩, e⟩
  rw [hK'] at ha hb
  exact Reps.of_dc ha hb ⟨fun γ hγ => (hc.1 γ hγ).2, hc.2⟩

theorem sphOp_rep (h : IsLab V P d) : SphOp V P d (rep V P d) := by
  rw [Hk3.rep, dif_pos h]
  exact h.choose_spec

theorem exists_reps (hK : hyp V P = K) {R : Finset (GA D V)} (hR : SphOp V P d R) :
    ∃ g, Reps K g R ∧ Reps K g (rep V P d) := by
  obtain ⟨e, f, ϖ, α, -, h, h1, h2, -, -, -, hα, hD, -⟩ := id hR
  exact ⟨α, reps_of_sphOp hK h h1 h2 hα hD hR, reps_of_sphOp hK h h1 h2 hα hD (sphOp_rep ⟨R, hR⟩)⟩

theorem dualLab_pairwise (h : d.Pairwise fun a b => b ≤ a) : (dualLab d).Pairwise fun a b => b ≤ a := by
  rw [dualLab, List.pairwise_reverse, List.pairwise_map]
  exact h.imp fun h => neg_le_neg h

theorem dualLab_dualLab (d : List ℤ) : dualLab (dualLab d) = d := by
  simp [dualLab]

theorem unif_ne_zero (h2 : ϖ ∉ P.asIdeal ^ 2) : (ϖ : D.host.E) ≠ 0 := fun h => h2 (by
  rw [show ϖ = 0 from RingOfIntegers.ext h]
  exact zero_mem _)

open GlobalTheory.HeckeDual in

theorem exists_dual {R : Finset (GA D V)} (hR : SphOp V P d R) :
    ∃ R', SphOp V P (dualLab d) R' ∧ R'.card = R.card := by
  obtain ⟨e, f, ϖ, α, hS, hef, hϖ, hϖ2, hd, hJ, hχ, hα, hdiv, hR, hrep⟩ := hR
  obtain ⟨he, v, hf⟩ := idem_of_isPrimeIdem hef
  obtain ⟨a, rfl⟩ := (GlobalTheory.HeckeDual.suppF_iff V hf α).1 hα
  obtain ⟨δ, hδ, hσδ⟩ := exists_skew D
  haveI := isLattice_frameLat V
  have hK : ∀ g, g ∈ {k | k ∈ KsphC V ∅ ∧ SuppF V f k} ↔
      ∃ k ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram (GlobalTheory.AdelicU.frameLat V) v,
        GlobalTheory.AdelicU.emb D.sp.cm.sig V.gram v k = g := fun g => by
    constructor
    · rintro ⟨h3, h2⟩
      obtain ⟨k, rfl⟩ := (GlobalTheory.HeckeDual.suppF_iff V hf g).1 h2
      rw [GlobalTheory.AdelicU.KsphC_eq] at h3
      have h4 := (GlobalTheory.AdelicU.mem_levelOff.1 h3).2.2 v (Finset.notMem_empty v)
      rw [GlobalTheory.AdelicU.proj_emb_self] at h4
      exact ⟨k, h4, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      refine ⟨?_, (GlobalTheory.HeckeDual.suppF_iff V hf _).2 ⟨k, rfl⟩⟩
      rw [GlobalTheory.AdelicU.KsphC_eq]
      exact GlobalTheory.AdelicU.emb_mem_levelOff (Finset.notMem_empty v) hk
  obtain ⟨R', h1, h2, h3⟩ := exists_rep_inv
    (modular_eq_one D.sp.cm.sig V.gram (fun x => star_star x) hδ hσδ
      ((GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm).2 V) v)
    (GlobalTheory.AdelicU.emb D.sp.cm.sig V.gram v) (GlobalTheory.AdelicU.emb_injective _ _ v) _
    (GlobalTheory.AdelicU.isOpen_stabLoc _ _ _ v) (GlobalTheory.AdelicU.isCompact_stabLoc _ _ _ v) _ hK a R
    (fun γ hγ => (hrep.1 γ hγ).2) hrep.2
  refine ⟨R', ⟨e, f, ϖ, _, hS, hef, hϖ, hϖ2, dualLab_pairwise hd, hJ, hχ,
    (GlobalTheory.HeckeDual.suppF_iff V hf _).2 (inv_mem ⟨a, rfl⟩),
    (GlobalTheory.DivDual.divAt_inv_and_mul V e _ d _ he (unif_ne_zero hϖ2) hdiv).1,
    fun γ hγ => (GlobalTheory.HeckeDual.suppF_iff V hf _).2 (h1 γ hγ).1, fun γ hγ => ⟨?_, (h1 γ hγ).2⟩, h2⟩, h3⟩
  obtain ⟨x, rfl⟩ := (h1 γ hγ).1
  exact GlobalTheory.AdelicU.mem_finPts.2 (GlobalTheory.AdelicU.projInf_emb _ _ v x)

theorem opOf_single {M : Type} [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (d : List ℤ) (u : M) :
    opOf π P (Finsupp.single d 1) u = ∑ γ ∈ rep V P d, π γ u := by
  rw [opOf, Finsupp.sum_single_index (by simp), one_smul, LinearMap.sum_apply]

end Labels

open GlobalTheory.IdemSupport in

theorem label_operators : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E), (∀ d R, SphOp V P d R → R.card = (rep V P d).card ∧ ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (u : M), (∀ k ∈ hyp V P, π k u = u) → ∑ γ ∈ R, π γ u = opOf π P (Finsupp.single d 1) u) ∧ (∀ c, ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (u : M), (∀ k ∈ hyp V P, π k u = u) → ∀ k ∈ hyp V P, π k (opOf π P c u) = opOf π P c u) ∧ (IsLab V P (List.replicate V.rank 0) ∧ ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (u : M), (∀ k ∈ hyp V P, π k u = u) → opOf π P (Finsupp.single (List.replicate V.rank 0) 1) u = u) ∧ (∀ d, (IsLab V P d ↔ IsLab V P (dualLab d)) ∧ (rep V P (dualLab d)).card = (rep V P d).card) ∧ ∀ e f g, IsPrimeIdem P e f → SuppF V f g → ∃ d, IsLab V P d ∧ (∀ γ ∈ rep V P d, ∃ k₁ ∈ hyp V P, ∃ k₂ ∈ hyp V P, γ = k₁ * g * k₂) ∧ ∀ γ ∈ rep V P (dualLab d), ∃ k₁ ∈ hyp V P, ∃ k₂ ∈ hyp V P, γ = k₁ * g⁻¹ * k₂ := by
  intro D V P
  obtain ⟨K, hK⟩ := exists_hyp V P
  obtain ⟨-, ϖ, -, h1, h2⟩ := exists_real_unif D P
  have fix : ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (u : M),
      (∀ k ∈ hyp V P, π k u = u) → ∀ x, ∀ l ∈ K, π (x * l) u = π x u := by
    intro M _ _ π u hu x l hl
    rw [map_mul, Module.End.mul_apply, hu l (hK ▸ hl)]
  have c1 : ∀ d R, SphOp V P d R → R.card = (rep V P d).card ∧ ∀ (M : Type) [AddCommGroup M] [Module ℂ M]
      (π : GA D V →* Module.End ℂ M) (u : M), (∀ k ∈ hyp V P, π k u = u) →
      ∑ γ ∈ R, π γ u = opOf π P (Finsupp.single d 1) u := by
    intro d R hR
    obtain ⟨g, r1, r2⟩ := exists_reps hK hR
    refine ⟨r1.card_eq r2, fun M _ _ π u hu => ?_⟩
    rw [opOf_single, ← r1.sum_eq r2 (one_mem K) (fun x => π x u) (fix M π u hu)]
    simp only [one_mul]
  have dual : ∀ d, IsLab V P d → IsLab V P (dualLab d) := fun d ⟨R, hR⟩ => (exists_dual hR).imp fun _ h => h.1
  refine ⟨c1, fun c M _ _ π u hu k hk => ?_, ?_, fun d => ?_, fun e f g h hg => ?_⟩
  · simp only [opOf, Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
    refine Finset.sum_congr rfl fun d _ => congrArg _ ?_
    by_cases hd : IsLab V P d
    · obtain ⟨g, r1, -⟩ := exists_reps hK (sphOp_rep hd)
      rw [← r1.sum_eq r1 (k := k) (by rwa [hK] at hk) (fun x => π x u) (fix M π u hu)]
      simp only [map_mul, Module.End.mul_apply]
    · simp only [Hk3.rep, dif_neg hd, Finset.sum_empty]
  · obtain ⟨e, f, h⟩ := (supported_group_and_prime_idempotents V).2.1 P
    have hD := divAt_one V (GlobalTheory.HeckeDual.idem_of_isPrimeIdem h).1 (tie_of_isPrimeIdem h) (ϖ : D.host.E)
    have hg : SuppF V f 1 := (one_mem (suppGroup V f) :)
    have hl := isLab_of_divAt h h1 h2 (by simp) hg hD
    refine ⟨hl, fun M _ _ π u hu => ?_⟩
    have r1 := reps_of_sphOp hK h h1 h2 hg hD (sphOp_rep hl)
    have r2 : Reps K 1 {1} := by
      refine ⟨fun γ hγ => ⟨1, one_mem _, 1, one_mem _, by simpa using hγ⟩, ?_⟩
      rintro _ ⟨a, ha, b, hb, rfl⟩
      exact ⟨1, ⟨Finset.mem_singleton_self _, by simpa using mul_mem ha hb⟩,
        fun γ hγ => Finset.mem_singleton.1 hγ.1⟩
    have := r1.sum_eq r2 (one_mem K) (fun x => π x u) (fix M π u hu)
    rw [opOf_single]
    simpa using this
  · have hi : IsLab V P d ↔ IsLab V P (dualLab d) := ⟨dual d, fun h => dualLab_dualLab d ▸ dual _ h⟩
    refine ⟨hi, ?_⟩
    by_cases hd : IsLab V P d
    · obtain ⟨R', r1, r2⟩ := exists_dual (sphOp_rep hd)
      rw [← (c1 _ _ r1).1, r2]
    · rw [Hk3.rep, Hk3.rep, dif_neg hd, dif_neg (_root_.mt hi.2 hd)]
  · have he := (GlobalTheory.HeckeDual.idem_of_isPrimeIdem h).1
    obtain ⟨d, hd, hD⟩ := exists_divAt V he (tie_of_isPrimeIdem h) h1 h2 g
    have hl := isLab_of_divAt h h1 h2 hd hg hD
    have h0 := (supported_group_and_prime_idempotents V).2.2.1 P e f h
    obtain ⟨L, hL⟩ := ((supported_group_and_prime_idempotents V).1 f h0.1 h0.2.1).1
    rw [hK]
    exact ⟨d, hl, (reps_of_sphOp hK h h1 h2 hg hD (sphOp_rep hl)).1,
      (reps_of_sphOp hK h h1 h2 ((hL _).1 (inv_mem ((hL _).2 hg)))
        (GlobalTheory.DivDual.divAt_inv_and_mul V e _ d g he (unif_ne_zero h2) hD).1 (sphOp_rep (dual d hl))).1⟩

end GlobalTheory.SphLabelOps
