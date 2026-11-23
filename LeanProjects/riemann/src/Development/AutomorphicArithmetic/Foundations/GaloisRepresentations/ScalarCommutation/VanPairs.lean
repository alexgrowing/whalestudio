import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.TypeSlice
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.OrbZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeCentralizerComm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraMapQrOneBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowMemConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatIntOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralityFromPadicNormBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelWeilOrbitalMeasure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenvalueNormBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianOneByOneIsScalar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelWeilMeasureOfCongruentForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BetaTwistedInvolutionEqComplexConjOfMarked
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BetaTwistedInvolutionEqComplexConjOfMarkedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedPowersPadicIntegral
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.BoundQ
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralizerElementPadicBounded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralizerScalarPadicBounded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugatePlaceLiesOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KottwitzPointCountOneClassCommensurableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitarySimilitudeIntegralSubgroupCommensuratedFrStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactOpenLevelConjCommensurableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudePairAdelicProdUnramifiedEmbeddingInjecStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapCentralizerRegularTwistedCentraliserStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudePairRegularImageAtPStatement

set_option autoImplicit false

noncomputable section

open MeasureTheory Matrix NumberField Polynomial GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.StabFin UpperTheory.Gal.LocalSmoothExtension
open Formalism.UG (Hecke)
open scoped TensorProduct Classical

namespace UpperTheory.Gal.Spc

private theorem units_field {M L : Type} [CommRing M] [Algebra ℚ M] [Module.Finite ℚ M] [Field L]
    (π : M →+* L) (hπ : Function.Surjective π) (c : M →ₐ[ℚ] M)
    (hc : ∀ (τ : M →+* ℂ) (a : M), τ (c a) = (starRingEnd ℂ) (τ a)) :
    ∃ T : Set Lˣ, T.Finite ∧ ∀ x : Mˣ, x ∈ GlobalTheory.LKTorus.simT ℚ c →
      (∀ (q : ℕ) [Fact q.Prime] (τ : M →+* PadicAlgCl q), ‖τ (x : M)‖ ≤ 1) →
      (∀ (q : ℕ) [Fact q.Prime] (τ : M →+* PadicAlgCl q), ‖τ ((x⁻¹ : Mˣ) : M)‖ ≤ 1) →
      Units.map (π : M →* L) x ∈ T := by
  haveI : CharZero L := (RingHom.charZero_iff (π.comp (algebraMap ℚ M)).injective).1 inferInstance
  haveI : Module.Finite ℚ L := Module.Finite.of_surjective π.toRatAlgHom.toLinearMap hπ
  haveI : NumberField L := ⟨⟩
  let τ₀ : L →ₐ[ℚ] ℂ := IsAlgClosed.lift
  have hker : ∀ a, π a = 0 → π (c a) = 0 := by
    intro a ha
    apply (τ₀ : L →+* ℂ).injective
    have h := hc ((τ₀ : L →+* ℂ).comp π) a
    simp only [RingHom.comp_apply] at h
    rw [ha, map_zero, map_zero] at h
    simpa using h
  let s := Function.surjInv hπ
  have hs : ∀ y, π (s y) = y := Function.surjInv_eq hπ
  have hcomp : ∀ a, π (c (s (π a))) = π (c a) := by
    intro a
    have h := hker (s (π a) - a) (by rw [map_sub, hs, sub_self])
    rw [map_sub, map_sub, sub_eq_zero] at h
    exact h
  let cL : L →ₐ[ℚ] L :=
    { toFun := fun y => π (c (s y))
      map_one' := by
        have := hcomp 1
        simpa using this
      map_mul' := fun y y' => by
        obtain ⟨a, rfl⟩ := hπ y
        obtain ⟨b, rfl⟩ := hπ y'
        rw [← map_mul, hcomp, hcomp, hcomp, map_mul, map_mul]
      map_zero' := by
        have := hcomp 0
        simpa using this
      map_add' := fun y y' => by
        obtain ⟨a, rfl⟩ := hπ y
        obtain ⟨b, rfl⟩ := hπ y'
        rw [← map_add, hcomp, hcomp, hcomp, map_add, map_add]
      commutes' := fun r => by
        have := hcomp (algebraMap ℚ M r)
        simpa using this }
  have hcL : ∀ a, cL (π a) = π (c a) := hcomp
  have hcLc : ∀ (τ : L →+* ℂ) (y : L), τ (cL y) = (starRingEnd ℂ) (τ y) := by
    intro τ y
    obtain ⟨a, rfl⟩ := hπ y
    rw [hcL]
    exact hc (τ.comp π) a
  refine ⟨_, GlobalTheory.LKTorus.simT_integral_finite L cL hcLc, fun x hx h1 h2 => ?_⟩
  obtain ⟨t, ht⟩ := hx
  refine ⟨⟨t, ?_⟩, ?_, ?_⟩
  · show π (x : M) * cL (π (x : M)) = _
    rw [hcL, ← map_mul, ht]
    simp
  · exact GlobalTheory.isIntegral_of_forall_padicAlgCl_norm_le_one L _ fun q _ τ => h1 q (τ.comp π)
  · have e : ((Units.map (π : M →* L) x)⁻¹ : Lˣ) = Units.map (π : M →* L) x⁻¹ := (map_inv _ _).symm
    rw [e]
    exact GlobalTheory.isIntegral_of_forall_padicAlgCl_norm_le_one L _ fun q _ τ => h2 q (τ.comp π)

private theorem units_finite {M : Type} [CommRing M] [Algebra ℚ M] [Module.Finite ℚ M] [IsReduced M]
    (c : M →ₐ[ℚ] M) (hc : ∀ (τ : M →+* ℂ) (a : M), τ (c a) = (starRingEnd ℂ) (τ a)) :
    {x : Mˣ | x ∈ GlobalTheory.LKTorus.simT ℚ c ∧ (∀ (q : ℕ) [Fact q.Prime] (τ : M →+* PadicAlgCl q), ‖τ (x : M)‖ ≤ 1) ∧
      ∀ (q : ℕ) [Fact q.Prime] (τ : M →+* PadicAlgCl q), ‖τ ((x⁻¹ : Mˣ) : M)‖ ≤ 1}.Finite := by
  haveI : IsArtinianRing M := IsArtinianRing.of_finite ℚ M
  haveI : Finite (MaximalSpectrum M) := inferInstance
  have key : ∀ m : MaximalSpectrum M, ∃ T : Set (M ⧸ m.asIdeal)ˣ, T.Finite ∧ ∀ x : Mˣ, x ∈ GlobalTheory.LKTorus.simT ℚ c →
      (∀ (q : ℕ) [Fact q.Prime] (τ : M →+* PadicAlgCl q), ‖τ (x : M)‖ ≤ 1) →
      (∀ (q : ℕ) [Fact q.Prime] (τ : M →+* PadicAlgCl q), ‖τ ((x⁻¹ : Mˣ) : M)‖ ≤ 1) →
      Units.map ((Ideal.Quotient.mk m.asIdeal : M →+* M ⧸ m.asIdeal) : M →* M ⧸ m.asIdeal) x ∈ T := by
    intro m
    haveI := m.isMaximal
    letI : Field (M ⧸ m.asIdeal) := Ideal.Quotient.field m.asIdeal
    exact units_field (Ideal.Quotient.mk m.asIdeal) Ideal.Quotient.mk_surjective c hc
  choose T hT hxT using key
  let φ : Mˣ → ∀ m : MaximalSpectrum M, (M ⧸ m.asIdeal)ˣ := fun x m =>
    Units.map ((Ideal.Quotient.mk m.asIdeal : M →+* M ⧸ m.asIdeal) : M →* M ⧸ m.asIdeal) x
  have hφ : Function.Injective φ := by
    intro x y h
    apply Units.ext
    rw [← sub_eq_zero]
    have hmem : ((x : M) - y) ∈ (⊥ : Ideal M).jacobson := by
      rw [Ideal.jacobson, Ideal.mem_sInf]
      rintro J ⟨-, hJ⟩
      have h1 := congrArg Units.val (congrFun h ⟨J, hJ⟩)
      exact Ideal.Quotient.eq.1 h1
    obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := M)
    have h2 : ((x : M) - y) ^ n ∈ ((⊥ : Ideal M).jacobson) ^ n := Ideal.pow_mem_pow hmem n
    rw [hn] at h2
    exact IsReduced.eq_zero _ ⟨n, by simpa using h2⟩
  refine ((Set.Finite.pi' hT).preimage hφ.injOn).subset ?_
  rintro x ⟨h0, h1, h2⟩
  exact fun m => hxT m x h0 h1 h2

private theorem fm_reduced {p : ℕ} [Fact p.Prime] {G : HTGroup p} (P : Pair G) : IsReduced (FM P) := by
  refine ⟨fun a ha => ?_⟩
  obtain ⟨n, hn⟩ := ha
  obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective a
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · have h1 : (1 : FM P) = 0 := by simpa using hn
    rw [← mul_one (AdjoinRoot.mk P.pol f), h1, mul_zero]
  rw [← map_pow, AdjoinRoot.mk_eq_zero] at hn
  have hsq : Squarefree P.pol := P.reg.2.squarefree
  exact AdjoinRoot.mk_eq_zero.2 ((hsq.dvd_pow_iff_dvd hpos.ne').1 hn)

private theorem fm_finite {p : ℕ} [Fact p.Prime] {G : HTGroup p} (P : Pair G) : Module.Finite ℚ (FM P) := by
  haveI : Module.Finite G.F (FM P) :=
    (AdjoinRoot.powerBasis (minpoly.ne_zero (IsIntegral.of_finite G.F (P.γ : G.C)))).finite
  exact Module.Finite.trans G.F (FM P)

private theorem stab_finite {p : ℕ} [Fact p.Prime] (G : HTGroup p) (ha : G.a = 1) (P : Pair G) (μ : ℂ) (hM : P.Mark μ)
    (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) (r : ℕ) (z : Gr G r) (L : G.Level)
    (K : Subgroup (Gr G r)) (hr : 0 < r) (hK : Subgroup.Commensurable K (KHT p G.m G.n r G.Fw))
    (y : G.GAf × Gr G r) : Finite (stab (P.toAf x t hx) (P.toQr r z) L.K.toSubgroup K y) := by
  set S := stab (P.toAf x t hx) (P.toQr r z) L.K.toSubgroup K y with hSdef
  have hmem : ∀ w : P.cent, w ∈ S ↔ P.toAf x t hx w ∈ L.K.toSubgroup.map (MulAut.conj y.1).toMonoidHom ∧
      P.toQr r z w ∈ K.map (MulAut.conj y.2).toMonoidHom := fun w => Iff.rfl
  have hpre : ∀ w : P.cent, ∃ a : FM P, jM P a = ((w : G.Cˣ × ℚˣ).1 : G.C) := fun w =>
    exists_jM P _ (by have := w.2.1; exact congrArg Units.val this)
  choose A hA using hpre
  have hApow : ∀ (w : P.cent) (k : ℕ), A (w ^ k) = A w ^ k := fun w k => jM_injective P (by
    rw [hA, map_pow, hA]; rfl)
  have hAinv : ∀ w : P.cent, A w * A w⁻¹ = 1 := fun w => jM_injective P (by
    rw [map_mul, hA, hA, map_one]
    show ((w : G.Cˣ × ℚˣ).1 : G.C) * (((w : G.Cˣ × ℚˣ).1⁻¹ : G.Cˣ) : G.C) = 1
    exact Units.mul_inv _)
  have hbd : ∀ w ∈ S, ∀ (q : ℕ) [Fact q.Prime] (τ : FM P →+* PadicAlgCl q), ‖τ (A w)‖ ≤ 1 := by
    intro w hw q _ τ
    by_cases hq : q = p
    · subst hq
      by_cases hov : LiesOver G.Kq G.u (τ.comp (algebraMap G.F (FM P)))
      · exact GlobalTheory.T.centralizer_element_padic_bounded q G P r z K y.2 hr hK w ((hmem w).1 hw).2 _ (hA w) τ hov
      · have hov' := GlobalTheory.T.conjugate_place_lies_over q G _ hov
        set τ' := τ.comp (iM P).toRingHom
        have hτ' : LiesOver G.Kq G.u (τ'.comp (algebraMap G.F (FM P))) := by
          intro k
          have := hov' k
          simp only [RingHom.comp_apply] at this ⊢
          rw [← this]
          show τ (iM P (algebraMap G.F (FM P) k)) = _
          rw [iM_algF]; rfl
        have hwi : w⁻¹ ∈ S := S.inv_mem hw
        have h1 := GlobalTheory.T.centralizer_element_padic_bounded q G P r z K y.2 hr hK w⁻¹ ((hmem _).1 hwi).2 _ (hA _) τ' hτ'
        have h2 := GlobalTheory.T.centralizer_scalar_padic_bounded q G P r z K y.2 hr hK w ((hmem w).1 hw).2
        have e : A w = iM P (algebraMap ℚ (FM P) (((w : G.Cˣ × ℚˣ).2 : ℚ)) * A w⁻¹) := by
          have e0 : algebraMap ℚ (FM P) (((w : G.Cˣ × ℚˣ).2 : ℚ)) * A w⁻¹ = iM P (A w) := by
            rw [← mul_iM_of_cent P w (A w) (hA w), mul_comm (A w), mul_assoc, hAinv, mul_one]
          rw [e0, iM_iM]
        have e2 : τ (A w) = τ' (algebraMap ℚ (FM P) (((w : G.Cˣ × ℚˣ).2 : ℚ))) * τ' (A w⁻¹) := by
          rw [e, ← map_mul]; rfl
        rw [e2, norm_mul, RingHom.map_rat_algebraMap, eq_ratCast,
          ← map_ratCast (algebraMap ℚ_[q] (PadicAlgCl q)), PadicAlgCl.norm_extends]
        exact mul_le_one₀ h2 (norm_nonneg _) h1
    · obtain ⟨B, hB⟩ := UpperTheory.Gal.Spc.boundQ p G P x t hx L y.1 q hq
      let f : FM P →ₗ[ℚ] (Fin (Module.finrank ℚ G.C) → ℚ) :=
        (Finsupp.linearEquivFunOnFinite ℚ ℚ _).toLinearMap ∘ₗ (Module.finBasis ℚ G.C).repr.toLinearMap ∘ₗ
          ((jM P).restrictScalars ℚ).toLinearMap
      have hf : Function.Injective f := by
        intro a b hab
        apply jM_injective P
        simpa [f] using hab
      refine GlobalTheory.T.bounded_powers_padic_integral (FM P) q _ f hf (A w) B (fun k i => ?_) τ
      rw [← hApow]
      have := hB (w ^ k) (S.pow_mem hw k).1 i
      simpa [f, hA] using this
  haveI := fm_reduced P
  haveI := fm_finite P
  have hfin := units_finite (iM P) (GlobalTheory.T.betaTwistedInvolution_eq_complexConj_of_marked p G P μ ha hM)
  let U : S → (FM P)ˣ := fun w => ⟨A w, A (w : P.cent)⁻¹, hAinv w, by rw [mul_comm]; exact hAinv w⟩
  have hU : ∀ w : S, U w ∈ {x : (FM P)ˣ | x ∈ GlobalTheory.LKTorus.simT ℚ (iM P) ∧
      (∀ (q : ℕ) [Fact q.Prime] (τ : FM P →+* PadicAlgCl q), ‖τ (x : FM P)‖ ≤ 1) ∧
      ∀ (q : ℕ) [Fact q.Prime] (τ : FM P →+* PadicAlgCl q), ‖τ ((x⁻¹ : (FM P)ˣ) : FM P)‖ ≤ 1} := by
    intro w
    refine ⟨⟨(w : P.cent).1.2, ?_⟩, fun q _ τ => hbd w w.2 q τ, fun q _ τ => hbd _ (S.inv_mem w.2) q τ⟩
    exact mul_iM_of_cent P w (A w) (hA w)
  have hUinj : Function.Injective U := by
    intro w w' h
    have h1 : A w = A w' := congrArg Units.val h
    have hu : ((w : P.cent) : G.Cˣ × ℚˣ).1 = ((w' : P.cent) : G.Cˣ × ℚˣ).1 :=
      Units.ext (by rw [← hA, ← hA, h1])
    have hs : ((w : P.cent) : G.Cˣ × ℚˣ).2 = ((w' : P.cent) : G.Cˣ × ℚˣ).2 := by
      have e1 := (w : P.cent).2.2
      have e2 := (w' : P.cent).2.2
      rw [hu, e2] at e1
      have e3 : algebraMap ℚ G.C (((w' : P.cent) : G.Cˣ × ℚˣ).2 : ℚ) = algebraMap ℚ G.C (((w : P.cent) : G.Cˣ × ℚˣ).2 : ℚ) :=
        (Units.mul_left_inj P.β).1 e1
      exact Units.ext ((algebraMap ℚ G.C).injective e3).symm
    exact Subtype.ext (Subtype.ext (Prod.ext hu hs))
  haveI := hfin.to_subtype
  exact Finite.of_injective (fun w => (⟨U w, hU w⟩ : {x : (FM P)ˣ | x ∈ GlobalTheory.LKTorus.simT ℚ (iM P) ∧
      (∀ (q : ℕ) [Fact q.Prime] (τ : FM P →+* PadicAlgCl q), ‖τ (x : FM P)‖ ≤ 1) ∧
      ∀ (q : ℕ) [Fact q.Prime] (τ : FM P →+* PadicAlgCl q), ‖τ ((x⁻¹ : (FM P)ˣ) : FM P)‖ ≤ 1}))
    (fun w w' h => hUinj (congrArg Subtype.val h))

private theorem pointSum_zero {Γ G₁ G₂ : Type} [Group Γ] [Group G₁] [Group G₂] (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂)
    (θ : G₂ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (γ : G₁) (δ : G₂) (f₁ : G₁ → ℂ) (φ : G₂ → ℂ)
    (hK₁ : ∀ g : G₁, (K₁.map (MulAut.conj g).toMonoidHom).Commensurable K₁)
    (hK₂ : ∀ g : G₂, (K₂.map (MulAut.conj g).toMonoidHom).Commensurable K₂) (hθ : K₂.map θ ≤ K₂)
    (hf₁ : ∀ k ∈ K₁, ∀ x, f₁ (k⁻¹ * x * k) = f₁ x) (hφ : ∀ k ∈ K₂, ∀ x, φ (k⁻¹ * x * θ k) = φ x)
    (hc₁ : ∀ g : Γ, ι₁ g * γ = γ * ι₁ g) (hc₂ : ∀ g : Γ, ι₂ g * δ = δ * θ (ι₂ g))
    (hι : Function.Injective (ι₁.prod ι₂)) (hstab : ∀ x : G₁ × G₂, Finite (stab ι₁ ι₂ K₁ K₂ x))
    (h0 : orbK (MonoidHom.id G₁) K₁ γ f₁ = 0) : pointSum ι₁ ι₂ θ K₁ K₂ γ δ f₁ φ = 0 := by
  by_cases hs : {q : DoubleCoset.Quotient ((ι₁.prod ι₂).range : Set (G₁ × G₂))
      ((K₁.prod K₂ : Subgroup (G₁ × G₂)) : Set (G₁ × G₂)) |
      f₁ ((Quotient.out q).1⁻¹ * γ * (Quotient.out q).1) *
        φ ((Quotient.out q).2⁻¹ * δ * θ (Quotient.out q).2) ≠ 0}.Finite
  · rw [GlobalTheory.T.kottwitz_pointCount_one_class_commensurable ι₁ ι₂ θ K₁ K₂ γ δ f₁ φ hK₁ hK₂ hθ hf₁ hφ hc₁ hc₂ hι hstab hs]
    unfold pointSide
    rw [h0]
    simp
  · unfold pointSum
    refine finsum_of_infinite_support fun hfin => hs (hfin.subset fun q hq => ?_)
    haveI := hstab (Quotient.out q)
    exact mul_ne_zero (inv_ne_zero (Nat.cast_ne_zero.2 Nat.card_pos.ne')) hq

private theorem termAt_zero {p : ℕ} [Fact p.Prime] (G : HTGroup p) (ha : G.a = 1) (Lv : G.Level) (Q : Pair G) (μ : ℂ)
    (hM : Q.Mark μ) (f : G.GAf → ℂ) (hf : f ∈ Hecke ℂ Lv.K.toSubgroup) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) Q.β x t) (δ z : Gr G 1) (hn : IsNrm G 1 Q.atP δ z)
    (h0 : orbK (MonoidHom.id G.GAf) Lv.K.toSubgroup (Q.toAf x t hx Q.self) f = 0) :
    Q.termAt Lv.K.toSubgroup f 1 (Kp G) (oneP G) x t hx δ z = 0 := by
  have hreg := GlobalTheory.T.similitudePair_regular_image_at_p p G Q
  have hB := GlobalTheory.T.map_centralizer_regular_twistedCentraliser p G 1 Q.atP δ z one_pos hreg.2.1 hn
  have hK184 := GlobalTheory.T.unitarySimilitudeIntegralSubgroup_commensurated_frobenius p G 1 one_pos
  have hc1 : ∀ g : Q.cent, Q.toAf x t hx g * Q.toAf x t hx Q.self = Q.toAf x t hx Q.self * Q.toAf x t hx g := by
    intro g
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    refine Prod.ext ?_ (mul_comm _ _)
    exact g.2.1
  have hc2 : ∀ g : Q.cent, Q.toQr 1 z g * δ = δ * sigG G 1 (Q.toQr 1 z g) := by
    intro g
    have hm : carry G 1 z (locC G g.1) ∈ GlobalTheory.BCT.twCent (sigG G 1) δ :=
      hB ▸ Subgroup.mem_map_of_mem _ (hreg.2.2 g)
    exact hm
  have hbi : Formalism.UG.IsBiInv Lv.K.toSubgroup f := hf.1
  have hφ : ∀ k ∈ Kp G, ∀ y, oneP G (k⁻¹ * y * sigG G 1 k) = oneP G y := by
    intro k hk y
    have hk' : sigG G 1 k ∈ Kp G := hK184.2.2 (Subgroup.mem_map_of_mem _ hk)
    have hiff : k⁻¹ * y * sigG G 1 k ∈ Kp G ↔ y ∈ Kp G := by
      rw [(Kp G).mul_mem_cancel_right hk', (Kp G).mul_mem_cancel_left ((Kp G).inv_mem hk)]
    unfold oneP
    by_cases hw : y ∈ Kp G
    · rw [Set.indicator_of_mem (show _ ∈ (Kp G : Set (Gr G 1)) from hiff.2 hw),
        Set.indicator_of_mem (show _ ∈ (Kp G : Set (Gr G 1)) from hw)]
      rfl
    · rw [Set.indicator_of_notMem (show _ ∉ (Kp G : Set (Gr G 1)) from fun h => hw (hiff.1 h)),
        Set.indicator_of_notMem (show _ ∉ (Kp G : Set (Gr G 1)) from hw)]
  exact pointSum_zero _ _ _ _ _ _ _ _ _ (GlobalTheory.T.compactOpenLevel_conj_commensurable p G Lv) hK184.1 hK184.2.2
    (fun k hk y => hbi ⟨k⁻¹, Subgroup.inv_mem _ hk⟩ ⟨k, hk⟩ _) hφ hc1 hc2 (GlobalTheory.T.similitudePair_adelicProdUnramifiedEmbedding_injective p G Q x t hx 1 z)
    (stab_finite G ha Q μ hM x t hx 1 z Lv (Kp G) one_pos (Subgroup.Commensurable.refl _)) h0

private theorem charpoly_at_self {p : ℕ} [Fact p.Prime] {G : HTGroup p} {k : Type} [Field k] [Algebra G.F k] (R : Pl G k)
    (Q : Pair G) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) Q.β x t) :
    (R.at (Q.toAf x t hx Q.self)).charpoly = (R.ι (Q.γ : G.C)).charpoly := by
  have h := Matrix.charpoly_units_conj (Units.map (R.κ : AfP p ⊗[ℚ] G.C →* Matrix (Fin G.n) (Fin G.n) k) x)
    (R.ι (Q.γ : G.C))
  rw [← h, ← R.κ_ι]
  have e : R.at (Q.toAf x t hx Q.self) =
      R.κ (x : AfP p ⊗[ℚ] G.C) * R.κ (1 ⊗ₜ (Q.γ : G.C)) * R.κ ((x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) := by
    rw [← map_mul, ← map_mul]
    rfl
  rw [e, ← Matrix.coe_units_inv]
  rfl

end UpperTheory.Gal.Spc

open UpperTheory.Gal.Spc in
theorem UpperTheory.Gal.Spc.vanPairs :
    UpperTheory.Gal.Spc.VanPairs := by
  intro p _ G ha Lv k _ _ _ _ _ _ _ R H _ _ _ _ S k₁ _ _ P₁ f hf hC _ Q hm hirr
  obtain ⟨μ, hM⟩ := hm
  unfold Pair.term
  split_ifs with h
  · have hcp := GlobalTheory.charpoly_algHom_eq_map_minpoly G.F k G.C G.n G.rankC R.ι (Q.γ : G.C) Q.reg.1
    have hat := charpoly_at_self R Q Q.trivAf.choose Q.trivAf.choose_spec.choose Q.trivAf.choose_spec.choose_spec
    rw [hcp] at hat
    refine termAt_zero G ha Lv Q μ hM f hf _ _ _ h.choose.1 h.choose.2 h.choose_spec ?_
    exact orbK_eq_zero_of_cuspSlices S f hf hC _ (by rw [hat]; exact Q.reg.2.map)
      (by
        rw [hat]
        exact GlobalTheory.VanishNonEll.not_irreducible_map _ _ (minpoly.monic (IsIntegral.of_finite G.F _)) hirr)
      (GlobalTheory.LKCentAf.twCent_comm Q _ _ _)
  · rfl
