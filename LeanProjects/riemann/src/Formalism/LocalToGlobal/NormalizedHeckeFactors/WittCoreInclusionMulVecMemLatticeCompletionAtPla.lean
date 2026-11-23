import Formalism.LocalToGlobal.NormalizedHeckeFactors.TwDefs
import Formalism.LocalRingCardinality.DataNChoice
import Formalism.LocalRingCardinality.DataIdx
import Formalism.LocalToGlobal.GaloisLevelStructure.TiedGal
import Formalism.LocalToGlobal.UnitaryNorms.LeastSplitAuxiliaryPrimeThetaChainSpec

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.TwC Polynomial
open scoped TensorProduct NNReal

namespace Formalism.L2

set_option synthInstance.maxHeartbeats 400000 in

structure TwFrame (D : D7) where

  K0 : ∀ i, Loc.FinExt (D.ntw.l i)
  eO0 : ∀ i, D.ntw.O0 i ≃+* intOf (D.ntw.l i) (K0 i).1

  j0 : ∀ i, ↥D.LL0 →+* PadicAlgCl (D.ntw.l i)

  Lw : ∀ i, Loc.FinExt (D.ntw.l i)
  eO : ∀ i, D.ntw.O i ≃+* clC (D.ntw.l i) (Kt (D.ntw.l i) (K0 i) (Lw i))

  eOk : ∀ i k, D.ntw.Ok i k ≃+* clC (D.ntw.l i) (Kt (D.ntw.l i) (K0 i) (Lw i) ⊔ muK (D.ntw.l i) k)

  iCq : ∀ i, FractionRing (D.ntw.O i) →+* ℂ

  S0x : D.ntw.Tw → Finset (HeightOneSpectrum (𝓞 D.host.E))

def ConjPreservesLL0 (D : D7) : Prop :=
  ∀ x : ↥D.LL0, ∃ y : ↥D.LL0, (y : D.what₂.LL) = star (x : D.what₂.LL)

theorem ll0Conj_of_normal (D : D7) (h : Normal ℚ D.LL0) : ConjPreservesLL0 D := by
  intro x
  let σ : D.what₂.LL →ₐ[ℚ] D.what₂.LL := (starRingEnd D.what₂.LL).toRatAlgHom
  have hmap : D.LL0.map σ = D.LL0 := (IntermediateField.normal_iff_forall_map_eq.1 h) σ
  have hx : σ (x : D.what₂.LL) ∈ D.LL0 := by
    have h1 : σ (x : D.what₂.LL) ∈ D.LL0.map σ := ⟨x, x.2, rfl⟩
    rwa [hmap] at h1
  exact ⟨⟨σ x, hx⟩, rfl⟩

def DoubleSEven (D : D7) : Prop :=
  ∀ i lam, Even (D.ntw.s2 i lam)

set_option synthInstance.maxHeartbeats 400000 in

structure NTwTied (D : D7) (F : TwFrame D) : Prop where

  pl_emb : ∀ i, ∃ w : HeightOneSpectrum (𝓞 ↥D.LL0), ((D.ntw.l i : ℕ) : 𝓞 ↥D.LL0) ∈ w.asIdeal ∧
    ∀ x : 𝓞 ↥D.LL0, x ∈ w.asIdeal ↔ ∃ y ∈ IsLocalRing.maximalIdeal (D.ntw.O0 i),
      algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) y = D.ntw.emb0 i (x : ↥D.LL0)

  ringSpec_baseIntegersEquiv_algebraMap : ∀ i (z : ℤ_[D.ntw.l i]),
    ((F.eO0 i (algebraMap ℤ_[D.ntw.l i] (D.ntw.O0 i) z) : PadicAlgCl (D.ntw.l i))) =
      algebraMap ℚ_[D.ntw.l i] (PadicAlgCl (D.ntw.l i)) (z : ℚ_[D.ntw.l i])

  ringSpec_baseEmbedding_compatible : ∀ i (x : ↥D.LL0) (y z : D.ntw.O0 i), z ≠ 0 →
    (D.ntw.emb0 i x * algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) z =
        algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) y ↔
      F.j0 i x * (F.eO0 i z : PadicAlgCl (D.ntw.l i)) = (F.eO0 i y : PadicAlgCl (D.ntw.l i)))

  eO_alg : ∀ i (y : D.ntw.O0 i), ((F.eO i (algebraMap (D.ntw.O0 i) (D.ntw.O i) y) : ℂ_[D.ntw.l i])) =
    algebraMap (PadicAlgCl (D.ntw.l i)) ℂ_[D.ntw.l i] (F.eO0 i y : PadicAlgCl (D.ntw.l i))

  eOk_alg : ∀ i k (x : D.ntw.O i), ((F.eOk i k (algebraMap (D.ntw.O i) (D.ntw.Ok i k) x) : ℂ_[D.ntw.l i])) =
    (F.eO i x : ℂ_[D.ntw.l i])

  mu_g : ∀ i k, D.ntw.l i = D.host.g k → muK (D.ntw.l i) 1 ≤ Kt (D.ntw.l i) (F.K0 i) (F.Lw i)

  hk_split : ∀ i j b k P, P ∉ D.ntw.S0 i → ∃ s : Multiset (FractionRing (D.ntw.O i)),
    (LinearMap.charpoly (D.ntw.hk i j b k P)).map (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))) =
      (s.map fun a => X - C a).prod

  ringSpec_excludedPlaces_eq : ∀ i, (D.ntw.S0 i : Set (HeightOneSpectrum (𝓞 D.host.E))) =
    placesOver D.host.E (D.ntw.l i) ∪ (⋃ k, placesOver D.host.E (D.host.g k)) ∪
      placesOver D.host.E D.host.pde ∪ placesOver D.host.E D.host.pde' ∪ ↑(F.S0x i)

  concreteTwistFrame_extraExcludedPlaces_conj : ∀ i P P', P ∈ F.S0x i → IsConjPl D.host P P' → P' ∈ F.S0x i

  B_range : ∀ i j b, LinearMap.range (D.nexp.embB i j b) =
    D.nexp.Bsup i j b ⊓ (NForms.V0 D i j b).restrictScalars (D.ntw.O i)

  sig_inj : ∀ i (s s' : D.ntw.Sig i), D.ntw.jS i s = D.ntw.jS i s' → D.ntw.side i s = D.ntw.side i s' →
    (∀ k P, 1 ≤ k → k ≤ D.R.r → IsSplitPl D.host P → P ∉ D.ntw.S0 i →
      D.ntw.hEig i s k P = D.ntw.hEig i s' k P) → s = s'

  qs_pos : ∀ i lam P, P ∉ D.ntw.S0 i →
    F.iCq i (D.ntw.qs i lam P) = ((((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ (-(D.ntw.s2 i lam : ℝ) / 2) : ℝ) : ℂ)

  S0x_contains_ccK_places : ∀ i (p : ℕ), p.Prime → p ∣ Ideal.absNorm D.host.ccK → placesOver D.host.E p ⊆ ↑(F.S0x i)

  S0x_contains_q0_places : ∀ i, placesOver D.host.E (Formalism.MainNotions.AbsolutelyIrreducibleSpan.q0 D) ⊆ ↑(F.S0x i)

  S0x_contains_two_places : ∀ i, placesOver D.host.E 2 ⊆ ↑(F.S0x i)

  S0x_contains_ramified_places : ∀ i (p : ℕ), p.Prime → p ∣ (NumberField.discr D.host.E).natAbs → placesOver D.host.E p ⊆ ↑(F.S0x i)

set_option synthInstance.maxHeartbeats 400000 in

structure TwChoiceTied (D : D7) (c : NChoice D) : Prop where
  twOf : ∀ a, D.ntw.twOf a = c.twI (D.nd.w a)
  twSide : ∀ a, D.ntw.twSide a = c.sd (D.nd.w a)

theorem pD_eq_pDC (D : D7) (i : D.ntw.Tw) : D.ntw.pD i = pDC D.host (D.ntw.l i) :=
  Finset.coe_injective ((D.ntw.pD_eq i).trans (coe_pDC D.host _).symm)

theorem NTwTied.emb0b_eq_emb0_conj {D : D7} {F : TwFrame D} (_T : NTwTied D F) (hc : ConjPreservesLL0 D) (i : D.ntw.Tw)
    (x : ↥D.LL0) :
    ∃ y : ↥D.LL0, (y : D.what₂.LL) = star (x : D.what₂.LL) ∧ D.ntw.emb0b i x = D.ntw.emb0 i y := by
  obtain ⟨y, hy⟩ := hc x
  exact ⟨y, hy, D.ntw.restX_coefficientEmbedding_conj i x y hy⟩

theorem clC_mono (l : ℕ) [Fact l.Prime] {F F' : IntermediateField ℚ_[l] (PadicAlgCl l)} (h : F ≤ F') :
    clC l F ≤ clC l F' := by
  intro x hx
  refine ⟨?_, hx.2⟩
  have hm : F.toSubalgebra.toSubring.map (algebraMap (PadicAlgCl l) ℂ_[l]) ≤
      F'.toSubalgebra.toSubring.map (algebraMap (PadicAlgCl l) ℂ_[l]) := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨y, h hy, rfl⟩
  exact Subring.topologicalClosure_minimal _ (hm.trans (Subring.le_topologicalClosure _))
    (Subring.isClosed_topologicalClosure _) hx.1

theorem l_not_unit_clC (l : ℕ) [Fact l.Prime] (F : IntermediateField ℚ_[l] (PadicAlgCl l)) :
    ¬ IsUnit ((l : ℕ) : clC l F) := by
  rintro ⟨u, hu⟩
  set v : clC l F := ((u⁻¹ : (clC l F)ˣ) : clC l F) with hv
  have h1 : v * ((l : ℕ) : clC l F) = 1 := by rw [hv, ← hu]; exact u.inv_mul
  have h1' : (v : ℂ_[l]) * ((l : ℕ) : ℂ_[l]) = 1 := by
    have h := congrArg (fun y : clC l F => (y : ℂ_[l])) h1
    simp only [Subring.coe_mul, Subring.coe_one] at h
    rw [← h]
    congr 1
  have h2 : Valued.v (v : ℂ_[l]) ≤ 1 := (Subring.mem_inf.mp v.2).2
  have h3 := congrArg Valued.v h1'
  rw [map_mul, PadicComplex.valuation_p, map_one] at h3
  have hl : (1 : ℝ≥0) < (l : ℝ≥0) := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have h4 : Valued.v (v : ℂ_[l]) * (1 / (l : ℝ≥0)) < 1 := by
    calc Valued.v (v : ℂ_[l]) * (1 / (l : ℝ≥0)) ≤ 1 * (1 / (l : ℝ≥0)) := by gcongr
      _ < 1 := by rw [one_mul, div_lt_one (by positivity)]; exact hl
  exact absurd h3 (ne_of_lt h4)

theorem cc_frame (D : D7) (fr : OmFrame D) : ∃ (c : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) (j : AlgebraicClosure ℚ →+* ℂ),
    (∀ x, j (c x) = starRingEnd ℂ (j x)) ∧ ∀ x, fr.eOm (D.ntw.cc x) = c (fr.eOm x) := by
  obtain ⟨⟨j, hj⟩, _⟩ := D.ntw.cc_cm
  refine ⟨(fr.eOm.symm.trans D.ntw.cc).trans fr.eOm, j.comp fr.eOm.symm.toRingHom, fun x => ?_, fun x => ?_⟩
  · simp [hj]
  · simp

theorem TwChoiceTied.l_eq (D : D7) (c : NChoice D) (T : TwChoiceTied D c) (a : D.nd.Loc) :
    D.nd.l a = D.what₂.places.resChar (D.nd.w a) := by
  rw [← D.ntw.twOf_l a, T.twOf a, c.twI_l]

theorem NTwTied.sig_unique {D : D7} {F : TwFrame D} (T : NTwTied D F) (i : D.ntw.Tw) (s s' : D.ntw.Sig i)
    (hj : D.ntw.jS i s = D.ntw.jS i s') (hb : D.ntw.side i s = D.ntw.side i s')
    (x : TensorProduct (D.ntw.O i) (FractionRing (D.ntw.O i)) (D.ntw.B i (D.ntw.jS i s) (D.ntw.side i s)))
    (hx : x ≠ 0)
    (h : ∀ k P, P ∉ D.ntw.S0 i →
      ((D.ntw.hk i (D.ntw.jS i s) (D.ntw.side i s) k P).lTensor (FractionRing (D.ntw.O i))) x =
        algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (D.ntw.hEig i s k P) • x ∧
      ((D.ntw.hk i (D.ntw.jS i s) (D.ntw.side i s) k P).lTensor (FractionRing (D.ntw.O i))) x =
        algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (D.ntw.hEig i s' k P) • x) : s = s' := by
  refine T.sig_inj i s s' hj hb fun k P _ _ _ hP => ?_
  have h2 := (h k P hP).1.symm.trans (h k P hP).2
  have h3 : (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (D.ntw.hEig i s k P) -
      algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (D.ntw.hEig i s' k P)) • x = 0 := by
    exact (sub_smul _ _ x).trans (by rw [h2, sub_self])
  rcases smul_eq_zero.mp h3 with h4 | h4
  · exact IsFractionRing.injective (D.ntw.O i) (FractionRing (D.ntw.O i)) (sub_eq_zero.mp h4)
  · exact absurd h4 hx

theorem eG_mul_self (D : D7) (i : D.ntw.Tw) (j : ℕ) (b : Bool) :
    NForms.eG D i j b * NForms.eG D i j b = NForms.eG D i j b := by
  unfold NForms.eG
  rw [← map_mul, D.nexp.eAlg_idem]

theorem eG_actG (D : D7) (i : D.ntw.Tw) (j : ℕ) (b : Bool) (g : G0g D.nd) (f : D.nexp.Fm i j b) :
    NForms.eG D i j b (D.nexp.actG i j b g f) = D.nexp.actG i j b g (NForms.eG D i j b f) := by
  have h := congrArg (MonoidAlgebra.lift (FractionRing (D.ntw.O i))
    (Module.End (FractionRing (D.ntw.O i)) (D.nexp.Fm i j b)) (G0g D.nd)
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (D.nexp.actG i j b)))
    (D.nexp.eAlg_central i b (MonoidAlgebra.of (FractionRing (D.ntw.O i)) (G0g D.nd) g))
  rw [map_mul, map_mul, MonoidAlgebra.lift_of] at h
  exact LinearMap.congr_fun h f

theorem goodPart_le_typeSubspace (D : D7) (i : D.ntw.Tw) (j : ℕ) (b : Bool) : NForms.V0 D i j b ≤ NForms.Fm0 D i j b := by
  rintro _ ⟨y, hy0, rfl⟩
  have hy : y ∈ NForms.Fm0 D i j b := hy0
  simp only [NForms.Fm0, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, LinearEquiv.coe_coe, sub_eq_zero] at hy ⊢
  intro u
  rw [← eG_actG, hy u, map_smul]

theorem V0_eq_type_inf_range (D : D7) (i : D.ntw.Tw) (j : ℕ) (b : Bool) :
    NForms.V0 D i j b = NForms.Fm0 D i j b ⊓ LinearMap.range (NForms.eG D i j b) := by
  apply le_antisymm
  · exact le_inf (goodPart_le_typeSubspace D i j b) LinearMap.map_le_range
  · intro x hx
    obtain ⟨hx0, z, rfl⟩ := Submodule.mem_inf.mp hx
    refine ⟨NForms.eG D i j b z, hx0, ?_⟩
    show NForms.eG D i j b (NForms.eG D i j b z) = NForms.eG D i j b z
    rw [← Module.End.mul_apply, eG_mul_self]

theorem NTwTied.range_embB_le_type_forms {D : D7} {F : TwFrame D} (T : NTwTied D F) (i : D.ntw.Tw) (j : ℕ) (b : Bool) :
    LinearMap.range (D.nexp.embB i j b) ≤ (NForms.Fm0 D i j b).restrictScalars (D.ntw.O i) := by
  rw [T.B_range i j b]
  exact fun x hx => goodPart_le_typeSubspace D i j b (Submodule.mem_inf.mp hx).2

theorem NTwTied.range_eq_all {D : D7} {F : TwFrame D} (T : NTwTied D F) (i : D.ntw.Tw) (j : ℕ) (b : Bool) :
    LinearMap.range (D.nexp.embB i j b) =
      D.nexp.Bsup i j b ⊓ (NForms.Fm0 D i j b).restrictScalars (D.ntw.O i) ⊓
        (LinearMap.range (NForms.eG D i j b)).restrictScalars (D.ntw.O i) := by
  rw [T.B_range i j b, V0_eq_type_inf_range]
  ext x
  simp only [Submodule.mem_inf, Submodule.restrictScalars_mem]
  tauto

theorem NTwTied.mem_range_iff {D : D7} {F : TwFrame D} (T : NTwTied D F) (i : D.ntw.Tw) (j : ℕ) (b : Bool)
    (f : D.nexp.Fm i j b) :
    f ∈ LinearMap.range (D.nexp.embB i j b) ↔
      f ∈ D.nexp.Bsup i j b ∧ f ∈ NForms.Fm0 D i j b ∧ NForms.eG D i j b f = f := by
  rw [T.range_eq_all i j b]
  simp only [Submodule.mem_inf, Submodule.restrictScalars_mem, LinearMap.mem_range]
  constructor
  · rintro ⟨⟨h1, h2⟩, z, hz⟩
    refine ⟨h1, h2, ?_⟩
    rw [← hz, ← Module.End.mul_apply, eG_mul_self]
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2⟩, f, h3⟩

theorem NTwTied.smul_eG_mem {D : D7} {F : TwFrame D} (T : NTwTied D F) (i : D.ntw.Tw) (j : ℕ) (b : Bool)
    (c : D.ntw.O i) (f : D.nexp.Fm i j b) (hf : f ∈ NForms.Fm0 D i j b)
    (hB : c • NForms.eG D i j b f ∈ D.nexp.Bsup i j b) :
    c • NForms.eG D i j b f ∈ LinearMap.range (D.nexp.embB i j b) := by
  rw [T.mem_range_iff]
  refine ⟨hB, ?_, ?_⟩
  · rw [← algebraMap_smul (FractionRing (D.ntw.O i))]
    exact (NForms.Fm0 D i j b).smul_mem _ (goodPart_le_typeSubspace D i j b ⟨f, hf, rfl⟩)
  · rw [← algebraMap_smul (FractionRing (D.ntw.O i)), map_smul, ← Module.End.mul_apply, eG_mul_self]

theorem NTwTied.delta_prime_places_subset_S0 {D : D7} {F : TwFrame D} (T : NTwTied D F) (i : D.ntw.Tw) :
    placesOver D.host.E D.host.pde ∪ placesOver D.host.E D.host.pde' ⊆ ↑(D.ntw.S0 i) := by
  rw [T.ringSpec_excludedPlaces_eq i]
  rintro P (hP | hP)
  · exact Or.inl (Or.inl (Or.inr hP))
  · exact Or.inl (Or.inr hP)

theorem NTwTied.S0_contains_record_minimum {D : D7} {F : TwFrame D} (T : NTwTied D F) (i : D.ntw.Tw) :
    placesOver D.host.E (D.ntw.l i) ∪ (⋃ k, placesOver D.host.E (D.host.g k)) ∪ ↑(D.ntw.pD i) ⊆ ↑(D.ntw.S0 i) := by
  have hpD := D.ntw.pD_eq i
  rw [T.ringSpec_excludedPlaces_eq i]
  rintro P ((hP | hP) | hP)
  · exact Or.inl (Or.inl (Or.inl (Or.inl hP)))
  · exact Or.inl (Or.inl (Or.inl (Or.inr hP)))
  · rw [hpD] at hP
    split_ifs at hP
    · exact Or.inl (Or.inr hP)
    · exact Or.inl (Or.inl (Or.inr hP))

theorem NTwTied.wittCoreInclusion_mulVec_mem_latticeCompletionAtPlace {D : D7} {F : TwFrame D} (T : NTwTied D F) (i : D.ntw.Tw) (x : ↥D.LL0) :
    F.j0 i x ∈ (F.K0 i).1 := by
  obtain ⟨⟨y, z⟩, hyz⟩ := IsLocalization.surj (nonZeroDivisors (D.ntw.O0 i)) (D.ntw.emb0 i x)
  have hz : (z : D.ntw.O0 i) ≠ 0 := nonZeroDivisors.ne_zero z.2
  have h := (T.ringSpec_baseEmbedding_compatible i x y z hz).mp hyz
  have hz' : ((F.eO0 i z : intOf (D.ntw.l i) (F.K0 i).1) : PadicAlgCl (D.ntw.l i)) ≠ 0 := by
    intro h0
    apply hz
    exact (F.eO0 i).map_eq_zero_iff.mp (Subtype.ext h0)
  have hx : F.j0 i x = (F.eO0 i y : PadicAlgCl (D.ntw.l i)) / (F.eO0 i z : PadicAlgCl (D.ntw.l i)) := by
    rw [eq_div_iff hz', h]
  rw [hx]
  exact (F.K0 i).1.div_mem (F.eO0 i y).2.1 (F.eO0 i z).2.1

theorem NTwTied.qs_eq {D : D7} {F : TwFrame D} (T : NTwTied D F) (h2 : DoubleSEven D) (i : D.ntw.Tw)
    (lam : D.ntw.abelian₂ i) (P : HeightOneSpectrum (𝓞 D.host.E)) (hP : P ∉ D.ntw.S0 i) :
    D.ntw.qs i lam P =
      ((Ideal.absNorm P.asIdeal : ℕ) : FractionRing (D.ntw.O i)) ^ (-(D.ntw.s2 i lam / 2)) := by
  obtain ⟨m, hm⟩ := h2 i lam
  apply (F.iCq i).injective
  rw [T.qs_pos i lam P hP, map_zpow₀, map_natCast, hm]
  have e1 : (-((m + m : ℤ) : ℝ) / 2) = ((-m : ℤ) : ℝ) := by push_cast; ring
  have e2 : (m + m) / 2 = m := by omega
  rw [e1, Real.rpow_intCast, e2]
  push_cast
  rfl

theorem qs_pos_of_eq (D : D7) (h2 : DoubleSEven D) (i : D.ntw.Tw) (ι : FractionRing (D.ntw.O i) →+* ℂ)
    (lam : D.ntw.abelian₂ i) (P : HeightOneSpectrum (𝓞 D.host.E))
    (h : D.ntw.qs i lam P =
      ((Ideal.absNorm P.asIdeal : ℕ) : FractionRing (D.ntw.O i)) ^ (-(D.ntw.s2 i lam / 2))) :
    ι (D.ntw.qs i lam P) =
      ((((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ (-(D.ntw.s2 i lam : ℝ) / 2) : ℝ) : ℂ) := by
  obtain ⟨m, hm⟩ := h2 i lam
  rw [h, map_zpow₀, map_natCast, hm]
  have e1 : (-((m + m : ℤ) : ℝ) / 2) = ((-m : ℤ) : ℝ) := by push_cast; ring
  have e2 : (m + m) / 2 = m := by omega
  rw [e1, Real.rpow_intCast, e2]
  push_cast
  rfl

theorem placesOver_conj (D : D7) (p : ℕ) {P P' : HeightOneSpectrum (𝓞 D.host.E)} (hP : P ∈ placesOver D.host.E p)
    (hc : IsConjPl D.host P P') : P' ∈ placesOver D.host.E p := by
  have h : (((p : 𝓞 D.host.E)) : D.host.E) = D.host.conj (((p : 𝓞 D.host.E)) : D.host.E) := by
    simp only [map_natCast]
  exact (hc _ _ h).1 hP

def lowPr (D : D7) : Finset ℕ :=
  insert 2 (insert (Formalism.MainNotions.AbsolutelyIrreducibleSpan.q0 D)
    ((Ideal.absNorm D.host.ccK).primeFactors ∪ (NumberField.discr D.host.E).natAbs.primeFactors))

theorem lowPr_ne_zero (D : D7) : ∀ p ∈ lowPr D, p ≠ 0 := by
  intro p hp
  simp only [lowPr, Finset.mem_insert, Finset.mem_union] at hp
  rcases hp with rfl | rfl | hp | hp
  · norm_num
  · exact (Formalism.L2.Host.leastSplitAuxiliaryPrimeThetaChain_spec D).1.ne_zero
  · exact (Nat.prime_of_mem_primeFactors hp).ne_zero
  · exact (Nat.prime_of_mem_primeFactors hp).ne_zero

theorem low_prime_places_finite (D : D7) : (⋃ p ∈ (lowPr D : Set ℕ), placesOver D.host.E p).Finite :=
  Set.Finite.biUnion (Finset.finite_toSet _) fun p hp => placesOver_finite' D.host.E p (lowPr_ne_zero D p hp)

theorem S0x_enlarge_closed (D : D7) (S : Finset (HeightOneSpectrum (𝓞 D.host.E)))
    (hS : ∀ P P', P ∈ S → IsConjPl D.host P P' → P' ∈ S) :
    ∃ S' : Finset (HeightOneSpectrum (𝓞 D.host.E)), S ⊆ S' ∧ (∀ P P', P ∈ S' → IsConjPl D.host P P' → P' ∈ S') ∧
      (∀ (p : ℕ), p.Prime → p ∣ Ideal.absNorm D.host.ccK → placesOver D.host.E p ⊆ ↑S') ∧
      placesOver D.host.E (Formalism.MainNotions.AbsolutelyIrreducibleSpan.q0 D) ⊆ ↑S' ∧ placesOver D.host.E 2 ⊆ ↑S' ∧
      (∀ (p : ℕ), p.Prime → p ∣ (NumberField.discr D.host.E).natAbs → placesOver D.host.E p ⊆ ↑S') := by
  classical
  have hN : Ideal.absNorm D.host.ccK ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact D.host.ccK_ne_bot
  have hd : (NumberField.discr D.host.E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero D.host.E)
  have hmem : ∀ p ∈ lowPr D, placesOver D.host.E p ⊆ ↑(S ∪ (low_prime_places_finite D).toFinset) := by
    intro p hp P hP
    refine Finset.mem_union_right _ ?_
    rw [Set.Finite.mem_toFinset]
    exact Set.mem_biUnion hp hP
  refine ⟨S ∪ (low_prime_places_finite D).toFinset, Finset.subset_union_left, ?_, ?_, ?_, ?_, ?_⟩
  · intro P P' hP hc
    rcases Finset.mem_union.1 hP with h | h
    · exact Finset.mem_union_left _ (hS P P' h hc)
    · refine Finset.mem_union_right _ ?_
      rw [Set.Finite.mem_toFinset] at h ⊢
      obtain ⟨p, hp⟩ := Set.mem_iUnion.1 h
      obtain ⟨hp1, hp2⟩ := Set.mem_iUnion.1 hp
      exact Set.mem_biUnion hp1 (placesOver_conj D p hp2 hc)
  · intro p hp hdvd
    exact hmem p (by simp [lowPr, Nat.mem_primeFactors, hp, hdvd, hN])
  · exact hmem _ (by simp [lowPr])
  · exact hmem _ (by simp [lowPr])
  · intro p hp hdvd
    exact hmem p (by simp [lowPr, Nat.mem_primeFactors, hp, hdvd, hd])

theorem NTwTied.q0_places_subset_S0 {D : D7} {F : TwFrame D} (T : NTwTied D F) (i : D.ntw.Tw) :
    placesOver D.host.E (Formalism.MainNotions.AbsolutelyIrreducibleSpan.q0 D) ⊆ ↑(D.ntw.S0 i) := by
  rw [T.ringSpec_excludedPlaces_eq i]
  exact fun P hP => Or.inr (T.S0x_contains_q0_places i hP)

theorem NTwTied.norm_ccK_places_subset_S0 {D : D7} {F : TwFrame D} (T : NTwTied D F) (i : D.ntw.Tw) (p : ℕ) (hp : p.Prime)
    (hdvd : p ∣ Ideal.absNorm D.host.ccK) : placesOver D.host.E p ⊆ ↑(D.ntw.S0 i) := by
  rw [T.ringSpec_excludedPlaces_eq i]
  exact fun P hP => Or.inr (T.S0x_contains_ccK_places i p hp hdvd hP)

theorem NTwTied.two_ramified_places_subset_S0 {D : D7} {F : TwFrame D} (T : NTwTied D F) (i : D.ntw.Tw) :
    placesOver D.host.E 2 ⊆ ↑(D.ntw.S0 i) ∧ ∀ (p : ℕ), p.Prime → p ∣ (NumberField.discr D.host.E).natAbs →
      placesOver D.host.E p ⊆ ↑(D.ntw.S0 i) := by
  rw [T.ringSpec_excludedPlaces_eq i]
  exact ⟨fun P hP => Or.inr (T.S0x_contains_two_places i hP), fun p hp hdvd P hP => Or.inr (T.S0x_contains_ramified_places i p hp hdvd hP)⟩

end Formalism.L2
