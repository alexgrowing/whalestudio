import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRingEquivSplitPrime

noncomputable section

namespace GlobalTheory.LFun.SplitChart

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU
open Formalism.MainNotions.SchurIrreducible (IsSplit)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)}
  {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)}

theorem continuous_complMap (h : w.under (𝓞 F) = v) : Continuous (complMap h) := by
  subst h
  refine continuous_of_continuousAt_zero _ ?_
  rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero _ _).tendsto_right_iff]
  intro γ _
  have h0 : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := by simp
  obtain ⟨k, hk⟩ : ∃ k : ℤ, MonoidWithZeroHom.ValueGroup₀.embedding γ.1 = WithZero.exp k :=
    ⟨_, (WithZero.exp_log h0).symm⟩
  filter_upwards [(GlobalTheory.Idele.isOpen_valued_le (K := F) (w.under (𝓞 F)) (-((k.natAbs + 1 : ℕ) : ℤ))).mem_nhds
    (by simp)] with a ha
  rw [Valuation.restrict_lt_iff_lt_embedding, hk]
  exact (GlobalTheory.AdeleBaseChange.locMap_valued w _ a ha).trans_lt (WithZero.exp_lt_exp.2 (by omega))

theorem exists_splitPrime_eq (hc : IsCMExt F E σ) (hv : IsSplit (E := E) v) (h : w.under (𝓞 F) = v) :
    ∃ τ : E →ₐ[F] Fv F v, splitPrime τ = w := by
  obtain ⟨P, Q, hne, hP, hQ⟩ := hv
  by_cases e : w = P
  · exact (existsUnique_splitPrime_eq hc (e ▸ hne) h (HeightOneSpectrum.ext hQ)).exists
  · exact (existsUnique_splitPrime_eq hc e h (HeightOneSpectrum.ext hP)).exists

theorem exists_equiv_complMap (τ : E →ₐ[F] Fv F v) (h : (splitPrime τ).under (𝓞 F) = v) :
    ∃ ψ : Fv F v ≃+* (splitPrime τ).adicCompletion E, (∀ a, ψ a = complMap h a) ∧
      (∀ x : E, ψ (τ x) = algebraMap E _ x) ∧ (∀ a, Valued.v (ψ a) = Valued.v a) ∧ Continuous ψ ∧
      Continuous ψ.symm := by
  obtain ⟨φ, h1, h2, h3, h4⟩ := GlobalTheory.SplitCompletion.exists_ringEquiv_splitPrime τ
  have h5 : ∀ x : E, φ.symm (τ x) = algebraMap E _ x := fun x => by rw [← h1, φ.symm_apply_apply]
  refine ⟨φ.symm, congrFun ((HeightOneSpectrum.denseRange_algebraMap F v).equalizer h4 (continuous_complMap h)
    (funext fun a => ?_)), h5, fun a => by rw [← h2, φ.apply_symm_apply], h4, h3⟩
  exact ((congrArg φ.symm (τ.commutes a).symm).trans (h5 _)).trans (complMap_algebraMap h a).symm

section Transport

variable {τ : E →ₐ[F] Fv F v} {h : w.under (𝓞 F) = v} {ψ : Fv F v ≃+* w.adicCompletion E}

theorem toCompl_eq (h1 : ∀ a, ψ a = complMap h a) (h2 : ∀ x : E, ψ (τ x) = algebraMap E _ x)
    (y : Fv F v ⊗[F] E) : toCompl h y = ψ (splitProj τ y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x => rw [toCompl_tmul, splitProj_tmul, map_mul, h1, h2]

omit [Algebra F E] in
theorem map_mem_Ov_iff (h3 : ∀ a, Valued.v (ψ a) = Valued.v a) {a : Fv F v} :
    ψ a ∈ Ov E w ↔ a ∈ v.adicCompletionIntegers F := by
  change Valued.v (ψ a) ≤ 1 ↔ Valued.v a ≤ 1
  rw [h3]

theorem map_mem_latAt_iff (h2 : ∀ x : E, ψ (τ x) = algebraMap E _ x) (h3 : ∀ a, Valued.v (ψ a) = Valued.v a)
    {u : Fin n → Fv F v} : (fun i => ψ (u i)) ∈ latAt w L ↔ u ∈ splitLat τ L := by
  constructor
  · intro hu
    have key : ∀ y ∈ latAt w L, (fun i => ψ.symm (y i)) ∈ splitLat τ L := fun y hy => by
      induction hy using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨z, hz, rfl⟩ := hx
        refine ⟨_, tmul_mem_latLoc (one_mem _) hz, funext fun i => ?_⟩
        change splitProj τ (1 ⊗ₜ[F] z i) = ψ.symm (algebraMap E _ (z i))
        rw [splitProj_tmul, one_mul, ← h2, ψ.symm_apply_apply]
      | zero => exact (funext fun _ => map_zero ψ.symm : (fun i => ψ.symm ((0 : Fin n → _) i)) = 0) ▸ zero_mem _
      | add a b _ _ ha hb =>
        have := add_mem ha hb
        convert this using 1
        exact funext fun i => map_add ψ.symm _ _
      | smul a b _ hb =>
        have := (splitLat τ L).smul_mem ⟨ψ.symm a, (map_mem_Ov_iff h3).1 (by rw [ψ.apply_symm_apply]; exact a.2)⟩ hb
        convert this using 1
        exact funext fun i => map_mul ψ.symm _ _
    simpa using key _ hu
  · rintro ⟨y, hy, rfl⟩
    refine latLoc_induction (p := fun y => (fun i => ψ (splitVec τ y i)) ∈ latAt w L) (fun a ha x hx => ?_) ?_
      (fun y z hy hz => ?_) (fun y hy => ?_) hy
    · have := (latAt w L).smul_mem ⟨ψ a, (map_mem_Ov_iff h3).2 ha⟩ (Submodule.subset_span ⟨x, hx, rfl⟩)
      convert this using 1
      funext i
      change ψ (a * τ (x i)) = ψ a * algebraMap E _ (x i)
      rw [map_mul, h2]
    · convert zero_mem (latAt w L) using 1
      funext i
      simp [splitVec]
    · convert add_mem hy hz using 1
      funext i
      simp [splitVec]
    · convert neg_mem hy using 1
      funext i
      simp [splitVec]

theorem isFrameAt_bc (h2 : ∀ x : E, ψ (τ x) = algebraMap E _ x) (h3 : ∀ a, Valued.v (ψ a) = Valued.v a)
    {β : GL (Fin n) (Fv F v)} (hβ : IsSplitBasis τ L β) : IsFrameAt w L (bc ψ.toRingHom β) := fun y => by
  obtain ⟨u, rfl⟩ : ∃ u : Fin n → Fv F v, y = fun i => ψ (u i) := ⟨fun i => ψ.symm (y i), by simp⟩
  have e : (bc ψ.toRingHom β).1 *ᵥ (fun i => ψ (u i)) = fun i => ψ ((β.1 *ᵥ u) i) :=
    funext fun i => (RingHom.map_mulVec ψ.toRingHom β.1 u i).symm
  simp only [e, map_mem_Ov_iff h3, map_mem_latAt_iff h2 h3]
  exact hβ u

omit [Algebra F E] in
theorem bc_mem_KGL_iff (h3 : ∀ a, Valued.v (ψ a) = Valued.v a) {x : GL (Fin n) (Fv F v)} :
    bc ψ.toRingHom x ∈ KGL w n ↔ x ∈ GLint (Fin n) (v.adicCompletionIntegers F).toSubring := by
  rw [mem_GLint_iff, mem_GLint_iff]
  exact and_congr (forall₂_congr fun _ _ => map_mem_Ov_iff h3) (forall₂_congr fun _ _ => map_mem_Ov_iff h3)

end Transport

theorem continuous_bc {A B : Type} [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B]
    {f : A →+* B} (hf : Continuous f) : Continuous (bc (n := Fin n) f) :=
  Units.continuous_iff.2 ⟨Units.continuous_val.matrix_map hf, Units.continuous_coe_inv.matrix_map hf⟩

theorem exists_isSplitChart (hc : IsCMExt F E σ) (hJ : IsHermND σ J) (hL : L.FG)
    (hL' : Submodule.span E (L : Set (Fin n → E)) = ⊤) (h : w.under (𝓞 F) = v) (hv : IsSplit (E := E) v)
    (hd : IsSelfDualAt σ J L v) : ∃ e, IsSplitChart σ J L h e ∧ Continuous e ∧ Continuous e.symm := by
  obtain ⟨τ, rfl⟩ := exists_splitPrime_eq hc hv h
  obtain ⟨ψ, h1, h2, h3, h4, h5⟩ := exists_equiv_complMap τ h
  have : Submodule.IsLattice E L := ⟨hL, hL'⟩
  obtain ⟨β, hβ⟩ := exists_isSplitBasis τ L hc
  refine ⟨(splitEquivIn hc hJ τ β).toMulEquiv.trans (Units.mapEquiv ψ.mapMatrix.toMulEquiv),
    ⟨⟨_, isFrameAt_bc h2 h3 hβ, fun g => ?_⟩, fun g => ?_⟩,
    (continuous_bc (f := ψ.toRingHom) h4).comp (splitEquivIn hc hJ τ β).continuous,
    (splitEquivIn hc hJ τ β).symm.continuous.comp (continuous_bc (f := ψ.symm.toRingHom) h5)⟩
  · change bc ψ.toRingHom (β⁻¹ * splitHom σ J τ g * β) = _
    rw [map_mul, map_mul, map_inv]
    congr 2
    exact Units.ext (Matrix.ext fun i j => (toCompl_eq h1 h2 _).symm)
  · exact (mem_stabLoc_iff_GLint hc hJ hd hβ).trans (bc_mem_KGL_iff h3).symm

theorem absNorm_splitPrime (τ : E →ₐ[F] Fv F v) :
    Ideal.absNorm (splitPrime τ).asIdeal = Ideal.absNorm v.asIdeal := by
  have hle : v.asIdeal = (splitPrime τ).asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) :=
    (Ideal.ext (algebraMap_mem_splitPrime τ)).symm
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  refine (Nat.card_eq_of_bijective (Ideal.quotientMap _ _ hle.le) ⟨Ideal.quotientMap_injective' hle.ge, fun y => ?_⟩).symm
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨a, ha⟩ := ReciprocityTheory.Aut.adic_exists_approx v (τ x) (apply_coe_mem τ x)
  refine ⟨Ideal.Quotient.mk _ a, (Ideal.Quotient.eq.2 ((mem_splitPrime τ _).2 ?_)).symm⟩
  exact ((map_sub τ (x : E) (algebraMap F E a)).trans (congrArg _ (τ.commutes (a : F)))) ▸ ha

theorem exists_conj_place (hc : IsCMExt F E σ) (h : w.under (𝓞 F) = v) (hv : IsSplit (E := E) v) :
    ∃ w' : HeightOneSpectrum (𝓞 E), w ≠ w' ∧ (∀ u, u.under (𝓞 F) = v ↔ u = w ∨ u = w') ∧
      Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal ∧ Ideal.absNorm w'.asIdeal = Ideal.absNorm v.asIdeal ∧
      w'.asIdeal = w.asIdeal.comap (RingOfIntegers.mapRingHom (σ : E →+* E)) := by
  obtain ⟨τ, rfl⟩ := exists_splitPrime_eq hc hv h
  refine ⟨splitPrime (τ.comp σ), (splitPrime_comp_ne hc τ).symm, fun u => ⟨fun hu => ?_, ?_⟩, absNorm_splitPrime τ,
    absNorm_splitPrime _, Ideal.ext (mem_splitPrime_comp τ σ)⟩
  · obtain ⟨ρ, rfl⟩ := exists_splitPrime_eq hc hv hu
    exact (eq_or_eq_comp_conj hc τ ρ).imp (congrArg _) (congrArg _)
  · rintro (rfl | rfl) <;> exact splitPrime_under _

theorem split_chart_and_places (hc : IsCMExt F E σ) (hJ : IsHermND σ J) (hL : L.FG)
    (hL' : Submodule.span E (L : Set (Fin n → E)) = ⊤) (h : w.under (𝓞 F) = v) (hv : IsSplit (E := E) v)
    (hd : IsSelfDualAt σ J L v) :
    (∃ e, IsSplitChart σ J L h e ∧ Continuous e ∧ Continuous e.symm) ∧
      ∃ w' : HeightOneSpectrum (𝓞 E), w ≠ w' ∧ (∀ u, u.under (𝓞 F) = v ↔ u = w ∨ u = w') ∧
        Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal ∧ Ideal.absNorm w'.asIdeal = Ideal.absNorm v.asIdeal ∧
        w'.asIdeal = w.asIdeal.comap (RingOfIntegers.mapRingHom (σ : E →+* E)) :=
  ⟨exists_isSplitChart hc hJ hL hL' h hv hd, exists_conj_place hc h hv⟩

theorem isSplit_of_algHom (hc : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) : IsSplit (E := E) v :=
  ⟨splitPrime (τ.comp σ), splitPrime τ, splitPrime_comp_ne hc τ, Ideal.ext (algebraMap_mem_splitPrime _),
    Ideal.ext (algebraMap_mem_splitPrime _)⟩

theorem exists_isSplitChart_one (hc : IsCMExt F E σ) (n : ℕ) :
    ∃ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (h : w.under (𝓞 F) = v), IsSplit (E := E) v ∧
      ∃ e, IsSplitChart σ (1 : Matrix (Fin n) (Fin n) E) (stdLattice E n) h e ∧ Continuous e ∧ Continuous e.symm := by
  obtain ⟨v, ⟨τ⟩⟩ := exists_split_place hc
  have hL : Submodule.IsLattice E (stdLattice E n) := isLattice_stdLattice
  exact ⟨v, _, splitPrime_under τ, isSplit_of_algHom hc τ, exists_isSplitChart hc (isHermND_one σ n) hL.fg
    hL.span_eq_top _ (isSplit_of_algHom hc τ) (isSelfDualAt_stdLattice_one σ v)⟩

end GlobalTheory.LFun.SplitChart

end
