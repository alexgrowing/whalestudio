import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitarySphericalReps
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TrivialParameterBound
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SatakeTrivialRangeBound
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BcParamEqOfSatUEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenIsCompactLevelOffFinEmpty
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedConjugatePlaceUniformiser
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuadraticUnramifiedIffInertOrSplit
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdmissibleUnitaryConjugateDualStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SemilinearEquivPreservesPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeActsByScalarCommutativeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SatakeParameterOfSphericalStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSatakeParameterSphericalUnramifiedUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitarySatakeTransformStarParameterEqOfUnitarisaStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormSatakeLeOfUnitarySphericalGLStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SatakeParameterGLStarEqInvOfUnitarisableStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuadraticPowerCharacterSplitPlacesValuesInverseStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SqValueEqOneAtInertPlaceOfRestrictsToQuadraticStatement

noncomputable section

namespace GlobalTheory.LPositivity

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.UnitarySphericalReps
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)

section Analysis

theorem isPosReal_iff {z : ℂ} : IsPosReal z ↔ ∃ r : ℝ, 0 < r ∧ z = r :=
  ⟨fun h => ⟨z.re, h.2, Complex.ext rfl (by simpa using h.1)⟩, by rintro ⟨r, hr, rfl⟩; exact ⟨rfl, hr⟩⟩

theorem isPosReal_prod {ι : Type} (s : Finset ι) {f : ι → ℂ} (h : ∀ i ∈ s, IsPosReal (f i)) :
    IsPosReal (∏ i ∈ s, f i) := by
  refine Finset.prod_induction f IsPosReal (fun a b ha hb => ?_) ⟨rfl, one_pos⟩ h
  obtain ⟨x, hx, rfl⟩ := isPosReal_iff.1 ha
  obtain ⟨y, hy, rfl⟩ := isPosReal_iff.1 hb
  exact isPosReal_iff.2 ⟨x * y, mul_pos hx hy, by simp⟩

theorem isPosReal_of_hasProd {ι : Type} {f : ι → ℂ} {a : ℂ} (ha : HasProd f a) (h0 : a ≠ 0)
    (h : ∀ i, IsPosReal (f i)) : IsPosReal a := by
  have hc : IsClosed {z : ℂ | z.im = 0 ∧ 0 ≤ z.re} :=
    (isClosed_eq Complex.continuous_im continuous_const).inter (isClosed_le continuous_const Complex.continuous_re)
  have := hc.mem_of_tendsto ha (Eventually.of_forall fun s =>
    ⟨(isPosReal_prod s fun i _ => h i).1, (isPosReal_prod s fun i _ => h i).2.le⟩)
  exact ⟨this.1, this.2.lt_of_ne fun e => h0 (Complex.ext e.symm this.1)⟩

theorem isPosReal_eulerFac {B : Multiset ℂˣ} {x : ℂ} (hB : B.map star = B) (hx : star x = x)
    (h : ∀ b ∈ B, ‖(b : ℂ) * x‖ < 1) : IsPosReal (eulerFac B x) := by
  have hre : ∀ b ∈ B, 0 < (1 - (b : ℂ) * x).re := fun b hb => by
    have := (Complex.re_le_norm _).trans_lt (h b hb)
    rw [Complex.sub_re, Complex.one_re]
    linarith
  set u : ℂ := (B.map fun b : ℂˣ => Complex.log (1 - (b : ℂ) * x)).sum with hu
  have h1 : eulerPoly B x = Complex.exp u := by
    rw [hu, Complex.exp_multiset_sum, Multiset.map_map, eulerPoly]
    refine congrArg _ (Multiset.map_congr rfl fun b hb => (Complex.exp_log fun e => ?_).symm)
    simpa [e] using hre b hb
  have h2 : starRingEnd ℂ u = u := by
    conv_rhs => rw [hu, ← hB, Multiset.map_map]
    rw [hu, map_multiset_sum, Multiset.map_map]
    refine congrArg _ (Multiset.map_congr rfl fun b hb => ?_)
    have h3 : (1 - (b : ℂ) * x).arg ≠ Real.pi := fun e => by
      have := (Complex.arg_eq_pi_iff.1 e).1
      linarith [hre b hb]
    simp only [Function.comp_apply, Units.coe_star]
    rw [← Complex.log_conj _ h3, map_sub, map_one, map_mul, show starRingEnd ℂ x = x from hx]
    rfl
  obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 h2
  exact isPosReal_iff.2 ⟨(Real.exp r)⁻¹, by positivity, by rw [eulerFac, h1, hr]; simp⟩

variable {K : Type} [Field K] [NumberField K]

theorem star_npow (w : HeightOneSpectrum (𝓞 K)) (s : ℝ) : star (npow w (-(s : ℂ))) = npow w (-(s : ℂ)) := by
  rw [npow, ← Complex.ofReal_neg, ← Complex.ofReal_natCast, ← Complex.ofReal_cpow (Nat.cast_nonneg _)]
  exact Complex.conj_ofReal _

theorem norm_lt_one_of_bounded {T : Set (HeightOneSpectrum (𝓞 K))} {c : Fam K} {r : ℕ} {κ : ℝ} (h : Bounded T c r κ)
    {s : ℂ} (hs : κ < s.re) {w : HeightOneSpectrum (𝓞 K)} (hw : w ∉ T) :
    ∀ b ∈ c w, ‖(b : ℂ) * npow w (-s)‖ < 1 := fun _ hb =>
  (h.norm_le le_rfl hw hb).trans_lt
    (Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast one_lt_absNorm w) (by linarith))

theorem summable_norm_mul {ι : Type} {a g : ι → ℂ} {c : ℂ} (ha : Summable fun i => ‖a i‖)
    (hg : Tendsto g cofinite (𝓝 c)) : Summable fun i => ‖a i * g i‖ := by
  refine summable_of_isBigO ha ?_
  simpa using ((Asymptotics.isBigO_refl a cofinite).mul (hg.isBigO_one ℂ)).norm_norm

theorem tendsto_one_of_summable {ι : Type} {g : ι → ℂ} (hg : Summable fun i => ‖g i - 1‖) :
    Tendsto g cofinite (𝓝 1) := tendsto_iff_norm_sub_tendsto_zero.2 hg.tendsto_cofinite_zero

theorem summable_locL {T : Set (HeightOneSpectrum (𝓞 K))} {c : Fam K} {s : ℂ} (h : Converges T c s) :
    Summable fun w : {w // w ∉ T} => ‖locL c w s - 1‖ := by
  refine (summable_norm_mul h.2 ((tendsto_one_of_summable h.2).inv₀ one_ne_zero)).congr fun w => ?_
  rw [sub_mul, mul_inv_cancel₀ (h.1 w w.2), one_mul, norm_sub_rev]
  rfl

theorem summable_prod {ι κ : Type} (s : Finset κ) {f : κ → ι → ℂ} (h : ∀ k ∈ s, Summable fun i => ‖f k i - 1‖) :
    Summable fun i => ‖∏ k ∈ s, f k i - 1‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [summable_zero]
  | insert k s hk ih =>
    have h1 := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    have h2 := h k (Finset.mem_insert_self _ _)
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => ?_)
      ((summable_norm_mul h2 (tendsto_one_of_summable h1)).add h1)
    rw [Finset.prod_insert hk]
    exact (congrArg _ (by ring)).trans_le (norm_add_le _ _)

end Analysis

section Normalising

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem isPosReal_etaL (S : Set (HeightOneSpectrum (𝓞 F))) (k : ℕ) {s : ℝ} (hs : 1 < s) :
    IsPosReal (etaL E S k s) := by
  have hc : Converges S (etaFam E k) s := converges_etaFam S k hs
  refine isPosReal_of_hasProd hc.hasProd hc.ne_zero fun v => isPosReal_eulerFac ?_ (star_npow _ _)
    (norm_lt_one_of_bounded (bounded_etaFam S k) (zero_lt_one.trans hs) v.2)
  unfold etaFam etaU
  have : star (-1 : ℂˣ) = -1 := Units.ext (by simp)
  split_ifs <;> simp [this]

theorem dPositive (D : Formalism.BasicNotions.D7) : DPositive D := by
  intro S a t ht
  have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hc : ∀ i < a, Converges (S : Set (HeightOneSpectrum (𝓞 D.host.F))) (etaFam D.host.E (a + t + i))
      (2 * ((((a + t : ℕ) : ℂ) - a) / 2) + a - i) := fun i hi => converges_etaFam _ _ (by
    have : (i : ℝ) + 1 ≤ a := by exact_mod_cast hi
    simp
    linarith)
  refine ⟨hc, summable_prod _ fun i hi => summable_locL (hc i (Finset.mem_range.1 hi)), ?_⟩
  rw [(dS_eq _ a ht).1]
  refine isPosReal_prod _ fun k hk => ?_
  have := (Finset.mem_Icc.1 hk).1
  exact isPosReal_etaL _ k (s := k) (by exact_mod_cast (by omega : 1 < k))

end Normalising

section Transport

variable {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

theorem irreducible_comp (e : G ≃* H) (h : ρ.IsIrreducible) :
    Representation.IsIrreducible (ρ.comp e.symm.toMonoidHom) := by
  let f : Subrepresentation (ρ.comp e.symm.toMonoidHom) ≃o Subrepresentation ρ :=
    { toFun := fun S => ⟨S.toSubmodule, fun g x hx => by simpa using S.apply_mem_toSubmodule (e g) hx⟩
      invFun := fun S => ⟨S.toSubmodule, fun g x hx => S.apply_mem_toSubmodule (e.symm g) hx⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  exact f.isSimpleOrder

theorem unitarisable_comp (e : G ≃* H) (h : GlobalTheory.LGrp.IsUnitarisable ρ) :
    GlobalTheory.LGrp.IsUnitarisable (ρ.comp e.symm.toMonoidHom) :=
  h.imp fun _ hB => ⟨hB.1, hB.2.1, fun g => hB.2.2 (e.symm g)⟩

theorem fixed_comp (e : G ≃* H) {K : Subgroup G} {K' : Subgroup H} (hK : ∀ g, g ∈ K ↔ e g ∈ K') :
    fixed (ρ.comp e.symm.toMonoidHom) K' = fixed ρ K := Submodule.ext fun _ => mem_fixed_comp_symm e hK

theorem smooth_comp [TopologicalSpace G] [TopologicalSpace H] (e : G ≃* H) (he : Continuous e.symm)
    (h : IsSmooth ρ) : IsSmooth (ρ.comp e.symm.toMonoidHom) := fun x => (h x).preimage he

theorem admissible_comp [TopologicalSpace G] [TopologicalSpace H] (e : G ≃* H) (he : Continuous e)
    (he' : Continuous e.symm) (h : IsAdmissible ρ) : IsAdmissible (ρ.comp e.symm.toMonoidHom) := by
  refine ⟨smooth_comp e he' h.1, fun K ho hk => ?_⟩
  rw [fixed_comp e (K := K.comap e.toMonoidHom) fun _ => Iff.rfl]
  refine h.2 _ (ho.preimage he) ?_
  convert hk.image he' using 1
  exact (e.toEquiv.image_symm_eq_preimage _).symm

end Transport

section Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)}
  {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} {h : w.under (𝓞 F) = v}
  {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ (GLoc σ J v) V} {B : Multiset ℂˣ}
  (hc : IsCMExt F E σ) (hJ : IsHermND σ J) (hL : Submodule.IsLattice E L) (hd : IsSelfDualAt σ J L v)

include hc hJ hL hd

theorem exists_inert_chart (h : w.under (𝓞 F) = v) (hv : IsInertAt F E v w) :
    ∃ c ϖ e, IsUnramInv ϖ c (qV F v) ∧ IsInertChart σ J L h c e ∧ Continuous e ∧ Continuous e.symm := by
  obtain ⟨-, ⟨c, hcj, -⟩, -, -, H⟩ := (exists_isInertChart σ hc v).2 w h hv
  obtain ⟨⟨ϖ, hU⟩, H⟩ := H c hcj
  obtain ⟨e, he⟩ := H n J L hJ hL.fg hL.span_eq_top hd
  exact ⟨c, ϖ, e, hU, he⟩

theorem exists_hasParam (h : w.under (𝓞 F) = v) (hv : IsSplit (E := E) v ∨ IsInertAt F E v w)
    (hi : ρ.IsIrreducible) (ha : IsAdmissible ρ) (hs : GlobalTheory.LGrp.IsSpherical ρ (stabLoc σ J L v)) :
    ∃ B, HasParam σ J L h ρ B := by
  have hf := ha.2 _ (isOpen_stabLoc σ J L v) (isCompact_stabLoc σ J L v)
  rcases hv with hv | hv
  · obtain ⟨e, he, -⟩ := SplitChart.exists_isSplitChart hc hJ hL.fg hL.span_eq_top h hv hd
    obtain ⟨B, hB⟩ := GlobalTheory.T.satake_parameter_of_spherical E w n V (ρ.comp e.symm.toMonoidHom)
      (fun e0 => hs ((fixed_comp e he.2).symm.trans e0))
      (GlobalTheory.T.hecke_acts_by_scalar_commutative _ _ (Final.GLintComm E w n) (Final.HeckeCommGL E w n ℂ) V _ (irreducible_comp e hi)
        (by rw [fixed_comp e he.2]; exact hf))
    exact ⟨B, Or.inl ⟨hv, e, he, hB⟩⟩
  · obtain ⟨c, ϖ, e, hU, he, h1, h2⟩ := exists_inert_chart hc hJ hL hd h hv
    obtain ⟨α, hα⟩ := GlobalTheory.T.exists_satake_parameter_spherical_unramifiedUnitary E w ϖ c _ n hU V (ρ.comp e.symm.toMonoidHom) (irreducible_comp e hi)
      (admissible_comp e h1 h2 ha) fun e0 => hs ((fixed_comp e he.2.2).symm.trans e0)
    exact ⟨_, Or.inr ⟨hv, c, ϖ, e, α, hU, he, hα, rfl⟩⟩

theorem norm_le_of_hasParam (h1 : GlobalTheory.IndefiniteRowSideFullHecke.SatakeTrivialRangeBound.SatakeTrivialBound) (h2 : GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.SatakeBoundInert)
    (hi : ρ.IsIrreducible) (ha : IsSmooth ρ) (hu : GlobalTheory.LGrp.IsUnitarisable ρ) (hB : HasParam σ J L h ρ B) :
    ∀ b ∈ B, ‖(b : ℂ)‖ ≤ ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (((n : ℝ) - 1) / 2) := by
  have hB' := hB
  rcases hB' with ⟨hv, -⟩ | ⟨hv, c', ϖ, e', α, hU, he', hα, rfl⟩
  · obtain ⟨e, he, -, hce⟩ := SplitChart.exists_isSplitChart hc hJ hL.fg hL.span_eq_top h hv hd
    refine GlobalTheory.T.norm_satake_le_of_unitary_spherical_GL h1 E w n V (ρ.comp e.symm.toMonoidHom) B ⟨smooth_comp e hce ha, irreducible_comp e hi⟩
      (unitarisable_comp e hu) ⟨fun e0 => hB.isSpherical ((fixed_comp e he.2).symm.trans e0), fun x hx h0 => ?_⟩
    exact (hB.isParamVec ((mem_fixed_comp_symm e he.2).1 hx) h0).isSatVecGL hv he
  · obtain ⟨c, -, e, -, he, -, hce⟩ := exists_inert_chart hc hJ hL hd h hv
    obtain rfl : c = c' := he.1.unique he'.1
    have hb := h2 _ ϖ c _ n hU V (ρ.comp e.symm.toMonoidHom) α ⟨smooth_comp e hce ha, irreducible_comp e hi⟩
      (unitarisable_comp e hu) ⟨fun e0 => hB.isSpherical ((fixed_comp e he.2.2).symm.trans e0), fun x hx h0 =>
        IsSatVecU.of_chart he' he
          (hα.2 x ((mem_fixed_comp_symm e' he'.2.2).2 ((mem_fixed_comp_symm e he.2.2).1 hx)) h0)⟩
    have hN : Ideal.absNorm w.asIdeal = qV F v ^ 2 := InertChart.absNorm_eq hc.2.2.1 hv
    have hq : (1 : ℝ) ≤ (qV F v : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast (one_lt_absNorm v).le)
    rw [hN, Nat.cast_pow]
    intro b hb'
    simp only [bcParam, Multiset.mem_add, Multiset.mem_map, Multiset.mem_replicate] at hb'
    rcases hb' with (⟨i, -, rfl⟩ | ⟨i, -, rfl⟩) | ⟨hn, rfl⟩
    · exact (hb i).2
    · have := (hb i).1
      rw [Real.rpow_neg (by positivity)] at this
      rw [Units.val_inv_eq_inv_val, norm_inv]
      exact inv_le_of_inv_le₀ (by positivity) this
    · have : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
      simpa using Real.one_le_rpow hq (by linarith)

theorem param_conj_place {w' : HeightOneSpectrum (𝓞 E)} {h' : w'.under (𝓞 F) = v} (hne : w ≠ w') {B' : Multiset ℂˣ}
    (hu : GlobalTheory.LGrp.IsUnitarisable ρ) (hB : HasParam σ J L h ρ B) (hB' : HasParam σ J L h' ρ B') :
    B' = B.map star := by
  have hv : IsSplit (E := E) v := ⟨w, w', hne, congrArg (·.asIdeal) h, congrArg (·.asIdeal) h'⟩
  obtain ⟨x, hx⟩ := hB.exists_vec
  obtain ⟨e, he, -⟩ := SplitChart.exists_isSplitChart hc hJ hL.fg hL.span_eq_top h hv hd
  rw [GlobalTheory.T.satakeParameterGL_star_eq_inv_of_unitarisable E w n V _ x B (unitarisable_comp e hu) (hx.isSatVecGL hv he)]
  exact ConjPlace.eq_map_inv_of_hasParam hc hJ hd hne hB hB'

omit hc hJ hL hd in

theorem param_star_of_inert (hv : IsInertAt F E v w) (hu : GlobalTheory.LGrp.IsUnitarisable ρ) (hB : HasParam σ J L h ρ B) :
    B.map star = B := by
  rcases hB with ⟨hv', -⟩ | ⟨-, c, ϖ, e, α, hU, he, hα, rfl⟩
  · exact absurd hv' (not_isSplit_of_isInertAt hv)
  · obtain ⟨x, hx⟩ := hα.exists_vec
    conv_rhs => rw [← bcParam_eq_of_satU_eq (α := fun i => star (α i)) hU
      (GlobalTheory.T.unitarySatakeTransform_star_parameter_eq_of_unitarisable _ ϖ c _ n hU V _ x α (unitarisable_comp e hu) hx)]
    simp [bcParam, star_inv, Function.comp_def]

end Local

section Global

open Formalism.BasicNotions Formalism.BasicNotions.TH

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem split_or_inert (D : D7) (w : HeightOneSpectrum (𝓞 D.host.E)) :
    IsSplit (E := D.host.E) (w.under (𝓞 D.host.F)) ∨ IsInertAt D.host.F D.host.E (w.under (𝓞 D.host.F)) w := by
  haveI := D.host.isCMField_hostE
  haveI := GlobalTheory.PlaceComp.unramified (E := D.host.E) D.sp.cm
  set v := w.under (𝓞 D.host.F) with hv
  rcases (GlobalTheory.quadratic_unramified_iff_inert_or_split D.host.F D.host.E (isCMExt_host D).2.2.1 v).1
    (fun u _ => Algebra.unramified_iff_forall.1 inferInstance ⟨u.asIdeal, u.isPrime⟩) with h | h
  · exact Or.inr ((h.isMaximal (Ideal.map_ne_bot_of_ne_bot v.ne_bot)).eq_of_le w.isPrime.ne_top Ideal.map_comap_le)
  · obtain ⟨P, Q, hne, e⟩ := Set.ncard_eq_two.1 h
    have hP : P ∈ v.asIdeal.primesOver (𝓞 D.host.E) := by simp [e]
    have hQ : Q ∈ v.asIdeal.primesOver (𝓞 D.host.E) := by simp [e]
    have := hP.2
    have := hQ.2
    exact Or.inl ⟨⟨P, hP.1, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩,
      ⟨Q, hQ.1, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, fun e => hne (congrArg (·.asIdeal) e),
      hP.2.over.symm, hQ.2.over.symm⟩

variable {D : D7} {V : HSp D}

theorem isUnitarySph_smoothDual {v : HeightOneSpectrum (𝓞 D.host.F)} {X : Type} [AddCommGroup X] [Module ℂ X]
    {ρ : Representation ℂ (Gv V v) X} (h : IsUnitarySph V v ρ) : IsUnitarySph V v (GlobalTheory.LGrp.smoothDual ρ) := by
  have := SelfDual.isLattice_frameLat V
  obtain ⟨φ, h1, h2⟩ := GlobalTheory.T.admissible_unitary_conjugate_dual _ (Kv V v) (isOpen_stabLoc _ _ _ v) (isCompact_stabLoc _ _ _ v) X ρ h.adm h.unitary
  obtain ⟨a, b, c, d⟩ := GlobalTheory.T.semilinear_equiv_preserves_properties _ (Kv V v) X _ ρ _ φ h1 h2
  exact ⟨a h.irred, b h.adm, c h.unitary, d h.sph⟩

theorem star_eq_inv {z : ℂˣ} (h : ‖(z : ℂ)‖ = 1) : star z = z⁻¹ :=
  Units.ext (by simpa using (Complex.inv_eq_conj h).symm)

theorem lConvPos (h1 : GlobalTheory.IndefiniteRowSideFullHecke.SatakeTrivialRangeBound.SatakeTrivialBound) (h2 : GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.SatakeBoundInert)
    {S : Finset (HeightOneSpectrum (𝓞 D.host.F))} {X : HeightOneSpectrum (𝓞 D.host.F) → Type}
    [∀ v, AddCommGroup (X v)] [∀ v, Module ℂ (X v)] {π : ∀ v, Representation ℂ (Gv V v) (X v)}
    {μ : (Formalism.L2.Theta.AE D)ˣ →* Circle} (hπ : ∀ v ∉ S, IsUnitarySph V v (π v))
    (hμ : UnrOff μ (S : Set (HeightOneSpectrum (𝓞 D.host.F)))) {b : ℕ} (hb : Formalism.L2.Theta.ResEta D μ b) :
    LConvPos V S π μ := by
  classical
  have hc := isCMExt_host D
  have hJ := GlobalTheory.Mem.VolExists.isHermND D.sp.cm V
  have hL := SelfDual.isLattice_frameLat V
  have hd := SelfDual.isSelfDualAt_frameLat D V
  refine ⟨⟨paramFam D.sp.cm.sig V.gram (frameLat V) π, fun v hv w h => ?_⟩, fun c hπc => ?_⟩
  · subst h
    obtain ⟨B, hB⟩ := exists_hasParam hc hJ hL (hd _) rfl (split_or_inert D w) (hπ _ hv).irred (hπ _ hv).adm
      (hπ _ hv).sph
    exact hB.hasParam_paramOf
  have hbd : Bounded (above D.host.E (S : Set (HeightOneSpectrum (𝓞 D.host.F)))) c V.rank
      (((V.rank : ℝ) - 1) / 2) := fun w hw => ⟨(hπc.card hw).le, norm_le_of_hasParam hc hJ hL (hd _) h1 h2
        (hπ _ hw).irred (hπ _ hw).adm.1 (hπ _ hw).unitary (hπc _ hw w rfl)⟩
  have hcv : ∀ s : ℂ, ((V.rank : ℝ) + 1) / 2 < s.re →
      Converges (above D.host.E (S : Set (HeightOneSpectrum (𝓞 D.host.F)))) (twist c (val μ)⁻¹) s :=
    fun s hs => hbd.converges_twist_val μ (by linarith)
  refine ⟨hcv, fun s hs => isPosReal_of_hasProd (hasProd_Lv (hcv s hs)) (hcv s hs).ne_zero fun v => ?_⟩
  have hlt : ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v.1 →
      ∀ x ∈ twist c (val μ)⁻¹ w, ‖(x : ℂ) * npow w (-(s : ℂ))‖ < 1 := fun w hw =>
    norm_lt_one_of_bounded (hbd.twist fun u _ => by simp [norm_val]) (by rw [Complex.ofReal_re]; linarith)
      (fun e => v.2 (hw ▸ e))
  have hun : ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v.1 → UnrAt μ w := fun w hw =>
    hμ w fun e => v.2 (hw ▸ e)
  by_cases hv : IsSplit (E := D.host.E) v.1
  · obtain ⟨w, hw⟩ : ∃ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v.1 := by
      obtain ⟨P, -, -, hP, -⟩ := hv
      exact ⟨P, HeightOneSpectrum.ext hP⟩
    obtain ⟨w', hne, hall, hN, hN', -⟩ := SplitChart.exists_conj_place hc hw hv
    have hw' := (hall w').2 (Or.inr rfl)
    have e : Formalism.L2.Host.aboveF (L := D.host.E) D.host.F v.1 = {w, w'} := by ext u; simp [mem_aboveF, hall]
    have e2 : npow w' (-(s : ℂ)) = npow w (-(s : ℂ)) := by rw [npow, npow, hN, hN']
    have e3 : twist c (val μ)⁻¹ w' = (twist c (val μ)⁻¹ w).map star := by
      have hm := GlobalTheory.T.quadraticPowerCharacter_splitPlaces_values_inverse _ _ _ hc μ b hb w w' (hw.trans hw'.symm) hne (hun w hw) (hun w' hw')
      have hs : (val μ w')⁻¹ = star (val μ w)⁻¹ := by
        rw [star_inv, star_eq_inv (norm_val μ w), inv_inv, eq_comm, eq_inv_iff_mul_eq_one, hm]
      simp only [twist, Pi.inv_apply, hs, Multiset.map_map, Function.comp_def, star_mul',
        param_conj_place hc hJ hL (hd _) hne (hπ _ v.2).unitary (hπc _ v.2 w hw) (hπc _ v.2 w' hw')]
    rw [Lv, e, Finset.prod_pair hne, locL, locL, e2, ← eulerFac_add]
    refine isPosReal_eulerFac (by
      rw [e3, Multiset.map_add, Multiset.map_map, add_comm]
      simp only [Function.comp_def, star_star, Multiset.map_id']) (star_npow _ _) fun x hx => ?_
    exact (Multiset.mem_add.1 hx).elim (hlt w hw x) (e2 ▸ hlt w' hw' x)
  · refine isPosReal_prod _ fun w hw => ?_
    have hw := mem_aboveF.1 hw
    have hi : IsInertAt D.host.F D.host.E v.1 w := hw ▸ (split_or_inert D w).resolve_left (hw ▸ hv)
    refine isPosReal_eulerFac ?_ (star_npow _ _) (hlt w hw)
    have hs : star (val μ w)⁻¹ = (val μ w)⁻¹ := by
      rw [star_inv, star_eq_inv (norm_val μ w), inv_inv, eq_inv_iff_mul_eq_one, ← sq,
        GlobalTheory.T.sq_value_eq_one_at_inert_place_of_restrictsToQuadratic _ _ _ hc μ b hb _ w hi (hun w hw)]
    conv_rhs => rw [twist, ← param_star_of_inert hi (hπ _ v.2).unitary (hπc _ v.2 w hw)]
    simp only [twist, Pi.inv_apply, hs, Multiset.map_map, Function.comp_def, star_mul']

end Global

theorem statement_of_bounds (h1 : GlobalTheory.IndefiniteRowSideFullHecke.SatakeTrivialRangeBound.SatakeTrivialBound) (h2 : GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.SatakeBoundInert) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitarySphericalReps.Statement := fun D =>
  ⟨fun _ _ _ _ _ _ _ hπ _ hμ ⟨_, hb⟩ =>
    ⟨lConvPos h1 h2 hπ hμ hb, lConvPos h1 h2 (fun v hv => isUnitarySph_smoothDual (hπ v hv)) hμ hb⟩, dPositive D⟩

end GlobalTheory.LPositivity

end
