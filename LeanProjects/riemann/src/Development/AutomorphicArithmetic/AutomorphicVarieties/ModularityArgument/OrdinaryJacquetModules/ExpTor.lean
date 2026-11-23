import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.CoreOrdAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.EpsArt
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.WeilGroupDenseInGaloisGroup
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.SuppFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.PolFacts
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportOfPrincipalSeriesSubquotient

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z UpperTheory.V.Z.Ord

private theorem unit_norm {Γ K : Type} [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ] [NormedField K]
    (χ : Γ →* Kˣ) (hχ : Continuous fun s => (χ s : K)) (s : Γ) : ‖(χ s : K)‖ = 1 := by
  have key : ∀ t, ‖(χ t : K)‖ ≤ 1 := fun t => by
    obtain ⟨C, hC⟩ := (isCompact_range hχ.norm).bddAbove
    refine not_lt.1 fun hlt => ?_
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt C hlt
    have h1 := hC ⟨t ^ m, rfl⟩
    simp only [map_pow, Units.val_pow_eq_pow_val, norm_pow] at h1
    exact absurd hm (not_lt.2 h1)
  refine le_antisymm (key s) ?_
  have h2 := key s⁻¹
  rw [map_inv, Units.val_inv_eq_inv_val, norm_inv] at h2
  exact (inv_le_one₀ (norm_pos_iff.2 (χ s).ne_zero)).1 h2

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem ord_unif : ord k (ImaginaryQuadraticEtaCharacter.unif k) = 1 := by
  have hs := (ImaginaryQuadraticEtaCharacter.polFacts k).1
  obtain ⟨p, hp⟩ := valuation_surjective (uniformizer k : ValueGroupWithZero k)
  exact ord_eq_one (le_antisymm (le_uniformizer_iff.2 hs.1) (hp ▸ hs.2 p (hp ▸ uniformizer_lt_one)))

end Local

section Gal

variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime]
  {w : Plc L} {A : ValuationSubring Ω} {h : IsPlaceOver A w} {a : Weil h →* (w.adicCompletion L)ˣ}

private theorem algPow_add' (d e : (L →+* Qbar l) → ℤ) (x : (w.adicCompletion L)ˣ) :
    algPow w (d + e) (x : w.adicCompletion L) = algPow w d (x : w.adicCompletion L) * algPow w e (x : w.adicCompletion L) := by
  haveI := GlobalTheory.HeckeGal.finite_contEmb (l := l) w
  unfold algPow
  rw [← finprod_mul_distrib (Set.toFinite _) (Set.toFinite _)]
  exact finprod_congr fun j => by rw [Pi.add_apply, zpow_add₀ ((map_ne_zero j.1).2 x.ne_zero)]

private theorem algPow_ne (d : (L →+* Qbar l) → ℤ) (x : (w.adicCompletion L)ˣ) :
    algPow w d (x : w.adicCompletion L) ≠ 0 := by
  haveI := GlobalTheory.HeckeGal.finite_contEmb (l := l) w
  haveI := Fintype.ofFinite (W.Emb l w)
  unfold algPow
  rw [show (∏ᶠ j : {j : w.adicCompletion L →+* Qbar l // Continuous j}, j.1 (x : w.adicCompletion L) ^ d (j.1.comp (algebraMap L (w.adicCompletion L)))) = _ from finprod_eq_prod_of_fintype _]
  exact Finset.prod_ne_zero_iff.2 fun j _ => zpow_ne_zero _ ((map_ne_zero j.1).2 x.ne_zero)

private theorem algPow_nat [Fintype (W.Emb l w)] (d : (L →+* Qbar l) → ℤ) (N : ℕ) (hN : N ≠ 0) :
    algPow w d ((N : ℕ) : w.adicCompletion L) = (N : Qbar l) ^ ∑ j : W.Emb l w, d (j.1.comp (algebraMap L _)) := by
  have h0 : (N : Qbar l) ≠ 0 := Nat.cast_ne_zero.2 hN
  have hp : ∀ (T : Finset (W.Emb l w)) (c : W.Emb l w → ℤ), ∏ j ∈ T, (N : Qbar l) ^ c j = (N : Qbar l) ^ ∑ j ∈ T, c j :=
    fun T c => T.cons_induction (by simp) fun j T hj ih => by rw [Finset.prod_cons, Finset.sum_cons, ih, zpow_add₀ h0]
  unfold algPow
  rw [finprod_eq_prod_of_fintype]
  simp only [map_natCast]
  exact hp _ _

private theorem sum_eq_zero [Fintype (W.Emb l w)] (ha : IsLocalArtin h a) (d : (L →+* Qbar l) → ℤ)
    (χ : Dec (F := L) A →* (Qbar l)ˣ) (hχ : Continuous χ)
    (hv : ∀ s : Weil h, (χ (Subgroup.inclusion (Weil_le_Dec h) s) : Qbar l) = algPow w d (a s : w.adicCompletion L)) :
    ∑ j : W.Emb l w, d (j.1.comp (algebraMap L _)) = 0 := by
  haveI : CompactSpace (Dec (F := L) A) := isCompact_iff_compactSpace.1 (isClosed_Dec A).isCompact
  haveI : CharZero (w.adicCompletion L) := algebraRat.charZero _
  have hl0 : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  obtain ⟨s, hs⟩ := ha.surj (Units.mk0 (l : w.adicCompletion L) (Nat.cast_ne_zero.2 hl0))
  have h1 := unit_norm χ (Units.continuous_val.comp hχ) (Subgroup.inclusion (Weil_le_Dec h) s)
  rw [hv, hs, Units.val_mk0, algPow_nat d l hl0, norm_zpow] at h1
  exact (zpow_eq_one_iff_right₀ (norm_nonneg _) (GlobalTheory.PlaceBridge.norm_l_lt_one (l := l)).ne).1 h1

private theorem gap_zero [Fintype (W.Emb l w)] {n : ℕ} {hh : Fin n → (L →+* Qbar l) → ℤ}
    (hm : ∀ τ, StrictMono fun j => hh j τ) {i j : Fin n}
    (hs : ∑ t : W.Emb l w, (hh j - hh i - 1) (t.1.comp (algebraMap L _)) = 0) (x : w.adicCompletion L) :
    algPow w (hh j - hh i - 1) x = 1 := by
  have key : ∀ t : W.Emb l w, (hh j - hh i - 1) (t.1.comp (algebraMap L _)) = 0 := fun t => by
    rcases lt_or_ge i j with hlt | hge
    · refine (Finset.sum_eq_zero_iff_of_nonneg fun t _ => ?_).1 hs t (Finset.mem_univ _)
      have := hm (t.1.comp (algebraMap L _)) hlt
      simp only [Pi.sub_apply, Pi.one_apply] at this ⊢
      omega
    · have hneg : ∀ t : W.Emb l w, (hh j - hh i - 1) (t.1.comp (algebraMap L _)) < 0 := fun t => by
        have := (hm (t.1.comp (algebraMap L _))).monotone hge
        simp only [Pi.sub_apply, Pi.one_apply] at this ⊢
        omega
      exact absurd hs (Finset.sum_neg (fun t _ => hneg t) ⟨t, Finset.mem_univ _⟩).ne
  exact finprod_eq_one_of_forall_eq_one fun t => by rw [key t, zpow_zero]

end Gal

section Near

open Filter Topology

variable {L : Type} [Field L] [NumberField L] {l : ℕ} [Fact l.Prime] {w : Plc L}

private theorem pow_tendsto (x : w.adicCompletion L) (hx : Valued.v x < 1) :
    Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) := by
  rw [(Valued.hasBasis_nhds_zero _ _).tendsto_right_iff]
  intro γ _
  have hne : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := by simp
  obtain ⟨n, hn⟩ := exists_pow_lt₀ hx (Units.mk0 _ hne)
  filter_upwards [eventually_ge_atTop n] with m hm
  rw [Valuation.restrict_lt_iff_lt_embedding, map_pow]
  exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' hx.le hm) hn

private theorem near_one (hw : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal) {U : Set (w.adicCompletion L)ˣ} (hU : IsOpen U) (h1 : (1 : (w.adicCompletion L)ˣ) ∈ U) :
    ∃ (N : ℕ) (u : (w.adicCompletion L)ˣ), 2 ≤ N ∧ (u : w.adicCompletion L) = (N : w.adicCompletion L) ∧ u ∈ U ∧
      ord (w.adicCompletion L) u = 0 := by
  haveI : CharZero (w.adicCompletion L) := algebraRat.charZero _
  have hv : Valued.v (l : w.adicCompletion L) < 1 := by
    have h4 : Valued.v (algebraMap L (w.adicCompletion L) (((l : ℕ) : 𝓞 L) : L)) < 1 := by
      rw [show Valued.v (algebraMap L (w.adicCompletion L) (((l : ℕ) : 𝓞 L) : L)) =
        w.valuation L (algebraMap (𝓞 L) L ((l : ℕ) : 𝓞 L)) from HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _]
      exact (HeightOneSpectrum.valuation_lt_one_iff_mem w _).2 hw
    simpa using h4
  have hne : ∀ M : ℕ, (((1 + l ^ M : ℕ)) : w.adicCompletion L) ≠ 0 := fun M => Nat.cast_ne_zero.2 (by omega)
  have ht : Tendsto (fun M : ℕ => Units.mk0 _ (hne M)) atTop (𝓝 1) := by
    rw [Units.isEmbedding_val₀.tendsto_nhds_iff]
    have := (pow_tendsto _ hv).const_add (1 : w.adicCompletion L)
    simpa [Function.comp_def] using this
  obtain ⟨M, hM, hMU⟩ := ((eventually_ge_atTop 1).and (ht.eventually (hU.mem_nhds h1))).exists
  have hl : 0 < l ^ M := pow_pos (Fact.out : l.Prime).pos _
  refine ⟨1 + l ^ M, _, by omega, rfl, hMU, ?_⟩
  have hvM : Valued.v ((l : w.adicCompletion L) ^ M) < 1 := by
    rw [map_pow]
    exact pow_lt_one₀ zero_le' hv (by omega)
  rw [SphCompletion.ord_completion, Units.val_mk0]
  push_cast
  rw [Valuation.map_one_add_of_lt _ hvM]
  simp

end Near

section Tw

variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime]
  {w : Plc L} {A : ValuationSubring Ω} {h : IsPlaceOver A w} {a : Weil h →* (w.adicCompletion L)ˣ}

private theorem twist_val (H : GlobalTheory.Published.GlobalArtinReciprocity) (ι : Qbar l ≃+* ℂ) {n : ℕ}
    (hw : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal) (ha : IsLocalArtin h a) {hh : Fin n → (L →+* Qbar l) → ℤ}
    {ω : Fin n → (w.adicCompletion L)ˣ →* ℂˣ} {ψ : Fin n → Dec (F := L) A →* (Qbar l)ˣ}
    (hO : ∀ j, OrdChar ι a (ω j) (hh j) (ψ j)) (i j : Fin n) (s : Weil h) :
    (((ψ i * (ψ j * (cycBar L Ω l).comp (Dec (F := L) A).subtype)⁻¹) (Subgroup.inclusion (Weil_le_Dec h) s) : (Qbar l)ˣ) : Qbar l) *
        (ι.symm (ω j (a s)) * ((normV w : ℕ) : Qbar l) ^ deg s) =
      ι.symm (ω i (a s)) * algPow w (hh j - hh i - 1) (a s : w.adicCompletion L) := by
  set inc := Subgroup.inclusion (Weil_le_Dec h)
  set ε := (cycBar L Ω l).comp (Dec (F := L) A).subtype
  set X := (ψ i * (ψ j * ε)⁻¹) (inc s) with hX
  have hε : (ε (inc s) : Qbar l) = ((normV w : ℕ) : Qbar l) ^ deg s * algPow w 1 (a s : w.adicCompletion L) :=
    UpperTheory.V.Loc.epsArt H h hw a ha s
  have hv : ∀ k, (ψ k (inc s) : Qbar l) = ι.symm (ω k (a s)) * algPow w (-hh k) (a s : w.adicCompletion L) :=
    fun k => (hO k).val s _ rfl (Set.mem_univ _)
  have e00 : ψ i (inc s) = X * (ψ j (inc s) * ε (inc s)) := (inv_mul_cancel_right _ _).symm
  have e0 : (ψ i (inc s) : Qbar l) = (X : Qbar l) * ((ψ j (inc s) : Qbar l) * (ε (inc s) : Qbar l)) := by
    rw [← Units.val_mul, ← Units.val_mul, ← e00]
  have e2 : algPow w (-hh i) (a s : w.adicCompletion L) = algPow w (hh j - hh i - 1) (a s : w.adicCompletion L) *
      (algPow w (-hh j) (a s : w.adicCompletion L) * algPow w 1 (a s : w.adicCompletion L)) := by
    rw [← algPow_add', ← algPow_add']
    congr 1
    ring
  rw [hv, hv, hε, e2] at e0
  refine mul_right_cancel₀ (mul_ne_zero (algPow_ne (-hh j) (a s)) (algPow_ne 1 (a s))) ?_
  linear_combination -e0

private theorem abs_val (ι : Qbar l ≃+* ℂ) (ha : IsLocalArtin h a) (s : Weil h) :
    ι.symm (absPow (w.adicCompletion L) 1 (a s)) = ((normV w : ℕ) : Qbar l) ^ deg s := by
  have := DFunLike.congr_fun (ha.absPow_comp 1) s
  rw [Complex.ofReal_one] at this
  rw [← MonoidHom.comp_apply, this, GlobalTheory.WeilDeligne.unrChar_apply, Units.val_zpow_eq_zpow_val, map_zpow₀]
  simp

private theorem cyc_cont' : Continuous ((cycBar L Ω l).comp (Dec (F := L) A).subtype) :=
  ((Continuous.units_map ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom).toMonoidHom
    ((continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val)).comp (continuous_cycZ L Ω l)).comp continuous_subtype_val

private theorem q_ne : ((normV w : ℕ) : Qbar l) ≠ 0 := Nat.cast_ne_zero.mpr (one_lt_normV w).ne_bot

private theorem link (H : GlobalTheory.Published.GlobalArtinReciprocity) (ι : Qbar l ≃+* ℂ) {n : ℕ}
    (hw : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal) (ha : IsLocalArtin h a) {hh : Fin n → (L →+* Qbar l) → ℤ}
    (hm : ∀ τ, StrictMono fun j => hh j τ) {ω : Fin n → (w.adicCompletion L)ˣ →* ℂˣ}
    {ψ : Fin n → Dec (F := L) A →* (Qbar l)ˣ} (hO : ∀ j, OrdChar ι a (ω j) (hh j) (ψ j)) (i j : Fin n)
    (e : ω i = ω j * absPow (w.adicCompletion L) 1) : ψ i = ψ j * (cycBar L Ω l).comp (Dec (F := L) A).subtype := by
  haveI := GlobalTheory.HeckeGal.finite_contEmb (l := l) w
  haveI := Fintype.ofFinite (W.Emb l w)
  have hc : Continuous (ψ i * (ψ j * (cycBar L Ω l).comp (Dec (F := L) A).subtype)⁻¹) :=
    (hO i).cont.mul ((hO j).cont.mul cyc_cont').inv
  have hx : ∀ s : Weil h, (((ψ i * (ψ j * (cycBar L Ω l).comp (Dec (F := L) A).subtype)⁻¹) (Subgroup.inclusion (Weil_le_Dec h) s) : (Qbar l)ˣ) : Qbar l) =
      algPow w (hh j - hh i - 1) (a s : w.adicCompletion L) := fun s => by
    have h1 := twist_val H ι hw ha hO i j s
    have e' : ω i (a s) = ω j (a s) * absPow (w.adicCompletion L) 1 (a s) := by rw [e]; rfl
    rw [e', Units.val_mul, map_mul, abs_val ι ha] at h1
    exact mul_right_cancel₀ (mul_ne_zero ((map_ne_zero ι.symm).2 (Units.ne_zero _)) (zpow_ne_zero _ q_ne)) (h1.trans (mul_comm _ _))
  have h1 := gap_zero hm (sum_eq_zero ha _ _ hc hx)
  refine mul_inv_eq_one.1 (MonoidHom.ext fun g => Units.ext ?_)
  refine congrFun ((UpperTheory.weil_group_dense_in_galois_group L Ω w A h).equalizer (Units.continuous_val.comp hc) continuous_const
    (funext fun s => ?_)) g
  exact (hx s).trans (h1 _)

private theorem tors (H : GlobalTheory.Published.GlobalArtinReciprocity) (ι : Qbar l ≃+* ℂ) {n : ℕ}
    (hw : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal) (ha : IsLocalArtin h a) {hh : Fin n → (L →+* Qbar l) → ℤ}
    (hm : ∀ τ, StrictMono fun j => hh j τ) {ω : Fin n → (w.adicCompletion L)ˣ →* ℂˣ}
    {ψ : Fin n → Dec (F := L) A →* (Qbar l)ˣ} (hO : ∀ j, OrdChar ι a (ω j) (hh j) (ψ j)) (i j : Fin n) (m : ℕ) (hm1 : 1 ≤ m)
    (e : ψ i ^ m = (ψ j * (cycBar L Ω l).comp (Dec (F := L) A).subtype) ^ m) :
    ‖((ω j (ImaginaryQuadraticEtaCharacter.unif (w.adicCompletion L)) : ℂˣ) : ℂ)‖ = (normV w : ℝ) * ‖((ω i (ImaginaryQuadraticEtaCharacter.unif (w.adicCompletion L)) : ℂˣ) : ℂ)‖ := by
  haveI := GlobalTheory.HeckeGal.finite_contEmb (l := l) w
  haveI := Fintype.ofFinite (W.Emb l w)
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = ψ i * (ψ j * (cycBar L Ω l).comp (Dec (F := L) A).subtype)⁻¹ := ⟨_, rfl⟩
  have hρm : ∀ g, ((ρ g : (Qbar l)ˣ) : Qbar l) ^ m = 1 := fun g => by
    have h1 : ρ ^ m = 1 := by rw [hρ, mul_pow, inv_pow, e, mul_inv_cancel]
    have h2 := DFunLike.congr_fun h1 g
    rw [MonoidHom.pow_apply, MonoidHom.one_apply] at h2
    rw [← Units.val_pow_eq_pow_val, h2, Units.val_one]
  obtain ⟨N, u, hN, hu, huU, hu0⟩ := near_one hw (IsOpen.inter (hO i).smooth (hO j).smooth) ⟨one_mem _, one_mem _⟩
  obtain ⟨s, hs⟩ := ha.surj u
  have hd : deg s = 0 := by
    have := ha.ord_eq s
    rw [hs, hu0] at this
    omega
  have h1 := twist_val H ι hw ha hO i j s
  have hiu : ω i u = 1 := huU.1
  have hju : ω j u = 1 := huU.2
  rw [← hρ, hs, hiu, hju, hd, hu, algPow_nat _ N (by omega)] at h1
  simp only [Units.val_one, map_one, zpow_zero, mul_one, one_mul] at h1
  have h3 : ∑ t : W.Emb l w, (hh j - hh i - 1) (t.1.comp (algebraMap L _)) = 0 := by
    have h2 := hρm (Subgroup.inclusion (Weil_le_Dec h) s)
    rw [h1] at h2
    have h5 := congrArg (fun z => ‖ι z‖) h2
    simp only [map_pow, map_zpow₀, map_natCast, map_one, norm_pow, norm_zpow, norm_one, Complex.norm_natCast] at h5
    have h6 := (pow_eq_one_iff_of_nonneg (zpow_nonneg (Nat.cast_nonneg _) _) (by omega)).1 h5
    exact (zpow_eq_one_iff_right₀ (Nat.cast_nonneg _) (by exact_mod_cast (by omega : N ≠ 1))).1 h6
  have hone := gap_zero hm h3
  obtain ⟨s0, hs0⟩ := ha.surj (ImaginaryQuadraticEtaCharacter.unif (w.adicCompletion L))
  have hd0 : deg s0 = -1 := by
    have := ha.ord_eq s0
    rw [hs0, ord_unif] at this
    omega
  have h4 := twist_val H ι hw ha hO i j s0
  rw [← hρ, hs0, hd0, hone, mul_one, zpow_neg_one] at h4
  have h5 := congrArg (fun z => ‖ι z‖) h4
  simp only [map_mul, map_inv₀, map_natCast, RingEquiv.apply_symm_apply, norm_mul, norm_inv, Complex.norm_natCast] at h5
  have h6 : ‖ι ((ρ (Subgroup.inclusion (Weil_le_Dec h) s0) : (Qbar l)ˣ) : Qbar l)‖ = 1 :=
    Complex.norm_eq_one_of_pow_eq_one (n := m) (by rw [← map_pow, hρm, map_one]) (by omega)
  rw [h6, one_mul] at h5
  have hq : (normV w : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (one_lt_normV w).ne_bot
  rw [← h5]
  field_simp

end Tw

section Top

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
  {w : HeightOneSpectrum (𝓞 F)} {A : ValuationSubring Ω} {h : IsPlaceOver A w} {a : Weil h →* (w.adicCompletion F)ˣ}

private theorem normV_absNorm : normV w = Ideal.absNorm w.asIdeal := by
  rw [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]

private theorem abs_unif (ι : Qbar l ≃+* ℂ) (ha : IsLocalArtin h a) :
    ((absPow (w.adicCompletion F) 1 (ImaginaryQuadraticEtaCharacter.unif (w.adicCompletion F)) : ℂˣ) : ℂ) = ((normV w : ℕ) : ℂ)⁻¹ := by
  obtain ⟨s0, hs0⟩ := ha.surj (ImaginaryQuadraticEtaCharacter.unif (w.adicCompletion F))
  have hd0 : deg s0 = -1 := by
    have := ha.ord_eq s0
    rw [hs0, ord_unif] at this
    omega
  have h1 := congrArg ι (abs_val ι ha s0)
  rw [hs0, hd0, ι.apply_symm_apply, zpow_neg_one, map_inv₀, map_natCast] at h1
  exact h1

private theorem supp_ps [IsTotallyComplex F] {n : ℕ} (hn : 1 ≤ n) (π : CuspSub F n) {ω : Fin n → (w.adicCompletion F)ˣ →* ℂˣ}
    (hs : ∀ i, IsSmoothChar (ω i)) (hσ : ∀ σ, π.IsLocComp w σ → IsSubquotient σ.ρ (PS ω)) :
    Gam.TorAt π w ∧ ∀ s, Gam.SuppAt π w s → (∀ i, ω i * absPow (w.adicCompletion F) (((n : ℂ) - 1) / 2) ∈ ImaginaryQuadraticEtaCharacter.chars s) ∧
      ∀ ξ ∈ ImaginaryQuadraticEtaCharacter.chars s, ∃ i, ξ = ω i * absPow (w.adicCompletion F) (((n : ℂ) - 1) / 2) := by
  haveI : CharZero (w.adicCompletion F) := algebraRat.charZero _
  have hμ : ∀ i, IsSmoothChar (ω i * absPow (w.adicCompletion F) (((n : ℂ) - 1) / 2)) :=
    fun i => (hs i).mul (isSmoothChar_absPow _)
  have key : ∀ σ, π.IsLocComp w σ → HasSupport σ.ρ (Finset.univ.val.map fun i => IrrGL.ofChar _ (hμ i)) := fun σ h1 =>
    hasSupport_of_isSubquotient_prinSeries (w.adicCompletion F) n _ hμ ⟨_, σ.ρ, σ.smooth, σ.irred⟩ (hσ σ h1)
  refine ⟨fun σ h1 => ⟨_, (key σ h1).of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred), fun y hy => ?_⟩, fun s ⟨σ, h1, h2⟩ => ?_⟩
  · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hy
    rfl
  · obtain rfl := (Gam.suppFacts F n hn π w).2.1 s _ ⟨σ, h1, h2⟩ ⟨σ, h1, key σ h1⟩
    refine ⟨fun i => ⟨hμ i, Multiset.mem_map.2 ⟨i, Finset.mem_univ_val _, rfl⟩⟩, fun ξ ⟨hξ, hm⟩ => ?_⟩
    obtain ⟨i, -, e⟩ := Multiset.mem_map.1 hm
    exact ⟨i, ((ImaginaryQuadraticEtaCharacter.polFacts _).2.2.1 _ _ _ _ e).symm⟩

end Top
