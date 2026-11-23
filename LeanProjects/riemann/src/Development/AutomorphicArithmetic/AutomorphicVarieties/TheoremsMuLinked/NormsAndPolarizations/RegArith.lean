import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.CjApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.EpsArt
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaArtinLit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDEqSumOfAgree
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.WtBridge
open IsLocalRing Matrix NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th UpperTheory.V.Th.Nm GlobalTheory.GalOfCusp

private theorem norm_one {Γ K : Type} [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ] [NormedField K]
    (ψ : Γ →* Kˣ) (hψ : Continuous fun s => (ψ s : K)) (s : Γ) : ‖(ψ s : K)‖ = 1 := by
  have key : ∀ t, ‖(ψ t : K)‖ ≤ 1 := fun t => by
    obtain ⟨C, hC⟩ := (isCompact_range hψ.norm).bddAbove
    refine not_lt.1 fun hlt => ?_
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt C hlt
    have h1 := hC ⟨t ^ m, rfl⟩
    simp only [map_pow, Units.val_pow_eq_pow_val, norm_pow] at h1
    exact absurd hm (not_lt.2 h1)
  refine le_antisymm (key s) ?_
  have h2 := key s⁻¹
  rw [map_inv, Units.val_inv_eq_inv_val, norm_inv] at h2
  exact (inv_le_one₀ (norm_pos_iff.2 (ψ s).ne_zero)).1 h2

open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands in
private theorem emb_ne (H : GlobalTheory.Published.GlobalArtinReciprocity) {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {w : Plc L} {A : ValuationSubring Ω} {h : IsPlaceOver A w}
    {a : Weil h →* (w.adicCompletion L)ˣ} (hw : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal) (ha : IsLocalArtin h a) :
    Nonempty (Emb l w) := by
  let inc := Subgroup.inclusion (Weil_le_Dec h)
  let ε := (cycBar L Ω l).comp (Dec (F := L) A).subtype
  have hεc : Continuous ε := ((Continuous.units_map ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom).toMonoidHom
    ((continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val)).comp (continuous_cycZ L Ω l)).comp continuous_subtype_val
  have hε : ∀ s : Weil h, (ε (inc s) : Qbar l) = ((normV w : ℕ) : Qbar l) ^ deg s * Hi.algPow w 1 (a s : w.adicCompletion L) :=
    UpperTheory.V.Loc.epsArt H h hw a ha
  by_contra hE
  haveI : IsEmpty (Emb l w) := not_nonempty_iff.1 hE
  haveI : CompactSpace (Dec (F := L) A) := isCompact_iff_compactSpace.1 (isClosed_Dec A).isCompact
  have h1 := norm_one ε (Units.continuous_val.comp hεc) (inc (frob h))
  rw [hε, deg_frob, zpow_one, Hi.algPow, finprod_of_isEmpty, mul_one, GlobalTheory.Pst.normV_eq_pow (l := l) hw, Nat.cast_pow, norm_pow] at h1
  have h2 := (pow_eq_one_iff_of_nonneg (norm_nonneg _) (fun h0 => by
    have := one_lt_normV w
    rw [GlobalTheory.Pst.normV_eq_pow (l := l) hw, h0] at this
    exact lt_irrefl _ this)).1 h1
  exact (GlobalTheory.PlaceBridge.norm_l_lt_one (l := l)).ne h2

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands in
private theorem main (H : GlobalTheory.Published.GlobalArtinReciprocity) {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {w : Plc F} {A : ValuationSubring Ω} (h : IsPlaceOver A w)
    {a : Weil h →* (w.adicCompletion F)ˣ} (hw : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal) (ha : IsLocalArtin h a) {n : ℕ}
    (wt : Fin n → Emb l w → ℤ) (hm : ∀ τ, StrictMono fun j => wt j τ) (ψ : Fin n → Dec (F := F) A →* (Qbar l)ˣ)
    (hψ : ∀ j, IsLocAlg h (ψ j) (wt j)) : ∃ g, Function.Injective fun i => ψ i g := by
  haveI := emb_ne H hw ha
  haveI : Finite (Emb l w) := GlobalTheory.HeckeGal.finite_contEmb (l := l) w
  haveI := Fintype.ofFinite (Emb l w)
  haveI : CompactSpace (Ine (F := F) A) := isCompact_iff_compactSpace.1 (isClosed_Ine A).isCompact
  choose ph hph using hψ
  let U : Subgroup (Ine (F := F) A) := ⨅ j, (ph j).ker
  have hU : IsOpen (U : Set (Ine (F := F) A)) := by
    simp only [U, Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun j => (hph j).1
  haveI : Finite (Ine (F := F) A ⧸ U) := U.quotient_finite_of_isOpen hU
  have hN : U.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hl : ValuativeRel.valuation (w.adicCompletion F) (l : w.adicCompletion F) < 1 := by
    have e : (ValuativeRel.valuation (w.adicCompletion F)).IsEquiv (Valued.v : Valuation (w.adicCompletion F) _) := by
      haveI := Valuation.Compatible.ofValuation (Valued.v : Valuation (w.adicCompletion F) _)
      exact ValuativeRel.isEquiv _ _
    rw [e.lt_one_iff_lt_one, ← map_natCast (algebraMap (𝓞 F) (w.adicCompletion F)),
      IsScalarTower.algebraMap_apply (𝓞 F) F (w.adicCompletion F)]
    erw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact (w.valuation_lt_one_iff_mem _).2 hw
  have hu : ValuativeRel.valuation (w.adicCompletion F) (1 + l : w.adicCompletion F) = 1 :=
    (ValuativeRel.valuation (w.adicCompletion F)).map_one_add_of_lt hl
  have hu0 : (1 + l : w.adicCompletion F) ≠ 0 := fun h => by simp [h] at hu
  obtain ⟨s, hs⟩ := ha.surj (Units.mk0 _ hu0)
  have hd : deg s = 0 := by
    have h2 := ha.ord_eq s
    rw [hs, GlobalTheory.SmGL.ord_eq_zero_iff.2 hu] at h2
    omega
  have hI : (s : G F Ω) ∈ Ine (F := F) A := actsAs_zero_iff.1 (actsAs_of_deg (a := 0) (b := 0) (by simpa using hd))
  let σ : Ine (F := F) A := ⟨s, hI⟩
  haveI : U.Normal := Subgroup.normal_iInf_normal fun j => inferInstance
  have hmem : σ ^ U.index ∈ U := U.pow_index_mem σ
  have e : ((a (ineIncl h (σ ^ U.index)) : (w.adicCompletion F)ˣ) : w.adicCompletion F) = (1 + l) ^ U.index := by
    rw [map_pow, map_pow, show ineIncl h σ = s from rfl, hs]
    simp
  let q : ℕ := (1 + l) ^ U.index
  have hq : 1 < q := Nat.one_lt_pow hN (by have := (Fact.out : l.Prime).pos; omega)
  have hq0 : (q : Qbar l) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hp : ∀ (T : Finset (Emb l w)) (c : Emb l w → ℤ), ∏ j ∈ T, (q : Qbar l) ^ c j = (q : Qbar l) ^ ∑ j ∈ T, c j :=
    fun T c => T.cons_induction (by simp) fun j T hj ih => by rw [Finset.prod_cons, Finset.sum_cons, ih, zpow_add₀ hq0]
  have key : ∀ j, ((ψ j (Subgroup.inclusion (Weil_le_Dec h) (ineIncl h (σ ^ U.index))) : (Qbar l)ˣ) : Qbar l) =
      (q : Qbar l) ^ ∑ τ, -wt j τ := fun j => by
    have h3 := (hph j).2 a ha (σ ^ U.index)
    rw [show ph j (σ ^ U.index) = 1 from Subgroup.mem_iInf.1 hmem j, finprod_eq_prod_of_fintype, e, mul_one] at h3
    rw [h3, ← hp]
    refine Finset.prod_congr rfl fun τ _ => ?_
    simp [q]
  refine ⟨Subgroup.inclusion (Weil_le_Dec h) (ineIncl h (σ ^ U.index)), fun i j hij => ?_⟩
  have h4 : (q : Qbar l) ^ ∑ τ, -wt i τ = (q : Qbar l) ^ ∑ τ, -wt j τ := by
    rw [← key, ← key]
    exact congrArg Units.val hij
  have h5 : (q : ℚ) ^ ∑ τ, -wt i τ = (q : ℚ) ^ ∑ τ, -wt j τ := by
    apply Rat.cast_injective (α := Qbar l)
    simpa using h4
  have h6 := zpow_right_injective₀ (a := (q : ℚ)) (by positivity) (by exact_mod_cast hq.ne') h5
  have hs : StrictAnti fun j => ∑ τ, -wt j τ := fun i j hij =>
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun τ _ => neg_lt_neg (hm τ hij)
  exact hs.injective h6

theorem UpperTheory.V.Th.Nm.regArith :
    GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) {n : ℕ} (h : s.Wt n) (v : Vl l L) (ψ : Fin n → Dec (F := L) (s.A v) →* (Qbar l)ˣ), h.Incr → (∀ j, IsLocAlg (s.hw v) (ψ j) (h v j)) → ∃ g, Function.Injective fun i => ψ i g := by
  intro H l _ L Ω _ _ _ _ _ _ s n h v ψ hI hψ
  obtain ⟨a, ha⟩ := UpperTheory.V.Loc.localArtinReciprocity H (s.hw v)
  have h1 := (s.hA v.1 ((l : ℕ) : 𝓞 (W.Lp L))).2 v.2
  exact main H.aut.art (s.hw v) ((s.hw v.1 _).1 (by simpa using h1)) ha (h v) (hI v) ψ hψ
