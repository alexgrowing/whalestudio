import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.RealAway
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.FlagAb
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.DescWeak
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.SplitComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.GalUnitary
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatFrob
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsSplitAtOfUnramifiedOfInertiaDegEqOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.Classical
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.UpU
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.IsSubquotientOfHasSupport
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.EqOfTwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.MonoOfMemSumList
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.WtBridge
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FlagWD
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.OrdCharIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.EpsArt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.CompatCsd
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.ExistenceOfGaloisRepresentationsOfHyp
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.WDAway
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LocFixed
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.RepApi
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.WeilGroupDenseInGaloisGroup
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.BuildingComponentUniqueness
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsUnramifiedAtTotallyRealOfInertiaLeRestrictionR
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsSplitAtOfDecompositionLeRestrictionRange
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EqOneOfTraceTranslationInvariantSemisimple
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGenericOfIsLocComp
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamAndJumpsRankOneLAdicCharacter
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdeleEmbeddingExtension
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDEqSumOfAgree
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.SphericalTwists.SplitW
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.SphericalTwists.RowProps
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.SphericalTwists.UnramifiedTwists.SatFrobT
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.GalUnitaryT
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.WitApi

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
open UpperTheory.GalN.V UpperTheory.V.Z.Win UpperTheory.V.Z.Desc.W UpperTheory.Zero.LLC

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

section

variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime]
  {w : Plc L} {A : ValuationSubring Ω} {h : IsPlaceOver A w} {a : Weil h →* (w.adicCompletion L)ˣ}

private theorem algPow_add (d e : (L →+* Qbar l) → ℤ) (x : (w.adicCompletion L)ˣ) :
    algPow w (d + e) (x : w.adicCompletion L) = algPow w d (x : w.adicCompletion L) * algPow w e (x : w.adicCompletion L) := by
  haveI := GlobalTheory.HeckeGal.finite_contEmb (l := l) w
  unfold algPow
  rw [← finprod_mul_distrib (Set.toFinite _) (Set.toFinite _)]
  exact finprod_congr fun j => by rw [Pi.add_apply, zpow_add₀ ((map_ne_zero j.1).2 x.ne_zero)]

private theorem sum_zero [Fintype (W.Emb l w)] (ha : IsLocalArtin h a) (d : (L →+* Qbar l) → ℤ)
    (χ : Dec (F := L) A →* (Qbar l)ˣ) (hχ : Continuous χ)
    (hv : ∀ s : Weil h, (χ (Subgroup.inclusion (Weil_le_Dec h) s) : Qbar l) = algPow w d (a s : w.adicCompletion L)) :
    ∑ j : W.Emb l w, d (j.1.comp (algebraMap L _)) = 0 := by
  haveI : CompactSpace (Dec (F := L) A) := isCompact_iff_compactSpace.1 (isClosed_Dec A).isCompact
  haveI : CharZero (w.adicCompletion L) := algebraRat.charZero _
  have hl : (l : Qbar l) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  obtain ⟨s, hs⟩ := ha.surj (Units.mk0 (l : w.adicCompletion L) (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero))
  have h1 := norm_one χ (Units.continuous_val.comp hχ) (Subgroup.inclusion (Weil_le_Dec h) s)
  rw [hv, hs, algPow, finprod_eq_prod_of_fintype] at h1
  simp only [Units.val_mk0, map_natCast] at h1
  have hp : ∀ (T : Finset (W.Emb l w)) (c : W.Emb l w → ℤ), ∏ j ∈ T, (l : Qbar l) ^ c j = (l : Qbar l) ^ ∑ j ∈ T, c j :=
    fun T c => T.cons_induction (by simp) fun j T hj ih => by rw [Finset.prod_cons, Finset.sum_cons, ih, zpow_add₀ hl]
  rw [hp, norm_zpow] at h1
  exact (zpow_eq_one_iff_right₀ (norm_nonneg _) (GlobalTheory.PlaceBridge.norm_l_lt_one (l := l)).ne).1 h1

private theorem not_linked (H : GlobalTheory.Published.GlobalArtinReciprocity) (ι : Qbar l ≃+* ℂ) {n : ℕ} (hw : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal)
    (ha : IsLocalArtin h a) {hh : Fin n → (L →+* Qbar l) → ℤ} (hm : ∀ τ, StrictMono fun j => hh j τ)
    {ω : Fin n → (w.adicCompletion L)ˣ →* ℂˣ} {ψ : Fin n → Dec (F := L) A →* (Qbar l)ˣ}
    (hO : ∀ j, OrdChar ι a (ω j) (hh j) (ψ j))
    (hne : ∀ i j, ψ i ≠ ψ j * (cycBar L Ω l).comp (Dec (F := L) A).subtype) (i j : Fin n) (hij : i ≠ j) :
    ω i ≠ ω j ∧ ω i ≠ ω j * absPow (w.adicCompletion L) 1 := by
  haveI := GlobalTheory.HeckeGal.finite_contEmb (l := l) w
  haveI := Fintype.ofFinite (W.Emb l w)
  let inc := Subgroup.inclusion (Weil_le_Dec h)
  let ε := (cycBar L Ω l).comp (Dec (F := L) A).subtype
  have hεc : Continuous ε := ((Continuous.units_map ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom).toMonoidHom
    ((continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val)).comp (continuous_cycZ L Ω l)).comp continuous_subtype_val
  have hε : ∀ s : Weil h, (ε (inc s) : Qbar l) = ((normV w : ℕ) : Qbar l) ^ deg s * algPow w 1 (a s : w.adicCompletion L) :=
    UpperTheory.V.Loc.epsArt H h hw a ha
  have hv : ∀ k (s : Weil h), (ψ k (inc s) : Qbar l) = ι.symm (ω k (a s)) * algPow w (-hh k) (a s : w.adicCompletion L) :=
    fun k s => (hO k).val s _ rfl (Set.mem_univ _)
  have hN : Nonempty (W.Emb l w) := by
    by_contra hE
    haveI : IsEmpty (W.Emb l w) := not_nonempty_iff.1 hE
    haveI : CompactSpace (Dec (F := L) A) := isCompact_iff_compactSpace.1 (isClosed_Dec A).isCompact
    have h1 := norm_one ε (Units.continuous_val.comp hεc) (inc (frob h))
    rw [hε, deg_frob, zpow_one, algPow, finprod_of_isEmpty, mul_one, GlobalTheory.Pst.normV_eq_pow (l := l) hw, Nat.cast_pow, norm_pow] at h1
    have h2 := (pow_eq_one_iff_of_nonneg (norm_nonneg _) (fun h0 => by
      have := one_lt_normV w
      rw [GlobalTheory.Pst.normV_eq_pow (l := l) hw, h0] at this
      exact lt_irrefl _ this)).1 h1
    exact (GlobalTheory.PlaceBridge.norm_l_lt_one (l := l)).ne h2
  have hneg : ∀ d : W.Emb l w → ℤ, (∀ t, d t < 0) → ∑ t, d t ≠ 0 := fun d hd =>
    (Finset.sum_neg (fun t _ => hd t) Finset.univ_nonempty).ne
  constructor
  · intro e
    have h1 := sum_zero ha (hh j - hh i) (ψ i * (ψ j)⁻¹) ((hO i).cont.mul (hO j).cont.inv) fun s => by
      rw [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.mul_inv_eq_iff_eq_mul, hv, hv, e, mul_left_comm,
        ← algPow_add]
      congr 2
      ring
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · exact (Finset.sum_pos (fun t _ => sub_pos.2 (hm _ hlt)) Finset.univ_nonempty).ne' h1
    · exact hneg _ (fun t => sub_neg.2 (hm _ hlt)) h1
  · intro e
    have hc : Continuous (ψ i * (ψ j * ε)⁻¹) := (hO i).cont.mul ((hO j).cont.mul hεc).inv
    have hab : ∀ s : Weil h, ι.symm (absPow (w.adicCompletion L) 1 (a s)) = ((normV w : ℕ) : Qbar l) ^ deg s := fun s => by
      have := DFunLike.congr_fun (ha.absPow_comp 1) s
      rw [Complex.ofReal_one] at this
      rw [← MonoidHom.comp_apply, this, GlobalTheory.WeilDeligne.unrChar_apply, Units.val_zpow_eq_zpow_val, map_zpow₀]
      simp
    have hx : ∀ s : Weil h, (((ψ i * (ψ j * ε)⁻¹) (inc s) : (Qbar l)ˣ) : Qbar l) =
        algPow w (hh j - hh i - 1) (a s : w.adicCompletion L) := fun s => by
      rw [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.mul_inv_eq_iff_eq_mul, MonoidHom.mul_apply,
        Units.val_mul, hv, hv, hε, e, MonoidHom.mul_apply, Units.val_mul, map_mul, hab,
        show -hh i = (hh j - hh i - 1) + (-hh j + 1) by ring, algPow_add, algPow_add]
      ring
    have h1 := sum_zero ha _ _ hc hx
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun t _ => by
        have := hm (t.1.comp (algebraMap L _)) hlt
        simp only [Pi.sub_apply, Pi.one_apply] at this ⊢
        omega).1 h1
      refine hne i j (mul_inv_eq_one.1 (MonoidHom.ext fun g => Units.ext ?_))
      refine congrFun ((UpperTheory.weil_group_dense_in_galois_group L Ω w A h).equalizer (Units.continuous_val.comp hc) continuous_const
        (funext fun s => ?_)) g
      refine (hx s).trans (finprod_eq_one_of_forall_eq_one fun t => ?_)
      rw [h2 t (Finset.mem_univ _), zpow_zero]
    · refine hneg _ (fun t => ?_) h1
      have := hm (t.1.comp (algebraMap L _)) hlt
      simp only [Pi.sub_apply, Pi.one_apply] at this ⊢
      omega

end

private theorem dual_of_weights {n : ℕ} (μ ν : DomWeight n)
    (h : (Finset.univ.val.map fun j : Fin n => μ.w j.rev + (j : ℕ)).map (fun k : ℤ => (k : ℂ)) =
      (infOfWeight ν).map fun z => ((n : ℂ) - 1) / 2 - z) : ν = μ.dual := by
  have h1 : (Finset.univ.val.map fun j : Fin n => μ.w j.rev + (j : ℕ)) =
      Finset.univ.val.map fun j : Fin n => -ν.w j + (j : ℕ) := by
    refine Multiset.map_injective (Int.cast_injective (α := ℂ)) (h.trans ?_)
    rw [infOfWeight, Multiset.map_map, Multiset.map_map]
    exact Multiset.map_congr rfl fun j _ => by simp only [Function.comp_apply]; push_cast; ring
  have m1 : StrictMono fun j : Fin n => μ.w j.rev + (j : ℕ) := fun i j hij =>
    add_lt_add_of_le_of_lt (μ.anti (Fin.rev_le_rev.2 hij.le)) (by exact_mod_cast hij)
  have m2 : StrictMono fun j : Fin n => -ν.w j + (j : ℕ) := fun i j hij =>
    add_lt_add_of_le_of_lt (neg_le_neg (ν.anti hij.le)) (by exact_mod_cast hij)
  have h2 := (m1.range_inj m2).1 (Set.ext fun z => by simpa using (congrArg (z ∈ ·) h1).to_iff)
  obtain ⟨u, hu⟩ := ν
  have h3 : u = μ.dual.w := funext fun j => by
    have := congrFun h2 j
    simp only [DomWeight.dual] at this ⊢
    omega
  subst h3
  rfl

section

variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime]
  {w : Plc L} {A : ValuationSubring Ω} {ι : Qbar l ≃+* ℂ} {n : ℕ}

private theorem emb_place (j : W.Emb l w) (x : 𝓞 L) : ‖j.1.comp (algebraMap L _) (x : L)‖ < 1 ↔ x ∈ w.asIdeal := by
  have h1 : w.asIdeal ≤ (GlobalTheory.EvExtend.placeOf (j.1.comp (algebraMap L _))).asIdeal := fun y hy => by
    rw [GlobalTheory.EvExtend.mem_placeOf, ← tendsto_pow_atTop_nhds_zero_iff_norm_lt_one]
    have h2 : Valued.v (algebraMap L (w.adicCompletion L) (y : L)) < 1 := by
      rw [show Valued.v (algebraMap L (w.adicCompletion L) (y : L)) = w.valuation L (algebraMap (𝓞 L) L y) from
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _]
      exact (HeightOneSpectrum.valuation_lt_one_iff_mem w _).2 hy
    have h3 := (j.2.tendsto 0).comp (Valued.tendsto_zero_pow_of_v_lt_one h2)
    simpa [Function.comp_def] using h3
  rw [w.isMaximal.eq_of_le (GlobalTheory.EvExtend.placeOf _).isPrime.ne_top h1, GlobalTheory.EvExtend.mem_placeOf]

private theorem jumps_eq (h : IsPlaceOver A w) (hw : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal) {r : Dec (F := L) A →* GL (Fin n) (Qbar l)}
    {J J' : (L →+* Qbar l) → Multiset ℤ} {P P' : Weil h → ℂ[X]} (H : DRat ι h r J P) (H' : DRat ι h r J' P')
    (j : W.Emb l w) : J (j.1.comp (algebraMap L _)) = J' (j.1.comp (algebraMap L _)) := by
  obtain ⟨O, _, _, _, Bw, hj⟩ := Af.exists_bridge (l := l) h hw
  obtain ⟨τ', hτ'⟩ := GlobalTheory.CharAboveRead.exists_isInduced_of _ w hw (emb_place j) A h O Bw hj
  obtain ⟨LL, r', hM, -, τ₁, hτ₁, hc⟩ := (H O Bw hj).2.1 _ _ _ hτ'
  ext k
  exact_mod_cast (hc k).trans (GlobalTheory.Pst.IsJumpsAt.count_eq _ hM hτ₁ ((H' O Bw hj).2.1 _ _ _ hτ') k).symm

private theorem flag_cont {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] {r : Γ →* GL (Fin n) (Qbar l)}
    (hr : Continuous r) {ψ : Fin n → Γ →* (Qbar l)ˣ} (hf : W.HasFlag r ψ) (i : Fin n) : Continuous (ψ i) := by
  obtain ⟨g, hg⟩ := hf
  have h1 : Continuous fun s => (ψ i s : Qbar l) :=
    ((Units.continuous_val.comp ((continuous_const.mul hr).mul continuous_const)).matrix_elem i i).congr fun s => (hg s).2 i
  exact Units.continuous_iff.2 ⟨h1, (h1.comp continuous_inv).congr fun s => by simp⟩

private theorem above [IsCMField L] (P : Af.Hypotheses₂) (hPs : PsT) (hl : l ≠ 2) {ρ : G L Ω →* GL (Fin n) (Qbar l)}
    {HT : (L →+* Qbar l) → Multiset ℤ} (hρ : Continuous ρ) (HG : HasHTAt ρ HT w) (h : IsPlaceOver A w)
    (hw : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal) {τ : SmIrr (GLw n w)} (H : LocGlobT ι ρ w τ) {rc : IrrGL (w.adicCompletion L) → WD h}
    (hrc : IsRecT h rc) (hp : GlobalTheory.RoadU.PlainTor (IrrGL.of τ.ρ τ.smooth τ.irred)) (hg : Gd (rc (algNorm τ)))
    (lam : Wt L l n) {ψ : Fin n → Dec (F := L) A →* (Qbar l)ˣ}
    (hψ : ∀ i, W.IsLocAlg h (ψ i) fun t => htW lam i (t.1.comp (algebraMap L _)))
    (hf : W.HasFlag (ρ.comp (Dec (F := L) A).subtype) ψ)
    (hne : ∀ i j, ψ i ≠ ψ j * (cycBar L Ω l).comp (Dec (F := L) A).subtype) :
    (∃ ω : Fin n → (w.adicCompletion L)ˣ →* ℂˣ, Nonempty (τ.ρ.Equiv (PS ω)) ∧
      ∀ i, OrdChar ι (artOf h) (ω i) (htW lam i) (ψ i)) ∧
    ∀ j : W.Emb l w, HT (j.1.comp (algebraMap L _)) = Finset.univ.val.map fun i => htW lam i (j.1.comp (algebraMap L _)) := by
  have ha : IsLocalArtin h (artOf h) := by
    obtain ⟨a, ha, -⟩ := hrc
    exact Classical.epsilon_spec ⟨a, ha⟩
  have hc : Continuous (ρ.comp (Dec (F := L) A).subtype) := hρ.comp continuous_subtype_val
  choose ω hω using fun i => (Loc.ordCharIff P.litN.aut.art h ι _ ha (htW lam i) (ψ i)).1.2 ⟨flag_cont hc hf i, hψ i⟩
  have hD : DRat ι h (ρ.comp (Dec (F := L) A).subtype) HT fun s => (rc (algNorm τ)).charPol s := fun O _ _ _ Bw hj =>
    have h1 := HG A h O Bw hj
    ⟨h1.1, h1.2, fun s => by rw [((H A h rc hrc).2 O Bw hj hg).2]⟩
  have hD' := Loc.flagWD P.litN L Ω l hl ι n w hw A h _ ha _ hc _ ω ψ hω hf _ _ hD
  refine ⟨⟨ω, ?_, hω⟩, jumps_eq h hw hD hD'⟩
  have hs : IsSubquotient τ.ρ (PS ω) := by
    obtain ⟨O, _, _, _, Bw, hj⟩ := Af.exists_bridge (l := l) h hw
    exact hPs P.litN L Ω n w A h _ ha rc hrc τ hp ω (fun i => (hω i).smooth) fun s =>
      ((hD O Bw hj).2.2 s).symm.trans ((hD' O Bw hj).2.2 s)
  refine (psIrr P.litN _ n ω (fun i => (hω i).smooth) (not_linked P.litN.aut.art ι hw ha (fun t i j hij => ?_) hω hne)).2
    _ τ.ρ τ.irred hs
  exact add_lt_add_of_le_of_lt ((lam t).anti (Fin.rev_le_rev.2 hij.le)) (by exact_mod_cast hij)

private theorem unram_of_fixed [IsCMField L] {σ : Submodule ℂ (UA L n → ℂ)} {τ : SmIrr (GLw n w)}
    (hτ : IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ)
    (hs : Function.Surjective ((cLoc w).comp (locU n w).subtype)) (hf : Af.HasFixed τ.ρ (GlobalTheory.LFun.KGL w n)) : IsUnramU σ w := by
  obtain ⟨hi, f, f0, fm, fe⟩ := hτ
  obtain ⟨z, hz, hf⟩ := hf
  refine ⟨f z, fm z, fun h0 => ?_, fun x hx hk => ?_⟩
  · let K : Subrepresentation τ.ρ := ⟨LinearMap.ker f, fun g v hv => by
      obtain ⟨x, rfl⟩ := hs g
      rw [LinearMap.mem_ker] at hv ⊢
      rw [fe, hv, map_zero]⟩
    rcases hi.eq_bot_or_eq_top K with hK | hK
    · have h1 : z ∈ K.toSubmodule := h0
      rw [hK] at h1
      exact hz h1
    · refine f0 (LinearMap.ext fun v => ?_)
      have h1 : v ∈ K.toSubmodule := by rw [hK]; trivial
      exact h1
  · have := fe ⟨x, hx⟩ z
    rw [← this]
    exact congrArg f (hf _ hk)

end

private theorem chi_comap {n : ℕ} {A Γ H : Type} [CommRing A] [Group Γ] [Group H] (D : W.GDet n A Γ) (φ : H →* Γ) (g : H) :
    (D.comap φ).chi (MonoidAlgebra.single g 1) = D.chi (MonoidAlgebra.single (φ g) 1) := by
  change D.D A[X] (MonoidAlgebra.mapDomainRingHom A[X] φ _) = D.D A[X] _
  rw [map_sub]
  simp

private theorem ker_le {n : ℕ} {k Γ H : Type} [Field k] [CharZero k] [Group Γ] [Group H] {D : W.GDet n k Γ} {φ : H →* Γ}
    {ρ : H →* GL (Fin n) k} (hn : 1 ≤ n) (e : D.comap φ = W.GDet.ofRep (W.mat ρ)) (hs : Formalism.MainNotions.N.IsSSRep ρ) {g : H}
    (hg : φ g = 1) : ρ g = 1 := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  refine UpperTheory.eq_one_of_trace_translation_invariant_semisimple H k n ρ hs g fun y => ?_
  have h1 : ∀ z, (ρ z : Matrix (Fin n) (Fin n) k).charpoly = D.chi (MonoidAlgebra.single (φ z) 1) := fun z =>
    ((AlgebraTools.Det.repApi (W.mat ρ)).2.1 z).symm.trans (by rw [← e, chi_comap])
  rw [Matrix.trace_eq_neg_charpoly_coeff, Matrix.trace_eq_neg_charpoly_coeff, h1, h1, map_mul, hg, mul_one]

theorem UpperTheory.V.Z.Desc.W.toT (P : Af.Hypotheses₂) {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    {w : Plc L} {A : ValuationSubring Ω} {h : IsPlaceOver A w} {rc : IrrGL (w.adicCompletion L) → WD h} (k : IsRec h rc) : IsRecT h rc :=
  isRecT_of_isRec P.litN.loc.dzt k
