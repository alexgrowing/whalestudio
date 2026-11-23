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
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

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

private theorem spherical (P : Af.Hypotheses₂) {ρ : G L Ω →* GL (Fin n) (Qbar l)} (hρ : Continuous ρ) (h : IsPlaceOver A w)
    (hw : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal) (hI : ∀ g ∈ Ine (F := L) A, ρ g = 1) {τ : SmIrr (GLw n w)} (H : Af.LocGlob ι ρ w τ) :
    Af.HasFixed τ.ρ (GlobalTheory.LFun.KGL w n) := by
  obtain ⟨rc, hrc⟩ := P.exists_rec h
  obtain ⟨v, hv, hf⟩ := Af.locFixed P L Ω n 1 le_rfl w A h rc hrc τ (Af.wdAway P L Ω l ι n 1 le_rfl ρ hρ w hw A h 1
    (fun _ _ _ => rfl) ⟨1, fun g hg => by simp [hI g hg]⟩ _ ((H A h rc hrc).1 hw))
  refine ⟨v, hv, fun u hu => hf u (Af.locGL_mem_KLev n w ?_ hu)⟩
  rw [Nat.cast_one]
  exact (Ideal.ne_top_iff_one _).1 w.isPrime.ne_top

private theorem flag_cont {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] {r : Γ →* GL (Fin n) (Qbar l)}
    (hr : Continuous r) {ψ : Fin n → Γ →* (Qbar l)ˣ} (hf : W.HasFlag r ψ) (i : Fin n) : Continuous (ψ i) := by
  obtain ⟨g, hg⟩ := hf
  have h1 : Continuous fun s => (ψ i s : Qbar l) :=
    ((Units.continuous_val.comp ((continuous_const.mul hr).mul continuous_const)).matrix_elem i i).congr fun s => (hg s).2 i
  exact Units.continuous_iff.2 ⟨h1, (h1.comp continuous_inv).congr fun s => by simp⟩

private theorem above [IsCMField L] (P : Af.Hypotheses₂) (hl : l ≠ 2) {ρ : G L Ω →* GL (Fin n) (Qbar l)}
    {HT : (L →+* Qbar l) → Multiset ℤ} (hρ : Continuous ρ) (HG : Af.HasHT ρ HT) (h : IsPlaceOver A w)
    (hw : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal) {τ : SmIrr (GLw n w)} (H : Af.LocGlob ι ρ w τ)
    (lam : Wt L l n) {ψ : Fin n → Dec (F := L) A →* (Qbar l)ˣ}
    (hψ : ∀ i, W.IsLocAlg h (ψ i) fun t => htW lam i (t.1.comp (algebraMap L _)))
    (hf : W.HasFlag (ρ.comp (Dec (F := L) A).subtype) ψ)
    (hne : ∀ i j, ψ i ≠ ψ j * (cycBar L Ω l).comp (Dec (F := L) A).subtype) :
    (∃ ω : Fin n → (w.adicCompletion L)ˣ →* ℂˣ, Nonempty (τ.ρ.Equiv (PS ω)) ∧
      ∀ i, OrdChar ι (artOf h) (ω i) (htW lam i) (ψ i)) ∧
    ∀ j : W.Emb l w, HT (j.1.comp (algebraMap L _)) = Finset.univ.val.map fun i => htW lam i (j.1.comp (algebraMap L _)) := by
  obtain ⟨rc, hrc⟩ := P.exists_rec h
  have ha : IsLocalArtin h (artOf h) := by
    obtain ⟨a, ha, -⟩ := hrc
    exact Classical.epsilon_spec ⟨a, ha⟩
  have hc : Continuous (ρ.comp (Dec (F := L) A).subtype) := hρ.comp continuous_subtype_val
  choose ω hω using fun i => (Loc.ordCharIff P.litN.aut.art h ι _ ha (htW lam i) (ψ i)).1.2 ⟨flag_cont hc hf i, hψ i⟩
  have hD : DRat ι h (ρ.comp (Dec (F := L) A).subtype) HT fun s => (rc (algNorm τ)).charPol s := fun O _ _ _ Bw hj =>
    have h1 := HG w A h O Bw hj
    ⟨h1.1, h1.2, ((H A h rc hrc).2 O Bw hj).2
      (Or.inl (UpperTheory.V.Lev.flagAb P.litN ι hw h _ ha _ hc _ ω ψ hω hf Bw hj h1.1))⟩
  have hD' := Loc.flagWD P.litN L Ω l hl ι n w hw A h _ ha _ hc _ ω ψ hω hf _ _ hD
  refine ⟨⟨ω, ?_, hω⟩, jumps_eq h hw hD hD'⟩
  have hs : IsSubquotient τ.ρ (PS ω) := by
    obtain ⟨O, _, _, _, Bw, hj⟩ := Af.exists_bridge (l := l) h hw
    exact (psRec P.litN L Ω n w A h _ ha rc hrc τ ω fun i => (hω i).smooth).2 fun s =>
      ((hD O Bw hj).2.2 s).symm.trans ((hD' O Bw hj).2.2 s)
  refine (psIrr P.litN _ n ω (fun i => (hω i).smooth) (not_linked P.litN.aut.art ι hw ha (fun t i j hij => ?_) hω hne)).2
    _ τ.ρ τ.irred hs
  exact add_lt_add_of_le_of_lt ((lam t).anti (Fin.rev_le_rev.2 hij.le)) (by exact_mod_cast hij)

private theorem conj_of_split [IsCMField L]
    (hE : ∀ w : Plc L, Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield L)) w.asIdeal) (r r' : G L Ω →* GL (Fin n) (Qbar l))
    (hr : Continuous r) (hr' : Continuous r') (hs : Formalism.MainNotions.N.IsSSRep r) (hs' : Formalism.MainNotions.N.IsSSRep r')
    (hw : ∀ᶠ w : Plc L in Filter.cofinite, IsSplitAt w → ∃ B, Af.FrobEig ι r w B ∧ Af.FrobEig ι r' w B) :
    ∃ P : GL (Fin n) (Qbar l), ∀ s, r' s = P * r s * P⁻¹ := by
  have contCoeff : ∀ i : ℕ, Continuous fun M : Matrix (Fin n) (Fin n) (Qbar l) => M.charpoly.coeff i := fun i => by
    have h : (fun M : Matrix (Fin n) (Fin n) (Qbar l) => M.charpoly.coeff i) =
        fun M => MvPolynomial.eval (fun ij : Fin n × Fin n => M ij.1 ij.2) ((Matrix.charpoly.univ (Qbar l) (Fin n)).coeff i) := by
      funext M
      exact (Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (RingHom.id _) (fun ij : Fin n × Fin n => M ij.1 ij.2) i).symm
    rw [h]
    exact (MvPolynomial.continuous_eval _).comp (continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1))
  have hD := GlobalTheory.Published.ChebotarevDegreeOne.dense (F := L) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne'
    (Filter.eventually_cofinite.1 hw)
  have hc : ∀ g : G L Ω, (r g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly =
      (r' g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly := by
    intro g
    ext i
    have h1 : Continuous fun g : G L Ω => (r g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i :=
      (contCoeff i).comp (Units.continuous_val.comp (hr.comp continuous_inv))
    have h2 : Continuous fun g : G L Ω => (r' g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i :=
      (contCoeff i).comp (Units.continuous_val.comp (hr'.comp continuous_inv))
    refine congrFun (Continuous.ext_on hD h1 h2 ?_) g
    rintro σ ⟨v, hv, hd, A, hA, hσ⟩
    obtain ⟨B, hB, hB'⟩ := not_not.1 hv (UpperTheory.isSplitAt_of_unramified_of_inertiaDeg_eq_one L v (hE v) hd)
    have h := ((hB A hA).2 σ hσ).trans ((hB' A hA).2 σ hσ).symm
    have h' := Polynomial.map_injective ι.toRingHom ι.injective h
    simp only [h']
  obtain ⟨P, hP⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix r r' hs hs' (fun g => by simpa using hc g⁻¹)
  exact ⟨P⁻¹, fun s => by rw [hP s, inv_inv]⟩

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

theorem UpperTheory.V.Z.Desc.jPTw :
    Af.HypothesesH → Z.Desc.DescWeak → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ), ∀ (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) (R : HD Q ι Λ) (K : (hset Q R.τ₀).Lev), V.S' = s.S → ∀ J : Ideal B.B, R.IsJ B K J →
    ∀ (x : B.Pt) (h : s.Wt n) (ρ : G L Ω →* GL (Fin n) (Qbar l)), 2 ≤ n → n ≤ 4 → x.Arith h →
    x.IsRep ρ → Continuous ρ → Af.IsAutCsd ι ρ → (∀ g ∈ Ine (F := L) (s.A s.v0), ρ g = 1) →
    (∀ v : Vl l L, W.HasFlag (ρ.comp (Dec (F := L) (s.A v)).subtype) (x.psi v) ∧
      ∀ i j, x.psi v i ≠ x.psi v j * (cycBar L Ω l).comp (Dec (F := L) (s.A v)).subtype) →
    J ≤ RingHom.ker x := by
  intro PH hD l _ L Ω _ _ _ _ _ _ s n hn V Q c r ι B Λ R K hS J hJ x h ρ hn2 hn4 hx hρ hc ⟨π, hreg, hd, hatt⟩ h0 hfl
  have P := PH.toClassicalTheorems
  have hE := UpperTheory.isUnramifiedAt_totallyReal_of_inertia_le_restriction_range L Ω s.unr
  obtain ⟨lam, hlam⟩ := (wtBridge P.litN l L Ω s n hn V Q c R.m R.τ₀ r B Λ R.θ R.theta h hx.1).1
  have hLG := Af.compatCsd PH L Ω l ι n hn ρ π hc hreg hd hatt
  have hund : ∀ {A : ValuationSubring Ω} {w : Plc L}, IsPlaceOver A w → IsPlaceOver A (w.under (𝓞 (Lp L))) :=
    fun hA y => hA (algebraMap (𝓞 (Lp L)) (𝓞 L) y)
  have hwv : ∀ v, (s.w v).under (𝓞 (Lp L)) = v := fun v =>
    HeightOneSpectrum.ext (Ideal.ext fun y => (hund (s.hw v) y).symm.trans (s.hA v y))
  have hl : ∀ w : Plc L, ((l : ℕ) : 𝓞 L) ∈ w.asIdeal ↔ ((l : ℕ) : 𝓞 (Lp L)) ∈ (w.under (𝓞 (Lp L))).asIdeal := fun w => by
    rw [← map_natCast (algebraMap (𝓞 (Lp L)) (𝓞 L))]
    rfl
  have hsp : ∀ w : Plc L, w.under (𝓞 (Lp L)) ∈ V.S' → IsSplitAt w := fun w hw =>
    UpperTheory.isSplitAt_of_decomposition_le_restriction_range L Ω _ _ (s.hA _) (V.split _ hw) w rfl
  have hin : ∀ w : Plc L, ((l : ℕ) : 𝓞 L) ∈ w.asIdeal → w.under (𝓞 (Lp L)) ∈ V.S' := fun w hw =>
    V.sub (Or.inl ((hl w).1 hw))
  have hI : ∀ w : Plc L, w.under (𝓞 (Lp L)) ∉ V.S' → ∀ A, IsPlaceOver A w → ∀ g ∈ Ine (F := L) A, ρ g = 1 := fun w hw A hA g hg => by
    refine ker_le hn hρ hatt.1 (Subtype.ext ((QuotientGroup.eq_one_iff _).2 ?_))
    refine Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ?_)
    simp only [Set.mem_iUnion]
    exact ⟨_, hw, A, hund hA, hg⟩
  have hlv : ∀ v : Vl l L, ((l : ℕ) : 𝓞 L) ∈ (s.w v).asIdeal := fun v => by
    rw [hl, hwv]
    exact v.2
  have hψ : ∀ (v : Vl l L) i, W.IsLocAlg (s.hw v) (x.psi v i) fun t => htW lam i (t.1.comp (algebraMap L _)) :=
    fun v i => (funext (hlam v i)).symm ▸ hx.2 v i
  obtain ⟨σ, hσ, hunr, hsat⟩ := hD L hE l Fact.out V.S' V.fin hsp hin n hn2 hn4 π hreg hd
    fun w hw => by
      obtain ⟨A, hA⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A w := exists_isPlaceOver Ω w
      obtain ⟨⟨τ, hτ⟩, hi⟩ := Af.locCompC P L n π w
      obtain ⟨b, hb⟩ := (Af.satLoc P L n w τ).1 (spherical P hc hA (mt (hin w) hw) (hI w hw A hA) (hLG w τ hτ))
      exact ⟨b, ((Af.satLoc P L n w τ).2 _ π.finPart (hi τ hτ) b).2 hb⟩
  obtain ⟨ρ', HT', hc', hs', -, hHT', hwt, hLG', -, -⟩ := Af.galUnitary PH L Ω hE l s.odd ι n hn σ hσ
  have hfin : ∀ᶠ w : Plc L in Filter.cofinite, ((l : ℕ) : 𝓞 L) ∉ w.asIdeal := by
    have h0 : Ideal.span {((l : ℕ) : 𝓞 L)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast (Fact.out : l.Prime).ne_zero
    exact (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr (not_not.1 hv)
  obtain ⟨g, hg⟩ := conj_of_split (ι := ι) hE ρ ρ' hc hc' hatt.1 hs' (by
    filter_upwards [hsat, hatt.2, hfin] with w h1 ⟨b, hb, hF⟩ hw hs
    obtain ⟨τ, b', h2, h3, h4⟩ := h1 hs
    obtain rfl := hb.unique h4
    exact ⟨_, hF, Af.satFrob P L Ω l ι n ρ' hc' w hw τ b h3 fun A hA rc hrc => (hLG' w hs τ h2 A hA rc hrc).1 hw⟩)
  have hone : ∀ {t}, ρ t = 1 → ρ' t = 1 := fun e => by rw [hg, e, mul_one, mul_inv_cancel]
  have hρ' : x.IsRep ρ' := by
    refine hρ.trans ((AlgebraTools.Det.repApi (W.mat ρ')).2.2.2.2.2.2.2 (W.mat ρ) g fun t => ?_)
    have e : g * ρ t = ρ' t * g := by rw [hg, inv_mul_cancel_right]
    exact congrArg Units.val e
  have hfl' : ∀ v : Vl l L, W.HasFlag (ρ'.comp (Dec (F := L) (s.A v)).subtype) (x.psi v) := fun v => by
    obtain ⟨a, ha⟩ := (hfl v).1
    refine ⟨a * g⁻¹, fun t => ?_⟩
    have e : a * g⁻¹ * (ρ'.comp (Dec (F := L) (s.A v)).subtype) t * (a * g⁻¹)⁻¹ = a * (ρ.comp (Dec (F := L) (s.A v)).subtype) t * a⁻¹ := by
      simp only [MonoidHom.comp_apply, hg]
      group
    rw [e]
    exact ha t
  obtain ⟨Pw, hbc⟩ := UpperTheory.BaseChangeIdentities.splitComp
    (GlobalTheory.BcSpeh.bcSpeh_of_baseChange (GlobalTheory.BaseChangeBridge.main P.litN.aut.bc P.litN.loc.bern)
      (GlobalTheory.SpehInfChar.discreteSpectrumGL_of_residual P.litN.aut.mw)) L hE n hn σ hσ
  have hab := fun (v : Vl l L) => above P s.odd hc' hHT' (s.hw v) (hlv v)
    (hLG' _ (hsp _ (hin _ (hlv v))) _ (hbc _ (hsp _ (hin _ (hlv v))))) lam (hψ v) (hfl' v) (hfl v).2
  refine upU PH l L Ω s n hn V Q c r ι B Λ R K hS J hJ x h lam hx hlam σ ρ' hσ hc' hs' hρ' hLG'
    (fun y => ?_) (fun w hw => ?_) ?_ fun v => ?_
  · obtain ⟨ν, h1⟩ := GlobalTheory.T.exists_algebraicWeight_of_automorphic_definiteUnitary L n hn σ hσ (ι.toRingHom.comp y.res)
    have h3 := hwt y.res ν h1
    rw [show HT' y.res = _ from (hab y.1).2 y.2] at h3
    rwa [← dual_of_weights (lam y.res) ν h3]
  · by_cases hs : IsSplitAt w
    · obtain ⟨A, hA⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A w := exists_isPlaceOver Ω w
      refine unram_of_fixed (hbc w hs) ?_
        (spherical P hc' hA (mt (hin w) hw) (fun t ht => hone (hI w hw A hA t ht)) (hLG' w hs _ (hbc w hs)))
      obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL L n w hs
      exact fun g => ⟨e.symm g, (he _).symm.trans (e.apply_symm_apply g)⟩
    · exact hunr w hs
  · have hp : ((l : ℕ) : 𝓞 L) ∉ (s.w s.v0).asIdeal := fun hm => by
      have h1 := (hl _).1 hm
      rw [hwv] at h1
      have h2 := GlobalTheory.Pst.normV_eq_pow (l := l) h1
      rw [s.norm_v0_eq_one] at h2
      exact s.p_ne ((Nat.Prime.eq_one_or_self_of_dvd s.p_prime l (h2 ▸ dvd_pow_self l fun h3 => s.p_prime.ne_one
        (by rw [h2, h3, pow_zero]))).resolve_left (Fact.out : l.Prime).ne_one).symm
    have hs := hsp (s.w s.v0) (by rw [hwv]; exact V.sub (Or.inr (Or.inr rfl)))
    obtain ⟨z, hz, hf⟩ := spherical P hc' (s.hw s.v0) hp (fun t ht => hone (h0 t ht)) (hLG' _ hs _ (hbc _ hs))
    refine ⟨Pw _ _, hbc _ hs, (Submodule.ne_bot_iff _).2 ⟨z, fun u hu => hf u ?_, hz⟩⟩
    rw [← GlobalTheory.HeckeEigConj.KO_eq_KGL]
    obtain ⟨u, -, rfl⟩ := hu
    exact ⟨u, rfl⟩
  · obtain ⟨ω, h1, h2⟩ := (hab v).1
    exact ⟨Pw _ _, ω, hbc _ (hsp _ (hin _ (hlv v))), h1, h2⟩
