import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.SphericalTwists.DualOfWeights
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.UnitaryHeckeData
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.WStmtx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TWtBridge
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TLocCompC
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TSatLoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.UpUW
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TSatFrobT
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LocFlagWD
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TPsIrr
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
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
private theorem above [IsCMField L] (P : _root_.UpperTheory.V.Af.Hypotheses') (hPs : _root_.UpperTheory.V.Z.Desc.W.PseudoLocalDescent) (hl : l ≠ 2) {ρ : G L Ω →* GL (Fin n) (Qbar l)}
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
  have hD' := _root_.UpperTheory.V.Loc.flag_weil_deligne_of_literal_automorphy_n P.litN L Ω l hl ι n w hw A h _ ha _ hc _ ω ψ hω hf _ _ hD
  refine ⟨⟨ω, ?_, hω⟩, jumps_eq h hw hD hD'⟩
  have hs : IsSubquotient τ.ρ (PS ω) := by
    obtain ⟨O, _, _, _, Bw, hj⟩ := Af.exists_bridge (l := l) h hw
    exact hPs P.litN L Ω n w A h _ ha rc hrc τ hp ω (fun i => (hω i).smooth) fun s =>
      ((hD O Bw hj).2.2 s).symm.trans ((hD' O Bw hj).2.2 s)
  refine (_root_.UpperTheory.V.Hi.prin_series_irreducible_and_unique_subquotient P.litN _ n ω (fun i => (hω i).smooth) (not_linked P.litN.aut.art ι hw ha (fun t i j hij => ?_) hω hne)).2
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
theorem UpperTheory.V.Z.Desc.W.isRecT_of_isRecT (_P : _root_.UpperTheory.V.Af.Hypotheses') {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    {w : Plc L} {A : ValuationSubring Ω} {h : IsPlaceOver A w} {rc : IrrGL (w.adicCompletion L) → WD h} (k : IsRecT h rc) : IsRecT h rc := k
theorem UpperTheory.V.Z.Desc.W.jPT_of_alt :
    RecTExists → CompatT → PlainRec → Same → _root_.UpperTheory.V.Z.Desc.W.SphTAlt → _root_.UpperTheory.V.Z.Desc.W.PseudoLocalDescent → UnlOf → _root_.UpperTheory.V.Af.HypothesesH' → Z.Desc.DescWeak → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ), ∀ (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) (R : _root_.UpperTheory.V.Hi.CaseU.UnitaryHeckeData Q ι Λ) (K : (hset Q R.τ₀).Lev), V.S' = s.S → ∀ J : Ideal B.B, R.IsJ B K J →
    ∀ (x : B.Pt) (h : s.Wt n) (ρ : G L Ω →* GL (Fin n) (Qbar l)), 2 ≤ n → n ≤ 4 → x.Arith h →
    x.IsRep ρ → Continuous ρ → (AutCsd0 ι ρ ∧ (Continuous ρ → WitA ι ρ)) → (∀ g ∈ Ine (F := L) (s.A s.v0), ρ g = 1) →
    (∀ v : Vl l L, W.HasFlag (ρ.comp (Dec (F := L) (s.A v)).subtype) (x.psi v) ∧
      ∀ i j, x.psi v i ≠ x.psi v j * (cycBar L Ω l).comp (Dec (F := L) (s.A v)).subtype) →
    J ≤ RingHom.ker x := by
  intro hEx hCo hPl hSame hSph hPs hUn PH hD l _ L Ω _ _ _ _ _ _ s n hn V Q c r ι B Λ R K hS J hJ x h ρ hn2 hn4 hx hρ hc ⟨⟨π, hreg, hd, hatt⟩, hW⟩ h0 hfl
  have P := PH.toClassicalTheorems
  have hE := UpperTheory.isUnramifiedAt_totallyReal_of_inertia_le_restriction_range L Ω s.unr
  obtain ⟨lam, hlam⟩ := (_root_.UpperTheory.V.Hi.arith_good_iff_hset_of_theta_incr_weight P.litN l L Ω s n hn V Q c R.m R.τ₀ r B Λ R.θ R.theta h hx.1).1
  have hpol : ∃ χ, GlobalTheory.ContraPair.PolarizedPair π χ := by
    refine ⟨quadChar L ^ n, fun v => ?_, ?_⟩
    · have e : (quadChar L ^ n).locInf v (-1) = (quadChar L).locInf v (-1) ^ n := rfl
      rw [e, quadChar_locInf]
    · rw [map_pow, compNorm_quadChar, one_pow]
      exact (GlobalTheory.ContraPair.dualIsConjBy_one π).2 hd
  obtain ⟨HT, hwt, hLG⟩ := hCo L Ω l ι n hn ρ π hc hreg hpol hatt
  have heq : ∀ (w : Plc L), ((l : ℕ) : 𝓞 L) ∉ w.asIdeal → ∀ (A : ValuationSubring Ω) (hA : IsPlaceOver A w) rc, IsRecT hA rc →
      ∀ τ, π.IsLocComp w τ → IsWDOf ι ρ (rc (algNorm τ)) := fun w hw A hA rc hrc τ hτ =>
    (((hLG w τ hτ).1 A hA rc hrc).1 hw).isWDOf (guard_of hPl hreg hatt (hW hc) (Or.inl hw) hrc hτ).2
  have hsph : ∀ (w : Plc L), ((l : ℕ) : 𝓞 L) ∉ w.asIdeal → ∀ (A : ValuationSubring Ω), IsPlaceOver A w →
      (∀ g ∈ Ine (F := L) A, ρ g = 1) → ∀ τ, π.IsLocComp w τ → Af.HasFixed τ.ρ (GlobalTheory.LFun.KGL w n) := fun w hw A hA hI τ hτ => by
    obtain ⟨rc, hrc⟩ := hEx L Ω A w hA
    exact hSph P.litN L Ω l ι n ρ hc w hw A hA hI rc hrc τ (guard_of hPl hreg hatt (hW hc) (Or.inl hw) hrc hτ).1
      (heq w hw A hA rc hrc τ hτ)
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
      obtain ⟨⟨τ, hτ⟩, hi⟩ := _root_.UpperTheory.V.Af.local_comp_complex_of_printed_results P L n π w
      obtain ⟨b, hb⟩ := (_root_.UpperTheory.V.Af.satake_local_of_printed_results P L n w τ).1 (hsph w (mt (hin w) hw) A hA (hI w hw A hA) τ hτ)
      exact ⟨b, ((_root_.UpperTheory.V.Af.satake_local_of_printed_results P L n w τ).2 _ π.finPart (hi τ hτ) b).2 hb⟩
  obtain ⟨hloc, hinf⟩ := hSame L Ω hE l ι n hn π ρ hc hatt σ hσ hsat
  choose τ₀ hτ₀ using fun w => (_root_.UpperTheory.V.Af.local_comp_complex_of_printed_results P L n π w).1
  choose rcl hrcl using fun v : Vl l L => hEx L Ω _ _ (s.hw v)
  have hg := fun v : Vl l L => guard_of hPl hreg hatt (hW hc)
    (Or.inr (Or.inl (hUn L Ω l n ρ _ _ (s.hw v) _ (hfl v).1 (hfl v).2))) (hrcl v) (hτ₀ (s.w v))
  have hab := fun v : Vl l L => above P hPs s.odd hc ((hLG _ _ (hτ₀ _)).2 (hg v).1) (s.hw v) (hlv v) (hLG _ _ (hτ₀ _)).1 (hrcl v)
    (hg v).1 (hg v).2 lam (hψ v) (hfl v).1 (hfl v).2
  have hcl : ∀ w, IsSplitAt w → ∀ τ : SmIrr (GLw n w), IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ →
      algNorm τ = algNorm (τ₀ w) := fun w hw τ hτ => by
    unfold algNorm
    rw [IrrGL.of_eq_of.2 (UpperTheory.building_component_uniqueness L n σ hσ w hw _ _ _ _ hτ (hloc w hw _ (hτ₀ w)))]
  refine _root_.UpperTheory.V.Z.Desc.W.upU_w_alt PH l L Ω s n hn V Q c r ι B Λ R K hS J hJ x h lam hx hlam σ ρ hσ hc hatt.1 hρ (fun w hs hw τ b hτ hb => ?_)
    (fun y => ?_) (fun w hw => ?_) ?_ (fun v => ?_) fun u τ hu hτ rc hrc => ?_
  · refine _root_.UpperTheory.V.Z.Desc.W.satFrobT_alt P L Ω l ι n ρ hc w hw τ b hb fun A hA rc hrc => ?_
    rw [hcl w hs τ hτ]
    exact ((hLG w _ (hτ₀ w)).1 A hA rc hrc).1 hw
  · obtain ⟨ν, h1, h2⟩ := hinf (ι.toRingHom.comp y.res)
    have h3 := hwt y.res
    rw [CG.HasInfChar.infChar_eq (π := CG.mk π) h2, show HT y.res = _ from (hab y.1).2 y.2] at h3
    rwa [← dual_of_weights (lam y.res) ν h3]
  · by_cases hs : IsSplitAt w
    · obtain ⟨A, hA⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A w := exists_isPlaceOver Ω w
      refine unram_of_fixed (hloc w hs _ (hτ₀ w)) ?_ (hsph w (mt (hin w) hw) A hA (hI w hw A hA) _ (hτ₀ w))
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
    obtain ⟨z, hz, hf⟩ := hsph _ hp _ (s.hw s.v0) h0 _ (hτ₀ _)
    refine ⟨τ₀ _, hloc _ hs _ (hτ₀ _), (Submodule.ne_bot_iff _).2 ⟨z, fun u hu => hf u ?_, hz⟩⟩
    rw [← GlobalTheory.HeckeEigConj.KO_eq_KGL]
    obtain ⟨u, -, rfl⟩ := hu
    exact ⟨u, rfl⟩
  · obtain ⟨ω, h1, h2⟩ := (hab v).1
    exact ⟨τ₀ _, ω, hloc _ (hsp _ (hin _ (hlv v))) _ (hτ₀ _), h1, h2⟩
  · rw [hcl _ (hsp _ (by rw [hwv]; exact V.sub (Or.inr (Or.inl u.2)))) τ hτ]
    exact heq _ hu _ (s.hw u) rc (_root_.UpperTheory.V.Z.Desc.W.isRecT_of_isRecT P hrc) _ (hτ₀ _)
end
