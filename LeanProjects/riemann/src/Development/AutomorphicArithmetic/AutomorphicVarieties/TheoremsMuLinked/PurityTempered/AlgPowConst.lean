import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.FreeFlag
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.MonoAt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.FlagAb
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.FlagPol
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaArith
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.EpsArt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LevelIso
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilRepEquivOfCharpolyEqStatement

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Th

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem pure_zero {n : ℕ} {q : ℝ} {c : Fin n → ℂ} (hp : IsPurePair q (diagEnd c) 0) (i : Fin n) : ‖c i‖ = 1 := by
  by_contra hi
  have hle : (⊤ : Submodule ℂ (Fin n → ℂ)) ≤ LinearMap.ker (LinearMap.proj i : (Fin n → ℂ) →ₗ[ℂ] ℂ) := by
    rw [← hp.1]
    refine iSup_le fun k v hv => ?_
    rcases lt_trichotomy k 0 with hk | rfl | hk
    · obtain ⟨j, rfl⟩ : ∃ j : ℕ, k = -((j + 1 : ℕ) : ℤ) := ⟨(-k - 1).toNat, by omega⟩
      have hv' : v ∈ absSpace (diagEnd c) (q ^ (-((j + 1 : ℕ) : ℝ) / 2)) := by
        rwa [Int.cast_neg, Int.cast_natCast] at hv
      rw [(hp.2 (j + 1)).2.1 hv' (zero_mem _) (by simp)]
      exact zero_mem _
    · exact (mem_absSpace_diagEnd c _ v).1 hv i (by simpa using hi)
    · obtain ⟨j, rfl⟩ : ∃ j : ℕ, k = ((j + 1 : ℕ) : ℤ) := ⟨(k - 1).toNat, by omega⟩
      rw [Int.cast_natCast] at hv
      obtain ⟨u, -, rfl⟩ := (hp.2 (j + 1)).2.2 hv
      simp
  simpa using hle (Submodule.mem_top (x := fun _ => 1))

section

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {w : HeightOneSpectrum (𝓞 F)} {A : ValuationSubring Ω} {h : IsPlaceOver A w}

private theorem norms_eq {n : ℕ} (x : WD h) (μ : Fin n → Weil h →* ℂˣ) (hμ : ∀ i, GlobalTheory.WeilDeligne.IsSmooth (μ i))
    (hx : ∀ s, x.charPol s = ∏ i, (X - C (μ i s : ℂ))) {t : ℝ} (ht : (x.lpTw t).tempered)
    (hor : (∀ i j, ∃ s, (μ i s : ℂ) ≠ ((normV w : ℕ) : ℂ) ^ deg s * μ j s) ∨ x.mono0) (s : Weil h) (i j : Fin n) :
    ‖(μ i s : ℂ)‖ = ‖(μ j s : ℂ)‖ := by
  obtain ⟨m, b, rfl⟩ := x.exists_rep
  obtain ⟨e, he⟩ := GlobalTheory.T.weilRep_equiv_of_charpoly_eq F Ω A w h m n b (WDRep.ofChars h μ hμ) fun σ => by
    rw [WDRep.ofChars_ρ, charpoly_diagEnd, ← hx, WD.charPol_mk]
  simp only [WDRep.ofChars_ρ] at he
  have hN : b.N = 0 := by
    rcases hor with hne | h0
    · have h1 : ∀ j, b.N (e.symm (Pi.single j 1)) = 0 := fun j => by
        refine e.map_eq_zero_iff.1 (funext fun i => ?_)
        obtain ⟨σ, hσ⟩ := hne i j
        have h2 : b.ρ σ (e.symm (Pi.single j 1)) = (μ j σ : ℂ) • e.symm (Pi.single j 1) := by
          refine e.injective ?_
          rw [he, map_smul, e.apply_symm_apply]
          funext k
          by_cases hk : k = j
          · subst hk; simp
          · simp [hk]
        have h3 := congrFun (congrArg e (b.comm_apply σ (e.symm (Pi.single j 1)))) i
        rw [he, h2, map_smul, map_smul, map_smul, diagEnd_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
          ← mul_assoc] at h3
        exact (mul_eq_mul_right_iff.1 h3).resolve_left hσ
      exact ((Pi.basisFun ℂ (Fin n)).map e.symm).ext fun j => by
        rw [Module.Basis.map_apply, Pi.basisFun_apply, h1, LinearMap.zero_apply]
    · exact (WD.monodromyZero_ofWeilDeligneRepClass_iff b).1 h0
  rw [WD.lpTw_mk, WD.tempered_mk] at ht
  have h1 : ∀ φ : Weil h, deg φ = 1 → ∀ k, ‖((normV w : ℕ) : ℂ) ^ (t : ℂ) * μ k φ‖ = 1 := fun φ hφ =>
    pure_zero ((ht φ hφ).of_equiv e (fun v => by
      rw [WDRep.tw_ρ, hφ, zpow_one, LinearMap.smul_apply, map_smul, he]
      funext k
      simp [mul_assoc]) fun v => by simp [hN])
  have hc : ‖((normV w : ℕ) : ℂ) ^ (t : ℂ)‖ ≠ 0 := fun h0 => by
    simpa [h0] using h1 (frob h) deg_frob i
  have h2 : ∀ φ : Weil h, deg φ = 1 → ‖(μ i φ : ℂ)‖ = ‖(μ j φ : ℂ)‖ := fun φ hφ =>
    mul_left_cancel₀ hc (by rw [← norm_mul, ← norm_mul, h1 φ hφ, h1 φ hφ])
  have h3 := h2 (s * frob h ^ (1 - deg s)) (by simp [deg_frob])
  simp only [map_mul, map_zpow, Units.val_mul, Units.val_zpow_eq_zpow_val, norm_mul, norm_zpow, h2 _ deg_frob] at h3
  exact mul_right_cancel₀ (zpow_ne_zero _ (norm_ne_zero_iff.2 (Units.ne_zero _))) h3

end

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

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
  {w : HeightOneSpectrum (𝓞 F)} {A : ValuationSubring Ω} {h : IsPlaceOver A w} {a : Weil h →* (w.adicCompletion F)ˣ}

private theorem cyc_cont : Continuous ((cycBar F Ω l).comp (Dec (F := F) A).subtype) :=
  ((Continuous.units_map ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom).toMonoidHom
    ((continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val)).comp (continuous_cycZ F Ω l)).comp continuous_subtype_val

private theorem ex_elt (H : GlobalTheory.Published.GlobalArtinReciprocity) (hw : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal) (ha : IsLocalArtin h a) :
    ∃ s : Weil h, deg s ≠ 0 ∧ cycZ F Ω l s = 1 := by
  haveI := GlobalTheory.HeckeGal.finite_contEmb (l := l) w
  haveI := Fintype.ofFinite (W.Emb l w)
  haveI : CompactSpace (Dec (F := F) A) := isCompact_iff_compactSpace.1 (isClosed_Dec A).isCompact
  haveI : CharZero (w.adicCompletion F) := algebraRat.charZero _
  have hl : (l : Qbar l) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  obtain ⟨s, hs⟩ := ha.surj (Units.mk0 (l : w.adicCompletion F) (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero))
  refine ⟨s, fun h0 => ?_, ?_⟩
  · have h2 := ha.ord_eq s
    rw [h0, neg_zero, hs] at h2
    haveI : (Valued.v : Valuation (w.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
      Valuation.Compatible.ofValuation _
    have h3 := (ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion F))
      (Valued.v : Valuation (w.adicCompletion F) (WithZero (Multiplicative ℤ)))).eq_one_iff_eq_one.1
      (GlobalTheory.SmGL.ord_eq_zero_iff.1 h2)
    have h4 : Valued.v (algebraMap F (w.adicCompletion F) (((l : ℕ) : 𝓞 F) : F)) < 1 := by
      rw [show Valued.v (algebraMap F (w.adicCompletion F) (((l : ℕ) : 𝓞 F) : F)) =
        w.valuation F (algebraMap (𝓞 F) F ((l : ℕ) : 𝓞 F)) from HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _]
      exact (HeightOneSpectrum.valuation_lt_one_iff_mem w _).2 hw
    refine h4.ne (Eq.trans ?_ h3)
    simp
  · have h1 := UpperTheory.V.Loc.epsArt H h hw a ha s
    rw [hs, Hi.algPow, finprod_eq_prod_of_fintype, GlobalTheory.Pst.normV_eq_pow (l := l) hw] at h1
    simp only [Units.val_mk0, map_natCast, zpow_one, Finset.prod_const, Nat.cast_pow] at h1
    rw [← zpow_natCast, ← zpow_mul, ← zpow_natCast, ← zpow_add₀ hl] at h1
    have h2 : ‖(cycBar F Ω l s : Qbar l)‖ = 1 :=
      norm_one _ (Units.continuous_val.comp (cyc_cont (F := F) (A := A) (l := l))) (Subgroup.inclusion (Weil_le_Dec h) s)
    rw [h1, norm_zpow] at h2
    rw [(zpow_eq_one_iff_right₀ (norm_nonneg _) (GlobalTheory.PlaceBridge.norm_l_lt_one (l := l)).ne).1 h2, zpow_zero] at h1
    refine Units.ext (Subtype.ext ((algebraMap ℚ_[l] (Qbar l)).injective (Eq.trans h1 ?_)))
    simp

private theorem algPow_const (c : ℤ) (y : w.adicCompletion F) :
    Hi.algPow (l := l) w (-fun _ => -c) y = Hi.algPow w (fun _ => 1) y ^ c := by
  haveI := GlobalTheory.HeckeGal.finite_contEmb (l := l) w
  haveI := Fintype.ofFinite (W.Emb l w)
  unfold Hi.algPow
  rw [finprod_eq_prod_of_fintype, finprod_eq_prod_of_fintype, ← Finset.prod_zpow]
  exact Finset.prod_congr rfl fun j _ => by rw [Pi.neg_apply, neg_neg, zpow_one]

private theorem flag_cont {n : ℕ} {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] {r : Γ →* GL (Fin n) (Qbar l)}
    (hr : Continuous r) {ψ : Fin n → Γ →* (Qbar l)ˣ} (hf : W.HasFlag r ψ) (i : Fin n) : Continuous (ψ i) := by
  obtain ⟨g, hg⟩ := hf
  have h1 : Continuous fun s => (ψ i s : Qbar l) :=
    ((Units.continuous_val.comp ((continuous_const.mul hr).mul continuous_const)).matrix_elem i i).congr fun s => (hg s).2 i
  exact Units.continuous_iff.2 ⟨h1, (h1.comp continuous_inv).congr fun s => by simp⟩

end

theorem UpperTheory.V.Th.purLocS :
    Af.Hypotheses₂ → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (ι : Qbar l ≃+* ℂ) (n : ℕ) (r : G F Ω →* GL (Fin n) (Qbar l)), Continuous r → ∀ (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A w), ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → ∀ x : WD h, (∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : Induces Bw), IsPstAt (Loc.PP l) Bw (r.comp (Dec (F := F) A).subtype) ∧ Lev.SsCmp (wdAt (Loc.PP l) ι Bw h hj (r.comp (Dec (F := F) A).subtype)) x) → (∃ t : ℝ, (x.lpTw t).tempered) → ∀ (ψ : Fin n → Dec (F := F) A →* (Qbar l)ˣ) (m : Fin n → ℤ) (k : ℕ), W.HasFlag (r.comp (Dec (F := F) A).subtype) ψ → StrictAnti m → 0 < k → (∀ i (g : Dec (F := F) A), (g : G F Ω) ∈ Ine (F := F) A → (ψ i g * cycBar F Ω l g ^ (-m i)) ^ k = 1) → ((∀ i j, ψ i ≠ ψ j * (cycBar F Ω l).comp (Dec (F := F) A).subtype) ∨ x.mono0) → ∃ g : Dec (F := F) A, cycZ F Ω l g = 1 ∧ Pr.FreeRatios fun i => ψ i g := by
  intro P F Ω _ _ _ _ _ l _ _ ι n r hr w A h hw x hx ⟨t, ht⟩ ψ m k hf hm hk hI hor
  have hN := P.litN
  have H := hN.aut.art
  obtain ⟨rc, a, ha, -⟩ := P.exists_rec h
  obtain ⟨O, _, _, _, Bw, hj⟩ := Af.exists_bridge (l := l) h hw
  obtain ⟨hp, hcmp⟩ := hx O Bw hj
  have hc : Continuous (r.comp (Dec (F := F) A).subtype) := hr.comp continuous_subtype_val
  have hψc := flag_cont hc hf
  choose ω hω using fun i => (Loc.ordCharIff H h ι a ha (fun _ => -m i) (ψ i)).1.2
    ⟨hψc i, Loc.laArith H h hw (ψ i) (hψc i) (m i) k hk (hI i)⟩
  have hpol : ∀ s, (wdAt (Loc.PP l) ι Bw h hj (r.comp (Dec (F := F) A).subtype)).charPol s =
      ∏ i, (X - C (((ω i).comp a) s : ℂ)) := fun s => by
    obtain ⟨M, hM⟩ := hf
    obtain ⟨T⟩ := UpperTheory.V.Loc.tiedP l
    have hc := fun i => (UpperTheory.V.Loc.charDR hN h hw ι a ha (ω i) _ (ψ i) (hω i)).1 O Bw hj
    obtain ⟨-, F₂⟩ := UpperTheory.V.Loc.PstExact.flag T ι Bw h hj _ (fun i => GlobalTheory.TripleGal.rk1 (ψ i)) M
      (fun g => (hM g).1) (fun g i => ((hM g).2 i).trans (by simp [GlobalTheory.TripleGal.rk1]))
    rw [(F₂ hp).2 s]
    exact Finset.prod_congr rfl fun i _ => (hc i).2.2 s
  have hxp := fun s => (hcmp (Or.inl ((Lev.ssCalc F Ω A w h).1 n _ _ hpol)) s).symm.trans (hpol s)
  let inc := Subgroup.inclusion (Weil_le_Dec h)
  let ε : ↥(Dec (F := F) A) →* (Qbar l)ˣ := (cycBar F Ω l).comp (Dec (F := F) A).subtype
  let χ : Fin n → ↥(Dec (F := F) A) →* (Qbar l)ˣ := fun i => ψ i * ε ^ (-m i)
  have hχc : ∀ i, Continuous (χ i) := fun i => (hψc i).mul ((continuous_zpow (-m i)).comp cyc_cont)
  have hq : ((normV w : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (one_lt_normV w).ne_bot
  have hq' : ((normV w : ℕ) : Qbar l) ≠ 0 := Nat.cast_ne_zero.mpr (one_lt_normV w).ne_bot
  have hμ : ∀ i s, (((ω i).comp a) s : ℂ) = ((normV w : ℕ) : ℂ) ^ (m i * deg s) * ι (χ i (inc s) : Qbar l) := fun i s => by
    have h1 : (ψ i (inc s) : Qbar l) = ι.symm (ω i (a s)) * Hi.algPow w (-fun _ => -m i) (a s : w.adicCompletion F) :=
      (hω i).val s _ rfl (Set.mem_univ _)
    have h2 : (ε (inc s) : Qbar l) = _ := UpperTheory.V.Loc.epsArt H h hw a ha s
    have h3 : Hi.algPow (l := l) w (fun _ => 1) (a s : w.adicCompletion F) ≠ 0 := fun h0 =>
      (ε (inc s)).ne_zero (by rw [h2, h0, mul_zero])
    have h4 : (χ i (inc s) : Qbar l) = (ψ i (inc s) : Qbar l) * (ε (inc s) : Qbar l) ^ (-m i) := by simp [χ]
    have h5 : (χ i (inc s) : Qbar l) = ι.symm (ω i (a s)) * ((normV w : ℕ) : Qbar l) ^ (-(m i * deg s)) := by
      rw [h4, h1, h2, algPow_const, mul_zpow, ← zpow_mul, mul_mul_mul_comm, ← zpow_add₀ h3, add_neg_cancel, zpow_zero, mul_one,
        mul_neg, mul_comm (deg s)]
    rw [h5, map_mul, ι.apply_symm_apply, map_zpow₀, map_natCast, mul_left_comm, ← zpow_add₀ hq, add_neg_cancel, zpow_zero, mul_one]
    rfl
  obtain ⟨s, hs, hs1⟩ := ex_elt H hw ha
  refine ⟨inc s, hs1, fun i j hij N hN0 e => hij ?_⟩
  have hn := norms_eq x _ (fun i => ha.smooth (hω i).smooth) hxp ht (hor.imp_left fun hne i j => by
    by_contra hij
    simp only [not_exists, not_not, hμ] at hij
    obtain ⟨ha, h1⟩ := UpperTheory.continuous_character_compact_unit_values F Ω l ι w A h hw (χ i * (χ j)⁻¹) (1 + m j - m i)
      (Units.continuous_val.comp ((hχc i).mul (hχc j).inv)) (fun σ => by
        have h2 := hij σ
        have h3 : ι (χ j (inc σ) : Qbar l) ≠ 0 := (map_ne_zero ι).mpr (Units.ne_zero _)
        have h4 : ((normV w : ℕ) : ℂ) ^ (m i * deg σ) ≠ 0 := zpow_ne_zero _ hq
        change ι ((χ i (inc σ) * (χ j (inc σ))⁻¹ : (Qbar l)ˣ) : Qbar l) = _
        rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, sub_mul, add_mul, one_mul, zpow_sub₀ hq,
          zpow_add₀ hq, mul_inv_eq_iff_eq_mul₀ h3, div_mul_eq_mul_div, eq_div_iff h4, mul_comm, mul_assoc]
        exact h2)
    refine hne i j ?_
    have h5 : χ i = χ j := mul_inv_eq_one.mp h1
    have h6 : -m j = 1 + -m i := by omega
    simp only [χ] at h5
    rw [h6, zpow_add, zpow_one, ← mul_assoc] at h5
    exact mul_right_cancel h5) s i j
  have h7 : ε (inc s) = 1 := congrArg (Units.map ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom).toMonoidHom) hs1 |>.trans
    (map_one _)
  have h8 : ∀ i, χ i (inc s) = ψ i (inc s) := fun i => by simp [χ, h7]
  have h9 : ‖ι (ψ i (inc s) : Qbar l)‖ = ‖ι (ψ j (inc s) : Qbar l)‖ := by
    refine (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) hN0.ne').1 ?_
    rw [← norm_pow, ← norm_pow, ← map_pow, ← map_pow, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val]
    exact congrArg (fun u : (Qbar l)ˣ => ‖ι (u : Qbar l)‖) e
  rw [hμ, hμ, h8, h8, norm_mul, norm_mul, h9, norm_zpow, norm_zpow, Complex.norm_natCast] at hn
  have h10 := mul_right_cancel₀ (norm_ne_zero_iff.2 ((map_ne_zero ι).mpr (Units.ne_zero _))) hn
  have hq1 : (1 : ℝ) < (normV w : ℕ) := by exact_mod_cast one_lt_normV w
  exact hm.injective (mul_right_cancel₀ hs (zpow_right_injective₀ (zero_lt_one.trans hq1) hq1.ne' h10))
