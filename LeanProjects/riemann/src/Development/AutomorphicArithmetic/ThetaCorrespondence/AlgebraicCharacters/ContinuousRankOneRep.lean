import Development.AutomorphicArithmetic.ThetaCorrespondence.AlgebraicCharacters.ChBasic
import Development.AutomorphicArithmetic.ThetaCorrespondence.AlgebraicCharacters.ChCoef
import Development.AutomorphicArithmetic.ThetaCorrespondence.AlgebraicCharacters.EmbOrbitAlt
import Development.AutomorphicArithmetic.ThetaCorrespondence.AlgebraicCharacters.WdAtModel
import Development.AutomorphicArithmetic.ThetaCorrespondence.AlgebraicCharacters.ArtNorm
import Development.AutomorphicArithmetic.ThetaCorrespondence.AlgebraicCharacters.ExField
import Development.AutomorphicArithmetic.ThetaCorrespondence.AlgebraicCharacters.EmbOrbit
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaWDUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaDeRham
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteEmb
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.EpsArt
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaCyc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenKerOfInfConn
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRecLawsSuppUnitSurj
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal
open GlobalTheory.LocLanglands GlobalTheory.Published GlobalTheory.Pst GlobalTheory.TripleGal UpperTheory.V.W UpperTheory.V
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace UpperTheory.Lit.CharWD

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
  {A : ValuationSubring Ω} {w : Plc F}

private instance embFin : Fintype (Emb l w) := haveI := finite_contEmb (l := l) w; Fintype.ofFinite _

private def alg (wt : Emb l w → ℤ) : (w.adicCompletion F)ˣ →* (Qbar l)ˣ :=
  ∏ τ : Emb l w, (Units.map τ.1.toMonoidHom) ^ wt τ

private theorem alg_val (wt : Emb l w → ℤ) (x : (w.adicCompletion F)ˣ) :
    (alg wt x : Qbar l) = ∏ᶠ τ : Emb l w, τ.1 (x : w.adicCompletion F) ^ wt τ := by
  rw [finprod_eq_prod_of_fintype]
  simp [alg]

private theorem alg_add (wt wt' : Emb l w → ℤ) : alg (wt + wt') = alg wt * alg wt' := by
  simp [alg, zpow_add, Finset.prod_mul_distrib]

private theorem alg_cont (wt : Emb l w → ℤ) : Continuous (alg wt) := by
  have : (alg wt : _ → _) = fun x => ∏ τ : Emb l w, (Units.map τ.1.toMonoidHom x) ^ wt τ := by
    funext x; simp [alg]
  rw [this]
  exact continuous_finset_prod _ fun τ _ => (Continuous.units_map _ τ.2).zpow _

private theorem cont_gq (s : GQ l) : Continuous s := by
  refine (AddMonoidHomClass.isometry_of_norm s fun x => ?_).continuous
  exact (spectralNorm_eq_of_equiv s x).symm

private theorem norm_lt (τ : Emb l w) (u : w.adicCompletion F) (hu : Valued.v u < 1) : ‖τ.1 u‖ < 1 := by
  have h1 := (τ.2.tendsto 0).comp (Valued.tendsto_zero_pow_of_v_lt_one hu)
  rw [map_zero] at h1
  rw [← tendsto_pow_atTop_nhds_zero_iff_norm_lt_one]
  simpa [Function.comp_def] using h1

private theorem ord_zero [Nonempty (Emb l w)] (u : (w.adicCompletion F)ˣ) (hu : alg (l := l) (fun _ => 1) u = 1) :
    GlobalTheory.SmGL.ord (w.adicCompletion F) u = 0 := by
  have key : ∀ u : (w.adicCompletion F)ˣ, alg (l := l) (fun _ => 1) u = 1 → ¬ Valued.v (u : w.adicCompletion F) < 1 := by
    intro u hu h
    have h1 := alg_val (l := l) (fun _ => 1) u
    rw [hu, finprod_eq_prod_of_fintype] at h1
    have h2 := congrArg norm h1
    simp only [Units.val_one, norm_one, zpow_one, norm_prod] at h2
    refine absurd h2.symm (ne_of_lt ?_)
    obtain ⟨τ⟩ := ‹Nonempty (Emb l w)›
    have := Finset.prod_lt_prod_of_nonempty (s := Finset.univ) (f := fun τ : Emb l w => ‖τ.1 u‖) (g := fun _ => 1)
      (fun τ _ => by simp) (fun τ _ => norm_lt τ u h) ⟨τ, by simp⟩
    simpa using this
  have h1 := key u hu
  have h2 := key u⁻¹ (by rw [map_inv, hu, inv_one])
  rw [Units.val_inv_eq_inv_val, map_inv₀, inv_lt_one₀ (by simp [zero_lt_iff])] at h2
  haveI : (Valued.v : Valuation (w.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact GlobalTheory.SmGL.ord_eq_zero_iff.2 ((ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion F))
      (Valued.v : Valuation (w.adicCompletion F) (WithZero (Multiplicative ℤ)))).eq_one_iff_eq_one.2
      (le_antisymm (not_lt.1 h2) (not_lt.1 h1)))

private theorem continuous_rank_one_rep {Γ K : Type} [Group Γ] [TopologicalSpace Γ] [Field K] [TopologicalSpace K] (μ : Γ →* Kˣ)
    (hμ : Continuous μ) : Continuous fun g => ((rk1 μ g : GL (Fin 1) K) : Matrix (Fin 1) (Fin 1) K) := by
  refine continuous_matrix fun i j => ?_
  fin_cases i; fin_cases j
  simpa [rk1, Function.comp_def] using Units.continuous_val.comp hμ

variable (ι : Qbar l ≃+* ℂ) (h : IsPlaceOver A w)
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O)
  (hj : GlobalTheory.Pst.Induces Bw) (a : Weil h →* (w.adicCompletion F)ˣ)

private def Df (wt : Emb l w → ℤ) (d : Weil h →* (Qbar l)ˣ) : Prop :=
  ∀ κ : ↥(Dec (F := F) A) →* (Qbar l)ˣ, Continuous κ → IsLocAlg h κ wt →
    WDis (Loc.PP l) ι h Bw hj κ (κ.comp (Subgroup.inclusion (Weil_le_Dec h)) * (alg wt).comp a * d)

variable (hG : GlobalArtinReciprocity) (hD : HeckeLAdicCharacterDeRham) (hP : DeRhamPotSemistable) (hB : ChBasic)
include hG hD hP hj in
private theorem pst (ν : ↥(Dec (F := F) A) →* (Qbar l)ˣ) (hν : Continuous ν) {wt : Emb l w → ℤ} (H : IsLocAlg h ν wt) :
    IsPstAt (Loc.PP l) Bw (rk1 ν) := by
  obtain ⟨T⟩ := Loc.tiedP l
  exact hP.isPstAt T Bw _ (continuous_rank_one_rep ν hν) (Loc.laDeRham hG hG.heckeLAdicCharacter hD hP h ν hν wt H O Bw hj).1

include hG Bw hj ι in
private theorem exw (wt : Emb l w → ℤ) : ∃ ν : ↥(Dec (F := F) A) →* (Qbar l)ˣ, Continuous ν ∧ IsLocAlg h ν wt := by
  obtain ⟨E, _, _, _, _, u, hu, Bw', art, χ, n, μ, ν, -, -, -, -, -, -, -, hν, -, H, -⟩ :=
    Loc.laGlob hG hG.heckeLAdicCharacter h wt Bw hj ι
  exact ⟨ν, hν, H⟩

include hG hD hP in
private theorem df_zero (ha : IsLocalArtin h a) : Df ι h Bw hj a 0 1 := by
  intro ψ hψ H
  have pψ := pst h Bw hj hG hD hP ψ hψ H
  obtain ⟨ph, hph, eph⟩ := H
  have sψ : IsSmooth (ψ.comp (Subgroup.inclusion (Weil_le_Dec h))) := by
    refine .of_open hph (by simp) fun σ hσ => Units.ext ?_
    have h1 := eph a ha σ
    have h3 : ph σ = 1 := hσ
    simpa [h3] using h1
  have e : ψ.comp (Subgroup.inclusion (Weil_le_Dec h)) * (alg (0 : Emb l w → ℤ)).comp a * 1 =
      ψ.comp (Subgroup.inclusion (Weil_le_Dec h)) := by
    ext; simp [alg]
  rw [e]
  exact ⟨pψ, sψ.of_le fun σ hσ => by rw [MonoidHom.comp_apply, hσ, map_one],
    ParamAboveModel.eq_lpOfChar h _ (GlobalTheory.Pst.Test.lpDim_wdAt _ ι Bw h hj _) _ _
      (Loc.wdPotUnr h Bw hj ι ψ hψ sψ pψ)⟩

include hG hD hP hB in
private theorem df_of (ha : IsLocalArtin h a) {wt : Emb l w → ℤ} {d : Weil h →* (Qbar l)ˣ}
    (ν : ↥(Dec (F := F) A) →* (Qbar l)ˣ) (hν : Continuous ν) (H : IsLocAlg h ν wt)
    (hw : WDis (Loc.PP l) ι h Bw hj ν (ν.comp (Subgroup.inclusion (Weil_le_Dec h)) * (alg wt).comp a * d)) :
    Df ι h Bw hj a wt d := by
  intro κ hκ Hκ
  have pκ := pst h Bw hj hG hD hP κ hκ Hκ
  obtain ⟨ph, hph⟩ := H
  obtain ⟨ph', hph'⟩ := Hκ
  have h0 := ((Loc.laMul h).1 _ _ _ _ _ _ hph' ((Loc.laMul h).1 _ _ _ _ _ _ hph hph).2).1
  rw [add_neg_cancel] at h0
  have hψ : Continuous (κ * ν⁻¹ : ↥(Dec (F := F) A) →* (Qbar l)ˣ) := hκ.mul hν.inv
  have e : κ * ν⁻¹ * ν = κ := inv_mul_cancel_right _ _
  have := (hB ι h Bw hj).2.1 _ _ _ _ hψ hν (df_zero ι h Bw hj a hG hD hP ha _ hψ ⟨_, h0⟩) hw (by rwa [e])
  rw [e] at this
  convert this using 1
  ext; simp [alg, mul_assoc]

include hG hB in
private theorem df_uniq {wt : Emb l w → ℤ} {d d' : Weil h →* (Qbar l)ˣ}
    (H : Df ι h Bw hj a wt d) (H' : Df ι h Bw hj a wt d') : d = d' := by
  obtain ⟨ν, hν, Hν⟩ := exw ι h Bw hj hG wt
  exact mul_left_cancel (((hB ι h Bw hj).1 ν hν (H ν hν Hν).1).unique (H ν hν Hν) (H' ν hν Hν))

include hG hD hP hB in
private theorem df_ex (ha : IsLocalArtin h a) : ∃ δ : (Emb l w → ℤ) →+ Additive (Weil h →* (Qbar l)ˣ),
    ∀ wt, Df ι h Bw hj a wt (δ wt).toMul := by
  have H : ∀ wt, ∃ d, Df ι h Bw hj a wt d := fun wt => by
    obtain ⟨ν, hν, Hν⟩ := exw ι h Bw hj hG wt
    obtain ⟨ξ, hξ, -⟩ := (hB ι h Bw hj).1 ν hν (pst h Bw hj hG hD hP ν hν Hν)
    exact ⟨_, df_of ι h Bw hj a hG hD hP hB ha ν hν Hν (by rwa [mul_inv_cancel_left])⟩
  choose d hd using H
  refine ⟨AddMonoidHom.mk' (fun wt => Additive.ofMul (d wt)) fun wt wt' => ?_, hd⟩
  obtain ⟨ν, hν, ph, Hν⟩ := exw ι h Bw hj hG wt
  obtain ⟨ν', hν', ph', Hν'⟩ := exw ι h Bw hj hG wt'
  have H2 : IsLocAlg h (ν * ν') (wt + wt') := ⟨_, ((Loc.laMul h).1 _ _ _ _ _ _ Hν Hν').1⟩
  refine congrArg Additive.ofMul (df_uniq ι h Bw hj a hG hB (hd _) (d' := d wt * d wt')
    (df_of ι h Bw hj a hG hD hP hB ha _ (hν.mul hν') H2 ?_))
  convert (hB ι h Bw hj).2.1 _ _ _ _ hν hν' (hd _ ν hν ⟨_, Hν⟩) (hd _ ν' hν' ⟨_, Hν'⟩)
    (pst h Bw hj hG hD hP _ (hν.mul hν') H2) using 1
  ext1
  simp only [alg_add, MonoidHom.mul_apply, MonoidHom.comp_apply]
  ac_rfl

private theorem hom_sum {M : Type} [CommGroup M] (δ : (Emb l w → ℤ) →+ Additive M) (wt : Emb l w → ℤ) [DecidableEq (Emb l w)] :
    (δ wt).toMul = ∏ τ : Emb l w, (δ (Pi.single τ 1)).toMul ^ wt τ := by
  conv_lhs => rw [pi_eq_sum_univ' wt]
  simp only [map_sum, map_zsmul, toMul_sum, toMul_zsmul]

include hG hB in
private theorem df_coef (hC : ChCoef) [DecidableEq (Emb l w)] {d d' : Weil h →* (Qbar l)ˣ} (s : GQ l) (τ τ' : Emb l w)
    (hs : ∀ x, τ'.1 x = s (τ.1 x)) (H : Df ι h Bw hj a (Pi.single τ 1) d) (H' : Df ι h Bw hj a (Pi.single τ' 1) d')
    (σ : Weil h) : (d' σ : Qbar l) = s (d σ) := by
  obtain ⟨ν, hν, ph, Hν⟩ := exw ι h Bw hj hG (Pi.single τ 1)
  have k : ∀ (τ : Emb l w) (x : w.adicCompletion F) (f : ℤ → ℤ), f 0 = 0 →
      ∏ᶠ t : Emb l w, t.1 x ^ f (Pi.single (M := fun _ => ℤ) τ 1 t) = τ.1 x ^ f 1 := fun τ x f hf => by
    rw [finprod_eq_single _ τ fun t ht => by simp [Pi.single_eq_of_ne ht, hf]]
    simp
  let S : (Qbar l)ˣ →* (Qbar l)ˣ := Units.map (s : Qbar l →* Qbar l)
  have hν' : Continuous (S.comp ν) := (Continuous.units_map _ (cont_gq s)).comp hν
  have H2 : IsLocAlg h (S.comp ν) (Pi.single τ' 1) := by
    refine ⟨S.comp ph, Subgroup.isOpen_mono (fun x hx => ?_) Hν.1, fun b hb x => ?_⟩
    · rw [MonoidHom.mem_ker] at hx ⊢
      rw [MonoidHom.comp_apply, hx, map_one]
    · have := Hν.2 b hb x
      rw [k τ _ (fun n => -n) rfl] at this
      rw [k τ' _ (fun n => -n) rfl, hs, ← map_zpow₀, ← this]
      simp [S]
  have e := DFunLike.congr_fun (((hB ι h Bw hj).1 _ hν' (H' _ hν' H2).1).unique (H' _ hν' H2)
    (hC ι h Bw hj s ν _ hν (H ν hν ⟨ph, Hν⟩))) σ
  have e' := congrArg Units.val e
  simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, Units.val_mul, map_mul, alg_val, S, Units.coe_map,
    MonoidHom.coe_coe, k _ _ (fun n => n) rfl, zpow_one, hs] at e'
  exact mul_left_cancel₀ (by simp) e'

include hG hB in
private theorem df_cyc (ha : IsLocalArtin h a) {d : Weil h →* (Qbar l)ˣ} (H : Df ι h Bw hj a (fun _ => -1) d) : d = 1 := by
  have hl := Loc.natCast_mem_of_induces h Bw hj
  have hc : Continuous ((cycBar F Ω l).comp (Dec (F := F) A).subtype) :=
    ((Continuous.units_map _ (show Continuous (fun x : ℤ_[l] => algebraMap ℚ_[l] (Qbar l) (x : ℚ_[l])) from
      (continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val)).comp (continuous_cycZ F Ω l)).comp
      continuous_subtype_val
  refine MonoidHom.ext fun σ => Units.ext ?_
  have h1 := (hB ι h Bw hj).2.2 _ (H _ hc ⟨_, Loc.laCyc hG h hl⟩) σ
  have h2 := Loc.epsArt hG h hl a ha σ
  have h3 : Hi.algPow w (fun _ => 1) (a σ : w.adicCompletion F) = (alg (l := l) (fun _ => 1) (a σ) : Qbar l) :=
    (alg_val _ _).symm
  have h4 : alg (l := l) (fun _ => 1) (a σ) * alg (l := l) (fun _ => -1) (a σ) = 1 := by
    rw [← MonoidHom.mul_apply, ← alg_add]
    simp [alg]
  have h5 : ((normV w : ℕ) : Qbar l) ^ deg σ ≠ 0 := zpow_ne_zero _ (Nat.cast_ne_zero.2 (one_lt_normV w).ne_bot)
  simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, Units.val_mul] at h1
  change (cycBar F Ω l (σ : G F Ω) : Qbar l) * _ * _ = _ at h1
  rw [h2, h3, mul_assoc (_ ^ _), ← Units.val_mul, h4, Units.val_one, mul_one] at h1
  exact mul_left_cancel₀ h5 (h1.trans (mul_one _).symm)

include hG hB in
private theorem df_unit (hC : ChCoef) (hE : EmbOrbit) (ha : IsLocalArtin h a)
    (δ : (Emb l w → ℤ) →+ Additive (Weil h →* (Qbar l)ˣ)) (hδ : ∀ wt, Df ι h Bw hj a wt (δ wt).toMul) (σ : Weil h) :
    ∃ s : Weil h, deg s = 0 ∧ ∀ wt, (δ wt).toMul σ = alg wt (a s) := by
  classical
  rcases isEmpty_or_nonempty (Emb l w) with hn | hn
  · exact ⟨1, deg_one, fun wt => by simp [Subsingleton.elim wt 0]⟩
  obtain ⟨u, hu⟩ := hE l w (fun τ => ((δ (Pi.single τ 1)).toMul σ : Qbar l))
    (fun s τ τ' hs => df_coef ι h Bw hj a hG hB hC s τ τ' hs (hδ _) (hδ _) σ) hn
  have h0 : u ≠ 0 := by
    rintro rfl
    obtain ⟨τ⟩ := hn
    simpa using hu τ
  obtain ⟨s, hs⟩ := ha.surj (Units.mk0 u h0)
  have k : ∀ wt, (δ wt).toMul σ = alg wt (a s) := fun wt => by
    rw [hom_sum, hs]
    refine Units.ext ?_
    simp [alg, hu]
  refine ⟨s, ?_, k⟩
  rw [← neg_eq_zero, ← ha.ord_eq]
  refine ord_zero (l := l) _ ?_
  rw [← k, show (fun _ => 1 : Emb l w → ℤ) = -fun _ => -1 from rfl, map_neg, toMul_neg,
    df_cyc ι h Bw hj a hG hB ha (hδ _)]
  simp

include hG hD hP hB in
private theorem df_res (hC : ChCoef) (hE : EmbOrbit) (hR : ChRes) (hN : ArtNorm) (ha : IsLocalArtin h a)
    {F' : Type} [Field F'] [NumberField F'] [Algebra F F'] [Algebra F' Ω] [IsScalarTower F F' Ω] [IsAlgClosure F' Ω]
    {w' : Plc F'} (h' : IsPlaceOver A w') {wt : Emb l w → ℤ} {d : Weil h →* (Qbar l)ˣ} (H : Df ι h Bw hj a wt d)
    (σ : Weil h) (σ' : Weil h') (hσ : ∀ z, (σ : G F Ω) z = (σ' : G F' Ω) z) :
    ∃ (s : Weil h) (s' : Weil h'), deg s' = 0 ∧ (∀ z, (s : G F Ω) z = (s' : G F' Ω) z) ∧ d σ = alg wt (a s) := by
  classical
  obtain ⟨O', _, _, _, Bw', hj', hres⟩ := hR ι h h' Bw hj
  obtain ⟨res, N, -, hN1, hN2⟩ := hN l h h' (Loc.natCast_mem_of_induces h Bw hj)
  obtain ⟨a', ha'⟩ := Loc.laArtin hG h'
  obtain ⟨δ, hδ⟩ := df_ex ι h' Bw' hj' a' hG hD hP hB ha'
  obtain ⟨s', hs', k⟩ := df_unit ι h' Bw' hj' a' hG hB hC hE ha' δ hδ σ'
  have kN : ∀ (m : Emb l w → ℤ) y, alg m (N y) = alg (m ∘ res) y := fun m y => by
    refine Units.ext ?_
    simp only [alg_val, hN1, finprod_eq_prod_of_fintype, finprod_eq_if]
    rw [← Finset.prod_fiberwise Finset.univ res]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← Finset.prod_filter, ← Finset.prod_zpow]
    exact Finset.prod_congr rfl fun t ht => by rw [Function.comp_apply, (Finset.mem_filter.1 ht).2]
  let r : G F' Ω →* G F Ω := AlgEquiv.restrictScalarsHom F
  have hr : Continuous r := Af.continuous_restrictScalarsHom _ _ _
  let rD : Dec (F := F') A →* Dec (F := F) A := (r.comp (Dec (F := F') A).subtype).codRestrict _ fun g => g.2
  let rI : Ine (F := F') A →* Ine (F := F) A := (r.comp (Ine (F := F') A).subtype).codRestrict _ fun g => g.2
  have hrD : Continuous rD := (hr.comp continuous_subtype_val).subtype_mk _
  have hrI : Continuous rI := (hr.comp continuous_subtype_val).subtype_mk _
  obtain ⟨ν, hν, ph, Hν⟩ := exw ι h Bw hj hG wt
  have hν' : Continuous (ν.comp rD) := hν.comp hrD
  have H2 : IsLocAlg h' (ν.comp rD) (wt ∘ res) := by
    refine ⟨ph.comp rI, Hν.1.preimage hrI, fun b hb x => ?_⟩
    have h1 := Hν.2 a ha (rI x)
    rw [hN2 a b ha hb _ (ineIncl h' x) fun _ => rfl] at h1
    exact h1.trans ((alg_val (-wt) _).symm.trans ((congrArg _ (kN _ _)).trans (alg_val _ _)))
  have hνν : ∀ (g : ↥(Dec (F := F) A)) (g' : ↥(Dec (F := F') A)), (∀ z, (g : G F Ω) z = (g' : G F' Ω) z) →
      ν g = ν.comp rD g' := fun g g' hg => congrArg ν (Subtype.ext (AlgEquiv.ext hg))
  obtain ⟨ξ', h1, h2⟩ := hres ν _ hν hνν _ (H ν hν ⟨ph, Hν⟩)
  have h3 := h2 σ σ' hσ
  rw [((hB ι h' Bw' hj').1 _ hν' h1.1).unique h1 (hδ _ _ hν' H2)] at h3
  simp only [MonoidHom.mul_apply] at h3
  rw [MonoidHom.comp_apply, hνν _ (Subgroup.inclusion (Weil_le_Dec h') σ') hσ, MonoidHom.comp_apply (alg wt),
    hN2 a a' ha ha' σ σ' hσ, kN] at h3
  refine ⟨ineIncl h (rI ⟨_, deg_eq_zero_iff.1 hs'⟩), s', hs', fun _ => rfl, ?_⟩
  rw [hN2 a a' ha ha' _ s' fun _ => rfl, kN, ← k]
  exact mul_left_cancel h3

include hG hD hP hB in
private theorem df_one (hC : ChCoef) (hE : EmbOrbit) (hR : ChRes) (hN : ArtNorm) (hX : ExField) (ha : IsLocalArtin h a)
    {wt : Emb l w → ℤ} {d : Weil h →* (Qbar l)ˣ} (H : Df ι h Bw hj a wt d) : d = 1 := by
  have k : ∀ σ, deg σ = -1 → d σ = 1 := fun σ hσ => by
    by_contra hc
    obtain ⟨F', _, _, w', h', ⟨σ', hσ'⟩, hV⟩ := hX h a ha σ hσ {x | alg wt x ≠ d σ}
      ((isOpen_ne_fun (alg_cont wt) continuous_const).mem_nhds (by simpa using Ne.symm hc))
    obtain ⟨s, s', h1, h2, h3⟩ := df_res ι h Bw hj a hG hD hP hB hC hE hR hN ha h' H σ σ' hσ'
    exact hV s s' h1 h2 h3.symm
  have k1 : d (frob h) = 1 := by simpa using k (frob h)⁻¹ (by simp)
  refine MonoidHom.ext fun σ => ?_
  simpa [k1] using k (frob h ^ (-deg σ - 1) * σ) (by simp; ring)

private theorem core (hG : GlobalArtinReciprocity) (hD : HeckeLAdicCharacterDeRham) (hP : DeRhamPotSemistable) (hB : ChBasic)
    (hC : ChCoef) (hE : EmbOrbit) (hR : ChRes) (hN : ArtNorm) (hX : ExField) : LocWD := by
  intro F Ω _ _ _ _ _ l _ A w ι h O _ _ _ Bw hj a ha κ hκ wt hwt
  obtain ⟨δ, hδ⟩ := df_ex ι h Bw hj a hG hD hP hB ha
  refine ⟨_, hδ wt κ hκ hwt, fun σ => ?_⟩
  rw [df_one ι h Bw hj a hG hD hP hB hC hE hR hN hX ha (hδ wt), mul_one, ← alg_val]
  rfl

end UpperTheory.Lit.CharWD

open UpperTheory.Lit.CharWD in
theorem UpperTheory.Lit.CharWD.locWD :
    GlobalArtinReciprocity → HeckeLAdicCharacterDeRham → DeRhamPotSemistable → LocWD :=
  fun hG hD hP => core hG hD hP chBasic chCoef embOrbit chRes (artNorm hG) (exField hG)
