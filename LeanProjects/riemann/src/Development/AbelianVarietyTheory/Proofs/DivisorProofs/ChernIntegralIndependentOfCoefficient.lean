import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DownwardChartLocalHolomorphicSection
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ArInt
open GlobalTheory.ChartGlue GlobalTheory.Points
open Topology Filter

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatMass

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

theorem cHess_zero (v : ReciprocityTheory.L2DbarEstimates.V D) :
    ReciprocityTheory.L2DbarEstimates.cHess D (fun _ => ((0 : ℝ) : ℂ)) v = 0 := by
  have h := ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cHess_add_smul isOpen_univ (p := fun _ => (0 : ℝ)) (q := fun _ => (0 : ℝ))
    contDiffOn_const contDiffOn_const 1 (Set.mem_univ v)
  simp only [mul_zero, add_zero, Complex.ofReal_one, one_smul] at h
  simpa using h

variable {A B : LB X} {c : AlgChart p σ D} {y : CxPts p σ}

theorem hess_tens {ψ : Weight p σ A} {φ : Weight p σ B} (hψ : ψ.IsCInf) (hφ : φ.IsCInf) (hy : y ∈ c.e.source)
    {a : A.ι} {b : B.ι} (ha : y ∈ ptsIn p σ (A.U a)) (hb : y ∈ ptsIn p σ (B.U b)) :
    c.hess (ψ.tens φ) (a, b) y = c.hess ψ a y + c.hess φ b y := by
  have ho := isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (A.U a ⊓ B.U b))
  have hm := mem_over c.e hy (mem_ptsIn_inf.2 ⟨ha, hb⟩)
  have e := ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cHess_add_smul ho
    ((contDiffOn_chart (hψ a) c).mono fun v hv => ⟨hv.1, (mem_ptsIn_inf.1 hv.2).1⟩)
    ((contDiffOn_chart (hφ b) c).mono fun v hv => ⟨hv.1, (mem_ptsIn_inf.1 hv.2).2⟩) 1 hm
  simp only [one_mul, Complex.ofReal_one, one_smul] at e
  exact e

theorem hess_dual {φ : Weight p σ B} (hφ : φ.IsCInf) (hy : y ∈ c.e.source) {b : B.ι}
    (hb : y ∈ ptsIn p σ (B.U b)) : c.hess φ.dual b y = -c.hess φ b y := by
  have ho := isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (B.U b))
  have hm := mem_over c.e hy hb
  have e := ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cHess_add_smul ho (p := fun _ => (0 : ℝ)) contDiffOn_const
    (contDiffOn_chart (hφ b) c) (-1) hm
  rw [cHess_zero, zero_add] at e
  simp only [zero_add, neg_one_mul, Complex.ofReal_neg, Complex.ofReal_one, neg_smul, one_smul] at e
  show ReciprocityTheory.L2DbarEstimates.cHess D (fun v => ((φ.dual.φ b (c.e.symm v) : ℝ) : ℂ)) (c.e y) =
    -ReciprocityTheory.L2DbarEstimates.cHess D (fun v => ((φ.φ b (c.e.symm v) : ℝ) : ℂ)) (c.e y)
  refine (congrArg (fun g => ReciprocityTheory.L2DbarEstimates.cHess D g (c.e y)) ?_).trans e
  funext v
  simp only [Function.comp_apply]
  exact Complex.ofReal_neg _

theorem hess_zpow {φ : Weight p σ B} (hφ : φ.IsCInf) (hy : y ∈ c.e.source) (n : ℤ) (j : PUnit → B.ι)
    (hb : y ∈ ptsIn p σ (B.U (j PUnit.unit))) : c.hess (φ.zpow n) j y = (n : ℂ) • c.hess φ (j PUnit.unit) y := by
  have ho := isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (B.U (j PUnit.unit)))
  have hm := mem_over c.e hy hb
  have e := ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cHess_add_smul ho (p := fun _ => (0 : ℝ)) contDiffOn_const
    (contDiffOn_chart (hφ (j PUnit.unit)) c) n hm
  rw [cHess_zero, zero_add] at e
  show ReciprocityTheory.L2DbarEstimates.cHess D (fun v => (((φ.zpow n).φ j (c.e.symm v) : ℝ) : ℂ)) (c.e y) =
    (n : ℂ) • ReciprocityTheory.L2DbarEstimates.cHess D (fun v => ((φ.φ (j PUnit.unit) (c.e.symm v) : ℝ) : ℂ)) (c.e y)
  rw [show ((n : ℂ)) = (((n : ℝ) : ℂ)) by push_cast; rfl]
  refine (congrArg (fun g => ReciprocityTheory.L2DbarEstimates.cHess D g (c.e y)) ?_).trans e
  funext v
  simp only [Function.comp_apply, Weight.zpow_φ, zero_add]

def HessFlat (φ : Weight p σ B) (D : ℕ) : Prop :=
  ∀ (c : AlgChart p σ D) (y : CxPts p σ) (i : B.ι), y ∈ c.e.source → y ∈ ptsIn p σ (B.U i) → c.hess φ i y = 0

theorem hessFlat_zp {M : HermLB p} (h : HessFlat (M.φ σ) D) (m : ℤ) : HessFlat ((zp M m).φ σ) D := by
  intro c y i hy hi
  obtain ⟨hi₁, hi₂⟩ := mem_ptsIn_inf.1 hi
  have h₁ : y ∈ ptsIn p σ (M.B.U (i.1 PUnit.unit)) := (mem_pow_iff (n := ((m.toNat : ℕ) : ℤ)) (j := i.1)).1 hi₁
  have h₂ : y ∈ ptsIn p σ (M.B.U (i.2 PUnit.unit)) := (mem_pow_iff (n := (((-m).toNat : ℕ) : ℤ)) (j := i.2)).1 hi₂
  have e := hess_tens ((M.cInf σ).zpow _) ((M.cInf σ).zpow _).dual hy hi₁ hi₂
  change c.hess (((M.φ σ).pow m.toNat).tens ((M.φ σ).pow (-m).toNat).dual) (i.1, i.2) y = 0
  rw [e, hess_dual ((M.cInf σ).zpow _) hy hi₂, hess_zpow (M.cInf σ) hy _ _ h₁,
    hess_zpow (M.cInf σ) hy _ _ h₂, h c y _ hy h₁, h c y _ hy h₂]
  simp

theorem chernDens_tens_flat {L N : HermLB p} (h : HessFlat (N.φ σ) D) (hy : y ∈ c.e.source) :
    c.chernDens ((L.tens N).φ σ) y = c.chernDens (L.φ σ) y := by
  have ha := mem_pick (L.φ σ).isLB y
  have hb := mem_pick (N.φ σ).isLB y
  rw [c.chernDens_eq ((L.tens N).cInf σ) hy (i := (pick (L.φ σ).isLB y, pick (N.φ σ).isLB y))
    (mem_ptsIn_inf.2 ⟨ha, hb⟩), c.chernDens_eq (L.cInf σ) hy ha]
  change _ * (c.hess ((L.φ σ).tens (N.φ σ)) _ y).det.re = _
  rw [hess_tens (L.cInf σ) (N.cInf σ) hy ha hb, h c y _ hy hb, add_zero]

theorem chernPart_tens_flat {L N : HermLB p} (h : HessFlat (N.φ σ) D) (ε : ℤˣ) :
    ((L.tens N).φ σ).chernPart D ε = (L.φ σ).chernPart D ε := by
  refine iSup_congr fun c => congrArg (MeasureTheory.Measure.map _) (MeasureTheory.withDensity_congr_ae
    (MeasureTheory.ae_restrict_of_forall_mem c.e.open_target.measurableSet fun v hv => ?_))
  simp only [Function.comp_apply, chernDens_tens_flat h (c.e.map_target hv)]

theorem isometric_comb_update {ι : Type} [Fintype ι] [DecidableEq ι] (L : ι → HermLB p) (n : ι → ℤ) (i : ι) :
    (comb L n).Isometric ((comb L (Function.update n i 0)).tens (zp (L i) (n i))) := by
  refine HermLB.icls_eq_iff.1 ?_
  rw [HermLB.icls_tens, icls_comb, icls_comb, icls_zp]
  have key : ∀ j, n j • (L j).icls = Function.update n i 0 j • (L j).icls + (Pi.single i (n i) : ι → ℤ) j • (L j).icls := by
    intro j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  rw [Finset.sum_congr rfl fun j _ => key j, Finset.sum_add_distrib]
  congr 1
  simp [Pi.single_apply]

end GlobalTheory.FlatMass

namespace GlobalTheory.FlatMass

open GlobalTheory.CoverNorm

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

theorem hessFlat_of_norms (V : Cover Y) (M : HermLB V.p)
    {lg : ∀ v : HeightOneSpectrum (𝓞 F), TrueGeo.Ext v → AlgPt Y → ℝ}
    (hN : Norms V M (fun _ => 1) (fun _ _ => 0) lg) (σ : 𝓞 F →+* ℂ) (D : ℕ) : HessFlat (M.φ σ) D := by
  have hinj : Function.Injective σ := (RingHom.injective_iff_ker_eq_bot _).2
    (Ideal.eq_bot_of_comap_eq_bot (R := ℤ) (eq_bot_iff.2 fun n hn => by simpa using hn))
  obtain ⟨τ, rfl⟩ : ∃ τ : F →+* ℂ, τ.comp (algebraMap (𝓞 F) F) = σ :=
    ⟨IsFractionRing.lift (K := F) hinj, RingHom.ext fun x => by
      rw [RingHom.comp_apply, IsFractionRing.lift_algebraMap]⟩
  intro c y₀ a hy₀ ha
  have hsp (z : CxPts V.p (τ.comp (algebraMap (𝓞 F) F))) :
      z.1 ≫ V.p = spMap τ ≫ spMap (algebraMap (𝓞 F) F) :=
    z.2.trans (Spec.map_comp (CommRingCat.ofHom _) (CommRingCat.ofHom _))
  let lift (z : CxPts V.p (τ.comp (algebraMap (𝓞 F) F))) : CxPts (V.π ≫ Y.str) τ :=
    ⟨V.pb.lift z.1 (spMap τ) (hsp z), V.pb.lift_snd _ _ _⟩
  have hj (z : CxPts V.p (τ.comp (algebraMap (𝓞 F) F))) : (lift z).1 ≫ V.j = z.1 := V.pb.lift_fst _ _ _
  have hunder (z : CxPts V.p (τ.comp (algebraMap (𝓞 F) F))) : V.j (under (lift z)) = under z := by
    show V.j ((lift z).1 _) = z.1 _
    rw [← hj z]
    rfl
  obtain ⟨r, -, hu, hc, -⟩ := hN
  let ja : (M.B.pull V.j).ι := fun _ => a
  have hmem (z : CxPts V.p (τ.comp (algebraMap (𝓞 F) F))) (hz : z ∈ ptsIn V.p _ (M.B.U a)) :
      under (lift z) ∈ (M.B.pull V.j).U ja :=
    mem_pull.2 (by rw [hunder]; exact mem_ptsIn.1 hz)
  have hunit (z : CxPts V.p (τ.comp (algebraMap (𝓞 F) F))) (hz : z ∈ ptsIn V.p _ (M.B.U a)) :
      UnitAt (under (lift z)) (r ja : V.G.functionField) := by
    simpa using hu ja _ (hmem z hz)
  obtain ⟨U, hxU, g, hg⟩ := (hunit y₀ ha).regAt.exists_fnOf
  obtain ⟨W', hW, hxW, n, g', hn, hg'⟩ :=
    T.exists_integral_multiple_extension F V.X V.G V.p (V.π ≫ Y.str) V.j V.pb U _ hxU Unit (fun _ => g)
  have hpre (z : CxPts V.p (τ.comp (algebraMap (𝓞 F) F))) (hz : z ∈ ptsIn V.p _ W') :
      lift z ∈ ptsIn (V.π ≫ Y.str) τ (V.j ⁻¹ᵁ W') := by
    refine mem_ptsIn.2 ?_
    show V.j (under (lift z)) ∈ W'
    rw [hunder]
    exact mem_ptsIn.1 hz
  have hval (z : CxPts V.p (τ.comp (algebraMap (𝓞 F) F))) (hz : z ∈ ptsIn V.p _ W') :
      (n : ℂ) * ratVal (r ja : V.G.functionField) (lift z) = ev V.p _ W' (g' ()) z := by
    have h1 := hpre z hz
    rw [← hg, ratVal_fnOf (mem_ptsIn.2 (hW (mem_ptsIn.1 h1))), ← ev_res hW h1 g]
    show (n : ℂ) * valR (lift z).1 (V.j ⁻¹ᵁ W') (resG V.G hW g) = valR z.1 W' (g' ())
    rw [← hj z, ← Cover.valR_app_comp (lift z).1 V.j W' h1, ← hg' (), ZH.CrdCalc.valR_eq _ _ h1,
      ZH.CrdCalc.valR_eq _ _ h1, map_mul, map_natCast]
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hweight (z : CxPts V.p (τ.comp (algebraMap (𝓞 F) F))) (hz : z ∈ ptsIn V.p _ (W' ⊓ M.B.U a)) :
      (M.φ _).φ a z = Real.log (‖(n : ℂ)⁻¹ * ev V.p _ W' (g' ()) z‖ ^ 2) := by
    obtain ⟨hz₁, hz₂⟩ := mem_ptsIn_inf.1 hz
    have H := hc τ (lift z) ⟨(lift z).1 ≫ V.π, by rw [Category.assoc]; exact (lift z).2⟩ z ja rfl (hj z).symm
      (hmem z hz₂)
    rw [← hval z hz₁, ← mul_assoc, inv_mul_cancel₀ hn', one_mul, Real.log_pow]
    simp only [map_one, one_mul] at H
    change (0 : ℝ) = _ - (M.φ _).φ a z / 2 at H
    push_cast
    linarith
  have hne (z : CxPts V.p (τ.comp (algebraMap (𝓞 F) F))) (hz : z ∈ ptsIn V.p _ (W' ⊓ M.B.U a)) :
      (n : ℂ)⁻¹ * ev V.p _ W' (g' ()) z ≠ 0 := by
    obtain ⟨hz₁, hz₂⟩ := mem_ptsIn_inf.1 hz
    rw [← hval z hz₁, ← mul_assoc, inv_mul_cancel₀ hn', one_mul]
    exact ratVal_ne_zero (hunit z hz₂)
  have hy₀W : y₀ ∈ ptsIn V.p _ W' := by
    refine mem_ptsIn.2 ?_
    show under y₀ ∈ W'
    rw [← hunder y₀]
    exact hxW
  have ho := isOpen_over c.e (isOpen_ptsIn (p := V.p) (σ := τ.comp (algebraMap (𝓞 F) F)) (W' ⊓ M.B.U a))
  have hm := mem_over c.e hy₀ (mem_ptsIn_inf.2 ⟨hy₀W, ha⟩)
  have hol : DifferentiableOn ℂ (fun v => (n : ℂ)⁻¹ * ev V.p _ W' (g' ()) (c.e.symm v))
      (c.e.target ∩ c.e.symm ⁻¹' ptsIn V.p _ (W' ⊓ M.B.U a)) :=
    ((c.holo W' (g' ())).mono fun v hv => ⟨hv.1, (mem_ptsIn_inf.1 hv.2).1⟩).const_mul _
  show ReciprocityTheory.L2DbarEstimates.cHess D (fun v => (((M.φ _).φ a (c.e.symm v) : ℝ) : ℂ)) (c.e y₀) = 0
  rw [ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr (g₂ := fun v =>
    ((Real.log (‖(n : ℂ)⁻¹ * ev V.p _ W' (g' ()) (c.e.symm v)‖ ^ 2) : ℝ) : ℂ)) ?_]
  · ext i j
    exact ReciprocityTheory.L2DbarEstimates.Y.cmpa_hess_log ho hm hol (fun v hv => hne _ hv.2) i j
  · filter_upwards [ho.mem_nhds hm] with v hv
    rw [hweight _ hv.2]

theorem chernInt_comb_update_of_norms : Hypotheses2 → ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (D : ℕ), Y.dim = D → ∀ (M : HermLB V.p) (lg : ∀ v : HeightOneSpectrum (𝓞 F), TrueGeo.Ext v → AlgPt Y → ℝ), Norms V M (fun _ => 1) (fun _ _ => 0) lg → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (L : ι → HermLB V.p) (i : ι), L i = M → ∀ (n : ι → ℤ) (σ : 𝓞 F →+* ℂ), ((comb L n).φ σ).chernInt D Set.univ (fun _ => 1) = ((comb L (Function.update n i 0)).φ σ).chernInt D Set.univ (fun _ => 1) := by
  intro _ F _ _ Y V D _ M lg hN ι _ _ L i hLi n σ
  subst hLi
  have hflat : HessFlat ((zp (L i) (n i)).φ σ) D := hessFlat_zp (hessFlat_of_norms V (L i) hN σ D) (n i)
  rw [(isometric_comb_update L n i).chernInt_eq σ D]
  simp only [Weight.chernInt, chernPart_tens_flat hflat]

end GlobalTheory.FlatMass
