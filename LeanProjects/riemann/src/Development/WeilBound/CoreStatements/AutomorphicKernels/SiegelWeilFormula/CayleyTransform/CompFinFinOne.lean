import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction
import Development.WeilBound.ThetaLifts.LatticeBasics.ExistsIsGauss
import Development.WeilBound.ThetaLifts.LatticeBasics.IsCompactOfUnits
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight

noncomputable section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

namespace PositivityTheory.SiegelWeilFormula.Place

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem continuous_piInf {w : InfinitePlace F} (τ : EmbOver E w) : Continuous (piInf τ : AE F E → ℂ) :=
  GlobalTheory.Grow.continuous_infEmb_compInf F w τ

theorem piInf_cA (h : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) (z : AE F E) :
    piInf τ (cA σ z) = star (piInf τ z) :=
  Dense.piInf_cA h τ z

theorem map_cA {p q : Type} (h : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) (X : Matrix p q (AE F E)) :
    (X.map (cA σ)).map (piInf τ) = (X.map (piInf τ)).map star :=
  Matrix.ext fun i j => piInf_cA h τ (X i j)

omit [NumberField E] in

theorem compFin_finOne (v : Pl F) (z : AE F E) : compFin F E v (finOne F • z) = compFin F E v z := by
  have e0 := St.compFin_smul (E := E) v (a := 1 - St.eF F) (sub_self (1 : Af F)) z
  rw [sub_smul, one_smul, map_sub, sub_eq_zero] at e0
  exact e0.symm

theorem ad_ext (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) {a b : AE F E}
    (h1 : ∀ w, piInf (τ w) a = piInf (τ w) b) (h2 : finOne F • a = finOne F • b) : a = b :=
  PositivityTheory.ThKG.Tow.Levi.ad_ext h τ h1 fun v => by rw [← compFin_finOne v a, h2, compFin_finOne]

theorem mat_ext (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) {p q : Type} {a b : Matrix p q (AE F E)}
    (h1 : ∀ w, a.map (piInf (τ w)) = b.map (piInf (τ w))) (h2 : finOne F • a = finOne F • b) : a = b :=
  Matrix.ext fun i j => ad_ext h τ (fun w => congrFun (congrFun (h1 w) i) j) (congrFun (congrFun h2 i) j)

omit [NumberField E] in

theorem piInf_finOne {w : InfinitePlace F} (τ : EmbOver E w) (z : AE F E) : piInf τ (finOne F • z) = 0 := by
  rw [St.piInf_smul]
  have : (finOne F).1 w = 0 := rfl
  rw [this, map_zero, zero_mul]

theorem exists_sec (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) :
    ∃ s : (InfinitePlace F → ℂ) → AE F E, Continuous s ∧ (∀ x w, piInf (τ w) (s x) = x w) ∧
      (∀ x, finOne F • s x = 0) ∧ (∀ x y, s (x + y) = s x + s y) ∧ (∀ x y, s (x * y) = s x * s y) := by
  have := h.1
  have hr : ∀ w : InfinitePlace F, w.IsReal := fun w => IsTotallyReal.isReal w
  let ρ : (InfinitePlace F → ℝ) → AF F := fun t =>
    pairA F (fun w => (InfinitePlace.Completion.isometryEquivRealOfIsReal (hr w)).symm (t w)) 0
  have hρ : Continuous ρ := by
    have : Continuous fun (t : InfinitePlace F → ℝ) (w : InfinitePlace F) =>
        (InfinitePlace.Completion.isometryEquivRealOfIsReal (hr w)).symm (t w) :=
      continuous_pi fun w => (IsometryEquiv.continuous _).comp (continuous_apply w)
    exact this.prodMk continuous_const
  have eρ : ∀ t w, InfinitePlace.Completion.extensionEmbedding w ((ρ t).1 w) = t w := fun t w => by
    rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (hr w)]
    exact congrArg _ ((InfinitePlace.Completion.isometryEquivRealOfIsReal (hr w)).apply_symm_apply (t w))
  obtain ⟨a, ha, -⟩ := PositivityTheory.ThKG.Tow.Levi.exists_inf h τ fun _ => Complex.I
  let s : (InfinitePlace F → ℂ) → AE F E := fun z => ρ (fun w => (z w).re) • 1 + ρ (fun w => (z w).im) • a
  have hs1 : ∀ x w, piInf (τ w) (s x) = x w := fun x w => by
    change piInf (τ w) (ρ (fun w => (x w).re) • 1 + ρ (fun w => (x w).im) • a) = x w
    rw [map_add, St.piInf_smul, St.piInf_smul, eρ, eρ, ha, map_one, mul_one, Complex.re_add_im]
  have hs2 : ∀ x v, compFin F E v (s x) = 0 := fun x v => by
    change compFin F E v (ρ (fun w => (x w).re) • 1 + ρ (fun w => (x w).im) • a) = 0
    rw [map_add, St.compFin_smul v rfl, St.compFin_smul v rfl, add_zero]
  have hc : Continuous s := by
    have h1 : Continuous fun z : InfinitePlace F → ℂ => ρ fun w => (z w).re :=
      hρ.comp (continuous_pi fun w => Complex.continuous_re.comp (continuous_apply w))
    have h2 : Continuous fun z : InfinitePlace F → ℂ => ρ fun w => (z w).im :=
      hρ.comp (continuous_pi fun w => Complex.continuous_im.comp (continuous_apply w))
    have h3 : ∀ b : AE F E, Continuous fun x : AF F => x • b := fun b =>
      Continuous.fun_smul (f := fun x : AF F => x) (g := fun _ => b) continuous_id' continuous_const
    exact Continuous.fun_add (f := fun z : InfinitePlace F → ℂ => ρ (fun w => (z w).re) • (1 : AE F E))
      (g := fun z => ρ (fun w => (z w).im) • a) ((h3 1).comp' h1) ((h3 a).comp' h2)
  clear_value s
  have ext' : ∀ b c : AE F E, (∀ w, piInf (τ w) b = piInf (τ w) c) → (∀ v, compFin F E v b = compFin F E v c) → b = c :=
    fun b c h1 h2 => PositivityTheory.ThKG.Tow.Levi.ad_ext h τ h1 h2
  refine ⟨s, hc, hs1, fun x => ?_, fun x y => ?_, fun x y => ?_⟩
  · refine ext' _ _ (fun w => ?_) fun v => ?_
    · rw [piInf_finOne, map_zero]
    · rw [compFin_finOne, hs2, map_zero]
  · refine ext' _ _ (fun w => ?_) fun v => ?_
    · rw [map_add, hs1, hs1, hs1, Pi.add_apply]
    · rw [map_add, hs2, hs2, hs2, add_zero]
  · refine ext' _ _ (fun w => ?_) fun v => ?_
    · rw [map_mul, hs1, hs1, hs1, Pi.mul_apply]
    · rw [map_mul, hs2, hs2, hs2, zero_mul]

theorem at_of_finOne {a : AF F} (hf : finOne F * a = 0) : At (evI F) a := by
  intro u hu
  have hu1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (hu.trans (map_zero _).symm)
  have e : u = u * finOne F :=
    Prod.ext (by change u.1 = u.1 * 0; rw [hu1, mul_zero]) (by change u.2 = u.2 * 1; rw [mul_one])
  rw [smul_eq_mul, e, mul_assoc, hf, mul_zero]

theorem psi_at {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (hF : IsTotallyReal F) (w : InfinitePlace F) (a : AF F)
    (hf : finOne F * a = 0) (hw : ∀ u, u ≠ w → InfinitePlace.Completion.extensionEmbedding u (a.1 u) = 0) :
    ψ a = Complex.exp (-(2 * Real.pi * Complex.I) * ((InfinitePlace.Completion.extensionEmbedding w (a.1 w)).re : ℂ)) := by
  rw [hψ.2.2 a (at_of_finOne hf), Dense.trace_evI hF, Finset.sum_eq_single w (fun u _ hu => by rw [hw u hu, Complex.zero_re])
    (fun hw' => absurd (Finset.mem_univ w) hw')]

theorem psi_trace_at {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (w : InfinitePlace F) (z : AE F E) (hf : finOne F • z = 0) (hw : ∀ u, u ≠ w → piInf (τ u) z = 0) :
    ψ (Algebra.trace (AF F) (AE F E) z) =
      Complex.exp (-(2 * Real.pi * Complex.I) * ((2 * (piInf (τ w) z).re : ℝ) : ℂ)) := by
  have e : ∀ u, InfinitePlace.Completion.extensionEmbedding u ((Algebra.trace (AF F) (AE F E) z).1 u) =
      piInf (τ u) z + star (piInf (τ u) z) := fun u => by rw [Dense.ext_trace h (τ u), Dense.piInf_cA h]
  have hf' : finOne F * Algebra.trace (AF F) (AE F E) z = 0 := by
    rw [← smul_eq_mul, ← LinearMap.map_smul, hf, map_zero]
  rw [psi_at hψ h.1 w _ hf' fun u hu => by rw [e u, hw u hu, star_zero, add_zero], e w]
  congr 3
  rw [Complex.add_re, Complex.star_def, Complex.conj_re, two_mul]

variable (d : SD σ)

theorem _root_.PositivityTheory.SiegelWeilFormula.SD.cm (d : SD σ) : IsCMExt F E σ := d.ok.good.cm

theorem _root_.PositivityTheory.SiegelWeilFormula.SD.std (d : SD σ) : IsStd d.B.ψ := d.ok.good.std

theorem continuous_cw (w : InfinitePlace F) {p q : Type} : Continuous (fun X : Matrix p q (AE F E) => d.cw w X) :=
  continuous_id.matrix_map (continuous_piInf (d.B.emb w))

theorem cw_ext {p q : Type} {X Z : Matrix p q (AE F E)} (h1 : ∀ w, d.cw w X = d.cw w Z) (h2 : finOne F • X = finOne F • Z) :
    X = Z :=
  mat_ext d.cm d.B.emb h1 h2

theorem cw_cA (w : InfinitePlace F) {p q : Type} (X : Matrix p q (AE F E)) : d.cw w (X.map (cA σ)) = (d.cw w X).map star :=
  map_cA d.cm _ X

end PositivityTheory.SiegelWeilFormula.Place

end
