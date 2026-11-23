import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.CProps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SeriesEqDens
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeVolumeUnramifiedStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelCharactersUnramifiedStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.GunrJt

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gen PositivityTheory.SiegelWeilFormula.Gunr Filter
open scoped TensorProduct

theorem integral_of_factor {V P Q : Type} [AddCommGroup V] [MeasurableSpace V] [MeasurableAdd V] (μ : Measure V)
    [μ.IsAddLeftInvariant] [AddCommGroup P] [AddCommGroup Q] [Fintype Q] (ι : P →+ V) (hι : Function.Injective ι)
    (r : P →+ Q) (hr : Function.Surjective r) (hH : MeasurableSet (ι '' {x | r x = 0}))
    (hvol : μ (Set.range ι) = 1) (f : V → ℂ) (g : Q → ℂ) (hf : ∀ x, f (ι x) = g (r x))
    (hf0 : ∀ y, y ∉ Set.range ι → f y = 0) :
    ∫ y, f y ∂μ = ((Fintype.card Q : ℂ))⁻¹ * ∑ c, g c := by
  classical
  set H : Set V := ι '' {x | r x = 0} with hHdef
  choose s hs using hr
  let Pc : Q → Set V := fun c => ι '' {x | r x = c}
  have hPc : ∀ c, Pc c = (fun y => -ι (s c) + y) ⁻¹' H := by
    intro c
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x - s c, ?_, ?_⟩
      · have hx' : r x = c := hx
        simp [hx', hs]
      · simp [map_sub]
        abel
    · rintro ⟨x, hx, hxy⟩
      refine ⟨x + s c, ?_, ?_⟩
      · have hx' : r x = 0 := hx
        simp [hx', hs]
      · have hxy' : ι x = -ι (s c) + y := hxy
        rw [map_add, hxy']
        abel
  have hPm : ∀ c, MeasurableSet (Pc c) := fun c => by
    rw [hPc]
    exact (measurable_const_add _) hH
  have hPμ : ∀ c, μ (Pc c) = μ H := fun c => by
    rw [hPc]
    exact measure_preimage_add μ _ _
  have hdis : ∀ c c', c ≠ c' → Disjoint (Pc c) (Pc c') := by
    intro c c' hc
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨x, hx, rfl⟩ ⟨x', hx', he⟩
    have := hι he
    subst this
    exact hc (hx.symm.trans hx')
  have hU : Set.range ι = ⋃ c ∈ (Finset.univ : Finset Q), Pc c := by
    ext y
    simp only [Set.mem_range, Finset.mem_univ, Set.iUnion_true, Set.mem_iUnion]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨r x, x, rfl, rfl⟩
    · rintro ⟨c, x, -, rfl⟩
      exact ⟨x, rfl⟩
  have hsum : (Fintype.card Q : ENNReal) * μ H = 1 := by
    rw [← hvol, hU, measure_biUnion_finset (fun c _ c' _ h => hdis c c' h) (fun c _ => hPm c)]
    simp [hPμ, Finset.card_univ]
  have hcard : (Fintype.card Q : ENNReal) ≠ 0 := by
    have : Fintype.card Q ≠ 0 := Fintype.card_ne_zero
    exact_mod_cast this
  have hHfin : μ H ≠ ⊤ := by
    intro h
    rw [h, ENNReal.mul_top hcard] at hsum
    exact ENNReal.top_ne_one hsum
  have hreal : μ.real H = ((Fintype.card Q : ℝ))⁻¹ := by
    have h := congrArg ENNReal.toReal hsum
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_one] at h
    exact eq_inv_of_mul_eq_one_right h
  have hdec : f = fun y => ∑ c, (Pc c).indicator (fun _ => g c) y := by
    funext y
    by_cases hy : y ∈ Set.range ι
    · obtain ⟨x, rfl⟩ := hy
      rw [Finset.sum_eq_single (r x)]
      · have hm : ι x ∈ Pc (r x) := ⟨x, rfl, rfl⟩
        rw [Set.indicator_of_mem hm]
        exact hf x
      · intro c _ hc
        exact Set.indicator_of_notMem (Set.disjoint_left.1 (hdis _ _ hc.symm) ⟨x, rfl, rfl⟩) _
      · simp
    · rw [hf0 y hy]
      symm
      refine Finset.sum_eq_zero fun c _ => Set.indicator_of_notMem ?_ _
      rintro ⟨x, -, rfl⟩
      exact hy ⟨x, rfl⟩
  have hint : ∀ c, Integrable ((Pc c).indicator (fun _ => g c)) μ := fun c =>
    (integrable_indicator_iff (hPm c)).2 (integrableOn_const (by rw [hPμ]; exact hHfin))
  rw [hdec, integral_finset_sum _ (fun c _ => hint c)]
  simp only [integral_indicator_const _ (hPm _)]
  have : ∀ c, μ.real (Pc c) = ((Fintype.card Q : ℝ))⁻¹ := fun c => by
    rw [← hreal, Measure.real, Measure.real, hPμ]
  simp only [this, Complex.real_smul, ← Finset.mul_sum]
  push_cast
  rfl

def redHom {R : Type} [CommRing R] (ϖ : R) (k a b : ℕ) :
    Matrix (Fin a) (Fin b) R →+ Matrix (Fin a) (Fin b) (R ⧸ lev ϖ k) where
  toFun := red ϖ k
  map_zero' := by ext; simp [red]
  map_add' x y := by ext; simp [red]

theorem redHom_surjective {R : Type} [CommRing R] (ϖ : R) (k a b : ℕ) : Function.Surjective (redHom ϖ k a b) := by
  intro y
  choose f hf using fun i j => Ideal.Quotient.mk_surjective (y i j)
  exact ⟨Matrix.of f, by ext i j; exact hf i j⟩

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def emb {v : HeightOneSpectrum (𝓞 F)} (S : Subring (Fv F v ⊗[F] E)) (M n : ℕ) :
    Matrix (Fin M) (Fin n) S →+ (Fin n → Fin M → Fv F v ⊗[F] E) where
  toFun x := fun a i => (x i a : Fv F v ⊗[F] E)
  map_zero' := by funext a i; simp
  map_add' x y := by funext a i; simp

theorem emb_injective {v : HeightOneSpectrum (𝓞 F)} (S : Subring (Fv F v ⊗[F] E)) (M n : ℕ) :
    Function.Injective (emb S M n) := by
  intro x y h
  ext i a
  exact congrFun (congrFun h a) i

variable {σ : E →ₐ[F] E} {M n d : ℕ} {J : Matrix (Fin M) (Fin M) E} {T : Matrix (Fin n) (Fin n) E}
  {bs : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)} {ψv : Fv F v → ℂ} {S : Subring (Fv F v ⊗[F] E)}
  {σS : S →+* S} {ϖ : Fv F v} {ε : ℤ}

theorem mem_S_iff (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) (z : Fv F v ⊗[F] E) :
    z ∈ S ↔ ∀ j, (Algebra.TensorProduct.basis (Fv F v) bs).repr z j ∈ v.adicCompletionIntegers F := by
  have : z ∈ (S : Set (Fv F v ⊗[F] E)) ↔ z ∈ Rv bs v := by rw [hG.carrier]
  exact this

theorem isOpen_scaled (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) (c : Fv F v) :
    IsOpen {z : Fv F v ⊗[F] E | c • z ∈ S} := by
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  have hO : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isOpen_valuationSubring _
  have e : {z : Fv F v ⊗[F] E | c • z ∈ S} =
      ⋂ j, (fun z => c * (Algebra.TensorProduct.basis (Fv F v) bs).coord j z) ⁻¹' (v.adicCompletionIntegers F : Set (Fv F v)) := by
    ext z
    simp [mem_S_iff hG]
  rw [e]
  refine isOpen_iInter_of_finite fun j => hO.preimage ?_
  exact continuous_const.mul (IsModuleTopology.continuous_of_linearMap _)

theorem range_emb (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) :
    Set.range (emb S M n) = (latV bs v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) := by
  ext Y
  constructor
  · rintro ⟨x, rfl⟩ a i
    exact (mem_S_iff hG _).1 (x i a).2
  · intro hY
    refine ⟨Matrix.of fun i a => ⟨Y a i, (mem_S_iff hG _).2 (hY a i)⟩, ?_⟩
    funext a i
    rfl

theorem coe_pow_mul (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) (k : ℕ) (c : S) :
    ((c * hG.pS ^ k : S) : Fv F v ⊗[F] E) = (ϖ ^ k) • (c : Fv F v ⊗[F] E) := by
  rw [Subring.coe_mul, Subring.coe_pow, Algebra.smul_def, map_pow, mul_comm]
  rfl

theorem image_ker (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) (k : ℕ) :
    emb S M n '' {x | redHom hG.pS k M n x = 0} = {Y | ∀ a i, (ϖ ^ k)⁻¹ • Y a i ∈ S} := by
  have hϖ : ϖ ^ k ≠ 0 := pow_ne_zero _ hG.unif_ne
  ext Y
  constructor
  · rintro ⟨x, hx, rfl⟩ a i
    have h0 : Ideal.Quotient.mk (lev hG.pS k) (x i a) = 0 := congrFun (congrFun hx i) a
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 h0)
    show (ϖ ^ k)⁻¹ • (x i a : Fv F v ⊗[F] E) ∈ S
    rw [← hc, coe_pow_mul, smul_smul, inv_mul_cancel₀ hϖ, one_smul]
    exact c.2
  · intro hY
    refine ⟨Matrix.of fun i a => ⟨_, hY a i⟩ * hG.pS ^ k, ?_, ?_⟩
    · ext i a
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton'.2 ⟨_, rfl⟩)
    · funext a i
      show (((⟨_, hY a i⟩ : S) * hG.pS ^ k : S) : Fv F v ⊗[F] E) = Y a i
      rw [coe_pow_mul]
      show (ϖ ^ k) • ((ϖ ^ k)⁻¹ • Y a i) = Y a i
      rw [smul_smul, mul_inv_cancel₀ hϖ, one_smul]

theorem measurable_image_ker (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) (k : ℕ) :
    MeasurableSet (emb S M n '' {x | redHom hG.pS k M n x = 0}) := by
  rw [image_ker hG k]
  have e : {Y : Fin n → Fin M → Fv F v ⊗[F] E | ∀ a i, (ϖ ^ k)⁻¹ • Y a i ∈ S} =
      ⋂ a, ⋂ i, (fun Y : Fin n → Fin M → Fv F v ⊗[F] E => Y a i) ⁻¹' {z | (ϖ ^ k)⁻¹ • z ∈ S} := by
    ext Y
    simp
  rw [e]
  haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  refine MeasurableSet.iInter fun a => MeasurableSet.iInter fun i => ?_
  exact ((measurable_pi_apply i).comp (measurable_pi_apply a)) (isOpen_scaled hG _).measurableSet

open GlobalTheory.CompanionTheory.UnrDens in
theorem trace_red (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) (k : ℕ) (X : Matrix (Fin n) (Fin n) S)
    (x : Matrix (Fin M) (Fin n) S) :
    Matrix.trace (red hG.pS k X * (PositivityTheory.PfSWUS.Loc.cT (barσ σS hG.pS hG.quad.fix_ϖ k) (red hG.pS k x) *
        red hG.pS k (matS S J hG.J_int) * red hG.pS k x)) =
      Ideal.Quotient.mk (lev hG.pS k) (Matrix.trace (X * (PositivityTheory.PfSWUS.Loc.cT σS x * matS S J hG.J_int * x))) := by
  have e : PositivityTheory.PfSWUS.Loc.cT (barσ σS hG.pS hG.quad.fix_ϖ k) (red hG.pS k x) = red hG.pS k (PositivityTheory.PfSWUS.Loc.cT σS x) := by
    ext i j
    rfl
  have hm : ∀ {a b c : ℕ} (A : Matrix (Fin a) (Fin b) S) (B : Matrix (Fin b) (Fin c) S),
      red hG.pS k A * red hG.pS k B = red hG.pS k (A * B) := fun A B => by
    simp only [red]
    exact (Matrix.map_mul (f := Ideal.Quotient.mk (lev hG.pS k))).symm
  rw [e, hm, hm, hm]
  simp only [Matrix.trace, Matrix.diag_apply, red, Matrix.map_apply, map_sum]

theorem gram_emb (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) (x : Matrix (Fin M) (Fin n) S) (c a : Fin n) :
    gramR (Fv F v) σ J (emb S M n x) c a =
      ((PositivityTheory.PfSWUS.Loc.cT σS x * matS S J hG.J_int * x) c a : S) := by
  simp only [gramR, hR, hform, JR, Matrix.mul_apply, PositivityTheory.PfSWUS.Loc.cT, Matrix.transpose_apply, Matrix.map_apply, emb, matS,
    Matrix.of_apply, AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddSubmonoidClass.coe_finset_sum, Subring.coe_mul, hG.sig,
    Finset.sum_mul]
  exact Finset.sum_comm

theorem psi_gram (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) (k : ℕ) (X : Matrix (Fin n) (Fin n) S)
    (hX : PositivityTheory.PfSWUS.Loc.cT σS X = X) (x : Matrix (Fin M) (Fin n) S) :
    ψv (trPair (Fv F v) (hG.hermLev k X hX : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) (gramR (Fv F v) σ J (emb S M n x))) =
      hG.psiLev (one_mem _) k
        (Ideal.Quotient.mk (lev hG.pS k) (Matrix.trace (X * (PositivityTheory.PfSWUS.Loc.cT σS x * matS S J hG.J_int * x)))) := by
  rw [GoodLoc.psiLev_mk]
  unfold psiF
  congr 1
  have e2 : (∑ a, ∑ c, (hG.hermLev k X hX : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a c *
        gramR (Fv F v) σ J (emb S M n x) c a) =
      (ϖ ^ k)⁻¹ • ((Matrix.trace (X * (PositivityTheory.PfSWUS.Loc.cT σS x * matS S J hG.J_int * x)) : S) : Fv F v ⊗[F] E) := by
    simp only [gram_emb hG, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply (M := X), AddSubmonoidClass.coe_finset_sum,
      Subring.coe_mul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    show ((ϖ ^ k)⁻¹ • (X a c : Fv F v ⊗[F] E)) * _ = _
    rw [smul_mul_assoc]
  rw [trPair, e2, map_smul, smul_eq_mul, one_mul]
  congr 1
  simp only [one_div, map_inv₀]
  congr 1
  exact map_ofNat _ 2

theorem jtLev : JtLev := by
  intro F E _ _ _ _ _ σ M n d J T bs v ψv S σS ϖ ε hG μv hμ k X hX
  have hvol : μv (latV bs v) = 1 := GlobalTheory.T.lattice_volume_unramified F E σ M n d J T bs v ψv S σS ϖ ε hG μv hμ
  have hlev : IsLevelChars σS hG.pS (hG.psiLev (one_mem _)) :=
    GlobalTheory.T.level_characters_unramified F E σ M n d J T bs v ψv S σS ϖ ε hG 1 (one_mem _) norm_one
  have hR : IsUnrQuad S σS hG.pS (Ideal.absNorm v.asIdeal) ε := hG.quad
  have hfin : ∀ k, Finite (S ⧸ lev hG.pS k) := fun k => Nat.finite_of_card_ne_zero (by
    rw [GlobalTheory.T.unramified_quotient_card S σS hG.pS _ ε hR k]
    have := hR.one_lt
    exact pow_ne_zero _ (by omega))
  letI : ∀ k, Fintype (S ⧸ lev hG.pS k) := fun k => Fintype.ofFinite _
  have hε : (ε : ℂ) ^ 2 = 1 := by
    rcases hR.eps with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
  haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (Fv F v ⊗[F] E) := IsModuleTopology.toContinuousAdd (Fv F v) _
  haveI : μv.IsAddHaarMeasure := hμ.1
  have hB : red hG.pS k X ∈ hermMod σS hG.pS n k := ⟨X, hX, rfl⟩
  have hS : IsUnimod σS (matS S J hG.J_int) := hG.J_unimod
  have hgauss := GlobalTheory.CompanionTheory.SiegLoc.gauss_full hR hlev hε k (matS S J hG.J_int) hS (red hG.pS k X) hB
  have hint := integral_of_factor μv (emb S M n) (emb_injective S M n) (redHom hG.pS k M n)
    (redHom_surjective hG.pS k M n) (measurable_image_ker hG k) (by rw [range_emb hG]; exact hvol)
    (fun Y => (latV bs v).indicator 1 Y * ψv (trPair (Fv F v)
      (hG.hermLev k X hX : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) (gramR (Fv F v) σ J Y)))
    (fun x => hG.psiLev (one_mem _) k (Matrix.trace (red hG.pS k X *
      (PositivityTheory.PfSWUS.Loc.cT (GlobalTheory.CompanionTheory.UnrDens.barσ σS hG.pS hR.fix_ϖ k) x * red hG.pS k (matS S J hG.J_int) * x))))
    (fun x => by
      have hm : emb S M n x ∈ (latV bs v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) := by
        rw [← range_emb hG]; exact ⟨x, rfl⟩
      rw [Set.indicator_of_mem hm, Pi.one_apply, one_mul, psi_gram hG k X hX x]
      congr 1
      exact (trace_red hG k X x).symm)
    (fun Y hY => by
      rw [range_emb hG] at hY
      rw [Set.indicator_of_notMem hY, zero_mul])
  have hc0 : (Fintype.card (Matrix (Fin M) (Fin n) (S ⧸ lev hG.pS k)) : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero (α := Matrix (Fin M) (Fin n) (S ⧸ lev hG.pS k)))
  unfold jtR
  rw [hint, hgauss, Nat.card_eq_fintype_card, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]

end GlobalTheory.CompanionTheory.GunrJt
end
