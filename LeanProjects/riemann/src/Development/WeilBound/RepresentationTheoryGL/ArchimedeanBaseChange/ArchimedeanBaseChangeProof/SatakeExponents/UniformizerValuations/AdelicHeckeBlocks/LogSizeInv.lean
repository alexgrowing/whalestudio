import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.GlobalTheory

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

namespace PositivityTheory.Rg.BcB.F

attribute [local instance] borelG borelF borelH

namespace Op

theorem bsG (n : ℕ) : BorelSpace (G n) := ⟨rfl⟩

theorem bsF (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) : BorelSpace (Hf E a b) := ⟨rfl⟩

attribute [local instance] bsG bsF

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem logSize_inv {n : ℕ} (g : GA E n) : logSize g⁻¹ = logSize g := by
  rw [logSize, logSize, inv_inv, add_comm]

theorem adjVal_spec (h2 : MultAlg) {n : ℕ} (μ : Measure (G n)) [μ.IsHaarMeasure] {M : Mods E n} (k : Kers M)
    (val : InfinitePlace E → Inf n → ℂ) (T : ℝ) (v : InfinitePlace E) (hk : IsMult μ (M v) (k v) (val v) T) :
    IsMult μ (M v) (adjK k v) (adjVal μ k val T v) T ∧
      ∀ χ, IsHerm χ → adjVal μ k val T v χ = starRingEnd ℂ (val v χ) := by
  have hex : ∃ val₁, IsMult μ (M v) (adjK k v) val₁ T ∧ ∀ χ, IsHerm χ → val₁ χ = starRingEnd ℂ (val v χ) := by
    obtain ⟨-, -, h, -⟩ := h2 n μ (M v) (k v) (k v) (val v) (val v) T T hk hk
    exact h
  have e : adjVal μ k val T v = hex.choose := dif_pos hex
  rw [e]
  exact hex.choose_spec

variable (B : Block E)

theorem opOf_eq (h1 : OpEx) {Φ : Matrix B.I B.I (H E B.a B.b → ℂ)} {T : B.Hb →L[ℂ] B.Hb} (hΦ : IsTestM Φ)
    (hT : IsROp B.D Φ T) : B.opOf Φ = T := by
  have hex : ∃ T, IsROp B.D Φ T := ⟨T, hT⟩
  have e : B.opOf Φ = hex.choose := dif_pos hex
  rw [e]
  exact ((h1 E B.a B.b B.D B.I).1 Φ hΦ).unique hex.choose_spec hT

theorem test (h3 : TensTest) (t : PT B) (ht : t.Ok) : IsTestM t.Φ := by
  haveI := B.ha; haveI := B.hb
  exact (h3 E B.a B.b B.μa B.μb B.Ma B.Mb B.κ t.ka t.kb t.va t.vb t.T t.ψ ht.ka ht.kb ht.ψ).1

theorem rop (h1 : OpEx) (h3 : TensTest) (t : PT B) (ht : t.Ok) : IsROp B.D t.Φ t.op := by
  have hex := ((h1 E B.a B.b B.D B.I).1 t.Φ (test B h3 t ht)).exists
  have e : B.opOf t.Φ = hex.choose := dif_pos hex
  show IsROp B.D t.Φ (B.opOf t.Φ)
  rw [e]
  exact hex.choose_spec

theorem mulOk (h2 : MultAlg) (h4 : TensMul) (t t' : PT B) (ht : t.Ok) (ht' : t'.Ok) : (t.mul t').Ok := by
  haveI := B.ha; haveI := B.hb; haveI := B.hν
  refine ⟨add_nonneg ht.T ht'.T, add_nonneg (add_nonneg ht.r ht'.r) B.c_nonneg, fun v => ?_, fun v => ?_, ?_, ?_⟩
  · exact (h2 B.a B.μa (B.Ma v) (t.ka v) (t'.ka v) (t.va v) (t'.va v) t.T t'.T (ht.ka v) (ht'.ka v)).1
  · exact (h2 B.b B.μb (B.Mb v) (t.kb v) (t'.kb v) (t.vb v) (t'.vb v) t.T t'.T (ht.kb v) (ht'.kb v)).1
  · exact (h4 E B.a B.b B.D B.μa B.μb B.ν B.Ma B.Mb B.κ t.ka t'.ka t.kb t'.kb t.va t'.va t.vb t'.vb t.T t'.T t.ψ t'.ψ
      B.compat ht.ka ht.kb ht'.ka ht'.kb ht.ψ ht'.ψ).1
  · intro x y g hg
    have hg' : ∑ z, ∫ h, t.ψ x z h * t'.ψ z y (h⁻¹ * g) ∂B.ν ≠ 0 := hg
    obtain ⟨z, hz⟩ : ∃ z, ∫ h, t.ψ x z h * t'.ψ z y (h⁻¹ * g) ∂B.ν ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hg' (Finset.sum_eq_zero fun z _ => hc z)
    obtain ⟨h, hh⟩ : ∃ h, t.ψ x z h * t'.ψ z y (h⁻¹ * g) ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hz (by simp [hc])
    have s1 := ht.size x z h (left_ne_zero_of_mul hh)
    have s2 := ht'.size z y (h⁻¹ * g) (right_ne_zero_of_mul hh)
    have e1 : g.1 = h.1 * (h⁻¹ * g).1 := by rw [← Prod.fst_mul, mul_inv_cancel_left]
    have e2 : g.2 = h.2 * (h⁻¹ * g).2 := by rw [← Prod.snd_mul, mul_inv_cancel_left]
    show logSize (finGL E B.a g.1) ≤ t.r + t'.r + B.c ∧ logSize (finGL E B.b g.2) ≤ t.r + t'.r + B.c
    rw [e1, e2, map_mul, map_mul]
    constructor
    · linarith [B.ca (finGL E B.a h.1) (finGL E B.a (h⁻¹ * g).1), s1.1, s2.1]
    · linarith [B.cb (finGL E B.b h.2) (finGL E B.b (h⁻¹ * g).2), s1.2, s2.2]

theorem mulOp (h1 : OpEx) (h3 : TensTest) (h4 : TensMul) (t t' : PT B) (ht : t.Ok) (ht' : t'.Ok) :
    (t.mul t').op = t.op * t'.op := by
  haveI := B.ha; haveI := B.hb; haveI := B.hν
  have hm := h4 E B.a B.b B.D B.μa B.μb B.ν B.Ma B.Mb B.κ t.ka t'.ka t.kb t'.kb t.va t'.va t.vb t'.vb t.T t'.T t.ψ t'.ψ
      B.compat ht.ka ht.kb ht'.ka ht'.kb ht.ψ ht'.ψ
  have hΦ : (t.mul t').Φ = mulM B.D.μ t.Φ t'.Φ := hm.2.symm
  have h := (h1 E B.a B.b B.D B.I).2 t.Φ t'.Φ t.op t'.op (test B h3 t ht) (test B h3 t' ht') (rop B h1 h3 t ht)
    (rop B h1 h3 t' ht')
  show B.opOf (t.mul t').Φ = _
  rw [hΦ]
  exact opOf_eq B h1 h.1 h.2.1

theorem adjOk (h2 : MultAlg) (t : PT B) (ht : t.Ok) : t.adj.Ok := by
  haveI := B.ha; haveI := B.hb
  refine ⟨ht.T, ht.r, fun v => (adjVal_spec h2 B.μa t.ka t.va t.T v (ht.ka v)).1,
    fun v => (adjVal_spec h2 B.μb t.kb t.vb t.T v (ht.kb v)).1, fun x y => ⟨?_, ?_⟩, ?_⟩
  · exact Complex.continuous_conj.comp ((ht.ψ y x).1.comp continuous_inv)
  · exact ((ht.ψ y x).2.comp_homeomorph (Homeomorph.inv _)).comp_left (g := starRingEnd ℂ) (map_zero _)
  · intro x y g hg
    have hg' : t.ψ y x g⁻¹ ≠ 0 := fun h0 => hg (by show starRingEnd ℂ (t.ψ y x g⁻¹) = 0; rw [h0, map_zero])
    have s := ht.size y x g⁻¹ hg'
    rw [Prod.fst_inv, Prod.snd_inv, map_inv, map_inv, logSize_inv, logSize_inv] at s
    exact s

theorem adjOp (h1 : OpEx) (h2 : MultAlg) (h3 : TensTest) (t : PT B) (ht : t.Ok) :
    t.adj.op = ContinuousLinearMap.adjoint t.op := by
  haveI := B.ha; haveI := B.hb
  have ha := h3 E B.a B.b B.μa B.μb B.Ma B.Mb B.κ t.ka t.kb t.va t.vb t.T t.ψ ht.ka ht.kb ht.ψ
  have hΦ : t.adj.Φ = adjM t.Φ := ha.2.symm
  have h := (h1 E B.a B.b B.D B.I).2 t.Φ t.Φ t.op t.op (test B h3 t ht) (test B h3 t ht) (rop B h1 h3 t ht)
    (rop B h1 h3 t ht)
  have htest : IsTestM (adjM t.Φ) := hΦ ▸ test B h3 t.adj (adjOk B h2 t ht)
  show B.opOf t.adj.Φ = _
  rw [hΦ]
  exact opOf_eq B h1 htest h.2.2

theorem mulVal (t t' : PT B) (χa : InfinitePlace E → Inf B.a) (χb : InfinitePlace E → Inf B.b) :
    (t.mul t').val χa χb = t.val χa χb * t'.val χa χb := by
  simp only [PT.val, PT.mul, valA, Pi.mul_apply, Finset.prod_mul_distrib]
  ring

theorem adjValEq (h2 : MultAlg) (t : PT B) (ht : t.Ok) (χa : InfinitePlace E → Inf B.a)
    (χb : InfinitePlace E → Inf B.b) (ha : ∀ v, IsHerm (χa v)) (hb : ∀ v, IsHerm (χb v)) :
    t.adj.val χa χb = starRingEnd ℂ (t.val χa χb) := by
  haveI := B.ha; haveI := B.hb
  simp only [PT.val, PT.adj, valA]
  rw [map_mul, map_prod, map_prod]
  congr 1
  · exact Finset.prod_congr rfl fun v _ => (adjVal_spec h2 B.μa t.ka t.va t.T v (ht.ka v)).2 _ (ha v)
  · exact Finset.prod_congr rfl fun v _ => (adjVal_spec h2 B.μb t.kb t.vb t.T v (ht.kb v)).2 _ (hb v)

theorem commPhi (h2 : MultAlg) (t t' : PT B) (ht : t.Ok) (ht' : t'.Ok)
    (hψ : mulF B.ν t.ψ t'.ψ = mulF B.ν t'.ψ t.ψ) : (t.mul t').Φ = (t'.mul t).Φ := by
  haveI := B.ha; haveI := B.hb
  have ea : ∀ v (g : GA E B.a), convK B.μa t.ka t'.ka v (gInf v g).val = convK B.μa t'.ka t.ka v (gInf v g).val :=
    fun v g => (h2 B.a B.μa (B.Ma v) (t.ka v) (t'.ka v) (t.va v) (t'.va v) t.T t'.T (ht.ka v) (ht'.ka v)).2.1 _
      (Matrix.isUnits_det_units _).ne_zero
  have eb : ∀ v (g : GA E B.b), convK B.μb t.kb t'.kb v (gInf v g).val = convK B.μb t'.kb t.kb v (gInf v g).val :=
    fun v g => (h2 B.b B.μb (B.Mb v) (t.kb v) (t'.kb v) (t.vb v) (t'.vb v) t.T t'.T (ht.kb v) (ht'.kb v)).2.1 _
      (Matrix.isUnits_det_units _).ne_zero
  funext i j g
  simp only [PT.Φ, PT.mul, tens, entA, hψ, ea, eb]

end Op

theorem blkOp (h1 : OpEx) (h2 : MultAlg) (h3 : TensTest) (h4 : TensMul) : BlockOperatorsProductAdjoint := by
  intro E _ _ _ B t t' ht ht'
  exact ⟨Op.test B h3 t ht, Op.rop B h1 h3 t ht, Op.mulOk B h2 h4 t t' ht ht', Op.mulOp B h1 h3 h4 t t' ht ht',
    Op.adjOk B h2 t ht, Op.adjOp B h1 h2 h3 t ht, Op.mulVal B t t', Op.adjValEq B h2 t ht⟩

theorem blkComm (h1 : OpEx) (h2 : MultAlg) (h3 : TensTest) (h4 : TensMul) : BlockPureTensorsCommute := by
  intro E _ _ _ B t t' ht ht' hψ
  show t.op * t'.op = t'.op * t.op
  rw [← Op.mulOp B h1 h3 h4 t t' ht ht', ← Op.mulOp B h1 h3 h4 t' t ht' ht]
  exact congrArg B.opOf (Op.commPhi B h2 t t' ht ht' hψ)

end PositivityTheory.Rg.BcB.F

end
