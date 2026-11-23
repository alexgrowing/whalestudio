import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.SphComm2
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.FmTools

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

open UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.F.RS

attribute [local instance] borelG borelF borelA borelH

private theorem heckeVec_fst {G₁ G₂ V : Type} [Group G₁] [Group G₂] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (G₁ × G₂) V) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) {x : V}
    (hx : x ∈ fixed ρ (K₁.prod K₂)) (f : G₁ → ℂ) (h : G₂ → ℂ)
    (hf : ∀ g, ∀ k ∈ K₁, f (g * k) = f g) (h0 : ∀ g, g ∉ K₂ → h g = 0) (h1 : ∀ g ∈ K₂, h g = 1) :
    heckeVec ρ (K₁.prod K₂) (fun g => f g.1 * h g.2) x =
      heckeVec (ρ.comp (MonoidHom.inl G₁ G₂)) K₁ f x := by
  unfold heckeVec
  let e : G₁ ⧸ K₁ → (G₁ × G₂) ⧸ (K₁.prod K₂) := fun c => QuotientGroup.mk (c.out, 1)
  have he : Function.Injective e := by
    intro c d hcd
    have h2 := QuotientGroup.eq.1 hcd
    have h3 : c.out⁻¹ * d.out ∈ K₁ := by simpa using (Subgroup.mem_prod.1 h2).1
    rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' d]
    exact QuotientGroup.eq.2 h3
  have hsupp : Function.support (fun c : (G₁ × G₂) ⧸ (K₁.prod K₂) => (f c.out.1 * h c.out.2) • ρ c.out x) ⊆ Set.range e := by
    intro d hd
    have hk : d.out.2 ∈ K₂ := by
      by_contra hn
      exact hd (by simp [h0 _ hn])
    refine ⟨QuotientGroup.mk d.out.1, ?_⟩
    rw [← QuotientGroup.out_eq' d]
    refine QuotientGroup.eq.2 (Subgroup.mem_prod.2 ⟨?_, by simpa using hk⟩)
    have h3 : (QuotientGroup.mk d.out.1 : G₁ ⧸ K₁).out⁻¹ * d.out.1 ∈ K₁ :=
      QuotientGroup.eq.1 (QuotientGroup.out_eq' _)
    simpa using h3
  have key : ∑ᶠ d : (G₁ × G₂) ⧸ (K₁.prod K₂), (f d.out.1 * h d.out.2) • ρ d.out x =
      ∑ᶠ c : G₁ ⧸ K₁, (f (e c).out.1 * h (e c).out.2) • ρ (e c).out x := by
    rw [← finsum_mem_range he (f := fun d : (G₁ × G₂) ⧸ (K₁.prod K₂) => (f d.out.1 * h d.out.2) • ρ d.out x),
      finsum_mem_def, Set.indicator_eq_self.2 hsupp]
  refine key.trans (finsum_congr fun c => ?_)
  have hm : ((c.out, 1) : G₁ × G₂)⁻¹ * (e c).out ∈ K₁.prod K₂ :=
    QuotientGroup.eq.1 (QuotientGroup.out_eq' (e c)).symm
  obtain ⟨m1, m2⟩ := Subgroup.mem_prod.1 hm
  have m1' : c.out⁻¹ * (e c).out.1 ∈ K₁ := by simpa using m1
  have m2' : (e c).out.2 ∈ K₂ := by simpa using m2
  have hfd : f (e c).out.1 = f c.out := by
    have := hf c.out _ m1'
    rwa [mul_inv_cancel_left] at this
  have hρ : ρ (e c).out x = ρ (c.out, 1) x := by
    have h5 : ρ (((c.out, 1) : G₁ × G₂) * (((c.out, 1) : G₁ × G₂)⁻¹ * (e c).out)) x = ρ (c.out, 1) x := by
      rw [map_mul, Module.End.mul_apply, GlobalTheory.LGrp.mem_fixed.1 hx _ hm]
    rwa [mul_inv_cancel_left] at h5
  rw [hfd, h1 _ m2', hρ, mul_one]
  rfl

private theorem heckeVec_snd {G₁ G₂ V : Type} [Group G₁] [Group G₂] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (G₁ × G₂) V) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) {x : V}
    (hx : x ∈ fixed ρ (K₁.prod K₂)) (f : G₂ → ℂ) (h : G₁ → ℂ)
    (hf : ∀ g, ∀ k ∈ K₂, f (g * k) = f g) (h0 : ∀ g, g ∉ K₁ → h g = 0) (h1 : ∀ g ∈ K₁, h g = 1) :
    heckeVec ρ (K₁.prod K₂) (fun g => h g.1 * f g.2) x =
      heckeVec (ρ.comp (MonoidHom.inr G₁ G₂)) K₂ f x := by
  unfold heckeVec
  let e : G₂ ⧸ K₂ → (G₁ × G₂) ⧸ (K₁.prod K₂) := fun c => QuotientGroup.mk (1, c.out)
  have he : Function.Injective e := by
    intro c d hcd
    have h2 := QuotientGroup.eq.1 hcd
    have h3 : c.out⁻¹ * d.out ∈ K₂ := by simpa using (Subgroup.mem_prod.1 h2).2
    rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' d]
    exact QuotientGroup.eq.2 h3
  have hsupp : Function.support (fun c : (G₁ × G₂) ⧸ (K₁.prod K₂) => (h c.out.1 * f c.out.2) • ρ c.out x) ⊆ Set.range e := by
    intro d hd
    have hk : d.out.1 ∈ K₁ := by
      by_contra hn
      exact hd (by simp [h0 _ hn])
    refine ⟨QuotientGroup.mk d.out.2, ?_⟩
    rw [← QuotientGroup.out_eq' d]
    refine QuotientGroup.eq.2 (Subgroup.mem_prod.2 ⟨by simpa using hk, ?_⟩)
    have h3 : (QuotientGroup.mk d.out.2 : G₂ ⧸ K₂).out⁻¹ * d.out.2 ∈ K₂ :=
      QuotientGroup.eq.1 (QuotientGroup.out_eq' _)
    simpa using h3
  have key : ∑ᶠ d : (G₁ × G₂) ⧸ (K₁.prod K₂), (h d.out.1 * f d.out.2) • ρ d.out x =
      ∑ᶠ c : G₂ ⧸ K₂, (h (e c).out.1 * f (e c).out.2) • ρ (e c).out x := by
    rw [← finsum_mem_range he (f := fun d : (G₁ × G₂) ⧸ (K₁.prod K₂) => (h d.out.1 * f d.out.2) • ρ d.out x),
      finsum_mem_def, Set.indicator_eq_self.2 hsupp]
  refine key.trans (finsum_congr fun c => ?_)
  have hm : ((1, c.out) : G₁ × G₂)⁻¹ * (e c).out ∈ K₁.prod K₂ :=
    QuotientGroup.eq.1 (QuotientGroup.out_eq' (e c)).symm
  obtain ⟨m1, m2⟩ := Subgroup.mem_prod.1 hm
  have m1' : (e c).out.1 ∈ K₁ := by simpa using m1
  have m2' : c.out⁻¹ * (e c).out.2 ∈ K₂ := by simpa using m2
  have hfd : f (e c).out.2 = f c.out := by
    have := hf c.out _ m2'
    rwa [mul_inv_cancel_left] at this
  have hρ : ρ (e c).out x = ρ (1, c.out) x := by
    have h5 : ρ (((1, c.out) : G₁ × G₂) * (((1, c.out) : G₁ × G₂)⁻¹ * (e c).out)) x = ρ (1, c.out) x := by
      rw [map_mul, Module.End.mul_apply, GlobalTheory.LGrp.mem_fixed.1 hx _ hm]
    rwa [mul_inv_cancel_left] at h5
  rw [hfd, h1 _ m1', hρ, one_mul]
  rfl

private theorem tj_zero_mem {E : Type} [Field E] [NumberField E] (w : Pl E) (n : ℕ) (ϖ : w.adicCompletion E) :
    ∀ g ∈ KGL w n, Tj ℂ n (Ov E w) ϖ 0 g = 1 := by
  intro g hg
  unfold Tj
  refine Set.indicator_of_mem ?_ _
  exact ⟨g, hg, 1, one_mem _, by simp [diagJ]⟩

private theorem tj_zero_not {E : Type} [Field E] [NumberField E] (w : Pl E) (n : ℕ) (ϖ : w.adicCompletion E) :
    ∀ g, g ∉ KGL w n → Tj ℂ n (Ov E w) ϖ 0 g = 0 := by
  intro g hg
  unfold Tj
  refine Set.indicator_of_notMem ?_ _
  rintro ⟨x, hx, y, hy, e⟩
  refine hg ?_
  have : g = x * y := Units.ext (by simpa [diagJ] using e)
  rw [this]
  exact mul_mem hx hy

private theorem tj_right {E : Type} [Field E] [NumberField E] (w : Pl E) (n : ℕ) {ϖ : w.adicCompletion E}
    (hϖ : IsUnifV E w ϖ) (i : ℕ) : ∀ g, ∀ k ∈ KGL w n, Tj ℂ n (Ov E w) ϖ i (g * k) = Tj ℂ n (Ov E w) ϖ i g := by
  intro g k hk
  have := (Tj_mem_hecke (n := n) hϖ i).1 1 ⟨k, hk⟩ g
  simpa using this

private theorem sat_zero (q n : ℕ) (B : Multiset ℂˣ) : satEig q n B 0 = 1 := by
  simp [satEig, Multiset.esymm]

theorem UpperTheory.Zero.ConvolutionTheory.EB.sat2Slice :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (G : H E a b → ℂ) (B₁ B₂ : Multiset ℂˣ), IsSat2 w (pairRt a b w) G B₁ B₂ →
    (∀ (φ : Sm E a) m₂, (φ.1 = fun x => G (x, m₂)) → φ ≠ 0 → IsSatVecGL w (UpperTheory.V.Cj.S.fL a w) φ B₁) ∧
    ∀ (φ : Sm E b) m₁, (φ.1 = fun x => G (m₁, x)) → φ ≠ 0 → IsSatVecGL w (UpperTheory.V.Cj.S.fL b w) φ B₂ := by
  intro E _ _ _ a b w G B₁ B₂ hS
  obtain ⟨hfix, c₁, c₂, hT⟩ := hS
  refine ⟨fun φ m₂ hφ h0 => ?_, fun φ m₁ hφ h0 => ?_⟩
  · have hG0 : G ≠ 0 := by
      rintro rfl
      exact h0 (Subtype.ext hφ)
    have s1 : IsSatVecGL w ((pairRt a b w).comp (MonoidHom.inl _ _)) G B₁ := by
      refine ⟨hG0, GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_, c₁, fun ϖ hϖ i hi => ?_⟩
      · exact GlobalTheory.LGrp.mem_fixed.1 hfix _ (Subgroup.mem_prod.2 ⟨hk, one_mem _⟩)
      · have h1 := hT ϖ hϖ i hi 0 (Nat.zero_le _)
        rw [heckeVec_fst _ _ _ hfix _ _ (tj_right w a hϖ i) (tj_zero_not w b ϖ) (tj_zero_mem w b ϖ),
          sat_zero, mul_one] at h1
        exact h1
    let L : (H E a b → ℂ) →ₗ[ℂ] (GA E a → ℂ) :=
      { toFun := fun F x => F (x, m₂), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have s2 : IsSatVecGL w ((rightReg ℂ (GA E a) ℂ).comp (embW a w)) (L G) B₁ :=
      s1.map L (fun g y => by
        funext x
        simp [L, pairRt, rightReg, LinearMap.funLeft]) (fun e => h0 (Subtype.ext (hφ.trans e)))
    have e : (Sm E a).subtype φ = L G := hφ
    rw [← e] at s2
    exact IsSatVecGL.of_map (Sm E a).subtype (fun _ _ => rfl) Subtype.val_injective s2
  · have hG0 : G ≠ 0 := by
      rintro rfl
      exact h0 (Subtype.ext hφ)
    have s1 : IsSatVecGL w ((pairRt a b w).comp (MonoidHom.inr _ _)) G B₂ := by
      refine ⟨hG0, GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_, c₂, fun ϖ hϖ i hi => ?_⟩
      · exact GlobalTheory.LGrp.mem_fixed.1 hfix _ (Subgroup.mem_prod.2 ⟨one_mem _, hk⟩)
      · have h1 := hT ϖ hϖ 0 (Nat.zero_le _) i hi
        rw [heckeVec_snd _ _ _ hfix _ _ (tj_right w b hϖ i) (tj_zero_not w a ϖ) (tj_zero_mem w a ϖ),
          sat_zero, one_mul] at h1
        exact h1
    let L : (H E a b → ℂ) →ₗ[ℂ] (GA E b → ℂ) :=
      { toFun := fun F x => F (m₁, x), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have s2 : IsSatVecGL w ((rightReg ℂ (GA E b) ℂ).comp (embW b w)) (L G) B₂ :=
      s1.map L (fun g y => by
        funext x
        simp [L, pairRt, rightReg, LinearMap.funLeft]) (fun e => h0 (Subtype.ext (hφ.trans e)))
    have e : (Sm E b).subtype φ = L G := hφ
    rw [← e] at s2
    exact IsSatVecGL.of_map (Sm E b).subtype (fun _ _ => rfl) Subtype.val_injective s2
