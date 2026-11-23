import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SplitAt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ImportsBis
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.LiftRel
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SpanCont
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.ContMkE
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.WeLoc
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.WhTorus
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.HeckeExpl
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.FixTr
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.AeInt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.GoodOfGoodAt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.LcLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.EigOfSat
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalSatakeAlmostAll

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H
open scoped Classical

private theorem below_ev {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {p : P F → Prop} (h : ∀ᶠ v in cofinite, p v) : ∀ᶠ w : P E in cofinite, ∀ v, Below v w → p v := by
  have hfin : ∀ v : P F, {w : P E | Below v w}.Finite := fun v => by
    haveI := v.isMaximal
    refine Set.Finite.of_finite_image (f := HeightOneSpectrum.asIdeal)
      ((IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 E)).subset ?_) (fun _ _ _ _ h => HeightOneSpectrum.ext h)
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨w.isPrime, ⟨hw⟩⟩
  have hS : {v | ¬ p v}.Finite := h
  have : (⋃ v ∈ {v | ¬ p v}, {w : P E | Below v w}).Finite := hS.biUnion fun v _ => hfin v
  filter_upwards [this.eventually_cofinite_notMem] with w hw v hv
  by_contra hc
  exact hw (Set.mem_biUnion hc hv)

private def LRel {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E]
    {D : Dat F E} (W : Weil D) (π : TR.CuspSub F 2) (h₀ : GL (Fin 2) (A E)) (Φ : GL (Fin 2) (A E) → ℂ) (v : P F) : Prop :=
  W.η.UnrAt v → W.η.val v = -1 → ∀ α β : ℂˣ, π.HasSat v {α, β} → ∀ (ϖ : (Kv v)ˣ) (z : (A E)ˣ), IsU ϖ →
    (z : A E) = D.mkE (idl v ϖ : (A F)ˣ) 0 → ideleNorm F E z = idl v ϖ ^ 2 →
    WE D Φ (aE z * h₀) = (q v)⁻¹ * ((α : ℂ) ^ 2 + (β : ℂ) ^ 2) * WE D Φ h₀ ∧
      ∀ h, Φ (Matrix.GeneralLinearGroup.scalar (Fin 2) z * h) = ((α : ℂ) * β) ^ 2 * Φ h

private theorem we_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E)
    (h : GL (Fin 2) (A E)) : WE D (0 : GL (Fin 2) (A E) → ℂ) h = 0 := by
  simp [WE]

private theorem span_rel {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E]
    (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2) (h₀ : GL (Fin 2) (A E)) (Φ : Sm E 2) (hΦ : Φ ∈ span W M π) :
    ∀ᶠ v : P F in cofinite, LRel W π h₀ Φ.1 v := by
  have hc : ∀ Ψ ∈ span W M π, Continuous Ψ.1 := fun Ψ h => (spanCont F E D W M π Ψ h).1
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, φ, hφ, e⟩ := hx
    rw [e]
    exact liftRel F E D W M π f hf φ hφ h₀
  | zero =>
    refine Filter.Eventually.of_forall fun v _ _ α β _ ϖ z _ _ _ => ⟨?_, fun h => ?_⟩
    · show WE D (0 : GL (Fin 2) (A E) → ℂ) _ = _ * WE D (0 : GL (Fin 2) (A E) → ℂ) _
      simp [we_zero]
    · show (0 : GL (Fin 2) (A E) → ℂ) _ = _ * (0 : GL (Fin 2) (A E) → ℂ) _
      simp
  | add x y hx hy ihx ihy =>
    filter_upwards [ihx, ihy] with v h1 h2 hu hv α β hB ϖ z hϖ hz hn
    obtain ⟨a1, a2⟩ := h1 hu hv α β hB ϖ z hϖ hz hn
    obtain ⟨b1, b2⟩ := h2 hu hv α β hB ϖ z hϖ hz hn
    have e : ∀ h, WE D (x + y).1 h = WE D x.1 h + WE D y.1 h := fun h => by
      have := (weEig F E D x.1 (hc x hx)).2.2 y.1 1 (hc y hy) h
      simpa using this
    refine ⟨?_, fun h => ?_⟩
    · rw [e, e, a1, b1]; ring
    · show x.1 _ + y.1 _ = _ * (x.1 _ + y.1 _)
      rw [a2, b2]; ring
  | smul c x hx ihx =>
    filter_upwards [ihx] with v h1 hu hv α β hB ϖ z hϖ hz hn
    obtain ⟨a1, a2⟩ := h1 hu hv α β hB ϖ z hϖ hz hn
    have e : ∀ h, WE D (c • x).1 h = c * WE D x.1 h := fun h => by
      have := (weEig F E D 0 continuous_const).2.2 x.1 c (hc x hx) h
      simpa [we_zero] using this
    refine ⟨?_, fun h => ?_⟩
    · rw [e, e, a1]; ring
    · show c * x.1 _ = _ * (c * x.1 _)
      rw [a2]; ring

private theorem pairs {a b c d : ℂ} (hs : c + d = a + b) (hp : c * d = a * b) : (c = a ∧ d = b) ∨ (c = b ∧ d = a) := by
  have h : (c - a) * (c - b) = 0 := by linear_combination c * hs - hp
  rcases mul_eq_zero.1 h with h | h
  · have e : c = a := sub_eq_zero.1 h
    exact Or.inl ⟨e, by rw [e] at hs; exact add_left_cancel hs⟩
  · have e : c = b := sub_eq_zero.1 h
    exact Or.inr ⟨e, by rw [e, add_comm a] at hs; exact add_left_cancel hs⟩

theorem UpperTheory.ConvolutionTheory.R2.H.unrInert :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), ThetaLiftTrivialOrbitTermsVanish W M π → ∀ Q : CuspSub E 2, Q.V ≤ span W M π →
      ∀ᶠ w : P E in cofinite, ∀ v : P F, Below v w → Inert D v w → ∀ B, π.HasSat v B → (CG.mk Q).HasSat w (B.map (· ^ 2)) := by
  intro F E _ _ _ _ _ _ _ D W M π hN Q hQ
  obtain ⟨y, hy, h0⟩ := (Submodule.ne_bot_iff _).1 Q.ne_bot
  have hsp := hQ hy
  obtain ⟨hcont, hleft⟩ := spanCont F E D W M π y hsp
  obtain ⟨-, hwh⟩ := UpperTheory.ConvolutionTheory.R2.cusp F E D W M π hN y hsp
  obtain ⟨h₀, hh₀⟩ : ∃ h₀, WE D y.1 h₀ ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact h0 (hwh hc)
  obtain ⟨h₁, hh₁⟩ : ∃ h₁, y.1 h₁ ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact h0 (Subtype.ext (funext hc))
  have hδ : D.δ ≠ 0 := fun e => by
    have h1 : D.θ = 0 := pow_eq_zero_iff two_ne_zero |>.1 (by rw [D.sq, e, map_zero])
    exact D.b.ne_zero 1 (D.b1.trans h1)
  have hne : (⟨y, hy⟩ : Q.V) ≠ 0 := fun e => h0 (congrArg Subtype.val e)
  filter_upwards [below_ev (span_rel D W M π h₀ y hsp), W.quad, GlobalTheory.CuspRep.AeFix.eventually_mem_fixed E 2 Q ⟨y, hy⟩,
    (aeK E).1 h₀, GlobalTheory.CompanionTheory.SatAe.eventually_exists_hasSat Q, below_ev (gdAe F D.δ hδ)] with w hrel hq hfix hk ⟨B', hB'⟩ hgd v hv hin B hB
  obtain ⟨hu, hval⟩ := hq v hv
  have hnv : 1 < normV v := by
    have := GlobalTheory.LFun.one_lt_absNorm v
    simpa [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using this
  have hn : normV w ≠ normV v := fun e => by
    have h3 := hin.norm
    rw [e] at h3
    nlinarith
  rw [if_neg hn] at hval
  obtain ⟨α, β, rfl⟩ := Multiset.card_eq_two.1 (GlobalTheory.LFun.HasSatGL.card hB)
  obtain ⟨α', β', rfl⟩ := Multiset.card_eq_two.1 (GlobalTheory.LFun.HasSatGL.card hB')
  obtain ⟨p, hp⟩ : ∃ p, Formalism.UG.IsUnifV F v p := v.valuedAdicCompletion_surjective F _
  have hp0 : p ≠ 0 := fun h0 => by simp [Formalism.UG.IsUnifV, h0] at hp
  obtain ⟨ϖ', hϖ', hz, hnz⟩ := hin.unif (Units.mk0 p hp0) hp
  obtain ⟨r1, r2⟩ := hrel v hv hu hval α β hB (Units.mk0 p hp0) (idl w ϖ') hp hz hnz
  have hfix' : ∀ g, ∀ k ∈ GlobalTheory.LFun.KGL w 2, y.1 (g * finGL E 2 (locGL E 2 w k)) = y.1 g := fun g k hk =>
    congrFun (congrArg (fun x : Q.V => x.1.1) (GlobalTheory.LGrp.mem_fixed.1 hfix k hk)) g
  have hEig : EigAt w {α', β'} y.1 := UpperTheory.V.Af.StrongMultiplicityOne.eigOfSat E 2 Q w _ hB' y hy hfix'
  have hEw := (weEig F E D y.1 hcont).2.1 w _ hEig
  have hE1 : Eig w {α', β'} fun x => WE D y.1 (lc w x * h₀) := by
    have := (fixTr E w _ h₀ hk).2 _ hEw 1
    simpa [lc] using this
  obtain ⟨χ, hχ, hχe⟩ := weLoc F E D v w (hgd v hv) hin
  have hnl : ∀ b x, WE D y.1 (lc w (nL b * x) * h₀) = χ b * WE D y.1 (lc w x * h₀) := fun b x => by
    obtain ⟨u, t, e1, e2⟩ := hχe b
    rw [map_mul, (lcLaws E w).1, e1, mul_assoc, ((weEig F E D y.1 hcont).1 hleft) u t, e2]
  obtain ⟨t1, -⟩ := whTorus E w ϖ' hϖ' χ hχ α' β' _ hE1 hnl
  obtain ⟨R, -, -, hR⟩ := heckeExpl E w ϖ' hϖ'
  have hc := (hR α' β' _ (hEig h₁) 1).2
  have hc' : y.1 (h₁ * Matrix.GeneralLinearGroup.scalar (Fin 2) (idl w ϖ')) = (α' : ℂ) * β' * y.1 h₁ := by
    simp only [one_mul, map_one, mul_one] at hc
    rw [← (lcLaws E w).2.2.2.2.1]
    exact hc
  have hp' : (α' : ℂ) * β' = (α : ℂ) ^ 2 * (β : ℂ) ^ 2 := by
    have h2 := r2 h₁
    rw [GlobalTheory.CuspRep.scalar_comm, hc'] at h2
    have h3 := mul_right_cancel₀ hh₁ h2
    rw [h3]
    ring
  have e1 : WE D y.1 (lc w (dL ϖ' 1) * h₀) = WE D y.1 (aE (idl w ϖ') * h₀) := by rw [(lcLaws E w).2.2.2.1]
  have e2 : WE D y.1 (lc w 1 * h₀) = WE D y.1 h₀ := by simp
  beta_reduce at t1
  rw [e1, e2, r1] at t1
  have hcard : ∀ {K : Type} [Field K] [NumberField K] (u : P K), q u = (normV u : ℂ) := fun u => by
    simp [q, normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hqw : q w = q v ^ 2 := by
    rw [hcard, hcard, hin.norm]
    push_cast
    rfl
  have hqv : q v ≠ 0 := by
    rw [hcard]
    exact Nat.cast_ne_zero.2 (by omega)
  have hsq : q w ^ (1 / 2 : ℂ) = q v := by
    rw [hqw, hcard]
    have e : ((normV v : ℂ) ^ 2) = ((((normV v : ℝ) ^ 2 : ℝ)) : ℂ) := by push_cast; rfl
    rw [e, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; rfl, ← Complex.ofReal_cpow (by positivity),
      ← Real.sqrt_eq_rpow, Real.sqrt_sq (by positivity)]
    simp
  have hs : (α' : ℂ) + β' = (α : ℂ) ^ 2 + (β : ℂ) ^ 2 := by
    rw [hsq, hqw] at t1
    have h3 : q v ^ 2 * ((q v)⁻¹ * ((α : ℂ) ^ 2 + (β : ℂ) ^ 2) * WE D y.1 h₀) =
        q v * ((α : ℂ) ^ 2 + (β : ℂ) ^ 2) * WE D y.1 h₀ := by
      field_simp
    rw [h3] at t1
    exact (mul_left_cancel₀ hqv (mul_right_cancel₀ hh₀ t1)).symm
  rcases pairs hs hp' with ⟨a, b⟩ | ⟨a, b⟩
  · have a' : α' = α ^ 2 := Units.ext (by simpa using a)
    have b' : β' = β ^ 2 := Units.ext (by simpa using b)
    rw [a', b'] at hB'
    simpa using hB'
  · have a' : α' = β ^ 2 := Units.ext (by simpa using a)
    have b' : β' = α ^ 2 := Units.ext (by simpa using b)
    rw [a', b', Multiset.pair_comm] at hB'
    simpa using hB'
