import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.TanOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.WsLink
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicPointGalois
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PointTheoremBaseObject
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TNiceFour
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.RRFree
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.IsAutCsdA

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Th
open UpperTheory.V.Ws.Eb
private theorem tan_one {K H : Type} [CommRing K] [Group H] {n : ℕ} {ρ : H →* GL (Fin n) K} {y : H → Matrix (Fin n) (Fin n) K}
    {ρ' : H →* GL (Fin n) (DualNumber K)} (h : IsTan ρ y ρ') (g : H) (hg : ρ' g = 1) : y g = 0 := by
  have e1 := h g
  rw [hg] at e1
  have e2 : (ρ g : Matrix (Fin n) (Fin n) K) = 1 := by
    ext i j
    have := congrArg TrivSqZeroExt.fst (e1 i j)
    by_cases h : i = j <;> simpa [Matrix.one_apply, h] using this.symm
  ext i j
  have := congrArg TrivSqZeroExt.snd (e1 i j)
  rw [e2, mul_one] at this
  by_cases h : i = j <;> simpa [Matrix.one_apply, h] using this.symm
private theorem at_l (hP : Loc.LocalPublishedTheorems) {l : ℕ} [Fact l.Prime] {F : W.GFrame l} {c : Coef l} {n : ℕ} {r : W.Resid F c.O n}
    (B : W.UniversalOrdinaryDeterminantRing r) (Λ : W.LamObj r) (x' : B.B →ₐ[c.O] DualNumber (PadicAlgCl l)) (hΛ : ∀ a, (x' (Λ.toPair B.u a)).snd = 0)
    {ρ : F.G₀ →* GL (Fin n) (PadicAlgCl l)} {y : F.G₀ → Matrix (Fin n) (Fin n) (PadicAlgCl l)} {ρ' : F.G₀ →* GL (Fin n) (DualNumber (PadicAlgCl l))}
    (hcont : Continuous ρ) (hy : y ∈ Z1 (Loc.adGL ρ)) (htan : IsTan ρ y ρ') {P : GL (Fin n) (PadicAlgCl l)}
    {R : Representation (PadicAlgCl l) F.Γ (Matrix (Fin n) (Fin n) (PadicAlgCl l))} (hR : IsAdExt F ρ P R)
    {z : F.Γ → Matrix (Fin n) (Fin n) (PadicAlgCl l)} (hzy : ∀ g : F.G₀, z g = y g) (v : F.Vl)
    (hfl : W.HasFlag (ρ'.comp (F.φ v)) fun i => W.pushCh (x' : B.B →+* DualNumber (PadicAlgCl l)) (B.u.ψ v i))
    (m : Fin n → ℤ) (k : ℕ) (hm : ∀ i j, i < j → m j + 2 ≤ m i) (hk : 0 < k) (φ : F.Gv v →* Formalism.BasicNotions.Loc.GQ l)
    (hφ : Topology.IsOpenEmbedding φ) (h1 : ∀ g, φ g ∈ Loc.Iq l ↔ g ∈ F.Iv v)
    (h2 : ∀ i, ∀ g ∈ F.Iv v, (W.pushCh ((dF _).comp (x' : B.B →+* DualNumber (PadicAlgCl l))) (B.u.ψ v i) g *
      Loc.cycA l l (PadicAlgCl l) (φ g) ^ (-m i)) ^ k = 1) :
    (fun g : F.Gv v => z (F.φ v g)) ∈ Loc.finiteCocycles φ (R.comp (F.η.ker.subtype.comp (F.φ v)) :
      Representation (PadicAlgCl l) (F.Gv v) (Matrix (Fin n) (Fin n) (PadicAlgCl l))) := by
  have e1 : (R.comp (F.η.ker.subtype.comp (F.φ v)) : Representation (PadicAlgCl l) (F.Gv v) (Matrix (Fin n) (Fin n) (PadicAlgCl l))) =
      Loc.adGL (ρ.comp (F.φ v)) := MonoidHom.ext fun g => LinearMap.ext fun X => hR.ad _ X
  rw [e1]
  simp only [hzy]
  refine locL hP φ hφ (ρ.comp (F.φ v)) (hcont.comp (F.φ_cont v)) _
    ⟨hy.1.comp (F.φ_cont v), fun g h => ?_⟩ _ (htan.comp (F.φ v)) _ m k hfl hm hk fun i g hg => ⟨?_, h2 i g ((h1 g).1 hg)⟩
  · exact (congrArg y (map_mul _ g h)).trans (hy.2 _ _)
  · have e2 := congrArg Units.val (DFunLike.congr_fun (W.LamObj.toPair_spec r Λ B.u v i) ⟨g, (h1 g).1 hg⟩)
    exact (congrArg (fun b => (x' b).snd) e2).symm.trans (hΛ _)
section
variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {s : W.HidaSetting l L Ω} {V : s.Lev} {c : Coef l} {n : ℕ} {r : W.Resid V.frame c.O n} {B : W.UniversalOrdinaryDeterminantRing r}
private theorem over_l (v : W.Vl l L) : (s.A v).valuation (l : Ω) < 1 := by
  simpa using (s.hA v _).2 v.2
private theorem arith (hP : _root_.UpperTheory.V.Af.HypothesesH') (x : B.Pt) (m : W.Vl l L → Fin n → ℤ) (hm : ∀ v i j, i < j → m v j + 2 ≤ m v i) (k : ℕ) (hk : 0 < k)
    (hw : ∀ (v : W.Vl l L) i (g : Dec (F := L) (s.A v)), (g : G L Ω) ∈ Ine (F := L) (s.A v) →
      (x.psi v i g * cycBar L Ω l g ^ (-m v i)) ^ k = 1) : x.Arith fun v j _ => -m v j := by
  have hl : ∀ v : W.Vl l L, ((l : ℕ) : 𝓞 L) ∈ (s.w v).asIdeal := fun v => by
    refine (s.hw v _).1 ?_
    simpa using over_l (s := s) v
  refine ⟨fun v τ i j hij => ?_, fun v j => ?_⟩
  · have := hm v i j hij
    simp only
    omega
  · exact UpperTheory.V.Loc.laArith hP.toClassicalTheorems.litN.aut.art (s.hw v) (hl v) _ (Ws.Pt.psi_cont x v j) (m v j) k hk (hw v j)
private theorem noRatio (x : B.Pt) (m : W.Vl l L → Fin n → ℤ) (hm : ∀ v i j, i < j → m v j + 2 ≤ m v i) (k : ℕ) (hk : 0 < k)
    (hw : ∀ (v : W.Vl l L) i (g : Dec (F := L) (s.A v)), (g : G L Ω) ∈ Ine (F := L) (s.A v) →
      (x.psi v i g * cycBar L Ω l g ^ (-m v i)) ^ k = 1) (v : W.Vl l L) (i j : Fin n) :
    x.psi v i ≠ x.psi v j * (cycBar L Ω l).comp (Dec (F := L) (s.A v)).subtype := by
  intro hij
  have hne : 1 - m v i + m v j ≠ 0 := by
    rcases lt_trichotomy i j with h | h | h
    · have := hm v i j h
      omega
    · subst h
      omega
    · have := hm v j i h
      omega
  obtain ⟨g, hg, hg1⟩ := Ws.Pt.cycIne L Ω l (s.A v) (over_l v) ((1 - m v i + m v j) * k)
    (mul_ne_zero hne (by exact_mod_cast hk.ne'))
  have hgD : g ∈ Dec (F := L) (s.A v) :=
    (GlobalTheory.WeilDeligne.Weil_le_Dec (s.hw v)) (GlobalTheory.WeilDeligne.ineIncl (s.hw v) ⟨g, hg⟩).2
  have h1 := hw v i ⟨g, hgD⟩ hg
  have h2 := hw v j ⟨g, hgD⟩ hg
  have e : x.psi v i ⟨g, hgD⟩ = x.psi v j ⟨g, hgD⟩ * cycBar L Ω l g := by
    rw [hij]; rfl
  apply hg1
  have e2 : x.psi v i ⟨g, hgD⟩ * cycBar L Ω l g ^ (-m v i) =
      (x.psi v j ⟨g, hgD⟩ * cycBar L Ω l g ^ (-m v j)) * cycBar L Ω l g ^ (1 - m v i + m v j) := by
    rw [e, mul_assoc, mul_assoc, ← zpow_add, ← zpow_one_add]
    congr 2
    ring
  change (x.psi v i ⟨g, hgD⟩ * cycBar L Ω l g ^ (-m v i)) ^ k = 1 at h1
  change (x.psi v j ⟨g, hgD⟩ * cycBar L Ω l g ^ (-m v j)) ^ k = 1 at h2
  rw [e2, mul_pow, h2, one_mul] at h1
  rw [zpow_mul, zpow_natCast, h1]
private theorem par (x : B.Pt) (m : W.Vl l L → Fin n → ℤ) (hm : ∀ v i j, i < j → m v j + 2 ≤ m v i) (k : ℕ) (hk : 0 < k)
    (hw : ∀ (v : W.Vl l L) i (g : Dec (F := L) (s.A v)), (g : G L Ω) ∈ Ine (F := L) (s.A v) →
      (x.psi v i g * cycBar L Ω l g ^ (-m v i)) ^ k = 1) : Par x := fun v =>
  ⟨m v, k, fun i j h => by have := hm v i j h; omega, hk, fun i j g hg => by
    have e : x.psi v i g / x.psi v j g * cycBar L Ω l g ^ (m v j - m v i) =
        (x.psi v i g * cycBar L Ω l g ^ (-m v i)) / (x.psi v j g * cycBar L Ω l g ^ (-m v j)) := by
      rw [mul_div_mul_comm, div_eq_mul_inv (_ ^ (-m v i)), ← zpow_neg, ← zpow_add]
      congr 2
      ring
    rw [e, div_pow, hw v i g hg, hw v j g hg, div_one]⟩
private theorem free (hP : _root_.UpperTheory.V.Af.HypothesesH') (hn : 1 ≤ n) (ι : PadicAlgCl l ≃+* ℂ) (x : B.Pt) (ρ : G L Ω →* GL (Fin n) (PadicAlgCl l))
    (m : W.Vl l L → Fin n → ℤ) (hρ : Continuous ρ) (haut : _root_.UpperTheory.V.Z.Win.IsAutCsdA ι ρ) (hm : ∀ v i j, i < j → m v j + 2 ≤ m v i)
    (hfl : ∀ v : W.Vl l L, W.HasFlag (ρ.comp (Dec (F := L) (s.A v)).subtype) (x.psi v)) (k : ℕ) (hk : 0 < k)
    (hw : ∀ (v : W.Vl l L) i (g : Dec (F := L) (s.A v)), (g : G L Ω) ∈ Ine (F := L) (s.A v) →
      (x.psi v i g * cycBar L Ω l g ^ (-m v i)) ^ k = 1) : Free V.frame fun v => x.psi v := fun v : W.Vl l L => by
  obtain ⟨g, hg, hf⟩ := _root_.UpperTheory.V.Z.Win.RR.exists_cycZ_eq_one_freeRatios_of_ne_mul_cycBar hP L Ω l s.odd ι n hn ρ hρ haut (s.A v) (over_l v) (x.psi v) (m v) k (hfl v)
    (fun i j h => by have := hm v i j h; omega) hk (hw v) (noRatio x m hm k hk hw v)
  refine ⟨g, ?_, hf⟩
  have e : V.ε (toGS Ω V.S' (W.resP L Ω g)) = cycZ (W.Lp L) Ω l (W.resP L Ω g) := DFunLike.congr_fun V.hε _
  exact e.trans hg
end
theorem UpperTheory.V.Th.eigenbasis_rank_four :
    _root_.UpperTheory.V.Ws.UnramifiedInputs → _root_.UpperTheory.V.Th.AdjointLiftingTheorem → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : W.HidaSetting l L Ω) (V : s.Lev), V.S' = s.S → (¬ ∃ ζ : L, IsPrimitiveRoot ζ l) → ∀ (c : Coef l), W.Large L c → ∀ (r : W.Resid V.frame c.O 4) (B : W.UniversalOrdinaryDeterminantRing r) (Λ : W.LamObj r) (ι : PadicAlgCl l ≃+* ℂ) (J : Ideal B.B), B.HidaPropsAlt ι J Λ → r.V0ok → (∀ η : V.frame.G₀ →* (ResidueField c.O)ˣ, η ^ 2 = 1 → (V.frame.eps c.O (ResidueField c.O)).ker ≤ η.ker → (∀ i, ∃ j, η * r.chib i = r.chib j) → η = 1) → (∃ i j, ∀ m : ℕ, 0 < m → m ≤ 4 → (r.chib i / r.chib j) ^ m ≠ 1) → ∀ (x : B.Pt) (ρ : G L Ω →* GL (Fin 4) (PadicAlgCl l)) (m : W.Vl l L → Fin 4 → ℤ), J ≤ RingHom.ker x → x.IsRep ρ → Continuous ρ →
          _root_.UpperTheory.V.Z.Win.IsAutCsdA ι ρ → (∀ g ∈ Ine (F := L) (s.A s.v0), ρ g = 1) → Af.IsIrr (ρ.comp (cycBar L Ω l).ker.subtype) → (∀ v i j, i < j → m v j + 2 ≤ m v i) →
          (∀ v : W.Vl l L, W.HasFlag (ρ.comp (Dec (F := L) (s.A v)).subtype) (x.psi v)) →
          (∃ k : ℕ, 0 < k ∧ ∀ (v : W.Vl l L) i (g : Dec (F := L) (s.A v)), (g : G L Ω) ∈ Ine (F := L) (s.A v) → (x.psi v i g * cycBar L Ω l g ^ (-m v i)) ^ k = 1) →
          ∀ q : Ideal B.B, q.IsPrime → q ≤ RingHom.ker x → J ≤ q := by
  intro hU hAd l _ L Ω _ _ _ _ _ _ s V hV hζ c hc r B Λ ι J hJ h0 hC hD4 x ρ m hJx hx hρ haut hv0 hirr hm hfl ⟨k, hk, hkk⟩
  obtain ⟨Λ', ⟨e'⟩⟩ := hU.lam l L Ω s V c 4 r
  obtain ⟨e₁⟩ := lamIso Λ' Λ
  obtain ⟨e, he⟩ : ∃ e : MvPowerSeries (Fin (4 * Module.finrank ℚ (W.Lp L))) c.O →ₐ[c.O] Λ.Λ, Function.Bijective e :=
    ⟨(e'.symm.trans e₁ :), (e'.symm.trans e₁).bijective⟩
  refine regOfTan c _ B.B ((Λ.toPair B.u).comp e) J ?_ (fun a ha b hb => ?_) x hJx fun x' hx' hΛ => ?_
  · exact hJ.ring.fin.comp (RingHom.Finite.of_surjective (e : MvPowerSeries (Fin (4 * Module.finrank ℚ (W.Lp L))) c.O →+* Λ.Λ) he.2)
  · exact hJ.ring.tf (e a) ((map_ne_zero_iff e he.1).2 ha) b hb
  have hΛ' : ∀ a, (x' (Λ.toPair B.u a)).snd = 0 := fun a => by
    obtain ⟨a, rfl⟩ := he.2 a
    exact hΛ a
  have hxx : (dF _).comp (x' : B.B →+* DualNumber (PadicAlgCl l)) = (x : B.B →+* PadicAlgCl l) := RingHom.ext hx'
  have hn1 : 1 ≤ 4 := by omega
  obtain ⟨ρ₀, rfl, hfull, hD⟩ := factor V B x ρ hn1 hx hirr
  obtain ⟨ρ', y, hD', hred, hfull', hcont, hy, htan⟩ := liftRep B x' ρ₀ hn1 hfull (by rw [hxx, hD])
  obtain ⟨hO, hI⟩ := relKill B x' ρ' hfull' hD'
  obtain ⟨P', hP'⟩ := relForm B x' ρ' hfull' hD'
  obtain ⟨hP, hrel⟩ := cocRel V.frame c.O ρ₀ y ρ' P' htan hP'
  obtain ⟨R, hR⟩ := adExt V.frame c.O ρ₀ _ hfull hP
  obtain ⟨Z, hZ⟩ := hrel R hR
  obtain ⟨z, hz, hzy⟩ := cocExt V.frame ρ₀ _ R hfull hcont hR y hy Z hZ
  have hinj : ∀ v : V.frame.Vl, Function.Injective fun i => W.pushCh ((dF _).comp (x' : B.B →+* DualNumber (PadicAlgCl l))) (B.u.ψ v i) := fun v => by
    rw [hxx]
    refine psiInj (s.A v.1) (s.w v.1) (s.hw v.1) ?_ (x.psi v) (m v) k
      (StrictAnti.injective fun i j h => by have := hm v i j h; omega) hk (hkk v)
    have h1 := (s.hA v.1 ((l : ℕ) : 𝓞 (W.Lp L))).2 v.2
    exact (s.hw v.1 _).1 (by simpa using h1)
  have hfl₀ : ∀ v : V.frame.Vl, W.HasFlag (ρ₀.comp (V.frame.φ v)) fun i => W.pushCh ((dF _).comp (x' : B.B →+* DualNumber (PadicAlgCl l))) (B.u.ψ v i) := fun v => by
    rw [hxx]
    exact hfl v
  have hfl' : ∀ v : V.frame.Vl, W.HasFlag (ρ'.comp (V.frame.φ v)) fun i => W.pushCh (x' : B.B →+* DualNumber (PadicAlgCl l)) (B.u.ψ v i) := fun v =>
    flagDual _ _ (hinj v) (by rw [← hred] at hfl₀; exact hfl₀ v) (hO v)
  have hbk := bkAb V R z hz
    (fun v φ hφ h1 h2 => at_l hU.coh.loc B Λ x' hΛ' hcont hy htan hR hzy v (hfl' v) (m v) k (hm v) hk φ hφ h1 fun i g hg => by
      rw [hxx, h2]
      exact hkk v i g hg)
    (bkAw V hV r R z hz (fun u g hg => (hzy g).trans (tan_one htan g (hI u g hg)))
      fun g hg => (hzy g).trans (cocycle_vanishes_on_inertia_of_point_pseudodeformation V B x ρ₀ h0 hD hcont y hy g hg))
  have hapt : _root_.UpperTheory.V.Th.AutomorphicPointGalois ι x ρ₀ := ⟨hcont, hx, ⟨_, arith hU.pr x m hm k hk hkk⟩, haut, by
    rintro _ ⟨g, hg, rfl⟩
    exact hv0 g hg, hfl⟩
  have hirr₀ : U3.MatIrr ⊤ (W.mat ρ₀) := fun N hN => (AlgebraTools.Det.irrIffSpan (W.mat ρ₀)).2 hfull N fun g v hv => hN g trivial v hv
  have hnice := _root_.UpperTheory.V.Th.nice0four_alt ι x ρ₀ hapt hirr₀ (free hU.pr hn1 ι x _ m hρ haut hm hfl k hk hkk) hC hD4
  obtain ⟨X, hX⟩ := hAd l L Ω s V hV hζ c hc 4 (by omega) le_rfl r h0 B ι x ρ₀ hnice (par x m hm k hk hkk) _ R hP hR z hz hbk
  obtain ⟨Q, hQ⟩ := conjOf ρ₀ y ρ' X htan fun g => by rw [← hzy, hX, hR.ad]
  exact constOf B x' ρ₀ ρ' Q hD' hQ hinj hfl₀ hfl'
end
