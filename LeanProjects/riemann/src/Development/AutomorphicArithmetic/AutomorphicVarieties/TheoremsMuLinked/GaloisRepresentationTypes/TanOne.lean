import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.WeightInfinitesimalCharacters.FreeFlagU
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.NiceFour
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.IsAlgClosureField
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.LamIso
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.RegOfTan
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.Factor
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.LiftRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.RelKill
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.RelForm
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.CocRel
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.AeComm
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.CocExt
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.PsiInj
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.FlagDual
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.BkAbEmb
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.AwAvg
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.LocLOpen
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.CocycleVanishesOnInertiaOfPointPseudodeformation
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.ConjOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.ConstOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidueFlagPoints.CycIne

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

private theorem arith (hP : Af.HypothesesH) (x : B.Pt) (m : W.Vl l L → Fin n → ℤ) (hm : ∀ v i j, i < j → m v j + 2 ≤ m v i) (k : ℕ) (hk : 0 < k)
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

private theorem free (hP : Af.HypothesesH) (hn : 1 ≤ n) (ι : PadicAlgCl l ≃+* ℂ) (x : B.Pt) (ρ : G L Ω →* GL (Fin n) (PadicAlgCl l))
    (m : W.Vl l L → Fin n → ℤ) (hρ : Continuous ρ) (haut : Af.IsAutCsd ι ρ) (hm : ∀ v i j, i < j → m v j + 2 ≤ m v i)
    (hfl : ∀ v : W.Vl l L, W.HasFlag (ρ.comp (Dec (F := L) (s.A v)).subtype) (x.psi v)) (k : ℕ) (hk : 0 < k)
    (hw : ∀ (v : W.Vl l L) i (g : Dec (F := L) (s.A v)), (g : G L Ω) ∈ Ine (F := L) (s.A v) →
      (x.psi v i g * cycBar L Ω l g ^ (-m v i)) ^ k = 1) : Free V.frame fun v => x.psi v := fun v : W.Vl l L => by
  obtain ⟨g, hg, hf⟩ := Z.J.freeFlagU hP L Ω l s.odd ι n hn ρ hρ haut (s.A v) (over_l v) (x.psi v) (m v) k (hfl v)
    (fun i j h => by have := hm v i j h; omega) hk (hw v) (noRatio x m hm k hk hw v)
  refine ⟨g, ?_, hf⟩
  have e : V.ε (toGS Ω V.S' (W.resP L Ω g)) = cycZ (W.Lp L) Ω l (W.resP L Ω g) := DFunLike.congr_fun V.hε _
  exact e.trans hg

end
