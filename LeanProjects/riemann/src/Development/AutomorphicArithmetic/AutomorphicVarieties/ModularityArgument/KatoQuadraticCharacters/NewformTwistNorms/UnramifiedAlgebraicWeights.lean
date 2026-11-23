import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.CuspSemisimpleReal
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.GlobFixed
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LocCompR
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HasSatOfFixed
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.KLocal
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Places
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Decomp
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.NormSpan
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CharOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.CompactBoxLattices.CentChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.NewformTwistNorms.NewVec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.NewformTwistNorms.MultisetEqOfProdEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.NewformTwistNorms.MemKLevOneOfMemK1G
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Deadel

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.NewLevel

open UpperTheory.V.Af.Nf CongruenceSubgroup GlobalTheory.CuspRep Neutral.B1 Formalism.L2.Host

private theorem level_zero_eq_maximal_compact (w : HeightOneSpectrum (𝓞 ℚ)) : UpperTheory.V.Sd.K1 w 0 = GlobalTheory.LFun.KGL w 2 := by
  ext g
  refine ⟨fun ⟨k, _, e⟩ => ⟨k, e⟩, fun ⟨k, e⟩ => ⟨k, ?_, e⟩⟩
  haveI : Subsingleton (w.adicCompletionIntegers ℚ ⧸ IsLocalRing.maximalIdeal (w.adicCompletionIntegers ℚ) ^ 0) :=
    Ideal.Quotient.subsingleton_iff.2 (by simp)
  exact Subsingleton.elim _ _

private theorem locGL_comm' {v w : HeightOneSpectrum (𝓞 ℚ)} (h : v ≠ w) (g : GL (Fin 2) (v.adicCompletion ℚ))
    (k : GL (Fin 2) (w.adicCompletion ℚ)) : locGL ℚ 2 v g * locGL ℚ 2 w k = locGL ℚ 2 w k * locGL ℚ 2 v g := by
  refine UpperTheory.V.Af.GlobalFixedVectors.gl_ext fun x => ?_
  rw [map_mul, map_mul]
  by_cases hx : x = v
  · subst hx; rw [pLoc_locGL_of_ne h, mul_one, one_mul]
  · rw [pLoc_locGL_of_ne hx, mul_one, one_mul]

private theorem normV_surj' {p : ℕ} (hp : p.Prime) : ∃ w : HeightOneSpectrum (𝓞 ℚ), normV w = p := by
  have h0 : Prime ((p : ℕ) : 𝓞 ℚ) := by
    have h : Prime ((p : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp hp
    have e : ((p : ℕ) : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm ((p : ℕ) : ℤ) := by simp
    rw [e]
    exact (MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm.toMulEquiv).mpr h
  let w : HeightOneSpectrum (𝓞 ℚ) := ⟨Ideal.span {((p : ℕ) : 𝓞 ℚ)}, (Ideal.span_singleton_prime h0.ne_zero).mpr h0,
    by rw [Ne, Ideal.span_singleton_eq_bot]; exact h0.ne_zero⟩
  refine ⟨w, (places w).2.2.1.symm.trans ?_⟩
  change Ideal.absNorm (Ideal.span {((p : ℕ) : 𝓞 ℚ)}) = p
  rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank]
  simp

private noncomputable abbrev Eo (v : InfinitePlace ℚ) (i j : Fin 2) : Module.End ℂ (TR.Sm ℚ 2) := TR.Eop v i j

private noncomputable def LowS (k : ℕ) : Submodule ℂ (TR.Sm ℚ 2) :=
  (⨅ v : InfinitePlace ℚ, LinearMap.ker (Eo v 0 1 - Eo v 1 0 - (Complex.I * (k : ℂ)) • (1 : Module.End ℂ (TR.Sm ℚ 2)))) ⊓
  (⨅ v : InfinitePlace ℚ, LinearMap.ker (Eo v 0 0 - Eo v 1 1 - Complex.I • (Eo v 0 1 + Eo v 1 0))) ⊓
  (⨅ v : InfinitePlace ℚ, LinearMap.ker (Eo v 0 0 + Eo v 1 1))

private theorem mem_LowS {k : ℕ} {φ : TR.Sm ℚ 2} : φ ∈ LowS k ↔ ((∀ v, TR.Eop v 0 1 φ - TR.Eop v 1 0 φ = (Complex.I * (k : ℂ)) • φ) ∧
      (∀ v, TR.Eop v 0 0 φ - TR.Eop v 1 1 φ = Complex.I • (TR.Eop v 0 1 φ + TR.Eop v 1 0 φ)) ∧
      (∀ v, TR.Eop v 0 0 φ + TR.Eop v 1 1 φ = 0)) := by
  simp only [LowS, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.add_apply, Module.End.one_apply, sub_eq_zero, and_assoc]

private theorem lowS_fin {k : ℕ} {φ : TR.Sm ℚ 2} (h : φ ∈ LowS k) (u : GL (Fin 2) (Af ℚ)) : TR.finRep ℚ 2 u φ ∈ LowS k := by
  obtain ⟨h1, h2, h3⟩ := mem_LowS.1 h
  have e : ∀ v i j, TR.Eop v i j (TR.finRep ℚ 2 u φ) = TR.finRep ℚ 2 u (TR.Eop v i j φ) := fun v i j =>
    LinearMap.congr_fun (TR.lie_rt_fin _ u) φ
  refine mem_LowS.2 ⟨fun v => ?_, fun v => ?_, fun v => ?_⟩
  · rw [e, e, ← map_sub, h1, map_smul]
  · rw [e, e, e, e, ← map_sub, h2, map_smul, map_add]
  · rw [e, e, ← map_add, h3, map_zero]

theorem newLevel : Af.Hypotheses₂ → Published.CuspSemisimpleReal → ∀ (k : ℕ), 2 ≤ k → ∀ (g : Newform k) (j : ℤ) (π : TR.CuspSub ℚ 2),
    (∀ᶠ w : Pl in Filter.cofinite, ∃ Bs, π.HasSat w Bs ∧
      ((algSat 2 (normV w) Bs).map fun b => Polynomial.X - Polynomial.C ((normV w : ℂ) ^ j * b)).prod = g.heckePoly (normV w)) →
    ∀ (w : Pl) (Bs : Multiset ℂˣ), π.HasSat w Bs → ¬ normV w ∣ g.M := by
  intro P hS k hk g j π hπ w Bs hw hd
  have hM : 1 ≤ g.M := g.pos
  have hk1 : 1 ≤ k := by omega
  obtain ⟨π₀, ψ, hψ, hψ0, hlev, hlow, hsat⟩ := UpperTheory.V.Z.Kato.NewVec.newVec hS P.admR k hk g
  obtain ⟨B, hB⟩ := GlobalTheory.NewLevel.spherical_of_normTwist P.smoR k hk g j π π₀ hπ hsat w Bs hw
  let L : Submodule ℂ (TR.Sm ℚ 2) :=
    LowS k ⊓ ⨅ q, ⨅ (_ : q ≠ w), Hi.fixd (UpperTheory.V.Sd.locSm ℚ q) (UpperTheory.V.Sd.K1 q (lev g.M q))
  let U : Submodule ℂ π₀.V := L.comap π₀.V.subtype
  have hU : ∀ h, ∀ x ∈ U, π₀.locRep w h x ∈ U := by
    intro h x hx
    simp only [U, L, Submodule.mem_comap, Submodule.mem_inf, Submodule.mem_iInf, Submodule.subtype_apply] at hx ⊢
    refine ⟨lowS_fin hx.1 _, fun q hq u hu => ?_⟩
    have h1 : TR.finRep ℚ 2 (locGL ℚ 2 q u) x.1 = x.1 := hx.2 q hq u hu
    change TR.finRep ℚ 2 (locGL ℚ 2 q u) (TR.finRep ℚ 2 (locGL ℚ 2 w h) x.1) = TR.finRep ℚ 2 (locGL ℚ 2 w h) x.1
    rw [← Module.End.mul_apply, ← map_mul, locGL_comm' hq, map_mul, Module.End.mul_apply, h1]
  have hU0 : U ≠ ⊥ := by
    intro h
    have hm : (⟨ψ, hψ⟩ : π₀.V) ∈ U := by
      simp only [U, L, Submodule.mem_comap, Submodule.mem_inf, Submodule.mem_iInf, Submodule.subtype_apply]
      exact ⟨mem_LowS.2 hlow, fun q _ => hlev q⟩
    rw [h, Submodule.mem_bot] at hm
    exact hψ0 (congrArg Subtype.val hm)
  obtain ⟨σ, hσ⟩ := (locCompR P ℚ 2 π₀ w).1
  have hiso := (locCompR P ℚ 2 π₀ w).2 σ hσ
  have hσf : HasFixed σ.ρ (GlobalTheory.LFun.KGL w 2) := by
    refine hiso.hasFixed (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w 2).2 ?_
    obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 hB.1
    exact ⟨y, hy0, fun u hu => GlobalTheory.LGrp.mem_fixed.1 hy u hu⟩
  obtain ⟨x, hxU, hx0, hxf⟩ := UpperTheory.V.Af.GlobalFixedVectors.sub_fixed σ.ρ σ.irred (π₀.locRep w) hiso.2 U hU hU0 _ hσf
  simp only [U, L, Submodule.mem_comap, Submodule.mem_inf, Submodule.mem_iInf, Submodule.subtype_apply] at hxU
  obtain ⟨hxl, hxq⟩ := hxU
  obtain ⟨hwt, hlo, hone⟩ := mem_LowS.1 hxl
  have hx0' : (x : TR.Sm ℚ 2) ≠ 0 := fun e => hx0 (Subtype.ext e)
  have hp := (places w).1
  have hN : 1 ≤ g.M / normV w := Nat.div_pos (Nat.le_of_dvd hM hd) hp.pos
  have hNM : g.M / normV w ∣ g.M := Nat.div_dvd_of_dvd hd
  have hNne : g.M / normV w ≠ g.M := (Nat.div_lt_self hM hp.one_lt).ne
  have hcusp := π₀.cusp x.1 x.2
  have hfix : ∀ u ∈ K1G (g.M / normV w), TR.finRep ℚ 2 u x.1 = x.1 :=
    GlobalTheory.NewLevelInv.inv_K1G g.M w hM hd x.1 hcusp.1.level (fun q hq => hxq q hq) (by
      rw [level_zero_eq_maximal_compact]; exact fun u hu => congrArg Subtype.val (hxf u hu))
  obtain ⟨ω, hω, -⟩ := UpperTheory.V.Sd.Wc.centChar P ℚ π₀
  have hc : ∀ (z : Ideles ℚ) (g' : GA ℚ 2),
      x.1.1 (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g') = ((ω.1 z : ℂˣ) : ℂ) * x.1.1 g' :=
    fun z g' => hω z x.1 x.2 g'
  obtain ⟨χ, hχ⟩ := UpperTheory.V.Br.charOf _ hN ω x.1 hx0' hone hfix hc
  obtain ⟨f, hf, hL⟩ := UpperTheory.V.Br.deadel k _ hN χ ω hχ x.1 hcusp ⟨hwt, hlo, hone⟩ hfix hc
  haveI : NeZero (g.M / normV w) := ⟨by omega⟩
  have hf0 : f ≠ 0 := by
    rintro rfl
    refine hx0' (Subtype.ext (funext fun g' => ?_))
    obtain ⟨γ, h, u, hu, rfl⟩ := decomp _ hN g'
    rw [hL γ h u hu]
    simp [nsl]
  have hhol : UpperTheory.V.Sd.IsHol k (lev (g.M / normV w)) ω x.1 :=
    ⟨hcusp.1, fun q u hu => hfix _ (kLocal _ hN q u hu), hc, hwt, hlo⟩
  refine hf0 (g.new _ hNM hNne f χ hf ?_)
  refine Filter.eventually_cofinite.2 ((Set.finite_le_nat g.M).subset fun q hq => ?_)
  simp only [Set.mem_setOf_eq, _root_.not_imp] at hq
  obtain ⟨hqp, hqe⟩ := hq
  by_contra hqM
  have hqd : ¬ q ∣ g.M := fun h => hqM (Nat.le_of_dvd hM h)
  obtain ⟨wq, rfl⟩ := normV_surj' hqp
  obtain ⟨α, β, hq2, hsum, -⟩ := hsat wq hqd
  have hqN : ¬ normV wq ∣ g.M / normV w := fun h => hqd (h.trans hNM)
  have hv : GlobalTheory.LFun.IsSatVecGL wq (UpperTheory.V.Sd.locSm ℚ wq) x.1 {α, β} :=
    (hq2.2 x (GlobalTheory.LGrp.mem_fixed.2 fun u hu => Subtype.ext (hfix _ (kLocal _ hN wq u (by
      rwa [(places wq).2.2.2 _ hN hqN, level_zero_eq_maximal_compact])))) hx0).map π₀.V.subtype (fun _ _ => rfl) hx0'
  obtain ⟨h1, -⟩ := UpperTheory.V.Br.eigOf k _ hk1 hN χ ω hχ f x.1 hL hhol wq α β hqN hv
  rw [hsum] at h1
  exact hqe h1

end GlobalTheory.NewLevel

end
