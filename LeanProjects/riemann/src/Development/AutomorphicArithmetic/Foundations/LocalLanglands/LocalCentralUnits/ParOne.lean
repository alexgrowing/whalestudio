import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.WDBasic
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ClBasic
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.TwTame
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.TameArt
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ResBase
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.IsoUniq
import Development.WeilBound.CoreStatements.AutomorphicKernels.DepthZeroCuspidal.IsTateEpsUnramTwist
import Development.WeilBound.CoreStatements.AutomorphicKernels.DepthZeroCuspidal.TameLpOfCharIff
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRecLawsSuppUnitSurj
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CuspLawsOfLawsLit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsExtensionCharacterTwist

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GLp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Zero.LLC

section Fin

private theorem charpoly_one {R : Type} [CommRing R] (M : Matrix (Fin 1) (Fin 1) R) :
    M.charpoly = X - C (M 0 0) := by
  rw [Matrix.charpoly, Matrix.det_fin_one, Matrix.charmatrix_apply_eq]

private theorem smul_of_finrank_one {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (hV : Module.finrank ℂ V = 1) (f : V →ₗ[ℂ] V) (v : V) : f v = LinearMap.trace ℂ V f • v := by
  obtain ⟨b, hb, hall⟩ := finrank_eq_one_iff'.1 hV
  obtain ⟨c, hc⟩ := hall (f b)
  have hf : f = c • LinearMap.id := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨d, rfl⟩ := hall x
    simp [hc.symm, smul_smul, mul_comm]
  have ht : LinearMap.trace ℂ V f = c := by
    rw [hf, map_smul, LinearMap.trace_id, hV]; simp
  rw [ht, hf]; simp

end Fin

section Key

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem fixed_ne_bot_of_equiv {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (e : ρ.Equiv σ) {H : Subgroup G} {v : V}
    (hv : ∀ u ∈ H, ρ u v = v) (h0 : v ≠ 0) : fixed σ H ≠ ⊥ := by
  refine (Submodule.ne_bot_iff _).2 ⟨e.toIntertwiningMap v, GlobalTheory.Parabolic.mem_fixed.2 fun u hu => ?_, fun h1 => ?_⟩
  · rw [← e.toIntertwiningMap.isIntertwining, hv u hu]
  · have h2 : e.toLinearEquiv v = 0 := h1
    exact h0 (e.toLinearEquiv.injective (h2.trans (map_zero _).symm))

private theorem dz_one : DZ (IrrGL.ofChar (1 : kˣ →* ℂˣ) isSmoothChar_one) :=
  fixed_ne_bot_of_equiv (equivRep (IrrRep.det (k := k) (Fin 1) 1 isSmoothChar_one)) (v := (1 : ℂ))
    (fun u _ => by
      show (((1 : kˣ →* ℂˣ) (GeneralLinearGroup.det u) : ℂˣ) : ℂ) • (1 : ℂ) = 1
      simp) (one_ne_zero (α := ℂ))

variable {g : ℕ} [Fact g.Prime] {K : Type} [Field K] [Algebra (ZMod g) K]

private theorem character_one {θ : Kˣ →* ℂˣ} {τ : FDRep ℂ (Gn g 1)} (hN : Names g 1 θ τ) :
    Module.finrank ℂ τ = 1 := by
  have h1 := hN 1 (by rw [charpoly_one]; exact irreducible_X_sub_C _) 1 (by rw [charpoly_one]; simp)
  rw [FDRep.char_one] at h1
  simp at h1
  exact_mod_cast h1

private theorem val_of_inflates {i : ℚ_[g] ≃+* k} {θ : Kˣ →* ℂˣ} {τ : FDRep ℂ (Gn g 1)} (hN : Names g 1 θ τ)
    {σ : IrrRep (GL (Fin 1) k)} {χ : kˣ →* ℂˣ} {hχ : IsSmoothChar χ} (e : σ.ρ.Equiv (IrrRep.det (Fin 1) χ hχ).ρ)
    (hinf : GlobalTheory.SerSys.TameGen.Inflates (σ.ρ.comp (GeneralLinearGroup.map i.toRingHom)) τ)
    (u : ℤ_[g]ˣ) (z : Kˣ) (hz : algebraMap (ZMod g) K (PadicInt.toZMod (u : ℤ_[g])) = z) (x : kˣ)
    (hx : (x : k) = i ((u : ℤ_[g]) : ℚ_[g])) : χ x = θ z := by
  obtain ⟨φ, hφ0, hφ⟩ := hinf
  obtain ⟨v, hv⟩ : ∃ v, φ v ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hφ0 (LinearMap.ext hc)
  set c : GL (Fin 1) ℤ_[g] := GeneralLinearGroup.scalar (Fin 1) u with hc
  have hy0 : ((red g 1 c : Gn g 1) : Mt g 1) 0 0 = PadicInt.toZMod (u : ℤ_[g]) := by
    simp [red, hc, GeneralLinearGroup.scalar]
  have hd : GeneralLinearGroup.det (GeneralLinearGroup.map i.toRingHom (inc g 1 c)) = x := by
    ext
    rw [hx]
    simp [inc, hc, GeneralLinearGroup.scalar]
  have hσ : ∀ (t : GL (Fin 1) k) (y : σ.V), σ.ρ t y = (χ (GeneralLinearGroup.det t) : ℂ) • y := by
    intro t y
    apply e.toLinearEquiv.injective
    have h1 : e.toIntertwiningMap (σ.ρ t y) = (IrrRep.det (Fin 1) χ hχ).ρ t (e.toIntertwiningMap y) := by
      rw [← e.toIntertwiningMap.isIntertwining]
    refine h1.trans ?_
    rw [map_smul]
    rfl
  have hτ : τ.character (red g 1 c) = ((θ z : ℂˣ) : ℂ) := by
    have := hN (red g 1 c) (by rw [charpoly_one]; exact irreducible_X_sub_C _) z
      (by rw [charpoly_one, hy0]; simp [hz])
    simpa using this
  have h2 := hφ c v
  rw [smul_of_finrank_one (character_one hN) (τ.ρ (red g 1 c)) v, map_smul] at h2
  have h3 : LinearMap.trace ℂ τ (τ.ρ (red g 1 c)) = ((θ z : ℂˣ) : ℂ) := hτ
  rw [h3] at h2
  have h4 : (σ.ρ.comp (GeneralLinearGroup.map i.toRingHom)) (inc g 1 c) (φ v) = ((χ x : ℂˣ) : ℂ) • φ v := by
    rw [MonoidHom.comp_apply, hσ, hd]
  rw [h4] at h2
  exact (Units.ext (smul_left_injective ℂ hv h2)).symm

end Key

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

private theorem irr_lpOfChar (ξ : Weil h →* ℂˣ) (hξ : IsSmooth ξ) : IsIrrWD (WD.lpOfChar h ξ hξ) := by
  refine ⟨1, WDRep.ofChars h (ι := Fin 1) (fun _ => ξ) (fun _ => hξ), rfl, ?_⟩
  have h1 : (WDRep.ofChars h (ι := Fin 1) (fun _ => ξ) (fun _ => hξ)).ρ =
      GlobalTheory.FiniteGL.lineRep ((Units.coeHom ℂ).comp ξ) := by
    refine MonoidHom.ext fun σ => LinearMap.ext fun v => funext fun i => ?_
    simp [GlobalTheory.FiniteGL.lineRep_apply, diagEnd_apply]
  rw [h1]
  exact GlobalTheory.FiniteGL.lineRep_isIrreducible _

private theorem dim_lpOfChar (ξ : Weil h →* ℂˣ) (hξ : IsSmooth ξ) : (WD.lpOfChar h ξ hξ).lpDim = 1 := by
  simp [WD.lpOfChar]

private theorem dual_lpOfChar {ξ ξ' : Weil h →* ℂˣ} (hξ : IsSmooth ξ) (hξ' : IsSmooth ξ') (e : ∀ σ, ξ' σ = (ξ σ)⁻¹) :
    (WD.lpOfChar h ξ hξ).lpDual = WD.lpOfChar h ξ' hξ' := by
  rw [WD.lpOfChar, WD.lpDual_mk, WD.lpOfChar]
  refine WD.sound ⟨(Pi.basisFun ℂ (Fin 1)).dualBasis.equivFun, fun σ f => ?_, fun f => ?_⟩
  · funext i
    simp [Module.Basis.dualBasis_equivFun, diagEnd_apply, e]
    have h1 : (diagEnd fun _ : Fin 1 => ((ξ σ : ℂ))⁻¹) (Pi.single i 1) = ((ξ σ : ℂ))⁻¹ • (Pi.single i 1 : Fin 1 → ℂ) := by
      funext j
      simp [diagEnd_apply]
    rw [h1, map_smul, smul_eq_mul]
  · funext i
    simp

private theorem typeAt_ofChar {a : Weil h →* (w.adicCompletion E)ˣ} (ha : IsLocalArtin h a)
    (χ : (w.adicCompletion E)ˣ →* ℂˣ) (hχ : IsSmoothChar χ) :
    TypeAt (IrrGL.ofChar χ hχ) (WD.lpOfChar h (χ.comp a) (ha.smooth hχ)) := by
  intro g _ i hi n hn D R hR θ hθ τ hτ hN σ hcl hinf
  obtain rfl : n = 1 := congrArg Sigma.fst hcl
  obtain ⟨e⟩ : Nonempty (σ.ρ.Equiv (IrrRep.det (Fin 1) χ hχ).ρ) :=
    IrrRep.cl_eq_iff.1 (sigma_mk_injective (β := fun n => IrrCl (GL (Fin n) (w.adicCompletion E))) hcl)
  refine ⟨(WD.monodromyZero_ofWeilDeligneRepClass_iff _).2 rfl, fun t => ?_⟩
  obtain ⟨u, hu, hu'⟩ := resBase E Ω A w h a ha g i hi 1 one_pos D R hR t
  have hz : algebraMap (ZMod g) D.K (PadicInt.toZMod (u : ℤ_[g])) = (R t : D.Kˣ) := by
    rw [hu']; simp
  have key := val_of_inflates hN e hinf u (R t) hz (a (ineIncl h t)) hu
  rw [WD.inePol_of_mem_Ine _ t.2, WD.lpOfChar, WD.charPol_mk, WDRep.ofChars_ρ, charpoly_diagEnd]
  simp [key]

end UpperTheory.Zero.LLC

open UpperTheory.Zero.LLC in
theorem UpperTheory.Zero.LLC.parOne :
    UpperTheory.Zero.LLC.ParOne := by
  intro E Ω _ _ _ _ _ A w h a ha χ hχ
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  have hdz : DZ (IrrGL.ofChar χ hχ) ↔ TameChar χ := by
    have h1 := twTame _ (IrrGL.ofChar 1 isSmoothChar_one) χ hχ one_pos dz_one
    rwa [IrrGL.tw_ofChar, IrrGL.ofChar_inj.2 (one_mul χ)] at h1
  have heig : ∀ σ, ((WD.lpOfChar h (χ.comp a) (ha.smooth hχ)).eig σ).prod = (χ (a σ) : ℂ) := fun σ => by
    rw [eig_lpOfChar]; simp
  have hcc := GlobalTheory.LocLanglands.ExtTwist.hasCentralChar_ofChar χ hχ
  refine ⟨irr_lpOfChar _ _, dim_lpOfChar _ _, hcc, heig, hdz, fun ht => ⟨irr_lpOfChar _ _, dim_lpOfChar _ _, ?_, ?_, typeAt_ofChar ha χ hχ⟩,
    fun χ' hχ' h'' => ⟨IrrGL.tw_ofChar _ _ _ _, ?_⟩, fun h'' => ⟨?_, ?_⟩, fun χ' hχ' e => IrrGL.ofChar_inj.1 e⟩
  · exact (PositivityTheory.LocalParametersCuspidal.DZC.tame_lpOfChar_iff _ _).2 ((tameArt E Ω A w h a ha χ hχ).1 ht)
  · intro ω hω σ
    obtain ⟨ω₀, -, -, hu⟩ := (clBasic _ (IrrGL.ofChar χ hχ)).1
    rw [heig, hu ω hω, hu χ hcc]
  · exact PositivityTheory.LocalParametersCuspidal.DepthZeroGlueing.lpOfChar_lpTwist _ _ _ fun σ => rfl
  · exact GlobalTheory.LocLanglands.CuspModel.dualCl_ofChar _ _ _ _ rfl
  · exact dual_lpOfChar _ _ fun σ => rfl

end
