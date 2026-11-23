import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.LogarithmicNormBounds.LinkedUnitaryEndsOfInputs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PointTheoremBaseObject
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LevelRelationTwoX
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SymUse
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SdStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicPointGalois
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.EndPtOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ChainRankFourGood
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.IsSeed
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.COpenEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PrSeedPtOf

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Alg
open UpperTheory.V.W UpperTheory.V.Pr UpperTheory.V.J
open private UpperTheory.V.J.oe_big UpperTheory.V.J.oe_res from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.OpenEx
namespace UpperTheory.Gal.projectedFormsSystemPart
def OpenEx2EAlt : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : Coef l)
    [CharP (ResidueField c.O) l] (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N)
    (η : G ℚ Ω →* ℤˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ), LinkHyp c N e η σ B M → Even N →
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] (Φ : Fr.Frame l (ResidueField c.O)) (C₀ : ℕ)
    (k : GalLink η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B M L Φ), Φ.Ok C₀ → Φ.Big C₀ → SeedClause c η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ L →
    ∀ (A : Subalgebra c.O (PadicAlgCl l)) [Module.Finite c.O A],
    ∃ (c₁ : Coef l) (_ : Fr.IsCoef l c₁.O) (f : ResidueField c.O →+* ResidueField c₁.O) (R : CReal k c₁ f 3 (cycBar L Ω l)⁻¹)
      (Λ : LamObj R.r) (J : Ideal R.B₀.B) (φ : R.B₀.B →ₐ[c₁.O] R.S.B) (m : ℕ),
      (∀ x ∈ A, x ∈ c₁.O) ∧ Large L c₁ ∧ IsKa σ M ι 3 (cycBar L Ω l)⁻¹ ∧ R.B₀.ModularAlt ι J Λ ∧ Num R.B₀ Λ J ∧
      Nonempty (Λ.Λ ≃ₐ[c₁.O] MvPowerSeries (Fin m) c₁.O) ∧ R.T.IsPhi φ ∧ Function.Surjective φ ∧ AllGood R.S (J.map φ) ∧
      R.T.DimT J ∧ _root_.UpperTheory.Gal.projectedFormsSystemPart.EndPtAlt R ι φ
theorem UnitaryRankTwoFlagsAlt (hO : _root_.UpperTheory.Gal.projectedFormsSystemPart.OpenEx2EAlt) (hX : XiEx) (hT : XiTI) (hA : XiArith) (hTan : TanA) (hR : _root_.UpperTheory.Gal.projectedFormsSystemPart.Red2Alt) (hU : _root_.UpperTheory.V.J.UnramifiedEndsStatement) (hE : End)
    (hι : ∀ (l : ℕ) [Fact l.Prime], Nonempty (Qbar l ≃+* ℂ)) : UpperTheory.V.Z.J.LinkedUnlE := by
  intro Ω _ _ _ l _ c _ N _ e ψ η σ g₁ B M H hev L _ _ _ _ _ Φ C₀ k hok hbig hseed A _ _ _ ρ hρ hψ r hr hirr v hpc i j
  by_contra hno
  push Not at hno
  obtain ⟨ι⟩ := hι l
  obtain ⟨c₁, _, f, R, Λ, J, φ, m, hAc, hL, hka, hmod, hnum, hΛ, hφ, hsurj, hgood, hdim, hend⟩ :=
    hO Ω l ι c N e ψ η σ g₁ B M H hev L Φ C₀ k hok hbig hseed A
  obtain ⟨ξ, h1, h2⟩ := hX Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f R A hAc ρ hρ
  have hr' : ∀ s, (r s).val = (R.S.ρ.r (k.p0 s)).map fun a => (ξ a).1 := fun s => by
    rw [hr s]; ext a b; exact (h1 _ a b).symm
  have hi : IsIrr r := by
    have := hirr ⊤ (by simp)
    exact ⟨this.1, fun s w hw => Submodule.mem_top, fun U hU h => this.2.2 U hU fun s w hw => h s.1 w hw⟩
  have hψ' : ∀ v i, ∀ g ∈ Φ.Iv v, (ξ (R.S.ρ.ψ v i g).val).1 =
      (Chr.Psi l e (Chr.dirG ℚ Ω ψ) (k.j v g) ^ Fr.w 3 i).val.1 := fun v i g hg =>
    (h2 v i g).trans (by rw [hψ v i g hg]; rfl)
  obtain ⟨t1, t2, t3⟩ := hT Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f R ξ r hr' hi
  obtain ⟨⟨w, hw⟩, hip⟩ := hA Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f R hka φ hφ ξ r hr' hi hψ'
  obtain ⟨D, hD, D', hD', k1, k2, hli⟩ := hTan Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f R ξ r hr' hi hψ' v hpc i j
    fun g => (h2 v i g).trans ((hno g).trans (congrArg (· * _) (h2 v j g).symm))
  exact hE Ω l c η _ σ g₁ B M L Φ k c₁ f _ R φ hφ hsurj J ξ w
    (hU l L Ω R.s R.V c₁ 3 R.r R.B₀ Λ ι J m (by norm_num) hΛ hmod.dense hmod.end1 hnum) t1 hw hip
    (hR Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f _ R hL hka φ hφ hsurj J hgood hdim hmod.dense hend (ptA R ξ) t2 t3)
    D hD D' hD' k1 k2 hli
set_option maxHeartbeats 1600000 in
theorem openEx2E_alt :
    GlobalTheory.Published.GlobalArtinReciprocity → UpperTheory.V.W.LocCFTAll → _root_.UpperTheory.V.W.ModUAlt → _root_.UpperTheory.V.J.ModNAlt → UpperTheory.V.W.LevEx → UpperTheory.V.W.LamEx → UpperTheory.V.W.ProModularRingExists → _root_.UpperTheory.V.Z.Sym.UnitaryThreeAutomorphyDense → _root_.UpperTheory.V.Sd.Seed2Alt → UpperTheory.V.Sd.Twist → UpperTheory.V.Sd.AlgCyc → UpperTheory.V.Sd.AlgRes → _root_.UpperTheory.Gal.projectedFormsSystemPart.OpenEx2EAlt := by
  intro hA hLoc hMod hN hLev hLam hB0 hS3 hS2 hTw hCyc hRes Ω _ _ _ l _ ι c _ N _ e ψ η σ g₁ B M H hev L _ _ _ _ _ Φ C₀ k hok hbig hseed A _
  obtain ⟨K, _, _, _, N', w, χ', η', θ, j, hD, hne, hord, hη, hcong, hdisc⟩ := hseed
  have hv : Nonempty Φ.V := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := hbig.1
    simp [UpperTheory.V.Fr.Frame.d] at this
  obtain ⟨v⟩ := hv
  have hker : η.ker = galOf ℚ K Ω := by
    rw [← hD.η_ker]
    ext s
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, ← Units.val_eq_one, ← Units.val_eq_one, hη s]
    exact_mod_cast Iff.rfl
  haveI := hD.imag
  obtain ⟨κ, hκ⟩ := hTw K Ω hD.quad l hok.l_odd hdisc ι σ hD.cc
  obtain ⟨hk3, hk2⟩ := UpperTheory.V.Pr.kaOf hCyc hRes Ω l ι c N e ψ η σ g₁ B M H L Φ k
  obtain ⟨ka, hk2, hka⟩ := hk2 K hker κ hκ
  obtain ⟨c₂, hcc, hAc⟩ := UpperTheory.V.J.oe_big c A
  obtain ⟨c₁, hle₁, hL, hv3, hv2, -⟩ := UpperTheory.V.Pr.coefEx l c₂ L Ω _ _ hk3.alg.1 hk2.alg.1
  have hle : c.O ≤ c₁.O := hcc.trans hle₁
  obtain ⟨f, hf⟩ := UpperTheory.V.J.oe_res hle
  haveI hco := UpperTheory.V.Pr.coefIs l c₁
  obtain ⟨R₂⟩ := UpperTheory.V.Pr.cRealEx hA hLoc hLev hB0 Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f 2 ka C₀ (Or.inl rfl)
    hok hbig hle hf hk2 hv2
  obtain ⟨R₃⟩ := UpperTheory.V.Pr.cRealEx hA hLoc hLev hB0 Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f 3 _ C₀ (Or.inr rfl)
    hok hbig hle hf hk3 hv3
  obtain ⟨m₃, hm₃, -, r₃, -, s₃⟩ := hS3 K L Ω l ι σ N' w χ' η' θ j hD hne M H.3
    (by rw [mul_comm]; exact (Nat.mul_dvd_mul_left l hev.two_dvd).trans H.2)
    (UpperTheory.V.Z.Sym.Pl.linkUnr Ω l _ η _ σ g₁ B M L Φ k) (UpperTheory.V.Z.Sym.Pl.chiUnr Ω l c N e ψ χ' j hord hcong M H.2 L) 2
  obtain ⟨m₂, hm₂, -, r₂, -, -, -, s₂⟩ := hS2 K L Ω l ι σ N' w χ' η' θ j hD κ ka hκ hka 2
  obtain ⟨-, hμ⟩ := UpperTheory.V.Pr.degEq Ω l ι c N e ψ η σ g₁ B M H L Φ k v
  obtain ⟨Λ₂, hΛ₂⟩ := hLam l L Ω R₂.s R₂.V c₁ 2 R₂.r
  obtain ⟨Λ₃, hΛ₃⟩ := hLam l L Ω R₃.s R₃.V c₁ 3 R₃.r
  obtain ⟨J₂, hJ₂⟩ := hMod l L Ω R₂.s R₂.V R₂.hV hμ c₁ hL 2 (by norm_num) R₂.r R₂.B₀ Λ₂ ι
  obtain ⟨J₃, hJ₃, hnum⟩ := hN l L Ω R₃.s R₃.V R₃.hV hμ c₁ hL R₃.r R₃.v0 R₃.B₀ Λ₃ ι
  have h₂ := _root_.UpperTheory.V.J.mod_l_open_existence ι H v R₂ Λ₂ hΛ₂ J₂ hJ₂
    (_root_.UpperTheory.V.Pr.seedPtOf_alt hA Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f 2 ka R₂ hk2 χ' j hord hcong m₂ hm₂ _ (by
      convert s₂ using 2 with i i i <;> fin_cases i <;> simp [UpperTheory.V.Fr.w]) J₂ hJ₂.pt)
  have h₃ := _root_.UpperTheory.V.J.mod_l_open_existence ι H v R₃ Λ₃ hΛ₃ J₃ hJ₃
    (_root_.UpperTheory.V.Pr.seedPtOf_alt hA Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f 3 _ R₃ hk3 χ' j hord hcong m₃ hm₃ _ (by
      convert s₃ using 2 with i i i <;> fin_cases i <;> simp [UpperTheory.V.Fr.w]) J₃ hJ₃.pt)
  obtain ⟨φ, hφ, hsurj, hgood⟩ := UpperTheory.V.J.absGood l c₁.O _ R₂.T R₃.T J₂ J₃ h₂ h₃
  obtain ⟨R₀, hp⟩ := cRealAv hLev hB0 Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f 3 _ C₀ (Or.inr rfl)
    hok hbig hle hf hk3 hv3 R₃.s.p R₃.s.p_prime.ne_zero
  obtain ⟨Λ₀, hΛ₀⟩ := hLam l L Ω R₀.s R₀.V c₁ 3 R₀.r
  obtain ⟨J₀, hJ₀⟩ := hMod l L Ω R₀.s R₀.V R₀.hV hμ c₁ hL 3 (by norm_num) R₀.r R₀.B₀ Λ₀ ι
  have h₀ := _root_.UpperTheory.V.J.mod_l_open_existence ι H v (setS R₀ R₃.S) Λ₀ hΛ₀ J₀ hJ₀
    (_root_.UpperTheory.V.Pr.seedPtOf_alt hA Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f 3 _ (setS R₀ R₃.S) hk3 χ' j hord hcong m₃ hm₃ _ (by
      convert s₃ using 2 with i i i <;> fin_cases i <;> simp [UpperTheory.V.Fr.w]) J₀ hJ₀.pt)
  obtain ⟨φ₀, hφ₀, -, hgood₀⟩ := UpperTheory.V.J.absGood l c₁.O _ R₂.T (setS R₀ R₃.S).T J₂ J₀ h₂ h₀
  exact ⟨c₁, hco, f, R₃, Λ₃, J₃, φ, _, fun x hx => hle₁ (hAc x hx), hL, hk3, hJ₃, hnum, hΛ₃, hφ, hsurj, hgood, h₃.dim,
    _root_.UpperTheory.Gal.projectedFormsSystemPart.endPt_of_allGood_of_arithmeticPointClassicality R₃ R₀ hp hφ hgood hJ₃.end2 hφ₀ hgood₀ hJ₀.end2⟩
theorem linkedUnlE_alt (hG : GlobalTheory.Published.GlobalArtinReciprocity) (h1 : W.LocCFTAll) (h2 : _root_.UpperTheory.V.W.ModUAlt) (hN : _root_.UpperTheory.V.J.ModNAlt) (h3 : W.LevEx)
    (h4 : W.LamEx) (h5 : W.ProModularRingExists) (s3 : _root_.UpperTheory.V.Z.Sym.UnitaryThreeAutomorphyDense) (s2 : _root_.UpperTheory.V.Sd.Seed2Alt) (tw : Sd.Twist) (cy : Sd.AlgCyc) (re : Sd.AlgRes)
    (hT : TanA) (hC : _root_.UpperTheory.V.Th.DenseThresholdMainCase) : UpperTheory.V.Z.J.LinkedUnlE :=
  _root_.UpperTheory.Gal.projectedFormsSystemPart.UnitaryRankTwoFlagsAlt (_root_.UpperTheory.Gal.projectedFormsSystemPart.openEx2E_alt hG h1 h2 hN h3 h4 h5 s3 s2 tw cy re) xiEx xiTI (xiArith hG) hT (_root_.UpperTheory.Gal.projectedFormsSystemPart.red2_alt hG hC) _root_.UpperTheory.V.J.unramified_algebraic_weights endJ
    fun l _ => GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex l
end UpperTheory.Gal.projectedFormsSystemPart
end
end
