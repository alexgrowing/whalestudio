import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.ConjugacyTypeUnfolding
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CexpTwoPiINegInvNatSmulAddStar
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemFlagUnipotentRadicalIffSecondModel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RangeBesselAnisotropicEmbeddingEqSecondModelSubg
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GramEqOfInst
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StarEqHostConj
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsOrthDec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TranslateToSecondModelCuspFormMapValueAutomorphi
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodRightTranslationInvariant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitOfCocompact
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag

open Formalism.L2.SG Formalism.L2.SG.PoincareInHH Formalism.BasicNotions Formalism.L2.Theta GlobalTheory.MixPer GlobalTheory.MixModel MeasureTheory
  GlobalTheory.Core.Mi GlobalTheory.IndefiniteRowSideFullHecke.ConjugacyTypeUnfolding Formalism.L2.SG.InstExistsPf Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH Matrix

noncomputable section

namespace GlobalTheory.Core.Mi.PerCmp

theorem exists_castE {D : D7} {I : Formalism.MainNotions.S.AutInst} (h : I = instOf D) :
    ∃ ιE : I.E ≃+* D.host.E, ∀ y, ιE y ≍ y := by
  subst h; exact ⟨RingEquiv.refl _, fun _ => HEq.rfl⟩

theorem crdY_eq {D : D7} {I : Formalism.MainNotions.S.AutInst} (h : I = instOf D) (ιE : I.E ≃+* D.host.E)
    (hι : ∀ y, ιE y ≍ y) (hr : (D.sp.Y 0).rank = I.n) (x : Fin I.n → I.E) :
    crdY h x = fun k => ιE (x (Fin.cast hr k)) := by
  subst h; funext k; exact (eq_of_heq (hι _)).symm

structure Scaled {D : D7} (X : HidaSetting.HidaSetting D) (h : X.B.I = instOf D) (u : D.what₂.Word)
    {V₀ A L : HSp D} (d : HypDec (D.sp.Y 0) V₀ D.R.rS) (o : OrthDec V₀ A L)
    (ζ : Fin L.rank → D.host.E) (lam : D.host.E) : Prop where
  ne : lam ≠ 0
  e_eq : d.e = Matrix.of fun k (a : Fin D.R.rS) => lam ^ (D.R.rS - (a : ℕ)) * crdY h (X.eR a) k
  f_eq : d.e' = Matrix.of fun k (a : Fin D.R.rS) =>
    (star (lam ^ (D.R.rS - (a : ℕ))))⁻¹ * crdY h (X.fR a) k
  line : IsLineVec L ζ
  z_eq : d.i₀.mulVec (vecB o ζ) = crdY h (X.zR u)

variable {D : D7} {X : HidaSetting.HidaSetting D} {h : X.B.I = instOf D} {u : D.what₂.Word}
  {V₀ A L : HSp D} {d : HypDec (D.sp.Y 0) V₀ D.R.rS} {o : OrthDec V₀ A L}
  {ζ : Fin L.rank → D.host.E} {lam : D.host.E}

theorem hyp_linIndep {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) :
    LinearIndependent D.host.E d.e.transpose := by
  have h1 : Function.Injective d.e.mulVec := by
    intro x y hxy
    have := congrArg (fun v => (d.e'.conjTranspose * HSpace.gram S).mulVec v) hxy
    simpa [Matrix.mulVec_mulVec, d.e'e] using this
  exact Matrix.mulVec_injective_iff.mp h1

theorem hyp_e_i₀ {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) :
    d.e.conjTranspose * HSpace.gram S * d.i₀ = 0 := by
  have := congrArg Matrix.conjTranspose d.i₀e
  simpa [Matrix.conjTranspose_mul, gram_conjTranspose, Matrix.mul_assoc] using this

theorem Scaled.tieψ (hS : Scaled X h u d o ζ lam) {ψ : AddChar (AF ↥D.host.F) ℂ}
    (hψ : IsStdChar D ψ (-1)) {θ : D.host.E} (hθ : θ * lam⁻¹ = thetaS D) (n : GA D (D.sp.Y 0)) :
    star (psiBes ψ d θ (vecB o ζ) n) =
      X.psiInfU u ((RowsJoinPinned.iotaX X h) n).1 * X.psiFinU u ((RowsJoinPinned.iotaX X h) n).2 := by
  obtain ⟨ιE, hι⟩ := exists_castE h
  have hr := rank_eq X h
  have hA := GlobalTheory.Core.TieSign.simpleSum_eq D d (fun a => crdY h (X.eR a)) (fun a => crdY h (X.fR a))
    (crdY h (X.zR u)) (vecB o ζ) 1 lam one_ne_zero hS.ne (by simp only [one_mul]; exact hS.e_eq)
    (by simp only [one_mul]; exact hS.f_eq) (by rw [one_smul]; exact hS.z_eq) n
  have hc := GlobalTheory.Core.TieSign.core D ψ hψ X.B.I h ιE hι hr X.psiEf X.psiEf_add X.psiEf_int
    X.psiEf_rat X.B.g (Pf.modulus_g_ne_zero X) X.eR X.fR (X.zR u) n
  have e1 : (fun a => crdY h (X.eR a)) = fun a k => ιE (X.eR a (Fin.cast hr k)) :=
    funext fun a => crdY_eq h ιE hι hr _
  have e2 : ∀ a, crdY h (X.fR a) = fun k => ιE (X.fR a (Fin.cast hr k)) :=
    fun a => crdY_eq h ιE hι hr _
  rw [e1, crdY_eq h ιE hι hr (X.zR u), Finset.sum_congr rfl fun a _ => by rw [e2 a]] at hA
  have hg : θ * lam⁻¹ = ((X.B.g : ℕ) : D.host.E)⁻¹ := by
    rw [hθ, thetaS, X.g_eq, one_div]
  rw [psiBes, hA, ← mul_assoc, ← map_mul, hg]
  exact hc

structure Match {ψ : AddChar (AF ↥D.host.F) ℂ} (B : SBes X h u ψ A)
    (hF : IsFrame X h u d o ζ) (ψ₀ : AddChar (AF ↥D.host.F) ℂ) (ν : Measure (flagN d))
    (𝓝 : Set (flagN d)) : Prop where
  emb : embA B.d B.o = embA d o
  per : ∀ φ f, B.lev.per ψ φ f = besPer ψ₀ (thetaS D) d o ζ B.vA.μ B.vA.𝓕 ν 𝓝 φ f

def scaleCols {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (c : Fin ρ → D.host.E)
    (hc : ∀ a, c a ≠ 0) : HypDec S S₀ ρ where
  e := d.e * Matrix.diagonal c
  e' := d.e' * Matrix.diagonal fun a => (star (c a))⁻¹
  i₀ := d.i₀
  ee := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc _ _ (HSpace.gram S), Matrix.mul_assoc,
      ← Matrix.mul_assoc _ d.e, d.ee, Matrix.zero_mul, Matrix.mul_zero]
  e'e' := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc _ _ (HSpace.gram S), Matrix.mul_assoc,
      ← Matrix.mul_assoc _ d.e', d.e'e', Matrix.zero_mul, Matrix.mul_zero]
  e'e := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc _ _ (HSpace.gram S), Matrix.mul_assoc,
      ← Matrix.mul_assoc _ d.e, d.e'e, Matrix.one_mul, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    simp only [Pi.star_apply, star_inv₀, star_star]
    exact inv_mul_cancel₀ (hc a)
  iso := d.iso
  i₀e := by rw [← Matrix.mul_assoc, d.i₀e, Matrix.zero_mul]
  i₀e' := by rw [← Matrix.mul_assoc, d.i₀e', Matrix.zero_mul]
  rank_add := d.rank_add

def IdentLev {ψ : AddChar (AF ↥D.host.F) ℂ} (B : SBes X h u ψ A) (Y : Full.Full X) (c : ℂ) : Prop :=
  ∀ (T : PoincareSetting.Cu X u Y.hK) (f : X.B.I.GA → ℂ) (φ : RowDict.L2X X), RowFun X f →
    (φ : X.B.I.GA → ℂ) =ᵐ[RowDict.muX X] f →
      inner ℂ (star φ) (PoincareSetting.PuFun X u Y.hK (Y.Dt u) T) =
        c * ∫ y, B.lev.per ψ (B.colForm T (X.Wu u y))
          (fun g => f (RowsJoinPinned.iotaX X h g * (y, X.xu u))) ∂X.nuQ u

def IdentFrame (hF : IsFrame X h u d o ζ) (hK : X.LevelSubgroupCharacter) (ψ : AddChar (AF ↥D.host.F) ℂ)
    (μ : Measure (GA D A)) (𝓕 : Set (GA D A)) (ν : Measure (flagN d)) (𝓝 : Set (flagN d))
    (Dt : Set X.B.I.GA) (c : ℂ) : Prop :=
  ∀ (T : PoincareSetting.Cu X u hK) (f : X.B.I.GA → ℂ), IsConjType X f →
    ∀ φ : X.B.I.L2 X.B.μf X.B.fund,
      ((φ : X.B.I.GA → ℂ) =ᵐ[(X.B.I.muA X.B.μf).restrict X.B.fund] fun x => star (f x)) →
        inner ℂ φ (PoincareSetting.PuFun X u hK Dt T) =
          c * ∫ y, perAt hF hK ψ μ 𝓕 ν 𝓝 T f y ∂X.nuQ u

def FrameLaw (X : HidaSetting.HidaSetting D) (h : X.B.I = instOf D) (u : D.what₂.Word)
    (ψ : AddChar (AF ↥D.host.F) ℂ) (A : HSp D) (hK : X.LevelSubgroupCharacter) (Dt : Set X.B.I.GA)
    (C : Set ℂ) : Prop :=
  ∀ (V₀ L : HSp D) (d : HypDec (D.sp.Y 0) V₀ D.R.rS) (o : OrthDec V₀ A L)
    (ζ : Fin L.rank → D.host.E) (hF : IsFrame X h u d o ζ) (μ : Measure (GA D A))
    (ν : Measure (flagN d)), μ.IsHaarMeasure → ν.IsHaarMeasure →
    ∀ (𝓕 : Set (GA D A)) (𝓝 : Set (flagN d)), IsFundamentalDomain (GQ A) 𝓕 μ →
      IsFundamentalDomain (NFlagQ (D.sp.Y 0) d.e) 𝓝 ν →
        ∃ c ∈ C, IdentFrame hF hK ψ μ 𝓕 ν 𝓝 Dt c

def posReals : Set ℂ := {c | ∃ r : ℝ, 0 < r ∧ c = r}

theorem besPer_domN {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L)
    (ζ : Fin L.rank → D.host.E) {ψ : AddChar (AF ↥D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ)
    (θ : D.host.E) (μ 𝓕) (ν : Measure (flagN d)) (hν : ν.IsHaarMeasure) {𝓝 𝓝' : Set (flagN d)}
    (h𝓝 : IsFundamentalDomain (NFlagQ S d.e) 𝓝 ν) (h𝓝' : IsFundamentalDomain (NFlagQ S d.e) 𝓝' ν)
    (φ : GA D A → ℂ) (f : GA D S → ℂ) (hf : ∀ γ ∈ GQ S, ∀ g, f (γ * g) = f g) :
    besPer ψ θ d o ζ μ 𝓕 ν 𝓝 φ f = besPer ψ θ d o ζ μ 𝓕 ν 𝓝' φ f := by
  obtain ⟨j1, j2, j3, j4⟩ := GlobalTheory.Mem.TrueRecord.top_NFlag S (isIsoSub_e d)
  haveI : Countable (NFlagQ S d.e) := by
    have hinj : Function.Injective
        (fun x : NFlagQ S d.e => (⟨x.1.1, x.2⟩ : GQ S)) := fun x y hxy =>
      Subtype.ext (Subtype.ext (congrArg (fun z : GQ S => z.1) hxy))
    exact hinj.countable
  unfold besPer
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  refine h𝓝.setIntegral_eq h𝓝' fun γ n => ?_
  have hγ : ((γ : flagN d) : GA D S) ∈ GQ S := Subgroup.mem_subgroupOf.1 γ.2
  change besFun ψ θ d o ζ φ f a ((γ : flagN d) * n) = _
  simp only [besFun, Subgroup.coe_mul]
  rw [psiBes_mul d ψ θ _ γ.1.2 n.2, GlobalTheory.CharLaws.psiBes_rat ψ d hψ.2.2.1 θ _ hγ, one_mul,
    mul_assoc ((γ : flagN d) : GA D S), hf _ hγ]

theorem besPer_domA {ρ : ℕ} (B : GlobalTheory.Unf.BesLev D ρ) {ψ : AddChar (AF ↥D.host.F) ℂ}
    (hψ : IsCharAF D.host.F ψ) {𝓕 : Set (GA D B.A)} (h𝓕 : IsFundamentalDomain (GQ B.A) 𝓕 B.vA.μ)
    (φ : GA D B.A → ℂ) (f : GA D B.V → ℂ) (hφ : ∀ γ ∈ GQ B.A, ∀ g, φ (γ * g) = φ g)
    (hf : ∀ γ ∈ GQ B.V, ∀ g, f (γ * g) = f g) :
    besPer ψ 1 B.d B.o B.ζ B.vA.μ 𝓕 B.vN.ν B.vN.𝓝 φ f = B.per ψ φ f := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B.A
  haveI := B.vA.haar
  exact h𝓕.setIntegral_eq B.vA.fund fun γ x => Shift.inner_left B ψ hψ φ f hφ hf γ.2 x

def withDom {ψ : AddChar (AF ↥D.host.F) ℂ} (B : SBes X h u ψ A) (𝓕 : Set (GA D A))
    (h𝓕 : IsFundamentalDomain (GQ A) 𝓕 B.vA.μ) (𝓝 : Set (flagN B.d))
    (h𝓝 : GlobalTheory.Per.IsUnitN _ B.d.e B.vN.ν 𝓝) : SBes X h u ψ A :=
  { B with vA := ⟨B.vA.μ, 𝓕, B.vA.haar, h𝓕⟩, vN := ⟨B.vN.ν, 𝓝, h𝓝⟩ }

def ErrorExponentStatement (X : HidaSetting.HidaSetting D) (h : X.B.I = instOf D) (hK : X.LevelSubgroupCharacter)
    (ψ : AddChar (AF ↥D.host.F) ℂ) (u : D.what₂.Word) (A : HSp D) : Prop :=
  ∀ (V₀ L : HSp D) (d : HypDec (D.sp.Y 0) V₀ D.R.rS) (o : OrthDec V₀ A L)
    (ζ : Fin L.rank → D.host.E) (hF : IsFrame X h u d o ζ) (μ : Measure (GA D A))
    (ν : Measure (flagN d)), μ.IsHaarMeasure → ν.IsHaarMeasure →
    ∃ c : ℝ, 0 < c ∧ ∀ (𝓕 : Set (GA D A)) (𝓝 : Set (flagN d)), IsFundamentalDomain (GQ A) 𝓕 μ →
      IsFundamentalDomain (NFlagQ (D.sp.Y 0) d.e) 𝓝 ν →
      ∀ Dt : Set X.B.I.GA, PoincareSetting.IsReps X u Dt →
        ∀ (T : PoincareSetting.Cu X u hK) (f : X.B.I.GA → ℂ), IsConjType X f →
          Unfolds hF hK ψ μ 𝓕 ν 𝓝 T f Dt c

def Conv (X : HidaSetting.HidaSetting D) (h : X.B.I = instOf D) (hK : X.LevelSubgroupCharacter)
    (ψ : AddChar (AF ↥D.host.F) ℂ) (u : D.what₂.Word) (A : HSp D) : Prop :=
  ∀ (V₀ L : HSp D) (d : HypDec (D.sp.Y 0) V₀ D.R.rS) (o : OrthDec V₀ A L)
    (ζ : Fin L.rank → D.host.E) (hF : IsFrame X h u d o ζ) (μ : Measure (GA D A))
    (ν : Measure (flagN d)), μ.IsHaarMeasure → ν.IsHaarMeasure →
    ∀ (𝓕 : Set (GA D A)) (𝓝 : Set (flagN d)), IsFundamentalDomain (GQ A) 𝓕 μ →
      IsFundamentalDomain (NFlagQ (D.sp.Y 0) d.e) 𝓝 ν →
        ∀ (T : PoincareSetting.Cu X u hK) (f : X.B.I.GA → ℂ), IsConjType X f →
          (∀ y, AbsConv μ 𝓕 ν 𝓝 (perFun hF hK ψ T f y)) ∧
            Integrable (perAt hF hK ψ μ 𝓕 ν 𝓝 T f) (X.nuQ u)

end GlobalTheory.Core.Mi.PerCmp
