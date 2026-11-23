import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.KillExempt
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.NormCharSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.QuadraticInductionGL2Alt
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd

noncomputable section

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open GlobalTheory.CuspRep UpperTheory.V.Published
open scoped ComplexConjugate Classical

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E

section Defs

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

abbrev FA (K : Type) [Field K] [NumberField K] (n : ℕ) : Type := AdelicGLn.FiniteAdelicGL K n

abbrev fin1 (h : FA K n) : G1 K n := MultiplicityOne.finProj K n h

abbrev arc1 (k : archCompact K n) : G1 K n := archP K n (k : archGroup K n)

structure IsHaarK (κ : Measure (archCompact K n)) : Prop where
  prob : IsProbabilityMeasure κ
  left : ∀ k, MeasurePreserving (k * ·) κ κ
  right : ∀ k, MeasurePreserving (· * k) κ κ

structure IdemA (κ : Measure (archCompact K n)) (e : archCompact K n → ℂ) : Prop where
  haar : IsHaarK κ
  cont : Continuous e
  star : ∀ k, e k⁻¹ = conj (e k)
  idem : ∀ k, ∫ h, e h * e (h⁻¹ * k) ∂κ = e k

def FixA (κ : Measure (archCompact K n)) (e : archCompact K n → ℂ) (φ : G1 K n → ℂ) : Prop :=
  ∀ g, ∫ k, e k * φ (g * arc1 k) ∂κ = φ g

def FixF (U : Subgroup (FA K n)) (φ : G1 K n → ℂ) : Prop := ∀ u ∈ U, ∀ g, φ (g * fin1 u) = φ g

def BiA (κ : Measure (archCompact K n)) (e : archCompact K n → ℂ) (β : TI K n) : Prop :=
  ∀ g : archGroup K n, ∫ k, e k * β ((k : archGroup K n)⁻¹ * g) ∂κ = β g ∧ ∫ k, β (g * (k : archGroup K n)⁻¹) * e k ∂κ = β g

def pOp (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (κ : Measure (archCompact K n)) (e : archCompact K n → ℂ) (v : LL μ) : LL μ :=
  ∫ k, e k • rightRegularRep (Gam K n) μ (arc1 k) v ∂κ

def RankInf (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (τ : Submodule ℂ (LL μ)) (κ : Measure (archCompact K n))
    (e : archCompact K n → ℂ) : Prop :=
  IdemA κ e ∧ (∃ v ∈ τ, v ≠ 0 ∧ pOp μ κ e v = v) ∧ ∀ g : archGroup K n, ∃ c : ℂ, ∀ v ∈ τ, pOp μ κ e v = v →
    pOp μ κ e (rightRegularRep (Gam K n) μ (archP K n g) v) = c • v

def hop (U : Subgroup (FA K n)) (h : FA K n) (φ : G1 K n → ℂ) (x : G1 K n) : ℂ :=
  ∑ᶠ c ∈ {c : FA K n ⧸ U | ∃ u ∈ U, c = QuotientGroup.mk (u * h)}, φ (x * fin1 c.out)

def Lev (U : ∀ w : Pl K, Subgroup (Gw n w)) : Prop := ∀ w, CO (U w) ∧ U w ≤ GLnLocal.integralGL (w.adicCompletion K) n

def SphOff (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (τ : Submodule ℂ (LL μ)) (S : Set (Pl K)) : Prop :=
  ∀ w ∉ S, τ ⊓ fixL μ w (GLnLocal.integralGL (w.adicCompletion K) n) ≠ ⊥

variable {μ₂ : Measure (G1 K 2)} [μ₂.IsHaarMeasure]

structure ArchLine (τ₁ τ₂ : Submodule ℂ (L2 μ₂)) (κ : Measure (archCompact K (2 + 2))) (e : archCompact K (2 + 2) → ℂ)
    (κ₂ : Measure (archCompact K 2)) (p₁ p₂ : archCompact K 2 → ℂ) (k₀ : archCompact K (2 + 2)) : Prop where
  idem : IdemA κ e
  rank₁ : RankInf μ₂ τ₁ κ₂ p₁
  rank₂ : RankInf μ₂ τ₂ κ₂ p₂
  val : ∀ f, IsSec τ₁ τ₂ f → FixA κ e f → ∀ h : FA K (2 + 2),
    (∀ m₂, FixA κ₂ p₁ fun m₁ => f (lv m₁ m₂ 0 * arc1 k₀ * fin1 h)) ∧ ∀ m₁, FixA κ₂ p₂ fun m₂ => f (lv m₁ m₂ 0 * arc1 k₀ * fin1 h)
  inj : ∀ f, IsSec τ₁ τ₂ f → FixA κ e f → (∀ (h : FA K (2 + 2)) m₁ m₂, f (lv m₁ m₂ 0 * arc1 k₀ * fin1 h) = 0) → f = 0
  ex : ∀ S : Finset (Pl K), SphOff μ₂ τ₁ S → SphOff μ₂ τ₂ S →
    ∃ (U : ∀ w : Pl K, Subgroup (Gw (2 + 2) w)) (f : G1 K (2 + 2) → ℂ), Lev U ∧ f ≠ 0 ∧ IsSec τ₁ τ₂ f ∧ FixA κ e f ∧ FixF (levOn S U) f

structure IsTy (D : TypeDat K n) (κ : Measure (archCompact K n)) (e : archCompact K n → ℂ) (U : Subgroup (FA K n)) : Prop where
  level : D.Level U
  fix : ∀ f : G1 K n → ℂ, Continuous f → (D.Fix f ↔ FixA κ e f ∧ FixF U f)
  hecke : ∀ (β : TI K n) (φ : TF K n), BiA κ e β → (∀ u ∈ U, ∀ x, φ (u * x) = φ x ∧ φ (x * u) = φ x) → D.Hecke (tens β φ)

variable {μ : Measure (G1 K (2 + 2))} {τ₁ τ₂ : Submodule ℂ (L2 μ₂)} {D : TypeDat K (2 + 2)} {d : ℕ}

def HeckeAt (A : Line μ τ₁ τ₂ D d) (U : Subgroup (FA K (2 + 2))) (h : FA K (2 + 2)) (M : Eu d →ₗ[ℂ] Eu d) : Prop :=
  ∀ v, flat 0 (A.sec (M v)) = hop U h (flat 0 (A.sec v))

end Defs

def SplitBad (F : Type) [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E]
    (π : CuspSub E 2) : Prop :=
  ∀ v : Pl F, ¬ GM.Split E v → GM.Unr E v ∧ ∀ w : Pl E, w.under (𝓞 F) = v → ∃ B, (CG.mk π).HasSat w B

def IndCs : Prop :=
  ∀ (K M : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field M] [NumberField M] [IsTotallyComplex M] [Algebra K M],
    Module.finrank K M = 2 → ∀ π : CuspSub M 2, Z.Bc.MixWtC K π → SplitBad K π →
    ∃ P : CuspSub K (2 * 2), Z.Bc.IndSys (CG.mk π).HasSat (CG.mk P).HasSat ∧ ∀ (τ τ' : M →+* ℂ) (m m' : Multiset ℂ), τ ≠ τ' →
      τ.comp (algebraMap K M) = τ'.comp (algebraMap K M) → π.HasInfChar τ m → π.HasInfChar τ' m' →
      P.HasInfChar (τ.comp (algebraMap K M)) (m + m')

def ForSwap (p : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [IsTotallyComplex F]
    [IsTotallyComplex E] (_ : E ≃ₐ[F] E) (_ _ : Submodule ℂ (L2 (BW.mu1 E 2))) (_ : Twist (BW.mu1 E 2)), Prop) : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [IsTotallyComplex F]
    [IsTotallyComplex E] (σ : E ≃ₐ[F] E), Module.finrank F E = 2 → (∀ τ, τ ∈ Subgroup.zpowers σ) →
    ∀ (τ₁ τ₂ : Submodule ℂ (L2 (BW.mu1 E 2))) (θ₂ : Twist (BW.mu1 E 2)), Pair (BW.mu1 E 2) τ₁ τ₂ → UpperTheory.ConvolutionTheory.K.IsGal σ.toRingEquiv θ₂ →
      τ₁.map (θ₂.U : L2 (BW.mu1 E 2) →ₗ[ℂ] L2 (BW.mu1 E 2)) = τ₂ → τ₂.map (θ₂.U : L2 (BW.mu1 E 2) →ₗ[ℂ] L2 (BW.mu1 E 2)) = τ₁ →
      p F E σ τ₁ τ₂ θ₂

def IsSq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E ≃ₐ[F] E} (D : InfD σ 1) {n : ℕ}
    (eF : archCompact F n → ℂ) (e : archCompact E n → ℂ) : Prop :=
  ∀ (k : archCompact E n) (kk : Fin 2 → archCompact F n), (∀ i, (kk i : archGroup F n) = compA D n i k) → e k = ∏ i, eF (kk i)

def ArchEx : Prop := ForSwap fun F E _ _ _ _ _ _ _ _ σ τ₁ τ₂ _ => ∀ D : InfD σ 1,
  ∃ (κF : Measure (archCompact F (2 + 2))) (eF : archCompact F (2 + 2) → ℂ) (κ : Measure (archCompact E (2 + 2)))
    (e : archCompact E (2 + 2) → ℂ) (κ₂ : Measure (archCompact E 2)) (p₁ p₂ : archCompact E 2 → ℂ) (k₀ : archCompact E (2 + 2)),
    IdemA κF eF ∧ IsSq D eF e ∧ ArchLine τ₁ τ₂ κ e κ₂ p₁ p₂ k₀

def IrrW : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (μ : Measure (G1 K (2 + 2))) [μ.IsHaarMeasure] (μ₂ : Measure (G1 K 2))
    [μ₂.IsHaarMeasure] (τ₁ τ₂ : Submodule ℂ (L2 μ₂)), Pair μ₂ τ₁ τ₂ → ∀ κ e κ₂ p₁ p₂ k₀, ArchLine τ₁ τ₂ κ e κ₂ p₁ p₂ k₀ →
    ∀ (S : Finset (Pl K)) (U : ∀ w : Pl K, Subgroup (Gw (2 + 2) w)), Lev U → ∀ (D : TypeDat K (2 + 2)), IsTy D κ e (levOn S U) →
    ∀ (d : ℕ) (A : Line μ τ₁ τ₂ D d) (P : Submodule ℂ (Eu d)),
      (∀ w ∈ S, ∀ (g : Gw (2 + 2) w) M, HeckeAt A (levOn S U) (AdelicGLn.localEmbedding w g) M → ∀ v ∈ P, M v ∈ P) → P = ⊥ ∨ P = ⊤

def HeckeEx : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (μ : Measure (G1 K (2 + 2))) [μ.IsHaarMeasure] (μ₂ : Measure (G1 K 2))
    [μ₂.IsHaarMeasure] (τ₁ τ₂ : Submodule ℂ (L2 μ₂)), Pair μ₂ τ₁ τ₂ → ∀ κ e, IdemA κ e →
    ∀ (S : Finset (Pl K)) (U : ∀ w : Pl K, Subgroup (Gw (2 + 2) w)), Lev U → ∀ (D : TypeDat K (2 + 2)), IsTy D κ e (levOn S U) →
    ∀ (d : ℕ) (A : Line μ τ₁ τ₂ D d), (∀ h, ∃! M, HeckeAt A (levOn S U) h M) ∧
      (∀ w w' : Pl K, w ≠ w' → ∀ g g' M M', HeckeAt A (levOn S U) (AdelicGLn.localEmbedding w g) M →
        HeckeAt A (levOn S U) (AdelicGLn.localEmbedding w' g') M' → Commute M M') ∧
      ∀ (b : TI K (2 + 2)) (φ : TF K (2 + 2)) (β : ℝ → Eu d →L[ℂ] Eu d), (∀ x, φ x = (levOn S U : Set (FA K (2 + 2))).indicator 1 x) →
        ActsBy μ A (tens b φ) β → ∀ h M, HeckeAt A (levOn S U) h M → Commute M (symb β 0 : Eu d →ₗ[ℂ] Eu d)

def HeckeInj : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (μ : Measure (G1 K (2 + 2))) [μ.IsHaarMeasure] (μ₂ : Measure (G1 K 2))
    [μ₂.IsHaarMeasure] (τ₁ τ₂ : Submodule ℂ (L2 μ₂)), Pair μ₂ τ₁ τ₂ → ∀ κ e, IdemA κ e →
    ∀ (S : Finset (Pl K)) (U : ∀ w : Pl K, Subgroup (Gw (2 + 2) w)), Lev U → ∀ (D : TypeDat K (2 + 2)), IsTy D κ e (levOn S U) →
    ∀ (d : ℕ) (A : Line μ τ₁ τ₂ D d), ∀ w ∈ S, U w = GLnLocal.iwahori (w.adicCompletion K) (2 + 2) → ∀ ν : Fin (2 + 2) → ℤ, Antitone ν →
      ∀ M, HeckeAt A (levOn S U) (AdelicGLn.localEmbedding w (Cartan.diagPow (w.adicCompletion K) (2 + 2) ν)) M → Function.Injective M

def TypeOf : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (κ : Measure (archCompact K n)) (e : archCompact K n → ℂ), IdemA κ e →
    ∀ U : Subgroup (FA K n), U ≤ AdelicGLn.integralFiniteGL K n → IsOpen (U : Set (FA K n)) →
    ∃ D : TypeDat K n, IsTy D κ e U ∧ ∀ (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (θ : Twist μ),
      (∀ k : archCompact K n, ∃ k' : archCompact K n, θ.e (arc1 k) = arc1 k' ∧ e k' = e k) →
      (∀ u ∈ U, ∃ u' ∈ U, θ.e (fin1 u) = fin1 u') → (∀ g, θ.e (θ.e g) = g) → Stable D θ

def AmpEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyComplex F] [IsTotallyComplex E]
    (σ : E ≃ₐ[F] E) (D : InfD σ 1) (n : ℕ), 0 < n → ∀ (κF : Measure (archCompact F n)) (eF : archCompact F n → ℂ)
    (κ : Measure (archCompact E n)) (e : archCompact E n → ℂ), IdemA κF eF → IdemA κ e → IsSq D eF e →
    ∀ (νE : Measure (archGroup E n)) [νE.IsHaarMeasure] (νF : Measure (archGroup F n)) [νF.IsHaarMeasure],
      νE = Measure.map (glueA D n) (Measure.pi fun _ => νF) →
    ∀ φ : G1 E n → ℂ, Continuous φ → φ ≠ 0 → FixA κ e φ →
      ∃ (b a : TI F n) (aE : TI E n) (aF : TI F n), ArchSlot D νE νF b a aE aF ∧ BiA κ e aE ∧
        ∃ g, ∫ y, aE y * φ (g * archP E n y) ∂νE ≠ 0

def TensAmp : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (n : ℕ), 0 < n → ∀ (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (𝔞 : Amp μ)
    (φ : TF K n), (∀ x, φ x = (𝔞.U : Set (FA K n)).indicator 1 x) →
    (∃ c : ℝ, 0 < c ∧ (∀ Θ : G1 K n → ℂ, Continuous Θ → FixF 𝔞.U Θ → ∀ x, ∫ g, tens 𝔞.a₀ φ g * Θ (x * g) ∂μ =
      c * ∫ y, 𝔞.a₀ y * Θ (x * archP K n y) ∂𝔞.ν) ∧ Rop μ (tens 𝔞.a₀ φ) = (c : ℂ) • 𝔞.A) ∧
    ∀ c : ℂ, IsLeftSmooth (c • tens 𝔞.a₀ φ : TG K n)

def FinTw : Prop :=
  ∀ (W X : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] [Nontrivial W] (T : Fin 2 → X → Module.End ℂ W),
    (∀ x y, Commute (T 0 x) (T 1 y)) → (∀ P : Submodule ℂ W, (∀ i x, ∀ w ∈ P, T i x w ∈ P) → P = ⊥ ∨ P = ⊤) →
    ∀ U : W ≃ₗ[ℂ] W, (∀ i x w, U (T (i + 1) x w) = T i x (U w)) → ∀ i x, Function.Injective (T i x) →
      ∃ᶠ j : ℕ in atTop, LinearMap.trace ℂ W ((T i x ^ j) ∘ₗ (U : W →ₗ[ℂ] W)) ≠ 0

def SwapAt : Prop := ForSwap fun F E _ _ _ _ _ _ _ _ σ τ₁ τ₂ _ =>
  (∀ (τ : E →+* ℂ) m, SInf (BW.mu1 E 2) τ₂ τ m ↔ SInf (BW.mu1 E 2) τ₁ (τ.comp σ.toRingEquiv.toRingHom) m) ∧
  ∀ w w' : Pl E, w.under (𝓞 F) = w'.under (𝓞 F) → (w ≠ w' ∨ ¬ GM.Split E (w.under (𝓞 F))) →
    ∀ B, SSat (BW.mu1 E 2) τ₂ w B ↔ SSat (BW.mu1 E 2) τ₁ w' B

def RigidE : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (τ₁ τ₂ : Submodule ℂ (L2 (BW.mu1 E 2))), Pair (BW.mu1 E 2) τ₁ τ₂ →
    ∀ (S : Set (Pl E)), S.Finite → ∀ m₁ m₂ B₁ B₂, At (BW.mu1 E 2) S τ₁ m₁ B₁ → At (BW.mu1 E 2) S τ₂ m₂ B₂ →
    (∀ b : Datum E (2 + 2), b.Pt S (fun τ => m₁ τ + m₂ τ) (fun w => B₁ w + B₂ w) →
      b.r = 2 ∧ (∀ i, b.d i = 2) ∧ ∃ i j, i ≠ j ∧ At (b.μ i) S (b.V i) m₁ B₁ ∧ At (b.μ j) S (b.V j) m₂ B₂) ∧
    ∀ (μ : Measure (G1 E (2 + 2))) [μ.IsHaarMeasure] (V : Submodule ℂ (LL μ)), IsSummand μ V →
      ¬ At μ S V (fun τ => m₁ τ + m₂ τ) fun w => B₁ w + B₂ w

def RigidF : Prop := ForSwap fun F E _ _ _ _ _ _ _ _ _ τ₁ τ₂ _ =>
  ∀ (SE : Set (Pl E)) (SF : Set (Pl F)), SE.Finite → SF.Finite → ∀ m₁ m₂ B₁ B₂, At (BW.mu1 E 2) SE τ₁ m₁ B₁ → At (BW.mu1 E 2) SE τ₂ m₂ B₂ →
    ∀ (b : Datum F (2 + 2)) Λ' t', b.Pt SF Λ' t' → ¬ ∀ w ∉ SE, B₁ w + B₂ w = bcSat t' w

def LocSm : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [IsTotallyComplex F]
    [IsTotallyComplex E] (σ : E ≃ₐ[F] E), Module.finrank F E = 2 → (∀ τ, τ ∈ Subgroup.zpowers σ) → ∀ n : ℕ, 0 < n →
    ∀ (q : Pl F) (w₀ : PlacesOver E q) (S : Finset (Pl F)), q ∉ S → (∀ v ∉ S, GM.Unr E v) → (∀ v ∈ S, GM.Split E v) →
    ∀ U₀ : ∀ w : Pl E, Subgroup (Gw n w), Lev U₀ → ∀ SE : Finset (Pl E), (∀ w, w ∈ SE ↔ w.under (𝓞 F) ∈ S ∨ w.under (𝓞 F) = q) →
    ∃ (L : GM.Loc σ n q w₀) (U : ∀ w : Pl E, Subgroup (Gw n w)), L.S = S ∧ Lev U ∧ (∀ w : Pl E, w.under (𝓞 F) ∈ S → U w ≤ U₀ w) ∧
      (∀ w : Pl E, w.under (𝓞 F) = q → U w = GLnLocal.iwahori (w.adicCompletion E) n) ∧ GM.levE L.UE = levOn SE U ∧
      (∀ v, L.φ v = (L.UE v : Set (GL (Fin n) (CompletionsOver E v))).indicator 1) ∧
      ∀ (μ : Measure (G1 E n)) [μ.IsHaarMeasure] (θ : Twist μ), IsGalTwist σ θ →
        ∀ u ∈ levOn SE U, ∃ u' ∈ levOn SE U, θ.e (fin1 u) = fin1 u'

def GalLoc : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [IsTotallyComplex F]
    [IsTotallyComplex E] (σ : E ≃ₐ[F] E), Module.finrank F E = 2 → (∀ τ, τ ∈ Subgroup.zpowers σ) → ∀ n : ℕ, 0 < n →
    ∀ (μ : Measure (G1 E n)) [μ.IsHaarMeasure] (θ : Twist μ), (IsGalTwist σ θ ↔ UpperTheory.ConvolutionTheory.K.IsGal σ.toRingEquiv θ) ∧ (IsGalTwist σ θ →
      (∀ g, θ.e (θ.e g) = g) ∧
      (∀ (D : InfD σ 1) (eF : archCompact F n → ℂ) (e : archCompact E n → ℂ), IsSq D eF e →
        ∀ k : archCompact E n, ∃ k' : archCompact E n, θ.e (arc1 k) = arc1 k' ∧ e k' = e k) ∧
      ∀ v : Pl F, GM.Split E v → ∃ w : Fin 2 ≃ PlacesOver E v, ∀ (i : Fin 2) (g : Gw n v),
        θ.e (fin1 (AdelicGLn.localEmbedding (w i).1 (mapGL n (completionMap v (w i).1) g))) =
          fin1 (AdelicGLn.localEmbedding (w (i + 1)).1 (mapGL n (completionMap v (w (i + 1)).1) g)))

def FamNe : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [IsTotallyComplex F]
    [IsTotallyComplex E] (σ : E ≃ₐ[F] E), Module.finrank F E = 2 → (∀ τ, τ ∈ Subgroup.zpowers σ) →
    ∀ (μ : Measure (G1 E (2 + 2))) [μ.IsHaarMeasure] (θ : Twist μ), IsGalTwist σ θ → ∀ (𝔢 : Side θ 2) (𝔵 : Fam 𝔢) κ e κ₂ p₁ p₂ k₀,
      ArchLine 𝔵.τ₁ 𝔵.τ₂ κ e κ₂ p₁ p₂ k₀ → ∀ (S : Finset (Pl E)) (U : ∀ w : Pl E, Subgroup (Gw (2 + 2) w)), Lev U →
      (∀ w ∈ S, GM.Split E (w.under (𝓞 F)) ∧ ∀ w' : Pl E, w'.under (𝓞 F) = w.under (𝓞 F) → w' ∈ S) →
      𝔢.U = levOn S U → IsTy 𝔵.D κ e (levOn S U) → (∀ u ∈ levOn S U, ∃ u' ∈ levOn S U, θ.e (fin1 u) = fin1 u') →
      ∀ w₀ ∈ S, U w₀ = GLnLocal.iwahori (w₀.adicCompletion E) (2 + 2) → ∀ ν : Fin (2 + 2) → ℤ, Antitone ν → 𝔢.Uq 0 = Uiw μ w₀ ν →
      ∀ φ : TF E (2 + 2), (∀ x, φ x = (levOn S U : Set (FA E (2 + 2))).indicator 1 x) → 𝔢.g = tens 𝔢.a₀ φ → (∃ c : ℂ, c ≠ 0 ∧ 𝔢.a = c • 𝔢.g) → BiA κ e 𝔢.a₀ →
      (∃ v g, ∫ y, 𝔢.a₀ y * flat 0 (𝔵.A.sec v) (g * archP E (2 + 2) y) ∂𝔢.ν ≠ 0) →
      ∀ N : Eu 𝔵.d' ≃ₗᵢ[ℂ] Eu 𝔵.d, (∀ (Y : L2 μ →L[ℂ] L2 μ) s s', Act 𝔵.A.J Y s → Act 𝔵.A'.J Y s' → ∀ w, N (s' 0 w) = s 0 (N w)) →
      ∃ x : ℝ, 0 < x ∧ ∃ᶠ j : ℕ in atTop, 𝔵.tr N x j ≠ 0

def CoreInd : Prop := ForSwap fun F E _ _ _ _ _ _ _ _ _ τ₁ τ₂ _ =>
  ∀ S : Finset (Pl F), (∀ v ∈ S, GM.Split E v) → (∀ v ∉ S, GM.Unr E v) → ∀ m₁ m₂ B₁ B₂,
    At (BW.mu1 E 2) {w | w.under (𝓞 F) ∈ S} τ₁ m₁ B₁ → At (BW.mu1 E 2) {w | w.under (𝓞 F) ∈ S} τ₂ m₂ B₂ →
    ∀ (μF : Measure (G1 F (2 + 2))) [μF.IsHaarMeasure], ∃ (V : Submodule ℂ (LL μF)) (Λ : (F →+* ℂ) → Multiset ℂ) (t : Pl F → Multiset ℂ),
      IsSummand μF V ∧ T.AtAE μF V Λ t ∧ (fun τ => m₁ τ + m₂ τ) = bcInf Λ ∧ ∀ᶠ w in cofinite, B₁ w + B₂ w = bcSat t w

def SignMs : Prop :=
  ∀ (A B : Multiset ℂˣ), A.card = 4 → B.card = 2 → A.map (fun x => -x) = A → A.map (· ^ 2) = B + B →
    ∃ B' : Multiset ℂˣ, B = B'.map (· ^ 2) ∧ A = B' + B'.map fun b => -b

def SysOf : Prop :=
  ∀ (K M : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field M] [NumberField M] [IsTotallyComplex M] [Algebra K M] [IsGalois K M],
    Module.finrank K M = 2 → ∀ (π π' : CG M 2) (P : CG K (2 * 2)),
    (∀ w w' : Pl M, w.under (𝓞 K) = w'.under (𝓞 K) → (w ≠ w' ∨ ¬ GM.Split M (w.under (𝓞 K))) → ∀ B, π'.HasSat w B ↔ π.HasSat w' B) →
    WeakBC P.HasSat (R.sumSat (m := fun _ : Fin 2 => 2) ![π, π']) → Z.Bc.IndSys π.HasSat P.HasSat

def IndNorm : Prop :=
  ∀ (K M : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field M] [NumberField M] [IsTotallyComplex M] [Algebra K M] [IsGalois K M],
    Module.finrank K M = 2 → ∀ π : CuspSub M 2, GlobalTheory.DiscSpec.IsNormalised π →
    (∀ σ : M ≃ₐ[K] M, σ ≠ 1 → ¬ (UpperTheory.CBC.Cusp.cx π).ConjIso σ.toRingEquiv) → SplitBad K π →
    ∃ P : CuspSub K (2 * 2), Z.Bc.IndSys (CG.mk π).HasSat (CG.mk P).HasSat ∧ ∀ (τ τ' : M →+* ℂ) (m m' : Multiset ℂ), τ ≠ τ' →
      τ.comp (algebraMap K M) = τ'.comp (algebraMap K M) → π.HasInfChar τ m → π.HasInfChar τ' m' →
      P.HasInfChar (τ.comp (algebraMap K M)) (m + m')

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E
