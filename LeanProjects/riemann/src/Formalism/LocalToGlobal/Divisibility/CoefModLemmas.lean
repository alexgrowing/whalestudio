import Formalism.LocalToGlobal.Divisibility.CoefMod

open MvPolynomial NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.DIV

open Formalism.BasicNotions

def FockSHerm : Prop :=
  ∀ (K : Type) [Field K] [StarRing K] (σ : Type) (f g : MvPolynomial σ K), fockS g f = star (fockS f g)

def FockSQ : Prop :=
  ∀ (K : Type) [Field K] [StarRing K] [CharZero K] (σ : Type) (f g : MvPolynomial σ ℚ),
    fockS (map (algebraMap ℚ K) f) (map (algebraMap ℚ K) g) = algebraMap ℚ K (Formalism.GradedWeylDivisibility.fockQ f g)

def FockSAdj : Prop :=
  ∀ (K : Type) [Field K] [StarRing K] (ι : Type) [Fintype ι] (n : ℕ) (U : ι → Matrix (Fin n) (Fin n) K)
    (F F' : Pol K ι n),
    fockS (Formalism.GradedWeylDivisibility.blockAct K U F) F' = fockS F (Formalism.GradedWeylDivisibility.blockAct K (fun τ => (U τ)ᴴ) F')

def FockSTen : Prop :=
  ∀ (K : Type) [Field K] [StarRing K] (ι : Type) [Fintype ι] (n : ℕ)
    (f g : ι → MvPolynomial (Fin n × Fin n) K), fockS (ten f) (ten g) = ∏ τ, fockS (f τ) (g τ)

def ExtNormPos : Prop :=
  ∀ (K : Type) [Field K] [StarRing K] [CharZero K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n),
    ∃ q : ℚ, 0 < q ∧ extNorm K lam = algebraMap ℚ K q

def ActTen : Prop :=
  ∀ (K : Type) [Field K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (g : ι → GL (Fin n) K)
    (f : ι → MvPolynomial (Fin n × Fin n) K),
    actP lam g (ten f) = ten fun τ => sqAct K n (lam τ) (g τ) (f τ)

def ActRat : Prop :=
  ∀ (K : Type) [Field K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (K0 : Subfield K)
    (g : ι → GL (Fin n) K), (∀ τ a b, (g τ : Matrix (Fin n) (Fin n) K) a b ∈ K0) →
    ∀ i j, (bVV K lam).repr (rhoK lam g (bVV K lam j)) i ∈ K0

def PairTransport : Prop :=
  ∀ (K : Type) [Field K] [StarRing K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n)
    (G : ι → Matrix (Fin n) (Fin n) K) (g g' : ι → GL (Fin n) K) (F F' : Pol K ι n),
    pairP lam G (actP lam g F) (actP lam g' F') =
      pairP lam (fun τ => (g τ : Matrix (Fin n) (Fin n) K)ᴴ * G τ * (g' τ : Matrix (Fin n) (Fin n) K)) F F'

def PairInv : Prop :=
  ∀ (K : Type) [Field K] [StarRing K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n)
    (G : ι → Matrix (Fin n) (Fin n) K) (g : ι → GL (Fin n) K),
    (∀ τ, (g τ : Matrix (Fin n) (Fin n) K)ᴴ * G τ * (g τ : Matrix (Fin n) (Fin n) K) = G τ) →
    ∀ x y : VV K lam, pairK lam G (rhoK lam g x) (rhoK lam g y) = pairK lam G x y

def PairExtremal : Prop :=
  ∀ (K : Type) [Field K] [StarRing K] [CharZero K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n)
    (G : ι → Matrix (Fin n) (Fin n) K) (B : ι → GL (Fin n) K),
    (∀ τ, (B τ : Matrix (Fin n) (Fin n) K)ᴴ * G τ * (B τ : Matrix (Fin n) (Fin n) K) = 1) →
    pairP lam G (actP lam B (ten fun τ => extremal K n (lam τ))) (actP lam B (ten fun τ => extremal K n (lam τ))) = 1

def PairSymm : Prop :=
  ∀ (K : Type) [Field K] [StarRing K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n)
    (G : ι → Matrix (Fin n) (Fin n) K), (∀ τ, (G τ)ᴴ = G τ) → (pairK lam G).IsSymm

def PairNondeg : Prop :=
  ∀ (K : Type) [Field K] [StarRing K] [CharZero K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n)
    (G : ι → Matrix (Fin n) (Fin n) K), (∀ τ, IsUnit (G τ).det) → (pairK lam G).Nondegenerate

def PairRat : Prop :=
  ∀ (K : Type) [Field K] [StarRing K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (K0 : Subfield K)
    (G : ι → Matrix (Fin n) (Fin n) K), (∀ τ a b, G τ a b ∈ K0) →
    ∀ i j, pairK lam G (bVV K lam i) (bVV K lam j) ∈ K0

def PairPos : Prop :=
  ∀ (K : Type) [Field K] [StarRing K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n)
    (G : ι → Matrix (Fin n) (Fin n) K) (φ : K →+* ℂ), (∀ τ, ((G τ).map φ).PosDef) →
    (Matrix.of fun i j : VVIdx lam => φ (pairK lam G (bVV K lam i) (bVV K lam j))).PosDef

def BasisAtEx : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (M : Submodule (𝓞 K) (Fin n → K)), Submodule.IsLattice K M →
    ∀ w : HeightOneSpectrum (𝓞 K), ∃ B : GL (Fin n) K, IsBasisAt w M B

def NabIndep : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n)
    (w : HeightOneSpectrum (𝓞 K)) (M : ι → Submodule (𝓞 K) (Fin n → K)) (B B' : ι → GL (Fin n) K),
    (∀ τ, IsBasisAt w (M τ) (B τ)) → (∀ τ, IsBasisAt w (M τ) (B' τ)) → ∀ F : Pol K ι n,
      (actP lam B⁻¹ F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabStd K lam) ↔
        actP lam B'⁻¹ F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabStd K lam))

def DelIndep : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n)
    (w : HeightOneSpectrum (𝓞 K)) (M : ι → Submodule (𝓞 K) (Fin n → K)) (B B' : ι → GL (Fin n) K),
    (∀ τ, IsBasisAt w (M τ) (B τ)) → (∀ τ, IsBasisAt w (M τ) (B' τ)) → ∀ F : Pol K ι n,
      (actP lam B⁻¹ F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (delStd K lam) ↔
        actP lam B'⁻¹ F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (delStd K lam))

def NabDelFree : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n)
    (B : ι → GL (Fin n) K),
    nabP lam (fun τ => colLat (B τ)) = (nabStd K lam).map ((actP lam B).restrictScalars (𝓞 K)) ∧
    delP lam (fun τ => colLat (B τ)) = (delStd K lam).map ((actP lam B).restrictScalars (𝓞 K))

def NabDelLoc : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n)
    (M : ι → Submodule (𝓞 K) (Fin n → K)), (∀ τ, Submodule.IsLattice K (M τ)) →
    ∀ (w : HeightOneSpectrum (𝓞 K)) (B : ι → GL (Fin n) K), (∀ τ, IsBasisAt w (M τ) (B τ)) →
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabP lam M) =
        (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabStd K lam)).map ((actP lam B).restrictScalars (𝓞 K)) ∧
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (delP lam M) =
        (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (delStd K lam)).map ((actP lam B).restrictScalars (𝓞 K))

def NabRoundFree : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (m : ℕ) (lam : ι → DomWeight (m + 1))
    (B : ι → GL (Fin (m + 1)) K),
    nabP lam (fun τ => dualFr (colLat (B τ))) =
      Formalism.GradedWeylDivisibility.tensorLat (𝓞 K) K fun τ =>
        Formalism.GradedWeylDivisibility.nablaLTw (𝓞 K) K m (lam τ).w (B τ : Matrix (Fin (m + 1)) (Fin (m + 1)) K)

def NabLeVV : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n)
    (M : ι → Submodule (𝓞 K) (Fin n → K)), (∀ τ, Submodule.IsLattice K (M τ)) →
    ∀ F ∈ nabP lam M, F ∈ VV K lam

def NabDelLattice : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n)
    (M : ι → Submodule (𝓞 K) (Fin n → K)), (∀ τ, Submodule.IsLattice K (M τ)) →
    Submodule.IsLattice K (nabK lam M) ∧ Submodule.IsLattice K (delK lam M)

def DelLeNab : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n)
    (M : ι → Submodule (𝓞 K) (Fin n → K)), delK lam M ≤ nabK lam M

def NabDelEquiv : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n)
    (M : ι → Submodule (𝓞 K) (Fin n → K)) (g : ι → GL (Fin n) K),
    nabP lam (fun τ => gLat (g τ) (M τ)) = (nabP lam M).map ((actP lam g).restrictScalars (𝓞 K)) ∧
    delP lam (fun τ => gLat (g τ) (M τ)) = (delP lam M).map ((actP lam g).restrictScalars (𝓞 K))

def NabDelStable : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n)
    (M : ι → Submodule (𝓞 K) (Fin n → K)) (g : ι → GL (Fin n) K), (∀ τ, gLat (g τ) (M τ) = M τ) →
    (∀ x ∈ nabK lam M, rhoK lam g x ∈ nabK lam M) ∧ (∀ x ∈ delK lam M, rhoK lam g x ∈ delK lam M)

def NabDelDual : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n)
    (G : ι → Matrix (Fin n) (Fin n) K) (M : ι → Submodule (𝓞 K) (Fin n → K)),
    (∀ τ, (G τ)ᴴ = G τ) → (∀ τ, IsUnit (G τ).det) → (∀ τ, Submodule.IsLattice K (M τ)) →
    Formalism.HermitianLatticesTheory.dual (pairK lam G) (nabK lam M) = delK lam (fun τ => hdualFr (G τ) (M τ)) ∧
    Formalism.HermitianLatticesTheory.dual (pairK lam G) (delK lam M) = nabK lam (fun τ => hdualFr (G τ) (M τ))

def DualFrHdual : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n : ℕ) (G : Matrix (Fin n) (Fin n) K)
    (M : Submodule (𝓞 K) (Fin n → K)), Gᴴ = G → IsUnit G.det → Submodule.IsLattice K M →
    hdualFr (G⁻¹)ᵀ (dualFr M) = dualFr (hdualFr G M)

def DualFrLattice : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n : ℕ) (G : Matrix (Fin n) (Fin n) K)
    (M : Submodule (𝓞 K) (Fin n → K)), IsUnit G.det → Submodule.IsLattice K M →
    Submodule.IsLattice K (dualFr M) ∧ Submodule.IsLattice K (hdualFr G M)

def TauLatLattice : Prop :=
  ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] (ι : Type) (n : ℕ) (emb : ι → E →+* K) (τ : ι)
    (L : Submodule (𝓞 E) (Fin n → E)), Submodule.IsLattice E L → Submodule.IsLattice K (tauLat emb τ L)

def TauLatG : Prop :=
  ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] (ι : Type) (n : ℕ) (emb : ι → E →+* K) (τ : ι)
    (L : Submodule (𝓞 E) (Fin n → E)) (γ : GL (Fin n) E),
    tauLat emb τ (L.map ((Matrix.mulVecLin (γ : Matrix (Fin n) (Fin n) E)).restrictScalars (𝓞 E))) =
      gLat (embGL emb γ τ) (tauLat emb τ L)

def TauLatDual : Prop :=
  ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [StarRing K] (ι : Type) (n : ℕ)
    (emb : ι → E →+* K) (cE : E →+* E) (τ : ι), (∀ x, star (emb τ x) = emb τ (cE x)) →
    ∀ (J : Matrix (Fin n) (Fin n) E) (L L' : Submodule (𝓞 E) (Fin n → E)), IsUnit J.det → Submodule.IsLattice E L →
      (∀ y, y ∈ L' ↔ ∀ x ∈ L, Formalism.UG.hform cE J x y ∈ (algebraMap (𝓞 E) E).range) →
      hdualFr (gramK emb J τ) (tauLat emb τ L) = tauLat emb τ L'

def GramHerm : Prop :=
  ∀ (E K : Type) [Field E] [Field K] [StarRing K] (ι : Type) (n : ℕ)
    (emb : ι → E →+* K) (cE : E →+* E) (τ : ι), (∀ x, star (emb τ x) = emb τ (cE x)) →
    ∀ J : Matrix (Fin n) (Fin n) E, Formalism.UG.IsHerm cE J →
      (gramK emb J τ)ᴴ = gramK emb J τ ∧ (gramKd emb J τ)ᴴ = gramKd emb J τ

def UJUnitary : Prop :=
  ∀ (E K : Type) [Field E] [Field K] [StarRing K] (ι : Type) (n : ℕ)
    (emb : ι → E →+* K) (cE : E →+* E) (τ : ι), (∀ x, star (emb τ x) = emb τ (cE x)) →
    ∀ (J : Matrix (Fin n) (Fin n) E) (γ : GL (Fin n) E), γ ∈ Formalism.UG.UJ cE J →
      ((embGL emb γ τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᴴ * gramK emb J τ *
        ((embGL emb γ τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = gramK emb J τ ∧
      (IsUnit J.det →
        ((invTrK (embGL emb γ) τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᴴ * gramKd emb J τ *
          ((invTrK (embGL emb γ) τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = gramKd emb J τ)

def RoundGL : Prop :=
  ∀ (E K : Type) [Field E] [Field K] (ι : Type) (n : ℕ) (emb : ι → E →+* K) (cE : E →+* E)
    (Jg γ : GL (Fin n) E), γ ∈ Formalism.UG.UJ cE (Jg : Matrix (Fin n) (Fin n) E) →
    invTrK (embGL emb γ) =
      invTrK (embGL emb Jg⁻¹) * embGL (fun τ => (emb τ).comp cE) γ * (invTrK (embGL emb Jg⁻¹))⁻¹

def RoundLat : Prop :=
  ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] (ι : Type) (n : ℕ)
    (emb : ι → E →+* K) (cE : E →+* E) (τ : ι), (∀ x, cE (cE x) = x) →
    ∀ (Jg : GL (Fin n) E) (L L' : Submodule (𝓞 E) (Fin n → E)), Submodule.IsLattice E L →
      Formalism.UG.IsHerm cE (Jg : Matrix (Fin n) (Fin n) E) →
      (∀ y, y ∈ L' ↔ ∀ x ∈ L, Formalism.UG.hform cE (Jg : Matrix (Fin n) (Fin n) E) x y ∈ (algebraMap (𝓞 E) E).range) →
      dualFr (tauLat emb τ L) = gLat (invTrK (embGL emb Jg⁻¹) τ) (tauLat (fun τ => (emb τ).comp cE) τ L')

def RoundGram : Prop :=
  ∀ (E K : Type) [Field E] [Field K] [StarRing K] (ι : Type) (n : ℕ)
    (emb : ι → E →+* K) (cE : E →+* E) (τ : ι), (∀ x, star (emb τ x) = emb τ (cE x)) →
    ∀ Jg : GL (Fin n) E, Formalism.UG.IsHerm cE (Jg : Matrix (Fin n) (Fin n) E) →
      ((invTrK (embGL emb Jg⁻¹) τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᴴ *
          gramKd emb (Jg : Matrix (Fin n) (Fin n) E) τ *
          ((invTrK (embGL emb Jg⁻¹) τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        gramK (fun τ => (emb τ).comp cE) (Jg : Matrix (Fin n) (Fin n) E) τ

theorem fockSHerm : FockSHerm := by
  classical
  intro K _ _ σ f g
  rw [fockS_eq_sum g f (f.support ∪ g.support) Finset.subset_union_right,
    fockS_eq_sum f g (f.support ∪ g.support) Finset.subset_union_left, star_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [star_mul', star_star, star_natCast]
  ring

theorem actTen : ActTen := by
  intro K _ ι _ n lam g f
  have h1 : ∀ τ, trAct g (Formalism.GradedWeylDivisibility.blockEmb K τ (f τ)) =
      Formalism.GradedWeylDivisibility.blockEmb K τ (Formalism.GradedWeylDivisibility.rowAct K ((g τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ (f τ)) :=
    fun τ => (Formalism.GradedWeylDivisibility.blockActTensor K K ι n n _).1 τ (f τ)
  simp only [actP, ten, LinearMap.smul_apply, AlgHom.toLinearMap_apply, map_prod, h1, sqAct, detTwK,
    smul_eq_C_mul]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_mul]
  simp only [Formalism.GradedWeylDivisibility.blockEmb, rename_C]

theorem natW_antitone {n : ℕ} (lam : DomWeight n) : Antitone lam.natW := by
  intro i j hij
  have := lam.anti hij
  simp only [DomWeight.natW]
  omega

theorem localization_mono {R W : Type} [CommRing R] [AddCommGroup W] [Module R W] (p : Ideal R) [p.IsPrime]
    {L L' : Submodule R W} (h : L ≤ L') : Formalism.HermitianLatticesTheory.localization₂ p L ≤ Formalism.HermitianLatticesTheory.localization₂ p L' := by
  rintro x ⟨s, hs, hx⟩
  exact ⟨s, hs, h hx⟩

theorem transLat_mono {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    {T T' : Submodule (𝓞 K) (Pol K ι n)} (h : T ≤ T') (M : ι → Submodule (𝓞 K) (Fin n → K)) :
    transLat lam T M ≤ transLat lam T' M :=
  iInf_mono fun w => iInf_mono fun _ => iInf_mono fun _ => Submodule.comap_mono (localization_mono w.asIdeal h)

theorem delStd_le_nabStd (K : Type) [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) :
    delStd K lam ≤ nabStd K lam := by
  refine Submodule.span_mono ?_
  rintro P ⟨F, hF, rfl⟩
  exact ⟨F, fun τ => Submodule.map_mono (Formalism.GradedWeylDivisibility.weylLeDual (𝓞 K) n n le_rfl _ (natW_antitone (lam τ))) (hF τ), rfl⟩

theorem delLeNab : DelLeNab := by
  intro K _ _ ι _ n lam M
  exact Submodule.comap_mono (transLat_mono lam (delStd_le_nabStd K lam) M)

theorem nabP_colLat_le {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (B : ι → GL (Fin n) K) (w : HeightOneSpectrum (𝓞 K)) {F : Pol K ι n} (hF : F ∈ nabP lam fun τ => colLat (B τ)) :
    actP lam B⁻¹ F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabStd K lam) := by
  have h := hF
  simp only [nabP, transLat, Submodule.mem_iInf] at h
  exact h w B fun _ => rfl

theorem bc_coe {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (φ : A →+* B) (g : GL (Fin n) A) :
    ((Formalism.UG.bc φ g : GL (Fin n) B) : Matrix (Fin n) (Fin n) B) = (g : Matrix (Fin n) (Fin n) A).map φ := rfl

theorem embGL_coe {E K : Type} [Field E] [Field K] {ι : Type} {n : ℕ} (emb : ι → E →+* K) (γ : GL (Fin n) E) (τ : ι) :
    ((embGL emb γ τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = (γ : Matrix (Fin n) (Fin n) E).map (emb τ) := rfl

theorem embGL_inv {E K : Type} [Field E] [Field K] {ι : Type} {n : ℕ} (emb : ι → E →+* K) (γ : GL (Fin n) E) (τ : ι) :
    (embGL emb γ τ)⁻¹ = embGL emb γ⁻¹ τ := by
  rw [map_inv]; rfl

theorem invTrK_coe {K : Type} [Field K] {ι : Type} {n : ℕ} (g : ι → GL (Fin n) K) (τ : ι) :
    ((invTrK g τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (((g τ)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ := rfl

theorem map_conjTranspose_eq {E K : Type} [Field E] [Field K] [StarRing K] {n : ℕ} (φ : E →+* K) (cE : E →+* E)
    (h : ∀ x, star (φ x) = φ (cE x)) (A : Matrix (Fin n) (Fin n) E) : (A.map φ)ᴴ = (Formalism.UG.cT cE A).map φ := by
  ext i j
  simp [Formalism.UG.cT, Matrix.conjTranspose_apply, h]

theorem conjTranspose_transpose' {K : Type} [Field K] [StarRing K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K) :
    (Aᵀ)ᴴ = (Aᴴ)ᵀ := by
  ext i j
  simp [Matrix.conjTranspose_apply]

theorem gramHerm : GramHerm := by
  intro E K _ _ _ ι n emb cE τ h J hJ
  have h1 : (gramK emb J τ)ᴴ = gramK emb J τ := by
    unfold gramK
    rw [map_conjTranspose_eq (emb τ) cE h, hJ]
  refine ⟨h1, ?_⟩
  unfold gramKd
  unfold gramK at h1
  rw [conjTranspose_transpose', Matrix.conjTranspose_nonsing_inv, h1]

theorem uJUnitary : UJUnitary := by
  intro E K _ _ _ ι n emb cE τ h J γ hγ
  have hγ' : Formalism.UG.cT cE (γ : Matrix (Fin n) (Fin n) E) * J * (γ : Matrix (Fin n) (Fin n) E) = J := hγ
  have h1 : ((γ : Matrix (Fin n) (Fin n) E).map (emb τ))ᴴ * J.map (emb τ) * (γ : Matrix (Fin n) (Fin n) E).map (emb τ)
      = J.map (emb τ) := by
    rw [map_conjTranspose_eq (emb τ) cE h, ← Matrix.map_mul, ← Matrix.map_mul, hγ']
  refine ⟨h1, fun _ => ?_⟩
  rw [invTrK_coe, Matrix.coe_units_inv, embGL_coe]
  unfold gramKd
  set g := (γ : Matrix (Fin n) (Fin n) E).map (emb τ) with hg
  set G := J.map (emb τ) with hG
  rw [conjTranspose_transpose', ← Matrix.transpose_mul, ← Matrix.transpose_mul, Matrix.conjTranspose_nonsing_inv,
    ← Matrix.mul_inv_rev, ← Matrix.mul_inv_rev, h1]

theorem tauLatG : TauLatG := by
  intro E K _ _ _ _ ι n emb τ L γ
  unfold tauLat gLat
  rw [Submodule.map_span]
  congr 1
  ext y
  simp only [Set.mem_image, SetLike.mem_coe, Submodule.mem_map, LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨_, ⟨x, hx, rfl⟩, ?_⟩
    funext a
    simp [embGL_coe, Matrix.mulVec, dotProduct, map_sum]
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨_, ⟨x, hx, rfl⟩, ?_⟩
    funext a
    simp [embGL_coe, Matrix.mulVec, dotProduct, map_sum]

section Adj

variable {K : Type} [Field K] [StarRing K]

theorem fockL_monomial_left {σ : Type} (u : σ →₀ ℕ) (c : K) (g : MvPolynomial σ K) :
    fockL (monomial u c) g = star c * g.coeff u * (mfact u : K) := by
  classical
  rw [fockL_apply, fockS_eq_sum _ _ {u} support_monomial_subset, Finset.sum_singleton, coeff_monomial, if_pos rfl]

theorem fockL_symm {σ : Type} (f g : MvPolynomial σ K) : fockL f g = star (fockL g f) :=
  fockSHerm K σ g f

theorem fockL_pderiv_X {σ : Type} [DecidableEq σ] (v : σ) (f g : MvPolynomial σ K) :
    fockL (pderiv v f) g = fockL f (X v * g) := by
  induction f using MvPolynomial.induction_on' with
  | monomial u c =>
    rw [pderiv_monomial, fockL_monomial_left, fockL_monomial_left, coeff_X_mul']
    by_cases hv : u v = 0
    · have : v ∉ u.support := Finsupp.notMem_support_iff.mpr hv
      simp [hv, this]
    · have : v ∈ u.support := Finsupp.mem_support_iff.mpr hv
      rw [if_pos this]
      unfold mfact
      rw [Formalism.REAL.prod_factorial_support_sub_single u v hv, star_mul', star_natCast]
      push_cast; ring
  | add p q hp hq => rw [map_add, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, hp, hq]

theorem fockL_X_pderiv {σ : Type} [DecidableEq σ] (v : σ) (f g : MvPolynomial σ K) :
    fockL (X v * f) g = fockL f (pderiv v g) := by
  rw [fockL_symm, ← fockL_pderiv_X, ← fockL_symm]

theorem fockL_C_left {σ : Type} (a : K) (g : MvPolynomial σ K) : fockL (C a) g = star a * constantCoeff g := by
  rw [← monomial_zero', fockL_monomial_left]
  simp [constantCoeff, mfact]

variable {ι : Type} [Fintype ι] {n : ℕ}

omit [StarRing K] in
theorem blockAct_X (U : ι → Matrix (Fin n) (Fin n) K) (v : ι × Fin n × Fin n) :
    Formalism.GradedWeylDivisibility.blockAct K U (X v) = ∑ b : Fin n, C (U v.1 v.2.1 b) * X (v.1, (b, v.2.2)) := by
  simp [Formalism.GradedWeylDivisibility.blockAct]

omit [StarRing K] in
theorem constantCoeff_blockAct (U : ι → Matrix (Fin n) (Fin n) K) (g : Pol K ι n) :
    constantCoeff (Formalism.GradedWeylDivisibility.blockAct K U g) = constantCoeff g := by
  have : (constantCoeff : Pol K ι n →+* K).comp (Formalism.GradedWeylDivisibility.blockAct K U).toRingHom = constantCoeff := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp
    · intro i; simp [blockAct_X]
  exact congrArg (fun φ : Pol K ι n →+* K => φ g) this

omit [StarRing K] in

theorem pderiv_blockAct [DecidableEq ι] (V : ι → Matrix (Fin n) (Fin n) K) (s : ι) (a t : Fin n) (g : Pol K ι n) :
    pderiv (s, (a, t)) (Formalism.GradedWeylDivisibility.blockAct K V g) =
      ∑ b : Fin n, C (V s b a) * Formalism.GradedWeylDivisibility.blockAct K V (pderiv (s, (b, t)) g) := by
  induction g using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq, mul_add, Finset.sum_add_distrib]
  | mul_X p k hp =>
    have hX : pderiv (s, (a, t)) (Formalism.GradedWeylDivisibility.blockAct K V (X k)) =
        if k.1 = s ∧ k.2.2 = t then C (V s k.2.1 a) else 0 := by
      rw [blockAct_X, map_sum]
      by_cases hk : k.1 = s ∧ k.2.2 = t
      · obtain ⟨h1, h2⟩ := hk
        subst h1; subst h2
        rw [if_pos ⟨rfl, rfl⟩, Finset.sum_eq_single a]
        · simp [pderiv_X]
        · intro b _ hb
          rw [Derivation.leibniz, pderiv_C, pderiv_X_of_ne (by
            intro h; exact hb (by simpa using congrArg (fun z : ι × Fin n × Fin n => z.2.1) h))]
          simp
        · simp
      · rw [if_neg hk]
        refine Finset.sum_eq_zero fun b _ => ?_
        rw [Derivation.leibniz, pderiv_C, pderiv_X_of_ne (by
          intro h
          apply hk
          exact ⟨by simpa using congrArg (fun z : ι × Fin n × Fin n => z.1) h,
            by simpa using congrArg (fun z : ι × Fin n × Fin n => z.2.2) h⟩)]
        simp
    rw [map_mul, Derivation.leibniz, hX, hp, smul_eq_mul, smul_eq_mul]
    simp_rw [Derivation.leibniz, smul_eq_mul, map_add, map_mul, mul_add, Finset.sum_add_distrib]
    congr 1
    · by_cases hk : k.1 = s ∧ k.2.2 = t
      · obtain ⟨h1, h2⟩ := hk
        subst h1; subst h2
        rw [if_pos ⟨rfl, rfl⟩, Finset.sum_eq_single k.2.1]
        · rw [show ((k.1, (k.2.1, k.2.2)) : ι × Fin n × Fin n) = k from rfl, pderiv_X_self, map_one]; ring
        · intro b _ hb
          rw [pderiv_X_of_ne (by
            intro h; exact hb (by simpa using (congrArg (fun z : ι × Fin n × Fin n => z.2.1) h).symm))]
          simp
        · simp
      · rw [if_neg hk, mul_zero]
        symm
        refine Finset.sum_eq_zero fun b _ => ?_
        rw [pderiv_X_of_ne (by
          intro h
          apply hk
          exact ⟨by simpa using congrArg (fun z : ι × Fin n × Fin n => z.1) h,
            by simpa using congrArg (fun z : ι × Fin n × Fin n => z.2.2) h⟩)]
        simp
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring

theorem fockL_blockAct_adj (U : ι → Matrix (Fin n) (Fin n) K) (F F' : Pol K ι n) :
    fockL (Formalism.GradedWeylDivisibility.blockAct K U F) F' = fockL F (Formalism.GradedWeylDivisibility.blockAct K (fun τ => (U τ)ᴴ) F') := by
  classical
  induction F using MvPolynomial.induction_on generalizing F' with
  | C a => rw [algHom_C, algebraMap_eq, fockL_C_left, fockL_C_left, constantCoeff_blockAct]
  | add p q hp hq => rw [map_add, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, hp, hq]
  | mul_X p v hp =>
    have e1 : Formalism.GradedWeylDivisibility.blockAct K U (p * X v) =
        ∑ b : Fin n, U v.1 v.2.1 b • (X (v.1, (b, v.2.2)) * Formalism.GradedWeylDivisibility.blockAct K U p) := by
      rw [map_mul, blockAct_X, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_eq_C_mul]; ring
    rw [e1, map_sum, LinearMap.sum_apply]
    simp_rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, fockL_X_pderiv, hp]
    rw [mul_comm p, fockL_X_pderiv, show v = (v.1, (v.2.1, v.2.2)) from rfl, pderiv_blockAct, map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← smul_eq_C_mul, map_smul, Matrix.conjTranspose_apply, starRingEnd_apply]

end Adj

theorem fockSAdj : FockSAdj := by
  intro K _ _ ι _ n U F F'
  exact fockL_blockAct_adj U F F'

theorem pairP_apply {K : Type} [Field K] [StarRing K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (G : ι → Matrix (Fin n) (Fin n) K) (F F' : Pol K ι n) :
    pairP lam G F F' = gramTw lam G / extNorm K lam * fockL F (Formalism.GradedWeylDivisibility.blockAct K (fun τ => (G τ)ᵀ) F') := rfl

theorem detTw_eq {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (g : ι → GL (Fin n) K) :
    detTwK lam g = ∏ τ, ((g τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det ^ (lam τ).detShift := by
  unfold detTwK detPow
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [Units.val_zpow_eq_zpow_val]
  rfl

theorem pairTransport : PairTransport := by
  intro K _ _ ι _ n lam G g g' F F'
  have hs : gramTw lam (fun τ => (g τ : Matrix (Fin n) (Fin n) K)ᴴ * G τ * (g' τ : Matrix (Fin n) (Fin n) K)) =
      star (detTwK lam g) * gramTw lam G * detTwK lam g' := by
    rw [detTw_eq, detTw_eq, star_prod]
    unfold gramTw
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, mul_zpow, mul_zpow, star_zpow₀]
  have hb : Formalism.GradedWeylDivisibility.blockAct K (fun τ => (((g τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ)ᴴ)
        (Formalism.GradedWeylDivisibility.blockAct K (fun τ => (G τ)ᵀ) (trAct g' F')) =
      Formalism.GradedWeylDivisibility.blockAct K
        (fun τ => ((g τ : Matrix (Fin n) (Fin n) K)ᴴ * G τ * (g' τ : Matrix (Fin n) (Fin n) K))ᵀ) F' := by
    unfold trAct
    rw [← AlgHom.comp_apply, ← AlgHom.comp_apply, blockAct_comp, blockAct_comp]
    congr 2
    funext τ
    rw [Matrix.transpose_mul, Matrix.transpose_mul, conjTranspose_transpose']
  rw [pairP_apply, pairP_apply, hs]
  simp only [actP, LinearMap.smul_apply, AlgHom.toLinearMap_apply, LinearMap.map_smulₛₗ, map_smul, smul_eq_mul,
    starRingEnd_apply]
  unfold trAct at hb ⊢
  rw [fockL_blockAct_adj, hb]
  ring

theorem pairK_apply {K : Type} [Field K] [StarRing K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (G : ι → Matrix (Fin n) (Fin n) K) (x y : VV K lam) : pairK lam G x y = pairP lam G x.1 y.1 :=
  LinearMap.domRestrict₁₂_apply _ _ _ x y

theorem rhoK_coe {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (g : ι → GL (Fin n) K) (x : VV K lam) : ((rhoK lam g x : VV K lam) : Pol K ι n) = actP lam g x.1 := rfl

theorem pairInv : PairInv := by
  intro K _ _ ι _ n lam G g hg x y
  rw [pairK_apply, pairK_apply, rhoK_coe, rhoK_coe, pairTransport K ι n lam G g g x.1 y.1]
  simp only [hg]

theorem pairSymm : PairSymm := by
  intro K _ _ ι _ n lam G hG
  have hc : star (gramTw lam G / extNorm K lam) = gramTw lam G / extNorm K lam := by
    have h1 : star (gramTw lam G) = gramTw lam G := by
      unfold gramTw
      rw [star_prod]
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [star_zpow₀, ← Matrix.det_conjTranspose, hG]
    have h2 : star (extNorm K lam) = extNorm K lam := by
      unfold extNorm
      rw [star_prod]
      refine Finset.prod_congr rfl fun τ _ => ?_
      exact (fockSHerm K _ _ _).symm
    rw [star_div₀, h1, h2]
  have e : (fun τ => ((G τ)ᵀ)ᴴ) = fun τ => (G τ)ᵀ := by
    funext τ
    rw [conjTranspose_transpose', hG]
  rw [LinearMap.isSymm_def]
  intro x y
  rw [pairK_apply, pairK_apply, pairP_apply, pairP_apply, starRingEnd_apply, star_mul', hc, ← fockL_symm,
    fockL_blockAct_adj, e]

theorem pairExtremal_of : FockSTen → ExtNormPos → PairExtremal := by
  intro hT hP K _ _ _ ι _ n lam G B hB
  rw [pairTransport K ι n lam G B B]
  simp only [hB]
  obtain ⟨q, hq, hq'⟩ := hP K ι n lam
  have hne : extNorm K lam ≠ 0 := by
    rw [hq']
    simpa using hq.ne'
  have h1 : gramTw lam (fun _ : ι => (1 : Matrix (Fin n) (Fin n) K)) = 1 := by
    unfold gramTw
    simp
  rw [pairP_apply, h1]
  simp only [Matrix.transpose_one]
  rw [blockAct_one, AlgHom.id_apply, fockL_apply, hT K ι n]
  exact div_mul_cancel₀ 1 hne |>.trans rfl |> fun h => by simpa [extNorm] using h

section Equiv

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ}

theorem colLat_mul (g B : GL (Fin n) K) : colLat (g * B) = gLat g (colLat B) := by
  unfold colLat gLat
  rw [Submodule.map_span, ← Set.range_comp]
  congr 2

theorem localization_gLat (w : HeightOneSpectrum (𝓞 K)) (g : GL (Fin n) K) (M : Submodule (𝓞 K) (Fin n → K)) :
    Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (gLat g M) = gLat g (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M) := by
  ext x
  constructor
  · rintro ⟨s, hs, y, hy, hyx⟩
    have hyx' : (g : Matrix (Fin n) (Fin n) K) *ᵥ y = s • x := hyx
    refine ⟨((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x, ⟨s, hs, ?_⟩, ?_⟩
    · have : s • (((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x) = y := by
        rw [← Matrix.mulVec_smul, ← hyx', Matrix.mulVec_mulVec]
        simp
      rw [this]
      exact hy
    · show (g : Matrix (Fin n) (Fin n) K) *ᵥ (((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x) = x
      rw [Matrix.mulVec_mulVec]
      simp
  · rintro ⟨y, ⟨s, hs, hy⟩, rfl⟩
    refine ⟨s, hs, s • y, hy, ?_⟩
    show (g : Matrix (Fin n) (Fin n) K) *ᵥ (s • y) = s • ((g : Matrix (Fin n) (Fin n) K) *ᵥ y)
    rw [Matrix.mulVec_smul]

theorem gLat_injective (g : GL (Fin n) K) : Function.Injective (gLat (K := K) g) := by
  refine Submodule.map_injective_of_injective ?_
  intro x y hxy
  have h : (g : Matrix (Fin n) (Fin n) K) *ᵥ x = (g : Matrix (Fin n) (Fin n) K) *ᵥ y := hxy
  have := congrArg (fun z => ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ z) h
  simpa [Matrix.mulVec_mulVec] using this

theorem isBasisAt_gLat (w : HeightOneSpectrum (𝓞 K)) (g B : GL (Fin n) K) (M : Submodule (𝓞 K) (Fin n → K)) :
    IsBasisAt w (gLat g M) (g * B) ↔ IsBasisAt w M B := by
  unfold IsBasisAt
  rw [colLat_mul, localization_gLat, localization_gLat]
  exact (gLat_injective g).eq_iff

omit [NumberField K] in
theorem polyAction_mul (lam : ι → DomWeight n) (g h : ι → GL (Fin n) K) (F : Pol K ι n) :
    actP lam (g * h) F = actP lam g (actP lam h F) :=
  congrArg (fun φ : Module.End K (Pol K ι n) => φ F) ((rhoP lam).map_mul g h)

omit [NumberField K] in
theorem polyAction_one₂ (lam : ι → DomWeight n) (F : Pol K ι n) : actP lam 1 F = F :=
  congrArg (fun φ : Module.End K (Pol K ι n) => φ F) (rhoP lam).map_one

theorem mem_transLat_gLat (lam : ι → DomWeight n) (T : Submodule (𝓞 K) (Pol K ι n))
    (M : ι → Submodule (𝓞 K) (Fin n → K)) (g : ι → GL (Fin n) K) (F : Pol K ι n) :
    F ∈ transLat lam T (fun τ => gLat (g τ) (M τ)) ↔ actP lam g⁻¹ F ∈ transLat lam T M := by
  simp only [transLat, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars]
  constructor
  · intro h w B hB
    have h1 := h w (g * B) fun τ => (isBasisAt_gLat w (g τ) (B τ) (M τ)).mpr (hB τ)
    rwa [mul_inv_rev, polyAction_mul] at h1
  · intro h w B hB
    have h1 := h w (g⁻¹ * B) fun τ => (isBasisAt_gLat w (g τ) ((g⁻¹ * B) τ) (M τ)).mp (by
      have : g τ * (g⁻¹ * B) τ = B τ := by simp
      rw [this]
      exact hB τ)
    rwa [← polyAction_mul, mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel, mul_one] at h1

theorem transLat_gLat (lam : ι → DomWeight n) (T : Submodule (𝓞 K) (Pol K ι n))
    (M : ι → Submodule (𝓞 K) (Fin n → K)) (g : ι → GL (Fin n) K) :
    transLat lam T (fun τ => gLat (g τ) (M τ)) = (transLat lam T M).map ((actP lam g).restrictScalars (𝓞 K)) := by
  ext F
  rw [mem_transLat_gLat, Submodule.mem_map]
  constructor
  · intro h
    refine ⟨_, h, ?_⟩
    show actP lam g (actP lam g⁻¹ F) = F
    rw [← polyAction_mul, mul_inv_cancel, polyAction_one₂]
  · rintro ⟨y, hy, rfl⟩
    show actP lam g⁻¹ (actP lam g y) ∈ _
    rw [← polyAction_mul, inv_mul_cancel, polyAction_one₂]
    exact hy

end Equiv

theorem nabDelEquiv : NabDelEquiv := by
  intro K _ _ ι _ n lam M g
  exact ⟨transLat_gLat lam _ M g, transLat_gLat lam _ M g⟩

theorem fockSQ : FockSQ := by
  intro K _ _ _ σ f g
  have hinj : Function.Injective (algebraMap ℚ K) := (algebraMap ℚ K).injective
  unfold fockS Formalism.GradedWeylDivisibility.fockQ mfact
  rw [support_map_of_injective _ hinj, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [coeff_map, map_mul, map_natCast, eq_ratCast, star_ratCast]

theorem map_extremal {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (n : ℕ) (lam : DomWeight n) :
    map φ (extremal R n lam) = extremal S n lam := by
  unfold extremal Formalism.GradedWeylDivisibility.hw Formalism.GradedWeylDivisibility.lpMinor
  rw [map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_pow, RingHom.map_det]
  congr 2
  ext p q
  simp

theorem extNormPos : ExtNormPos := by
  intro K _ _ _ ι _ n lam
  refine ⟨∏ τ, Formalism.GradedWeylDivisibility.fockQ (extremal ℚ n (lam τ)) (extremal ℚ n (lam τ)), ?_, ?_⟩
  · refine Finset.prod_pos fun τ _ => ?_
    exact (Formalism.GradedWeylDivisibility.fockQPos _ _ (extremal ℚ n (lam τ))).2 (Formalism.GradedWeylDivisibility.hwNe ℚ n n le_rfl _)
  · unfold extNorm
    rw [map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← fockSQ K, map_extremal]

section Checks

variable {K : Type} [Field K]

def lamVec : DomWeight 2 where
  w := ![1, 0]
  anti := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all

def vecP (v : Fin 2 → K) : Pol K Unit 2 := ∑ a : Fin 2, C (v a) * X ((), (a, 0))

theorem lamVec_detShift : lamVec.detShift = 0 := by
  simp [DomWeight.detShift, lamVec]

theorem lamVec_natW : lamVec.natW = ![1, 0] := by
  funext i
  fin_cases i <;> simp only [DomWeight.natW, lamVec_detShift] <;> simp [lamVec]

theorem extremal_lamVec : extremal K 2 lamVec = X (0, 0) := by
  unfold extremal Formalism.GradedWeylDivisibility.hw
  rw [lamVec_natW, Fin.prod_univ_two]
  simp [Formalism.GradedWeylDivisibility.nuNext, Formalism.GradedWeylDivisibility.lpMinor]

variable [StarRing K]

theorem fockL_X_X {σ : Type} [DecidableEq σ] (i j : σ) :
    fockL (X i : MvPolynomial σ K) (X j) = if i = j then 1 else 0 := by
  have h := fockL_X_pderiv (K := K) i 1 (X j)
  rw [mul_one] at h
  rw [h, ← C_1, fockL_C_left, pderiv_X]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij, Ne.symm hij]

theorem pairP_vecP (G : Unit → Matrix (Fin 2) (Fin 2) K) (v w : Fin 2 → K) :
    pairP (fun _ => lamVec) G (vecP v) (vecP w) = star v ⬝ᵥ (G () *ᵥ w) := by
  have h1 : gramTw (fun _ : Unit => lamVec) G = 1 := by simp [gramTw, lamVec_detShift]
  have h2 : extNorm K (fun _ : Unit => lamVec) = 1 := by
    simp only [extNorm, Finset.univ_unique, Finset.prod_singleton, extremal_lamVec]
    rw [← fockL_apply, fockL_X_X, if_pos rfl]
  rw [pairP_apply, h1, h2]
  simp only [vecP, blockAct_X, Fin.sum_univ_two, Matrix.transpose_apply,
    ← smul_eq_C_mul, map_add, map_smul, LinearMap.map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, fockL_X_X,
    smul_add, smul_smul]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  simp only [starRingEnd_apply]
  ring

def lamChar (e : ℤ) : DomWeight 1 where
  w := fun _ => e
  anti := fun _ _ _ => le_rfl

theorem pairP_char (e : ℤ) (G : Unit → Matrix (Fin 1) (Fin 1) K) :
    pairP (fun _ => lamChar e) G (1 : Pol K Unit 1) 1 = G () 0 0 ^ e := by
  have h0 : (lamChar e).natW = fun _ => 0 := by
    funext i
    simp [DomWeight.natW, DomWeight.detShift, lamChar]
  have h2 : extNorm K (fun _ : Unit => lamChar e) = 1 := by
    simp only [extNorm, Finset.univ_unique, Finset.prod_singleton, extremal, Formalism.GradedWeylDivisibility.hw, h0]
    simp only [Formalism.GradedWeylDivisibility.nuNext]
    simp only [Nat.sub_self, dite_eq_ite, ite_self, pow_zero]
    rw [← fockL_apply, ← C_1, fockL_C_left]
    simp
  have hb : Formalism.GradedWeylDivisibility.blockAct K (fun τ => (G τ)ᵀ) (1 : Pol K Unit 1) = 1 := map_one _
  rw [pairP_apply, h2, hb, ← C_1, fockL_C_left]
  simp [gramTw, lamChar, DomWeight.detShift]

end Checks

section RankOne

variable {K : Type} [Field K] [NumberField K]

theorem colLat_one_eq (B : GL (Fin 1) K) :
    colLat B = Submodule.span (𝓞 K) {fun _ : Fin 1 => (B : Matrix (Fin 1) (Fin 1) K) 0 0} := by
  unfold colLat
  congr 1
  ext x
  simp only [Set.mem_range, Set.mem_singleton_iff]
  constructor
  · rintro ⟨j, rfl⟩
    funext a
    rw [Subsingleton.elim a 0, Subsingleton.elim j 0]
  · rintro rfl
    refine ⟨0, ?_⟩
    funext a
    rw [Subsingleton.elim a 0]

end RankOne

end Formalism.L2.DIV
