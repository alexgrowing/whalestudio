import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.IntBasisAlt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.JointApproxOfMem

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal

namespace UpperTheory.Gal.ClosedPhiFromClosedTrace

def IsOp2 {l : ℕ} [Fact l.Prime] {K : FinExt l} {d : ℕ} (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (n₁ n₂ : ℕ) (s : Per.Bcris l)
    (V : Matrix (Fin d) (Fin d) (Per.Bcris l)) : Prop :=
  ∃ U, IsPerU ρ U ∧ V * U.map ⇑(Per.φB l ^ n₂) = s • U.map ⇑(Per.φB l ^ n₁)

def LinkOp2 : Prop :=
  ∀ (R : Type) [CommRing R] (π s : R) (d d' : ℕ) (W Z Zs : Matrix (Fin d) (Fin d) R)
    (W₁ Z₁ Zs₁ : Matrix (Fin d') (Fin d') R) (Pm R₀ : Matrix (Fin d) (Fin d') R),
    Zs * Z = s • (1 : Matrix (Fin d) (Fin d) R) → Z₁ * Zs₁ = s • (1 : Matrix (Fin d') (Fin d') R) →
    (∀ i j, π ∣ (Pm * Z₁ - Z * R₀) i j) → (∀ i j, π ∣ (Pm * W₁ - W * R₀) i j) →
    ∀ i j, π ∣ ((s • (W * Zs)) * Pm - Pm * (s • (W₁ * Zs₁))) i j

def OpOne2 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (τ₁ : Per.Acris l), IsUnit (iB l τ₁) → ∀ (K : FinExt l) (N k n₁ n₂ d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l])
    (y y' Q Q' : Matrix (Fin d) (Fin d) (Per.Acris l)) (U : Matrix (Fin d) (Fin d) (Per.Bcris l)),
    y * y' = τ₁ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) →
    Q * Q' = (l : Per.Acris l) ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) →
    IsPerU ρ U → iB l τ₁ ^ N • U = (y * Q).map (iB l) →
    (y * Q) * (Q' * y') = (τ₁ ^ (2 * N) * (l : Per.Acris l) ^ (2 * k)) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) ∧
    (Q' * y') * (y * Q) = (τ₁ ^ (2 * N) * (l : Per.Acris l) ^ (2 * k)) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) ∧
    IsUnit (iB l ((phiA l ^ n₂) τ₁ ^ (3 * N) * (l : Per.Acris l) ^ (4 * k) * (phiA l ^ n₁) τ₁ ^ N)) ∧
    IsOp2 ρ n₁ n₂ (iB l ((phiA l ^ n₂) τ₁ ^ (3 * N) * (l : Per.Acris l) ^ (4 * k) * (phiA l ^ n₁) τ₁ ^ N))
      (((phiA l ^ n₂) (τ₁ ^ (2 * N) * (l : Per.Acris l) ^ (2 * k)) •
        ((y * Q).map ⇑(phiA l ^ n₁) * (Q' * y').map ⇑(phiA l ^ n₂))).map (iB l))

def LinkZ : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (N M : ℕ), ∃ n : ℕ, ∀ (k d d' : ℕ)
    (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (ρ' : ↥(GK K) → Matrix (Fin d') (Fin d') ℤ_[l]) (F : Frame bk N d ρ) (F' : Frame bk N d' ρ')
    (Y : Matrix (Fin d) (Fin d) (Ainf l)) (Y₁ : Matrix (Fin d') (Fin d') (Ainf l)), Y.map (inclW l) = inclW l τ ^ N • F.T →
    Y₁.map (inclW l) = inclW l τ ^ N • F'.T → ∀ (Q Q' : Matrix (Fin d) (Fin d) (Per.Acris l)) (Q₁ Q₁' : Matrix (Fin d') (Fin d') (Per.Acris l)),
    IsSecQ bk N k F.A Q Q' → IsSecQ bk N k F'.A Q₁ Q₁' → ∀ (Pi : Matrix (Fin d) (Fin d') ℤ_[l]) (R : Matrix (Fin d) (Fin d') bk.S),
    (∀ i j, (l : WCb l) ^ n ∣ (zW Pi * F'.T - F.T * R.map bk.evW) i j) →
    ∀ i j, (l : Per.Acris l) ^ M ∣ (Pi.map (zC l) * (Y₁.map (fI l) * Q₁) - (Y.map (fI l) * Q) * R.map (f0 bk)) i j

def OpEx2 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ →
    ∀ (P : LocPrime l) (AI : LocAinf l P) (_ : LocTied l P AI) (n₁ n₂ : ℕ), FixUr K n₁ → FixUr K n₂ →
    ∀ (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ m, Frame bk N (tw.d' m) fun g => (tw.ρ' m g).val)
      (F₀ : Frame bk N d fun g => (ρ g).val) (r : ℕ), (∀ m, (F m).IsCr) → F₀.IsCr →
      (∀ n', ∃ m, n' ≤ m ∧ Link bk F₀.T (F m).T (tw.Pi m) n' r) →
    ∃ (s : Per.Acris l) (V : Matrix (Fin d) (Fin d) (Per.Acris l)) (V' : ∀ m, Matrix (Fin (tw.d' m)) (Fin (tw.d' m)) (Per.Acris l)),
      IsUnit (iB l s) ∧ IsOp2 ρ n₁ n₂ (iB l s) (V.map (iB l)) ∧ (∀ m, IsOp2 (tw.ρ' m) n₁ n₂ (iB l s) ((V' m).map (iB l))) ∧
      ∀ M, ∃ m, M ≤ m ∧ ∀ i j, (l : Per.Acris l) ^ M ∣ (V * (tw.Pi m).map (zC l) - (tw.Pi m).map (zC l) * V' m) i j

def FixOf : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O), Induces Bw → ∀ (g : ↥(Weil h)), FixUr Bw.Kw (alpha l g).natAbs

def WeilPhi2 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (g : ↥(Weil h)) (n₁ n₂ : ℕ), alpha l g = (n₂ : ℤ) - n₁ →
    ∀ (L : FinExt l) (a : ℕ) (R : Representation ↥L.1 ↥(GK Bw.Kw) (Fin a → ↥L.1)) [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P R)]
      (m : (Fin a → ↥L.1) ⊗[ℚ_[l]] Bst P), m ∈ Dst P R → ∃ x : ↥(Dpst P R),
      (x : (Fin a → ↥L.1) ⊗[ℚ_[l]] Bst P) = (phiV P ↥L.1 (Fin a → ↥L.1) ^ n₂) m ∧
      ((weilD Bw h P R g x : ↥(Dpst P R)) : (Fin a → ↥L.1) ⊗[ℚ_[l]] Bst P) = (phiV P ↥L.1 (Fin a → ↥L.1) ^ n₁) m

def TieRep2 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : Om l ≃+* ℂ) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Induces Bw) (g : ↥(Weil h)) (n₁ n₂ : ℕ), alpha l g = (n₂ : ℤ) - n₁ →
    ∀ (L : FinExt l) (a d : ℕ) (R : Representation ↥L.1 ↥(GK Bw.Kw) (Fin a → ↥L.1)) [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P R)],
    Module.finrank ℂ (WDSpace P ι R) = a → ∀ (ρ : ↥(GK Bw.Kw) →* GL (Fin d) ℤ_[l]) (b : Fin d → Matrix (Fin a) (Fin a) ↥L.1)
      (e : Fin d → ℤ_[l]), (∀ g j (k : Fin a), R g (fun i => b j i k) = ∑ i, ((ρ g).val i j : ℚ_[l]) • fun i' => b i i' k) →
      ∑ i, (e i : ℚ_[l]) • b i = 1 → ∀ (s : Per.Bcris l) (V : Matrix (Fin d) (Fin d) (Per.Bcris l)), IsOp2 ρ n₁ n₂ s V →
      IsTr (uB T) s (V *ᵥ fun i => Per.zB l (e i)) (fun i => (((b i).trace : ↥L.1) : Om l))
        (ι.symm (LinearMap.trace ℂ (WDSpace P ι R) (wdRho P ι Bw h hj R g)))

def Tie2 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : Om l ≃+* ℂ) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Induces Bw) (g : ↥(Weil h)) (n₁ n₂ : ℕ), alpha l g = (n₂ : ℤ) - n₁ →
    ∀ (a d : ℕ) (r : ↥(Dec (F := E) A) →* GL (Fin a) (Om l)), IsCrysAt P Bw r →
    ∀ (ρ : ↥(GK Bw.Kw) →* GL (Fin d) ℤ_[l]) (b : Fin d → Matrix (Fin a) (Fin a) (Om l)) (e : Fin d → ℤ_[l]),
      Reads ρ (r.comp Bw.e.symm.toMonoidHom) b e → ∀ (s : Per.Bcris l) (V : Matrix (Fin d) (Fin d) (Per.Bcris l)), IsOp2 ρ n₁ n₂ s V →
      IsTr (uB T) s (V *ᵥ fun i => Per.zB l (e i)) (fun i => (b i).trace) (wdTr P ι Bw h hj r g)

def ClosedTr : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Om l ≃+* ℂ)
    (a : ℕ), 1 ≤ a → ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Induces Bw)
      (J : (E →+* Om l) → Multiset ℤ) (r : Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Om l)), Continuous r → IsSSRep r →
    ∀ (C : Set (Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Om l))) (g : ↥(Weil h)) (θ : Om l),
      JointApprox r C (fun ρ => wdTr P ι Bw h hj (ρ.comp (Dec (F := E) A).subtype) g) θ →
      (∀ ρ ∈ C, Continuous ρ ∧ GlobalTheory.GalOfCusp.IsSstAt P Bw (ρ.comp (Dec (F := E) A).subtype) ∧
        IsCrysAt P Bw (ρ.comp (Dec (F := E) A).subtype) ∧
        ∀ (τ : E →+* Om l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
          IsJumpsAt P Bw (ρ.comp (Dec (F := E) A).subtype) τ (J τ)) →
      wdTr P ι Bw h hj (r.comp (Dec (F := E) A).subtype) g = θ

def PowTr : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (x : WD h) (σ : ↥(Weil h)) (n : ℕ),
    GlobalTheory.CongPhi.phiSum x σ n = -(x.charPol (σ ^ n)).nextCoeff

end UpperTheory.Gal.ClosedPhiFromClosedTrace

end
