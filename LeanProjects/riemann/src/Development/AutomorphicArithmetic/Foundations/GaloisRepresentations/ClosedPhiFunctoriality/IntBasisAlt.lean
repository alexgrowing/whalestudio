import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.JointApproxOfMem

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal

namespace UpperTheory.Gal.ClosedPhiFromClosedTrace

def CoverJ : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (a : ℕ) (L₀ : FinExt l)
    (r : Γ →* GL (Fin a) (Om l)), Continuous r → Formalism.MainNotions.N.IsSSRep r → ∀ Cl : Set (Γ →* GL (Fin a) (Om l)), (∀ ρ ∈ Cl, Continuous ρ) →
    ∀ (p : (Γ →* GL (Fin a) (Om l)) → Om l) (θ : Om l), JointApprox r Cl p θ →
    ∃ Cv : Cover L₀ r Cl, ∀ n, ‖θ - ∑ k, (Cv.lay n).c k * p ((Cv.lay n).rep k)‖ ≤ ((l : ℝ) ^ n)⁻¹

def CoreU : Prop :=
  ∀ (R : Type) [CommRing R] (d l q N : ℕ), (∀ x : R, (l : R) * x = 0 → x = 0) → IsAdicComplete (Ideal.span {(l : R)}) R →
    ∀ (φ : R →+* R) (u : R), φ u = u ^ q → 0 < q → ∀ (α α' β β' Γ : Matrix (Fin d) (Fin d) R),
    α * α' = ((l : R) ^ (2 * N)) • (1 : Matrix (Fin d) (Fin d) R) → β * β' = ((l : R) ^ (2 * N)) • (1 : Matrix (Fin d) (Fin d) R) →
    (l : R) • (α - β) = u ^ q • Γ → ∀ n₀ : ℕ, (∀ n, n₀ ≤ n → (l : R) ^ ((2 * N + 1) * (n + 1) + 1) ∣ u ^ (q ^ (n + 1) - 1)) →
    ∃ Q Q' : Matrix (Fin d) (Fin d) R, Q * Q' = (l : R) ^ (2 * (n₀ + 2 * N * n₀)) • (1 : Matrix (Fin d) (Fin d) R) ∧
      (∃ Y, Q - (l : R) ^ (n₀ + 2 * N * n₀) • (1 : Matrix (Fin d) (Fin d) R) = u • Y) ∧
      (∃ Y, Q' - (l : R) ^ (n₀ + 2 * N * n₀) • (1 : Matrix (Fin d) (Fin d) R) = u • Y) ∧ Q * β = α * Q.map φ

def SecU : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (N : ℕ), ∃ k : ℕ, ∀ (d : ℕ) (A A' : Matrix (Fin d) (Fin d) bk.S),
    A * A' = bk.E ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) bk.S) → ∃ Q Q', IsSecQ bk N k A Q Q'

def InvQ : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (N k d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l])
    (F : Frame bk N d fun g => (ρ g).val), F.IsCr → ∀ Q Q', IsSecQ bk N k F.A Q Q' →
    ∀ g : ↥(GK K), (F.ε g).map (fI l) * Q.map (sigA (g : GQ l)) = Q

def InvU : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → IsUnit (iB l (fI l τ)) ∧
    ∀ (N k d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (F : Frame bk N d fun g => (ρ g).val) (Y Y' : Matrix (Fin d) (Fin d) (Ainf l))
      (Q Q' : Matrix (Fin d) (Fin d) (Per.Acris l)), Y.map (inclW l) = inclW l τ ^ N • F.T →
      Y * Y' = τ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Ainf l)) →
      Q * Q' = (l : Per.Acris l) ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) →
      (∀ g : ↥(GK K), (F.ε g).map (fI l) * Q.map (sigA (g : GQ l)) = Q) →
      ∃ U, IsPerU ρ U ∧ iB l (fI l τ) ^ N • U = (Y.map (fI l) * Q).map (iB l)

def ZeroAp : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (c M : ℕ), ∃ n : ℕ, ∀ (d d' : ℕ) (D : Matrix (Fin d) (Fin d') (Per.Acris l))
    (F : Matrix (Fin d) (Fin d) (Per.Acris l)) (F' : Matrix (Fin d') (Fin d') (Per.Acris l)), (∀ i j, uC bk ∣ D i j) →
    (∀ i j, (l : Per.Acris l) ^ n ∣ ((l : Per.Acris l) ^ c • D - F * D.map (phiA l) * F') i j) → ∀ i j, (l : Per.Acris l) ^ M ∣ D i j

def LinkA : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (N d d' n : ℕ)
    (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (ρ' : ↥(GK K) → Matrix (Fin d') (Fin d') ℤ_[l]) (F : Frame bk N d ρ) (F' : Frame bk N d' ρ')
    (Y : Matrix (Fin d) (Fin d) (Ainf l)) (Y' : Matrix (Fin d') (Fin d') (Ainf l)), Y.map (inclW l) = inclW l τ ^ N • F.T →
    Y'.map (inclW l) = inclW l τ ^ N • F'.T → ∀ (Pi : Matrix (Fin d) (Fin d') ℤ_[l]) (R : Matrix (Fin d) (Fin d') bk.S),
    (∀ i j, (l : WCb l) ^ n ∣ (zW Pi * F'.T - F.T * R.map bk.evW) i j) →
    (∀ i j, (l : Ainf l) ^ n ∣ (Pi.map (Per.zA l) * Y' - Y * R.map bk.ev) i j) ∧
      ∀ i j, (l : bk.S) ^ n ∣ (R * F'.A - F.A * R.map (frobS l bk.a)) i j

def LinkRec : Prop :=
  ∀ (R : Type) [CommRing R] (φ : R →+* R) (lr π : R) (v w : Rˣ) (N d d' : ℕ) (α β Q : Matrix (Fin d) (Fin d) R)
    (α₁ β₁ β₁' Q₁ : Matrix (Fin d') (Fin d') R) (R₁ R₀ : Matrix (Fin d) (Fin d') R),
    β₁ * β₁' = (lr * w) ^ (2 * N) • (1 : Matrix (Fin d') (Fin d') R) →
    (lr * v) ^ N • (Q * β) = (lr * w) ^ N • (α * Q.map φ) → (lr * v) ^ N • (Q₁ * β₁) = (lr * w) ^ N • (α₁ * Q₁.map φ) →
    (∀ i j, π ∣ (R₁ * α₁ - α * R₁.map φ) i j) → (∀ i j, π ∣ (R₀ * β₁ - β * R₀.map φ) i j) →
    ∃ (F : Matrix (Fin d) (Fin d) R) (F' : Matrix (Fin d') (Fin d') R),
      ∀ i j, π ∣ (lr ^ (3 * N) • (R₁ * Q₁ - Q * R₀) - F * (R₁ * Q₁ - Q * R₀).map φ * F') i j

def LinkQ : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (N M : ℕ), ∃ n : ℕ, ∀ (k d d' : ℕ) (A : Matrix (Fin d) (Fin d) bk.S)
    (A₁ A₁' : Matrix (Fin d') (Fin d') bk.S) (Q Q' : Matrix (Fin d) (Fin d) (Per.Acris l)) (Q₁ Q₁' : Matrix (Fin d') (Fin d') (Per.Acris l))
    (R : Matrix (Fin d) (Fin d') bk.S), A₁ * A₁' = bk.E ^ (2 * N) • (1 : Matrix (Fin d') (Fin d') bk.S) →
    IsSecQ bk N k A Q Q' → IsSecQ bk N k A₁ Q₁ Q₁' → (∀ i j, (l : bk.S) ^ n ∣ (R * A₁ - A * R.map (frobS l bk.a)) i j) →
    ∀ i j, (l : Per.Acris l) ^ M ∣ (R.map (fA bk) * Q₁ - Q * R.map (f0 bk)) i j

def LinkOp : Prop :=
  ∀ (R : Type) [CommRing R] (φ : R →+* R) (π s : R), φ π = π → ∀ (d d' : ℕ) (Z Zs : Matrix (Fin d) (Fin d) R)
    (Z₁ Zs₁ : Matrix (Fin d') (Fin d') R) (Pm R₀ : Matrix (Fin d) (Fin d') R), Pm.map φ = Pm → R₀.map φ = R₀ →
    Zs * Z = s • (1 : Matrix (Fin d) (Fin d) R) → Z₁ * Zs₁ = s • (1 : Matrix (Fin d') (Fin d') R) →
    (∀ i j, π ∣ (Pm * Z₁ - Z * R₀) i j) →
    ∀ i j, π ∣ ((s • (Z.map φ * Zs)) * Pm - Pm * (s • (Z₁.map φ * Zs₁))) i j

def FixW : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (P : LocPrime l) (AI : LocAinf l P) (_ : LocTied l P AI) (n : ℕ), FixUr K n →
    ∀ s : bk.S, (phiA l ^ n) (f0 bk s) = f0 bk s

def OpOne : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (τ₁ : Per.Acris l), IsUnit (iB l τ₁) → ∀ (K : FinExt l) (N k n d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l])
    (y y' Q Q' : Matrix (Fin d) (Fin d) (Per.Acris l)) (U : Matrix (Fin d) (Fin d) (Per.Bcris l)),
    y * y' = τ₁ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) →
    Q * Q' = (l : Per.Acris l) ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) →
    IsPerU ρ U → iB l τ₁ ^ N • U = (y * Q).map (iB l) →
    (y * Q) * (Q' * y') = (τ₁ ^ (2 * N) * (l : Per.Acris l) ^ (2 * k)) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) ∧
    (Q' * y') * (y * Q) = (τ₁ ^ (2 * N) * (l : Per.Acris l) ^ (2 * k)) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) ∧
    IsUnit (iB l (τ₁ ^ (3 * N) * (l : Per.Acris l) ^ (4 * k) * (phiA l ^ n) τ₁ ^ N)) ∧
    IsOp ρ n (iB l (τ₁ ^ (3 * N) * (l : Per.Acris l) ^ (4 * k) * (phiA l ^ n) τ₁ ^ N))
      (((τ₁ ^ (2 * N) * (l : Per.Acris l) ^ (2 * k)) • ((y * Q).map ⇑(phiA l ^ n) * (Q' * y'))).map (iB l))

def OpEx : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ →
    ∀ (P : LocPrime l) (AI : LocAinf l P) (_ : LocTied l P AI) (n : ℕ), FixUr K n →
    ∀ (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ m, Frame bk N (tw.d' m) fun g => (tw.ρ' m g).val)
      (F₀ : Frame bk N d fun g => (ρ g).val) (r : ℕ), (∀ m, (F m).IsCr) → F₀.IsCr →
      (∀ n', ∃ m, n' ≤ m ∧ Link bk F₀.T (F m).T (tw.Pi m) n' r) →
    ∃ (s : Per.Acris l) (V : Matrix (Fin d) (Fin d) (Per.Acris l)) (V' : ∀ m, Matrix (Fin (tw.d' m)) (Fin (tw.d' m)) (Per.Acris l)),
      IsUnit (iB l s) ∧ IsOp ρ n (iB l s) (V.map (iB l)) ∧ (∀ m, IsOp (tw.ρ' m) n (iB l s) ((V' m).map (iB l))) ∧
      ∀ M, ∃ m, M ≤ m ∧ ∀ i j, (l : Per.Acris l) ^ M ∣ (V * (tw.Pi m).map (zC l) - (tw.Pi m).map (zC l) * V' m) i j

def FrEx : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K L₀ : FinExt l) (bk : BK K) (τp : Ainf l), bk.IsPer τp →
    ∀ (P : LocPrime l) (AI : LocAinf l P) (_ : LocTied l P AI) (a : ℕ), (∀ (τ : ↥K.1 →ₐ[ℚ_[l]] Om l) (x : ↥K.1), τ x ∈ L₀.1) →
    ∀ (r : ↥(GK K) →* GL (Fin a) (Om l)) (Cl : Set (↥(GK K) →* GL (Fin a) (Om l))) (Cv : Cover L₀ r Cl)
      (J : (↥K.1 →ₐ[ℚ_[l]] Om l) → Multiset ℤ),
    (∀ ρ₁ ∈ Cl, ∀ (L : FinExt l) (r' : ↥(GK K) →* GL (Fin a) ↥L.1) (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1)), L₀.1 ≤ L.1 →
      (∀ g v, R g v = (r' g).val *ᵥ v) → (∀ g i j, (((r' g).val i j : ↥L.1) : Om l) = (ρ₁ g).val i j) →
      IsSst P R ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥L.1) (n : ℤ), multV (P.PD K) R τ n = ((J (L.1.val.comp τ)).count n : ℤ)) →
    (∀ ρ₁ ∈ Cl, ∀ (L : FinExt l) (r' : ↥(GK K) →* GL (Fin a) ↥L.1) (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1)), L₀.1 ≤ L.1 →
      (∀ g v, R g v = (r' g).val *ᵥ v) → (∀ g i j, (((r' g).val i j : ↥L.1) : Om l) = (ρ₁ g).val i j) → IsCrys (P.PD K) R) →
    ∃ (N : ℕ) (F : ∀ m, Frame bk N (Cv.tw.d' m) fun g => (Cv.tw.ρ' m g).val) (F₀ : Frame bk N Cv.d fun g => (Cv.ρ g).val) (rr : ℕ),
      (∀ m, (F m).IsCr) ∧ F₀.IsCr ∧ ∀ n', ∃ m, n' ≤ m ∧ Link bk F₀.T (F m).T (Cv.tw.Pi m) n' rr

def IntBasis : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (F : IntermediateField ℚ_[l] (Om l)) (n : ℕ) (x : Fin n → Om l), (∀ i, ‖x i‖ ≤ 1) →
    ∃ (m : ℕ) (e : Fin m → Om l), LinearIndependent ↥F e ∧ (∀ j, ‖e j‖ ≤ 1) ∧
      ∀ i, ∃ c : Fin m → ↥F, (∀ j, ‖(c j : Om l)‖ ≤ 1) ∧ x i = ∑ j, (c j : Om l) * e j

def Func : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (F : IntermediateField ℚ_[l] (Om l)) (I : Type) [Finite I] (x : I → Om l) (z : Om l), (∀ i, ‖x i‖ ≤ 1) →
    ‖z‖ ≤ 1 → ∃ lam : Om l →ₗ[↥F] ↥F, (∀ i, ‖(lam (x i) : Om l)‖ ≤ 1) ∧ ‖z‖ ≤ ‖(lam z : Om l)‖ ∧ ‖(lam z : Om l)‖ ≤ 1

def TrId : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (B : Type) [CommRing B] (u : ↥(MaximalUnramifiedExtension l) →+* B) (zb : ℤ_[l] →+* B),
    (∀ z : ℤ_[l], u (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (z : ℚ_[l])) = zb z) → ∀ (s : B) (d d' m : ℕ) (t : Fin d → Om l)
    (t' : Fin d' → Fin m → Om l) (c pv : Fin m → Om l) (p θ : Om l) (Pi : Matrix (Fin d) (Fin d') ℤ_[l]) (e : Fin d → ℤ_[l])
    (e' : Fin d' → ℤ_[l]) (V : Matrix (Fin d) (Fin d) B) (V' : Matrix (Fin d') (Fin d') B),
    IsTr u s (V *ᵥ fun i => zb (e i)) t p → (∀ k, IsTr u s (V' *ᵥ fun i => zb (e' i)) (fun j => t' j k) (pv k)) →
    ∀ lam : Om l →ₗ[↥(MaximalUnramifiedExtension l)] ↥(MaximalUnramifiedExtension l), s * u (lam (p - θ)) =
      ∑ i, ((V * Pi.map zb - Pi.map zb * V') *ᵥ (fun j => zb (e' j)) - V *ᵥ fun i => zb ((Pi *ᵥ e' - e) i)) i * u (lam (t i)) +
      ∑ j, (V' *ᵥ fun i => zb (e' i)) j * u (lam (∑ i, zOm l (Pi i j) * t i - ∑ k, c k * t' j k)) - s * u (lam (θ - ∑ k, c k * pv k))

def TrStep : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (s : Per.Acris l) (d d' m M c₁ c₂ : ℕ) (t : Fin d → Om l)
    (t' : Fin d' → Fin m → Om l) (c pv : Fin m → Om l) (p θ : Om l) (Pi : Matrix (Fin d) (Fin d') ℤ_[l]) (e : Fin d → ℤ_[l])
    (e' : Fin d' → ℤ_[l]) (V : Matrix (Fin d) (Fin d) (Per.Acris l)) (V' : Matrix (Fin d') (Fin d') (Per.Acris l)),
    IsTr (uB T) (iB l s) (V.map (iB l) *ᵥ fun i => Per.zB l (e i)) t p →
    (∀ k, IsTr (uB T) (iB l s) (V'.map (iB l) *ᵥ fun i => Per.zB l (e' i)) (fun j => t' j k) (pv k)) →
    (∀ i j, (l : Per.Acris l) ^ M ∣ (V * Pi.map (zC l) - Pi.map (zC l) * V') i j) → (∀ i, (l : ℤ_[l]) ^ M ∣ (Pi *ᵥ e' - e) i) →
    (∀ j, ‖∑ i, zOm l (Pi i j) * t i - ∑ k, c k * t' j k‖ ≤ ((l : ℝ) ^ M)⁻¹) → ‖θ - ∑ k, c k * pv k‖ ≤ ((l : ℝ) ^ M)⁻¹ →
    (∀ i, ‖(l : Om l) ^ c₁ * t i‖ ≤ 1) → ‖(l : Om l) ^ c₁ * (p - θ)‖ ≤ 1 → ((l : ℝ) ^ c₂)⁻¹ ≤ ‖(l : Om l) ^ c₁ * (p - θ)‖ →
    (l : Per.Acris l) ^ M ∣ (l : Per.Acris l) ^ c₂ * s

def TrLim : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (_ : BK K) (Γ : Type) [Group Γ]
    [TopologicalSpace Γ] (L₀ : FinExt l) (a : ℕ) (r : Γ →* GL (Fin a) (Om l)) (Cl : Set (Γ →* GL (Fin a) (Om l))) (Cv : Cover L₀ r Cl)
    (s : Per.Acris l) (V : Matrix (Fin Cv.d) (Fin Cv.d) (Per.Acris l))
    (V' : ∀ m, Matrix (Fin (Cv.tw.d' m)) (Fin (Cv.tw.d' m)) (Per.Acris l)) (p θ : Om l) (pv : ∀ m, Fin (Cv.lay m).m → Om l),
    IsUnit (iB l s) → IsTr (uB T) (iB l s) (V.map (iB l) *ᵥ fun i => Per.zB l (Cv.e i)) (fun i => (Cv.b i).trace) p →
    (∀ m k, IsTr (uB T) (iB l s) ((V' m).map (iB l) *ᵥ fun i => Per.zB l ((Cv.lay m).e i)) (fun j => ((Cv.lay m).b j k).trace) (pv m k)) →
    (∀ M, ∃ m, M ≤ m ∧ ∀ i j, (l : Per.Acris l) ^ M ∣ (V * (Cv.tw.Pi m).map (zC l) - (Cv.tw.Pi m).map (zC l) * V' m) i j) →
    (∀ m, ‖θ - ∑ k, (Cv.lay m).c k * pv m k‖ ≤ ((l : ℝ) ^ m)⁻¹) → p = θ

def TrLin : Prop :=
  ∀ (k B W J : Type) [Field k] [CommRing B] [AddCommGroup W] [Module k W] [FiniteDimensional k W] [Fintype J] (a : ℕ),
    Module.finrank k W = a → ∀ (κ : k →+* B) (ψ : W →+ (Fin a → B)), (∀ (c : k) (x : W), ψ (c • x) = κ c • ψ x) →
    ∀ (T : Module.End k W) (x : J → Fin a → W) (w : J → B),
    (∀ i i', ∑ j, w j * ψ (x j i') i = if i = i' then 1 else 0) → ∑ i, ∑ j, w j * ψ (T (x j i)) i = κ (LinearMap.trace k W T)

def CoordEx : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (L : FinExt l) (a : ℕ),
    ∃ ψ : (Fin a → ↥L.1) ⊗[ℚ_[l]] Bst P →+ (Fin a → OB P), IsCoord P L ψ

def CoordWD : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) (K L : FinExt l) (a : ℕ) (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1))
    (ψ₀ : (Fin a → ↥L.1) ⊗[ℚ_[l]] Bst P →+ (Fin a → OB P)), IsCoord P L ψ₀ →
    ∃ ψ : WDSpace P ι R →+ (Fin a → OB P), (∀ (c : ℂ) (x : WDSpace P ι R), ψ (c • x) = ((ι.symm c ⊗ₜ 1 : OB P)) • ψ x) ∧
      ∀ x : ↥(Dpst P R), ψ (wdMk P ι R x) = ψ₀ x

def ColInv : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K L : FinExt l) (a d : ℕ)
    (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1)) (v : Fin d → Fin a → ↥L.1),
    (∀ g j, R g (v j) = ∑ i, ((ρ g).val i j : ℚ_[l]) • v i) → ∀ U, IsPerU ρ U → ∀ (j : Fin d),
    (∑ i, v i ⊗ₜ[ℚ_[l]] (Polynomial.C (T.eB.symm (U i j)) : Bst P)) ∈ Dst P R ∧ ∀ n : ℕ,
      (phiV P ↥L.1 (Fin a → ↥L.1) ^ n) (∑ i, v i ⊗ₜ[ℚ_[l]] (Polynomial.C (T.eB.symm (U i j)) : Bst P)) =
        ∑ i, v i ⊗ₜ[ℚ_[l]] (Polynomial.C (T.eB.symm ((Per.φB l ^ n) (U i j))) : Bst P)

def WeilPhi : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O), Induces Bw → ∀ (g : ↥(Weil h)) (n : ℕ), alpha l g = -(n : ℤ) →
    FixUr Bw.Kw n ∧ ∀ (L : FinExt l) (a : ℕ) (R : Representation ↥L.1 ↥(GK Bw.Kw) (Fin a → ↥L.1))
      [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P R)] (x : ↥(Dpst P R)), (x : (Fin a → ↥L.1) ⊗[ℚ_[l]] Bst P) ∈ Dst P R →
      ((weilD Bw h P R g x : ↥(Dpst P R)) : (Fin a → ↥L.1) ⊗[ℚ_[l]] Bst P) = (phiV P ↥L.1 (Fin a → ↥L.1) ^ n) x

def TestTr : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (d : ℕ) (s : Per.Bcris l) (v v₀ : Fin d → Per.Bcris l)
    (t : Fin d → Om l) (p : Om l), v = s • v₀ →
    (∑ i, t i ⊗ₜ (Polynomial.C (T.eB.symm (v₀ i)) : Bst P) : OB P) = p ⊗ₜ 1 → IsTr (uB T) s v t p

def TieRep : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : Om l ≃+* ℂ) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Induces Bw) (g : ↥(Weil h)) (n : ℕ), alpha l g = -(n : ℤ) →
    ∀ (L : FinExt l) (a d : ℕ) (R : Representation ↥L.1 ↥(GK Bw.Kw) (Fin a → ↥L.1)) [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P R)],
    Module.finrank ℂ (WDSpace P ι R) = a → ∀ (ρ : ↥(GK Bw.Kw) →* GL (Fin d) ℤ_[l]) (b : Fin d → Matrix (Fin a) (Fin a) ↥L.1)
      (e : Fin d → ℤ_[l]), (∀ g j (k : Fin a), R g (fun i => b j i k) = ∑ i, ((ρ g).val i j : ℚ_[l]) • fun i' => b i i' k) →
      ∑ i, (e i : ℚ_[l]) • b i = 1 → ∀ (s : Per.Bcris l) (V : Matrix (Fin d) (Fin d) (Per.Bcris l)), IsOp ρ n s V →
      IsTr (uB T) s (V *ᵥ fun i => Per.zB l (e i)) (fun i => (((b i).trace : ↥L.1) : Om l))
        (ι.symm (LinearMap.trace ℂ (WDSpace P ι R) (wdRho P ι Bw h hj R g)))

def Comparison₂ : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : Om l ≃+* ℂ) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Induces Bw) (g : ↥(Weil h)) (n : ℕ), alpha l g = -(n : ℤ) →
    ∀ (a d : ℕ) (r : ↥(Dec (F := E) A) →* GL (Fin a) (Om l)), IsCrysAt P Bw r →
    ∀ (ρ : ↥(GK Bw.Kw) →* GL (Fin d) ℤ_[l]) (b : Fin d → Matrix (Fin a) (Fin a) (Om l)) (e : Fin d → ℤ_[l]),
      Reads ρ (r.comp Bw.e.symm.toMonoidHom) b e → ∀ (s : Per.Bcris l) (V : Matrix (Fin d) (Fin d) (Per.Bcris l)), IsOp ρ n s V →
      IsTr (uB T) s (V *ᵥ fun i => Per.zB l (e i)) (fun i => (b i).trace) (wdTr P ι Bw h hj r g)

end UpperTheory.Gal.ClosedPhiFromClosedTrace

end
