import Formalism.LocalToGlobal.BesselHermitianTheta.TiedBessel
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory Matrix
open Formalism.L2.Theta Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.Mi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Scalar

variable {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}

def PsiRat (ψ : AddChar (AF D.host.F) ℂ) : Prop :=
  ∀ x : D.host.E, ψ (Algebra.trace (AF D.host.F) (AE D) (incA D x)) = 1

def IsEmbHom (ι : A.V →ₗ[D.host.E] B.V) (s : GA D A →* GA D B) : Prop :=
  ∀ h, EmbRel B A ι (s h) h

def IsQuotPair (V : HSp D) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) : Prop :=
  μ.IsHaarMeasure ∧ IsFundamentalDomain (GQ V) 𝓕 μ

def IsNPair (d : BesDat A B ι) (μN : Measure (NFlag B d.e)) (𝓕N : Set (NFlag B d.e)) : Prop :=
  μN.IsHaarMeasure ∧ IsFundamentalDomain (NFlagQ B d.e) 𝓕N μN ∧ μN 𝓕N = 1

def besIntd (ψ : AddChar (AF D.host.F) ℂ) (d : BesDat A B ι) (s : GA D A →* GA D B) (φ : GA D A → ℂ)
    (F : GA D B → ℂ) (h : GA D A) (n : NFlag B d.e) : ℂ :=
  φ h * F ((n : GA D B) * s h * (d.y : GA D B)) * star (besChar ψ d (n : GA D B))

def IsBesPer (ψ : AddChar (AF D.host.F) ℂ) (d : BesDat A B ι) (s : GA D A →* GA D B) (μ : Measure (GA D A))
    (𝓕 : Set (GA D A)) (μN : Measure (NFlag B d.e)) (𝓕N : Set (NFlag B d.e)) (φ : GA D A → ℂ) (F : GA D B → ℂ)
    (b : ℂ) : Prop :=
  (∀ h, IntegrableOn (besIntd ψ d s φ F h) 𝓕N μN) ∧
    IntegrableOn (fun h => ∫ n in 𝓕N, besIntd ψ d s φ F h n ∂μN) 𝓕 μ ∧
    b = ∫ h in 𝓕, ∫ n in 𝓕N, besIntd ψ d s φ F h n ∂μN ∂μ

def BesStd (ψ : AddChar (AF D.host.F) ℂ) (d : BesDat A B ι) (s : GA D A →* GA D B) (μ : Measure (GA D A))
    (𝓕 : Set (GA D A)) (μN : Measure (NFlag B d.e)) (𝓕N : Set (NFlag B d.e)) : Prop :=
  Continuous ψ ∧ PsiRat ψ ∧ HSpace.IsIsomEmb A B ι ∧ IsAniso A ∧ IsEmbHom ι s ∧ IsQuotPair A μ 𝓕 ∧
    IsNPair d μN 𝓕N

def BesPerConv : Prop :=
  ∀ (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (ψ : AddChar (AF D.host.F) ℂ) (d : BesDat A B ι)
    (s : GA D A →* GA D B) (μ : Measure (GA D A)) (𝓕 : Set (GA D A)) (μN : Measure (NFlag B d.e))
    (𝓕N : Set (NFlag B d.e)), BesStd ψ d s μ 𝓕 μN 𝓕N →
    ∀ (φ : GA D A → ℂ) (F : GA D B → ℂ), IsAutFun A φ → IsAutFun B F →
      ∃ b, IsBesPer ψ d s μ 𝓕 μN 𝓕N φ F b

def BesPerEqvU : Prop :=
  ∀ (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (ψ : AddChar (AF D.host.F) ℂ) (d : BesDat A B ι)
    (s : GA D A →* GA D B) (μ : Measure (GA D A)) (𝓕 : Set (GA D A)) (μN : Measure (NFlag B d.e))
    (𝓕N : Set (NFlag B d.e)), BesStd ψ d s μ 𝓕 μN 𝓕N →
    ∀ (φ : GA D A → ℂ) (F : GA D B → ℂ), IsAutFun A φ → IsAutFun B F → ∀ (y' : GA D A) (b : ℂ),
      IsBesPer ψ d s μ 𝓕 μN 𝓕N φ F b →
      IsBesPer ψ d s μ 𝓕 μN 𝓕N (rTr A y' φ) (rTr B ((d.y : GA D B)⁻¹ * s y' * (d.y : GA D B)) F) b

def BesPerEqvN : Prop :=
  ∀ (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (ψ : AddChar (AF D.host.F) ℂ) (d : BesDat A B ι)
    (s : GA D A →* GA D B) (μ : Measure (GA D A)) (𝓕 : Set (GA D A)) (μN : Measure (NFlag B d.e))
    (𝓕N : Set (NFlag B d.e)), BesStd ψ d s μ 𝓕 μN 𝓕N →
    ∀ (φ : GA D A → ℂ) (F : GA D B → ℂ), IsAutFun A φ → IsAutFun B F → ∀ (n₀ : NFlag B d.e) (b : ℂ),
      IsBesPer ψ d s μ 𝓕 μN 𝓕N φ F b →
      IsBesPer ψ d s μ 𝓕 μN 𝓕N φ (rTr B ((d.y : GA D B)⁻¹ * (n₀ : GA D B) * (d.y : GA D B)) F)
        (besChar ψ d (n₀ : GA D B) * b)

end Scalar

section Vec

variable {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}

def rTrLin (V : HSp D) (k : GA D V) : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ) where
  toFun := rTr V k
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def SobContN {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (Lie : Set (Matrix (Fin n) (Fin n) ℂ))
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (N : ℕ) (ℓ : H →ₗ[ℂ] ℂ) : Prop :=
  ∃ (L : List (List (Matrix (Fin n) (Fin n) ℂ))) (C : ℝ), (∀ l ∈ L, l.length ≤ N ∧ ∀ X ∈ l, X ∈ Lie) ∧
    ∀ w, SmoothVec Lie σ w → ‖ℓ w‖ ≤ C * (L.map fun l => ‖l.foldr (dRep σ) w‖).sum

variable (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
  {Vt : D.what₂.Tau → Type} [∀ τ, NormedAddCommGroup (Vt τ)] [∀ τ, InnerProductSpace ℂ (Vt τ)]
  {S : D.what₂.Tau → SPar}

open Classical in

def IsColMap (π : ∀ τ, Matrix (Fin A.rank) (Fin A.rank) ℂ → (Vt τ →L[ℂ] Vt τ))
    (Φ : MultilinearMap ℂ (fun τ => Vt τ) (GA D A → ℂ)) : Prop :=
  (∀ v, IsAutFun A (Φ v)) ∧
    ∀ τ, ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D A τ), ∀ v : ∀ τ, Vt τ,
      Φ (Function.update v τ (π τ h (v τ))) = rTr A (atTau θ A τ h) (Φ v)

def IsBesFormAt (ψ : AddChar (AF D.host.F) ℂ) (d : BesDat A B ι) (s : GA D A →* GA D B)
    (π : ∀ τ, Matrix (Fin A.rank) (Fin A.rank) ℂ → (Vt τ →L[ℂ] Vt τ)) (M : DSModel B S) (τ : D.what₂.Tau) (N : ℕ)
    (L : Vt τ →ₗ[ℂ] M.sm τ →ₗ[ℂ] ℂ) : Prop :=
  (∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D A τ), ∀ (a : Vt τ) (x w : M.sm τ),
      (w : M.H τ) = M.rep τ (infMat D.sp.cm.sig B.gram (θ τ) (s (atTau θ A τ h))) x → L (π τ h a) w = L a x) ∧
    (∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D B τ), atTau θ B τ g ∈ NFlag B d.e → ∀ (a : Vt τ) (x w : M.sm τ),
      (w : M.H τ) = M.rep τ g x → L a w = besChar ψ d (atTau θ B τ g) * L a x) ∧
    ∀ a : Vt τ, ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, SobContN (lieAt B τ) (M.rep τ) N ℓ ∧ ∀ w : M.sm τ, ℓ w = L a w

def LocUniqAt (ψ : AddChar (AF D.host.F) ℂ) (d : BesDat A B ι) (s : GA D A →* GA D B)
    (π : ∀ τ, Matrix (Fin A.rank) (Fin A.rank) ℂ → (Vt τ →L[ℂ] Vt τ)) (M : DSModel B S) (τ : D.what₂.Tau) (N : ℕ) : Prop :=
  ∀ L₁ L₂ : Vt τ →ₗ[ℂ] M.sm τ →ₗ[ℂ] ℂ, IsBesFormAt θ ψ d s π M τ N L₁ → IsBesFormAt θ ψ d s π M τ N L₂ →
    ∃ a b : ℂ, (a ≠ 0 ∨ b ≠ 0) ∧ a • L₁ + b • L₂ = 0

open Classical in

def IsBesForm (ψ : AddChar (AF D.host.F) ℂ) (d : BesDat A B ι) (s : GA D A →* GA D B)
    (π : ∀ τ, Matrix (Fin A.rank) (Fin A.rank) ℂ → (Vt τ →L[ℂ] Vt τ)) (M : DSModel B S) (N : ℕ)
    (ℓ : MultilinearMap ℂ (fun τ => Vt τ) (MultilinearMap ℂ (fun τ => M.sm τ) ℂ)) : Prop :=
  (∀ τ, ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D A τ), ∀ (v : ∀ τ, Vt τ) (x : M.Vec) (w : M.sm τ),
      (w : M.H τ) = M.rep τ (infMat D.sp.cm.sig B.gram (θ τ) (s (atTau θ A τ h))) (x τ) →
      ℓ (Function.update v τ (π τ h (v τ))) (Function.update x τ w) = ℓ v x) ∧
    (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D B τ), atTau θ B τ g ∈ NFlag B d.e →
      ∀ (v : ∀ τ, Vt τ) (x : M.Vec) (w : M.sm τ), (w : M.H τ) = M.rep τ g (x τ) →
      ℓ v (Function.update x τ w) = besChar ψ d (atTau θ B τ g) * ℓ v x) ∧
    ∀ τ (v : ∀ τ, Vt τ) (x : M.Vec), ∃ L : M.H τ →ₗ[ℂ] ℂ, SobContN (lieAt B τ) (M.rep τ) N L ∧
      ∀ w : M.sm τ, L w = ℓ v (Function.update x τ w)

open Classical in

def UnifSob (M : DSModel B S) (N : ℕ) (T : MMap M) : Prop :=
  ∀ Ω : Set (GA D B), IsCompact Ω → ∀ τ (x : M.Vec),
    ∃ (L : List (List (Matrix (Fin B.rank) (Fin B.rank) ℂ))) (C : ℝ), (∀ l ∈ L, l.length ≤ N ∧ ∀ X ∈ l, X ∈ lieAt B τ) ∧
      ∀ g ∈ Ω, ∀ w : M.sm τ, ‖T (Function.update x τ w) g‖ ≤
        C * (L.map fun l => ‖l.foldr (dRep (M.rep τ)) (w : M.H τ)‖).sum

def IsBesNum (ψ : AddChar (AF D.host.F) ℂ) (d : BesDat A B ι) (s : GA D A →* GA D B) (μ : Measure (GA D A))
    (𝓕 : Set (GA D A)) (μN : Measure (NFlag B d.e)) (𝓕N : Set (NFlag B d.e)) {M : DSModel B S}
    (Φ : MultilinearMap ℂ (fun τ => Vt τ) (GA D A → ℂ)) (T : MMap M)
    (ℓ : MultilinearMap ℂ (fun τ => Vt τ) (MultilinearMap ℂ (fun τ => M.sm τ) ℂ)) (Bn : ℂ) : Prop :=
  ∀ (v : ∀ τ, Vt τ) (x : M.Vec), IsBesPer ψ d s μ 𝓕 μN 𝓕N (Φ v) (T x) (ℓ v x * Bn)

end Vec

def ProdUniq : Prop :=
  ∀ (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (ψ : AddChar (AF D.host.F) ℂ) (d : BesDat A B ι) (s : GA D A →* GA D B)
    (Vt : D.what₂.Tau → Type) [∀ τ, NormedAddCommGroup (Vt τ)] [∀ τ, InnerProductSpace ℂ (Vt τ)]
    (π : ∀ τ, Matrix (Fin A.rank) (Fin A.rank) ℂ → (Vt τ →L[ℂ] Vt τ)) (S : D.what₂.Tau → SPar) (M : DSModel B S) (N : ℕ),
    (∀ τ, LocUniqAt θ ψ d s π M τ N) →
    ∀ ℓ₁ ℓ₂ : MultilinearMap ℂ (fun τ => Vt τ) (MultilinearMap ℂ (fun τ => M.sm τ) ℂ),
      IsBesForm θ ψ d s π M N ℓ₁ → IsBesForm θ ψ d s π M N ℓ₂ → ∃ a b : ℂ, (a ≠ 0 ∨ b ≠ 0) ∧ a • ℓ₁ + b • ℓ₂ = 0

def BesFormOfPer : Prop :=
  ∀ (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (ψ : AddChar (AF D.host.F) ℂ) (d : BesDat A B ι) (s : GA D A →* GA D B) (μ : Measure (GA D A))
    (𝓕 : Set (GA D A)) (μN : Measure (NFlag B d.e)) (𝓕N : Set (NFlag B d.e)),
    IsInfFam θ → BesStd ψ d s μ 𝓕 μN 𝓕N →
    ∀ (Vt : D.what₂.Tau → Type) [∀ τ, NormedAddCommGroup (Vt τ)] [∀ τ, InnerProductSpace ℂ (Vt τ)]
      (π : ∀ τ, Matrix (Fin A.rank) (Fin A.rank) ℂ → (Vt τ →L[ℂ] Vt τ)) (S : D.what₂.Tau → SPar) (M : DSModel B S)
      (J : Set (GA D B)) (χ : GA D B → ℂ) (N : ℕ) (Φ : MultilinearMap ℂ (fun τ => Vt τ) (GA D A → ℂ)) (T : MMap M),
      IsColMap θ π Φ → IsMultMap θ M J χ T → UnifSob M N T →
      ∃ ℓ : MultilinearMap ℂ (fun τ => Vt τ) (MultilinearMap ℂ (fun τ => M.sm τ) ℂ),
        IsBesForm θ ψ d s π M N ℓ ∧ ∀ v x, IsBesPer ψ d s μ 𝓕 μN 𝓕N (Φ v) (T x) (ℓ v x)

def BesNumExists : Prop :=
  ∀ (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (ψ : AddChar (AF D.host.F) ℂ) (d : BesDat A B ι) (s : GA D A →* GA D B) (μ : Measure (GA D A))
    (𝓕 : Set (GA D A)) (μN : Measure (NFlag B d.e)) (𝓕N : Set (NFlag B d.e)),
    IsInfFam θ → BesStd ψ d s μ 𝓕 μN 𝓕N →
    ∀ (Vt : D.what₂.Tau → Type) [∀ τ, NormedAddCommGroup (Vt τ)] [∀ τ, InnerProductSpace ℂ (Vt τ)]
      (π : ∀ τ, Matrix (Fin A.rank) (Fin A.rank) ℂ → (Vt τ →L[ℂ] Vt τ)) (S : D.what₂.Tau → SPar) (M : DSModel B S)
      (J : Set (GA D B)) (χ : GA D B → ℂ) (N : ℕ) (Φ : MultilinearMap ℂ (fun τ => Vt τ) (GA D A → ℂ)) (T : MMap M)
      (ℓ : MultilinearMap ℂ (fun τ => Vt τ) (MultilinearMap ℂ (fun τ => M.sm τ) ℂ)),
      (∀ τ, LocUniqAt θ ψ d s π M τ N) → IsColMap θ π Φ → IsMultMap θ M J χ T → UnifSob M N T →
      IsBesForm θ ψ d s π M N ℓ → ℓ ≠ 0 → ∃! Bn, IsBesNum ψ d s μ 𝓕 μN 𝓕N Φ T ℓ Bn

def BesNumEqvU : Prop :=
  ∀ (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (ψ : AddChar (AF D.host.F) ℂ) (d : BesDat A B ι) (s : GA D A →* GA D B) (μ : Measure (GA D A))
    (𝓕 : Set (GA D A)) (μN : Measure (NFlag B d.e)) (𝓕N : Set (NFlag B d.e)), BesStd ψ d s μ 𝓕 μN 𝓕N →
    ∀ (Vt : D.what₂.Tau → Type) [∀ τ, NormedAddCommGroup (Vt τ)] [∀ τ, InnerProductSpace ℂ (Vt τ)]
      (π : ∀ τ, Matrix (Fin A.rank) (Fin A.rank) ℂ → (Vt τ →L[ℂ] Vt τ)) (S : D.what₂.Tau → SPar) (M : DSModel B S)
      (Φ : MultilinearMap ℂ (fun τ => Vt τ) (GA D A → ℂ)) (T : MMap M)
      (ℓ : MultilinearMap ℂ (fun τ => Vt τ) (MultilinearMap ℂ (fun τ => M.sm τ) ℂ)),
      IsColMap θ π Φ → (∀ x, IsAutFun B (T x)) → ∀ (y' : GA D A) (Bn : ℂ),
      IsBesNum ψ d s μ 𝓕 μN 𝓕N Φ T ℓ Bn →
      IsBesNum ψ d s μ 𝓕 μN 𝓕N ((rTrLin A y').compMultilinearMap Φ)
        (postOn M (rTrLin B ((d.y : GA D B)⁻¹ * s y' * (d.y : GA D B))) T) ℓ Bn

def BesNumEqvN : Prop :=
  ∀ (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (ψ : AddChar (AF D.host.F) ℂ) (d : BesDat A B ι) (s : GA D A →* GA D B) (μ : Measure (GA D A))
    (𝓕 : Set (GA D A)) (μN : Measure (NFlag B d.e)) (𝓕N : Set (NFlag B d.e)), BesStd ψ d s μ 𝓕 μN 𝓕N →
    ∀ (Vt : D.what₂.Tau → Type) [∀ τ, NormedAddCommGroup (Vt τ)] [∀ τ, InnerProductSpace ℂ (Vt τ)]
      (π : ∀ τ, Matrix (Fin A.rank) (Fin A.rank) ℂ → (Vt τ →L[ℂ] Vt τ)) (S : D.what₂.Tau → SPar) (M : DSModel B S)
      (Φ : MultilinearMap ℂ (fun τ => Vt τ) (GA D A → ℂ)) (T : MMap M)
      (ℓ : MultilinearMap ℂ (fun τ => Vt τ) (MultilinearMap ℂ (fun τ => M.sm τ) ℂ)),
      IsColMap θ π Φ → (∀ x, IsAutFun B (T x)) → ∀ (n₀ : NFlag B d.e) (Bn : ℂ),
      IsBesNum ψ d s μ 𝓕 μN 𝓕N Φ T ℓ Bn →
      IsBesNum ψ d s μ 𝓕 μN 𝓕N Φ (postOn M (rTrLin B ((d.y : GA D B)⁻¹ * (n₀ : GA D B) * (d.y : GA D B))) T) ℓ
        (besChar ψ d (n₀ : GA D B) * Bn)

end Formalism.IndefR.Mi

end
