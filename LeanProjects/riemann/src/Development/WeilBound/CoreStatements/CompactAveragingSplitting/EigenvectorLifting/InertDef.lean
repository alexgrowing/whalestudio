import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.FinSplit
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ComplementaryThetaInert

noncomputable section

namespace PositivityTheory.ThK

open scoped Matrix
open NumberField IsDedekindDomain Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}

abbrev Fn (F : Type) [Field F] [NumberField F] (n d : ℕ) (v : Pl F) : Type := (Fin n × Fin d → Fv F v) → ℂ

structure PairOK (B : Base F E) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (om : Rep σ X W) : Prop where
  base : B.IsGood σ
  herm : ∃ r s, X.IsHerm σ B r s
  skew : ∃ r s, W.IsSkew σ B r s
  good : M.IsGood B.ψ
  weil : ∃ χX χW, M.IsWeil B.ψ χX χW om

structure IsLocRep {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (om : Rep σ X W) (v : Pl F)
    (ω : UA σ X.J × UA σ W.J → Module.End ℂ (Fn F n d v))
    (ρ : Matrix (Fin n) (Fin d) (AE F E) → Module.End ℂ (Fn F n d v)) : Prop where
  pres : ∀ g ∈ UAt σ X (evFin F v), ∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB _, ω (g, h) φ ∈ SB _
  acts : ∀ g ∈ UAt σ X (evFin F v), ∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB _, ∀ φ₁,
    Acts (evFin F v) (om (g, h)) φ φ₁ ↔ φ₁ = ω (g, h) φ
  one : ∀ φ ∈ SB _, ω 1 φ = φ
  mul : ∀ g ∈ UAt σ X (evFin F v), ∀ h ∈ UAt σ W (evFin F v), ∀ g' ∈ UAt σ X (evFin F v), ∀ h' ∈ UAt σ W (evFin F v),
    ∀ φ ∈ SB _, ω (g * g', h * h') φ = ω (g, h) (ω (g', h') φ)
  smooth : ∀ φ ∈ SB _, ∃ U ∈ 𝓝 (1 : UA σ W.J), ∀ h ∈ U, h ∈ UAt σ W (evFin F v) → ω (1, h) φ = φ
  presH : ∀ u, At (evFin F v) u → ∀ φ ∈ SB _, ρ u φ ∈ SB _
  actsH : ∀ u, At (evFin F v) u → ∀ φ ∈ SB _, ∀ φ₁, Acts (evFin F v) (M.co.rho ψ u) φ φ₁ ↔ φ₁ = ρ u φ
  impl : ∀ g ∈ UAt σ X (evFin F v), ∀ h ∈ UAt σ W (evFin F v), ∀ u, At (evFin F v) u → ∀ φ ∈ SB _,
    ω (g, h) (ρ u φ) = ρ (mat g * u * (mat h)ᵀ) (ω (g, h) φ)

def latW (W : Spc F E d) (v : Pl F) : AddSubgroup (Fin d → AE F E) :=
  AddSubgroup.closure {z | ∃ a : AF F, At (evFin F v) a ∧ evFin F v a ∈ v.adicCompletionIntegers F ∧
    ∃ y ∈ W.L, z = fun i => a • inclR (F := F) (AF F) (y i)}

variable (σ) in

def KAt (W : Spc F E d) (v : Pl F) : Set (UA σ W.J) :=
  {k | k ∈ UAt σ W (evFin F v) ∧ ∀ y ∈ latW W v, mat k *ᵥ y ∈ latW W v ∧ mat k⁻¹ *ᵥ y ∈ latW W v}

variable (σ) in

structure IsLagAt (W : Spc F E d) (v : Pl F) {m : ℕ} (Cy : Matrix (Fin d) (Fin m) (AE F E)) : Prop where
  rank : d = 2 * m
  supp : At (evFin F v) Cy
  iso : Cyᵀ * incM F W.J * Cy.map (cA σ) = 0
  free : ∀ t : Fin m → AE F E, At (evFin F v) t → Cy *ᵥ t = 0 → t = 0

variable (σ) in

def IsAdaptedAt (W : Spc F E d) (v : Pl F) {m : ℕ} (Cy : Matrix (Fin d) (Fin m) (AE F E)) : Prop :=
  ∃ Cx : Matrix (Fin d) (Fin m) (AE F E), IsLagAt σ W v Cx ∧
    ∀ y ∈ latW W v, ∃ s t : Fin m → AE F E, Cy *ᵥ s ∈ latW W v ∧ Cx *ᵥ t ∈ latW W v ∧ y = Cy *ᵥ s + Cx *ᵥ t

variable (σ) in

def PAt (W : Spc F E d) (v : Pl F) {m : ℕ} (Cy : Matrix (Fin d) (Fin m) (AE F E)) : Set (UA σ W.J) :=
  {p | p ∈ UAt σ W (evFin F v) ∧ ∃ t : Matrix (Fin m) (Fin m) (AE F E), mat p * Cy = Cy * t}

def IsEvAt {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (v : Pl F) {m : ℕ}
    (Cy : Matrix (Fin d) (Fin m) (AE F E)) (l : Fn F n d v →ₗ[ℂ] ℂ) : Prop :=
  ∀ z : Matrix (Fin n) (Fin m) (AE F E), ∀ φ ∈ SB _, ∀ φ₁, Acts (evFin F v) (M.co.rho ψ (z * Cyᵀ)) φ φ₁ → l φ₁ = l φ

def AllPairs (Q : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    (_ : Base F E) {X : Spc F E n} {W : Spc F E d} (_ : Model σ X W) (_ : Rep σ X W), Pl F → Prop) : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (B : Base F E)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (om : Rep σ X W), PairOK B X W M om → ∀ v, Q B M om v

def LocRepEx : Prop := AllPairs fun B _ _ M om v => ∃ ω ρ, IsLocRep M B.ψ om v ω ρ

def KCompact : Prop := AllPairs fun {_ _} _ _ _ _ _ {σ _ _} _ _ W _ _ v => IsCompact (KAt σ W v)

def Iwasawa : Prop := AllPairs fun {F E} _ _ _ _ _ {σ _ d} _ _ W _ _ v => Even d → (∃ w, Formalism.UG.IsInertAt F E v w) →
  ∃ (m : ℕ) (Cy : Matrix (Fin d) (Fin m) (AE F E)), IsLagAt σ W v Cy ∧ IsAdaptedAt σ W v Cy ∧
    (∀ h ∈ UAt σ W (evFin F v), ∃ p ∈ PAt σ W v Cy, ∃ k ∈ KAt σ W v, h = p * k) ∧
    ∀ c : UA σ W.J → ℂ, (∀ k ∈ KAt σ W v, ∀ k' ∈ KAt σ W v, c (k * k') = c k * c k') →
      (∀ k ∈ KAt σ W v, k ∈ PAt σ W v Cy → c k = 1) → ∀ k ∈ KAt σ W v, c k = 1

def EvLine : Prop := AllPairs fun {F E} _ _ _ _ _ {σ n d} B _ W M _ v => ∀ (m : ℕ) (Cy : Matrix (Fin d) (Fin m) (AE F E)),
  IsLagAt σ W v Cy → ∀ l l' : Fn F n d v →ₗ[ℂ] ℂ, IsEvAt M B.ψ v Cy l → IsEvAt M B.ψ v Cy l' → (∃ φ ∈ SB _, l φ ≠ 0) →
    ∃ c : ℂ, ∀ φ ∈ SB _, l' φ = c * l φ

def EvVac : Prop := AllPairs fun {F E} _ _ _ _ _ {σ n d} B _ W M _ v => (∃ w, Formalism.UG.IsInertAt F E v w) →
  ∀ (m : ℕ) (Cy : Matrix (Fin d) (Fin m) (AE F E)), IsLagAt σ W v Cy → IsAdaptedAt σ W v Cy →
    ∃ l : Fn F n d v →ₗ[ℂ] ℂ, IsEvAt M B.ψ v Cy l ∧ l (M.vac v) ≠ 0

def VacEigen : Prop := AllPairs fun {F _} _ _ _ _ _ {σ _ _} _ _ W M om v => ∀ k ∈ KAt σ W v,
  ∃ c : ℂ, Acts (evFin F v) (om (1, k)) (M.vac v) (c • M.vac v)

def InertOf : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ v : Pl F, IsEmpty (E →ₐ[F] Fv F v) → ∃ w, Formalism.UG.IsInertAt F E v w

def CoinvEmbeds : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ)
    (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v w, Formalism.UG.IsInertAt F E v w → v ∉ X.T → ∀ (m : ℕ) (Cy : Matrix (Fin (a + a')) (Fin m) (AE F E)), IsLagAt σ G.W v Cy →
      (∀ l, IsEvAt G.M B.ψ v Cy l → (∃ φ ∈ SB _, l φ ≠ 0) → ∀ φ ∈ SB _, φ ∈ augAt om v ↔
        ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ₁, Acts (evFin F v) (om (1, h)) φ φ₁ → l φ₁ = 0) ∧
      ∀ l, IsEvAt G.M' B.ψ v Cy l → (∃ φ ∈ SB _, l φ ≠ 0) → ∀ φ ∈ SB _, φ ∈ augAt om' v ↔
        ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ₁, Acts (evFin F v) (om' (1, h)) φ φ₁ → l φ₁ = 0

end PositivityTheory.ThK
