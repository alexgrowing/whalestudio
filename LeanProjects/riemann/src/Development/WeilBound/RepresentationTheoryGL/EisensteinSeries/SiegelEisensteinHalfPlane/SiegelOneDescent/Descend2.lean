import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.DictInf

noncomputable section

open NumberField Matrix
open scoped NumberField.AdeleRing

namespace PositivityTheory.RgEis.So

open GroundTheory.Global

def Descend2 : Prop := ForRep fun {G} _ _ {_W} _ _ K ρ => ∀ (G₁ : Type) [Group G₁] [TopologicalSpace G₁]
  [IsTopologicalGroup G₁] [T2Space G₁] [LocallyCompactSpace G₁] (j : G₁ →* G) (Γ P : Subgroup G) (Γ₁ K₁ : Subgroup G₁)
  (c : G → ℂ) (η η' β : G → ℝ) (s : P → G₁), Continuous j → IsCompact (K₁ : Set G₁) → K₁ ≤ K.comap j → Γ₁.map j = Γ →
  Continuous s → (∀ p, j (s p) = p) → (∀ p : P, (p : G) ∈ K → s p ∈ K₁) → Iwa (P.comap j) K₁ →
  IsPar Γ K P c → IsHt Γ K P η → IsHt Γ K P η' → IsHt Γ K P β →
  (AllRep K₁ fun ρ₁ => HasWall Γ₁ K₁ (P.comap j) (P.comap j) (c ∘ j) (η ∘ j) (η' ∘ j) (β ∘ j) ρ₁) →
  HasWall Γ K P P c η η' β ρ

def dg {R : Type} [CommRing R] (ι : Type) [Fintype ι] [DecidableEq ι] (x : Rˣ) : GL (ι ⊕ ι) R :=
  ⟨Matrix.diagonal (Sum.elim (fun _ => 1) fun _ => (x : R)), Matrix.diagonal (Sum.elim (fun _ => 1) fun _ => ((x⁻¹ : Rˣ) : R)),
    by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext a; cases a <;> simp,
    by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext a; cases a <;> simp⟩

variable {F E R : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [CommRing R]

structure Base [TopologicalSpace R] (A : Ad E R) (ε : ℤˣ) (ν : 𝔸[F] →+* R) (r : R → 𝔸[F]) (δ : Eˣ) (α : IdeleGroup F)
    (ω : HeckeCharacter F) : Prop where
  cont : Continuous ν
  inj : Function.Injective ν
  fix : ∀ x, A.σ (ν x) = ν x
  rcont : Continuous r
  rfix : ∀ x, A.σ x = x → ν (r x) = x
  rat : ∀ y : F, ν (algebraMap F 𝔸[F] y) = A.i (algebraMap F E y)
  rat' : ∀ (e : E) (x : 𝔸[F]), A.i e = ν x → ∃ y : F, x = algebraMap F 𝔸[F] y
  int : ∀ x, ν x ∈ A.O ↔ x ∈ intAd F
  inf : ∀ w : A.W, ∃ v : InfinitePlace F, ∀ x, A.φ w (ν x) = (adStd F).φ v x
  inf' : ∀ v : InfinitePlace F, ∃ w : A.W, ∀ x, A.φ w (ν x) = (adStd F).φ v x
  lg : ∀ x : IdeleGroup F, A.lg (Units.map ν.toMonoidHom x) = 2 * (adStd F).lg x
  lgσ : ∀ x : Rˣ, A.lg (Units.map A.σ.toMonoidHom x) = A.lg x
  δσ : A.σ (A.i δ) = -(((ε : ℤ) : R) * A.i δ)
  δα : ∃ u : Rˣ, A.i δ = ν α * u ∧ (u : R) ∈ A.O ∧ ((u⁻¹ : Rˣ) : R) ∈ A.O ∧ ∀ w, ‖A.φ w u‖ = 1
  ωχ : ∀ x : IdeleGroup F, ω.toIdele x = A.χ (Units.map ν.toMonoidHom x)

variable (A : Ad E R) (ν : 𝔸[F] →+* R) (ι : Type) [Fintype ι] [DecidableEq ι]

def cover : Subgroup (Rˣ × GL (ι ⊕ ι) 𝔸[F]) :=
  MonoidHom.ker (MonoidHom.fst _ _ * (Units.map A.σ.toMonoidHom).comp (MonoidHom.fst _ _) *
    ((Units.map ν.toMonoidHom).comp Matrix.GeneralLinearGroup.det).comp (MonoidHom.snd _ _))

def prj : cover A ν ι →* GL (ι ⊕ ι) 𝔸[F] := (MonoidHom.snd _ _).comp (cover A ν ι).subtype

def cΓ : Subgroup (cover A ν ι) :=
  ((Units.map A.i.toMonoidHom).range.prod ((adStd F).ratGL (ι ⊕ ι))).subgroupOf _

variable {A ν ι}

def IsJ {ε : ℤˣ} (δ : Eˣ) (j : cover A ν ι →* A.U ε ι) : Prop :=
  ∀ x, (((j x).1 : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) = (x.1.1 : R) •
    (((dg ι (Units.map A.i.toMonoidHom δ))⁻¹ * Matrix.GeneralLinearGroup.map ν x.1.2 * dg ι (Units.map A.i.toMonoidHom δ) :
      GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R)

def cK {ε : ℤˣ} (α : IdeleGroup F) (j : cover A ν ι →* A.U ε ι) : Subgroup (cover A ν ι) :=
  (A.uK ε ι).comap j ⊓ (((adStd F).kGL (ι ⊕ ι)).map (MulAut.conj (dg ι α)).toMonoidHom).comap (prj A ν ι)

def c0 (x : cover A ν ι) : ℂ := A.χ x.1.1

def c1 {ε : ℤˣ} (j : cover A ν ι →* A.U ε ι) (x : cover A ν ι) : ℂ := A.uC ε ι (j x) * (c0 x)⁻¹

def ld (x : cover A ν ι) : ℝ := (adStd F).lg (Matrix.GeneralLinearGroup.det (prj A ν ι x))

def ForJ (Q : ∀ {F E R : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] (A : Ad E R) (ε : ℤˣ) (ν : 𝔸[F] →+* R) {ι : Type} [Fintype ι] [DecidableEq ι],
    ι → Eˣ → IdeleGroup F → HeckeCharacter F → (cover A ν ι →* A.U ε ι) → Prop) : Prop :=
  ∀ (F E R : Type) [Field F] [NumberField F] [Field E] [Algebra F E] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] (A : Ad E R) (ε : ℤˣ) (ν : 𝔸[F] →+* R) (r : R → 𝔸[F])
    (δ : Eˣ) (α : IdeleGroup F) (ω : HeckeCharacter F) (ι : Type) [Fintype ι] [DecidableEq ι] (i : ι)
    (j : cover A ν ι →* A.U ε ι), A.Good → Base A ε ν r δ α ω → (∀ x, x = i) → IsJ δ j → Q A ε ν i δ α ω j

def JEx : Prop :=
  ∀ (F E R : Type) [Field F] [NumberField F] [Field E] [Algebra F E] [CommRing R] [TopologicalSpace R]
    (A : Ad E R) (ε : ℤˣ) (ν : 𝔸[F] →+* R) (r : R → 𝔸[F]) (δ : Eˣ) (α : IdeleGroup F) (ω : HeckeCharacter F) (ι : Type)
    [Fintype ι] [DecidableEq ι] (i : ι), Base A ε ν r δ α ω → (∀ x, x = i) → ∃ j : cover A ν ι →* A.U ε ι, IsJ δ j

def JTop : Prop := ForJ fun {_} {_} {_} _ _ _ _ _ _ _ A _ ν {ι} _ _ _ _ _ _ j =>
  Continuous j ∧ T2Space (cover A ν ι) ∧ LocallyCompactSpace (cover A ν ι) ∧ SecondCountableTopology (cover A ν ι)

def JCpt : Prop := ForJ fun {_} {_} {_} _ _ _ _ _ _ _ A _ ν {ι} _ _ _ _ α _ j => IsCompact (cK α j : Set (cover A ν ι))

def JPar : Prop := ForJ fun {F} {_} {_} _ _ _ _ _ _ _ A ε ν {ι} _ _ i _ _ _ j =>
  stab 𝔸[F] ({Sum.inr i}ᶜ : Set (ι ⊕ ι)) = stab 𝔸[F] {Sum.inl i} ∧
  (A.uQ ε Set.univ).comap j = (stab 𝔸[F] {Sum.inl i}).comap (prj A ν ι) ∧
  ∀ x, prj A ν ι x ∈ stab 𝔸[F] {Sum.inl i} →
    bdet (Sum.inl '' (Set.univ : Set ι)) (j x).1 = x.1.1 * Units.map ν.toMonoidHom (bdet {Sum.inl i} (prj A ν ι x)) ∧
    Matrix.GeneralLinearGroup.det (prj A ν ι x) = bdet {Sum.inl i} (prj A ν ι x) * bdet {Sum.inr i} (prj A ν ι x)

def JIwa : Prop := ForJ fun {F} {_} {_} _ _ _ _ _ _ _ A _ ν {ι} _ _ i _ α _ j =>
  Iwa ((stab 𝔸[F] {Sum.inl i}).comap (prj A ν ι)) (cK α j)

def JRat : Prop := ForJ fun {F} {_} {_} _ _ _ _ _ _ _ A ε ν {ι} _ _ i _ _ _ j =>
  (cΓ A ν ι).map j = A.uΓ ε ι ∧
  ∀ g ∈ (adStd F).ratGL (ι ⊕ ι), ∃ γ ∈ cΓ A ν ι, g * (prj A ν ι γ)⁻¹ ∈ stab 𝔸[F] {Sum.inl i}

def JSec : Prop := ForJ fun {_} {_} {_} _ _ _ _ _ _ _ A ε ν {ι} _ _ _ _ α _ j =>
  ∃ s : A.uQ ε (Set.univ : Set ι) → cover A ν ι, Continuous s ∧ (∀ p, j (s p) = p) ∧
    ∀ p : A.uQ ε (Set.univ : Set ι), (p : A.U ε ι) ∈ A.uK ε ι → s p ∈ cK α j

def JCh : Prop := ForJ fun {_} {_} {_} _ _ _ _ _ _ _ A _ ν {ι} _ _ _ _ α _ j =>
  IsCh (cΓ A ν ι) ⊤ (c0 : cover A ν ι → ℂ) ∧ IsHt (cΓ A ν ι) (cK α j) ⊤ (ld : cover A ν ι → ℝ)

def JMir : Prop := ForJ fun {_} {_} {_} _ _ _ _ _ _ _ A ε ν {ι} _ _ i _ α ω j => Iwa (A.uQ ε (Set.univ : Set ι)) (A.uK ε ι) →
  MirData (prj A ν ι) (cΓ A ν ι) (cK α j) (Sum.inl i) (Sum.inr i) ω (Sum.elim (fun _ => 1) fun _ => α) (c1 j)
    (fun x => (A.uH ε Set.univ (j x) + ld x) / 2) (fun x => (A.uH ε Set.univ (j x) - ld x) / 2) ld

section CM

open scoped TensorProduct
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

def nuCM (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] : 𝔸[F] →+* AE F E :=
  (Algebra.TensorProduct.includeLeft : AF F →ₐ[F] AF F ⊗[F] E).toRingHom

def BFix : Prop := ForCM fun {F E} _ _ _ _ _ σ χ => Continuous (nuCM F E) ∧ Function.Injective (nuCM F E) ∧
  (∀ x, (adCM σ χ).σ (nuCM F E x) = nuCM F E x) ∧
  ∃ r : AE F E → 𝔸[F], Continuous r ∧ ∀ x, (adCM σ χ).σ x = x → nuCM F E (r x) = x

def BRat : Prop := ForCM fun {F E} _ _ _ _ _ σ χ =>
  (∀ y : F, nuCM F E (algebraMap F 𝔸[F] y) = (adCM σ χ).i (algebraMap F E y)) ∧
  ∀ (e : E) (x : 𝔸[F]), (adCM σ χ).i e = nuCM F E x → ∃ y : F, x = algebraMap F 𝔸[F] y

def BInt : Prop := ForCM fun {F E} _ _ _ _ _ σ χ => ∀ x, nuCM F E x ∈ (adCM σ χ).O ↔ x ∈ intAd F

def BInf : Prop := ForCM fun {F E} _ _ _ _ _ σ χ =>
  (∀ w : (adCM σ χ).W, ∃ v : InfinitePlace F, ∀ x, (adCM σ χ).φ w (nuCM F E x) = (adStd F).φ v x) ∧
  ∀ v : InfinitePlace F, ∃ w : (adCM σ χ).W, ∀ x, (adCM σ χ).φ w (nuCM F E x) = (adStd F).φ v x

def BLg : Prop := ForCM fun {F E} _ _ _ _ _ σ χ =>
  (∀ x : IdeleGroup F, (adCM σ χ).lg (Units.map (nuCM F E).toMonoidHom x) = 2 * (adStd F).lg x) ∧
  ∀ x : (AE F E)ˣ, (adCM σ χ).lg (Units.map (adCM σ χ).σ.toMonoidHom x) = (adCM σ χ).lg x

def BDel : Prop := ForCM fun {F E} _ _ _ _ _ σ χ => ∃ (δ : Eˣ) (α : IdeleGroup F) (u : (AE F E)ˣ), σ δ = -δ ∧
  (adCM σ χ).i δ = nuCM F E α * u ∧ (u : AE F E) ∈ (adCM σ χ).O ∧ ((u⁻¹ : (AE F E)ˣ) : AE F E) ∈ (adCM σ χ).O ∧
  ∀ w, ‖(adCM σ χ).φ w u‖ = 1

def BaseCM : Prop := ForCM fun {F E} _ _ _ _ _ σ χ => ∀ ε : ℤˣ, ∃ r δ α ω, Base (adCM σ χ) ε (nuCM F E) r δ α ω

end CM

end PositivityTheory.RgEis.So
