import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.GlobIn

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.So

def DatOk : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Δ : F) (A : SD Δ), A.Ok → A.dat.Ok ∧ (∀ t, A.dat.Cone t ↔ A.Cone t) ∧ (∀ v ∈ A.Sg, IsInts (Kv v) (Ov v) ∧ (2 : Kv v) ≠ 0 ∧ A.s v ≠ 0 ∧
    (∀ u ∈ Uo (Kv v), A.χ v u = 1) ∧ A.χ v = absPow (Kv v) 1) ∧
    (∀ g : GA Δ, g ∈ A.dat.UG ↔ (∀ v (h : v ∈ A.Sg), eU (A.hs v h) (g.1 v) ∈ (A.V v).J 3) ∧ ∀ v ∉ A.Sg, g.1 v ∈ KU (Ov v) _) ∧
    ∀ g : DA Δ, g ∈ A.dat.U2 ↔ (∀ v (h : v ∈ A.Sg), eD (A.hs v h) (g.1 v) ∈ (A.V v).J 2) ∧ ∀ v ∉ A.Sg, g.1 v ∈ KD _ (Ov v)

def ElEx : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Δ : F) (A : SD Δ), A.Ok → (∀ d, ∃! g, A.IsElG g d) ∧ (∀ d, ∃! g, A.IsElD g d) ∧
    (∀ g g' d d', A.IsElG g d → A.IsElG g' d' → A.IsElG (g * g') (d * d')) ∧
    (∀ g g' d d', A.IsElD g d → A.IsElD g' d' → A.IsElD (g * g') (d * d')) ∧ ∀ g t, A.IsElD g (SD.dS t) → g ∈ SA Δ

def OpDc : Prop :=
  ∀ (Γ G V : Type) [Group Γ] [Group G] [AddCommGroup V] [Module ℂ V] (B : Base Γ G V), B.ω = 1 → ∀ g : G, AlgebraTools.FinOrb B.U B.U g →
    (Base.Tw.one B).IsTest (fun y => one (y ∈ DC B.U g)) ∧
    ∀ φ : B.Forms, ((Base.Tw.one B).R (fun y => one (y ∈ DC B.U g)) φ).1 = dcF B.U g φ.1

def DcBasic : Prop :=
  ∀ (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V] (U : Subgroup G) (a : G), AlgebraTools.FinOrb U U a → ∀ φ : G → V, (∀ u ∈ U, ∀ g, φ (g * u) = φ g) →
    (∀ u ∈ U, ∀ g, dcF U a φ (g * u) = dcF U a φ g) ∧ (∀ g, dcF U a φ g = ∑ᶠ (y : G ⧸ U) (_ : y.out ∈ DC U a), φ (g * y.out)) ∧
    (∀ b ∈ DC U a, dcF U b φ = dcF U a φ) ∧ (a ∈ U → dcF U a φ = φ) ∧
    ∀ R : Finset G, (∀ y ∈ R, y ∈ DC U a) → (∀ y ∈ DC U a, ∃! r, r ∈ R ∧ r⁻¹ * y ∈ U) → ∀ g, dcF U a φ g = ∑ r ∈ R, φ (g * r)

def UFMul : Prop :=
  ∀ (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V] (U : Subgroup G) (a b : G), AlgebraTools.FinOrb U U a → AlgebraTools.FinOrb U U b → AlgebraTools.FinOrb U U (a * b) → UF U a b →
    ∀ φ : G → V, (∀ u ∈ U, ∀ g, φ (g * u) = φ g) → dcF U a (dcF U b φ) = dcF U (a * b) φ

def UFBox : Prop :=
  ∀ (I G : Type) [Group G] (Gv : I → Type) [∀ v, Group (Gv v)] (K U : ∀ v, Subgroup (Gv v)) (P : RPG G Gv K) (S : Finset I),
    (∀ v ∉ S, U v = K v) → ∀ a : G, (∀ v ∉ S, P.p v a ∈ U v) →
    (∀ g, g ∈ DC (P.box U) a ↔ (∀ v ∈ S, P.p v g ∈ DC (U v) (P.p v a)) ∧ ∀ v ∉ S, P.p v g ∈ U v) ∧
    ((∀ v ∈ S, AlgebraTools.FinOrb (U v) (U v) (P.p v a)) → AlgebraTools.FinOrb (P.box U) (P.box U) a) ∧
    ∀ b : G, (∀ v ∉ S, P.p v b ∈ U v) → (∀ v ∈ S, UF (U v) (P.p v a) (P.p v b)) → UF (P.box U) a b

def DcMap : Prop :=
  ∀ (G G' V : Type) [Group G] [Group G'] [AddCommGroup V] [Module ℂ V] (e : G →* G'), Function.Bijective e → ∀ (U' : Subgroup G') (a b : G),
    (∀ g, g ∈ DC (U'.comap e) a ↔ e g ∈ DC U' (e a)) ∧ (AlgebraTools.FinOrb (U'.comap e) (U'.comap e) a ↔ AlgebraTools.FinOrb U' U' (e a)) ∧
    (UF (U'.comap e) a b ↔ UF U' (e a) (e b)) ∧
    (AlgebraTools.FinOrb U' U' (e a) → ∀ φ : G' → V, (∀ u ∈ U', ∀ g, φ (g * u) = φ g) →
      dcF (U'.comap e) a (φ ∘ e) = dcF U' (e a) φ ∘ e)

def DcSub : Prop :=
  ∀ (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V] (S U : Subgroup G) (a : S), AlgebraTools.FinOrb U U (a : G) →
    (∀ u ∈ U, ∃ c ∈ U, c * a = a * c ∧ u * c⁻¹ ∈ S ∧ c⁻¹ * u ∈ S) → S.Normal →
    AlgebraTools.FinOrb (U.subgroupOf S) (U.subgroupOf S) a ∧ (∀ g : S, g ∈ DC (U.subgroupOf S) a ↔ (g : G) ∈ DC U a) ∧
    (∀ b : S, (∀ u ∈ U, ∃ c ∈ U, c * a = a * c ∧ c * b = b * c ∧ u * c⁻¹ ∈ S ∧ c⁻¹ * u ∈ S) → UF U a b → UF (U.subgroupOf S) a b) ∧
    ∃ R : Finset S, (∀ y ∈ R, y ∈ DC (U.subgroupOf S) a) ∧ (∀ y ∈ DC (U.subgroupOf S) a, ∃! r, r ∈ R ∧ r⁻¹ * y ∈ U.subgroupOf S) ∧
      ∀ y ∈ DC U a, ∃! r : S, r ∈ R ∧ (r : G)⁻¹ * y ∈ U

def DcLocal : Prop :=
  ∀ (H G V : Type) [Group H] [Group G] [AddCommGroup V] [Module ℂ V] (j : H →* G) (p : G →* H) (J : Subgroup H) (U : Subgroup G),
    (∀ h, p (j h) = h) → (∀ u ∈ U, p u ∈ J ∧ ∀ h, u * (j (p u))⁻¹ * j h = j h * (u * (j (p u))⁻¹)) → (∀ h ∈ J, j h ∈ U) →
    ∀ d : H, AlgebraTools.FinOrb J J d → AlgebraTools.FinOrb U U (j d) ∧ ∀ φ : G → V, (∀ u ∈ U, ∀ g, φ (g * u) = φ g) →
      dcF U (j d) φ = dc ((rightReg ℂ G V).comp j) J J d φ

def ExpoEq : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a : kˣ →* ℂˣ),
    (∀ d : Fin 3 → kˣ, Dict.expo ![a, 1, a⁻¹] d = a (d 0 / d 2) * absPow k (-1) (d 0 / d 2)) ∧
    (∀ t : kˣ, Dict.expo ![a, 1] ![t, t⁻¹] = a t * absPow k (-1) t) ∧
    ∀ (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), (∀ d, Dict.expo ψ d ≠ 0) ∧ Dict.expo ψ 1 = 1 ∧ ∀ d d', Dict.expo ψ (d * d') = Dict.expo ψ d * Dict.expo ψ d'

def CharShape : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Δ : F) (A : SD Δ), A.Ok → ∀ χ : ParN F 3 → ℂ, (∀ d d', A.DomS d → A.DomS d' → χ (d * d') = χ d * χ d') →
    (∀ d, (∀ v ∈ A.Sg, ∀ i, d v i ∈ (A.V v).H) → χ d = 1) → (∀ d, A.DomS d → χ (SD.sg d) = χ d) →
    ∃ (b : ℂ) (β : Dat.Par F → ℂ), (∀ t t', A.Cone t → A.Cone t' → β (t * t') = β t * β t') ∧
      (∀ t, A.Cone t → ∑ y ∈ A.Ys, χ (A.dG t y) = b * β t) ∧
      (b ≠ 0 → ∀ a : Chs F, (∀ t, A.Cone t → β t = A.exS a t) → ∀ d, A.DomS d → χ d = A.exG a d)

def GOpsEx : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Δ : F) (A : SD Δ), A.Ok → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ch : F → ℂ) (B : Base (U3 Δ) (GA Δ) V) (s : B.Tw), A.dat.IsBG ch B s → ∃ u Θ, A.GOps B s u Θ

def UnitaryThreeTestFunctionHeckeRelations : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Δ : F) (A : SD Δ), A.Ok → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ch : F → ℂ) (B : Base (U3 Δ) (GA Δ) V) (s : B.Tw), A.dat.IsBG ch B s →
    (∀ d g, A.IsElG g d → s.IsTest (A.F0 d) ∧
      s.R (A.F0 d) = (Base.Tw.one B).R (fun y => one (y ∈ DC B.U g)) * s.R (A.F0 1) ∧
      s.R (A.F0 (SD.sg d)) = s.R (A.F0 1) * (Base.Tw.one B).R (fun y => one (y ∈ DC B.U g))) ∧
    ∀ t, A.Cone t → A.dat.FG t = fun g => ∑ y ∈ A.Ys, A.F0 (A.dG t y) g

def GSpec : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Δ : F) (A : SD Δ), A.Ok → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (B : Base (U3 Δ) (GA Δ) V) (s : B.Tw) [FiniteDimensional ℂ B.Forms] u Θ, A.GOps B s u Θ →
    ∃ (I : Type) (X : Finset I) (b : I → ℂ) (β : I → Dat.Par F → ℂ),
      (∀ i ∈ X, ∀ t t', A.Cone t → A.Cone t' → β i (t * t') = β i t * β i t') ∧
      (∀ t, A.Cone t → LinearMap.trace ℂ B.Forms (s.R (A.dat.FG t)) = ∑ i ∈ X, b i * β i t) ∧
      ∀ i ∈ X, b i ≠ 0 → ∀ a : Chs F, (∀ t, A.Cone t → β i t = A.exS a t) → ∃ φ ∈ B.Forms, φ ≠ 0 ∧ A.EigG φ a

def SOps : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Δ : F) (A : SD Δ), A.Ok → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ch : F → ℂ) (x : DA Δ) (B : Base (SU Δ) (SA Δ) V), A.dat.Off x → A.dat.IsBS ch x B →
    (∀ t (g : SA Δ), A.Cone t → A.IsElD g (SD.dS t) → AlgebraTools.FinOrb B.U B.U g ∧ A.dat.FSx t x = fun y => one (y ∈ DC B.U g)) ∧
    (∀ t (g : SA Δ), A.Cone t → A.IsElD g (SD.dS t) → ∀ φ : B.Forms, ((Base.Tw.one B).R (A.dat.FSx t x) φ).1 = dcF B.U g φ.1) ∧
    ∀ t t', A.Cone t → A.Cone t' → (Base.Tw.one B).R (A.dat.FSx (t * t') x) =
      (Base.Tw.one B).R (A.dat.FSx t x) * (Base.Tw.one B).R (A.dat.FSx t' x)

def TorPart : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Δ : F) (A : SD Δ), A.Ok → ∀ u ∈ A.dat.U2, ∃ c ∈ A.dat.U2, u * c⁻¹ ∈ SA Δ ∧ c⁻¹ * u ∈ SA Δ ∧ ∀ g d, A.IsElD g d → c * g = g * c

def KOps : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Δ : F) (A : SD Δ), A.Ok → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ch : F → ℂ) (B : Base (DX Δ) (DA Δ) V), A.dat.IsBK ch B →
    (∀ t g, A.Cone t → A.IsElD g (fun v => ![t v, 1]) → ∀ φ : B.Forms,
      ((Base.Tw.one B).R (A.dat.FK t) φ).1 = (∏ v ∈ A.Sg, (((A.χ v (t v))⁻¹ : ℂˣ) : ℂ)) • dcF A.dat.U2 g φ.1) ∧
    (∀ φ ∈ B.Forms, ∀ u ∈ A.dat.U2, ∀ g, φ (g * u) = φ g) ∧
    ∀ φ ∈ B.Forms, ∀ (z : Dat.Par F) s, A.IsElD s (fun v => ![z v, z v]) → ∀ g, φ (g * s) = (∏ v ∈ A.Sg, (A.χ v (z v) : ℂ)) • φ g

def KSpec : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Δ : F) (A : SD Δ), A.Ok → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ch : F → ℂ) (B : Base (DX Δ) (DA Δ) V), A.dat.IsBK ch B →
    (∀ t t', A.Cone t → A.Cone t' → (Base.Tw.one B).R (A.dat.FK (t * t')) = (Base.Tw.one B).R (A.dat.FK t) * (Base.Tw.one B).R (A.dat.FK t')) ∧
    ∀ (a : Chs F) (φ : B.Forms), (∀ t, A.Cone t → (Base.Tw.one B).R (A.dat.FK t) φ = A.exS a t • φ) → A.EigK φ.1 (a ^ 2)

def DMul : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Δ : F) (A : SD Δ), A.Ok → ∀ g d, A.IsElD g d → AlgebraTools.FinOrb A.dat.U2 A.dat.U2 g ∧ ∀ g' d', A.IsElD g' d' → A.DomS d → A.DomS d' → UF A.dat.U2 g g'

def PosSpec : Prop :=
  ∀ (P N I J : Type) [CommSemigroup P] [Fintype J] [AddCommGroup N] [Module ℂ N] [FiniteDimensional ℂ N] (Mi : J → Type) [∀ j, AddCommGroup (Mi j)]
    [∀ j, Module ℂ (Mi j)] [∀ j, FiniteDimensional ℂ (Mi j)] (u : ∀ j, P → Module.End ℂ (Mi j)) (w : P → Module.End ℂ N),
    (∀ j p q, u j (p * q) = u j p * u j q) → (∀ p q, w (p * q) = w p * w q) →
    ∀ (X : Finset I) (b : I → ℂ) (β : I → P → ℂ), (∀ i ∈ X, ∀ p q, β i (p * q) = β i p * β i q) → ∀ a c : ℝ, 0 < a →
    (∀ p, ∑ i ∈ X, b i * β i p = a * ∑ j, LinearMap.trace ℂ (Mi j) (u j p) + c * LinearMap.trace ℂ N (w p)) →
    ∀ χ : P → ℂ, χ ≠ 0 → (∃ j, ∃ v : Mi j, v ≠ 0 ∧ ∀ p, u j p v = χ p • v) →
    (∃ i ∈ X, b i ≠ 0 ∧ β i = χ) ∨ ∃ v : N, v ≠ 0 ∧ ∀ p, w p v = χ p • v

end UpperTheory.V.Z.Sym.So

end
