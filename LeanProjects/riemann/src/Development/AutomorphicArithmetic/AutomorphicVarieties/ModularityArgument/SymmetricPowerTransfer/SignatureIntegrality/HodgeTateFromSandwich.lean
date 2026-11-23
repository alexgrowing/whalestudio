import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.QuaternionDoubleCosetIndicator

noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

namespace UpperTheory.V.Z.Sym.Sig

open Classical Loc Glob

def OrbMap : Prop :=
  ∀ (T G G' : Type) [Group T] [Group G] [Group G'] (e : G →* G'), Function.Bijective e → ∀ (ι : T →* G) (C : Subgroup T) (θ : G →* G)
    (θ' : G' →* G'), (∀ g, e (θ g) = θ' (e g)) → ∀ (U' : Subgroup G') (f : G' → ℂ) (δ : G), (∀ u ∈ U', ∀ x, f (u⁻¹ * x * θ' u) = f x) →
    (∀ t, (ι t)⁻¹ * δ * θ (ι t) = δ) → C.Normal →
    orb ι C θ (U'.comap e) (fun g => f (e g)) δ = orb (e.comp ι) C θ' U' f (e δ) ∧
    (FinOrb ι θ (U'.comap e) (fun g => f (e g)) δ ↔ FinOrb (e.comp ι) θ' U' f (e δ)) ∧
    ∀ y : G, ((MulAction.stabilizer G (y : G ⧸ U'.comap e)).comap ι) = (MulAction.stabilizer G' (e y : G' ⧸ U')).comap (e.comp ι)

def EU : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (O : Type) [CommRing O] [Algebra O k], IsInts k O → (2 : k) ≠ 0 → ∀ (Δ s : k) (hs : s * s = Δ), s ≠ 0 →
    Function.Bijective (eU hs) ∧ (∀ g, eU hs (theta Δ g) = th k 3 (eU hs g)) ∧ (KO k (Fin 3)).comap (eU hs) = KU O Δ ∧
    ∀ (δ : U3 Δ) (τ : k), HasTau δ τ ↔
      ((eU hs δ * th k 3 (eU hs δ) : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k).charpoly = (X - 1) * (X ^ 2 - C τ * X + 1)

def ED : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (O : Type) [CommRing O] [Algebra O k], IsInts k O → (2 : k) ≠ 0 → ∀ (Δ s : k) (hs : s * s = Δ), s ≠ 0 →
    Function.Bijective (eD hs) ∧ (KO k (Fin 2)).comap (eD hs) = KD Δ O ∧
    (GeneralLinearGroup.scalar (Fin 2) : kˣ →* GL (Fin 2) k).range.comap (eD hs) = ZD Δ ∧
    (∀ (z : kˣ) (g : DX Δ), IsScal z g ↔ eD hs g = GeneralLinearGroup.scalar (Fin 2) z) ∧
    (∀ g : DX Δ, (mt g).det = algebraMap k _ (eD hs g : Matrix (Fin 2) (Fin 2) k).det ∧
      (mt g).trace = algebraMap k _ (eD hs g : Matrix (Fin 2) (Fin 2) k).trace) ∧
    ∀ V : Lev k, (V.ZJ 2).comap (eD hs) = ZD Δ ⊔ (V.J 2).comap (eD hs)

def Roots : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (O : Type) [CommRing O] [Algebra O k], IsInts k O → ∀ a : kˣ, valuation k (a : k) < 1 →
    Function.Surjective (evU (root_left a) / evU (root_right a)) ∧
    Cint O ((a : k) + (a⁻¹ : kˣ)) = (Uo k).comap (evU (root_left a) / evU (root_right a)) ∧
    ∀ z, ev (root_left a) (quo z) = (evU (root_left a) z / evU (root_right a) z : kˣ) ∧
      ev (root_right a) (quo z) = (evU (root_right a) z / evU (root_left a) z : kˣ)

def ModelG : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (O : Type) [CommRing O] [Algebra O k], IsInts k O → (2 : k) ≠ 0 → ∀ (Δ s : k) (hs : s * s = Δ), s ≠ 0 →
    (∀ (τ c : k) (d m : EL Δ τ) δ ι Q, IsDat c d m → Models c d m δ ι Q → HasTau δ τ ∧ ∀ t, (ι t)⁻¹ * δ * theta Δ (ι t) = δ) ∧
    ∀ a : kˣ, valuation k (a : k) < 1 → ∀ (c : k) (d m : EL Δ ((a : k) + (a⁻¹ : kˣ))) δ ι Q, IsDat c d m → Models c d m δ ι Q →
      ∃ (g₀ : GL (Fin 3) k) (x y z : kˣ), eU hs δ = g₀ * dg ![x, y, z] * Phi k * (th k 3 g₀)⁻¹ ∧ x / z = a ∧
        ∀ t, eU hs (ι t) = g₀ * dg ![(evU (root_left a) / evU (root_right a)) t, 1, ((evU (root_left a) / evU (root_right a)) t)⁻¹] * g₀⁻¹

def ModelD : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (O : Type) [CommRing O] [Algebra O k], IsInts k O → (2 : k) ≠ 0 → ∀ (Δ s : k) (hs : s * s = Δ), s ≠ 0 →
    ∀ a : kˣ, valuation k (a : k) < 1 → ∀ (γ : DX Δ) j, HasTr γ ((a : k) + (a⁻¹ : kˣ)) → IsEmb ((a : k) + (a⁻¹ : kˣ)) γ j →
      ∃ g₀ : GL (Fin 2) k, eD hs γ = g₀ * dg ![a, a⁻¹] * g₀⁻¹ ∧
        ∀ t, eD hs (j t) = g₀ * dg ![evU (root_left a) t, evU (root_right a) t] * g₀⁻¹

def StabFin : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (V : Lev k) (n : ℕ) (y : GL (Fin n) k), ∃ m : ℕ, ∀ u : Fin n → kˣ, (∀ i, u i ∈ Uc k m) → y⁻¹ * dg u * y ∈ V.J n

def Supp0 : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (V : Lev k) (d : Fin 3 → kˣ), SDom d → ∀ g, V.unitaryDoubleCosetIndicator d g ≠ 0 → ∃ (g₀ : GL (Fin 3) k) (x y z : kˣ),
    g = g₀ * dg ![x, y, z] * Phi k * (th k 3 g₀)⁻¹ ∧ x / z / (d 0 / d 2) ∈ V.H

def TwistedOrbitalIntegralGL3Formula : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (V : Lev k) (Ry : Finset kˣ), V.IsSqReps Ry → ∀ t : kˣ, valuation k (t : k) < valuation k (unif k : k) ^ 2 →
    ∀ (T : Type) [CommGroup T] (r : T →* kˣ), Function.Surjective r → ∀ (g₀ : GL (Fin 3) k) (ι : T →* GL (Fin 3) k),
    (∀ s, ι s = g₀ * dg ![r s, 1, (r s)⁻¹] * g₀⁻¹) → ∀ x y z : kˣ, valuation k ((x / z : kˣ) : k) < 1 →
    FinOrb ι (th k 3) (V.J 3) (V.unitaryHeckeTestSum Ry t) (g₀ * dg ![x, y, z] * Phi k * (th k 3 g₀)⁻¹) ∧
    orb ι ((Uo k).comap r) (th k 3) (V.J 3) (V.unitaryHeckeTestSum Ry t) (g₀ * dg ![x, y, z] * Phi k * (th k 3 g₀)⁻¹) =
      (V.H.relIndex (Uo k) : ℂ) * (V.H.relIndex V.H2 : ℂ) * one (x / z / t ∈ V.H)

def OrbitalIntegralGL2Formula : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (V : Lev k) (χ : kˣ →* ℂˣ), (∀ u ∈ Uo k, χ u = 1) → ∀ t : kˣ, valuation k (t : k) < 1 →
    ∀ (T : Type) [CommGroup T] (p q : T →* kˣ), Function.Surjective (p / q) → ∀ (g₀ : GL (Fin 2) k) (ι : T →* GL (Fin 2) k),
    (∀ s, ι s = g₀ * dg ![p s, q s] * g₀⁻¹) → ∀ a : kˣ, valuation k (a : k) < 1 →
    (FinOrb ι (MonoidHom.id _) (V.ZJ 2) (V.quaternionDoubleCosetIndicator t) (g₀ * dg ![a, a⁻¹] * g₀⁻¹) ∧
      orb ι ((Uo k).comap (p / q)) (MonoidHom.id _) (V.ZJ 2) (V.quaternionDoubleCosetIndicator t) (g₀ * dg ![a, a⁻¹] * g₀⁻¹) =
        (V.H.relIndex (Uo k) : ℂ) * one (a / t ∈ V.H)) ∧
    ∀ b : kˣ, (b : k) = 1 + (a⁻¹ : kˣ) →
      FinOrb ι (MonoidHom.id _) (V.ZJ 2) (V.twistedCentralTestFunction χ t) (g₀ * dg ![a * b, b] * g₀⁻¹) ∧
      orb ι ((Uo k).comap (p / q)) (MonoidHom.id _) (V.ZJ 2) (V.twistedCentralTestFunction χ t) (g₀ * dg ![a * b, b] * g₀⁻¹) =
        (V.H.relIndex (Uo k) : ℂ) * one (a / t ∈ V.H)

def IndIff : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (V : Lev k) (t a : kˣ), valuation k (t : k) < 1 → valuation k (a : k) < 1 → (Ind V.H ((a : k) + (a⁻¹ : kˣ)) t ↔ a / t ∈ V.H)

def OkLev : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (O : Type) [CommRing O] [Algebra O k], IsInts k O → (2 : k) ≠ 0 → ∀ (Δ s : k) (hs : s * s = Δ), s ≠ 0 → ∀ (V : Lev k) (Ry : Finset kˣ), V.IsSqReps Ry → ∀ χ : kˣ →* ℂˣ, (∀ u ∈ Uo k, χ u = 1) →
    (V.data hs Ry χ).J ≤ KU O Δ ∧ (V.data hs Ry χ).J.relIndex (KU O Δ) ≠ 0 ∧ (V.data hs Ry χ).J2 ≤ KD Δ O ∧
      (V.data hs Ry χ).J2.relIndex (KD Δ O) ≠ 0 ∧ 0 < (V.data hs Ry χ).cG ∧ 0 < (V.data hs Ry χ).cS ∧
      ∀ t ∈ (V.data hs Ry χ).P, ∀ τ, Ind V.H τ t → IsSquare (τ ^ 2 - 4) ∧ ¬ IsIntegral O τ

def OkG : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (O : Type) [CommRing O] [Algebra O k], IsInts k O → (2 : k) ≠ 0 → ∀ (Δ s : k) (hs : s * s = Δ), s ≠ 0 → ∀ (V : Lev k) (Ry : Finset kˣ), V.IsSqReps Ry → ∀ χ : kˣ →* ℂˣ, (∀ u ∈ Uo k, χ u = 1) →
    ∀ t ∈ (V.data hs Ry χ).P, let S := V.data hs Ry χ
      (∀ u ∈ S.J, ∀ y, S.fG t (u * y) = S.fG t y ∧ S.fG t (y * theta Δ u) = S.fG t y) ∧
      {x : U3 Δ ⧸ S.J | S.fG t (theta Δ x.out) ≠ 0}.Finite ∧ ∀ δ τ, HasTau δ τ → S.fG t δ ≠ 0 → Ind S.H τ t

def OkGOrb : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (O : Type) [CommRing O] [Algebra O k], IsInts k O → (2 : k) ≠ 0 → ∀ (Δ s : k) (hs : s * s = Δ), s ≠ 0 → ∀ (V : Lev k) (Ry : Finset kˣ), V.IsSqReps Ry → ∀ χ : kˣ →* ℂˣ, (∀ u ∈ Uo k, χ u = 1) →
    ∀ t ∈ (V.data hs Ry χ).P, let S := V.data hs Ry χ
      ∀ (τ c : k) (d m : EL Δ τ) δ ι Q, IsDat c d m → Models c d m δ ι Q →
      FinOrb ι (theta Δ) S.J (S.fG t) δ ∧ orb ι (Cint O τ) (theta Δ) S.J (S.fG t) δ = S.cG * one (Ind S.H τ t) ∧
      (Ind S.H τ t → ∀ y : U3 Δ ⧸ S.J, ((MulAction.stabilizer (U3 Δ) y).comap ι).relIndex (Cint O τ) ≠ 0)

def OkS : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (O : Type) [CommRing O] [Algebra O k], IsInts k O → (2 : k) ≠ 0 → ∀ (Δ s : k) (hs : s * s = Δ), s ≠ 0 → ∀ (V : Lev k) (Ry : Finset kˣ), V.IsSqReps Ry → ∀ χ : kˣ →* ℂˣ, (∀ u ∈ Uo k, χ u = 1) →
    ∀ t ∈ (V.data hs Ry χ).P, let S := V.data hs Ry χ
      (∀ u ∈ S.J2, ∀ y, S.fS t (u * y) = S.fS t y ∧ S.fS t (y * u) = S.fS t y) ∧
      {x : SU Δ ⧸ S.J2.subgroupOf (SU Δ) | S.fS t x.out ≠ 0}.Finite ∧ ∀ γ τ, HasTr γ τ → S.fS t γ ≠ 0 → Ind S.H τ t

def OkK : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (O : Type) [CommRing O] [Algebra O k], IsInts k O → (2 : k) ≠ 0 → ∀ (Δ s : k) (hs : s * s = Δ), s ≠ 0 → ∀ (V : Lev k) (Ry : Finset kˣ), V.IsSqReps Ry → ∀ χ : kˣ →* ℂˣ, (∀ u ∈ Uo k, χ u = 1) →
    ∀ t ∈ (V.data hs Ry χ).P, let S := V.data hs Ry χ
      ((∀ u ∈ S.J2, ∀ y, S.fK t (u * y) = S.fK t y ∧ S.fK t (y * u) = S.fK t y) ∧
        ∀ z s', IsScal z s' → ∀ y, S.fK t (s' * y) = ((χ z)⁻¹ : ℂˣ) * S.fK t y) ∧
      {x : DX Δ ⧸ (ZD Δ ⊔ S.J2) | S.fK t x.out ≠ 0}.Finite ∧
      ∀ g, S.fK t g ≠ 0 → ∃ τ, Ind S.H τ t ∧ (mt g).trace ^ 2 = algebraMap k _ (2 + τ) * (mt g).det

def OkDOrb : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (O : Type) [CommRing O] [Algebra O k], IsInts k O → (2 : k) ≠ 0 → ∀ (Δ s : k) (hs : s * s = Δ), s ≠ 0 → ∀ (V : Lev k) (Ry : Finset kˣ), V.IsSqReps Ry → ∀ χ : kˣ →* ℂˣ, (∀ u ∈ Uo k, χ u = 1) →
    ∀ t ∈ (V.data hs Ry χ).P, let S := V.data hs Ry χ
      ∀ τ γ j, τ ^ 2 - 4 ≠ 0 → HasTr γ τ → IsEmb τ γ j → ∀ z : (Etau k τ)ˣ, (z : Etau k τ) = 1 + QuadraticAlgebra.omega →
      FinOrb j (MonoidHom.id _) (ZD Δ ⊔ S.J2) (S.fS t) γ ∧ FinOrb j (MonoidHom.id _) (ZD Δ ⊔ S.J2) (S.fK t) (j z) ∧
      orb j (Cint O τ) (MonoidHom.id _) (ZD Δ ⊔ S.J2) (S.fS t) γ = S.cS * one (Ind S.H τ t) ∧
      orb j (Cint O τ) (MonoidHom.id _) (ZD Δ ⊔ S.J2) (S.fK t) (j z) = S.cK * one (Ind S.H τ t) ∧
      (Ind S.H τ t → ∀ y : DX Δ ⧸ (ZD Δ ⊔ S.J2), ((MulAction.stabilizer (DX Δ) y).comap j).relIndex (Cint O τ) ≠ 0)

def SigMain : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (O : Type) [CommRing O] [Algebra O k], IsInts k O → (2 : k) ≠ 0 → ∀ (Δ s : k) (hs : s * s = Δ), s ≠ 0 → ∀ (V : Lev k) (Ry : Finset kˣ), V.IsSqReps Ry → ∀ χ : kˣ →* ℂˣ, (∀ u ∈ Uo k, χ u = 1) →
    SigOk O χ (V.data hs Ry χ)

end UpperTheory.V.Z.Sym.Sig

end
