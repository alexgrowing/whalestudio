import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsClosedImmersionIffPullRatio
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.ZH
open ReciprocityTheory.ChartRestriction.G.Out Classical
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

def GenVal {S : ThetaSys o Ω} (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (u₀ : U₀.toScheme ⟶ Sp S.R) (G : Over M.Z)
    (φ : pullback ρ.P.A.hom u₀ ⟶ G.left) (L : LB G.left) (w : LB.Iso (L.pull φ) (ρ.P.L.pull (pullback.fst ρ.P.A.hom u₀)))
    (k : ℤ) {I : Type} [Fintype I] (t : I → LB.Sec (LPow ρ.P.A ρ.P.L k (baseOver (Sp S.R)))) (c : I → Ω) (V : G.left.Opens)
    (σ : ∀ j, Γ(G.left, V ⊓ (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => k)).U j)) : Prop :=
  ∀ (K : Type) [Field K] (β : Ω →+* K) (g : Sp K ⟶ pullback ρ.P.A.hom u₀) (r : Sp K ⟶ (baseOver (Sp S.R) ⊗ ρ.P.A).left)
    (jP : ρ.P.L.ι) (jL : L.ι), g ≫ pullback.snd _ _ ≫ U₀.ι = spMap β ≫ M.pt →
    r ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left = g ≫ pullback.fst _ _ →
    Set.range (g ≫ pullback.fst ρ.P.A.hom u₀) ⊆ ρ.P.L.U jP → Set.range (g ≫ φ) ⊆ L.U jL → Set.range (g ≫ φ) ⊆ V →
    ∑ i, β (c i) * valF r _ ((t i).f (fun _ => jP)) =
      valF g _ (w.s (fun _ => jP, fun _ => jL)).val ^ k * valF (g ≫ φ) _ (σ (fun _ => jL))

def ImmersedBy {X Z : Scheme.{0}} (f : X ⟶ Z) (s : Z ⟶ Sp o) (B : LB X) (V : X.Opens) {J : Type}
    (σ : J → ∀ j, Γ(X, V ⊓ B.U j)) : Prop :=
  ∃ (m : ℕ) (e : Fin (m + 1) ≃ J) (π : V.toScheme ⟶ PSpace o m) (h : π ≫ PSpace.str o m = (V.ι ≫ f) ≫ s),
    IsImmersion (pullback.lift π (V.ι ≫ f) h) ∧
    ∀ (i : Fin (m + 1)) (j : B.ι) (T : V.toScheme.Opens) (hi : T ≤ π ⁻¹ᵁ ProjSpace.chart o m i)
      (hj : T ≤ V.ι ⁻¹ᵁ (V ⊓ B.U j)), IsUnit ((V.ι.appLE _ T hj).hom (σ (e i) j)) ∧
        ∀ k, (V.ι.appLE _ T hj).hom (σ (e k) j) = ProjSpace.pullRatio π T i hi k * (V.ι.appLE _ T hj).hom (σ (e i) j)

structure ZHOut {S : ThetaSys o Ω} (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) where
  u₀ : U₀.toScheme ⟶ Sp S.R
  u₀_gen : ∀ x : Sp Ω ⟶ U₀.toScheme, x ≫ U₀.ι = M.pt → x ≫ u₀ = spMap S.R.val.toRingHom
  G : Over M.Z
  [grp : GrpObj G]
  [comm : IsCommMonObj G]
  semi : IsSemiAbelian G
  dim : SmoothOfRelativeDimension S.g G.hom
  qproj : IsQProjOver (G.hom ≫ M.s)
  φ : pullback ρ.P.A.hom u₀ ⟶ G.left
  cart : IsGrpPullback ((Over.pullback u₀).obj ρ.P.A) G U₀.ι φ
  L : RigLB G
  cub : CubicalStr G L
  sym : L.IsSymmetric
  w : LB.Iso (L.L.pull φ) (ρ.P.L.pull (pullback.fst ρ.P.A.hom u₀))
  w_gen : w.IsGen

  w_rig : ∀ (K : Type) [Field K] (g : Sp K ⟶ pullback ρ.P.A.hom u₀) (x : Sp K ⟶ M.Z) (y : Sp K ⟶ Sp S.R)
    (jP : ρ.P.L.ι) (jL : L.L.ι), g ≫ φ = x ≫ eSec G → g ≫ pullback.fst _ _ = y ≫ eSec ρ.P.A →
    Set.range (g ≫ pullback.fst ρ.P.A.hom u₀) ⊆ ρ.P.L.U jP → Set.range (g ≫ φ) ⊆ L.L.U jL →
    valF y _ (ρ.rig.s (fun _ => jP)).val =
      valF g _ (w.s (fun _ => jP, fun _ => jL)).val * valF x _ (L.rig.s (fun _ => jL)).val
  hypS : HypS G L.L

  endo : ∀ f : (Over.pullback M.pt).obj G ⟶ (Over.pullback M.pt).obj G, IsMonHom f →
    ∃! F : G ⟶ G, IsMonHom F ∧ (Over.pullback M.pt).map F = f
  isoExt : ∀ (n : ℕ) (x x' : Fin n → (G ⊗ G ⟶ G)), (∀ i, IsMonHom (x i) ∧ IsMonHom (x' i)) → ∀ ε ε' : Fin n → ℤ, ∑ i, ε i = 0 → ∑ i, ε' i = 0 →
    LBIso ((LB.LinComb L.L (fun i => (x i).left) ε).pull (pullback.fst (G ⊗ G).hom M.pt))
      ((LB.LinComb L.L (fun i => (x' i).left) ε').pull (pullback.fst (G ⊗ G).hom M.pt)) →
    LBIso (LB.LinComb L.L (fun i => (x i).left) ε) (LB.LinComb L.L (fun i => (x' i).left) ε')
  split : ∀ z : M.Z, ∃ E : SplitExt (Sp (M.Z.residueField z)),
    E.IsGt ((Over.pullback (M.Z.fromSpecResidueField z)).obj G)
  ab : abLocus G = {z | S.TT M z = ⊥}

  pol : ∀ W : M.Z.Opens, (W : Set M.Z) ⊆ abLocus G →
    RelAmple ((Over.pullback W.ι).obj G) (L.L.pull (pullback.fst G.hom W.ι)) ∧
    KTriv ((Over.pullback W.ι).obj G) (L.L.pull (pullback.fst G.hom W.ι))

  sec : ∀ z, ∀ a ∈ S.HH M z, ∃ (W : M.Z.Opens) (h : W.toScheme ⟶ G.left), z ∈ W ∧ h ≫ G.hom = W.ι ∧
    ∀ (x : Sp Ω ⟶ W.toScheme) (x' : Sp Ω ⟶ pullback ρ.P.A.hom u₀), x ≫ W.ι = M.pt → x' ≫ φ ≫ G.hom = M.pt →
      x' ≫ pullback.fst _ _ = spMap S.R.val.toRingHom ≫ (ρ.pt a).left → x ≫ h = x' ≫ φ

  unif : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R], IsNoetherianRing R → IsIntegrallyClosed R →
    IsAdicComplete (IsLocalRing.maximalIdeal R) R → ∀ (ξ : Sp R ⟶ M.Z), (ξ ⁻¹' abLocus G).Nonempty →
    ∀ [IsCommMonObj ((Over.pullback ξ).obj G)],
    ∃ (D : DegData R (IsLocalRing.maximalIdeal R)) (A : PolAV (Sp (FractionRing R)))
      (U : Unif (IsLocalRing.maximalIdeal R) D A ((Over.pullback ξ).obj G)),
      LBIso U.LG.L (L.L.pull (pullback.fst G.hom ξ)) ∧ ∀ y, PsiUnitOn D.toPre y (ξ ⁻¹' abLocus G)

  theta : ∀ (W : M.Z.Opens) (x₀ : S.Gam), (∀ z ∈ W, x₀ ∈ S.supI M z) →
    ∃ σ ∈ secOn (LB.LinComb L.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 1)) (G.hom ⁻¹ᵁ W),
      GenVal ρ M U₀ u₀ G φ L.L w 1 (fun _ : Unit => ρ.th₁) (fun _ => (S.th x₀)⁻¹) _ σ ∧
      ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ M.Z), Set.range x ⊆ W →
        ∃ (g : Sp K ⟶ G.left) (j : _), g ≫ G.hom = x ∧ valF g _ (σ j) ≠ 0

  secOf : ∀ (W : M.Z.Opens) (x₀ : S.Gam) (v : S.J → Ω), (∀ z ∈ W, x₀ ∈ S.supI M z ∧ v ∈ EE.E z) →
    ∃ σ ∈ secOn (LB.LinComb L.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (S.N : ℤ))) (G.hom ⁻¹ᵁ W),
      GenVal ρ M U₀ u₀ G φ L.L w S.N ρ.s (fun l => v l / S.th x₀) _ σ

  sections : ∀ (W : M.Z.Opens) (x₀ : S.Gam) (b : Matrix S.J S.J Ω),
    (∀ z ∈ W, x₀ ∈ S.supI M z ∧ EE.E z = Submodule.span (M.O z) (Set.range b)) →
    ∃ σ : S.J → ∀ j, Γ(G.left, G.hom ⁻¹ᵁ W ⊓ (LB.LinComb L.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (S.N : ℤ))).U j),
      (∀ i, σ i ∈ secOn (LB.LinComb L.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (S.N : ℤ))) (G.hom ⁻¹ᵁ W) ∧
        GenVal ρ M U₀ u₀ G φ L.L w S.N ρ.s (fun l => b i l / S.th x₀) _ (σ i)) ∧
      ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ M.Z), Set.range x ⊆ W →
        (∀ g : Sp K ⟶ G.left, g ≫ G.hom = x → ∃ i j, valF g _ (σ i j) ≠ 0) ∧
        ∀ c : S.J → K, (∀ (g : Sp K ⟶ G.left) (j : _), g ≫ G.hom = x → ∑ i, c i * valF g _ (σ i j) = 0) → c = 0

  imm : ∀ (W : M.Z.Opens) (x₀ : S.Gam) (b : Matrix S.J S.J Ω),
    (∀ z ∈ W, x₀ ∈ S.supI M z ∧ EE.E z = Submodule.span (M.O z) (Set.range b)) →
    ∀ σ : S.J → ∀ j, Γ(G.left, G.hom ⁻¹ᵁ W ⊓ (LB.LinComb L.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (S.N : ℤ))).U j),
      (∀ i, σ i ∈ secOn (LB.LinComb L.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (S.N : ℤ))) (G.hom ⁻¹ᵁ W) ∧
        GenVal ρ M U₀ u₀ G φ L.L w S.N ρ.s (fun l => b i l / S.th x₀) _ (σ i)) →
      ImmersedBy G.hom M.s (LB.LinComb L.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (S.N : ℤ))) (G.hom ⁻¹ᵁ W) σ
attribute [instance] ZHOut.grp ZHOut.comm

def ZHGeoSt : Prop :=
  ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real), S.Big →
    ∀ (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), S.Over₀ M U₀ → S.IsEE M U₀ EE →
    (∃ (n a : ℕ) (GG : Fin n → S.J → Ω), ∀ z : M.Z, ∀ x₀ ∈ S.supI M z, ∀ w : S.J → Ω,
      w ∈ Submodule.span (M.O z) (Set.range fun k j => GG k j / S.th x₀ ^ a) ↔ ∀ v ∈ EE.E z, w ⬝ᵥ v ∈ M.O z) →
    Nonempty (ZHOut ρ M U₀ EE)

def ZHSt : Prop :=
  ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real), S.Big →
    ∀ (J₀ : Type) [Fintype J₀] (t₀ : J₀ → Ω), (∃ i, t₀ i ≠ 0) →
    Module.Finite (Subfield.closure (Set.range (algebraMap o Ω) ∪
      {x | ∃ i j : S.Gam × J₀, x = S.th j.1 * t₀ j.2 / (S.th i.1 * t₀ i.2)})) Ω →
    ∃ (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), S.Over₀ M U₀ ∧ M.HasDiv t₀ ∧ S.IsEE M U₀ EE ∧
      Nonempty (ZHOut ρ M U₀ EE)
end GlobalTheory.ZH
end
