import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
import Formalism.LocalToGlobal.ProjectiveLattices.IntAll

noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Char

variable {D : D7} {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}

def CUnit (c : Comp → ℂ) : Prop := ∀ k, ‖c k‖ = 1

def muPin (V : HSp D) {X : Comp → Data E r} (dict : GA D V → Σ k, Frame (X k).Ψ r) (mu : GA D V → ℂ)
    (c : Comp → ℂ) : GA D V → ℂ :=
  fun g => c (dict g).1 * mu g

theorem adel_muPin (V : HSp D) {X : Comp → Data E r} (dict : GA D V → Σ k, Frame (X k).Ψ r) (mu : GA D V → ℂ)
    (c : Comp → ℂ) (P : FDSec X) (g : GA D V) :
    adel V dict (muPin V dict mu c) P g = c (dict g).1 * mu g * P (dict g).1 (dict g).2 := rfl

def MuVal (V : HSp D) (χ : (AE D)ˣ →* Circle) (mu : GA D V → ℂ) : Prop :=
  (∀ g, ∃ x, IsDetRoot V g x) ∧ ∀ g x, IsDetRoot V g x → mu g = ((χ x : Circle) : ℂ)

theorem MuVal.norm {V : HSp D} {χ : (AE D)ˣ →* Circle} {mu : GA D V → ℂ} (h : MuVal V χ mu) (g : GA D V) :
    ‖mu g‖ = 1 := by
  obtain ⟨x, hx⟩ := h.1 g
  rw [h.2 g x hx]
  first
    | exact Circle.norm_coe _
    | exact Circle.abs_coe _
    | exact mem_sphere_zero_iff_norm.mp (χ x).2

def muRec {X : ThetaX D} (T : ThetaTied D X) (μ : D.what₂.Tup) (j : ℕ) : (AE D)ˣ →* Circle :=
  T.eChr (X.chrOf μ j)

def muRec0 {X : ThetaX D} (T : ThetaTied D X) (j : ℕ) : (AE D)ˣ →* Circle := muRec T D.what₂.mu0 j

def FinUnit (x : (AE D)ˣ) : Prop :=
  infPart D (x : AE D) = 1 ∧ finPart D (x : AE D) ∈ intAE D ∧ finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D

def MuConj {K : Type} [Field K] (σ₀ σ : K →+* ℂ) (χ₀ χσ : (AE D)ˣ →* Circle) : Prop :=
  ∀ x, FinUnit x → ∃ y : K, ((χ₀ x : Circle) : ℂ) = σ₀ y ∧ ((χσ x : Circle) : ℂ) = σ y

def CEquiv (V : HSp D) {K : Type} [Field K] (σ : K →+* ℂ) {C : Type} [AddCommGroup C] [Module K C]
    {X : Comp → Data E r} (rd : C →ₛₗ[σ] FDSec X) (dict : GA D V → Σ k, Frame (X k).Ψ r) (mu : GA D V → ℂ)
    (c : Comp → ℂ) {G0 : Type} [Group G0] (ρ : G0 →* (C →ₗ[K] C)) (chi : G0 →* Kˣ) (ℓ : G0 → GA D V) : Prop :=
  (∃ c' : Comp → ℂ, CUnit c' ∧ EquivariantFiniteGroup V σ rd dict (muPin V dict mu c') ρ chi ℓ) →
    EquivariantFiniteGroup V σ rd dict (muPin V dict mu c) ρ chi ℓ

end Char

section Dict

variable {D : D7}

def finVec (V : HSp D) (v : Fin V.rank → D.host.E) : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E :=
  fun i => (1 : Af D.host.F) ⊗ₜ v i

def gLat (V : HSp D) (g : GA D V) : Set (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :=
  (finHom V g).1.mulVec '' (latHat V : Set (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E))

def latG (V : HSp D) (g : GA D V) : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) :=
  Submodule.span (𝓞 D.host.E) {w | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ v, finVec V v ∈ gLat V g ∧ w = a • v}

def latGHat (V : HSp D) (g : GA D V) : AddSubgroup (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :=
  AddSubgroup.closure {w | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ z ∈ gLat V g,
    w = fun i => ((1 : Af D.host.F) ⊗ₜ a) * z i}

def LatEmb (V : HSp D) {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    (ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) : Prop :=
  Function.Injective ι ∧ LinearMap.range ι = latG V 1

def LatIsom (V : HSp D) {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La] (EF : LinearMap.BilinForm ℤ La)
    (ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) : Prop :=
  ∃ ε : ℤˣ, ∀ x y, ((EF x y : ℤ) : ℚ) = ((ε : ℤ) : ℚ) *
    Algebra.trace ℚ D.host.E (D.host.xi0 * V.hT (V.frame.equivFun.symm (ι x)) (V.frame.equivFun.symm (ι y)))

def ModelW (V : HSp D) {r : ℕ} (hr : V.rank = r) (X : Data D.host.E r) : Prop :=
  X.Gm = -(Matrix.reindex (finCongr hr) (finCongr hr) V.gram).transpose ∧ X.ξ0 = -D.host.xi0

def IsOrthogonalFrame {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) : Prop :=
  ∀ τ ∈ X.Ψ, gram τ X.Gm (x₀ τ) = Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {σ : c.F →+* ℂ} {r : ℕ}

open Classical in

def DictLat (U : Unf Xo c σ r) (V : HSp D) (hr : V.rank = r) (dict : GA D V → Σ k, Frame (U.X k).Ψ r)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) {g : ℕ} (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ)
    (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) : Prop :=
  ((∀ k a b, (((F.Di (ik k)).EF a b : ℤ) : ℚ) = Algebra.trace ℚ D.host.E
        (-(U.X k).ξ0 * herm (U.X k).Gm (φ k a : Fin r → D.host.E) (φ k b))) ∧
    ∀ k (x : (U.X k).dom), ∃ Pm : (F.Di (ik k)).La →+ (Fin g → ℂ),
      (∀ a j, Pm a j = perFr (U.X k) x.1 (φ k a : Fin r → D.host.E) (relab c σ (e j).1) (e j).2) ∧
      IsPeriod (F.Di (ik k)) (fun j => relab c σ (e j).1) Pm ∧ (U.un k x).x = F.u (ik k) Pm ∧
      ∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex (ik k) Pm z).left) (Pi.single (e.symm ⟨τ, i⟩) 1)
        ((U.un k x).u τ i)) ∧
    ∀ h : GA D V, ∃ γ ∈ GQ V,
      ((U.X (dict h).1).Λ : Set (Fin r → D.host.E)) =
        (fun v : Fin V.rank → D.host.E => v ∘ Fin.cast hr.symm) '' (latG V (γ * h) : Set _) ∧
      (∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
        ∃ w ∈ latGHat V (γ * h),
        finVec V ((φ (dict h).1 (F.t (ik (dict h).1) a) : Fin r → D.host.E) ∘ Fin.cast hr) -
          (finHom V (γ * h)).1.mulVec (finVec V (ι a)) = (l.M : ℕ) • w) ∧
      ∀ τ : (U.X (dict h).1).Ψ, mat (dict h).2 τ =
        Matrix.reindex (finCongr hr) (finCongr hr) (archM V (th (dict h).1 τ) (γ * h)) * x₀ τ.1

end Dict

structure CoreJ (D : D7) : Type 1 extends Core D where
  cE : ∀ (j : ℕ) (σ : Q.c.F →+* ℂ), (U j σ).Comp → ℂ
  chiW : ℕ → (Q.c.F →+* ℂ) → (AE D)ˣ →* Circle
  x₀ : ℕ → (Q.c.F →+* ℂ) → (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ
  iota : ∀ j : ℕ, (Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)

namespace CoreJ

variable {D : D7} (T : CoreJ D)

def phiJ (j : ℕ) (σ : T.Q.c.F →+* ℂ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) : GA D (T.V j σ) → ℂ :=
  (lieFac (T.Q.Dw j) (xiR D) a : ℂ) •
    adel (T.V j σ) (T.dict j σ) (muPin (T.V j σ) (T.dict j σ) (T.mu j σ) (T.cE j σ)) (rdU (T.U j σ) f)

theorem phiJ_apply (j : ℕ) (σ : T.Q.c.F →+* ℂ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) (g : GA D (T.V j σ)) :
    T.phiJ j σ a f g = T.cE j σ (T.dict j σ g).1 * T.toCore.phiAd j σ a f g := by
  have h1 : adel (T.V j σ) (T.dict j σ) (T.mu j σ) (rdU (T.U j σ) f) g =
      T.mu j σ g * rdU (T.U j σ) f (T.dict j σ g).1 (T.dict j σ g).2 := rfl
  simp only [phiJ, Core.phiAd, Pi.smul_apply, smul_eq_mul, adel_muPin, h1]
  ring

end CoreJ

def halfVec {D : D7} (V : HSp D) (b : 𝓞 D.host.E) (z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E :=
  fun i => ((1 : Af D.host.F) ⊗ₜ (b : D.host.E)) * z i

def KfHalf {D : D7} (V : HSp D) (Kf : Subgroup (GA D V)) (M : ℕ) (Mh : Ideal (𝓞 D.host.E)) : Prop :=
  ∀ k, k ∈ Kf ↔ k ∈ GfC V ∧ ∀ b ∈ Mh, ∀ z ∈ latHat V, ∃ y ∈ latHat V,
    (finHom V k).1.mulVec (halfVec V b z) - halfVec V b z = M • y

def AdPin {D : D7} (T : Core D) (j : ℕ) (σ : T.Q.c.F →+* ℂ) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ)
    (ι₀ : (T.Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)) : Prop :=
  ∃ (hr : (T.V j σ).rank = D.R.r)
    (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin ((T.Q.Dw j).mult τ))
    (F : FamilyUnif (T.Q.Xo j) (σ.comp (IntermediateField.inclusion T.Q.c.le).toRingHom)
      (fun i => relab T.Q.c σ (e i).1))
    (ik : (T.U j σ).Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] ((T.U j σ).X k).Λ)
    (th : ∀ k, ((T.U j σ).X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)),
    let ι := LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ ι₀
    LatEmb (T.V j σ) ι ∧ LatIsom (T.V j σ) (T.Q.Dw j).EF ι ∧ (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧
      DictLat (T.U j σ) (T.V j σ) hr (T.dict j σ) ι e F ik φ th x₀

structure LawsJ {D : D7} (T : CoreJ D) : Prop extends LawsM T.toCore where

  cUnit : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → CUnit (T.cE j σ)

  muVal : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → MuVal (T.V j σ) (T.chiW j σ) (T.mu j σ)

  muConj : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → MuConj T.σ₀ σ (T.chiW j T.σ₀) (T.chiW j σ)

  intAll : ∀ j, InR D j → IntAll (T.Q.Xo j) T.Q.c

  modelW : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → ∃ hr : (T.V j σ).rank = D.R.r,
    ∀ k, ModelW (T.V j σ) hr ((T.U j σ).X k)

  familyUniformisationBasePointOrthogonal : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → ∀ k, IsOrthogonalFrame ((T.U j σ).X k) (T.x₀ j σ)

  kfHalf : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ →
    KfHalf (T.V j σ) (T.Kf j σ) T.Q.l.M (T.Q.l.Mb.map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E))

  adPin : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → AdPin T.toCore j σ (T.x₀ j σ) (T.iota j)

end Formalism.L2.Pj
