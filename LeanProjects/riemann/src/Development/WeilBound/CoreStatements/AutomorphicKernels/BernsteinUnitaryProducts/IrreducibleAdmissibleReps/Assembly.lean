import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.RightWhit
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.HighestDerivProd
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.TwKerLeComapOf

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir

namespace PositivityTheory.PfBern.Assembly

section Deriv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {N : ℕ} {X Y Z : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] [AddCommGroup Z] [Module ℂ Z]

abbrev DerSp (ψ : AddChar k Circle) {n h : ℕ} (hn : n + h = N) (ρ : Representation ℂ (GL (Fin N) k) X) : Type :=
  TwJacquet (jacU₂ (stdSum hn) ρ) (rightUnip k n h) (rightWhit k ψ n h)

def jacMap₂ {n h : ℕ} (hn : n + h = N) {ρ : Representation ℂ (GL (Fin N) k) X}
    {σ : Representation ℂ (GL (Fin N) k) Y} (f : ρ.IntertwiningMap σ) :
    Jacquet ρ (unipRad k (two (stdSum hn))) →ₗ[ℂ] Jacquet σ (unipRad k (two (stdSum hn))) :=
  twMap ρ σ (unipRad k (two (stdSum hn))) 1 f.toLinearMap (fun g v => LinearMap.congr_fun (f.isIntertwining' g) v)

theorem jacMap₂_comm {n h : ℕ} (hn : n + h = N) {ρ : Representation ℂ (GL (Fin N) k) X}
    {σ : Representation ℂ (GL (Fin N) k) Y} (f : ρ.IntertwiningMap σ) (g : GL (Fin n) k × GL (Fin h) k)
    (v : Jacquet ρ (unipRad k (two (stdSum hn)))) :
    jacMap₂ hn f (jacU₂ (stdSum hn) ρ g v) = jacU₂ (stdSum hn) σ g (jacMap₂ hn f v) := by
  induction v using Submodule.Quotient.induction_on with
  | H x =>
  exact congrArg Submodule.Quotient.mk (LinearMap.congr_fun (f.isIntertwining' _) x)

def derMap (ψ : AddChar k Circle) {n h : ℕ} (hn : n + h = N) {ρ : Representation ℂ (GL (Fin N) k) X}
    {σ : Representation ℂ (GL (Fin N) k) Y} (f : ρ.IntertwiningMap σ) : DerSp ψ hn ρ →ₗ[ℂ] DerSp ψ hn σ :=
  twMap (jacU₂ (stdSum hn) ρ) (jacU₂ (stdSum hn) σ) (rightUnip k n h) (rightWhit k ψ n h) (jacMap₂ hn f)
    (jacMap₂_comm hn f)

end Deriv

section Sub

variable {G : Type} [Group G] {X D A B Z : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup D] [Module ℂ D]
  [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B] [AddCommGroup Z] [Module ℂ Z]

def subIncl {ρ : Representation ℂ G X} (S : Subrepresentation ρ) : S.toRepresentation.IntertwiningMap ρ where
  toLinearMap := S.toSubmodule.subtype
  isIntertwining' _ := by ext; rfl

def subProj {ρ : Representation ℂ G X} (S T : Subrepresentation ρ) (hc : IsCompl S.toSubmodule T.toSubmodule) :
    ρ.IntertwiningMap T.toRepresentation where
  toLinearMap := T.toSubmodule.projectionOnto S.toSubmodule hc.symm
  isIntertwining' g := by
    ext x
    have hx : x ∈ S.toSubmodule ⊔ T.toSubmodule := hc.sup_eq_top ▸ Submodule.mem_top
    obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.1 hx
    have hs' := S.apply_mem_toSubmodule g hs
    have ht' := T.apply_mem_toSubmodule g ht
    simp only [LinearMap.comp_apply, map_add,
      Submodule.projectionOnto_apply_of_mem_right hc.symm hs,
      Submodule.projectionOnto_apply_of_mem_right hc.symm hs',
      Submodule.projectionOnto_apply_of_mem_left hc.symm ht,
      Submodule.projectionOnto_apply_of_mem_left hc.symm ht', zero_add, map_zero]
    rfl

theorem subProj_subIncl_left {ρ : Representation ℂ G X} (S T : Subrepresentation ρ)
    (hc : IsCompl S.toSubmodule T.toSubmodule) (x : S.toSubmodule) : subProj S T hc (subIncl S x) = 0 :=
  Submodule.projectionOnto_apply_of_mem_right hc.symm x.2

theorem subProj_subIncl_right {ρ : Representation ℂ G X} (S T : Subrepresentation ρ)
    (hc : IsCompl S.toSubmodule T.toSubmodule) (x : T.toSubmodule) : subProj S T hc (subIncl T x) = x :=
  Submodule.projectionOnto_apply_of_mem_left hc.symm x.2

variable [TopologicalSpace G]

theorem isSmooth_sub {ρ : Representation ℂ G X} (hρ : IsSmooth ρ) (S : Subrepresentation ρ) :
    IsSmooth S.toRepresentation := by
  intro v
  convert hρ (v : X) using 1
  ext g
  simp only [Set.mem_setOf_eq]
  exact Subtype.ext_iff

omit [TopologicalSpace G] in

theorem eq_bot_or_eq_top_of_equiv_twist {σ : Representation ℂ G D} {τ : Representation ℂ G Z} {χ : G →* ℂˣ}
    (e : σ.Equiv (twist τ χ)) (hτ : τ.IsIrreducible) (I : Submodule ℂ D) (hI : ∀ g, ∀ y ∈ I, σ g y ∈ I) :
    I = ⊥ ∨ I = ⊤ := by
  let f : D →ₗ[ℂ] Z := e.toLinearEquiv.toLinearMap
  have key : ∀ g y, f (σ g y) = twist τ χ g (f y) :=
    fun g y => LinearMap.congr_fun (e.isIntertwining' g) y
  have hinv : ∀ g, ∀ z ∈ I.map f, τ g z ∈ I.map f := by
    intro g z hz
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hz
    have h2 : τ g (f y) = (((χ g)⁻¹ : ℂˣ) : ℂ) • twist τ χ g (f y) := by
      rw [twist_apply, smul_smul, Units.inv_mul, one_smul]
    rw [h2]
    exact Submodule.smul_mem _ _ (Submodule.mem_map.2 ⟨σ g y, hI g y hy, key g y⟩)
  let S : Subrepresentation τ := ⟨I.map f, fun g v hv => hinv g v hv⟩
  have hinjf : Function.Injective (Submodule.map f) :=
    Submodule.map_injective_of_injective e.toLinearEquiv.injective
  rcases hτ.eq_bot_or_eq_top S with hS | hS
  · left
    apply hinjf
    rw [Submodule.map_bot]
    exact congrArg Subrepresentation.toSubmodule hS
  · right
    apply hinjf
    rw [Submodule.map_top, LinearMap.range_eq_top.2 e.toLinearEquiv.surjective]
    exact congrArg Subrepresentation.toSubmodule hS

omit [TopologicalSpace G] in

theorem range_ne_bot_ne_top (DS : A →ₗ[ℂ] D) (DT : B →ₗ[ℂ] D) (Dp : D →ₗ[ℂ] B) (hinj : Function.Injective DS)
    [Nontrivial A] [Nontrivial B] (h0 : ∀ a, Dp (DS a) = 0) (h1 : ∀ b, Dp (DT b) = b) :
    LinearMap.range DS ≠ ⊥ ∧ LinearMap.range DS ≠ ⊤ := by
  refine ⟨?_, ?_⟩
  · intro h
    obtain ⟨a, ha⟩ := exists_ne (0 : A)
    have hm : DS a ∈ LinearMap.range DS := LinearMap.mem_range_self DS a
    rw [h, Submodule.mem_bot] at hm
    exact ha (hinj (hm.trans DS.map_zero.symm))
  · intro h
    obtain ⟨b, hb⟩ := exists_ne (0 : B)
    have hm : DT b ∈ LinearMap.range DS := h ▸ Submodule.mem_top
    obtain ⟨a, ha⟩ := hm
    apply hb
    rw [← h1 b, ← ha, h0]

end Sub

section Props

def IsHighestDeriv {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {N : ℕ} {X : Type} [AddCommGroup X] [Module ℂ X] (ψ : AddChar k Circle) (ρ : Representation ℂ (GL (Fin N) k) X)
    {n h : ℕ} (hn : n + h = N) : Prop :=
  Nontrivial (DerSp ψ hn ρ) ∧ ∀ (n' h' : ℕ) (hn' : n' + h' = N), h < h' → Subsingleton (DerSp ψ hn' ρ)

def ExistsAddChar : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∃ ψ : AddChar k Circle, Continuous ψ ∧ ψ ≠ 1

def IrrSmoothAdmissible : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (X : Type) [AddCommGroup X] [Module ℂ X]
    (π : Representation ℂ (GL (Fin N) k) X), IsSmooth π → π.IsIrreducible → IsAdmissible π

def AdmissibleProd : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
      (π₁ : Representation ℂ (GL (Fin r) k) V) (π₂ : Representation ℂ (GL (Fin t) k) W),
    IsAdmissible π₁ → IsAdmissible π₂ → IsAdmissible (prod₂ π₁ π₂)

def UnitarisableProd : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
      (π₁ : Representation ℂ (GL (Fin r) k) V) (π₂ : Representation ℂ (GL (Fin t) k) W),
    IsSmooth π₁ → IsUnitarisable π₁ → IsSmooth π₂ → IsUnitarisable π₂ → IsUnitarisable (prod₂ π₁ π₂)

def UnitaryAdmissibleComplement : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (X : Type) [AddCommGroup X] [Module ℂ X]
    (π : Representation ℂ (GL (Fin N) k) X), IsAdmissible π → IsUnitarisable π →
      ∀ S : Subrepresentation π, ∃ T : Subrepresentation π, IsCompl S.toSubmodule T.toSubmodule

def DerivInjective : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ →
    ∀ (n h N : ℕ) (hn : n + h = N) (X Y : Type) [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
      (ρ : Representation ℂ (GL (Fin N) k) X) (σ : Representation ℂ (GL (Fin N) k) Y), IsSmooth ρ → IsSmooth σ →
      ∀ f : ρ.IntertwiningMap σ, Function.Injective f → Function.Injective (derMap ψ hn f)

def HighestDerivUnitaryProd : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 →
    ∀ (r t N : ℕ) (hN : r + t = N) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
      (π₁ : Representation ℂ (GL (Fin r) k) V) (π₂ : Representation ℂ (GL (Fin t) k) W),
      IsSmooth π₁ → π₁.IsIrreducible → IsUnitarisable π₁ → IsSmooth π₂ → π₂.IsIrreducible → IsUnitarisable π₂ → 0 < N →
      ∃ (n h : ℕ) (hn : n + h = N), 0 < h ∧ IsHighestDeriv ψ (ind₂ (stdSum hN) (extTensor π₁ π₂)) hn ∧
        ∃ (r' t' : ℕ) (e : r' + t' = n) (σ₁ : Leib.GRep k r') (σ₂ : Leib.GRep k t') (χ : GL (Fin n) k →* ℂˣ),
          IsSmooth σ₁.ρ ∧ σ₁.ρ.IsIrreducible ∧ IsUnitarisable σ₁.ρ ∧
          IsSmooth σ₂.ρ ∧ σ₂.ρ.IsIrreducible ∧ IsUnitarisable σ₂.ρ ∧
          Nonempty ((derRep k ψ hn (ind₂ (stdSum hN) (extTensor π₁ π₂))).Equiv
            (twist (ind₂ (stdSum e) (extTensor σ₁.ρ σ₂.ρ)) χ))

def SummandsFullDepth : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 →
    ∀ (r t N : ℕ) (hN : r + t = N) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
      (π₁ : Representation ℂ (GL (Fin r) k) V) (π₂ : Representation ℂ (GL (Fin t) k) W),
      IsSmooth π₁ → π₁.IsIrreducible → IsUnitarisable π₁ → IsSmooth π₂ → π₂.IsIrreducible → IsUnitarisable π₂ →
      ∀ (n h : ℕ) (hn : n + h = N), IsHighestDeriv ψ (ind₂ (stdSum hN) (extTensor π₁ π₂)) hn →
        ∀ S : Subrepresentation (ind₂ (stdSum hN) (extTensor π₁ π₂)), S ≠ ⊥ → Nontrivial (DerSp ψ hn S.toRepresentation)

def ProdGL0Irreducible : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π₁ : Representation ℂ (GL (Fin 0) k) V) (π₂ : Representation ℂ (GL (Fin 0) k) W),
    π₁.IsIrreducible → π₂.IsIrreducible → (prod₂ π₁ π₂).IsIrreducible

end Props

section Main

end Main

end PositivityTheory.PfBern.Assembly
