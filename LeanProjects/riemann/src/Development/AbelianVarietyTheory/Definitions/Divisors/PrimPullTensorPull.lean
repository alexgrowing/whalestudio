import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Subsingleton
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.ChainComp

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)
open scoped NumberField TensorProduct
open GlobalTheory.Cris DividedPowers
attribute [local instance] Over.cartesianMonoidalCategory

universe u

namespace GlobalTheory.SSG

structure DRChain (C : Type) [CommRing C] (n : ℕ) : Type (u + 1) where

  M : Fin (n + 1) → Type u
  [acg : ∀ i, AddCommGroup (M i)]
  [mod : ∀ i, Module C (M i)]

  f : ∀ i : Fin n, M i.castSucc →ₗ[C] M i.succ

  g : M (Fin.last n) →ₗ[C] M 0

  ω : ∀ i, Submodule C (M i)

attribute [instance] DRChain.acg DRChain.mod

namespace DRChain

variable {C : Type} [CommRing C] {n : ℕ}

def comp (X : DRChain.{u} C n) : ∀ i : Fin (n + 1), X.M 0 →ₗ[C] X.M i :=
  Fin.induction LinearMap.id (fun i h ↦ X.f i ∘ₗ h)

@[simp] theorem comp_zero (X : DRChain.{u} C n) : X.comp 0 = LinearMap.id := rfl

@[simp] theorem comp_succ (X : DRChain.{u} C n) (i : Fin n) :
    X.comp i.succ = X.f i ∘ₗ X.comp i.castSucc := rfl

theorem comp_eq_chainComp (X : DRChain.{0} C n) : X.comp = chainComp X.f := rfl

def ofLMPoint {ϖ : C} [NeZero n] (P : LMPoint C ϖ n) : DRChain.{0} C n where
  M _ := Fin n → C
  f i := stdStep ϖ i
  g := LinearMap.id
  ω i := P.ℓ ⟨(i : ℕ) % n, Nat.mod_lt _ (NeZero.pos n)⟩

end DRChain

end GlobalTheory.SSG

namespace GlobalTheory.DeRham

variable {C : Type} [CommRing C] {O : Type} [Ring O]
  {B B' B'' : Over (Sp C)} [GrpObj B] [GrpObj B'] [GrpObj B'']

theorem primPull_comp (f : B ⟶ B') (g : B' ⟶ B'') [IsMonHom f] [IsMonHom g] :
    primPull (dp0 C) (𝟙 _) (f ≫ g) = primPull (dp0 C) (𝟙 _) f ∘ₗ primPull (dp0 C) (𝟙 _) g :=
  LinearMap.ext fun c ↦ (GrpMor.pull_pull (homMor (dp0 C) (𝟙 _) g) (homMor (dp0 C) (𝟙 _) f)
    (homMor (dp0 C) (𝟙 _) (f ≫ g)) (fun _ ↦ rfl) rfl c).symm

theorem primPull_congr {f g : B ⟶ B'} [IsMonHom f] [IsMonHom g] (e : f = g) :
    primPull (dp0 C) (𝟙 _) f = primPull (dp0 C) (𝟙 _) g := by
  subst e; rfl

theorem primPull_mul (f g : B ⟶ B') [IsMonHom f] [IsMonHom g] [IsMonHom (f * g)] :
    primPull (dp0 C) (𝟙 _) (f * g) = primPull (dp0 C) (𝟙 _) f + primPull (dp0 C) (𝟙 _) g :=
  LinearMap.ext fun c ↦ Subtype.ext (c.2 B f g)

theorem primPull_id : primPull (dp0 C) (𝟙 _) (𝟙 B) = LinearMap.id :=
  LinearMap.ext fun c ↦ Subtype.ext (IsMor.pullCohomologyOne_id _ c.1)

variable [IsCommMonObj B] [IsCommMonObj B'] [IsCommMonObj B'']

def opPull (ρ : RingAct B O) (x : O) : Module.End C (primDR B) :=
  haveI := ρ.hom x
  primPull (dp0 C) (𝟙 _) (ρ.act x)

theorem opPull_add (ρ : RingAct B O) (x y : O) : opPull ρ (x + y) = opPull ρ x + opPull ρ y := by
  haveI := ρ.hom
  have e : ρ.act (x + y) = ρ.act x * ρ.act y := ρ.map_add x y
  haveI : IsMonHom (ρ.act x * ρ.act y) := e ▸ ρ.hom _
  exact (primPull_congr e).trans (primPull_mul _ _)

theorem opPull_one (ρ : RingAct B O) : opPull ρ 1 = 1 := by
  haveI := ρ.hom
  exact (primPull_congr ρ.map_one).trans primPull_id

def opPullHom (ρ : RingAct B O) : O →+ Module.End C (primDR B) :=
  AddMonoidHom.mk' (opPull ρ) (opPull_add ρ)

def tensorPull (ρ : RingAct B O) : C ⊗[ℤ] O →ₗ[ℤ] Module.End C (primDR B) :=
  TensorProduct.lift (LinearMap.mk₂ ℤ (fun (c : C) (x : O) ↦ c • opPull ρ x)
    (fun c c' x ↦ add_smul c c' _)
    (fun k c x ↦ smul_assoc k c _)
    (fun c x y ↦ by rw [opPull_add, smul_add])
    (fun k c x ↦ by
      change c • opPullHom ρ (k • x) = k • (c • opPullHom ρ x)
      rw [map_zsmul, smul_comm]))

@[simp] theorem tensorPull_tmul (ρ : RingAct B O) (c : C) (x : O) :
    tensorPull ρ (c ⊗ₜ x) = c • opPull ρ x := rfl

def eigSub (ρ : RingAct B O) {K : Type} [CommRing K] [Algebra K O] (χ : K →+* C) :
    Submodule C (primDR B) :=
  ⨅ x : K, LinearMap.ker (opPull ρ (algebraMap K O x) - χ x • (1 : Module.End C (primDR B)))

theorem mem_eigSub {ρ : RingAct B O} {K : Type} [CommRing K] [Algebra K O] {χ : K →+* C}
    {h : primDR B} : h ∈ eigSub ρ χ ↔ ∀ x, opPull ρ (algebraMap K O x) h = χ x • h := by
  simp [eigSub, Submodule.mem_iInf, sub_eq_zero]

def epsPart (ρ : RingAct B O) {K : Type} [CommRing K] [Algebra K O] (χ : K →+* C) (ε : C ⊗[ℤ] O) :
    Submodule C (primDR B) :=
  eigSub ρ χ ⊓ LinearMap.range (tensorPull ρ ε)

theorem primPull_opPull {ρ : RingAct B O} {ρ' : RingAct B' O} {u : B' ⟶ B}
    (hu : GlobalTheory.IwLevel.IsLin ρ' ρ u) (x : O) :
    haveI := hu.hom
    primPull (dp0 C) (𝟙 _) u ∘ₗ opPull ρ x = opPull ρ' x ∘ₗ primPull (dp0 C) (𝟙 _) u := by
  haveI := hu.hom
  haveI := ρ.hom
  haveI := ρ'.hom
  unfold opPull
  rw [← primPull_comp, ← primPull_comp]
  exact primPull_congr (hu.comm x).symm

theorem primPull_tensorPull {ρ : RingAct B O} {ρ' : RingAct B' O} {u : B' ⟶ B}
    (hu : GlobalTheory.IwLevel.IsLin ρ' ρ u) (z : C ⊗[ℤ] O) :
    haveI := hu.hom
    primPull (dp0 C) (𝟙 _) u ∘ₗ tensorPull ρ z = tensorPull ρ' z ∘ₗ primPull (dp0 C) (𝟙 _) u := by
  haveI := hu.hom
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul c x => rw [tensorPull_tmul, tensorPull_tmul, LinearMap.comp_smul, LinearMap.smul_comp,
      primPull_opPull hu]
  | add z z' hz hz' => rw [map_add, map_add, LinearMap.comp_add, LinearMap.add_comp, hz, hz']

def pullPart {ρ : RingAct B O} {ρ' : RingAct B' O} {K : Type} [CommRing K] [Algebra K O] (χ : K →+* C)
    (ε : C ⊗[ℤ] O) (u : B' ⟶ B) (hu : GlobalTheory.IwLevel.IsLin ρ' ρ u) : epsPart ρ χ ε →ₗ[C] epsPart ρ' χ ε :=
  haveI := hu.hom
  (primPull (dp0 C) (𝟙 _) u).restrict fun h hh ↦ by
    refine ⟨mem_eigSub.2 fun x ↦ ?_, ?_⟩
    · have e := LinearMap.congr_fun (primPull_opPull hu (algebraMap K O x)) h
      simp only [LinearMap.comp_apply] at e
      rw [← e, mem_eigSub.1 hh.1 x, map_smul]
    · obtain ⟨y, hy⟩ := hh.2
      refine ⟨primPull (dp0 C) (𝟙 _) u y, ?_⟩
      rw [← hy]
      exact (LinearMap.congr_fun (primPull_tensorPull hu ε) y).symm

theorem pullPart_apply {ρ : RingAct B O} {ρ' : RingAct B' O} {K : Type} [CommRing K] [Algebra K O]
    (χ : K →+* C) (ε : C ⊗[ℤ] O) (u : B' ⟶ B) (hu : GlobalTheory.IwLevel.IsLin ρ' ρ u) (h : epsPart ρ χ ε) :
    haveI := hu.hom
    (pullPart χ ε u hu h : primDR B') = primPull (dp0 C) (𝟙 _) u h := rfl

end GlobalTheory.DeRham

namespace GlobalTheory.IwLevel

namespace Chain

variable {C : Type} [CommRing C] {A : Over (Sp C)} [GrpObj A] [IsCommMonObj A] {O : Type} [Ring O]
  {ρ : RingAct A O} {𝔴 : Ideal O} {d n : ℕ} (X : Chain ρ 𝔴 d n)

def close (i : Fin (n + 1)) {a : O} (ha : a ∈ 𝔴) : X.B i ⟶ A :=
  (X.existsUnique_close i ha).exists.choose

theorem π_close (i : Fin (n + 1)) {a : O} (ha : a ∈ 𝔴) : X.π i ≫ X.close i ha = ρ.act a :=
  (X.existsUnique_close i ha).exists.choose_spec

instance close_isMonHom (i : Fin (n + 1)) {a : O} (ha : a ∈ 𝔴) : IsMonHom (X.close i ha) := by
  have h := X.π_deg i
  have := h.flat
  have := h.surj
  haveI := (X.π_lin i).hom
  haveI := ρ.hom a
  have e := X.π_close i ha
  haveI := GlobalTheory.FlatQuotient.epi_tensorHom (X.π i) (X.π i)
  refine ⟨?_, ?_⟩
  · rw [← IsMonHom.one_hom (X.π i), Category.assoc, e, IsMonHom.one_hom]
  · rw [← cancel_epi (X.π i ⊗ₘ X.π i)]
    calc (X.π i ⊗ₘ X.π i) ≫ μ ≫ X.close i ha = (μ ≫ X.π i) ≫ X.close i ha := by
          rw [IsMonHom.mul_hom (X.π i), Category.assoc]
      _ = μ ≫ ρ.act a := by rw [Category.assoc, e]
      _ = (ρ.act a ⊗ₘ ρ.act a) ≫ μ := IsMonHom.mul_hom _
      _ = (X.π i ⊗ₘ X.π i) ≫ (X.close i ha ⊗ₘ X.close i ha) ≫ μ := by
          rw [← Category.assoc, tensorHom_comp_tensorHom, e]

theorem close_isLin (i : Fin (n + 1)) {a : O} (ha : a ∈ 𝔴) (hc : ∀ x, a * x = x * a) :
    IsLin (X.act i) ρ (X.close i ha) := by
  refine ⟨X.close_isMonHom i ha, fun x ↦ ?_⟩
  have h := X.π_deg i
  have := h.flat
  have := h.surj
  haveI := GlobalTheory.FlatQuotient.epi_of_flat_surjective (X.π i)
  rw [← cancel_epi (X.π i), ← Category.assoc, ← (X.π_lin i).comm, Category.assoc, X.π_close,
    ← Category.assoc, X.π_close, ← ρ.map_mul, ← ρ.map_mul, hc]

theorem isLin_eqToHom {i j : Fin (n + 1)} (h : i = j) :
    IsLin (X.act i) (X.act j) (eqToHom (congrArg X.B h)) := by
  subst h
  simpa using IsLin.id (X.act i)

def stepRev (j : Fin n) : X.B (Fin.rev j.succ) ⟶ X.B (Fin.rev j.castSucc) :=
  eqToHom (congrArg X.B (Fin.rev_succ j)) ≫ X.φ (Fin.rev j) ≫
    eqToHom (congrArg X.B (Fin.rev_castSucc j).symm)

theorem stepRev_isLin (j : Fin n) : IsLin (X.act _) (X.act _) (X.stepRev j) :=
  (X.isLin_eqToHom (Fin.rev_succ j)).comp ((X.φ_lin _).comp (X.isLin_eqToHom (Fin.rev_castSucc j).symm))

def closeRev {a : O} (ha : a ∈ 𝔴) : X.B (Fin.rev 0) ⟶ X.B (Fin.rev (Fin.last n)) :=
  eqToHom (congrArg X.B (Fin.rev_zero n)) ≫ X.close (Fin.last n) ha ≫ X.π 0 ≫
    eqToHom (congrArg X.B (Fin.rev_last n).symm)

theorem closeRev_isLin {a : O} (ha : a ∈ 𝔴) (hc : ∀ x, a * x = x * a) :
    IsLin (X.act _) (X.act _) (X.closeRev ha) :=
  (X.isLin_eqToHom (Fin.rev_zero n)).comp ((X.close_isLin _ ha hc).comp
    (X.π_zero_lin.comp (X.isLin_eqToHom (Fin.rev_last n).symm)))

open GlobalTheory.DeRham in

def drChain {K : Type} [CommRing K] [Algebra K O] (χ : K →+* C) (ε : C ⊗[ℤ] O) {a : O} (ha : a ∈ 𝔴)
    (hc : ∀ x, a * x = x * a) : GlobalTheory.SSG.DRChain.{1} C n where
  M j := epsPart (X.act (Fin.rev j)) χ ε
  f j := pullPart χ ε (X.stepRev j) (X.stepRev_isLin j)
  g := pullPart χ ε (X.closeRev ha) (X.closeRev_isLin ha hc)
  ω j := (PrimitiveSubmodule (X.B (Fin.rev j))).comap (epsPart (X.act (Fin.rev j)) χ ε).subtype

end Chain

section HT

open GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
  {C : Type} [CommRing C] {σ : R →+* C}

def HTIw.drChain {o : Obj b N (spMap σ)} {w : Ideal (𝓞 D.F)} (c : HTIw o w) (i : Fin D.a)
    (ε : C ⊗[ℤ] D.O) {a : 𝓞 D.F} (ha : a ∈ w) : GlobalTheory.SSG.DRChain.{1} C D.n :=
  Chain.drChain c (σ.comp (b.t i)) ε (Ideal.mem_map_of_mem (algebraMap (𝓞 D.F) D.O) ha)
    (fun x ↦ Algebra.commutes a x)

end HT

end GlobalTheory.IwLevel

namespace GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime]

def Datum.splitIdem (D : Datum p) {C : Type} [CommRing C] (e : ℤ_[p] →+* C) : C ⊗[ℤ] D.O :=
  TensorProduct.comm ℤ D.O C (TensorProduct.map LinearMap.id e.toAddMonoidHom.toIntLinearMap
    (D.splitP.some.symm (Matrix.single ⟨0, D.m_pos⟩ ⟨0, D.m_pos⟩ 1)))

end GlobalTheory.UPel.HT

section Basic₂

open GlobalTheory.SSG

variable {C : Type} [CommRing C]

example (n : ℕ) [NeZero n] : (DRChain.ofLMPoint (LMPoint.worst (C := C) n)).g = LinearMap.id := rfl

example : (DRChain.ofLMPoint (LMPoint.worst (C := C) 1)).comp (Fin.last 1) (fun _ ↦ 1) = 0 := by
  rw [show (Fin.last 1 : Fin 2) = (0 : Fin 1).succ from rfl, DRChain.comp_succ]
  change stdStep (0 : C) (0 : Fin 1) (fun _ ↦ 1) = 0
  funext j
  fin_cases j
  simp only [stdStep, LinearMap.coe_mk, AddHom.coe_mk]
  simp

example {O : Type} [Ring O] {B : Over (Sp C)} [GrpObj B] [IsCommMonObj B] (ρ : RingAct B O) :
    GlobalTheory.DeRham.tensorPull ρ (1 ⊗ₜ 1) = 1 := by
  rw [GlobalTheory.DeRham.tensorPull_tmul, GlobalTheory.DeRham.opPull_one, one_smul]

end Basic₂

section ExampleHT

open GlobalTheory.UPel.HT GlobalTheory.IwLevel

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
  {C : Type} [CommRing C] {σ : R →+* C}

example {o : Obj b N (spMap σ)} {w : Ideal (𝓞 D.F)} (c : HTIw o w) (i : Fin D.a) (ε : C ⊗[ℤ] D.O)
    {a : 𝓞 D.F} (ha : a ∈ w) (j : Fin (D.n + 1)) :
    (c.drChain i ε ha).M j = GlobalTheory.DeRham.epsPart (c.act (Fin.rev j)) (σ.comp (b.t i)) ε := rfl

example {o : Obj b N (spMap σ)} {w : Ideal (𝓞 D.F)} (c : HTIw o w) (i : Fin D.a) (ε : C ⊗[ℤ] D.O)
    {a : 𝓞 D.F} (ha : a ∈ w) (j : Fin D.n)
    (h : GlobalTheory.DeRham.epsPart (c.act (Fin.rev j.castSucc)) (σ.comp (b.t i)) ε) :
    haveI := (Chain.stepRev_isLin c j).hom
    ((show GlobalTheory.DeRham.epsPart (c.act (Fin.rev j.succ)) (σ.comp (b.t i)) ε from (c.drChain i ε ha).f j h) :
      GlobalTheory.DeRham.primDR (c.B (Fin.rev j.succ))) =
      GlobalTheory.DeRham.primPull (GlobalTheory.Cris.dp0 C) (𝟙 _) (Chain.stepRev c j) (h : GlobalTheory.DeRham.primDR _) := rfl

end ExampleHT
