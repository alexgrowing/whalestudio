import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.CompOfBis

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing Filter
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.Z.Mult (Cp At IsDec CompOf Mult)
open scoped Matrix TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.V.Z.J.D

section Abs

variable {G H W W' : Type} [Group G] [Group H] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

def Intw (τ : Representation ℂ G W') (ρ : Representation ℂ G W) (f : W' →ₗ[ℂ] W) : Prop := ∀ g v, f (τ g v) = ρ g (f v)

def Isot (ρ : Representation ℂ G W) (τ : Representation ℂ G W') : Prop :=
  (⊤ : Submodule ℂ W) ≤ ⨆ f : {f : W' →ₗ[ℂ] W // Intw τ ρ f}, LinearMap.range f.1

def AbsIrr (τ : Representation ℂ G W') : Prop :=
  τ.IsIrreducible ∧ ∀ f : W' →ₗ[ℂ] W', Intw τ τ f → ∃ a : ℂ, f = a • LinearMap.id

def box (ρ : Representation ℂ G W) (τ : Representation ℂ H W') : Representation ℂ (G × H) (W ⊗[ℂ] W') :=
  Representation.tprod (ρ.comp (MonoidHom.fst G H)) (τ.comp (MonoidHom.snd G H))

def piRep {I : Type} {Gi Wi : I → Type} [∀ i, Group (Gi i)] [∀ i, AddCommGroup (Wi i)] [∀ i, Module ℂ (Wi i)]
    (τ : ∀ i, Representation ℂ (Gi i) (Wi i)) : Representation ℂ (∀ i, Gi i) (⨂[ℂ] i, Wi i) :=
  PiTensorProduct.mapMonoidHom.comp (Pi.monoidHom fun i => (τ i).comp (Pi.evalMonoidHom Gi i))

def invT {m : ℕ} (K₁ : Subgroup G) (K₂ : Subgroup H) (τ₀ : K₁ →* GL (Fin m) ℂ) (ρ : Representation ℂ (G × H) W) :
    Submodule ℂ (Fin m → W) where
  carrier := {F | (∀ (k : K₁) i, ∑ j, τ₀ k i j • ρ (k, 1) (F j) = F i) ∧ ∀ k ∈ K₂, ∀ i, ρ (1, k) (F i) = F i}
  add_mem' {F F'} h h' := ⟨fun k i => by
    simp only [Pi.add_apply, map_add, smul_add, Finset.sum_add_distrib, h.1 k i, h'.1 k i], fun k hk i => by
    simp only [Pi.add_apply, map_add, h.2 k hk i, h'.2 k hk i]⟩
  zero_mem' := ⟨fun k i => by simp, fun k _ i => by simp⟩
  smul_mem' a F h := ⟨fun k i => by
    simp only [Pi.smul_apply, map_smul]
    rw [← h.1 k i, Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _, fun k hk i => by
    simp only [Pi.smul_apply, map_smul, h.2 k hk i]⟩

end Abs

def locEig {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ} {W : Type}
    [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin n) k) W) (b : ℕ) (φ : Fin n → Uo k → ℂ) (μ : Fin n → ℂ) :
    Submodule ℂ W :=
  fixd π (glIwa k n).N ⊓ fixd π ((glIwa k n).Nm b) ⊓
    (⨅ (i) (y), Module.End.eigenspace (π (eT k n i y : (glIwa k n).T)) (φ i y)) ⊓
    ⨅ j : Fin n, ((glIwa k n).uOp π (al k n (j + 1))).maxGenEigenspace (μ j)

def eigL {L : Type} [Field L] [NumberField L] {n : ℕ} {V : Type} [Fintype V] (S : V → Plc L) {W : Type} [AddCommGroup W]
    [Module ℂ W] (ρ : Representation ℂ (GV n S) W) (b : ℕ) (φ : ∀ v, Fin n → Uo ((S v).adicCompletion L) → ℂ)
    (μ : V → Fin n → ℂ) : Submodule ℂ W :=
  fixd ρ (iwS n S).N ⊓ fixd ρ ((iwS n S).Nm b) ⊓
    (⨅ (v) (i) (y), Module.End.eigenspace (ρ (eV n S v i y : (iwS n S).T)) (φ v i y)) ⊓
    ⨅ (v) (j : Fin n), ((iwS n S).uOp ρ (alV n S v (j + 1))).maxGenEigenspace (μ v j)

section Set

variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {c : Coef l} (H : HSet L Ω l n c) {A : Type} [CommRing A] [Algebra c.O A] (θ : H.X.I.T →* Aˣ) (ι : Qbar l ≃+* ℂ)
  (x : A →+* Qbar l) (lam : Wt L l n) {d : ℕ} (ξ : GV n H.Sl →* GL (Fin d) ℂ) (K : H.Lev) (b : ℕ) (ev : H.Op → ℂ)

def zPart : Submodule ℂ (Fin H.m → H.X.Fn ℂ d) :=
  H.OrdAt θ ι x lam ξ K b ⊓ ⨅ i, (H.opC ι lam d i).maxGenEigenspace (ev i)

def zL (d : ℕ) {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GV n H.Sl) W) : Submodule ℂ W :=
  eigL H.Sl ρ b (fun v i y => (ι (H.finPart θ x lam v i y))⁻¹) fun v j => H.lowVal ι lam v (j + 1) * ev (.inr (v, j))

end Set

section U

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  (n : ℕ) (s : HidaSetting l L Ω)

abbrev GS : Type := GV n (wt s) × GLw n (s.w s.v0)

def toGS : Ga l L n →* GS n s := MonoidHom.prod (Pi.monoidHom fun u : s.St => cmp n (s.w u)) (cmp n (s.w s.v0))

def GaS : Subgroup (Ga l L n) :=
  ⨅ (w : Plc L) (_ : w.under (𝓞 (Lp L)) ∉ s.St ∧ w.under (𝓞 (Lp L)) ≠ s.v0), (cmp n w).ker

open Classical in

def secS : GS n s →* Ga l L n :=
  if h : Function.Bijective ((toGS n s).comp (GaS n s).subtype) then
    (GaS n s).subtype.comp (MulEquiv.ofBijective _ h).symm.toMonoidHom
  else 1

def KS : Subgroup (Ga l L n) :=
  (toGS n s).ker ⊓ ⨅ (w : Plc L) (_ : w.under (𝓞 (Lp L)) ∉ s.S), (KO (w.adicCompletion L) (Fin n)).comap (cmp n w)

variable {n s} (V : s.Lev) (ι : Qbar l ≃+* ℂ) {lam : Wt L l n} {d : ℕ}
  (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))
  (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ)

variable (n) in

abbrev GL' : Type := GV n (fun v : V.frame.Vl => s.w v.1)

variable (n d) in

def actS : Representation ℂ (GL' n V × GS n s) (Ga l L n × GL' n V → Fin d → ℂ) :=
  (rtr ℂ (Ga l L n × GL' n V) (Fin d → ℂ)).comp
    (MonoidHom.prod ((secS n s).comp (MonoidHom.snd _ _)) (MonoidHom.fst _ _))

def VS {c : Coef l} {m : ℕ} (Q : QData V) (τ₀ : KT n (wt s) →* GL (Fin m) c.O) (σ : Submodule ℂ (UA L n → ℂ)) :
    Submodule ℂ (Ga l L n × GL' n V → Fin d → ℂ) :=
  (hset Q τ₀).X.AF ξ ⊓ Submodule.span ℂ {F | ∀ ℓ, toForm ι e F ℓ ∈ σ} ⊓
    fixd ((rtr ℂ (Ga l L n × GL' n V) (Fin d → ℂ)).comp (MonoidHom.inl _ _)) (KS n s)

variable (lam) in

def WtLink (lam' : InfinitePlace L → DomWeight n) : Prop :=
  ∀ σ : Submodule ℂ (UA L n → ℂ), IsAutRepU σ →
    ((∀ y : Emb l (fun v : V.frame.Vl => s.w v.1), HasWeightAt σ (ι.toRingHom.comp y.res) (lam y.res).dual) ↔
      ∀ v, HasWeightAt σ v.embedding (lam' v))

structure Comps (σ : Submodule ℂ (UA L n → ℂ)) : Type 1 where
  l : ∀ v : V.frame.Vl, SmIrr (GLw n (s.w v.1))
  u : ∀ u : s.St, SmIrr (GLw n (s.w u))
  o : SmIrr (GLw n (s.w s.v0))
  hl : ∀ v, Cp σ (s.w v.1) (l v)
  hu : ∀ v : s.St, Cp σ (s.w v) (u v)
  ho : Cp σ (s.w s.v0) o

variable {V} {σ : Submodule ℂ (UA L n → ℂ)} (C : Comps V σ)

abbrev Comps.repL := piRep fun v => (C.l v).ρ

abbrev Comps.repS := box (piRep fun u => (C.u u).ρ) C.o.ρ

abbrev Comps.inv {c : Coef l} {m : ℕ} (τ₀ : KT n (wt s) →* GL (Fin m) c.O) :=
  invT (KT n (wt s)) (Kc _ n 1)
    ((Matrix.GeneralLinearGroup.map (ι.toRingHom.comp (algebraMap c.O (Qbar l)))).comp τ₀) C.repS

end U

end UpperTheory.V.Z.J.D
