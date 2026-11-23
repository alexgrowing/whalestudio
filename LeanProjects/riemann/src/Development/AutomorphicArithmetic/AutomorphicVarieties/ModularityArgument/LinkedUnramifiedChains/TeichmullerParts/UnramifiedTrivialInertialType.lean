import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.AbsIrr
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary

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

def Reg (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ} (μ : Fin n → ℂ) : Prop :=
  ∃ ω : Fin n → ℂˣ, Function.Injective ω ∧ ∀ j, μ j = ∏ i with i ≤ j, (ω i : ℂ) * ((Nat.card 𝓀[k] : ℂ) ^ (i : ℕ))⁻¹

def KEq {L : Type} [Field L] [NumberField L] {n : ℕ} {w : Plc L} (τ τ' : SmIrr (GLw n w)) : Prop :=
  Nonempty (Representation.Equiv (τ.ρ.comp (KO (w.adicCompletion L) (Fin n)).subtype)
    (τ'.ρ.comp (KO (w.adicCompletion L) (Fin n)).subtype))

def LinAlg : Prop :=
  ∀ (A M W J : Type) [CommRing A] [AddCommGroup M] [Module A M] [Module.Free A M] [Module.Finite A M] [AddCommGroup W] [Module ℂ W]
    (T : Subalgebra A (Module.End A M)) (g : J → T), (∀ t t' : T, t * t' = t' * t) → Algebra.adjoin A (Set.range g) = ⊤ →
    ∀ (x : A →+* ℂ) (sp : M →+ W) (γ : J → Module.End ℂ W), (∀ a m, sp (a • m) = x a • sp m) →
    (∀ (κ : Type) (b : Module.Basis κ A M), LinearIndependent ℂ fun i => sp (b i)) → (∀ j m, sp ((g j).1 m) = γ j (sp m)) →
    ∀ z : T →+* ℂ, z.comp (algebraMap A T) = x →
    let Z := Submodule.span ℂ (Set.range sp) ⊓ ⨅ j, (γ j).maxGenEigenspace (z (g j))
    Z ≠ ⊥ ∧ (∀ t : T, Module.finrank ℂ Z ≤ ((LinearMap.charpoly t.1).map x).rootMultiplicity (z t)) ∧
      ∀ t : T, (∀ z' : T →+* ℂ, z'.comp (algebraMap A T) = x → z' t = z t → z' = z) →
        ((LinearMap.charpoly t.1).map x).rootMultiplicity (z t) ≤ Module.finrank ℂ Z

def LocSp : Prop :=
  ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l)
    (H : HSet L Ω l n c), H.Ax → ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (ι : Qbar l ≃+* ℂ) (x : A →ₐ[c.O] Qbar l) (lam : Wt L l n) (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ) (c0 : ℕ)
    (sp : H.X.Fn A H.m → Fin H.m → H.X.Fn ℂ d), H.IsSpec θ ι x.toRingHom lam ξ c0 sp → ∀ (K : H.Lev) (a : H.Op → c.O) [Fact (CommOn (H.MK θ a K) (H.op A))] [Module.Free A (H.MK θ a K)] [Module.Finite A (H.MK θ a K)]
    (z : H.TK θ a K →ₐ[c.O] Qbar l), z.toRingHom.comp (algebraMap A _) = x.toRingHom →
    (∀ (κ : Type) (b : Module.Basis κ A (H.MK θ a K)), LinearIndependent ℂ fun i => sp (b i)) ∧
    zPart H θ ι x.toRingHom lam ξ K c0 (fun i => ι (z (H.gen θ a K i))) =
      Submodule.span ℂ (sp '' H.MK θ a K) ⊓ ⨅ i, (H.opC ι lam d i).maxGenEigenspace (ι (z (H.gen θ a K i)))

def Ctl : Prop :=
  ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l)
    (H : HSet L Ω l n c), H.Ax → ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (ι : Qbar l ≃+* ℂ) (x : A →ₐ[c.O] Qbar l) (lam : Wt L l n) (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ) (c0 : ℕ)
    (sp : H.X.Fn A H.m → Fin H.m → H.X.Fn ℂ d), H.IsSpec θ ι x.toRingHom lam ξ c0 sp → ∀ (K : H.Lev) (a : H.Op → c.O) [Fact (CommOn (H.MK θ a K) (H.op A))] [Module.Free A (H.MK θ a K)] [Module.Finite A (H.MK θ a K)]
    (z : H.TK θ a K →ₐ[c.O] Qbar l), z.toRingHom.comp (algebraMap A _) = x.toRingHom →
    let Z := zPart H θ ι x.toRingHom lam ξ K c0 fun i => ι (z (H.gen θ a K i))
    Z ≠ ⊥ ∧ (∀ t : H.TK θ a K, Module.finrank ℂ Z ≤ ((LinearMap.charpoly t.1).map x.toRingHom).rootMultiplicity (z t)) ∧
      ∀ t : H.TK θ a K, (∀ z' : H.TK θ a K →ₐ[c.O] Qbar l, z'.toRingHom.comp (algebraMap A _) = x.toRingHom → z' t = z t → z' = z) →
        ((LinearMap.charpoly t.1).map x.toRingHom).rootMultiplicity (z t) ≤ Module.finrank ℂ Z

def UnitEv : Prop :=
  ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l)
    (H : HSet L Ω l n c), H.Ax → ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (ι : Qbar l ≃+* ℂ) (K : H.Lev) (a : H.Op → c.O) [Fact (CommOn (H.MK θ a K) (H.op A))] [Module.Finite A (H.MK θ a K)] (I : Ideal (H.TK θ a K))
    (D : W.GDet n (H.TK θ a K) H.Gq) (ψ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* (H.TK θ a K)ˣ), H.IsUniv θ a K I D ψ →
    ∀ (z : H.TK θ a K →ₐ[c.O] Qbar l) v j, ‖z (H.gen θ a K (.inr (v, j)))‖ = 1

def ZEq : Prop :=
  ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l)
    (H : HSet L Ω l n c), H.Ax → ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (ι : Qbar l ≃+* ℂ) (x : A →ₐ[c.O] Qbar l) (lam : Wt L l n) (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ) (c0 : ℕ)
    (sp : H.X.Fn A H.m → Fin H.m → H.X.Fn ℂ d), H.IsSpec θ ι x.toRingHom lam ξ c0 sp → ∀ (K : H.Lev) (ev : H.Op → ℂ), (∀ v j, ‖ι.symm (ev (.inr (v, j)))‖ = 1) →
    zPart H θ ι x.toRingHom lam ξ K c0 ev = H.Big ι ξ ⊓ fixd (H.X.raF d (H.τC ι)) (H.lev K) ⊓
      zL H θ ι x.toRingHom lam c0 ev d (H.X.rpF ℂ d H.m) ⊓ ⨅ p, (H.opC ι lam d (.inl p)).maxGenEigenspace (ev (.inl p))

def Slope : Prop :=
  ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l)
    (H : HSet L Ω l n c), H.Ax → ∀ (ι : Qbar l ≃+* ℂ) (lam : Wt L l n) (v : H.V) (u : Fin n → ℂ), (∀ j, ‖ι.symm (u j)‖ = 1) →
    Reg ((H.Sl v).adicCompletion L) fun j => H.lowVal ι lam v (j + 1) * u j

def Ord1 : Prop :=
  GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ), ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin n) k) W),
    GlobalTheory.PRep.IsSmooth π → π.IsIrreducible → ∀ (b : ℕ) (φ : Fin n → Uo k → ℂ) (μ : Fin n → ℂ),
    (∀ i (y : Uo k), (y : kˣ) ∈ Uc k (b + 1) → φ i y = 1) → Reg k μ → Module.rank ℂ (locEig π b φ μ) ≤ 1

def EigPi : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (n : ℕ) (V : Type) [Fintype V] (S : V → Plc L) (τ : ∀ v, SmIrr (GLw n (S v))) (b : ℕ)
    (φ : ∀ v, Fin n → Uo ((S v).adicCompletion L) → ℂ) (μ : V → Fin n → ℂ), (∀ v, Module.rank ℂ (locEig (τ v).ρ b (φ v) (μ v)) ≤ 1) →
    Module.rank ℂ (eigL S (piRep fun v => (τ v).ρ) b φ μ) ≤ 1

def SchurGL : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (n : ℕ) (w : Plc L) (τ : SmIrr (GLw n w)), AbsIrr τ.ρ

def Step : Prop :=
  ∀ (G H W W' : Type) [Group G] [Group H] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (ρ : Representation ℂ (G × H) W) (τ : Representation ℂ G W'), AbsIrr τ →
    Isot (ρ.comp (MonoidHom.inl G H)) τ → ∃ (X : Type) (_ : AddCommGroup X) (_ : Module ℂ X) (κ : Representation ℂ H X)
      (f : W' ⊗[ℂ] X ≃ₗ[ℂ] W), Intw (box τ κ) ρ f.toLinearMap

def BoxIrr : Prop :=
  ∀ (G H W W' : Type) [Group G] [Group H] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (ρ : Representation ℂ G W) (τ : Representation ℂ H W'), AbsIrr ρ → AbsIrr τ → AbsIrr (box ρ τ)

def BoxIsot : Prop :=
  ∀ (G H W W' : Type) [Group G] [Group H] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (ρ : Representation ℂ G W) (τ : Representation ℂ H W'), AbsIrr ρ → AbsIrr τ →
    ∀ (X : Type) [AddCommGroup X] [Module ℂ X] (κ : Representation ℂ (G × H) X), Isot (κ.comp (MonoidHom.inl G H)) ρ →
    Isot (κ.comp (MonoidHom.inr G H)) τ → Isot κ (box ρ τ)

def PiIrr : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (Gi Wi : I → Type) [∀ i, Group (Gi i)] [∀ i, AddCommGroup (Wi i)] [∀ i, Module ℂ (Wi i)]
    (τ : ∀ i, Representation ℂ (Gi i) (Wi i)), (∀ i, AbsIrr (τ i)) → AbsIrr (piRep τ)

def PiIsot : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (Gi Wi : I → Type) [∀ i, Group (Gi i)] [∀ i, AddCommGroup (Wi i)] [∀ i, Module ℂ (Wi i)]
    (τ : ∀ i, Representation ℂ (Gi i) (Wi i)), (∀ i, AbsIrr (τ i)) → ∀ (X : Type) [AddCommGroup X] [Module ℂ X]
    (κ : Representation ℂ (∀ i, Gi i) X), (∀ i, Isot (κ.comp (MonoidHom.mulSingle Gi i)) (τ i)) → Isot κ (piRep τ)

def SecS : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev), V.S' = s.S → Function.Bijective ((toGS n s).comp (GaS n s).subtype) ∧
    (∀ g, ∀ k ∈ KS n s, Commute (secS n s g) k) ∧ ∀ Q : QData V, ∀ g : Ga l L n, g ∈ (UQ n Q).map (Ub n s).subtype ↔
      ∃ k ∈ KS n s, ∃ p ∈ (KT n (wt s)).prod (Kc _ n 1), g = secS n s p * k

def IsotS : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev), V.S' = s.S → ∀ (Q : QData V) (c : Coef l) (ι : Qbar l ≃+* ℂ) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (lam : Wt L l n) (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))
    (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ), IsBasis ι e ξ → ∀ σ, IsAutRepU σ → ∀ C : Comps V σ, ∃ ρ : Representation ℂ (GL' n V × GS n s) (VS V ι e ξ Q τ₀ σ),
    Intw ρ (actS n V d) (VS V ι e ξ Q τ₀ σ).subtype ∧ Isot ρ (box C.repL C.repS)

def InfDim : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev), V.S' = s.S → ∀ (Q : QData V) (c : Coef l) (ι : Qbar l ≃+* ℂ) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (lam : Wt L l n) (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))
    (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ), IsBasis ι e ξ → ∀ lam', WtLink V ι lam lam' → ∀ σ, IsAutRepU σ → (∀ v, HasWeightAt σ v.embedding (lam' v)) →
    ∀ (U : Subgroup (finU L n)) (U' : Subgroup (Ga l L n × GL' n V)),
    U' = U.map ((MonoidHom.prod (away l L n).rangeRestrict (Pi.monoidHom fun v : V.frame.Vl => cLoc (s.w v.1))).comp (finU L n).subtype) →
    Module.rank ℂ ↥(σ ⊓ GlobalTheory.PRep.fixed (GlobalTheory.BCT.RF L n) U) = Module.rank ℂ ↥((hset Q τ₀).X.AF ξ ⊓ Submodule.span ℂ {F | ∀ ℓ, toForm ι e F ℓ ∈ σ} ⊓
      fixd (rtr ℂ (Ga l L n × GL' n V) (Fin d → ℂ)) U') * d ∧ (d : ℂ) = GlobalTheory.BCT.dimW lam'

def Flath : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev), V.S' = s.S → ∀ (Q : QData V) (c : Coef l) (ι : Qbar l ≃+* ℂ) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (lam : Wt L l n) (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))
    (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ), IsBasis ι e ξ → ∀ σ, IsAutRepU σ → VS V ι e ξ Q τ₀ σ ≠ ⊥ → ∀ C : Comps V σ,
    ∃ f : _ →ₗ[ℂ] (Ga l L n × GL' n V → Fin d → ℂ), Function.Injective f ∧ LinearMap.range f = VS V ι e ξ Q τ₀ σ ∧
      Intw (box C.repL C.repS) (actS n V d) f

def EigBox : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (n : ℕ) (V : Type) [Fintype V] (S : V → Plc L) (G H W W' X : Type) [Group G] [Group H]
    [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (GV n S) W)
    (κ : Representation ℂ (G × H) W') (π : Representation ℂ (GV n S × (G × H)) X) (f : W ⊗[ℂ] W' →ₗ[ℂ] X), Function.Injective f →
    Intw (box ρ κ) π f → ∀ (m : ℕ) (K₁ : Subgroup G) (K₂ : Subgroup H) (τ₀ : K₁ →* GL (Fin m) ℂ) (b : ℕ)
    (φ : ∀ v, Fin n → Uo ((S v).adicCompletion L) → ℂ) (μ : V → Fin n → ℂ),
    Module.rank ℂ ↥(invT K₁ K₂ τ₀ (π.comp (MonoidHom.inr _ _)) ⊓ Submodule.pi Set.univ fun _ =>
      LinearMap.range f ⊓ eigL S (π.comp (MonoidHom.inl _ _)) b φ μ) = Module.rank ℂ (eigL S ρ b φ μ) * Module.rank ℂ (invT K₁ K₂ τ₀ κ)

def YDim : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev), V.S' = s.S → ∀ (Q : QData V) (c : Coef l) (ι : Qbar l ≃+* ℂ) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (lam : Wt L l n) (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))
    (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ), IsBasis ι e ξ → ∀ σ, IsAutRepU σ → (∀ w : Plc L, w.under (𝓞 (Lp L)) ∉ s.S → IsUnramU σ w) →
    (∀ y : Emb l (fun v : V.frame.Vl => s.w v.1), HasWeightAt σ (ι.toRingHom.comp y.res) (lam y.res).dual) → ∀ (C : Comps V σ) (b : ℕ)
    (φ : ∀ v : V.frame.Vl, Fin n → Uo ((s.w v.1).adicCompletion L) → ℂ) (μ : V.frame.Vl → Fin n → ℂ),
    Module.rank ℂ ↥(YOf Q ι τ₀ e ξ σ ⊓ eigL (fun v : V.frame.Vl => s.w v.1) ((hset Q τ₀).X.rpF ℂ d m) b φ μ) =
      Module.rank ℂ (eigL (fun v : V.frame.Vl => s.w v.1) C.repL b φ μ) * Module.rank ℂ (C.inv ι τ₀)

def WtEx : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev), V.S' = s.S → ∀ (ι : Qbar l ≃+* ℂ) (lam : Wt L l n), ∃ lam', WtLink V ι lam lam'

def CompsEx : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev), V.S' = s.S → ∀ σ : Submodule ℂ (UA L n → ℂ), IsAutRepU σ → Nonempty (Comps V σ)

def IndepS : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (GlobalTheory.BCT.Pl E)), GlobalTheory.BCT.IsSection S →
    ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : GlobalTheory.BCT.Pl E, Subgroup (GlobalTheory.BCT.UL n w)),
    GlobalTheory.BCT.IsLevelFam (fun w : GlobalTheory.BCT.Pl E => MonoidHom.id (GlobalTheory.BCT.UL n w)) (GlobalTheory.BCT.KL n) K' →
    ∀ (J : Type) [Fintype J] (σ : J → Submodule ℂ (UA E n → ℂ)), IsDec S lam K' σ → iSupIndep σ

def Decomp : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev), V.S' = s.S → ∀ (Q : QData V) (c : Coef l) (ι : Qbar l ≃+* ℂ) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (lam : Wt L l n) (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))
    (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ), IsBasis ι e ξ → IsOpen (τ₀.ker : Set (KT n (wt s))) → ∀ lam', WtLink V ι lam lam' → ∀ b : ℕ,
    ∃ (S : Set (GlobalTheory.BCT.Pl L)) (K' : ∀ w : GlobalTheory.BCT.Pl L, Subgroup (GlobalTheory.BCT.UL n w)) (J : Type) (_ : Fintype J)
      (σ : J → Submodule ℂ (UA L n → ℂ)), GlobalTheory.BCT.IsSection S ∧
      GlobalTheory.BCT.IsLevelFam (fun w : GlobalTheory.BCT.Pl L => MonoidHom.id (GlobalTheory.BCT.UL n w)) (GlobalTheory.BCT.KL n) K' ∧
      (∀ w : Plc L, w.under (𝓞 (Lp L)) ∉ s.S → K' w = GlobalTheory.BCT.KL n w) ∧ IsDec S lam' K' σ ∧
      iSupIndep (fun i => YOf Q ι τ₀ e ξ (σ i)) ∧ (∀ i (w : Plc L), w.under (𝓞 (Lp L)) ∉ s.S → IsUnramU (σ i) w) ∧
      (∀ i, ∀ w ∈ S, IsSplitAt w → ∀ τ, Cp (σ i) w τ → GlobalTheory.PRep.fixed (τ.ρ.comp (GlobalTheory.BCT.UL n w).subtype) (K' w) ≠ ⊥) ∧
      (hset Q τ₀).Big ι ξ ⊓ fixd ((hset Q τ₀).X.rpF ℂ d m) ((hset Q τ₀).X.I.I1 b) ≤
        ⨆ i, YOf Q ι τ₀ e ξ (σ i) ⊓ fixd ((hset Q τ₀).X.rpF ℂ d m) ((hset Q τ₀).X.I.I1 b)

def ZDec : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev), V.S' = s.S → ∀ (Q : QData V) (c : Coef l) (ι : Qbar l ≃+* ℂ) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (lam : Wt L l n) (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))
    (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ), IsBasis ι e ξ → ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : (hset Q τ₀).X.I.T →* Aˣ) (x : A →ₐ[c.O] Qbar l) (c0 : ℕ)
    (sp : (hset Q τ₀).X.Fn A m → Fin m → (hset Q τ₀).X.Fn ℂ d), (hset Q τ₀).IsWt θ → (hset Q τ₀).IsSpec θ ι x.toRingHom lam ξ c0 sp →
    ∀ (K : (hset Q τ₀).Lev) (ev : (hset Q τ₀).Op → ℂ), (∀ v j, ‖ι.symm (ev (.inr (v, j)))‖ = 1) → ∀ (J : Type) [Fintype J] (σ : J → Submodule ℂ (UA L n → ℂ)),
    (∀ i, IsAutRepU (σ i)) → iSupIndep (fun i => YOf Q ι τ₀ e ξ (σ i)) →
    (hset Q τ₀).Big ι ξ ⊓ fixd ((hset Q τ₀).X.rpF ℂ d m) ((hset Q τ₀).X.I.I1 c0) ≤
      (⨆ i, YOf Q ι τ₀ e ξ (σ i) ⊓ fixd ((hset Q τ₀).X.rpF ℂ d m) ((hset Q τ₀).X.I.I1 c0)) →
    Module.finrank ℂ (zPart (hset Q τ₀) θ ι x.toRingHom lam ξ K c0 ev) = ∑ i, Module.finrank ℂ ↥(YOf Q ι τ₀ e ξ (σ i) ⊓ zPart (hset Q τ₀) θ ι x.toRingHom lam ξ K c0 ev)

def SphSame : Prop :=
  GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev), V.S' = s.S → ∀ (Q : QData V) (c : Coef l) (ι : Qbar l ≃+* ℂ) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (lam : Wt L l n) (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))
    (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ), IsBasis ι e ξ → ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : (hset Q τ₀).X.I.T →* Aˣ) (x : A →ₐ[c.O] Qbar l) (c0 : ℕ)
    (sp : (hset Q τ₀).X.Fn A m → Fin m → (hset Q τ₀).X.Fn ℂ d), (hset Q τ₀).IsWt θ → (hset Q τ₀).IsSpec θ ι x.toRingHom lam ξ c0 sp →
    ∀ (K : (hset Q τ₀).Lev) (ev : (hset Q τ₀).Op → ℂ), (∀ v j, ‖ι.symm (ev (.inr (v, j)))‖ = 1) → ∀ σ σ', IsAutRepU σ → IsAutRepU σ' →
    (∀ w, IsSplitAt w → ∃ τ, Cp σ w τ ∧ Cp σ' w τ) → YOf Q ι τ₀ e ξ σ ⊓ zPart (hset Q τ₀) θ ι x.toRingHom lam ξ K c0 ev ≠ ⊥ →
    YOf Q ι τ₀ e ξ σ' ⊓ zPart (hset Q τ₀) θ ι x.toRingHom lam ξ K c0 ev = YOf Q ι τ₀ e ξ σ' ⊓ zL (hset Q τ₀) θ ι x.toRingHom lam c0 ev d ((hset Q τ₀).X.rpF ℂ d m)

def AtSame : Prop :=
  GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev), V.S' = s.S → ∀ (Q : QData V) (c : Coef l) (ι : Qbar l ≃+* ℂ) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (lam : Wt L l n) (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))
    (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ), IsBasis ι e ξ → ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : (hset Q τ₀).X.I.T →* Aˣ) (x : A →ₐ[c.O] Qbar l) (c0 : ℕ)
    (sp : (hset Q τ₀).X.Fn A m → Fin m → (hset Q τ₀).X.Fn ℂ d), (hset Q τ₀).IsWt θ → (hset Q τ₀).IsSpec θ ι x.toRingHom lam ξ c0 sp →
    ∀ (K : (hset Q τ₀).Lev) (ev : (hset Q τ₀).Op → ℂ), ∀ σ σ', IsAutRepU σ → IsAutRepU σ' → YOf Q ι τ₀ e ξ σ ⊓ zPart (hset Q τ₀) θ ι x.toRingHom lam ξ K c0 ev ≠ ⊥ →
    YOf Q ι τ₀ e ξ σ' ⊓ zPart (hset Q τ₀) θ ι x.toRingHom lam ξ K c0 ev ≠ ⊥ → ∀ π : CuspSub L n, At π σ → At π σ'

def BcOf : Prop :=
  Af.HypothesesH → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω], GlobalTheory.BCT.Unr E →
    ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ σ : Submodule ℂ (UA E n → ℂ), IsAutRepU σ →
    ∀ ρ : G E Ω →* GL (Fin n) (Qbar l), Continuous ρ → Af.IsIrr ρ →
    (∀ᶠ w : Plc E in cofinite, IsSplitAt w → ∀ τ, Cp σ w τ → Af.LocGlob ι ρ w τ) →
    ∃ π : CuspSub E n, (CG.mk π).IsRegAlg ∧ GlobalTheory.ContraPair.DualIsConj π ∧ At π σ ∧
      (∀ φ lam, HasWeightAt σ φ lam → π.HasInfChar φ (infOfWeight lam)) ∧ ∀ w, IsUnramU σ w → ∃ B, (CG.mk π).HasSat w B

def PartRep : Prop :=
  ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l)
    (H : HSet L Ω l n c), H.Ax → ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (ι : Qbar l ≃+* ℂ) (x : A →ₐ[c.O] Qbar l) (lam : Wt L l n) (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ) (c0 : ℕ)
    (sp : H.X.Fn A H.m → Fin H.m → H.X.Fn ℂ d), H.IsSpec θ ι x.toRingHom lam ξ c0 sp → ∀ (K : H.Lev) (a : H.Op → c.O) [Fact (CommOn (H.MK θ a K) (H.op A))] [Module.Free A (H.MK θ a K)] [Module.Finite A (H.MK θ a K)]
    (z : H.TK θ a K →ₐ[c.O] Qbar l), z.toRingHom.comp (algebraMap A _) = x.toRingHom → ∀ (I : Ideal (H.TK θ a K)) (D : W.GDet n (H.TK θ a K) H.Gq)
    (ψ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* (H.TK θ a K)ˣ), H.IsUniv θ a K I D ψ → ∀ ρ : H.Gq →* GL (Fin n) (Qbar l), Continuous ρ →
    Af.IsIrr ρ → D.map z.toRingHom = W.GDet.ofRep (W.mat ρ) → ∀ Y : H.Part ι lam ξ,
    Y.Y ⊓ zPart H θ ι x.toRingHom lam ξ K c0 (fun i => ι (z (H.gen θ a K i))) ≠ ⊥ → ∃ g : GL (Fin n) (Qbar l), ∀ h, Y.r h = g * ρ h * g⁻¹

def UnramifiedTrivialInertialType : Prop :=
  ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ)
    (ρ : G L Ω →* GL (Fin n) (Qbar l)), Continuous ρ → ∀ (w : Plc L) (A : ValuationSubring Ω) (h : IsPlaceOver A w),
    ((l : ℕ) : 𝓞 L) ∉ w.asIdeal → (∀ g ∈ Ine (F := L) A, ρ g = 1) → ∀ τ : SmIrr (GLw n w), Af.LocGlob ι ρ w τ →
    ∀ rc, IsRec h rc → IsTypeWD h (fun _ : Fin n => 1) (rc (algNorm τ))

def TypePS : Prop :=
  GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (n : ℕ), 1 ≤ n →
    ∀ (π : CuspSub L n) (w : Plc L) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (τ : SmIrr (GLw n w)), π.IsLocComp w τ →
    ∀ χ : Fin n → Ine (F := L) A →* ℂˣ, (∀ rc, IsRec h rc → IsTypeWD h χ (rc (algNorm τ))) →
    ∃ ω : Fin n → (w.adicCompletion L)ˣ →* ℂˣ, (∀ i, IsSmoothChar (ω i)) ∧ Nonempty (τ.ρ.Equiv (PS ω)) ∧
      ∀ i (g : Ine (F := L) A), ω i (artOf h (ineIncl h g)) = χ i g

def PsRes : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ), ∀ ω ω' : Fin n → kˣ →* ℂˣ, (∀ i, IsSmoothChar (ω i)) → (∀ i, IsSmoothChar (ω' i)) → (∀ i (y : Uo k), ω i y = ω' i y) →
    Nonempty (Representation.Equiv ((PS ω).comp (KO k (Fin n)).subtype) ((PS ω').comp (KO k (Fin n)).subtype))

def ResEq : Prop :=
  GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (n : ℕ), 1 ≤ n →
    ∀ (π π' : CuspSub L n) (w : Plc L) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (τ τ' : SmIrr (GLw n w)), π.IsLocComp w τ →
    π'.IsLocComp w τ' → ∀ χ : Fin n → Ine (F := L) A →* ℂˣ, (∀ rc, IsRec h rc → IsTypeWD h χ (rc (algNorm τ))) →
    (∀ rc, IsRec h rc → IsTypeWD h χ (rc (algNorm τ'))) → KEq τ τ'

def InvEq : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev), V.S' = s.S → ∀ (c : Coef l) (ι : Qbar l ≃+* ℂ) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O) (σ σ' : Submodule ℂ (UA L n → ℂ))
    (C : Comps V σ) (C' : Comps V σ'), (∀ u, KEq (C.u u) (C'.u u)) → KEq C.o C'.o →
    Module.rank ℂ (C.inv ι τ₀) = Module.rank ℂ (C'.inv ι τ₀)

def Count : Prop :=
  Af.HypothesesH → Mult → CompOf → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev), V.S' = s.S → n ≤ 4 → ∀ (ι : Qbar l ≃+* ℂ) (lam : Wt L l n), ∃ a₀ : ℕ,
    ∀ (Q : QData V) (c : Coef l) (r : Resid V.frame c.O n) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O), TypeFor r ι τ₀ →
    ∀ (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))
    (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ), IsBasis ι e ξ → ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : (hset Q τ₀).X.I.T →* Aˣ) (x : A →ₐ[c.O] Qbar l) (c0 : ℕ)
    (sp : (hset Q τ₀).X.Fn A m → Fin m → (hset Q τ₀).X.Fn ℂ d), (hset Q τ₀).IsWt θ → (hset Q τ₀).IsSpec θ ι x.toRingHom lam ξ c0 sp →
    ∀ (K : (hset Q τ₀).Lev) (ev : (hset Q τ₀).Op → ℂ), (∀ v j, ‖ι.symm (ev (.inr (v, j)))‖ = 1) →
    zPart (hset Q τ₀) θ ι x.toRingHom lam ξ K c0 ev ≠ ⊥ → (∀ Y : (hset Q τ₀).Part ι lam ξ, Y.Y ⊓ zPart (hset Q τ₀) θ ι x.toRingHom lam ξ K c0 ev ≠ ⊥ → Af.IsIrr Y.r ∧ ∀ g ∈ V.frame.I0, Y.r g = 1) →
    ∃ (π : CuspSub L n) (σ : Submodule ℂ (UA L n → ℂ)) (C : Comps V σ), (∀ u : s.St, π.IsLocComp (s.w u) (C.u u)) ∧
      π.IsLocComp (s.w s.v0) C.o ∧ YOf Q ι τ₀ e ξ σ ≠ ⊥ ∧ IsAutRepU σ ∧
      (∀ rc, IsRec (s.hw s.v0) rc → IsTypeWD (s.hw s.v0) (fun _ : Fin n => 1) (rc (algNorm C.o))) ∧
      (Module.finrank ℂ (zPart (hset Q τ₀) θ ι x.toRingHom lam ξ K c0 ev) : Cardinal) = a₀ * Module.rank ℂ (C.inv ι τ₀)

end UpperTheory.V.Z.J.D
