import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.TowerRallisLemma
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.MuRange
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.KirCusp

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

open UpperTheory.V.Z.J.D

namespace UpperTheory.V.Z.Desc.V0

section Abs

variable {G H W : Type} [Group G] [Group H] [AddCommGroup W] [Module ℂ W]

def invE {m : ℕ} (K₁ : Subgroup G) (K₂ : Subgroup H) (τ₀ : K₁ →* GL (Fin m) ℂ) (ρ : Representation ℂ (G × H) W) (a : H →₀ ℤ)
    (N : ℕ) : Submodule ℂ (Fin m → W) :=
  invT K₁ K₂ τ₀ ρ ⊓ Submodule.pi Set.univ fun _ => ePart (ρ.comp (MonoidHom.inr G H)) a N

def inv1 {m : ℕ} (K₁ : Subgroup G) (τ₀ : K₁ →* GL (Fin m) ℂ) (ρ : Representation ℂ G W) : Submodule ℂ (Fin m → W) :=
  invT K₁ (⊥ : Subgroup Unit) τ₀ (ρ.comp (MonoidHom.fst G Unit))

end Abs

section Set

variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {c : Coef l} (H : HSet L Ω l n c)

def trA (A : Type) [CommRing A] : Representation A H.Ga (H.X.Fn A H.m) :=
  (rtr A (H.Ga × GV n H.Sl) (Fin H.m → A)).comp (MonoidHom.inl _ _)

def trF (d : ℕ) : Representation ℂ H.Ga (Fin H.m → H.X.Fn ℂ d) where
  toFun g := LinearMap.compLeft (rtr ℂ (H.Ga × GV n H.Sl) (Fin d → ℂ) (g, 1)) (Fin H.m)
  map_one' := by ext1 F; simp [← Prod.one_eq_mk]; rfl
  map_mul' g g' := by
    ext1 F
    rw [show ((g * g', 1) : H.Ga × GV n H.Sl) = (g, 1) * (g', 1) by simp, map_mul]
    rfl

structure Norm (g : H.Ga) : Prop where
  lev : ∀ K, ∀ u ∈ H.lev K, ∃ u' ∈ H.lev K, (u' : H.Ga) = g⁻¹ * u * g ∧ H.τ u' = H.τ u
  uq : ∀ u ∈ H.UQ, ∃ u' ∈ H.UQ, (u' : H.Ga) = g⁻¹ * u * g ∧ H.τ u' = H.τ u
  sph : ∀ w ∈ H.Wp, ∀ h, Commute g (H.sec w h : H.Ga)

structure NormK {G : Type} [Group G] (K₀ K₁ : Subgroup G) (β : G →* H.Ga) : Prop where
  norm : ∀ g ∈ K₀, Norm H (β g)
  triv : ∀ g ∈ K₁, ∃ u ∈ H.UQ, (u : H.Ga) = β g ∧ H.τ u = 1

variable {A : Type} [CommRing A] [Algebra c.O A] [IsLocalRing A] (θ : H.X.I.T →* Aˣ)

def Tr {d : ℕ} (sp : H.X.Fn A H.m → Fin H.m → H.X.Fn ℂ d) : Prop :=
  ∀ g, Norm H g → ∀ K, ∀ f ∈ H.X.Ord (H.τA A) θ (H.lev K), sp (trA H A g f) = trF H d g (sp f)

def IsProj {G : Type} [Group G] (β : G →* H.Ga) (a : G →₀ ℤ) (N : ℕ) {a₀ : H.Op → c.O} {K : H.Lev}
    (e : Module.End A (H.MK θ a₀ K)) : Prop :=
  ∀ m : H.MK θ a₀ K, N • (e m : H.X.Fn A H.m) = opE ((trA H A).comp β) a m

variable (ι : Qbar l ≃+* ℂ) (lam : Wt L l n) (K : H.Lev) {G : Type} [Group G] (β : G →* H.Ga) (a : G →₀ ℤ) (N : ℕ)

def IsDimE (D : ℕ) : Prop :=
  ∃ (x : A →ₐ[c.O] Qbar l) (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ) (c0 : ℕ) (sp : H.X.Fn A H.m → Fin H.m → H.X.Fn ℂ d)
    (ev : H.Op → ℂ), H.IsSpec θ ι x.toRingHom lam ξ c0 sp ∧ (∀ v j, ‖ι.symm (ev (.inr (v, j)))‖ = 1) ∧
    zPart H θ ι x.toRingHom lam ξ K c0 ev ≠ ⊥ ∧
    (∀ Y : H.Part ι lam ξ, Y.Y ⊓ zPart H θ ι x.toRingHom lam ξ K c0 ev ≠ ⊥ → Af.IsIrr Y.r) ∧
    D = Module.finrank ℂ ↥(zPart H θ ι x.toRingHom lam ξ K c0 ev ⊓ ePart ((trF H d).comp β) a N)

end Set

section U

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {n : ℕ} {s : HidaSetting l L Ω} {V : s.Lev} {c : Coef l} {m : ℕ}

variable (n s) in

def sec0 : GLw n (s.w s.v0) →* Ga l L n := (secS n s).comp (MonoidHom.inr _ _)

abbrev eC (Q : QData V) (τ₀ : KT n (wt s) →* GL (Fin m) c.O) (d : ℕ) (a : GLw n (s.w s.v0) →₀ ℤ) (N : ℕ) :=
  ePart ((trF (hset Q τ₀) d).comp (sec0 n s)) a N

abbrev cInv {σ : Submodule ℂ (UA L n → ℂ)} (C : Comps V σ) (ι : Qbar l ≃+* ℂ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (a : GLw n (s.w s.v0) →₀ ℤ) (N : ℕ) :=
  invE (KT n (wt s)) (Kc _ n 1) ((Matrix.GeneralLinearGroup.map (ι.toRingHom.comp (algebraMap c.O (Qbar l)))).comp τ₀) C.repS a N

abbrev cInv1 {σ : Submodule ℂ (UA L n → ℂ)} (C : Comps V σ) (ι : Qbar l ≃+* ℂ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O) :=
  inv1 (KT n (wt s)) ((Matrix.GeneralLinearGroup.map (ι.toRingHom.comp (algebraMap c.O (Qbar l)))).comp τ₀) (piRep fun u => (C.u u).ρ)

variable {r : Resid V.frame c.O n} (B : W.UniversalOrdinaryDeterminantRing r)

def NumE (Λ : LamObj r) (J : Ideal B.B) : Prop :=
  ∃ (M : Type) (_ : AddCommGroup M) (_ : Module B.B M) (_ : Module Λ.Λ M) (h : UpperTheory.V.J.Dat (Λ.toPair B.u) J M)
    (e : Module.End Λ.Λ M), Idem B.B e ∧
    ∀ (x y : B.Pt) (w : s.Wt n), J ≤ RingHom.ker x → J ≤ RingHom.ker y → x.Arith w → y.Good w → UpperTheory.V.J.IrrPt x → UpperTheory.V.J.IrrPt y →
      1 ≤ muE (Λ.toPair B.u) M h.hs e x ∧ muE (Λ.toPair B.u) M h.hs e x ≤ muE (Λ.toPair B.u) M h.hs e y

end U

def Spec2 : Prop :=
  ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l)
    (H : HSet L Ω l n c), H.Ax → ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (ι : Qbar l ≃+* ℂ) (x : A →ₐ[c.O] Qbar l) (lam : Wt L l n), H.Arith θ x.toRingHom lam →
    ∃ (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ) (c0 : ℕ) (sp : H.X.Fn A H.m → Fin H.m → H.X.Fn ℂ d),
      H.IsSpec θ ι x.toRingHom lam ξ c0 sp ∧ Tr H θ sp

def NormS : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev), V.S' = s.S → ∀ (Q : QData V) (c : Coef l) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O),
    NormK (hset Q τ₀) (KO _ (Fin n)) (Kc _ n 1) (sec0 n s)

def EEx : Prop :=
  ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l)
    (H : HSet L Ω l n c), H.Ax → ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (K : H.Lev) (a₀ : H.Op → c.O) [Fact (CommOn (H.MK θ a₀ K) (H.op A))] (G : Type) [Group G] (K₀ K₁ : Subgroup G) (β : G →* H.Ga)
    (a : G →₀ ℤ) (N : ℕ), NormK H K₀ K₁ β → IsE K₀ K₁ a N → IsUnit (N : A) →
    ∃ e : Module.End A (H.MK θ a₀ K), IsProj H θ β a N e ∧ e * e = e ∧ ∀ t : H.TK θ a₀ K, Commute e t.1

def MuZE : Prop :=
  ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l)
    (H : HSet L Ω l n c), H.Ax → ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (ι : Qbar l ≃+* ℂ) (x : A →ₐ[c.O] Qbar l) (lam : Wt L l n) (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ) (c0 : ℕ)
    (sp : H.X.Fn A H.m → Fin H.m → H.X.Fn ℂ d), H.IsSpec θ ι x.toRingHom lam ξ c0 sp → Tr H θ sp →
    ∀ (K : H.Lev) (a₀ : H.Op → c.O) [Fact (CommOn (H.MK θ a₀ K) (H.op A))]
    (B : Type) [CommRing B] [Algebra c.O B] (j : A →ₐ[c.O] B) (f : B →ₐ[c.O] H.TK θ a₀ K), Function.Surjective f →
    ∀ [Module B (H.MK θ a₀ K)] (hs : ∀ (b : A) (m : H.MK θ a₀ K), b • m = j b • m), (∀ (b : B) (m : H.MK θ a₀ K), b • m = (f b).1 m) →
    ∀ z : H.TK θ a₀ K →ₐ[c.O] Qbar l, z.toRingHom.comp (algebraMap A _) = x.toRingHom →
    ∀ (G : Type) [Group G] (K₀ K₁ : Subgroup G) (β : G →* H.Ga) (a : G →₀ ℤ) (N : ℕ), NormK H K₀ K₁ β → IsE K₀ K₁ a N → IsUnit (N : A) →
    ∀ e : Module.End A (H.MK θ a₀ K), IsProj H θ β a N e →
    muE j (H.MK θ a₀ K) hs e (z.comp f) = Module.finrank ℂ
      ↥(zPart H θ ι x.toRingHom lam ξ K c0 (fun i => ι (z (H.gen θ a₀ K i))) ⊓ ePart ((trF H d).comp β) a N)

def EigBoxE : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (n : ℕ) (V : Type) [Fintype V] (S : V → Plc L) (G H W W' X : Type) [Group G] [Group H]
    [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (GV n S) W)
    (κ : Representation ℂ (G × H) W') (π : Representation ℂ (GV n S × (G × H)) X) (f : W ⊗[ℂ] W' →ₗ[ℂ] X), Function.Injective f →
    Intw (box ρ κ) π f → ∀ (m : ℕ) (K₁ : Subgroup G) (K₂ : Subgroup H) (τ₀ : K₁ →* GL (Fin m) ℂ) (b : ℕ)
    (φ : ∀ v, Fin n → Uo ((S v).adicCompletion L) → ℂ) (μ : V → Fin n → ℂ) (a : H →₀ ℤ) (N : ℕ),
    Module.rank ℂ ↥(invE K₁ K₂ τ₀ (π.comp (MonoidHom.inr _ _)) a N ⊓ Submodule.pi Set.univ fun _ =>
      LinearMap.range f ⊓ eigL S (π.comp (MonoidHom.inl _ _)) b φ μ) = Module.rank ℂ (eigL S ρ b φ μ) * Module.rank ℂ (invE K₁ K₂ τ₀ κ a N)

def InvBox : Prop :=
  ∀ (G H W W' : Type) [Group G] [Group H] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (ρ : Representation ℂ G W)
    (κ : Representation ℂ H W') (m : ℕ) (K₁ : Subgroup G) (K₂ : Subgroup H) (τ₀ : K₁ →* GL (Fin m) ℂ) (a : H →₀ ℤ) (N : ℕ),
    Module.rank ℂ (invE K₁ K₂ τ₀ (box ρ κ) a N) = Module.rank ℂ (inv1 K₁ τ₀ ρ) * Module.rank ℂ ↥(fixd κ K₂ ⊓ ePart κ a N)

def InvEq1 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev), V.S' = s.S → ∀ (c : Coef l) (ι : Qbar l ≃+* ℂ) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O) (σ σ' : Submodule ℂ (UA L n → ℂ))
    (C : Comps V σ) (C' : Comps V σ'), (∀ u, KEq (C.u u) (C'.u u)) → Module.rank ℂ (cInv1 C ι τ₀) = Module.rank ℂ (cInv1 C' ι τ₀)

def YDimE : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev), V.S' = s.S → ∀ (Q : QData V) (c : Coef l) (ι : Qbar l ≃+* ℂ) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (lam : Wt L l n) (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))
    (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ), IsBasis ι e ξ → ∀ σ, IsAutRepU σ → (∀ w : Plc L, w.under (𝓞 (Lp L)) ∉ s.S → IsUnramU σ w) →
    (∀ y : Emb l (fun v : V.frame.Vl => s.w v.1), HasWeightAt σ (ι.toRingHom.comp y.res) (lam y.res).dual) → ∀ (C : Comps V σ) (b : ℕ)
    (φ : ∀ v : V.frame.Vl, Fin n → Uo ((s.w v.1).adicCompletion L) → ℂ) (μ : V.frame.Vl → Fin n → ℂ) (a : GLw n (s.w s.v0) →₀ ℤ) (N : ℕ),
    Module.rank ℂ ↥(YOf Q ι τ₀ e ξ σ ⊓ eigL (fun v : V.frame.Vl => s.w v.1) ((hset Q τ₀).X.rpF ℂ d m) b φ μ ⊓ eC Q τ₀ d a N) =
      Module.rank ℂ (eigL (fun v : V.frame.Vl => s.w v.1) C.repL b φ μ) * Module.rank ℂ (cInv C ι τ₀ a N)

def ZDecE : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev), V.S' = s.S → ∀ (Q : QData V) (c : Coef l) (ι : Qbar l ≃+* ℂ) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (lam : Wt L l n) (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))
    (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ), IsBasis ι e ξ → ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : (hset Q τ₀).X.I.T →* Aˣ) (x : A →ₐ[c.O] Qbar l) (c0 : ℕ)
    (sp : (hset Q τ₀).X.Fn A m → Fin m → (hset Q τ₀).X.Fn ℂ d), (hset Q τ₀).IsWt θ → (hset Q τ₀).IsSpec θ ι x.toRingHom lam ξ c0 sp →
    ∀ (K : (hset Q τ₀).Lev) (ev : (hset Q τ₀).Op → ℂ), (∀ v j, ‖ι.symm (ev (.inr (v, j)))‖ = 1) → ∀ (J : Type) [Fintype J] (σ : J → Submodule ℂ (UA L n → ℂ)),
    (∀ i, IsAutRepU (σ i)) → iSupIndep (fun i => YOf Q ι τ₀ e ξ (σ i)) →
    (hset Q τ₀).Big ι ξ ⊓ fixd ((hset Q τ₀).X.rpF ℂ d m) ((hset Q τ₀).X.I.I1 c0) ≤
      (⨆ i, YOf Q ι τ₀ e ξ (σ i) ⊓ fixd ((hset Q τ₀).X.rpF ℂ d m) ((hset Q τ₀).X.I.I1 c0)) →
    ∀ (a : GLw n (s.w s.v0) →₀ ℤ) (N : ℕ), (∀ g ∈ a.support, g ∈ KO _ (Fin n)) →
    Module.finrank ℂ ↥(zPart (hset Q τ₀) θ ι x.toRingHom lam ξ K c0 ev ⊓ eC Q τ₀ d a N) = ∑ i, Module.finrank ℂ ↥(YOf Q ι τ₀ e ξ (σ i) ⊓ zPart (hset Q τ₀) θ ι x.toRingHom lam ξ K c0 ev ⊓ eC Q τ₀ d a N)

def CountE : Prop :=
  Af.HypothesesH → Mult → CompOf → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev), V.S' = s.S → n ≤ 4 → ∀ (ι : Qbar l ≃+* ℂ) (lam : Wt L l n), ∃ a₀ : ℕ,
    ∀ (Q : QData V) (c : Coef l) (r : Resid V.frame c.O n) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O), TypeFor r ι τ₀ →
    ∀ (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))
    (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ), IsBasis ι e ξ → ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : (hset Q τ₀).X.I.T →* Aˣ) (x : A →ₐ[c.O] Qbar l) (c0 : ℕ)
    (sp : (hset Q τ₀).X.Fn A m → Fin m → (hset Q τ₀).X.Fn ℂ d), (hset Q τ₀).IsWt θ → (hset Q τ₀).IsSpec θ ι x.toRingHom lam ξ c0 sp →
    ∀ (K : (hset Q τ₀).Lev) (ev : (hset Q τ₀).Op → ℂ), (∀ v j, ‖ι.symm (ev (.inr (v, j)))‖ = 1) →
    zPart (hset Q τ₀) θ ι x.toRingHom lam ξ K c0 ev ≠ ⊥ → (∀ Y : (hset Q τ₀).Part ι lam ξ, Y.Y ⊓ zPart (hset Q τ₀) θ ι x.toRingHom lam ξ K c0 ev ≠ ⊥ → Af.IsIrr Y.r) →
    ∃ (π : CuspSub L n) (σ : Submodule ℂ (UA L n → ℂ)) (C : Comps V σ), (∀ u : s.St, π.IsLocComp (s.w u) (C.u u)) ∧
      π.IsLocComp (s.w s.v0) C.o ∧ YOf Q ι τ₀ e ξ σ ≠ ⊥ ∧ IsAutRepU σ ∧
      ∀ (a : GLw n (s.w s.v0) →₀ ℤ) (N : ℕ), (∀ g ∈ a.support, g ∈ KO _ (Fin n)) →
        (Module.finrank ℂ ↥(zPart (hset Q τ₀) θ ι x.toRingHom lam ξ K c0 ev ⊓ eC Q τ₀ d a N) : Cardinal) = a₀ * Module.rank ℂ (cInv C ι τ₀ a N)

def ZEqDimE : Prop :=
  Af.HypothesesH → Mult → CompOf → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev), V.S' = s.S → n ≤ 4 →
    ∃ (a : GLw n (s.w s.v0) →₀ ℤ) (N : ℕ), IsE (KO _ (Fin n)) (Kc _ n 1) a N ∧ ¬ l ∣ N ∧
    ∀ (Q : QData V) (c : Coef l) (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ) (m : ℕ)
    (τ₀ : KT n (wt s) →* GL (Fin m) c.O), TypeFor r ι τ₀ → ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A]
    (θ : (hset Q τ₀).X.I.T →* Aˣ), (hset Q τ₀).IsWt θ → ∀ (lam : Wt L l n) (K : (hset Q τ₀).Lev) (D D' : ℕ),
    IsDimE (hset Q τ₀) θ ι lam K (sec0 n s) a N D → IsDimE (hset Q τ₀) θ ι lam K (sec0 n s) a N D' → 1 ≤ D ∧ D = D'

def NumJE : Prop :=
  Af.HypothesesH → Mult → CompOf → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev), V.S' = s.S → n ≤ 4 → ∀ (Q : QData V) (c : Coef l) (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ) (B : W.UniversalOrdinaryDeterminantRing r)
    (Λ : LamObj r) (R : HD Q ι Λ) (K : (hset Q R.τ₀).Lev) (J : Ideal B.B), IsDomain Λ.Λ → R.IsJ B K J → J.IsRadical →
    NumE B Λ J

end UpperTheory.V.Z.Desc.V0
