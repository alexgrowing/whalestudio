import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.CoefficientRepTrivialOnUnramified
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ArithmeticPointClassicality

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped Matrix TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.V.Hi

def artOf {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {A : ValuationSubring Ω} {w : Plc L}
    (h : IsPlaceOver A w) : Weil h →* (w.adicCompletion L)ˣ := Classical.epsilon (IsLocalArtin h)

section Type_

variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {St : Type} {wt : St → Plc L} {At : St → ValuationSubring Ω} (ht : ∀ u, IsPlaceOver (At u) (wt u))

variable (n wt) in

abbrev KT : Subgroup (GV n wt) := Subgroup.pi Set.univ fun u => KO ((wt u).adicCompletion L) (Fin n)

def IsType {m : ℕ} (τ₀ : KT n wt →* GL (Fin m) ℂ) (χ : ∀ u, Fin n → Ine (F := L) (At u) →* ℂˣ) : Prop :=
  IsOpen (τ₀.ker : Set (KT n wt)) ∧
  ∀ (M : Type) [AddCommGroup M] [Module ℂ M] [Nontrivial M] (ρ : Representation ℂ (GV n wt) M) (σ : ∀ u, SmIrr (GLw n (wt u))),
    (∀ u, IsoSum (by classical exact ρ.comp (MonoidHom.mulSingle (fun u => GLw n (wt u)) u)) ⊤ (σ u)) →
    ((∃ F : Fin m → M, F ≠ 0 ∧ ∀ (k : KT n wt) i, ∑ j, τ₀ k i j • ρ k (F j) = F i) ↔
      ∀ u rc, IsRec (ht u) rc → IsTypeWD (ht u) (χ u) (rc (algNorm (σ u))))

end Type_

def HSet.IsMap {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
    {c : Coef l} (H : HSet L Ω l n c) {A : Type} [CommRing A] [Algebra c.O A] [IsLocalRing A] (θ : H.X.I.T →* Aˣ) (a : H.Op → c.O)
    (K : H.Lev) [Fact (CommOn (H.MK θ a K) (H.op A))] [Alg.IsCO c.O (H.TK θ a K)] {R : Type} [CommRing R] [Algebra c.O R]
    (D₀ : W.GDet n R H.Gq) (ψ₀ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* Rˣ) (f : R →ₐ[c.O] H.TK θ a K) : Prop :=
  H.IsUniv θ a K (maximalIdeal _) (D₀.map f.toRingHom) fun v i => W.pushCh f.toRingHom (ψ₀ v i)

def HSet.IsJ {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
    {c : Coef l} (H : HSet L Ω l n c) {A : Type} [CommRing A] [Algebra c.O A] [IsLocalRing A] (θ : H.X.I.T →* Aˣ) (a : H.Op → c.O)
    (K : H.Lev) {R : Type} [CommRing R] [Algebra c.O R] (D₀ : W.GDet n R H.Gq) (ψ₀ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* Rˣ)
    (lam : A →ₐ[c.O] R) (J : Ideal R) : Prop :=
  (H.MK θ a K = ⊥ ∧ J = ⊤) ∨ ∃ (_ : Fact (CommOn (H.MK θ a K) (H.op A))) (_ : Alg.IsCO c.O (H.TK θ a K))
    (f : R →ₐ[c.O] H.TK θ a K), H.MK θ a K ≠ ⊥ ∧ H.IsMap θ a K D₀ ψ₀ f ∧ Function.Surjective f ∧
      (∀ b, f (lam b) = algebraMap A _ b) ∧ J = RingHom.ker f

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]

namespace CaseU

variable (l L) (n : ℕ)

def away : UA L n →* ∀ w : {w : Plc L // ((l : ℕ) : 𝓞 L) ∉ w.asIdeal}, GLw n w.1 := Pi.monoidHom fun w => cLoc w.1

abbrev Ga : Type := (away l L n).range

variable {l L}

open Classical in

def cmp (w : Plc L) : Ga l L n →* GLw n w :=
  if h : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal then
    (Pi.evalMonoidHom (fun w : {w : Plc L // ((l : ℕ) : 𝓞 L) ∉ w.asIdeal} => GLw n w.1) ⟨w, h⟩).comp (away l L n).range.subtype
  else 1

variable (s : HidaSetting l L Ω)

abbrev wt : s.St → Plc L := fun u => s.w u

def Ub : Subgroup (Ga l L n) :=
  (⨅ u : s.St, (KO ((s.w u).adicCompletion L) (Fin n)).comap (cmp n (s.w u))) ⊓ (Kc _ n 1).comap (cmp n (s.w s.v0))

def toKT : Ub n s →* KT n (wt s) :=
  ((Pi.monoidHom fun u : s.St => cmp n (s.w u)).comp (Ub n s).subtype).codRestrict _
    fun g u _ => Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 g.2).1 u

def locA (w : Plc L) : Subgroup (Ub n s) :=
  ⨅ (w' : Plc L) (_ : w'.under (𝓞 (Lp L)) ≠ w.under (𝓞 (Lp L))), ((cmp n w').comp (Ub n s).subtype).ker

open Classical in

def sec (w : Plc L) : GLw n w →* Ub n s :=
  if h : Function.Bijective (((cmp n w).comp (Ub n s).subtype).comp (locA n s w).subtype) then
    (locA n s w).subtype.comp (MulEquiv.ofBijective _ h).symm.toMonoidHom
  else 1

variable {s} (V : s.Lev)

structure QData : Type 1 where
  Q : Type
  [fin : Fintype Q]
  wq : Q → Plc L
  inj : Function.Injective fun q => (wq q).under (𝓞 (Lp L))
  notS : ∀ q, (wq q).under (𝓞 (Lp L)) ∉ s.S
  range : V.S' = s.S ∪ Set.range fun q => (wq q).under (𝓞 (Lp L))

attribute [instance] QData.fin

def QData.empty (h : V.S' = s.S) : QData V where
  Q := Empty
  wq := Empty.elim
  inj q := q.elim
  notS q := q.elim
  range := by
    rw [h]
    exact (Set.union_eq_left.2 <| by rintro _ ⟨q, _⟩; exact q.elim).symm

variable {V} (Q : QData V)

def UQ : Subgroup (Ub n s) :=
  (⨅ (w : Plc L) (_ : w.under (𝓞 (Lp L)) ∉ V.S'), (KO (w.adicCompletion L) (Fin n)).comap ((cmp n w).comp (Ub n s).subtype)) ⊓
    ⨅ q : Q.Q, ((cmp n (Q.wq q)).comp (Ub n s).subtype).ker

variable {n} {c : Coef l} {m : ℕ}

def hset (τ₀ : KT n (wt s) →* GL (Fin m) c.O) : HSet L Ω l n c where
  V := V.frame.Vl
  Sl v := s.w v.1
  pl v := s.A v.1
  ovr v := s.hw v.1
  art v := artOf (s.hw v.1)
  Γ := ratU L n
  Ga := Ga l L n
  glob := (MonoidHom.prod (away l L n).rangeRestrict (Pi.monoidHom fun v : V.frame.Vl => cLoc (s.w v.1))).comp (ratU L n).subtype
  Ub := Ub n s
  m := m
  τ := τ₀.comp (toKT n s)
  Q := Q.Q
  wq := Q.wq
  Wp := {w | w.under (𝓞 (Lp L)) ∉ V.S' ∧ IsSplitAt w}
  sec := sec n s
  UQ := UQ n Q
  Gq := V.frame.G₀
  cG := isCompact_iff_compactSpace.1 (V.frame.η.ker.isClosed_of_isOpen V.frame.η_open).isCompact
  prj := V.pr
  admitted := Set.univ

variable (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ)

def TypeFor (τ₀ : KT n (wt s) →* GL (Fin m) c.O) : Prop :=
  ∀ t, r.IsTeich t → IsType (fun u : s.St => s.hw u)
    ((Matrix.GeneralLinearGroup.map (ι.toRingHom.comp (algebraMap c.O (Qbar l)))).comp τ₀)
    fun u i => W.pushCh (ι.toRingHom.comp (algebraMap c.O (Qbar l))) ((t i).comp (V.pr.comp (Ine (F := L) (s.A u)).subtype))

variable (τ₀ : KT n (wt s) →* GL (Fin m) c.O)

variable {r} in

def IsTheta (Λ : LamObj r) (θ : (hset Q τ₀).X.I.T →* Λ.Λˣ) : Prop :=
  ∀ (v : V.frame.Vl) (i : Fin n) (x : Weil (s.hw v.1)) (g : Dec (F := L) (s.A v.1)) (hg : g ∈ V.frame.Iv v) (y : Uo ((s.w v.1).adicCompletion L)),
    (g : G L Ω) = (x : G L Ω) → artOf (s.hw v.1) x = y →
    Λ.κ v i ⟨g, hg⟩ * (hset Q τ₀).epsV Λ.Λ v g ^ (i : ℕ) * θ (eV n _ v i y) = 1

structure IsRes (a : (hset Q τ₀).Op → c.O) : Prop where
  frob : ∀ (w : (hset Q τ₀).Wp) (B : ValuationSubring Ω) (σ : G L Ω), IsPlaceOver B w.1 → IsFrob B (normV w.1) σ →
    r.Dbar.chi (MonoidAlgebra.single (V.pr σ⁻¹) 1) =
      heckePol n (normV w.1) fun j => if h : 0 < j ∧ j - 1 < n then residue c.O (a (.inl (w, ⟨j - 1, h.2⟩))) else 1
  unif : ∀ (v : V.frame.Vl) (j : Fin n) (x : Weil (s.hw v.1)) (g : Dec (F := L) (s.A v.1)),
    (g : G L Ω) = (x : G L Ω) → artOf (s.hw v.1) x = unif _ →
    ((∏ i with i ≤ j, r.psib v i g * (hset Q τ₀).epsV (ResidueField c.O) v g ^ (i : ℕ) : (ResidueField c.O)ˣ) : ResidueField c.O) =
      residue c.O (a (.inr (v, j)))

def HasWt (s : HidaSetting l L Ω) (π : CuspSub L n) (lam : Wt L l n) : Prop :=
  ∀ (v : Vl l L) (j : W.Emb l (s.w v.1)), π.HasInfChar (ι.toRingHom.comp (j.1.comp (algebraMap L _)))
    (infOfWeight (lam (j.1.comp (algebraMap L _))).dual)

def PUHt (ρ : G L Ω →* GL (Fin n) (Qbar l)) : Prop := ∃ HT, Af.HasHT ρ HT

structure PU (lam : Wt L l n) (ρ : V.frame.G₀ →* GL (Fin n) (Qbar l)) : Prop where
  form : ∃ P, V.frame.IsForm c.O n ρ P
  type : ∀ t, r.IsTeich t → ∀ u : s.St, ∃ g : GL (Fin n) (Qbar l), ∀ x ∈ V.frame.Iu u,
    ((g * ρ x * g⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) =
      Matrix.diagonal fun i => algebraMap c.O (Qbar l) (t i x)
  cusp : Af.IsIrr ρ → ∃ π : CuspSub L n, (CG.mk π).IsRegAlg ∧ GlobalTheory.ContraPair.DualIsConj π ∧ Af.AttC ι (ρ.comp V.pr) π ∧ HasWt ι s π lam
  aut : ∃ σ : Submodule ℂ (UA L n → ℂ), IsAutRepU σ ∧ (∀ w, IsSplitAt w → ∀ τ : SmIrr (GLw n w),
      IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ → Af.LocGlob ι (ρ.comp V.pr) w τ) ∧
    (∀ y : Emb l (fun v : V.frame.Vl => s.w v.1), HasWeightAt σ (ι.toRingHom.comp y.res) (lam y.res).dual) ∧
    (∀ w : Plc L, w.under (𝓞 (Lp L)) ∉ V.S' → IsUnramU σ w) ∧
    (∀ w, IsSplitAt w → ∃ τ : SmIrr (GLw n w), IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ) ∧
    ∃ τ : SmIrr (GLw n (s.w s.v0)), IsCompAlong σ (locU n (s.w s.v0)) ((cLoc (s.w s.v0)).comp (locU n (s.w s.v0)).subtype) τ.ρ ∧
      fixd τ.ρ (Kc _ n 1) ≠ ⊥
  ht : PUHt (ρ.comp V.pr)

def infRep (lam : Wt L l n) :
    Representation ℂ (UA L n) (⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) :=
  PiTensorProduct.mapMonoidHom.comp (Pi.monoidHom fun e : Emb l (fun v : V.frame.Vl => s.w v.1) =>
    (GlobalTheory.Branching.sqRep ℂ n (lam e.res)).comp (cEmb (ι.toRingHom.comp e.res)))

variable {lam : Wt L l n} {d : ℕ}
  (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))

def toForm (F : Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) → Fin d → ℂ)
    (ℓ : Module.Dual ℂ (⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))) (g : UA L n) : ℂ :=
  ℓ (infRep ι lam g⁻¹ (e (F ((away l L n).rangeRestrict g, fun v => cLoc (s.w v.1) g))))

def IsBasis (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ) : Prop :=
  ∀ g x, e ((ξ g : Matrix (Fin d) (Fin d) ℂ) *ᵥ x) = algRep _ ι lam g (e x)

def YOf (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ) (σ : Submodule ℂ (UA L n → ℂ)) :
    Submodule ℂ (Fin m → (hset Q τ₀).X.Fn ℂ d) :=
  (hset Q τ₀).Big ι ξ ⊓ Submodule.span ℂ {F | ∀ i ℓ, toForm ι e (F i) ℓ ∈ σ}

variable {r} (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r)

structure HD : Type where
  m : ℕ
  τ₀ : KT n (wt s) →* GL (Fin m) c.O
  type : TypeFor r ι τ₀
  θ : (hset Q τ₀).X.I.T →* Λ.Λˣ
  theta : IsTheta Q τ₀ Λ θ
  isWt : (hset Q τ₀).IsWt θ
  a : (hset Q τ₀).Op → c.O
  res : IsRes Q r τ₀ a

variable {Q ι Λ} (R : HD Q ι Λ) (K : (hset Q R.τ₀).Lev)

abbrev HD.M := (hset Q R.τ₀).MK R.θ R.a K

def HD.IsJ (J : Ideal B.B) : Prop := (hset Q R.τ₀).IsJ R.θ R.a K B.u.D B.u.ψ (Λ.toPair B.u) J

def WtOf (h : s.Wt n) (lam : Wt L l n) : Prop :=
  ∀ (v : Vl l L) (j : Fin n) (τ : W.Emb l (s.w v.1)), htW lam j (τ.1.comp (algebraMap L _)) = h v j τ

end CaseU

end UpperTheory.V.Hi
