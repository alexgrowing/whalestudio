import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.HeckeCommRing
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open scoped TensorProduct Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Hi

open UpperTheory.V.W (Plc)
open UpperTheory.V.HV (Coef)

abbrev GLw {L : Type} [Field L] [NumberField L] (n : ℕ) (w : Plc L) : Type := GL (Fin n) (w.adicCompletion L)

section Alg

variable {L : Type} [Field L] [NumberField L] {l : ℕ} [Fact l.Prime] (n : ℕ) {V : Type} [Fintype V] (S : V → Plc L)

omit [Fintype V] in

abbrev GV : Type := ∀ v : V, GLw n (S v)

def iwS : Iwa (GV n S) := piIwa fun v : V => glIwa ((S v).adicCompletion L) n

def eV (v : V) (i : Fin n) (y : Uo ((S v).adicCompletion L)) : (iwS n S).T := by
  classical
  exact ⟨Pi.mulSingle v (eT _ n i y : GLw n (S v)), fun v' _ => by
    by_cases h : v' = v
    · subst h
      rw [Pi.mulSingle_eq_same]
      exact (eT _ n i y).2
    · rw [Pi.mulSingle_eq_of_ne h]
      exact (glIwa ((S v').adicCompletion L) n).T.one_mem⟩

omit [Fintype V] in

def alV (v : V) (j : ℕ) : GV n S := by
  classical
  exact Pi.mulSingle v (al ((S v).adicCompletion L) n j)

omit [Fintype V] in
variable (l) in

abbrev Emb : Type := Σ v : V, W.Emb l (S v)

variable {n S}

omit [Fintype V] in

def Emb.res (e : Emb l S) : L →+* Qbar l := e.2.1.comp (algebraMap L _)

variable (S) in

def algRep (ι : Qbar l ≃+* ℂ) (lam : Wt L l n) :
    Representation ℂ (GV n S) (⨂[ℂ] e : Emb l S, nablaSq ℂ n (lam e.res)) :=
  PiTensorProduct.mapMonoidHom.comp (Pi.monoidHom fun e : Emb l S =>
    ((GlobalTheory.Branching.sqRep ℂ n (lam e.res)).comp (Matrix.GeneralLinearGroup.map (ι.toRingHom.comp e.2.1))).comp
      (Pi.evalMonoidHom (fun v : V => GLw n (S v)) e.1))

def IsAlgWt (ι : Qbar l ≃+* ℂ) (lam : Wt L l n) {d : ℕ} (ξ : GV n S →* GL (Fin d) ℂ) : Prop :=
  ∃ e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l S, nablaSq ℂ n (lam e.res),
    ∀ g x, e ((ξ g : Matrix (Fin d) (Fin d) ℂ) *ᵥ x) = algRep S ι lam g (e x)

end Alg

def IsoSum {H M : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [AddCommGroup M] [Module ℂ M]
    (ρ : Representation ℂ H M) (Y : Submodule ℂ M) (σ : SmIrr H) : Prop :=
  Y ≤ ⨆ f : {f : σ.V →ₗ[ℂ] M // (∀ g v, f (σ.ρ g v) = ρ g (f v)) ∧ LinearMap.range f ≤ Y}, LinearMap.range f.1

structure HSet (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ)
    (c : Coef l) : Type 1 where
  V : Type
  [finV : Fintype V]
  Sl : V → Plc L
  pl : V → ValuationSubring Ω
  ovr : ∀ v, IsPlaceOver (pl v) (Sl v)
  art : ∀ v, Weil (ovr v) →* ((Sl v).adicCompletion L)ˣ
  Γ : Type
  Ga : Type
  [gΓ : Group Γ]
  [gA : Group Ga]
  glob : Γ →* Ga × GV n Sl
  Ub : Subgroup Ga
  m : ℕ
  τ : Ub →* GL (Fin m) c.O

  Q : Type
  [finQ : Fintype Q]
  wq : Q → Plc L

  Wp : Set (Plc L)
  sec : ∀ w : Plc L, GLw n w →* Ub

  UQ : Subgroup Ub
  Gq : Type
  [gG : Group Gq]
  [tG : TopologicalSpace Gq]
  [tgG : IsTopologicalGroup Gq]
  [cG : CompactSpace Gq]
  prj : G L Ω →* Gq

  admitted : Set (Wt L l n)

attribute [instance] HSet.finV HSet.finQ HSet.gΓ HSet.gA HSet.gG HSet.tG HSet.tgG HSet.cG

namespace HSet

variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {c : Coef l} (H : HSet L Ω l n c)

def X : Frame H.Γ H.Ga (GV n H.Sl) := ⟨iwS n H.Sl, H.glob, H.Ub⟩

abbrev Lev : Type := {K : ∀ q : H.Q, Subgroup (GLw n (H.wq q)) // ∀ q, IsOpen (K q : Set (GLw n (H.wq q))) ∧ IsCompact (K q : Set (GLw n (H.wq q)))}

def lev (K : H.Lev) : Subgroup H.X.Ub := H.UQ ⊔ ⨆ q : H.Q, (K.1 q).map (H.sec (H.wq q))

structure Ax : Prop where
  odd : l ≠ 2
  pos : 1 ≤ n
  Sl_over : ∀ v, ((l : ℕ) : 𝓞 L) ∈ (H.Sl v).asIdeal
  Sl_inj : Function.Injective H.Sl
  art_spec : ∀ v, IsLocalArtin (H.ovr v) (H.art v)
  Q_away : ∀ q, ((l : ℕ) : 𝓞 L) ∉ (H.wq q).asIdeal
  Wp_away : ∀ w ∈ H.Wp, ((l : ℕ) : 𝓞 L) ∉ w.asIdeal
  fin : ∀ K, H.X.FinLevel (H.lev K)
  τ_Q : ∀ q, ∀ g, H.τ (H.sec (H.wq q) g) = 1
  coefficientRep_trivial_on_unramified : ∀ w ∈ H.Wp, ∀ g, H.τ (H.sec w g) = 1
  Q_UQ : ∀ q, ∀ u ∈ H.UQ, ∀ g, Commute u (H.sec (H.wq q) g)
  Q_Q : ∀ q q', q ≠ q' → ∀ g g', Commute (H.sec (H.wq q) g) (H.sec (H.wq q') g')
  sectionsCommuteAtSplit : ∀ q, ∀ w ∈ H.Wp, ∀ g g', Commute (H.sec (H.wq q) g) (H.sec w g')
  W_le : ∀ w ∈ H.Wp, (KO (w.adicCompletion L) (Fin n)).map (H.sec w) ≤ H.UQ
  W_dec : ∀ w ∈ H.Wp, ∀ u ∈ H.UQ, ∃ k ∈ KO (w.adicCompletion L) (Fin n), ∃ u' ∈ H.UQ,
    u = H.sec w k * u' ∧ ∀ g, Commute u' (H.sec w g)
  Wm_mul_Wm_comm : ∀ w ∈ H.Wp, ∀ w' ∈ H.Wp, (∀ g g', Commute (H.sec w g) (H.sec w' g')) ∨
    ∃ e : GLw n w' ≃* GLw n w, (∀ g, e g ∈ KO (w.adicCompletion L) (Fin n) ↔ g ∈ KO (w'.adicCompletion L) (Fin n)) ∧
      ∀ g, H.sec w' g = H.sec w (e g)
  prj_cont : Continuous H.prj
  dense : Dense {g : H.Gq | ∃ w ∈ H.Wp, ∃ (A : ValuationSubring Ω) (σ : G L Ω),
    IsPlaceOver A w ∧ IsFrob A (normV w) σ ∧ g = H.prj σ⁻¹}

def dec (v : H.V) : Dec (F := L) (H.pl v) →* H.Gq := H.prj.comp (Dec (F := L) (H.pl v)).subtype

abbrev Op : Type := (H.Wp × Fin n) ⊕ (H.V × Fin n)

variable (A : Type) [CommRing A] [Algebra c.O A]

def τA : H.X.Ub →* GL (Fin H.m) A := (Matrix.GeneralLinearGroup.map (algebraMap c.O A)).comp H.τ

def op : H.Op → Module.End A (H.X.Fn A H.m)
  | .inl x => sphOp ((H.X.ra (H.τA A)).comp (H.sec x.1.1)) (x.2 + 1)
  | .inr x => H.X.U A H.m (alV n H.Sl x.1 (x.2 + 1))

variable {A} (θ : H.X.I.T →* Aˣ)

def MK [IsLocalRing A] (a : H.Op → c.O) (K : H.Lev) : Submodule A (H.X.Fn A H.m) :=
  locPart (H.X.Ord (H.τA A) θ (H.lev K)) (H.op A) fun i => algebraMap c.O A (a i)

structure IsWt [IsLocalRing A] : Prop where
  cont : H.X.I.ContChar θ
  free : ∀ K, H.X.Free (H.τA A) θ (H.lev K)

def finPart (x : A →+* Qbar l) (lam : Wt L l n) (v : H.V) (i : Fin n) (y : Uo ((H.Sl v).adicCompletion L)) : Qbar l :=
  x (θ (eV n H.Sl v i y)) / algPow (H.Sl v) (lowW lam i) ((y : ((H.Sl v).adicCompletion L)ˣ) : (H.Sl v).adicCompletion L)

def Arith (x : A →+* Qbar l) (lam : Wt L l n) : Prop :=
  ∃ e, ∀ v i (y : Uo ((H.Sl v).adicCompletion L)), (y : ((H.Sl v).adicCompletion L)ˣ) ∈ Uc _ e → H.finPart θ x lam v i y = 1

def Good (x : A →+* Qbar l) (lam : Wt L l n) : Prop :=
  lam ∈ H.admitted ∧ H.Arith θ x lam ∧ ∀ v i j, i ≠ j → ∃ y, H.finPart θ x lam v i y ≠ H.finPart θ x lam v j y

def DenseWt (lam : Wt L l n) : Prop := ∀ f : A, (∀ x : A →ₐ[c.O] Qbar l, H.Good θ x lam → x f = 0) → f = 0

variable (ι : Qbar l ≃+* ℂ)

def τC : H.X.Ub →* GL (Fin H.m) ℂ := (Matrix.GeneralLinearGroup.map (ι.toRingHom.comp (algebraMap c.O (Qbar l)))).comp H.τ

def Big {d : ℕ} (ξ : GV n H.Sl →* GL (Fin d) ℂ) : Submodule ℂ (Fin H.m → H.X.Fn ℂ d) :=
  Submodule.pi Set.univ (fun _ => H.X.AF ξ) ⊓ fixd (H.X.raF d (H.τC ι)) H.UQ

def atV (d : ℕ) (v : H.V) : Representation ℂ (GLw n (H.Sl v)) (Fin H.m → H.X.Fn ℂ d) := by
  classical
  exact (H.X.rpF ℂ d H.m).comp (MonoidHom.mulSingle (fun v : H.V => GLw n (H.Sl v)) v)

def atW (d : ℕ) (w : Plc L) : Representation ℂ (GLw n w) (Fin H.m → H.X.Fn ℂ d) := (H.X.raF d (H.τC ι)).comp (H.sec w)

structure Part (lam : Wt L l n) {d : ℕ} (ξ : GV n H.Sl →* GL (Fin d) ℂ) : Type 1 where
  Y : Submodule ℂ (Fin H.m → H.X.Fn ℂ d)
  le : Y ≤ H.Big ι ξ
  ne : Y ≠ ⊥
  σl : ∀ v : H.V, SmIrr (GLw n (H.Sl v))
  isoL : ∀ v, IsoSum (H.atV d v) Y (σl v)
  σq : ∀ q : H.Q, SmIrr (GLw n (H.wq q))
  isoQ : ∀ q : H.Q, IsoSum (H.atW ι d (H.wq q)) Y (σq q)
  a : H.Wp → ℕ → ℂ
  a_zero : ∀ w, a w 0 = 1
  sph : ∀ (w : H.Wp) j, ∀ F ∈ Y, sphOp (H.atW ι d w.1) j F = a w j • F
  r : H.Gq →* GL (Fin n) (Qbar l)
  cont : Continuous r
  ss : IsSSRep r
  frob : ∀ (w : H.Wp) (B : ValuationSubring Ω) (σ : G L Ω), IsPlaceOver B w.1 → IsFrob B (normV w.1) σ →
    (r (H.prj σ⁻¹) : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.map ι.toRingHom = heckePol n (normV w.1) (a w)
  atL : ∀ v, AtL ι (H.ovr v) (r.comp (H.dec v)) lam (σl v)
  atQ : ∀ (q : H.Q) (B : ValuationSubring Ω) (h : IsPlaceOver B (H.wq q)) (rc : IrrGL ((H.wq q).adicCompletion L) → WD h), IsRec h rc →
    Lev.WO ι (r.comp H.prj) (rc (algNorm (σq q)))

def Aut (P : Wt L l n → (H.Gq →* GL (Fin n) (Qbar l)) → Prop) : Prop :=
  ∀ lam ∈ H.admitted, ∀ (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ), IsAlgWt ι lam ξ → ∀ F ∈ H.Big ι ξ,
    (∃ K, F ∈ fixd (H.X.raF d (H.τC ι)) (H.lev K)) → (∃ e, F ∈ fixd (H.X.rpF ℂ d H.m) (H.X.I.I1 e)) →
    F ∈ ⨆ Y : {Y : H.Part ι lam ξ // P lam Y.r}, Y.1.Y

def lowVal (lam : Wt L l n) (v : H.V) (j : ℕ) : ℂ :=
  ι (∏ i ∈ Finset.univ.filter fun i : Fin n => (i : ℕ) < j,
    algPow (H.Sl v) (lowW lam i) ((unif ((H.Sl v).adicCompletion L) : ((H.Sl v).adicCompletion L)ˣ) : (H.Sl v).adicCompletion L))

def opC (lam : Wt L l n) (d : ℕ) : H.Op → Module.End ℂ (Fin H.m → H.X.Fn ℂ d)
  | .inl x => sphOp (H.atW ι d x.1.1) (x.2 + 1)
  | .inr x => (H.lowVal ι lam x.1 (x.2 + 1))⁻¹ • H.X.I.uOp (H.X.rpF ℂ d H.m) (alV n H.Sl x.1 (x.2 + 1))

def uzC (lam : Wt L l n) (d : ℕ) : Module.End ℂ (Fin H.m → H.X.Fn ℂ d) :=
  (∏ v, ∏ j ∈ Finset.range n, H.lowVal ι lam v j)⁻¹ • H.X.I.uOp (H.X.rpF ℂ d H.m) H.X.I.z

def ClAt (x : A →+* Qbar l) (lam : Wt L l n) {d : ℕ} (ξ : GV n H.Sl →* GL (Fin d) ℂ) (K : H.Lev) (e : ℕ) :
    Submodule ℂ (Fin H.m → H.X.Fn ℂ d) :=
  H.Big ι ξ ⊓ fixd (H.X.raF d (H.τC ι)) (H.lev K) ⊓ fixd (H.X.rpF ℂ d H.m) H.X.I.N ⊓ fixd (H.X.rpF ℂ d H.m) (H.X.I.Nm e) ⊓
    ⨅ (v) (i) (y), Module.End.eigenspace (H.X.rpF ℂ d H.m (eV n H.Sl v i y : H.X.I.T)) (ι (H.finPart θ x lam v i y))⁻¹

def OrdAt (x : A →+* Qbar l) (lam : Wt L l n) {d : ℕ} (ξ : GV n H.Sl →* GL (Fin d) ℂ) (K : H.Lev) (e : ℕ) :
    Submodule ℂ (Fin H.m → H.X.Fn ℂ d) :=
  ⨆ μ : {μ : ℂ // ‖ι.symm μ‖ = 1}, H.ClAt θ ι x lam ξ K e ⊓ (H.uzC ι lam d).maxGenEigenspace μ.1

structure IsSpec [IsLocalRing A] (x : A →+* Qbar l) (lam : Wt L l n) {d : ℕ} (ξ : GV n H.Sl →* GL (Fin d) ℂ) (c0 : ℕ)
    (sp : H.X.Fn A H.m → Fin H.m → H.X.Fn ℂ d) : Prop where
  alg : IsAlgWt ι lam ξ
  triv : ∀ v i (y : Uo ((H.Sl v).adicCompletion L)), (y : ((H.Sl v).adicCompletion L)ˣ) ∈ Uc _ (c0 + 1) → H.finPart θ x lam v i y = 1
  fin : ∀ K e, c0 ≤ e → FiniteDimensional ℂ (H.ClAt θ ι x lam ξ K e)
  stab : ∀ K e, c0 ≤ e → ∀ i, ∀ F ∈ H.ClAt θ ι x lam ξ K e, H.opC ι lam d i F ∈ H.ClAt θ ι x lam ξ K e
  int : ∀ K e, c0 ≤ e → ∀ i, ∀ F ∈ H.ClAt θ ι x lam ξ K e, F ≠ 0 → ∀ μ : ℂ, H.opC ι lam d i F = μ • F → ‖ι.symm μ‖ ≤ 1
  add : ∀ K, ∀ f ∈ H.X.Ord (H.τA A) θ (H.lev K), ∀ f' ∈ H.X.Ord (H.τA A) θ (H.lev K), sp (f + f') = sp f + sp f'
  smul : ∀ K, ∀ f ∈ H.X.Ord (H.τA A) θ (H.lev K), ∀ b : A, sp (b • f) = ι (x b) • sp f
  span : ∀ K e, c0 ≤ e → Submodule.span ℂ (sp '' H.X.Ord (H.τA A) θ (H.lev K)) = H.OrdAt θ ι x lam ξ K e
  indep : ∀ K (κ : Type) (b : Module.Basis κ A (H.X.Ord (H.τA A) θ (H.lev K))), LinearIndependent ℂ fun i => sp (b i)
  op : ∀ K i, ∀ f ∈ H.X.Ord (H.τA A) θ (H.lev K), sp (H.op A i f) = H.opC ι lam d i (sp f)
  act : ∀ K K' (q : H.Q) g, ∀ f ∈ H.X.Ord (H.τA A) θ (H.lev K), H.X.ra (H.τA A) (H.sec (H.wq q) g) f ∈ H.X.Ord (H.τA A) θ (H.lev K') →
    sp (H.X.ra (H.τA A) (H.sec (H.wq q) g) f) = H.atW ι d (H.wq q) g (sp f)

variable [IsLocalRing A] (a : H.Op → c.O) (K : H.Lev) [Fact (CommOn (H.MK θ a K) (H.op A))]

abbrev TK : Type := heckeAlg (H.MK θ a K) (H.op A)

abbrev gen (i : H.Op) : H.TK θ a K := heckeGen _ _ i

def genW (w : H.Wp) (j : ℕ) : H.TK θ a K := if h : 0 < j ∧ j - 1 < n then H.gen θ a K (.inl (w, ⟨j - 1, h.2⟩)) else 1

def epsV (R : Type) [CommRing R] [Algebra c.O R] (v : H.V) : Dec (F := L) (H.pl v) →* Rˣ :=
  (Units.map ((algebraMap c.O R).comp (algebraMap ℤ_[l] c.O)).toMonoidHom).comp
    ((cycZ L Ω l).comp (Dec (F := L) (H.pl v)).subtype)

structure IsUniv (I : Ideal (H.TK θ a K)) (D : W.GDet n (H.TK θ a K) H.Gq)
    (ψ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* (H.TK θ a K)ˣ) : Prop where
  cont : D.IsCont I
  ψ_cont : ∀ v i, Alg.AdicCont I fun g => (ψ v i g : H.TK θ a K)
  frob : ∀ (w : H.Wp) (B : ValuationSubring Ω) (σ : G L Ω), IsPlaceOver B w.1 → IsFrob B (normV w.1) σ →
    D.chi (MonoidAlgebra.single (H.prj σ⁻¹) 1) = heckePol n (normV w.1) (H.genW θ a K w)
  ψ_unit : ∀ v i (s : Weil (H.ovr v)) (g : Dec (F := L) (H.pl v)) (y : Uo ((H.Sl v).adicCompletion L)),
    (g : G L Ω) = (s : G L Ω) → H.art v s = y →
    (ψ v i g * H.epsV (H.TK θ a K) v g ^ (i : ℕ) : (H.TK θ a K)ˣ) * algebraMap A (H.TK θ a K) (θ (eV n H.Sl v i y)) = 1
  ψ_unif : ∀ v (j : Fin n) (s : Weil (H.ovr v)) (g : Dec (F := L) (H.pl v)),
    (g : G L Ω) = (s : G L Ω) → H.art v s = unif _ →
    ((∏ i with i ≤ j, ψ v i g * H.epsV (H.TK θ a K) v g ^ (i : ℕ) : (H.TK θ a K)ˣ) : H.TK θ a K) = H.gen θ a K (.inr (v, j))

structure Out (P : Wt L l n → (H.Gq →* GL (Fin n) (Qbar l)) → Prop) (I : Ideal (H.TK θ a K)) (D : W.GDet n (H.TK θ a K) H.Gq)
    (ψ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* (H.TK θ a K)ˣ) : Prop where
  univ : H.IsUniv θ a K I D ψ
  sep : ∀ lam ∈ H.admitted, H.DenseWt θ lam → ∀ t : H.TK θ a K,
    (∀ x : H.TK θ a K →ₐ[c.O] Qbar l, H.Good θ (x.toRingHom.comp (algebraMap A _)) lam → x t = 0) → t = 0
  pt : ∀ lam ∈ H.admitted, ∀ x : H.TK θ a K →ₐ[c.O] Qbar l, H.Arith θ (x.toRingHom.comp (algebraMap A _)) lam →
    ∃ r : H.Gq →* GL (Fin n) (Qbar l), Continuous r ∧ IsSSRep r ∧ P lam r ∧ D.map x.toRingHom = W.GDet.ofRep (W.mat r) ∧
      (H.Good θ (x.toRingHom.comp (algebraMap A _)) lam →
        ∀ v, W.HasFlag (r.comp (H.dec v)) (fun i => W.pushCh x.toRingHom (ψ v i)) ∧ PotCrys (H.pl v) (r.comp (H.dec v)))

end HSet

end UpperTheory.V.Hi
