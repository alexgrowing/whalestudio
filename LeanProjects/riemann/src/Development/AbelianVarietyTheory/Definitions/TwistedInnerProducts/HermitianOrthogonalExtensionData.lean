import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Development.AbelianVarietyTheory.Definitions.Foundations.StrictInterlaceIffDescEnum

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Grid

variable {D : D7}

section Sign

variable {E : Type} [Field E] [NumberField E] [StarRing E]

@[reducible] def sgn (ε : Bool) (V : Formalism.BasicNotions.HSpace E) : Formalism.BasicNotions.HSpace E where
  V := V.V
  hT := cond ε (-V.hT) V.hT
  herm := by
    cases ε
    · exact V.herm
    · exact ⟨fun x y => by simpa using V.herm.eq x y⟩
  nondeg := by
    cases ε
    · exact V.nondeg
    · exact ⟨fun x hx => V.nondeg.1 x fun y => by simpa using hx y, fun x hx => V.nondeg.2 x fun y => by simpa using hx y⟩
  rank := V.rank
  rank_eq := V.rank_eq
  frame := V.frame
  sig := fun τ => cond ε (V.sig τ).swap (V.sig τ)
  L0 := V.L0
  standardTuple_isLattice := V.standardTuple_isLattice
  baseLattice_isUnimodular := by
    cases ε
    · exact V.baseLattice_isUnimodular
    · have h := V.baseLattice_isUnimodular
      unfold Formalism.HermitianLatticesTheory.IsUnimodular Formalism.HermitianLatticesTheory.dual Formalism.E.hdual at h ⊢
      refine Eq.trans ?_ h
      ext x
      simp [Submodule.mem_iInf]

abbrev neg (V : Formalism.BasicNotions.HSpace E) : Formalism.BasicNotions.HSpace E := sgn true V

theorem sgn_false (V : Formalism.BasicNotions.HSpace E) : sgn false V = V := rfl

theorem neg_hT (V : Formalism.BasicNotions.HSpace E) (x y : V.V) : (neg V).hT x y = -V.hT x y := rfl

theorem neg_gram (V : Formalism.BasicNotions.HSpace E) : (neg V).gram = -V.gram := rfl

theorem neg_sig (V : Formalism.BasicNotions.HSpace E) (τ : E →+* ℂ) : (neg V).sig τ = ((V.sig τ).2, (V.sig τ).1) := rfl

theorem sgn_rank (ε : Bool) (V : Formalism.BasicNotions.HSpace E) : (sgn ε V).rank = V.rank := rfl

theorem hasSignature_neg {n : Type} {J : Matrix n n ℂ} {p q : ℕ} (h : Formalism.UG.HasSignature J p q) :
    Formalism.UG.HasSignature (-J) q p := by
  obtain ⟨e, P, hP⟩ := h
  let s : Fin p ⊕ Fin q ≃ Fin q ⊕ Fin p := Equiv.sumComm _ _
  refine ⟨e.trans s, Units.map (Matrix.reindexAlgEquiv ℂ ℂ s).toMonoidHom P, ?_⟩
  have h1 : Formalism.UG.Jpq q p = -(Formalism.UG.Jpq p q).submatrix s.symm s.symm := by
    ext (a | a) (b | b) <;> simp [Formalism.UG.Jpq, s, Matrix.one_apply]
  rw [h1, ← hP, ← Matrix.submatrix_mul_equiv _ _ _ s.symm, ← Matrix.submatrix_mul_equiv _ _ _ s.symm, ← Matrix.neg_mul,
    ← Matrix.mul_neg]
  rfl

theorem sigOK_sgn (ε : Bool) {V : Formalism.BasicNotions.HSpace E} (h : V.SigOK) : (sgn ε V).SigOK := by
  cases ε
  · exact h
  · intro τ
    have e : (neg V).gram.map τ = -(V.gram.map τ) := by ext i j; simp [neg_gram]
    show Formalism.UG.HasSignature ((neg V).gram.map τ) (V.sig τ).2 (V.sig τ).1
    rw [e]
    exact hasSignature_neg (h τ)

end Sign

theorem hr_sgn (ε : Bool) (V : HSp D) :
    HR (AF D.host.F) D.sp.cm.sig (sgn ε V).gram = HR (AF D.host.F) D.sp.cm.sig V.gram := by
  cases ε
  · rfl
  · ext g
    have e : JR (F := D.host.F) (AF D.host.F) (neg V).gram = -JR (F := D.host.F) (AF D.host.F) V.gram := by
      ext i j; simp [JR, neg_gram]
    show Formalism.UG.cT _ _ * JR (F := D.host.F) (AF D.host.F) (neg V).gram * _ = JR (F := D.host.F) (AF D.host.F) (neg V).gram ↔
      Formalism.UG.cT _ _ * JR (F := D.host.F) (AF D.host.F) V.gram * _ = JR (F := D.host.F) (AF D.host.F) V.gram
    rw [e, Matrix.mul_neg, Matrix.neg_mul, neg_inj]

def ofSgn (ε : Bool) (V : HSp D) : GA D (sgn ε V) ≃* GA D V where
  toFun g := ⟨g.1, hr_sgn ε V ▸ g.2⟩
  invFun g := ⟨g.1, (hr_sgn ε V).symm ▸ g.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem mt_ofSgn (ε : Bool) (V : HSp D) (g : GA D (sgn ε V)) : Formalism.L2.Theta.mt V (ofSgn ε V g) = Formalism.L2.Theta.mt (sgn ε V) g := rfl

theorem ofSgn_false (V : HSp D) (g : GA D V) : ofSgn false V g = g := rfl

theorem continuous_ofSgn (ε : Bool) (V : HSp D) : Continuous (ofSgn ε V) :=
  Continuous.subtype_mk continuous_subtype_val _

theorem continuous_ofSgn_symm (ε : Bool) (V : HSp D) : Continuous (ofSgn ε V).symm :=
  Continuous.subtype_mk continuous_subtype_val _

theorem neg_gram_inv (V : HSp D) : (neg V).gram⁻¹ = -V.gram⁻¹ := by
  refine Matrix.inv_eq_right_inv ?_
  rw [neg_gram, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
  exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (gram_det_ne V))

theorem hO_neg (S T : HSp D) (x y : WO S T) : hO (neg S) T x y = -hO S T x y := by
  unfold hO
  rw [neg_gram_inv]
  simp [Finset.sum_neg_distrib]

theorem symplO_neg (S T : HSp D) (x y : WO S T) : symplO (neg S) T x y = -symplO S T x y := by
  unfold symplO
  rw [hO_neg, mul_neg, map_neg]

def sgnM (ε : Bool) {k : ℕ} (s : Matrix (Fin k) (Fin k) ℂ) : Matrix (Fin k) (Fin k) ℂ := cond ε (-s) s

theorem isCartanInv_sgn (ε : Bool) (V : HSp D) (τ : D.what₂.Tau) {s : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (h : IsCartanInv (gramAt D V τ) s) : IsCartanInv (gramAt D (sgn ε V) τ) (sgnM ε s) := by
  cases ε
  · exact h
  · have e : gramAt D (neg V) τ = -gramAt D V τ := by ext i j; simp [gramAt, neg_gram]
    show IsCartanInv (gramAt D (neg V) τ) (-s)
    rw [e]
    refine ⟨by simpa using h.1, by simpa using h.2.1, by simpa using h.2.2⟩

section Princ

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

def princGL (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (I : Ideal (𝓞 E)) : Subgroup (GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :=
  (Formalism.UG.bc (Ideal.Quotient.mk (idS F I))).ker.map (frGL β)

theorem mem_princGL {β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {I : Ideal (𝓞 E)} {x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} :
    x ∈ princGL β I ↔ ∃ y, frGL β y = x ∧ ∀ i j, (y.1 - 1) i j ∈ idS F I := by
  have key : ∀ y : GL (Fin n) (Formalism.L2.Herm.intAf F E),
      Formalism.UG.bc (Ideal.Quotient.mk (idS F I)) y = 1 ↔ ∀ i j, (y.1 - 1) i j ∈ idS F I := by
    intro y
    rw [Units.ext_iff, ← Matrix.ext_iff]
    refine forall₂_congr fun i j => ?_
    rw [Matrix.sub_apply, ← Ideal.Quotient.eq]
    have h1 : (1 : GL (Fin n) (Formalism.L2.Herm.intAf F E ⧸ idS F I)).1 i j =
        Ideal.Quotient.mk (idS F I) ((1 : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) i j) := by
      simp only [Units.val_one, Matrix.one_apply]
      split_ifs <;> simp
    rw [h1]
    rfl
  exact ⟨fun ⟨y, hy, e⟩ => ⟨y, e, (key y).1 hy⟩, fun ⟨y, e, hy⟩ => ⟨y, (key y).2 hy, e⟩⟩

theorem princGL_top (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : princGL β ⊤ = St β := by
  ext x
  rw [mem_princGL]
  refine ⟨fun ⟨y, hy, _⟩ => ⟨y, hy⟩, fun ⟨y, hy⟩ => ⟨y, hy, fun i j => ?_⟩⟩
  simp [idS, Ideal.map_top]

theorem princGL_mono (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) {I I' : Ideal (𝓞 E)} (h : I ≤ I') :
    princGL β I ≤ princGL β I' := fun _ hx => by
  obtain ⟨y, h2, h3⟩ := mem_princGL.1 hx
  exact mem_princGL.2 ⟨y, h2, fun i j => Ideal.map_mono h (h3 i j)⟩

end Princ

variable (D) in

structure Node where

  V : HSp D

  S : D.what₂.Tau → SPar

  M : DSModel V S

  Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)

  β : GL (Fin V.rank) (Lev.EAf D)

namespace Node

variable (N : Node D)

def InLat (y : N.V.V) : Prop := N.V.frame.equivFun y ∈ N.Λ

structure Is (ν q : ℕ) (S : D.what₂.Tau → SPar) : Prop where

  rank : N.V.rank = ν

  sigOK : N.V.SigOK

  sig : ∀ τ : D.host.E →+* ℂ, N.V.sig τ = (ν - q, q)

  par : N.S = S

  frame : IsSDFrame N.V N.β N.Λ 1

abbrev Maps : Type := SmT N.M →ₗ[ℂ] (GA D N.V → ℂ)

abbrev Cusp (θ : InfFam D) : Submodule ℂ N.Maps := MultT θ N.M ∅ 1

theorem multT_le_cusp (θ : InfFam D) (J : Set (GA D N.V)) (χ : GA D N.V → ℂ) : MultT θ N.M J χ ≤ N.Cusp θ :=
  Submodule.map_mono (Submodule.span_mono fun _ h => ⟨h.aut, h.cusp, fun _ _ hk => absurd hk (Set.notMem_empty _), h.equiv, h.cont⟩)

def princ (I : Ideal (𝓞 D.host.E)) : Subgroup (GL (Fin N.V.rank) (Lev.EAf D)) :=
  UA D.sp.cm N.V.gram ⊓ princGL N.β I

theorem mem_princ {I : Ideal (𝓞 D.host.E)} {x : GL (Fin N.V.rank) (Lev.EAf D)} :
    x ∈ N.princ I ↔ x ∈ UA D.sp.cm N.V.gram ∧ ∃ y, frGL N.β y = x ∧ ∀ i j, (y.1 - 1) i j ∈ idS D.host.F I :=
  and_congr_right fun _ => mem_princGL

theorem princ_top : N.princ ⊤ = UA D.sp.cm N.V.gram ⊓ St N.β := by
  rw [princ, princGL_top]

theorem princ_mono {I I' : Ideal (𝓞 D.host.E)} (h : I ≤ I') : N.princ I ≤ N.princ I' :=
  inf_le_inf_left _ (princGL_mono _ h)

structure MeasDat where

  ν : Measure (GA D N.V)

  fd : Set (GA D N.V)

def MeasDat.Is {N : Node D} (m : N.MeasDat) (df : Prop) (K : Subgroup (GL (Fin N.V.rank) (Lev.EAf D))) : Prop :=
  (df → IsMeasDef N.V K m.ν m.fd) ∧ (¬ df → Lev.IsMeasFD N.V K m.ν m.fd)

end Node

section Pair

variable (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (ε : Bool)

abbrev WRep (S T : HSp D) : Type := GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)

def WRep.toSgn {S T : HSp D} (ω : WRep S T) : WRep (sgn ε S) T :=
  ω.comp ((ofSgn ε S).toMonoidHom.prodMap (MonoidHom.id _))

def IsWeil (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : WRep S T) : Prop :=
  IsWeilDatumO ψ (sgn ε S) T χS χT (ω.toSgn ε)

theorem isWeil_false (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : WRep S T) :
    IsWeil ψ false S T χS χT ω ↔ IsWeilDatumO ψ S T χS χT ω := Iff.rfl

variable (S T : Node D)

abbrev Pol : Type := PolF D T.V.rank S.V.rank

def cartS : D.what₂.Tau → Matrix (Fin S.V.rank) (Fin S.V.rank) ℂ := fun τ => sgnM ε (cart S.M τ)

def fock (f : WO S.V T.V → ℂ) : Pol S T →ₗ[ℂ] (WO S.V T.V → ℂ) :=
  pureTensorO ψ θ (sgn ε S.V) T.V (cartS ε S) (cart T.M) (onb (V := S.V) S.M) (onb T.M) f

def IsVac (f : WO S.V T.V → ℂ) : Prop :=
  IsVacO ψ θ (sgn ε S.V) T.V (cartS ε S) (cart T.M) S.Λ T.Λ f

def IsFinVec (f : WO S.V T.V → ℂ) : Prop :=
  IsThetaFunO ψ (sgn ε S.V) T.V f ∧
    ∀ τ, IsFockVacAt (heisO ψ (sgn ε S.V) T.V) θ τ (cplxO (cartS ε S τ) (cart T.M τ)) f

theorem IsVac.isFinVec {f : WO S.V T.V → ℂ} (h : IsVac ψ θ ε S T f) : IsFinVec ψ θ ε S T f :=
  ⟨h.2.theta, h.2.fock⟩

abbrev Coset (I : Ideal (𝓞 D.host.E)) : Type := Matrix (Fin T.V.rank) (Fin S.V.rank) (𝓞 D.host.E ⧸ I)

def InCosetOf (I : Ideal (𝓞 D.host.E)) (c : Coset S T I) (x : WO S.V T.V) : Prop :=
  ∀ i j, ∃ h : frMapO S.V T.V S.β T.β x i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E,
    Ideal.Quotient.mk (idS D.host.F I) ⟨_, h⟩ = cmpS D.host.F I (c i j)

open Classical in

def cosetInd (e : AE D) (I : Ideal (𝓞 D.host.E)) (c : Coset S T I) (x : WO S.V T.V) : ℂ :=
  if IsHalf e x ∧ InCosetOf S T I c x then 1 else 0

def IsCosetVec (e : AE D) (I : Ideal (𝓞 D.host.E)) (c : Coset S T I) (f₀ f : WO S.V T.V → ℂ) : Prop :=
  IsThetaAt ψ (symplO (sgn ε S.V) T.V) (heisO ψ (sgn ε S.V) T.V) e (latO (sgn ε S.V) T.V S.Λ T.Λ fun _ => True) 1 f₀
    (cosetInd S T e I c) f

variable {S T}

theorem InCosetOf.unique {I : Ideal (𝓞 D.host.E)} (hI : I ≠ ⊥) {c c' : Coset S T I} {x : WO S.V T.V}
    (h : InCosetOf S T I c x) (h' : InCosetOf S T I c' x) : c = c' := by
  ext i j
  obtain ⟨_, h1⟩ := h i j
  obtain ⟨_, h2⟩ := h' i j
  exact cmpS_inj I hI (h1.symm.trans h2)

theorem exists_inCosetOf {I : Ideal (𝓞 D.host.E)} (hI : I ≠ ⊥) (x : WO S.V T.V) :
    (∃ c, InCosetOf S T I c x) ↔ IsIntM (frMapO S.V T.V S.β T.β x) := by
  refine ⟨fun ⟨c, h⟩ i j => (h i j).1, fun h => ?_⟩
  choose c hc using fun i j => cmpS_surj (F := D.host.F) I hI (Ideal.Quotient.mk _ ⟨_, h i j⟩)
  exact ⟨fun i j => c i j, fun i j => ⟨h i j, (hc i j).symm⟩⟩

theorem finite_coset {I : Ideal (𝓞 D.host.E)} (hI : I ≠ ⊥) : Finite (Coset S T I) := by
  have := Ideal.finiteQuotientOfFreeOfNeBot I hI
  exact Pi.finite

end Pair

structure IsIntw {V W : HSp D} {S S' : D.what₂.Tau → SPar} {X P : Type} [AddCommGroup P] [Module ℂ P] (θ : InfFam D)
    (M : DSModel V S) (M' : DSModel W S') (ω : GA D V × GA D W →* Module.End ℂ (X → ℂ)) (pt : P → (X → ℂ))
    (It : P →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M) : Prop where

  ne : It ≠ 0

  bdd : ∀ φ w, ∃ c : ℝ, ∀ v : M'.Vec,
    ‖ellT M w (inclT M (It φ (PiTensorProduct.tprod ℂ v)))‖ ≤ c * ∏ τ, ‖(v τ : M'.H τ)‖

  eqK : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ φ φ', pt φ' = ω (atTau θ V τ g, 1) (pt φ) →
    ∀ v, inclT M (It φ' v) = actT M τ g (inclT M (It φ v))

  eqg : ∀ τ, ∀ Y ∈ lieAt V τ, ∀ φ φ', (∀ z, HasDerivAt (fun t : ℝ => ω (oneP θ V τ Y t, 1) (pt φ) z) (pt φ' z) 0) →
    ∀ v, DerT M τ Y (It φ v) (It φ' v)

  invK : ∀ τ, ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D W τ), ∀ φ φ' v v', pt φ' = ω (1, atTau θ W τ h) (pt φ) →
    inclT M' v' = actT M' τ h (inclT M' v) → It φ' v' = It φ v

  invg : ∀ τ, ∀ Y ∈ lieAt W τ, ∀ φ φ' v v', (∀ z, HasDerivAt (fun t : ℝ => ω (1, oneP θ W τ Y t) (pt φ) z) (pt φ' z) 0) →
    DerT M' τ Y v v' → It φ' v + It φ v' = 0

theorem isIntw_iff {V W : HSp D} {S S' : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) (M' : DSModel W S')
    (ω : WRep V W) (pt : PolF D W.rank V.rank → (WO V W → ℂ)) (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M) :
    IsIntw θ M M' ω pt It ↔ IsItW θ M M' ω pt It :=
  ⟨fun h => ⟨h.ne, h.bdd, h.eqK, h.eqg, h.invK, h.invg⟩, fun h => ⟨h.ne, h.bdd, h.eqK, h.eqg, h.invK, h.invg⟩⟩

def WRep.swap {S T : HSp D} (ω : WRep S T) : GA D T × GA D S →* Module.End ℂ (WO S T → ℂ) :=
  ω.comp (MulEquiv.prodComm (M := GA D T) (N := GA D S)).toMonoidHom

theorem WRep.swap_apply {S T : HSp D} (ω : WRep S T) (h : GA D T) (g : GA D S) : ω.swap (h, g) = ω (g, h) := rfl

structure ArrS (S T : Node D) where

  ω : WRep S.V T.V

  vac : WO S.V T.V → ℂ

  It : Pol S T →ₗ[ℂ] SmT T.M →ₗ[ℂ] SmT S.M

structure ArrT (S T : Node D) where

  ω : WRep S.V T.V

  vac : WO S.V T.V → ℂ

  It : Pol S T →ₗ[ℂ] SmT S.M →ₗ[ℂ] SmT T.M

section Arrows

variable (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (ε : Bool) {S T : Node D}

structure ArrS.Is (a : ArrS S T) (χS χT : (AE D)ˣ →* Circle) : Prop where

  weil : IsWeil ψ ε S.V T.V χS χT a.ω

  vac : IsVac ψ θ ε S T a.vac

  intw : IsItW θ S.M T.M a.ω (fock ψ θ ε S T a.vac) a.It

structure ArrT.Is (a : ArrT S T) (χS χT : (AE D)ˣ →* Circle) : Prop where

  weil : IsWeil ψ ε S.V T.V χS χT a.ω

  vac : IsVac ψ θ ε S T a.vac

  intw : IsIntw θ T.M S.M a.ω.swap (fock ψ θ ε S T a.vac) a.It

def ArrS.int (a : ArrS S T) (m : T.MeasDat) (Φ : WO S.V T.V → ℂ) (F : GA D T.V → ℂ) : GA D S.V → ℂ :=
  Lift.liftInt m.ν m.fd (thetaKO a.ω) Φ F

def ArrT.int (a : ArrT S T) (m : S.MeasDat) (Φ : WO S.V T.V → ℂ) (F : GA D S.V → ℂ) : GA D T.V → ℂ :=
  Lift.liftInt m.ν m.fd (fun h g Φ => thetaKO a.ω g h Φ) Φ F

def ArrS.IsLift (a : ArrS S T) (m : T.MeasDat) (f : WO S.V T.V → ℂ) (io : T.Cusp θ →ₗ[ℂ] S.Cusp θ) : Prop :=
  Lift.IsIo m.ν m.fd (thetaKO a.ω) (fock ψ θ ε S T f) a.It (T.Cusp θ) (S.Cusp θ) io

def ArrT.IsLift (a : ArrT S T) (m : S.MeasDat) (f : WO S.V T.V → ℂ) (io : S.Cusp θ →ₗ[ℂ] T.Cusp θ) : Prop :=
  Lift.IsIo m.ν m.fd (fun h g Φ => thetaKO a.ω g h Φ) (fock ψ θ ε S T f) a.It (S.Cusp θ) (T.Cusp θ) io

def ArrT.IsAdj (a : ArrT S T) (Tp : Pol S T →ₗ⋆[ℂ] SmT T.M →ₗ[ℂ] SmT S.M) : Prop :=
  ∀ (P : Pol S T) (v : S.M.Vec) (w : T.M.Vec),
    ellT T.M (fun τ => w τ) (inclT T.M (a.It P (PiTensorProduct.tprod ℂ v))) =
      starRingEnd ℂ (ellT S.M (fun τ => v τ) (inclT S.M (Tp P (PiTensorProduct.tprod ℂ w))))

def ArrT.IsLiftConj (a : ArrT S T) (Tp : Pol S T →ₗ⋆[ℂ] SmT T.M →ₗ[ℂ] SmT S.M) (m : T.MeasDat) (f : WO S.V T.V → ℂ)
    (up : T.Cusp θ →ₗ[ℂ] S.Cusp θ) : Prop :=
  Lift.IsIoUp m.ν m.fd (fun h g Φ => thetaKO a.ω g h Φ) (fock ψ θ ε S T f) Tp (S.Cusp θ) (T.Cusp θ) up

variable {ψ θ ε}

theorem ArrS.IsLift.int_eq {a : ArrS S T} {m : T.MeasDat} {f : WO S.V T.V → ℂ} {io : T.Cusp θ →ₗ[ℂ] S.Cusp θ}
    (h : a.IsLift ψ θ ε m f io) (F : T.Cusp θ) (P : Pol S T) (v : SmT T.M) :
    a.int m (fock ψ θ ε S T f P) (F.1 v) = (io F).1 (a.It P v) := funext fun g => h.eq F P v g

theorem ArrT.IsLift.int_eq {a : ArrT S T} {m : S.MeasDat} {f : WO S.V T.V → ℂ} {io : S.Cusp θ →ₗ[ℂ] T.Cusp θ}
    (h : a.IsLift ψ θ ε m f io) (F : S.Cusp θ) (P : Pol S T) (v : SmT S.M) :
    a.int m (fock ψ θ ε S T f P) (F.1 v) = (io F).1 (a.It P v) := funext fun g => h.eq F P v g

end Arrows

section Cast

variable {S S' T T' : Node D}

def ArrS.cast (hS : S = S') (hT : T = T') (a : ArrS S T) : ArrS S' T' := hS ▸ hT ▸ a

def Node.MeasDat.cast (h : S = S') (m : S.MeasDat) : S'.MeasDat := h ▸ m

def castFun (hS : S = S') (hT : T = T') (f : WO S.V T.V → ℂ) : WO S'.V T'.V → ℂ := hS ▸ hT ▸ f

def Node.castMaps (h : S = S') : S.Maps ≃ₗ[ℂ] S'.Maps := h ▸ LinearEquiv.refl ℂ S.Maps

def Node.castCusp (θ : InfFam D) (h : S = S') : S.Cusp θ ≃ₗ[ℂ] S'.Cusp θ := h ▸ LinearEquiv.refl ℂ (S.Cusp θ)

theorem Node.coe_castCusp (θ : InfFam D) (h : S = S') (F : S.Cusp θ) :
    (Node.castCusp θ h F).1 = Node.castMaps h F.1 := by subst h; rfl

theorem Node.castMaps_mem (θ : InfFam D) (h : S = S') (F : S.Maps) : Node.castMaps h F ∈ S'.Cusp θ ↔ F ∈ S.Cusp θ := by
  subst h; rfl

theorem ArrS.is_cast (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (ε : Bool) (hS : S = S') (hT : T = T') (a : ArrS S T)
    (χS χT : (AE D)ˣ →* Circle) : (a.cast hS hT).Is ψ θ ε χS χT ↔ a.Is ψ θ ε χS χT := by subst hS hT; rfl

theorem isFinVec_cast (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (ε : Bool) (hS : S = S') (hT : T = T')
    (f : WO S.V T.V → ℂ) : IsFinVec ψ θ ε S' T' (castFun hS hT f) ↔ IsFinVec ψ θ ε S T f := by subst hS hT; rfl

theorem ArrS.isLift_cast (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (ε : Bool) (hS : S = S') (hT : T = T') (a : ArrS S T)
    (m : T.MeasDat) (f : WO S.V T.V → ℂ) (io : T'.Cusp θ →ₗ[ℂ] S'.Cusp θ) :
    (a.cast hS hT).IsLift ψ θ ε (m.cast hT) (castFun hS hT f) io ↔
      a.IsLift ψ θ ε m f ((Node.castCusp θ hS).symm.toLinearMap ∘ₗ io ∘ₗ (Node.castCusp θ hT).toLinearMap) := by
  subst hS hT; rfl

theorem ArrS.cast_vac (hS : S = S') (hT : T = T') (a : ArrS S T) : (a.cast hS hT).vac = castFun hS hT a.vac := by
  subst hS hT; rfl

theorem ArrS.cast_It_congr (hS : S = S') (hT : T = T') {a b : ArrS S T} (h : a.It = b.It) :
    (a.cast hS hT).It = (b.cast hS hT).It := by subst hS hT; exact h

end Cast

structure HermitianOrthogonalExtensionData (A B : Node D) (c : ℕ) where

  ι : A.V.V →ₗ[D.host.E] B.V.V

  a : Fin c → B.V.V

abbrev FrId (D : D7) : Type := FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E

structure HermitianOrthogonalExtensionData.Is {A B : Node D} {c : ℕ} (d : HermitianOrthogonalExtensionData A B c) (g : Fin c → Fin c → D.host.E) (𝔟 : Fin c → FrId D) : Prop where

  isom : Formalism.BasicNotions.HSpace.IsIsomEmb A.V B.V d.ι

  orth : ∀ x p, B.V.hD (d.ι x) (d.a p) = 0

  gram : ∀ p q, B.V.hD (d.a p) (d.a q) = g p q

  rank : A.V.rank + c = B.V.rank

  lat : ∀ y, B.InLat y ↔ ∃ x, A.InLat x ∧ ∃ t : Fin c → D.host.E, (∀ p, t p ∈ 𝔟 p) ∧ y = d.ι x + ∑ p, t p • d.a p

def antiDiagonalSignGramMatrix (K : Type) [Ring K] (c : ℕ) (p q : Fin c) : K :=
  if p.1 + q.1 + 1 = c then (if p = q then -1 else 1) else 0

def staircaseExtensionIdeal (𝔰 : Ideal (𝓞 D.host.E)) (c : ℕ) (p : Fin c) : FrId D :=
  (D.host.AA * ((D.host.conj • 𝔰 : Ideal (𝓞 D.host.E)) : FrId D)⁻¹) ^ (c - p.1) * (D.host.AAbar⁻¹ * (𝔰 : FrId D)) ^ (p.1 + 1)

example : antiDiagonalSignGramMatrix ℤ 1 0 0 = -1 := by decide

example : (Matrix.of (antiDiagonalSignGramMatrix ℤ 2)) = !![0, 1; 1, 0] := by decide

example : (Matrix.of (antiDiagonalSignGramMatrix ℤ 3)) = !![0, 0, 1; 0, -1, 0; 1, 0, 0] := by decide

example : staircaseExtensionIdeal (D := D) ⊤ 1 0 = D.host.AA * D.host.AAbar⁻¹ := by
  simp [staircaseExtensionIdeal, Ideal.pointwise_smul_def, Ideal.map_top]

example (V : HSp D) (x y : V.V) : (neg (neg V)).hT x y = V.hT x y := by simp [neg_hT]

end GlobalTheory.Grid

end
