import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Formalism.LocalToGlobal.JointCharacters.LocEMulLocE
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IntegralTransport
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.WeilIdempotents

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.MainNotions.KudlaSiegelWeil (Pl FinF FinE FF Over Split LocW Restr IntV)
open GlobalTheory.IndefiniteRowSideFullHecke.SymplecticTensorMeasures (ConjIsom basConj omTens toHom)
open Formalism.IndefR.Datum (IsHalf IsLatVac)
open scoped TensorProduct Classical

namespace GlobalTheory.LocWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def idem (D : D7) : Pl D → AE D
  | .inl v => GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices.idemFin D v
  | .inr τ => GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices.idemInf D (InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E)))

theorem idem_mul_self (v : Pl D) : idem D v * idem D v = idem D v := by
  rcases v with v | τ
  · simp only [idem, GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices.idemFin]
    rw [← map_mul]
    congr 1
    refine Prod.ext (mul_zero _) ?_
    change singleV D.host.F v 1 * singleV D.host.F v 1 = singleV D.host.F v 1
    refine DFunLike.ext _ _ fun u => ?_
    change evalV D.host.F u (singleV D.host.F v 1 * singleV D.host.F v 1) = evalV D.host.F u (singleV D.host.F v 1)
    rw [map_mul]
    by_cases h : u = v
    · subst h
      have : evalV D.host.F u (singleV D.host.F u 1) = 1 := RestrictedProduct.single_eq_same
        (fun w : HeightOneSpectrum (𝓞 D.host.F) => w.adicCompletionIntegers D.host.F) u 1
      rw [this, mul_one]
    · have : evalV D.host.F u (singleV D.host.F v 1) = 0 := RestrictedProduct.single_eq_of_ne
        (fun w : HeightOneSpectrum (𝓞 D.host.F) => w.adicCompletionIntegers D.host.F) 1 h
      rw [this, mul_zero]
  · simp only [idem, GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices.idemInf]
    rw [← map_mul]
    congr 1
    refine Prod.ext ?_ (mul_zero _)
    exact (Pi.single_mul (α := fun w : InfinitePlace D.host.F => w.Completion) _ 1 1).symm.trans (by rw [mul_one]; rfl)

theorem cA_algebraMap (a : AF D.host.F) : cA D (algebraMap (AF D.host.F) (AE D) a) = algebraMap (AF D.host.F) (AE D) a := by
  simp [cA, sigR, Algebra.TensorProduct.algebraMap_apply]

theorem cA_idem (v : Pl D) : cA D (idem D v) = idem D v := by
  rcases v with v | τ <;> exact cA_algebraMap _

def cutGL {R : Type} [CommRing R] {n : ℕ} {e : R} (he : e * e = e) : GL (Fin n) R →* GL (Fin n) R :=
  let f : Matrix (Fin n) (Fin n) R →* Matrix (Fin n) (Fin n) R :=
    { toFun := fun g => e • g + (1 - e) • (1 : Matrix (Fin n) (Fin n) R)
      map_one' := by rw [← add_smul]; simp
      map_mul' := fun g h => by
        have h1 : e * (1 - e) = 0 := by rw [mul_sub, he, mul_one, sub_self]
        have h2 : (1 - e) * (1 - e) = 1 - e := by rw [sub_mul, one_mul, h1, sub_zero]
        simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_one,
          Matrix.one_mul, he, h1, h2, mul_comm (1 - e) e, zero_smul, add_zero, zero_add, smul_add] }
  Units.map f

theorem cutGL_val {R : Type} [CommRing R] {n : ℕ} {e : R} (he : e * e = e) (g : GL (Fin n) R) :
    (cutGL he g).val = e • g.val + (1 - e) • (1 : Matrix (Fin n) (Fin n) R) := rfl

theorem cutGL_mem {R : Type} [CommRing R] {n : ℕ} {e : R} (he : e * e = e) (c : R →+* R) (hc : c e = e)
    (J : Matrix (Fin n) (Fin n) R) {g : GL (Fin n) R} (hg : g ∈ Formalism.UG.UJ c J) : cutGL he g ∈ Formalism.UG.UJ c J := by
  have hg' : Formalism.UG.cT c g.val * J * g.val = J := hg
  show Formalism.UG.cT c (cutGL he g).val * J * (cutGL he g).val = J
  have h1 : e * (1 - e) = 0 := by rw [mul_sub, he, mul_one, sub_self]
  have h2 : (1 - e) * (1 - e) = 1 - e := by rw [sub_mul, one_mul, h1, sub_zero]
  have e1 : Formalism.UG.cT c (cutGL he g).val = e • Formalism.UG.cT c g.val + (1 - e) • (1 : Matrix (Fin n) (Fin n) R) := by
    ext i j
    simp only [cutGL_val, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, map_add, map_mul, map_sub, map_one, hc, Matrix.one_apply, eq_comm (a := j)]
    split_ifs <;> simp
  rw [e1, cutGL_val]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_one,
    Matrix.one_mul, he, h1, h2, mul_comm (1 - e) e, zero_smul, add_zero, zero_add, smul_add, hg']
  rw [← add_smul]; simp

def comp (V : HSp D) (v : Pl D) : GA D V →* GA D V :=
  ((cutGL (idem_mul_self v)).comp (matHom V)).codRestrict (HR (AF D.host.F) D.sp.cm.sig V.gram) fun g =>
    cutGL_mem (idem_mul_self v) (cA D) (cA_idem v) _ g.2

theorem mt_comp (V : HSp D) (v : Pl D) (g : GA D V) :
    mt V (comp V v g) = idem D v • mt V g + (1 - idem D v) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := rfl

def GAt (V : HSp D) (v : Pl D) : Subgroup (GA D V) := (comp V v).range

def Gk (θ : InfF D) (V : HSp D) (A : CptF V) : Subgroup (GA D V) :=
  GfC V ⊔ Subgroup.closure {k | V.SigOK ∧ IsKinf θ V A k}

def KAt (θ : InfF D) (V : HSp D) (A : CptF V) (τ : D.what₂.Tau) : Subgroup (GA D V) := (Gk θ V A).map (comp V (.inr τ))

def OneP (V : HSp D) (τ : D.what₂.Tau) : Type :=
  {γ : Multiplicative ℝ →* GA D V // Continuous γ ∧ ∀ t, γ t ∈ GAt V (.inr τ)}

def OneP.triv (V : HSp D) (τ : D.what₂.Tau) : OneP V τ := ⟨1, continuous_const, fun _ => one_mem _⟩

def OneP.at {V : HSp D} {τ : D.what₂.Tau} (γ : OneP V τ) (t : ℝ) : GA D V := γ.1 (Multiplicative.ofAdd t)

abbrev HAlg (θ : InfF D) (V : HSp D) (A : CptF V) (τ : D.what₂.Tau) : Type :=
  MonoidAlgebra ℂ (Monoid.Coprod (KAt θ V A τ) (FreeMonoid (OneP V τ)))

def ofK (θ : InfF D) (V : HSp D) (A : CptF V) (τ : D.what₂.Tau) : KAt θ V A τ →* HAlg θ V A τ :=
  (MonoidAlgebra.of ℂ _).comp Monoid.Coprod.inl

def ofLie (θ : InfF D) (V : HSp D) (A : CptF V) (τ : D.what₂.Tau) (γ : OneP V τ) : HAlg θ V A τ :=
  MonoidAlgebra.of ℂ _ (Monoid.Coprod.inr (FreeMonoid.of γ))

def Hloc (θ : InfF D) (V : HSp D) (A : CptF V) : Pl D → Type
  | .inl v => GAt V (.inl v)
  | .inr τ => HAlg θ V A τ

instance (θ : InfF D) (V : HSp D) (A : CptF V) : ∀ v, Monoid (Hloc θ V A v)
  | .inl v => inferInstanceAs (Monoid (GAt V (.inl v)))
  | .inr τ => inferInstanceAs (Monoid (HAlg θ V A τ))

def aug (θ : InfF D) (V : HSp D) (A : CptF V) : ∀ v, Hloc θ V A v →* ℂ
  | .inl _ => 1
  | .inr τ => (MonoidAlgebra.lift ℂ ℂ (Monoid.Coprod (KAt θ V A τ) (FreeMonoid (OneP V τ)))
      (Monoid.Coprod.lift 1 (FreeMonoid.lift fun _ => 0))).toMonoidHom

def loc (θ : InfF D) (V : HSp D) (A : CptF V) : ∀ v, Gk θ V A →* Hloc θ V A v
  | .inl v => (comp V (.inl v)).rangeRestrict.comp (Gk θ V A).subtype
  | .inr τ => (ofK θ V A τ).comp ((comp V (.inr τ)).subgroupMap (Gk θ V A))

def IsEvalAt (D : D7) (v : FinF D) (w : FinE D) (φ : AE D →+* v.adicCompletion (FF D)) : Prop :=
  (∀ a, φ (algebraMap (AF D.host.F) (AE D) a) = evalV D.host.F v (sndA D.host.F a)) ∧
    ∀ x : 𝓞 D.host.E, Valued.v (φ (incA D (x : D.host.E))) < 1 ↔ x ∈ w.asIdeal

structure SplitFrames (D : D7) where
  ev : ∀ (v : FinF D) (w : FinE D), Split D v → Over D w v → (AE D →+* v.adicCompletion (FF D))
  ev_spec : ∀ v w hv hw, IsEvalAt D v w (ev v w hv hw)
  ev_conj : ∀ v w w' hv hw hw', w' ≠ w → ∀ x, ev v w' hv hw' x = ev v w hv hw (cA D x)
  sc : ∀ (v : FinF D) (w : FinE D), Split D v → Over D w v → (v.adicCompletion (FF D))ˣ
  sc_spec : ∀ v w hv hw x, IntV v 0 (((sc v w hv hw)⁻¹ : (v.adicCompletion (FF D))ˣ) * x) ↔
    x ∈ Submodule.span (v.adicCompletionIntegers (FF D)) {y | ∃ a ∈ D.host.AA, y = ev v w hv hw (incA D a)}
  fr : ∀ (V : HSp D) (v : FinF D) (w : FinE D), Split D v → Over D w v → GL (Fin V.rank) (v.adicCompletion (FF D))
  fr_spec : ∀ V v w hv hw y, (∀ i, IntV v 0 (((fr V v w hv hw)⁻¹).val.mulVec y i)) ↔
    y ∈ Submodule.span (v.adicCompletionIntegers (FF D)) {z | ∃ x ∈ L0c D V, z = fun i => ev v w hv hw (incA D (x i))}
  fr_dual : ∀ V v w w' hv hw hw', w' ≠ w →
    (fr V v w' hv hw').valᵀ * V.gram.map (fun a => ev v w hv hw (incA D a)) * (fr V v w hv hw).val = 1

def SplitFrames.gl (Fr : SplitFrames D) (V : HSp D) (v : FinF D) (w : FinE D) (hw : Over D w v) :
    GAt V (.inl v) →* GL (Fin V.rank) (v.adicCompletion (FF D)) :=
  if hv : Split D v then
    (MulAut.conj (Fr.fr V v w hv hw)⁻¹).toMonoidHom.comp
      ((Matrix.GeneralLinearGroup.map (Fr.ev v w hv hw)).comp ((matHom V).comp (GAt V (.inl v)).subtype))
  else 1

def SplitFrames.coord (Fr : SplitFrames D) (V W : HSp D) (v : FinF D) (w : FinE D) (hv : Split D v) (hw : Over D w v)
    (y : WA V W) : Matrix (Fin V.rank) (Fin W.rank) (v.adicCompletion (FF D)) :=
  (((Fr.sc v w hv hw)⁻¹ : (v.adicCompletion (FF D))ˣ) : v.adicCompletion (FF D)) •
    (((Fr.fr V v w hv hw)⁻¹).val * y.map (Fr.ev v w hv hw) * ((Fr.fr W v w hv hw)⁻¹).valᵀ)

def SplitFrames.AtPl (Fr : SplitFrames D) {V W : HSp D} (v : FinF D) (w : FinE D) (hv : Split D v) (hw : Over D w v)
    (y : WA V W) : Prop :=
  IsHalf (idem D (.inl v)) y ∧ y.map (fun a => Fr.ev v w hv hw (cA D a)) = 0

def SplitFrames.AtConj (Fr : SplitFrames D) {V W : HSp D} (v : FinF D) (w : FinE D) (hv : Split D v) (hw : Over D w v)
    (y : WA V W) : Prop :=
  IsHalf (idem D (.inl v)) y ∧ y.map (Fr.ev v w hv hw) = 0

def IsLocEmb (D : D7) (j : ∀ w : FinE D, (w.adicCompletion D.host.E)ˣ →* (AE D)ˣ) : Prop :=
  ∀ w, Continuous (j w) ∧ AllSome (fun e => Formalism.L2.JoinChr.IsPlIdem D e w) fun e => ∀ k : D.host.Eˣ,
    (j w (Units.map (algebraMap D.host.E (w.adicCompletion D.host.E)).toMonoidHom k) : AE D) =
      Formalism.L2.JoinChr.locE D e (k : D.host.E)

variable {X : ThetaX D} {T : ThetaTied D X}

def orbit {M : Type} [AddCommGroup M] [Module ℂ M] (A : Subalgebra ℂ (Module.End ℂ M)) (f : M) : Submodule ℂ M :=
  (Subalgebra.toSubmodule A).map (LinearMap.applyₗ f)

theorem mem_orbit {M : Type} [AddCommGroup M] [Module ℂ M] {A : Subalgebra ℂ (Module.End ℂ M)} {f x : M} :
    x ∈ orbit A f ↔ ∃ a ∈ A, a f = x := Iff.rfl

def heisAlg (Wl : WeilTied D X T) (V W : HSp D) : Pl D → Subalgebra ℂ (Module.End ℂ (X.Sch V W))
  | .inl v => Algebra.adjoin ℂ {A | ∃ u : WA V W, IsHalf (idem D (.inl v)) u ∧
      ∀ Φ, Wl.evS V W (A Φ) = Heisenberg₂ Wl.ψ V W u (Wl.evS V W Φ)}
  | .inr τ => Algebra.adjoin ℂ {A | ∃ L : ℝ →+ WA V W, IsRealDir V W L ∧ (∀ t, IsHalf (idem D (.inr τ)) (L t)) ∧
      ∀ Φ, Wl.evS V W (A Φ) = dRho Wl.ψ V W L (Wl.evS V W Φ)}

def latTens {V W : HSp D} (s : ConjIsom V) (t : ConjIsom W) : AddSubgroup (WA V W) :=
  AddSubgroup.closure {u | ∃ α ∈ intAf D.host.F, ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ x ∈ L0c D V, ∃ y ∈ L0c D W,
    u = toHom s t (Matrix.of fun i j => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * x i * y j))}

def IsCompatibleHSpPair (V W : HSp D) : Prop := V.rank ≠ W.rank ∧ V.SigOK ∧ W.SigOK

def omB {Wl : WeilTied D X T} (K : KfinTied Wl) {V W : HSp D} (hp : IsCompatibleHSpPair V W) (χ χ' : X.Chr) :
    GA D V × GA D W →* Module.End ℂ (X.Sch V W) :=
  omTens Wl (basConj K V hp.2.1) (basConj K W hp.2.2) χ χ'

def homB {Wl : WeilTied D X T} (K : KfinTied Wl) {V W : HSp D} (hp : IsCompatibleHSpPair V W) (y : WA V W) : WA V W :=
  toHom (basConj K V hp.2.1) (basConj K W hp.2.2) y

def Splitting (T : ThetaTied D X) (V W : HSp D) (χ χ' : X.Chr) : Prop :=
  ResEta D (T.eChr χ) V.rank ∧ ResEta D (T.eChr χ') W.rank

def IsVac {Wl : WeilTied D X T} (K : KfinTied Wl) (θ : InfF D) {V W : HSp D} (hp : IsCompatibleHSpPair V W) (f : X.Sch V W) : Prop :=
  f ≠ 0 ∧ IsLatVac (Heisenberg₂ Wl.ψ V W) (latTens (basConj K V hp.2.1) (basConj K W hp.2.2)) (Wl.evS V W f) ∧
    ∃ J, IsFockCx θ V W (K.cpt V) (K.cpt W) J ∧ ∀ L, IsRealDir V W L → annOp Wl.ψ V W J L (Wl.evS V W f) = 0

def IsDerOn (Wl : WeilTied D X T) {V W : HSp D} (N : Submodule ℂ (X.Sch V W)) (p : ℝ → Module.End ℂ (X.Sch V W))
    (A : Module.End ℂ (X.Sch V W)) : Prop :=
  ∀ Φ ∈ N, ∀ w, HasDerivAt (fun t => Wl.evS V W (p t Φ) w) (Wl.evS V W (A Φ) w) 0

structure IsLinModel {Wl : WeilTied D X T} (K : KfinTied Wl) (Fr : SplitFrames D) {V W : HSp D} (hp : IsCompatibleHSpPair V W)
    (v : FinF D) (w : FinE D) (hv : Split D v) (hw : Over D w v) (N : Submodule ℂ (X.Sch V W)) (f : X.Sch V W)
    (M : X.Sch V W → Matrix (Fin V.rank) (Fin W.rank) (v.adicCompletion (FF D)) → ℂ) : Prop where
  vac : ∀ Xm, M f Xm = if ∀ i j, IntV v 0 (Xm i j) then 1 else 0
  trans : ∀ y, Fr.AtPl v w hv hw y → ∀ Φ ∈ N, ∀ Φ', Wl.evS V W Φ' = Heisenberg₂ Wl.ψ V W (homB K hp y) (Wl.evS V W Φ) →
    ∀ Xm, M Φ' Xm = M Φ (Xm + Fr.coord V W v w hv hw y)
  modul : ∀ y, Fr.AtConj v w hv hw y → ∀ Φ ∈ N, ∀ Φ', Wl.evS V W Φ' = Heisenberg₂ Wl.ψ V W (homB K hp y) (Wl.evS V W Φ) →
    ∀ u, Fr.AtPl v w hv hw u → M Φ' (Fr.coord V W v w hv hw u) =
      Wl.ψ (sympl V W (homB K hp u) (homB K hp y)) * M Φ (Fr.coord V W v w hv hw u)

structure PairData {Wl : WeilTied D X T} (K : KfinTied Wl) (θ : InfF D) (Fr : SplitFrames D) (V W : HSp D)
    (om : X.Chr → X.Chr → (GA D V × GA D W →* Module.End ℂ (X.Sch V W))) : Type 1 where
  S : Pl D → Type
  [sA : ∀ v, AddCommGroup (S v)]
  [sM : ∀ v, Module ℂ (S v)]
  omL : X.Chr → X.Chr → ∀ v, Representation ℂ (Hloc θ V (K.cpt V) v × Hloc θ W (K.cpt W) v) (S v)
  vac : ∀ v, S v
  pure : (∀ v, S v) → X.Sch V W
  pure_span : Submodule.span ℂ {Φ | ∃ φ, Restr vac φ ∧ Φ = pure φ} = X.kfin V W
  pure_om : ∀ χ χ', Splitting T V W χ χ' → ∀ (g : Gk θ V (K.cpt V)) (h : Gk θ W (K.cpt W)) φ, Restr vac φ →
    om χ χ' ((g : GA D V), (h : GA D W)) (pure φ) = pure fun v => omL χ χ' v (loc θ V _ v g, loc θ W _ v h) (φ v)
  pure_mlin : ∀ φ v (c : ℂ) (x y : S v), Restr vac φ →
    pure (Function.update φ v (c • x + y)) = c • pure (Function.update φ v x) + pure (Function.update φ v y)
  linM : ∀ (v : FinF D) (w : FinE D), Over D w v →
    S (.inl v) →ₗ[ℂ] (Matrix (Fin V.rank) (Fin W.rank) (v.adicCompletion (FF D)) → ℂ)
  linM_inj : ∀ v w (hw : Over D w v), Split D v → Function.Injective (linM v w hw)
  linM_eq : ∀ χ χ' v w (hw : Over D w v), Splitting T V W χ χ' → Split D v →
    ∀ g k : _, ∃ c : ℂ, c ≠ 0 ∧ ∀ φ, linM v w hw (omL χ χ' (.inl v) (g, k) φ) = c • fun Xm =>
      linM v w hw φ (Units.val (Fr.gl V v w hw g)⁻¹ * Xm * (Units.val (Fr.gl W v w hw k)⁻¹).transpose)

attribute [instance] PairData.sA PairData.sM

structure PairTrue {Wl : WeilTied D X T} (K : KfinTied Wl) (θ : InfF D) (Fr : SplitFrames D) {V W : HSp D} (hp : IsCompatibleHSpPair V W)
    (S : Pl D → Type) [∀ v, AddCommGroup (S v)] [∀ v, Module ℂ (S v)] (vac : ∀ v, S v) (pure : (∀ v, S v) → X.Sch V W)
    (omL : X.Chr → X.Chr → ∀ v, Hloc θ V (K.cpt V) v × Hloc θ W (K.cpt W) v → Module.End ℂ (S v))
    (linM : ∀ (v : FinF D) (w : FinE D), Over D w v →
      S (.inl v) → Matrix (Fin V.rank) (Fin W.rank) (v.adicCompletion (FF D)) → ℂ) : Prop where

  vac_true : IsVac K θ hp (pure vac)

  emb_inj : ∀ v, Function.Injective fun x : S v => pure (Function.update vac v x)
  emb_range : ∀ v Φ, (∃ x : S v, pure (Function.update vac v x) = Φ) ↔ Φ ∈ orbit (heisAlg Wl V W v) (pure vac)

  heis_pure : ∀ φ, Restr vac φ → ∀ v, ∀ A ∈ heisAlg Wl V W v, ∀ x : S v,
    pure (Function.update vac v x) = A (pure (Function.update vac v (φ v))) → pure (Function.update φ v x) = A (pure φ)

  om_fin : ∀ χ χ', Splitting T V W χ χ' → ∀ (v : FinF D) (g : GAt V (.inl v)) (h : GAt W (.inl v)) (x : S (.inl v)),
    pure (Function.update vac (.inl v) (omL χ χ' (.inl v) (g, h) x)) =
      omB K hp χ χ' ((g : GA D V), (h : GA D W)) (pure (Function.update vac (.inl v) x))

  om_cpt : ∀ χ χ', Splitting T V W χ χ' → ∀ τ (k : KAt θ V (K.cpt V) τ) (k' : KAt θ W (K.cpt W) τ) (x : S (.inr τ)),
    pure (Function.update vac (.inr τ) (omL χ χ' (.inr τ) (ofK θ V _ τ k, ofK θ W _ τ k') x)) =
      omB K hp χ χ' ((k : GA D V), (k' : GA D W)) (pure (Function.update vac (.inr τ) x))

  om_lieV : ∀ χ χ', Splitting T V W χ χ' → ∀ τ (γ : OneP V τ) (x : S (.inr τ)) (w : WA V W),
    HasDerivAt (fun t => Wl.evS V W (omB K hp χ χ' (γ.at t, 1) (pure (Function.update vac (.inr τ) x))) w)
      (Wl.evS V W (pure (Function.update vac (.inr τ) (omL χ χ' (.inr τ) (ofLie θ V _ τ γ, 1) x))) w) 0
  om_lieW : ∀ χ χ', Splitting T V W χ χ' → ∀ τ (δ : OneP W τ) (x : S (.inr τ)) (w : WA V W),
    HasDerivAt (fun t => Wl.evS V W (omB K hp χ χ' (1, δ.at t) (pure (Function.update vac (.inr τ) x))) w)
      (Wl.evS V W (pure (Function.update vac (.inr τ) (omL χ χ' (.inr τ) (1, ofLie θ W _ τ δ) x))) w) 0

  om_linV : ∀ χ χ', Splitting T V W χ χ' → ∀ τ (c : ℂ) (a a' : HAlg θ V (K.cpt V) τ) (b : HAlg θ W (K.cpt W) τ),
    omL χ χ' (.inr τ) ((c • a + a' : HAlg θ V (K.cpt V) τ), b) = c • omL χ χ' (.inr τ) (a, b) + omL χ χ' (.inr τ) (a', b)
  om_linW : ∀ χ χ', Splitting T V W χ χ' → ∀ τ (c : ℂ) (a : HAlg θ V (K.cpt V) τ) (b b' : HAlg θ W (K.cpt W) τ),
    omL χ χ' (.inr τ) (a, (c • b + b' : HAlg θ W (K.cpt W) τ)) = c • omL χ χ' (.inr τ) (a, b) + omL χ χ' (.inr τ) (a, b')

  lin : ∀ v w (hv : Split D v) (hw : Over D w v), ∃ M, IsLinModel K Fr hp v w hv hw
      (orbit (heisAlg Wl V W (.inl v)) (pure vac)) (pure vac) M ∧
    ∀ x, linM v w hw x = M (pure (Function.update vac (.inl v) x))

structure LocalWeilCompatibility {Wl : WeilTied D X T} (K : KfinTied Wl) {L : LocW D X} (h : LocWTied D X T Wl L) where
  θ : InfF D
  θ_inf : IsInfFam θ

  j : ∀ w : FinE D, (w.adicCompletion D.host.E)ˣ →* (AE D)ˣ
  j_emb : IsLocEmb D j
  locChr : ∀ χ w u, ((L.locChr χ w u : ℂˣ) : ℂ) = (T.eChr χ (j w u) : Circle)
  unr : ∀ χ w, L.unr χ w ↔ ∀ u : (w.adicCompletion D.host.E)ˣ, Valued.v (u : w.adicCompletion D.host.E) = 1 → L.locChr χ w u = 1
  val : ∀ χ w, L.unr χ w → ∀ u : (w.adicCompletion D.host.E)ˣ,
    Valued.v (u : w.adicCompletion D.host.E) = WithZero.exp (-1 : ℤ) → L.val χ w = ((L.locChr χ w u : ℂˣ) : ℂ)
  gk : ∀ V g, g ∈ L.Gk V ↔ h.eG V g ∈ Gk θ V (K.cpt V)

  eH : ∀ V v, L.Hloc V v ≃* Hloc θ V (K.cpt V) v
  aug : ∀ V v x, L.aug V v x = aug θ V (K.cpt V) v (eH V v x)
  loc : ∀ V v (g : L.Gk V), eH V v (L.loc V v g) = loc θ V (K.cpt V) v ⟨h.eG V g, (gk V g).1 g.2⟩

  Fr : SplitFrames D
  glL : ∀ V v w hw g, L.glL V v w hw g = Fr.gl V v w hw (eH V (.inl v) g)
  pair : ∀ (V W : HSp D) (hp : IsCompatibleHSpPair V W), PairTrue K θ Fr hp (L.SchL V W) (L.vac V W) (L.pure V W)
    (fun χ χ' v p => L.omL V W χ χ' v ((eH V v).symm p.1, (eH W v).symm p.2)) fun v w hw => L.linM V W v w hw

def KfinOff (X : ThetaX D) : Prop := ∀ V W : HSp D, V.rank ≠ W.rank → ¬ (V.SigOK ∧ W.SigOK) → X.kfin V W = ⊥

end GlobalTheory.LocWeil

end
