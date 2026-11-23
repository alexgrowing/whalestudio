import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPins
import Formalism.LocalToGlobal.ProjectiveLattices.SpMapAlgHomId
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.HalfGeometricCovers
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SignatureEmbeddingCoverComp
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NotIsOfFinOrderUnitQuot
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.XiZeroImPos
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RationalPointsAdelicUnitaryEqUnitary
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CompletedLatticeEqAdelicCompletionAndGram
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SecBCAndCuspBC
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.UnimodularStandardLattice

set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSectionVars false

noncomputable section

namespace GlobalTheory.ClassTieCompare

open Formalism.L2.Pj NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.ComplexResidueRing GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDeterminantRoot GlobalTheory.IndefiniteRowSideFullHecke.HalfGeometricCovers
open GlobalTheory.XiDetCompare (Reads TrivRat TrivFix XiValC XiValAtC embOf Reaches)
open Formalism.L2.PjFree (Unf.ofPj)
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Scalar

variable {D : D7} (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) {n : ℕ}

def IsDetOf (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (𝔠 : Ideal (𝓞 D.host.E)) : Prop :=
  𝔠 ⊔ barI H 𝔠 = ⊤ ∧ Submodule.span (𝓞 D.host.E) (detSet L) * idlE (barI H 𝔠) = idlE 𝔠

def GenOff (bad : ℕ) (𝔠 : Ideal (𝓞 D.host.E)) (x : (AE D)ˣ) : Prop :=
  infPart D (x : AE D) = 1 ∧ Generates ((finU D x : IdF D) : AdE D.host.F D.host.E) 𝔠 ∧
    ((finU D x : IdF D) : AdE D.host.F D.host.E) - 1 ∈ idHat D.host.F (Ideal.span {(bad : 𝓞 D.host.E)})

def HasDet (bad : ℕ) (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Prop :=
  ∃ 𝔠 x, IsDetOf H L 𝔠 ∧ GenOff bad 𝔠 x

def ReadsId {K : IntermediateField ℚ ℂ} (χ : (AE D)ˣ →* Circle) (bad : ℕ) (B : Ideal (𝓞 D.host.E) → K) : Prop :=
  ∀ 𝔠 x, GenOff bad 𝔠 x → ((B 𝔠 : K) : ℂ) = ((χ x : Circle) : ℂ) * ((Real.sqrt (Ideal.absNorm 𝔠 : ℝ) : ℝ) : ℂ)

def SquareLaw (n bad r : ℕ) : Prop :=
  ∀ (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (𝔠 : Ideal (𝓞 D.host.E)), GlobalTheory.ClassScalarCompare.Guard H bad L →
    IsDetOf H L 𝔠 → ∃ q : ℚ, 0 < q ∧
      q ^ 2 * (((L ⊓ stdLat D.host.E n).toAddSubgroup.addSubgroupOf L.toAddSubgroup).index : ℚ) ^ r = (Ideal.absNorm 𝔠 : ℚ)

variable {H} {Dw : Datum H} {l : Level H} {c : Coeff l}

theorem isDetOf_unique {L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {a b : Ideal (𝓞 D.host.E)} (ha : IsDetOf H L a)
    (hb : IsDetOf H L b) : a = b := by
  have e : idlE (a * barI H b) = idlE (b * barI H a) := by
    have m : ∀ I J : Ideal (𝓞 D.host.E), idlE (I * J) = idlE I * idlE J := fun I J =>
      Submodule.map_mul I J (Algebra.ofId (𝓞 D.host.E) D.host.E)
    rw [m, m, ← ha.2]
    conv_rhs => rw [← hb.2]
    ring
  have e' : a * barI H b = b * barI H a :=
    Submodule.map_injective_of_injective (f := Algebra.linearMap (𝓞 D.host.E) D.host.E)
      (FaithfulSMul.algebraMap_injective (𝓞 D.host.E) D.host.E) e
  exact le_antisymm
    (Ideal.le_of_dvd ((Ideal.isCoprime_iff_sup_eq.2 hb.1).dvd_of_dvd_mul_right ⟨_, e'⟩))
    (Ideal.le_of_dvd ((Ideal.isCoprime_iff_sup_eq.2 ha.1).dvd_of_dvd_mul_right ⟨_, e'.symm⟩))

theorem exists_epIs_iff (bad : ℕ) (B : Ideal (𝓞 D.host.E) → c.F) :
    (∃ epF : Submodule (𝓞 D.host.E) (Fin n → D.host.E) → c.F, EpIs (Dw := Dw) c bad B epF) ↔
      SquareLaw H n bad (Dw.p + Dw.q) := by
  classical
  constructor
  · rintro ⟨epF, h⟩ L 𝔠 g h1
    obtain ⟨q, q0, q1, -⟩ := h L 𝔠 g.1 g.2.1 g.2.2 h1.1 h1.2
    exact ⟨q, q0, q1⟩
  · intro h
    have key : ∀ L : Submodule (𝓞 D.host.E) (Fin n → D.host.E), ∃ v : c.F, ∀ 𝔠, GlobalTheory.ClassScalarCompare.Guard H bad L →
        IsDetOf H L 𝔠 → ∃ q : ℚ, 0 < q ∧
          q ^ 2 * (((L ⊓ stdLat D.host.E n).toAddSubgroup.addSubgroupOf L.toAddSubgroup).index : ℚ) ^ (Dw.p + Dw.q) =
            (Ideal.absNorm 𝔠 : ℚ) ∧ v = (B 𝔠)⁻¹ * (q : c.F) := by
      intro L
      by_cases hL : ∃ 𝔠, GlobalTheory.ClassScalarCompare.Guard H bad L ∧ IsDetOf H L 𝔠
      · obtain ⟨𝔠, g, h1⟩ := hL
        obtain ⟨q, q0, q1⟩ := h L 𝔠 g h1
        refine ⟨(B 𝔠)⁻¹ * (q : c.F), fun 𝔠' _ h2 => ?_⟩
        obtain rfl := isDetOf_unique h1 h2
        exact ⟨q, q0, q1, rfl⟩
      · exact ⟨0, fun 𝔠 g h1 => absurd ⟨𝔠, g, h1⟩ hL⟩
    choose epF hepF using key
    exact ⟨epF, fun L 𝔠 g1 g2 g3 h1 h2 => hepF L 𝔠 ⟨g1, g2, g3⟩ ⟨h1, h2⟩⟩

theorem DefinedMod.of_dvd {χ : (AE D)ˣ →* Circle} {m m' : ℕ} (h : DefinedMod χ m) (hd : m ∣ m') : DefinedMod χ m' := by
  intro x hx h1
  refine h x hx (AddSubgroup.closure_mono ?_ h1)
  rintro _ ⟨a, ha, o, ho, rfl⟩
  exact ⟨a, ha, o, Ideal.span_singleton_le_span_singleton.2 (Nat.cast_dvd_cast hd) ho, rfl⟩

end Scalar

section Value

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {n r : ℕ}
variable (V : HSp D) (hr : V.rank = r)

def iotaV (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)) : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E) :=
  LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ ι

def finR : GA D V →* GL (Fin r) (AdE D.host.F D.host.E) :=
  (Units.map (Matrix.reindexRingEquiv (AdE D.host.F D.host.E) (finCongr hr)).toMonoidHom).comp (finHom V)

def gramR : Matrix (Fin r) (Fin r) D.host.E := -(Matrix.reindex (finCongr hr) (finCongr hr) V.gram).transpose

section One

variable {c : Coeff l} {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (dict : GA D V → Σ k, Frame (U.X k).Ψ r)
  (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)

def DictWith (Q : ∀ (g : ℕ) (lab : Fin g → D.host.E →+* ℂ)
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) lab) (ik : U.Comp → Fin F.n),
    (∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ) → Prop) : Prop :=
  IsUnf U ∧ (∀ k, ModelW V hr (U.X k)) ∧
    ∃ (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
      (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
      (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ)
      (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)),
      (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧ DictLat U V hr dict (iotaV V hr ι) e F ik φ th x₀ ∧ Q g _ F ik φ

def IsDict : Prop := DictWith V hr U dict ι x₀ fun _ _ _ _ _ => True

def ValDict (c0 : ℂ) (xi : (AdE D.host.F D.host.E)ˣ →* ℂˣ) (f : Rul Xo c) : Prop :=
  DictWith V hr U dict ι x₀ fun _ _ F ik φ => ∀ h γ : GA D V, MarkBy U V hr dict (iotaV V hr ι) F ik φ h γ →
    rdU U f (dict h).1 (dict h).2 = c0 * ((xi (Matrix.GeneralLinearGroup.det (finHom V (γ * h))) : ℂˣ) : ℂ)

def Onto : Prop :=
  (∀ h, (dict h).2 ∈ (U.X (dict h).1).dom) ∧ (∀ k, ∃ h, (dict h).1 = k) ∧
  ∀ (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ)
    (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)),
    (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) → DictLat U V hr dict (iotaV V hr ι) e F ik φ th x₀ →
      Function.Bijective ik ∧ ∀ ψ, (∀ k, ψ (ik k) = embOf (Unf.ofPj U) F ik φ k) →
        Reaches (finR V hr) (Unf.ofPj U) dict F ik ψ (gramR V hr) ι

def FamFree (σ : c.F →+* ℂ) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)) (ξ : IdF D →* Circle) (f : Rul Xo c) : Prop :=
  ∀ c0 : ℂ, XiValC Xo c c0 (gramR V hr) (-D.host.xi0) ι ξ σ f →
    ∀ (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
      (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
      (ψ : ∀ i, (F.Di i).La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)),
      AllMarked D.host.F (gramR V hr) (-D.host.xi0) ι F ψ → XiValAtC c0 (gramR V hr) ι ξ σ F ψ f

variable {V hr U dict ι x₀} {c0 : ℂ} {xi : (AdE D.host.F D.host.E)ˣ →* ℂˣ} {ξ : IdF D →* Circle} {f : Rul Xo c}

end One

section Diag

variable {V} {c : Coeff l} {σ : c.F →+* ℂ} {U : Unf Xo c σ V.rank} {dict : GA D V → Σ k, Frame (U.X k).Ψ V.rank}
  {ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)} {x₀ : (D.host.E →+* ℂ) → Matrix (Fin V.rank) (Fin V.rank) ℂ}
  {g : ℕ}

end Diag

section Compare

variable {V hr} {c : Coeff l} {σ : c.F →+* ℂ} {U : Unf Xo c σ r} {dict : GA D V → Σ k, Frame (U.X k).Ψ r}
  {ι : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)} {x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ}
  {c0 : ℂ} {xi : (AdE D.host.F D.host.E)ˣ →* ℂˣ} {ξ : IdF D →* Circle} {f : Rul Xo c}

end Compare

theorem cXiVal_iff {c : Coeff l} (σ0 : c.F →+* ℂ) {Tup : Type} (d : Tup → DeltaDat Xo c n)
    (U₂ : ∀ t, Unf (d t).Xo₂ (d t).c₂ (σ0.comp ((d t).eF.symm : (d t).c₂.F →+* c.F)) r)
    (dict₂ : ∀ t, GA D V → Σ k, Frame ((U₂ t).X k).Ψ r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (xi : Tup → (AdE D.host.F D.host.E)ˣ →* ℂˣ) :
    CXiVal V hr σ0 d U₂ dict₂ (iotaV V hr ι) x₀ xi ↔ ∃ c0 : ℂ, (∃ m : ℕ, 0 < m ∧ c0 ^ m = 1) ∧
      ∀ t, ValDict V hr (U₂ t) (dict₂ t) ι x₀ c0 (xi t) (d t).cδ := Iff.rfl

end Value

section Record

variable {D : D7} {T : CoreJ D} {X : ThetaX D} (Tt : ThetaTied D X) (j : ℕ) {c' : Coeff T.Q.l} (h : T.Q.c.F ≤ c'.F)
  (ka : WeightFamilies.Wt D j) (lam : D.what₂.Tau → DomWeight D.R.nV)
  (PQ : D.what₂.Tup → Ideal (𝓞 D.host.E)) (β : Fin D.R.r → (T.Q.Dw j).La)
  (Cl : D.what₂.Tup → Type) [∀ t, Fintype (Cl t)]
  (Lh : ∀ t, Cl t → Submodule (𝓞 D.host.E) (Fin D.R.nV → D.host.E)) (gam : ∀ t, Cl t → ℕ) (vol : D.what₂.Tup → c'.F)
  (thAd : ∀ t, (Cl t → VVc c' lam) → AutQ (T.V j (sig0 T.Q.c)) → ℂ) (Pl : ∀ t, (Cl t → VVc c' lam) → Prop) (ph : ℂ)
  (ξ : D.what₂.Tup → IdF D →* Circle) (bad : D.what₂.Tup → ℕ)
  (d : D.what₂.Tup → DeltaDat (T.Q.Xo j) c' D.R.nV)
  (φ : ∀ t, (Fin D.R.nV → LevQc (T.Q.Dw j) (d t).l₂) → c'.F)
  (w : ∀ t, Cl t → (Fin D.R.nV → LevQ (T.Q.Dw j) (d t).l₂) → c'.F)
  (La : ∀ t, Cl t → GenLat D.host.E D.R.nV) (Nc : ∀ t, Cl t → ℕ) (ep : ∀ t, Cl t → c'.F)
  (io : VVc c' lam →ₗ[c'.F] MvPolynomial (LtN (T.Q.Dw j) D.R.nV) c'.F)
  (hr : (T.V j (sig0 T.Q.c)).rank = D.R.r) (B : D.what₂.Tup → Ideal (𝓞 D.host.E) → c'.F)
  (epF : D.what₂.Tup → Submodule (𝓞 D.host.E) (Fin D.R.nV → D.host.E) → c'.F) (cond : ℕ) (hw : VVc c' lam)
  (U₂ : ∀ t, Unf (d t).Xo₂ (d t).c₂ ((sig0 c').comp ((d t).eF.symm : (d t).c₂.F →+* c'.F)) D.R.r)
  (dict₂ : ∀ t, GA D (T.V j (sig0 T.Q.c)) → Σ k, Frame ((U₂ t).X k).Ψ D.R.r)
  (xi : D.what₂.Tup → (AdE D.host.F D.host.E)ˣ →* ℂˣ)

def FirstAt : Prop :=
  OneMapTieP h (LLc D) (T.U j) (sig0 c') (T.V j (sig0 T.Q.c)) hr (T.dict j (sig0 T.Q.c)) (T.mu j (sig0 T.Q.c)) (xiR D) (wtA ka)
    (levAll (Dw := T.Q.Dw j) T.Q.l) d Cl bad Lh La Nc gam vol ep B epF (D.host.QS * D.host.q) D.host.d cond (DV.tauEmb D) lam io hw φ w
    U₂ dict₂ (iotaV _ hr (T.iota j)) (T.x₀ j (sig0 T.Q.c)) xi thAd Pl (T.cE j (sig0 T.Q.c)) ph

def Shared : Prop :=
  LLc D ≤ c'.F ∧ LevActLaws (T.Q.Xo j) T.Q.c (levAll (Dw := T.Q.Dw j) T.Q.l) ∧
    LevActLaws (T.Q.Xo j) c' (levAll (Dw := T.Q.Dw j) T.Q.l) ∧
    LevActExtends (T.Q.Xo j) (levAll (Dw := T.Q.Dw j) T.Q.l) h (wtA ka) D.R.nV ∧
    CuspBaseChange (T.Q.Xo j) h (unf T j) (wtA ka) D.R.nV ∧ CovPin (T.Q.Xo j) c' d ∧
    (∀ t, 2 ∣ bad t ∧ D.host.QS * D.host.q ∣ bad t ∧ D.host.d ∣ bad t) ∧ RepsCov (T.Q.Xo j) c' Cl d bad Lh La Nc gam ∧
    IoPin j ka lam io ∧ WPin (T.Q.Xo j) c' Cl d φ w ∧ GeoRow j h ka lam Cl gam vol thAd Pl ph d w La Nc ep io

def AllWeights : Prop :=
  (∀ b m, CuspBaseChange (T.Q.Xo j) h (unf T j) b m) ∧
    ∀ b m, LevActExtends (T.Q.Xo j) (levAll (Dw := T.Q.Dw j) T.Q.l) h b m

def Bound : Prop :=
  InR D j ∧ LawsJ T ∧ WeightPin j ka lam ∧ CharPin T Tt j ξ PQ ∧
    (∀ k, IsomEmb ((T.U j (sig0 T.Q.c)).X k).Gm ((T.U j (sig0 T.Q.c)).X k).ξ0 (T.Q.Dw j) (T.iota j)) ∧
    EquivPin j h (wtA ka) ∧
    (∀ t, (d t).I ≤ PQ t ∧ Squarefree (d t).pd ∧
      (∀ p : ℕ, p.Prime → p ∣ (d t).pd → Ideal.span {(p : 𝓞 D.host.E)} ⊔ PQ t ≠ ⊤) ∧ IsTwist (ξ t) (d t).pd) ∧
    (∀ t, bad t ≠ 0 ∧ DefinedMod (muRec Tt t j) (bad t)) ∧
    (∀ t, ClassesAt D.R.r T.Q.l.M (d t).l₂.M (bad t) (PQ t) (Lh t) (gam t) ∧ ∃ m : ℕ, 0 < m ∧ vol t = ((m : c'.F))⁻¹) ∧
    SpansMod (Mfr T.Q.l) β ∧ ∀ t, DatumVal T.Q.l (d t).l₂ (r_le_nV D) (ξ t) (PQ t) β (φ t)

def XiUpTo (c0 : ℂ) : Prop :=
  ∀ t, XiValC (d t).Xo₂ (d t).c₂ c0 (gramR _ hr) (-D.host.xi0) (T.iota j) (ξ t) (sig0 (d t).c₂) (d t).cδ

def Ties : Prop :=
  ∀ t, Reads (xi t) (ξ t) ∧ ReadsId (chiSplit Tt t j) (bad t) (B t) ∧
    Onto _ hr (U₂ t) (dict₂ t) (T.iota j) (T.x₀ j (sig0 T.Q.c))

def FirstOnly : Prop :=
  AllWeights j h ∧ (∀ t, cond ∣ bad t) ∧ (∀ t, EpIs (Dw := T.Q.Dw j) c' (bad t) (B t) (epF t) ∧ BAbs c' (B t)) ∧
    hwOK c' lam hw ∧ ∀ t, IsDict _ hr (U₂ t) (dict₂ t) (T.iota j) (T.x₀ j (sig0 T.Q.c))

def SecondOnly : Prop :=
  Bound Tt j h ka lam PQ β Cl Lh gam vol ξ bad d φ ∧ (∀ t k, HasDet T.Q.H (bad t) (Lh t k)) ∧
    ∀ t, rdU (U₂ t) (d t).cδ (dict₂ t 1).1 (dict₂ t 1).2 = 1

variable {Tt j h ka lam PQ β Cl Lh gam vol thAd Pl ph ξ bad d φ w La Nc ep io hr B epF cond hw U₂ dict₂ xi}

theorem laws_give (h1 : InR D j) (h2 : LawsJ T) : D.R.r = (T.Q.Dw j).p + (T.Q.Dw j).q ∧
    LatEmb (T.V j (sig0 T.Q.c)) (iotaV _ hr (T.iota j)) ∧ ∀ g, ∃ x, IsDetRoot (T.V j (sig0 T.Q.c)) g x := by
  obtain ⟨_, _, _, _, _, _, _, k, -⟩ := h2.adPin j h1 _ T.toCore.good_σ₀
  exact ⟨(h2.unf j h1 _ T.toCore.good_σ₀).1, k, (h2.muVal j h1 _ T.toCore.good_σ₀).1⟩

theorem Bound.nonempty (hB : Bound Tt j h ka lam PQ β Cl Lh gam vol ξ bad d φ) :
    Nonempty D.what₂.Tup ∧ ∀ t, Nonempty (Cl t) :=
  ⟨⟨D.what₂.mu0⟩, fun t => ((hB.2.2.2.2.2.2.2.2.1 t).1.1 (stdLat _ _) GlobalTheory.Survey.UnimodularStandardLattice.unimod_std
    (GlobalTheory.Survey.UnimodularStandardLattice.trivAt_std _) (GlobalTheory.Survey.UnimodularStandardLattice.trivAt_std _)).exists.elim fun k _ => ⟨k⟩⟩

variable (Tt j h ka lam PQ β Cl Lh gam vol thAd Pl ph ξ bad d φ w La Nc ep io hr B epF cond hw U₂ dict₂ xi)

end Record

end GlobalTheory.ClassTieCompare
