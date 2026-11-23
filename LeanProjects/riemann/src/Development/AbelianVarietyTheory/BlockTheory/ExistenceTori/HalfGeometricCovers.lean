import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPinsRec
import Formalism.LocalToGlobal.ProjectiveLattices.IsLevMove
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
import Formalism.LocalRingCardinality.DataKap
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.ComplexResidueRing
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryDeterminantRoot

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.HalfGeometricCovers

open Formalism.L2.Pj NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory.IndefiniteRowSideFullHecke.ComplexResidueRing GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDeterminantRoot
open scoped TensorProduct

section Adeles

variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def idHat (𝔞 : Ideal (𝓞 E)) : AddSubgroup (AdE F E) :=
  AddSubgroup.closure {z | ∃ a, IsIntF F a ∧ ∃ o ∈ 𝔞, z = a ⊗ₜ ((o : 𝓞 E) : E)}

variable {F}

def IsIntUnit (y : (AdE F E)ˣ) : Prop :=
  (y : AdE F E) ∈ intAdE F E ∧ ((y⁻¹ : (AdE F E)ˣ) : AdE F E) ∈ intAdE F E

def TrivMod (ξ : (AdE F E)ˣ →* Circle) (𝔞 : Ideal (𝓞 E)) : Prop :=
  ∀ y : (AdE F E)ˣ, IsIntUnit y → (y : AdE F E) - 1 ∈ idHat F 𝔞 → ξ y = 1

def RamExactly (ξ : (AdE F E)ˣ →* Circle) (𝔣 : Ideal (𝓞 E)) : Prop :=
  𝔣 ≠ ⊥ ∧ TrivMod ξ 𝔣 ∧ ∀ P 𝔤 : Ideal (𝓞 E), P.IsPrime → 𝔣 = P * 𝔤 → ¬ TrivMod ξ 𝔤

example : RamExactly (1 : (AdE F E)ˣ →* Circle) ⊤ := by
  refine ⟨top_ne_bot, fun _ _ _ => rfl, fun P 𝔤 hP h _ => hP.ne_top ?_⟩
  exact top_le_iff.1 (h.le.trans Ideal.mul_le_left)

def Generates (x : AdE F E) (𝔠 : Ideal (𝓞 E)) : Prop :=
  ∀ y, y ∈ idHat F 𝔠 ↔ ∃ z ∈ intAdE F E, y = x * z

end Adeles

section Lattices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [IsCMField E] [Algebra F E]
variable {H : Host E} {Dw : Datum H} {r n : ℕ}

def barI (H : Host E) (𝔞 : Ideal (𝓞 E)) : Ideal (𝓞 E) := 𝔞.map (H.bar : 𝓞 E →+* 𝓞 E)

def SpansMod (𝔞 : Ideal (𝓞 E)) (β : Fin r → Dw.La) : Prop :=
  Submodule.span (𝓞 E) (Set.range β) ⊔ (𝔞 • ⊤ : Submodule (𝓞 E) Dw.La) = ⊤

def InSupp (hrn : r ≤ n) (𝔐 𝔔 : Ideal (𝓞 E)) (β βq : Fin r → Dw.La) (x : Fin n → Dw.La)
    (u : Matrix (Fin r) (Fin r) (𝓞 E)) : Prop :=
  (∀ b : Fin n, r ≤ b.val → x b ∈ ((𝔐 * 𝔔) • ⊤ : Submodule (𝓞 E) Dw.La)) ∧
  (∀ b : Fin r, x (Fin.castLE hrn b) - β b ∈ (𝔐 • ⊤ : Submodule (𝓞 E) Dw.La)) ∧
  (∀ b : Fin r, x (Fin.castLE hrn b) - ∑ a, u a b • βq a ∈ (𝔔 • ⊤ : Submodule (𝓞 E) Dw.La)) ∧
  Ideal.span {u.det} ⊔ 𝔔 = ⊤

def DatumVal (l l₂ : Level H) {K : IntermediateField ℚ ℂ} (hrn : r ≤ n) (ξ : (AdE F E)ˣ →* Circle) (PQ : Ideal (𝓞 E))
    (β : Fin r → Dw.La) (φ : (Fin n → LevQc Dw l₂) → K) : Prop :=
  ∃ βq : Fin r → Dw.La, SpansMod (barI H PQ) βq ∧ ∀ x : Fin n → LevQc Dw l₂,
    (∀ u, InSupp hrn (Mfr l) (barI H PQ) β βq (fun b => qRep (x b)) u →
      ∃ y : (AdE F E)ˣ, IsIntUnit y ∧ (y : AdE F E) - diagE F ((u.det : 𝓞 E) : E) ∈ idHat F (barI H PQ) ∧
        (y : AdE F E) - 1 ∈ idHat F PQ ∧ ((φ x : K) : ℂ) = ((ξ y : Circle) : ℂ)) ∧
    ((¬ ∃ u, InSupp hrn (Mfr l) (barI H PQ) β βq (fun b => qRep (x b)) u) → φ x = 0)

def InLevel (r M : ℕ) (PQ : Ideal (𝓞 E)) (γ : Matrix (Fin n) (Fin n) E) : Prop :=
  (γ.map cc).transpose * γ = 1 ∧ OneMod M γ ∧
    ∃ k : ℕ, Nat.Coprime k (Ideal.absNorm PQ) ∧ ∀ i b : Fin n, r ≤ i.val → b.val < r →
      ∃ o ∈ PQ, (k : E) * γ i b = ((o : 𝓞 E) : E)

def Carries (γ : Matrix (Fin n) (Fin n) E) (L L' : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  ∀ v, v ∈ L' ↔ ∃ u ∈ L, v = γ.mulVec u

def ClassesAt {Cl : Type} (r M M₂ bad : ℕ) (PQ : Ideal (𝓞 E)) (Lh : Cl → Submodule (𝓞 E) (Fin n → E)) (gam : Cl → ℕ) : Prop :=
  (∀ L : Submodule (𝓞 E) (Fin n → E), (⟨L⟩ : GenLat E n).Unimod → (⟨L⟩ : GenLat E n).TrivAt bad →
    (⟨L⟩ : GenLat E n).TrivAt M₂ → ∃! k, ∃ γ, InLevel r M PQ γ ∧ Carries γ (Lh k) L) ∧
  ∀ k, 0 < gam k ∧ gam k = Nat.card {γ : Matrix (Fin n) (Fin n) E // InLevel r M PQ γ ∧ Carries γ (Lh k) (Lh k)}

example (r M : ℕ) (PQ : Ideal (𝓞 E)) (L : Submodule (𝓞 E) (Fin n → E)) :
    InLevel r M PQ (1 : Matrix (Fin n) (Fin n) E) ∧ Carries 1 L L := by
  refine ⟨⟨?_, ⟨1, by simp, fun i j => ⟨0, by simp⟩⟩, 1, by simp, fun i b hi hb => ⟨0, zero_mem _, ?_⟩⟩, fun v => by simp⟩
  · rw [Matrix.map_one _ (by simp [cc]) (by simp [cc])]
    simp
  · have : i ≠ b := fun e => by subst e; omega
    simp [Matrix.one_apply_ne this]

end Lattices

section Record

variable {D : D7}

abbrev IdF (D : D7) : Type := (AdE D.host.F D.host.E)ˣ

def finU (D : D7) : (AE D)ˣ →* IdF D := Units.map (finPart D).toMonoidHom

def LLc (D : D7) : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ (Set.range D.what₂.embLL)

theorem r_le_nV (D : D7) : D.R.r ≤ D.R.nV := Nat.le_add_right _ _

def chiSplit {X : ThetaX D} (Tt : ThetaTied D X) (t : D.what₂.Tup) (j : ℕ) : (AE D)ˣ →* Circle :=
  Tt.eChr (X.chrOf t j * X.etaT⁻¹)

def EpVal (H : Host D.host.E) (χ : (AE D)ˣ →* Circle) (bad r : ℕ) {n : ℕ} (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (ep : ℂ) : Prop :=
  ∃ (𝔠 : Ideal (𝓞 D.host.E)) (x : (AE D)ˣ), 𝔠 ⊔ barI H 𝔠 = ⊤ ∧
    Submodule.span (𝓞 D.host.E) (detSet L) * idlE (barI H 𝔠) = idlE 𝔠 ∧
    infPart D (x : AE D) = 1 ∧ Generates ((finU D x : IdF D) : AdE D.host.F D.host.E) 𝔠 ∧
    ((finU D x : IdF D) : AdE D.host.F D.host.E) - 1 ∈ idHat D.host.F (Ideal.span {(bad : 𝓞 D.host.E)}) ∧
    ep = (((χ x)⁻¹ : Circle) : ℂ) *
      ((Real.sqrt ((((L ⊓ stdLat D.host.E n).toAddSubgroup.addSubgroupOf L.toAddSubgroup).index : ℝ) ^ r) : ℝ) : ℂ)⁻¹

def DefinedMod (χ : (AE D)ˣ →* Circle) (m : ℕ) : Prop :=
  ∀ x : (AE D)ˣ, FinUnit x →
    ((finU D x : IdF D) : AdE D.host.F D.host.E) - 1 ∈ idHat D.host.F (Ideal.span {(m : 𝓞 D.host.E)}) → χ x = 1

def WeightPin (j : ℕ) (ka : WeightFamilies.Wt D j) (lam : D.what₂.Tau → DomWeight D.R.nV) : Prop :=
  DV.KapDef D ∧ ka.n = D.R.nV ∧ (∀ τ i, (ka.aP τ i : ℤ) = D.what₂.kaBig j τ i) ∧
  (∀ τ i, (ka.aM τ i : ℤ) = -D.what₂.kaSmall j τ (Fin.rev i)) ∧
  ∀ (j' : Fin D.R.m), j'.1 + 1 = j → ∀ τ (i : Fin D.R.nV),
    (((lam τ).w i : ℤ) : ℚ) = (ext0 (ka.aP τ) i.1 : ℚ) - (ext0 (ka.aM τ) (Fin.rev i).1 : ℚ) +
      ((((D.R.sigW j).1 : ℚ) - ((D.R.sigW j).2 : ℚ)) / 2 - (D.hc τ).e j' - 1 / 2)

variable (T : CoreJ D) {X : ThetaX D} (Tt : ThetaTied D X) (j : ℕ)

abbrev unf : ∀ σ : T.Q.c.F →+* ℂ, Formalism.L2.PjFree.Unf (T.Q.Xo j) T.Q.c σ D.R.r := fun σ =>
  { Comp := (T.U j σ).Comp, fin := (T.U j σ).fin, X := (T.U j σ).X, un := (T.U j σ).un }

abbrev LevGrp : Type := LaMod (T.Q.Dw j) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw j) T.Q.l

def CharPin (ξ : D.what₂.Tup → IdF D →* Circle) (PQ : D.what₂.Tup → Ideal (𝓞 D.host.E)) : Prop :=
  T.chiW j T.σ₀ = muRec0 Tt j ∧
  ∀ t, (∀ x, muRec Tt t j x = muRec0 Tt j x * ξ t (finU D x)) ∧ (PQ t).IsRadical ∧
    RamExactly (ξ t) (PQ t * barI T.Q.H (PQ t))

variable {T} {c' : Coeff T.Q.l} (h : T.Q.c.F ≤ c'.F)

def IsPinnedCover₂ (d : D.what₂.Tup → DeltaDat (T.Q.Xo j) c' D.R.nV) (ξ : D.what₂.Tup → IdF D →* Circle)
    (PQ : D.what₂.Tup → Ideal (𝓞 D.host.E)) : Prop :=
  CovPin (T.Q.Xo j) c' d ∧ ∀ t, (d t).I ≤ PQ t ∧ Squarefree (d t).pd ∧
    (∀ p : ℕ, p.Prime → p ∣ (d t).pd → Ideal.span {(p : 𝓞 D.host.E)} ⊔ PQ t ≠ ⊤) ∧ IsTwist (ξ t) (d t).pd ∧
    ∀ k : (T.U j (sig0 T.Q.c)).Comp, IsXiDet (d t).Xo₂ (d t).c₂ ((T.U j (sig0 T.Q.c)).X k).Gm
      ((T.U j (sig0 T.Q.c)).X k).ξ0 (T.iota j) (ξ t) (d t).cδ

def FieldPin (a : (D.host.E →+* ℂ) × ℕ → ℕ) : Prop :=
  LLc D ≤ c'.F ∧ LevActLaws (T.Q.Xo j) T.Q.c (levAll (Dw := T.Q.Dw j) T.Q.l) ∧
    LevActLaws (T.Q.Xo j) c' (levAll (Dw := T.Q.Dw j) T.Q.l) ∧
    LevActExtends (T.Q.Xo j) (levAll (Dw := T.Q.Dw j) T.Q.l) h a D.R.nV ∧
    CuspBaseChange (T.Q.Xo j) h (unf T j) a D.R.nV ∧ Nonempty (T.U j (sig0 T.Q.c)).Comp ∧
    ∀ k, IsomEmb ((T.U j (sig0 T.Q.c)).X k).Gm ((T.U j (sig0 T.Q.c)).X k).ξ0 (T.Q.Dw j) (T.iota j)

def EquivPin (a : (D.host.E →+* ℂ) × ℕ → ℕ) : Prop :=
  ∀ (hr : (T.V j (sig0 T.Q.c)).rank = D.R.r) (k : LevGrp T j) (κ : GA D (T.V j (sig0 T.Q.c))),
    let ι := LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota j
    κ ∈ GfC (T.V j (sig0 T.Q.c)) →
    (∀ z, z ∈ UnitaryDeterminantRoot.latHat D.host.F ι ↔ (finHom (T.V j (sig0 T.Q.c)) κ).1.mulVec z ∈ UnitaryDeterminantRoot.latHat D.host.F ι) →
    MarkAt (F := D.host.F) T.Q.l ι ι (liftLa k) (finHom (T.V j (sig0 T.Q.c)) κ).1 →
    ∀ f ∈ Formalism.L2.PjFree.cusp (T.Q.Xo j) c' (unfFamUp h (unf T j)) a D.R.nV, ∀ g : GA D (T.V j (sig0 T.Q.c)),
      T.cE j (sig0 T.Q.c) (T.dict j (sig0 T.Q.c) g).1 *
          Formalism.L2.PjFree.rdU (unfoldingOfFieldLe (T.Q.Xo j) h (unf T j)) (levAct (T.Q.Xo j) c' (levAll (Dw := T.Q.Dw j) T.Q.l) k f)
            (T.dict j (sig0 T.Q.c) g).1 (T.dict j (sig0 T.Q.c) g).2 =
        T.cE j (sig0 T.Q.c) (T.dict j (sig0 T.Q.c) (g * κ)).1 *
          Formalism.L2.PjFree.rdU (unfoldingOfFieldLe (T.Q.Xo j) h (unf T j)) f (T.dict j (sig0 T.Q.c) (g * κ)).1 (T.dict j (sig0 T.Q.c) (g * κ)).2

variable (ka : WeightFamilies.Wt D j) (lam : D.what₂.Tau → DomWeight D.R.nV)
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

def BadAt : Prop :=
  ∀ t, bad t ≠ 0 ∧ ∃ cond : ℕ, BadPin (bad t) (D.host.QS * D.host.q) D.host.d cond ∧ DefinedMod (muRec Tt t j) cond

def RepsPin : Prop :=
  RepsCov (T.Q.Xo j) c' Cl d bad Lh La Nc gam ∧
    ∀ t, ClassesAt D.R.r T.Q.l.M (d t).l₂.M (bad t) (PQ t) (Lh t) (gam t) ∧ ∃ m : ℕ, 0 < m ∧ vol t = ((m : c'.F))⁻¹

def EpPin : Prop :=
  ∀ t k, EpVal T.Q.H (chiSplit Tt t j) (bad t) D.R.r (Lh t k) ((ep t k : c'.F) : ℂ)

def IoPin : Prop :=
  ∃ hw : VVc c' lam, IoLFRec c' (fun τ => embF c' (DV.tauEmb D τ)) lam (wtA ka) io hw

def DatumPin : Prop :=
  SpansMod (Mfr T.Q.l) β ∧ (∀ t, DatumVal T.Q.l (d t).l₂ (r_le_nV D) (ξ t) (PQ t) β (φ t)) ∧
    WPin (T.Q.Xo j) c' Cl d φ w

def GeoPins : Prop :=
  InR D j ∧ LawsJ T ∧ WeightPin j ka lam ∧ CharPin T Tt j ξ PQ ∧ FieldPin j h (wtA ka) ∧ EquivPin j h (wtA ka) ∧
    IsPinnedCover₂ j d ξ PQ ∧ BadAt Tt j bad ∧ RepsPin j PQ Cl Lh gam vol bad d La Nc ∧ EpPin Tt j Cl Lh bad ep ∧
    IoPin j ka lam io ∧ DatumPin j PQ β Cl ξ d φ w

def GeoRow : Prop :=
  RowUp (T.Q.Xo j) h (unf T j) (fun q : AutQ (T.V j (sig0 T.Q.c)) => T.dict j (sig0 T.Q.c) q.out)
    (fun q => T.mu j (sig0 T.Q.c) q.out) (xiR D) (wtA ka) (levAll (Dw := T.Q.Dw j) T.Q.l) d Cl w La Nc gam vol ep io
    thAd Pl (LLc D) (T.cE j (sig0 T.Q.c)) ph

def GeoHalf : Prop :=
  GeoPins Tt j h ka lam PQ β Cl Lh gam vol ξ bad d φ w La Nc ep io ∧
    GeoRow j h ka lam Cl gam vol thAd Pl ph d w La Nc ep io

def GeoHalfEx : Prop :=
  ∃ (ξ : D.what₂.Tup → IdF D →* Circle) (bad : D.what₂.Tup → ℕ) (d : D.what₂.Tup → DeltaDat (T.Q.Xo j) c' D.R.nV)
    (φ : ∀ t, (Fin D.R.nV → LevQc (T.Q.Dw j) (d t).l₂) → c'.F)
    (w : ∀ t, Cl t → (Fin D.R.nV → LevQ (T.Q.Dw j) (d t).l₂) → c'.F)
    (La : ∀ t, Cl t → GenLat D.host.E D.R.nV) (Nc : ∀ t, Cl t → ℕ) (ep : ∀ t, Cl t → c'.F)
    (io : VVc c' lam →ₗ[c'.F] MvPolynomial (LtN (T.Q.Dw j) D.R.nV) c'.F),
    GeoHalf Tt j h ka lam PQ β Cl Lh gam vol thAd Pl ph ξ bad d φ w La Nc ep io

end Record

end GlobalTheory.IndefiniteRowSideFullHecke.HalfGeometricCovers
