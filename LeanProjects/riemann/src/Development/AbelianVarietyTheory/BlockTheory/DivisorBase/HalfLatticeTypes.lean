import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
import Formalism.LocalToGlobal.ProjectiveLattices.LiftLaSpec
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
import Formalism.LocalToGlobal.IndefiniteReal.FWExist

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.HalfLatticeTypes

open NumberField IsDedekindDomain Module AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AllWt
open scoped TensorProduct

attribute [local instance] Over.cartesianMonoidalCategory

section Action

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

abbrev Rs (l : Level H) : Type := 𝓞 E ⧸ l.Mb

theorem half_ne_bot (l : Level H) : l.Mb ≠ ⊥ := fun h => by
  have h1 := l.prod
  rw [h, Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero] at h1
  have := l.three_le
  omega

instance (l : Level H) : Finite (Rs l) := Ideal.finiteQuotientOfFreeOfNeBot _ (half_ne_bot l)

abbrev Gz (l : Level H) (r : ℕ) : Type := GL (Fin r) (Rs l)

instance (l : Level H) (r : ℕ) : Fintype (Gz l r) := Fintype.ofFinite _

variable {l l' : Level H} {r : ℕ}

def Reads (e : Basis (Fin r) (Rs l) (LaMod Dw l)) (γ : LaMod Dw l' ≃ₗ[𝓞 E] LaMod Dw l')
    (g : Matrix (Fin r) (Fin r) (Rs l)) : Prop :=
  ∀ a : Dw.La, (Submodule.Quotient.mk (liftLa γ a) : LaMod Dw l) = Matrix.toLin e e g (Submodule.Quotient.mk a)

def IsUnip {R : Type} [CommRing R] (u : Matrix (Fin r) (Fin r) R) : Prop :=
  (∀ i, u i i = 1) ∧ ∀ i j, j < i → u i j = 0

def superSum {R : Type} [CommRing R] (u : Matrix (Fin r) (Fin r) R) : R :=
  ∑ i : Fin r, ∑ j : Fin r, if (j : ℕ) = i + 1 then u i j else 0

variable (Xo' : Moduli Dw l') (c' : Coeff l') {K : Type} [Field K] (ι : K →+* c'.F)
  (e : Basis (Fin r) (Rs l) (LaMod Dw l))

set_option synthInstance.maxHeartbeats 400000 in

def typeSub (ψ₀ : AddChar (Rs l) K) : Submodule c'.F (Rul Xo' c') where
  carrier := {f | ∀ (γ : LaMod Dw l' ≃ₗ[𝓞 E] LaMod Dw l') (u : Matrix (Fin r) (Fin r) (Rs l)), Reads e γ u → IsUnip u →
    ∀ (p : TRing c'.F) (y y' : FrPt Xo' c' p.R), levR (liftLa γ, LinearMap.id) y y' →
      f p y' = ι (ψ₀ (-superSum u)) • f p y}
  zero_mem' := fun γ u _ _ p y y' _ => by simp
  add_mem' := fun {f g} hf hg γ u h1 h2 p y y' h => by
    simp only [Pi.add_apply, hf γ u h1 h2 p y y' h, hg γ u h1 h2 p y y' h, smul_add]
  smul_mem' := fun a f hf γ u h1 h2 p y y' h => by
    simp only [Pi.smul_apply, hf γ u h1 h2 p y y' h]
    exact smul_comm _ _ _

def MoveG (g : Gz l r) {S : Type} [CommRing S] [Algebra c'.F S] (y y' : FrPt Xo' c' S) : Prop :=
  ∃ γ : LaMod Dw l' ≃ₗ[𝓞 E] LaMod Dw l', Reads e γ g ∧
    (∀ q ∈ l.Mb • (⊤ : Submodule (𝓞 E) (LaMod Dw l')), γ q = q) ∧ levR (liftLa γ, LinearMap.id) y y'

def actG (g : Gz l r) : Rul Xo' c' →ₗ[c'.F] Rul Xo' c' :=
  actL (K := c'.F) (fun S _ _ => FrPt Xo' c' S)
    (fun {S : Type} [CommRing S] [Algebra c'.F S] (g' : Gz l r) (y y' : FrPt Xo' c' S) => MoveG Xo' c' e g' y y') g

def idemCoeff (X : Finset (Gz l r → K)) (χ : (Rs l)ˣ →* Kˣ) (k : Gz l r) : K :=
  (Formalism.L2.DIV.idemOf X).coeff k * (((χ (Matrix.GeneralLinearGroup.det k))⁻¹ : Kˣ) : K)

set_option synthInstance.maxHeartbeats 400000 in

def idemOp (X : Finset (Gz l r → K)) (χ : (Rs l)ˣ →* Kˣ) : Rul Xo' c' →ₗ[c'.F] Rul Xo' c' :=
  ∑ k : Gz l r, HSMul.hSMul (α := c'.F) (ι (idemCoeff X χ k)) (actG Xo' c' e k)

variable {Xo' c'} {n : ℕ} (U' : ∀ σ : c'.F →+* ℂ, Unf Xo' c' σ n)

def typeLat (ψ₀ : AddChar (Rs l) K) (G : WTZ E) : Submodule (𝓞 c'.F) (cuspW Xo' c' U' G) :=
  latW U' G ⊓ ((typeSub Xo' c' ι e ψ₀).comap (cuspW Xo' c' U' G).subtype).restrictScalars (𝓞 c'.F)

def goodLat (ψ₀ : AddChar (Rs l) K) (X : Finset (Gz l r → K)) (χ : (Rs l)ˣ →* Kˣ) (G : WTZ E) :
    Submodule (𝓞 c'.F) (cuspW Xo' c' U' G) :=
  typeLat ι e U' ψ₀ G ⊓
    (((Submodule.span c'.F (typeLat ι e U' ψ₀ G : Set (cuspW Xo' c' U' G))).map
      (idemOp Xo' c' ι e X χ ∘ₗ (cuspW Xo' c' U' G).subtype)).comap
        (cuspW Xo' c' U' G).subtype).restrictScalars (𝓞 c'.F)

set_option synthInstance.maxHeartbeats 400000 in

example (ψ₀ : AddChar (Rs l) K) (χ : (Rs l)ˣ →* Kˣ) (G : WTZ E) : goodLat ι e U' ψ₀ ∅ χ G = ⊥ := by
  refine eq_bot_iff.2 fun f hf => ?_
  obtain ⟨g, -, hg⟩ := hf.2
  have h0 : idemOp Xo' c' ι e (∅ : Finset (Gz l r → K)) χ = 0 := by simp [idemOp, idemCoeff, Formalism.L2.DIV.idemOf]
  rw [h0] at hg
  exact Subtype.ext hg.symm

example (γ : LaMod Dw l ≃ₗ[𝓞 E] LaMod Dw l) (q : LaMod Dw l) (hq : q ∈ l.Mb • (⊤ : Submodule (𝓞 E) (LaMod Dw l))) :
    γ q = q := by
  have : q = 0 := by
    refine Submodule.smul_induction_on (p := fun q => q = 0) hq (fun a ha x _ => ?_) (fun x y hx hy => by rw [hx, hy, add_zero])
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact (Submodule.Quotient.mk_eq_zero _).2 (Submodule.smul_mem_smul ha Submodule.mem_top)
  rw [this, map_zero]

example (a b c d : ℤ) : superSum !![a, b; c, d] = b := by simp [superSum, Fin.sum_univ_two]

open MonObj in

def IsLevelMap (Xo' : Moduli Dw l') (Xo : Moduli Dw l) (π : Xo'.X ⟶ Xo.X) (m : SABMap Xo'.univ.t Xo.univ.t π) : Prop :=
  (∃ jK : KA l →+* KA l', (∀ x, ((jK x : KA l') : ℂ) = ((x : KA l) : ℂ)) ∧ π ≫ Xo.s = Xo'.s ≫ spMap jK) ∧
    (∀ a, (Xo'.univ.eta a ^ (l'.M / l.M)).left ≫ m.φ = π ≫ (Xo.univ.eta a).left) ∧
    ∀ a, (Xo'.univ.etaA a ^ (l'.A / l.A)).left ≫ m.φ = π ≫ (Xo.univ.etaA a).left

def FrAbove {Xo : Moduli Dw l} {c : Coeff l} {π : Xo'.X ⟶ Xo.X} (m : SABMap Xo'.univ.t Xo.univ.t π) {k : Type}
    [CommRing k] [Algebra c.F k] [Algebra c'.F k] (y' : FrPt Xo' c' k) (y : FrPt Xo c k) : Prop :=
  y'.x ≫ π = y.x ∧ (∀ τ i, y'.u τ i ≫ m.φ = y.u τ i) ∧
  ∃ (w₀ : LB.Iso Xo'.univ.t.PP.L (Xo.univ.t.PP.L.pull m.φ)) (pm : Gx y'.x ⟶ Gx y.x)
    (t : LB.Sec (LB.LinComb (Xo.univ.t.PP.L.pull m.φ) (K := Fin 1)
      (fun _ => (snd (Over.mk y'.x) Xo'.univ.t.G).left) (fun _ => 1))),
    w₀.IsGen ∧
    LB.Gen.Maps (LB.linCombIso w₀ (K := PUnit) (fun _ => eSec Xo'.univ.t.G) (fun _ => 1))
      Xo'.univ.t.PP.rig (m.cm.rigPull Xo.univ.t.PP.L Xo.univ.t.PP.rig) ∧
    pm ≫ (snd (Over.mk y.x) Xo.univ.t.G).left = (snd (Over.mk y'.x) Xo'.univ.t.G).left ≫ m.φ ∧
    pm ≫ (fst (Over.mk y.x) Xo.univ.t.G).left = (fst (Over.mk y'.x) Xo'.univ.t.G).left ∧
    SecMaps (LB.linCombIso w₀ (K := Fin 1) (fun _ => (snd (Over.mk y'.x) Xo'.univ.t.G).left) (fun _ => 1)) y'.s t ∧
    ∀ (i : Fin 1 → Xo.univ.t.PP.L.ι)
      (h : (LB.LinComb (Xo.univ.t.PP.L.pull m.φ) (K := Fin 1)
        (fun _ => (snd (Over.mk y'.x) Xo'.univ.t.G).left) (fun _ => 1)).U (fun _ _ => i 0) ≤ pm ⁻¹ᵁ (PPx y.x).U i),
      (pm.appLE _ _ h).hom (y.s.f i) = t.f (fun _ _ => i 0)

end Action

section Record

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsUnifAt {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
    {σ : c.F →+* ℂ} (U : Unf Xo c σ D.R.r) (V : HSp D) (dict : GA D V → Σ k, Frame (U.X k).Ψ D.R.r)
    (ι₀ : Dw.La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)) : Prop :=
  IsUnf U ∧ ∃ (hr : V.rank = D.R.r) (Kf : Subgroup (GA D V))
    (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ)
    (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun i => relab c σ (e i).1))
    (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ),
    (∀ k, ModelW V hr (U.X k)) ∧ (∀ k, IsOrthogonalFrame (U.X k) x₀) ∧ IsLevelK V l.M Kf ∧
      (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧ DictIsUnif V dict Kf th hr ∧
      LatEmb V (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ ι₀) ∧
      LatIsom V Dw.EF (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ ι₀) ∧
      DictLat U V hr dict (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ ι₀) e F ik φ th x₀

def kapZ (D : D7) (i : Fin D.R.m) : WTZ D.host.E :=
  wtZ (wtA (Formalism.IndefR.FWT.kapTop D i)) (Formalism.IndefR.FWT.kapTop D i).n

variable (T : CoreJ D) (i : Fin D.R.m)

def latM (e : Basis (Fin D.R.r) (Rs T.Q.l) (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)) (ψ₀ : AddChar (Rs T.Q.l) T.Q.c.F)
    (X : Finset (Gz T.Q.l D.R.r → T.Q.c.F)) (χ : (Rs T.Q.l)ˣ →* (T.Q.c.F)ˣ) :
    Submodule (𝓞 T.Q.c.F) (cuspW (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.U ((i : ℕ) + 1)) (kapZ D i)) :=
  goodLat (RingHom.id T.Q.c.F) e (T.U ((i : ℕ) + 1)) ψ₀ X χ (kapZ D i)

def normM : (T.Q.c.F →+* ℂ) → cuspW (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.U ((i : ℕ) + 1)) (kapZ D i) → ℝ :=
  normW (T.U ((i : ℕ) + 1)) (xiR D) (T.V ((i : ℕ) + 1)) (T.dict ((i : ℕ) + 1)) (kapZ D i)

variable {T i} {l' : Level T.Q.H} {Xo' : Moduli (T.Q.Dw ((i : ℕ) + 1)) l'} {c' : Coeff l'}

abbrev incl (hle : T.Q.c.F ≤ c'.F) : T.Q.c.F →+* c'.F := (IntermediateField.inclusion hle).toRingHom

def IsUpper (cc : ℕ) (hle : T.Q.c.F ≤ c'.F) (U' : ∀ σ : c'.F →+* ℂ, Unf Xo' c' σ D.R.r)
    (dict' : ∀ σ, GA D (D.sp.W ((i : ℕ) + 1)) → Σ k, Frame ((U' σ).X k).Ψ D.R.r) : Prop :=
  Nat.Coprime (D.host.g 0 * D.host.g 1) 15 ∧ l'.M = D.host.g 0 * D.host.g 1 * 15 ^ cc ∧ l'.A = 1 ∧ T.Q.l.Dvd l' ∧
    (letI := (incl hle).toAlgebra; IsGalois T.Q.c.F c'.F) ∧
    ∀ σ, GoodEmb c' σ → IsUnifAt (U' σ) (D.sp.W ((i : ℕ) + 1)) (dict' σ) (T.iota ((i : ℕ) + 1))

def UnramifiedPrimeToFifteen (hle : T.Q.c.F ≤ c'.F) : Prop :=
  letI := (incl hle).toAlgebra
  ∀ P : HeightOneSpectrum (𝓞 c'.F), (15 : 𝓞 c'.F) ∉ P.asIdeal → Algebra.IsUnramifiedAt (𝓞 T.Q.c.F) P.asIdeal

def normN (U' : ∀ σ : c'.F →+* ℂ, Unf Xo' c' σ D.R.r)
    (dict' : ∀ σ, GA D (D.sp.W ((i : ℕ) + 1)) → Σ k, Frame ((U' σ).X k).Ψ D.R.r) :
    (c'.F →+* ℂ) → cuspW Xo' c' U' (kapZ D i) → ℝ :=
  normW U' (xiR D) (fun _ => D.sp.W ((i : ℕ) + 1)) dict' (kapZ D i)

def IsPullBack (hle : T.Q.c.F ≤ c'.F) {U' : ∀ σ : c'.F →+* ℂ, Unf Xo' c' σ D.R.r}
    (pb : cuspW (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.U ((i : ℕ) + 1)) (kapZ D i) →ₛₗ[incl hle]
      cuspW Xo' c' U' (kapZ D i)) : Prop :=
  ∃ (π : Xo'.X ⟶ (T.Q.Xo ((i : ℕ) + 1)).X) (m : SABMap Xo'.univ.t (T.Q.Xo ((i : ℕ) + 1)).univ.t π),
    IsLevelMap Xo' (T.Q.Xo ((i : ℕ) + 1)) π m ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra T.Q.c.F k] [Algebra c'.F k],
      (∀ a, algebraMap c'.F k (incl hle a) = algebraMap T.Q.c.F k a) →
      (∀ y' : FrPt Xo' c' k, ∃ y : FrPt (T.Q.Xo ((i : ℕ) + 1)) T.Q.c k, FrAbove m y' y) ∧
      ∀ (y' : FrPt Xo' c' k) (y : FrPt (T.Q.Xo ((i : ℕ) + 1)) T.Q.c k), FrAbove m y' y → ∀ f,
        evR Xo' c' (pb f : Rul Xo' c') y' = evR (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (f : T.R ((i : ℕ) + 1)) y

def ForAllData (D : D7)
    (P : ∀ (T : CoreJ D) (i : Fin D.R.m) (l' : Level T.Q.H) (Xo' : Moduli (T.Q.Dw ((i : ℕ) + 1)) l') (c' : Coeff l')
      (_ : T.Q.c.F ≤ c'.F) (U' : ∀ σ : c'.F →+* ℂ, Unf Xo' c' σ D.R.r)
      (_ : ∀ σ, GA D (D.sp.W ((i : ℕ) + 1)) → Σ k, Frame ((U' σ).X k).Ψ D.R.r)
      (_ : Basis (Fin D.R.r) (Rs T.Q.l) (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)) (_ : AddChar (Rs T.Q.l) T.Q.c.F)
      (_ : Finset (Gz T.Q.l D.R.r → T.Q.c.F)) (_ : (Rs T.Q.l)ˣ →* (T.Q.c.F)ˣ), Prop) : Prop :=
  ∀ (T : CoreJ D), LawsJ T → ∀ (i : Fin D.R.m) (cc : ℕ) (l' : Level T.Q.H) (Xo' : Moduli (T.Q.Dw ((i : ℕ) + 1)) l')
    (c' : Coeff l') (hle : T.Q.c.F ≤ c'.F) (U' : ∀ σ : c'.F →+* ℂ, Unf Xo' c' σ D.R.r)
    (dict' : ∀ σ, GA D (D.sp.W ((i : ℕ) + 1)) → Σ k, Frame ((U' σ).X k).Ψ D.R.r), IsUpper cc hle U' dict' →
    ∀ (e : Basis (Fin D.R.r) (Rs T.Q.l) (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)) (ψ₀ : AddChar (Rs T.Q.l) T.Q.c.F),
      ψ₀.IsPrimitive → ∀ X : Finset (Gz T.Q.l D.R.r → T.Q.c.F), (∀ χ ∈ X, Formalism.L2.DIV.IsAbsIrrChar χ) →
        ∀ χ : (Rs T.Q.l)ˣ →* (T.Q.c.F)ˣ, P T i l' Xo' c' hle U' dict' e ψ₀ X χ

def SlopeDescent (D : D7) : Prop :=
  ForAllData D fun T i _ _ c' hle U' dict' e ψ₀ X χ =>
    Formalism.HN.rkK (latM T i e ψ₀ X χ) = Formalism.HN.rkK (goodLat (incl hle) e U' ψ₀ X χ (kapZ D i)) ∧
      (goodLat (incl hle) e U' ψ₀ X χ (kapZ D i) ≠ ⊥ →
        GlobalTheory.AllWt.slope (normN U' dict') (goodLat (incl hle) e U' ψ₀ X χ (kapZ D i)) - Real.log (rootDiscr c'.F) ≤
          GlobalTheory.AllWt.slope (normM T i) (latM T i e ψ₀ X χ))

def ringCost (K : Type) [Field K] [NumberField K] : ℝ := Real.log (finrank ℚ K) + Real.log (rootDiscr K)

def SlopeDescentCost (D : D7) : Prop :=
  ForAllData D fun T i _ _ c' hle U' dict' e ψ₀ X χ =>
    goodLat (incl hle) e U' ψ₀ X χ (kapZ D i) ≠ ⊥ →
      GlobalTheory.AllWt.slope (normN U' dict') (goodLat (incl hle) e U' ψ₀ X χ (kapZ D i)) - ringCost c'.F ≤
        GlobalTheory.AllWt.slope (normM T i) (latM T i e ψ₀ X χ)

def PullBackDescent (D : D7) : Prop :=
  ForAllData D fun T i _ _ c' hle U' dict' e ψ₀ X χ =>
    ∃ pb, IsPullBack hle (U' := U') pb ∧
      (∀ (n : ℕ) (b : Fin n → _), LinearIndependent T.Q.c.F b → LinearIndependent c'.F fun k => pb (b k)) ∧
      (∀ σ f, normN U' dict' σ (pb f) = normM T i (σ.comp (incl hle)) f) ∧
      (∀ f, f ∈ latM T i e ψ₀ X χ ↔ pb f ∈ goodLat (incl hle) e U' ψ₀ X χ (kapZ D i)) ∧
      Submodule.span c'.F (pb '' (latM T i e ψ₀ X χ : Set _)) =
        Submodule.span c'.F (goodLat (incl hle) e U' ψ₀ X χ (kapZ D i) : Set _)

def ExactDescent (D : D7) : Prop :=
  ForAllData D fun T i _ _ c' hle U' _ e ψ₀ X χ =>
    UnramifiedPrimeToFifteen hle → IsCoprime (discr D.host.E) 15 → ∀ pb, IsPullBack hle (U' := U') pb →
      Submodule.span (𝓞 c'.F) (pb '' (latM T i e ψ₀ X χ : Set _)) = goodLat (incl hle) e U' ψ₀ X χ (kapZ D i)

end Record

end GlobalTheory.IndefiniteRowSideFullHecke.HalfLatticeTypes
