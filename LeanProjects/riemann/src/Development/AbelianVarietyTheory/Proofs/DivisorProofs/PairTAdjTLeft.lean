import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HodgeTateLatticePointFinrankTateModule
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RosatiAdjIffLamEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumBLieMemHtLatIffOfPointOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTorusLeLieSpan

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.CompHt GlobalTheory.CM
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PointMap

section General

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O]
  [Algebra O C] {Λ : Type} [CommRing Λ] [StarRing Λ] (P P' : Point p v O Λ)

def mapT (α : P.A.A ⟶ P'.A.A) [IsMonHom α] : P.T →ₗ[ℤ_[p]] P'.T :=
  Tate.map p (IndepPoint.ptsHom α _)

theorem lev_mapT (α : P.A.A ⟶ P'.A.A) [IsMonHom α] (t : P.T) (n : ℕ) :
    (mapT P P' α t).lev n = t.lev n ≫ α := rfl

def mapV [Algebra ℤ_[p] C] (α : P.A.A ⟶ P'.A.A) [IsMonHom α] : P.V →ₗ[C] P'.V :=
  (mapT P P' α).baseChange C

variable [IsAlgClosed C] [CharZero C]

def adjT (α : P.A.A ⟶ P'.A.A) [IsMonHom α] : P'.T →ₗ[ℤ_[p]] P.T :=
  (LinearEquiv.ofBijective _ P.pairT_bijective).symm.toLinearMap ∘ₗ (mapT P P' α).dualMap ∘ₗ pairT P'.A P'.eps

theorem pairT_adjT_left (α : P.A.A ⟶ P'.A.A) [IsMonHom α] (t : P'.T) (s : P.T) :
    pairT P.A P.eps (adjT P P' α t) s = pairT P'.A P'.eps t (mapT P P' α s) :=
  LinearMap.congr_fun ((LinearEquiv.ofBijective _ P.pairT_bijective).apply_symm_apply
    ((mapT P P' α).dualMap (pairT P'.A P'.eps t))) s

theorem pairT_mapT (α : P.A.A ⟶ P'.A.A) [IsMonHom α] (s : P.T) (t : P'.T) :
    pairT P'.A P'.eps (mapT P P' α s) t = pairT P.A P.eps s (adjT P P' α t) := by
  rw [← (isAlt_pairT P'.A P'.eps).neg_eq t, ← pairT_adjT_left, (isAlt_pairT P.A P.eps).neg_eq]

def adjV [Algebra ℤ_[p] C] (α : P.A.A ⟶ P'.A.A) [IsMonHom α] : P'.V →ₗ[C] P.V :=
  (adjT P P' α).baseChange C

theorem adjV_tmul [Algebra ℤ_[p] C] (α : P.A.A ⟶ P'.A.A) [IsMonHom α] (c : C) (t : P'.T) :
    adjV P P' α (c ⊗ₜ t) = c ⊗ₜ adjT P P' α t := rfl

end General

section Good

variable {Λ : Type} [CommRing Λ] [StarRing Λ]

def pullAct {S S' : Scheme.{0}} (f : S' ⟶ S) (B : Out.PolAV S) (o : B.OAct Λ) :
    (StrictPull.polPull B f).OAct Λ := (exists_oAct_polPull f B o).choose

theorem eq_map_of_fst {S S' : Scheme.{0}} (f : S' ⟶ S) {X Y : Over S} (a : X ⟶ Y)
    (b : (Over.pullback f).obj X ⟶ (Over.pullback f).obj Y)
    (h : b.left ≫ pullback.fst Y.hom f = pullback.fst X.hom f ≫ a.left) : b = (Over.pullback f).map a :=
  Over.OverMorphism.ext (pullback.hom_ext (h.trans (pullback.lift_fst _ _ _).symm)
    ((Over.w b).trans (Over.w ((Over.pullback f).map a)).symm))

theorem pullAct_act {S S' : Scheme.{0}} (f : S' ⟶ S) (B : Out.PolAV S) (o : B.OAct Λ) (a : Λ) :
    (pullAct f B o).act a = (Over.pullback f).map (o.act a) :=
  eq_map_of_fst f _ _ ((exists_oAct_polPull f B o).choose_spec a)

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O]
  [Algebra O C] (hv : v.Integers O) (ε : Eps p C) {R : Type} [CommRing R] (j : R →+* O)

def goodPoint (B : Out.PolAV (Sp R)) (o : B.OAct Λ) : Point p v O Λ :=
  ofGoodReduction hv ε (StrictPull.polPull B (spMap j)) (pullAct (spMap j) B o)

variable {B B' : Out.PolAV (Sp R)} (o : B.OAct Λ) (o' : B'.OAct Λ)

theorem goodPoint_oGt (a : Λ) : (goodPoint hv ε j B o).oGt.act a = (Over.pullback (spMap j)).map (o.act a) :=
  pullAct_act _ B o a

theorem goodPoint_oA (a : Λ) : (goodPoint hv ε j B o).oA.act a =
    (Over.pullback (spMap (algebraMap O C))).map ((Over.pullback (spMap j)).map (o.act a)) :=
  (pullAct_act _ _ (pullAct (spMap j) B o) a).trans (congrArg _ (pullAct_act _ B o a))

def homO (f : B.A ⟶ B'.A) : (goodPoint hv ε j B o).Gt ⟶ (goodPoint hv ε j B' o').Gt :=
  (Over.pullback (spMap j)).map f

def homC (f : B.A ⟶ B'.A) : (goodPoint hv ε j B o).A.A ⟶ (goodPoint hv ε j B' o').A.A :=
  (Over.pullback (spMap (algebraMap O C))).map ((Over.pullback (spMap j)).map f)

instance (f : B.A ⟶ B'.A) [IsMonHom f] : IsMonHom (homO hv ε j o o' f) :=
  inferInstanceAs (IsMonHom ((Over.pullback (spMap j)).map f))

instance (f : B.A ⟶ B'.A) [IsMonHom f] : IsMonHom (homC hv ε j o o' f) :=
  inferInstanceAs (IsMonHom ((Over.pullback (spMap (algebraMap O C))).map ((Over.pullback (spMap j)).map f)))

def homT (f : B.A ⟶ B'.A) [IsMonHom f] : (goodPoint hv ε j B o).T →ₗ[ℤ_[p]] (goodPoint hv ε j B' o').T :=
  mapT _ _ (homC hv ε j o o' f)

def homV [Algebra ℤ_[p] C] (f : B.A ⟶ B'.A) [IsMonHom f] :
    (goodPoint hv ε j B o).V →ₗ[C] (goodPoint hv ε j B' o').V :=
  mapV _ _ (homC hv ε j o o' f)

def homLie (f : B.A ⟶ B'.A) [IsMonHom f] (x : LieG (goodPoint hv ε j B o).Gt) : LieG (goodPoint hv ε j B' o').Gt :=
  TorusTateLie.lieMap (homO hv ε j o o' f) x

theorem lev_homT (f : B.A ⟶ B'.A) [IsMonHom f] (t : (goodPoint hv ε j B o).T) (n : ℕ) :
    (homT hv ε j o o' f t).lev n = t.lev n ≫ homC hv ε j o o' f := rfl

end Good

section Triples

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def patAct {S : Scheme.{0}} (T : PAT H S) : letI := H.starRing; T.pol.OAct (𝓞 E) :=
  letI := H.starRing
  haveI : IsCommMonObj T.t.G := T.ab.comm
  ⟨T.t.act.toRingAct, fun a =>
    (GlobalTheory.RosLam.rosatiAdj_iff_lamEq GlobalTheory.firstFiveLaws.1.globalFns _ T.pol _ _ (T.t.act.hom a) (T.t.act.hom _)).2 (by
      change GlobalTheory.CM.LamEq _ _ _ _ _ (T.t.act.act (H.bar a))
      simpa [GlobalTheory.CM.LamEq] using T.t.adj a)⟩

variable {K : Type} [Field K] {ℓ : ℕ} [Fact ℓ.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type}
  [CommRing O] [Algebra O C] (hv : v.Integers O) (ε : Eps ℓ C) (i : K →+* C)

abbrev patPoint (T : PAT H (Sp (𝓞 K))) : letI := H.starRing; Point ℓ v O (𝓞 E) :=
  letI := H.starRing
  goodPoint hv ε (embO hv i) T.pol (patAct T)

section Linear

variable {T T' : PAT H (Sp (𝓞 K))} {f : T.t.G ⟶ T'.t.G} (hf : Serre.IsLinearHom T.t.act T'.t.act f)

abbrev patT : letI := H.starRing; (patPoint hv ε i T).T →ₗ[ℤ_[ℓ]] (patPoint hv ε i T').T :=
  letI := H.starRing
  haveI : IsMonHom (C := Over (Sp (𝓞 K))) (M := T.pol.A) (N := T'.pol.A) f := hf.isMonHom
  homT (B := T.pol) (B' := T'.pol) hv ε (embO hv i) (patAct T) (patAct T') f

abbrev patV [Algebra ℤ_[ℓ] C] : letI := H.starRing; (patPoint hv ε i T).V →ₗ[C] (patPoint hv ε i T').V :=
  letI := H.starRing
  haveI : IsMonHom (C := Over (Sp (𝓞 K))) (M := T.pol.A) (N := T'.pol.A) f := hf.isMonHom
  homV (B := T.pol) (B' := T'.pol) hv ε (embO hv i) (patAct T) (patAct T') f

abbrev patLie : letI := H.starRing; LieG (patPoint hv ε i T).Gt → LieG (patPoint hv ε i T').Gt :=
  letI := H.starRing
  haveI : IsMonHom (C := Over (Sp (𝓞 K))) (M := T.pol.A) (N := T'.pol.A) f := hf.isMonHom
  homLie (B := T.pol) (B' := T'.pol) hv ε (embO hv i) (patAct T) (patAct T') f

end Linear

variable [NumberField K] {ρ : 𝓞 K} {σ₁ : K →+* ℂ} {p q : ℕ} (X : CMObj H K ρ σ₁ p q)

abbrev pointB : letI := H.starRing; Point ℓ v O (𝓞 E) := patPoint hv ε i X.B

abbrev pointA (b : Bool) : letI := H.starRing; Point ℓ v O (𝓞 E) := patPoint hv ε i (X.A b)

abbrev phiT (k : Fin p ⊕ Fin q) :
    letI := H.starRing; (pointA hv ε i X k.isLeft).T →ₗ[ℤ_[ℓ]] (pointB hv ε i X).T := patT hv ε i (X.lin k)

abbrev phiV [Algebra ℤ_[ℓ] C] (k : Fin p ⊕ Fin q) :
    letI := H.starRing; (pointA hv ε i X k.isLeft).V →ₗ[C] (pointB hv ε i X).V := patV hv ε i (X.lin k)

abbrev phiLie (k : Fin p ⊕ Fin q) :
    letI := H.starRing; LieG (pointA hv ε i X k.isLeft).Gt → LieG (pointB hv ε i X).Gt := patLie hv ε i (X.lin k)

abbrev phiVP [Algebra ℤ_[ℓ] C] (a : Fin p) :
    letI := H.starRing; (pointA hv ε i X true).V →ₗ[C] (pointB hv ε i X).V :=
  patV (T := X.A true) hv ε i (X.lin (Sum.inl a))

abbrev phiVQ [Algebra ℤ_[ℓ] C] (b : Fin q) :
    letI := H.starRing; (pointA hv ε i X false).V →ₗ[C] (pointB hv ε i X).V :=
  patV (T := X.A false) hv ε i (X.lin (Sum.inr b))

end Triples

end GlobalTheory.PointMap
