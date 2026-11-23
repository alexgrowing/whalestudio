import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowsAre
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalizationFreeStageTrueGroupColumnChoiceStep
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsBIffCoreB
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.Ties

section Gen

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] {O : Type} [CommRing O] {φ : O →+* ℂ} {σ : K →+* ℂ}

def castEq {m m' : Mat1 K G} (h : m = m') : (Fin m'.n → K) ≃ₗ[K] (Fin m.n → K) := h ▸ LinearEquiv.refl K _

theorem forms_cast {m m' : Mat1 K G} {s : Sp1 O φ G} (h : m = m') (t : Tie1 σ m s) :
    FormsTie σ (t.j.comp (castEq h).toLinearMap) m'.H m'.E s.e := by
  subst h; exact t.forms

theorem lat_cast {m m' : Mat1 K G} {s : Sp1 O φ G} (h : m = m') (t : Tie1 σ m s) :
    OLatTie σ s.lat (t.j.comp (castEq h).toLinearMap) m'.N := by
  subst h; exact t.latT

theorem cen_cast {m m' : Mat1 K G} {s : Sp1 O φ G} (h : m = m') (t : Tie1 σ m s)
    (z : Subalgebra.center ℂ (MonoidAlgebra ℂ G)) (a : MonoidAlgebra K G)
    (ha : ∀ g, σ (a.coeff g) = (z : MonoidAlgebra ℂ G).coeff g) (x) :
    s.act z (t.j (castEq h x)) = t.j (castEq h ((m'.op a).mulVec x)) := by
  subst h; exact t.cen z a ha x

theorem sameOn_tie {τ : Type} (mA : τ → Mat1 K G) (s : τ → Sp1 O φ G) (tA : ∀ μ, Tie1 σ (mA μ) (s μ)) {μ μ' : τ} (hμ : μ = μ')
    {m' : Mat1 K G} (h : mA μ' = m') (j : (Fin m'.n → K) →ₛₗ[σ] (s μ).A.T) (hj : HEq j ((tA μ').cast h).j) :
    SameOn (tA μ).j j := by
  subst hμ; subst h
  obtain rfl : j = (tA μ).j := eq_of_heq hj
  exact ⟨rfl, fun x x' hx => congrArg _ (funext fun a => hx a a rfl)⟩

theorem sameOn_cast {τ : Type} (mL : τ → Mat1 K G) {μ μ' : τ} (hμ : μ = μ') {m' m'' : Mat1 K G} (h : mL μ = m') (h' : mL μ' = m'')
    (j : (Fin m''.n → K) → Fin (mL μ).n → K) (hj : ∀ x, HEq (j x) x) : SameOn (castEq h) j := by
  subst hμ; subst h; subst h'
  exact ⟨rfl, fun x x' hx => (funext fun a => hx a a rfl).trans (eq_of_heq (hj x')).symm⟩

end Gen

theorem stdIso_dat {X : Stages} {px : PreX X.B.toPre} {I : ColIn X.B px} {hX : X.B.fields.Ok} {T : TwDat X.B}
    {Wt : Set X.B.places.Pl} (z : Dat X I hX T Wt) : StdIso X px (z.R.eG.trans z.cG) := by
  obtain ⟨plg, iso, h1, -, -, h4⟩ := z.pins.keep.grp
  have hP : z.R.Pg = (X.B.primes px).vGs := z.lev.Pg
  refine ⟨plg.trans (Equiv.subtypeEquivRight fun x => by rw [hP]; exact Iff.rfl), iso, h1, fun g kv => ?_⟩
  exact (z.idG g (plg kv).1 _ (plg kv).2).symm.trans (h4 g kv)

variable {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}

set_option maxHeartbeats 2000000 in

theorem mLU_eq (Z Z' : w.Lt) (hX : B.fields.Ok) {Xg Xg' : Finset (Gc B w.px → B.LL)} {tr tr' : TrI B w.px} (h1 : Xg' = Xg)
    (h2 : tr' = tr) (a : w.I.ι) (i : Fin (w.st Z').toD7.R.m) :
    HEq (mLU (w.st Z) w.I hX Xg tr a ((i : ℕ) + 1))
      (lMat (D := (w.st Z').toD7) (famR (w.st Z') w.I hX Set.univ Xg' tr').A (lev0 w.I) (chr0 w.I) i (tAll w.I a)) := by
  subst h1; subst h2
  have e : mLU (w.st Z') w.I hX Xg' tr' a ((i : ℕ) + 1) =
      lMat (D := (w.st Z').toD7) (famR (w.st Z') w.I hX Set.univ Xg' tr').A (lev0 w.I) (chr0 w.I) i (tAll w.I a) := by
    have hi : 1 ≤ (i : ℕ) + 1 ∧ (i : ℕ) + 1 ≤ (w.st Z').toD7.R.m := ⟨by omega, i.2⟩
    unfold mLU
    rw [dif_pos hi]
    exact (by with_unfolding_all exact ((Eq.refl (lMat (D := (w.st Z').toD7) (famR (w.st Z') w.I hX Set.univ Xg' tr').A (lev0 w.I) (chr0 w.I) i (tAll w.I a))) :))
  exact (by with_unfolding_all exact ((heq_of_eq e) :))

set_option maxHeartbeats 2000000 in

theorem crd_eq (Z : w.Lt) (hX : B.fields.Ok) {Xg Xg' : Finset (Gc B w.px → B.LL)} {tr tr' : TrI B w.px} (h1 : Xg' = Xg)
    (h2 : tr' = tr) (a : w.I.ι) (M : Hs) (e : Df.MtCx w.I a ≃ₗ[ℂ] M.T)
    (j : (Fin (mAU (w.st Z) w.I hX Xg tr true a).n → (w.st Z).toD7.what₂.LL) →ₛₗ[(w.st Z).toD7.what₂.embLL] M.T)
    (j' : (Fin (mAU (w.st Z) w.I hX Xg' tr' true a).n → (w.st Z).toD7.what₂.LL) →ₛₗ[(w.st Z).toD7.what₂.embLL] M.T) (hj : HEq j' j)
    (h : ∀ y, IsCrd w.I hX a e
      (rowForm (D := (w.st Z).toD7) (famR (w.st Z) w.I hX Set.univ Xg tr).A (lev1 w.I) (chr1 w.I) (tAll w.I a) y) (j y)) (y) :
    IsCrd w.I hX a e
      (rowForm (D := (w.st Z).toD7) (famR (w.st Z) w.I hX Set.univ Xg' tr').A (lev1 w.I) (chr1 w.I) (tAll w.I a) y) (j' y) := by
  subst h1; subst h2
  obtain rfl : j' = j := eq_of_heq hj
  exact h y

theorem algebra_eq {k L : Type} [Field k] [Field L] (σ : L →+* ℂ) (v : k → ℂ) (i i' : Algebra k L)
    (hi : ∀ y, σ (@algebraMap k L _ _ i y) = v y) (hi' : ∀ y, σ (@algebraMap k L _ _ i' y) = v y) : i = i' :=
  Algebra.algebra_ext _ _ fun y => σ.injective ((hi y).trans (hi' y).symm)

set_option maxHeartbeats 4000000 in

theorem brgStd_copy0 (Z Z' : w.Lt) (hX : B.fields.Ok) (U : Set w.I.ι) (Xg : Finset (Gc B w.px → B.LL)) (tr : TrI B w.px)
    (k : Type) [Field k] [NumberField k] (v : k → ℂ)
    (i : Algebra k (w.st Z).toD7.what₂.LL) (i' : Algebra k (w.st Z').toD7.what₂.LL)
    (hi : ∀ y : k, (w.st Z).toD7.what₂.embLL (algebraMap k (w.st Z).toD7.what₂.LL y) = v y)
    (hi' : ∀ y : k, (w.st Z').toD7.what₂.embLL (algebraMap k (w.st Z').toD7.what₂.LL y) = v y)
    (R : RealDat3 (w.st Z).toD7 (famR (w.st Z) w.I hX U Xg tr) k)
    (R' : RealDat3 (w.st Z').toD7 (famR (w.st Z') w.I hX U Xg tr) k)
    (hR : HEq R' (real3 (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) ⟨Z'.W, Z'.V, Z'.S, Z'.N, Z'.G⟩ (iK := i) R))
    (h : BrgStd (w.st Z) w.I hX U Xg tr R.toRealDat) : BrgStd (w.st Z') w.I hX U Xg tr R'.toRealDat := by
  have ei : ((by with_unfolding_all exact (i :))) = i' := algebra_eq (w.st Z').toD7.what₂.embLL v _ i' ((by with_unfolding_all exact (hi :))) hi'
  subst ei
  have eR : ((by with_unfolding_all exact ((real3 (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) ⟨Z'.W, Z'.V, Z'.S, Z'.N, Z'.G⟩ (iK := i) R) :))) = R' :=
    eq_of_heq ((by with_unfolding_all exact (hR.symm :)))
  subst eR
  exact (by with_unfolding_all exact (h :))

set_option maxHeartbeats 4000000 in

theorem brgStd_copy (Z Z' : w.Lt) (hX : B.fields.Ok) (U : Set w.I.ι) {Xg Xg' : Finset (Gc B w.px → B.LL)} {tr tr' : TrI B w.px}
    (h1 : Xg' = Xg) (h2 : tr' = tr) (c : Formalism.L2.Pj.CoreJ (w.st Z).toD7) (c' : Formalism.L2.Pj.CoreJ (w.st Z').toD7)
    (i : Algebra c.Q.c.F (w.st Z).toD7.what₂.LL) (i' : Algebra c'.Q.c.F (w.st Z').toD7.what₂.LL)
    (hi : ∀ y : c.Q.c.F, B.embLL (algebraMap c.Q.c.F (w.st Z).toD7.what₂.LL y) = (y : ℂ))
    (hi' : ∀ y : c'.Q.c.F, B.embLL (algebraMap c'.Q.c.F (w.st Z').toD7.what₂.LL y) = (y : ℂ))
    (R : RealDat3 (w.st Z).toD7 (famR (w.st Z) w.I hX U Xg tr) c.Q.c.F)
    (R' : RealDat3 (w.st Z').toD7 (famR (w.st Z') w.I hX U Xg' tr') c'.Q.c.F)
    (hc : HEq c' (coreJ (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) ⟨Z'.W, Z'.V, Z'.S, Z'.N, Z'.G⟩ c))
    (hR : HEq R' (real3 (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) ⟨Z'.W, Z'.V, Z'.S, Z'.N, Z'.G⟩ (iK := i) R))
    (h : BrgStd (w.st Z) w.I hX U Xg tr R.toRealDat) : BrgStd (w.st Z') w.I hX U Xg' tr' R'.toRealDat := by
  subst h1; subst h2
  have ec : ((by with_unfolding_all exact ((coreJ (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) ⟨Z'.W, Z'.V, Z'.S, Z'.N, Z'.G⟩ c) :))) = c' := (by with_unfolding_all exact ((eq_of_heq hc.symm) :))
  subst ec
  exact (by with_unfolding_all exact ((brgStd_copy0 Z Z' hX U Xg' tr' c.Q.c.F (fun y => (y : ℂ)) i ((i')) ((hi)) ((hi')) R ((R')) ((hR)) h) : _))

variable {Z₀ : w.Lt} {hX : B.fields.Ok} {Wt : Set B.places.Pl} {z₀ : Dat (w.st Z₀) w.I hX T Wt} {q : RowPk w z₀} {o : q.Over}

set_option maxHeartbeats 2000000 in

theorem mL_all (m : Moved o) (i : Fin (w.st o.Z).toD7.R.m) (a : w.I.ι) :
    q.p.mL a ((i : ℕ) + 1) =
      lMat (D := (w.st o.Z).toD7) (famR (w.st o.Z) w.I hX Set.univ m.z.Xg m.z.tr).A (lev0 w.I) (chr0 w.I) i (tAll w.I a) := by
  have h := mLU_eq Z₀ o.Z hX m.Xg m.tr a i
  have h' := q.mL a ((i : ℕ) + 1)
  exact (by with_unfolding_all exact ((eq_of_heq ((heq_of_eq h').trans h)) :))

set_option maxHeartbeats 4000000 in

def allT (h : o.Fits) (m : Moved o) (s : Side0 o) :
    AllT (w.st o.Z).toD7 (famR (w.st o.Z) w.I hX Set.univ m.z.Xg m.z.tr).A (lev0 w.I) (chr0 w.I) (lev1 w.I) (chr1 w.I) s.p0
      (tAll w.I) (m.z.R.eG.trans m.z.cG) where
  jA μ := (by with_unfolding_all exact ((m.t.tA true μ).j :))
  jA0 μ := (by with_unfolding_all exact ((m.t.tA false μ).j :))
  eMt i μ := (by with_unfolding_all exact ((castEq (mL_all m i μ)) :))
  formsA μ := (by with_unfolding_all exact ((m.t.tA true μ).forms :))
  latA μ := (by with_unfolding_all exact ((m.t.tA true μ).latT :))
  formsAtBottomLevel μ := (by with_unfolding_all exact ((m.t.tA false μ).forms :))
  latA0 μ := (by with_unfolding_all exact ((m.t.tA false μ).latT :))
  formsL i μ := (by with_unfolding_all exact ((forms_cast (mL_all m i μ) (q.p.tL μ ((i : ℕ) + 1))) :))
  latL i μ := (by with_unfolding_all exact ((lat_cast (mL_all m i μ) (q.p.tL μ ((i : ℕ) + 1))) :))
  cen μ z a ha := by
    have hs := stdIso_dat m.z
    have hc := h.cen _ hs
    let z' : Subalgebra.center ℂ (MonoidAlgebra ℂ (Gc B w.px)) := Bare.cenPull (m.z.R.eG.trans m.z.cG) z
    have hz := Bare.coeff_cenPull (m.z.R.eG.trans m.z.cG) z
    have ha' : ∀ g, (w.st o.Z).toD7.what₂.embLL (a.coeff g) = (z' : MonoidAlgebra ℂ (Gc B w.px)).coeff g :=
      fun g => (ha g).trans (hz g).symm
    refine ⟨fun x => ?_, fun x => ?_, fun i x => ?_⟩
    · have h1 := hc.amb μ ((by with_unfolding_all exact (z :))) z' ((by with_unfolding_all exact (hz :))) ((m.t.tA true μ).j ((by with_unfolding_all exact (x :))))
      have h2 := (m.t.tA true μ).cen z' a ha' ((by with_unfolding_all exact (x :)))
      exact (by with_unfolding_all exact ((eq_of_heq ((heq_of_eq h1).trans (heq_of_eq h2))) :))
    · have h1 := s.is _ hs μ ((by with_unfolding_all exact (z :))) z' ((by with_unfolding_all exact (hz :))) ((m.t.tA false μ).j ((by with_unfolding_all exact (x :))))
      have h2 := (m.t.tA false μ).cen z' a ha' ((by with_unfolding_all exact (x :)))
      exact (by with_unfolding_all exact ((eq_of_heq ((heq_of_eq h1).trans (heq_of_eq h2))) :))
    · have h1 := hc.mt μ ((i : ℕ) + 1) ((by with_unfolding_all exact (z :))) z' ((by with_unfolding_all exact (hz :))) ((q.p.tL μ ((i : ℕ) + 1)).j (castEq (mL_all m i μ) ((by with_unfolding_all exact (x :)))))
      have h2 := cen_cast (mL_all m i μ) (q.p.tL μ ((i : ℕ) + 1)) z' ((by with_unfolding_all exact (a :))) ((by with_unfolding_all exact (ha' :))) ((by with_unfolding_all exact (x :)))
      exact (by with_unfolding_all exact ((h1.trans h2) :))

set_option maxHeartbeats 2000000 in

theorem jA_same (h : o.Fits) {m : Moved o} {s : Side0 o} (r : ReadPk m s) (t) :
    SameOn ((allT h m s).jA (r.Y.tup t)) (r.Y.jA t) := (by with_unfolding_all exact ((sameOn_tie (mAU (w.st o.Z) w.I hX m.z.Xg m.z.tr true) (q.p.sA true) (m.t.tA true) (congrFun r.tup t) (m.t.hA true t)
    (((r.Y.jA t))) (((r.jA t)))) : _))

set_option maxHeartbeats 2000000 in

theorem rowReading_baseLevel_sameOn_allTuples (h : o.Fits) {m : Moved o} {s : Side0 o} (r : ReadPk m s) (t) :
    SameOn ((allT h m s).jA0 (r.Y.tup t)) (r.Y.jA0 t) := (by with_unfolding_all exact ((sameOn_tie (mAU (w.st o.Z) w.I hX m.z.Xg m.z.tr false) (q.p.sA false) (m.t.tA false) (congrFun r.tup t) (m.t.hA false t)
    (((r.Y.jA0 t))) (((r.jA0 t)))) : _))

set_option maxHeartbeats 2000000 in

theorem eMt_same (h : o.Fits) {m : Moved o} {s : Side0 o} (r : ReadPk m s) (i : Fin (w.st o.Z).toD7.R.m) (t) :
    SameOn ((allT h m s).eMt i (r.Y.tup t)) (r.Y.eMt i t) := (by with_unfolding_all exact ((sameOn_cast (fun a => q.p.mL a ((i : ℕ) + 1)) (congrFun r.tup t) (mL_all m i (r.Y.tup t)) (m.t.hL i t)
    (fun x => (by with_unfolding_all exact ((r.Y.eMt i t ((x))) : _))) ((by with_unfolding_all exact ((r.eMt i t) :)))) :))

set_option maxHeartbeats 2000000 in

theorem crd_moved (h : o.Fits) (m : Moved o) (s : Side0 o) (a : w.C.Tup) (y) :
    IsCrd w.I hX a (q.per.e a)
      (rowForm (D := (w.st o.Z).toD7) (famR (w.st o.Z) w.I hX Set.univ m.z.Xg m.z.tr).A (lev1 w.I) (chr1 w.I) (tAll w.I a) y)
      ((allT h m s).jA a y) := (by with_unfolding_all exact ((crd_eq Z₀ hX m.Xg m.tr a (q.p.sA true a).A (q.per.e a) (q.t.tA true a).j (((m.t.tA true a).j)) (((m.tA true a)))
    (q.per.crd a) ((y))) : _))

set_option maxHeartbeats 2000000 in

theorem io_junk {m : Moved o} {s : Side0 o} (r : ReadPk m s) (μ : (w.D o.Z).what₂.Tup) (h : ¬ Used0 (w.D o.Z) μ) (b : Bool) (j : ℕ) :
    (q.p.ch b).io μ j = 0 := by
  refine (m.t.ch b).junk μ (fun hu => h ?_) j
  rcases hu with hu | ⟨v, hu⟩
  · exact Or.inl hu
  · exact Or.inr ⟨v, hu.trans ((congrFun r.tup _).symm.trans (r.Y.muAt v).symm)⟩

set_option maxHeartbeats 2000000 in

theorem std_moved {m : Moved o} (c : m.Copy) (h : z₀.Std) : m.z.Std :=
  brgStd_copy Z₀ o.Z hX _ m.Xg m.tr z₀.core m.z.core z₀.alg m.z.alg z₀.alg_eq m.z.alg_eq z₀.R m.z.R ((by with_unfolding_all exact (c.core :))) ((by with_unfolding_all exact (c.R :))) h

set_option maxHeartbeats 4000000 in

theorem rxs_of_state : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), K.Over B.toPre → Forced K B T →
    pinAnd HasPk K B f T w → ∀ (P : Pre2 K w) (x : St P) (hη : ∀ j v, 1 ≤ j → j ≤ B.R.m → x.o.η j v = P.q.eta j v), ∀ t : RowsT K w x.o.Z P.Wt x.s.p0, t.r = x.rowsAre hη → Nonempty (RXs t) := by
  intro K B f T w _ _ _ P x hη t ht
  have key : ∀ (r : R3.RowsAre (w.st x.o.Z) w.I P.hX T P.Wt (Equiv.refl _) x.s.p0), x.rowsAre hη = r →
      ∀ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12,
        Nonempty (RXs (⟨P.hX, r, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ : RowsT K w x.o.Z P.Wt x.s.p0)) := ?_
  · exact key t.r ht.symm t.exAt t.inGeo t.grpAt t.grp t.mu t.exact t.untw t.emt0 t.emt t.etaF t.rowInt t.idx
  intro r hr
  induction hr
  intro h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  have hc := x.m.core P.core
  exact ⟨{
    all := (by with_unfolding_all exact ((allT x.fits x.m x.s) :))
    jA_use := (by with_unfolding_all exact ((jA_same x.fits x.r) :))
    movedReadingSameMaps_baseReading_agrees := (by with_unfolding_all exact ((rowReading_baseLevel_sameOn_allTuples x.fits x.r) :))
    eMt_use := (by with_unfolding_all exact ((eMt_same x.fits x.r) :))
    e := P.q.per.e
    eMt0 := P.q.per.ref
    eMtTw := P.q.per.tw
    crd := (by with_unfolding_all exact ((crd_moved x.fits x.m x.s) :))
    io := fun μ j h => ⟨io_junk x.r μ h true j, io_junk x.r μ h false j⟩
    sha := P.q.sha
    laws := (by with_unfolding_all exact (hc.1 :))
    canon := (by with_unfolding_all exact (hc.2.1 :))
    rank := (by with_unfolding_all exact (hc.2.2.1 :))
    pb := (by with_unfolding_all exact (hc.2.2.2 :))
    std := (by with_unfolding_all exact ((std_moved x.copy P.std) :)) }⟩

end GlobalTheory.Mem.R3.Rw.Ties

end
