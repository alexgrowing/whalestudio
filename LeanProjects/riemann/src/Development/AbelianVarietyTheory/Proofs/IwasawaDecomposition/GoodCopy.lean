import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsReadingInMovedRowData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSideReadingLevelZeroMoved
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowIdentificationsRealRowSideOfChainComparison
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIdentificationTypeRepresentativesClasses
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowBasisCongruenceLengthsOtherLaterStages
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHermPosChainRealEndSpaceTuple
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.CopyRead

section Copy

variable {B : Base} {C : Cols B} {a : Late B C} (b : Late B C) {px : PreX B.toPre} {I : ColIn B px} {hX : B.fields.Ok} {T : TwDat B}
  {Wt : Set B.places.Pl}

def cpR (z : Dat a.st I hX T Wt) :
    @RealDat3 b.st.toD7 _ _ _ _ _ _ (famR b.st I hX (usedOf I T Wt) z.Xg z.tr) (coreJ b z.core).Q.c.F _ _ ((by exact @alg B C a b (↥(@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (@Formalism.HC.HostRaw.instField (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (@Formalism.HC.HostRaw.instNF (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (Formalism.L2.Pj.instCMHost (@Late.st B C a).toD7) (@Formalism.L2.Pj.Par.H (@Late.st B C a).toD7 (@Formalism.L2.Pj.Core.Q (@Late.st B C a).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))) (@Formalism.L2.Pj.Par.l (@Late.st B C a).toD7 (@Formalism.L2.Pj.Core.Q (@Late.st B C a).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))) (@Formalism.L2.Pj.Par.c (@Late.st B C a).toD7 (@Formalism.L2.Pj.Core.Q (@Late.st B C a).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))))) (@IntermediateField.toField Rat Complex Rat.instField Complex.instField (@DivisionRing.toRatAlgebra Complex (@Field.toDivisionRing Complex Complex.instField) Complex.instCharZero) (@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (@Formalism.HC.HostRaw.instField (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (@Formalism.HC.HostRaw.instNF (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (Formalism.L2.Pj.instCMHost (@Late.st B C a).toD7) (@Formalism.L2.Pj.Par.H (@Late.st B C a).toD7 (@Formalism.L2.Pj.Core.Q (@Late.st B C a).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))) (@Formalism.L2.Pj.Par.l (@Late.st B C a).toD7 (@Formalism.L2.Pj.Core.Q (@Late.st B C a).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))) (@Formalism.L2.Pj.Par.c (@Late.st B C a).toD7 (@Formalism.L2.Pj.Core.Q (@Late.st B C a).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))))) (@Dat.alg (@Late.st B C a) px I hX T Wt z))) :=
  (by with_unfolding_all exact ((real3 b (iK := z.alg) z.R) :))

set_option maxHeartbeats 2000000 in

theorem rrT_copy (z₀ : Dat a.st I hX T Wt) (z : Dat b.st I hX T Wt) (h1 : z.Xg = z₀.Xg) (h2 : z.tr = z₀.tr)
    (h3 : HEq z.core (coreJ b z₀.core)) (h4 : HEq z.R (real3 b (iK := z₀.alg) z₀.R)) (y₀ : Hd z₀.R.toRealDat) (bb : Bool) (E : Hs)
    (jE : E.T →ₗ[ℂ] (y₀.C z₀.F.lv2).Amb 0) (n : ℕ) (c : Module.Basis (Fin n) ℂ E.T)
    (Xo : InfinitePlace B.LL → Matrix (Fin n) (Fin n) ℂ) (h : RrT z₀.F y₀ bb jE n c Xo) :
    ∀ (y : Hd z.R.toRealDat) (jE' : E.T →ₗ[ℂ] (y.C z.F.lv2).Amb 0), HEq jE' jE → RrT z.F y bb jE' n c Xo := by
  obtain @⟨Xg, tr, core, al, alg_eq, R, cG, geo, pins, lev, idG, good, mu, l1, l2⟩ := z
  dsimp only at h1 h2 h3 h4
  subst h1 h2
  obtain rfl : core = coreJ b z₀.core := eq_of_heq h3
  have e : al = (by with_unfolding_all exact ((alg b z₀.alg) :)) := by
    refine Algebra.algebra_ext _ _ fun y => B.embLL.injective ?_
    exact (alg_eq y).trans ((by with_unfolding_all exact ((z₀.alg_eq ((y))).symm : _)))
  subst e
  obtain rfl : R = cpR b z₀ := eq_of_heq (h4.trans ((by with_unfolding_all exact ((HEq.refl (cpR b z₀)) :))))
  intro y jE' hj
  exact (by with_unfolding_all exact (((@rr_eta_tr B C a b _ _ _ _ _ _ _ _ _ z₀.alg _ z₀.R z₀.F).2 y₀ ((y)) bb E jE ((jE')) n c ((Xo)) ((hj)) h) : _))

end Copy

set_option maxHeartbeats 1000000 in

theorem coords {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}
    {Y : Read (A3 := A3) R.toRealDat F.lv2 X0} (Z : RationalReadingWithoutCongruence R F X0 Y) (y : Hd R.toRealDat)
    (heq_eigen_embedding_zero : D.what₂.EE0 →ₗ[ℂ] (y.C F.lv2).Amb 0) (hinj : Function.Injective heq_eigen_embedding_zero) (n : ℕ) (c : Module.Basis (Fin n) ℂ D.what₂.EE0)
    (Xo : InfinitePlace D.what₂.LL → Matrix (Fin n) (Fin n) ℂ) (h : RrT F y false (E := ⟨D.what₂.EE0⟩) heq_eigen_embedding_zero n c Xo)
    (hz : ∀ v, HEq (Y.Iz.jE v).1 (heq_eigen_embedding_zero v)) :
    ∃ ε : X0.s.RR.V ≃ₗ[D.what₂.LL] (Fin n → D.what₂.LL), (∀ x, X0.s.jEE x = ∑ i, D.what₂.embLL (ε x i) • c i) ∧
      ∀ v, v ≠ A3.A.v0 → ∀ x x', Formalism.HermitianLatticesTheory.majAt X0.s.RR.b X0.s.RR.X v x x' =
        Formalism.HermitianLatticesTheory.majAt (Pi.basisFun D.what₂.LL (Fin n)) Xo v (ε x) (ε x') := by
  obtain ⟨rfl, a0, b0⟩ := h
  refine ⟨Z.eRR0.symm, fun x => hinj ?_, fun v hv x x' => ?_⟩
  · have h := Z.jEE0 (Z.eRR0.symm x)
    rw [Z.eRR0.apply_symm_apply] at h
    exact (eq_of_heq (hz _)).symm.trans (h.trans (a0 (Z.eRR0.symm x)).symm)
  · have h := Z.met0 v hv (Z.eRR0.symm x) (Z.eRR0.symm x')
    rw [Z.eRR0.apply_symm_apply, Z.eRR0.apply_symm_apply] at h
    exact h.trans (GoodSideLattices.majAt_cast rfl _ Xo v (b0 v).1 _ _).symm

variable {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z₀ : w.Lt} {hX : B.fields.Ok} {Wt : Set B.places.Pl}
  {z₀ : Dat (w.st Z₀) w.I hX T Wt} {q : RowPk w z₀}

set_option maxHeartbeats 1000000 in

theorem RRset_two {o o' : q.Over} (s : Side0 o) (s' : Side0 o') (μ : (w.D o.Z).what₂.Tup) :
    s.p0.s.RRset μ = (s'.p0.s.RRset μ) := by
  have h : ∀ k, s.p0.s.downTo μ k = (by with_unfolding_all exact ((s'.p0.s.downTo ((μ)) k) : _)) := by
    intro k
    induction k with
    | zero => exact (by with_unfolding_all exact ((Eq.refl (s.p0.s.downTo μ 0)) :))
    | succ k ih => exact (by with_unfolding_all exact ((congrArg (fun φ : type_of% (s.p0.s.downTo μ k) => φ.comp (s.p0.s.io μ k)) ih) :))
  have hi := congrArg (fun φ : type_of% (s.p0.s.downTo μ (w.D o.Z).R.m) =>
    (s.p0.s.multZero μ).toLinearEquiv.toLinearMap ∘ₗ φ ∘ₗ (s.p0.s.multTop μ).symm.toLinearEquiv.toLinearMap) (h (w.D o.Z).R.m)
  exact (by with_unfolding_all exact ((congrArg (fun φ : s.p0.s.Amb μ →ₗ[ℂ] (w.D o.Z).what₂.EE0 =>
    φ '' ((fun x => (s.p0.s.V0 μ ⊓ (s.p0.s.V0 μ ⊓ LinearMap.ker φ)ᗮ).starProjection x) ''
      ((s.p0.s.Mtilde μ).carrier ∩ (s.p0.s.V0 μ : Set (s.p0.s.Amb μ))))) hi) :))

set_option maxHeartbeats 1000000 in

theorem rrT_moved {o : q.Over} (m : Moved o) (hc : m.Copy) (hco : m.Coh) (b : Bool) {n c Xo}
    (h : RrT z₀.F q.y b (q.t.ch b).jE n c Xo) : RrT m.z.F m.y b (m.t.ch b).jE n c Xo :=
  rrT_copy (B := B) (C := w.C) (a := Z₀) o.Z z₀ m.z m.Xg m.tr ((by with_unfolding_all exact (hc.core :))) ((by with_unfolding_all exact (hc.R :))) q.y b _ _ n c Xo h m.y _ (hco.jE b)

theorem lat_tr {K : Type} [Field K] [NumberField K] [StarRing K] (e : K →+* ℂ) {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] {n : ℕ} (c : Module.Basis (Fin n) ℂ V) (Xo : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ)
    {ι : Type} (P : ι → HeightOneSpectrum (𝓞 K)) {S S' : ι → Set V} (hS : S = S') {RR RR' : HLat K} (hR : RR' = RR)
    {j : RR.V →ₛₗ[e] V} {j' : RR'.V →ₛₗ[e] V} (hj : HEq j' j)
    (h : ∃ ε : RR.V ≃ₗ[K] (Fin n → K), (∀ x, j x = ∑ i, e (ε x i) • c i) ∧
      (∀ v, v ≠ InfinitePlace.mk e → ∀ x x', Formalism.HermitianLatticesTheory.majAt RR.b RR.X v x x' =
        Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) Xo v (ε x) (ε x')) ∧
      ∀ x : RR.V, x ∈ RR.L ↔ ∀ u, ∃ d : 𝓞 K, d ∉ (P u).asIdeal ∧ d • x ∈ Submodule.span (𝓞 K) {z | j z ∈ S u}) :
    ∃ ε : RR'.V ≃ₗ[K] (Fin n → K), (∀ x, j' x = ∑ i, e (ε x i) • c i) ∧
      (∀ v, v ≠ InfinitePlace.mk e → ∀ x x', Formalism.HermitianLatticesTheory.majAt RR'.b RR'.X v x x' =
        Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) Xo v (ε x) (ε x')) ∧
      ∀ x : RR'.V, x ∈ RR'.L ↔ ∀ u, ∃ d : 𝓞 K, d ∉ (P u).asIdeal ∧ d • x ∈ Submodule.span (𝓞 K) {z | j' z ∈ S' u} := by
  subst hS hR
  cases hj
  exact h

set_option maxHeartbeats 2000000 in

theorem good_copy {K : Ctx} {P : Pre2 K w} (x : St P) (N : NStage B w.C (P.q.W x.o.η x.o.hη)) (m : Moved (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over)) (hc : m.Copy)
    (hco : m.Coh) (s : Side0 (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over)) (hR : s.RR = x.s.RR) (hj : HEq s.jEE x.s.jEE) : GoodSideLattices.Good m s := by
  obtain ⟨n, c, Xo, h⟩ := rrT_exists (w.st P.Z₀).toD7 (Gc B w.px) (PlS B w.px) (PlI B w.px) (TupU w.I (usedOf w.I T P.Wt))
    (famR (w.st P.Z₀) w.I P.hX (usedOf w.I T P.Wt) P.z.Xg P.z.tr) P.z.core.Q.c.F P.z.R P.z.F P.z.cG P.z.pins P.intersectionNumber_baseChange P.q.y false
    (P.q.p.ch false).EE (P.q.t.ch false).jE (P.q.t.ch false).jE_inj (P.q.t.ch false).jE_range
  have h0 := rrT_moved x.m x.copy x.coh false h
  have h1 := rrT_moved m hc hco false h
  have h2 := coords x.r.Z x.m.y ((by with_unfolding_all exact ((x.m.t.ch false).jE :))) ((by with_unfolding_all exact ((x.m.t.ch false).jE_inj :))) n ((by with_unfolding_all exact (c :))) ((by with_unfolding_all exact (Xo :))) ((by with_unfolding_all exact (h0 :))) ((by with_unfolding_all exact (x.pin.heq_eigen_embedding_zero :)))
  obtain ⟨ε, h2, h3⟩ := h2
  have h4 : (fun u : B.places.Pl => ((by with_unfolding_all exact ((x.s.p0.s.RRset ((w.D x.o.Z).what₂.muAt u)) :)) : Set (P.q.p.ch false).EE.T)) =
      fun u => (by with_unfolding_all exact ((s.p0.s.RRset ((w.D (RowPk.Over.Z (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over))).what₂.muAt u)) :)) :=
    funext fun u => (by with_unfolding_all exact ((RRset_two x.s s ((w.D x.o.Z).what₂.muAt u)) :))
  have h5 := lat_tr (K := B.LL) B.embLL c Xo ((by with_unfolding_all exact ((fun u : B.places.Pl => (w.D x.o.Z).plEq u) :))) h4 hR hj
    ⟨(by with_unfolding_all exact (ε :)), (by with_unfolding_all exact (h2 :)), (by with_unfolding_all exact (h3 :)), (by with_unfolding_all exact (x.r.Z.rr0 :))⟩
  obtain ⟨ε', k1, k2, k3⟩ := h5
  exact ⟨n, c, Xo, ε', h1, k1, k2, (by with_unfolding_all exact (k3 :))⟩

end GlobalTheory.Mem.R3.Rw.CopyRead

end
