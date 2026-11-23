import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.IndefiniteReal.CxCore
import Formalism.LocalToGlobal.IndefiniteReal.LiftGoodPartComplexEqRange
import Formalism.LocalToGlobal.IndefiniteReal.BridgeLemmas
import Formalism.LocalToGlobal.IndefiniteReal.ArithLemmas
import Formalism.LocalRingCardinality.HeightBoundGeFourthPowerRank

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.Links

namespace Tw

variable {s : Bool} {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem adjoint_map [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] (f : E →ₗ[ℂ] F) :
    LinearMap.adjoint (Tw.map s f) = Tw.map s (LinearMap.adjoint f) := by
  symm
  rw [LinearMap.eq_adjoint_iff]
  intro x y
  show cj s (inner ℂ (LinearMap.adjoint f (out x)) (out y)) = cj s (inner ℂ (out x) (f (out y)))
  rw [LinearMap.adjoint_inner_left]

theorem linInd' (s : Bool) {ι : Type} {v : ι → E} (h : LinearIndependent ℂ v) :
    LinearIndependent ℂ fun i => mk s (v i) := by
  rw [linearIndependent_iff'] at h ⊢
  intro u g hg i hi
  have h1 : ∑ i ∈ u, cj s (g i) • v i = 0 := hg
  have := congrArg (cj s) (h u (fun i => cj s (g i)) h1 i hi)
  rwa [cj_cj, map_zero] at this

theorem mk_smul (s : Bool) (c : ℂ) (y : E) : mk s (c • y) = cj s c • mk s y := by
  show c • y = cj s (cj s c) • y
  rw [cj_cj]

theorem span_top' (s : Bool) {ι : Type} {v : ι → E} (h : Submodule.span ℂ (Set.range v) = ⊤) :
    Submodule.span ℂ (Set.range fun i => mk s (v i)) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hx : out x ∈ Submodule.span ℂ (Set.range v) := h ▸ Submodule.mem_top
  change mk s (out x) ∈ _
  generalize out x = y at hx ⊢
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    exact Submodule.subset_span ⟨i, rfl⟩
  | zero => exact Submodule.zero_mem _
  | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
  | smul c y _ hy =>
    rw [mk_smul]
    exact Submodule.smul_mem _ _ hy

end Tw

section Semi

variable {K V W : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W] {σ : K →+* ℂ}

theorem span_semi (f : V →ₛₗ[σ] W) {κ : Type} (c : Module.Basis κ K V) :
    Submodule.span ℂ (Set.range fun i => f (c i)) = Submodule.span ℂ (Set.range f) := by
  apply le_antisymm
  · exact Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨c i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    have hx : x ∈ Submodule.span K (Set.range c) := c.span_eq ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact Submodule.subset_span ⟨i, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
    | smul a y _ hy => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hy

theorem linInd_semi (f : V →ₛₗ[σ] W) {ι ι' : Type} [Finite ι] (b : Module.Basis ι K V) (b' : Module.Basis ι' K V)
    (h : LinearIndependent ℂ fun i => f (b i)) : LinearIndependent ℂ fun i => f (b' i) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  have : FiniteDimensional K V := Module.Finite.of_basis b
  have : Finite ι' := Module.Finite.finite_basis b'
  have : Fintype ι' := Fintype.ofFinite ι'
  rw [linearIndependent_iff_card_eq_finrank_span] at h ⊢
  unfold Set.finrank at h ⊢
  rw [span_semi f b']
  rw [span_semi f b] at h
  rw [← h]
  exact (Module.finrank_eq_card_basis b').symm.trans (Module.finrank_eq_card_basis b)

theorem kForm_semi {H X : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup X] [Module ℂ X] (g : V →ₛₗ[σ] H)
    (e : H →ₗ[ℂ] X) (f : V →ₛₗ[σ] X) (hj : ∀ x, e (g x) = f x) (hinj : Function.Injective e)
    (hrange : LinearMap.range e = Submodule.span ℂ (Set.range f)) {ι ι' : Type} [Finite ι] (b : Module.Basis ι K V) (b' : Module.Basis ι' K V)
    (h : LinearIndependent ℂ fun i => f (b i)) :
    LinearIndependent ℂ (fun i => g (b' i)) ∧ Submodule.span ℂ (Set.range fun i => g (b' i)) = ⊤ := by
  refine ⟨LinearIndependent.of_comp e ?_, ?_⟩
  · have e1 : (e ∘ fun i => g (b' i)) = fun i => f (b' i) := funext fun i => hj _
    rw [e1]
    exact linInd_semi f b b' h
  · apply Submodule.map_injective_of_injective hinj
    rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, hrange]
    have e1 : (e ∘ fun i => g (b' i)) = fun i => f (b' i) := funext fun i => hj _
    rw [e1, span_semi f b']

end Semi

theorem hMod_exists {X : Type} [AddCommGroup X] [Module ℂ X] (V : Submodule ℂ X) [FiniteDimensional ℂ V]
    (ip : X → X → ℂ) (hadd : ∀ x ∈ V, ∀ y ∈ V, ∀ z ∈ V, ip (x + y) z = ip x z + ip y z)
    (hsm : ∀ (c : ℂ), ∀ x ∈ V, ∀ y ∈ V, ip (c • x) y = star c * ip x y)
    (hsym : ∀ x ∈ V, ∀ y ∈ V, star (ip y x) = ip x y) (hpos : ∀ x ∈ V, 0 ≤ (ip x x).re)
    (hdef : ∀ x ∈ V, ip x x = 0 → x = 0) : ∃ M : HMod X, M.Is V ip := by
  let core : InnerProductSpace.Core ℂ V :=
    { inner := fun x y => ip x y
      conj_inner_symm := fun x y => hsym x x.2 y y.2
      re_inner_nonneg := fun x => hpos x x.2
      add_left := fun x y z => hadd x x.2 y y.2 z z.2
      smul_left := fun x y r => hsm r x x.2 y y.2
      definite := fun x h => Subtype.ext (hdef x x.2 h) }
  letI : NormedAddCommGroup V := core.toNormedAddCommGroup
  letI : InnerProductSpace ℂ V := InnerProductSpace.ofCore core.toCore
  exact ⟨{ H := V, fH := ‹FiniteDimensional ℂ V›, e := V.subtype }, V.injective_subtype, V.range_subtype, fun _ _ => rfl⟩

theorem vw_root {K : Type} [Field K] [NumberField K] [StarRing K] (w : HeightOneSpectrum (𝓞 K)) (a : K) (n : ℕ) (hn : 0 < n)
    (h : a ^ n = 1) : Formalism.DivisionValues.vw w a = 0 := by
  have h1 : (n : ℤ) * Formalism.DivisionValues.vw w a = 0 := by
    unfold Formalism.DivisionValues.vw
    rw [← FractionalIdeal.count_pow, FractionalIdeal.spanSingleton_pow, h, FractionalIdeal.spanSingleton_one,
      FractionalIdeal.count_one]
  exact (mul_eq_zero.1 h1).resolve_left (by exact_mod_cast hn.ne')

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Links

open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

namespace RealDat

variable {R : RealDat D A Ks} {F : Face D A}

set_option maxHeartbeats 1000000 in
theorem kFormR_of (hM : R.IsModels) : (R.toCx F).KFormR := by
  intro t
  have hB := Formalism.IndefR.Bridge.ClassPres.extBij_holds (R.B.R t).pres
  obtain ⟨hinj, hrange, -⟩ := hM.HX t
  have h := kForm_semi (R.jX t) (R.HX t).e (R.B.R t).pres.extL (fun x => hM.jX t x) hinj (hrange.trans hB.2.symm)
    (Formalism.L2.DIV.CSD.basis _) (Module.Basis.ofVectorSpace _ _) hB.1
  exact ⟨Tw.linInd' (E := (R.HX t).H) _ h.1, Tw.span_top' (E := (R.HX t).H) _ h.2⟩

set_option maxHeartbeats 1000000 in
theorem kFormL_of (hM : R.IsModels) : (R.toCx F).KFormL := by
  intro i t
  have hB := Formalism.IndefR.Bridge.ClassPres.extBij_holds (R.B.L i t).pres
  obtain ⟨hinj, hrange, -⟩ := hM.HV i t
  have h := kForm_semi (R.jV i t) (R.HV i t).e (R.B.L i t).pres.extL (fun x => hM.jV i t x) hinj (hrange.trans hB.2.symm)
    (Formalism.L2.DIV.CSD.basis _) (Module.Basis.ofVectorSpace _ _) hB.1
  exact ⟨Tw.linInd' (E := (R.HV i t).H) _ h.1, Tw.span_top' (E := (R.HV i t).H) _ h.2⟩

set_option maxHeartbeats 1000000 in

theorem jIsoR_gen (hM : R.IsModels) (cv : CrdV A.fam.amb)
    (hcv : ∀ t x y, cv.hR t x y = (A.fam.R t).S.csum ((x : (A.fam.R t).S.Forms) : (A.fam.R t).S.Cl → (A.fam.R t).S.V) ((y : (A.fam.R t).S.Forms) : (A.fam.R t).S.Cl → (A.fam.R t).S.V)) :
    (R.toCx F).JIsoR cv := by
  intro t x y
  have key : cj (twAt D.what₂.embLL A.v0) (inner ℂ (R.jX t x) (R.jX t y)) =
      A.v0.embedding ((A.fam.R t).S.csum ((x : (A.fam.R t).S.Forms) : (A.fam.R t).S.Cl → (A.fam.R t).S.V) ((y : (A.fam.R t).S.Forms) : (A.fam.R t).S.Cl → (A.fam.R t).S.V)) := by
    rw [(hM.HX t).2.2, hM.jX, hM.jX, R.emb0]
    congr 1
    exact Formalism.IndefR.Bridge.ClassPres.isom_holds (R.B.R t).pres x y
  rw [hcv]
  exact key

theorem jIsoR_of (hM : R.IsModels) : (R.toCx F).JIsoR (cvOf A F.P0 F.ψ0 F.P1 F.ψ1) :=
  jIsoR_gen hM _ fun _ _ _ => rfl

set_option maxHeartbeats 1000000 in

theorem jIsoL_gen (hM : R.IsModels) (cv : CrdV A.fam.amb)
    (hcv : ∀ i t x y, cv.hL i t x y = (A.fam.L i t).S.csum ((x : (A.fam.L i t).S.Forms) : (A.fam.L i t).S.Cl → (A.fam.L i t).S.V) ((y : (A.fam.L i t).S.Forms) : (A.fam.L i t).S.Cl → (A.fam.L i t).S.V)) :
    (R.toCx F).JIsoL cv := by
  intro i t x y
  have key : cj (twAt D.what₂.embLL A.v0) (inner ℂ (R.jV i t x) (R.jV i t y)) =
      A.v0.embedding ((A.fam.L i t).S.csum ((x : (A.fam.L i t).S.Forms) : (A.fam.L i t).S.Cl → (A.fam.L i t).S.V) ((y : (A.fam.L i t).S.Forms) : (A.fam.L i t).S.Cl → (A.fam.L i t).S.V)) := by
    rw [(hM.HV i t).2.2, hM.jV, hM.jV, R.emb0]
    congr 1
    exact Formalism.IndefR.Bridge.ClassPres.isom_holds (R.B.L i t).pres x y
  rw [hcv]
  exact key

theorem jIsoL_of (hM : R.IsModels) : (R.toCx F).JIsoL (cvOf A F.P0 F.ψ0 F.P1 F.ψ1) :=
  jIsoL_gen hM _ fun _ _ _ _ => rfl

theorem prod_lamN (t : T) (p : A.fam.base.Ix) :
    ∏ j ∈ Finset.Icc 1 D.R.m, R.lamN t j p = ∏ j : Fin D.R.m, R.lam j t p A.v0 := by
  have h1 : ∀ n : ℕ, ∀ g : ℕ → ℝ, ∏ j ∈ Finset.Icc 1 n, g j = ∏ j ∈ Finset.range n, g (j + 1) := by
    intro n g
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.prod_Icc_succ_top (by omega), ih, Finset.prod_range_succ]
  rw [h1, ← Fin.prod_univ_eq_prod_range]
  refine Finset.prod_congr rfl fun j _ => ?_
  unfold lamN
  rw [dif_pos (by simp)]
  exact congrArg (fun k => R.lam k t p A.v0) (Fin.ext (Nat.add_sub_cancel _ _))

set_option maxHeartbeats 1000000 in
theorem thmAop_of (h : ∀ i t, Lift.IsLamP (R.thG i t) (LinearMap.adjoint (R.thG i t)) (R.Wp i) fun p => R.lam i t p A.v0)
    (b : Bool) : (R.toCx F).ThmAop b := by
  intro j t p w hw
  have hw1 : Tw.out (s := twAt D.what₂.embLL A.v0) (E := (R.HW j (sg0 D A)).H) w ∈ R.Wp j p := hw.1
  have key : Tw.map (twAt D.what₂.embLL A.v0) (R.thG j t) (LinearMap.adjoint (Tw.map (twAt D.what₂.embLL A.v0) (R.thG j t)) w) =
      ((R.lam j t p A.v0 : ℝ) : ℂ) • w := by
    rw [Tw.adjoint_map]
    show Tw.mk _ (R.thG j t (LinearMap.adjoint (R.thG j t) (Tw.out (s := twAt D.what₂.embLL A.v0) (E := (R.HW j (sg0 D A)).H) w))) = _
    rw [h j t p _ hw1, Tw.mk_smul, cj_ofReal]
    rfl
  exact key

set_option maxHeartbeats 1000000 in
theorem thmBop_of (h : Lift.IsKap D.R.m (fun t => R.Th t ∘ₗ LinearMap.adjoint (R.Th t)) R.EEp R.lamN R.kap) (b : Bool) :
    (R.toCx F).ThmBop b := by
  intro t p e he
  have he1 : Tw.out (s := twAt D.what₂.embLL A.v0) (E := R.HE.H) e ∈ R.EEp p := he.1
  have key : Tw.map (twAt D.what₂.embLL A.v0) (R.Th t) (LinearMap.adjoint (Tw.map (twAt D.what₂.embLL A.v0) (R.Th t)) e) =
      ((R.kap * ∏ j : Fin D.R.m, R.lam j t p A.v0 : ℝ) : ℂ) • e := by
    rw [Tw.adjoint_map]
    show Tw.mk _ (R.Th t (LinearMap.adjoint (R.Th t) (Tw.out (s := twAt D.what₂.embLL A.v0) (E := R.HE.H) e))) = _
    have h2 := h t p (Tw.out (s := twAt D.what₂.embLL A.v0) (E := R.HE.H) e) he1
    rw [LinearMap.comp_apply] at h2
    rw [h2, Tw.mk_smul, cj_ofReal, prod_lamN]
    rfl
  exact key

theorem zetaOK_of (Y : RealCol R F) (hY : Y.Char) : (R.toCx F).ZetaOK (fc := F.fc) Y.ζ := by
  refine ⟨hY.zeta0, fun u t h0 => ?_, fun u w => ?_⟩
  · obtain ⟨n, hn, h⟩ := hY.zeta u t
    rw [h0, zero_pow hn.ne'] at h
    exact zero_ne_one h
  · obtain ⟨n, hn, h⟩ := hY.zeta u ((R.toCx F).μ w)
    exact vw_root w _ n hn h

end RealDat

end Links

section Prim

open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

namespace RealDat

variable (R : RealDat D A Ks) (F : Face D A)

abbrev cv : CrdV A.fam.amb := cvOf A F.P0 F.ψ0 F.P1 F.ψ1

def PThmA : Prop :=
  ∀ i t, Lift.IsLamP (R.thG i t) (LinearMap.adjoint (R.thG i t)) (R.Wp i) fun p => R.lam i t p A.v0

def PThmB : Prop := Lift.IsKap D.R.m (fun t => R.Th t ∘ₗ LinearMap.adjoint (R.Th t)) R.EEp R.lamN R.kap

def TopMult : Prop :=
  ∀ t, LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e) =
    MultT R.θ R.MX (levS _ R.βX (R.datXt t)) (levChi _ R.βX (R.datXt t))

def PConj : Prop := ∀ i, (R.FW i).GalA

def PEig : Prop :=
  ∃ C0 C1, LiftsEig A (R.toCx F) F.P0 F.ψ0 C0 ∧ LiftsEig A (R.toCx F) F.P1 F.ψ1 C1 ∧ LiftsTyp A C0 ∧ LiftsTyp A C1

def PHecke : Prop := (∃ hE, HeckeThetaR A (R.toCx F) hE) ∧ ∃ hW, HeckeThetaL A (R.toCx F) hW

def PGUnit : Prop := CxPass.GUnit A (R.toCx F) (R.gEx F) ∧ CxPass.GUnitL A (R.toCx F) (R.gWx F)

def PGEquiv : Prop := CxPass.GEquiv A (R.toCx F) (R.gEx F) ∧ CxPass.GEquivL A (R.toCx F) (R.gWx F)

def PLevE : Prop :=
  CxPass.LevType A (R.toCx F) (P1 := F.P1) (ψ1 := F.ψ1) (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc) (R.gEx F) false F.P0 F.ψ0 ∧
    CxPass.LevType A (R.toCx F) (P1 := F.P1) (ψ1 := F.ψ1) (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc) (R.gEx F) true F.P1 F.ψ1 ∧
    CxPass.PrincipalInjectiveCommonRange A (R.toCx F) (P1 := F.P1) (ψ1 := F.ψ1) (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc)

def PLevW : Prop :=
  CxPass.LevTypeL A (R.toCx F) (P1 := F.P1) (ψ1 := F.ψ1) (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc) (R.gWx F) false F.P0 F.ψ0 ∧
    CxPass.LevTypeL A (R.toCx F) (P1 := F.P1) (ψ1 := F.ψ1) (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc) (R.gWx F) true F.P1 F.ψ1

variable {R F}

theorem inNonzeroPlaces_recursive_iff (C CH : ℝ) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) : R.NonzeroIndexPlace F w ↔ (R.toCx F).W1 F.cr (R.num F C CH) w := by
  constructor
  · rintro ⟨w', hw | hw, i, h⟩
    · subst hw
      rcases h with h | h | h | h | h
      · exact ⟨i, Or.inl h⟩
      · exact ⟨i, Or.inr (Or.inl h)⟩
      · exact ⟨i, Or.inr (Or.inr (Or.inl h))⟩
      · exact ⟨i, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))⟩
      · exact ⟨i, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))⟩
    · subst hw
      rw [ValuationRepresentative.conjPl_conjPl] at h
      rcases h with h | h | h | h | h
      · exact ⟨i, Or.inr (Or.inl h)⟩
      · exact ⟨i, Or.inl h⟩
      · exact ⟨i, Or.inr (Or.inr (Or.inr (Or.inl h)))⟩
      · exact ⟨i, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))⟩
      · exact ⟨i, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))⟩
  · rintro ⟨i, h | h | h | h | h | h⟩
    · exact ⟨w, Or.inl rfl, i, Or.inl h⟩
    · exact ⟨w, Or.inl rfl, i, Or.inr (Or.inl h)⟩
    · exact ⟨w, Or.inl rfl, i, Or.inr (Or.inr (Or.inl h))⟩
    · exact ⟨conjPl w, Or.inr rfl, i, Or.inr (Or.inr (Or.inl h))⟩
    · exact ⟨w, Or.inl rfl, i, Or.inr (Or.inr (Or.inr (Or.inl h)))⟩
    · exact ⟨w, Or.inl rfl, i, Or.inr (Or.inr (Or.inr (Or.inr h)))⟩

end RealDat

open RealDat in

structure PrimLinks (R : RealDat D A Ks) (F : Face D A) (Y : RealDat.RealCol R F) (C CH : ℝ) : Prop where
  heckeR : HeckeRatAllR A
  heckeL : HeckeRatAllL A
  hecke : R.PHecke F
  gUnit : R.PGUnit F
  gEquiv : R.PGEquiv F
  block : R.LBlock F
  ratZ : R.LRatZ F
  eig : R.PEig F
  pos : R.LPos F
  posScal : R.LPosScal
  levE : R.PLevE F
  thmB : R.PThmB
  sumE : ∀ b, (R.toCx F).PartsE b
  ratMu : R.LRatMu F
  unif : R.LUnif
  conj : R.PConj
  levelW : R.LLevelW F
  integral : R.LIntegral
  mLat : R.LMLat F
  levW : R.PLevW F
  thmA : R.PThmA
  sumW : ∀ b, (R.toCx F).PartsW b
  ratTh : R.LRatTh F
  scalConj : R.LScalConj F
  dimParts : ∀ b, (R.toCx F).DimParts b
  covol : R.LCovol F C CH
  onto : R.LOnto F C CH
  lamLow : R.LLamLow F C CH
  btVanish : (R.toCx F).BtVanish (fc := F.fc)
  mi0 : (R.toCx F).MatrixIdentityOffBase F.cr Y.ζ
  period : LPeriod Y
  passage : R.LPassage F C CH
  fun0 : R.LFun F C CH

theorem cxLinks_of_prims {s : ℕ} (hOk : A.fam.Ok s) (hsep : A.fam.TypesSep) {R : RealDat D A Ks} {F : Face D A}
    {Y : RealDat.RealCol R F} {C CH : ℝ} (hC : R.Char F) (hY : Y.Char) (hP : PrimLinks R F Y C CH) :
    (R.toCx F).CxLinks F.cr Y.toCol C CH := by
  obtain ⟨C0, C1, e0, e1, t0, t1⟩ := hP.eig
  obtain ⟨⟨hE, hhE⟩, ⟨hW, hhW⟩⟩ := hP.hecke
  have kR := RealDat.kFormR_of (F := F) hC.models
  have kL := RealDat.kFormL_of (F := F) hC.models
  have jR := RealDat.jIsoR_of (F := F) hC.models
  have jL := RealDat.jIsoL_of (F := F) hC.models
  exact links_of_core (s := s) (C0 := C0) (C1 := C1) (hE := hE) (hW := hW) (gE := R.gEx F) (gW := R.gWx F)
    { kFormR := kR
      kFormL := kL
      jIsoR := jR
      jIsoL := jL
      npTie := ⟨rfl, rfl⟩
      ok := hOk
      sep := hsep
      heckeR := hP.heckeR
      heckeL := hP.heckeL
      thetaR := hhE
      thetaL := hhW
      gUnit := hP.gUnit.1
      gEquiv := hP.gEquiv.1
      lev0 := hP.levE.1
      lev1 := hP.levE.2.1
      h2P := hP.levE.2.2
      gUnitL := hP.gUnit.2
      gEquivL := hP.gEquiv.2
      lower_level_lift_type := hP.levW.1
      upper_level_lift_type := hP.levW.2
      inBlock := hP.block
      ratZ := hP.ratZ
      eig0 := e0
      eig1 := e1
      typ0 := t0
      typ1 := t1
      pos := hP.pos
      h0 := RealDat.h0 hC.tup
      w1 := fun w hw => hC.tup.tw w ((RealDat.inNonzeroPlaces_recursive_iff C CH w).2 hw)
      h4pos := ⟨fun _ => hP.posScal.1, hP.posScal.2, RealDat.nP_pos⟩
      thmBop := RealDat.thmBop_of hP.thmB
      partsE := hP.sumE
      ratMu := hP.ratMu
      kForm := RealDat.kForm hP.unif
      mLat := hP.mLat
      ewNorm := RealDat.ewNorm
      thmAop := RealDat.thmAop_of hP.thmA
      partsW := hP.sumW
      ratTh := hP.ratTh
      galD := hP.scalConj
      dimParts := hP.dimParts
      l3 := hP.covol
      on := hP.onto
      l6 := hP.lamLow
      btVanish := hP.btVanish
      mi0 := hP.mi0
      zetaOK := RealDat.zetaOK_of Y hY
      l1e := hP.period
      fun0 := hP.fun0 } hP.passage

def primPkg {s : ℕ} (hOk : A.fam.Ok s) (hsep : A.fam.TypesSep) (R : RealDat D A Ks) (F : Face D A) (Y : RealDat.RealCol R F)
    (C CH : ℝ) (hC : R.Char F) (hY : Y.Char) (hP : PrimLinks R F Y C CH) :
    IndefPkg A.fam.amb (faceOf A F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) C CH :=
  cxPkgF A hOk hsep F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc (R.toCx F) Y.toCol C CH (cxLinks_of_prims hOk hsep hC hY hP)

theorem primPkg_spec {s : ℕ} (hOk : A.fam.Ok s) (hsep : A.fam.TypesSep) (R : RealDat D A Ks) (F : Face D A)
    (Y : RealDat.RealCol R F) (C CH : ℝ) (hC : R.Char F) (hY : Y.Char) (hP : PrimLinks R F Y C CH) :
    (primPkg hOk hsep R F Y C CH hC hY hP).Zs = (R.toCx F).zs ∧
      (primPkg hOk hsep R F Y C CH hC hY hP).core.base.toIndefData = (R.toCx F).data F.cr false ∧
      (primPkg hOk hsep R F Y C CH hC hY hP).core.cols.toIndefData = (R.toCx F).data F.cr true ∧
      (primPkg hOk hsep R F Y C CH hC hY hP).core.base.μ = R.mu :=
  ⟨rfl, rfl, rfl, rfl⟩

end Prim

section Geo

open Formalism.L2.Geo Formalism.MainNotions

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Gm : DV.Geo D.what₂.LL} {Lv : Type} {Fam : ShimFam D Gm Lv} (Kp : FormsKPkg Fam) [Algebra Kp.fs.KO D.what₂.LL]

def posEmb (σ : D.what₂.LL →+* ℂ) : Prop := ∀ ρ, labE σ (lab σ ρ) = tauE D ρ

def GeoTied (R : RealDat D A Kp.fs.KO) (e : G ≃* Kp.Hb) : Prop :=
  Arith.FormsL.PosOK posEmb D.what₂.embLL ∧ ∀ i : Fin D.R.m, ∃ (w : WeightFamilies.Wt D ((i : ℕ) + 1)) (ι : Kp.fs.Cusp ((i : ℕ) + 1) w →ₗ[Kp.fs.KO] (Fin (R.nW i) → D.what₂.LL)),
    Arith.CompatibleAtCompactLevel Kp e posEmb (R.νW i (R.fdW i)).toReal ((i : ℕ) + 1) w (R.FW i) ι

def CharG (R : RealDat D A Kp.fs.KO) (F : Face D A) (e : G ≃* Kp.Hb) : Prop := R.Char F ∧ GeoTied Kp R e

end Geo

section Exist

open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx

variable (D) in

def WeilExists : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsStdChar D ψ (-1) → IsHeckeChar D χS →
    IsHeckeChar D χT → ResEta D χS S.rank → ResEta D χT T.rank → ∃ ω, IsWeilDatumO ψ S T χS χT ω

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

namespace RealDat

variable (R : RealDat D A Ks) (F : Face D A)

def Base : Prop := R.toLevCh.Is A.μ0 ∧ R.IsGrp F ∧ R.IsFam ∧ R.IsModels

end RealDat

variable (D A Ks) in

def BaseExists (F : Face D A) : Prop := ∃ R : RealDat D A Ks, R.Base F

def ChainExists (F : Face D A) : Prop :=
  ∀ R : RealDat D A Ks, R.Base F → IsStdChar D R.ψ (-1) → ∃ ωY ωX vac vacX vY vX ItY ItX ioY ioX Th,
    RealDat.IsChain { R with ωY := ωY, ωX := ωX, vac := vac, vacX := vacX, vY := vY, vX := vX, ItY := ItY, ItX := ItX,
                             ioY := ioY, ioX := ioX, Th := Th }

def ThPExists (F : Face D A) : Prop :=
  ∀ R : RealDat D A Ks, R.Base F → IsStdChar D R.ψ (-1) → ∃ ωP vacP vP ioP thF thG,
    RealDat.IsThP { R with ωP := ωP, vacP := vacP, vP := vP, ioP := ioP, thF := thF, thG := thG }

def TupExists (R : RealDat D A Ks) (F : Face D A) : Prop :=
  ∃ mu twPl, RealDat.IsTup { R with mu := mu, twPl := twPl } F

end Exist

section Host

variable (D) in

structure HostHyp : Prop where
  interlace : (Ptw D).Interlace
  gap : ∀ (τ : D.what₂.Tau) (j : Fin D.R.m), ((D.R.t : ℚ) + 3) / 2 ≤ (D.hc τ).e j - (D.hc τ).b j ∧
    ∀ h : (j : ℕ) + 1 < D.R.m, ((D.R.t : ℚ) + 3) / 2 ≤ (D.hc τ).b ⟨(j : ℕ) + 1, h⟩ - (D.hc τ).e j
  gapR : ∀ (τ : D.what₂.Tau) (n : ℕ), n + 1 < D.R.r →
    100 * (D.R.r : ℚ) ^ 4 ≤ Formalism.L2.NTheta.lamAt (D.hc τ) n - Formalism.L2.NTheta.lamAt (D.hc τ) (n + 1)
  cloudGap : ∀ τ : D.what₂.Tau, 100 * (D.R.r : ℚ) ^ 4 ≤ Formalism.L2.NTheta.lamAt (D.hc τ) (D.R.k - 2) - Formalism.L2.NTheta.lamAt (D.hc τ) (D.R.k - 1)
  nodeGap : D.NodeGap (4 * ((D.R.N D.R.m : ℕ) : ℝ) ^ 3 + 2 * D.R.t + 6)
  nodeGapR : D.NodeGap (256 * (D.R.r : ℝ) ^ 4)

open Formalism.L2.Geo Formalism.MainNotions Formalism.IndefR.Cx in

def geoPkg {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Gm : DV.Geo D.what₂.LL} {Lv : Type}
    {Fam : ShimFam D Gm Lv} (Kp : FormsKPkg Fam) [Algebra Kp.fs.KO D.what₂.LL] {s : ℕ} (hOk : A.fam.Ok s) (hsep : A.fam.TypesSep)
    (R : RealDat D A Kp.fs.KO) (F : Face D A) (e : G ≃* Kp.Hb) (Y : RealDat.RealCol R F) (C CH : ℝ) (_hH : HostHyp D)
    (hG : CharG Kp R F e) (hY : Y.Char) (hP : PrimLinks R F Y C CH) :
    IndefPkg A.fam.amb (faceOf A F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) C CH :=
  primPkg hOk hsep R F Y C CH hG.1 hY hP

end Host

end Formalism.IndefR.Links

end
