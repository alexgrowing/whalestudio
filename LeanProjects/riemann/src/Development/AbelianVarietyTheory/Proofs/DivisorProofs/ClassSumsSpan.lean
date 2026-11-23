import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolSub0LeSpanRaw
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RawSeriesMoveDatum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldingFrameDeltaChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThird
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfFiniteIndex
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicLinearIndependent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOmegaField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHomogeneousOfRowDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesFirstStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelExtensionSecondStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesSixthStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelUnitValues
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalUnitaryMoveSelfDualToSplitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelTensorValues

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

open NumberField Matrix IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ClassSumSpan

theorem mem_span_of_map_mem {K M X : Type} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup X] [Module ℂ X]
    {σ : K →+* ℂ} (L : M →ₛₗ[σ] X) (C : Submodule K M)
    (hL : ∀ (m : ℕ) (b : Fin m → M), (∀ j, b j ∈ C) → LinearIndependent K b → LinearIndependent ℂ fun j => L (b j))
    {S : Set M} (hS : S ⊆ C) {f : M} (hf : f ∈ C) (h : L f ∈ Submodule.span ℂ (L '' S)) : f ∈ Submodule.span K S := by
  by_contra hn
  obtain ⟨T, hT, hfT⟩ := Submodule.mem_span_finite_of_mem_span h
  obtain ⟨T', hT', rfl⟩ := Finset.subset_set_image_iff.1 hT
  obtain ⟨B, hB, hsp, hli⟩ := exists_linearIndependent K (T' : Set M)
  have hfin : B.Finite := T'.finite_toSet.subset hB
  obtain ⟨m, e, hi, rfl⟩ := hfin.fin_param
  have h1 : LinearIndependent K e := (linearIndepOn_id_range_iff hi).1 hli
  have h2 : LinearIndependent K (Fin.cons f e : Fin (m + 1) → M) :=
    linearIndependent_finCons.2 ⟨h1, fun hm => hn (Submodule.span_mono (hB.trans hT') hm)⟩
  have h3 := hL _ _ (fun j => Fin.cases hf (fun j => hS (hT' (hB ⟨j, rfl⟩))) j) h2
  have h4 : (fun j => L ((Fin.cons f e : Fin (m + 1) → M) j)) = Fin.cons (L f) fun j => L (e j) :=
    funext fun j => Fin.cases rfl (fun _ => rfl) j
  rw [h4] at h3
  refine (linearIndependent_finCons.1 h3).2 (Submodule.span_le.2 ?_ hfT)
  intro x hx
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hx
  have h5 := Submodule.image_span_subset_span L (Set.range e) ⟨s, hsp.ge (Submodule.subset_span hs), rfl⟩
  rwa [← Set.range_comp] at h5

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem raw_at_point [StarRing (𝓞 E)] (nab : NabV Xo c) (hnab : IsNab Xo c nab) {n : ℕ} {Λ : GenLat E n} {N : ℕ}
    (hU : Λ.Unimod) (hT : Λ.TrivAt l.M) (hO : Λ.LevOK N l.M) {a : (E →+* ℂ) × ℕ → ℕ} {P : MvPolynomial (LtN Dw n) c.F}
    (hP : P ∈ harmL c Λ a) (w : (Fin n → LevQ Dw l) → c.F) {f : Rul Xo c} (hf : f ∈ sec Xo c a n)
    (h : ∀ (p : TRing c.F) (y : FrPt Xo c p.R), thLaValAt Xo c nab w Λ N P y (f p y))
    (S : Type) [Field S] [Algebra c.F S] (y : FrPt Xo c S) : ShortValAt Xo c nab w Λ 1 N P y (evR Xo c f y) := by
  have hL : Out.Laws := GlobalTheory.firstFiveLaws.1
  obtain ⟨hval, hnat⟩ := GlobalTheory.shortThetaValue_existsUnique_natural hL GlobalTheory.chartIndependence_unconditional E H Dw l Xo c
    nab hnab n Λ N hU hT hO a P hP.1 w 1
  obtain ⟨p, φ, y0, h0⟩ := GlobalTheory.Frames.allTest_of_secBaseChange hL.secBaseChange E H Dw l Xo c S y
  obtain ⟨v, hv, -⟩ := hval S y
  rw [GlobalTheory.CoverDescent.evR_of_test (GlobalTheory.Frames.algebraic_laws hL.secBaseChange E H Dw l Xo c).2.2.1 f hf.1 p φ y0 y h0,
    hnat p.R S φ y0 y h0 _ v (h p y0) hv]
  exact hv

end Gen

theorem exists_split_move {D : D7} (V : HSp D) (hg : V.gram = 1) (hL : Bridge.hLat V 1 = Formalism.L2.Pj.stdLat D.host.E V.rank)
    {H : Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}
    [StarRing (𝓞 D.host.E)] (nab : NabV Xo c) (h1 : 1 ≤ Dw.p + Dw.q) (hnab : IsNab Xo c nab) (hn : Even V.rank)
    {bad : ℕ} (hb : 0 < bad) (h2 : 2 ∣ bad) (hM : l.M ∣ bad) {Λ : GenLat D.host.E V.rank} {N : ℕ} (hU : Λ.Unimod)
    (hT : Λ.TrivAt bad) (hT' : Λ.TrivAt l.M) (hO : Λ.LevOK N l.M) {a : (D.host.E →+* ℂ) × ℕ → ℕ}
    {P : MvPolynomial (LtN Dw V.rank) c.F} (hP : P ∈ harmL c Λ a) (w : (Fin V.rank → LevQ Dw l) → c.F) :
    ∃ (h : GA D V) (Λ' : GenLat D.host.E V.rank) (N' : ℕ) (P' : MvPolynomial (LtN Dw V.rank) c.F) (z : c.F),
      SplitOffBad V bad h ∧ (∀ v, v ∈ Λ'.La ↔ (fun j => star (v j)) ∈ Bridge.hLat V (fin V h)) ∧ Λ'.LevOK N' l.M ∧
      GlobalTheory.ClassScalarCompare.Guard H bad (Bridge.hLat V (fin V h)) ∧ P' ∈ harmL c Λ' a ∧
      ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v : S), ShortValAt Xo c nab w Λ 1 N P y v →
        ∃ v', ShortValAt Xo c nab w Λ' 1 N' P' y v' ∧ v = algebraMap c.F S z * v' := by
  have hM0 : 0 < l.M := l.odd.pos
  have hT2 : Λ.TrivAt (bad * l.M) := by
    obtain ⟨k, hk, h⟩ := hT
    exact ⟨k, hk.mul_right (hk.coprime_dvd_right hM), h⟩
  obtain ⟨γ, h, hγ, hc, hh, hs, e⟩ := GlobalTheory.T.exists_rationalUnitary_move_selfDual_to_split D V hg hL H (bad * l.M) (Nat.mul_pos hb hM0) Λ hU hT2
  obtain ⟨N', c1, c2, c3, c4, c5⟩ := GlobalTheory.SplitReps.exists_conjLat V hg hL H l bad h2 h hs
  have g := GlobalTheory.ClassScalarCompare.guard_conjLat (H := H)
    (L := (GlobalTheory.UnRep.FullReps.conjLat H (Bridge.hLat V (fin V h))).La) ⟨c1, c2, c5⟩
  have e2 : (GlobalTheory.ClassScalarCompare.conjLat (GlobalTheory.UnRep.FullReps.conjLat H (Bridge.hLat V (fin V h))).La).La =
    Bridge.hLat V (fin V h) := GlobalTheory.ClassScalarCompare.conjLat_conjLat _
  rw [e2] at g
  rw [← e] at c3 c4
  have hc' : ∀ j, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence.CongAt l.M (fun i => γ i j) fun i =>
      (((1 : Matrix (Fin V.rank) (Fin V.rank) (𝓞 D.host.E)) i j : 𝓞 D.host.E) : D.host.E) := fun j => by
    obtain ⟨k, hk, hj⟩ := hc j
    refine ⟨k, hk.coprime_mul_left_right, fun i => ?_⟩
    obtain ⟨b, hb⟩ := hj i
    refine ⟨bad * b, hb.trans ?_⟩
    push_cast
    ring
  obtain ⟨z, hz⟩ := GlobalTheory.DatumMove.exists_move_const _ H Dw l Xo c nab h1 hnab _ hn Λ γ hU hγ hT' c3 w w
    (fun q q' hq => congrArg w (funext fun i => by
      rw [GlobalTheory.DatumMove.levMoves_eq hc' hq i]
      simp [Matrix.one_apply])) N N' hO c4 a P hP.1
  refine ⟨h, _, N', _, z, GlobalTheory.SplitReps.splitOffBad_of_suppSplit _ _ _ hh
    (GlobalTheory.SplitReps.suppSplit_mono (dvd_mul_right _ _) hs), fun v => ?_, c4, g,
    ((GlobalTheory.PushKeeps.push_keeps _ H Dw l c _ a γ hγ).2 Λ).2.2.2 P hP, hz⟩
  rw [e]
  rfl

theorem ep_ne_zero {D : D7} (V : HSp D) (hg : V.gram = 1) (hL : Bridge.hLat V 1 = Formalism.L2.Pj.stdLat D.host.E V.rank)
    {H : Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Geo.Tor.Level H} (c : Coeff l) {bad : ℕ}
    {B : Ideal (𝓞 D.host.E) → c.F} {epF : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) → c.F}
    (he : EpIs (Dw := Dw) c bad B epF) (hB : ∀ cc, cc ≠ ⊥ → cc ⊔ Ideal.span {(bad : 𝓞 D.host.E)} = ⊤ → B cc ≠ 0)
    {h : GA D V} (hs : SplitOffBad V bad h) (g : GlobalTheory.ClassScalarCompare.Guard H bad (Bridge.hLat V (fin V h))) :
    epF (Bridge.hLat V (fin V h)) ≠ 0 := by
  obtain ⟨-, e, P, h1, h2, h3⟩ := hs
  obtain ⟨y, hy⟩ := GlobalTheory.PtId.exists_isDetAt h1 V h
  have hbar : (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) = (GlobalTheory.IdemSupport.cO D : 𝓞 D.host.E →+* 𝓞 D.host.E) :=
    RingHom.ext fun a => RingOfIntegers.ext (H.bar_eq a)
  obtain ⟨cc, c0, c1, c2, c3, -⟩ := GlobalTheory.ClassScalarValue.exists_ideal V hg hL h e P y h1 h3 hy bad h2 1 1
    ⟨⟨continuous_const, fun _ => rfl⟩, fun _ _ _ _ _ _ => rfl⟩ (fun _ _ _ _ => rfl) (fun _ _ _ => by
      rw [Formalism.L2.Host.HChar.resFin_apply]
      exact Finset.prod_eq_one fun _ _ => rfl)
  rw [← hbar] at c1 c3
  obtain ⟨q, q0, -, q2⟩ := he _ cc g.1 g.2.1 g.2.2 c1 c3
  rw [q2]
  exact mul_ne_zero (inv_ne_zero (hB cc c0 c2)) (by exact_mod_cast q0.ne')

section Rec

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}

abbrev unfO (O : OMDat T.toCore R i Tp tup) := unfBC O.hle (T.U ((i : ℕ) + 1)) (inC O.c')

def atDict (O : OMDat T.toCore R i Tp tup) : FDSec (unfO O).X →ₗ[ℂ] (GA D (Wc D i) → ℂ) where
  toFun P g := P (O.dict g).1 (O.dict g).2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem goodEmbedding_baseEmbedding_coreData (O : OMDat T.toCore R i Tp tup) : GoodEmb T.Q.c O.s0 := T.toCore.good_σ₀

theorem isUnf_unfO (hT : LawsJ T) (O : OMDat T.toCore R i Tp tup) : IsUnf (unfO O) :=
  GlobalTheory.OneMapAll.isUnf_unfExt O.hle (inC O.c') (fun _ => rfl) (hT.unf _ (inR i) _ (goodEmbedding_baseEmbedding_coreData O))

theorem exists_castDict {Y : Type} {V W : HSp D} (hV : V = W) (dict : GA D V → Y) (g : GA D V) :
    ∃ g', castDict hV dict g' = dict g := by
  subst hV
  exact ⟨g, rfl⟩

theorem dict_mem (hT : LawsJ T) (O : OMDat T.toCore R i Tp tup) (g : GA D (Wc D i)) :
    (O.dict g).2 ∈ ((unfO O).X (O.dict g).1).dom := by
  obtain ⟨th, hr, -, hd⟩ := hT.dictU _ (inR i) _ (goodEmbedding_baseEmbedding_coreData O)
  exact hd.2.2.2.1 _

set_option maxHeartbeats 1000000 in

theorem atDict_indep (hT : LawsJ T) (O : OMDat T.toCore R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (m : ℕ)
    (b : Fin m → Rul (T.Q.Xo ((i : ℕ) + 1)) O.c') (hb : ∀ j, b j ∈ GlobalTheory.OneMapAll.cuspOver O κ)
    (hli : LinearIndependent O.c'.F b) : LinearIndependent ℂ fun j => atDict O (rdU (unfO O) (b j)) := by
  have h1 := (GlobalTheory.reading_linearIndependent_and_injective GlobalTheory.lawsFieldsSeparately.2.1 _ _ _ _ _ O.c' (inC O.c') _
    (Formalism.L2.PjFree.Unf.ofPj (unfO O)) ((Formalism.L2.PjFree.isUnf_ofPj _).2 (isUnf_unfO hT O)) _ _).1 m b
    (fun j => cusp_le_sec _ _ _ _ _ (hb j)) hli
  replace h1 : LinearIndependent ℂ fun j => rdU (unfO O) (b j) := h1
  rw [Fintype.linearIndependent_iff] at h1 ⊢
  intro w hw
  refine h1 w ?_
  obtain ⟨th, hr, -, hd⟩ := hT.dictU _ (inR i) _ (goodEmbedding_baseEmbedding_coreData O)
  have hmem : (∑ j, w j • rdU (unfO O) (b j)) ∈ holSub (unfO O).X (laU (unfO O) (wtA κ) (Vc D i).rank) :=
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (((mem_cusp _ _ _ _ _ _).1 (hb j)).2 _ (goodEmbedding_baseEmbedding_coreData O))
  have hEq := eqv_holSub (unfO O).X _ hmem
  have hz : atDict O (∑ j, w j • rdU (unfO O) (b j)) = 0 := by
    rw [← hw, map_sum]
    exact Finset.sum_congr rfl fun j _ => map_smul _ _ _
  funext k x
  by_cases hx : x ∈ ((unfO O).X k).dom
  · obtain ⟨g, γ, hγ, c, hc, hg⟩ := hd.2.2.2.2.1 k x hx
    have hdom := hd.2.2.2.1 g
    obtain ⟨g', hg'⟩ := exists_castDict O.hV (T.dict ((i : ℕ) + 1) O.s0) g
    have h0 : (∑ j, w j • rdU (unfO O) (b j)) (O.dict g').1 (O.dict g').2 = 0 := congrFun hz g'
    have e : O.dict g' = ⟨k, rmul (lact γ x) c⟩ := hg'.trans hg
    rw [e] at h0
    rw [hg] at hdom
    exact eq_zero_of_orbit _ _ _ (hEq.1 k) (hEq.2 k) hx hγ hc hdom h0
  · simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    have : rdU (unfO O) (b j) k x = 0 := dif_neg hx
    rw [this, mul_zero]

set_option maxHeartbeats 1000000 in

theorem rdU_mem_span_raw (hT : LawsJ T) (O : OMDat T.toCore R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1))
    (hn : κ.n = (Vc D i).rank) (hsz : 8 * D.R.f * D.R.r + 4 ≤ (Vc D i).rank) [StarRing (𝓞 D.host.E)]
    (nab : NabV (T.Q.Xo ((i : ℕ) + 1)) O.c') (hnab : IsNab _ O.c' nab) {bad : ℕ} (hb : 0 < bad)
    (x1 : Fin (Vc D i).rank → LevQc (T.Q.Dw ((i : ℕ) + 1)) T.Q.l) (hx : Submodule.span (𝓞 D.host.E) (Set.range x1) = ⊤)
    {f : Rul (T.Q.Xo ((i : ℕ) + 1)) O.c'} (hf : f ∈ GlobalTheory.OneMapAll.cuspOver O κ) :
    rdU (unfO O) f ∈ Submodule.span ℂ (rdU (unfO O) '' {f | f ∈ sec _ O.c' (wtA κ) (Vc D i).rank ∧
      ∃ (La : GenLat D.host.E (Vc D i).rank) (N : ℕ) (P : MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) O.c'.F),
        La.Unimod ∧ La.TrivAt bad ∧ La.TrivAt T.Q.l.M ∧ La.LevOK N T.Q.l.M ∧ P ∈ harmL O.c' La (wtA κ) ∧
        ∀ (p : TRing O.c'.F) (y : FrPt _ O.c' p.R), thLaValAt _ O.c' nab (phiHat O.c' (indPhi O.c' x1)) La N P y (f p y)}) := by
  have hj := inR i
  have hσ := goodEmbedding_baseEmbedding_coreData O
  obtain ⟨-, hA, -, -, -, hdeg, hnum⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q hT.pins
  have hr1 : 1 ≤ D.R.r := (hnum _ hj).2.1
  obtain ⟨hrk, hW⟩ := hT.modelW _ hj _ hσ
  have hG := GlobalTheory.RunIn.gamAt_of_lawsJ D T hT
  have hD : Dom (wtA κ) (Vc D i).rank := hn ▸ dom_wtA κ
  have hU := isUnf_unfO hT O
  have hle := GlobalTheory.RawSpan.holSub0_le_span_raw D.host.E T.Q.H _ T.Q.l _ O.c' (inC O.c') D.R.r (unfO O) hσ hU hr1 hA
    (fun k k' => ⟨(hW k).1.trans (hW k').1.symm, (hW k).2.trans (hW k').2.symm⟩)
    (by
      intro k ga hga hv
      refine hG _ hj _ hσ k ga hga fun x hx => ?_
      obtain ⟨u, hu, he⟩ := hv x hx
      refine ⟨u, hu, ?_⟩
      rw [he, Nat.cast_smul_eq_nsmul]
      exact add_sub_cancel_left _ _) nab hnab bad _ _ hb hD
    (by
      rw [hdeg]
      calc 4 * (2 * D.R.f * D.R.r) + 4 = 8 * D.R.f * D.R.r + 4 := by ring
        _ ≤ _ := hsz)
    (fun k => hT.chiTriv _ hj _ hσ _ _ hD k)
  refine Submodule.span_le.2 ?_ (hle ⟨((mem_cusp _ _ _ _ _ _).1 hf).2 _ hσ, fun k x hx => dif_neg hx⟩)
  rintro _ ⟨f', hf', rfl⟩
  simp only [Set.mem_iUnion] at hf'
  obtain ⟨x0, hx0, hf'⟩ := hf'
  exact Submodule.image_span_subset_span (rdU (unfO O)) _ ⟨f', GlobalTheory.DatumMove.rawSeries_move_datum _ _ _ _ _ O.c' nab
    (hU.1 ▸ hr1) hA hnab bad _ _ hb hD x0 x1 hx0 hx hf', rfl⟩

end Rec

section Main

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m}
  (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
  (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)

theorem mem_of_mul {X : Type} {S : Submodule ℂ (X → ℂ)} {a φ ψ : X → ℂ} (ha : ∀ x, a x ≠ 0) {I : Type} {s : I → X → ℂ}
    {u : ℂ} (hu : u ≠ 0) (hφ : φ ∈ Submodule.span ℂ (Set.range s)) (hs : ∀ j, ∃ p ∈ S, ∀ x, s j x = a x * p x)
    (h : ∀ x, φ x = u * a x * ψ x) : ψ ∈ S := by
  have key : ∀ φ ∈ Submodule.span ℂ (Set.range s), (fun x => (a x)⁻¹ * φ x) ∈ S := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      obtain ⟨p, hp, e⟩ := hs j
      convert hp using 1
      funext x
      rw [e, inv_mul_cancel_left₀ (ha x)]
    | zero =>
      convert S.zero_mem using 1
      funext x
      exact mul_zero _
    | add y z _ _ hy hz =>
      convert S.add_mem hy hz using 1
      funext x
      exact mul_add _ _ _
    | smul c y _ hy =>
      convert S.smul_mem c hy using 1
      funext x
      exact mul_left_comm _ _ _
  convert S.smul_mem u⁻¹ (key φ hφ) using 1
  funext x
  have := ha x
  rw [Pi.smul_apply, smul_eq_mul, h]
  field_simp

end Main

end GlobalTheory.ClassSumSpan
