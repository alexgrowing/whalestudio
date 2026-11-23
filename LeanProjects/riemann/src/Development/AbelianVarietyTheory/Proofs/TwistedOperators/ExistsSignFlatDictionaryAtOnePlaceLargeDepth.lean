import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsVEqOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCompletionPlaceDataStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProdEqSumOfFactorwiseLinearExpansionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatTensorPureTensorEqProdLocalFactorsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameLatticePointsEqIntegralMatricesLargeDepthStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalCharacterComponentsLargeDepthStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DictionaryPointsLocalMatricesLargeDepthStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselFrameOfGridLatticeLargeDepthStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiFrameOfGridLatticeLargeDepthStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatDictionaryScalarLargeDepthStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArrowLocalModelMovedFramesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeVacuumCombinationLocalModelStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatDictionaryDoubleStepAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatDictionaryLastTwoStepsAtPlaceStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil
open GlobalTheory.SplitFlip (Grid Edge oppositePath)

namespace GlobalTheory.FlatPlace

theorem prod_range_pairs (g : ℕ → ℂ) (n : ℕ) : ∏ j ∈ Finset.range (2 * n), g j = ∏ l ∈ Finset.range n, g (2 * l) * g (2 * l + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.mul_succ, Finset.prod_range_succ, Finset.prod_range_succ, ih, Finset.prod_range_succ, mul_assoc]

theorem prod_fin_pairs {m : ℕ} (hm : Even m) (g : Fin m → ℂ) :
    ∏ j, g j = ∏ l : Fin (m / 2), g ⟨2 * l, by have := l.2; omega⟩ * g ⟨2 * l + 1, by have := l.2; omega⟩ := by
  have h2 : m = 2 * (m / 2) := by obtain ⟨a, ha⟩ := hm; omega
  let g' : ℕ → ℂ := fun j => if h : j < m then g ⟨j, h⟩ else 1
  have e1 : ∏ j, g j = ∏ j ∈ Finset.range m, g' j := by
    rw [Finset.prod_range]
    exact Finset.prod_congr rfl fun j _ => by simp only [g', dif_pos j.2]
  rw [e1, congrArg Finset.range h2, prod_range_pairs, Finset.prod_range]
  refine Finset.prod_congr rfl fun l _ => ?_
  have := l.2
  simp only [g']
  rw [dif_pos (by omega), dif_pos (by omega)]

theorem exists_unpair {Y : ℕ → Type} [∀ j, Nonempty (Y j)] {n : ℕ} (q : ∀ l : Fin n, Y (2 * l) × Y (2 * l + 1)) :
    ∃ x : ∀ j, Y j, ∀ l : Fin n, (x (2 * l), x (2 * l + 1)) = q l := by
  have h : ∀ j, ∃ y : Y j, ∀ l : Fin n, (j = 2 * l → HEq y (q l).1) ∧ (j = 2 * l + 1 → HEq y (q l).2) := fun j => by
    by_cases h1 : ∃ l : Fin n, j = 2 * l
    · obtain ⟨l, rfl⟩ := h1
      refine ⟨(q l).1, fun l' => ⟨fun e => ?_, fun e => by omega⟩⟩
      obtain rfl : l = l' := Fin.ext (by omega)
      rfl
    · by_cases h2 : ∃ l : Fin n, j = 2 * l + 1
      · obtain ⟨l, rfl⟩ := h2
        refine ⟨(q l).2, fun l' => ⟨fun e => by omega, fun e => ?_⟩⟩
        obtain rfl : l = l' := Fin.ext (by omega)
        rfl
      · exact ⟨Classical.arbitrary _, fun l => ⟨fun e => absurd ⟨l, e⟩ h1, fun e => absurd ⟨l, e⟩ h2⟩⟩
  choose x hx using h
  exact ⟨x, fun l => Prod.ext (eq_of_heq ((hx _ l).1 rfl)) (eq_of_heq ((hx _ l).2 rfl))⟩

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Γ : Grid k)

theorem pureTensor_phiM (keep : Bool) (ε g : Γ.VertexGroup)
    (φ : ∀ b : Edge, Matrix (Fin (Γ.rank b.tgt)) (Fin (Γ.rank b.src)) k → ℂ) (z : Γ.Args) :
    Γ.lines₂ (oppositePath Γ.m) (phiM Γ (ε * g) g φ) z =
      zetaLoc Γ keep ε g * moved Γ keep g (Γ.lines₂ (oppositePath Γ.m) φ) z := by
  have h1 : Γ.edgeFactor .one (ε * g) = fun e => Γ.edgeFactor .one ε e * Γ.edgeFactor .one g e := by
    funext e
    simp only [Grid.edgeFactor, Pi.mul_apply, map_mul, GlobalTheory.SplitFlip.apow_mul, _root_.mul_inv_rev, Units.val_mul]
    ring
  have h2 : Γ.lines₂ (oppositePath Γ.m) (phiM Γ (ε * g) g φ) z = ((oppositePath Γ.m).map (Γ.edgeFactor .one ε)).prod *
      Γ.pathAct .one (oppositePath Γ.m) g (Γ.lines₂ (oppositePath Γ.m) φ) z := by
    simp only [Grid.lines₂, Grid.pathAct, phiM, h1, List.prod_map_mul, mul_assoc]
    rfl
  rw [h2, zetaLoc, moved]
  cases keep
  · simp only [Bool.false_eq_true, if_false, mul_assoc, Units.mul_inv_cancel_left]
  · simp only [if_true, mul_one, one_mul]

theorem flatTensor_phiM [MeasurableSpace k] [BorelSpace k] (hs : 1 ≤ Γ.s) (ψ : AddChar k Circle) (ν : Measure k) (keep : Bool)
    (ε g : Γ.VertexGroup) (φ : ∀ b : Edge, Matrix (Fin (Γ.rank b.tgt)) (Fin (Γ.rank b.src)) k → ℂ) (x : ColArgs Γ) (y : RowArgs Γ) :
    flatTensor hs ψ ν (Γ.lines₂ (oppositePath Γ.m) (phiM Γ (ε * g) g φ)) x y =
      zetaLoc Γ keep ε g * flatTensor hs ψ ν (moved Γ keep g (Γ.lines₂ (oppositePath Γ.m) φ)) x y := by
  simp only [flatTensor, flatIntegrand, pureTensor_phiM Γ keep, mul_assoc, integral_const_mul]

end Local

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)

theorem gv_row (t : T) (w : Pl D.host.E) (β : Cosets (G := locGrid ch.G t w) one_le_sLen (givenLevel ch.G t w)) (i : ℕ) :
    (epsV ch.G t w * (repsAt ch.G t w).elt β) (i, D.R.m) = 1 := by
  rw [Pi.mul_apply]
  by_cases hi : i = D.R.m
  · subst hi
    rw [epsV_eq_one t w (by omega), elt_eq_one t w β (by omega), mul_one]
  · have e1 : epsV ch.G t w (i, D.R.m) = 1 := dif_neg hi
    have e2 : (repsAt ch.G t w).elt β (i, D.R.m) = 1 := dif_neg hi
    rw [e1, e2, mul_one]

theorem colAt_up {t : T} {w : Pl D.host.E} {p : Place D (Kw w)} (hp : IsPlc w p) (x : ColArgs (locGrid ch.G t w)) (j : ℕ)
    (hj : j < D.R.m) : ch.S.toGridChoice.colAt t w (fun j => p.up (frTop ch.S.toGridChoice t w j j.2.le)
      (frTop ch.S.toGridChoice t w (j + 1) j.2) (x j)) j = x j := by
  rw [GridChoice.colAt, dif_pos hj]
  refine Eq.trans ?_ (Witness.down_up p (frTop ch.S.toGridChoice t w j hj.le) (frTop ch.S.toGridChoice t w (j + 1) hj) (x j))
  have e : p.π = (cpt w).comp (toEAf D) := RingHom.ext hp.2.1
  rw [Place.down, e]
  rfl

theorem placeAt_of (hc : ChrP ch) (ha : ArrP ch) (hl : LocP ch) (hd : DblP ch) (hz : LastP ch) (hb : CombP ch) (hs : ScalP ch) :
    PlaceAt ch (-1) := by
  obtain ⟨κ, z, h1, h2, h3⟩ := hs
  refine ⟨κ, z, h1, h2, fun t w hw β => ⟨_, h3 t w hw β, ?_⟩⟩
  intro e he M hM r r₀ h hr hr₀ hh φ hφ v f hv hf I S x d c hdc hx u
  obtain ⟨p, hp, rfl⟩ := GlobalTheory.T.exists_completionPlaceData D w e he
  have hm := D.R.two_le_m
  have hev : Even D.R.m := D.R.m_even
  have hP : IsPts ch t w β p.e r r₀ h := ⟨hr, hr₀, hh⟩
  have hV : ∀ j : Fin D.R.m, IsArrVec ch t w p.e φ j j.2 (v j) (f j) := fun j => ⟨hv j, hf j⟩
  have hcond := (hc t w hw p hp).2.1
  have hE : ∀ j (hj : j + 1 < D.R.m), Even j →
      Expands p j hj (facAt ch t w β φ j) (conAt ch.W hM f (h * r) j) (conAt ch.W hM v (h * r₀) j) := fun j hj hj' => by
    by_cases h2 : j + 2 = D.R.m
    · exact hz t w hw p hp β r r₀ h hP M hM φ v f hV j h2
    · exact hd t w hw p hp β r r₀ h hP M hM φ v f hV j hj' (by omega)
  have hΞ : ∀ (i : I) (j : Fin D.R.m), ∃ Ξ : SB (Matrix _ _ (Kw w)), i ∈ S →
      (∀ y, Ξ.1 y = (d i j).fn (p.up (frTop ch.S.toGridChoice t w j j.2.le) (frTop ch.S.toGridChoice t w (j + 1) j.2) y)) ∧
      p.IsCombAt ch.W.ψ (frTop ch.S.toGridChoice t w j j.2.le) (frTop ch.S.toGridChoice t w (j + 1) j.2) ((c i).1 j) Ξ.1 :=
    fun i j => by
      by_cases hi : i ∈ S
      · obtain ⟨Ξ, hΞ⟩ := hb t w hw p hp j j.2 (d i j) ((c i).1 j) (hdc i hi j).1 (hdc i hi j).2
        exact ⟨Ξ, fun _ => hΞ⟩
      · exact ⟨0, fun h => absurd h hi⟩
  choose Ξ hΞ using hΞ
  have hlt : ∀ l : Fin (D.R.m / 2), 2 * l.1 + 1 < D.R.m := fun l => by have := l.2; omega
  have hSB : ∀ j < D.R.m - 1, phiM (locGrid ch.G t w) (epsV ch.G t w * (repsAt ch.G t w).elt β) ((repsAt ch.G t w).elt β) φ
      (.theta D.R.m j) ∈ SB _ := fun j hj => by
    obtain ⟨-, -, -, Φ, hΦ, -⟩ := ha t w hw p hp φ j (by omega) _ _ (hV ⟨j, by omega⟩) _ _ (epsV_mem t w) 1 _ 1 _
      (hl t w hw p hp β r r₀ h hP j (by omega)).1 (hl t w hw p hp β r r₀ h hP (j + 1) (by omega)).1 _ _ (Equiv.refl _) (Equiv.refl _)
    obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := Kw w)
    have key : ∀ {A B : Type}, Topology.IsClosedEmbedding fun z : Matrix A B (Kw w) => zᵀ :=
      Function.LeftInverse.isClosedEmbedding (f := fun z => zᵀ) (fun z => rfl) continuous_id.matrix_transpose
        continuous_id.matrix_transpose
    have e : phiM (locGrid ch.G t w) (epsV ch.G t w * (repsAt ch.G t w).elt β) ((repsAt ch.G t w).elt β) φ (.theta D.R.m j) =
        Φ.1 ∘ fun z => zᵀ := funext fun z => (hΦ zᵀ).symm
    rw [e]
    exact ⟨Φ.2.1.comp_continuous key.continuous, Φ.2.2.comp_isClosedEmbedding key⟩
  have key := GlobalTheory.T.prod_eq_sum_of_factorwise_linear_expansion (Fin (D.R.m / 2)) _ I S
    (fun i => zetaLoc (locGrid ch.G t w) (keepAt ch.G w) (epsV ch.G t w) ((repsAt ch.G t w).elt β) * x i)
    (fun l i q => (Ξ i ⟨2 * l, by have := hlt l; omega⟩).1 q.1 * (Ξ i ⟨2 * l + 1, hlt l⟩).1 q.2)
    (fun l i => combC ch.W (c i) (conAt ch.W hM v (h * r₀)) (2 * l) (u (2 * l)) (u (2 * l + 1)))
    (fun l => facAt ch t w β φ (2 * l)) (fun l => conAt ch.W hM f (h * r) (2 * l) (u (2 * l)) (u (2 * l + 1)))
    (fun l y hy => by
      have := congrFun (congrFun ((hE (2 * l) (hlt l) (even_two_mul _) I S y _ _ (fun i => (c i).1 (2 * l))
        (fun i => (c i).1 (2 * l + 1)) fun i hi => ⟨(hΞ i ⟨2 * l, by have := hlt l; omega⟩ hi).2, (hΞ i ⟨2 * l + 1, hlt l⟩ hi).2⟩).1
        fun q₁ q₂ => hy (q₁, q₂)) (u (2 * l))) (u (2 * l + 1))
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, combC] using this)
    (fun l y hy => by
      have := congrFun (congrFun ((hE (2 * l) (hlt l) (even_two_mul _) I S y _ _ (fun i => (c i).1 (2 * l))
        (fun i => (c i).1 (2 * l + 1)) fun i hi => ⟨(hΞ i ⟨2 * l, by have := hlt l; omega⟩ hi).2, (hΞ i ⟨2 * l + 1, hlt l⟩ hi).2⟩).2
        hy) (u (2 * l))) (u (2 * l + 1))
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, combC] using this)
    (fun q => by
      obtain ⟨y, hy⟩ := exists_unpair (Y := fun j => Matrix (Fin (topRank (locGrid ch.G t w) (j + 1)))
        (Fin (topRank (locGrid ch.G t w) j)) (Kw w)) q
      have e1 := hx (fun j => p.up (frTop ch.S.toGridChoice t w j j.2.le) (frTop ch.S.toGridChoice t w (j + 1) j.2) (y j))
        fun j => Witness.up_half p _ _ _
      have e2 := GlobalTheory.T.flatTensor_pureTensor_eq_prod_localFactors (Kw w) (locGrid ch.G t w) one_le_sLen hm hev (psiAt ch.W w) (unitVol w) hcond.continuous hcond.ne_one
        (isUnitVol_unitVol w).1 _ hSB (ch.S.toGridChoice.colAt t w fun j => p.up (frTop ch.S.toGridChoice t w j j.2.le)
          (frTop ch.S.toGridChoice t w (j + 1) j.2) (y j)) 0
      replace e2 := ((flatTensor_phiM (locGrid ch.G t w) one_le_sLen (psiAt ch.W w) (unitVol w) (keepAt ch.G w) (epsV ch.G t w)
        ((repsAt ch.G t w).elt β) φ _ 0).trans (congrArg _ e1.symm)).symm.trans e2
      rw [Finset.prod_eq_one (s := Finset.range (locGrid ch.G t w).m) (fun i _ => by
        simp only [phiM, hφ, Grid.edgeFactor, mul_one]
        change ((_ : ℂˣ) : ℂ) * _ * _ * _ = 1
        rw [show (epsV ch.G t w * (repsAt ch.G t w).elt β) (Edge.ex i (locGrid ch.G t w).m).src = 1 from gv_row ch t w β i,
          show (epsV ch.G t w * (repsAt ch.G t w).elt β) (Edge.ex i (locGrid ch.G t w).m).tgt = 1 from gv_row ch t w β (i + 1)]
        simp), one_mul, Finset.prod_range] at e2
      refine Eq.trans (Finset.prod_congr rfl fun l _ => ?_) (e2.symm.trans ?_)
      · rw [colAt_up ch hp y _ (by have := hlt l; omega), colAt_up ch hp y _ (hlt l), hy l]
      · rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [← mul_assoc, prod_fin_pairs hev]
        congr 1
        refine Finset.prod_congr rfl fun l _ => ?_
        rw [(hΞ i _ hi).1, (hΞ i _ hi).1, ← hy l])
    fun l => ⟨0⟩
  simp only [evT, Pi.one_apply, Finset.prod_const_one, mul_one, Finset.prod_range]
  rw [key, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => mul_assoc _ _ _

theorem big_placeAt : Big fun ch => ∃ s, PlaceAt ch s :=
  big_mono (fun ch ⟨⟨⟨⟨⟨⟨⟨⟨⟨lat, chr⟩, loc⟩, bes⟩, jac⟩, scal⟩, arr⟩, comb⟩, dbl⟩, last⟩ =>
    ⟨-1, placeAt_of ch chr (arr lat chr) loc (dbl chr (arr lat chr) loc bes jac) (last chr (arr lat chr) loc bes jac) (comb lat) scal⟩)
  (((((((((GlobalTheory.T.frameLattice_points_eq_integralMatrices_largeDepth.and GlobalTheory.T.localCharacterComponents_largeDepth).and GlobalTheory.T.dictionaryPoints_localMatrices_largeDepth).and GlobalTheory.T.besselFrameOfGridLattice_largeDepth).and GlobalTheory.T.jacobiFrameOfGridLattice_largeDepth).and GlobalTheory.T.flatDictionaryScalar_largeDepth).and
    GlobalTheory.T.arrowLocalModel_movedFrames).and GlobalTheory.T.latticeVacuumCombination_localModel).and GlobalTheory.T.flatDictionary_doubleStep_at_place).and GlobalTheory.T.flatDictionary_lastTwoSteps_at_place)

end GlobalTheory.FlatPlace

end
