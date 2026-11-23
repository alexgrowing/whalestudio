import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.W1idxUnionW1jwFinite
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.Resize

variable {B : Base}

@[reducible] def preX {P : Pre} (X Y : PreX P) : PreX P := { X with a := Y.a, T_gt := Y.T_gt, a_gt := Y.a_gt, spread_le := Y.spread_le }

theorem preX_eq {P : Pre} {X Y : PreX P} (h : X.piG = Y.piG) (h' : X.piT = Y.piT) : preX X Y = Y := by
  cases X; cases Y; cases h; cases h'; rfl

@[reducible] def colIn {X : PreX B.toPre} (I : ColIn B X) (Y : PreX B.toPre) : ColIn B (preX X Y) :=
  @ColIn.mk B (preX X Y) I.C I.Ch I.sel I.S I.ι I.finι I.tup I.tup_inj I.mu0 I.muStar I.muStar' I.trueColumn_tuple_trivial_eq_one I.xi I.cst I.idx I.J

set_option maxHeartbeats 2000000 in

theorem laws {X : PreX B.toPre} (I : ColIn B X) (Y : PreX B.toPre) (l : TC.Laws I) : TC.Laws (colIn I Y) :=
  ⟨l.pr, l.ch, l.lev, l.per, l.ovr, l.atL, l.fmL, l.xi0, l.idx0, l.bij0, l.lat⟩

variable {f : Top.Fr B.toPre} {T : TwDat B}

set_option maxHeartbeats 4000000 in

@[reducible] def colW (w : ColW B f T) (Y : PreX B.toPre) : ColW B f T where
  px := preX w.px Y
  I := colIn w.I Y
  ok := ⟨w.ok.spaces, w.ok.ch_ok, w.ok.ch_tied, w.ok.weil, w.ok.pibar, w.ok.sel_ok, w.ok.T_mem, w.ok.g_mem, w.ok.ram_mem, w.ok.xi_reads,
    w.ok.xi_star, w.ok.xi_star', w.ok.sharp, w.ok.idx_ok, w.ok.amb_ok, w.ok.duStar⟩
  C_eq := w.C_eq
  S_eq := w.S_eq
  xi_range := w.xi_range
  pins := ⟨w.pins.iX, w.pins.cof⟩
  l := laws w.I Y w.l
  l0 := w.l0
  δ := w.δ
  exact := w.exact
  fld := w.fld
  val := w.val

set_option maxHeartbeats 4000000 in

@[reducible] def dat (w : ColW B f T) (Y : PreX B.toPre) (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : R3.Dat (w.st Z) w.I hX T Wt) :
    R3.Dat (w.st Z) (colIn w.I Y) hX T Wt :=
  @R3.Dat.mk (w.st Z) (preX w.px Y) (colIn w.I Y) hX T Wt z.Xg z.tr z.core z.alg z.alg_eq z.R z.cG z.geo z.pins
    ⟨z.lev.is, z.lev.C, z.lev.xiH, z.lev.Pg, z.lev.Q, z.lev.beta⟩ z.idG z.good z.mu z.fieldValues_mem_fixedField z.Ks_le

set_option maxHeartbeats 4000000 in

theorem pinned {K : Ctx} (w : ColW B f T) (Y : PreX B.toPre) (h : Pinned K B f T w) : Pinned K B f T (colW w Y) := by
  obtain ⟨p⟩ := h
  exact ⟨⟨p.isTw, p.jets, p.hX, p.above, p.half, p.d3b, p.selectedPlacesAgree, p.vals, p.roots⟩⟩

set_option maxHeartbeats 4000000 in

theorem grpAt (w : ColW B f T) (Y : PreX B.toPre) (Z : w.Lt) (h : GrpAt (w.st Z) w.I) : GrpAt (w.st Z) (colIn w.I Y) :=
  ⟨h.pl, h.idem, h.cen⟩

set_option maxHeartbeats 4000000 in

theorem fine (w : ColW B f T) (Y : PreX B.toPre) (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : R3.Dat (w.st Z) w.I hX T Wt) (h : Fine z) : Fine (w := colW w Y) (Z := Z) (dat w Y Z hX Wt z) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (by with_unfolding_all exact (h.1 :))
  · exact (by with_unfolding_all exact (h.2.1 :))
  · exact (by with_unfolding_all exact (h.2.2.1 :))
  · exact (by with_unfolding_all exact (h.2.2.2 :))

set_option maxHeartbeats 4000000 in

theorem holdsL (w : ColW B f T) (Y : PreX B.toPre) (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : R3.Dat (w.st Z) w.I hX T Wt) (h : HoldsL z.R z.F) : HoldsL (dat w Y Z hX Wt z).R (dat w Y Z hX Wt z).F := (by with_unfolding_all exact (h :))

set_option maxHeartbeats 4000000 in

theorem nonzeroIndexPlaces_adelicDataResized_eq (w : ColW B f T) (Y : PreX B.toPre) (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : R3.Dat (w.st Z) w.I hX T Wt) : (dat w Y Z hX Wt z).W1 (fun _ _ => 0) = z.W1 (fun _ _ => 0) := rfl

set_option maxHeartbeats 4000000 in

theorem seedW {K : Ctx} {P : Pre} {f : Top.Fr P} {F F₀ : IntermediateField ℚ ℂ} {X Y : PreX P} {S : Set ℕ}
    {L : IntermediateField ℚ ℂ} (h : SeedW K P f F F₀ X S L) (hG : X.piG = Y.piG) (hT : X.piT = Y.piT) : SeedW K P f F F₀ Y S L := by
  obtain ⟨B₀, f₀, T₀, w₀, Z₀, hX₀, Wt₀, z₀, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := h
  subst a1
  have e : w₀.px = X := eq_of_heq a5
  subst e
  refine ⟨B₀, f₀, T₀, colW w₀ Y, Z₀, hX₀, Wt₀, dat w₀ Y Z₀ hX₀ Wt₀ z₀, rfl, a2, a3, a4, heq_of_eq (preX_eq hG hT),
    pinned w₀ Y a6, a7, grpAt w₀ Y Z₀ a8, fine w₀ Y Z₀ hX₀ Wt₀ z₀ a9, holdsL w₀ Y Z₀ hX₀ Wt₀ z₀ a10, ?_, a12⟩
  intro v hv
  exact a11 v ((nonzeroIndexPlaces_adelicDataResized_eq w₀ Y Z₀ hX₀ Wt₀ z₀).le hv)

theorem finite_norm_eq {R : Ranks} (H : Formalism.BasicNotions.Host R) (n : ℕ) :
    {x : 𝓞 H.E | (x : H.E) * H.conj (x : H.E) = (n : H.E)}.Finite := by
  have hF := NumberField.Embeddings.finite_of_norm_le H.E ℂ (n + 1 : ℝ)
  refine (hF.preimage (f := fun x : 𝓞 H.E => (x : H.E)) RingOfIntegers.coe_injective.injOn).subset ?_
  intro x hx
  refine ⟨x.isIntegral_coe, fun φ => ?_⟩
  have h1 : φ (H.conj (x : H.E)) = starRingEnd ℂ (φ (x : H.E)) := Formalism.HC.HostAx.conjE_apply _ _ _
  have h2 := congrArg φ hx
  rw [map_mul, h1, map_natCast, Complex.mul_conj, Complex.normSq_eq_norm_sq] at h2
  have h3 : ‖φ (x : H.E)‖ ^ 2 = (n : ℝ) := by exact_mod_cast h2
  have h4 := norm_nonneg (φ (x : H.E))
  show ‖φ (x : H.E)‖ ≤ (n + 1 : ℝ)
  nlinarith

theorem finite_gens (P : Pre) : (Set.range fun X : PreX P => (X.piG, X.piT)).Finite := by
  have h1 := Set.Finite.pi' fun i : Fin 2 => finite_norm_eq P.host (P.host.g i)
  have h2 := Set.Finite.pi' fun u : P.Word => finite_norm_eq P.host (P.T u)
  refine (h1.prod h2).subset ?_
  rintro _ ⟨X, rfl⟩
  exact ⟨fun i => X.piG_norm i, fun u => X.piT_norm u⟩

theorem exists_gens_LLC (B : Base) : ∃ S₂ : Finset ℂ, (∀ z ∈ S₂, IsAlgebraic ℚ z) ∧
    B.LLC ≤ IntermediateField.adjoin ℚ (S₂ : Set ℂ) := by
  classical
  let b := Module.finBasis ℚ B.LL
  refine ⟨Finset.univ.image fun i => B.embLL (b i), ?_, ?_⟩
  · intro z hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hz
    exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (b i)).algHom B.embLL.toRatAlgHom
  · intro z hz
    obtain ⟨x, rfl⟩ := B.mem_LLC.1 hz
    have e : B.embLL x = ∑ i, (b.repr x i) • B.embLL (b i) := by
      conv_lhs => rw [← b.sum_repr x]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      exact map_rat_smul B.embLL _ _
    rw [e]
    refine sum_mem fun i _ => IntermediateField.smul_mem _ (IntermediateField.subset_adjoin _ _ ?_)
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩)

set_option maxHeartbeats 1000000 in

theorem finite_nonzeroIndexPlaces_referenceTuple (w : ColW B f T) (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : R3.Dat (w.st Z) w.I hX T Wt) (hH : HoldsL z.R z.F) : (z.W1 fun _ _ => 0).Finite := by
  have hok := hH.ok.ok2
  have hIw : ∀ j, {w' | (R3.s0Of z.R z.F).Iw j (R3.famR (w.st Z) w.I hX (R3.usedOf w.I T Wt) z.Xg z.tr).A.μ0 w' ≠ 0}.Finite :=
    fun j => GlobalTheory.Mem.NonzeroPlacesOverPrimes.idx_finite_of_fg _ _ _ (hH.mLat j).fg
      (Formalism.L2.DIV.BlockDat.Tl_lat hok.conj (hok.lifts j _) hok.irr).fg
  have hjw : ∀ j, {w' | Formalism.DivisionValues.jw (((R3.famR (w.st Z) w.I hX (R3.usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0
      (R3.zsOf z.R z.F)).HT j (R3.famR (w.st Z) w.I hX (R3.usedOf w.I T Wt) z.Xg z.tr).A.μ0) w'
      (((R3.famR (w.st Z) w.I hX (R3.usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (R3.zsOf z.R z.F)).Tl j
        (R3.famR (w.st Z) w.I hX (R3.usedOf w.I T Wt) z.Xg z.tr).A.μ0) ≠ 0}.Finite :=
    fun j => GlobalTheory.Mem.NonzeroPlacesOverPrimes.jw_finite_of_lat _ (Formalism.L2.DIV.BlockDat.HZ_det hok.conj (hok.lifts j _) hok.irr) _
      (Formalism.L2.DIV.BlockDat.Tl_lat hok.conj (hok.lifts j _) hok.irr)
  have hF := Set.finite_iUnion fun j => (hIw j).union (hjw j)
  refine ((hF.preimage (w.st Z).toD7.plEq.injective.injOn).union
    ((hF.preimage GlobalTheory.Mem.NonzeroPlacesOverPrimes.conjPl_injective.injOn).preimage (w.st Z).toD7.plEq.injective.injOn)).subset ?_
  rintro v ⟨j, w', hw', h | h | h⟩
  · rcases hw' with rfl | rfl
    · exact Or.inl (Set.mem_iUnion.2 ⟨j, Or.inl h⟩)
    · exact Or.inr (Set.mem_iUnion.2 ⟨j, Or.inl h⟩)
  · rcases hw' with rfl | rfl
    · exact Or.inl (Set.mem_iUnion.2 ⟨j, Or.inr h⟩)
    · exact Or.inr (Set.mem_iUnion.2 ⟨j, Or.inr h⟩)
  · exact absurd rfl h

theorem seedW_bound {K : Ctx} {P : Pre} {f : Top.Fr P} {F F₀ : IntermediateField ℚ ℂ} {X : PreX P}
    (h : SeedW K P f F F₀ X Set.univ ⊤) : ∃ (S : Finset ℕ) (S₂ : Finset ℂ), (∀ z ∈ S₂, IsAlgebraic ℚ z) ∧
      SeedW K P f F F₀ X (S : Set ℕ) (IntermediateField.adjoin ℚ (S₂ : Set ℂ)) := by
  obtain ⟨B₀, f₀, T₀, w₀, Z₀, hX₀, Wt₀, z₀, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, -, -⟩ := h
  obtain ⟨S₂, hS₂, hL⟩ := exists_gens_LLC B₀
  have hfin := (finite_nonzeroIndexPlaces_referenceTuple w₀ Z₀ hX₀ Wt₀ z₀ a10).image B₀.places.resChar
  refine ⟨hfin.toFinset, S₂, hS₂, B₀, f₀, T₀, w₀, Z₀, hX₀, Wt₀, z₀, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, fun v hv => ?_, hL⟩
  rw [Set.Finite.coe_toFinset]
  exact ⟨v, hv, rfl⟩

theorem seeds_uniform : SeedBd := by
  classical
  refine evG_all fun K P f F F₀ => ?_
  have key : ∀ c : (Fin 2 → 𝓞 P.host.E) × (P.Word → 𝓞 P.host.E), ∃ (S : Finset ℕ) (S₂ : Finset ℂ), (∀ z ∈ S₂, IsAlgebraic ℚ z) ∧
      ∀ Y : PreX P, (Y.piG, Y.piT) = c → SeedW K P f F F₀ Y Set.univ ⊤ →
        SeedW K P f F F₀ Y (S : Set ℕ) (IntermediateField.adjoin ℚ (S₂ : Set ℂ)) := by
    intro c
    by_cases hc : ∃ X : PreX P, (X.piG, X.piT) = c ∧ SeedW K P f F F₀ X Set.univ ⊤
    · obtain ⟨X, hX, hs⟩ := hc
      obtain ⟨S, S₂, hS₂, hb⟩ := seedW_bound hs
      refine ⟨S, S₂, hS₂, fun Y hY _ => ?_⟩
      have e := hX.trans hY.symm
      exact seedW hb (congrArg Prod.fst e) (congrArg Prod.snd e)
    · exact ⟨∅, ∅, by simp, fun Y hY hs => absurd ⟨Y, hY, hs⟩ hc⟩
  choose S S₂ hS₂ hS using key
  have hfin := finite_gens P
  refine ⟨hfin.toFinset.biUnion S, hfin.toFinset.biUnion S₂, ?_, fun Y hs => ?_⟩
  · intro z hz
    obtain ⟨c, -, hz⟩ := Finset.mem_biUnion.1 hz
    exact hS₂ c z hz
  · have hm : (Y.piG, Y.piT) ∈ hfin.toFinset := hfin.mem_toFinset.2 ⟨Y, rfl⟩
    refine (hS _ Y rfl hs).mono ?_ (IntermediateField.adjoin.mono _ _ _ ?_)
    · intro p hp
      exact Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨_, hm, hp⟩)
    · intro p hp
      exact Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨_, hm, hp⟩)

end GlobalTheory.Mem.R3.Rw.Resize

end
