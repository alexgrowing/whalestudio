import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelEntriesCompatibleTrueColumns
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MtOfFactors
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IpMtTie
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormOneFiniteAdeleDetClassOfIsDetLift
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointOverXHasAdelicPointBlockExtendMul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryAdelicTwistDiagonalAtPrimes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistPrimesAwayLevelAndTypePrimes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPtOfMulK1Standard
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryDiagonalBasePointLevelPrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InclMulInvMul
import Formalism.LocalToGlobal.HermitianForms.TiedTwJSym
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsSmulMemOfMemLocW
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemFiCComp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderTBijective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGLocIdGChiTied
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryOfIsON
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReductionModPrimeLevelPrimeSmulEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CevInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBasisAtOfIsLocBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemberStepCharts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEmbFIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiamondOperatorsOnCharts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartTiedLevelChainHostStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartTiedLevelChainStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelTwistPrimesStepZeroCharacterEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValLtOfRedM
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelsTopRowSym
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartTiedTopLevelChainStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianFormLastCoordinateUniformizerVectorSelf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InvSmulMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianChartComplexRationalIntegralFormsStatement

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.StdModel

theorem car_of_cols {D : D7} (C : ColsTiedSym D) : CarH C.herm.base C.forms ∧ CarT C.herm.base C.forms C.herm.atT :=
  ⟨⟨C.eV, fun u v a => by rw [C.res u]; exact (C.herm.atT u).res_F v a, C.car0, C.carC, C.carM, C.sp, C.fr0⟩,
    ⟨C.piU, C.res, C.carP, C.lattice₂, C.pr, C.prk, C.prC, C.z0, C.ga⟩⟩

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : Later B (I.cols l))

theorem existsUnique_stdDt : ∃! dt, I.StdDt l Z dt := by
  refine ⟨FullDt.u1Dt B.host I.SQ, fun x a ha => FullDt.normOneFiniteAdeleDetClass_of_isDetLift B.host I.SQ x a ha, fun dt h => ?_⟩
  ext x
  obtain ⟨a, ha⟩ := FullDt.exists_lift B.host x
  exact (h x a ha).trans (FullDt.normOneFiniteAdeleDetClass_of_isDetLift B.host I.SQ x a ha).symm

theorem stdDt_surjective {dt} (h : I.StdDt l Z dt) : Function.Surjective dt := fun t => by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective (s := KDq B.host I.SQ) t
  obtain ⟨x, hx⟩ := FullDt.exists_of_idele B.host a
  exact ⟨x, h x a hx⟩

theorem existsUnique_qpIs : ∃! Qp, I.QpIs Qp := by
  have hf : ∀ a, {p : ℕ | p.Prime ∧ ∃ P ∈ I.Q a, (p : 𝓞 B.fields.E) ∈ P.asIdeal}.Finite := fun a => by
    refine ((I.Q a).finite_toSet.biUnion (t := fun P => {p : ℕ | p.Prime ∧ (p : 𝓞 B.fields.E) ∈ P.asIdeal}) fun P _ => ?_).subset ?_
    · refine Set.Subsingleton.finite fun p hp q hq => ?_
      by_contra hne
      obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp.1 hq.1).2 hne)
      have e : (a : 𝓞 B.fields.E) * p + b * q = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 B.fields.E) hab
      exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (e ▸ add_mem (P.asIdeal.mul_mem_left _ hp.2) (P.asIdeal.mul_mem_left _ hq.2)))
    · rintro p ⟨hp, P, hP, h⟩
      exact Set.mem_biUnion hP ⟨hp, h⟩
  refine ⟨fun a => (hf a).toFinset, fun a p => by simp, fun Qp h => ?_⟩
  funext a
  ext p
  rw [h a p]
  simp

theorem exists_stdO (hI : I.Ok) (hP : Pins B X) : ∃ Qp O, I.QpIs Qp ∧ I.StdO l Z Qp O := by
  obtain ⟨Qp, hQ, -⟩ := existsUnique_qpIs I
  obtain ⟨O, hO, -⟩ := lift_objects I hI hP l Z Qp
  exact ⟨Qp, O, hQ, hO⟩

section Ker

variable {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : G.Inst (I.rec7 l Z) L} {Gl : G.LatInst (I.rec7 l Z)}
    {K : G.Consts} {Y : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX}

theorem stdKer_iff (t : KerEntTied ex) : I.StdKer l Z t ↔ I.StdKerTie l Z t :=
  ⟨fun ⟨a, b, c, d, e, f, g, h, i, j, k, m, n, o, p⟩ => ⟨a, b, c, d, e, f, g, h, i, j, k, m, n, o, p⟩,
    fun ⟨a, b, c, d, e, f, g, h, i, j, k, m, n, o, p⟩ => ⟨a, b, c, d, e, f, g, h, i, j, k, m, n, o, p⟩⟩

theorem exists_stdKer (hI : I.Ok) (hP : Pins B X) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a))
    (E : KerEnt (I.rec7 l Z) Y ex.tw) (hQ : I.QpIs Y.Qp) (hO : I.StdO l Z Y.Qp O) (hU : ∀ u a i, i < B.R.m → UnfIsAll (O u a) i)
    (hE : EntOk E O) (hS : ∀ u w h, ThAtServed (ex.ker u w h) E) : ∃ t : KerEntTied ex, I.StdKer l Z t ∧ t.O = O := by
  obtain ⟨t, h1, h2, -⟩ := kerEntTied_true I hI hP l Z L hT Gi Gl K Y cX ex O E hQ hO hU hE hS
  exact ⟨t, (stdKer_iff I l Z t).2 h1, h2⟩

theorem qpIs_of_stdKer (t : KerEntTied ex) (h : I.StdKer l Z t) : I.QpIs Y.Qp := by
  obtain ⟨cc, _, _, δ, _, Bs, χ, _, idl, _, _, cD, X', seam, _, Pr, _, _, Ch, sel, S, word, _, tup, hQ, _⟩ := t
  obtain ⟨h1, -, -, -, h5, h6, -, h8, -⟩ := h
  dsimp only at h1 h5 h6 h8
  subst h1 h6
  cases h5
  cases h8
  exact hQ

end Ker

section Tw

variable (l0 : I.Law0 l) {inQ : (I.rec7 l Z).what₂.Tup → HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) → Prop}
  {T : Formalism.L2.Herm.TwChTied (I.rec7 l Z) inQ} {H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)} {J : Formalism.L2.Herm.TwChJointS T H}
  {F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)}

theorem top_of_topK (W : TwFormsTiedS (I.rec7 l Z) (I.tw l l0 Z) T J F) (h : I.TopK l Z l0 W) (u a ha h1 β) :
    I.TopBase l Z u a (W.ch u a ha B.R.m h1 le_rfl β).lev.U
      fun c => ((W.ch u a ha B.R.m h1 le_rfl (T.chOf u a B.R.m c)).y ⟨c, rfl⟩).1 := by
  refine ReadsTop.topBase I l Z (h u a ha h1) β fun c => ?_
  have e : T.chOf u a B.R.m c = β := @Subsingleton.elim _ (@Unique.instSubsingleton _ (T.Ch_m u a).some) _ _
  rw [e]

theorem topK_of_stdW (W : TwFormsTiedS (I.rec7 l Z) (I.tw l l0 Z) T J F) (h : I.StdW l Z l0 W) : I.TopK l Z l0 W := h.topk

end Tw

set_option maxHeartbeats 1600000 in

theorem exists_topPt (hI : I.Ok) (hP : Pins B X) (u : B.Word) (a : I.ι) : ∃ k : GA B (B.R.N B.R.m),
    (∃ p : DecoF B.fields.E (B.R.N B.R.m) ∅ ∅ ∅, PtOf k p ∧ p.deco.1.N = stdLat B.fields.E (B.R.N B.R.m)) ∧
    (∀ (P : (B.primes X).vT u) (r j : Fin (B.R.N B.R.m)), r.1 + 1 = B.R.N B.R.m →
      HasRes P.1 (adAt B.host.F P.1 ((k⁻¹ : GA B (B.R.N B.R.m)).1 r j))
        (if j = r then Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO (X.piT u)) else 0)) ∧ I.TopPt l Z u a k := by
  classical
  obtain ⟨-, hf'⟩ := TwistPrimes.twist_primes_away I hI
  have hf := hf' u a
  obtain ⟨k, h1, h2, h3⟩ := GlobalTheory.Mem.Col2.BasePoint.exists_kStd X l.pr u (B.R.N B.R.m)
  obtain ⟨t, ht, htP, htw⟩ := TwUnit.exists_tw B.host.F B.host.E B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u) (B.primes X).vGs (I.Q a)
    (fun P hP => (hf P hP).1) (X.piT u) (fun P hP => (hf P hP).2.1)
  refine ⟨k * t, TopCh.KStd.exists_ptOf_mul_K1 _ _ _ k t ht h1, fun P r j hr => ?_,
    fun d g' g hd he => TilQ.pt_tilF_gen I hI hP l Z u a k t h1 h2 h3 ht htP d g' g hd he⟩
  have hP1 : P.1 ∉ I.Q a := fun h => (hf _ h).1.1 P.2
  have hP2 : conjPrime₂ P.1 ∉ I.Q a := fun h => (hf _ h).1.2.2.1 (by rw [CharValCompare.conjP_conjP]; exact P.2)
  have ht1 : rhoP B.host.F P.1 t = 1 := by
    refine Units.ext (Matrix.ext fun i j => (htw _ hP1 hP2 i j).trans ?_)
    show _ = (1 : Matrix _ _ _) i j
    rw [Matrix.one_apply]
  have e : rhoP B.host.F P.1 (k * t)⁻¹ = rhoP B.host.F P.1 k⁻¹ := by
    rw [_root_.mul_inv_rev, map_mul, map_inv (rhoP B.host.F P.1) t, ht1, inv_one, one_mul]
  have e' : adAt B.host.F P.1 (((k * t)⁻¹ : GA B (B.R.N B.R.m)).1 r j) = adAt B.host.F P.1 ((k⁻¹ : GA B (B.R.N B.R.m)).1 r j) :=
    congrArg (fun g : GL (Fin (B.R.N B.R.m)) (P.1.adicCompletion B.host.E) => g.1 r j) e
  rw [e']
  exact h3 P r j hr

theorem ipMt_smul (hI : I.Ok) (hP : Pins B X) (Z : Later B (I.cols l)) (u : B.Word) (a : I.ι) (s t : ℂ) (G G' : (I.per l u a).Mt) :
    I.ipMt l u a (s • G) (t • G') = starRingEnd ℂ s * t * I.ipMt l u a G G' := by
  obtain ⟨j, -, -, hm, hp, -⟩ := PerConj.period_conj I hI hP l Z u a
  have h := (IpMt.ipMt_tie I hI hP l Z u a j hm hp).1
  rw [h, h]
  simp [LinearMap.map_smulₛₗ]
  ring

set_option maxHeartbeats 1600000 in

theorem not_funKilled_both {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
    (S : Formalism.L2.Forms.StepLevel F E σ J T f bad) {p q : 𝓞 E} (hpq : IsCoprime p q) (hp : FunKilled S p) (hq : FunKilled S q)
    (v : HeightOneSpectrum (𝓞 F)) : (T : 𝓞 F) ∉ v.asIdeal := by
  intro hv
  have hm : ∀ r : 𝓞 E, inclE (F := F) (v.adicCompletion F) (r : E) ∈ intV E v := fun r =>
    Subring.subset_closure (Or.inl ⟨⟨r, r, rfl⟩, rfl⟩)
  obtain ⟨a, b, hab⟩ := hpq
  refine S.fT_ne v hv (LinearMap.ext fun t => ?_)
  let c : 𝓞 E → intV E v := fun r => ⟨_, hm r⟩
  have h1 : S.fT v hv (c p • c a • t) = 0 := hp v hv (c a • t) _ rfl
  have h2 : S.fT v hv (c q • c b • t) = 0 := hq v hv (c b • t) _ rfl
  have e : c p * c a + c q * c b = 1 := Subtype.ext (by
    show inclE (F := F) (v.adicCompletion F) (p : E) * inclE (F := F) (v.adicCompletion F) (a : E) +
      inclE (F := F) (v.adicCompletion F) (q : E) * inclE (F := F) (v.adicCompletion F) (b : E) = 1
    have := congrArg (fun r : 𝓞 E => inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E r)) hab
    simp only [map_add, map_mul, map_one] at this
    rw [← this, mul_comm _ (inclE (F := F) (v.adicCompletion F) (a : E)), mul_comm _ (inclE (F := F) (v.adicCompletion F) (b : E))])
  have : t = c p • c a • t + c q • c b • t := by rw [smul_smul, smul_smul, ← add_smul, e, one_smul]
  have h3 := congrArg (S.fT v hv) this
  rw [map_add, h1, h2, add_zero] at h3
  exact h3

set_option maxHeartbeats 1600000 in

theorem readsKTop_killed (hI : I.Ok) (hP : Pins B X) (u : B.Word) (a : I.ι) {bad : Set (HeightOneSpectrum (𝓞 B.host.F))} {Ch : Type}
    (chOf : (I.stp u a B.R.m).Cl → Ch)
    (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad B.R.m le_rfl (fun c : {c // chOf c = β} => (I.chain l u a).stab B.R.m c.1)
      (fun c => latCrd (I.rec7 l Z) B.R.m le_rfl (I.latAt u a B.R.m c.1))) (h : I.ReadsKTop l Z u a chOf K) :
    ∃ K' : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad B.R.m le_rfl (fun c : {c // chOf c = β} => (I.chain l u a).stab B.R.m c.1)
      (fun c => latCrd (I.rec7 l Z) B.R.m le_rfl (I.latAt u a B.R.m c.1)),
      I.ReadsKTop l Z u a chOf K' ∧ ∀ β, FunKilled (K' β).lev (X.piT u) := by
  obtain ⟨K', -, hK⟩ := charts_funKilled I hI hP l Z u a B.R.m le_rfl bad Ch chOf K (ReadsKTop.readsK I l Z h)
  obtain ⟨k, hR, hk⟩ := h
  refine ⟨K', ⟨k, ?_, hk⟩, fun β => (hK β).1⟩
  have hy : ∀ c, ((K' (chOf c)).y ⟨c, rfl⟩).1 = ((K (chOf c)).y ⟨c, rfl⟩).1 := fun c => by rw [(hK _).2.2.2.2.2.1]
  refine ⟨hR.key, hR.onto, fun β x => ?_, hR.k_std, hR.k_off, hR.k_T, fun c => ?_, fun c x q hq => ?_, fun c x κ h1 h2 => ?_, fun c s => ?_⟩
  · have := hR.lb β x
    rw [← (hK β).2.1] at this
    exact this
  · have := hR.pt c
    rw [← hy] at this
    exact this
  · rw [hy] at hq
    have := hR.lev c x q hq
    rw [← (hK _).2.2.2.1] at this
    exact this
  · rw [hy] at h2
    have hx : x.1 ∈ (K (chOf c)).lev.U := (hK _).2.2.2.1 ▸ x.2
    exact (congrArg Units.val ((hK _).2.2.2.2.1 x ⟨x.1, hx⟩ rfl)).trans (hR.chr c ⟨x.1, hx⟩ κ h1 h2)
  · have := hR.stab c s
    rw [← (hK _).2.2.2.2.2.2] at this
    exact this

section Frames

open GlobalTheory.Mem.FormSym

theorem hform_last {E : Type} [CommRing E] (σ : E →+* E) {N : ℕ} (hN : 0 < N) {J : Matrix (Fin N) (Fin N) E} (hJ : J = 1) {p : E}
    {z : Fin N → E} (hz : ∀ j, z j = if j.1 + 1 = N then p else 0) (x : Fin N → E) :
    hform σ J z x = σ p * x ⟨N - 1, by omega⟩ := by
  obtain rfl : z = fun j => if j.1 + 1 = N then p else 0 := funext hz
  subst hJ
  unfold hform
  simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_eq_single ⟨N - 1, by omega⟩]
  · simp [show N - 1 + 1 = N by omega]
  · intro b _ hb
    have : ¬ (b.1 + 1 = N) := fun h => hb (Fin.ext (by simp; omega))
    simp [this]
  · simp

theorem sigD_conj (D : D7) (x : D.host.E) : (sigD D : D.host.E →+* D.host.E) x = D.host.conj x := by
  first | rfl | exact Formalism.BasicNotions.Examples₂.star_eq_conj _ _

set_option maxHeartbeats 4000000 in

theorem exists_stdF_stdLvC : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∃ (Ch : B.Word → ℕ → Type) (chOf : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch u) (chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) ∧ (∀ u i, Finite (Ch u i)) ∧ (∀ u, Nonempty (Unique (Ch u B.R.m))) ∧ (∀ u u', (F u).gl = (F u').gl) ∧ CharacterCompatible (F B.u₀).gl B.R.m := by
  intro B X I hOk hPins l Z
  obtain ⟨G, hG, hChi⟩ := GlobalTheory.Mem.TypePrimes.exists_gLoc_idG_chiTied I hOk hPins l Z
  obtain ⟨-, -, -, hN⟩ := GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hOk hPins l Z

  have hch : ∀ (u : B.Word) (i : ℕ), ∃ (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u I.mu0 i).Cl → Ch)
      (K : ∀ (hi : i ≤ B.R.m) (β : Ch), LevelChart (I.rec7 l Z) (B.T u) (badG (I.rec7 l Z)) i hi
        (fun c : {c // chOf c = β} => (I.chain l u I.mu0).stab i c.1)
        (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u I.mu0 i c.1))),
      (∀ hi, I.ReadsK l Z u I.mu0 i hi chOf (K hi)) ∧ (∀ hi c, ((K hi (chOf c)).y ⟨c, rfl⟩).1 = I.yStd u i c) ∧
      ((i = 0 ∨ i = B.R.m) → Nonempty (Unique Ch)) ∧ ∀ hi β, FunKilled (K hi β).lev (X.piT u) := by
    intro u i
    by_cases hi : i ≤ B.R.m
    · obtain ⟨Ch, hF, chOf, K, h1, h2, h3⟩ := GlobalTheory.Mem.Col2.MemChart.exists_charts I hOk hPins l Z u i hi
      obtain ⟨K', h4, h5⟩ := GlobalTheory.Mem.Col2.TC.charts_funKilled I hOk hPins l Z u I.mu0 i hi _ Ch chOf K h1
      refine ⟨Ch, hF, chOf, fun _ => K', fun _ => h4, fun _ c => ?_, h3, fun _ β => (h5 β).1⟩
      rw [(h5 (chOf c)).2.2.2.2.2.1]
      exact h2 c
    · refine ⟨Unit, inferInstance, fun _ => (), fun h => absurd h hi, fun h => absurd h hi, fun h => absurd h hi, fun h => ?_, fun h => absurd h hi⟩
      exfalso
      rcases h with h | h <;> omega
  choose Ch hChF chOf K hRK hYs hU hFK using hch
  have hYs' : ∀ u i hi β c (e : chOf u i c = β), ((K u i hi β).y ⟨c, e⟩).1 = I.yStd u i c := by
    intro u i hi β c e
    subst e
    exact hYs u i hi c
  let A : ∀ u, AtTTied (D := I.rec7 l Z) u := fun u => GlobalTheory.Mem.AtLevel.atTTied I l Z u
  have hIdV : ∀ u, I.IdV l u I.mu0 (A u).eV := fun _ _ => rfl
  choose eY hIdY hde using fun u i (hi : i ≤ B.R.m) => ((hN i hi).2.2 u I.mu0).2
  choose Lv hLv using fun u i (hi : i ≤ B.R.m) => GlobalTheory.Mem.Col2.TC.exists_level_projections I hOk hPins l Z u I.mu0 i hi
  have hde1 : ∀ u i (hi : i ≤ B.R.m), ∃ C : GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E,
      cT (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) C.1 * C.1 = gramN (I.rec7 l Z) i hi ∧
      (∀ x : Fin ((I.rec7 l Z).R.N i) → (I.rec7 l Z).host.E, x ∈ selfDualLatticeCoords (I.rec7 l Z) i hi ↔
        ∀ a, (C.1 *ᵥ x) a ∈ (algebraMap (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E).range) ∧
      ∀ τ z, ((I.rec7 l Z).mem u).C.de i z τ = Formalism.L2.Forms.embT (I.rec7 l Z) τ C.1.det * ((eY u i hi z).1 τ).det := by
    intro u i hi
    refine ⟨1, ?_, fun x => ?_, fun τ z => ?_⟩
    · rw [(hN i hi).1]
      simp [cT]
    · rw [Units.val_one]
      simp only [Matrix.one_mulVec]
      exact (hN i hi).2.1 x
    · refine (hde u i hi τ z).trans ?_
      rw [Units.val_one, Matrix.det_one, map_one, one_mul]
  have hVG := fun u i (hi : i ≤ B.R.m) => GlobalTheory.T.hermitianChart_complex_rational_integral_forms I hOk hPins l Z u I.mu0 i hi _ (Ch u i) (chOf u i) (K u i hi)
    (eY u i hi) (hRK u i hi) (hIdY u i hi)
  have hIN := fun u i (hi : i ≤ B.R.m) => GlobalTheory.Mem.Col2.MetricTie.ipV_norm_tie I hOk hPins l Z u I.mu0 i hi (eY u i hi) (hIdY u i hi)
  have hNm : ∀ u i hi, NormTieG (D := I.rec7 l Z) ((I.rec7 l Z).fm u) (eY u i hi) := fun u i hi => (hIN u i hi).2
  have hDil := fun u i (hi : i ≤ B.R.m) => GlobalTheory.Mem.Col2.DiaChart.dilTied I hOk hPins l Z u I.mu0 i hi _ (Ch u i) (chOf u i) (K u i hi)
    (eY u i hi) (A u).eV (hRK u i hi) (hFK u i hi) (hIdY u i hi) (hIdV u)
  first
    | choose fMe hFv hFvT using fun u i (hi : i ≤ B.R.m) => GlobalTheory.T.chart_tied_level_chain I hOk hPins l Z u I.mu0 i hi _ (Ch u i) (chOf u i)
        (K u i hi) (A u).eV (Lv u i hi) (hRK u i hi) (hFK u i hi) (hIdV u) (hLv u i hi)
    | choose fMe hFv hFvT using fun u i (hi : i ≤ B.R.m) => GlobalTheory.T.chart_tied_level_chain I hOk hPins l Z u I.mu0 i hi _ (Ch u i) (chOf u i)
        (K u i hi) (A u).eV (Lv u i hi) (hRK u i hi) (hIdV u) (hLv u i hi) (hFK u i hi)
    | choose fMe hFv hFvT using fun u i (hi : i ≤ B.R.m) => GlobalTheory.T.chart_tied_level_chain I hOk hPins l Z u I.mu0 i hi _ (Ch u i) (chOf u i)
        (K u i hi) (A u).eV (Lv u i hi) (hRK u i hi) (hIdV u) (hFK u i hi) (hLv u i hi)
    | choose fMe hFv hFvT using fun u i (hi : i ≤ B.R.m) => GlobalTheory.T.chart_tied_level_chain I hOk hPins l Z u I.mu0 i hi _ (Ch u i) (chOf u i)
        (K u i hi) (A u).eV (Lv u i hi) (hRK u i hi) (hIdV u) (hLv u i hi)
  have hUp := fun u i (hi : i ≤ B.R.m) => GlobalTheory.Mem.Col2.UpChart.upNatTie I hOk hPins l Z u I.mu0 i hi _ (Ch u i) (chOf u i) (K u i hi)
    (eY u i hi) (A u).eV (Lv u i hi) (hRK u i hi) (hIdY u i hi) (hIdV u) (hLv u i hi)
  have hDn := fun u i (hi : i ≤ B.R.m) => GlobalTheory.T.chart_tied_level_chain_host I hOk hPins l Z u I.mu0 i hi _ (Ch u i) (chOf u i) (K u i hi)
    (eY u i hi) (A u).eV (Lv u i hi) (hRK u i hi) (hIdY u i hi) (hIdV u) (hLv u i hi)
  have hBw := fun u i (hi : i ≤ B.R.m) => GlobalTheory.Mem.Col2.TC.bw_tie I hOk hPins l Z u I.mu0 i hi (eY u i hi) (hIdY u i hi)

  have hHex : ∀ u i (β : Ch u i), ∃ (H : ∀ (j : Fin 2) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)),
      ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal → Subgroup (GL (Fin (B.R.N i)) (kv (I.rec7 l Z).host.F v)))
      (lam : ∀ j v h, H j v h →* ℂˣ), ∀ hi : i ≤ B.R.m, Nonempty (GLevH (K u i hi β).lev G H lam) := by
    intro u i β
    by_cases hi : i ≤ B.R.m
    · obtain ⟨H, lam, h⟩ := GlobalTheory.Mem.Col2.ChartLevel.chart_gLevH I hOk hPins l Z u G i hi (Ch u i) (chOf u i) (K u i hi) hG (hRK u i hi) β
      exact ⟨H, lam, fun _ => h⟩
    · exact ⟨fun _ _ _ => ⊤, fun _ _ _ => 1, fun h => absurd h hi⟩
  choose Hc lamC hGH using hHex

  choose J lamJ VJ Yb hYbF hYbA yb hJ using fun u => GlobalTheory.T.chart_tied_top_level_chain I hOk hPins l Z u G (Ch u (B.R.m - 1))
    (chOf u (B.R.m - 1)) (K u (B.R.m - 1) (Nat.sub_le _ _)) hG (hRK u _ _)

  choose KP WP hKP using fun u => GlobalTheory.Mem.Col2.TC.clsP_tie I hOk hPins l Z u

  choose jM hjM using fun u => GlobalTheory.Mem.Col2.PerConj.period_conj I hOk hPins l Z u I.mu0

  let β0 : ∀ u i, (i = 0 ∨ i = B.R.m) → Ch u i := fun u i h => (hU u i h).some.default
  have hβ0 : ∀ u i h c, chOf u i c = β0 u i h := fun u i h c => (hU u i h).some.uniq _
  have hSub : ∀ u i, (i = 0 ∨ i = B.R.m) → Subsingleton (Ch u i) := fun u i h => @Unique.instSubsingleton _ (hU u i h).some
  let clsF : ∀ u i hi (h : i = 0 ∨ i = B.R.m), ClsTied (D := I.rec7 l Z) u i hi := fun u i hi h =>
    clsOfChart (β0 u i h) (hβ0 u i h) (K u i hi (β0 u i h))
  let valF : ∀ u i hi (h : i = 0 ∨ i = B.R.m), ValTied (D := I.rec7 l Z) u (A u).eV i hi (clsF u i hi h) := fun u i hi h =>
    @valOfG _ u i hi (Ch u i) (chOf u i) (hSub u i h) (A u).eV (K u i hi) (β0 u i h) (hβ0 u i h) (eY u i hi) (hde1 u i hi)
      (hVG u i hi) (hIN u i hi).1 (hDil u i hi)
  have hR : ∀ u i hi (h : i = 0 ∨ i = B.R.m), ∃ k, I.Reads u I.mu0 i (fun _ => ()) (fun _ => (clsF u i hi h).lev.Lb)
      (fun _ => (clsF u i hi h).lev.U) (fun _ => (clsF u i hi h).lev.chi) (fun c => ((clsF u i hi h).y c).1)
      (fun c s => ((clsF u i hi h).stabI c s).1) k :=
    fun u i hi h => readsK_one I l Z (hRK u i hi) (β0 u i h) (hβ0 u i h)
  choose V0 hV0 using fun u => GlobalTheory.Mem.Col2.TC.GLev0.glev_zero I hOk hPins l Z u G (clsF u 0 (Nat.zero_le _) (Or.inl rfl)) hG
    (hR u 0 _ (Or.inl rfl))
  choose lamM lamP VM VP hVM using fun u => GlobalTheory.Mem.Col2.TC.levels_top_row_sym I hOk hPins l Z u G (clsF u B.R.m le_rfl (Or.inr rfl)) (KP u) hG
    (hR u _ le_rfl (Or.inr rfl)) (hKP u).1
  choose Tl Ta hTl using fun u => GlobalTheory.Mem.Col2.TC.til_ties I hOk hPins l Z u (A u) (clsF u B.R.m le_rfl (Or.inr rfl)) (KP u)
    (lvOfG (A u) (Lv u B.R.m le_rfl)) (valF u B.R.m le_rfl (Or.inr rfl)) rfl (hR u _ le_rfl (Or.inr rfl)) (hKP u).1
    (fun v c z h => (hLv u B.R.m le_rfl).1 v c z h) (hIdY u B.R.m le_rfl)
  choose eW heW hEvz using fun u => (hTl u).2.2
  have hNpos : 0 < B.R.N B.R.m := by
    have := k_le_N B.R B.R.m
    have := B.R.m_add_three_le_k
    omega
  have hTilFv : ∀ u, TilBaseFv (Tl u) (clsF u B.R.m le_rfl (Or.inr rfl)) (fun v => fMe u B.R.m le_rfl (β0 u B.R.m (Or.inr rfl)) v) := by
    intro u v t x r ht hr
    refine hFvT u B.R.m le_rfl (β0 u B.R.m (Or.inr rfl)) v x ⟨B.R.N B.R.m - 1, by omega⟩ r t (by show B.R.N B.R.m - 1 + 1 = _; omega) ht ?_
    refine hr.trans ((hform_last _ hNpos (hN B.R.m le_rfl).1 (hTl u).1 x).trans ?_)
    exact congrArg (fun s : B.host.E => s * (show B.host.E from x ⟨B.R.N B.R.m - 1, Nat.sub_lt hNpos Nat.one_pos⟩)) (sigD_conj (I.rec7 l Z) _)
  have hFrExt : ∀ u, FrExtFr (D := I.rec7 l Z) (Tl u).z0 G (VM u).fr (VP u).fr := by
    intro u
    rw [funext (hTl u).1]
    exact (hVM u).2.2.2
  let F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch u) (chOf u) := fun u =>
    { atT := A u
      gl := G
      gl_K := fun i => by rw [hG.piG]; exact X.piG_K i
      cls := clsF u
      val := valF u
      glev0 := V0 u
      lamM := lamM u
      lamM_eq := (hVM u).1
      glevM := VM u
      lv := fun i hi => lvOfG (A u) (Lv u i hi)
      fMe := fun i hi h v => fMe u i hi (β0 u i h) v
      fv := fun i hi h => fvOfG (A u) (Lv u i hi) (K u i hi) (β0 u i h) (hβ0 u i h) (fMe u i hi) (hFv u i hi)
      upN := fun i hi h => upOfG (A u) (Lv u i hi) (K u i hi) (β0 u i h) (hβ0 u i h) (eY u i hi) (valF u i hi h) rfl
        (hUp u i hi)
      dnN := fun i hi h => dnOfG (A u) (Lv u i hi) (K u i hi) (β0 u i h) (hβ0 u i h) (eY u i hi) (valF u i hi h) rfl
        (hDn u i hi)
      norm := fun i hi h => (normOfG (D := I.rec7 l Z) (u := u) (eY u i hi) (valF u i hi h) rfl (hNm u i hi) :)
      bw := fun i hi h => bwOfG (A u) (eY u i hi) (valF u i hi h) rfl (hBw u i hi)
      ch := fun i _ h2 β => K u i (le_of_succ_m h2) β
      H := Hc u
      lamC := lamC u
      glevC := fun i _ h2 β => (hGH u i β (le_of_succ_m h2)).some
      eYC := fun i _ h2 => eY u i (le_of_succ_m h2)
      deC := fun i _ h2 => hde1 u i (le_of_succ_m h2)
      valC := fun i _ h2 => hVG u i (le_of_succ_m h2)
      ipVC := fun i _ h2 => (hIN u i (le_of_succ_m h2)).1
      normC := fun i _ h2 => (hIN u i (le_of_succ_m h2)).2
      dilC := fun i _ h2 => hDil u i (le_of_succ_m h2)
      lvC := fun i _ h2 => Lv u i (le_of_succ_m h2)
      fMeC := fun i _ h2 => fMe u i (le_of_succ_m h2)
      fvC := fun i _ h2 => hFv u i (le_of_succ_m h2)
      upC := fun i _ h2 => hUp u i (le_of_succ_m h2)
      dnC := fun i _ h2 => hDn u i (le_of_succ_m h2)
      bwC := fun i _ h2 => hBw u i (le_of_succ_m h2)
      levJ := J u
      lamJ := lamJ u
      lamJ_eq := (hJ u).2.1
      glevJ := VJ u
      Yb := Yb u
      YbFin := hYbF u
      YbAct := hYbA u
      yb := yb u
      yb_orbit := (hJ u).2.2.1
      levJ_Lb := fun _ β => ((hJ u).2.2.2 β).1
      levJ_le := fun _ β => ((hJ u).2.2.2 β).2.1
      levJ_stab := fun _ β => ((hJ u).2.2.2 β).2.2.1
      levJ_chi := fun _ β => ((hJ u).2.2.2 β).2.2.2
      clsP := KP u
      valP := WP u
      normP := (hKP u).2.1
      lamP := lamP u
      eigenvalue_eq₂ := (hVM u).2.1
      glevP := VP u
      til := Tl u
      tilLat := (hTl u).2.1
      tilFv := hTilFv u
      tilAd := Ta u
      frExt := hFrExt u
      eWz := eW u
      evz := hEvz u
      jM := jM u
      per := ⟨(hjM u).2.1, (hjM u).2.2.1, (hjM u).2.2.2.1⟩
      DGam := rfl }
  refine ⟨Ch, chOf, F, fun u => ⟨?_, ?_⟩, hChF, fun u => hU u B.R.m (Or.inr rfl), fun _ _ => rfl, hChi⟩
  · exact
      { eV := fun _ => rfl
        piU := rfl
        res := rfl
        gl := hG
        ends := fun i hi h => hR u i hi h
        yE := fun i hi h c => hYs' u i hi _ c (hβ0 u i h c)
        mid := fun i _ h2 => hRK u i (le_of_succ_m h2)
        eY := fun i hi _ => hIdY u i hi
        eYC := fun i _ h2 => hIdY u i (le_of_succ_m h2)
        pr := fun i hi => (hLv u i hi).1
        prk := fun i hi => (hLv u i hi).2
        fr0 := hV0 u
        frP := (hVM u).2.2.1
        what₂ := (hKP u).1
        eW := (hKP u).2.2
        z0 := (hTl u).1
        eWz := heW u }
  · exact ⟨fun i _ h2 => hLv u i (le_of_succ_m h2), (hJ u).1⟩

theorem levJ_Uloc_eq (u : B.Word) {Ch Ch' : ℕ → Type} {chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i}
    {chOf' : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch' i} (F : FormsTiedSym (I.rec7 l Z) u Ch chOf) (F' : FormsTiedSym (I.rec7 l Z) u Ch' chOf')
    (h : I.StdLvC l Z u F) (h' : I.StdLvC l Z u F') (hg : F.gl = F'.gl) (hL : F.levJ.Lb = F'.levJ.Lb) (j : Fin 2) (v)
    (hv : ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal) : F.levJ.Uloc v = F'.levJ.Uloc v := by
  ext x
  by_cases hx : x ∈ levelVL (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) ((I.rec7 l Z).R.m - 1) (Nat.sub_le _ _)) v F.levJ.Lb
  · rw [F.glevJ.mem j v hv x hx, F'.glevJ.mem j v hv x (hL ▸ hx), h.2, h'.2, hg]
  · exact ⟨fun e => absurd (F.levJ.Uloc_lev v e) hx, fun e => absurd (hL ▸ F'.levJ.Uloc_lev v e) hx⟩

end Frames

end GlobalTheory.Mem.Col2.StdModel

end
