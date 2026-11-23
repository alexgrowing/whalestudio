import Development.WeilBound.CoreStatements.VolumeEquality.DegPushDefs
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RealTowerProportionalStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GoodTowerRealAgreementStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TestPolynomialShiftTotalStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CmHostRankBoundsStatement

noncomputable section

namespace SheetDecomposition

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

section

variable {Ω : Type} [Field Ω] {K : Type} [Fintype K] {ι : K → Type} [∀ b, Fintype (ι b)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ b, Fintype (ι' b)]

theorem asm_vdeg_join_inl (O : ValuationSubring Ω) (y : (Σ b, ι b) → Ω) (y' : (Σ b, ι' b) → Ω) (a : K → ℤ) :
    vdeg O (joinPt y y') (Sum.elim a (0 : K' → ℤ)) = vdeg O y a := by
  unfold vdeg
  rw [Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, zpow_zero, Finset.prod_const_one, mul_one]
  rfl

theorem asm_vdeg_join_inr (O : ValuationSubring Ω) (y : (Σ b, ι b) → Ω) (y' : (Σ b, ι' b) → Ω) (a : K' → ℤ) :
    vdeg O (joinPt y y') (Sum.elim (0 : K → ℤ) a) = vdeg O y' a := by
  unfold vdeg
  rw [Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, zpow_zero, Finset.prod_const_one, one_mul]
  rfl

end

theorem degPush_of (hEq : NumEq) (hPF : GeoPF) (hFib : FibNum) (hTr : TrdegU) (hRel : TestRelabel) (hTest : GeoTest)
    (hMap : NumMap) (hMass : MuMass) (hJoin : FieldJoin) (hIso : GenIso) (hFL : FibLink) (hML : MuLink) : DegPush := by
  classical
  obtain ⟨U, hU⟩ := hFib
  refine ⟨fun f p q => if Top.testDeg (Fin f) (p + q) p / U f p q = 0 then 1 else Top.testDeg (Fin f) (p + q) p / U f p q,
    fun f p q => ?_, ?_⟩
  · beta_reduce
    split_ifs with h
    · exact one_ne_zero
    · exact h
  intro _ hProp _ hG hInt E _ _ _ _ H D Xo l c Y _ T o II hY hX hII hp hq hqp a K _ J _ Ω _ _ W _ _ Dc Hd Or eb es _ _ eS eg
  have hIn : PB.Inputs := hG.2.2.2.2.2.2.2.2.2.1
  have : Nonempty (CMType H) := (GlobalTheory.T.cm_host_rank_bounds E H).2.1
  have hT : T.Proportional := GlobalTheory.T.real_tower_proportional hProp hIn II hII _ _ T _ (GlobalTheory.T.good_tower_real_agreement hG E H D Xo l c Y T o II hY hX hII hp hq)
  have htd : 0 < Top.testDeg (CMType H) (D.p + D.q) D.p := (GlobalTheory.T.test_polynomial_shift_total (CMType H) (D.p + D.q) D.p hp (by omega)).2.1
  have eg' : genPt Or.𝔐.ξ₀ = genPt (o.Or 2 a).𝔐.ξ₀ := by
    have g1 := congrArg (fun f => f (IsLocalRing.closedPoint _)) ((o.Or 2 a).g_over.symm.trans (o.Or 2 a).𝔐.fn_over)
    rw [eg]
    exact ((congrArg (fun x => (o.Fx a).ξf x) (Subsingleton.elim (α := PrimeSpectrum (o.Fx a).Ωf) _ _)).trans g1).trans
      (congrArg (fun x => (o.Or 2 a).𝔐.ξ₀ x) (Subsingleton.elim (α := PrimeSpectrum (o.Or 2 a).𝔐.Ω₀) _ _))
  have hvol := hT.1 a
  obtain ⟨M, 𝔐', Fl, e, hδ, hlines, eg', hprop⟩ : ∃ (M : Top.RootModel (CMType H) (D.p + D.q)) (𝔐' : HodgeCpt Y (o.S 2) M.y)
      (Fl : 𝔐'.Flag) (e : RootIx D → M.Ω), M.δ = Module.finrank ℚ c.F * Fl.deg ∧ Fl.RootLines M.xdeg e ∧
      genPt Or.𝔐.ξ₀ = genPt 𝔐'.ξ₀ ∧
      M.geoFun (Top.toA (Top.muSmall D.p ^ Top.dimX (CMType H) (D.p + D.q) D.p * Top.fibClass D.p)) = T.vol a *
        Top.degFl (Top.muSmall D.p ^ Top.dimX (CMType H) (D.p + D.q) D.p * Top.fibClass D.p : Top.RP (CMType H) (D.p + D.q)) :=
    ⟨_, _, _, _, (o.Or 2 a).δ_eq, (o.Or 2 a).lines, eg', hT.2.1 2 a _⟩
  obtain ⟨ψ₀, hψ₀⟩ := hIso _ _ _ _ _ Or.𝔐.gen₀ 𝔐'.gen₀ eg'
  let ψ : 𝔐'.Ω₀ →+* Ω := Or.𝔐.fn.comp ψ₀.toRingHom
  have hdom : GlobalTheory.CompanionTheory.Ar.Dominates Or.𝔐.ξ 𝔐'.ξ₀ Or.𝔐.f ψ := by
    have h := Or.𝔐.fn_over
    unfold GlobalTheory.CompanionTheory.Ar.Dominates at h ⊢
    rw [h, hψ₀, ← Category.assoc, ← Spec.map_comp]
    rfl
  let _ : Algebra 𝔐'.Ω₀ Ω := ψ.toAlgebra
  let _ : Algebra 𝔐'.Ω₀ M.Ω := 𝔐'.fn.toAlgebra
  have hdeg : Module.finrank 𝔐'.Ω₀ Ω = Or.deg := by
    let _ := Or.𝔐.fn.toAlgebra
    rw [← Or.cover.2]
    exact Algebra.finrank_eq_of_equiv_equiv ψ₀ (RingEquiv.refl Ω) rfl
  obtain ⟨b, u, hb, -, -, -, u1, u0, hfl, hai, hd0, hd⟩ := Fl.generic
  obtain ⟨Ω₃, _, _, i, d, n₂, hi, hu, hn, hn0, hnd⟩ := hJoin 𝔐'.Ω₀ Ω M.Ω _ _ u Fl.deg Or.deg ⟨u1, u0, hai, hd0, hd⟩ Or.cover.1 hdeg
  have : CharZero Ω := algebraRat.charZero Ω
  have : CharZero Ω₃ := charZero_of_injective_algebraMap (algebraMap Ω Ω₃).injective
  have : CharZero M.Ω := i.charZero
  let ee := (Fintype.equivFin (PairIx (CMType H) D.p D.q)).symm
  obtain ⟨hcount, htest⟩ := hTest hIn (CMType H) D.p D.q M Dc.n _ ee hqp Or.n_eq
  obtain ⟨hM1, hM2, hM3, -⟩ := hMap M.Ω Ω₃ i _ _ M.y _ M.birational (hcount ▸ M.arith) (hn ▸ hn0)
  have hP : IsPt Ω (fun x => i (M.y x)) _ := ⟨hM1.1, hM2 Ω, hTr _ _ _ Ω Ω₃ _ d hu⟩
  obtain ⟨hJ1, hJ2⟩ := hPF hIn II hII Ω Ω₃ _ _ _ _ Dc.y (fun x => i (M.y x)) Dc.n _ (fun _ => Hd.aMu)
    (fun j => fibDeg M.xdeg (ee j)) Dc.birational Dc.arith hP
  have hF := hU _ _ _ Ω Ω₃ _ _ _ _ d _ M.xdeg ee hu hP
    (hFL E H D l _ c Y _ _ _ _ _ 𝔐' Fl _ e b u Ω Ω₃ i hlines hb u1 u0 hfl fun a => ⟨ψ a, (RingHom.congr_fun hi a).symm⟩)
  have hμ := hML E H D Xo l c Y _ _ _ _ _ 𝔐' Fl _ e II K J Ω W Dc Hd _ Or ψ Ω₃ (algebraMap Ω Ω₃) i hlines eb es eS hdom hi.symm
  have hE := hEq ℚ Ω₃ _ _ _ _ _ _ _
    (Fin.append (fun _ : Fin Dc.n => muDeg M.xdeg) fun j => fibDeg M.xdeg (ee j))
    (Fin.append (fun _ : Fin Dc.n => Sum.elim Hd.aMu (0 : M.K → ℤ)) fun j => Sum.elim (0 : K → ℤ) (fibDeg M.xdeg (ee j)))
    hM1 hJ1 fun j => by
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simpa only [Fin.append_left, ValEq, asm_vdeg_join_inl] using hμ
      · refine ⟨1, one_ne_zero, fun O _ => ?_⟩
        simp only [Fin.append_right, asm_vdeg_join_inr, map_one, one_mul]
  have hG1 := (hMap Ω Ω (RingHom.id Ω) _ _ Dc.y Dc.n Dc.birational Dc.arith (by
    rw [show (RingHom.id Ω).fieldRange = ⊤ from RingHom.fieldRange_eq_top_iff.2 Function.surjective_id]
    have : Module.Finite (⊤ : Subfield Ω) Ω :=
      Module.Finite.of_surjective (Algebra.linearMap (⊤ : Subfield Ω) Ω) fun x => ⟨⟨x, trivial⟩, rfl⟩
    exact Module.finrank_pos)).2.2.2 Hd.aMu
  rw [hM3, hJ2, hF, hG1, hn] at hE
  have hE' := congrArg (Int.cast : ℤ → ℝ) hE
  push_cast at hE'
  rw [← htest, ← hMass hG hInt E H D Xo l c Y II K J Ω W Dc Hd _ Or hII, hprop, hδ] at hE'
  have hnd' : (n₂ : ℝ) * Fl.deg = d * Or.deg := by exact_mod_cast hnd
  have hdpos : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hu.2.2.2.1.ne'
  have := c.fin
  have hFpos : (0 : ℝ) < Module.finrank ℚ c.F := Nat.cast_pos.2 Module.finrank_pos
  have hOpos : (0 : ℝ) < Or.deg := Nat.cast_pos.2 Or.cover.1
  have key : Top.testDeg (CMType H) (D.p + D.q) D.p * Or.deg * Module.finrank ℚ c.F * T.vol a =
      U (Fintype.card (CMType H)) D.p D.q * degMu Hd := by
    apply mul_left_cancel₀ hdpos
    unfold Top.testDeg
    push_cast at hE'
    linear_combination hE' - (Module.finrank ℚ c.F * T.vol a *
      Top.degFl (Top.muSmall D.p ^ Top.dimX (CMType H) (D.p + D.q) D.p * Top.fibClass D.p : Top.RP (CMType H) (D.p + D.q))) * hnd'
  have hU0 : (U (Fintype.card (CMType H)) D.p D.q : ℝ) ≠ 0 := fun h => by
    rw [h, zero_mul] at key
    exact (mul_pos (mul_pos (mul_pos htd hOpos) hFpos) hvol).ne' key
  have hr := hRel (CMType H) (D.p + D.q) D.p
  have hr' : Top.testDeg (Fin (Fintype.card (CMType H))) (D.p + D.q) D.p = Top.testDeg (CMType H) (D.p + D.q) D.p := by
    rw [hr]
  simp only [hr']
  rw [if_neg (div_ne_zero htd.ne' hU0)]
  field_simp
  linear_combination -key

end SheetDecomposition
