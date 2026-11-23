import Development.WeilBound.CoreStatements.VolumeEquality.PiecesOf
import Development.WeilBound.CoreStatements.VolumeEquality.BaseUnifEx2
import Development.WeilBound.CoreStatements.VolumeEquality.SheetPiecesComponent
import Development.AutomorphicSpectrum.Proofs.MetricProofs.CuspWeightIntegrableOnFundamentalSetStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullIntersectionGenericBoundStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.WeilSt
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CmHostRankBoundsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AgreementPositiveStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ProportionalStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegrableOfResolutionStatementStatement

noncomputable section

namespace SheetDecomposition

open AlgebraicGeometry CategoryTheory Limits NumberField MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

theorem degMu_eq (h1 : HolNull) (h2 : ChartMeets) (h3 : RootBranches) (h4 : CoverRoots) (h5 : LocInj) (h7 : OnePiece)
    (hG : Top.Given) : ∃ κ : ℕ → ℕ → ℕ → ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E)
      (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l)
      (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type)
      [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
      (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd)
      (sm : CMType H → CMType H ⊕ CMType H) (j j' n : ℕ) (B : BaseUnif Y sm j j' n) (FF : Fin B.np → Set (Fin n → ℂ)) (v : ℝ)
      (Ω₁ Ω₂ : Type) [Field Ω₁] [Field Ω₂] (ξ₁ : Sp Ω₁ ⟶ Y.X) (g : Ω₁ →+* Ω₂) (cst : c.F →+* Ω₂),
      Or.sm = sm → Dc.j = j → Dc.j' = j' → Dc.n = n → 1 ≤ j' → 3 * j' + 1 ≤ j + j' → B.Locc →
      (∀ k, (B.F k).IsFundSet (B.Γ k) (FF k)) → (∀ k, ∫ t in FF k, ballDens (B.F k).q t = v) → genPt ξ₁ = genPt Or.𝔐.ξ₀ →
      spMap g ≫ ξ₁ ≫ Y.s = spMap (cst.comp (algebraMap (𝓞 c.F) c.F)) → (∀ a : Ω₁, IsAlgebraic ℤ a → g a ∈ cst.range) →
      degMu Hd = κ (Fintype.card (CMType H)) j j' * (Or.deg * Module.finrank ℚ c.F * v) := by
  classical
  obtain ⟨κ, -, hκ⟩ := transferU
  refine ⟨κ, ?_⟩
  intro E _ _ _ _ H D Xo l c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or sm j j' n B FF v Ω₁ Ω₂ _ _ ξ₁ g cst e1 e2 e3 e4 a1 a2 hL hF hv b1 b2 b3
  subst e1 e2 e3 e4
  obtain ⟨U, hU, hU', ⟨Z⟩⟩ := exists_sheets Or B h1 h2 h3 h4 h5 FF hF
  have h := hκ E H D Xo l c Y II K J Ω W Dc Hd S₀ Or (Z.pieces hG hF) (fun _ => 1) (fun _ _ => 1) (fun _ _ _ _ => rfl)
    (fun _ _ _ => rfl) fun k => by
      simp only [one_mul]
      exact (GlobalTheory.T.cusp_weight_integrable_on_fundamental_set E _ _ _ _ _ _ H (B.F k) (B.Γ k) (FF k) (B.arith k) (hF k) a1 a2).1
  refine h.trans (congrArg _ ?_)
  have := c.fin
  have : NumberField c.F := { to_charZero := inferInstance, to_finiteDimensional := c.fin }
  have hu := h7 hG E H D l (Xo l) c Y _ _ _ _ B _ Or.𝔐.ξ₀ Ω₁ Ω₂ ξ₁ g cst U hL Or.𝔐.gen₀ b1 b2 b3 hU hU'
  have hc : (Finset.univ.filter fun k => ∃ t ∈ GlobalTheory.CompanionTheory.Ar.Cusp.ballDom (B.F k).q, ⊤ ≤ B.pt k t ⁻¹ᵁ U).card = Module.finrank ℚ c.F := by
    rw [← NumberField.Embeddings.card c.F ℂ, ← Finset.card_univ]
    refine Finset.card_bij (fun k _ => B.κ k) (fun _ _ => Finset.mem_univ _) (fun k hk k' hk' e => ?_) fun κ' _ => ?_
    · exact (hu (B.κ k')).unique ⟨e, (Finset.mem_filter.1 hk).2⟩ ⟨rfl, (Finset.mem_filter.1 hk').2⟩
    · obtain ⟨k, hk, -⟩ := hu κ'
      exact ⟨k, Finset.mem_filter.2 ⟨Finset.mem_univ _, hk.2⟩, hk.1⟩
  show ∑ k : Fin B.np, (nSheets Or B U k : ℝ) * ∫ t in FF k, 1 * ballDens (B.F k).q t = _
  simp only [one_mul, hv, nSheets, Nat.cast_ite, Nat.cast_zero, ← Finset.sum_mul, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul]
  rw [← hc, mul_comm (Or.deg : ℝ)]

theorem volEq_of (h1 : HolNull) (h2 : ChartMeets) (h3 : RootBranches) (h4 : CoverRoots) (h5 : LocInj) (h6 : BaseUnifEx2)
    (h7 : OnePiece) (h8 : BallVolEq) (h9 : DegPush) : Cmp.CmpSt → Top.Given →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H)
      (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F))
      [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (D.p + D.q)) (o : Top.GoodOrigin Y T) (II : IntersectionSystem),
      Top.IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.q → 3 * D.q + 1 ≤ D.p + D.q → T.VolEq := by
  intro hC hG E _ _ _ _ H D Xo l c Y _ T o II hY hX hII hq hN
  obtain ⟨κ, hκ⟩ := degMu_eq h1 h2 h3 h4 h5 h7 hG
  obtain ⟨c₀, hc₀, hP⟩ := h9
  obtain ⟨B, hL⟩ := h6 hG E H D l (Xo l) c Y Sum.inr D.p D.q _ (by omega) (Or.inl ⟨rfl, rfl, rfl⟩) rfl
  obtain ⟨FF, hF⟩ := Classical.skolem.1 fun k =>
    GlobalTheory.T.exists_fundamental_set E _ _ _ _ _ _ (B.F k) (GlobalTheory.T.exists_group_dictionary E _ _ _ _ _ _ H (B.F k)).some _ (B.arith k)
  obtain ⟨v, hv⟩ : ∃ v, ∀ k, ∫ t in FF k, ballDens (B.F k).q t = v := by
    rcases isEmpty_or_nonempty (Fin B.np) with h | ⟨⟨k₀⟩⟩
    · exact ⟨0, h.elim⟩
    · exact ⟨_, fun k => h8 hG E H D l (Xo l) c Y _ B FF hq hN hF k k₀⟩
  have := c.fin
  have key : ∀ a, c₀ (Fintype.card (CMType H)) D.p D.q * T.vol a = κ (Fintype.card (CMType H)) D.p D.q * v := fun a => by
    obtain ⟨K, _, J, _, Ω, _, _, W, _, _, Dc, Hd, Or, e1, e2, e3, e4, e5, e6⟩ := GlobalTheory.T.full_intersection_generic_bound hG Link.weilSt E H D Xo l c Y II hII hY
      (by omega) hq _ (o.Or 2 a).𝔐.ξ₀ (o.Or 2 a).𝔐.gen₀ T.bad ∅ false (fun p hp => ((o.bad_iff p).1 hp).1) (by simp) (by simp)
      fun p hp hd => (o.bad_iff p).2 ⟨hp, (hd.mul_left 2).mul_right _⟩
    have eb : Or.bg = Sum.inl := e4
    have ej : Dc.j = D.p := e3
    have es : Or.sm = Sum.inr := by
      obtain ⟨τ⟩ : Nonempty (CMType H) := (GlobalTheory.T.cm_host_rank_bounds E H).2.1
      refine Or.side.elim (fun h => h.2.1) fun h => ?_
      simpa [eb] using congrFun h.1 τ
    have eg : genPt (o.Fx a).ξf = genPt Or.𝔐.ξ₀ := by
      have g1 := congrArg (fun f => f (IsLocalRing.closedPoint _)) ((o.Or 2 a).g_over.symm.trans (o.Or 2 a).𝔐.fn_over)
      rw [e1]
      exact ((congrArg (fun x => (o.Fx a).ξf x) (Subsingleton.elim (α := PrimeSpectrum (o.Fx a).Ωf) _ _)).trans g1).trans
        (congrArg (fun x => (o.Or 2 a).𝔐.ξ₀ x) (Subsingleton.elim (α := PrimeSpectrum (o.Or 2 a).𝔐.Ω₀) _ _))
    have ej' : Dc.j' = D.q := by have := Or.N_eq; unfold ComponentData.j'; omega
    have k1 := hκ E H D Xo l c Y II K J Ω W Dc Hd _ Or _ _ _ _ B FF v _ _ (o.Fx a).ξf (o.Or 2 a).g (o.Or 2 a).𝔐.cst es ej ej' Or.n_eq
      hq hN hL hF hv eg (by rw [← Category.assoc, ← (o.Or 2 a).g_over, Category.assoc, (o.Or 2 a).𝔐.cst_over]) (o.Or 2 a).g_const
    have k2 := hP GlobalTheory.T.agreement_positive GlobalTheory.T.proportional' hC hG (GlobalTheory.T.points_integrable_of_resolution_statement hG.2.2.2.2.1) E H D Xo l c Y T o II hY hX hII (by omega) hq
      (by omega) a K J Ω W Dc Hd Or eb es e5 ⟨fun p hp => e6 p (by simpa using hp), fun p hp => by simp [e2] at hp⟩ e2 eg.symm
    have hd : (Or.deg : ℝ) * Module.finrank ℚ c.F ≠ 0 :=
      mul_ne_zero (Nat.cast_ne_zero.2 Or.cover.1.ne') (Nat.cast_ne_zero.2 Module.finrank_pos.ne')
    exact mul_left_cancel₀ hd (by linear_combination k1 - k2)
  exact fun a a' => mul_left_cancel₀ (hc₀ _ _ _) ((key a).trans (key a').symm)

end SheetDecomposition
