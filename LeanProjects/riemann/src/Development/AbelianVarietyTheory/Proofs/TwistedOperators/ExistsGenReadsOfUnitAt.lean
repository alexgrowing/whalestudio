import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGenReads
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RealPoints
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdentityClassLatticeEqSelfDualFrameLattice
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianFormAtFrameLaws
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.WeightFloorInequalities

open AlgebraicGeometry NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
  Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FrameConst

section Fibre

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} {U : Unf Xo c σ r} {k : U.Comp} {x : (U.X k).dom}

set_option maxHeartbeats 1000000 in

theorem exists_genReads_of_unitAt (hσ : GoodEmb c σ) (hU : IsUnf U) (h1 : 1 ≤ r) (Wt : UnfAt U k x) (Y : UnitAt Wt) :
    ∃ (bas : (Fin Wt.g ⊕ Fin Wt.g → ℤ) ≃ₗ[ℤ] (U.X k).Λ) (idx : Fin Wt.g ≃ (U.X k).Ψ × Fin r),
      IsSympl (U.X k) bas ∧ IdxIs c σ (U.X k) idx Wt.e ∧ GenReads U k bas idx Wt.e x Y.θ ∧
        ∀ z w, hermForm Y.Hm z w = hx (U.X k) bas idx x.1 z w := by
  letI : Algebra c.F ℂ := σ.toAlgebra
  have hU' : Formalism.L2.PjFree.IsUnf (Formalism.L2.PjFree.Unf.ofPj U) := hU
  obtain ⟨W0⟩ := nonempty_uw hU'
  obtain ⟨hκ, hsd, -⟩ := GlobalTheory.Dict.uw_lattice E H Dw l Xo c σ _ _ hσ hU' h1 W0 k
  have hκ : (U.X k).κ0 = 2 * (U.X k).ξ0 := hκ
  have hdom : Formalism.L2.Pj.Dom (fun _ : (E →+* ℂ) × ℕ => 0) 0 := ⟨fun _ => antitone_const, by simp⟩
  obtain ⟨Dc, hDe, -⟩ := GlobalTheory.Dict.exists_dic E H Dw l c σ _ Wt.g 0 (U.X k) (fun _ => 0) Wt.e hσ hU.1
    (hU.2.1 k).1 (hU.2.1 k).2 hsd hdom
  have hper : ∀ x v j, pv (U.X k) Dc.idx x v j = perFr (U.X k) x v (relab c σ (Wt.e j).1) (Wt.e j).2 := fun x v j => by
    rw [Dc.per_eq, hDe]
    rfl
  have hty : ∀ j, rowType (U.X k) (Dc.idx j) = relab c σ (Wt.e j).1 := fun j => by
    rw [Dc.ty_eq, hDe]
    rfl
  have hb := Dc.sympl
  generalize Dc.bas = bas at hb
  generalize Dc.idx = idx at hper hty
  obtain ⟨-, -, -, -, -, -, huniq, -⟩ := GlobalTheory.Dict.hx_laws E r (U.X k) Wt.g bas idx 0 hb (by simp) x.1 x.2
  obtain ⟨ex, hl, e1, e2, e3, e4, -⟩ := exists_ex_transport Wt.F (Wt.ik k) Wt.Pm Wt.per
    (unC (Formalism.L2.PjFree.Unf.ofPj U) k x).x Wt.pt
  have hpv : ∀ a, Wt.Pm a = pv (U.X k) idx x.1 (Wt.φ k a : Fin r → E) := fun a => by
    funext j
    rw [Wt.pm_eq, hper]
  have hsurj : ∀ v ∈ (U.X k).Λ, ∃ a, (Wt.φ k a : Fin r → E) = v := fun v hv =>
    ⟨(Wt.φ k).symm ⟨v, hv⟩, by simp⟩
  have hrange : ∀ z, z ∈ Wt.Pm.range ↔ ∃ v ∈ (U.X k).Λ, z = pv (U.X k) idx x.1 v := fun z => by
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨_, (Wt.φ k a).2, hpv a⟩
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨a, rfl⟩ := hsurj v hv
      exact ⟨a, hpv a⟩
  have hEF : ∀ a b, (((Wt.F.Di (Wt.ik k)).EF a b : ℤ) : ℚ) = EF (U.X k) (Wt.φ k a : Fin r → E) (Wt.φ k b) := by
    intro a b
    rw [Wt.isom, EF_def, hκ]
    congr 1; ring
  have hhx : ∀ z w, hermForm Y.Hm z w = hx (U.X k) bas idx x.1 z w := by
    refine (huniq _ (U.X k).Λ_span).2 Y.Hm Y.herm ?_
    intro u hu v hv
    obtain ⟨a, rfl⟩ := hsurj u hu
    obtain ⟨b, rfl⟩ := hsurj v hv
    rw [← hpv, ← hpv, Y.c1, ← hEF]
    simp
  have hl' : (fun z => (ex z).left) = fun z => (Wt.F.ex (Wt.ik k) Wt.Pm z).left := funext hl
  refine ⟨bas, idx, hb, ⟨hper, hty⟩,
         ⟨{ ex := ex
            ex_add := e1
            ex_onto := e2
            ex_ker := fun z => (e3 z).trans (hrange z)
            ex_lin := fun a z => by simp only [hty]; exact e4 a z
            hol := ?_
            der := fun ℓ => by rw [hl']; exact Wt.der ℓ.1 ℓ.2
            fr := Y.fr
            fr_hol := fun j => by simp only [hl]; exact Y.c2 j
            fr_ne := fun j z => by rw [hl]; exact Y.c3 j z
            fr_g := fun j j' z => by rw [hl]; exact Y.c4 j j' z
            fr_0 := fun j => by rw [hl]; exact Y.c5 j
            χ := fun v => Y.χl (pv (U.X k) idx x.1 v)
            χ_norm := ?_
            fr_per := ?_ }, ?_⟩, hhx⟩
  · rw [hl']
    intro V f
    have := ReciprocityTheory.ChartRestriction.G.TB.ValAt.famHol Wt.F (Wt.ik k) Wt.Pm Wt.per V f
    simpa only [Set.mem_univ, true_and] using this
  · intro v hv
    obtain ⟨a, rfl⟩ := hsurj v hv
    rw [← hpv]
    obtain ⟨j, -⟩ := TopologicalSpace.Opens.mem_iSup.1
      (Xo.univ.t.PP.isLB.cover.ge (Set.mem_univ ((ex 0).left (IsLocalRing.closedPoint ℂ))))
    exact (Y.c6 a j 0).1
  · intro v hv j z
    obtain ⟨a, rfl⟩ := hsurj v hv
    rw [hl, ← hpv, ← hhx, ← hhx]
    exact (Y.c6 a j z).2
  · intro j z pt
    show _ = (ex z).left → _ → ⊤ ≤ (ex z).left ⁻¹ᵁ _ → _ = Y.θ z * Y.fr j z ^ (1 : ℤ)
    rw [hl, zpow_one]
    exact Y.c7 j z pt

end Fibre

variable {D : D7}

theorem rat_eq_of_archM {W : HSp D} {τ : D.host.E →+* ℂ} {t : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ}
    (ht : IsInfEmb τ t) {γ γ' h : GA D W} (hγ : γ ∈ GQ W) (hγ' : γ' ∈ GQ W)
    (e : archM W t (γ * h) = archM W t (γ' * h)) : γ = γ' := by
  have hmul : ∀ g g' : GA D W, archM W t (g * g') = archM W t g * archM W t g' := fun g g' => by
    unfold archM
    rw [map_mul, Units.val_mul, Matrix.map_mul]
  have h : archM W t γ = archM W t γ' := by
    rw [← mul_inv_cancel_right γ h, ← mul_inv_cancel_right γ' h, hmul (γ * h), hmul (γ' * h), e]
  have key : ∀ δ : GA D W, ∀ δ₀ : GL (Fin W.rank) D.host.E,
      (∀ i j, (matHom W δ).1 i j = (1 : AF D.host.F) ⊗ₜ δ₀.1 i j) → ∀ i j, archM W t δ i j = τ (δ₀.1 i j) := by
    intro δ δ₀ he i j
    change t (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) ((matHom W δ).1 i j)) = _
    rw [he, Algebra.TensorProduct.map_tmul, map_one]
    exact ht.1 _
  obtain ⟨δ₀, -, he⟩ := hγ
  obtain ⟨δ₁, -, he'⟩ := hγ'
  have h0 : ∀ i j, (matHom W γ).1 i j = (1 : AF D.host.F) ⊗ₜ δ₀.1 i j := fun i j =>
    (congrArg (fun x : GL (Fin W.rank) (AF D.host.F ⊗[D.host.F] D.host.E) => x.1 i j) he).symm
  have h1 : ∀ i j, (matHom W γ').1 i j = (1 : AF D.host.F) ⊗ₜ δ₁.1 i j := fun i j =>
    (congrArg (fun x : GL (Fin W.rank) (AF D.host.F ⊗[D.host.F] D.host.E) => x.1 i j) he').symm
  refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
  refine (h0 i j).trans (Eq.trans ?_ (h1 i j).symm)
  rw [τ.injective ((key γ δ₀ h0 i j).symm.trans ((congrFun (congrFun h i) j).trans (key γ' δ₁ h1 i j)))]

theorem atComp_of_frAt {W : HSp D} {S : D.what₂.Tau → Finset (ℚ × Bool)} (M : Formalism.IndefR.Mult.DSModel W S) {θ : InfFam D}
    (hθ : IsInfFam θ) {r : ℕ} (hr : W.rank = r) {Comp : Type} {X : Comp → Data D.host.E r}
    {dict : GA D W → Σ k, Frame (X k).Ψ r} {x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ} (h0 : IsModelBaseFrameFamily M hr x₀)
    (hΨ : ∀ k, ∀ τ ∈ (X k).Ψ, ∃ ρ, τ = tauE D ρ) {h γ γ₀ : GA D W} (hγ : γ ∈ GQ W) (hf : FrAt M θ hr dict γ h)
    (hx : (dict h).2 ∈ (X (dict h).1).dom) (ha : AtComp θ W hr X dict x₀ h γ₀) : AtComp θ W hr X dict x₀ h γ := by
  obtain ⟨τ, hτ⟩ : ∃ τ, τ ∈ (X (dict h).1).Ψ := by
    obtain ⟨τ₀⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
    by_cases h' : ComplexEmbedding.conjugate τ₀ ∈ (X (dict h).1).Ψ
    · exact ⟨_, h'⟩
    · exact ⟨τ₀, ((X (dict h).1).cmType τ₀).2 h'⟩
  obtain ⟨ρ, rfl⟩ := hΨ _ τ hτ
  have hm := hf ρ ⟨_, hτ⟩ rfl
  rw [← h0.mul] at hm
  have hm' : mat (dict h).2 ⟨_, hτ⟩ =
      Matrix.reindex (finCongr hr) (finCongr hr) (archM W (θ ρ) (γ₀ * h)) * x₀ (tauE D ρ) := by
    rw [← CcModel.realM_mt hθ W (γ₀ * h) (tauE D ρ) ⟨ρ, rfl⟩ _ (hθ ρ)]
    exact congrFun ha.2.2 ⟨_, hτ⟩
  have hd : (mat (dict h).2 ⟨_, hτ⟩).det ≠ 0 := (hx ⟨_, hτ⟩).1
  rw [hm, Matrix.det_mul] at hd
  have hu : IsUnit (x₀ (tauE D ρ)) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (right_ne_zero_of_mul hd))
  obtain rfl : γ = γ₀ := rat_eq_of_archM (hθ ρ) hγ ha.1 ((Matrix.reindex _ _).injective
    (hu.mul_right_cancel (hm.symm.trans hm')))
  exact ha

theorem realPt_fin (S T : HSp D) (X : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt S T X).map (finPart D) = 0 := by
  ext i j
  change Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) (pairA D.host.F 1 0 ⊗ₜ X i j) = 0
  rw [Algebra.TensorProduct.map_tmul]
  exact TensorProduct.zero_tmul _ _

theorem realM_realPt {θ : InfFam D} (hθ : IsInfFam θ) (S T : HSp D) (X : Matrix (Fin T.rank) (Fin S.rank) D.host.E)
    {τ : D.host.E →+* ℂ} (hτ : ∃ ρ, τ = tauE D ρ) (i j) :
    realM θ (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt S T X) τ i j = τ (X i j) := by
  rw [realM, dif_pos hτ]
  change θ hτ.choose (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)
    (pairA D.host.F 1 0 ⊗ₜ X i j)) = _
  rw [Algebra.TensorProduct.map_tmul]
  have := (hθ hτ.choose).1 (X i j)
  rw [← hτ.choose_spec] at this
  exact this

theorem isONLatBasis_one {i : Fin D.R.m} (h : VStd D i) : GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.IsONLatBasis (Vc D i) 1 := by
  refine ⟨fun a a' => ?_, ?_⟩
  · rw [h.1]
    simp [Matrix.one_apply, apply_ite, eq_comm]
  · rw [← GlobalTheory.Equiv.StdSpace.identityClassLattice_eq_selfDualFrameLattice, h.2, SetLike.coe_set_eq]
    apply le_antisymm
    · intro x hx
      choose y hy using fun a => Submodule.mem_one.1 (hx a trivial)
      rw [show x = ∑ a, y a • fun i' => (1 : Matrix _ _ D.host.E) i' a from funext fun b => by
        simp [Matrix.one_apply, ← hy, Algebra.smul_def]]
      exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨a, rfl⟩ b -
      show (1 : Matrix _ _ D.host.E) b a ∈ (1 : Submodule (𝓞 D.host.E) D.host.E)
      rw [Matrix.one_apply]
      split_ifs
      · exact Submodule.mem_one.2 ⟨1, map_one _⟩
      · exact zero_mem _

theorem exists_atComp_cast (T : CoreJ D) (hL : LawsJ T) (j : ℕ) (hj : InR D j) (σ : T.Q.c.F →+* ℂ) (hσ : GoodEmb T.Q.c σ)
    (W : HSp D) (hV : T.V j σ = W) (hr : W.rank = D.R.r) {θ : InfFam D} (hθ : IsInfFam θ)
    (hΨ : ∀ k, ∀ τ ∈ ((T.U j σ).X k).Ψ, ∃ ρ, τ = tauE D ρ) (h : GA D W) :
    ∃ γ, AtComp θ W hr (T.U j σ).X (castDict hV (T.dict j σ)) (T.x₀ j σ) h γ := by
  subst hV
  obtain ⟨_, g, e, F, ik, φ, th, -, -, h3, h4⟩ := hL.adPin j hj σ hσ
  exact CcModel.exists_atComp hθ hr (T.U j σ) (T.dict j σ) _ e F ik φ th _ hΨ h3 h4 h

set_option maxHeartbeats 1000000 in

theorem framePin_of_ccIs : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ) (hV : T.V ((i : ℕ) + 1) σ = Wc D i), σ = T.σ₀ → LawsJ T → R.models_inf → VStd D i → IsModelBaseFrameFamily (R.MW i (sg0 D A)) (rank_Wc i) (T.x₀ ((i : ℕ) + 1) σ) → GlobalTheory.AdTh.CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) (T.U ((i : ℕ) + 1) σ) (castDict hV (T.dict ((i : ℕ) + 1) σ)) (castDict hV (T.mu ((i : ℕ) + 1) σ)) (T.x₀ ((i : ℕ) + 1) σ) (R.ωP i A.μ0) (R.vacP i) (T.cE ((i : ℕ) + 1) σ) → GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i σ hV := by
  intro D G _ _ Pl0 T0 A T _ R i σ hV hσ hL hθ hS h0 hcc
  have hj := inR i
  have hg : GoodEmb T.Q.c σ := hσ ▸ T.toCore.good_σ₀
  have hU := hL.unf _ hj _ hg
  have hr1 : 1 ≤ D.R.r := by
    have h2 := D.R.two_le_m
    have h3 := D.R.m_add_three_le_k
    simp only [Ranks.r]; omega
  have hΨ : ∀ k, ∀ τ ∈ ((T.U ((i : ℕ) + 1) σ).X k).Ψ, ∃ ρ, τ = tauE D ρ := fun k τ hτ =>
    ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.exists_tau_of_inPsi T.Q hL.pins.1 τ (((hU.2.1 k).2 τ).1 hτ)
  refine ⟨1, 1, norm_one, isONLatBasis_one hS, fun h γ hγ hf hx Wt Y X z hz => ?_⟩
  obtain ⟨γ₀, ha⟩ := exists_atComp_cast T hL _ hj σ hg _ hV (rank_Wc i) hθ hΨ h
  have ha' := atComp_of_frAt _ hθ (rank_Wc i) h0 hΨ hγ hf hx ha
  obtain ⟨bas, idx, hb, hi, hgr, hH⟩ := exists_genReads_of_unitAt hg hU hr1 Wt Y
  have key := hcc.2 h γ ha' hx Wt.g bas idx Wt.e hb hi Y.θ hgr _ (realPt_fin (Vc D i) (Wc D i) X)
  have hzz : AdTh.zOf R.θ (Vc D i) (Wc D i) (rank_Wc i) _ idx (castDict hV (T.dict ((i : ℕ) + 1) σ) h).2
      (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) X) = z := by
    funext a j
    rw [hz a, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.perVec, ← hi.1, pv, Function.comp_apply, ← perC_emb, AdTh.zOf]
    congr 1
    funext τ m
    rw [realM_realPt hθ _ _ _ (hΨ _ _ τ.2)]
    simp [Matrix.one_apply, Data.emb]
  rw [hzz] at key
  rw [GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.thetaAt_eq, key]
  simp only [hH]
  rw [neg_mul, Complex.exp_neg]
  have := Complex.exp_ne_zero ((Real.pi / 2 : ℂ) * ∑ a, GlobalTheory.Dict.hx _ bas idx (castDict hV (T.dict ((i : ℕ) + 1) σ) h).2 (z a) (z a))
  field_simp

end GlobalTheory.FrameConst
