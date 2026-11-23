import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClsAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ConstantUniqueOfEqProduct
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StdCharFinitePartRationalEqExpTrace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldingFrameDeltaChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HxOfIsONFr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThAHeisEntireLinearInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DictionaryComponentFrameMarkingUniformisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelFormCompatBaseEmbedding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenReadsOfUnfBC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordEqOfPerConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulMemLatGHat
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUnique
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ProdLevelOneThetaEqVacuumTheta
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsLetterRowWeightDictionary
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UniformisationComponentLatticesMarkings
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnalyticFibreUnitFrameUniformisation
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FramedPointGeneratorIsThetaLevelOne
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DualHalfLevelMarkingExistsAndMatch
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ClassSumEvalComplexPointEqClassical
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsLiftMarked
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PureTensorLIntertwine
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EmbeddingsDifferOnInteger
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.CmHostUnitAddConjEqOne

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PtId

theorem mem_HHa_of_span {T : Type} (r : T → ℕ) (n : ℕ) (k : Type) [Field k] (cc : T → T) (isX : T → Prop) (a : T → ℕ → ℕ)
    {P : MvPolynomial (Letter T r n) k} (h : P ∈ Submodule.span k (HHa r n k cc isX a)) : P ∈ HHa r n k cc isX a := by
  induction h using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact ⟨zero_mem _, fun _ _ _ _ _ => map_zero _, fun m hm => by simp at hm⟩
  | add x y _ _ hx hy =>
    refine ⟨add_mem hx.1 hy.1, fun σ i i' hi t => by rw [map_add, hx.2.1 σ i i' hi t, hy.2.1 σ i i' hi t], fun m hm => ?_⟩
    rcases Finset.mem_union.1 (MvPolynomial.support_add hm) with h | h
    · exact hx.2.2 m h
    · exact hy.2.2 m h
  | smul c x _ hx =>
    exact ⟨Submodule.smul_mem _ c hx.1, fun σ i i' hi t => by rw [map_smul, hx.2.1 σ i i' hi t],
      fun m hm => hx.2.2 m (MvPolynomial.support_smul hm)⟩

theorem isHomogeneous_of_rowDeg {T : Type} [Fintype T] (r : T → ℕ) (n : ℕ) (k : Type) [Field k] (a : T → ℕ → ℕ)
    {P : MvPolynomial (Letter T r n) k} (h : RowDeg r n k a P) : P.IsHomogeneous (∑ σ, ∑ j : Fin (r σ), a σ j) := by
  intro m hm
  have h1 := h m (MvPolynomial.mem_support_iff.2 hm)
  rw [show Finsupp.weight 1 m = Finsupp.degree m from (DFunLike.congr_fun Finsupp.degree_eq_weight_one m).symm,
    Finsupp.degree_eq_sum, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun j _ => h1 σ j

theorem exists_isVarOf {D : D7} (V W : HSp D) {r : ℕ} (hr : W.rank = r) (X : Data D.host.E r) (hX : IsMod W hr X) (q0 : ℕ)
    (hq : X.p0 + q0 = r) : ∃ vr, IsVarOf V W X q0 vr := by
  let e1 : D.what₂.Tau ≃ X.Ψ := Equiv.ofBijective (fun ρ => ⟨tauE D ρ, (hX.psi _).2 ⟨ρ, rfl⟩⟩)
    ⟨fun a b h => GlobalTheory.StdRat.tauE_injective D (congrArg Subtype.val h), fun τ => by
      obtain ⟨ρ, h⟩ := (hX.psi τ.1).1 τ.2
      exact ⟨ρ, Subtype.ext h.symm⟩⟩
  let e2 : Fin q0 ⊕ Fin X.p0 ≃ Fin W.rank := finSumFinEquiv.trans (finCongr (by omega))
  refine ⟨e1.symm.prodCongr (e2.prodCongr (Equiv.refl _)), fun l => ⟨?_, rfl, ?_⟩⟩
  · exact (congrArg Subtype.val (e1.apply_symm_apply l.1)).symm
  · obtain ⟨τ, j | j, b⟩ := l <;> rfl

theorem exists_isDetAt {D : D7} {e : AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (h : IsIdemSum e P) (V : HSp D) (g : GA D V) :
    ∃ y, IsDetAt e V g y := by
  obtain ⟨ι, Q, es, h1, h2, h3⟩ := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum h
  have he : e * e = e := by
    conv_lhs => rw [h3, Finset.sum_mul]
    rw [h3]
    exact Finset.sum_congr rfl fun i hi => GlobalTheory.PlaceModelSum.mul_sum_orth h1 h2 hi
  obtain ⟨u, hu⟩ : IsUnit (Formalism.L2.Theta.mt V g).det := (Matrix.isUnit_iff_isUnit_det _).1 ⟨(matHom V g), rfl⟩
  have k1 : (e * (u : AE D) + (1 - e)) * (e * (u⁻¹ : (AE D)ˣ) + (1 - e)) = 1 := by
    have := u.mul_inv
    linear_combination (e * e) * this + ((2 : AE D) - u - (u⁻¹ : (AE D)ˣ)) * he
  exact ⟨⟨_, _, k1, (mul_comm _ _).trans k1⟩, by rw [IsDetAt, ← hu]⟩

theorem exists_point {D : D7} {H : Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}
    {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r) (hσ : GoodEmb c σ) (hU : IsUnf U) (h1 : 1 ≤ r) (hA : l.A = 1)
    (θ : InfFam D) (V W : HSp D) (hr : W.rank = r) (dict : GA D W → Σ k, Frame (U.X k).Ψ r)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (hmk : ∀ (Wt : UW (Formalism.L2.PjFree.Unf.ofPj U)) (h : GA D W), IsONFr (U.X (dict h).1) (dict h).2 ∧
      ∃ γ, AtComp θ W hr U.X dict x₀ h γ ∧ MarkAd l W hr ι (γ * h) (Wt.mark (dict h).1))
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (hD : Dom a V.rank) (mu : GA D W → ℂ)
    (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f₀ : WO V W → ℂ) (cst : U.Comp → ℂ)
    (hcc : CcIs θ V W hr U dict mu x₀ om f₀ cst) (h : GA D W) :
    letI : Algebra c.F ℂ := σ.toAlgebra
    ∃ (hx : (dict h).2 ∈ (U.X (dict h).1).dom) (g : ℕ) (Dc : Dic Dw c σ (U.X (dict h).1) g Dw.p V.rank a) (γ : GA D W)
      (mk : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)) (v : TF V.rank g) (ϑ : (Fin g → ℂ) → ℂ) (κ' : ℂ)
      (B : AnFib (U.X (dict h).1) Dc.bas Dc.idx Dc.e (dict h).2 (U.X (dict h).1).Λ
        (unC (Formalism.L2.PjFree.Unf.ofPj U) (dict h).1 ⟨(dict h).2, hx⟩)),
      AtComp θ W hr U.X dict x₀ h γ ∧ SelfD (U.X (dict h).1) (U.X (dict h).1).Λ ∧ IsMark l (U.X (dict h).1).Λ mk ∧
      B.Marked mk ∧ MarkAd l W hr ι (γ * h) mk ∧
      B.Reads 1 (unC (Formalism.L2.PjFree.Unf.ofPj U) (dict h).1 ⟨(dict h).2, hx⟩).s ϑ ∧
      IsVac (U.X (dict h).1) Dc.bas (H.w0 : D.host.E) (tens (stdL D.host.E V.rank) (U.X (dict h).1).Λ) v ∧
      (∀ z : Fin V.rank → Fin g → ℂ, ∏ b, ϑ (z b) = κ' * thA (U.X (dict h).1) Dc.bas Dc.idx v (dict h).2 z) ∧
      Reads θ V W hr (U.X (dict h).1) Dc.bas Dc.idx (om (1, γ * h) f₀) ((cst (dict h).1 * mu h * κ') • v) (dict h).2 := by
  letI : Algebra c.F ℂ := σ.toAlgebra
  obtain ⟨Wt⟩ := nonempty_uw (U := Formalism.L2.PjFree.Unf.ofPj U) hU
  obtain ⟨hon, γ, hat, hma⟩ := hmk Wt h
  have hn : Even V.rank := hD.2
  obtain ⟨-, hsd, hmark, -⟩ := uw_lattice _ H Dw l Xo c σ r (Formalism.L2.PjFree.Unf.ofPj U) hσ hU h1 Wt (dict h).1
  obtain ⟨Dc, hDe, -⟩ := exists_dic _ H Dw l c σ r Wt.g V.rank (U.X (dict h).1) a Wt.e hσ hU.1 (hU.2.1 _).1 (hU.2.1 _).2 hsd hD
  obtain ⟨hx, hux, -⟩ := hx_of_isONFr _ r Wt.g V.rank _ Dc.bas Dc.idx Dc.sympl hn _ hon
  have hw : IsIntegral ℤ (H.w0 : D.host.E) := H.w0.isIntegral_coe
  have hw' : (H.w0 : D.host.E) + cc (H.w0 : D.host.E) = 1 := by
    rw [cc, ← H.bar_eq]
    exact_mod_cast congrArg (fun t : 𝓞 D.host.E => (t : D.host.E)) (PullbackSections.CVA.cmHostUnit_add_conj_eq_one H)
  obtain ⟨v, hv⟩ :=
    (TensVac.vacua _ _ _ _ Dc.bas Dc.idx V.rank Dc.sympl hn _ hw hw' _ hsd 1 _ (Base.stdL_mem_Vset V.rank 1)).1
  have key := uw_anFib _ H Dw l Xo c σ r (Formalism.L2.PjFree.Unf.ofPj U) hσ hU h1 Wt (dict h).1 Dc.bas Dc.idx Dc.sympl
    (hDe ▸ Dc.per_eq) (hDe ▸ Dc.ty_eq) ⟨_, hx⟩ hux
  rw [← hDe] at key
  obtain ⟨B, hBm, ϑ, hϑ, -⟩ := key
  have hT := isTheta1_of_reads_generator _ H Dw l Xo c _ _ _ Dc.bas Dc.idx Dc.e _ _ _ B Dc.sympl hx hsd ϑ hϑ
  obtain ⟨κ', hκ⟩ := VacProd.prod_eq_mul_thA _ _ _ _ Dc.bas Dc.idx V.rank Dc.sympl hn _ hw hw' _ hsd v hv _ hx ϑ hT
  refine ⟨hx, Wt.g, Dc, γ, Wt.mark (dict h).1, v, ϑ, κ', B, hat, hsd, hmark, hBm, hma, hϑ, hv, hκ, ?_⟩
  obtain ⟨s1, s2⟩ := ((thA_heis_entire_linear_injective _ r Wt.g V.rank _ Dc.bas Dc.idx Dc.sympl hn _ hx v hv.1).2.2 v hv.1).1
    (cst (dict h).1 * mu h * κ') 0
  rw [zero_smul, add_zero] at s1 s2
  rw [zero_smul, add_zero] at s2
  refine ⟨s1, fun w hw0 => ?_⟩
  rw [hcc.2 h γ hat hx Wt.g Dc.bas Dc.idx Dc.e Dc.sympl ⟨Dc.per_eq, Dc.ty_eq⟩ ϑ ⟨B, hϑ⟩ w hw0, hκ, s2, Pi.smul_apply, smul_eq_mul]
  ring

theorem dict_cast {D : D7} (T : CoreJ D) (hL : LawsJ T) (j : ℕ) (hj : InR D j) (σ : T.Q.c.F →+* ℂ) (hσ : GoodEmb T.Q.c σ)
    (W : HSp D) (hV : T.V j σ = W) (hr : W.rank = D.R.r) :
    LatEmb W (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota j) ∧
    LatIsom W (T.Q.Dw j).EF (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota j) ∧
    (∀ g : GA D W, ∃ x, IsDetRoot W g x) ∧
    ∀ θ : InfFam D, IsInfFam θ → (∀ k, IsMod W hr ((T.U j σ).X k)) → 1 ≤ D.R.r →
      ∀ (Wt : UW (Formalism.L2.PjFree.Unf.ofPj (T.U j σ))) (h : GA D W),
        IsONFr ((T.U j σ).X (castDict hV (T.dict j σ) h).1) (castDict hV (T.dict j σ) h).2 ∧
        ∃ γ, AtComp θ W hr (T.U j σ).X (castDict hV (T.dict j σ)) (T.x₀ j σ) h γ ∧
          MarkAd T.Q.l W hr (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota j) (γ * h)
            (Wt.mark (castDict hV (T.dict j σ) h).1) := by
  subst hV
  obtain ⟨_, g, e, F, ik, φ, th, h1, h2, h3, h4⟩ := hL.adPin j hj σ hσ
  refine ⟨h1, h2, (hL.muVal j hj σ hσ).1, fun θ hθ hm h0 Wt h => ?_⟩
  obtain ⟨k1, γ, k2, k3, -⟩ := dict_atComp_markAd D _ _ _ _ _ σ _ (T.U j σ) hσ (hL.unf j hj σ hσ) h0 hL.pins.2.1.2 θ _ hr
    (T.dict j σ) _ g e F ik φ th _ hθ hm (hL.familyUniformisationBasePointOrthogonal j hj σ hσ) h3 h4 Wt h
  exact ⟨k1, γ, k2, k3⟩

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {F : Face D A}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
  {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}

abbrev unfO (O : OMDat T.toCore R i Tp tup) : Unf (T.Q.Xo ((i : ℕ) + 1)) O.c' (inC O.c') D.R.r :=
  unfBC O.hle (T.U ((i : ℕ) + 1)) (inC O.c')

set_option maxHeartbeats 1000000 in

theorem geo_value (hT : TieIn T R κ v₀) (O : OMDat T.toCore R i Tp tup)
    (hP : O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0)) {c0 : ℂ} (hc : CovAt O c0) (t : Tp)
    (X : Data D.host.E D.R.r) (g : ℕ)
    (Dc : Dic (T.Q.Dw ((i : ℕ) + 1)) O.c' (inC O.c') X g (T.Q.Dw ((i : ℕ) + 1)).p (Vc D i).rank (wtA (κ i)))
    (k : GA D (Wc D i)) (xk : (AE D)ˣ) (hk : IsDetRoot (Wc D i) k xk) (hX : IsMod (Wc D i) (rank_Wc i) X)
    (hp : X.p0 = (T.Q.Dw ((i : ℕ) + 1)).q) (hpq : (T.Q.Dw ((i : ℕ) + 1)).p ≠ (T.Q.Dw ((i : ℕ) + 1)).q)
    (hrk : D.R.r = (T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q) (hn : Even (Vc D i).rank)
    (hΛ : latR (rank_Wc i) (latG (Wc D i) k) = X.Λ) (hsd : SelfD X X.Λ) (x : Frame X.Ψ D.R.r) (hx : x ∈ X.dom)
    (hxk : x = frMove R.θ (Wc D i) (rank_Wc i) X k (fun τ => T.x₀ ((i : ℕ) + 1) O.s0 τ.1))
    (mk mk₂ : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)) (hm : IsMark T.Q.l X.Λ mk)
    (hm₂ : IsMark (O.dδ t).l₂ X.Λ mk₂) (ha₂ : MarkAd (O.dδ t).l₂ (Wc D i) (rank_Wc i) (iotaW T i) k mk₂)
    (hov : MarkOver T.Q.l (O.dδ t).l₂ X.Λ mk mk₂) (v : TF (Vc D i).rank g) (ϑ : (Fin g → ℂ) → ℂ) (κ' : ℂ)
    (hv : IsVac X Dc.bas (T.Q.H.w0 : D.host.E) (tens (stdL D.host.E (Vc D i).rank) X.Λ) v)
    (hκ : ∀ z : Fin (Vc D i).rank → Fin g → ℂ, ∏ b, ϑ (z b) = κ' * thA X Dc.bas Dc.idx v x z)
    (Y : O.Cl' t → (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (O.dδ t).l₂) → Matrix (Fin (Vc D i).rank) (Fin D.R.r) D.host.E)
    (hY : ∀ j, IsRoots (O.dδ t).l₂ X.Λ mk₂ (O.Nc t j) (Y j)) (xs : O.Cl' t → VsV D i O.c'.F)
    (f : Rul (T.Q.Xo ((i : ℕ) + 1)) O.c') (hf : GlobalTheory.OneMapTuples.IsCls O t xs f) :
    letI : Algebra O.c'.F ℂ := (inC O.c').toAlgebra
    ∀ (y : FrPt (T.Q.Xo ((i : ℕ) + 1)) O.c' ℂ) (B : AnFib X Dc.bas Dc.idx Dc.e x X.Λ y), B.Marked mk → B.Reads 1 y.s ϑ →
      evR (T.Q.Xo ((i : ℕ) + 1)) O.c' f y = c0 * ((R.xi (tup t) xk : Circle) : ℂ) * κ' *
        clsSum (inC O.c') X Dc.hr Dc.bas Dc.idx Dc.eL (O.w t) (O.La t) (O.Nc t) (O.gam t) (O.vol t) (O.ep t)
          (fun j => O.io (xs j)) X.Λ v Y x := by
  letI : Algebra O.c'.F ℂ := (inC O.c').toAlgebra
  letI : Algebra (O.dδ t).c₂.F ℂ := ((inC O.c').comp ((O.dδ t).eF.symm : (O.dδ t).c₂.F →+* O.c'.F)).toAlgebra
  intro y B hB hϑ
  have halg : ∀ s : O.c'.F, algebraMap (O.dδ t).c₂.F ℂ ((O.dδ t).eF s) = algebraMap O.c'.F ℂ s := fun s => rfl
  obtain ⟨hlev, hA₂, hnab⟩ := hP.cov t
  obtain ⟨y₂, B₂, hov₂, hB₂, hrd⟩ := MarkLift.exists_lift_marked _ _ _ _ _ O.c' _ (O.dδ t) halg hlev hT.laws.pins.2.1.2 hA₂
    (fun h => absurd h hpq) _ g X Dc.bas Dc.idx Dc.e x X.Λ y B Dc.sympl hx hsd mk mk₂ hm hB hm₂ hov
  obtain ⟨-, cga, hio⟩ := hP.io
  have h1 := evR_eq_clsSum GlobalTheory.ChartFree.chartIndep _ _ _ _ _ O.c' _ (O.dδ t) halg hnab _ g X Dc.bas Dc.idx Dc.e x X.Λ y y₂ B₂ hov₂
    Dc.sympl hx hsd _ Dc.hr Dc.eL hrk hn Dc.dir_eq ϑ v κ' (hrd ϑ hϑ) hv hκ mk₂ hm₂ hB₂ (O.Cl' t) (O.w t) (O.La t) (O.Nc t)
    (O.gam t) (O.vol t) (O.ep t) _ O.io xs (wtA (κ i))
    (fun j => ⟨((hP.reps t).1 j).1, ((hP.reps t).1 j).2.2.1, ((hP.reps t).1 j).2.2.2.1⟩)
    (fun j => mem_HHa_of_span _ _ _ _ _ _ (hio.2.2.1 ▸ LinearMap.mem_range_self _ _)) Y hY f hf
  subst hxk
  rw [h1, hc t X g Dc.bas Dc.idx Dc.e k xk mk₂ hX hp Dc.sympl ⟨Dc.per_eq, Dc.ty_eq⟩ hΛ hk hm₂ ha₂ y₂ B₂ hB₂]
  rfl

end GlobalTheory.PtId
