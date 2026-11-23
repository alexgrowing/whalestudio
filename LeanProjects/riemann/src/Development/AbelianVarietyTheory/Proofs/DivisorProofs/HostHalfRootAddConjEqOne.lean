import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasWitness
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPushFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanThetaAnFib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApplyPvNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsObjMapPhi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnFibFrEqOfExLeftEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalMatrixIsRatOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvREqOfReadsSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermFormReindex
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsLetterRowWeightDictionary
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FramedPointGeneratorIsThetaLevelOne
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianFormAtFrameLaws
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CastFrMemDom
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelOneThetaEqSmulOfSelfDualLattice
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UniformisationComponentLatticesMarkings
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitFrameEqOrthonormalMulTriangular
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaMultiplierUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.CmHostUnitAddConjEqOne
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NegBaseElementImNegBaseEmbedding

open AlgebraicGeometry CategoryTheory NumberField Matrix MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.FrameEquiv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000

namespace GlobalTheory.FrameEquiv.GenMove

section Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem perFr_cast {r : ℕ} {X' X : Data E r} (h : SameSp X' X)
    (x : Frame X'.Ψ r) (v : Fin r → E) (τ : E →+* ℂ) (i : ℕ) :
    perFr X' x v τ i = perFr X (castFr h.psi x) v τ i := by
  obtain ⟨h1, h2, h3, -, -⟩ := h
  cases X
  cases X'
  dsimp only at h1 h2 h3
  subst h1 h2 h3
  rfl

theorem hostHalfRoot_add_conj_eq_one (H : Geo.Tor.Host E) : (H.w0 : E) + cc (H.w0 : E) = 1 := by
  have := congrArg (algebraMap (𝓞 E) E) (PullbackSections.CVA.cmHostUnit_add_conj_eq_one H)
  rw [map_add, map_one] at this
  exact (congrArg _ (H.bar_eq _).symm).trans this

variable {H : Geo.Tor.Host E} {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} [Algebra c.F ℂ]
  {r g : ℕ}

open MonObj in

theorem marked_congr {X : Data E r}
    {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r} {e : Fin g ≃ Lt1 Dw} {x : Frame X.Ψ r}
    {L : Lt E r} {y : FrPt Xo c ℂ} (A : AnFib X bas idx e x L y) {mk mk' : Dw.La →ₗ[𝓞 E] (Fin r → E)}
    (h : A.Marked mk) (hc : ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), ∃ u ∈ L, mk a = mk' a + l.M • u) :
    A.Marked mk' := by
  intro a ha
  obtain ⟨u, hu, e'⟩ := hc a ha
  have hM : (l.M : E) ≠ 0 := by have := l.three_le; exact_mod_cast (by omega : l.M ≠ 0)
  have hadd : ∀ u v, pv X idx x (u + v) = pv X idx x u + pv X idx x v := fun u v => by
    unfold pv; rw [per_add]; rfl
  rw [h a ha, e', smul_add, ← Nat.cast_smul_eq_nsmul E, inv_smul_smul₀ hM, hadd, A.ex_add,
    (A.ex_ker _).2 ⟨u, hu, rfl⟩, _root_.mul_one]

theorem ne_zero_of_meanOne {X : Data E r} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r}
    {x : Frame X.Ψ r} {L : Lt E r} {θ : (Fin g → ℂ) → ℂ} (h : MeanOne X bas idx x L θ) : θ ≠ 0 := by
  rintro rfl
  obtain ⟨_, _, _, _, h⟩ := h
  simp at h

theorem values_of_move {X' X : Data E r} (h : SameSp X' X)
    {bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X'.Λ} {idx' : Fin g ≃ X'.Ψ × Fin r}
    {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r} {e : Fin g ≃ Lt1 Dw}
    {x' : Frame X'.Ψ r} {x : Frame X.Ψ r} {y y' y₂ : FrPt Xo c ℂ} (A : AnFib X' bas' idx' e x' X'.Λ y)
    (A₂ : AnFib X bas idx e x X.Λ y₂) (ga : GL (Fin r) E) (hs' : IsSympl X' bas') (hs : IsSympl X bas)
    (hx' : x' ∈ X'.dom) (hL' : SelfD X' X'.Λ) (hun : IsUn X ga)
    (hpv : ∀ v, pv X' idx' x' v = pv X idx (castFr h.psi x') v)
    (hty : ∀ j, rowType X' (idx' j) = rowType X (idx j)) (hA : l.A = 1)
    (e1 : mapL ga X'.Λ = X.Λ) (e2 : lact ga (castFr h.psi x') = x)
    {gM gA : Dw.La →ₗ[𝓞 E] Dw.La} (hlev : levR (gM, gA) y y')
    {mk' mk : Dw.La →ₗ[𝓞 E] (Fin r → E)} (hmk : IsMark l X.Λ mk) (hm' : A.Marked mk') (hm : A₂.Marked mk)
    (hc : ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), ∃ u ∈ X.Λ,
      (ga : Matrix (Fin r) (Fin r) E) *ᵥ mk' (gM a) = mk a + l.M • u)
    {θ θ₂ : (Fin g → ℂ) → ℂ} (hθ : A.Reads 1 y.s θ) (hθ₂ : A₂.Reads 1 y₂.s θ₂)
    (h1 : MeanOne X' bas' idx' x' X'.Λ θ) :
    ∃ t : ℂ, θ₂ = t • θ ∧ (∃ v, θ (pv X' idx' x' v) ≠ 0) ∧
      (∀ v, pv X idx x ((ga : Matrix (Fin r) (Fin r) E) *ᵥ v) = pv X' idx' x' v) ∧
      (∀ z w, hx X bas idx x z w = hx X' bas' idx' x' z w) ∧
      ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, evR Xo c f y₂ = t ^ n * evR Xo c f y' := by
  obtain ⟨A', hR', hM'⟩ := GlobalTheory.AnMove.anFib_move E H Dw l Xo c r g X' bas' idx' e x' _ y y' A hs' hx' hL' gM gA hlev
  obtain ⟨hd, -, hsd, A'', hR'', -, hM''⟩ := GlobalTheory.Dict.anFib_move E H Dw l Xo c r g X' X h bas' idx' bas idx e x' _ y' A' ga
    hs' hs hx' hL' hun hpv hty
  have hR := hR'' _ (hR' _ hθ)
  have hM := hM'' _ (hM' _ hm')
  have hx1 := h.castFr_mem_dom hx'
  obtain ⟨-, -, him', -⟩ := hx_laws E r X' g bas' idx' 0 hs' Even.zero x' hx'
  obtain ⟨-, -, -, -, -, -, huniq, hinv⟩ := hx_laws E r X g bas idx 0 hs Even.zero _ hx1
  obtain ⟨-, hpv2, -, hhx2⟩ := hinv ga hun
  have hhx (z w) : hx X bas idx (lact ga (castFr h.psi x')) z w = hx X' bas' idx' x' z w := by
    rw [hhx2, hx_eq_hermForm idx']
    refine ((huniq X.Λ X.Λ_span).2 _ (Hm_isHermitian idx' hs' hx') (fun u _ v _ => ?_) z w).symm
    rw [← hpv, ← hpv, ← hx_eq_hermForm, him', h.EF_eq]
  clear hR'' hM''
  revert A'' hd hsd
  rw [e1]
  subst e2
  intro hd hsd A'' hR hM
  have hM2 : A''.Marked mk := marked_congr A'' hM hc
  have hex := GlobalTheory.Dict.anFib_ex_eq E H Dw l Xo c r g X bas idx e _ _ y' y₂ A'' A₂ hs hd hsd hA mk hmk hM2 hm
  have hfr := GlobalTheory.FrameEquiv.anFib_fr_eq_of_ex_left_eq E H Dw l Xo c r g X bas idx e _ _ y' y₂ A'' A₂ hs hd hsd hex
  have t1 := isTheta1_of_reads_generator E H Dw l Xo c r g X bas idx e _ _ y' A'' hs hd hsd θ hR
  have t2 := isTheta1_of_reads_generator E H Dw l Xo c r g X bas idx e _ _ y₂ A₂ hs hd hsd θ₂ hθ₂
  have hne := ne_zero_of_meanOne h1
  obtain ⟨t, ht⟩ := ThetaOne.exists_eq_smul_of_isTheta1 E r X g bas idx 0 hs Even.zero (H.w0 : E) H.w0.2
    (hostHalfRoot_add_conj_eq_one H) _ hsd _ hd θ₂ θ t2 t1 hne
  refine ⟨t, ht, exists_apply_pv_ne_zero E r X' g bas' idx' hs' x' hx' θ t1.1.continuous hne,
    fun v => (hpv2 v).trans (hpv v).symm, hhx, ?_⟩
  exact GlobalTheory.FrameEquiv.evR_eq_of_reads_smul E H Dw l Xo c r g X bas idx e _ _ y' y₂ A'' A₂ hs hd hsd hex hfr θ t hR (ht ▸ hθ₂)

end Classical

section Adelic

open GlobalTheory.IndefiniteRowSideFullHecke.ColumnDataLaws

theorem map_mul_zero {A B m n : Type} [CommRing A] [CommRing B] [Fintype m] (π : A →+* B) (P : Matrix m m A)
    (w : Matrix m n A) (h : ∀ a b, π (w a b) = 0) (a : m) (b : n) : π ((P * w) a b) = 0 := by
  rw [Matrix.mul_apply, map_sum]
  exact Finset.sum_eq_zero fun i _ => by rw [map_mul, h, mul_zero]

theorem map_mul_congr {A B K m n : Type} [CommRing A] [CommRing B] [CommRing K] [Fintype m] (π : A →+* B)
    (j : K →+* A) (P : Matrix m m K) (w : Matrix m n A) (X : Matrix m n K) (h : ∀ a b, π (w a b) = π (j (X a b)))
    (a : m) (b : n) : π ((P.map j * w) a b) = π (j ((P * X) a b)) := by
  rw [Matrix.mul_apply, Matrix.mul_apply, map_sum, map_sum, map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_mul, map_mul, map_mul, h]; rfl

variable {D : D7}

theorem isRealPt_actO (V W : HSp D) {ga : GL (Fin W.rank) D.host.E} {δ : GA D W} (hδ : GlobalTheory.Ker.IsRatOf W ga δ)
    {X : Matrix (Fin W.rank) (Fin V.rank) D.host.E} {w : WO V W} (hw : IsRealPt V W X w) :
    IsRealPt V W ((ga : Matrix (Fin W.rank) (Fin W.rank) D.host.E) * X) (actO V W 1 δ w) := by
  rw [GlobalTheory.OneMapRef.RatPt.actO_one, hδ]
  refine ⟨fun a b => ?_, fun a b => ?_⟩
  · exact map_mul_zero (finPart D) _ _ hw.1 a b
  · exact map_mul_congr (infPart D) (incA D) _ _ _ hw.2 a b

theorem eFrame_move {V W : HSp D} {ψ : AddChar (AF D.host.F) ℂ}
    {om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} (hψ : IsStdChar D ψ (-1))
    (hom : GlobalTheory.Ker.IsWeak ψ V W om) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) {δ κ : GA D W} (hδ : δ ∈ GQ W)
    {m : ℂ} (hκ : om (1, κ) f = m • f) (g : GA D W) (w : WO V W) :
    eFrame ψ V W om f (δ * g * κ) (actO V W 1 δ w) = m * eFrame ψ V W om f g w := by
  have e : ((1, δ * g * κ) : GA D V × GA D W) = (1, δ) * (1, g) * (1, κ) := by simp
  have hg := hom.om_pres (1, g) f hf
  have h1 := hom.om_aut 1 (one_mem _) δ hδ _ (GlobalTheory.OneMapRef.RatPt.isTheta_heisO hψ hg w)
  rw [hom.om_heis 1 δ w _ hg] at h1
  unfold eFrame
  rw [← h1, e, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hκ, map_smul, map_smul]
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  ring

theorem isUnitFr_of_archM (W : HSp D) (X : Data D.host.E W.rank) (hX : ModelW W rfl X)
    {x₀ : (D.host.E →+* ℂ) → Matrix (Fin W.rank) (Fin W.rank) ℂ} (h0 : IsOrthogonalFrame X x₀)
    {th : X.Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} (hth : ∀ τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th τ))
    (g : GA D W) (x : Frame X.Ψ W.rank)
    (hx : ∀ τ : X.Ψ, mat x τ = Matrix.reindex (finCongr rfl) (finCongr rfl) (archM W (th τ) g) * x₀ τ.1) :
    IsUnitFr X x := by
  refine ((GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular _ _ X.p0 X.Ψ X.Gm X.Gm_herm).2.1 x
    fun τ => ?_).2
  rw [← h0 τ.1 τ.2, hx τ, GlobalTheory.RecDictModel.gram_eq, GlobalTheory.RecDictModel.gram_eq, hX.1]
  have hu := GlobalTheory.RecDictModel.archM_unitary W (hth τ) g
  have e1 : ∀ A : Matrix (Fin W.rank) (Fin W.rank) ℂ, Matrix.reindex (finCongr rfl) (finCongr rfl) A = A :=
    fun A => rfl
  have e2 : ((-(Matrix.reindex (finCongr rfl) (finCongr rfl) W.gram).transpose).map τ.1).transpose =
      -(W.gram.map τ.1) := by
    ext a b; simp
  rw [e1, e2, Matrix.conjTranspose_mul]
  congr 1
  conv_rhs => rw [← hu]
  simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]

end Adelic

end GlobalTheory.FrameEquiv.GenMove

open GlobalTheory.FrameEquiv.GenMove GlobalTheory.IndefiniteRowSideFullHecke.ColumnDataLaws in

theorem GlobalTheory.FrameEquiv.frameConst_levelMove : ∀ (D : D7) (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (W : HSp D) (U : Unf Xo c σ W.rank) (dict : GA D W → Σ k, Frame (U.X k).Ψ W.rank) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin W.rank) (Fin W.rank) ℂ), GeoSet W U dict x₀ → LatEmb W ι → ∀ (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (L : Lt D.host.E W.rank) (f₀ : WO V W → ℂ) (mu : GA D W → ℂ), AdSet V W ψ θ om s L f₀ mu → ∀ cc : U.Comp → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.ColumnDataLaws.IsFrameConst W rfl dict ι x₀ ψ V om f₀ mu cc → ∀ (κ : GA D W) (lev levA : Dw.La →ₗ[𝓞 D.host.E] Dw.La), GlobalTheory.IndefiniteRowSideFullHecke.GeneralDiagonalMatrix.StabLat W κ → GlobalTheory.IndefiniteRowSideFullHecke.GeneralDiagonalMatrix.LevAgrees W ι l.M (Mfr l) κ lev → ∀ (h : GA D W) (hx : (dict h).2 ∈ (U.X (dict h).1).dom) (y' : FrPt Xo c (CAt σ)), levR (lev, levA) (U.un (dict h).1 ⟨(dict h).2, hx⟩) y' → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ), ∀ f ∈ sec Xo c a V.rank, cc (dict h).1 * toC (evR Xo c f y') = cc (dict (h * κ)).1 * rdU U f (dict (h * κ)).1 (dict (h * κ)).2 := by
  intro D H Dw l Xo c σ W U dict ι x₀ hG hι V ψ θ om s L f₀ mu hAd cc hcc κ lev levA hκ hlev h hx y' hy' a f hf
  obtain ⟨⟨d, hd⟩, hall⟩ := hcc
  obtain ⟨_, ⟨γ, hγ⟩, hA⟩ := hall d hd h
  obtain ⟨hx₂, ⟨γ', hγ'⟩, hA'⟩ := hall d hd (h * κ)
  obtain ⟨⟨Pm, hPm⟩, hB⟩ := hA γ hγ
  obtain ⟨⟨Pm', hPm'⟩, hB'⟩ := hA' γ' hγ'
  obtain ⟨⟨⟨Hm, ϑ⟩, hp⟩, hC⟩ := hB Pm hPm
  obtain ⟨⟨⟨Hm', ϑ'⟩, hp'⟩, hC'⟩ := hB' Pm' hPm'
  replace hC := hC _ hp
  replace hC' := hC' _ hp'
  clear hA hA' hB hB' hall
  obtain ⟨ga, hs, hrat, hun, e1, e2, hcong⟩ :=
    GlobalTheory.FrameEquiv.LatMove.lattice_move D H Dw l Xo c σ W U dict ι x₀ hG hι d hd κ lev hκ hlev h γ γ' hγ hγ'
  obtain ⟨hσ, hU, h1, hA1, hmod, -, -, -, hor, -⟩ := hG
  obtain ⟨-, -, hom, -, -, ⟨hψ, hvac⟩, hmul, hnorm, -, hstab, -⟩ := hAd
  have hu := isUnitFr_of_archM W _ (hmod _) (hor _) (hd.1 _) _ _ hγ.2
  have hu' := isUnitFr_of_archM W _ (hmod _) (hor _) (hd.1 _) _ _ hγ'.2
  obtain ⟨Wt, hWt⟩ := GlobalTheory.FrameEquiv.hasWitness_of_is D H Dw l Xo c σ _ U hσ hU h1 W rfl dict ι x₀ d hd
  obtain ⟨g, e, F, ik, φ, th⟩ := d
  cases hWt
  have hU' := (Formalism.L2.PjFree.isUnf_ofPj U).2 hU
  have key : ∀ k : U.Comp, SelfD (U.X k) (U.X k).Λ ∧ IsMark l (U.X k).Λ (Wt.mark k) ∧
      ∃ (bas : (Fin Wt.g ⊕ Fin Wt.g → ℤ) ≃ₗ[ℤ] (U.X k).Λ) (idx : Fin Wt.g ≃ (U.X k).Ψ × Fin W.rank),
      IsSympl (U.X k) bas ∧
      (∀ x v j, pv (U.X k) idx x v j = perFr (U.X k) x v (relab c σ (Wt.e j).1) (Wt.e j).2) ∧
      (∀ j, rowType (U.X k) (idx j) = relab c σ (Wt.e j).1) := fun k => by
    obtain ⟨-, hsd, hmk, -⟩ := uw_lattice _ H Dw l Xo c σ _ _ hσ hU' h1 Wt k
    obtain ⟨Dc, hDc, -⟩ := exists_dic _ H Dw l c σ _ Wt.g 0 (U.X k) 0 Wt.e hσ hU.1 (hU.2.1 k).1 (hU.2.1 k).2 hsd
      ⟨fun _ => antitone_const, Even.zero⟩
    have hper := Dc.per_eq
    have hty := Dc.ty_eq
    rw [hDc] at hper hty
    exact ⟨hsd, hmk, Dc.bas, Dc.idx, Dc.sympl, hper, hty⟩
  obtain ⟨hsd, -, bas, idx, hsy, hper, hty⟩ := key (dict h).1
  obtain ⟨-, hmk', bas', idx', hsy', hper', hty'⟩ := key (dict (h * κ)).1
  let _ : Algebra c.F ℂ := σ.toAlgebra
  obtain ⟨A, hM, hR, hm1, hH⟩ := (GlobalTheory.FrameEquiv.canTheta_anFib _ H Dw l Xo c σ _ _ hσ hU' h1 Wt (dict h).1 bas idx hsy hper hty
    ⟨_, hx⟩ hu Pm (fun a j => congrFun (hPm a) j)).2 Hm ϑ hp
  obtain ⟨A₂, hM₂, hR₂, -, hH₂⟩ := (GlobalTheory.FrameEquiv.canTheta_anFib _ H Dw l Xo c σ _ _ hσ hU' h1 Wt (dict (h * κ)).1 bas' idx' hsy'
    hper' hty' ⟨_, hx₂⟩ hu' Pm' (fun a j => congrFun (hPm' a) j)).2 Hm' ϑ' hp'
  obtain ⟨t, ht, ⟨v, hv⟩, hpv, hhx, hval⟩ := values_of_move (y' := y') hs A A₂ ga hsy hsy' hx hsd hun
    (fun v => funext fun j => (hper _ v j).trans ((perFr_cast hs _ _ _ _).trans (hper' _ v j).symm))
    (fun j => (hty j).trans (hty' j).symm) hA1 e1 e2 hy' hmk' hM hM₂ hcong hR hR₂ hm1
  have hf₂ : rdU U f (dict (h * κ)).1 (dict (h * κ)).2 = t ^ V.rank * toC (evR Xo c f y') :=
    (dif_pos hx₂).trans (hval a V.rank f hf)
  obtain ⟨⟨w, hw⟩, hE⟩ := hC (Matrix.of fun i _ => v i)
  have hE1 := hE w hw
  have hE2 := (hC' _).2 _ (isRealPt_actO V W hrat hw)
  have hz : ∀ u, DictDat.coord W dict ⟨Wt.g, Wt.e, Wt.F, Wt.ik, Wt.φ, th⟩ h u = pv _ idx (dict h).2 u :=
    fun u => funext fun j => (hper _ u j).symm
  have hz' : ∀ u, DictDat.coord W dict ⟨Wt.g, Wt.e, Wt.F, Wt.ik, Wt.φ, th⟩ (h * κ) u =
      pv _ idx' (dict (h * κ)).2 u := fun u => funext fun j => (hper' _ u j).symm
  have hcol : ∀ b : Fin V.rank, (fun i => ((ga : Matrix (Fin W.rank) (Fin W.rank) D.host.E) *
      (Matrix.of fun i _ => v i : Matrix (Fin W.rank) (Fin V.rank) D.host.E)) (Fin.cast rfl i) b) =
      (ga : Matrix (Fin W.rank) (Fin W.rank) D.host.E) *ᵥ v := fun b => rfl
  have hcol0 : ∀ b : Fin V.rank, (fun i =>
      (Matrix.of fun i _ => v i : Matrix (Fin W.rank) (Fin V.rank) D.host.E) (Fin.cast rfl i) b) = v := fun b => rfl
  have hmove := eFrame_move hψ hom hvac.theta (mul_mem hγ'.1.1 (inv_mem hγ.1.1)) (hstab κ hκ) (γ * h) w
  have eg : γ' * γ⁻¹ * (γ * h) * κ = γ' * (h * κ) := by group
  rw [eg] at hmove
  have hHH : ∀ z z', hermForm Hm' z z' = hermForm Hm z z' :=
    fun z z' => (hH₂ z z').trans ((hhx z z').trans (hH z z').symm)
  replace hpv : ∀ u, pv (U.X (dict (h * κ)).1) idx' (dict (h * κ)).2
      ((ga : Matrix (Fin W.rank) (Fin W.rank) D.host.E) *ᵥ u) = pv (U.X (dict h).1) idx (dict h).2 u := hpv
  replace hv : ϑ (pv (U.X (dict h).1) idx (dict h).2 v) ≠ 0 := hv
  simp only [hz, hz', hcol, hcol0, hpv, hHH, hmove, hmul, ht, Pi.smul_apply, smul_eq_mul, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, mul_pow] at hE1 hE2
  have n1 : mu h ≠ 0 := norm_ne_zero_iff.1 (by rw [hnorm]; exact one_ne_zero)
  have n2 : mu κ ≠ 0 := norm_ne_zero_iff.1 (by rw [hnorm]; exact one_ne_zero)
  have hc : cc (dict h).1 = cc (dict (h * κ)).1 * t ^ V.rank := by
    apply mul_right_cancel₀ (mul_ne_zero (mul_ne_zero n1 n2) (pow_ne_zero V.rank hv))
    linear_combination hE2 - mu κ * hE1
  rw [hf₂, hc, mul_assoc]
