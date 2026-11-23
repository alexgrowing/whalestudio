import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWTie
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibExtMarked
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrthonormalNegFirstFamilyFrameCartanMoveStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AnalyticFibreDescriptionLevelMoveMarkingCompStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicThetaOfTestFunctionExistsLawsFockVectorsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassSumLatticeForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormRationality
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormSignIndependent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormScalarExtension
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormHeckeEigen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaDataLevelFormsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGroupActsByLiftTranslationPrincipalType
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfOfBasePins
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ClassSumEvalComplexPointEqClassical
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsLiftMarked
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ProdLevelOneThetaEqVacuumTheta
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FramedPointGeneratorIsThetaLevelOne
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DualHalfLevelMarkingExistsAndMatch
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HalfIntegralGeneratorAddConjEqOne
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtOfMemGfC
import Development.AbelianVarietyTheory.Proofs.HeightProofs.NoCommonZeroIffOfSec
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EqOfForallAlgClosed
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EmbeddingsDifferOnInteger
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.CmHostUnitAddConjEqOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.PolyDerivMonomialOne

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.WeilParts

namespace GlobalTheory.OneMapRef

theorem mem_HHa_span {T : Type} (r : T → ℕ) (n : ℕ) (k : Type) [Field k] (cc : T → T) (isX : T → Prop) (a : T → ℕ → ℕ)
    {P : MvPolynomial (Letter T r n) k} (h : P ∈ Submodule.span k (HHa r n k cc isX a)) : P ∈ HHa r n k cc isX a := by
  classical
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

section Marks

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {r : ℕ} {L : Lt E r} {mk : Dw.La →ₗ[𝓞 E] (Fin r → E)}

theorem isMark_sign (h : IsMark l L mk) (ε : ℤˣ) : IsMark l L ((ε : ℤ) • mk) := by
  rcases Int.units_eq_one_or ε with rfl | rfl
  · simpa using h
  · have e : ∀ a, (((-1 : ℤˣ) : ℤ) • mk) a = -mk a := fun a => by simp
    refine ⟨fun a => by rw [e]; exact neg_mem (h.mem a), fun a ha ⟨u, hu, hu'⟩ => h.inj a ha ⟨-u, neg_mem hu, ?_⟩,
      fun v hv => ?_⟩
    · rw [smul_neg, ← hu', e, neg_neg]
    · obtain ⟨a, ha, u, hu, hu'⟩ := h.surj v hv
      exact ⟨-a, neg_mem ha, u, hu, by rw [e, map_neg, neg_neg, hu']⟩

open CategoryTheory MonObj in

theorem marked_of_congr {Xo : Moduli Dw l} {c : Coeff l} [Algebra c.F ℂ] {g : ℕ} {X : Data E r}
    {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r} {e : Fin g ≃ Lt1 Dw} {x : Frame X.Ψ r}
    {y : FrPt Xo c ℂ} (A : AnFib X bas idx e x L y) {mk' : Dw.La →ₗ[𝓞 E] (Fin r → E)}
    (h : A.Marked mk) (hc : ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), ∃ u ∈ L, mk a = mk' a + l.M • u) :
    A.Marked mk' := by
  intro a ha
  obtain ⟨u, hu, e'⟩ := hc a ha
  have hM : (l.M : E) ≠ 0 := by have := l.three_le; exact_mod_cast (by omega : l.M ≠ 0)
  have hadd : ∀ u v, pv X idx x (u + v) = pv X idx x u + pv X idx x v := fun u v => by
    unfold pv; rw [per_add]; rfl
  rw [h a ha, e', smul_add, ← Nat.cast_smul_eq_nsmul E, inv_smul_smul₀ hM, hadd, A.ex_add,
    (A.ex_ker _).2 ⟨u, hu, rfl⟩, _root_.mul_one]

end Marks

theorem kernel_value {D : D7} {S T : HSp D} {r g : ℕ} {hr : T.rank = r} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
    {X : Data D.host.E r} {eT : D.what₂.Tau ≃ X.Ψ} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r}
    (hS : IsSet ψ θ S T hr X eT bas) {χS χT : (AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (hom : IsWeilDatumO ψ S T χS χT om) {q : ℕ} (hp : X.p0 = q) {Z : Fam T} (hZ : IsONeg T q Z) {h : GA D S} (hh : h ∈ GfC S)
    {γ : GA D T} (hγ : γ ∈ GQ T) (k : GA D T) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (Q : MvPolynomial (FVar D T.rank S.rank) ℂ) {φ : TF S.rank g} (hφ : GlobalTheory.SW.IsSB φ)
    (hz : Zak ψ θ hr eT bas idx (frOf hr eT (mvZ θ (γ * k) Z)) φ (om (h, γ * k) f)) {q0 : ℕ} (hq : X.p0 + q0 = r) :
    thetaKO om h k (fv ψ θ S T q Z f Q) = thP X hq bas idx φ (toP S hr eT hq Q) (frOf hr eT (mvZ θ (γ * k) Z)) := by
  subst hp
  obtain ⟨hZ', hc, -⟩ := (GlobalTheory.T.orthonormalNegFirstFamily_frame_cartan_move D S T r g hr ψ θ X eT bas idx hS Z hZ).2.2.2.2 (γ * k)
  have h1 := GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ S hh
  obtain ⟨h2, h3⟩ := GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ S T χS χT om hom hS.2.1 (fun _ => 1) (fun _ => 1) (fun _ => 1)
    (fun _ => 1) (cartZ T X.p0 Z) (cartZ T X.p0 (mvZ θ (γ * k) Z)) Z (mvZ θ (γ * k) Z) h (γ * k)
    (fun τ => by rw [h1]) hc (fun τ => by rw [h1, Matrix.mul_one]) (fun _ => rfl) f hf Q
  have h4 := (((GlobalTheory.T.adelicTheta_of_testFunction_exists_laws_fockVectors D S T r g hr ψ θ X eT bas idx hS _ hZ').1 φ hφ).2 _ hz).2.2.2.2.2.2 q0 hq Q
  rw [← h4]
  have h5 := hom.om_aut 1 (one_mem _) γ hγ _ (hom.om_pres (h, k) _ h2)
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, _root_.one_mul, h3] at h5
  exact h5.symm

theorem isThetaFunO_of_isVacO {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {sS : Fam S} {sT : Fam T}
    {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)} {f : WO S T → ℂ}
    (h : IsVacO ψ θ S T sS sT LS LT f) : IsThetaFunO ψ S T f := h.2.2

theorem thR_smul_of_prod {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} {X : Data E r}
    {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r} {x : Frame X.Ψ r} {v : TF n g}
    {th : (Fin g → ℂ) → ℂ} {κ : ℂ} (h : ∀ z : Fin n → Fin g → ℂ, ∏ b, th (z b) = κ * thA X bas idx v x z) (a : ℂ)
    (w : Ker.WR X n) :
    a * (Ker.gaussR X bas idx x (Ker.zR X idx x w) * ∏ b, th (Ker.zR X idx x w b)) = Ker.thR X bas idx ((a * κ) • v) x w := by
  rw [h]
  simp only [Ker.thR, thA, SW.thS, Pi.smul_apply, smul_eq_mul, _root_.mul_assoc, tsum_mul_left]
  ring

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {F : Face D A}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
  {i : Fin D.R.m}

def TermAt (O : OMDat T.toCore R i Unit (fun _ => A.μ0)) (ε : ℤˣ) : Prop :=
  ∀ (t : Unit) (h : O.Cl' t → GA D (Vc D i)) (J' : Subgroup (Bridge.Gf (Vc D i))), RepsR R i A.μ0 h (O.bad t) J' (O.Lh t) (O.gam t) (O.vol t) → ∀ (k : O.Cl' t) (g' : GA D (Wc D i)) (X : Data D.host.E D.R.r) (eT : D.what₂.Tau ≃ X.Ψ) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin D.R.r), IsSet R.ψ R.θ (Vc D i) (Wc D i) (rank_Wc i) X eT bas → X.p0 = (T.Q.Dw ((i : ℕ) + 1)).q → ∀ L : Lt D.host.E D.R.r, SelfD X L → latW (rank_Wc i) L = latG (Wc D i) g' → ∀ v : TF (Vc D i).rank g, IsVac X bas (T.Q.H.w0 : D.host.E) (tens (stdL D.host.E (Vc D i).rank) L) v → ∀ a : ℂ, Zak R.ψ R.θ (rank_Wc i) eT bas idx (frOf (rank_Wc i) eT (mvZ R.θ g' (baseZ R i))) (a • v) (R.ωP i A.μ0 (1, g') (R.vacP i)) → ∀ mk₂ : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E), (∀ b, mk₂ b ∈ L) → MarkAd (rank_Wc i) (O.dδ t).l₂ (iotaW T i) g' mk₂ → ∀ Y : (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (O.dδ t).l₂) → Matrix (Fin (Vc D i).rank) (Fin D.R.r) D.host.E, IsRoots (O.dδ t).l₂ L ((ε : ℤ) • mk₂) (O.Nc t k) Y → GlobalTheory.SW.IsSB (gphi X bas (T.Q.H.w0 : D.host.E) (O.La t k).La L v (fun q => inC O.c' (O.w t k q)) Y) ∧ Zak R.ψ R.θ (rank_Wc i) eT bas idx (frOf (rank_Wc i) eT (mvZ R.θ g' (baseZ R i))) ((a * inC O.c' (O.ep t k * ((((O.La t k).mIdx (O.Nc t k) D.R.r : O.c'.F))⁻¹ * ((Nat.card (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (O.dδ t).l₂) : O.c'.F))⁻¹ * ((O.La t k).zCard (O.Nc t k) D.R.r : O.c'.F)))) • gphi X bas (T.Q.H.w0 : D.host.E) (O.La t k).La L v (fun q => inC O.c' (O.w t k q)) Y) (R.ωP i A.μ0 (h k, g') (R.vP i A.μ0))

def IoAt (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (O : OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : ℂ)
    (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) : Prop :=
  ∀ x : VsV D i O.c'.F, ∃ Q : PolF D (Wc D i).rank (Vc D i).rank, (∀ f, IsThetaFunO R.ψ (Vc D i) (Wc D i) f → pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A))) f (R.ioP i (PiTensorProduct.tprod ℂ u) (O.c0' x)) = fv R.ψ R.θ (Vc D i) (Wc D i) (T.Q.Dw ((i : ℕ) + 1)).q (baseZ R i) f Q) ∧ ∀ (X : Data D.host.E D.R.r) (eT : D.what₂.Tau ≃ X.Ψ) (g : ℕ) (Dc : Dic (T.Q.Dw ((i : ℕ) + 1)) O.c' (inC O.c') X g (T.Q.Dw ((i : ℕ) + 1)).p (Vc D i).rank (wtA (κ i))), (∀ ρ, (eT ρ).1 = tauE D ρ) → MvPolynomial.C ph * toP (Vc D i) (rank_Wc i) eT Dc.hr Q = MvPolynomial.C ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℝ) : ℂ) * MvPolynomial.rename Dc.eL (MvPolynomial.map (inC O.c') (O.io x))

def CovAt (O : OMDat T.toCore R i Unit (fun _ => A.μ0)) (c0 : ℂ) : Prop :=
  ∀ (ε : ℤˣ) (t : Unit) (g' : GA D (Wc D i)) (X : Data D.host.E D.R.r) (eT : D.what₂.Tau ≃ X.Ψ) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin D.R.r) (e : Fin g ≃ Lt1 (T.Q.Dw ((i : ℕ) + 1))), IsSet R.ψ R.θ (Vc D i) (Wc D i) (rank_Wc i) X eT bas → X.p0 = (T.Q.Dw ((i : ℕ) + 1)).q → Matched T.Q.c O.s0 X idx e → ∀ L : Lt D.host.E D.R.r, SelfD X L → latW (rank_Wc i) L = latG (Wc D i) g' → ∀ mk₂ : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E), (∀ b, mk₂ b ∈ L) → MarkAd (rank_Wc i) (O.dδ t).l₂ (iotaW T i) g' mk₂ → letI : Algebra (O.dδ t).c₂.F ℂ := ((inC O.c').comp ((O.dδ t).eF.symm : (O.dδ t).c₂.F →+* O.c'.F)).toAlgebra; ∀ (y₂ : FrPt (O.dδ t).Xo₂ (O.dδ t).c₂ ℂ) (A₂ : AnFib X bas idx e (frOf (rank_Wc i) eT (mvZ R.θ g' (baseZ R i))) L y₂), A₂.Marked ((ε : ℤ) • mk₂) → evR (O.dδ t).Xo₂ (O.dδ t).c₂ (O.dδ t).cδ y₂ = c0 * ((O.xi t (Matrix.GeneralLinearGroup.det (finHom (Wc D i) g')) : ℂˣ) : ℂ)

theorem io_mem (O : OMDat T.toCore R i Unit (fun _ => A.μ0))
    (hP : O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0)) (x : VsV D i O.c'.F) :
    O.io x ∈ HHa (T.Q.Dw ((i : ℕ) + 1)).mult (Vc D i).rank O.c'.F ComplexEmbedding.conjugate (InPsi T.Q.H)
      (fun τ j => wtA (κ i) (τ, j)) :=
  hP.io.2.elim fun _ h => mem_HHa_span _ _ _ _ _ _ (h.2.2.1 ▸ LinearMap.mem_range_self _ _)

end GlobalTheory.OneMapRef

end
