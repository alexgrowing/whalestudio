import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KerDatTuple
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Formalism.LocalToGlobal.IndefiniteReal.RhoGeo
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BaseRatAtOfPhaseOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicLiftEqGeometricClassSumAllTuples
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameConstantsOfCharacterisationCore
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstUpToCenter
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EmbeddingsDifferOnInteger
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverSectionsLinearIndependentAdelicReadings
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FunctionFieldAlgClosedLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverValueCore
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFrameOfRichRec
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

namespace GlobalTheory.OnCmp.CoverRoot

theorem xiVal_cast {D : D7} (T : Full D) (hT : LawsFull T) (j n : ℕ) (hj : InR D j) (σ : T.Q.c.F →+* ℂ)
    (hσ : σ = T.toTop.toCore.σ₀) (W : HSp D) (hV : T.V j σ = W) (hr : W.rank = D.R.r) :
    ∃ (U₂ : _) (dict₂ : _), CXiVal W hr σ (Tup := Unit) (fun _ => T.dδ j n) U₂ dict₂
      (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota j) (T.x₀ j σ) fun _ => T.xi := by
  subst hσ hV
  obtain ⟨_, U, d, h⟩ := hT.xiVal j hj n
  exact ⟨U, d, h⟩

theorem value_mem {D : D7} (T : Full D) (hT : LawsFull T) (j n : ℕ) (hj : InR D j) (τ : (T.dδ j n).c₂.F →+* ℂ)
    (hτ : τ = (T.dδ j n).c₂.F.val.toRingHom) (y : FrPt (T.dδ j n).Xo₂ (T.dδ j n).c₂ (CAt τ)) :
    ∃ z, toC (evR (T.dδ j n).Xo₂ (T.dδ j n).c₂ (T.dδ j n).cδ y) = τ z := by
  subst hτ
  obtain ⟨Cls, _, _, δ, gdet, -, h⟩ := hT.sh.dRoot j hj n
  exact ⟨_, h y⟩

open GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal GlobalTheory.AdTh.CoverVal in
set_option maxHeartbeats 1000000 in

theorem cover_value_root : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ χ : (AE D)ˣ →* Circle, ChrEq χ (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) → ∃ c0' : ℂ, c0' ∈ D.what₂.embLL.range ∧ (∃ m : ℕ, 0 < m ∧ c0' ^ m = 1) ∧ (∀ (X : ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E D.R.r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin D.R.r) (e : Fin g ≃ Lt1 (T.Q.Dw ((i : ℕ) + 1))) (k : GA D (Wc D i)) (xk : (AE D)ˣ) (mk : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)), GlobalTheory.AdTh.IsMod (Wc D i) (rank_Wc i) X → X.p0 = (T.Q.Dw ((i : ℕ) + 1)).q → GlobalTheory.ThFr.IsSympl X bas → GlobalTheory.AdTh.IdxIs T.Q.c (O i).s0 X idx e → GlobalTheory.AdTh.latR (rank_Wc i) (latG (Wc D i) k) = X.Λ → IsDetRoot (Wc D i) k xk → GlobalTheory.Dict.IsMark (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂ X.Λ mk → GlobalTheory.AdTh.MarkAd (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂ (Wc D i) (rank_Wc i) (iotaW T.J i) k mk → letI : Algebra (T.dδ ((i : ℕ) + 1) (Vc D i).rank).c₂.F ℂ := ((O i).s0.comp ((T.dδ ((i : ℕ) + 1) (Vc D i).rank).eF.symm : (T.dδ ((i : ℕ) + 1) (Vc D i).rank).c₂.F →+* T.Q.c.F)).toAlgebra; ∀ (y₂ : FrPt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).Xo₂ (T.dδ ((i : ℕ) + 1) (Vc D i).rank).c₂ ℂ) (A₂ : GlobalTheory.Dict.AnFib X bas idx e (GlobalTheory.AdTh.frMove R.θ (Wc D i) (rank_Wc i) X k (fun τ => T.J.x₀ ((i : ℕ) + 1) (O i).s0 τ.1)) X.Λ y₂), A₂.Marked mk → evR (T.dδ ((i : ℕ) + 1) (Vc D i).rank).Xo₂ (T.dδ ((i : ℕ) + 1) (Vc D i).rank).c₂ (T.dδ ((i : ℕ) + 1) (Vc D i).rank).cδ y₂ = c0' * ((χ xk : Circle) : ℂ)) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw O hT hR i hO v _ hval0 hrun χ hχ
  have hI : TieIn T.J R κ v₀ := ⟨fw.laws, fw.alg_eq, fw.kap, fw.hv₀, fw.chiR, fw.x0⟩
  have hs : (O i).s0 = T.toTop.toCore.σ₀ := sOv_eq _ _ _
  obtain ⟨U₂, dict₂, c0, hroot, hc⟩ := xiVal_cast T hT _ (Vc D i).rank (inR i) (O i).s0 hs (Wc D i) (O i).hV (rank_Wc i)
  obtain ⟨hU, hW, g', e', F', ik, φ, th, hth, hD, hval⟩ := hc ()
  have hlev := hT.sh.dLev _ (inR i) (Vc D i).rank
  have hA := hT.lvA _ (inR i) (Vc D i).rank
  obtain ⟨-, -, -, χ₁, hχ₁, hxi⟩ := hrun
  obtain rfl : χ₁ = χ := GlobalTheory.ChrEqUnique.idc_unique D _ _ _ hχ₁ hχ
  obtain ⟨hX₀, hon₀, -, hp₀, -, -, h1, -, hΨ₀, -⟩ := GlobalTheory.AdTh.models_at_record_core D G Pl0 T0 A T.J R F κ v₀ hR hI i (O i).s0
    hs (T.dict _ (O i).s0 1).1
  have hτ : (O i).s0.comp ((T.dδ ((i : ℕ) + 1) (Vc D i).rank).eF.symm : (T.dδ ((i : ℕ) + 1) (Vc D i).rank).c₂.F →+* T.Q.c.F) =
      (T.dδ ((i : ℕ) + 1) (Vc D i).rank).c₂.F.val.toRingHom := RingHom.ext fun _ => rfl
  have hσ : GoodEmb (T.dδ ((i : ℕ) + 1) (Vc D i).rank).c₂ ((O i).s0.comp
      ((T.dδ ((i : ℕ) + 1) (Vc D i).rank).eF.symm : (T.dδ ((i : ℕ) + 1) (Vc D i).rank).c₂.F →+* T.Q.c.F)) := rfl
  have hmod : ∀ j, IsMod (Wc D i) (rank_Wc i) ((U₂ ()).X j) := fun j =>
    isMod_of _ _ _ (hW j) fun ρ => ((hU.2.1 j).2 _).2 ((hΨ₀ _).1 ((hX₀.psi _).2 ⟨ρ, rfl⟩))
  have hor : ∀ j, IsOrthogonalFrame ((U₂ ()).X j) (T.x₀ ((i : ℕ) + 1) (O i).s0) := fun j τ hτ => by
    have hsp := sameSp_of (hmod j) hX₀ ((hU.2.1 j).1.trans hp₀.symm)
    rw [hsp.gm, hsp.p0]
    exact hon₀ ⟨τ, hsp.psi ▸ hτ⟩
  obtain ⟨Wt⟩ := nonempty_uw ((Formalism.L2.PjFree.isUnf_ofPj _).2 hU)
  obtain ⟨hex, -, hrat, hmul⟩ := GlobalTheory.Member.isDetRoot_laws D (Wc D i)
  have hv : ∀ (k : GA D (Wc D i)) (xk : (AE D)ˣ), IsDetRoot (Wc D i) k xk →
      rdU (U₂ ()) (T.dδ ((i : ℕ) + 1) (Vc D i).rank).cδ (dict₂ () k).1 (dict₂ () k).2 = c0 * ((χ₁ xk : Circle) : ℂ) := by
    intro k xk hxk
    obtain ⟨γ', hγ', h2, h3, -⟩ := hD.2 k
    obtain ⟨a, ha⟩ := hrat γ' hγ'
    have hv := hval k γ' ⟨hγ', h2, h3⟩
    rw [hxi _ _ (hmul _ _ _ _ ha hxk), map_mul, hχ.1.2 a, _root_.one_mul] at hv
    exact hv
  have hat := GlobalTheory.AdTh.dict_atComp_markAd D _ _ _ _ _ _ _ (U₂ ()) hσ hU h1 hA R.θ (Wc D i) (rank_Wc i)
    (dict₂ ()) (iotaW T.J i) g' e' F' ik φ th _ hR.models.inf hmod hor hth hD Wt
  refine ⟨c0, ?_, hroot, ?_⟩
  · obtain ⟨x1, hx1⟩ := hex 1
    obtain ⟨hon, -⟩ := hat 1
    obtain ⟨-, hu2, -⟩ := GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular D.host.E D.R.r ((U₂ ()).X (dict₂ () 1).1).p0
      ((U₂ ()).X (dict₂ () 1).1).Ψ ((U₂ ()).X (dict₂ () 1).1).Gm ((U₂ ()).X (dict₂ () 1).1).Gm_herm
    have hd : (dict₂ () 1).2 ∈ ((U₂ ()).X (dict₂ () 1).1).dom := (hu2 _ hon).1
    obtain ⟨z, hz⟩ := value_mem T hT _ _ (inR i) _ hτ ((U₂ ()).un _ ⟨_, hd⟩)
    have h2 : c0 * ((χ₁ x1 : Circle) : ℂ) = _ := ((hv 1 x1 hx1).symm.trans (dif_pos hd)).trans hz
    obtain ⟨y, hy⟩ := GlobalTheory.BigOn.CoreWit.exists_val_of_chrEq hχ x1
    obtain ⟨b, hb⟩ := hval0 y
    have hres := res_embLL T.J hI.alg hI.laws.pins.2.2.1
    refine ⟨algebraMap T.Q.c.F D.what₂.LL ((T.dδ ((i : ℕ) + 1) (Vc D i).rank).eF.symm z) / b, ?_⟩
    rw [map_div₀, hb, ← hy, div_eq_iff (Circle.coe_ne_zero _), h2]
    exact (DFunLike.congr_fun hres _).trans (DFunLike.congr_fun hs.symm _)
  · intro X g bas idx e k xk mk hX hp hsy hi hL hxk hmk hk y₂ A₂ hA₂
    obtain ⟨hon, γ, ⟨hγ, hl, hf⟩, hma, -⟩ := hat k
    obtain ⟨hd, hpt⟩ := point_eq (Formalism.L2.PjFree.Unf.ofPj (U₂ ())) hσ hU h1 hA hR.models.inf (Wc D i) (rank_Wc i) (iotaW T.J i)
      _ Wt (dict₂ () k).1 (dict₂ () k).2 γ k hγ (hmod _) hl hf hon hma X g bas idx e mk hX hp hsy hi hL hmk hk y₂ A₂ hA₂
    exact (evR_eq_of_point _ hlev.2.2.2.2.2.2.2.1 _ y₂ hpt).trans ((dif_pos hd).symm.trans (hv k xk hxk))

end GlobalTheory.OnCmp.CoverRoot
