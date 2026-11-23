import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecoStabTrivial
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPointOfLastCoordinateDilationOnePrime
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteAdeleIdempotentOfFMulSelf
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryClassRepresentativesBijective
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteAdeleProjectionIntegralReduction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsVTOver
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FrameGlInt

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mat_int {p : SplitPt D k} {S : HSp D} {L : Lat S} (hL : ∀ z, z ∈ L ↔ z ∈ intVec D S.rank)
    (β : Frame p S (Fin S.rank)) {Λ : Submodule 𝒪[k] (Fin S.rank → k)} (h : β.IsLat L Λ) (g : GL (Fin S.rank) k)
    (hg : g • Λ = Λ) (r s : Fin S.rank) : (β.b * g.val * β.b') r s ∈ 𝒪[k] := by
  have hmem : ∀ x, x ∈ Λ ↔ ∀ r, (β.b *ᵥ x) r ∈ 𝒪[k] := fun x => by
    rw [h x, GlobalTheory.SeeSaw.StdOff.mem_latV_int hL]
    exact forall_congr' fun r =>
      ((p.int_iff _).trans (and_iff_right (GlobalTheory.SeeSaw.StdOff.sec_mem_idAt p _)).symm).symm
  have h1 : β.b' *ᵥ Pi.single s 1 ∈ Λ := (hmem _).2 fun r => by
    rw [Matrix.mulVec_mulVec, β.bb', Matrix.one_mulVec, Pi.single_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  have h2 : g • (β.b' *ᵥ Pi.single s 1) ∈ Λ := hg ▸ Submodule.smul_mem_pointwise_smul _ _ _ h1
  have h3 := (hmem _).1 h2 r
  convert h3 using 1
  rw [show g • (β.b' *ᵥ Pi.single s 1) = g.val *ᵥ (β.b' *ᵥ Pi.single s 1) from rfl, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, Matrix.mulVec_single_one]
  rfl

theorem finM_mul (V : HSp D) {n : ℕ} (hn : V.rank = n) (g h : GA D V) :
    GlobalTheory.AdForm.finM V hn (g * h) = GlobalTheory.AdForm.finM V hn g * GlobalTheory.AdForm.finM V hn h := by
  simp [GlobalTheory.AdForm.finM, Formalism.L2.Theta.mt, Matrix.map_mul, Matrix.submatrix_mul_equiv]

theorem prF_finM (q : SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt q.e PP) (V : HSp D)
    {n : ℕ} (hn : V.rank = n) (g : GA D V) (r s : Fin n) :
    q.prF he (GlobalTheory.AdForm.finM V hn g r s) = (Formalism.L2.Theta.mt V g).map q.pr ((finCongr hn).symm r) ((finCongr hn).symm s) := by
  simp [GlobalTheory.AdForm.finM, Matrix.reindex_apply, SplitPt.prF_toEAf]

theorem finM_one (V : HSp D) {n : ℕ} (hn : V.rank = n) : GlobalTheory.AdForm.finM V hn 1 = 1 := by
  simp [GlobalTheory.AdForm.finM, Formalism.L2.Theta.mt]

end GlobalTheory.FrameGlInt

namespace GlobalTheory.FrameGlInt

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

set_option maxHeartbeats 1600000 in

theorem exists_int (p : SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt p.e PP) (S : HSp D)
    {n : ℕ} (hn : S.rank = n) (hgram : S.gram.reindex (finCongr hn) (finCongr hn) = 1) {L : Lat S}
    (hL : ∀ z, z ∈ L ↔ z ∈ intVec D S.rank) (β : Frame p S (Fin S.rank)) {Λ : Submodule 𝒪[k] (Fin S.rank → k)}
    (hlat : β.IsLat L Λ) (g : GL (Fin S.rank) k) (hgl : g • Λ = Λ) :
    ∃ δ : GL (Fin n) (GlobalTheory.AdForm.EF D), δ.1 = GlobalTheory.AdForm.finM S hn (β.gl g) ∧
      δ ∈ Formalism.UG.UPts (sigD D) (1 : Matrix (Fin n) (Fin n) D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) ∧
      (∀ r r', δ.1 r r' ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) ∧
      (∀ r r', (δ⁻¹).1 r r' ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) := by
  obtain ⟨⟨x, hx0⟩, hx⟩ := GlobalTheory.AdForm.RdVal.finM_mem S hn _ hgram.symm (β.gl g)
  refine ⟨x, hx, hx0, ?_⟩
  have hgl' : g⁻¹ • Λ = Λ := by
    conv_lhs => rw [← hgl]
    exact inv_smul_smul g _
  have hcomp : ∀ h : GL (Fin S.rank) k, h • Λ = Λ → ∀ r s,
      toEAf D p.e * GlobalTheory.AdForm.finM S hn (β.gl h) r s ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    intro h hh r s
    rw [← p.prF_mem_iff he]
    have e1 := prF_finM p he S hn (β.gl h) r s
    rw [β.gl_mat h] at e1
    exact e1 ▸ mat_int hL β hlat h hh _ _
  set σ := Formalism.UG.sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) with hσ

  have hu0 : Formalism.UG.cT σ x.1 * ((1 : Matrix (Fin n) (Fin n) D.host.E).map
      (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))) * x.1 =
      (1 : Matrix (Fin n) (Fin n) D.host.E).map (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := hx0
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at hu0
  have hinvM : (x⁻¹).1 = Formalism.UG.cT σ x.1 := by
    calc (x⁻¹).1 = (Formalism.UG.cT σ x.1 * x.1) * (x⁻¹).1 := by rw [hu0, one_mul]
      _ = _ := by rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]

  have hxi : (x⁻¹).1 = GlobalTheory.AdForm.finM S hn (β.gl g⁻¹) := by
    have h1 : x.1 * GlobalTheory.AdForm.finM S hn (β.gl g⁻¹) = 1 := by
      rw [hx, ← finM_mul, ← map_mul, mul_inv_cancel, map_one, finM_one]
    calc (x⁻¹).1 = (x⁻¹).1 * (x.1 * GlobalTheory.AdForm.finM S hn (β.gl g⁻¹)) := by rw [h1, mul_one]
      _ = _ := by rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  obtain ⟨hf, -⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D p.e PP he
  have hσmem : ∀ y ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, σ y ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    fun y hy => GlobalTheory.Mem.Col2.sigR_mem_rInt D.sp.cm hy
  have hσσ : ∀ y, σ (σ y) = y := Formalism.L2.DIV.sigR_sigR D.sp.cm
  have hcA : toEAf D (cA D p.e) = σ (toEAf D p.e) := GlobalTheory.AdForm.RdVal.toEAf_sig p.e
  have hint : ∀ r r', x.1 r r' ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    intro r r'
    have hs := congrArg (toEAf D) (β.gl_supp g ((finCongr hn).symm r) ((finCongr hn).symm r'))
    have hxr : x.1 r r' = toEAf D (Formalism.L2.Theta.mt S (β.gl g) ((finCongr hn).symm r) ((finCongr hn).symm r')) := by
      rw [hx]; rfl
    have hcm : toEAf D ((1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) ((finCongr hn).symm r) ((finCongr hn).symm r')) ∈
        Formalism.L2.Herm.intAf D.host.F D.host.E := by
      rw [Matrix.one_apply]; split_ifs
      · rw [RingHom.map_one]; exact one_mem _
      · rw [RingHom.map_zero]; exact zero_mem _
    rw [Matrix.sub_apply, RingHom.map_mul, RingHom.map_sub, RingHom.map_add, hcA, ← hxr] at hs
    have hdec : x.1 r r' = toEAf D p.e * x.1 r r' + σ (toEAf D p.e * (x⁻¹).1 r' r) +
        (1 - toEAf D p.e - σ (toEAf D p.e)) *
          toEAf D ((1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) ((finCongr hn).symm r) ((finCongr hn).symm r')) := by
      have e2 : σ (toEAf D p.e * (x⁻¹).1 r' r) = σ (toEAf D p.e) * x.1 r r' := by
        rw [hinvM, map_mul]
        show σ (toEAf D p.e) * σ (σ (x.1 r r')) = _
        rw [hσσ]
      rw [e2]
      linear_combination (-1 : GlobalTheory.AdForm.EF D) * hs
    rw [hdec]
    refine add_mem (add_mem ?_ ?_) (mul_mem (sub_mem (sub_mem (one_mem _) hf) (hσmem _ hf)) hcm)
    · exact hx ▸ hcomp g hgl r r'
    · exact hσmem _ (hxi ▸ hcomp g⁻¹ hgl' r' r)
  exact ⟨hint, fun r r' => by
    rw [hinvM]
    exact hσmem _ (hint r' r)⟩

end GlobalTheory.FrameGlInt

theorem GlobalTheory.AdForm.frameGl_int : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ j (hj : j ≤ B.R.m) (i : ι) (v : (I.atT l u a).vT), Formalism.L2.NTheta.IsIdemAt (p i).e v.1 → ∀ (g : GL (Fin ((I.rec7 l Z).sp.X j).rank) k) (s : 𝓀[k]ˣ), g • Q j i = s • Q j i →
    ∃ δ : TC.GA B (B.R.N j), δ.1 = finM _ (rankN (I.rec7 l Z) j hj) ((β j i).gl g) ∧ δ ∈ Formalism.L2.Herm.UstdAf B.sp.cm (B.R.N j) ∧
      (∀ r r', δ.1 r r' ∈ Formalism.L2.DIV.RInt B.host.F B.host.E) ∧ (∀ r r', (δ⁻¹).1 r r' ∈ Formalism.L2.DIV.RInt B.host.F B.host.E) := by
  intro B X I hOk hPins l Z u a k _ _ _ _ ι p β Q L hStd j hj i v hIdem g s hgs
  have hg1 : gramN (I.rec7 l Z) j hj = 1 := ((TC.spaces_in_coordinates I hOk hPins l Z).2.2.2 j hj).1
  obtain ⟨-, hT⟩ := hStd
  obtain ⟨hL, hT'⟩ := hT j hj
  obtain ⟨hlat, -⟩ := hT' i
  have hgl : g • (Q j i).lat = (Q j i).lat := by
    have := congrArg GlobalTheory.LatPair.Pair.lat hgs
    rwa [GlobalTheory.LatPair.Pair.smul_lat, GlobalTheory.LatPair.Pair.dia_lat] at this
  obtain ⟨δ, h1, h2, h3, h4⟩ := GlobalTheory.FrameGlInt.exists_int (p i) hIdem _ (rankN (I.rec7 l Z) j hj) hg1 hL (β j i) hlat g hgl
  exact ⟨δ, h1, h2, h3, h4⟩

end
