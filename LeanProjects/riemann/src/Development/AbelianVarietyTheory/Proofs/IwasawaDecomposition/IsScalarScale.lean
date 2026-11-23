import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsModelHolomorphicIntegralExtremalWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtremalVectorsHolomorphicModelUniqueUpToPhase

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.HeightCounting
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SerVec

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
  {v₀ v₁ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}

theorem evW_scale {j : Fin D.R.m} {c : D.what₂.Tau → ℂ}
    (h : ∀ τ, v₁ j (sg0 D A3.A) τ = c τ • v₀ j (sg0 D A3.A) τ) (x : S.WL ((j : ℕ) + 1)) :
    evW YS v₁ j x = (∏ τ, c τ) • evW YS v₀ j x := by
  change (Rl.HW j (sg0 D A3.A)).e _ (v₁ j _) = (∏ τ, c τ) • (Rl.HW j (sg0 D A3.A)).e _ (v₀ j _)
  rw [show v₁ j (sg0 D A3.A) = fun τ => c τ • v₀ j (sg0 D A3.A) τ from funext h]
  exact MultilinearMap.map_smul_univ _ _ _

theorem realRd_scale {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) {j : Fin D.R.m} (b : Bool) {C : ℂ} (hC : C ≠ 0)
    (h : ∀ x, evW YS v₁ j x = C • evW YS v₀ j x) (ν : ℂ) :
    realRd YS v₁ hρ i j b (C * ν) = realRd YS v₀ hρ i j b ν := by
  have key : ∀ x, evK YS v₁ hρ i j b x = C • evK YS v₀ hρ i j b x := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, smul_zero]
    | add x y hx hy => rw [map_add, map_add, hx, hy, smul_add]
    | tmul a f => rw [evK_tmul, evK_tmul, h, smul_comm]
  refine LinearMap.ext fun f => ?_
  change (C * ν)⁻¹ • evK YS v₁ hρ i j b _ = ν⁻¹ • evK YS v₀ hρ i j b _
  refine (congrArg _ (key _)).trans ?_
  rw [smul_smul, mul_inv, mul_right_comm, inv_mul_cancel₀ hC, one_mul]

theorem isScale_scale {j : Fin D.R.m} {c : D.what₂.Tau → ℂ}
    (h : ∀ τ, v₁ j (sg0 D A3.A) τ = c τ • v₀ j (sg0 D A3.A) τ) (B : GlobalTheory.ExportSeries.Base (Vc D j) (Wc D j)) {s : ℂ}
    (hs : IsScale Rl v₀ B s) : IsScale Rl v₁ B ((∏ τ, c τ) * s) := by
  obtain ⟨gramR, c0R, c0L, ht, u, hu, hF⟩ := hs
  refine ⟨gramR, c0R, c0L, ht, fun τ => c τ • u τ, fun τ => ?_, fun F => ?_⟩
  · rw [h, ← hu]; rfl
  · rw [MultilinearMap.map_smul_univ, map_smul, mul_smul, ← hF]
    exact map_smul (GlobalTheory.ExportSeries.harmFn (Wc D j).rank B.w B.F.BS) _ _

theorem isNorm_scale {j : Fin D.R.m} {c : D.what₂.Tau → ℂ} (hc : ∀ τ, c τ ≠ 0)
    (h : ∀ τ, v₁ j (sg0 D A3.A) τ = c τ • v₀ j (sg0 D A3.A) τ) (B : GlobalTheory.ExportSeries.Base (Vc D j) (Wc D j)) {ν : ℂ}
    (hν : IsNorm Rl v₀ B ν) : IsNorm Rl v₁ B ((∏ τ, c τ) * ν) := by
  obtain ⟨h0, s, hs, n, hn, he⟩ := hν
  refine ⟨mul_ne_zero (Finset.prod_ne_zero_iff.2 fun τ _ => hc τ) h0, _, isScale_scale h B hs, n, hn, ?_⟩
  rw [mul_pow, he, ← mul_pow, mul_left_comm]

theorem scale_symm {j : Fin D.R.m} {c : D.what₂.Tau → ℂ} (hc : ∀ τ, c τ ≠ 0)
    (h : ∀ τ, v₁ j (sg0 D A3.A) τ = c τ • v₀ j (sg0 D A3.A) τ) (τ : D.what₂.Tau) :
    v₀ j (sg0 D A3.A) τ = (c τ)⁻¹ • v₁ j (sg0 D A3.A) τ := by
  rw [h, smul_smul, inv_mul_cancel₀ (hc τ), one_smul]

theorem isScalar_scale {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) {j : Fin D.R.m} (b : Bool) {c : D.what₂.Tau → ℂ}
    (hc : ∀ τ, c τ ≠ 0) (h : ∀ τ, v₁ j (sg0 D A3.A) τ = c τ • v₀ j (sg0 D A3.A) τ) {ν : ℂ}
    (hν : IsScalar YS v₀ hρ i j b ν) : IsScalar YS v₁ hρ i j b ((∏ τ, c τ) * ν) := by
  have hC : (∏ τ, c τ) ≠ 0 := Finset.prod_ne_zero_iff.2 fun τ _ => hc τ
  have hc' : ∀ τ, (c τ)⁻¹ ≠ 0 := fun τ => inv_ne_zero (hc τ)
  have h' := scale_symm hc h
  refine ⟨mul_ne_zero hC hν.ne, fun ⟨ν', h1⟩ => isNorm_scale hc h _ (hν.norm ⟨_, isNorm_scale hc' h' _ h1⟩), fun ⟨ν', h1, h2⟩ => ?_⟩
  rw [realRd_scale YS hρ i b hC (evW_scale YS h)]
  refine hν.rat ⟨_, isNorm_scale hc' h' _ h1, ?_⟩
  rw [realRd_scale YS hρ i b (Finset.prod_ne_zero_iff.2 fun τ _ => hc' τ) (evW_scale YS h')]
  exact h2

theorem exists_cell {ρ : Setup D.ntw} {hρ : ρ.Good} {i : D.ntw.Tw} {j : Fin D.R.m} {b : Bool} {rd rd' : Rd ρ D.nexp i j b}
    (e : rd' = rd) (t : CellTie hρ D.nexp rd) : ∃ t' : CellTie hρ D.nexp rd', t'.rdV = t.rdV := by
  subst e
  exact ⟨t, rfl⟩

theorem serAt_scale {c : Fin D.R.m → D.what₂.Tau → ℂ} (hc : ∀ j τ, c j τ ≠ 0)
    (h : ∀ j τ, v₁ j (sg0 D A3.A) τ = c j τ • v₀ j (sg0 D A3.A) τ)
    (hv : ∀ j, FWT.IsChosenExtremalVector Rl.toRealDat j (sg0 D A3.A) (v₁ j _)) {Xe : Formalism.L2.NExpTied D}
    {PV : ∀ i : Fin D.R.m, principalLevelFrame.RowPsi (Vc D i) D.R.nV} {cf : Formalism.L2.Host.CharFrame D}
    {Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host} (Z : SerAt YS v₀ Xe PV cf Pq) :
    Nonempty (SerAt YS v₁ Xe PV cf Pq) := by
  have e : ∀ i j b, realRd YS v₁ Z.ex.good i j b ((∏ τ, c j τ) * Z.ex.ν i j b) = realRd YS v₀ Z.ex.good i j b (Z.ex.ν i j b) :=
    fun i j b => realRd_scale YS _ i b (Finset.prod_ne_zero_iff.2 fun τ _ => hc j τ) (evW_scale YS (h j)) _
  choose t ht using fun i j b => exists_cell (e i j b) (Z.ex.tie i j b)
  refine ⟨{ ex :=
              { ρ := Z.ex.ρ
                good := Z.ex.good
                pin := Z.ex.pin
                vec := hv
                ν := fun i j b => (∏ τ, c j τ) * Z.ex.ν i j b
                scalar := fun i j b => isScalar_scale YS _ i b (hc j) (h j) (Z.ex.scalar i j b)
                tie := t
                hecke := fun i j b => by rw [e]; exact Z.ex.hecke i j b
                univ := Z.ex.univ }
            bad := Z.bad
            ch := Z.ch
            join := fun i j b k Q ψ hA hT => ?_
            sup := Z.sup
            off := Z.off
            lam := Z.lam
            lam_ok := Z.lam_ok
            lam_teich := Z.lam_teich
            lam_C := Z.lam_C
            lam_q := Z.lam_q
            lam_tie := Z.lam_tie }⟩
  obtain ⟨ω, h1, h2⟩ := Z.join i j b k Q ψ hA hT
  refine ⟨ω, h1, fun f g => ?_⟩
  rw [← h2 f g, ← ht i j b]

theorem serAt_vec : ∀ {D : D7} (X : RealSide D) (g₀ g₁ : GlobalTheory.RealGeo.GeoHalf X.core X.R.toRealDat fun _ => 1) {S : NX.RatDat D.ntw} (YS : NX.NExpRealS X.R X.cG S) (Xe : Formalism.L2.NExpTied D) (PV : ∀ i : Fin D.R.m, principalLevelFrame.RowPsi (Vc D i) D.R.nV) (cf : Formalism.L2.Host.CharFrame D) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host), SerAt YS g₀.v₀ Xe PV cf Pq → Nonempty (SerAt YS g₁.v₀ Xe PV cf Pq) := by
  intro D X g₀ g₁ S YS Xe PV cf Pq Z
  have hL : ∀ j, FWT.ExtLine (X.R.MW j (sg0 D X.A3.A)) := fun j =>
    GlobalTheory.HolLowOnce.extLine_of_holShape D _ _ _
      (GlobalTheory.DefLift.holShape_fixed D X.Γ X.Pl0 X.T X.A3.A _ X.R.toRealDat X.char.models.order j).1
  choose c hc h using fun j τ => hL j _ _ (g₀.fw.hv₀ j _).1 (g₁.fw.hv₀ j _).1 τ
  exact serAt_scale YS (fun j τ h0 => by simpa [h0] using hc j τ) h (fun j => g₁.fw.hv₀ j _) Z

end GlobalTheory.SerVec
