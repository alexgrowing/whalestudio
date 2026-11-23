import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUniOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticModelFlagHeightFifth
open NumberField CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula Formalism.L2.Pj GlobalTheory GlobalTheory.ArInt GlobalTheory.VB GlobalTheory.CovTest GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.TwoLat GlobalTheory.OrthFilt GlobalTheory.VdmRec GlobalTheory.TrueGeo
open GlobalTheory.LieVB (omega)
open GlobalTheory.LocM (tanEv)
open Formalism.MainNotions.DIV.Cons (intO)
open scoped Classical
open GlobalTheory.LieFilt

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieFilt

open GlobalTheory.ArLieBase.MetOfEig

theorem evalPt_app_comp {R : Type} [CommRing R] {X W : Scheme.{0}} (x : Sp R ⟶ W) (j : W ⟶ X) (V : X.Opens)
    (h : ⊤ ≤ (x ≫ j) ⁻¹ᵁ V) (h' : ⊤ ≤ x ⁻¹ᵁ (j ⁻¹ᵁ V)) (f : Γ(X, V)) :
    TangentOrigin.evalPt x (j ⁻¹ᵁ V) h' (j.app V f) = TangentOrigin.evalPt (x ≫ j) V h f := by
  simp only [TangentOrigin.evalPt, Scheme.Hom.comp_appLE, CommRingCat.hom_comp, RingHom.comp_apply]

theorem exists_affine_le_all {X : Scheme.{0}} {ι : Type} [Finite ι] (x : X) (U₀ : X.Opens) (U : ι → X.Opens)
    (h₀ : x ∈ U₀) (h : ∀ i, x ∈ U i) : ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧ V ≤ U₀ ∧ ∀ i, V ≤ U i := by
  let O : X.Opens := ⟨(U₀ : Set X) ∩ ⋂ i, (U i : Set X), U₀.2.inter (isOpen_iInter_of_finite fun i => (U i).2)⟩
  have hx : x ∈ O := ⟨h₀, Set.mem_iInter.2 h⟩
  obtain ⟨V, hV, hxV, hle⟩ := exists_isAffineOpen_mem_and_subset hx
  exact ⟨V, hV, hxV, fun z hz => (hle hz).1, fun i z hz => Set.mem_iInter.1 (hle hz).2 i⟩

theorem orthEmb_of_tanCoord : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
    {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
    {β : Oz →+* c.F} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) {F : Type} [Field F] [NumberField F] (e : F ≃+* c.F)
    {X W : Scheme.{0}} {q : X ⟶ Sp (𝓞 F)} {jB : W ⟶ X} {πB : W ⟶ gen Z} (ρ : X ⟶ Z.X), IsPullback jB (πB ≫ genStr Z ≫ spMap e.toRingHom) q (spMap (algebraMap (𝓞 F) F)) → jB ≫ ρ = πB ≫ genι Z →
    ∀ {L : X.Modules} {g : ℕ} {ℓ : ∀ ch : VB.Chart (omega Z.t.G) g, Fin g → Γ(L, ρ ⁻¹ᵁ ch.U)} (hℓ : ∀ ch, VB.IsFrame (ℓ ch)), IsVB (omega Z.t.G) g →
    ∀ (G : ∀ σ', EigMet Z σ') (hL : VMetric q L g), MetDict Z e ρ hℓ G hL →
    ∀ {M : (E →+* ℂ) → X.Modules} (t : ∀ τ, FrAssign Z (M τ) (Dw.mult τ) jB) (h : ∀ τ, VMetric q (M τ) (Dw.mult τ))
      (T : ∀ τ, M τ ⟶ L), (∀ τ, IsLieFrames Z e jB πB (M τ) _ τ false (t τ)) →
      (∀ τ, IsLieMet Z e q jB πB (M τ) _ τ false rfl G (h τ) (t τ)) → (∀ τ, TanCoord Z jB πB (t τ) ρ hℓ (T τ)) →
    OrthEmb hL h T := by
  intro E _ _ _ H Dw l Xo c Oz _ β Z F _ _ e X W q jB πB ρ hpb hρ L g ℓ hℓ hω G hL hMD M t h T hLF hLM hTC
  have key : ∀ (σ₀ : 𝓞 F →+* ℂ) (y : CxPts q σ₀), ∃ (cL : VB.Chart L g) (cM : ∀ τ, VB.Chart (M τ) (Dw.mult τ)),
      y ∈ CxPts.ptsIn q σ₀ cL.U ∧ (∀ τ, y ∈ CxPts.ptsIn q σ₀ (cM τ).U) ∧
      (∀ τ i j, HermFrame.form ((hL.met σ₀).G cL y) (cL.crd q σ₀ ((T τ).app _ ((cM τ).e i)) y)
        (cL.crd q σ₀ ((T τ).app _ ((cM τ).e j)) y) = ((h τ).met σ₀).G (cM τ) y i j) ∧
      ∀ τ τ', τ ≠ τ' → ∀ i j, HermFrame.form ((hL.met σ₀).G cL y) (cL.crd q σ₀ ((T τ).app _ ((cM τ).e i)) y)
        (cL.crd q σ₀ ((T τ').app _ ((cM τ').e j)) y) = 0 := by
    intro σ₀ y
    obtain ⟨σ, rfl⟩ := exists_comp_eq σ₀
    let x₀ : X := y.1 (IsLocalRing.closedPoint ℂ)
    obtain ⟨U, eω, hU, heω⟩ := hω (ρ x₀)
    let ch : VB.Chart (omega Z.t.G) g := ⟨U, eω, heω⟩
    choose UM eM hUM heM using fun τ => (h τ).isVB x₀
    obtain ⟨V, hVa, hyV, hVU, hVM⟩ := exists_affine_le_all x₀ (ρ ⁻¹ᵁ ch.U) UM hU hUM
    let cM : ∀ τ, VB.Chart (M τ) (Dw.mult τ) := fun τ =>
      ⟨V, fun i => Twist.resM (M τ) (hVM τ) (eM τ i), (heM τ).res (hVM τ)⟩
    let cL : VB.Chart L g := ⟨ρ ⁻¹ᵁ ch.U, ℓ ch, hℓ ch⟩
    have hy₀ : y ∈ CxPts.ptsIn q _ V := CxPts.mem_ptsIn.2 hyV
    have hyL : y ∈ CxPts.ptsIn q _ cL.U := CxPts.mem_ptsIn.2 (hVU hyV)
    let zg : Sp ℂ ⟶ W := hpb.lift y.1 (spMap σ) (by rw [y.2, MetOfEig.spMap_comp])
    have hzg : zg ≫ jB = y.1 := hpb.lift_fst _ _ _
    have hzs : zg ≫ πB ≫ genStr Z ≫ spMap e.toRingHom = spMap σ := hpb.lift_snd _ _ _
    let yc : CxPts (genStr Z) (σ.comp e.symm.toRingHom) := ⟨zg ≫ πB, genStr_of hzs⟩
    have hpt : yc.1 ≫ genι Z = zg ≫ πB ≫ genι Z := Category.assoc _ _ _
    have hx : ⊤ ≤ (zg ≫ jB) ⁻¹ᵁ V := by rw [hzg]; exact hy₀
    have hb : ∀ τ, IsEigBasis Z (σ.comp e.symm.toRingHom) (yc.1 ≫ genι Z) τ
        (t τ V (cM τ).e (cM τ).isFrame ℂ zg hx) := fun τ => by
      rw [hpt]; exact (hLF τ).1 V (cM τ).e (cM τ).isFrame ℂ zg hx σ hzs
    let u : EigFrame Z (σ.comp e.symm.toRingHom) (yc.1 ≫ genι Z) :=
      ⟨fun τ => t τ V (cM τ).e (cM τ).isFrame ℂ zg hx, fun τ i => ((hb τ).1 i).1, fun τ i => ((hb τ).1 i).2,
        fun τ w hw he => (hb τ).2 w ⟨hw, he⟩⟩
    have hyρ : y.1 ≫ ρ = yc.1 ≫ genι Z := by rw [hpt, ← hzg, Category.assoc, hρ]
    have hch : ⊤ ≤ (yc.1 ≫ genι Z) ⁻¹ᵁ ch.U := by rw [← hyρ]; exact hyL
    let P : Matrix (Fin g) (Σ τ, Fin (Dw.mult τ)) ℂ :=
      fun b s => cL.crd q _ ((T s.1).app V ((cM s.1).e s.2)) y b
    have hP : IsTanMat Z (yc.1 ≫ genι Z) ch (fun s : Σ τ, Fin (Dw.mult τ) => u.v s.1 s.2) P := by
      show IsTanMat Z ((zg ≫ πB) ≫ genι Z) ch
        (fun s : Σ τ, Fin (Dw.mult τ) => t s.1 V (cM s.1).e (cM s.1).isFrame ℂ zg hx s.2) P
      rw [Category.assoc]
      rintro ⟨τ, i⟩ hv hV b
      have := hTC τ ch V hVU hVa (cM τ).e (cM τ).isFrame ℂ zg hx hx i hv hV b
      refine Eq.trans ?_ this
      simp only [P, Matrix.map_apply, Matrix.of_apply]
      rw [cL.crd_eq _ le_rfl hVU hy₀ b, CxPts.ev_eq hy₀, CxPts.evHom_eq_evalPt, Twist.resM_self]
      exact (evalPt_congr hzg.symm _ _ hx _).trans (evalPt_app_comp zg jB V hx hx _).symm
    obtain ⟨h1, h2⟩ := hMD σ y yc hyρ ch hch u P hP
    refine ⟨cL, cM, hyL, fun _ => hy₀, fun τ i j => ?_, fun τ τ' hne i j => h2 ⟨τ, i⟩ ⟨τ', j⟩ hne⟩
    have hM := hLM τ σ y zg yc hzg rfl (cM τ) hx u (fun _ => rfl)
    rw [hM]
    exact h1 τ i j
  refine ⟨fun τ σ V s s' y hy => ?_, fun τ τ' hne σ V s s' y hy => ?_⟩
  · obtain ⟨cL, cM, hyL, hyM, h1, -⟩ := key σ y
    rw [(hL.met _).form_eq cL hyL _ _ hy, ((h τ).met _).form_eq (cM τ) (hyM τ) _ _ hy,
      cL.crd_app (cM τ) (T τ) s hy (hyM τ), cL.crd_app (cM τ) (T τ) s' hy (hyM τ), ← HermFrame.form_chg]
    congr 1
    ext i j
    rw [HermFrame.chg_apply]
    exact h1 τ i j
  · obtain ⟨cL, cM, hyL, hyM, -, h2⟩ := key σ y
    rw [(hL.met _).form_eq cL hyL _ _ hy, cL.crd_app (cM τ) (T τ) s hy (hyM τ),
      cL.crd_app (cM τ') (T τ') s' hy (hyM τ'), HermFrame.form_mulVec]
    have h0 : ∀ (A : Matrix (Fin g) (Fin (Dw.mult τ)) ℂ) (B : Matrix (Fin g) (Fin (Dw.mult τ')) ℂ)
        (K : Matrix (Fin g) (Fin g) ℂ), (∀ i j, HermFrame.form K (fun a => A a i) (fun a => B a j) = 0) →
        A.transpose * K * B.conjTranspose.transpose = 0 := fun A B K hh => by
      ext i j
      have := hh i j
      rw [HermFrame.form_eq_sum, Finset.sum_comm] at this
      simpa [Matrix.mul_apply, Finset.sum_mul] using this
    rw [h0]
    · simp
    · exact h2 τ τ' hne

end GlobalTheory.LieFilt

end
