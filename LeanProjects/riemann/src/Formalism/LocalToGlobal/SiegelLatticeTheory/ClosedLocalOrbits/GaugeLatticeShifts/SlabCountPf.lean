import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabCountPfSteps
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ChiTrivOut

noncomputable section

open scoped Classical ComplexConjugate ENNReal NNReal
open MeasureTheory

namespace Formalism.L2.SG.Pf.SlabCount

open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PoincareInHH.Cut Formalism.L2.SG.TermOp.KExpCut Formalism.L2.SG.Full
  Formalism.L2.SG.Pf.Slab

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Eq

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
  {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem gterm_eq_of {t t' : GTerm X u u' F0 F0' what₂ rows'} (h1 : t.lam = t'.lam) (h2 : t.lam' = t'.lam')
    (n ν : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hn : n ∈ NLam t.lam (lf D F0)) (hν : ν ∈ NLam t.lam' (lf D F0'))
    (he : t'.lin = n * t.lin * ν) : t = t' := by
  obtain ⟨l, m, l', m', c⟩ := t
  obtain ⟨l2, m2, l2', m2', c2⟩ := t'
  dsimp only at h1 h2
  subst h1 h2
  have hc : c = c2 := by
    rw [← Quot.out_eq c, ← Quot.out_eq c2]
    exact Quot.sound ⟨n, hn, ν, hν, he⟩
  subst hc
  rfl

end Eq

theorem countC_of_leviFin (hL : LeviFinC) : CountC := by
  intro D X Y u u'
  obtain ⟨F, hF⟩ := hL D X Y u'
  refine ⟨((∑ Λ₁ ∈ Y.what₂ u', ∑ Λ₂ ∈ Y.what₂ u', (F Λ₁ Λ₂).card : ℕ) : ℝ≥0∞), ENNReal.natCast_ne_top _, ?_⟩
  intro T T' Λ hΛ E hE x
  have hWD : PhWellDef X u Y.hK := Formalism.L2.SG.Pf.phWellDef_holds X u
  have hWD' : PhWellDef X u' Y.hK := Formalism.L2.SG.Pf.phWellDef_holds X u'
  have hLI : PhLeftInv X u Y.hK :=
    phLeftInv_of X u Y.hK hWD (Formalism.L2.SG.Pf.ratLevi_holds X u) (Formalism.L2.SG.Pf.psiProd_holds X u)
  have hLI' : PhLeftInv X u' Y.hK :=
    phLeftInv_of X u' Y.hK hWD' (Formalism.L2.SG.Pf.ratLevi_holds X u') (Formalism.L2.SG.Pf.psiProd_holds X u')

  let I := Σ t : {t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') // t.lam = Λ}, E t.1
  have hlift : ∀ i : I, ∃ (xm : X.B.I.GA) (nm : (VS D).V ≃ₗ[D.host.E] (VS D).V),
      RatLink X xm nm ∧ (i.2 : X.B.I.Ginf) = xm.1 ∧ nm ∈ NLam Λ (lf D (X.Fu u)) := by
    intro i
    have hm : (i.2 : X.B.I.Ginf) ∈ ROset X (X.Fu u) (X.Fu u) Λ Λ 1 := (hE i.1.1 i.1.2).1 i.2.2
    obtain ⟨xm, nm, h1, h2, h3, -⟩ := hm
    exact ⟨xm, nm, h1, h2, h3⟩
  choose xm nm hxm hmx hnm using hlift

  let g : I → X.B.I.GA := fun i => (i.1.1.pt)⁻¹ * xm i
  have hg : ∀ i : I, RatLink X (g i) ((i.1.1.lin)⁻¹ * nm i) := fun i =>
    Formalism.L2.SG.TermOp.Vanish.ratLink_mul X (Formalism.L2.SG.TermOp.Vanish.ratLink_inv X i.1.1.rep.2.1) (hxm i)
  have hgr : ∀ i : I, g i ∈ Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I := fun i => ratLink_mem X (hg i)
  have hdec : ∀ i : I, ∃ p : (Srat X u') × (Y.Dt u'), (p.1 : X.B.I.GA) * (p.2 : X.B.I.GA) = g i :=
    fun i => ((Y.reps u').2 (g i) (hgr i)).exists
  choose p hp using hdec
  let φ : I → Y.Dt u' := fun i => (p i).2
  let G : Y.Dt u' → ℝ≥0∞ := fun δ => ‖Ph X u' Y.hK T' ((δ : X.B.I.GA) * (x, aB Y u Λ))‖ₑ

  have hκ : ∀ i : I, (aB Y u Λ)⁻¹ * (xm i).2 * aB Y u Λ ∈ X.K2 := by
    intro i
    have hn : nm i ∈ NLam ((Y.cs u).lamOf ((Y.cs u).base Λ)) (lf D (X.Fu u)) := by
      rw [(Y.cs u).base_lam Λ hΛ]; exact hnm i
    exact (Formalism.L2.SG.Pf.nilradical_conj_level' D X Y u ((Y.cs u).base Λ) (xm i) (nm i) hn (hxm i)).1
  have e1 : ∀ i : I, ((i.2 : X.B.I.Ginf) * x, aB Y u Λ) = xm i * (x, (xm i).2⁻¹ * aB Y u Λ) := by
    intro i
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_mul]; rw [hmx i]
    · simp only [Prod.snd_mul]; group
  have e2 : ∀ i : I, ((x, aB Y u Λ) : X.B.I.GA) =
      (x, (xm i).2⁻¹ * aB Y u Λ) * (1, (aB Y u Λ)⁻¹ * (xm i).2 * aB Y u Λ) := by
    intro i
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_mul, mul_one]
    · simp only [Prod.snd_mul]; group
  have hA : ∀ i : I, ‖Ph X u Y.hK T ((i.2 : X.B.I.Ginf) * x, aB Y u Λ)‖ₑ = ‖Ph X u Y.hK T (x, aB Y u Λ)‖ₑ := by
    intro i
    rw [e1 i, hLI T _ (Formalism.L2.SG.Pf.RegroupPf.nlam_srat u Λ (hxm i) (hnm i))]
    conv_rhs => rw [e2 i]
    rw [enorm_ph_right Y.hK hWD T _ _ (hκ i)]
  have hB : ∀ i : I, ‖Ph X u' Y.hK T' (i.1.1.pt⁻¹ * ((i.2 : X.B.I.Ginf) * x, aB Y u Λ))‖ₑ = G (φ i) := by
    intro i
    show _ = ‖Ph X u' Y.hK T' (((p i).2 : X.B.I.GA) * (x, aB Y u Λ))‖ₑ
    rw [e1 i, ← mul_assoc, show i.1.1.pt⁻¹ * xm i = g i from rfl, ← hp i, mul_assoc,
      hLI' T' _ (p i).1.2]
    conv_rhs => rw [e2 i, ← mul_assoc]
    rw [enorm_ph_right Y.hK hWD' T' _ _ (hκ i)]

  have hfib : ∀ k : Y.Dt u', ∃ (S : Finset (Submodule (𝓞 D.host.E) (VS D).V × ((VS D).V ≃ₗ[D.host.E] (VS D).V)))
      (e : I → Submodule (𝓞 D.host.E) (VS D).V × ((VS D).V ≃ₗ[D.host.E] (VS D).V)),
      S.card ≤ ∑ Λ₁ ∈ Y.what₂ u', ∑ Λ₂ ∈ Y.what₂ u', (F Λ₁ Λ₂).card ∧
      ∀ i, φ i = k → e i ∈ S ∧ ∀ j, φ j = k → e i = e j → i = j := by
    intro k
    by_cases h0 : ∃ i0, φ i0 = k
    swap
    · exact ⟨∅, fun _ => (⊥, 1), by simp, fun i hi => absurd ⟨i, hi⟩ h0⟩
    obtain ⟨i0, hi0⟩ := h0
    let σ : I → (VS D).V ≃ₗ[D.host.E] (VS D).V := fun i =>
      ((i0.1.1.lin)⁻¹ * nm i0) * ((i.1.1.lin)⁻¹ * nm i)⁻¹
    let e : I → Submodule (𝓞 D.host.E) (VS D).V × ((VS D).V ≃ₗ[D.host.E] (VS D).V) := fun i =>
      (i.1.1.lam', if h : ∃ f ∈ F i0.1.1.lam' i.1.1.lam', f⁻¹ * σ i ∈ NLam i.1.1.lam' (lf D (X.Fu u'))
        then h.choose else 1)
    have hex : ∀ i, φ i = k →
        ∃ f ∈ F i0.1.1.lam' i.1.1.lam', f⁻¹ * σ i ∈ NLam i.1.1.lam' (lf D (X.Fu u')) := by
      intro i hi
      refine hF _ i0.1.1.mem' _ i.1.1.mem' (σ i) (g i0 * (g i)⁻¹)
        (Formalism.L2.SG.TermOp.Vanish.ratLink_mul X (hg i0) (Formalism.L2.SG.TermOp.Vanish.ratLink_inv X (hg i))) ?_ ?_ ?_
      · have h0 := i0.1.1.rep.2.2.1
        have h1 := i.1.1.rep.2.2.1
        exact (Formalism.HermitianLatticesTheory.isom (VS D).hT).mul_mem
          ((Formalism.HermitianLatticesTheory.isom (VS D).hT).mul_mem ((Formalism.HermitianLatticesTheory.isom (VS D).hT).inv_mem h0) (hnm i0).1.1)
          ((Formalism.HermitianLatticesTheory.isom (VS D).hT).inv_mem
            ((Formalism.HermitianLatticesTheory.isom (VS D).hT).mul_mem ((Formalism.HermitianLatticesTheory.isom (VS D).hT).inv_mem h1) (hnm i).1.1))
      · have hpe : ((p i0).2 : X.B.I.GA) = ((p i).2 : X.B.I.GA) :=
          congrArg Subtype.val (hi0.trans hi.symm)
        have hgg : g i0 * (g i)⁻¹ = ((p i0).1 : X.B.I.GA) * ((p i).1 : X.B.I.GA)⁻¹ := by
          rw [← hp i0, ← hp i, hpe]; group
        rw [hgg]
        exact (Srat X u').mul_mem (p i0).1.2 ((Srat X u').inv_mem (p i).1.2)
      · have hs : σ i = (i0.1.1.lin)⁻¹ * (nm i0 * ((nm i)⁻¹ * i.1.1.lin)) := by
          simp only [σ, mul_inv_rev, inv_inv, mul_assoc]
        have ht : Formalism.HermitianLatticesTheory.gmap i.1.1.lin i.1.1.lam' = Λ := i.1.1.rep.2.2.2.1.trans i.1.2
        have ht0 : Formalism.HermitianLatticesTheory.gmap i0.1.1.lin i0.1.1.lam' = Λ := i0.1.1.rep.2.2.2.1.trans i0.1.2
        rw [hs, Formalism.L2.SG.Pf.gmap_mul, Formalism.L2.SG.Pf.gmap_mul, Formalism.L2.SG.Pf.gmap_mul, ht,
          (Formalism.L2.SG.Pf.nlam_inv (hnm i)).1.2, (hnm i0).1.2]
        exact Formalism.L2.SG.Pf.gmap_inv ht0
    refine ⟨(Y.what₂ u').biUnion (fun Λ₂ => (F i0.1.1.lam' Λ₂).image (fun f => (Λ₂, f))), e, ?_, ?_⟩
    · calc ((Y.what₂ u').biUnion (fun Λ₂ => (F i0.1.1.lam' Λ₂).image (fun f => (Λ₂, f)))).card
          ≤ ∑ Λ₂ ∈ Y.what₂ u', ((F i0.1.1.lam' Λ₂).image (fun f => (Λ₂, f))).card := Finset.card_biUnion_le
        _ ≤ ∑ Λ₂ ∈ Y.what₂ u', (F i0.1.1.lam' Λ₂).card := Finset.sum_le_sum fun _ _ => Finset.card_image_le
        _ ≤ ∑ Λ₁ ∈ Y.what₂ u', ∑ Λ₂ ∈ Y.what₂ u', (F Λ₁ Λ₂).card :=
          Finset.single_le_sum (f := fun Λ₁ => ∑ Λ₂ ∈ Y.what₂ u', (F Λ₁ Λ₂).card) (fun _ _ => Nat.zero_le _)
            i0.1.1.mem'
    · intro i hi
      have hei : e i = (i.1.1.lam', (hex i hi).choose) := by
        simp only [e, dif_pos (hex i hi)]
      refine ⟨?_, ?_⟩
      · rw [hei]
        exact Finset.mem_biUnion.2 ⟨i.1.1.lam', i.1.1.mem', Finset.mem_image.2 ⟨_, (hex i hi).choose_spec.1, rfl⟩⟩
      intro j hj hij
      have hej : e j = (j.1.1.lam', (hex j hj).choose) := by
        simp only [e, dif_pos (hex j hj)]
      rw [hei, hej] at hij
      have hl' : i.1.1.lam' = j.1.1.lam' := congrArg Prod.fst hij
      have hf : (hex i hi).choose = (hex j hj).choose := congrArg Prod.snd hij
      have hνi := (hex i hi).choose_spec.2
      have hνj := (hex j hj).choose_spec.2
      rw [← hf, ← hl'] at hνj
      have hν : i.1.1.lin⁻¹ * nm i * ((nm j)⁻¹ * j.1.1.lin) ∈ NLam i.1.1.lam' (lf D (X.Fu u')) := by
        have := Formalism.L2.SG.Pf.nlam_mul (Formalism.L2.SG.Pf.nlam_inv hνi) hνj
        have hq : ((hex i hi).choose⁻¹ * σ i)⁻¹ * ((hex i hi).choose⁻¹ * σ j) =
            i.1.1.lin⁻¹ * nm i * ((nm j)⁻¹ * j.1.1.lin) := by
          simp only [σ]; group
        rwa [hq] at this
      obtain ⟨ti, mi⟩ := i
      obtain ⟨tj, mj⟩ := j
      have hnΛ : nm ⟨tj, mj⟩ * (nm ⟨ti, mi⟩)⁻¹ ∈ NLam ti.1.lam (lf D (X.Fu u)) := by
        rw [ti.2]; exact Formalism.L2.SG.Pf.nlam_mul (hnm _) (Formalism.L2.SG.Pf.nlam_inv (hnm _))
      have htt : ti = tj := Subtype.ext (gterm_eq_of (ti.2.trans tj.2.symm) hl' _ _ hnΛ hν (by group))
      subst htt

      have hr : ((xm ⟨ti, mi⟩ * (xm ⟨ti, mj⟩)⁻¹).1 : X.B.I.Ginf) ∈
          ROsub X (X.Fu u) (X.Fu u') ti.1.lam ti.1.lam' ti.1.lin := by
        refine ⟨xm ⟨ti, mi⟩ * (xm ⟨ti, mj⟩)⁻¹, nm ⟨ti, mi⟩ * (nm ⟨ti, mj⟩)⁻¹,
          Formalism.L2.SG.TermOp.Vanish.ratLink_mul X (hxm _) (Formalism.L2.SG.TermOp.Vanish.ratLink_inv X (hxm _)), rfl,
          ?_, ?_⟩
        · rw [ti.2]; exact Formalism.L2.SG.Pf.nlam_mul (hnm _) (Formalism.L2.SG.Pf.nlam_inv (hnm _))
        · convert hν using 1
          all_goals rfl
      have hT := hE ti.1 ti.2
      obtain ⟨q, -, hq⟩ := hT.2 (mi : X.B.I.Ginf) (hT.1 mi.2)
      have h1 := hq ⟨1, mi⟩ (one_mul _)
      have h2 := hq ⟨⟨_, hr⟩, mj⟩ (by
        show (xm ⟨ti, mi⟩ * (xm ⟨ti, mj⟩)⁻¹).1 * (mj : X.B.I.Ginf) = mi
        rw [Prod.fst_mul, Prod.fst_inv, hmx ⟨ti, mi⟩, hmx ⟨ti, mj⟩]
        group)
      have hm : mj = mi := congrArg Prod.snd (h2.trans h1.symm)
      rw [hm]

  have hsig : (∑' t : {t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') // t.lam = Λ}, ∑' m : E t.1,
        ‖Ph X u Y.hK T ((m : X.B.I.Ginf) * x, aB Y u Λ)‖ₑ *
          ‖Ph X u' Y.hK T' (t.1.pt⁻¹ * ((m : X.B.I.Ginf) * x, aB Y u Λ))‖ₑ) =
      ∑' i : I, ‖Ph X u Y.hK T ((i.2 : X.B.I.Ginf) * x, aB Y u Λ)‖ₑ *
          ‖Ph X u' Y.hK T' (i.1.1.pt⁻¹ * ((i.2 : X.B.I.Ginf) * x, aB Y u Λ))‖ₑ :=
    (ENNReal.tsum_sigma' (fun i : I => ‖Ph X u Y.hK T ((i.2 : X.B.I.Ginf) * x, aB Y u Λ)‖ₑ *
          ‖Ph X u' Y.hK T' (i.1.1.pt⁻¹ * ((i.2 : X.B.I.Ginf) * x, aB Y u Λ))‖ₑ)).symm
  rw [hsig]
  calc ∑' i : I, ‖Ph X u Y.hK T ((i.2 : X.B.I.Ginf) * x, aB Y u Λ)‖ₑ *
          ‖Ph X u' Y.hK T' (i.1.1.pt⁻¹ * ((i.2 : X.B.I.Ginf) * x, aB Y u Λ))‖ₑ
      = ∑' i : I, ‖Ph X u Y.hK T (x, aB Y u Λ)‖ₑ * G (φ i) := tsum_congr fun i => by rw [hA i, hB i]
    _ = ‖Ph X u Y.hK T (x, aB Y u Λ)‖ₑ * ∑' i : I, G (φ i) := ENNReal.tsum_mul_left
    _ ≤ ‖Ph X u Y.hK T (x, aB Y u Λ)‖ₑ *
          (((∑ Λ₁ ∈ Y.what₂ u', ∑ Λ₂ ∈ Y.what₂ u', (F Λ₁ Λ₂).card : ℕ) : ℝ≥0∞) * ∑' δ : Y.Dt u', G δ) :=
        by gcongr; exact tsum_comp_le_of_fibre φ G _ hfib
    _ = _ := by rw [mul_left_comm]

end Formalism.L2.SG.Pf.SlabCount
