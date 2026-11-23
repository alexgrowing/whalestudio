import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdmissibleRepresentationFactorisation
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalModelPeriodLattices
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSlopeBoundsFramesStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.Pad.LieGen

theorem grSet_subset_whole {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {c : Coeff l} {X : Scheme.{0}} (t : SAB H X) {C : Type} [NontriviallyNormedField C]
    {f : c.F →+* C} {x : Sp C ⟶ X} {u : Vecs Dw t C} (hu : GlobalTheory.LocM.IsFrame t f x u)
    (Λ : Set (Sp (DualNumber C) ⟶ t.G.left)) (j : Fin (letters Dw).length) :
    Guard.grSet t x Λ (u ((letters Dw).get j).1) ((letters Dw).get j).2 ⊆
      Guard.grSet t x Λ (fun i => u ((letters Dw).get i).1 ((letters Dw).get i).2) j := by
  rintro r ⟨cf, h0, hz, ⟨w, hw, hc⟩, rfl⟩
  obtain ⟨cg, hg0, hgj, hg⟩ := (GlobalTheory.Proof.frame_combination_coeff_unique.concat_frame _ _ _ _ _ _ _ _ f x u hu).2 j cf w hz hc
  exact ⟨cg, hgj ▸ h0, hg0, ⟨w, hw, hg⟩, by rw [hgj]⟩

theorem bdd_whole {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W}
    {i₀ : Idx H p} (hp : p.Prime) (Z : LocM.Mdl Y i₀) (l : ℕ) (x : Pad.Letter Dw)
    (h : letterOf Dw (.inr l) = some x) : GenId.Bdd Z false false (.inl (x.1, (x.2 : ℕ))) (.inr l) := by
  obtain ⟨hl, hx⟩ := List.getElem?_eq_some_iff.1 h
  set j : Fin (letters Dw).length := ⟨l, hl⟩
  have hx' : (letters Dw).get j = x := hx
  subst hx'
  obtain ⟨m, hm⟩ := GlobalTheory.T.exists_slope_bounds_frames Dw Z.i.c (Y Z.i).t p hp
  refine ⟨m, fun y a φ hφ => ?_⟩
  have F := Pull.chart_frame Z hφ
  obtain ⟨c', h1, h2, h3⟩ := hm y.C.S y.C.norm_p _ _ _ F j
  have hpos : (0 : ℝ) < p := Nat.cast_pos.2 hp.pos
  simp only [lnStep, dif_pos ((letters Dw).get j).2.2, dif_pos hl, Bool.false_eq_true, false_and, if_false, sub_zero]
  refine (HTFrame.abs_log_sInf_sub_le h1 ?_ (grSet_subset_whole _ F _ j) h3).trans ?_
  · rintro r ⟨cf, -, -, -, rfl⟩
    positivity
  · rw [← Real.log_pow]
    exact Real.log_le_log (by linarith) h2

section

variable {D : D7} {A : Amb D} {N j : ℕ} (S : Sig A N j)

theorem mult_tau (t : D.what₂.Tau) : S.Dw.mult (DV.tauEmb D t) = j := by
  rw [Datum.mult, if_pos (A.cm t), S.p_eq]

theorem mult_conj_tau (t : D.what₂.Tau) : S.Dw.mult (conjEmb (DV.tauEmb D t)) = N - j := by
  rw [Datum.mult, if_neg (GlobalTheory.Proof.LetterConjugation.conj_ne (A.cm t))]
  have := S.p_eq
  have := S.rank_eq
  omega

def rootLetter (r : DV.Rt D.what₂.Tau N) : Pad.Letter S.Dw :=
  if h : (r.2 : ℕ) < j then ⟨DV.tauEmb D r.1, ⟨r.2, by rw [mult_tau S]; exact h⟩⟩
  else ⟨conjEmb (DV.tauEmb D r.1), ⟨N - 1 - r.2, by rw [mult_conj_tau S]; have := r.2.2; omega⟩⟩

theorem rootLetter_injective : Function.Injective (rootLetter S) := by
  have hinj : Function.Injective (DV.tauEmb D) := fun a b e =>
    D.eTau.injective (Subtype.ext (Formalism.MainNotions.LocalModelPeriodLattices.emb_injective D e))
  have hc : Function.Injective (conjEmb : (D.host.E →+* ℂ) → (D.host.E →+* ℂ)) := fun a b e => by
    have h2 : ∀ τ : D.host.E →+* ℂ, conjEmb (conjEmb τ) = τ := fun τ => by ext x; simp [conjEmb]
    rw [← h2 a, ← h2 b, e]
  rintro ⟨t, i⟩ ⟨t', i'⟩ h
  unfold rootLetter at h
  dsimp only at h
  split_ifs at h with h1 h2 h2
  · obtain ⟨e1, e2⟩ := Sigma.mk.inj_iff.1 h
    obtain rfl := hinj e1
    have := Fin.mk.inj_iff.1 (eq_of_heq e2)
    exact Prod.ext rfl (Fin.ext this)
  · obtain ⟨e1, -⟩ := Sigma.mk.inj_iff.1 h
    exact absurd ((congrArg (fun σ : D.host.E →+* ℂ => σ (A.H.rt : D.host.E)) e1).symm.trans (A.cm t))
      (GlobalTheory.Proof.LetterConjugation.conj_ne (A.cm t'))
  · obtain ⟨e1, -⟩ := Sigma.mk.inj_iff.1 h
    exact absurd ((congrArg (fun σ : D.host.E →+* ℂ => σ (A.H.rt : D.host.E)) e1).trans (A.cm t'))
      (GlobalTheory.Proof.LetterConjugation.conj_ne (A.cm t))
  · obtain ⟨e1, e2⟩ := Sigma.mk.inj_iff.1 h
    obtain rfl := hinj (hc e1)
    have e3 : N - 1 - (i : ℕ) = N - 1 - (i' : ℕ) := Fin.mk.inj_iff.1 (eq_of_heq e2)
    have := i.2
    have := i'.2
    refine Prod.ext rfl (Fin.ext ?_)
    show (i : ℕ) = i'
    omega

open Classical in

def rootIdx (r : DV.Rt D.what₂.Tau N) : Fin (D.R.f * N) :=
  finCongr (length_letters S)
    (((GlobalTheory.Proof.LetterConjugation.nodup_letters S.Dw).getEquivOfForallMemList _ (GlobalTheory.Proof.LetterConjugation.mem_letters S.Dw)).symm
      (rootLetter S r))

theorem rootIdx_bijective : Function.Bijective (rootIdx S) := by
  classical
  refine (Fintype.bijective_iff_injective_and_card _).2 ⟨fun r r' h => rootLetter_injective S ?_, by
    simp [D.what₂.card_Tau]⟩
  simpa [rootIdx] using h

def rootEquiv : Fin (D.R.f * N) ≃ DV.Rt D.what₂.Tau N := (Equiv.ofBijective _ (rootIdx_bijective S)).symm

theorem letterOf_rootEquiv (l : Fin (D.R.f * N)) :
    letterOf S.Dw (.inr (l : ℕ)) = some (rootLetter S (rootEquiv S l)) := by
  classical
  rw [letterOf_whole S l]
  congr 1
  have h := (Equiv.ofBijective _ (rootIdx_bijective S)).apply_symm_apply l
  change rootIdx S (rootEquiv S l) = l at h
  unfold rootIdx at h
  rw [Equiv.apply_eq_iff_eq_symm_apply, Equiv.symm_apply_eq] at h
  rw [h]
  rfl

end

section Main

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ} [Fact p.Prime] {hp : p.Prime}
  {W : ValuationSubring ℂ} {hW : (p : ℂ) ∈ W.nonunits} (z : AdmAt S κ hp hW) (jc : DV.KW p →+* ℂ)

theorem c1_whole (l : Fin (D.R.f * N)) (x : Pad.Letter S.Dw) (h : letterOf S.Dw (.inr (l : ℕ)) = some x) :
    ∃ V : (mdlOf z jc).Z.VDiv, (mdlOf z jc).Z.c1 ((mdlOf z jc).lieW.x l) =
      (mdlOf z jc).Z.c1 (z.stepLB false (.inl (x.1, (x.2 : ℕ)))) + (mdlOf z jc).Z.cD V := by
  have h1 : letterOf S.Dw (.inl (x.1, (x.2 : ℕ))) = some x := dif_pos x.2.2
  obtain ⟨u, -⟩ := exists_isGenId hp hW z.full (bdd_whole hp z.Z l x h) (z.line false _ x h1) (z.line false _ x h)
  have e : (mdlOf z jc).Z.c1 (z.line false _ x h).L = (mdlOf z jc).Z.c1 (z.line false _ x h1).L -
      (mdlOf z jc).Z.cD (vdiv hp hW (Formalism.DegreeFormula.dimFl D.what₂.Tau N) (z.line false _ x h1).L (z.line false _ x h).L u) :=
    firstChern_eq_sub_divisor hp hW (Formalism.DegreeFormula.dimFl D.what₂.Tau N) (z.line false _ x h1).L (z.line false _ x h).L u
  refine ⟨-vdiv hp hW (Formalism.DegreeFormula.dimFl D.what₂.Tau N) (z.line false _ x h1).L (z.line false _ x h).L u, ?_⟩
  have e2 := LinearMap.map_neg (mdlOf z jc).Z.cD
    (vdiv hp hW (Formalism.DegreeFormula.dimFl D.what₂.Tau N) (z.line false _ x h1).L (z.line false _ x h).L u :
      (mdlOf z jc).Z.VDiv)
  refine (congrArg _ (mdlOf_lieW z jc l).1).trans ((congrArg _ (z.stepLB_of_some false h)).trans (e.trans ?_))
  rw [sub_eq_add_neg, ← e2]
  exact congrArg (· + _) (congrArg _ (z.stepLB_of_some false h1).symm)

theorem c1_dual_mdl (L : FinLB z.Z.X) : (mdlOf z jc).Z.c1 L.dual = -(mdlOf z jc).Z.c1 L :=
  firstChern_dual_eq_neg hp hW z.Z _ L

end Main

theorem lieW_gen : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (p : ℕ) [Fact p.Prime] (hp : p.Prime)
    (W : ValuationSubring ℂ) (hW : (p : ℂ) ∈ W.nonunits) (z : AdmAt S κ hp hW) (jc : DV.KW p →+* ℂ),
    ∃ (e : Fin (D.R.f * N) ≃ DV.Rt D.what₂.Tau N) (V : Fin (D.R.f * N) → (mdlOf z jc).Z.VDiv), ∀ l,
      (mdlOf z jc).Z.c1 ((mdlOf z jc).lieW.x l) = (if ((e l).2 : ℕ) < j then (1 : ℚ) else -1) •
        (mdlOf z jc).Z.c1 (rootOf z jc (false, e l)) + (mdlOf z jc).Z.cD (V l) := by
  intro D A N j S κ p _ hp W hW z jc
  choose V hV using fun l => c1_whole z jc l _ (letterOf_rootEquiv S l)
  refine ⟨rootEquiv S, V, fun l => ?_⟩
  rw [hV l]
  congr 1
  generalize rootEquiv S l = r
  obtain ⟨t, i⟩ := r
  have hp' := S.p_eq
  have hq := S.rank_eq
  unfold rootOf admitted.rootLB
  dsimp only
  by_cases hi : (i : ℕ) < j
  · have hx : ((rootLetter S (t, i)).1, ((rootLetter S (t, i)).2 : ℕ)) = (DV.tauEmb D t, (i : ℕ)) := by
      unfold rootLetter
      rw [dif_pos hi]
    rw [if_pos (show (i : ℕ) < S.Dw.p by omega), if_pos hi, one_smul, hx]
  · have hx : ((rootLetter S (t, i)).1, ((rootLetter S (t, i)).2 : ℕ)) =
        (conjEmb (DV.tauEmb D t), S.Dw.p + S.Dw.q - 1 - (i : ℕ)) := by
      unfold rootLetter
      rw [dif_neg hi]
      simp only [Prod.mk.injEq, true_and]
      omega
    rw [if_neg (show ¬ (i : ℕ) < S.Dw.p by omega), if_neg hi, hx, c1_dual_mdl, neg_one_smul, neg_neg]

end GlobalTheory.ShFam.Pad.LieGen
