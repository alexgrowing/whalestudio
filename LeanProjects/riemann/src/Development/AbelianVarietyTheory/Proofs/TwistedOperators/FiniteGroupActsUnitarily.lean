import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitaryAtAllRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormGoodRowsFiniteGroupActionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormLiftFormsFiniteGroupActionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TranslateUnitaryLifts
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ReprMemOfBasisRational

noncomputable section

open Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Links NumberField
open Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Bridge Formalism.L2.Theta
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAtAllPlaces

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FiniteGroupUnitary

theorem isUnitaryRep_of_norm {G H : Type} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ρ : Representation ℂ G H) (h : ∀ g x, ‖ρ g x‖ = ‖x‖) : IsUnitaryRep ρ := by
  intro g x y
  let e : H →ₗᵢ[ℂ] H := ⟨ρ g, h g⟩
  exact e.inner_map_map x y

section ClassSum

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) (σ : K →+* ℂ)

theorem pairAt_eq_of_rat (x y : S.V) (hx : ∀ i, S.bV.repr x i ∈ cmMax K) : pairAt S σ x y = σ (S.pair x y) := by

  have hexp : S.pair x y = ∑ i, ∑ j, star (S.bV.repr x i) * S.gramV i j * S.bV.repr y j := by
    conv_lhs => rw [← S.bV.sum_repr x, ← S.bV.sum_repr y]
    simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, CSD.gramV, Matrix.of_apply,
      starRingEnd_apply, RingHom.id_apply, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hexp]
  simp only [pairAt, map_sum, map_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_

  have hc : ∀ τ : K →+* ℂ, τ (star (S.bV.repr x i)) = starRingEnd ℂ (τ (S.bV.repr x i)) := hx i
  rw [hc σ]

theorem csumAt_eq_of_rat (f f' : S.Cl → S.V) (hf : S.IsRat f) : csumAt S σ f f' = σ (S.csum f f') := by
  simp only [csumAt, CSD.csum, map_sum, map_mul, map_inv₀, map_natCast]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [pairAt_eq_of_rat S σ (f c) (f' c) (fun i => hf c i)]

theorem csumAt_add_left (f g f' : S.Cl → S.V) : csumAt S σ (f + g) f' = csumAt S σ f f' + csumAt S σ g f' := by
  simp only [csumAt, pairAt, Pi.add_apply, map_add, Finsupp.add_apply, add_mul, mul_add, Finset.sum_add_distrib]

theorem csumAt_smul_left (a : K) (f f' : S.Cl → S.V) :
    csumAt S σ (a • f) f' = starRingEnd ℂ (σ a) * csumAt S σ f f' := by
  simpa using csumAt_smul S σ a 1 f f'

private theorem csumAt_add_right (f g g' : S.Cl → S.V) :
    csumAt S σ f (g + g') = csumAt S σ f g + csumAt S σ f g' := by
  simp only [csumAt, pairAt, Pi.add_apply, map_add, Finsupp.add_apply, mul_add, Finset.sum_add_distrib]

private theorem csumAt_smul_right' (b : K) (f f' : S.Cl → S.V) :
    csumAt S σ f (b • f') = σ b * csumAt S σ f f' := by
  simpa using csumAt_smul S σ 1 b f f'

private theorem csumAt_sum_left {ι : Type} (s : Finset ι) (F : ι → S.Cl → S.V) (f' : S.Cl → S.V) :
    csumAt S σ (∑ i ∈ s, F i) f' = ∑ i ∈ s, csumAt S σ (F i) f' := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [csumAt, pairAt]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, csumAt_add_left, ih]

private theorem csumAt_sum_right {ι : Type} (s : Finset ι) (f : S.Cl → S.V) (F : ι → S.Cl → S.V) :
    csumAt S σ f (∑ i ∈ s, F i) = ∑ i ∈ s, csumAt S σ f (F i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [csumAt, pairAt]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, csumAt_add_right, ih]

theorem csumAt_map (hb : S.HasRatBasis) (U : Module.End K S.Forms)
    (hU : ∀ f : S.Forms, S.IsRat (f : S.Cl → S.V) → S.IsRat (U f : S.Cl → S.V))
    (hc : ∀ f f' : S.Forms, S.csum (U f : S.Cl → S.V) (U f' : S.Cl → S.V) = S.csum (f : S.Cl → S.V) (f' : S.Cl → S.V))
    (f f' : S.Forms) :
    csumAt S σ (U f : S.Cl → S.V) (U f' : S.Cl → S.V) = csumAt S σ (f : S.Cl → S.V) (f' : S.Cl → S.V) := by
  obtain ⟨b, hbr⟩ := hb

  have key : ∀ i j, csumAt S σ (U (b i) : S.Cl → S.V) (U (b j) : S.Cl → S.V) =
      csumAt S σ (b i : S.Cl → S.V) (b j : S.Cl → S.V) := by
    intro i j
    rw [csumAt_eq_of_rat S σ _ _ (hU _ (hbr i)), csumAt_eq_of_rat S σ _ _ (hbr i), hc]

  rw [← b.sum_repr f, ← b.sum_repr f']
  simp only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul, csumAt_sum_left, csumAt_sum_right,
    csumAt_smul_left, csumAt_smul_right', key]

end ClassSum

section Presented

variable {G Γ W K : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K]
  [NumberField K] [StarRing K] {ι : Γ →* G} {S : CSD K} {σ₀ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W}

theorem adInner_g0Act (l : LevDatG G) (hρ : ∀ γ x x', inner ℂ (ρ γ x) (ρ γ x') = inner ℂ x x')
    (hn : ∀ q ∈ l.Q, ∀ k ∈ l.J, q⁻¹ * k * q ∈ l.J) (hch : ∀ q, ‖(l.ch q : ℂ)‖ = 1)
    {I : Type} [Fintype I] {y : I → G} (hy : IsReps ι l.J y) (κ : l.Q) {F F' : G → W}
    (hF : F ∈ AdForms ι ρ l.J l.χ) (hF' : F' ∈ AdForms ι ρ l.J l.χ) :
    adInner ι l.J y (g0Act l.ch κ F) (g0Act l.ch κ F') = adInner ι l.J y F F' := by

  have hκ : ∀ k, (κ : G)⁻¹ * k * κ ∈ l.J ↔ k ∈ l.J := by
    intro k
    constructor
    · intro hk
      have h2 := hn (κ : G)⁻¹ (l.Q.inv_mem κ.2) _ hk
      have e : ((κ : G)⁻¹)⁻¹ * ((κ : G)⁻¹ * k * κ) * (κ : G)⁻¹ = k := by group
      rwa [e] at h2
    · intro hk
      exact hn κ κ.2 k hk
  have hχ : ∀ k : l.J, ‖(l.χ k : ℂ)‖ = 1 := fun k => by rw [← l.ch_J k]; exact hch _

  have hy' := GlobalTheory.ClassSumTranslate.isReps_mul ι hκ hy
  rw [← GlobalTheory.ClassSumTranslate.adInnerIndep ι ρ l.J l.χ hρ hχ I I (fun i => y i * κ) y hy' hy F hF F' hF']
  have hn1 : ‖(((l.ch κ)⁻¹ : ℂˣ) : ℂ)‖ = 1 := by
    rw [Units.val_inv_eq_inv_val, norm_inv, hch κ, inv_one]
  have hc : starRingEnd ℂ (((l.ch κ)⁻¹ : ℂˣ) : ℂ) * (((l.ch κ)⁻¹ : ℂˣ) : ℂ) = 1 := by
    rw [RCLike.conj_mul, hn1]
    simp
  unfold adInner g0Act
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [GlobalTheory.ClassSumTranslate.stab_mul ι hκ (y i), inner_smul_left, inner_smul_right, ← mul_assoc (starRingEnd ℂ _), hc,
    one_mul]

theorem isUnitaryAtAll_of_tie (l : LevDatG G) (P : ClassPres ι S σ₀ ρ l.J l.χ) {G₀ : Type} [Group G₀]
    (act : Representation K G₀ S.Forms) (T : ActTie ι P l.Q l.ch act)
    (hσ : ∀ a : K, σ₀ (star a) = starRingEnd ℂ (σ₀ a))
    (hρ : ∀ γ x x', inner ℂ (ρ γ x) (ρ γ x') = inner ℂ x x')
    (hn : ∀ q ∈ l.Q, ∀ k ∈ l.J, q⁻¹ * k * q ∈ l.J) (hch : ∀ q, ∃ n : ℕ, 0 < n ∧ l.ch q ^ n = 1)
    (hrat : ∀ γ j, ∃ c : S.ιV → K, (∀ i, c i ∈ cmMax K) ∧ ρ γ (P.coef (S.bV j)) = ∑ i, σ₀ (c i) • P.coef (S.bV i)) :
    IsUnitaryAtAll S act := by

  have hchn : ∀ q, ‖(l.ch q : ℂ)‖ = 1 := by
    intro q
    obtain ⟨n, hn, hq⟩ := hch q
    have h1 : (l.ch q : ℂ) ^ n = 1 := by
      rw [← Units.val_pow_eq_pow_val, hq, Units.val_one]
    have h2 : ‖(l.ch q : ℂ)‖ ^ n = 1 := by rw [← norm_pow, h1, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h2
  have hχ : ∀ k, ∃ n : ℕ, 0 < n ∧ l.χ k ^ n = 1 := by
    intro k
    obtain ⟨n, hn, hk⟩ := hch ⟨k, l.J_le k.2⟩
    exact ⟨n, hn, by rw [← l.ch_J k]; exact hk⟩

  have hb : S.HasRatBasis := by
    refine (GlobalTheory.classPres_dcOp_rat ι S σ₀ ρ l.J l.χ P {1} 1 hσ hχ hrat ?_).1
    intro f
    funext h
    simp [dcOp]
  intro σ g f f'
  obtain ⟨κ, hκ⟩ := T.red_surj g
  refine csumAt_map S σ hb (act g) ?_ ?_ f f'
  ·

    intro f hf c i
    rw [← GlobalTheory.PresRat.mem_cmComplex_iff σ₀ hσ, ← GlobalTheory.PresBasic.repr_coef P, ← GlobalTheory.PresBasic.ext_y P, T.act_eq g κ hκ f]
    have hd := P.dec_spec (P.y c * (κ : G))
    unfold g0Act
    rw [hd, GlobalTheory.PresBasic.ext_dec P, map_smul, Finsupp.smul_apply, smul_eq_mul]
    refine mul_mem ?_ (GlobalTheory.PresRat.act_mem P hσ hχ hrat _ _ _ (fun j => hf _ j) i)
    obtain ⟨n, hn, hq⟩ := hch κ
    refine GlobalTheory.PresRat.mem_cmComplex_of_pow hn ?_
    rw [← Units.val_pow_eq_pow_val, inv_pow, hq, inv_one, Units.val_one]
  ·
    intro f f'
    apply σ₀.injective
    have e1 := GlobalTheory.PresBasic.isom P (act g f) (act g f')
    have e2 := GlobalTheory.PresBasic.isom P f f'
    rw [← e1, ← e2, T.act_eq g κ hκ f, T.act_eq g κ hκ f']
    exact adInner_g0Act l hρ hn hchn P.reps κ (GlobalTheory.PresBasic.extMem P f) (GlobalTheory.PresBasic.extMem P f')

end Presented

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks]
  [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem levEnv_ch_pow (V : TH.HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank)
    (q : (levEnv V β L).Q) : ∃ n : ℕ, 0 < n ∧ (levEnv V β L).ch q ^ n = 1 := by

  obtain ⟨n, hn, hx⟩ := isOfFinOrder_iff_pow_eq_one.1 (GlobalTheory.HeckeRational.levFn_isOfFinOrder β (Formalism.IndefR.Lev.flagL L)
    (Formalism.UG.bc (Formalism.IndefR.Lev.swapAE D) q.1.1))
  refine ⟨n, hn, ?_⟩
  have e : (levEnv V β L).ch q = Formalism.L2.DIV.levFn β (Formalism.IndefR.Lev.flagL L)
      (Formalism.UG.bc (Formalism.IndefR.Lev.swapAE D) q.1.1) := rfl
  rw [e, hx]

theorem definiteUnitary (R : RealDat D A Ks) (h : R.fam_tie) (hX : R.models_cX) (hV : R.models_cV) : DefiniteUnitary A := by
  obtain ⟨gramR, c0R, c0L, hT⟩ := h
  refine ⟨fun t => ?_, fun i t => ?_⟩
  ·
    exact isUnitaryAtAll_of_tie (levEnv D.sp.X' R.βX (R.datXt t)) (R.B.R t).pres (A.leftGroupActionRight t) (R.B.R t).act_tie
      D.starLL_cx (fun γ x x' => hX.2.1 _ x x') (GlobalTheory.ClassSumTranslate.levEnv_normal _ _ _) (levEnv_ch_pow _ _ _)
      (fun γ j => GlobalTheory.HeckeRational.action_rational _ _ (R.B.R t).pres (hT.coefR t) hT.mapR
        (fun g a b => (GlobalTheory.coefAction_repr_mem_subfield _ (cmMax D.what₂.LL) _
          (fun τ x => GlobalTheory.HeckeRational.labLL_mem_cmMax τ x) g a b).1) γ j)
  ·
    exact isUnitaryAtAll_of_tie (levEnv (Vc D i) (R.βV i) (R.datVt i t)) (R.B.L i t).pres (A.leftGroupActionLift i t) (R.B.L i t).act_tie
      D.starLL_cx (fun γ x x' => (hV i).2.1 _ x x') (GlobalTheory.ClassSumTranslate.levEnv_normal _ _ _) (levEnv_ch_pow _ _ _)
      (fun γ j => GlobalTheory.HeckeRational.action_rational _ _ (R.B.L i t).pres (hT.coefL i t) (hT.mapL i)
        (fun g a b => (GlobalTheory.coefAction_repr_mem_subfield _ (cmMax D.what₂.LL) _
          (fun τ x => GlobalTheory.HeckeRational.labLL_mem_cmMax τ x) g a b).2) γ j)

end GlobalTheory.FiniteGroupUnitary
