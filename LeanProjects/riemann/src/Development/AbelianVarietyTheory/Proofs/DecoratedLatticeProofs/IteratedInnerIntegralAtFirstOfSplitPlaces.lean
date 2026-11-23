import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValQOfValQr
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceDoubleStepLocalIteratedIntegralProofStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalInvariantIntegralsSymmetricHaarSubgroupsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupClosedEmbeddingIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalSchrodingerModelUniqTransportExistsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisOFinsetSum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombAwayFromPlaceKeepsVacuumStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OtherPlacesConvolutionFiniteAwayOrthogonalStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.QVal GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.QValInner

variable {D : D7}

theorem pcomb_eq_sum {G : Type} (e : G →₀ ℂ) (F : G → ℂ) : GlobalTheory.PosOne.comb e F = ∑ a ∈ e.support, e a * F a := rfl

theorem pcomb_congr {G : Type} (e : G →₀ ℂ) {F F' : G → ℂ} (h : ∀ a ∈ e.support, F a = F' a) :
    GlobalTheory.PosOne.comb e F = GlobalTheory.PosOne.comb e F' :=
  Finset.sum_congr rfl fun a ha => by show e a * F a = e a * F' a; rw [h a ha]

theorem pcomb_mapDomain {G H : Type} (e : G →₀ ℂ) (φ : G → H) (F : H → ℂ) :
    GlobalTheory.PosOne.comb (e.mapDomain φ) F = GlobalTheory.PosOne.comb e (fun a => F (φ a)) := by
  classical
  unfold GlobalTheory.PosOne.comb
  exact Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)

theorem pcomb_fsum {G ι : Type} (f : ι →₀ ℂ) (k : ι → ℂ → (G →₀ ℂ)) (F : G → ℂ) :
    GlobalTheory.PosOne.comb (f.sum k) F = f.sum fun a b => GlobalTheory.PosOne.comb (k a b) F :=
  Finsupp.sum_sum_index (h := fun g a => a * F g) (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)

theorem pcomb_single {G : Type} (x : G) (y : ℂ) (F : G → ℂ) : GlobalTheory.PosOne.comb (Finsupp.single x y) F = y * F x :=
  Finsupp.sum_single_index (h := fun g a => a * F g) (zero_mul _)

theorem pcomb_conv_cons {G : Type} [Monoid G] (e : G →₀ ℂ) (l : List (G →₀ ℂ)) (F : G → ℂ) :
    GlobalTheory.PosOne.comb (conv (e :: l)) F =
      GlobalTheory.PosOne.comb (conv l) (fun b => GlobalTheory.PosOne.comb e (fun a => F (a * b))) := by
  classical
  show GlobalTheory.PosOne.comb ((e.sum fun g a => (conv l).sum fun h b => Finsupp.single (g * h) (a * b))) F = _
  rw [pcomb_fsum]
  have e1 : ∀ g a, GlobalTheory.PosOne.comb ((conv l).sum fun h b => Finsupp.single (g * h) (a * b)) F =
      (conv l).sum fun h b => a * b * F (g * h) := fun g a => by
    rw [pcomb_fsum]; exact Finsupp.sum_congr fun h _ => pcomb_single _ _ _
  simp only [e1]
  show (e.sum fun g a => (conv l).sum fun h b => a * b * F (g * h)) = (conv l).sum fun b c => c * (e.sum fun a d => d * F (a * b))
  rw [Finsupp.sum_comm]
  refine Finsupp.sum_congr fun b _ => ?_
  simp only [Finsupp.mul_sum]
  refine Finsupp.sum_congr fun a _ => ?_
  ring

theorem conv_support_mem {G : Type} [Monoid G] (M : Submonoid G) (l : List (G →₀ ℂ))
    (h : ∀ e ∈ l, ∀ g ∈ e.support, g ∈ M) : ∀ g ∈ (conv l).support, g ∈ M := by
  classical
  induction l with
  | nil =>
    intro g hg
    have : g = 1 := by simpa [conv] using Finsupp.support_single_subset hg
    exact this ▸ M.one_mem
  | cons e l ih =>
    intro g hg
    have ih' := ih fun e' he' => h e' (List.mem_cons_of_mem _ he')
    change g ∈ (e.sum fun g a => (conv l).sum fun h b => Finsupp.single (g * h) (a * b)).support at hg
    obtain ⟨x, hx, hg⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hg)
    obtain ⟨y, hy, hg⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hg)
    rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hg)]
    exact M.mul_mem (h e List.mem_cons_self x hx) (ih' y hy)

theorem comb_eq_fsum (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c : WO S T →₀ ℂ) (f : WO S T → ℂ) :
    comb ψ S T c f = c.sum fun u a => a • heisO ψ S T u f := rfl

theorem comb_aconv_cons (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c : WO S T →₀ ℂ) (l : List (WO S T →₀ ℂ))
    (h : ∀ x ∈ c.support, ∀ y ∈ (aconv l).support, symplO S T x y = 0) (f : WO S T → ℂ) :
    comb ψ S T (aconv (c :: l)) f = comb ψ S T c (comb ψ S T (aconv l) f) := by
  classical
  rw [GlobalTheory.HeisComb.comb_comb]
  show comb ψ S T ((c.sum fun g a => (aconv l).sum fun h b => Finsupp.single (g + h) (a * b))) f = _
  rw [comb_eq_fsum, Finsupp.sum_sum_index (h := fun u a => a • heisO ψ S T u f) (fun _ => zero_smul ℂ _) (fun _ _ _ => add_smul _ _ _)]
  refine Finset.sum_congr rfl fun x hx => ?_
  beta_reduce
  rw [Finsupp.sum_sum_index (h := fun u a => a • heisO ψ S T u f) (fun _ => zero_smul ℂ _) (fun _ _ _ => add_smul _ _ _)]
  refine Finset.sum_congr rfl fun y hy => ?_
  beta_reduce
  rw [Finsupp.sum_single_index (h := fun u a => a • heisO ψ S T u f) (zero_smul ℂ _), GlobalTheory.WeilVacMove.heisO_heisO]
  have h0 : symplOH S T x y = 0 := by unfold symplOH; rw [h x hx y hy, mul_zero]
  rw [h0, AddChar.map_zero_eq_one, one_smul]

end GlobalTheory.QValInner

namespace GlobalTheory.QValInner
open GlobalTheory.Grow
variable {D : D7}

theorem congGrp_le (V : HSp D) {I J : Ideal (AE D)} (hIJ : I ≤ J) : congGrp V I ≤ congGrp V J := by
  intro x hx
  rw [congGrp, MonoidHom.mem_ker, MonoidHom.comp_apply] at hx ⊢
  have e : Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk J) (matHom V x) =
      Matrix.GeneralLinearGroup.map (Ideal.Quotient.factor hIJ)
        (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I) (matHom V x)) := by
    ext i j
    simp
  rw [e, hx, map_one]

theorem grpOff_le_at' (V : HSp D) {P : Pl D → Prop} {v : Pl D} (hv : P v) : grpOff V P ≤ grpOff V (· = v) := by
  apply congGrp_le
  exact le_iInf fun w => iInf_le_of_le ⟨w.1, by rw [w.2]; exact hv⟩ le_rfl

theorem grpAt_le_grpOff' (V : HSp D) {P P' : Pl D → Prop} (h : ∀ p, P p → ¬ P' p) : grpAt V P ≤ grpOff V P' := by
  apply congGrp_le
  intro a ha
  refine (Submodule.mem_iInf _).2 fun w => ?_
  exact (Submodule.mem_iInf _).1 (Submodule.mem_inf.1 ha).2 ⟨w.1, fun hp => h w.1 hp w.2⟩

theorem quotient_integral_fsum {G : Type} [Group G] [MeasurableSpace G] {R : Subgroup G} {ρ : Measure R} {μ : Measure G}
    {ι : Type} (s : Finset ι) (g : ι → G → ℂ) (z : ι → ℂ) (hs : ∀ i ∈ s, IsQuotIntL1 ρ μ (g i) (z i)) :
    IsQuotIntL1 ρ μ (fun h => ∑ i ∈ s, g i h) (∑ i ∈ s, z i) := by
  classical
  revert hs
  refine Finset.induction_on s ?_ ?_
  · intro _
    have e : (fun h => ∑ i ∈ (∅ : Finset ι), g i h) = 0 := by funext h; simp
    rw [e, Finset.sum_empty]
    exact IsQuotIntL1.zero
  · intro a s ha ih hs
    have := (hs a (Finset.mem_insert_self a s)).add (ih fun i hi => hs i (Finset.mem_insert_of_mem hi))
    rw [Finset.sum_insert ha]
    convert this using 1
    funext h
    simp [Finset.sum_insert ha]

end GlobalTheory.QValInner

namespace GlobalTheory.QValInner

theorem rest_grp : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (S : Dbl2 ψ σ) (r : ℕ) (Q : Fin (r + 1) → QStep S),
    Function.Injective (fun i => (Q i).q.v) →
    ∀ a ∈ (conv (List.ofFn fun i : Fin r => (Q i.succ).e₀.mapDomain (Q i.succ).gl₀)).support, a ∈ grpOff S.B.V (· = (Q 0).q.v) := by
  classical
  intro D ψ σ S r Q hinj
  refine conv_support_mem (grpOff S.B.V (· = (Q 0).q.v)).toSubmonoid _ ?_
  intro e he g hg
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 he
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hg)
  have hr := (GlobalTheory.T.splitPlace_local_group_closedEmbedding_integral D (Q i.succ).k (Q i.succ).q S.B.V _ (Q i.succ).F.G₀ (Q i.succ).gl₀ (Q i.succ).loc₀).2.1
  have ha : (Q i.succ).gl₀ a ∈ grpAt S.B.V (· = (Q i.succ).q.v) := hr ▸ ⟨a, rfl⟩
  refine grpAt_le_grpOff' _ ?_ ha
  rintro p rfl h
  exact Fin.succ_ne_zero i (hinj h)

end GlobalTheory.QValInner

namespace GlobalTheory.QValInner

theorem innerVal_iter2 : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (r : ℕ) (Q : Fin (r + 1) → QStep S), Function.Injective (fun i => (Q i).q.v) → ∀ m₁ s₁ m₂ s₂, LocNorm (Q 0) m₁ s₁ m₂ s₂ → ∀ c₁ c₂ f₁ f₂ φ f g h₁ h₂, Hyps Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ → ∀ x ∈ grpAt S.J.W (places fun i => Q i.succ), ∀ y ∈ grpAt S.B'.V (places fun i => Q i.succ), Iter2 s₁ m₁ s₂ m₂ (fun x₀ y₀ => integrand Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ (x * (Q 0).gl₁ x₀) (y * (Q 0).gl₂ y₀)) (innerVal Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ x y) := by
  classical
  intro D ψ hψ σ S r Q hinj m₁ s₁ m₂ s₂ hL c₁ c₂ f₁ f₂ φ f g h₁ h₂ hH x hx y hy
  obtain ⟨hc, t1, t2, hv, hφ, hf, ht, hg, hh₁, hh₂⟩ := hH
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hL
  have hc2 : (Q 0).c = 2 * σ := by have := (Q 0).F.bes'.1; omega
  obtain ⟨⟨fc₁, aw₁, or₁⟩, ⟨fc₂, aw₂, or₂⟩⟩ := GlobalTheory.T.otherPlacesConvolution_finite_away_orthogonal D ψ σ S r Q hinj
  have hdisj : ∀ p, (places fun i : Fin r => Q i.succ) p → ¬ (p = (Q 0).q.v) := by
    rintro p ⟨i, rfl⟩ h
    exact Fin.succ_ne_zero i (hinj h)
  have hP0 : (places Q) ((Q 0).q.v) := ⟨0, rfl⟩
  have hx0 : x ∈ grpOff S.J.W (· = (Q 0).q.v) := grpAt_le_grpOff' _ hdisj hx
  have hy0 : y ∈ grpOff S.B'.V (· = (Q 0).q.v) := grpAt_le_grpOff' _ hdisj hy
  have hg0 : g ∈ grpOff S.B.V (· = (Q 0).q.v) := grpOff_le_at' _ hP0 hg
  have hh₁0 : h₁ ∈ grpOff S.J.W (· = (Q 0).q.v) := grpOff_le_at' _ hP0 hh₁
  have hh₂0 : h₂ ∈ grpOff S.B'.V (· = (Q 0).q.v) := grpOff_le_at' _ hP0 hh₂
  have hE := rest_grp D ψ σ S r Q hinj
  have hcomm := (GlobalTheory.T.splitPlace_local_group_closedEmbedding_integral D (Q 0).k (Q 0).q S.B.V _ (Q 0).F.G₀ (Q 0).gl₀ (Q 0).loc₀).2.2.2.1
  set E := conv (List.ofFn fun i : Fin r => (Q i.succ).e₀.mapDomain (Q i.succ).gl₀) with hEdef
  set f₁' := comb ψ _ _ (aconv (List.ofFn fun i : Fin r => (Q i.succ).D₁)) f₁ with hf₁'
  set f₂' := comb ψ _ _ (aconv (List.ofFn fun i : Fin r => (Q i.succ).D₂)) f₂ with hf₂'
  have hvac : (Q 0).Vac f₁' f₂' := GlobalTheory.T.heisenbergComb_awayFromPlace_keeps_vacuum D ψ hψ σ S (Q 0) _ _ fc₁ fc₂ aw₁ aw₂ f₁ f₂ t1 t2 (hv 0)

  let Gf : GA D S.B.V → GL ((Q 0).n₁ ⊕ Fin ((Q 0).c + 1 + 1)) (Q 0).k → GL ((Q 0).n₂ ⊕ Fin ((Q 0).c + 1)) (Q 0).k → ℂ :=
    fun a' x₀ y₀ => GlobalTheory.PosOne.comb (Q 0).e₀ fun a => S.val c₁ c₂ (comb ψ _ _ (Q 0).D₁ f₁') (comb ψ _ _ (Q 0).D₂ f₂') φ f
      (g * a' * (Q 0).gl₀ a) (h₁ * x * (Q 0).gl₁ x₀) (h₂ * y * (Q 0).gl₂ y₀)
  let Z : GA D S.B.V → ℂ := fun a' => (Q 0).volJ * ∑ γ : (Q 0).A₁, ∑ β : (Q 0).A₂, (Q 0).w₁ γ * (Q 0).w₂ β *
    S.val (aconv [c₁, (Q 0).d₁ γ]) (aconv [c₂, (Q 0).d₂ γ β]) f₁' f₂' φ (trc (((Q 0).e₂ β).mapDomain (Q 0).gl₂) f)
      (g * a') (h₁ * x) (h₂ * y)
  have cv := GlobalTheory.T.localInvariantIntegrals_symmetric_haarSubgroups (Q 0).k (Q 0).ν (Q 0).unitVol
  have cv2 := ((cv (Q 0).n₂ ((Q 0).c + 1) (σ + 1) (Q 0).m₂ m₂ (Q 0).haar₂ a5 (Q 0).vol₂).1 (by omega) s₂ a7 a8).2
  have cv1 := ((cv (Q 0).n₁ ((Q 0).c + 1 + 1) (σ + 1) (Q 0).m₁ m₁ (Q 0).haar₁ a1 (Q 0).vol₁).2 (by omega) (by omega) s₁ a3 a4).2
  have hV : ∀ a', ∃ u : GL ((Q 0).n₁ ⊕ Fin ((Q 0).c + 1 + 1)) (Q 0).k → ℂ, a' ∈ E.support →
      (∀ x₀, IsQuotIntL1 s₂ m₂ (Gf a' x₀) (u x₀)) ∧ IsQuotIntL1 s₁ m₁ u (Z a') := by
    intro a'
    by_cases ha : a' ∈ E.support
    · obtain ⟨u, hu1, hu2⟩ := GlobalTheory.T.splitPlaceDoubleStepLocalIteratedIntegral_proof D ψ hψ σ S (Q 0) m₁ m₂ a1 a5 a2 a6 c₁ c₂ (hc 0).1 (hc 0).2 f₁' f₂' hvac φ f hφ hf
        (ht 0) (g * a') (mul_mem hg0 (hE a' ha)) (h₁ * x) (mul_mem hh₁0 hx0) (h₂ * y) (mul_mem hh₂0 hy0)
      exact ⟨u, fun _ => ⟨fun x₀ => cv2 _ _ (hu1 x₀), cv1 _ _ hu2⟩⟩
    · exact ⟨0, fun h => absurd h ha⟩
  choose u hu using hV

  have hK : ∀ x₀ y₀, integrand Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ (x * (Q 0).gl₁ x₀) (y * (Q 0).gl₂ y₀) =
      ∑ a' ∈ E.support, E a' * Gf a' x₀ y₀ := by
    intro x₀ y₀
    simp only [Gf]
    unfold integrand
    simp only [List.ofFn_succ]
    rw [pcomb_conv_cons, comb_aconv_cons ψ _ _ _ _ or₁, comb_aconv_cons ψ _ _ _ _ or₂, pcomb_eq_sum]
    refine Finset.sum_congr rfl fun b hb => ?_
    congr 1
    rw [pcomb_mapDomain]
    refine pcomb_congr _ fun a _ => ?_
    rw [hcomm a b (hE b hb), hf₁', hf₂']
    simp only [mul_assoc]
  have hI : innerVal Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ x y = ∑ a' ∈ E.support, E a' * Z a' := by
    simp only [Z]
    unfold innerVal integrand
    simp only [pcomb_eq_sum, Finset.mul_sum]
    symm
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun β _ => ?_
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  refine ⟨fun x₀ => ∑ a' ∈ E.support, E a' * u a' x₀, ?_, fun x₀ => ?_⟩
  · rw [hI]
    exact quotient_integral_fsum E.support (fun a' x₀ => E a' * u a' x₀) (fun a' => E a' * Z a')
      fun a' ha => ((hu a' ha).2.smul (E a'))
  · simp only [hK]
    exact quotient_integral_fsum E.support (fun a' y₀ => E a' * Gf a' x₀ y₀) (fun a' => E a' * u a' x₀)
      fun a' ha => (((hu a' ha).1 x₀).smul (E a'))

end GlobalTheory.QValInner

end
