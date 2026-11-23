import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.CoreExists
import Formalism.LocalToGlobal.ProjectiveLattices.ReadQuot
import Development.AbelianVarietyTheory.Counterexamples.UpperHalfSurvey.MemSSgtOfZeroOnDom
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ReadingLinearIndependentAndInjective

noncomputable section
namespace GlobalTheory.OneEmbeddingProbe
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

theorem rdU_eq_zero (U : Unf Xo c σ r) (f : Rul Xo c) (h : ∀ k, ∀ x ∈ (U.X k).dom, rdU U f k x = 0) :
    rdU U f = 0 := by
  funext k x
  by_cases hx : x ∈ (U.X k).dom
  · exact h k x hx
  · classical
    show (if h : x ∈ (U.X k).dom then toC (evR Xo c f (U.un k ⟨x, h⟩)) else 0) = 0
    rw [dif_neg hx]

theorem indep_one {K M : Type} [Field K] [AddCommGroup M] [Module K M] {f : M} (h : f ≠ 0) :
    LinearIndependent K (fun _ : Fin 1 => f) := linearIndependent_unique_iff.2 h

theorem inj_of_indep (U : Unf Xo c σ r) (h : RdIndep1 U) (a n) (hd : Dom a n) (f) (hf : f ∈ sec Xo c a n)
    (h0 : ∀ k, ∀ x ∈ (U.X k).dom, rdU U f k x = 0) : f = 0 := by
  by_contra hne
  have := h a n hd 1 (fun _ => f) (fun _ => hf) (indep_one hne)
  exact this.ne_zero 0 (rdU_eq_zero U f h0)

theorem domInj_of_indep (U : Unf Xo c σ r) (h : RdIndep1 U) : RdDomInj1 U :=
  fun a n hd f hf _ h0 => inj_of_indep U h a n hd f hf h0

theorem domInj_iff (U : Unf Xo c σ r) : RdDomInj1 U ↔
    ∀ a n, Dom a n → ∀ f ∈ sec Xo c a n, rdU U f = 0 → f = 0 :=
  ⟨fun h a n hd f hf h0 => h a n hd f hf (h0 ▸ Submodule.zero_mem _) (fun k x _ => by rw [h0]; rfl),
   fun h a n hd f hf _ h0 => h a n hd f hf (rdU_eq_zero U f h0)⟩

theorem sec_eq_zero_of_isEmpty (U : Unf Xo c σ r) [IsEmpty U.Comp] (h : RdDomInj1 U) (a n) (hd : Dom a n)
    (f) (hf : f ∈ sec Xo c a n) : f = 0 :=
  (domInj_iff U).1 h a n hd f hf (funext fun k => isEmptyElim k)

def copy (U : Unf Xo c σ r) : Formalism.L2.PjFree.Unf Xo c σ r := ⟨U.Comp, U.X, U.un⟩

theorem isUnf_copy (U : Unf Xo c σ r) : Formalism.L2.PjFree.IsUnf (copy U) ↔ IsUnf U := Iff.rfl

theorem indep_of_isUnf (hS : Out.SecBaseChangeSt) (U : Unf Xo c σ r) (hU : IsUnf U) : RdIndep1 U ∧ RdDomInj1 U :=
  have h : RdIndep1 U := fun a n _ =>
    (GlobalTheory.reading_linearIndependent_and_injective hS E H Dw l Xo c σ r (copy U) ((isUnf_copy U).2 hU) a n).1
  ⟨h, domInj_of_indep U h⟩

theorem invFun_relab_injective (c : Coeff l) (σ : c.F →+* ℂ) :
    Function.Injective (Function.invFun (relab (E := E) c σ)) := by
  have hi : Function.Injective (relab (E := E) c σ) := by
    intro τ τ' h
    ext a
    have := σ.injective (RingHom.congr_fun h a)
    exact congrArg Subtype.val this
  exact (Function.rightInverse_invFun (Finite.injective_iff_surjective.1 hi)).injective

theorem conjEmb_inj {τ τ' : E →+* ℂ} (h : conjEmb τ = conjEmb τ') : τ = τ' := by
  ext a
  exact (starRingEnd ℂ).injective (RingHom.congr_fun h a)

open Classical in

def step (ρ : E →+* ℂ) (m : ℕ) : (E →+* ℂ) × ℕ → ℕ := fun p => if p.1 = ρ ∧ p.2 < m then 1 else 0

theorem dom_step (ρ : E →+* ℂ) (m : ℕ) : Dom (step ρ m) 0 := by
  refine ⟨fun τ i j hij => ?_, by simp⟩
  simp only [step]
  split_ifs with h1 h2 <;> first | omega | exact absurd ⟨h1.1, by omega⟩ h2

theorem chi_eq_one (U : Unf Xo c σ r)
    (h : ∀ a n, Dom a n → ∀ k, ∀ γ ∈ (U.X k).Γ, (U.X k).χ (laU U a n k) γ = 1)
    (k : U.Comp) (la : Wt (U.X k).Ψ r) (γ) (hγ : γ ∈ (U.X k).Γ) : (U.X k).χ la γ = 1 := by
  classical
  have hne : ∀ la, (U.X k).χ la γ ≠ 0 := fun la e => by
    obtain ⟨n, hn, h1⟩ := (U.X k).χ_fin la
    have := h1 γ hγ
    rw [e, zero_pow hn.ne'] at this
    exact zero_ne_one this
  have h0 : (U.X k).χ 0 γ = 1 := by
    have := (U.X k).χ_add 0 0 γ hγ
    rw [add_zero] at this
    exact (mul_eq_left₀ (hne 0)).1 this.symm
  let S : AddSubgroup (Wt (U.X k).Ψ r) :=
    { carrier := {la | (U.X k).χ la γ = 1}
      zero_mem' := h0
      add_mem' := fun {a b} ha hb => by
        show _ = _
        rw [(U.X k).χ_add a b γ hγ, ha, hb, one_mul]
      neg_mem' := fun {a} ha => by
        have := (U.X k).χ_add a (-a) γ hγ
        rw [add_neg_cancel, h0, show (U.X k).χ a γ = 1 from ha, one_mul] at this
        exact this.symm }
  have hst : ∀ ρ m, laU U (step ρ m) 0 k ∈ S := fun ρ m => h _ _ (dom_step ρ m) k γ hγ
  have hI := invFun_relab_injective (E := E) c σ
  have hcn : ∀ τ τ' : (U.X k).Ψ, conjEmb τ.1 ≠ τ'.1 := fun τ τ' e =>
    ((U.X k).cmType τ.1).1 τ.2 (by
      show conjEmb τ.1 ∈ _
      rw [e]; exact τ'.2)
  have hsing : ∀ (τ0 : (U.X k).Ψ) (j0 : Fin r), (Pi.single τ0 (Pi.single j0 1) : Wt (U.X k).Ψ r) ∈ S := by
    intro τ0 j0
    by_cases hj : (U.X k).p0 ≤ (j0 : ℕ)
    · have e : (Pi.single τ0 (Pi.single j0 1) : Wt (U.X k).Ψ r) =
          laU U (step (Function.invFun (relab c σ) τ0.1) (j0 - (U.X k).p0 + 1)) 0 k -
            laU U (step (Function.invFun (relab c σ) τ0.1) (j0 - (U.X k).p0)) 0 k := by
        funext τ j
        simp only [Pi.sub_apply, laU, step, hI.eq_iff, hcn τ τ0, false_and, if_false, Subtype.val_inj]
        by_cases ht : τ = τ0
        · subst ht
          simp only [Pi.single_eq_same, Pi.single_apply, true_and, Fin.ext_iff]
          split_ifs <;> simp <;> omega
        · simp [ht]
      rw [e]; exact S.sub_mem (hst _ _) (hst _ _)
    · have e : (Pi.single τ0 (Pi.single j0 1) : Wt (U.X k).Ψ r) =
          laU U (step (Function.invFun (relab c σ) (conjEmb τ0.1)) ((U.X k).p0 - 1 - j0)) 0 k -
            laU U (step (Function.invFun (relab c σ) (conjEmb τ0.1)) ((U.X k).p0 - j0)) 0 k := by
        funext τ j
        simp only [Pi.sub_apply, laU, step, hI.eq_iff, (hcn τ0 τ).symm, false_and, if_false]
        by_cases ht : τ = τ0
        · subst ht
          simp only [Pi.single_eq_same, Pi.single_apply, true_and, Fin.ext_iff]
          split_ifs <;> simp <;> omega
        · have : conjEmb τ.1 ≠ conjEmb τ0.1 := fun e => ht (Subtype.ext (conjEmb_inj e))
          simp [ht, this]
      rw [e]; exact S.sub_mem (hst _ _) (hst _ _)
  have e : la = ∑ τ, ∑ j, la τ j • (Pi.single τ (Pi.single j 1) : Wt (U.X k).Ψ r) := by
    funext τ j
    simp [Finset.sum_apply, Pi.single_apply, ite_apply]
  show la ∈ S
  rw [e]
  exact S.sum_mem fun τ _ => S.sum_mem fun j _ => S.zsmul_mem (hsing τ j) _

section Adelic
variable (U : Unf Xo c σ r) {V : HSp D} {dict : GA D V → Σ k, Frame (U.X k).Ψ r} {mu : GA D V → ℂ}
  {Kf : Subgroup (GA D V)} {th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {hr : V.rank = r}

theorem adelAut_of_dominant
    (hχ : ∀ a n, Dom a n → ∀ k, ∀ γ ∈ (U.X k).Γ, (U.X k).χ (laU U a n k) γ = 1)
    (hd : DictIsUnif V dict Kf th hr) (hm : MuUnit V dict mu) (hc : Continuous mu)
    (hL : ∀ g₀ : GA D V, ∃ N ∈ 𝓝 g₀, ∃ (k : U.Comp) (x : GA D V → Frame (U.X k).Ψ r), ContinuousOn x N ∧
      ∀ g ∈ N, x g ∈ (U.X k).dom ∧ ∃ γ ∈ (U.X k).Γ, dict g = ⟨k, lact γ (x g)⟩) : AdelAut V dict mu := by
  intro la P hP
  refine ⟨fun γ hγ g => ?_, ?_⟩
  · obtain ⟨γ', hγ', he⟩ := hd.1 γ hγ g
    have hE := (hP (dict g).1).1.1.2.2 γ' hγ' (dict g).2 (hd.2.2.2.1 g)
    show mu (γ * g) * P (dict (γ * g)).1 (dict (γ * g)).2 = mu g * P (dict g).1 (dict g).2
    rw [he, hm.1, hm.2.2.1 γ hγ, one_mul]
    show mu g * P (dict g).1 (lact γ' (dict g).2) = _
    rw [hE, chi_eq_one U hχ _ _ _ hγ', one_mul]
  · rw [continuous_iff_continuousAt]
    intro g₀
    obtain ⟨N, hN, k, x, hx, hs⟩ := hL g₀
    have hsec : (U.X k).IsSec (la k) (P k) := (hP k).1.1
    have hc' : ContinuousOn (fun g => mu g * P k (x g)) N :=
      hc.continuousOn.mul (hsec.1.continuousOn.comp hx fun g hg => (hs g hg).1)
    have heq : (fun g => mu g * P k (x g)) =ᶠ[𝓝 g₀] adel V dict mu P := by
      filter_upwards [hN] with g hg
      obtain ⟨hd, γ, hγ, he⟩ := hs g hg
      show mu g * P k (x g) = mu g * P (dict g).1 (dict g).2
      rw [he]
      show mu g * P k (x g) = mu g * P k (lact γ (x g))
      rw [hsec.2.2 γ hγ (x g) hd, chi_eq_one U hχ _ _ _ hγ, one_mul]
    exact (hc'.continuousAt hN).congr heq

theorem meas_of_aut (h : AdelAut V dict mu) : AdelMeas1 U V dict mu := by
  intro la P hP
  obtain ⟨hL, hC⟩ := h la P hP
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  rw [onQ_eq_lift _ hL]
  exact Measurable.aestronglyMeasurable (measurable_from_quotient.2 hC.measurable)

theorem aeZero_of_aut (hA : AdelAut V dict mu) (hQ : QuotSupp V) (hmu : MuUnit V dict mu)
    (hd : DictIsUnif V dict Kf th hr) : AeDom1 U V dict mu := by
  intro la P hP hae k x hx
  have hA' := adelAut_holSub hA la hP
  have hz : ∀ g, adel V dict mu P g = 0 := hQ _ hA'.2 hA'.1 hae
  have hEq := eqv_holSub U.X la hP
  obtain ⟨g, γ, hγ, b, hb, hg⟩ := hd.2.2.2.2.1 k x hx
  have hdom := hd.2.2.2.1 g
  have h0 := hz g
  change mu g * P (dict g).1 (dict g).2 = 0 at h0
  rw [hg] at h0 hdom
  have hmu0 : mu g ≠ 0 := by
    intro h
    have := hmu.2.1 g
    rw [h, norm_zero] at this
    exact zero_ne_one this
  exact eq_zero_of_orbit _ (la k) (P k) (hEq.1 k) (hEq.2 k) hx hγ hb hdom ((mul_eq_zero.1 h0).resolve_left hmu0)

theorem four_laws (hS : Out.SecBaseChangeSt) (hU : IsUnf U)
    (hχ : ∀ a n, Dom a n → ∀ k, ∀ γ ∈ (U.X k).Γ, (U.X k).χ (laU U a n k) γ = 1)
    (hd : DictIsUnif V dict Kf th hr) (hm : MuUnit V dict mu) (hc : Continuous mu)
    (hL : ∀ g₀ : GA D V, ∃ N ∈ 𝓝 g₀, ∃ (k : U.Comp) (x : GA D V → Frame (U.X k).Ψ r), ContinuousOn x N ∧
      ∀ g ∈ N, x g ∈ (U.X k).dom ∧ ∃ γ ∈ (U.X k).Γ, dict g = ⟨k, lact γ (x g)⟩)
    (hT : VolTieG D) (hs : V.SigOK) :
    RdIndep1 U ∧ RdDomInj1 U ∧ AdelMeas1 U V dict mu ∧ AeDom1 U V dict mu :=
  have hA := adelAut_of_dominant U hχ hd hm hc hL
  ⟨(indep_of_isUnf hS U hU).1, (indep_of_isUnf hS U hU).2, meas_of_aut U hA,
    aeZero_of_aut U hA (quotSupp_of V (finVol_of_volTie hT V hs) (volPair_of_tie hT V hs)) hm hd⟩

theorem meas_zero : AdelMeas1 U V dict 0 := by
  intro la P _
  have : onQ V (adel V dict 0 P) = fun _ => 0 := by funext q; exact zero_mul _
  rw [this]; exact aestronglyMeasurable_const

theorem aeZero_zero_iff : AeDom1 U V dict 0 ↔ ∀ la, ∀ P ∈ holSub U.X la, ∀ k, ∀ x ∈ (U.X k).dom, P k x = 0 :=
  ⟨fun h la P hP => h la P hP (Filter.Eventually.of_forall fun _ => zero_mul _), fun h la P hP _ => h la P hP⟩

theorem meas_off_dom (h : AdelMeas1 U V dict mu) (P : FDSec U.X) (hP : ∀ k, ∀ x ∈ (U.X k).dom, P k x = 0) :
    AEStronglyMeasurable (onQ V (adel V dict mu P)) (muQ1 V) :=
  h (fun _ => 0) P fun k => (GlobalTheory.FJCheck.mem_SSgt_of_zero_on_dom (U.X k) 0 0 (hP k)).1

theorem adel_eq_zero_of_off_dom (hd : ∀ g, (dict g).2 ∈ (U.X (dict g).1).dom) (P : FDSec U.X)
    (hP : ∀ k, ∀ x ∈ (U.X k).dom, P k x = 0) : adel V dict mu P = 0 := by
  funext g
  show mu g * P _ _ = 0
  rw [hP _ _ (hd g), mul_zero]

theorem zero_of_dict_off_dom (hd : ∀ g, (dict g).2 ∉ (U.X (dict g).1).dom) (h : AeDom1 U V dict mu) (la)
    (f : Rul Xo c) (hf : rdU U f ∈ holSub U.X la) : rdU U f = 0 := by
  refine rdU_eq_zero U f (h la _ hf (Filter.Eventually.of_forall fun q => ?_))
  classical
  show mu q.out * (if h : (dict q.out).2 ∈ (U.X _).dom then toC (evR Xo c f (U.un _ ⟨_, h⟩)) else 0) = 0
  rw [dif_neg (hd _), mul_zero]

end Adelic
end GlobalTheory.OneEmbeddingProbe
