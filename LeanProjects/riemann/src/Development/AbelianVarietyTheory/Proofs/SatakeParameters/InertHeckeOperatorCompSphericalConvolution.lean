import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDoubleCosetsDefiniteUnitaryMaximalLevelStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsCharacterEigenvectorOfCommutingRepresentat
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvMemDoubleCosetAndComm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryDoubleCosetFiniteLeftCosetsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMaxCompactOfTrivOutsideLocalIntegralStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteInertHeckeSupportCosetsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertLocalMemLocalUnitaryGroupStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertLocalIntegralOfMemLatticeStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsTrivOutsideInertLocalEqStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.UG

noncomputable section

open GlobalTheory.SatInd

namespace GlobalTheory.InertConv

theorem eq_of_coset {G : Type} [Group G] {K : Subgroup G} {k : Type} {H : G → k}
    (hH : ∀ (a : G) (c : K), H (a * c) = H a) {a b : G} (hab : (a : G ⧸ K) = b) : H a = H b := by
  have hc := QuotientGroup.eq.1 hab
  have := hH a ⟨a⁻¹ * b, hc⟩
  change H (a * (a⁻¹ * b)) = H a at this
  rw [mul_inv_cancel_left] at this
  exact this.symm

theorem finsum_eq_of_support_subset_range {α β M : Type} [AddCommMonoid M] {F : α → M} {e : β → α}
    (he : Function.Injective e) (hs : Function.support F ⊆ Set.range e) :
    ∑ᶠ c, F c = ∑ᶠ d, F (e d) := by
  rw [← finsum_mem_range he, ← finsum_mem_inter_support, Set.inter_eq_right.2 hs, finsum_mem_support]

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
  {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {w : HeightOneSpectrum (𝓞 L)}

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem conv_of (Dv : InertDatum L n v w) (U : Subgroup (GAf L n))
    (hU : ∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n))
    (hA : ∀ x : GAf L n, Dv.loc x ∈ GU Dv.σw n)
    (hE : ∀ u ∈ Umax L n, ∀ i j, ((Dv.loc u : GL (Fin n) (w.adicCompletion L)) :
      Matrix (Fin n) (Fin n) (w.adicCompletion L)) i j ∈ intL (w.adicCompletion L))
    (hC : ∀ y ∈ GU Dv.σw n, ∃ x : GAf L n, TrivOutside {v} x ∧ Dv.loc x = y)
    (W : Type) [AddCommGroup W] [Module ℂ W]
    (h : GU Dv.σw n → ℂ) (hh : h ∈ Hecke ℂ (KU Dv.σw n))
    (h' : GU Dv.σw n → ℂ) (hh' : h' ∈ Hecke ℂ (KU Dv.σw n))
    (f : GAf L n → W) (hf : ∀ κ ∈ U, NG.rt L n κ f = f) :
    heckeFunI L n U Dv (conv (KU Dv.σw n) h h') f =
      heckeFunI L n U Dv h (heckeFunI L n U Dv h' f) := by
  classical
  set K := KU Dv.σw n with hKdef
  let lam : GAf L n →* GU Dv.σw n := MonoidHom.codRestrict (GlobalTheory.SatInd.CosetFin.locHom Dv) _ hA
  have hlam : ∀ x, ((lam x : GU Dv.σw n) : GL (Fin n) (w.adicCompletion L)) = Dv.loc x := fun _ => rfl
  have hK1 : ∀ u ∈ Umax L n, lam u ∈ K := by
    intro u hu
    refine GlobalTheory.SatInd.DCoset.mem_KU_of_entries (lam u) (fun i j => hE u hu i j) (fun i j => ?_)
    rw [← map_inv]
    exact hE u⁻¹ (inv_mem hu) i j
  have hR : ∀ x x' : GAf L n, TrivOutside {v} x → TrivOutside {v} x' →
      ((x : GAf L n ⧸ U) = x' ↔ ((lam x : GU Dv.σw n ⧸ K) = lam x')) := by
    intro x x' hx hx'
    have ht : TrivOutside {v} (x⁻¹ * x') :=
      GlobalTheory.SatInd.CosetFin.trivOutside_mul (GlobalTheory.SatInd.CosetFin.trivOutside_inv hx) hx'
    rw [QuotientGroup.eq, QuotientGroup.eq, ← map_inv, ← map_mul]
    constructor
    · intro hu; exact hK1 _ ((hU _ ht).1 hu)
    · intro hk
      exact (hU _ ht).2 (GlobalTheory.T.mem_maxCompact_of_trivOutside_local_integral L n v w Dv _ ht fun i j => GlobalTheory.SatInd.CosetFin.entries_int hk i j)
  have hCs : ∀ d : GU Dv.σw n ⧸ K, ∃ x : GAf L n, TrivOutside {v} x ∧ lam x = d.out := fun d => by
    obtain ⟨x, hx, e⟩ := hC _ d.out.2
    exact ⟨x, hx, Subtype.ext e⟩
  choose s hs1 hs2 using hCs
  have heT : ∀ d : GU Dv.σw n ⧸ K, ∃ x : GAf L n, (x : GAf L n ⧸ U) = (s d : GAf L n ⧸ U) ∧
      TrivOutside {v} x := fun d => ⟨s d, rfl, hs1 d⟩
  have hρ1 : ∀ d, TrivOutside {v} (heT d).choose := fun d => (heT d).choose_spec.2
  have hρ2 : ∀ d, ((lam (heT d).choose : GU Dv.σw n) : GU Dv.σw n ⧸ K) = d := fun d => by
    rw [(hR _ _ (hρ1 d) (hs1 d)).1 (heT d).choose_spec.1, hs2 d, QuotientGroup.out_eq']
  have he : Function.Injective (fun d : GU Dv.σw n ⧸ K => ((s d : GAf L n) : GAf L n ⧸ U)) := by
    intro d d' hdd
    have := (hR _ _ (hs1 d) (hs1 d')).1 hdd
    rwa [hs2, hs2, QuotientGroup.out_eq', QuotientGroup.out_eq'] at this

  have step2 : ∀ (H : GU Dv.σw n → ℂ), (∀ (a : GU Dv.σw n) (c : K), H (a * c) = H a) →
      ∀ (F : GAf L n → W) (g : GAf L n),
      heckeFunI L n U Dv H F g = ∑ᶠ d : GU Dv.σw n ⧸ K, H d.out • F (g * (heT d).choose) := by
    intro H hH F g
    show (∑ᶠ c : GAf L n ⧸ U, _) = _
    rw [finsum_eq_of_support_subset_range he]
    · refine finsum_congr fun d => ?_
      rw [dif_pos (heT d)]
      have hv : Dv.hval H (Dv.loc (heT d).choose) = H d.out := by
        rw [InertDatum.hval, dif_pos (hA _)]
        exact eq_of_coset hH (by rw [QuotientGroup.out_eq']; exact hρ2 d)
      rw [hv]
    · intro c hc
      rw [Function.mem_support] at hc
      by_cases hT : ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x
      · obtain ⟨x, hxc, hx⟩ := hT
        refine ⟨(lam x : GU Dv.σw n ⧸ K), ?_⟩
        show ((s _ : GAf L n) : GAf L n ⧸ U) = c
        rw [← hxc]
        refine (hR _ _ (hs1 _) hx).2 ?_
        rw [hs2, QuotientGroup.out_eq']
      · rw [dif_neg hT] at hc
        exact absurd rfl hc

  have hRi : ∀ (H : GU Dv.σw n → ℂ), H ∈ Hecke ℂ K → ∀ (a : GU Dv.σw n) (c : K), H (a * c) = H a :=
    fun H hH a c => by simpa using hH.1 1 c a
  have hLi : ∀ (H : GU Dv.σw n → ℂ), H ∈ Hecke ℂ K → ∀ (c : K) (a : GU Dv.σw n), H (c * a) = H a :=
    fun H hH c a => by simpa using hH.1 c 1 a
  have hconvR : ∀ (a : GU Dv.σw n) (c : K), conv K h h' (a * c) = conv K h h' a := by
    intro a c
    simp only [Formalism.UG.conv]
    refine finsum_congr fun x => ?_
    rw [← mul_assoc, hRi h' hh']
  have hfin : ∀ H ∈ Hecke ℂ K, Set.Finite {d : GU Dv.σw n ⧸ K | H d.out ≠ 0} := by
    rintro H ⟨-, S, hS⟩
    refine (S.finite_toSet.biUnion fun t _ => GlobalTheory.T.unitary_doubleCoset_finite_left_cosets Dv.ϖ Dv.σw _ n Dv.unram t).subset ?_
    intro d hd
    obtain ⟨t, ht, a, b, hab⟩ := hS _ hd
    refine Set.mem_biUnion ht ⟨(a : GU Dv.σw n), a.2, ?_⟩
    conv_rhs => rw [← QuotientGroup.out_eq' d]
    rw [hab]
    exact (QuotientGroup.mk_mul_of_mem _ b.2).symm
  have hfU : ∀ a b : GAf L n, (a : GAf L n ⧸ U) = b → ∀ g, f (g * a) = f (g * b) := by
    intro a b hab g
    have hu := QuotientGroup.eq.1 hab
    have : f (g * a * (a⁻¹ * b)) = f (g * a) := congrFun (hf _ hu) (g * a)
    rw [← this, mul_assoc, mul_inv_cancel_left]
  funext g
  rw [step2 _ hconvR f g, step2 h (hRi h hh) _ g]
  have inner : ∀ d : GU Dv.σw n ⧸ K,
      heckeFunI L n U Dv h' f (g * (heT d).choose) =
        ∑ᶠ e : GU Dv.σw n ⧸ K, h' (d.out⁻¹ * e.out) • f (g * (heT e).choose) := by
    intro d
    rw [step2 h' (hRi h' hh') f]
    set x := lam (heT d).choose with hx
    have hk : x⁻¹ * d.out ∈ K := QuotientGroup.eq.1 (by rw [QuotientGroup.out_eq']; exact hρ2 d)
    have hL : ∀ y, h' (d.out⁻¹ * y) = h' (x⁻¹ * y) := by
      intro y
      have := hLi h' hh' ⟨(x⁻¹ * d.out)⁻¹, inv_mem hk⟩ (x⁻¹ * y)
      rw [← this]
      congr 1
      show _ = (x⁻¹ * d.out)⁻¹ * (x⁻¹ * y)
      group
    refine Eq.trans ?_ (finsum_comp_equiv (MulAction.toPerm x : Equiv.Perm (GU Dv.σw n ⧸ K)))
    refine finsum_congr fun e => ?_
    simp only [MulAction.toPerm_apply]
    congr 1
    · rw [hL]
      refine eq_of_coset (hRi h' hh') ?_
      rw [QuotientGroup.out_eq', ← smul_eq_mul, ← MulAction.Quotient.smul_mk, QuotientGroup.out_eq',
        inv_smul_smul]
    · rw [mul_assoc]
      refine hfU _ _ ((hR _ _ (GlobalTheory.SatInd.CosetFin.trivOutside_mul (hρ1 d) (hρ1 e)) (hρ1 _)).2 ?_) g
      rw [map_mul, hρ2, ← hx, ← smul_eq_mul, ← MulAction.Quotient.smul_mk, hρ2]
  rw [finsum_congr fun d => congrArg (h d.out • ·) (inner d)]
  have hSe : Set.Finite (⋃ (d : GU Dv.σw n ⧸ K) (_ : d ∈ {d : GU Dv.σw n ⧸ K | h d.out ≠ 0}),
      (fun c : GU Dv.σw n ⧸ K => (d.out • c : GU Dv.σw n ⧸ K)) '' {c : GU Dv.σw n ⧸ K | h' c.out ≠ 0}) :=
    (hfin h hh).biUnion fun d _ => (hfin h' hh').image _
  have hmem : ∀ d e : GU Dv.σw n ⧸ K, h d.out ≠ 0 → h' (d.out⁻¹ * e.out) ≠ 0 →
      e ∈ hSe.toFinset := by
    intro d e hd he'
    rw [Set.Finite.mem_toFinset]
    refine Set.mem_biUnion hd ⟨d.out⁻¹ • e, ?_, smul_inv_smul d.out e⟩
    have hc : (((d.out⁻¹ • e).out : GU Dv.σw n) : GU Dv.σw n ⧸ K) = ↑(d.out⁻¹ * e.out) := by
      rw [QuotientGroup.out_eq', ← smul_eq_mul, ← MulAction.Quotient.smul_mk, QuotientGroup.out_eq']
    show h' (d.out⁻¹ • e).out ≠ 0
    rw [eq_of_coset (hRi h' hh') hc]
    exact he'
  have hL1 : (∑ᶠ e : GU Dv.σw n ⧸ K, conv K h h' e.out • f (g * (heT e).choose)) =
      ∑ e ∈ hSe.toFinset, (∑ d ∈ (hfin h hh).toFinset, h d.out * h' (d.out⁻¹ * e.out)) •
        f (g * (heT e).choose) := by
    rw [finsum_eq_sum_of_support_subset _ (s := hSe.toFinset) ?_]
    · refine Finset.sum_congr rfl fun e _ => ?_
      congr 1
      show (∑ᶠ d : GU Dv.σw n ⧸ K, h d.out * h' (d.out⁻¹ * e.out)) = _
      apply finsum_eq_sum_of_support_subset
      intro d hd
      rw [Function.mem_support] at hd
      rw [Set.Finite.coe_toFinset]
      exact left_ne_zero_of_mul hd
    · intro e he
      rw [Function.mem_support] at he
      have h1 : conv K h h' e.out ≠ 0 := fun h0 => he (by rw [h0, zero_smul])
      obtain ⟨d, hd⟩ : ∃ d : GU Dv.σw n ⧸ K, h d.out * h' (d.out⁻¹ * e.out) ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        exact h1 (finsum_eq_zero_of_forall_eq_zero hcon)
      exact hmem d e (left_ne_zero_of_mul hd) (right_ne_zero_of_mul hd)
  have hR1 : (∑ᶠ d : GU Dv.σw n ⧸ K, h d.out • ∑ᶠ e : GU Dv.σw n ⧸ K,
      h' (d.out⁻¹ * e.out) • f (g * (heT e).choose)) =
      ∑ d ∈ (hfin h hh).toFinset, ∑ e ∈ hSe.toFinset, (h d.out * h' (d.out⁻¹ * e.out)) •
        f (g * (heT e).choose) := by
    rw [finsum_eq_sum_of_support_subset _ (s := (hfin h hh).toFinset) ?_]
    · refine Finset.sum_congr rfl fun d hd => ?_
      rw [Set.Finite.mem_toFinset] at hd
      rw [finsum_eq_sum_of_support_subset _ (s := hSe.toFinset) ?_, Finset.smul_sum]
      · exact Finset.sum_congr rfl fun e _ => by rw [mul_smul]
      · intro e he
        rw [Function.mem_support] at he
        exact hmem d e hd (fun h0 => he (by rw [h0, zero_smul]))
    · intro d hd
      rw [Function.mem_support] at hd
      rw [Set.Finite.coe_toFinset]
      exact fun h0 => hd (by rw [h0, zero_smul])
  rw [hL1, hR1, Finset.sum_comm]
  exact Finset.sum_congr rfl fun e _ => by rw [Finset.sum_smul]

theorem heckeFunI_conv : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (U : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W], ∀ h ∈ Hecke ℂ (KU Dv.σw n), ∀ h' ∈ Hecke ℂ (KU Dv.σw n), ∀ f : GAf L n → W, (∀ κ ∈ U, NG.rt L n κ f = f) → heckeFunI L n U Dv (conv (KU Dv.σw n) h h') f = heckeFunI L n U Dv h (heckeFunI L n U Dv h' f) := by
  intro L _ _ _ n v w Dv U hU W _ _ h hh h' hh' f hf
  exact conv_of Dv U hU (GlobalTheory.T.inertLocal_mem_localUnitaryGroup L n v w Dv) (GlobalTheory.T.inertLocal_integral_of_mem_latticeStabilizer L n v w Dv) (GlobalTheory.T.exists_trivOutside_inertLocal_eq L n v w Dv)
    W h hh h' hh' f hf

end GlobalTheory.InertConv
