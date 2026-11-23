import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetHypOfIsTripleOfGalHodge
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTwLFull
import Formalism.LocalToGlobal.UnitaryNorms.CharShare

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Neutral.B1 GlobalTheory.HeckeGal GlobalTheory.GalChar

noncomputable section

namespace GlobalTheory.DeltaGal

theorem continuous_comp_of_isOpen_ker {Gp M Y : Type*} [Group Gp] [TopologicalSpace Gp] [IsTopologicalGroup Gp]
    [Group M] [TopologicalSpace Y] (f : Gp →* M) (h : IsOpen (f.ker : Set Gp)) (u : M → Y) :
    Continuous (fun g => u (f g)) := by
  refine continuous_iff_continuousAt.2 fun g => ?_
  have hm : (fun x => g⁻¹ * x) ⁻¹' (f.ker : Set Gp) ∈ nhds g :=
    ((continuous_const.mul continuous_id).isOpen_preimage _ h).mem_nhds (by simp)
  refine (continuousAt_const (y := u (f g))).congr ?_
  filter_upwards [hm] with x hx
  simp only [Set.mem_preimage, SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv] at hx
  rw [inv_mul_eq_one.1 hx]

theorem delta_isGal : GlobalTheory.Published.ChebotarevDegreeOne → ∀ {D : D7} {cf : CharFrame D} {b0 b1 : Big D} {Sx : Finset (PlE D.host)} {T : TwR D.LL0 D.nd} (Sp : RingSpec D cf b0 b1 Sx T) {art : Ideles D.host.E →* Gab D.host.E D.nd.Om}, IsGlobalArtin art → ∀ (i : T.Tw) (κ : FractionRing (T.O0 i) →+* Qbar (T.l i)) (ι : Qbar (T.l i) ≃+* ℂ), (∀ x : D.LL0, ι (κ (T.emb0 i x)) = D.what₂.embLL (x : D.what₂.LL)) → IsGal art κ ι (cf.delAt (T.l i)) 0 (T.delta i) := by
  intro _ D cf b0 b1 Sx T Sp art hart i κ ι hι
  set χ := cf.delAt (T.l i) with hχ
  have hfin : ∃ n, 0 < n ∧ χ.OrderDvd n := by
    rw [hχ]; unfold CharFrame.delAt; split_ifs
    exacts [cf.isDel'.fin, cf.isDel.fin]
  obtain ⟨n, hn, hord⟩ := hfin
  have hpos : IsAlgPos χ 0 := fun k _ => by
    rw [HChar.inf_eq_one_of_order hn hord k]; simp
  refine ⟨hpos, continuous_comp_of_isOpen_ker (T.delta i) (T.delta_open i) (fun u => (u : T.O0 i)), ?_⟩
  obtain ⟨r', hr'c, hr'⟩ := hart.exists_isLAdicOf ι hpos
  suffices h : inQ κ (T.delta i) = r' by rw [h]; exact hr'
  have hc : Continuous (inQ κ (T.delta i)) :=
    continuous_comp_of_isOpen_ker (T.delta i) (T.delta_open i) (Units.map (toQ κ : T.O0 i →* Qbar (T.l i)))
  have h0 : Ideal.span {((T.l i : ℕ) : 𝓞 D.host.E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (T.lPrime i).out.ne_zero
  have hl : ∀ᶠ v : HeightOneSpectrum (𝓞 D.host.E) in Filter.cofinite, ((T.l i : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal :=
    (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr (not_not.1 hv)
  have hS := Filter.eventually_cofinite.1 (hl.and (GlobalTheory.Mem.UnrAe.unr_ae_and_level _ χ).1)
  refine mul_inv_eq_one.1 (GlobalTheory.FrobDense.eq_one_of_frob _ _ art hart _ (inQ κ (T.delta i) * r'⁻¹)
    (hc.mul hr'c.inv) hS.toFinset fun v hv A hA σ hσ => ?_)
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hv
  rw [MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv_eq_one]
  apply Units.ext
  rw [hr'.frob_unr hart (Or.inr rfl) hv.2 hA hσ]
  obtain ⟨x, hx1, hx2⟩ := Sp.deltaRead i v hv.1 hv.2 A σ hA hσ
  show κ (algebraMap _ _ ((T.delta i σ : T.O0 i))) = _
  rw [hx2]
  apply ι.injective
  rw [hι, hx1, map_inv₀, RingEquiv.apply_symm_apply, Units.val_inv_eq_inv_val]

end GlobalTheory.DeltaGal
