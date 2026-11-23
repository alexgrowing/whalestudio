import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsNonvanishing

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TopologicalSpace
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory.PushInv

open LBGerm

theorem exists_basisOn_any {S : Scheme.{0}} (hS : SecBaseChangeAnySt) (P : PolAV S) (x : S) :
    ∃ V : S.Opens, x ∈ V ∧ ∃ θ ∈ secOn P.L (P.A.hom ⁻¹ᵁ V), IsBasisOn P.A P.L V θ := by
  obtain ⟨V, hV, b, hb⟩ := hS S P 1 le_rfl x
  have hq : Unique (Fin (1 ^ P.g)) := by rw [one_pow]; infer_instance
  let T : Over S := overRes (T := baseOver S) V
  have hT : T.hom = V.ι := Category.comp_id _
  haveI : IsOpenImmersion T.hom := by rw [hT]; exact inferInstanceAs (IsOpenImmersion V.ι)
  haveI : IsOpenImmersion (snd T P.A).left := inferInstanceAs (IsOpenImmersion (pullback.snd T.hom P.A.hom))
  have hr : ∀ g : P.A.left, P.A.hom g ∈ V → g ∈ Set.range (snd T P.A).left := fun g hg => by
    rw [range_snd, hT]
    exact ⟨⟨_, hg⟩, rfl⟩
  choose θ hθ using fun i => exists_lift (snd T P.A).left (P.A.hom ⁻¹ᵁ V ⊓ P.L.U i) (fun g hg => hr g hg.1)
    ((LPow P.A P.L (1 : ℕ) T).U (fun _ => i)) (fun z hz => (mem_chart _ _ _ _ _ _).2 hz.2)
    ((b hq.default).f (fun _ => i))
  refine ⟨V, hV, θ, mem_secOn_of_germ θ fun g i j hg hi hj => ?_, fun R _ q hqV => ?_⟩
  · obtain ⟨z, rfl⟩ := hr g hg
    apply stalk_inj (snd T P.A).left z
    have hi' := (mem_chart P.A P.L T (1 : ℕ) z (fun _ => i)).2 hi
    have hj' := (mem_chart P.A P.L T (1 : ℕ) z (fun _ => j)).2 hj
    rw [map_mul, ← gs_stalkMap _ z (P.A.hom ⁻¹ᵁ V ⊓ P.L.U i) ⟨hg, hi⟩, ← gs_stalkMap _ z (P.A.hom ⁻¹ᵁ V ⊓ P.L.U j) ⟨hg, hj⟩,
      ← gm_comp _ (𝟙 _) z (P.L.U i ⊓ P.L.U j) ⟨hi, hj⟩, Category.comp_id]
    have e₁ := hθ i _ (𝟙 _) z ⟨hg, hi⟩
    have e₂ := hθ j _ (𝟙 _) z ⟨hg, hj⟩
    have e₃ := gm_lpow P.A P.L T (𝟙 _) z _ _ hi' hj'
    rw [Category.id_comp] at e₁ e₂ e₃
    rw [e₁, e₂, gs_compat (b hq.default) (𝟙 _) z hi' hj', e₃]
  · obtain ⟨t, rfl⟩ : ∃ t : Spec (CommRingCat.of R) ⟶ T.left, t ≫ T.hom = q :=
      ⟨IsOpenImmersion.lift T.hom q (by rw [hT]; exact hqV.trans (Scheme.Opens.range_ι V).ge), IsOpenImmersion.lift_fac _ _ _⟩
    choose b' hb' using fun i => exists_pull P.A P.L (1 : ℕ) (homAt t ▷ P.A) (whiskerRight_snd (homAt t) P.A) (b i)
    obtain ⟨hli, hsp⟩ := hb R t b' hb'
    have e : (homAt t ▷ P.A).left ≫ (snd T P.A).left = (snd (baseAt t) P.A).left :=
      congrArg CommaMorphism.left (whiskerRight_snd (homAt t) P.A)
    have val : ∀ (z : (baseAt t ⊗ P.A).left) i, (snd (baseAt t) P.A).left z ∈ P.L.U i →
        gs (𝟙 _) z _ ((b' hq.default).f (fun _ => i)) = gs (snd (baseAt t) P.A).left z _ (θ i) := fun z i hi => by
      have hi' := (mem_chart P.A P.L (baseAt t) (1 : ℕ) z (fun _ => i)).2 hi
      have hV' : P.A.hom ((snd (baseAt t) P.A).left z) ∈ V := by
        rw [← Scheme.Hom.comp_apply, w_snd, Scheme.Hom.comp_apply]
        exact hqV ⟨_, rfl⟩
      have hm : (snd T P.A).left ((homAt t ▷ P.A).left z) ∈ P.A.hom ⁻¹ᵁ V ⊓ P.L.U i := by
        rw [← Scheme.Hom.comp_apply, e]; exact ⟨hV', hi⟩
      have e₁ := hθ i _ (homAt t ▷ P.A).left z hm
      rw [e] at e₁
      rw [e₁, hb' hq.default (fun _ => i)]
      exact (gs_appLE (homAt t ▷ P.A).left _ _ _ (𝟙 _) z hi' _).trans (by rw [Category.id_comp])
    refine ⟨fun s => ?_, fun r h0 => ?_⟩
    · rw [Set.range_unique] at hsp
      obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 (hsp.ge (Submodule.mem_top (x := SecM.ofSec P.A s)))
      refine ⟨r, fun z i hi => ?_⟩
      have hi' := (mem_chart P.A P.L (baseAt t) (1 : ℕ) z (fun _ => i)).2 hi
      have := gs_smul P.A P.L (baseAt t) _ r (SecM.ofSec P.A (b' hq.default)) (fun _ => i) z hi'
      rw [hr] at this
      exact this.trans (congrArg _ (val z i hi))
    · refine Fintype.linearIndependent_iff.1 hli (fun _ => r) ?_ hq.default
      rw [Fintype.sum_unique]
      refine Subtype.ext (funext fun j => fn_ext fun z hz => ?_)
      obtain ⟨i, rfl⟩ : ∃ i, j = fun _ => i := ⟨j 0, funext fun k => by rw [Subsingleton.elim k 0]⟩
      have hi := (mem_chart P.A P.L (baseAt t) (1 : ℕ) z (fun _ => i)).1 hz
      refine (gs_smul P.A P.L (baseAt t) _ r (SecM.ofSec P.A (b' hq.default)) (fun _ => i) z hz).trans ?_
      exact ((congrArg _ (val z i hi)).trans (h0 z i hi)).trans (gs_zero _ z _ hz).symm

theorem pushInvertible_any : Out.SecBaseChangeAnySt → Out.GlobalSectionsRankAlgClosed →
    ∀ (S : Scheme.{0}) (Q : Out.PolAV S), PushInvertible Q.A Q.L := by
  intro hS _ S P x
  obtain ⟨V, hV, θ, hθ, H⟩ := exists_basisOn_any hS P x
  haveI := P.smoothDim
  haveI : Smooth P.A.hom := SmoothOfRelativeDimension.smooth P.g _
  refine ⟨V, hV, θ, hθ, fun W hW s hs => ?_, exists_nonvanishing H⟩
  have e : ∀ (a : Γ(S, W)) (g : P.A.left) i, P.A.hom g ∈ W → g ∈ P.L.U i →
      gs (𝟙 _) g _ ((P.A.hom.appLE W (P.A.hom ⁻¹ᵁ W ⊓ P.L.U i) inf_le_left).hom a *
        resG P.A.left (inf_le_inf_right _ (P.A.hom.preimage_mono hW)) (θ i)) =
      gs P.A.hom g W a * gs (𝟙 _) g _ (θ i) := fun a g i hg hi => by
    have hm : g ∈ P.A.hom ⁻¹ᵁ W ⊓ P.L.U i := ⟨hg, hi⟩
    rw [gs_mul (𝟙 _) g _ hm, gs_res (𝟙 _) g _ hm, gs_appLE _ _ _ _ (𝟙 _) g hm, Category.id_comp]
  obtain ⟨a, ha⟩ := exists_coeff H hW hs
  refine ⟨a, fun i => fn_ext fun g hg => (ha g i hg.1 hg.2).trans (e a g i hg.1 hg.2).symm, fun a' ha' => ?_⟩
  exact eq_of_mul H hW _ _ fun g i hg hi =>
    ((e a' g i hg hi).symm.trans (congrArg _ (ha' i).symm)).trans (ha g i hg hi)

end GlobalTheory.PushInv
