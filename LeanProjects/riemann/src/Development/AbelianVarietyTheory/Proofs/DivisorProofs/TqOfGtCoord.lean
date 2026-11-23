import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolOfSecondQuotient
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SurjectiveCubeBaseChange
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsCPMapCompCancel
import Development.AbelianVarietyTheory.Definitions.Uniformization.NotExistsEvenTwistSymOne
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum
open GlobalTheory.UU GlobalTheory.LN

def tqOfGtCoord {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)
    (hB : IsAbelianScheme (thickObj R I e D.P.A)) : TQ (thickObj R I e G) D.X where
  B := thickObj R I e D.P.A
  isAb := hB
  q := g.q
  i := g.i
  q_hom := g.q_hom
  i_hom := g.i_hom
  q_flat := g.q_flat
  q_surj := g.q_surj
  q_affine := g.q_affine
  isKernel := g.isKernel
  loc b χ := by
    have := g.q_hom
    have := g.i_hom
    let ψ := D.Oφ (D.prBe I e) χ
    have hψ : ∀ k, D.Oφ g.pG χ k = g.q.left ≫ ψ k := fun k => by
      fin_cases k
      · show (padd _ _ _).left = ((Over.map (thick R I e)).map g.q ≫ padd _ _ _).left
        congr 1
        refine Eq.trans ?_ (MonObj.comp_mul _ _ _).symm
        rw [← Category.assoc, toUnit_unique (_ ≫ toUnit _) (toUnit _)]; rfl
      · show (_ ≫ _ : _ ⟶ D.P.A).left = ((Over.map (thick R I e)).map g.q ≫ _ ≫ _).left
        rw [← Category.assoc, toUnit_unique (_ ≫ toUnit _) (toUnit _)]
      · rfl
      · show (_ ≫ _ : _ ⟶ D.P.A).left = ((Over.map (thick R I e)).map g.q ≫ _ ≫ _).left
        rw [← Category.assoc, toUnit_unique (_ ≫ toUnit _) (toUnit _)]
    choose j hj using fun k => exists_chart D.P.isLB (ψ k b)
    have hle : g.q.left ⁻¹ᵁ LB.wchart D.P.L ψ j ≤ LB.wchart D.P.L (D.Oφ g.pG χ) j := fun x hx =>
      Set.mem_iInter.2 fun k => by rw [hψ]; exact Set.mem_iInter.1 hx k
    refine ⟨LB.wchart D.P.L ψ j, Set.mem_iInter.2 hj, res hle ((g.t χ).s j), fun Z t x h₁ h₂ => ?_⟩
    have ap : ∀ (r : Z.left ⟶ (thickObj R I e G).left) (V) (h : ⊤ ≤ r ⁻¹ᵁ V) (u : Γ((thickObj R I e G).left, V)ˣ)
        (z : Z.left), gm (𝟙 Z.left) z ⊤ (Units.map (r.appLE V ⊤ h).hom.toMonoidHom u) = gm r z V u :=
      fun r V h u z => (gm_res (𝟙 Z.left) z h trivial (pullU r V u)).trans ((gm_pull _ r z V (h trivial) u).trans
        (by rw [Category.id_comp]))
    have key : Units.map (((t ≫ g.i) * x).left.appLE _ ⊤ h₁).hom.toMonoidHom (res hle ((g.t χ).s j)) =
        chV t χ * Units.map (x.left.appLE _ ⊤ h₂).hom.toMonoidHom (res hle ((g.t χ).s j)) := unit_ext fun z _ => by
      obtain ⟨J, hJ⟩ := exists_good_pt D.P.isLB z
      have m₁ := h₁ (show z ∈ (⊤ : Z.left.Opens) from trivial)
      have m₂ := h₂ (show z ∈ (⊤ : Z.left.Opens) from trivial)
      have hq : ((t ≫ g.i) * x) ≫ g.q = x ≫ g.q := by
        rw [MonObj.mul_comp, Category.assoc, g.isKernel.w, ← Category.assoc,
          toUnit_unique (t ≫ toUnit _) (toUnit Z), ← Hom.one_def, _root_.one_mul]
      have hk : ∀ k, ((t ≫ g.i) * x).left ≫ D.Oφ g.pG χ k = x.left ≫ D.Oφ g.pG χ k := fun k => by
        rw [hψ, ← Category.assoc, ← Category.assoc, ← Over.comp_left, hq, Over.comp_left]
      rw [map_mul, ap, ap]
      refine ((gm_res _ z hle m₁ _).trans (gen_trans (g.t_gen χ) _ z (hle m₁) (hJ.mem _ _))).trans (Eq.trans ?_
        (congrArg (_ * ·) ((gm_res _ z hle m₂ _).trans (gen_trans (g.t_gen χ) _ z (hle m₂) (hJ.mem _ _)))).symm)
      have w := (val_pull hJ _ _ _).symm.trans ((val_corr hJ (g.t_weight χ) (lift t x).left).trans
        ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _))))
      rw [← Over.comp_left, ← Over.comp_left, lift_snd] at w
      have e₁ : lift t x ≫ lift (fst _ _ ≫ g.i) (snd _ _) ≫ μ[thickObj R I e G] = (t ≫ g.i) * x := by
        rw [Hom.mul_def, ← Category.assoc, comp_lift, lift_fst_assoc, lift_snd]
      have e₂ : val (charGen D.X (thickObj R I e G) D.P.L χ) (lift t x).left z J = gm (𝟙 Z.left) z ⊤ (chV t χ) := by
        refine (gm_res _ z _ (hJ.mem _ _) _).trans ((gm_pull _ _ z ⊤ trivial _).trans ?_)
        rw [← Over.comp_left, lift_fst, gm_charUnit]
      rw [e₁, e₂] at w
      refine (congrArg₂ (· * ·) ?_ w).trans (mul_left_comm _ _ _)
      exact Finset.prod_congr rfl fun k _ => congrArg
        (fun q => gm q z (D.P.L.U (j k) ⊓ D.P.L.U (J q)) (D.P.L.g (j k) (J q)) ^ Oinvε k) (hk k)
    exact (congrArg Units.val key).trans (congrArg (· * _) (chV_val t χ))

set_option maxHeartbeats 2000000 in

theorem unif_evenOn : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) →
    ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G],
    IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∃ P : GlobalTheory.UU.CP G, P.L = U.LG ∧ EvenOn P := by
  intro R _ _ _ _ D A G _ _ hS U
  obtain ⟨hL, -, -, -, -⟩ := GlobalTheory.firstFiveLaws
  obtain ⟨w, hw⟩ := U.ext
  let U' := GlobalTheory.ValueForm.toPreU U.toUnifPre hL.globalFns hS w hw
  refine ⟨U'.P, rfl, ?_⟩
  obtain ⟨P₀, w₀, h₀⟩ := exists_isLevelCP (maximalIdeal R) 0 U'.P
  obtain ⟨rig, hr, c, σ, h₁, h₂, h₃, H⟩ := exists_isCPMap U'.P (toBase_mul_pullback G (thick R (maximalIdeal R) 0)) _
    (pull_isLB U'.P.L.isLB _) _ (pullIso_isGen U'.P.L.isLB (pullback.fst G.hom (thick R (maximalIdeal R) 0)))
  obtain ⟨w₁, k₁⟩ := GlobalTheory.ClosedPol.cpMap_congr (Category.id_comp _).symm (Category.id_comp _).symm h₀
    (by rw [Category.id_comp, Category.id_comp]; exact pullback.condition)
  obtain ⟨w₂, k₂, -⟩ := (isCPMap_comp_cancel _ _ _ _ _ _ _ _ _ _ P₀ _ _ _ (𝟙 _) (by simp) _ H).2
    (toBase_mul_of_isMonHom (𝟙 _) _) w₁ k₁
  have H' := GlobalTheory.ClosedPol.isCPMap_w hL.globalFns U' 0 H
  obtain ⟨w₃, -, k₃⟩ := H'.exists_comp k₂ (by rw [Category.id_comp, Category.id_comp]; exact Over.w (U'.gt 0).pG)
  obtain ⟨w₄, k₄⟩ := GlobalTheory.ClosedPol.cpMap_congr (Category.id_comp _) (Category.id_comp _) k₃ (Over.w (U'.gt 0).pG)
  have hB : IsAbelianScheme (thickObj R (maximalIdeal R) 0 D.toPre.P.A) :=
    GlobalTheory.isAbelianScheme_pullback_obj _ _ D.toPre.P.isAb
  let g := U'.gt 0
  have := g.q_hom
  let Q₀ := tqOfGtCoord g hB
  obtain ⟨M₀, v, hv⟩ := exists_isLevelCP (maximalIdeal R) 0 (CP.ofDegPre hL.globalFns D.toPre)
  have hw' : g.q.left ≫ (thickObj R (maximalIdeal R) 0 D.toPre.P.A).hom =
      (thickObj R (maximalIdeal R) 0 G).hom ≫ 𝟙 _ :=
    (Over.w g.q).trans (Category.comp_id _).symm
  have hw'' : (g.q.left ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) 0)) ≫ D.toPre.P.A.hom =
      (thickObj R (maximalIdeal R) 0 G).hom ≫ 𝟙 _ ≫ thick R (maximalIdeal R) 0 := by
    exact (Over.w g.pG).trans (congrArg (_ ≫ ·) (Category.id_comp _).symm)
  obtain ⟨w₅, k₅⟩ := GlobalTheory.ClosedPol.cpMap_congr (Category.id_comp _).symm rfl k₄ hw''
  obtain ⟨w₆, k₆, -⟩ := (isCPMap_comp_cancel _ _ _ _ _ _ _ _ _ M₀ P₀ _ _ _ g.q.left hw' hw'' hv).2
    (toBase_mul_of_isMonHom g.q hw') w₅ k₅
  let Dsc : Q₀.Desc P₀ := ⟨M₀, w₆, k₆⟩
  obtain ⟨τ, hτ⟩ := Dsc.exists_even
  exact ⟨D.toPre.X, D.toPre.addX, D.toPre.freeX, D.toPre.finX, Q₀, P₀, ⟨w₀, h₀⟩, τ, hτ⟩

end GlobalTheory.Mum
