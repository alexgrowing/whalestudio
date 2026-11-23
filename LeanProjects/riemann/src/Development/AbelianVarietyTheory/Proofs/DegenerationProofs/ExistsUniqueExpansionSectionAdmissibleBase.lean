import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecEqZeroAndHomEqOfThickenings
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AbelianProjectiveBaseChange
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueThickTorusLevelWeightExpansion
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsExpansionSectionLineBundlePower
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalEqZeroOfWeightSum

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

noncomputable section
namespace GlobalTheory.CompleteBaseExpansion
open GlobalTheory.BaseExpansionExists

section General
variable {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}

theorem pull_le (h : Y' ⟶ Y) (j : PUnit → K → L.ι) :
    ((LB.LinComb L φ ε).pull h).U j ≤ LB.wchart L (fun k => h ≫ φ k) (j PUnit.unit) :=
  fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (mem_pull.1 hy) k

theorem le_pull (h : Y' ⟶ Y) (j : K → L.ι) :
    LB.wchart L (fun k => h ≫ φ k) j ≤ ((LB.LinComb L φ ε).pull h).U (fun _ => j) :=
  fun _ hy => mem_pull.2 (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k)

theorem g_pull (h : Y' ⟶ Y) (y : Y') (j j' : PUnit → K → L.ι) (hj : y ∈ ((LB.LinComb L φ ε).pull h).U j)
    (hj' : y ∈ ((LB.LinComb L φ ε).pull h).U j') :
    gs (𝟙 Y') y _ (((LB.LinComb L φ ε).pull h).g j j').val =
      (trF (fun k => h ≫ φ k) ε (𝟙 Y') y (j PUnit.unit) (j' PUnit.unit)).val := by
  have hm : (𝟙 Y' : Y' ⟶ Y') y ∈ ((LB.LinComb L φ ε).pull h).U j ⊓ ((LB.LinComb L φ ε).pull h).U j' := ⟨hj, hj'⟩
  refine (gs_unit (𝟙 Y') y _ hm _).trans (congrArg Units.val ?_)
  refine (gm_pull_g (LB.LinComb L φ ε) h (𝟙 Y') y j j' hj hj').trans ?_
  refine (gm_linComb L φ ε (𝟙 Y' ≫ h) y _ _ (mem_pull.1 hj) (mem_pull.1 hj')).trans ?_
  simp only [trF, Category.assoc]

theorem exists_in (h : Y' ⟶ Y) (s : LB.Sec (LB.LinComb L (fun k => h ≫ φ k) ε)) :
    ∃ s' : LB.Sec ((LB.LinComb L φ ε).pull h), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (j : PUnit → K → L.ι),
      r z ∈ ((LB.LinComb L φ ε).pull h).U j →
      gs r z _ (s'.f j) = gs r z (LB.wchart L (fun k => h ≫ φ k) (j PUnit.unit)) (s.f (j PUnit.unit)) := by
  refine ⟨⟨fun j => (Y'.presheaf.map (homOfLE (pull_le h j)).op).hom (s.f (j PUnit.unit)),
    fun j j' => fn_ext fun y hy => ?_⟩, fun Z r z j hz => gs_res r z _ hz _⟩
  refine ((gs_res (𝟙 Y') y _ hy _).trans (gs_res (𝟙 Y') y (pull_le h j) hy.1 _)).trans (Eq.trans ?_
    ((gs_mul (𝟙 Y') y _ hy _ _).trans (congrArg₂ (· * ·) (g_pull h y j j' hy.1 hy.2)
      ((gs_res (𝟙 Y') y _ hy _).trans (gs_res (𝟙 Y') y (pull_le h j') hy.2 _)))).symm)
  exact sec_trans s (𝟙 Y') y (pull_le h j hy.1) (pull_le h j' hy.2)

theorem exists_out (h : Y' ⟶ Y) (s' : LB.Sec ((LB.LinComb L φ ε).pull h)) :
    ∃ s : LB.Sec (LB.LinComb L (fun k => h ≫ φ k) ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (j : K → L.ι),
      r z ∈ LB.wchart L (fun k => h ≫ φ k) j →
      gs r z (LB.wchart L (fun k => h ≫ φ k) j) (s.f j) =
        gs r z (((LB.LinComb L φ ε).pull h).U (fun _ => j)) (s'.f (fun _ => j)) := by
  refine ⟨⟨fun j => (Y'.presheaf.map (homOfLE (le_pull (ε := ε) h j)).op).hom (s'.f (fun _ => j)),
    fun j j' => fn_ext fun y hy => ?_⟩, fun Z r z j hz => gs_res r z _ hz _⟩
  have hm : (𝟙 Y' : Y' ⟶ Y') y ∈ ((LB.LinComb L φ ε).pull h).U (fun _ => j) ⊓
    ((LB.LinComb L φ ε).pull h).U (fun _ => j') := ⟨le_pull h j hy.1, le_pull h j' hy.2⟩
  refine ((gs_res (𝟙 Y') y _ hy _).trans (gs_res (𝟙 Y') y (le_pull h j) hy.1 _)).trans (Eq.trans ?_
    ((gs_mul (𝟙 Y') y _ hy _ _).trans (congrArg₂ (· * ·) ((gs_unit (𝟙 Y') y _ hy _).trans
      (congrArg Units.val (gm_linComb L _ ε (𝟙 Y') y j j' hy.1 hy.2)))
      ((gs_res (𝟙 Y') y _ hy _).trans (gs_res (𝟙 Y') y (le_pull h j') hy.2 _)))).symm)
  exact (gs_res (𝟙 Y') y _ hm _).symm.trans ((congrArg (gs (𝟙 Y') y _) (s'.compat _ _)).trans
    ((gs_mul (𝟙 Y') y _ hm _ _).trans (congrArg₂ (· * ·) (g_pull h y _ _ hm.1 hm.2) (gs_res (𝟙 Y') y _ hm _))))

theorem gs_eq_of_sval (hL : L.IsLB) {φ' : K → (Y' ⟶ X)} (s : LB.Sec (LB.LinComb L φ ε))
    (s' : LB.Sec (LB.LinComb L φ' ε)) (r : Z ⟶ Y) (r' : Z ⟶ Y') (e : ∀ k, r ≫ φ k = r' ≫ φ' k) (z : Z)
    (h : ∀ J, Good L z J → sval s r z J = sval s' r' z J) (j : K → L.ι) (hj : r' z ∈ LB.wchart L φ' j) :
    gs r z (LB.wchart L φ j) (s.f j) = gs r' z (LB.wchart L φ' j) (s'.f j) := by
  obtain ⟨J, hJ⟩ := exists_good_pt hL z
  have hj₀ : r z ∈ LB.wchart L φ j := Set.mem_iInter.2 fun k =>
    (congrArg (fun p : Z ⟶ X => p z ∈ L.U (j k)) (e k)).mpr (Set.mem_iInter.1 hj k)
  refine (sec_trans s r z hj₀ (hJ.mem φ r)).trans (Eq.trans ?_ (sec_trans s' r' z hj (hJ.mem φ' r')).symm)
  refine congrArg₂ (· * ·) (congrArg Units.val (Finset.prod_congr rfl fun k _ => ?_)) (h J hJ)
  beta_reduce
  rw [e k]

end General

section Levels
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}

theorem exists_limit (hS : SecAlgSt) (hI : IsAdicComplete I R) (D : DegPre R) (k : ℕ) (α : D.X)
    (f : ∀ e, LB.Sec (LB.LinComb D.P.L (fun i => (D.prBe I e).left ≫ D.famφB α i) (DegPre.famε k)))
    (hf : ∀ e z J, Good D.P.L z J → sval (f (e + 1)) (thickMap R I e D.P.A) z J = sval (f e) (𝟙 _) z J) :
    ∃ s : LB.Sec (LB.LinComb D.P.L (D.famφB α) (DegPre.famε k)),
      ∀ e z J, Good D.P.L z J → sval s (D.prBe I e).left z J = sval (f e) (𝟙 _) z J := by
  choose f' hf' using fun e => exists_in (φ := D.famφB α) (fstG I e D.P.A).left (f e)
  obtain ⟨s', hs', -⟩ := hS R I hI D.P.A D.P.isAb.smooth
    (AbProj.isProjBy_of_isPullback D.P (IsPullback.id_horiz _)) _ (DVR.linComb_isLB _ D.P.isLB _ _) f'
    fun e z J hJ => by
      refine (hf' _ _ _ z _ (hJ.mem (fun _ : PUnit => (fstG I (e + 1) D.P.A).left) _)).trans
        (Eq.trans ?_ (hf' _ _ _ z _ (hJ.mem (fun _ : PUnit => (fstG I e D.P.A).left) _)).symm)
      have E : thickMap R I e D.P.A ≫ (fstG I (e + 1) D.P.A).left = 𝟙 _ ≫ (fstG I e D.P.A).left :=
        (thickMap_fst e).trans (Category.id_comp _).symm
      beta_reduce
      rw [E]
      exact gs_eq_of_sval D.P.isLB _ _ _ _ (fun i => (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ D.famφB α i) E).trans (Category.assoc _ _ _))) z (hf e z) _
        (pull_le _ _ (hJ.mem (fun _ : PUnit => (fstG I e D.P.A).left) _))
  obtain ⟨s₁, hs₁⟩ := exists_out (𝟙 _) s'
  obtain ⟨s, hs⟩ := exists_sec D.P.isLB (φ' := D.famφB α) (ε' := DegPre.famε k)
    (fun U _ h => by simp only [Category.id_comp]) s₁
  refine ⟨s, fun e z J hJ => (hs _ _ z J hJ).trans ((hs₁ _ _ z _ (hJ.mem _ _)).trans ?_)⟩
  have hN : Good (LB.LinComb D.P.L (D.famφB α) (DegPre.famε k)) z (fun ψ i => J (ψ ≫ D.famφB α i)) :=
    fun ψ => hJ.mem _ ψ
  refine Eq.trans ?_ ((hs' e z _ hN).trans
    ((hf' _ _ _ z _ (hN.mem (fun _ : PUnit => (fstG I e D.P.A).left) _)).trans ?_))
  · exact (sval_of s' _ z _ _ (fun _ => funext fun i => congrArg J (Category.assoc _ _ _))).symm
  · exact (sval_of (f e) _ z J _ (fun i => congrArg J (Category.assoc _ _ _).symm)).symm

variable {D : DegPre R} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem exists_expT (hS' : SecAlgSt) (hI : IsAdicComplete I R) (U : PreU I D A G) (k : ℕ) (σ : U.SecGT (𝟙_ _) k) :
    ∃ f, U.ExpT (𝟙_ _) k σ f := by
  have hB := D.P.isLB
  have hG := U.P.L.isLB
  have lam : (snd (𝟙_ _) G).left ≫ (λ_ G).inv.left = 𝟙 _ := by
    rw [← Over.comp_left, ← leftUnitor_hom, Iso.hom_inv_id, Over.id_left]
  have lam' : (λ_ G).inv.left ≫ (snd (𝟙_ _) G).left = 𝟙 _ := by
    rw [← Over.comp_left, ← leftUnitor_hom, Iso.inv_hom_id, Over.id_left]

  have lev : ∀ e : ℕ, ∃ τ : LB.Sec (LB.LinComb D.P.L (K := Fin 1) (fun _ => (U.gt e).pG.left) (fun _ => (k : ℤ))),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) JG J,
        Good U.P.L.L z JG → Good D.P.L z J →
        sval τ r z J = (gw (U.w e) r z (J (r ≫ (U.gt e).pG.left))
          (fun _ => JG (r ≫ (fstG I e G).left))).val ^ k *
          sval σ ((r ≫ (fstG I e G).left) ≫ (λ_ G).inv.left) z JG := fun e => by
    obtain ⟨s, hs⟩ := exists_pull (φ' := fun _ : Fin 1 => (fstG I e G).left)
      ((fstG I e G).left ≫ (λ_ G).inv.left)
      (fun _ => by rw [Category.assoc, lam', Category.comp_id]) σ
    obtain ⟨τ, hτ⟩ := exists_carry hG hB (U.w e) (U.w_gen e) k s
    refine ⟨τ, fun Z r z JG J hJG hJ => (hτ Z r z JG J hJG hJ).trans (congrArg _ ((hs Z r z JG hJG).trans ?_))⟩
    exact congrArg (fun p => sval σ p z JG) (Category.assoc _ _ _).symm
  choose τ hτ using lev
  have ex := fun e => existsUnique_level_expansion R I D e G (U.gt e) k (τ e)
  choose f hf hu using ex
  choose S hS hsum using hf

  have compat : ∀ α e z J, Good D.P.L z J →
      sval (f (e + 1) α) (thickMap R I e D.P.A) z J = sval (f e α) (𝟙 _) z J := by
    intro α e
    choose f' hf' using fun β => exists_pull
      (φ' := fun i => (D.prBe I e).left ≫ D.famφB β i) (thickMap R I e D.P.A)
      (fun i => ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ D.famφB β i) (thickMap_prBe e))).symm) (f (e + 1) β)
    have E : f' = f e := by
      refine hu e f' ⟨S (e + 1), fun β hβ => zero_of_sval hB fun y J hJ =>
        (hf' β _ _ y J hJ).trans (sval_zero (hS _ β hβ) _ hJ), fun z J hJ => ?_⟩
      obtain ⟨JG, hJG⟩ := exists_good_pt hG z
      have a := sum_of_id (hsum (e + 1)) (thickMap R I e G) z hJ
      have b : sval (τ e) (𝟙 (thickObj R I e G).left) z J =
          sval (τ (e + 1)) (thickMap R I e G) z J := by
        refine (hτ e _ _ z JG J hJG hJ).trans (Eq.trans ?_ (hτ (e + 1) _ _ z JG J hJG hJ).symm)
        have c := U.w_compat e _ (𝟙 _) z _ _ (hJ (U.gt e).pG.left) (hJG (fstG I e G).left)
        rw [Category.id_comp] at c
        rw [U.gt_q, thickMap_fst, c]
        simp only [Category.id_comp]
      refine b.trans (a.trans (Finset.sum_congr rfl fun β _ => congrArg₂ (· * ·) ?_ (congrArg Units.val ?_)))
      · exact (congrArg (fun p => sval (f (e + 1) β) p z J) (q_thickMap U e).symm).trans (hf' β _ _ z J hJ).symm
      · exact ((congrArg (fun p => val ((U.gt (e + 1)).t β) p z J) (Category.id_comp _).symm).trans
          (val_pull hJ _ _ _).symm).trans (val_corr hJ (U.gt_t e β) _)
    intro z J hJ
    rw [← E]
    exact ((hf' α _ _ z J hJ).trans (congrArg (fun p => sval (f (e + 1) α) p z J) (Category.id_comp _))).symm
  choose s hs using fun α => exists_limit hS' hI D k α (fun e => f e α) (compat α)
  choose F hF using fun α => exists_pull (snd (𝟙_ _) D.P.A).left (famφT_eq (𝟙_ _) α) (s α)
  refine ⟨F, fun e => ⟨S e, fun Z x rG rB hrG hrB _ z JG J hJG hJ => ?_⟩⟩
  have v : ∀ α, sval (F α) rB z J = sval (f e α) (x ≫ (U.gt e).q.left) z J := fun α => by
    refine (hF α _ _ z J hJ).trans ?_
    have a := sval_eq_of_id (hs α e) (x ≫ (U.gt e).q.left) z hJ
    refine Eq.trans (congrArg (fun p => sval (s α) p z J) (hrB.trans (Category.assoc _ _ _).symm)) (a.trans ?_)
    exact congrArg (fun p => sval (f e α) p z J) (Category.comp_id _)
  refine ⟨fun α hα => (v α).trans (sval_zero (hS e α hα) _ hJ), ?_⟩
  have r : rG = (x ≫ (fstG I e G).left) ≫ (λ_ G).inv.left := by
    rw [← hrG, Category.assoc, lam, Category.comp_id]
  rw [r]
  refine (hτ e _ x z JG J hJG hJ).symm.trans ((sum_of_id (hsum e) x z hJ).trans ?_)
  exact Finset.sum_congr rfl fun α _ => congrArg (· * _) (v α).symm

theorem expT_unique [IsNoetherianRing R] (hI : I ≤ Ideal.jacobson ⊥) (U : PreU I D A G) (k : ℕ)
    (σ : U.SecGT (𝟙_ _) k) (f f' : ∀ α, SecBT D (𝟙_ _) k α) (h : U.ExpT (𝟙_ _) k σ f) (h' : U.ExpT (𝟙_ _) k σ f') :
    f = f' := by
  have hd := ExpUniq.expT_diff h h'
  have := D.P.isAb.smooth
  have := D.P.isAb.geomConnected
  have lam : (snd (𝟙_ _) D.P.A).left ≫ (λ_ D.P.A).inv.left = 𝟙 _ := by
    rw [← Over.comp_left, ← leftUnitor_hom, Iso.hom_inv_id, Over.id_left]
  have lam' : (λ_ D.P.A).inv.left ≫ (snd (𝟙_ _) D.P.A).left = 𝟙 _ := by
    rw [← Over.comp_left, ← leftUnitor_hom, Iso.inv_hom_id, Over.id_left]
  refine funext fun α => ExpUniq.eq_of_diffSec (zero_of_sval D.P.isLB fun y J hJ => ?_)
  obtain ⟨s, hs⟩ := exists_pull (λ_ D.P.A).inv.left (fun _ => rfl) (ExpUniq.diffSec (f α) (f' α))
  have h₀ := (sec_eq_zero_and_hom_eq_of_thickenings R I hI D.P.A).1 _ (DVR.linComb_isLB _ D.P.isLB _ _) s
    fun e j => fn_ext fun z hz => by
      have hz' : (𝟙 (thickObj R I e D.P.A).left : _ ⟶ _) z ∈ (fstG I e D.P.A).left ⁻¹ᵁ _ := hz
      refine (gs_pull (𝟙 _) (fstG I e D.P.A).left z _ hz' _).trans (Eq.trans ?_ ((gs_eq (𝟙 _) z _ hz' _).trans
        ((congrArg _ (map_zero _)).trans (map_zero _))).symm)
      refine ExpUniq.gs_eq_zero_of_sval D.P.isLB s _ z (fun J hJ => (hs _ _ z J hJ).trans ?_) j hz'
      refine ExpUniq.sval_term_eq_zero hd (fun Z r z J hJ => by rw [ExpUniq.sval_diffSec _ _ _ hJ, sub_self]) α e _
        (pullback.snd D.P.A.hom (thick R I e)) ?_ z J hJ
      rw [Category.assoc _ _ (snd (𝟙_ _) D.P.A).left, lam', Category.comp_id, Category.id_comp]
      exact pullback.condition
  have E := (hs _ (snd (𝟙_ _) D.P.A).left y J hJ).symm.trans (sval_zero h₀ _ hJ)
  rwa [lam] at E

end Levels

theorem main : Laws → Laws2 → Ega → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I → I ≠ ⊤ → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (k : ℕ) (σ : U.SecGT (𝟙_ _) k), ∃! f : ∀ α, SecBT D (𝟙_ _) k α, U.ExpT (𝟙_ _) k σ f := by
  intro _ _ hE R _ _ _ I hR _ D A G _ _ U k σ
  have := hR.1
  have := hR.2.2.2
  exact existsUnique_of_exists_of_unique (exists_expT hE.2.2.1 hR.2.2.2 U k σ)
    (expT_unique (IsAdicComplete.le_jacobson_bot I) U k σ)

end GlobalTheory.CompleteBaseExpansion
end
