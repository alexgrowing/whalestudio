import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFiniteCubeInduction
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCharacterGroupIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationPolarisedAbelianSchemesIsoStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AbelianPartIsoIsMonHomAndRigidified
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCAndCoordCorrespondStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespondStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IdentificationLinear

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UnifUniq

theorem exists_cast {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ φ' : K → (Y ⟶ X)} {ε : K → ℤ}
    (h : φ' = φ) (t : LB.Gen (LB.LinComb L φ ε)) : ∃ b : LB.Gen (LB.LinComb L φ' ε),
      (∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (p : K → L.ι),
        gm r z (LB.wchart L φ' p) (b.s p) = gm r z (LB.wchart L φ p) (t.s p)) ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), val b r z J = val t r z J := by
  subst h
  exact ⟨t, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩

theorem exists_transport {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F F' : X' ⟶ X} (h : F' = F)
    (P : ∀ F : X' ⟶ X, LB.Iso L' (L.pull F) → Prop) (w : LB.Iso L' (L.pull F)) (hw : P F w) : ∃ w', P F' w' := by
  subst h
  exact ⟨w, hw⟩

variable {R : Type} [CommRing R] [IsDomain R]

theorem exists_section (W : (Spec (CommRingCat.of R)).Opens) (hW : genericPoint (Spec (CommRingCat.of R)) ∈ W) :
    ∃ r : (TK R).left ⟶ (jK R ⁻¹ᵁ W).toScheme, r ≫ (jK R ⁻¹ᵁ W).ι = 𝟙 _ :=
  ⟨IsOpenImmersion.lift (jK R ⁻¹ᵁ W).ι (𝟙 _) (by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hy : jK R y = genericPoint (Spec (CommRingCat.of R)) := by
      rw [genericPoint_eq_bot_of_affine]
      apply PrimeSpectrum.ext
      show Ideal.comap (algebraMap R (FractionRing R)) (PrimeSpectrum.asIdeal y) = ⊥
      rw [@Ideal.eq_bot_of_prime _ _ (PrimeSpectrum.asIdeal y) (PrimeSpectrum.isPrime y)]
      exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R (FractionRing R))
    show jK R y ∈ W
    rw [hy]; exact hW), IsOpenImmersion.lift_fac _ _ _⟩

theorem exists_isPullDeg_id (D D' : DegPre R) (W : (Spec (CommRingCat.of R)).Opens)
    (hW : genericPoint (Spec (CommRingCat.of R)) ∈ W) (ψW : PsiOn D W)
    (e : D'.P.A ≅ (Over.pullback (specOf (RingHom.id R))).obj D.P.A) (he : IsMonHom e.hom)
    (w : LB.Iso D'.P.L (D.P.L.pull (e.hom.left ≫ pullback.fst D.P.A.hom (specOf (RingHom.id R))))) (hw : w.IsGen)
    (hE : eSec D'.P.A ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf (RingHom.id R)) = eSec D.P.A)
    (hr : PMaps w (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => eSec D.P.A) (fun _ => 1) D'.rig D.rig (𝟙 _))
    (xe : D'.X ≃+ D.X)
    (hc : ∀ x, (D'.c x).left ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf (RingHom.id R)) = (D.c (xe x)).left)
    (hψ : ∀ x, PMaps w (K := PUnit) (fun _ => D'.xK x) (fun _ => D.xK (xe x)) (fun _ => -1) (D'.psi x)
      (D.psi (xe x)) (𝟙 _)) :
    ∃ hD : IsPullDeg (RingHom.id R) D D', hD.e = e ∧ HEq hD.w w ∧ hD.xe = xe := by
  have hs := specOf_id R
  obtain ⟨r, hr₀⟩ := exists_section W hW
  have hE' : eSec D'.P.A ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf (RingHom.id R)) =
      specOf (RingHom.id R) ≫ eSec D.P.A := by
    rw [hE, hs]; exact (Category.id_comp _).symm
  have hx : ∀ x, D'.xK x ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf (RingHom.id R)) = D.xK (xe x) := fun x => by
    show (jK R ≫ (D'.c x).left) ≫ _ = jK R ≫ (D.c (xe x)).left
    rw [Category.assoc, hc]
  refine ⟨⟨e, he, w, hw, hE', ?_, xe, fun x => ?_, W, ψW, r ≫ (jK R ∣_ W), ?_, fun x => ?_⟩, rfl, HEq.rfl, rfl⟩
  · refine (maps_iff w _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf (RingHom.id R)) _
      (rigPull_le (G' := D'.P.A) (G := D.P.A) _ (specOf (RingHom.id R)) hE' D.P.L) (fun _ => rfl)).2 ?_
    have : ∀ q : (𝟙_ (Over (Spec (CommRingCat.of R)))).left ⟶ (𝟙_ (Over (Spec (CommRingCat.of R)))).left, q = 𝟙 _ →
        PMaps w (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => eSec D.P.A) (fun _ => 1) D'.rig D.rig q := by
      rintro _ rfl; exact hr
    exact this _ hs
  · rw [hc]
    exact ((congrArg (· ≫ (D.c (xe x)).left) hs).trans (Category.id_comp _)).symm
  · rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hr₀, hs]
    exact (Category.id_comp _).trans (Category.comp_id _).symm
  · obtain ⟨b, hb, vb⟩ := exists_cast (K := PUnit) (ε := fun _ => -1)
      (φ' := fun _ => D'.xK x ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf (RingHom.id R)))
      (φ := fun _ => D.xK (xe x)) (funext fun _ => hx x) (D.psi (xe x))
    refine ⟨b, fun jN jL => ?_, corr_of_val D.P.isLB fun y J hJ => ?_⟩
    · refine unit_ext fun y hy => ?_
      have v := hψ x _ (𝟙 _) y jN (fun _ => jL)
        (fun k => Set.mem_iInter.1 (GeneratorPullback.mapsAt_le_b _ _ _ _ jN jL hy) k)
        (fun k => Set.mem_iInter.1 (GeneratorPullback.mapsAt_le_a _ _ _ _ jN jL hy) k)
      rw [Category.id_comp, Fintype.prod_unique] at v
      refine (gm_res _ y _ hy _).trans ((hb _ _ y jN).trans (v.trans (Eq.symm ((map_mul _ _ _).trans
        (congrArg₂ (· * ·) ?_ (gm_res _ y _ hy _))))))
      exact (map_zpow _ _ _).trans (congrArg (· ^ (-1 : ℤ)) (gm_pull (𝟙 _) _ y _ hy _))
    · have v := val_corr hJ (ψW.psi_eq (xe x)) r
      rw [val_pull hJ, val_pull hJ, hr₀] at v
      rw [vb, val_pull hJ, Category.id_comp, v]

end GlobalTheory.UnifUniq

namespace GlobalTheory

set_option maxHeartbeats 800000 in

theorem unifUniq : GlobalFnsSt → SecBaseChangeSt → AmpleSt → UnifUniqSt := by
  intro hG hS hA R _ _ _ I hR D D' A A' G _ _ hsa U U' wL hwg hwm
  have hs := specOf_id R
  have he₀ : eSec G ≫ 𝟙 G.left = 𝟙 _ ≫ eSec G := (Category.comp_id _).trans (Category.id_comp _).symm
  have g₁ := (isGen_iff _).2 (isoPullId_pgen hwg (rfl : 𝟙 G.left = 𝟙 _))
  have m₁ := isoPullId_maps hwm (rfl : 𝟙 G.left = 𝟙 _) rfl he₀
  obtain ⟨Φ, w, hΦ⟩ := GlobalTheory.T.uniformisation_polarised_abelianSchemes_iso hG hS hA R I hR D D' A A' G hsa U.toUnifPre U'.toUnifPre _ he₀ g₁ m₁
  have hhom := abelianPartIso_isMonHom_and_rigidified R I hR D D' A A' G hsa U.toUnifPre U'.toUnifPre _ he₀ g₁ m₁
    Φ w hΦ
  obtain ⟨xe, hxe⟩ := unifPre_characterGroup_iso R I hR D D' A A' G hsa U.toUnifPre U'.toUnifPre
  have hc := GlobalTheory.T.unifPre_c_and_coord_correspond_alt hG R I hR D D' A A' G hsa U.toUnifPre U'.toUnifPre Φ w hΦ.1 hhom.1
    (fun e => (hΦ.2 e).1) xe hxe
  have hψ := GlobalTheory.T.uniformisation_trivialisations_correspond hG hS R I hR D D' A A' G hsa U.toUnifPre U'.toUnifPre _ he₀ g₁ m₁ (U.expand 1 le_rfl)
    (U'.expand 1 le_rfl) Φ w hΦ hhom xe hc
  have hlin := UnifLinear.identification_linear R I hR D D' A A' G hsa U.toUnifPre U'.toUnifPre Φ
    (fun e => (hΦ.2 e).1) xe hxe
  obtain ⟨hmon, hrig⟩ := hhom
  obtain ⟨hc₁, hc₂⟩ := hc
  have gp : IsGrpPullback D'.toPre.P.A D.toPre.P.A (specOf (RingHom.id R)) Φ.hom.left :=
    (isGrpPullback_of_iso Φ).congr hs.symm rfl
  obtain ⟨e, me, hF⟩ := grpPullback_iso gp (isGrpPullback_pullback D.toPre.P.A (specOf (RingHom.id R)))
  have hE : eSec D'.toPre.P.A ≫ Φ.hom.left = eSec D.toPre.P.A := by
    rw [eSec, eSec, ← Over.comp_left, IsMonHom.one_hom]
  have hc₁' : ∀ x, (D'.toPre.c x).left ≫ Φ.hom.left = (D.toPre.c (xe x)).left := fun x => by
    rw [← Over.comp_left, hc₁]
  have hact : ∀ (a' : D'.toPre.P.A ⟶ D'.toPre.P.A) (a : D.toPre.P.A ⟶ D.toPre.P.A), a' ≫ Φ.hom = Φ.hom ≫ a →
      a' ≫ e.hom = e.hom ≫ (Over.pullback (specOf (RingHom.id R))).map a := fun a' a h => by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · have a₂ : ((Over.pullback (specOf (RingHom.id R))).map a).left ≫
          pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R)) = pullback.fst _ _ ≫ a.left :=
        pullback.lift_fst _ _ _
      have h' := congrArg (fun q => q.left) h
      simp only [Over.comp_left] at h'
      rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc]
      refine (congrArg (a'.left ≫ ·) hF).trans (h'.trans (Eq.symm ?_))
      refine (congrArg (e.hom.left ≫ ·) a₂).trans ?_
      rw [← Category.assoc]
      exact congrArg (· ≫ a.left) hF
    · exact (Over.w (a' ≫ e.hom)).trans (Over.w (e.hom ≫ (Over.pullback (specOf (RingHom.id R))).map a)).symm
  have hlin' : ∀ (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] [Module O D'.toPre.X]
      (ιD : D.toPre.OAct O) (ιD' : D'.toPre.OAct O) (ιA : A.OAct O) (ιA' : A'.OAct O)
      (ιG : RingAct G O), U.OLinear O ιD ιA ιG → U'.OLinear O ιD' ιA' ιG →
      (∀ (a : O) (y : D'.toPre.X), xe (a • y) = a • xe y) ∧
      ∀ a, ιD'.onB.act a ≫ e.hom = e.hom ≫ (Over.pullback (specOf (RingHom.id R))).map (ιD.onB.act a) :=
    fun O _ _ _ _ ιD ιD' ιA ιA' ιG h h' =>
      ⟨(hlin O ιD ιD' ιA ιA' ιG h h').1, fun a => hact _ _ ((hlin O ιD ιD' ιA ιA' ιG h h').2 a)⟩
  obtain ⟨w', g', r', ψ', t', s'⟩ := UnifUniq.exists_transport hF (fun (F : D'.toPre.P.A.left ⟶ D.toPre.P.A.left)
    (w : LB.Iso D'.toPre.P.L (D.toPre.P.L.pull F)) => w.IsGen ∧
      PMaps w (K := PUnit) (fun _ => eSec D'.toPre.P.A) (fun _ => eSec D.toPre.P.A) (fun _ => 1)
        D'.toPre.rig D.toPre.rig (𝟙 _) ∧
      (∀ x, PMaps w (K := PUnit) (fun _ => D'.toPre.xK x) (fun _ => D.toPre.xK (xe x)) (fun _ => -1)
        (D'.toPre.psi x) (D.toPre.psi (xe x)) (𝟙 _)) ∧
      (∀ (n : ℕ) (x : D'.toPre.X), PMaps w (D'.toPre.Oφ (U'.gt n).pG x) (D.toPre.Oφ (U.gt n).pG (xe x)) Oinvε
        ((U'.gt n).t x) ((U.gt n).t (xe x)) (𝟙 _)) ∧
      ∀ (n : ℕ) (z : (thickObj R I n G).left) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι)
        (jL' : U'.LG.L.ι), (U.gt n).pG.left z ∈ D.toPre.P.L.U jM → (U'.gt n).pG.left z ∈ D'.toPre.P.L.U jM' →
        (fstG I n G).left z ∈ U.LG.L.U jL → (fstG I n G).left z ∈ U'.LG.L.U jL' →
        gw w (𝟙 _ ≫ (U'.gt n).pG.left) z jM jM' * gw (U'.w n) (𝟙 _) z jM' (fun _ => jL') =
          gw (U.w n) (𝟙 _) z jM (fun _ => jL) * gv wL (𝟙 _ ≫ (fstG I n G).left) z jL jL') w
    ⟨hΦ.1, hrig, hψ, fun n x => ((hc₂ n).2 x).2, fun n z jM jM' jL jL' h₁ h₂ h₃ h₄ =>
      ((hΦ.2 n).2 _ (𝟙 _) z jM jM' jL jL' h₁ h₂ h₃ h₄).trans
        (congrArg (_ * ·) (gw_isoPullId wL rfl _ z jL jL' h₃ h₄))⟩
  have hp : ∀ n : ℕ, (U'.gt n).pG.left ≫ e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R)) =
      (U.gt n).pG.left := fun n => (congrArg (_ ≫ ·) hF).trans (hΦ.2 n).1
  have hO : ∀ (n : ℕ) (x : D'.toPre.X) (k : Fin 4), D'.toPre.Oφ ((U'.gt n).pG) x k ≫ e.hom.left ≫
      pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R)) = 𝟙 _ ≫ D.toPre.Oφ ((U.gt n).pG) (xe x) k :=
    fun n x k => (congrArg (_ ≫ ·) hF).trans (((hc₂ n).2 x).1 k)
  obtain ⟨W, hW, ⟨ψW⟩⟩ := psiOnExists R I hR D
  obtain ⟨hD, e₁, e₂, e₃⟩ := UnifUniq.exists_isPullDeg_id D.toPre D'.toPre W hW ψW e me w' g'
    ((congrArg (_ ≫ ·) hF).trans hE) r' xe (fun x => (congrArg (_ ≫ ·) hF).trans (hc₁' x)) ψ'
  subst e₁ e₃
  obtain rfl := eq_of_heq e₂
  refine ⟨hD, fun n => ⟨hp n, fun x => ⟨hO n x, ?_⟩,
    fun jM jM' jL' jL => res_eq_of_gm fun y hy => ?_⟩, hlin'⟩
  · exact (maps_iff hD.w _ _ _ _ _ (𝟙 _) _ (GeneratorPullback.pullAlong_le D.toPre.P.L _ _ _ _ (hO n x))
      (fun _ => rfl)).2 (t' n x)
  · have H := s' n y (jM PUnit.unit) jM' jL jL' (mem_pull.1 hy.1.2.1) (mem_pull.1 hy.1.1.2.1) hy.2.1 hy.2.2
    exact (congrArg₂ (· * ·) (gm_pull (𝟙 _) _ y _ hy.1.1.1 _) rfl).trans
      (H.trans (congrArg₂ (· * ·) rfl (gm_pull (𝟙 _) _ y _ hy.2 _).symm))

end GlobalTheory
