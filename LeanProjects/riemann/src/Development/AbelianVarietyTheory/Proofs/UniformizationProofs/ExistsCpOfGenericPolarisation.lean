import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfLocalOnBase
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueGeneratorExtendDiscreteValuationRing
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubicalExtendsAndExtendGen
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RigidifiedIsoRespectsCubeAndSymmetry

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.SymExtend

theorem exists_normalised {X Y S : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} (p : Y ⟶ S) (e : S ⟶ Y) (he : e ≫ p = 𝟙 S)
    (h0 : ∀ (U : Type) [CommGroup U] (h : (S ⟶ X) → U), ∏ k, h (e ≫ φ k) ^ ε k = 1)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) :
    ∃ u : LB.Gen (LB.LinComb L φ ε), u.IsGen ∧
      ∀ (Z : Scheme.{0}) (b : Z ⟶ S) (z : Z) (J), Good L z J → val u (b ≫ e) z J = 1 := by
  obtain ⟨t', ht', hv⟩ := exists_gen hL (φ' := φ) (ε' := ε)
    (fun V _ k => by
      have q := h0 V (fun χ => k (p ≫ χ))
      refine Eq.trans (DVR.prod_sum₂ (K := K) (K' := K) (U := V) _
        (c := ∏ i, k (φ i) ^ ε i) rfl
        (DVR.prod_neg _ _ ((Finset.prod_congr rfl fun i _ => by
          show k ((p ≫ e) ≫ _) ^ _ = _
          rw [Category.assoc]).trans q))) ?_
      simp)
    (LB.mulGen L _ _ _ _ t (LB.invGen L _ _ (LB.pullGen L _ _ t (p ≫ e))))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _)))
  refine ⟨t', ht', fun Z b z J hJ => ?_⟩
  have : (b ≫ e) ≫ p ≫ e = b ≫ e := by
    rw [Category.assoc, ← Category.assoc e, he, Category.id_comp]
  rw [hv Z _ z J hJ, val_mul hJ, val_inv, val_pull hJ, this, mul_inv_cancel]

theorem prod_sym_unit {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] (U : Type) [CommGroup U]
    (h : (S ⟶ G.left) → U) :
    ∏ k : Fin 2, h (eSec G ≫ ![(ι[G]).left, 𝟙 G.left] k) ^ (![1, -1] : Fin 2 → ℤ) k = 1 :=
  (prod_sym (η[G]) h).trans (by
    have e : (η[G])⁻¹ = η[G] := (GrpObj.one_inv : η[G] ≫ ι[G] = η[G])
    rw [e, mul_inv_cancel])

theorem sym_comp {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] {f : S' ⟶ S} {F : G'.left ⟶ G.left} {hw : F ≫ G.hom = G'.hom ≫ f}
    (mul : ∀ (T : Over S') (x y : T ⟶ G'), toBase hw (x * y) = toBase hw x * toBase hw y) (k : Fin 2) :
    ![(ι[G']).left, 𝟙 G'.left] k ≫ F = F ≫ ![(ι[G]).left, 𝟙 G.left] k := by
  fin_cases k
  · have := inv_left_comp mul (𝟙 G')
    rw [Hom.inv_def, Category.id_comp] at this
    exact this.trans (congrArg (· ≫ _) (Category.id_comp F))
  · exact (Category.id_comp _).trans (Category.comp_id _).symm

theorem surjective_cube_of_generic (hG : GlobalFnsSt) {R : Type} [CommRing R] [IsDomain R]
    (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [Flat G.hom]
    {A : Over (Spec (CommRingCat.of (FractionRing R)))} [GrpObj A] (hA : IsAbelianScheme A)
    (gen : (Over.pullback (jK R)).obj G ≅ A) : Function.Surjective (G3 G).hom.appTop.hom := by
  have : IsDominant (jK R) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))).le.trans bot_le)⟩
  have := IsSchemeTheoreticallyDominant.of_isDominant (jK R)
  have hg : IsPullback (gen.inv.left ≫ pullback.fst G.hom (jK R)) A.hom G.hom (jK R) := by
    have : IsIso gen.inv.left := inferInstanceAs (IsIso ((Over.forget _).map gen.inv))
    have s : IsPullback gen.inv.left A.hom (pullback.snd G.hom (jK R)) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨(Over.w gen.inv).trans (Category.comp_id _).symm⟩
    simpa using s.paste_horiz (IsPullback.of_hasPullback G.hom (jK R))
  have s₁ : Function.Surjective G.hom.appTop.hom :=
    RigidIsoCube.surjective_appTop_of_baseChange hg (eSec G) (Over.w η[G]) (hG _ _ hA).2
  have : Flat (G ⊗ G).hom := by rw [Over.tensorObj_hom]; infer_instance
  have sj : Function.Surjective ((snd G (G ⊗ G)).left ≫ (snd G G).left ≫ G.hom).appTop.hom :=
    surj_comp (RigidIsoCube.surjective_snd_of_generic hG (jK R) G hA hg _)
      (surj_comp (RigidIsoCube.surjective_snd_of_generic hG (jK R) G hA hg _) s₁)
  rwa [Over.w, Over.w] at sj

theorem exists_sym (hG : GlobalFnsSt) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G]
    [IsCommMonObj G] [Smooth G.hom] [GeometricallyConnected G.hom] (gen : (Over.pullback (jK V)).obj G ≅ A.A)
    [IsMonHom gen.hom] (L : LB G.left) (hL : L.IsLB)
    (w : LB.Iso (A.L.pull gen.hom.left) (L.pull (pullback.fst G.hom (jK V)))) (hw : w.IsGen) :
    ∃ s : LB.Gen (LB.LinComb L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1]), s.IsGen ∧
      LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ s (eSec G)) (LB.oneGen L) := by
  have := A.isAb.comm
  let G' : Over (Spec (CommRingCat.of (FractionRing V))) := (Over.pullback (jK V)).obj G
  let j : pullback G.hom (jK V) ⟶ G.left := pullback.fst G.hom (jK V)
  obtain ⟨u, hu⟩ := exists_gen_neg_of_sym hG A.isAb A.isLB A.sym
  obtain ⟨a, ha, -⟩ := CubTransport.exists_pmaps ((isGen_iff _).1 (pullIso_isGen A.isLB gen.hom.left)) A.isLB
    (pull_isLB A.isLB _) gen.hom.left
    (sym_comp (f := 𝟙 _) (hw := by simp) (toBase_mul_of_isMonHom gen.hom _)) u hu
  obtain ⟨t₀, ht₀, -⟩ := exists_up ((isGen_iff _).1 hw) hL (pull_isLB A.isLB _) a ha
  obtain ⟨t₁, ht₁, -⟩ := exists_gen hL (φ' := fun k => j ≫ (![(ι[G]).left, 𝟙 G.left] : Fin 2 → _) k) (ε' := ![1, -1])
    (fun U _ h => Finset.prod_congr rfl fun k _ =>
      congrArg (fun q => h q ^ _) (sym_comp (toBase_mul_pullback G (jK V)) k)) t₀ ht₀
  have e₂ : eSec G' ≫ j = jK V ≫ eSec G := (cubeMapOf (isGrpPullback_pullback G (jK V))).e_comm
  obtain ⟨t, ht, hv⟩ := exists_normalised hL G'.hom (eSec G') (Over.w η[G']) (fun U _ h => by
    refine Eq.trans (Finset.prod_congr rfl fun k _ => ?_) (prod_sym_unit G U fun q => h (jK V ≫ q))
    exact congrArg (fun q => h q ^ _) ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e₂).trans
      (Category.assoc _ _ _)))) t₁ ht₁
  obtain ⟨ρ, hρ, hρv⟩ := exists_gen hL (φ' := fun k => eSec G ≫ (![(ι[G]).left, 𝟙 G.left] : Fin 2 → _) k)
    (ε' := ![1, -1]) (fun U _ h => (Fintype.prod_empty _).trans (prod_sym_unit G U h).symm)
    (LB.oneGen L) (LB.isGen_oneGen L)
  obtain ⟨s₀, ⟨hs₀, -⟩, -⟩ := GenExtend.existsUnique_gen_extend V (FractionRing V) G.left G.left G.hom (eSec G)
    inferInstance (forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ inferInstance inferInstance)
    (Over.w η[G]) (eSec G') e₂ L hL (Fin 2) _ _ t ρ ht hρ (corr_of_val hL fun y J hJ =>
      ((val_pull hJ t _ _).trans (hv _ _ y J hJ)).trans
        ((val_pull hJ ρ _ _).trans ((hρv _ _ y J hJ).trans (val_one _))).symm)
  obtain ⟨s, hs, hsv⟩ := exists_normalised hL G.hom (eSec G) (Over.w η[G]) (prod_sym_unit G) s₀ hs₀
  exact ⟨s, hs, corr_of_val hL fun y J hJ =>
    ((val_pull hJ s _ _).trans (hsv _ _ y J hJ)).trans (val_one _).symm⟩

end GlobalTheory.SymExtend

namespace GlobalTheory

theorem exists_cp_of_generic_polarisation : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDVR V → ∀ (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (gen : (Over.pullback (jK V)).obj G ≅ A.A), IsMonHom gen.hom → ∀ (LG : RigLB G) (c : CubicalStr G LG) (w : LB.Iso (A.L.pull gen.hom.left) (LG.L.pull (pullback.fst G.hom (jK V)))), w.IsGen → ∃ P : CP G, P.L = LG ∧ HEq P.c c := by
  intro hL V _ _ _ hV A G _ _ hG gen hgen LG c w hw
  have := hV.1
  have := hG.smooth
  have := hG.geomConnected
  obtain ⟨s, hs, hr⟩ := SymExtend.exists_sym hL.globalFns V A G gen LG.L LG.isLB w hw
  exact ⟨CP.ofSurjective (SymExtend.surjective_cube_of_generic hL.globalFns G A.isAb gen) LG c s hs hr, rfl, HEq.rfl⟩

end GlobalTheory
