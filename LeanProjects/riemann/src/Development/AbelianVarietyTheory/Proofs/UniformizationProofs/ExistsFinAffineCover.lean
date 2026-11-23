import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CechHOneVanishesOnOpenOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKerIffMinors
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfMemChart
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw GlobalTheory.PrimNorm
noncomputable section
namespace GlobalTheory.PrimVan

variable {X Y Y' : Scheme.{0}}

theorem gm_tw_one (A B : LB Y) (y : Y) (p q : A.ι × B.ι) (hp : y ∈ A.U p.1 ⊓ B.U p.2)
    (hq : y ∈ A.U q.1 ⊓ B.U q.2) :
    gm (𝟙 Y) y (A.U p.1 ⊓ B.U p.2 ⊓ (A.U q.1 ⊓ B.U q.2)) ((tw A B 1).g p q) =
      gm (𝟙 Y) y _ (A.g p.1 q.1) * gm (𝟙 Y) y _ (B.g p.2 q.2) := by
  refine (gm_div (pw B (-1)) A (𝟙 Y) y p q ⟨hp, hq⟩).trans ?_
  congr 1
  change (gm (𝟙 Y) y (B.U p.2 ⊓ B.U q.2) (B.g p.2 q.2 ^ (-1 : ℤ)))⁻¹ = _
  rw [zpow_neg_one, map_inv, inv_inv]

def chartTw (M : LB X) (p q : Y ⟶ X) :
    ChartPull (tw (M.pull p) (M.pull q) 1) (LB.LinComb M (K := Fin 2) ![p, q] ![1, 1]) (𝟙 Y) :=
  have le : ∀ a : (M.pull p).ι × (M.pull q).ι, (M.pull p).U a.1 ⊓ (M.pull q).U a.2 ≤
      LB.wchart M (K := Fin 2) ![p, q] ![a.1 PUnit.unit, a.2 PUnit.unit] := fun a y hy =>
    Set.mem_iInter.2 fun k => by
      fin_cases k
      exacts [mem_pull.1 hy.1, mem_pull.1 hy.2]
  { idx := fun a => ![a.1 PUnit.unit, a.2 PUnit.unit]
    le := le
    g := fun y a b ha hb => by
      refine (gm_tw_one (M.pull p) (M.pull q) y a b ha hb).trans (Eq.trans ?_
        (gm_linComb M _ _ (𝟙 Y) y _ _ (le a ha) (le b hb)).symm)
      rw [gm_pull_g M p (𝟙 Y) y _ _ ha.1 hb.1, gm_pull_g M q (𝟙 Y) y _ _ ha.2 hb.2, Fin.prod_univ_two]
      exact congrArg₂ (· * ·) (zpow_one _).symm (zpow_one _).symm }

def chartTwTriv (N : LB Y) (q : Y ⟶ Y') :
    ChartPull (tw N ((Inh.trivLB Y').pull q) 1) N (𝟙 Y) where
  idx a := a.1
  le _ _ hy := hy.1
  g y a b ha hb := by
    refine (gm_tw_one N ((Inh.trivLB Y').pull q) y a b ha hb).trans ?_
    rw [Inh.linComb_triv_g, map_one, _root_.mul_one]

def chartInv (M : LB X) :
    ChartPull (pw M (-1)) (LB.LinComb M (K := PUnit) (fun _ => 𝟙 X) fun _ => -1) (𝟙 X) :=
  have le : ∀ i : M.ι, M.U i ≤ LB.wchart M (K := PUnit) (fun _ => 𝟙 X) fun _ => i := fun _ _ hy =>
    Set.mem_iInter.2 fun _ => hy
  { idx := fun i _ => i
    le := le
    g := fun y i j hi hj => by
      refine Eq.trans ?_ (gm_linComb M _ _ (𝟙 X) y _ _ (le i hi) (le j hj)).symm
      rw [Fintype.prod_unique, Category.id_comp]
      exact map_zpow _ _ _ }

theorem nontrivial_sec_of_lbIso {L M : LB X} (hL : L.IsLB) (hM : M.IsLB) (h : LBIso L M)
    (hn : Nontrivial (LB.Sec L)) : Nontrivial (LB.Sec M) := by
  obtain ⟨w, hw⟩ := h
  exact (((SecOn.topEquiv L).symm ≪≫ₗ SecOn.congr hL hM w hw ⊤) ≪≫ₗ
    SecOn.topEquiv M).injective.nontrivial

theorem nontrivial_sec_pull [IsIntegral X] (M : LB X) (e : X ⟶ X) [IsIso e]
    (hn : Nontrivial (LB.Sec M)) : Nontrivial (LB.Sec (M.pull e)) := by
  rw [TrivLocus.nontrivial_sec_iff] at hn ⊢
  obtain ⟨σ, i, hi⟩ := hn
  obtain ⟨x, hx⟩ := TrivLocus.nonempty_of_ne_zero hi
  obtain ⟨y, rfl⟩ := e.homeomorph.surjective x
  have hy : y ∈ (M.pull e).U fun _ => i := mem_pull.2 hx
  refine ⟨SecOn.topEquiv _ (SecOn.pullLE M e ⊤ ⊤ le_top (GlobalTheory.LB.ofSec σ ⊤)), fun _ => i, ?_⟩
  refine (SecOn.topEquiv_f _ _).trans_ne ?_
  refine TrivLocus.rs_ne_zero _ ⟨y, hy⟩ ?_
  refine (SecOn.coord_pullLE e le_top (GlobalTheory.LB.ofSec σ ⊤) fun _ => i).trans_ne ?_
  refine TrivLocus.rs_ne_zero (U := e ⁻¹ᵁ (⊤ ⊓ M.U i)) (V := ⊤ ⊓ (M.pull e).U fun _ => i)
    (fun _ hz => ⟨trivial, mem_pull.1 hz.2⟩) ⟨y, trivial, hy⟩ ?_
  refine (map_ne_zero_iff _ (ConcreteCategory.bijective_of_isIso (e.app _)).1).2 ?_
  exact TrivLocus.rs_ne_zero (U := M.U i) (V := ⊤ ⊓ M.U i) inf_le_right ⟨_, trivial, hx⟩ hi

variable {K : Type} [Field K] {B : Over (Spec (CommRingCat.of K))} [GrpObj B] [IsCommMonObj B]
  {M : LB B.left}

theorem ptCls_mul (hM : M.IsLB) (hu : ∃ u : LB.Gen (abelian₂ B M), u.IsGen)
    {T : Over (Spec (CommRingCat.of K))} (x y : T ⟶ B) :
    ptCls M T (x * y) = ptCls M T x * ptCls M T y ∧ ptCls M T 1 = 1 := by
  have h1 : ptCls M T 1 = 1 := by
    obtain ⟨i, hi⟩ := exists_chart hM (η[B].left (IsLocalRing.closedPoint K))
    have := (hasGen_iff hM (K := PUnit) (fun _ => (1 : T ⟶ B).left) fun _ => 1).1
      (AbSquare.exists_gen_of_mem_chart hM _ _ (fun _ => i) fun _ z => by
        change η[B].left ((toUnit T).left z) ∈ _
        have : (toUnit T).left z = IsLocalRing.closedPoint K :=
          Subsingleton.elim (α := PrimeSpectrum K) _ _
        rw [this]; exact hi)
    rwa [Fintype.prod_unique, zpow_one] at this
  refine ⟨?_, h1⟩
  have h := (hasGen_iff hM _ _).1 (MulPull.HasGen.pull hu (lift x y).left)
  have h' := (prod_square (lift x y) (fst B B) (snd B B) (cls M)).symm.trans h
  rw [lift_fst, lift_snd] at h'
  change ptCls M T (x * y) * (ptCls M T x)⁻¹ * (ptCls M T y)⁻¹ * ptCls M T 1 = 1 at h'
  rw [h1, _root_.mul_one, mul_inv_eq_one, mul_inv_eq_iff_eq_mul, _root_.mul_comm (ptCls M T y)] at h'
  exact h'

theorem lbIso_pull_mul (hM : M.IsLB) (hu : ∃ u : LB.Gen (abelian₂ B M), u.IsGen) :
    LBIso (M.pull μ[B].left) (tw (M.pull (fst B B).left) (M.pull (snd B B).left) 1) := by
  refine LBIso.chartPull (chartPullId _) (chartTw M _ _) ((lbIso_iff hM _ _ _ _).2 ?_)
  have h := (ptCls_mul hM hu (fst B B) (snd B B)).1
  have e : fst B B * snd B B = μ[B] := by rw [Hom.mul_def, lift_fst_snd, Category.id_comp]
  rw [e] at h
  rw [Fintype.prod_unique, Fin.prod_univ_two]
  exact (zpow_one _).trans (h.trans (congrArg₂ (· * ·) (zpow_one _).symm (zpow_one _).symm))

theorem lbIso_pull_inv (hM : M.IsLB) (hu : ∃ u : LB.Gen (abelian₂ B M), u.IsGen) :
    LBIso (M.pull (𝟙 B : B ⟶ B)⁻¹.left) (pw M (-1)) := by
  refine LBIso.chartPull (chartPullId _) (chartInv M) ((lbIso_iff hM _ _ _ _).2 ?_)
  obtain ⟨h, h1⟩ := ptCls_mul hM hu (𝟙 B : B ⟶ B)⁻¹ (𝟙 B)
  rw [inv_mul_cancel, h1] at h
  rw [Fintype.prod_unique, Fintype.prod_unique, zpow_one, zpow_neg_one]
  exact eq_inv_of_mul_eq_one_left h.symm

omit [IsCommMonObj B] in

theorem isIntegral_left (hB : IsAbelianScheme B) : IsIntegral B.left :=
  have := forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ B.hom hB.smooth
    hB.geomConnected
  GeometricallyIntegral.geometrically_isIntegral (f := B.hom) _ _ _ (IsPullback.of_id_fst (f := B.hom))

theorem subsingleton_sec (hB : IsAbelianScheme B) (hM : M.IsLB) (hu : ∃ u : LB.Gen (abelian₂ B M), u.IsGen)
    (hn : ¬ Triv M) : Subsingleton (LB.Sec M) := by
  have := isIntegral_left hB
  have := hB.proper
  refine not_nontrivial_iff_subsingleton.1 fun h => hn ?_
  have hi : IsIso (𝟙 B : B ⟶ B)⁻¹ := by
    have e : (𝟙 B : B ⟶ B)⁻¹ ≫ (𝟙 B : B ⟶ B)⁻¹ = 𝟙 B := by
      rw [GrpObj.comp_inv, Category.comp_id, inv_inv]
    exact ⟨_, e, e⟩
  have : IsIso (𝟙 B : B ⟶ B)⁻¹.left := inferInstanceAs (IsIso ((Over.forget _).map (𝟙 B : B ⟶ B)⁻¹))
  exact (TrivLocus.triv_iff (isField_of_universallyClosed K B.hom) M hM.cover).2
    ⟨h, nontrivial_sec_of_lbIso (LB.isLB_pull hM _) (isLB_pw hM _) (lbIso_pull_inv hM hu)
      (nontrivial_sec_pull M _ h)⟩

def homologyZeroEquiv {R : Type} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R)) (N : LB X) {κ : Type}
    [LinearOrder κ] {D : κ → X.Opens} (hc : ⨆ i, D i = ⊤) :
    (cechLB f N D).homology 0 ≃ₗ[R] SecOnR f N ⊤ :=
  (cechHomologyZeroIso (secCube f N D)).toLinearEquiv.trans
    ((LinearEquiv.ofEq (LinearMap.ker (GlobalTheory.Cube.d (secCube f N D) (0 + 1)))
      (LinearMap.ker ((cechLB f N D).d 0 1).hom) (by rw [cechLB_d f N D 0]; rfl)).trans
      (CechOne.kerEquiv N f (fun _ => le_top) hc.ge).symm)

theorem exists_fin_affine_cover (X : Scheme.{0}) [CompactSpace X] :
    ∃ (n : ℕ) (D : Fin n → X.Opens), (∀ i, IsAffineOpen (D i)) ∧ ⨆ i, D i = ⊤ := by
  obtain ⟨s, hs, e⟩ := (isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens
    (U := (Set.univ : Set X))).1 ⟨isCompact_univ, isOpen_univ⟩
  obtain ⟨n, ⟨φ⟩⟩ := Finite.exists_equiv_fin (α := s) (h := hs)
  refine ⟨n, fun i => (φ.symm i).1.1, fun i => (φ.symm i).1.2, top_unique fun x _ => ?_⟩
  obtain ⟨U, hU, hx⟩ := Set.mem_iUnion₂.1 (e.le (Set.mem_univ x))
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨φ ⟨U, hU⟩, show x ∈ (φ.symm (φ ⟨U, hU⟩)).1.1 by
    rw [Equiv.symm_apply_apply]; exact hx⟩

theorem eq_zero_of_conv (h o : ℕ → ℕ) (h0 : h 0 = 0) (o0 : o 0 ≠ 0)
    (e : ∀ n, ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, h x.1 * o x.2 = ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, h x.1 * h x.2)
    (n : ℕ) : h n = 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hr : ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, h x.1 * h x.2 = 0 := Finset.sum_eq_zero fun x hx => by
      have hx := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
      rcases Nat.eq_zero_or_pos x.2 with h2 | h2
      · rw [h2, h0, mul_zero]
      · rw [ih x.1 (by omega), zero_mul]
    have := Finset.sum_eq_zero_iff.1 ((e n).trans hr) (n, 0) (by simp)
    exact (mul_eq_zero.1 this).resolve_right o0

omit [IsCommMonObj B] in

theorem isPullback_mul_snd : IsPullback μ[B].left (snd B B).left B.hom B.hom := by
  have e : fst B B * snd B B = μ[B] := by rw [Hom.mul_def, lift_fst_snd, Category.id_comp]
  let α : B ⊗ B ≅ B ⊗ B :=
    { hom := lift (fst B B * snd B B) (snd B B)
      inv := lift (fst B B * (snd B B)⁻¹) (snd B B)
      hom_inv_id := by
        ext1
        · simp [MonObj.comp_mul, GrpObj.comp_inv]
        · simp
      inv_hom_id := by
        ext1
        · simp [MonObj.comp_mul]
        · simp }
  refine (IsPullback.of_hasPullback B.hom B.hom).of_iso ((Over.forget _).mapIso α).symm (Iso.refl _)
    (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · rw [← e]
    exact congrArg (·.left) (show fst B B ≫ 𝟙 B = α.inv ≫ (fst B B * snd B B) by
      simp [α, MonObj.comp_mul])
  · exact congrArg (·.left) (show snd B B ≫ 𝟙 B = α.inv ≫ snd B B by simp [α])

theorem acyclic_of_kuenneth
    (kun : ∀ (K : Type) [Field K] (Y Y' Z : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of K)) (f' : Y' ⟶ Spec (CommRingCat.of K)) (p₁ : Z ⟶ Y) (p₂ : Z ⟶ Y') (M : LB Y) (M' : LB Y'), IsPullback p₁ p₂ f f' → M.IsLB → M'.IsLB → IsSeparated f → IsSeparated f' → ∀ (κ₁ : Type) [LinearOrder κ₁] [Fintype κ₁] (U : κ₁ → Y.Opens) (κ₂ : Type) [LinearOrder κ₂] [Fintype κ₂] (W : κ₂ → Y'.Opens) (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → Z.Opens), (∀ i, IsAffineOpen (U i)) → ⨆ i, U i = ⊤ → (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = ⊤ → (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (∀ n, Module.Finite K ((cechLB f M U).homology n)) → (∀ n, Module.Finite K ((cechLB f' M' W).homology n)) → ∀ n, Module.finrank K ((cechLB (p₁ ≫ f) (tw (M.pull p₁) (M'.pull p₂) 1) D).homology n) = ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, Module.finrank K ((cechLB f M U).homology x.1) * Module.finrank K ((cechLB f' M' W).homology x.2))
    (hB : IsAbelianScheme B) (hM : M.IsLB)
    (hadd : LBIso (M.pull μ[B].left) (tw (M.pull (fst B B).left) (M.pull (snd B B).left) 1))
    (hs : Subsingleton (LB.Sec M)) {κ : Type} [LinearOrder κ] [Fintype κ] {D : κ → B.left.Opens}
    (hD : ∀ i, IsAffineOpen (D i)) (hc : ⨆ i, D i = ⊤)
    (hfM : ∀ n, Module.Finite K ((cechLB B.hom M D).homology n))
    (hfO : ∀ n, Module.Finite K ((cechLB B.hom (Inh.trivLB _) D).homology n)) :
    (cechLB B.hom M D).Acyclic := by
  have := isIntegral_left hB
  have := hB.proper
  have hO := Inh.trivLB_isLB B.left
  have : CompactSpace B.left := QuasiCompact.compactSpace_of_compactSpace B.hom
  have : CompactSpace (B ⊗ B).left :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst B.hom B.hom)
  obtain ⟨m, E, hE, hEc⟩ := exists_fin_affine_cover (B ⊗ B).left
  have k₁ := kun K _ _ _ _ _ _ _ M _ isPullback_mul_snd hM hO inferInstance inferInstance
    κ D κ D _ E hD hc hD hc hE hEc hfM hfO
  have k₂ := kun K _ _ (B ⊗ B).left _ _ (fst B B).left (snd B B).left M M
    (IsPullback.of_hasPullback B.hom B.hom) hM hM inferInstance inferInstance
    κ D κ D _ E hD hc hD hc hE hEc hfM hfM
  have l₁ := isLB_tw (LB.isLB_pull hM μ[B].left) (LB.isLB_pull hO (snd B B).left) 1
  have l₂ := isLB_tw (LB.isLB_pull hM (fst B B).left) (LB.isLB_pull hM (snd B B).left) 1
  obtain ⟨w, hw⟩ := LBIso.chartPull (chartTwTriv _ (snd B B).left) (chartPullId _) hadd
  rw [Over.w μ[B], ← Over.w (fst B B)] at k₁
  have key := eq_zero_of_conv (fun n => Module.finrank K ((cechLB B.hom M D).homology n))
    (fun n => Module.finrank K ((cechLB B.hom (Inh.trivLB _) D).homology n)) ?_ ?_ fun n =>
      (k₁ n).symm.trans (Eq.trans (LinearEquiv.finrank_eq (HomologicalComplex.homologyMapIso
        (cechLBCongr _ E l₁ l₂ w hw) n).toLinearEquiv) (k₂ n))
  · intro n
    have := hfM n
    rw [HomologicalComplex.exactAt_iff_isZero_homology, ModuleCat.isZero_iff_subsingleton]
    exact Module.finrank_zero_iff.1 (key n)
  · have : Subsingleton ((cechLB B.hom M D).homology 0) :=
      ((homologyZeroEquiv B.hom M hc).toEquiv.trans (SecOnR.topEquiv B.hom M).toEquiv).subsingleton
    exact Module.finrank_zero_of_subsingleton
  · have : Nontrivial (LB.Sec (Inh.trivLB B.left)) :=
      ((TrivLocus.triv_iff (isField_of_universallyClosed K B.hom) _ hO.cover).1 (triv_trivLB _)).1
    have : Nontrivial ((cechLB B.hom (Inh.trivLB _) D).homology 0) :=
      ((homologyZeroEquiv B.hom _ hc).toEquiv.trans (SecOnR.topEquiv B.hom _).toEquiv).nontrivial
    have := hfO 0
    exact Module.finrank_pos.ne'

end GlobalTheory.PrimVan
