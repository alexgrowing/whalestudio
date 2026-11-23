import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.InvariantVectorFieldsAlongGroupHom
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ConstThickeningFieldStructure
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueInvariantVectorFieldOfTangent
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLieBasisIffIsUnitDet
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KS.DlogPol

section Germs
variable {X Y Z : Scheme.{0}}

theorem gs_rsT (r : Z ⟶ Y) (z : Z) {O₀ O : Y.Opens} (h : O ≤ O₀) (hz : r z ∈ O) (s : Γ(Y, O₀)) :
    gs r z O (rsT s O) = gs r z O₀ s := by
  rw [rsT, dif_pos h]
  exact gs_res r z h hz s

theorem gs_pbT (r : Z ⟶ Y) (f : Y ⟶ X) (z : Z) {O₀ : X.Opens} {O : Y.Opens} (h : O ≤ f ⁻¹ᵁ O₀) (hz : r z ∈ O)
    (s : Γ(X, O₀)) : gs r z O (pbT f s O) = gs (r ≫ f) z O₀ s := by
  rw [pbT, dif_pos h]
  exact (gs_res r z h hz ((f.app O₀).hom s)).trans (gs_pull r f z O₀ (h hz) s)

theorem gs_one (r : Z ⟶ Y) (z : Z) (O : Y.Opens) (hz : r z ∈ O) : gs r z O 1 = 1 := by
  simp only [gs_eq r z O hz, map_one]

theorem gs_sub (r : Z ⟶ Y) (z : Z) (O : Y.Opens) (hz : r z ∈ O) (a b : Γ(Y, O)) :
    gs r z O (a - b) = gs r z O a - gs r z O b := by
  simp only [gs_eq r z O hz, map_sub]

theorem gs_constFn {R : Type} [CommRing R] (p : Y ⟶ Sp R) (r : Z ⟶ Y) (z : Z) (O : Y.Opens) (hz : r z ∈ O) (a : R) :
    gs r z O (constFn p O a) = gs (r ≫ p) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) :=
  (gs_res r z (show O ≤ p ⁻¹ᵁ ⊤ from fun _ _ => trivial) hz ((p.app ⊤).hom _)).trans (gs_pull r p z ⊤ trivial _)

theorem eps_sq {K : Type} [Field K] (p : X ⟶ Sp (DualNumber K)) (U : X.Opens) :
    constFn p U DualNumber.eps * constFn p U DualNumber.eps = 0 := by
  unfold constFn
  rw [← map_mul, ← map_mul, DualNumber.eps_mul_eps, map_zero, map_zero]

end Germs

theorem exists_gen {K : Type} [Field K] {X Y Y' : Scheme.{0}} (π : Y' ⟶ Sp (DualNumber K)) (τ ρ : Y' ⟶ Y)
    (hτ : ∀ (y : Y') (W : Y.Opens), τ y ∈ W → ρ y ∈ W) (m : Y ⟶ X) (L : LB X) (hL : L.IsLB)
    (k : C1 (fun i => m ⁻¹ᵁ L.U i))
    (hk : ∀ i j (y : Y'), m (τ y) ∈ L.U i → m (τ y) ∈ L.U j →
      gs (τ ≫ m) y _ (L.g i j).val = gs (ρ ≫ m) y _ (L.g i j).val *
        (1 + gs π y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))).inv.hom DualNumber.eps) *
          gs ρ y _ (k i j)))
    (hc : IsCob _ k) :
    ∃ t : LB.Gen (LB.LinComb L (K := Fin 2) (fun n => ![τ, ρ] n ≫ m) ![1, -1]), t.IsGen := by
  obtain ⟨b, hb⟩ := hc
  let φ : Fin 2 → (Y' ⟶ X) := fun n => ![τ, ρ] n ≫ m
  have h₀ : ∀ (J : Fin 2 → L.ι) (y : Y'), y ∈ LB.wchart L φ J → m (τ y) ∈ L.U (J 0) := fun J y hy =>
    Set.mem_iInter.1 hy 0
  have h₀' : ∀ (J : Fin 2 → L.ι) (y : Y'), y ∈ LB.wchart L φ J → m (ρ y) ∈ L.U (J 0) := fun J y hy =>
    hτ y (m ⁻¹ᵁ L.U (J 0)) (h₀ J y hy)
  have h₁ : ∀ (J : Fin 2 → L.ι) (y : Y'), y ∈ LB.wchart L φ J → m (ρ y) ∈ L.U (J 1) := fun J y hy =>
    Set.mem_iInter.1 hy 1
  have le : ∀ J : Fin 2 → L.ι, LB.wchart L φ J ≤ (ρ ≫ m) ⁻¹ᵁ (L.U (J 0) ⊓ L.U (J 1)) := fun J y hy =>
    ⟨h₀' J y hy, h₁ J y hy⟩
  let u : ∀ J : Fin 2 → L.ι, Γ(Y', LB.wchart L φ J)ˣ := fun J =>
    ⟨1 - constFn π _ DualNumber.eps * pbT ρ (b (J 0)) _, 1 + constFn π _ DualNumber.eps * pbT ρ (b (J 0)) _,
      by linear_combination (-(pbT ρ (b (J 0)) (LB.wchart L φ J)) ^ 2) * eps_sq π (LB.wchart L φ J),
      by linear_combination (-(pbT ρ (b (J 0)) (LB.wchart L φ J)) ^ 2) * eps_sq π (LB.wchart L φ J)⟩
  refine ⟨⟨fun J => res (le J) (pullU (ρ ≫ m) _ (L.g (J 0) (J 1))) * u J⟩, isGen_of_gm _ fun y J J' hJ hJ' => ?_⟩
  set e := gs π y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))).inv.hom DualNumber.eps) with he
  have ee : e * e = 0 := by
    rw [he, ← gs_mul π y ⊤ trivial, ← map_mul, DualNumber.eps_mul_eps, map_zero, gs_eq π y ⊤ trivial, map_zero, map_zero]
  have val : ∀ J : Fin 2 → L.ι, y ∈ LB.wchart L φ J →
      (gm (𝟙 Y') y (LB.wchart L φ J) (res (le J) (pullU (ρ ≫ m) _ (L.g (J 0) (J 1))) * u J)).val =
        (gm (ρ ≫ m) y _ (L.g (J 0) (J 1))).val * (1 - e * gs ρ y _ (b (J 0))) := fun J hJ => by
    rw [map_mul, Units.val_mul, gm_res (𝟙 Y') y (le J) hJ, gm_pull (𝟙 Y') (ρ ≫ m) y _ (le J hJ), Category.id_comp,
      ← gs_unit (𝟙 Y') y _ hJ]
    congr 1
    change gs (𝟙 Y') y _ (1 - constFn π _ DualNumber.eps * pbT ρ (b (J 0)) _) = _
    rw [gs_sub _ _ _ hJ, gs_one _ _ _ hJ, gs_mul _ _ _ hJ, gs_constFn _ _ _ _ hJ,
      gs_pbT (𝟙 Y') ρ y (O₀ := m ⁻¹ᵁ L.U (J 0)) (fun y hy => h₀' J y hy) hJ, Category.id_comp, Category.id_comp]
  have tr : trF φ ![1, -1] (𝟙 Y') y J J' =
      gm (τ ≫ m) y _ (L.g (J 0) (J' 0)) * (gm (ρ ≫ m) y _ (L.g (J 1) (J' 1)))⁻¹ := by
    rw [trF, Fin.prod_univ_two]
    simp only [Category.id_comp]
    simp [φ]
  have c₁ := gm_cocycle hL (ρ ≫ m) y (h₀' J y hJ) (h₀' J' y hJ') (h₁ J' y hJ')
  have c₂ := gm_cocycle hL (ρ ≫ m) y (h₀' J y hJ) (h₁ J y hJ) (h₁ J' y hJ')
  have k₁ := hk _ _ y (h₀ J y hJ) (h₀ J' y hJ')
  have m₀ : ρ y ∈ m ⁻¹ᵁ L.U (J 0) ⊓ m ⁻¹ᵁ L.U (J' 0) := ⟨h₀' J y hJ, h₀' J' y hJ'⟩
  rw [hb, gs_sub _ _ _ m₀, gs_rsT _ _ inf_le_right m₀, gs_rsT _ _ inf_le_left m₀,
    gs_unit (τ ≫ m) y (L.U (J 0) ⊓ L.U (J' 0)) ⟨h₀ J y hJ, h₀ J' y hJ'⟩, gs_unit (ρ ≫ m) y (L.U (J 0) ⊓ L.U (J' 0)) m₀, ← he] at k₁
  change gm (𝟙 Y') y (LB.wchart L φ J) _ = trF φ ![1, -1] (𝟙 Y') y J J' * gm (𝟙 Y') y (LB.wchart L φ J') _
  rw [tr, _root_.mul_assoc, mul_left_comm, eq_inv_mul_iff_mul_eq]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, val J hJ, val J' hJ', k₁]
  have d := congrArg Units.val (c₁.trans c₂.symm)
  rw [Units.val_mul, Units.val_mul] at d
  linear_combination (-(1 - e * gs ρ y _ (b (J 0)))) * d +
    ((gm (ρ ≫ m) y _ (L.g (J 0) (J' 0))).val * (gm (ρ ≫ m) y _ (L.g (J' 0) (J' 1))).val *
      (gs ρ y _ (b (J' 0)) - gs ρ y _ (b (J 0))) * gs ρ y _ (b (J' 0))) * ee

theorem isUnit_pbT {X Y : Scheme.{0}} (m : Y ⟶ X) (L : LB X) (i j : L.ι) :
    IsUnit (pbT m (L.g i j).val (m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U j)) := by
  rw [pbT, dif_pos (show m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U j ≤ m ⁻¹ᵁ (L.U i ⊓ L.U j) from fun _ h => h)]
  exact (L.g i j).isUnit.map _

theorem isCoc_dlog {X Y : Scheme.{0}} (m : Y ⟶ X) (L : LB X) (hL : L.IsLB)
    (d : ∀ O : Y.Opens, Γ(Y, O) → Γ(Y, O)) (hmul : ∀ W f f', d W (f * f') = f * d W f' + f' * d W f)
    (hres : ∀ W W' (f : Γ(Y, W)), W' ≤ W → d W' (rsT f W') = rsT (d W f) W')
    (φ : C1 (fun i => m ⁻¹ᵁ L.U i))
    (hφ : ∀ i j, pbT m (L.g i j).val (m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U j) * φ i j =
      d _ (pbT m (L.g i j).val (m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U j))) : IsCoc _ φ := by
  intro i j k
  set O : Y.Opens := m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U j ⊓ m ⁻¹ᵁ L.U k with hO
  let G : L.ι → L.ι → Γ(Y, O) := fun a b => rsT (pbT m (L.g a b).val (m ⁻¹ᵁ L.U a ⊓ m ⁻¹ᵁ L.U b)) O
  have hd : ∀ a b, O ≤ m ⁻¹ᵁ L.U a ⊓ m ⁻¹ᵁ L.U b → d O (G a b) = G a b * rsT (φ a b) O := fun a b h => by
    rw [hres _ _ _ h, ← hφ]
    simp only [G, rsT, dif_pos h, map_mul]
  have hg : ∀ a b, O ≤ m ⁻¹ᵁ L.U a ⊓ m ⁻¹ᵁ L.U b → ∀ y ∈ O,
      gs (𝟙 Y) y O (G a b) = (gm m y _ (L.g a b)).val := fun a b h y hy => by
    rw [gs_rsT _ _ h hy, gs_pbT (𝟙 Y) m y (O₀ := L.U a ⊓ L.U b) (O := m ⁻¹ᵁ L.U a ⊓ m ⁻¹ᵁ L.U b) (fun _ h => h) (h hy), Category.id_comp,
      gs_unit m y (L.U a ⊓ L.U b) (h hy)]
  have l₁ : O ≤ m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U j := inf_le_left
  have l₂ : O ≤ m ⁻¹ᵁ L.U j ⊓ m ⁻¹ᵁ L.U k := fun _ h => ⟨h.1.2, h.2⟩
  have l₃ : O ≤ m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U k := fun _ h => ⟨h.1.1, h.2⟩
  have co : G i j * G j k = G i k := fn_ext fun y hy => by
    rw [gs_mul _ _ _ hy, hg _ _ l₁ y hy, hg _ _ l₂ y hy, hg _ _ l₃ y hy, ← Units.val_mul,
      gm_cocycle hL m y hy.1.1 hy.1.2 hy.2]
  have un : IsUnit (G i k) := by
    simp only [G, rsT, dif_pos l₃]
    exact (isUnit_pbT m L i k).map _
  have e := hmul O (G i j) (G j k)
  rw [co, hd _ _ l₁, hd _ _ l₂, hd _ _ l₃] at e
  refine un.mul_left_cancel ?_
  change G i k * (rsT (φ i j) O + rsT (φ j k) O) = G i k * rsT (φ i k) O
  linear_combination (-1 : Γ(Y, O)) * e - (rsT (φ i j) O + rsT (φ j k) O) * co

theorem preimage_transl {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] (w : epsR K ⟶ A) (hw : IsTangent w)
    (W : A.left.Opens) :
    ((fst (epsR K) A ≫ w) * snd (epsR K) A).left ⁻¹ᵁ W = (snd (epsR K) A).left ⁻¹ᵁ W := by
  let z : 𝟙_ (Over (Sp K)) ⟶ epsR K := Over.homMk (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) (by
    change Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1)
  have hz : z ≫ w = η[A] := Over.OverMorphism.ext hw
  let j : A ⟶ epsR K ⊗ A := lift (toUnit A ≫ z) (𝟙 A)
  have j₁ : j ≫ snd (epsR K) A = 𝟙 A := lift_snd _ _
  have j₂ : j ≫ ((fst (epsR K) A ≫ w) * snd (epsR K) A) = 𝟙 A := by
    rw [MonObj.comp_mul, j₁, lift_fst_assoc, Category.assoc, hz, ← Hom.one_def, _root_.one_mul]
  have j₃ : j.left ≫ (fst (epsR K) A).left = A.hom ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom := by
    have := congrArg (fun q => q.left) (lift_fst (toUnit A ≫ z) (𝟙 A))
    refine this.trans ?_
    change (toUnit A).left ≫ _ = _
    congr 1
  have h := (GlobalTheory.ConstThickening.structure_dualNumber K A.left (epsR K ⊗ A).left A.hom (fst (epsR K) A).left (snd (epsR K) A).left j.left
    (IsPullback.of_hasPullback (epsR K).hom A.hom).flip (congrArg (fun q => q.left) j₁) j₃).1
    (((fst (epsR K) A ≫ w) * snd (epsR K) A).left ⁻¹ᵁ W)
  rw [← h, ← Scheme.Hom.comp_preimage j.left, ← Over.comp_left, j₂]
  rfl

theorem dlog_independent : ∀ (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)) (g : ℕ) (v : Fin g → (epsR K ⟶ P₀.A)) (dd : Fin g → ∀ O : P₀.A.left.Opens, Γ(P₀.A.left, O) → Γ(P₀.A.left, O)), IsLieBasis v → (∀ a, IsInvDer (v a) (dd a)) → ∀ (X : Scheme.{0}) (m : P₀.A.left ⟶ X) (L : LB X), L.IsLB → LBIso P₀.L (L.pull m) → (∃ φ, IsDlog m L dd φ) ∧ ∀ φ, IsDlog m L dd φ → (∀ a, IsCoc _ (φ a)) ∧ ∀ c, IsCob _ (lc P₀.A.hom c φ) → c = 0 := by
  intro K _ P g v dd hv hdd X m L hL ⟨u, hu⟩
  refine ⟨⟨fun a i j => ((isUnit_pbT m L i j).unit⁻¹ : _ˣ).val * dd a _ (pbT m (L.g i j).val _), fun a i j => ?_⟩,
    fun φ hφ => ⟨fun a => ?_, fun c hc => ?_⟩⟩
  · rw [← _root_.mul_assoc, IsUnit.mul_val_inv, _root_.one_mul]
  · obtain ⟨-, h₁, h₂, -⟩ := (GlobalTheory.KS.InvField.main K P.A (v a) (hv.1 a)).2 _ (hdd a)
    exact isCoc_dlog m L hL (dd a) h₁ h₂ (φ a) (hφ a)
  have := P.isAb.comm
  obtain ⟨a₁, a₂, a₃, -⟩ := GlobalTheory.LieComb.lieComb_algebra K P.A g v hv.1
  obtain ⟨w, hw, -⟩ := a₁ c
  have tw := a₂ c w hw
  obtain ⟨dw, hdw⟩ := (GlobalTheory.KS.InvField.main K P.A w tw).1
  have hsum : ∀ (W : P.A.left.Opens) (h : Γ(P.A.left, W)), dw W h = ∑ a, constFn P.A.hom _ (c a) * dd a W h :=
    GlobalTheory.KS.InvHom.invDer_along_hom K P.A P.A (𝟙 _) g v dd w dw c inferInstance hv.1 tw hdd hdw (by rwa [Category.comp_id])
  have pre := preimage_transl w tw
  set τ := ((fst (epsR K) P.A ≫ w) * snd (epsR K) P.A).left with hτ
  set ρ := (snd (epsR K) P.A).left with hρ
  obtain ⟨t, ht⟩ := exists_gen (fst (epsR K) P.A).left τ ρ (fun y W hy => (pre W).le hy) m L hL _ (fun i j y hi hj => by
    have hy : y ∈ ρ ⁻¹ᵁ (m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U j) := (pre _).le ⟨hi, hj⟩
    have e := congrArg (gs (𝟙 _) y _) (hdw (m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U j) (pbT m (L.g i j).val _))
    have e₂ : dw _ (pbT m (L.g i j).val (m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U j)) =
        pbT m (L.g i j).val (m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U j) * lc P.A.hom c φ i j := by
      rw [hsum, lc, Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => by rw [← hφ a i j, mul_left_comm]
    rw [e₂, gs_add _ _ _ hy, gs_mul _ _ _ hy, gs_constFn _ _ _ _ hy, gs_pbT _ _ _ (pre _).ge hy,
      gs_pbT _ _ _ le_rfl hy, gs_pbT _ _ _ le_rfl hy, Category.id_comp, Category.id_comp, Category.id_comp,
      gs_mul _ _ _ hy, gs_pbT _ m y (O₀ := L.U i ⊓ L.U j) (O := m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U j) (fun _ h => h) ⟨hi, hj⟩,
      gs_pbT _ m y (O₀ := L.U i ⊓ L.U j) (O := m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U j) (fun _ h => h) hy] at e
    refine e.trans ?_
    ring) hc
  obtain ⟨s, hs⟩ := exists_down ((isGen_iff u).1 hu) hL P.isLB t ht
  have w1 : w = 1 := P.ktriv (DualNumber K) _ w fun p =>
    ⟨⊤, trivial, gen_chartPull (chartPullPull (Out.translDiff P.A P.L w) _ _ rfl) s hs⟩
  have h0 : IsLieComb 0 v w := by
    have := a₃ 0 Fin.elim0 Fin.elim0 Fin.elim0 w (fun i => i.elim0) ⟨Fin.elim0, fun i => i.elim0, by rw [w1]; rfl⟩
    simpa using this
  exact (hv.2 w tw).unique hw h0

end GlobalTheory.KS.DlogPol
end
