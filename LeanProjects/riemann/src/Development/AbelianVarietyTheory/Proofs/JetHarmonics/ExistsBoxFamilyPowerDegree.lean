import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdFam
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.OneCSt
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.BoxProductLinearIndependent
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SecScalOfPointwise
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.RankAndGOfIsPowDeg
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TwistedPowerSectionBasisBaseChange

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.IntegralBox

open GlobalTheory.BoxIndep GlobalTheory.FieldBaseChange

theorem span_of_indep_residue {V M M' : Type} [CommRing V] [IsLocalRing V] [AddCommGroup M] [Module V M]
    [AddCommGroup M'] [Module (ResidueField V) M'] (π : M →ₛₗ[residue V] M') {I : Type} [Fintype I]
    (b t : I → M) (hb : ∀ s, ∃ c : I → V, s = ∑ i, c i • b i)
    (ht : ∀ c : I → ResidueField V, ∑ a, c a • π (t a) = 0 → c = 0) (s : M) :
    ∃ c : I → V, s = ∑ a, c a • t a := by
  classical
  choose w hw using fun a => hb (t a)
  let A : Matrix I I V := Matrix.of w
  have hA : IsUnit A.det := by
    rw [← residue_ne_zero_iff_isUnit, RingHom.map_det]
    intro h
    obtain ⟨c, hc, hc'⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h
    refine hc (ht c ?_)
    have e : ∀ i, ∑ a, c a * residue V (w a i) = 0 := fun i => congrFun hc' i
    simp only [hw, map_sum, map_smulₛₗ, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero fun i _ => by rw [← Finset.sum_smul, e, zero_smul]
  obtain ⟨d, rfl⟩ := hb s
  refine ⟨Matrix.vecMul d A⁻¹, ?_⟩
  have e : ∀ i, ∑ a, Matrix.vecMul d A⁻¹ a * w a i = d i := fun i =>
    congrFun (show Matrix.vecMul (Matrix.vecMul d A⁻¹) A = d by
      rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hA, Matrix.vecMul_one]) i
  simp only [hw, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => by rw [← Finset.sum_smul, e]

theorem exists_tensor_pow (F O : Type) [Field F] [CommRing O] [Algebra F O] {m : ℕ} (j : ℕ)
    (β : Fin j → Fin m → O) (hβ : ∀ i, LinearIndependent F (β i)) :
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra F B) (em : Fin j → (O →ₐ[F] B)),
      LinearIndependent F (fun a : Fin j → Fin m => ∏ i, em i (β i (a i))) := by
  induction j with
  | zero =>
    refine ⟨F, inferInstance, inferInstance, fun i => i.elim0, ?_⟩
    rw [linearIndependent_unique_iff]
    simp
  | succ j ih =>
    obtain ⟨B, _, _, em, h⟩ := ih (fun i => β i.succ) (fun i => hβ _)
    refine ⟨TensorProduct F O B, inferInstance, inferInstance,
      Fin.cons Algebra.TensorProduct.includeLeft
        (fun i => (Algebra.TensorProduct.includeRight).comp (em i)), ?_⟩
    have h2 := ((hβ 0).tmul_of_isDomain h).comp (Fin.consEquiv (fun _ : Fin (j+1) => Fin m)).symm
      (Equiv.injective _)
    refine (congrArg (fun v : (Fin (j + 1) → Fin m) → TensorProduct F O B => LinearIndependent F v)
      (funext fun a => ?_)).mpr h2
    simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, AlgHom.comp_apply, Function.comp_apply]
    rw [← map_prod, Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, _root_.one_mul]
    rfl

variable {X Y Z : Scheme.{0}}

theorem exists_test {F : Type} [Field F] (p : X ⟶ Spec (CommRingCat.of F)) (x : X) {j : ℕ} {U : Fin j → X.Opens}
    (hx : ∀ i, x ∈ U i) {m : ℕ} (s : ∀ i, Fin m → Γ(X, U i))
    (hs : ∀ i (c : Fin m → F), ∑ l, germOf p x (c l) * gs (𝟙 X) x (U i) (s i l) = 0 → c = 0) :
    ∃ (Z : Scheme.{0}) (q : Z ⟶ Spec (CommRingCat.of F)) (r : Fin j → (Z ⟶ X)), (∀ i, r i ≫ p = q) ∧
      (∀ i z, r i z ∈ U i) ∧ ∀ c : (Fin j → Fin m) → F,
        (∀ z, ∑ a, germOf q z (c a) * ∏ i, gs (r i) z (U i) (s i (a i)) = 0) → c = 0 := by
  let : Algebra F (X.presheaf.stalk x) := (germOf p x).toAlgebra
  have hβ : ∀ i, LinearIndependent F (fun l => gs (𝟙 X) x (U i) (s i l)) := fun i =>
    Fintype.linearIndependent_iff.2 fun c hc => congrFun (hs i c (by simp only [Algebra.smul_def] at hc; exact hc))
  obtain ⟨B, _, _, em, h⟩ := exists_tensor_pow F _ j _ hβ
  refine ⟨Spec (CommRingCat.of B), Spec.map (CommRingCat.ofHom (algebraMap F B)),
    fun i => (Spec.map (CommRingCat.ofHom (em i).toRingHom) : _ ⟶ Spec (X.presheaf.stalk x)) ≫ X.fromSpecStalk x,
    fun i => ?_, fun i z => fromSpecStalk_mem x (hx i) _, fun c hc => ?_⟩
  · rw [Category.assoc, fromSpecStalk_comp]
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a
    exact (em i).commutes a
  · funext a
    refine Fintype.linearIndependent_iff.1 h c (eq_zero_of_germOf (B := CommRingCat.of B) _ fun z => ?_) a
    rw [← hc z, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Algebra.smul_def, map_mul, map_prod]
    congr 1
    · rw [← Category.id_comp (Spec.map _), germOf_map]; rfl
    · refine Finset.prod_congr rfl fun i _ => ?_
      rw [gs_fromSpecStalk x (hx i)]
      exact (germOf_map (B := X.presheaf.stalk x) (𝟙 _) (CommRingCat.ofHom (em i).toRingHom) z _).symm

theorem eq_zero_of_generic [IsIntegral Y] {R : Type} [CommRing R] (π : Y ⟶ Spec (CommRingCat.of R)) {L : LB X}
    {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : SecOver π (LB.LinComb L φ ε)) {J}
    (hJ : Good L (genericPoint Y) J) (h : sval s (𝟙 Y) (genericPoint Y) J = 0) : s = 0 := by
  refine SecOps.sec_ext fun jj => fn_ext fun y hy => congrArg _ ?_
  have hy' : genericPoint Y ∈ LB.wchart L φ jj :=
    ((genericPoint_spec _).mem_open_set_iff (TopologicalSpace.Opens.isOpen _)).mpr ⟨y, trivial, hy⟩
  apply germ_injective_of_isIntegral _ _ hy'
  refine (gs_eq (𝟙 _) _ _ hy' _).symm.trans (Eq.trans ?_ (map_zero _).symm)
  exact (sec_trans s (𝟙 _) _ hy' (hJ.mem φ _)).trans ((congrArg _ h).trans (mul_zero _))

theorem sval_comb {R : Type} [CommRing R] (π : Y ⟶ Spec (CommRingCat.of R)) {L : LB X}
    {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {I : Type} [Fintype I] (c : I → R)
    (s : I → SecOver π (LB.LinComb L φ ε)) (r : Z ⟶ Y) {z : Z} {J} (hJ : Good L z J) :
    sval (∑ i, c i • s i : SecOver π _) r z J =
      ∑ i, germOf (B := CommRingCat.of R) (r ≫ π) z (c i) * sval (s i) r z J := by
  rw [sval_sum' hJ]
  exact Finset.sum_congr rfl fun i _ => by rw [sval_smul' hJ, germOf_apply]; rfl

section Box

variable {V : Type} [CommRing V] [IsDomain V] {R : Type} [CommRing R] (φ : V →+* R) (D : DegPre V)

theorem isPullback_snd : IsPullback (snd (Over.mk (spMap φ)) D.P.A).left (fst (Over.mk (spMap φ)) D.P.A).left
    D.P.A.hom (spMap φ) := (IsPullback.of_hasPullback (spMap φ) D.P.A.hom).flip

abbrev SecMod (k : ℕ) (α : D.X) : Type := SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB α) (DegPre.famε k))

abbrev SecModBC (k : ℕ) (α : D.X) : Type :=
  SecOver (R := R) (fst (Over.mk (spMap φ)) D.P.A).left
    (LB.LinComb D.P.L (fun a => (snd (Over.mk (spMap φ)) D.P.A).left ≫ D.famφB α a) (DegPre.famε k))

noncomputable def pullBC (k : ℕ) (α : D.X) : SecMod D k α →ₛₗ[φ] SecModBC φ D k α :=
  pullOver D.P.L (DegPre.famε k) (isPullback_snd φ D).w (fun _ => rfl)

theorem sval_pullBC {k : ℕ} {α : D.X} (s : SecMod D k α) (r : Z ⟶ (Over.mk (spMap φ) ⊗ D.P.A).left) {z : Z} {J}
    (hJ : Good D.P.L z J) :
    sval (pullBC φ D k α s) r z J = sval s (r ≫ (snd (Over.mk (spMap φ)) D.P.A).left) z J :=
  sval_pullOver (isPullback_snd φ D).w (fun _ => rfl) s r hJ

theorem exists_basis [IsLocalRing V] [IsNoetherianRing V] (hT : TwistBaseChangeStatement) {k : ℕ} (hk : 1 ≤ k)
    (α : D.X) : ∃ b : Fin (k ^ D.P.g) → SecMod D k α, (∀ s, ∃ c : Fin (k ^ D.P.g) → V, s = ∑ i, c i • b i) ∧
      ∀ c : Fin (k ^ D.P.g) → R, ∑ i, c i • pullBC φ D k α (b i) = 0 → c = 0 := by
  have hL := D.P.isLB
  obtain ⟨m, b, rfl, hb⟩ := hT V D k hk α
  have H₀ : IsPullback (𝟙 D.P.A.left) D.P.A.hom D.P.A.hom (spMap (RingHom.id V)) := by
    have : spMap (RingHom.id V) = 𝟙 _ := by simp [spMap]
    rw [this]
    exact IsPullback.id_horiz _
  have hψ₀ : ∀ k, D.famφB α k = 𝟙 _ ≫ D.famφB α k := fun k => (Category.id_comp _).symm
  have h0 := ZH.BasisBaseChange.basis_of_isPullback (RingHom.id V) hL (D.famφB α) (DegPre.famε k) b
    (hb V (RingHom.id V) _ fun _ _ => rfl) H₀ hψ₀
  have e0 : ∀ i, pullOver D.P.L (DegPre.famε k) H₀.w hψ₀ (b i) = b i := fun i => sec_ext' hL fun y J hJ =>
    (sval_pullOver H₀.w hψ₀ _ _ hJ).trans (by rw [Category.comp_id])
  simp only [e0] at h0
  have h1 := ZH.BasisBaseChange.basis_of_isPullback φ hL (D.famφB α) (DegPre.famε k) b
    (hb R φ _ fun _ _ => rfl) (isPullback_snd φ D) (fun _ => rfl) (0 : SecModBC φ D k α)
  exact ⟨b, fun s => (h0 s).exists, fun c hc => h1.unique hc.symm
    (Finset.sum_eq_zero fun i _ => zero_smul R _).symm⟩

end Box

theorem box_indep {V : Type} [CommRing V] [IsDomain V] {F : Type} [Field F] (φ : V →+* F) {j : ℕ}
    {D D' : DegPre V} (pD : IsPowDeg D' D j) {k m : ℕ} (b : ∀ α, Fin m → SecMod D k α)
    (hb : ∀ α (c : Fin m → F), ∑ i, c i • pullBC φ D k α (b α i) = 0 → c = 0) (α' : D'.X)
    (c : (Fin j → Fin m) → F)
    (hc : ∑ a, c a • pullBC φ D' k α' (boxFamB pD k (fun i α => b α (a i)) α') = 0) : c = 0 := by
  let T₀ : Over (Spec (CommRingCat.of V)) := Over.mk (spMap φ)
  have := D.P.isAb.smooth
  have := D.P.isAb.geomConnected
  have hg := geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres D.P.A.hom
  have hint : IsIntegral (T₀ ⊗ D.P.A).left := hg.geometrically_isIntegral _ _ _ (isPullback_snd φ D)
  choose J₀ hJ₀ using fun χ : (T₀ ⊗ D.P.A).left ⟶ D.P.A.left =>
    exists_chart D.P.isLB (χ (genericPoint (T₀ ⊗ D.P.A).left))
  have hJ₀ : Good D.P.L _ J₀ := hJ₀
  obtain ⟨Z, q, r, hq, hr, H⟩ := exists_test (F := F) (fst T₀ D.P.A).left _
    (fun i => hJ₀.mem (fun a => (snd T₀ D.P.A).left ≫ D.famφB (pD.xe α' i) a) (𝟙 _))
    (fun i l => (pullBC φ D k (pD.xe α' i) (b _ l)).f _)
    (fun i c hc => hb _ c (eq_zero_of_generic _ _ hJ₀ ((sval_comb _ c _ (𝟙 _) hJ₀).trans (by
      rw [Category.id_comp]; exact hc))))
  let T : Over (Spec (CommRingCat.of V)) := Over.mk (q ≫ T₀.hom)
  let q' : T ⟶ T₀ := Over.homMk q rfl
  let r' : Fin j → (T ⟶ T₀ ⊗ D.P.A) := fun i => Over.homMk (r i) (by
    rw [← Over.w (fst T₀ D.P.A), ← Category.assoc, hq]; rfl)
  let ρ : T ⟶ T₀ ⊗ D'.P.A := lift q' (Fan.IsLimit.lift pD.pw.lim fun i => r' i ≫ snd _ _)
  have hρ : ∀ i, (ρ ≫ snd _ _) ≫ pD.pw.pr i = r' i ≫ snd _ _ := fun i => by
    rw [lift_snd]
    exact Fan.IsLimit.fac pD.pw.lim _ i
  have hρ' : ∀ i, ((ρ.left : Z ⟶ _) ≫ (snd T₀ D'.P.A).left) ≫ (pD.pw.pr i).left =
      r i ≫ (snd T₀ D.P.A).left := fun i => congrArg (fun g => g.left) (hρ i)
  have hρq : (ρ.left : Z ⟶ _) ≫ (fst T₀ D'.P.A).left = q :=
    congrArg (fun g => g.left) (lift_fst q' (Fan.IsLimit.lift pD.pw.lim fun i => r' i ≫ snd _ _))
  refine H c fun z => ?_
  choose J hJ using fun ψ : Z ⟶ D.P.A.left => exists_chart D.P.isLB (ψ z)
  have hJ : Good D.P.L z J := hJ
  choose J' hJ' using fun ψ : Z ⟶ D'.P.A.left => exists_chart D'.P.isLB (ψ z)
  have hJ' : Good D'.P.L z J' := hJ'
  have E := (sval_comb _ c _ (ρ.left : Z ⟶ _) hJ').symm.trans
    ((congrArg (fun s : SecModBC φ D' k α' => sval (Z := Z) s ρ.left z J') hc).trans (sval_zero' hJ' _))
  rw [hρq] at E
  obtain ⟨u, hu⟩ : ∃ u : Z.presheaf.stalk z, ∀ a : Fin j → Fin m,
      u * sval (Z := Z) (pullBC φ D' k α' (boxFamB pD k (fun i α => b α (a i)) α')) ρ.left z J' =
      ∏ i, sval (pullBC φ D k (pD.xe α' i) (b _ (a i))) (r i) z J := by
    refine ⟨(∏ a, bw pD.w (((ρ.left : Z ⟶ _) ≫ (snd T₀ D'.P.A).left) ≫ D'.famφB α' a) z
      (fun i => J ((((ρ.left : Z ⟶ _) ≫ (snd T₀ D'.P.A).left) ≫ D'.famφB α' a) ≫ (pD.pw.pr i).left))
      (J' (((ρ.left : Z ⟶ _) ≫ (snd T₀ D'.P.A).left) ≫ D'.famφB α' a)) ^ DegPre.famε k a).val, fun a => ?_⟩
    obtain ⟨hψ, H'⟩ := isBoxFamB_boxFamB pD k (fun i α => b α (a i)) α'
    refine (congrArg _ (sval_pullBC φ D' _ _ hJ')).trans ((BoxFamScalar.box_sval pD.w hψ _ _ _ H' _ z hJ hJ').trans
      (Finset.prod_congr rfl fun i _ => ?_))
    rw [sval_pullBC φ D _ _ hJ]
    exact congrArg (fun g => sval (b _ (a i)) g z J) (hρ' i)
  obtain ⟨v, hv⟩ : ∃ v : Fin j → Z.presheaf.stalk z, ∀ i l,
      gs (r i) z (LB.wchart D.P.L (fun a => (snd T₀ D.P.A).left ≫ D.famφB (pD.xe α' i) a)
          (fun a => J₀ (𝟙 _ ≫ (snd T₀ D.P.A).left ≫ D.famφB (pD.xe α' i) a)))
        ((pullBC φ D k (pD.xe α' i) (b _ l)).f
          (fun a => J₀ (𝟙 _ ≫ (snd T₀ D.P.A).left ≫ D.famφB (pD.xe α' i) a))) =
      v i * sval (pullBC φ D k (pD.xe α' i) (b _ l)) (r i) z J :=
    ⟨_, fun i l => sec_trans _ (r i) z (hr i z) (hJ.mem _ (r i))⟩
  refine Eq.trans (Finset.sum_congr rfl fun a _ => ?_) ((Finset.mul_sum _ _ ((∏ i, v i) * u)).symm.trans
    ((congrArg _ E).trans (mul_zero _)))
  refine Eq.trans (congrArg _ (((Finset.prod_congr rfl fun i _ => hv i (a i)).trans Finset.prod_mul_distrib).trans
    (congrArg _ (hu a).symm))) ?_
  exact (congrArg _ (_root_.mul_assoc _ _ _).symm).trans (mul_left_comm _ _ _)

theorem main : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] (j : ℕ) (D D' : DegPre V) (pD : IsPowDeg D' D j) (k : ℕ), 1 ≤ k → ∀ (α' : D'.X) (β' : D'.SecB k α'), ∃ (l : ℕ) (c : Fin l → V) (f : Fin l → Fin j → ∀ α : D.X, D.SecB k α) (f' : Fin l → ∀ α : D'.X, D'.SecB k α), (∀ a, IsBoxFamB pD k (f' a) (f a)) ∧ ∀ jj, β'.f jj = ∑ a, constFn D'.P.A.hom _ (c a) * (f' a α').f jj := by
  intro _ _ _ hT V _ _ _ _ j D D' pD k hk α' β'
  choose b _ hb using exists_basis (residue V) D hT hk
  obtain ⟨b', hb', -⟩ := exists_basis (residue V) D' hT hk α'
  have hg := (rank_and_g_of_isPowDeg V j D D' pD).2
  let e : Fin (k ^ D'.P.g) ≃ (Fin j → Fin (k ^ D.P.g)) := Fintype.equivOfCardEq (by
    simp [hg, ← pow_mul, mul_comm])
  obtain ⟨c, hc⟩ := span_of_indep_residue (pullBC (residue V) D' k α') b'
    (fun n => boxFamB pD k (fun i α => b α (e n i)) α') hb' (fun c hc => by
      have := box_indep (residue V) pD b hb α' (fun a => c (e.symm a)) (by
        rw [← hc, ← e.sum_comp]
        simp only [Equiv.symm_apply_apply])
      funext n
      simpa using congrFun this (e n)) β'
  exact ⟨_, c, fun n i α => b α (e n i), fun n => boxFamB pD k (fun i α => b α (e n i)),
    fun n => isBoxFamB_boxFamB pD k _, (ZH.BasisBaseChange.isLin_iff D'.P.A.hom _ c β').2 hc⟩

end GlobalTheory.IntegralBox
