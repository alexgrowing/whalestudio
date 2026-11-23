import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdFam
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.BoxProductLinearIndependent
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxSec

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

namespace BoxFamIndep

open ReciprocityTheory.ChartRestriction.G.Geo.Tor BoxIndep

theorem exists_tensor_pow (F O : Type) [Field F] [CommRing O] [Algebra F O] {A : Type} {m : ℕ} (β : A → Fin m → O)
    (hβ : ∀ c : Fin m → F, (∀ α, ∑ l, c l • β α l = 0) → c = 0) (j : ℕ) :
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra F B) (em : Fin j → (O →ₐ[F] B)),
      ∀ c : (Fin j → Fin m) → F,
        (∀ α : Fin j → A, ∑ a, c a • ∏ i, em i (β (α i) (a i)) = 0) → c = 0 := by
  induction j with
  | zero =>
    refine ⟨F, inferInstance, inferInstance, fun i => i.elim0, fun c hc => ?_⟩
    have := hc (fun i => i.elim0)
    funext a
    rw [Fintype.sum_unique] at this
    rw [Subsingleton.elim a default]
    simpa using this
  | succ j ih =>
    obtain ⟨B, _, _, em, h⟩ := ih
    refine ⟨TensorProduct F O B, inferInstance, inferInstance,
      Fin.cons Algebra.TensorProduct.includeLeft
        (fun i => (Algebra.TensorProduct.includeRight).comp (em i)), fun c hc => ?_⟩
    have key : ∀ (α₀ : A) (α : Fin j → A), ∑ l : Fin m, β α₀ l ⊗ₜ[F]
        (∑ a : Fin j → Fin m, c (Fin.cons l a) • ∏ i, em i (β (α i) (a i))) = 0 := by
      intro α₀ α
      rw [← hc (Fin.cons α₀ α), ← (Fin.consEquiv (fun _ : Fin (j+1) => Fin m)).sum_comp, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, AlgHom.comp_apply]
      rw [← map_prod, Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
        Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, _root_.one_mul, TensorProduct.tmul_smul]
      rfl
    have key2 : ∀ l, (fun a : Fin j → Fin m => c (Fin.cons l a)) = 0 := fun l => h _ fun α => by
      refine (Module.forall_dual_apply_eq_zero_iff F _).1 fun φ => ?_
      refine congrFun (hβ (fun l => φ (∑ a : Fin j → Fin m, c (Fin.cons l a) • ∏ i, em i (β (α i) (a i))))
        fun α₀ => ?_) l
      have := congrArg (fun t => TensorProduct.rid F O (LinearMap.lTensor O φ t)) (key α₀ α)
      simpa only [map_sum (LinearMap.lTensor O φ), map_sum (TensorProduct.rid F O), LinearMap.lTensor_tmul,
        TensorProduct.rid_tmul, map_zero] using this
    funext a
    have := congrFun (key2 (a 0)) (Fin.tail a)
    simp only [Fin.cons_self_tail] at this
    exact this

variable {X Z : Scheme.{0}}

theorem exists_test {F : Type} [Field F] (p : X ⟶ Spec (CommRingCat.of F)) (x : X) {A : Type} {U : A → X.Opens}
    (hx : ∀ α, x ∈ U α) {m : ℕ} (s : ∀ α, Fin m → Γ(X, U α))
    (hs : ∀ c : Fin m → F, (∀ α, ∑ l, germOf p x (c l) * gs (𝟙 X) x (U α) (s α l) = 0) → c = 0) (j : ℕ) :
    ∃ (Z : Scheme.{0}) (q : Z ⟶ Spec (CommRingCat.of F)) (r : Fin j → (Z ⟶ X)), (∀ i, r i ≫ p = q) ∧
      (∀ i z α, r i z ∈ U α) ∧ ∀ c : (Fin j → Fin m) → F,
        (∀ (α : Fin j → A) z, ∑ a, germOf q z (c a) * ∏ i, gs (r i) z (U (α i)) (s (α i) (a i)) = 0) → c = 0 := by
  let : Algebra F (X.presheaf.stalk x) := (germOf p x).toAlgebra
  obtain ⟨B, _, _, em, h⟩ := exists_tensor_pow F _ (fun α l => gs (𝟙 X) x (U α) (s α l))
    (fun c hc => hs c fun α => by
      have := hc α
      simp only [Algebra.smul_def] at this
      exact this) j
  refine ⟨Spec (CommRingCat.of B), Spec.map (CommRingCat.ofHom (algebraMap F B)),
    fun i => (Spec.map (CommRingCat.ofHom (em i).toRingHom) : _ ⟶ Spec (X.presheaf.stalk x)) ≫ X.fromSpecStalk x,
    fun i => ?_, fun i z α => fromSpecStalk_mem x (hx α) _, fun c hc => ?_⟩
  · rw [Category.assoc, fromSpecStalk_comp]
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a
    exact (em i).commutes a
  · refine h c fun α => eq_zero_of_germOf (B := CommRingCat.of B) _ fun z => ?_
    rw [← hc α z, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Algebra.smul_def, map_mul, map_prod]
    congr 1
    · rw [← Category.id_comp (Spec.map _), germOf_map]; rfl
    · refine Finset.prod_congr rfl fun i _ => ?_
      rw [gs_fromSpecStalk x (hx _)]
      exact (germOf_map (B := X.presheaf.stalk x) (𝟙 _) (CommRingCat.ofHom (em i).toRingHom) z _).symm

variable {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ}

theorem sum_f {D : DegPre R} {K : Type} (S : Finset K) (b : K → Fam D F k) (α : D.X) (jj) :
    ((∑ l ∈ S, b l).s α).f jj = ∑ l ∈ S, ((b l).s α).f jj := by
  classical
  induction S using Finset.induction_on with
  | empty => rfl
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_f, ih]

theorem gs_comb {D : DegPre R} {K : Type} [Fintype K] (c : K → F) (b : K → Fam D F k) (α : D.X) (jj)
    (r : Z ⟶ (DegPre.BF D F).left) (z : Z) (hz : r z ∈ LB.wchart D.P.L (DegPre.famφ D F α) jj) :
    gs r z (LB.wchart D.P.L (DegPre.famφ D F α) jj) (((∑ l, c l • b l).s α).f jj) =
      ∑ l, germOf (B := CommRingCat.of F) (r ≫ (fst (TF (R := R) F) D.P.A).left) z (c l) *
        gs r z (LB.wchart D.P.L (DegPre.famφ D F α) jj) (((b l).s α).f jj) := by
  refine (congrArg _ (sum_f _ _ α jj)).trans ?_
  refine (gs_fsum r z _ hz _ _).trans (Finset.sum_congr rfl fun l _ => ?_)
  refine (gs_mul r z _ hz _ _).trans (congrArg (· * _) ?_)
  exact (gs_res r z le_top hz _).trans
    ((gs_pull r (fst (TF (R := R) F) D.P.A).left z ⊤ trivial _).trans (germOf_apply _ _ _).symm)

theorem main {j : ℕ} {D D' : DegPre R} (pD : IsPowDeg D' D j) {m : ℕ} (b : Fin m → Fam D F k)
    (hb : LinearIndependent F b) (b' : (Fin j → Fin m) → Fam D' F k)
    (hb' : ∀ a, IsBoxFam pD F k (b' a) (fun i => b (a i))) : LinearIndependent F b' := by
  refine Fintype.linearIndependent_iff.2 fun c hc => congrFun (?_ : c = 0)
  have := D.P.isAb.smooth
  have := D.P.isAb.geomConnected
  have hg := geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres D.P.A.hom
  have hint : IsIntegral (DegPre.BF D F).left :=
    hg.geometrically_isIntegral (TF (R := R) F).hom _ _ (IsPullback.of_hasPullback (TF (R := R) F).hom D.P.A.hom).flip
  choose J₀ hJ₀ using fun χ : (DegPre.BF D F).left ⟶ D.P.A.left =>
    exists_chart D.P.isLB (χ (genericPoint (DegPre.BF D F).left))
  have hx : ∀ α, genericPoint (DegPre.BF D F).left ∈
      LB.wchart D.P.L (DegPre.famφ D F α) (fun a => J₀ (DegPre.famφ D F α a)) :=
    fun α => Set.mem_iInter.2 fun a => hJ₀ _
  obtain ⟨Z, q, r, hq, hr, H⟩ := exists_test (F := F) (fst (TF (R := R) F) D.P.A).left _ hx
    (fun α l => ((b l).s α).f (fun a => J₀ (DegPre.famφ D F α a)))
    (fun c hc => funext <| Fintype.linearIndependent_iff.1 hb c <| fam_ext fun α jj => by
      refine fn_ext fun y hy => congrArg _ ?_
      have hy' : genericPoint (DegPre.BF D F).left ∈ LB.wchart D.P.L (DegPre.famφ D F α) jj :=
        ((genericPoint_spec _).mem_open_set_iff (TopologicalSpace.Opens.isOpen _)).mpr ⟨y, trivial, hy⟩
      apply germ_injective_of_isIntegral _ _ hy'
      refine (gs_eq (𝟙 _) _ _ hy' _).symm.trans (Eq.trans ?_ (map_zero _).symm)
      refine (sec_trans _ (𝟙 _) _ hy' (hx α)).trans ?_
      refine (congrArg _ ((gs_comb c b α _ (𝟙 _) _ (hx α)).trans ?_)).trans (mul_zero _)
      rw [Category.id_comp]
      exact hc α) j
  let T : Over (Spec (CommRingCat.of R)) := Over.mk (q ≫ (TF (R := R) F).hom)
  let q' : T ⟶ TF (R := R) F := Over.homMk q rfl
  let r' : Fin j → (T ⟶ DegPre.BF D F) := fun i => Over.homMk (r i) (by
    rw [← Over.w (fst (TF (R := R) F) D.P.A), ← Category.assoc, hq]; rfl)
  let ρ : T ⟶ DegPre.BF D' F := lift q' (Fan.IsLimit.lift pD.pw.lim fun i => r' i ≫ snd _ _)
  have hρ : ∀ i, ρ ≫ TF (R := R) F ◁ pD.pw.pr i = r' i := fun i => by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, whiskerLeft_fst, lift_fst]
      exact Over.OverMorphism.ext (hq i).symm
    · rw [Category.assoc, whiskerLeft_snd, ← Category.assoc, lift_snd]
      exact Fan.IsLimit.fac pD.pw.lim _ i
  have hρ' : ∀ i, (ρ.left : Z ⟶ _) ≫ prB pD F i = r i := fun i => congrArg (fun g => g.left) (hρ i)
  have hρq : (ρ.left : Z ⟶ _) ≫ (fst (TF (R := R) F) D'.P.A).left = q :=
    congrArg (fun g => g.left) (lift_fst q' (Fan.IsLimit.lift pD.pw.lim fun i => r' i ≫ snd _ _))
  refine H c fun α z => ?_
  obtain ⟨α', rfl⟩ := pD.xe.surjective α
  choose J hJ using fun ψ : Z ⟶ D.P.A.left => exists_chart D.P.isLB (ψ z)
  have hJ : Good D.P.L z J := hJ
  choose J' hJ' using fun ψ : Z ⟶ D'.P.A.left => exists_chart D'.P.isLB (ψ z)
  have hJ' : Good D'.P.L z J' := hJ'
  have hm := hJ'.mem (DegPre.famφ D' F α') (ρ.left : Z ⟶ _)
  have E := (gs_comb c b' α' _ (ρ.left : Z ⟶ _) z hm).symm.trans
    ((congrArg (fun s : Fam D' F k => gs (Y := Z) ρ.left z _ ((s.s α').f _)) hc).trans (gs_zero _ _ _ hm))
  rw [hρq] at E
  have E' := fun a => BoxPhi.fam_val pD (hb' a) α' (Z := Z) ρ.left z hJ hJ'
  simp only [hρ'] at E'
  obtain ⟨u, hu⟩ : ∃ u : Z.presheaf.stalk z, ∀ a, u * sval (Z := Z) ((b' a).s α') ρ.left z J' =
      ∏ i, sval ((b (a i)).s (pD.xe α' i)) (r i) z J := ⟨_, E'⟩
  obtain ⟨v, hv⟩ : ∃ v : Fin j → Z.presheaf.stalk z, ∀ i l,
      gs (r i) z (LB.wchart D.P.L (DegPre.famφ D F (pD.xe α' i)) (fun a => J₀ (DegPre.famφ D F (pD.xe α' i) a)))
        (((b l).s (pD.xe α' i)).f (fun a => J₀ (DegPre.famφ D F (pD.xe α' i) a))) =
      v i * sval ((b l).s (pD.xe α' i)) (r i) z J :=
    ⟨_, fun i l => sec_trans _ (r i) z (hr i z _) (hJ.mem _ (r i))⟩
  refine Eq.trans (Finset.sum_congr rfl fun a _ => ?_) ((Finset.mul_sum _ _ ((∏ i, v i) * u)).symm.trans
    ((congrArg _ E).trans (mul_zero _)))
  refine Eq.trans (congrArg _ (((Finset.prod_congr rfl fun i _ => hv i (a i)).trans Finset.prod_mul_distrib).trans
    (congrArg _ (hu a).symm))) ?_
  exact (congrArg _ (_root_.mul_assoc _ _ _).symm).trans (mul_left_comm _ _ _)

end BoxFamIndep

theorem boxFam_linearIndependent : ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (D D' : DegPre R) (pD : IsPowDeg D' D j) (F : Type) [Field F] [Algebra (FractionRing R) F] (k m : ℕ) (b : Fin m → Fam D F k), LinearIndependent F b → ∀ b' : (Fin j → Fin m) → Fam D' F k, (∀ a, IsBoxFam pD F k (b' a) (fun i => b (a i))) → LinearIndependent F b' :=
  fun _ _ _ _ _ _ pD _ _ _ _ _ b hb b' hb' => BoxFamIndep.main pD b hb b' hb'

end GlobalTheory
