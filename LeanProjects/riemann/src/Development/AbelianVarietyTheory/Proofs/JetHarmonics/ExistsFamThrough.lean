import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdFam
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.BOfNsmulLeft
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsFamRep
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.OneCSt
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsLeastOfDiscrete
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsRepresentativesModNsmul
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBasisOfEq
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.FamEqOnClassOfEq
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.LinOfSval
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsBoxFamilyMultilinearMapStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsBoxFamilyPowerDegreeStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.UnitBallBox

theorem exists_secScal {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} (σ : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y) (φ' : K → (Y' ⟶ X))
    (e : φ' = fun a => h ≫ φ a) :
    ∃ s : LB.Sec (LB.LinComb L φ' ε), GeneratorPullback.SecScal L φ' ε s φ ε σ h 1 := by
  subst e
  exact ⟨DVR.pullSec L φ ε σ h, SectionScalarValuation.secScal_of_sval hL fun y J hJ => (SectionScalarValuation.sval_pullSec _ _ _ _ _ y hJ).symm⟩

section Fam

variable {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ}

theorem sum_f {D : DegPre R} {K : Type} (S : Finset K) (b : K → Fam D F k) (α : D.X) (jj) :
    ((∑ l ∈ S, b l).s α).f jj = ∑ l ∈ S, ((b l).s α).f jj := by
  classical
  induction S using Finset.induction_on with
  | empty => rfl
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_f, ih]

theorem eq_sum_of_classes (hG : GlobalFnsSt) {D : DegPre R} {N : Type} [Fintype N] (e : N → D.X)
    (he : ∀ χ : D.X, ∃! i, ∃ m : D.X, χ = e i + k • m) (S : Fam D F k) (T : N → Fam D F k)
    (h₁ : ∀ i jj, ((T i).s (e i)).f jj = (S.s (e i)).f jj)
    (h₀ : ∀ i β, (∀ mu, e i + k • mu ≠ β) → ∀ jj, ((T i).s β).f jj = 0) : S = ∑ i, T i := by
  refine fam_ext fun χ jj => ?_
  obtain ⟨i, ⟨m, rfl⟩, -⟩ := he χ
  refine fam_eq_on_class_of_eq hG R D F k _ _ (e i) (fun jj => ?_) m jj
  rw [sum_f, Finset.sum_eq_single i, h₁]
  · intro i' _ hi
    exact h₀ i' (e i) (fun m hm => hi ((he (e i)).unique ⟨m, hm.symm⟩ ⟨0, by rw [smul_zero, add_zero]⟩)) jj
  · intro h; exact absurd (Finset.mem_univ i) h

variable {j : ℕ} {D D' : DegPre R} (pD : IsPowDeg D' D j)

theorem box_zero {S : Fam D' F k} {s : Fin j → Fam D F k} (hS : IsBoxFam pD F k S s) (β : D'.X) (i : Fin j)
    (h : ∀ jj, ((s i).s (pD.xe β i)).f jj = 0) (jj) : (S.s β).f jj = 0 := by
  obtain ⟨hφ, H⟩ := hS β
  refine sec_ext_val D'.P.isLB (s' := SecOps.secZero) (fun y J' hJ' => ?_) jj
  choose J hJ using fun χ : (DegPre.BF D' F).left ⟶ D.P.A.left => exists_chart D.P.isLB (χ y)
  have hJ : Good D.P.L y J := hJ
  have A := BoxFamScalar.box_sval pD.w hφ (S.s β) (fun i => (s i).s (pD.xe β i)) _ H (𝟙 _) y hJ hJ'
  rw [Finset.prod_eq_zero (Finset.mem_univ i) (UUA.sval_zero_of h _ y J (hJ.mem _ _))] at A
  rw [UUA.sval_zero_of (s := SecOps.secZero) (fun _ => rfl) _ y J' (hJ'.mem _ _)]
  exact (Units.mul_right_eq_zero _).1 A

theorem box_secScal {S : Fam D' F k} {s : Fin j → Fam D F k} (hS : IsBoxFam pD F k S s)
    {f' : ∀ α : D'.X, D'.SecB k α} {f : Fin j → ∀ α : D.X, D.SecB k α} (hf : IsBoxFamB pD k f' f) (α' : D'.X)
    (h : ∀ i, GeneratorPullback.SecScal D.P.L (DegPre.famφ D F (pD.xe α' i)) (DegPre.famε k) ((s i).s (pD.xe α' i))
      (D.famφB (pD.xe α' i)) (DegPre.famε k) (f i (pD.xe α' i)) (DegPre.prB D F).left 1) :
    GeneratorPullback.SecScal D'.P.L (DegPre.famφ D' F α') (DegPre.famε k) (S.s α')
      (D'.famφB α') (DegPre.famε k) (f' α') (DegPre.prB D' F).left 1 := by
  obtain ⟨hφ, H⟩ := hS α'
  obtain ⟨hψ, H'⟩ := hf α'
  have e₄ : ∀ i, (DegPre.prB D' F).left ≫ (pD.pw.pr i).left =
      prB pD F i ≫ (DegPre.prB D F).left := fun i => by
    rw [← Over.comp_left, ← Over.comp_left]; congr 1; exact (whiskerLeft_snd _ _).symm
  exact BoxFamScalar.secScal_box D.P.isLB D'.P.isLB pD.w (GC.famφ_eq D' F α') e₄
    (S.s α') (fun i => (s i).s (pD.xe α' i)) (f' α') (fun i => f i (pD.xe α' i))
    (fun y _ _ hJ hJ' => BoxFamScalar.box_sval pD.w hφ (S.s α') (fun i => (s i).s (pD.xe α' i)) _ H (𝟙 _) y hJ hJ')
    (fun y _ _ hJ hJ' => BoxFamScalar.box_sval pD.w hψ (f' α') (fun i => f i (pD.xe α' i)) _ H' _ y hJ hJ')
    (fun _ => 1) 1 (fun y => by simp only [NuBox.gs_one, Finset.prod_const_one]) h

theorem lin_pull {D : DegPre R} {α : D.X} {l : ℕ} (c : Fin l → R) (β : D.SecB k α) (f : Fin l → D.SecB k α)
    (hβ : ∀ jj, β.f jj = ∑ a, constFn D.P.A.hom _ (c a) * (f a).f jj)
    (βF : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k)))
    (fF : Fin l → LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k)))
    (h : GeneratorPullback.SecScal D.P.L (DegPre.famφ D F α) (DegPre.famε k) βF
      (D.famφB α) (DegPre.famε k) β (DegPre.prB D F).left 1)
    (hf : ∀ a, GeneratorPullback.SecScal D.P.L (DegPre.famφ D F α) (DegPre.famε k) (fF a)
      (D.famφB α) (DegPre.famε k) (f a) (DegPre.prB D F).left 1) (jj) :
    βF.f jj = ∑ a, DegPre.constBF D F (algebraMap (FractionRing R) F (algebraMap R (FractionRing R) (c a))) _ *
      (fF a).f jj := by
  refine NuBox.lin_of_sval D.P.isLB
    (fun a => gF D F (algebraMap (FractionRing R) F (algebraMap R (FractionRing R) (c a)))) fF (fun y J hJ => ?_) jj
  rw [← SectionScalarValuation.secScal_sval h (𝟙 _) y hJ, SectionScalarValuation.sval_lin (fun a => scal D.P.A.hom (c a)) f hβ _ y hJ]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [SectionScalarValuation.secScal_sval (hf a) (𝟙 _) y hJ]
  refine congrArg (· * _) ?_
  let g : R →+* F := (algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))
  have hTF : jFK (R := R) F ≫ jK R = Spec.map (CommRingCat.ofHom g) := by
    show Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) F)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have g₁ : (𝟙 _ ≫ (DegPre.prB D F).left) ≫ D.P.A.hom =
      (fst (TF (R := R) F) D.P.A).left ≫ Spec.map (CommRingCat.ofHom g) := by
    rw [Category.id_comp, Over.w, ← hTF]
    exact (Over.w (fst (TF (R := R) F) D.P.A)).symm
  refine (IntegralCoord.gs_appTop _ D.P.A.hom y _).trans ?_
  rw [g₁, ← IntegralCoord.gs_appTop, IntegralCoord.specMap_appTop, Iso.inv_hom_id_apply]
  exact ((IntegralCoord.gs_appTop (𝟙 _) (fst (TF (R := R) F) D.P.A).left y _).trans (by rw [Category.id_comp]; rfl)).symm

end Fam

theorem exists_fam_through (hG : GlobalFnsSt) {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    {ϖ : V} (hϖ : Irreducible ϖ) (D : DegData V (maximalIdeal V)) {Q : D.toPre.X → ℤ} (hQ : QForm.IsQ D.toPre ϖ Q)
    (F : Type) [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v)
    {k : ℕ} (hk : 1 ≤ k) (α : D.toPre.X) (σ : D.toPre.SecB k α) :
    ∃ s : Fam D.toPre F k, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) (s.s α)
      (D.toPre.famφB α) (DegPre.famε k) σ (DegPre.prB D.toPre F).left 1 ∧
      (∀ β, (∀ mu, α + k • mu ≠ β) → ∀ jj, (s.s β).f jj = 0) ∧
      ∀ t : F, ((((Q α : ℚ) / k : ℚ)) : WithTop ℚ) ≤ v t → NuGe D Q F v k (t • s) 0 := by
  classical
  obtain ⟨hinj, e, he⟩ := exists_representatives_mod_nsmul D.toPre.X k hk
  obtain ⟨σF, hσ⟩ := exists_secScal D.toPre.P.isLB σ (DegPre.prB D.toPre F).left (DegPre.famφ D.toPre F α)
    (funext fun i => GC.famφ_eq D.toPre F α i)
  obtain ⟨s, hs₁, hs₀⟩ := UUA.exists_fam_rep (F := F) hG D.tau_bimult k α
    (fun x y h => hinj x y (add_left_cancel h)) σF
  refine ⟨s, hs₁ ▸ hσ, hs₀, fun t ht => ?_⟩
  rw [n1a V ϖ hϖ D Q hQ F v hv k hk
    (insert α ((Finset.univ.image e).filter fun β => ∀ mu, α + k • mu ≠ β)) (fun χ => ?_) (t • s) 0]
  · intro β hβ
    rcases Finset.mem_insert.1 hβ with rfl | hβ
    · refine ⟨1, fun _ => t, fun _ => σ, fun _ => σF, fun _ => hσ, fun _ => by rwa [zero_add], fun jj => ?_⟩
      rw [Fin.sum_univ_one, smul_f, hs₁]
      rfl
    · refine ⟨0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun jj => ?_⟩
      rw [smul_f, hs₀ β (Finset.mem_filter.1 hβ).2 jj, mul_zero, Fin.sum_univ_zero]
  · obtain ⟨i, ⟨m, rfl⟩, -⟩ := he χ
    by_cases h : ∀ mu, α + k • mu ≠ e i
    · exact ⟨e i, Finset.mem_insert_of_mem
        (Finset.mem_filter.2 ⟨Finset.mem_image_of_mem _ (Finset.mem_univ i), h⟩), m, rfl⟩
    · push_neg at h
      obtain ⟨mu, hmu⟩ := h
      exact ⟨α, Finset.mem_insert_self _ _, mu + m, by rw [← hmu, smul_add, add_assoc]⟩

theorem exists_comp_off {R : Type} [CommRing R] [IsDomain R] {j : ℕ} {D D' : DegPre R} (pD : IsPowDeg D' D j)
    (k : ℕ) {α' β : D'.X} (h : ∀ mu, α' + k • mu ≠ β) : ∃ i, ∀ mu, pD.xe α' i + k • mu ≠ pD.xe β i := by
  by_contra hn
  push_neg at hn
  choose mu hmu using hn
  refine h (pD.xe.symm mu) (pD.xe.injective (funext fun i => ?_))
  rw [map_add, map_nsmul, AddEquiv.apply_symm_apply]
  exact hmu i

set_option maxHeartbeats 800000 in

theorem main : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] (ϖ : V), Irreducible ϖ → ∀ (j : ℕ) (D D' : DegData V (maximalIdeal V)) (pD : IsPowDeg D'.toPre D.toPre j) (Q : D.toPre.X → ℤ), QForm.IsQ D.toPre ϖ Q → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] [IsAlgClosed F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ k : ℕ, 1 ≤ k → ∀ S : Fam D'.toPre F k, NuGe D' (fun x => ∑ i, Q (pD.xe x i)) F v k S 0 → ∃ (l : ℕ) (c : Fin l → F) (s : Fin l → Fin j → Fam D.toPre F k) (S' : Fin l → Fam D'.toPre F k), (∀ a, (0 : WithTop ℚ) ≤ v (c a)) ∧ (∀ a i, NuGe D Q F v k (s a i) 0) ∧ (∀ a, IsBoxFam pD F k (S' a) (s a)) ∧ S = ∑ a, c a • S' a := by
  intro hL hL₂ hL₄ hT V _ _ _ _ ϖ hϖ j D D' pD Q hQ F _ _ _ v hv k hk S hS
  classical
  have hG := hL.globalFns
  obtain ⟨bx, hbx⟩ := GlobalTheory.T.exists_boxFamily_multilinear_map hG V j D.toPre D'.toPre pD F k
  obtain ⟨-, e, he⟩ := exists_representatives_mod_nsmul D'.toPre.X k hk
  have hπ : v (algebraMap (FractionRing V) F (algebraMap V (FractionRing V) ϖ)) = ((1 : ℚ) : WithTop ℚ) := by
    have h1 : HasVal ϖ (algebraMap V (FractionRing V) ϖ) 1 := ⟨1, by simp⟩
    rw [hv _ _ h1]; simp
  choose t ht₀ ht using fun α : D.toPre.X => ValuedPrincipal.exists_val_eq_rat v hπ ((Q α : ℚ) / k)
  have hinv : ∀ α, ((-((Q α : ℚ) / k) : ℚ) : WithTop ℚ) ≤ v (t α)⁻¹ := fun α => by
    obtain ⟨r, hr, hr'⟩ := ValuedPrincipal.exists_val_eq v (ht₀ α)
    rw [ht, WithTop.coe_inj] at hr
    rw [hr', hr]
  choose g hg hg₀ hgν using fun α σ => exists_fam_through hG hϖ D hQ F hv hk α σ
  choose n a σ σF hσ ha hsum using fun x => hS (e x)
  choose l c f f' hf hlin using fun x m => GlobalTheory.T.exists_box_family_power_degree hL hL₂ hL₄ hT V j D.toPre D'.toPre pD k hk (e x) (σ x m)
  let N := Σ x, Σ m : Fin (n x), Fin (l x m)
  let G : N → Fin j → Fam D.toPre F k := fun p i => g (pD.xe (e p.1) i) (f p.1 p.2.1 p.2.2 i (pD.xe (e p.1) i))
  let b : N → F := fun p =>
    a p.1 p.2.1 * algebraMap (FractionRing V) F (algebraMap V (FractionRing V) (c p.1 p.2.1 p.2.2))
  let E := (Fintype.equivFin N).symm
  have hB : ∀ p, IsBoxFam pD F k (bx (G p)) (G p) := fun p => (hbx _ _).2 rfl
  refine ⟨_, fun u => b (E u) * ∏ i, (t (pD.xe (e (E u).1) i))⁻¹,
    fun u i => t (pD.xe (e (E u).1) i) • G (E u) i, fun u => bx fun i => t (pD.xe (e (E u).1) i) • G (E u) i,
    fun u => ?_, fun u i => hgν _ _ _ (ht _).ge, fun u => (hbx _ _).2 rfl, ?_⟩
  · beta_reduce
    generalize E u = p
    obtain ⟨x, m, u⟩ := p
    have h₁ := ha x m
    have h₂ := GC.v_alg_nonneg hϖ hv (c x m u)
    have h₃ := NuBox.le_val_prod v Finset.univ _ _ fun i => hinv (pD.xe (e x) i)
    rw [AddValuation.map_mul, AddValuation.map_mul]
    refine le_trans (le_of_eq ?_) (add_le_add (add_le_add h₁ h₂) h₃)
    rw [add_zero, ← WithTop.coe_add, Finset.sum_neg_distrib, ← Finset.sum_div]
    push_cast
    simp
  · have hE : ∑ u, (b (E u) * ∏ i, (t (pD.xe (e (E u).1) i))⁻¹) •
        (bx fun i => t (pD.xe (e (E u).1) i) • G (E u) i) = ∑ p, b p • bx (G p) := by
      rw [← E.sum_comp]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [bx.map_smul_univ, smul_smul, _root_.mul_assoc, ← Finset.prod_mul_distrib,
        Finset.prod_eq_one fun i _ => inv_mul_cancel₀ (ht₀ _), _root_.mul_one]
    rw [hE, Fintype.sum_sigma]
    refine eq_sum_of_classes hG e he S _ (fun x jj => ?_) (fun x β hβ jj => ?_)
    · rw [hsum x jj, Fintype.sum_sigma, sum_f]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [lin_pull (c x m) (σ x m) (fun u => f' x m u (e x)) (hlin x m) (σF x m)
        (fun u => (bx (G ⟨x, m, u⟩)).s (e x)) (hσ x m)
        (fun u => box_secScal pD (hB ⟨x, m, u⟩) (hf x m u) (e x) fun i => hg _ _) jj, sum_f, Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      simp only [smul_f, b, constBF_eq, resTop, map_mul, _root_.mul_assoc]
    · obtain ⟨i, hi⟩ := exists_comp_off pD k hβ
      rw [sum_f]
      refine Finset.sum_eq_zero fun p _ => ?_
      rw [smul_f, box_zero pD (hB ⟨x, p⟩) β i (hg₀ _ _ _ hi) jj, mul_zero]

end GlobalTheory.UnitBallBox
