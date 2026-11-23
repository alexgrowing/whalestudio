import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionsHaveFiniteDimensionInvarianceIsomorphism
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaSectionsVeryAmplePeriodic
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MemSubringOfLocalInverse
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.VampIsoOfSegreCoordinates
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianVarietyCutOutBoundedDegreeTorsionStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SqIsPowGrp
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionsDimAdditionGraphPrincipalPolarisation

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZV

noncomputable section

namespace GlobalTheory.AddGraph

open GlobalTheory.CechPic

theorem pull_inv_cls {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] (L : LB A.left) (hL : L.IsLB)
    (hs : Out.Sym A L) : pull (GrpObj.inv : A ⟶ A).left (cls L hL) = cls L hL := by
  have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  obtain ⟨U, hU, ht⟩ := hs (default : PrimeSpectrum K)
  obtain rfl : U = ⊤ := eq_top_iff.2 fun q _ => by rw [Subsingleton.elim q (default : PrimeSpectrum K)]; exact hU
  have e := (cls_eq_zero_iff (LB.isLB_linComb hL _ _)).2 ht
  rw [cls_linComb hL, Fin.sum_univ_two] at e
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul, pull_comp] at e
  obtain ⟨ψ, k⟩ : ∃ ψ : A.left ⟶ (A.hom ⁻¹ᵁ ⊤).toScheme, ψ ≫ (A.hom ⁻¹ᵁ ⊤).ι = 𝟙 _ :=
    ⟨A.left.topIso.inv, A.left.topIso.inv_hom_id⟩
  have e' := congrArg (pull ψ) (add_neg_eq_zero.1 e)
  rwa [← pull_comp ψ, ← pull_comp ψ, k, pull_id, pull_id] at e'

theorem pull_inv_hom {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] (f : B ⟶ A)
    (hf : (GrpObj.inv : B ⟶ B) ≫ f = f ≫ (GrpObj.inv : A ⟶ A)) (c : Pic A.left)
    (hc : pull (GrpObj.inv : A ⟶ A).left c = c) :
    pull (GrpObj.inv : B ⟶ B).left (pull f.left c) = pull f.left c := by
  rw [← pull_comp, ← Over.comp_left, hf, Over.comp_left, pull_comp, hc]

theorem lab_add {o : Type} [CommRing o] {S : Scheme.{0}} {g k : ℕ} [NeZero k] {J : Type} {b : TBase o k} {s : S ⟶ Sp o}
    (t : TObj g k J b s) (a a' : Ix g k) : t.lab (a + a') = t.lab a * t.lab a' := by
  haveI := t.ab.comm
  simp only [TObj.lab, Out.linComb, List.prod_ofFn]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← pow_add, Pi.add_apply, ZMod.val_add]
  exact (pow_eq_pow_mod _ (t.torsion i)).symm

def red (g : ℕ) {k k' : ℕ} (h : k' ∣ k) (a : Ix g k) : Ix g k' := fun i => ZMod.castHom h (ZMod k') (a i)

theorem red_surjective (g : ℕ) {k k' : ℕ} (h : k' ∣ k) : Function.Surjective (red g h) := fun a =>
  ⟨fun i => (ZMod.castHom_surjective h (a i)).choose, funext fun i => (ZMod.castHom_surjective h (a i)).choose_spec⟩

theorem modEq_of_red {g k k' : ℕ} [NeZero k] (h : k' ∣ k) {a a' : Ix g k} (e : red g h a = red g h a') (i) :
    (a i).val ≡ (a' i).val [MOD k'] := by
  have := congrFun e i
  simp only [red, ZMod.castHom_apply, ZMod.cast_eq_val] at this
  exact (ZMod.natCast_eq_natCast_iff _ _ _).1 this

theorem square_data {K : Type} [Field K] (P P₂ : Out.PolAV (Sp K)) (e : P₂.A ≅ P.A ⊗ P.A)
    (h₁ : IsMonHom (e.hom ≫ fst P.A P.A)) (h₂ : IsMonHom (e.hom ≫ snd P.A P.A)) (Z : Over (Sp K)) (π : Z ⟶ P.A)
    [IsIso π] (N : ℕ) (M : LB (Z ⊗ Z).left) (hM : M.IsLB)
    (hc : cls M hM = N • pull (fst Z Z ≫ π).left (cls P.L P.isLB) + N • pull (snd Z Z ≫ π).left (cls P.L P.isLB) +
      N • pull ((fst Z Z ≫ π) * (snd Z Z ≫ π)).left (cls P.L P.isLB)) :
    ∃ (E : (Z ⊗ Z).left ≅ P₂.A.left), E.hom ≫ P₂.A.hom = (Z ⊗ Z).hom ∧ SymB (A := P₂.A) (M.pull E.inv) ∧
      (∀ n r, SectionsHaveFiniteDimension (P.A ⊗ P.A).hom (lbPow (LB.LinComb P.L (K := Fin 3) ![(fst P.A P.A).left, (snd P.A P.A).left,
        (fst P.A P.A * snd P.A P.A).left] ![(N : ℤ), (N : ℤ), (N : ℤ)]) n) r → SectionsHaveFiniteDimension (Z ⊗ Z).hom (lbPow M n) r) ∧
      (∀ x y : Out.baseOver (Sp K) ⟶ Z, (lift (x ≫ π) (y ≫ π) ≫ e.inv).left ≫ E.inv = (lift x y).left) ∧
      ∀ (k : ℕ) (I : Type) (u : I → (Out.baseOver (Sp K) ⟶ P.A)), (∀ x, x ^ k = 1 → ∃ i, u i = x) →
        ∀ x : Out.baseOver (Sp K) ⟶ P₂.A, x ^ k = 1 → ∃ i : I × I, lift (u i.1) (u i.2) ≫ e.inv = x := by
  haveI := P.isAb.comm
  let F : Z ⊗ Z ≅ P.A ⊗ P.A := tensorIso (asIso π) (asIso π)
  have F₁ : F.hom ≫ fst _ _ = fst Z Z ≫ π := tensorHom_fst _ _
  have F₂ : F.hom ≫ snd _ _ = snd Z Z ≫ π := tensorHom_snd _ _
  let G : Z ⊗ Z ≅ P₂.A := F ≪≫ e.symm
  have G₁ : G.inv ≫ fst Z Z ≫ π = e.hom ≫ fst _ _ := by
    rw [← F₁]; simp [G]
  have G₂ : G.inv ≫ snd Z Z ≫ π = e.hom ≫ snd _ _ := by
    rw [← F₂]; simp [G]
  have hinv := pull_inv_cls P.A P.L P.isLB P.sym
  refine ⟨(Over.forget _).mapIso G, Over.w G.hom, ?_, fun n r H => ?_, fun x y => ?_,
    fun k I u hu x hx => ?_⟩
  · show LBIso (M.pull G.inv.left) ((M.pull G.inv.left).pull (GrpObj.inv : P₂.A ⟶ P₂.A).left)
    refine (cls_eq_iff (pull_isLB hM _) (pull_isLB (pull_isLB hM _) _)).1 ?_
    rw [cls_pull (pull_isLB hM _), cls_pull hM, hc]
    simp only [map_add, map_nsmul, ← pull_comp G.inv.left, ← Over.comp_left, Hom.mul_def, ← Category.assoc G.inv (lift _ _), comp_lift, G₁, G₂]
    have i₁ : (GrpObj.inv : P₂.A ⟶ P₂.A) ≫ e.hom ≫ fst _ _ = (e.hom ≫ fst _ _) ≫ (GrpObj.inv : P.A ⟶ P.A) :=
      GrpObj.inv_hom _
    have i₂ : (GrpObj.inv : P₂.A ⟶ P₂.A) ≫ e.hom ≫ snd _ _ = (e.hom ≫ snd _ _) ≫ (GrpObj.inv : P.A ⟶ P.A) :=
      GrpObj.inv_hom _
    rw [pull_inv_hom _ i₁ _ hinv, pull_inv_hom _ i₂ _ hinv, pull_inv_hom _ _ _ hinv]
    rw [← Hom.mul_def, MonObj.comp_mul, i₁, i₂, ← Hom.inv_def, ← Hom.inv_def, ← Hom.inv_def, mul_inv]
  · have hN := LB.isLB_linComb P.isLB (K := Fin 3) ![(fst P.A P.A).left, (snd P.A P.A).left,
        (fst P.A P.A * snd P.A P.A).left] ![(N : ℤ), (N : ℤ), (N : ℤ)]
    have hNn := LB.isLB_linComb hN (K := PUnit) (fun _ => 𝟙 _) (fun _ => (n : ℤ))
    have hMn := LB.isLB_linComb hM (K := PUnit) (fun _ => 𝟙 _) (fun _ => (n : ℤ))
    have H' : SectionsHaveFiniteDimension (F.hom.left ≫ (P.A ⊗ P.A).hom) (LB.pull _ F.hom.left) r := ((GlobalTheory.SecDim.lbPow_mul_and_pull_and_sectionsFiniteDim_iso_invariant K _ _ _ hNn).2.2.2.2.2 _ ((Over.forget _).mapIso F) r).1 H
    rw [Over.w F.hom] at H'
    refine ((GlobalTheory.SecDim.lbPow_mul_and_pull_and_sectionsFiniteDim_iso_invariant K _ _ _ (pull_isLB hNn _)).2.1 _ hMn ?_).1 r H'
    refine (cls_eq_iff (pull_isLB hNn _) hMn).1 ?_
    rw [cls_pull hNn, cls_lbPow hN, cls_lbPow hM, hc, cls_linComb P.isLB, Fin.sum_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, natCast_zsmul, map_add, map_nsmul,
      ← pull_comp, ← Over.comp_left, MonObj.comp_mul, F₁, F₂]
  · show (lift (x ≫ π) (y ≫ π) ≫ e.inv).left ≫ G.inv.left = _
    rw [← Over.comp_left]
    congr 1
    simp [G, F]
  · obtain ⟨a₁, ha₁⟩ := hu (x ≫ e.hom ≫ fst _ _) (by rw [← MonObj.pow_comp, hx, MonObj.one_comp])
    obtain ⟨a₂, ha₂⟩ := hu (x ≫ e.hom ≫ snd _ _) (by rw [← MonObj.pow_comp, hx, MonObj.one_comp])
    refine ⟨(a₁, a₂), ?_⟩
    rw [ha₁, ha₂, Iso.comp_inv_eq]
    ext1 <;> simp

end GlobalTheory.AddGraph

open GlobalTheory.AddGraph GlobalTheory.CechPic in

theorem GlobalTheory.cutBy_graph_addition : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)), ∃ (Q : Polynomial ℚ) (d : ℕ), ∀ (K : Type) [Field K] [IsAlgClosed K] (β : o →+* K) (t : TObj g ((n ^ j) ^ 2) J b (spMap β)) σ (p : Ix g ((n ^ j) ^ 2) → Ix g ((n ^ j) ^ 2) → K) (M₂ : LB ((Over.mk (𝟙 (Sp K)) ⊗ t.A) ⊗ (Over.mk (𝟙 (Sp K)) ⊗ t.A)).left) (th₂ : Ix g ((n ^ j) ^ 2) × Ix g ((n ^ j) ^ 2) → M₂.Sec), M₂.IsLB → t.Emb (n ^ 2) (Over.mk (𝟙 _)) σ → (∀ (T : Type) [CommRing T] (x : Sp T ⟶ ((Over.mk (𝟙 (Sp K)) ⊗ t.A) ⊗ (Over.mk (𝟙 (Sp K)) ⊗ t.A)).left) (v₁ v₂ : _ → T), SecCoord _ σ (x ≫ (fst (Over.mk (𝟙 (Sp K)) ⊗ t.A) (Over.mk (𝟙 (Sp K)) ⊗ t.A)).left) v₁ → SecCoord _ σ (x ≫ (snd (Over.mk (𝟙 (Sp K)) ⊗ t.A) (Over.mk (𝟙 (Sp K)) ⊗ t.A)).left) v₂ → SecCoord M₂ th₂ x (fun i => v₁ i.1 * v₂ i.2)) → (∀ h, SecCoord _ σ (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab h ^ n ^ j)).left (p h)) → CutBy (graphIdeal ((Over.mk (𝟙 (Sp K)) ⊗ t.A) ⊗ (Over.mk (𝟙 (Sp K)) ⊗ t.A)).hom M₂ th₂ (𝟙 _) _ σ (lift (toUnit _ ≫ (Over.homMk (𝟙 _) (by simp) : 𝟙_ (Over (Sp K)) ⟶ Over.mk (𝟙 (Sp K)))) ((fst (Over.mk (𝟙 (Sp K)) ⊗ t.A) (Over.mk (𝟙 (Sp K)) ⊗ t.A) ≫ snd _ t.A) * (snd (Over.mk (𝟙 (Sp K)) ⊗ t.A) (Over.mk (𝟙 (Sp K)) ⊗ t.A) ≫ snd _ t.A))).left) Q d (fun (h : Ix g ((n ^ j) ^ 2) × Ix g ((n ^ j) ^ 2)) i => p h.1 i.1.1 * p h.2 i.1.2 * p (h.1 + h.2) i.2) := by
  intro hL hL2 g J _ Mat κ n hn hodd
  have hn1 := hn.one_lt
  haveI : NeZero ((n ^ 2) ^ 2) := ⟨by positivity⟩
  obtain ⟨d, k₀, H⟩ := GlobalTheory.T.abelianVariety_cut_out_bounded_degree_torsion hL hL2 (2 * g) (2 * (n ^ 2) ^ 2)
    ((Ix g ((n ^ 2) ^ 2) × Ix g ((n ^ 2) ^ 2)) × Ix g ((n ^ 2) ^ 2))
  refine ⟨max 2 k₀, fun j hj o _ b => ?_⟩
  haveI : NeZero ((n ^ j) ^ 2) := ⟨by positivity⟩
  have hdiv : n ^ 2 ∣ n ^ j := pow_dvd_pow n (le_of_max_le_left hj)
  have hdiv' : (n ^ 2) ^ 2 ∣ (n ^ j) ^ 2 := pow_dvd_pow_of_dvd hdiv 2
  have hδ : 3 ^ g * ((n ^ 2) ^ 2) ^ (2 * g) ≤ (2 * (n ^ 2) ^ 2) ^ (2 * g) := by
    rw [mul_pow 2, pow_mul 2]
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by norm_num) g)
  obtain ⟨Q, HQ⟩ := H _ hδ ((Ix g ((n ^ j) ^ 2) × Ix g ((n ^ j) ^ 2)) × Ix g ((n ^ j) ^ 2))
    (Prod.map (Prod.map (red g hdiv') (red g hdiv')) (red g hdiv'))
    (((red_surjective g hdiv').prodMap (red_surjective g hdiv')).prodMap (red_surjective g hdiv'))
  refine ⟨Q, d, fun K _ _ β t σ p M₂ th₂ hM₂ hemb hseg hp => ?_⟩
  obtain ⟨hiso, hH, hva, hHiso, hper, -, hlab⟩ := GlobalTheory.embSec_veryAmple_periodic hL hL2 o g (n ^ j) J b K β t (n ^ 2) σ hodd.pow hdiv
    (hn.two_le.trans (Nat.le_self_pow two_ne_zero n)) hemb
  haveI := t.ab.comm
  haveI hπ : IsIso (snd (Over.mk (𝟙 (Sp K))) t.A) := by
    haveI : IsIso ((Over.forget _).map (snd (Over.mk (𝟙 (Sp K))) t.A)) := hiso
    exact isIso_of_reflects_iso _ (Over.forget _)
  have hZ : (fst (Over.mk (𝟙 (Sp K))) t.A).left = ((Over.mk (𝟙 (Sp K))) ⊗ t.A).hom := (Category.comp_id _).symm.trans (Over.w (fst (Over.mk (𝟙 (Sp K))) t.A))
  rw [hZ] at hva
  obtain ⟨hva₂, hiso₂, hper₂⟩ := GlobalTheory.ZV.SegreSquare.vamp_iso_of_segre_coordinates K _ ((Over.mk (𝟙 (Sp K))) ⊗ t.A) _ σ M₂ th₂ hH hM₂ hva hseg
  suffices key : ∀ add : ((Over.mk (𝟙 (Sp K))) ⊗ t.A) ⊗ ((Over.mk (𝟙 (Sp K))) ⊗ t.A) ⟶ (Over.mk (𝟙 (Sp K))) ⊗ t.A, add ≫ snd (Over.mk (𝟙 (Sp K))) t.A =
      (fst ((Over.mk (𝟙 (Sp K))) ⊗ t.A) ((Over.mk (𝟙 (Sp K))) ⊗ t.A) ≫ snd _ t.A) * (snd ((Over.mk (𝟙 (Sp K))) ⊗ t.A) ((Over.mk (𝟙 (Sp K))) ⊗ t.A) ≫ snd _ t.A) →
      CutBy (graphIdeal (((Over.mk (𝟙 (Sp K))) ⊗ t.A) ⊗ ((Over.mk (𝟙 (Sp K))) ⊗ t.A)).hom M₂ th₂ (𝟙 _) _ σ add.left) Q d
        (fun (h : Ix g ((n ^ j) ^ 2) × Ix g ((n ^ j) ^ 2)) i => p h.1 i.1.1 * p h.2 i.1.2 * p (h.1 + h.2) i.2) from
    key _ (lift_snd _ _)
  intro add hadd'
  obtain ⟨M, th, hM, hvaM, hisoM, hI, hco, hperM⟩ := GlobalTheory.ZV.GraphSystem.exists_product_system K _ _ _ _ _ _ _ _ M₂ _ th₂ σ (𝟙 _) add.left hM₂ hH hva₂ hva
    inferInstance (Category.id_comp _) (Over.w add)
  obtain ⟨P₂, e, h₁, h₂, hg, -⟩ := GlobalTheory.SquarePol.exists_square K t.pol
  have cH := (cls_eq_iff hH (pull_isLB (LB.isLB_linComb t.isLB _ _) _)).2 hHiso
  rw [cls_pull (LB.isLB_linComb t.isLB _ _), cls_lbPow t.isLB, map_nsmul] at cH
  have c₂ := (cls_eq_iff hM₂ (LB.isLB_linComb hH _ _)).2 hiso₂
  rw [cls_linComb hH, Fin.sum_univ_two, cH] at c₂
  have cM := (cls_eq_iff (LB.isLB_div hM (pull_isLB hM₂ _)) (pull_isLB hH _)).2 hisoM
  rw [cls_div hM (pull_isLB hM₂ _), cls_pull hM₂, cls_pull hH, pull_id, sub_eq_iff_eq_add', c₂, cH] at cM
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, map_nsmul, ← pull_comp, ← Over.comp_left, hadd'] at cM
  obtain ⟨E, hE, hsym, hH0, hpt, htor⟩ := @square_data K _ t.pol P₂ e h₁ h₂ ((Over.mk (𝟙 (Sp K))) ⊗ t.A) (snd (Over.mk (𝟙 (Sp K))) t.A) hπ ((n ^ 2) ^ 2) M hM cM
  rw [hI, ← hE]
  refine HQ K P₂ hg _ E M th (n ^ j) _ (fun h => lift (t.lab h.1 ^ n ^ j) (t.lab h.2 ^ n ^ j) ≫ e.inv) _ hM hsym
    (hE ▸ hvaM) (fun a a' haa => ?_) (fun m hm => ?_) ((le_of_max_le_right hj).trans (Nat.lt_pow_self hn1).le) ?_
    (htor _ _ (fun h => t.lab h ^ n ^ j) hlab) (fun h => ?_)
  · have e₁ := congrArg (fun z => z.1.1) haa
    have e₂ := congrArg (fun z => z.1.2) haa
    have e₃ := congrArg (fun z => z.2) haa
    exact hperM a a' (hper₂ _ _ (hper _ _ (modEq_of_red hdiv' e₁)) (hper _ _ (modEq_of_red hdiv' e₂)))
      (hper _ _ (modEq_of_red hdiv' e₃))
  · rw [hE, Nat.mul_assoc, ← mul_pow]
    exact hH0 m _ (GlobalTheory.sectionsDim_additionGraph_principalPolarisation hL hL2 K t.pol _ (Nat.one_le_iff_ne_zero.2 (NeZero.ne _)) m hm)
  · have u := (b.unit.map β).ne_zero
    rw [map_natCast, Nat.cast_pow] at u
    exact ne_zero_pow two_ne_zero u
  · have k : (lift (t.lab h.1 ^ n ^ j) (t.lab h.2 ^ n ^ j) ≫ e.inv).left ≫ E.inv =
        (lift (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab h.1 ^ n ^ j)) (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab h.2 ^ n ^ j))).left := by
      refine Eq.trans ?_ (hpt _ _)
      exact congrArg (fun z => (z ≫ e.inv).left ≫ E.inv) (congrArg₂ lift (lift_snd _ _).symm (lift_snd _ _).symm)
    refine k ▸ hco K _ (fun i => p h.1 i.1 * p h.2 i.2) (p (h.1 + h.2)) (hseg K _ _ _ ?_ ?_) ?_
    · rw [Category.comp_id, ← Over.comp_left, lift_fst]; exact hp _
    · rw [Category.comp_id, ← Over.comp_left, lift_snd]; exact hp _
    · have : lift (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab h.1 ^ n ^ j)) (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab h.2 ^ n ^ j)) ≫ add =
          lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab (h.1 + h.2) ^ n ^ j) := by
        rw [← cancel_mono (snd (Over.mk (𝟙 (Sp K))) t.A), Category.assoc, hadd', MonObj.comp_mul, lab_add, mul_pow]
        simp
      rw [← Over.comp_left, this]; exact hp _
