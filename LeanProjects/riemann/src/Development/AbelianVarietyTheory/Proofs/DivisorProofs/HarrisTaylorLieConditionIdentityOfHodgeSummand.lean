import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieRankAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFirstDeRhamStructureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRelDimOfIsSemiAbelian
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTLieCrys

theorem isLieImage_sum {C : Type} [CommRing C] {A : Over (Sp C)} [GrpObj A] :
    ∀ (n : ℕ) (H : Fin n → HdR A) (u : Fin n → (epsR C ⟶ A)), (∀ i, IsLieImage (H i) (u i)) →
      IsLieImage (∑ i, H i) (List.ofFn u).prod
  | 0, H, u, _ => by
      simpa using (isLieImage_one_iff (A := A)).2 (zero_mem _)
  | n + 1, H, u, hu => by
      rw [Fin.sum_univ_succ, List.ofFn_succ, List.prod_cons]
      exact (hu 0).add (isLieImage_sum n _ _ fun i => hu i.succ)

theorem comp_listProd {𝒞 : Type*} [Category 𝒞] [CartesianMonoidalCategory 𝒞] {M X Y : 𝒞} [MonObj M]
    (f : X ⟶ Y) : ∀ (n : ℕ) (u : Fin n → (Y ⟶ M)),
      f ≫ (List.ofFn u).prod = (List.ofFn fun i => f ≫ u i).prod
  | 0, u => by simp
  | n + 1, u => by
      rw [List.ofFn_succ, List.prod_cons, MonObj.comp_mul, comp_listProd f n, List.ofFn_succ,
        List.prod_cons]

theorem one_left_eq {C : Type} [CommRing C] (A : Over (Sp C)) [GrpObj A] (x : Sp C ⟶ Sp C) (hx : x = 𝟙 (Sp C)) :
    (1 : Over.mk x ⟶ A).left = η[A].left := by
  have w := Over.w (toUnit (Over.mk x))
  rw [Hom.one_def, Over.comp_left]
  have e1 : (toUnit (Over.mk x)).left = x := by
    simpa using w
  rw [e1, hx]
  exact Category.id_comp _

def overId {P S : Scheme.{0}} (q q' : P ⟶ S) (h : q' = q) : Over.mk q ⟶ Over.mk q' :=
  Over.homMk (𝟙 P) ((Category.id_comp q').trans h)

theorem overId_rfl {P S : Scheme.{0}} (q : P ⟶ S) : overId q q rfl = 𝟙 _ :=
  Over.OverMorphism.ext rfl

theorem overId_comp {P S : Scheme.{0}} (q q' : P ⟶ S) (h : q' = q) (h' : q = q') :
    overId q' q h' ≫ overId q q' h = 𝟙 _ := by
  subst h
  rw [overId_rfl, Category.id_comp]

theorem overId_comp_left {T P S : Scheme.{0}} (q q' : P ⟶ S) (h : q' = q) {A : Over S}
    (f : Over.mk q' ⟶ A) (a : T ⟶ P) (b : T ⟶ A.left) (e : a ≫ f.left = b) :
    a ≫ (overId q q' h ≫ f).left = b := by
  subst h
  rw [overId_rfl, Category.id_comp]
  exact e

theorem overId_scal {P S : Scheme.{0}} (q q' : P ⟶ S) (h : q' = q) {A : Over S}
    (f : Over.mk q' ⟶ A) (g : A ⟶ A) (a : P ⟶ P) (e : Over.mk q ⟶ Over.mk q) (he : e.left = a)
    (hf : (f ≫ g).left = a ≫ f.left) : (overId q q' h ≫ f) ≫ g = e ≫ overId q q' h ≫ f := by
  subst h
  subst he
  rw [overId_rfl, Category.id_comp]
  exact Over.OverMorphism.ext hf

theorem overId_scal_left {P S : Scheme.{0}} (q q' : P ⟶ S) (h : q' = q) {A : Over S}
    (f : Over.mk q' ⟶ A) (g : A ⟶ A) (a : P ⟶ P) (e : Over.mk q' ⟶ Over.mk q') (he : e.left = a)
    (hf : f ≫ g = e ≫ f) : ((overId q q' h ≫ f) ≫ g).left = a ≫ (overId q q' h ≫ f).left := by
  subst h
  subst he
  rw [overId_rfl, Category.id_comp, hf]
  rfl

theorem epsPt_hq (C : Type) [CommRing C] :
    spMap (algebraMap C (DualNumber C)) ≫ spMap (RingHom.id C) = spMap (algebraMap C (DualNumber C)) := by
  rw [show spMap (RingHom.id C) = 𝟙 (Sp C) from Spec.map_id _, Category.comp_id]

theorem lieAt_id_of_liftFil : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (o₀ : GlobalTheory.UPel.HT.Obj b N (spMap π ≫ spMap tR)), ∀ (A : Over (Sp C)) [GrpObj A] [IsCommMonObj A] (i : o₀.A.left ⟶ A.left) (h : IsGrpPullback o₀.A A (spMap π) i), IsAbelianScheme A → ∀ (act : GlobalTheory.UPel.HT.OActN D.O A), (∀ c, (o₀.act.act c).left ≫ i = i ≫ (act.act c).left) → (∀ d : Crys (divided₂ hsq) (spMap π) o₀.A, (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O D.ω); push (divided₂ hsq) (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O D.ω)) (d)) - tR b.ρ • d ∈ liftFil (divided₂ hsq) h → ∃ w : Fin D.a → Crys (divided₂ hsq) (spMap π) o₀.A, (∀ i (c : 𝓞 D.F), (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O c); push (divided₂ hsq) (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O c)) (w i)) - tR (b.t i c) • w i ∈ liftFil (divided₂ hsq) h) ∧ d - ∑ i, w i ∈ liftFil (divided₂ hsq) h) → GlobalTheory.UPel.HT.LieAt b act tR (spMap (RingHom.id C)) := by
  intro p _ D R _ b N C C₀ _ _ _ _ π hπ hsq tR o₀ A _ _ i h hA act hact hyp
  obtain ⟨g, hg⟩ := GlobalTheory.SemiAbelianDim.exists_relDim_of_isSemiAbelian C A
    (GlobalTheory.isSemiAbelian_of_isAbelianScheme A hA)
  have ADR := GlobalTheory.T.abelianScheme_firstDeRham_structure
  obtain ⟨LE1, LE2⟩ : LieExact A := (ADR.2.1 C A g hA hg).1
  have bij : Function.Bijective (crysToDR (divided₂ hsq) h) :=
    GlobalTheory.Published.AbelianDeRham.Rigid.crysToDR_bijective ADR.2.2.2.1 hA hg (isDPNilpotent_squareZero hsq) hπ rfl h
  have eqv : ∀ (c : D.O) (d : Crys (divided₂ hsq) (spMap π) o₀.A),
      (haveI := o₀.act.hom c; crysToDR (divided₂ hsq) h (push (divided₂ hsq) (spMap π) (o₀.act.act c) d)) =
      (haveI := act.hom c; push (dp0 C) (𝟙 _) (act.act c) (crysToDR (divided₂ hsq) h d)) := by
    intro c d
    haveI := o₀.act.hom c
    haveI := act.hom c
    exact crysToDR_push (divided₂ hsq) h h (o₀.act.act c) (act.act c) (hact c).symm d
  have hq := epsPt_hq C
  have one_left := one_left_eq A (spMap (RingHom.id C)) (Spec.map_id _)
  intro v hv
  obtain ⟨hv1, hv2⟩ := hv
  let v' : epsR C ⟶ A := overId _ _ hq ≫ v
  have tan' : IsTangent v' := overId_comp_left _ _ hq v _ _ (hv1.trans one_left)
  obtain ⟨H0, hH0⟩ := LE2 v' tan'
  obtain ⟨d, rfl⟩ := bij.2 H0
  have scal : v' ≫ act.act (algebraMap (𝓞 D.F) D.O D.ω) = GlobalTheory.GrpTangent.epsScale (tR b.ρ) ≫ v' :=
    overId_scal _ _ hq v _ _ _ (GlobalTheory.GrpTangent.epsScale_left _) hv2
  have hmem : (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O D.ω);
      push (divided₂ hsq) (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O D.ω)) d) - tR b.ρ • d ∈
      liftFil (divided₂ hsq) h := by
    haveI := act.hom (algebraMap (𝓞 D.F) D.O D.ω)
    rw [liftFil, Submodule.mem_comap, map_sub, map_smul, eqv]
    have h1 := hH0.push (act.act (algebraMap (𝓞 D.F) D.O D.ω))
    rw [scal] at h1
    exact h1.sub_mem (hH0.smul (tR b.ρ))
  obtain ⟨w, hw, hsum⟩ := hyp d hmem
  have ex : ∀ j, ∃ u : epsR C ⟶ A, IsLieImage (crysToDR (divided₂ hsq) h (w j)) u :=
    fun j => (LE1 _).exists
  choose u hu using ex
  have hu_scal : ∀ j (c : 𝓞 D.F), u j ≫ act.act (algebraMap (𝓞 D.F) D.O c) =
      GlobalTheory.GrpTangent.epsScale (tR (b.t j c)) ≫ u j := by
    intro j c
    haveI := act.hom (algebraMap (𝓞 D.F) D.O c)
    have m := hw j c
    rw [liftFil, Submodule.mem_comap, map_sub, map_smul, eqv] at m
    have k2 := ((hu j).smul (tR (b.t j c))).add (isLieImage_one_iff.2 m)
    rw [_root_.mul_one, add_sub_cancel] at k2
    exact (LE1 _).unique ((hu j).push _) k2
  have hprod : v' = (List.ofFn u).prod := by
    rw [liftFil, Submodule.mem_comap, map_sub, map_sum] at hsum
    have k2 := (isLieImage_sum _ _ _ hu).add (isLieImage_one_iff.2 hsum)
    rw [_root_.mul_one, add_sub_cancel] at k2
    exact (LE1 _).unique hH0 k2
  refine ⟨fun j => overId _ _ hq.symm ≫ u j, fun j c => ⟨?_, ?_⟩, ?_⟩
  · exact overId_comp_left _ _ hq.symm (u j) _ _ (Eq.trans (hu j).1 one_left.symm)
  · exact overId_scal_left _ _ hq.symm (u j) _ _ _ (GlobalTheory.GrpTangent.epsScale_left _) (hu_scal j c)
  · have e1 : v = overId _ _ hq.symm ≫ v' := by
      show v = overId _ _ hq.symm ≫ (overId _ _ hq ≫ v)
      rw [← Category.assoc, overId_comp, Category.id_comp]
    rw [e1, hprod, comp_listProd]
end GlobalTheory.HTLieCrys
