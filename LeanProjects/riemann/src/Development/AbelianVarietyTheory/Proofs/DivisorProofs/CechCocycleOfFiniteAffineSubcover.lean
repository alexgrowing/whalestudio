import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechGluingOfKodairaSpencerRelation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheaf
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RhoIsCoc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardNonempty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPullOneBijectiveLatticeCoverStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechFin

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechFin

variable {Z : Scheme.{0}}

theorem sf_resG_resG {U V V' : Z.Opens} (h : V ≤ U) (h' : V' ≤ V) (x : Γ(Z, U)) :
    resG Z h' (resG Z h x) = resG Z (h'.trans h) x :=
  (congrArg (fun q => q.hom x) (Z.presheaf.map_comp (homOfLE h).op (homOfLE h').op)).symm

theorem sf_resG_id {U : Z.Opens} (h : U ≤ U) (x : Γ(Z, U)) : resG Z h x = x :=
  congrArg (fun q => q.hom x) (Z.presheaf.map_id (Opposite.op U))

theorem sf_resG_inj {U V : Z.Opens} (h : V ≤ U) (h' : U ≤ V) {x y : Γ(Z, U)}
    (e : resG Z h x = resG Z h y) : x = y := by
  have := congrArg (resG Z h') e
  rwa [sf_resG_resG, sf_resG_resG, sf_resG_id, sf_resG_id] at this

variable {J : Type} (W : J → Z.Opens) (c : ∀ i i' : J, Γ(Z, W i ⊓ W i'))

def sfCr (U : Z.Opens) (i i' : J) (h : U ≤ W i ⊓ W i') : Γ(Z, U) := resG Z h (c i i')

theorem sfCr_res {U V : Z.Opens} (i i' : J) (h : U ≤ W i ⊓ W i') (h' : V ≤ U) :
    resG Z h' (sfCr W c U i i' h) = sfCr W c V i i' (h'.trans h) :=
  sf_resG_resG _ _ _

theorem sfCr_add (hc : IsCoc W c) (U : Z.Opens) (i i' i'' : J) (h : U ≤ W i ⊓ W i' ⊓ W i'') :
    sfCr W c U i i' (h.trans inf_le_left) +
      sfCr W c U i' i'' (h.trans (le_inf (inf_le_left.trans inf_le_right) inf_le_right)) =
      sfCr W c U i i'' (h.trans (le_inf (inf_le_left.trans inf_le_left) inf_le_right)) := by
  have e := congrArg (resG Z h) (hc i i' i'')
  rw [map_add, sf_resG_resG, sf_resG_resG, sf_resG_resG] at e
  exact e

theorem sfCr_self (hc : IsCoc W c) (U : Z.Opens) (i : J) (h : U ≤ W i ⊓ W i) :
    sfCr W c U i i h = 0 := by
  have e := sfCr_add W c hc U i i i (le_inf h (h.trans inf_le_left))
  have e2 : sfCr W c U i i h + sfCr W c U i i h = sfCr W c U i i h := e
  linear_combination e2

theorem sfCr_congr (U : Z.Opens) {i j i' : J} (e : i = j) (h : U ≤ W i ⊓ W i') (h' : U ≤ W j ⊓ W i') :
    sfCr W c U i i' h = sfCr W c U j i' h' := by subst e; rfl

theorem sfCr_congr2 (U : Z.Opens) {i i' j' : J} (e : i' = j') (h : U ≤ W i ⊓ W i') (h' : U ≤ W i ⊓ W j') :
    sfCr W c U i i' h = sfCr W c U i j' h' := by subst e; rfl

variable {R : Type} [CommRing R] (s : Z ⟶ Sp R)

theorem cechAffineCochainValue_congr_source (f : C1 (OAff s)) {A A' B : Z.affineOpens} (e : A = A') (h : B.1 ≤ A.1) (h' : B.1 ≤ A'.1) :
    fv s f h = fv s f h' := by subst e; rfl

end GlobalTheory.CechFin

open GlobalTheory.CechPoset in

theorem GlobalTheory.CechFin.cocycle_of_finite_affine_subcover : ∀ (R : Type) [CommRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R) (J : Type) (W : J → Z.Opens) (hW : ∀ i, IsAffineOpen (W i)) (hW2 : ∀ i i', IsAffineOpen (W i ⊓ W i')), (∀ I : Finset J, I.Nonempty → IsAffineOpen (⨅ i ∈ I, W i)) → ∀ S : Finset J, ⨆ i ∈ S, W i = ⊤ → ∀ c : ∀ i i' : J, Γ(Z, W i ⊓ W i'), IsCoc W c → ∃ (f : Z1 (OAff s)) (h : ∀ i, Γ(Z, W i)), ∀ i ∈ S, ∀ i' ∈ S, c i i' = rho W s hW hW2 f.1 i i' + (resG Z inf_le_left (h i) - resG Z inf_le_right (h i')) := by
  intro R _ Z s J W hW hW2 hI S hS c hc
  let κ := {j // j ∈ S}
  letI : LinearOrder κ := LinearOrder.lift' (Fintype.equivFin κ) (Fintype.equivFin κ).injective
  let D : κ → Z.Opens := fun k => W k.1
  have hD : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ k ∈ I, D k) := by
    classical
    intro I hIn
    have := hI (I.image Subtype.val) (hIn.image _)
    rwa [Finset.iInf_finset_image] at this
  have hcov : ⨆ k, D k = ⊤ := by
    rw [← hS, iSup_subtype']
  have hinf : ∀ a b : NE κ, (cov D hD (a ⊓ b)).1 = (cov D hD a).1 ⊓ (cov D hD b).1 :=
    fun a b => Finset.iInf_union
  have hsup : ⨆ a, (cov D hD a).1 = ⊤ := by
    refine eq_top_iff.2 (hcov.symm.le.trans (iSup_le fun k => ?_))
    refine le_trans (le_of_eq ?_) (le_iSup (fun a => (cov D hD a).1)
      (OrderDual.toDual ⟨{k}, Finset.singleton_nonempty k⟩))
    simp [cov]
  have hmem : ∀ (a : (NE κ)ᵒᵖ) (k : κ), k ∈ sub a → (cov D hD a.unop).1 ≤ W k.1 :=
    fun a k hk => biInf_le (fun k => D k) hk
  let Fv : C1 (covF s D hD) := fun a b φ =>
    sfCr W c (cov D hD b.unop).1 (mn b).1 (mn a).1
      (le_inf (hmem b _ (mn_mem b)) (hmem b _ (sub_subset φ (mn_mem a))))
  have hF : Fv ∈ Z1 (covF s D hD) := by
    intro a b d φ ψ
    have e := sfCr_add W c hc (cov D hD d.unop).1 (mn d).1 (mn b).1 (mn a).1
      (le_inf (le_inf (hmem d _ (mn_mem d)) (hmem d _ (sub_subset ψ (mn_mem b))))
        (hmem d _ (sub_subset ψ (sub_subset φ (mn_mem a)))))
    show sfCr W c (cov D hD d.unop).1 (mn d).1 (mn a).1 _ =
      resG Z (cov_mono D hD (leOfHom ψ.unop)) (sfCr W c (cov D hD b.unop).1 (mn b).1 (mn a).1 _) +
        sfCr W c (cov D hD d.unop).1 (mn d).1 (mn b).1 _
    rw [sfCr_res]
    rw [add_comm]
    exact e.symm
  obtain ⟨y, hy⟩ := (GlobalTheory.T.cech_pull_one_bijective_lattice_cover R Z s (NE κ) (cov D hD) (cov_mono D hD) hinf hsup).2
    (H1.mk _ ⟨Fv, hF⟩)
  obtain ⟨f0, rfl⟩ := H1.mk_surjective _ y
  rw [CoefMap.pullCohomologyOne_class, H1.mk_eq_mk] at hy
  obtain ⟨g, hg⟩ := hy

  let hfun : ∀ i, Γ(Z, W i) := fun i => @dite _ (i ∈ S) (Classical.propDecidable _) (fun hi =>
      -resG Z (le_of_eq (Finset.iInf_singleton (⟨i, hi⟩ : κ) D).symm :
        W i ≤ (cov D hD (ne {(⟨i, hi⟩ : κ)} (Finset.singleton_nonempty _)).unop).1)
        (g (ne {(⟨i, hi⟩ : κ)} (Finset.singleton_nonempty _)))) (fun _ => 0)
  refine ⟨-f0, hfun, fun i hi i' hi' => ?_⟩
  let k : κ := ⟨i, hi⟩
  let k' : κ := ⟨i', hi'⟩
  let a := ne {k} (Finset.singleton_nonempty k)
  let a' := ne {k'} (Finset.singleton_nonempty k')
  let b := ne {k, k'} (Finset.insert_nonempty k {k'})
  have ca : (cov D hD a.unop).1 = W i := Finset.iInf_singleton k D
  have ca' : (cov D hD a'.unop).1 = W i' := Finset.iInf_singleton k' D
  have cb : (cov D hD b.unop).1 = W i ⊓ W i' := by
    show (⨅ j ∈ ({k, k'} : Finset κ), D j) = _
    rw [Finset.iInf_insert, Finset.iInf_singleton]
  let φ : a ⟶ b := homOf (Finset.singleton_subset_iff.2 (Finset.mem_insert_self k {k'}))
  let φ' : a' ⟶ b := homOf (Finset.singleton_subset_iff.2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self k')))
  have hab : (cov D hD b.unop).1 ≤ (cov D hD a.unop).1 := cov_mono D hD (leOfHom φ.unop)
  have ha'b : (cov D hD b.unop).1 ≤ (cov D hD a'.unop).1 := cov_mono D hD (leOfHom φ'.unop)
  have hBP : (cov D hD b.unop).1 ≤ W i ⊓ W i' := cb.le
  have hPB : W i ⊓ W i' ≤ (cov D hD b.unop).1 := cb.ge
  have mna : mn a = k := Finset.min'_singleton k
  have mna' : mn a' = k' := Finset.min'_singleton k'
  have hxB : (cov D hD b.unop).1 ≤ W (mn b).1 := hmem b _ (mn_mem b)
  have h4 := congrFun (congrFun (congrFun hg a) b) φ
  have h5 := congrFun (congrFun (congrFun hg a') b) φ'
  have h4' : (show Γ(Z, (cov D hD b.unop).1) from g b) - resG Z hab (g a) = fv s f0.1 (A := cov D hD a.unop) (B := cov D hD b.unop) hab -
      sfCr W c (cov D hD b.unop).1 (mn b).1 i (le_inf hxB (hBP.trans inf_le_left)) := by
    rw [← sfCr_congr2 W c _ (congrArg Subtype.val mna) (le_inf hxB (hab.trans (hmem a _ (mn_mem a))))]
    exact h4
  have h5' : (show Γ(Z, (cov D hD b.unop).1) from g b) - resG Z ha'b (g a') = fv s f0.1 (A := cov D hD a'.unop) (B := cov D hD b.unop) ha'b -
      sfCr W c (cov D hD b.unop).1 (mn b).1 i' (le_inf hxB (hBP.trans inf_le_right)) := by
    rw [← sfCr_congr2 W c _ (congrArg Subtype.val mna') (le_inf hxB (ha'b.trans (hmem a' _ (mn_mem a'))))]
    exact h5
  have c1 := sfCr_add W c hc (cov D hD b.unop).1 i (mn b).1 i'
    (le_inf (le_inf (hBP.trans inf_le_left) hxB) (hBP.trans inf_le_right))
  have c2 := sfCr_add W c hc (cov D hD b.unop).1 (mn b).1 i (mn b).1
    (le_inf (le_inf hxB (hBP.trans inf_le_left)) hxB)
  rw [sfCr_self W c hc] at c2
  have r1 := res_val s f0 (A := ⟨W i, hW i⟩) (B := ⟨W i ⊓ W i', hW2 i i'⟩) (C := cov D hD b.unop)
    inf_le_left hBP
  have r2 := res_val s f0 (A := ⟨W i', hW i'⟩) (B := ⟨W i ⊓ W i', hW2 i i'⟩) (C := cov D hD b.unop)
    inf_le_right hBP
  rw [cechAffineCochainValue_congr_source s f0.1 (Subtype.ext ca.symm) _ hab] at r1
  rw [cechAffineCochainValue_congr_source s f0.1 (Subtype.ext ca'.symm) _ ha'b] at r2
  have erho : resG Z hBP (rho W s hW hW2 (-f0).1 i i') =
      -resG Z hBP (fv s f0.1 (A := ⟨W i, hW i⟩) (B := ⟨W i ⊓ W i', hW2 i i'⟩) inf_le_left) +
        resG Z hBP (fv s f0.1 (A := ⟨W i', hW i'⟩) (B := ⟨W i ⊓ W i', hW2 i i'⟩) inf_le_right) := by
    show resG Z hBP (-fv s f0.1 (A := ⟨W i, hW i⟩) (B := ⟨W i ⊓ W i', hW2 i i'⟩) inf_le_left -
      -fv s f0.1 (A := ⟨W i', hW i'⟩) (B := ⟨W i ⊓ W i', hW2 i i'⟩) inf_le_right) = _
    rw [map_sub, map_neg, map_neg]; ring
  have e0 : resG Z hBP (c i i') = sfCr W c (cov D hD b.unop).1 i i' hBP := rfl
  have t1 : resG Z hBP (resG Z inf_le_left (hfun i)) = -resG Z hab (g a) := by
    simp only [hfun, @dif_pos _ (Classical.propDecidable _) hi]
    rw [map_neg, map_neg]
    exact congrArg Neg.neg ((sf_resG_resG _ _ _).trans (sf_resG_resG _ _ _))
  have t2 : resG Z hBP (resG Z inf_le_right (hfun i')) = -resG Z ha'b (g a') := by
    simp only [hfun, @dif_pos _ (Classical.propDecidable _) hi']
    rw [map_neg, map_neg]
    exact congrArg Neg.neg ((sf_resG_resG _ _ _).trans (sf_resG_resG _ _ _))
  rw [r1, r2] at erho
  apply sf_resG_inj hBP hPB
  rw [map_add, map_sub, t1, t2]
  linear_combination e0 - erho - h4' + h5' - c1 + c2
