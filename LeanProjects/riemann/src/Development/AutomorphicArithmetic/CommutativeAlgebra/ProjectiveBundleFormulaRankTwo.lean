import Development.AutomorphicArithmetic.CommutativeAlgebra.TateTwistAffineLineProjectionEquiv
import Development.AutomorphicArithmetic.CommutativeAlgebra.BijectiveCohomologyGmProductKummerCup
import Development.AutomorphicArithmetic.CommutativeAlgebra.ProjectiveBundleFormulaRankOneOfHomotopyInvarian
import Development.AutomorphicArithmetic.CommutativeAlgebra.MayerVietorisConnectingExistsUniqueAdditiveExact
import Development.AutomorphicArithmetic.CommutativeAlgebra.MayerVietorisConnectingCupPullback
import Development.AutomorphicArithmetic.CommutativeAlgebra.FirstChernClassEqZeroOfIsTrivialized
import Development.AutomorphicArithmetic.CommutativeAlgebra.KummerCocycleMayerVietorisOfCover
import Development.AutomorphicArithmetic.CupPullbacks.ConstCompSingle
import Development.AutomorphicArithmetic.CupPullbacks.TwoCore
import Development.AutomorphicArithmetic.CupPullbacks.TwoChart
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf

namespace UpperTheory.P2
variable {q : ℕ} [NeZero q]

private theorem inv_of_map {Y E : Spc} (f : Y ⟶ E) (hE : Inv q E) : Inv q Y :=
  fun U ⟨y⟩ => hE U ⟨y.map f⟩

private theorem eqv_iso {R : Type} [CommRing R] {A B : Spc} (f : A ⟶ B) [IsIso f] (F : Shv R) : Eqv R f F := by
  intro n
  constructor
  · intro a b h
    have := congrArg (pull R (inv f) F n) h
    rwa [← pull_comp, ← pull_comp, IsIso.inv_hom_id, pull_id, pull_id] at this
  · intro x
    refine ⟨pull R (inv f) F n x, ?_⟩
    rw [← pull_comp, IsIso.hom_inv_id, pull_id]

private theorem eqv_comp {R : Type} [CommRing R] {A B C : Spc} {f : A ⟶ B} {g : B ⟶ C} {F : Shv R} (hf : Eqv R f F) (hg : Eqv R g F) :
    Eqv R (f ≫ g) F := by
  intro n
  have := (hf n).comp (hg n)
  convert this using 1
  funext x
  exact pull_comp R f g F n x

private theorem cover_comp {R : Type} [CommRing R] {U V E E' : Spc} {f : U ⟶ E} {g : V ⟶ E} (h : E ⟶ E') [IsIso h]
    (hc : Cover2 R f g) : Cover2 R (f ≫ h) (g ≫ h) := by
  obtain ⟨m1, m2, he⟩ := hc
  refine ⟨mono_comp _ _, mono_comp _ _, fun n => ?_⟩
  have := he n
  have e : biprod.desc ((free R).map ((f ≫ h).app n)) ((free R).map ((g ≫ h).app n)) =
      biprod.desc ((free R).map (f.app n)) ((free R).map (g.app n)) ≫ (free R).map (h.app n) := by
    have e1 : (f ≫ h).app n = f.app n ≫ h.app n := rfl
    have e2 : (g ≫ h).app n = g.app n ≫ h.app n := rfl
    rw [e1, e2, Functor.map_comp, Functor.map_comp]
    exact biprod.hom_ext' _ _ (by simp) (by simp)
  rw [e]
  exact epi_comp _ _

private theorem eqv_fst {Y : Spc} (hY : Inv q Y) (i : ℤ) : Eqv _ (prod.fst : Y ⨯ Dv 1 ⟶ Y) (tw q i) := by
  have hP := tri_pullback Y 1
  have e : (prod.fst : Y ⨯ Dv 1 ⟶ Y) = hP.isoPullback.hom ≫ pullback.fst (triv Y 1) (PGL.pr 1) := by
    rw [IsPullback.isoPullback_hom_fst]
  rw [e]
  refine eqv_comp (eqv_iso _ _) ?_
  have hX : Inv q (pullback (triv Y 1) (PGL.pr 1)) := inv_of_map (pullback.fst _ _) hY
  set π := pullback.fst (triv Y 1) (PGL.pr 1)
  set ξ := c1 q (pullback.snd (triv Y 1) (PGL.pr 1) ≫ PGL.line 1)
  intro n
  have h : Function.Bijective _ := UpperTheory.projectiveBundleFormula_rank_one_of_homotopyInvariant q Y hY n i
  have h0 : ∀ j : Fin 1, n - 2 * (((j : ℕ) : ℤ)) = n := by
    intro j
    obtain rfl : j = 0 := Subsingleton.elim _ _
    simp
  have h1 : ∀ j : Fin 1, i - (((j : ℕ) : ℤ)) = i := by
    intro j
    obtain rfl : j = 0 := Subsingleton.elim _ _
    simp
  have ev : ∀ a : ∀ j : Fin 1, Ht q Y (n - 2 * (((j : ℕ) : ℤ))) (i - (((j : ℕ) : ℤ))),
      ∑ j : Fin 1, ((cup q (pull _ π _ _ (a j)) (cpow q ξ j)).cast (by ring) (by ring) : Ht q _ n i) =
        pull _ π _ _ ((a 0).cast (h0 0) (h1 0)) := by
    intro a
    rw [Fin.sum_univ_one]
    exact term0 hX π ξ _ (by simp) (a 0) _ _ _ _
  constructor
  · intro a b hab
    have := h.1 (a₁ := fun j => Ht.cast (h0 j).symm (h1 j).symm a) (a₂ := fun j => Ht.cast (h0 j).symm (h1 j).symm b) (by
      simp only
      rw [ev, ev, cast_cast, cast_cast]
      exact hab)
    exact cast_inj _ _ (congrFun this 0)
  · intro y
    obtain ⟨a, ha⟩ := h.2 y
    exact ⟨_, (ev a).symm.trans ha⟩

private theorem kun {E : Spc} (hE : Inv q E) (m j : ℤ) :
    Function.Bijective fun p : Ht q E (m + 1) (j + 1) × Ht q E m j =>
      pull _ (prod.snd : sch.obj (Gq q) ⨯ E ⟶ E) _ _ p.1 +
        cup q (pull _ (prod.snd : sch.obj (Gq q) ⨯ E ⟶ E) _ _ p.2) (pull _ (prod.fst : sch.obj (Gq q) ⨯ E ⟶ _) _ _ (kappa q)) := by
  have key : ∀ (n i m j : ℤ) (hm : n - 1 = m) (hj : i - 1 = j) (h : m + 1 = n) (h' : j + 1 = i),
      Function.Bijective fun p : Ht q E n i × Ht q E m j =>
        pull _ (prod.snd : sch.obj (Gq q) ⨯ E ⟶ E) _ _ p.1 +
          (cup q (pull _ (prod.snd : sch.obj (Gq q) ⨯ E ⟶ E) _ _ p.2)
            (pull _ (prod.fst : sch.obj (Gq q) ⨯ E ⟶ _) _ _ (kappa q))).cast h h' := by
    intro n i m j hm hj h h'
    subst hm hj
    exact UpperTheory.bijective_cohomology_gm_product_kummer_cup q E hE n i
  exact key (m + 1) (j + 1) m j (by ring) (by ring) rfl rfl

end UpperTheory.P2

open UpperTheory.P2 in
theorem UpperTheory.projectiveBundleFormula_rank_two :
    ∀ (q : ℕ) [NeZero q] (E : Spc), Inv q E → PBF q E 2 := by
  intro q _ E hE
  have hP := tri_pullback E 2
  set θ := hP.isoPullback with hθ
  set π := pullback.fst (triv E 2) (PGL.pr 2) with hπ
  set L := pullback.snd (triv E 2) (PGL.pr 2) ≫ PGL.line 2 with hL
  have hX : Inv q (pullback (triv E 2) (PGL.pr 2)) := inv_of_map π hE
  have hθπ : θ.hom ≫ π = prod.fst := hP.isoPullback_hom_fst
  have hθs : θ.hom ≫ pullback.snd (triv E 2) (PGL.pr 2) = prod.snd ≫ Dv.toPGL 2 := hP.isoPullback_hom_snd
  let f : Fin 2 → (WS E A1 ⟶ pullback (triv E 2) (PGL.pr 2)) := fun b => gch b ≫ θ.hom
  have hfπ : ∀ b, f b ≫ π = pe := by
    intro b
    simp only [f, Category.assoc, hθπ]
    exact prod.lift_fst _ _
  have hfL : ∀ b, f b ≫ L = (gch b ≫ prod.snd) ≫ Dv.line 2 := by
    intro b
    simp only [f, hL, Category.assoc]
    rw [← Category.assoc θ.hom, hθs]
    simp [Dv.line]
  have hcov : Cover2 (ZMod q) (f 0) (f 1) := cover_comp θ.hom (gch_cover (ZMod q))
  have hpb : IsPullback (cA (E := E) q) (cB q) (f 0) (f 1) :=
    (over_pullback hE).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) θ (by simp) (by simp) (by simp [f]) (by simp [f])
  set ψ := hpb.isoPullback with hψ
  have hψ1 : ψ.inv ≫ cA q = pullback.fst (f 0) (f 1) := by
    rw [Iso.inv_comp_eq]; exact hpb.isoPullback_hom_fst.symm
  have hψ2 : ψ.inv ≫ cB q = pullback.snd (f 0) (f 1) := by
    rw [Iso.inv_comp_eq]; exact hpb.isoPullback_hom_snd.symm
  let u : pullback (f 0) (f 1) ⟶ sch.obj (Gq q) := ψ.inv ≫ ps
  let ρ : pullback (f 0) (f 1) ⟶ sch.obj (Gq q) ⨯ E := ψ.inv ≫ prod.fst
  have hρ1 : ρ ≫ prod.fst = u := by simp only [ρ, u, ps, Category.assoc]
  have hρ2 : pullback.fst (f 0) (f 1) ≫ f 0 ≫ π = ρ ≫ prod.snd := by
    rw [hfπ 0, ← hψ1, Category.assoc, cA, mkW_pe]
    simp only [ρ, pe, Category.assoc]
  have hρE : ∀ i, Eqv _ ρ (tw q i) := fun i => eqv_comp (eqv_iso _ _) (eqv_fst (inv_of_map prod.snd hE) i)
  have hK : ∀ m j : ℤ, Function.Bijective fun p : Ht q E (m + 1) (j + 1) × Ht q E m j =>
      pull _ (pullback.fst (f 0) (f 1) ≫ f 0 ≫ π) _ _ p.1 +
        cup q (pull _ (pullback.fst (f 0) (f 1) ≫ f 0 ≫ π) _ _ p.2) (pull _ u _ _ (kappa q)) := by
    intro m j
    have := ((hρE (j + 1)) (m + 1)).comp (kun hE m j)
    convert this using 1
    have a1 : ∀ {n i : ℤ} (x : Ht q E n i), pull _ (pullback.fst (f 0) (f 1) ≫ f 0 ≫ π) _ _ x =
        pull _ ρ _ _ (pull _ prod.snd _ _ x) := by
      intro n i x
      rw [hρ2, pull_comp]
    have a2 : pull _ u _ _ (kappa q) = pull _ ρ _ _ (pull _ prod.fst _ _ (kappa q)) := by
      rw [← hρ1, pull_comp]
    funext p
    simp only [Function.comp]
    rw [a1, a1, a2, map_add, pull_cup]
  have t0 : IsTrivBy (f 0 ≫ L) wc := by rw [hfL]; exact gch_triv 0
  have t1 : IsTrivBy (f 1 ≫ L) wc := by rw [hfL]; exact gch_triv 1
  have uc : ∀ (T : Scheme.{0}) (y : Sx (pullback (f 0) (f 1)) 0 T),
      Units.map (show T ⟶ Gq q from y.map u).appTop.hom.toMonoidHom (tq q) =
        wc T (y.map (pullback.fst (f 0) (f 1))) * (wc T (y.map (pullback.snd (f 0) (f 1))))⁻¹ := by
    intro T y
    have e1 : y.map (pullback.fst (f 0) (f 1)) = (y.map ψ.inv).map (cA q) := by rw [← hψ1]; rfl
    have e2 : y.map (pullback.snd (f 0) (f 1)) = (y.map ψ.inv).map (cB q) := by rw [← hψ2]; rfl
    have w1 : wc T ((y.map ψ.inv).map (cA q)) = tv q (y.map ψ.inv) * wc T (y.map ψ.inv) :=
      Units.ext (cu_cA (y.map ψ.inv) 0)
    have w2 : wc T ((y.map ψ.inv).map (cB q)) = wc T (y.map ψ.inv) := Units.ext (cu_cB (y.map ψ.inv) 0)
    rw [e1, e2, w1, w2, mul_inv_cancel_right]
    rfl
  have hd := UpperTheory.kummer_cocycle_mayerVietoris_of_cover q (f 0) (f 1) L wc wc u hX hcov t0 t1 uc
  have h₁ : ∀ b i, Eqv _ (f b ≫ π) (tw q i) := by
    intro b i
    rw [hfπ]
    exact eqv_comp (eqv_fst (inv_of_map prod.snd hE) i) (UpperTheory.tateTwist_affineLine_projection_equiv q E i hE)
  exact lh2 hX π (c1 q L) fun m j => core π (f 0) (f 1) hcov _ _ (h₁ 0) (h₁ 1) hK hd m j
