import Development.EtaleCohomology.EtaleSheaves.CupProductRingLaws

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafNatCupPf

section

variable {R : Type} [CommRing R]

theorem chainsXIso_inv_map {E E' : Spc} (f : E ⟶ E') (p : ℕ) :
    (chainsXIso R E p).inv ≫ ((chains R).map f).f (-(p : ℤ)) =
      (free R).map (f.app (op (SimplexCategory.mk p))) ≫ (chainsXIso R E' p).inv := by
  dsimp only [chains, chainsXIso, Functor.comp_map]
  rw [ComplexShape.embeddingDownNat.extendFunctor_map (C := Shv R)]
  erw [HomologicalComplex.extendMap_f _ _ (i := p) (i' := -(p : ℤ)) rfl]
  simp only [chainsN]
  erw [Iso.inv_hom_id_assoc]
  simp
  rfl

theorem free_map_freeGen {P Q : PSh} (g : P ⟶ Q) (U : Scheme.{0}) (x : P.obj (op U)) :
    (((free R).map g).hom.app (op U)).hom (freeGen R P U x) = freeGen R Q U (g.app (op U) x) := by
  have h := congrArg (fun φ => (φ.app (op U)).hom (ModuleCat.freeMk (ULift.up x)))
    (toSheafify_naturality Scheme.etaleTopology ((freeP R).map g))
  have h2 : (((freeP R).map g).app (op U)).hom (ModuleCat.freeMk (ULift.up x)) =
      ModuleCat.freeMk (ULift.up (g.app (op U) x)) :=
    ModuleCat.free_map_apply (R := ULift.{1} R) _ _
  exact h.symm.trans (congrArg ((toSheafify Scheme.etaleTopology ((freeP R).obj Q)).app (op U)).hom h2)

theorem ev_pull {E E' : Spc} (f : E ⟶ E') {I : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E') I n) (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x =
      ev α p s h U ((f.app (op (SimplexCategory.mk p))).app (op U) x) := by
  simp only [ev]
  rw [Cochain.comp_v _ _ (zero_add n) (-(p : ℤ)) (-(p : ℤ)) s (add_zero _) h, Cochain.ofHom_v,
    ← Category.assoc, chainsXIso_inv_map, Category.assoc]
  rw [← free_map_freeGen]
  rfl

theorem sub_pull {E E' : Spc} (f : E ⟶ E') {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (j l : ℕ) (h : j + l ≤ N) :
    (f.app (op (SimplexCategory.mk l))).app (op U) (x.sub j l h) =
      Sx.sub (E := E') (N := N) ((f.app (op (SimplexCategory.mk N))).app (op U) x) j l h := by
  have := ConcreteCategory.congr_hom (congr_app (f.naturality (SimplexCategory.subinterval j l h).op) (op U)) x
  simp only [Sx.sub]
  exact this

theorem isAW_pull {I J K : Cx R} (μ : Pair I J K) {E E' : Spc} (f : E ⟶ E') {n m k : ℤ} (hk : n + m = k)
    (α : Cochain ((chains R).obj E') I n) (β : Cochain ((chains R).obj E') J m) (γ : Cochain ((chains R).obj E') K k)
    (hγ : μ.IsAW hk α β γ) :
    μ.IsAW hk ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n))
      ((Cochain.ofHom ((chains R).map f)).comp β (zero_add m))
      ((Cochain.ofHom ((chains R).map f)).comp γ (zero_add k)) := by
  intro N w h U x
  rw [ev_pull, hγ]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [ev_pull, ev_pull, sub_pull, sub_pull]

theorem pull_mk {E E' : Spc} (f : E ⟶ E') (F : Shv R) (n : ℤ) (z : Cocycle ((chains R).obj E') (res R F) n) :
    pull R f F n (CohomologyClass.mk z) = CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains R).map f)) z (zero_add n)) :=
  rfl

theorem zcomp_ofHom_val {E E' : Spc} (f : E ⟶ E') {I : Cx R} {n : ℤ} (z : Cocycle ((chains R).obj E') I n) :
    (zcomp (Cocycle.ofHom ((chains R).map f)) z (zero_add n)).1 = (Cochain.ofHom ((chains R).map f)).comp z.1 (zero_add n) :=
  rfl

end

open CupProductRingLaws in
theorem LeafNatCup_of (hc : LeafCupSpec) : LeafNatCup := by
  intro q _ E E' f n m i j a b
  obtain ⟨α, rfl⟩ := a.mk_surjective
  obtain ⟨β, rfl⟩ := b.mk_surjective
  obtain ⟨γ, hγ⟩ := (hc (ZMod q) (twPair q i j) E' rfl).1 α β
  have e1 : cup q (CohomologyClass.mk α) (CohomologyClass.mk β) = CohomologyClass.mk γ :=
    (hc (ZMod q) (twPair q i j) E' rfl).2 α β γ hγ
  have hAW := isAW_pull (twPair q i j) f rfl α.1 β.1 γ.1 hγ
  rw [← zcomp_ofHom_val, ← zcomp_ofHom_val, ← zcomp_ofHom_val] at hAW
  have e2 := (hc (ZMod q) (twPair q i j) E rfl).2 _ _ _ hAW
  rw [e1, pull_mk, pull_mk, pull_mk]
  exact e2.symm

end LateralTheory.E.LeafNatCupPf
