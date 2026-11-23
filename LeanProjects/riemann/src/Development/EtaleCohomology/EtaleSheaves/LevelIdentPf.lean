import Development.EtaleCohomology.EtaleSheaves.DescentInduction

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LevelIdentPf

def FreeSingleHomotopyEquivDiscreteChains : Prop := ∀ (R : Type) [CommRing R], ∃ e : ∀ P : PSh, HomotopyEquiv (sgl ((free R).obj P)) ((chains R).obj (disc.obj P)),
  (∀ P, sglι _ ≫ (e P).hom.f 0 = (chainsXIso R (disc.obj P) 0).inv) ∧
  ∀ {P Q : PSh} (f : P ⟶ Q), (e P).hom ≫ (chains R).map (disc.map f) =
    (CochainComplex.singleFunctor (Shv R) 0).map ((free R).map f) ≫ (e Q).hom

variable {R : Type} [CommRing R]

theorem cpull_comp {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (I : Cx R) (n : ℤ) (x : CohomologyClass M I n) :
    cpull (f ≫ g) I n x = cpull f I n (cpull g I n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.ofHom_comp]

theorem cpull_id (K I : Cx R) (n : ℤ) (x : CohomologyClass K I n) : cpull (𝟙 K) I n x = x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp]

theorem cpull_homotopy {K L : Cx R} {f g : K ⟶ L} (h : Homotopy f g) (I : Cx R) (n : ℤ) (x : CohomologyClass L I n) :
    cpull f I n x = cpull g I n x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  change CohomologyClass.mk (zcomp _ x _) = CohomologyClass.mk (zcomp _ x _)
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff]
  refine ⟨n - 1, by omega, n.negOnePow • (Cochain.ofHomotopy h).comp x.1 (by omega), ?_⟩
  rw [δ_units_smul, δ_comp _ _ (by omega) 0 (n + 1) n (by omega) (by omega) (by omega), δ_ofHomotopy]
  simp [zcomp, Cocycle.δ_eq_zero, Cochain.sub_comp, smul_smul, Int.units_mul_self]

theorem cpull_iso_bij {K L : Cx R} (e : HomotopyEquiv K L) (I : Cx R) (n : ℤ) :
    Function.Bijective (cpull e.hom I n) := by
  refine Function.bijective_iff_has_inverse.2 ⟨cpull e.inv I n, fun x => ?_, fun x => ?_⟩
  · rw [← cpull_comp, cpull_homotopy e.homotopyInvHomId, cpull_id]
  · rw [← cpull_comp, cpull_homotopy e.homotopyHomInvId, cpull_id]

theorem sq_iff {A B C D : Type*} {a : B → D} {b : A → B} {c : C → D} {d : A → C}
    (w : ∀ x, a (b x) = c (d x)) (ha : Function.Bijective a) (hd : Function.Bijective d) :
    (Function.Bijective b ↔ Function.Bijective c) ∧ (Function.Injective b ↔ Function.Injective c) := by
  have w' : a ∘ b = c ∘ d := funext w
  obtain ⟨d', hd1, hd2⟩ := Function.bijective_iff_has_inverse.1 hd
  have hc : c = a ∘ b ∘ d' := by
    funext y; simp only [Function.comp_apply, w, hd2 y]
  have hd'b : Function.Bijective d' := Function.bijective_iff_has_inverse.2 ⟨d, hd2, hd1⟩
  refine ⟨⟨fun hb => hc ▸ ha.comp (hb.comp hd'b), fun hc' => ?_⟩, ⟨fun hb => hc ▸ ha.1.comp (hb.comp hd'b.1), fun hc' => ?_⟩⟩
  · have : a ∘ b = c ∘ d := w'
    have hab : Function.Bijective (a ∘ b) := this ▸ hc'.comp hd
    obtain ⟨a', ha1, ha2⟩ := Function.bijective_iff_has_inverse.1 ha
    have : b = a' ∘ (a ∘ b) := by funext x; simp [ha1 (b x)]
    rw [this]; exact (Function.bijective_iff_has_inverse.2 ⟨a, ha2, ha1⟩).comp hab
  · intro x y hxy
    apply hd.1; apply hc'
    rw [← w, ← w, hxy]

theorem chains_f {E E' : Spc} (f : E ⟶ E') (n : ℕ) : ((chains R).map f).f (-(n : ℤ)) =
    (chainsXIso R E n).hom ≫ (free R).map (f.app (op (SimplexCategory.mk n))) ≫ (chainsXIso R E' n).inv := by
  dsimp only [chains, chainsXIso, Functor.comp_map]
  erw [HomologicalComplex.extendMap_f _ ComplexShape.embeddingDownNat (i := n) rfl]
  rfl

theorem cpull_isoHom_bij {K L : Cx R} (i : K ≅ L) (I : Cx R) (n : ℤ) : Function.Bijective (cpull i.hom I n) :=
  cpull_iso_bij (HomotopyEquiv.ofIso i) I n

theorem pull_eq {E E' : Spc} (f : E ⟶ E') (F : Shv R) (n : ℤ) (x : H R E' F n) :
    pull R f F n x = cpull ((chains R).map f) (res R F) n x := rfl

theorem LevelIdent_of (hS : FreeSingleHomotopyEquivDiscreteChains) : LateralTheory.E.DescStepPf.LevelIdent := by
  intro R _ F E E' f p j
  obtain ⟨e, -, he⟩ := hS R
  let S := CochainComplex.singleFunctor (Shv R) 0
  let g := f.app (op (SimplexCategory.mk p))
  have sq1 : S.map (((chains R).map f).f (-(p : ℤ))) ≫ S.map (chainsXIso R E' p).hom =
      S.map (chainsXIso R E p).hom ≫ S.map ((free R).map g) := by
    rw [← S.map_comp, ← S.map_comp, chains_f]; simp [g]
  have w1 : ∀ x, cpull (S.map (chainsXIso R E p).hom) (res R F) j (cpull (S.map ((free R).map g)) (res R F) j x) =
      cpull (S.map (((chains R).map f).f (-(p : ℤ)))) (res R F) j (cpull (S.map (chainsXIso R E' p).hom) (res R F) j x) := by
    intro x; rw [← cpull_comp, ← cpull_comp, sq1]
  have w2 : ∀ x, cpull (e (E.obj (op (SimplexCategory.mk p)))).hom (res R F) j (pull R (disc.map g) F j x) =
      cpull (S.map ((free R).map g)) (res R F) j (cpull (e (E'.obj (op (SimplexCategory.mk p)))).hom (res R F) j x) := by
    intro x; rw [pull_eq, ← cpull_comp, ← cpull_comp, he g]
  obtain ⟨b1, i1⟩ := sq_iff w1 (cpull_isoHom_bij (S.mapIso (chainsXIso R E p)) _ _)
    (cpull_isoHom_bij (S.mapIso (chainsXIso R E' p)) _ _)
  obtain ⟨b2, i2⟩ := sq_iff w2 (cpull_iso_bij _ _ _) (cpull_iso_bij _ _ _)
  exact ⟨b2.trans b1, i2.trans i1⟩

end LateralTheory.E.LevelIdentPf
