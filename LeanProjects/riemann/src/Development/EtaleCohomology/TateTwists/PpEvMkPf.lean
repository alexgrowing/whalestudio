import Development.EtaleCohomology.TateTwists.EtaleSemilinearCohomologyOperationExistsOfEvalua

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.EvMkPf

variable {R : Type} [CommRing R] {E : Spc} {I : Cx R}

theorem sq {X Y : Type 1} (h : X ⟶ Y) {M N : ModuleCat.{1} (ULift.{1} R)} (a : Y ⟶ M) (b : X ⟶ N) (φ : N ⟶ M)
    (H : ∀ x, a (h x) = φ (b x)) :
    (ModuleCat.free (ULift.{1} R)).map h ≫ ModuleCat.freeDesc a = ModuleCat.freeDesc b ≫ φ := by
  apply ModuleCat.free_hom_ext
  intro x
  simp [ModuleCat.free_map_apply, ModuleCat.freeDesc_apply, H]

noncomputable def eta (k : ℕ) (s : ℤ) (F : ∀ U : Scheme.{0}, Sx E k U → Sec (I.X s) U)
    (hF : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E k U), Sec.res g (F U x) = F V (x.res g)) :
    (freeP R).obj (E.obj (op (SimplexCategory.mk k))) ⟶ (I.X s).obj where
  app U := ModuleCat.freeDesc (X := ULift.{1} (Sx E k U.unop)) (↾fun x => F U.unop (ULift.down x))
  naturality U V g := sq _ _ _ _ (fun x => (hF V.unop U.unop g.unop x.down).symm)

noncomputable def phi (k : ℕ) (s : ℤ) (F : ∀ U : Scheme.{0}, Sx E k U → Sec (I.X s) U)
    (hF : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E k U), Sec.res g (F U x) = F V (x.res g)) :
    (free R).obj (E.obj (op (SimplexCategory.mk k))) ⟶ I.X s :=
  ((sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homEquiv
    ((freeP R).obj (E.obj (op (SimplexCategory.mk k)))) (I.X s)).symm (eta k s F hF)

theorem phi_unit (k : ℕ) (s : ℤ) (F : ∀ U : Scheme.{0}, Sx E k U → Sec (I.X s) U)
    (hF : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E k U), Sec.res g (F U x) = F V (x.res g)) :
    toSheafify Scheme.etaleTopology.{0} ((freeP R).obj (E.obj (op (SimplexCategory.mk k)))) ≫ (phi k s F hF).hom =
      eta k s F hF := by
  have := ((sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homEquiv
    ((freeP R).obj (E.obj (op (SimplexCategory.mk k)))) (I.X s)).apply_symm_apply (eta k s F hF)
  rw [Adjunction.homEquiv_unit] at this
  exact this

theorem phi_freeGen (k : ℕ) (s : ℤ) (F : ∀ U : Scheme.{0}, Sx E k U → Sec (I.X s) U)
    (hF : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E k U), Sec.res g (F U x) = F V (x.res g))
    (U : Scheme.{0}) (x : Sx E k U) :
    ((phi k s F hF).hom.app (op U)).hom (freeGen R _ U x) = F U x := by
  have h2 := congrArg (fun f => (f.app (op U)).hom (ModuleCat.freeMk (R := ULift.{1} R) (ULift.up.{1} x))) (phi_unit k s F hF)
  exact h2.trans (ModuleCat.freeDesc_apply _ _)

variable {n : ℤ} (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U)
  (ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g))

noncomputable def comp (p q : ℤ) (hpq : p + n = q) : ((chains R).obj E).X p ⟶ I.X q :=
  if hp : p ≤ 0 then
    (HomologicalComplex.XIsoOfEq _ (by omega : p = -((p.natAbs : ℕ) : ℤ))).hom ≫ (chainsXIso R E p.natAbs).hom ≫
      phi p.natAbs q (fun U x => a p.natAbs q (by omega) U x) (fun V U g x => ha _ _ _ V U g x)
  else 0

theorem aux {s : ℤ} (j k : ℕ) (e : j = k) (hjk : -(k : ℤ) = -(j : ℤ)) (hj : -(j : ℤ) + n = s) (hk : -(k : ℤ) + n = s) :
    (HomologicalComplex.XIsoOfEq ((chains R).obj E) hjk).hom ≫ (chainsXIso R E j).hom ≫
      phi j s (fun U x => a j s hj U x) (fun V U g x => ha _ _ _ V U g x) =
    (chainsXIso R E k).hom ≫ phi k s (fun U x => a k s hk U x) (fun V U g x => ha _ _ _ V U g x) := by
  subst e
  simp

theorem comp_neg (k : ℕ) (s : ℤ) (h : -(k : ℤ) + n = s) :
    comp a ha (-(k : ℤ)) s h = (chainsXIso R E k).hom ≫ phi k s (fun U x => a k s h U x) (fun V U g x => ha _ _ _ V U g x) := by
  unfold comp
  rw [dif_pos (by omega)]
  exact aux a ha _ _ (by omega) _ _ _

end LateralTheory.EtaleFoundations.EvMkPf

open LateralTheory.EtaleFoundations.EvMkPf in
theorem LateralTheory.EtaleFoundations.pp_ev_mk_of : LateralTheory.EtaleFoundations.pp_ev_mk := by
  intro R _ E I n a ha
  refine ⟨Cochain.mk (comp a ha), fun p s h U x => ?_⟩
  unfold ev
  rw [Cochain.mk_v, comp_neg a ha p s h, Iso.inv_hom_id_assoc]
  exact phi_freeGen _ _ _ _ U x
