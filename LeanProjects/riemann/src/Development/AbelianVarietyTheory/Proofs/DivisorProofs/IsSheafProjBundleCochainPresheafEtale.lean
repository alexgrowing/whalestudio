import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveBundleFormulaOfUnitOnEtalePoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivV
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotDComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroChains
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SxProdIsoHomSnd
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.CotSheaf

open CupSpec

variable {R : Type} [CommRing R] {q N : ℕ} {I : Cx R} {n : ℤ}

def fstHom {U W : Scheme.{0}} {E : Spc} {p : ℕ} (y : Sx (sch.obj U ⨯ E) p W) : W ⟶ U := y.map prod.fst

theorem fstHom_pair {U W : Scheme.{0}} {E : Spc} {p : ℕ} (v : W ⟶ U) (b : Sx E p W) :
    fstHom (sxPair (schSx v p) b) = v := sxPair_fst _ _

theorem fstHom_res {U W W' : Scheme.{0}} {E : Spc} {p : ℕ} (y : Sx (sch.obj U ⨯ E) p W) (w : W' ⟶ W) :
    fstHom (y.res w) = w ≫ fstHom y := by
  rw [fstHom, sxMap_res]; rfl

theorem fstHom_map {U Y W : Scheme.{0}} {E : Spc} {p : ℕ} (y : Sx (sch.obj Y ⨯ E) p W) (g : Y ⟶ U) :
    fstHom (y.map (prod.map (sch.map g) (𝟙 E))) = fstHom y ≫ g := by
  rw [fstHom, ← sxMap_comp, prod.map_fst, sxMap_comp]; rfl

theorem snd_map {U Y W : Scheme.{0}} {E : Spc} {p : ℕ} (y : Sx (sch.obj Y ⨯ E) p W) (g : Y ⟶ U) :
    (y.map (prod.map (sch.map g) (𝟙 E))).map prod.snd = y.map prod.snd := by
  rw [← sxMap_comp, prod.map_snd, Category.comp_id]

theorem sx_res_res {E : Spc} {p : ℕ} {U V W : Scheme.{0}} (x : Sx E p U) (f : V ⟶ U) (g : W ⟶ V) :
    (x.res f).res g = x.res (g ≫ f) := by
  change _ = (E.obj (op (SimplexCategory.mk p))).map (g ≫ f).op x
  rw [op_comp, FunctorToTypes.map_comp_apply]; rfl

theorem ev_res_pair {U W W' : Scheme.{0}} (α : Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) I n) (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + n = s) (y : Sx (sch.obj U ⨯ fibQ q N) p W) (w : W' ⟶ W) :
    Sec.res w (ev α p s h W y) =
      ev (I := I) (E := sch.obj W' ⨯ fibQ q N) (((cotPre R q N I n).map (w ≫ fstHom y).op).hom α) p s h W'
        (sxPair (schSx (𝟙 W') p) ((y.map prod.snd).res w)) := by
  rw [ev_res, cotPre_ev]
  congr 1
  apply sx_prod_ext
  · rw [sxPair_map, sxPair_fst, sxMap_res, schSx_map, Category.id_comp]
    rfl
  · rw [sxMap_res, sxPair_map, sxPair_snd]
    rfl

end GlobalTheory.EtC.CotSheaf

namespace GlobalTheory.EtC

open CupSpec CotSheaf

theorem cotPre_isSheaf (R : Type) [CommRing R] (q N : ℕ) (I : Cx R) (n : ℤ) :
    Presheaf.IsSheaf Scheme.etaleTopology.{0} (cotPre R q N I n) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget (ModuleCat.{1} (ULift.{1} R))), isSheaf_iff_isSheaf_of_type]
  have hI : ∀ s : ℤ, Presieve.IsSheaf Scheme.etaleTopology.{0} ((I.X s).obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) :=
    fun s => (isSheaf_iff_isSheaf_of_type _ _).1 ((Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget _)).1 (I.X s).cond)
  have sep : ∀ (s : ℤ) (W : Scheme.{0}) (T : Sieve W), T ∈ Scheme.etaleTopology.{0} W → ∀ t t' : Sec (I.X s) W,
      (∀ (W' : Scheme.{0}) (w : W' ⟶ W), T w → Sec.res w t = Sec.res w t') → t = t' :=
    fun s W T hT t t' ht => (hI s T hT).isSeparatedFor.ext fun _ w hw => ht _ w hw
  intro U S hS c hc
  rw [Presieve.compatible_iff_sieveCompatible] at hc
  have hC : ∀ {Y Z : Scheme.{0}} (f : Y ⟶ U) (g : Z ⟶ Y) (hf : S f),
      ((cotPre R q N I n).map g.op).hom (c f hf) = c (g ≫ f) (S.downward_closed hf g) := fun f g hf => (hc f g hf).symm

  have hcong : ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) {W : Scheme.{0}} (g g' : W ⟶ U) (hg : S g) (hg' : S g')
      (x x' : Sx (fibQ q N) p W), g = g' → x = x' →
      ev (I := I) (E := sch.obj W ⨯ fibQ q N) (c g hg) p s h W (sxPair (schSx (𝟙 W) p) x) =
        ev (I := I) (E := sch.obj W ⨯ fibQ q N) (c g' hg') p s h W (sxPair (schSx (𝟙 W) p) x') := by
    rintro p s h W g _ hg hg' x _ rfl rfl; rfl

  have hL : ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) {W W' : Scheme.{0}} (g : W ⟶ U) (hg : S g)
      (x : Sx (fibQ q N) p W) (t : W' ⟶ W),
      Sec.res t (ev (I := I) (E := sch.obj W ⨯ fibQ q N) (c g hg) p s h W (sxPair (schSx (𝟙 W) p) x)) =
        ev (I := I) (E := sch.obj W' ⨯ fibQ q N) (c (t ≫ g) (S.downward_closed hg t)) p s h W'
          (sxPair (schSx (𝟙 W') p) (x.res t)) := by
    intro p s h W W' g hg x t
    refine (ev_res_pair (c g hg) p s h _ t).trans ?_
    rw [fstHom_pair, Category.comp_id, hC, sxPair_snd]

  have hAm : ∀ γ : Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) I n,
      (∀ {Y : Scheme.{0}} (g : Y ⟶ U) (hg : S g), ((cotPre R q N I n).map g.op).hom γ = c g hg) →
      ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) {W W' : Scheme.{0}} (y : Sx (sch.obj U ⨯ fibQ q N) p W) (w : W' ⟶ W)
        (hw : S (w ≫ fstHom y)),
      Sec.res w (ev γ p s h W y) = ev (I := I) (E := sch.obj W' ⨯ fibQ q N) (c (w ≫ fstHom y) hw) p s h W'
          (sxPair (schSx (𝟙 W') p) ((y.map prod.snd).res w)) := by
    intro γ hγ p s h W W' y w hw
    refine (ev_res_pair γ p s h y w).trans ?_
    rw [hγ]

  have key : ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (W : Scheme.{0}) (y : Sx (sch.obj U ⨯ fibQ q N) p W),
      ∃ t : Sec (I.X s) W, ∀ (W' : Scheme.{0}) (w : W' ⟶ W) (hw : S (w ≫ fstHom y)),
        Sec.res w t = ev (I := I) (E := sch.obj W' ⨯ fibQ q N) (c (w ≫ fstHom y) hw) p s h W'
          (sxPair (schSx (𝟙 W') p) ((y.map prod.snd).res w)) := by
    intro p s h W y
    let fam : Presieve.FamilyOfElements ((I.X s).obj ⋙ forget (ModuleCat.{1} (ULift.{1} R)))
        (S.pullback (fstHom y)).arrows := fun W' w hw =>
      ev (I := I) (E := sch.obj W' ⨯ fibQ q N) (c (w ≫ fstHom y) hw) p s h W'
          (sxPair (schSx (𝟙 W') p) ((y.map prod.snd).res w))
    have hfam : fam.Compatible := by
      rw [Presieve.compatible_iff_sieveCompatible]
      intro Y Z f g hf
      refine Eq.trans ?_ (hL p s h (f ≫ fstHom y) hf _ g).symm
      exact hcong _ _ _ _ _ _ _ _ _ (Category.assoc _ _ _) (sx_res_res _ _ _).symm
    obtain ⟨t, ht, -⟩ := hI s _ (Scheme.etaleTopology.{0}.pullback_stable (fstHom y) hS) fam hfam
    exact ⟨t, fun W' w hw => ht w hw⟩
  choose a ha using key
  have hnat : ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (V W : Scheme.{0}) (g : V ⟶ W)
      (y : Sx (sch.obj U ⨯ fibQ q N) p W), Sec.res g (a p s h W y) = a p s h V (y.res g) := by
    intro p s h V W g y
    apply sep s V _ (Scheme.etaleTopology.{0}.pullback_stable (fstHom (y.res g)) hS)
    intro W' w hw
    have hw' : S ((w ≫ g) ≫ fstHom y) := by
      rw [fstHom_res] at hw; simpa [Category.assoc] using hw
    rw [secRes_res, ha p s h W y W' (w ≫ g) hw', ha p s h V (y.res g) W' w hw]
    refine hcong _ _ _ _ _ _ _ _ _ ?_ ?_
    · rw [fstHom_res, Category.assoc]
    · rw [sxMap_res, sx_res_res]
  obtain ⟨α, hα⟩ := ev_exists (R := R) (E := sch.obj U ⨯ fibQ q N) (I := I) (n := n) a hnat
  have hαam : ∀ {Y : Scheme.{0}} (g : Y ⟶ U) (hg : S g), ((cotPre R q N I n).map g.op).hom α = c g hg := by
    intro Y g hg
    apply ev_ext
    intro p s h W y
    rw [cotPre_ev, hα]
    apply sep s W _ (Scheme.etaleTopology.{0}.pullback_stable (fstHom (y.map (prod.map (sch.map g) (𝟙 _)))) hS)
    intro W' w hw
    rw [ha p s h W _ W' w hw]
    refine Eq.trans ?_ (ev_res_pair (c g hg) p s h y w).symm
    rw [hC, snd_map]
    refine hcong _ _ _ _ _ _ _ _ _ ?_ rfl
    rw [fstHom_map, Category.assoc]
  refine ⟨α, fun Y g hg => hαam g hg, fun β hβ => ?_⟩
  apply ev_ext
  intro p s h W y
  apply sep s W _ (Scheme.etaleTopology.{0}.pullback_stable (fstHom y) hS)
  intro W' w hw
  rw [hAm β (fun g hg => hβ g hg) p s h y w hw, hAm α (fun g hg => hαam g hg) p s h y w hw]

end GlobalTheory.EtC

end
