import Development.EtaleCohomology.TateTwists.EtaleSemilinearCohomologyOperationExistsOfEvalua
import Development.EtaleCohomology.KummerTheory.CupAWCutEv

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.EvBasicPf
variable {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}
open LateralTheory.KummerTheory.AW

theorem ev_sub (α β : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (α - β) p s h U x = ev α p s h U x - ev β p s h U x := by
  rw [ev_eq, Cochain.sub_v, Preadditive.comp_sub]
  exact map_sub (AddMonoidHom.mk' (fun φ : _ ⟶ I.X s => Sec.map φ (freeGen R _ U x)) (fun _ _ => rfl)) _ _

theorem ev_zero (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 := by
  rw [ev_eq, Cochain.zero_v, comp_zero]
  exact map_zero (AddMonoidHom.mk' (fun φ : _ ⟶ I.X s => Sec.map φ (freeGen R _ U x)) (fun _ _ => rfl))

theorem ev_zsmul (c : ℤ) (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0})
    (x : Sx E p U) : ev (c • α) p s h U x = c • ev α p s h U x := by
  exact map_zsmul (AddMonoidHom.mk' (fun β : Cochain ((chains R).obj E) I n => ev β p s h U x)
    (fun a b => ev_add a b p s h U x)) c α

theorem ev_post {J : Cx R} (m : I ⟶ J) (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s)
    (U : Scheme.{0}) (x : Sx E p U) :
    ev (α.comp (Cochain.ofHom m) (add_zero n)) p s h U x = Sec.map (m.f s) (ev α p s h U x) := by
  rw [ev_eq, Cochain.comp_zero_cochain_v, Cochain.ofHom_v, ev_eq]; rfl

theorem chainsXIso_nat {E' : Spc} (f : E' ⟶ E) (p : ℕ) :
    (chainsXIso R E' p).inv ≫ ((chains R).map f).f (-(p : ℤ)) =
      (free R).map (f.app (op (SimplexCategory.mk p))) ≫ (chainsXIso R E p).inv := by
  rw [Iso.inv_comp_eq]
  unfold chains chainsXIso
  change (HomologicalComplex.extendMap ((chainsN R).map f) ComplexShape.embeddingDownNat).f (-(p : ℤ)) = _
  exact HomologicalComplex.extendMap_f ((chainsN R).map f) ComplexShape.embeddingDownNat (i := p) (i' := -(p : ℤ)) rfl

theorem ev_pre {E' : Spc} (f : E' ⟶ E) (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s)
    (U : Scheme.{0}) (x : Sx E' p U) :
    ev ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x = ev α p s h U (x.map f) := by
  rw [ev_eq, Cochain.zero_cochain_comp_v, Cochain.ofHom_v, reassoc_of% (chainsXIso_nat (R := R) f p), ev_eq]
  change Sec.map ((chainsXIso R E p).inv ≫ α.v _ _ h) (Sec.map ((free R).map (f.app (op (SimplexCategory.mk p))))
    (freeGen R _ U x)) = _
  rw [map_freeGen]; rfl

end LateralTheory.EtaleFoundations.EvBasicPf

open LateralTheory.EtaleFoundations.EvBasicPf LateralTheory.KummerTheory.AW in
theorem LateralTheory.EtaleFoundations.pp_ev_basic_of : LateralTheory.EtaleFoundations.pp_ev_basic := fun _ _ =>
  ⟨fun α β p s h U x => ⟨ev_add α β p s h U x, ev_sub α β p s h U x, ev_zero p s h U x, fun c => ev_zsmul c α p s h U x⟩,
   fun α p s h _ _ g x => ev_res α p s h g x,
   fun α β hh => ev_ext α β hh,
   fun f α p s h U x => ev_pre f α p s h U x,
   fun m α p s h U x => ev_post m α p s h U x⟩
