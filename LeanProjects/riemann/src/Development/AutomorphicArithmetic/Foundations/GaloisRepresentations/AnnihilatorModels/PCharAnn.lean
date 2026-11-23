import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.charAnn_of :
    CharOfAnn := by
  intro K _ n M s hcard hgen hann hdet
  classical
  set L := AlgebraicClosure K
  set f : K →+* L := algebraMap K L
  have hf : Function.Injective f := f.injective
  set M' : Matrix (Fin n) (Fin n) L := M.map f
  have hchar : M'.charpoly = M.charpoly.map f := Matrix.charpoly_map M f
  have hpmap : (rootPol s).map f = (Multiset.map (fun a => Polynomial.X - Polynomial.C a) (s.map f)).prod := by
    simp [rootPol, Polynomial.map_multiset_prod, Multiset.map_map, Function.comp_def]
  have hannL : Polynomial.aeval M' (rootPol s) = 0 := by
    have h1 : M' = (Algebra.ofId K L).mapMatrix M := by
      rw [AlgHom.mapMatrix_apply]; rfl
    rw [h1, Polynomial.aeval_algHom_apply, hann, map_zero]
  set R := M'.charpoly.roots
  have hmem : ∀ r ∈ R, r ∈ s.map f := by
    intro r hr
    have hroot : M'.charpoly.IsRoot r := (Polynomial.mem_roots (Matrix.charpoly_monic M').ne_zero).1 hr
    have hsp : r ∈ spectrum L M' := Matrix.mem_spectrum_of_isRoot_charpoly hroot
    have hev : Polynomial.eval r ((rootPol s).map f) ∈ spectrum L (Polynomial.aeval M' ((rootPol s).map f)) :=
      spectrum.subset_polynomial_aeval M' _ ⟨r, hsp, rfl⟩
    have hz : Polynomial.aeval M' ((rootPol s).map f) = 0 := by
      rw [Polynomial.aeval_map_algebraMap]; exact hannL
    rw [hz] at hev
    have h0 : Polynomial.eval r ((rootPol s).map f) = 0 := by
      by_contra hne
      exact (spectrum.mem_iff.1 hev) (by
        simpa using (isUnit_iff_ne_zero.2 hne).map (algebraMap L (Matrix (Fin n) (Fin n) L)))
    have hne0 : (rootPol s).map f ≠ 0 := by
      rw [hpmap]; exact (Polynomial.monic_multiset_prod_of_monic _ _ (fun a _ => Polynomial.monic_X_sub_C a)).ne_zero
    have : r ∈ ((rootPol s).map f).roots := (Polynomial.mem_roots hne0).2 h0
    rwa [hpmap, Polynomial.roots_multiset_prod_X_sub_C] at this
  set g := Function.invFun f
  set t := R.map g
  have htR : t.map f = R := by
    rw [Multiset.map_map]
    conv_rhs => rw [← Multiset.map_id R]
    apply Multiset.map_congr rfl
    intro r hr
    obtain ⟨a, -, ha⟩ := Multiset.mem_map.1 (hmem r hr)
    exact Function.invFun_eq ⟨a, ha⟩
  have hRcard : R.card = n := by
    rw [IsAlgClosed.card_roots_eq_natDegree, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have htcard : t.card = s.card := by simp [t, hRcard, hcard]
  have htsub : ∀ x ∈ t, x ∈ s := by
    intro x hx
    have : f x ∈ s.map f := hmem (f x) (by rw [← htR]; exact Multiset.mem_map_of_mem f hx)
    obtain ⟨a, ha, hax⟩ := Multiset.mem_map.1 this
    rw [← hf hax]; exact ha
  have htprod : t.prod = s.prod := by
    apply hf
    rw [map_multiset_prod, htR, ← Matrix.det_eq_prod_roots_charpoly, ← hdet, RingHom.map_det]
    rfl
  have hts : t = s := hgen t htcard htsub htprod
  apply Polynomial.map_injective f hf
  rw [← hchar, hpmap, ← hts, htR]
  exact (Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq (Matrix.charpoly_monic M')
    (by rw [IsAlgClosed.card_roots_eq_natDegree])).symm
