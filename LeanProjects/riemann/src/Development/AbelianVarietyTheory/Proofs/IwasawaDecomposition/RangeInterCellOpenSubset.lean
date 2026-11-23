import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFlagCellOfNonvanishingLeadingMinorsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagCellPointEqOfTriangularFramesStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FlagEmb.Overlap

theorem spMap_spMap {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem exists_fieldPoint {A : Type} [CommRing A] (y : Sp A) :
    ∃ (k : Type) (_ : Field k) (ψ : A →+* k), ∀ q : Sp k, spMap ψ q = y := by
  refine ⟨(show PrimeSpectrum A from y).asIdeal.ResidueField, inferInstance, algebraMap _ _, fun q => ?_⟩
  apply PrimeSpectrum.ext
  change Ideal.comap _ (show PrimeSpectrum _ from q).asIdeal = _
  rw [show (show PrimeSpectrum _ from q).asIdeal = ⊥ from Ideal.eq_bot_of_prime _]
  exact Ideal.ker_algebraMap_residueField _

theorem inBlock_cellVec {T : Type} {m : T → ℕ} {S : Type} [CommRing S] {ι : Type} {c c' : Let m → ι → S}
    (h : InBlock c c') (w : Pm m) (x : CellVar m → S) : InBlock c (cellVec c' w x) := fun z =>
  Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (h ⟨z.1, w z.1 i⟩)

theorem map_lform {ι : Type} {M k : ℕ} {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (D : ι → Fin (M + 1) → S) (ρ : Fin k → ι) (q : Fin (plN M k + 1)) :
    φ (lform D ρ q) = lform (fun z => φ ∘ D z) ρ q := by
  simp [lform, map_prod]

theorem range_inter_cellOpen_subset : ∀ (O K : Type) [CommRing O] [Field K] (β : O →+* K) (X : Scheme.{0}) (s : X ⟶ Sp O) (T : Type) [Finite T] (m : T → ℕ) (M : ℕ) (B : Type) (V : B → X.affineOpens) (α : ∀ b, K →+* Γ(X, (V b).1)) (c D : ∀ b, Let m → Fin (M + 1) → Γ(X, (V b).1)) (P : Scheme.{0}) (p0 : P ⟶ X) (p : ∀ en : En m, P ⟶ PSpace O (plN M en.1)) (h : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ P)), IsCover β s V α c D → IsPlk β s V α c p0 p h → ∀ b w (W : P.Opens), IsCellOpen p0 p (V b) (D b) w W → ∀ b' w', Set.range (h b' w') ∩ (W : Set P) ⊆ Set.range (h b w) := by
  intro O K _ _ β X s T _ m M B V α c D P p0 p h hc hp b w W hW b' w'
  rintro _ ⟨⟨y, rfl⟩, hy⟩
  obtain ⟨k, _, ψ', hψ'⟩ := exists_fieldPoint y
  have hz : ∀ q : Sp k, (spMap ψ' ≫ h b' w') q = h b' w' y := fun q => by
    rw [Scheme.Hom.comp_apply, hψ']
  obtain ⟨φ, hφ, hne⟩ := (hW k (spMap ψ' ≫ h b' w')).1 (by
    rintro _ ⟨q, rfl⟩
    rw [hz]; exact hy)
  rw [Category.assoc, hp.base] at hφ
  have hφ' : spMap φ ≫ (V b).2.fromSpec =
      spMap (ψ'.comp (MvPolynomial.C : Γ(X, (V b').1) →+* CR m (V b'))) ≫ (V b').2.fromSpec := by
    rw [← hφ, cbase, ← Category.assoc, spMap_spMap]
  have hu : InBlock (fun z => φ ∘ c b z) (fun z => ψ' ∘ uvec (c b') w' z) := by
    have := inBlock_cellVec (hc.compat k b b' φ _ hφ') w' (ψ' ∘ MvPolynomial.X)
    convert this using 2 with z
    exact map_cellVec ψ' _ w' _ z
  obtain ⟨x, d, hd, ht⟩ := GlobalTheory.T.exists_flagCell_of_nonvanishing_leading_minors T m k M _ _ _ w ((hc.inv b).map φ) hu (fun τ j hj => by
    obtain ⟨hv, e⟩ := hp.plk b' w' (stdEn τ j hj)
    have := hne τ j hj _ _ _ (by rw [Category.assoc, e, spMap_pt])
    rw [map_plk] at this
    simpa only [map_lform] using this)
  have hψ : ∀ z, (MvPolynomial.eval₂Hom φ x : CR m (V b) →+* k) ∘ uvec (c b) w z =
      cellVec (fun z => φ ∘ c b z) w x z := fun z => by
    refine (map_cellVec _ _ w _ z).trans ?_
    congr 1
    · funext z r; simp
    · funext r; simp
  have key := GlobalTheory.T.flagCell_point_eq_of_triangular_frames O K β X s T m M B V α c D P p0 p h hc hp k b b' w w' (MvPolynomial.eval₂Hom φ x) ψ' d
    (by rw [hφ, cbase, ← Category.assoc, spMap_spMap, MvPolynomial.eval₂Hom_comp_C]) hd
    (by simpa only [hψ] using ht)
  obtain ⟨q⟩ : Nonempty (Sp k) := inferInstanceAs (Nonempty (PrimeSpectrum k))
  exact ⟨spMap (MvPolynomial.eval₂Hom φ x : CR m (V b) →+* k) q, by
    rw [← hz q, ← key, Scheme.Hom.comp_apply]⟩

end GlobalTheory.FlagEmb.Overlap
