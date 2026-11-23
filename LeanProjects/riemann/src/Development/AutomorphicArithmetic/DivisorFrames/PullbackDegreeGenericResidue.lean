import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.CovCmp
import Development.AutomorphicArithmetic.DivisorFrames.OrderCodimOneFiniteMap
import Development.AutomorphicArithmetic.DivisorFrames.ValuationNormSumExtensions
import Development.AutomorphicArithmetic.DivisorFrames.OrderEqValuationCodimOne
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.Toroidal
open GlobalTheory.VertCmp GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.CovCmp
open scoped Classical

private theorem surj_specializes {X : Scheme.{0}} [IsIntegral X] {x : X} (h : x ⤳ genericPoint X) :
    Function.Surjective (X.presheaf.stalkSpecializes h) := by
  obtain rfl : x = genericPoint X := (h.antisymm (genericPoint_specializes x)).eq
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  exact Function.surjective_id

private theorem finrank_fnMap {X X' : Scheme.{0}} [IsIntegral X] [IsIntegral X'] (g : X' ⟶ X)
    (hg : g (genericPoint X') ⤳ genericPoint X) :
    (letI := (SmallSec.fnMap g hg).toAlgebra; Module.finrank X.functionField X'.functionField) =
      g.residueDegree (genericPoint X') := by
  letI := (SmallSec.fnMap g hg).toAlgebra
  letI := (g.residueFieldMap (genericPoint X')).hom.toAlgebra
  let i₀ : X.functionField →+* X.residueField (g (genericPoint X')) :=
    (X.presheaf.stalkSpecializes hg ≫ X.residue _).hom
  let j₀ : X'.functionField →+* X'.residueField (genericPoint X') := (X'.residue _).hom
  let i := RingEquiv.ofBijective i₀ ⟨i₀.injective, (X.residue_surjective _).comp (surj_specializes hg)⟩
  let j := RingEquiv.ofBijective j₀ ⟨j₀.injective, X'.residue_surjective _⟩
  refine Algebra.finrank_eq_of_equiv_equiv i j ?_
  ext a
  exact congr($(Scheme.residue_residueFieldMap g (genericPoint X')) (X.presheaf.stalkSpecializes hg a))

private theorem toFF_mem {X X' : Scheme.{0}} [IsIntegral X] [IsIntegral X'] (g : X' ⟶ X)
    (hg : g (genericPoint X') ⤳ genericPoint X) {A : Type} [CommRing A] (p : X ⟶ Sp A) {x : X}
    {W : ValuationSubring X.functionField} (h : DominatesStalk W x) (a : A) :
    ∃ w ∈ W, SmallSec.fnMap g hg w = toFunctionField (g ≫ p) a := by
  obtain ⟨ψ, _, hψ⟩ := dominatesStalk_iff_exists_isLocalHom.1 h
  have _ : Nonempty (⊤ : X.Opens) := ⟨⟨x, trivial⟩⟩
  have e : toFunctionField p a = algebraMap _ X.functionField
      (X.presheaf.germ ⊤ x trivial (p.appTop ((Scheme.ΓSpecIso (.of A)).inv a))) :=
    (Scheme.algebraMap_germ_eq_germToFunctionField X (U := ⊤) (x := x) trivial _).symm
  refine ⟨toFunctionField p a, ?_, ?_⟩
  · rw [e, ← hψ]
    exact (ψ _).2
  · exact SmallSec.fnMap_fnOf g hg (U := ⊤) trivial trivial (p.appTop ((Scheme.ΓSpecIso (.of A)).inv a))

theorem UpperTheory.pullback_degree_generic_residue :
    ∀ (R : Type) [CommRing R] (X X' : Scheme.{0}) [IsIntegral X] [IsIntegral X'] [IsLocallyNoetherian X] [IsLocallyNoetherian X'] (q : X ⟶ Sp R) (q' : X' ⟶ Sp R) (d : ℕ), IsArithVar q d → IsArithVar q' d → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X' → ∀ (g : X' ⟶ X), g ≫ q = q' → ∀ (hg : g (genericPoint X') ⤳ genericPoint X), g.residueDegree (genericPoint X') ≠ 0 → ∀ η : X, Order.coheight η = 1 → ∀ a : X.functionField, a ≠ 0 → (∑ᶠ ζ : X', if g ζ = η then Scheme.ord (SmallSec.fnMap g hg a) ζ * (g.residueDegree ζ : ℤ) else 0) = (g.residueDegree (genericPoint X') : ℤ) * Scheme.ord a η := by
  intro R _ X X' _ _ _ _ q q' d hq hq' hX hX' g w hg hd η hη a ha
  have := GlobalTheory.IsNormalScheme.of_pred hX
  have := GlobalTheory.IsNormalScheme.of_pred hX'
  have hpr : IsProper q := (isProper_and_exists_isAmpleLB_of_isProjOver hq.isProjOver).1
  have hpr' : IsProper q' := (isProper_and_exists_isAmpleLB_of_isProjOver hq'.isProjOver).1
  have hsep : X.IsSeparated := ⟨by rw [← terminal.comp_from q]; infer_instance⟩
  have : CharZero X.functionField :=
    ((fnOf (⊤ : X.Opens) (TopologicalSpace.Opens.mem_top _)).charZero_iff
      (fnOf_injective ⊤ (TopologicalSpace.Opens.mem_top _))).1 hq.charZero
  have hr := finrank_fnMap g hg
  have hfin : (SmallSec.fnMap g hg).Finite := by
    letI := (SmallSec.fnMap g hg).toAlgebra
    exact Module.finite_of_finrank_pos (hr ▸ Nat.pos_of_ne_zero hd)
  have hN : ValCount.rnorm (SmallSec.fnMap g hg) (SmallSec.fnMap g hg a) =
      a ^ g.residueDegree (genericPoint X') := by
    letI := (SmallSec.fnMap g hg).toAlgebra
    rw [← hr]
    exact Algebra.norm_algebraMap a
  obtain ⟨W, hW⟩ := exists_dominatesStalk η
  have := hW.isDiscreteValuationRing hη
  rw [UpperTheory.order_eq_valuation_codim_one X η W hη hW a, ← ValCount.vord_pow, ← hN,
    (UpperTheory.valuation_norm_sum_extensions _ _ _ hfin W).2.2 _ ((map_ne_zero _).2 ha),
    UpperTheory.order_codim_one_finite_map X X' R q' g hg hfin η W hη hW]
  refine finsum_congr fun V => if_congr (and_iff_left_of_imp ?_) rfl rfl
  intro hV o
  obtain ⟨x, hx, e⟩ := toFF_mem g hg q hW o
  rw [← w, ← e]
  rw [← hV] at hx
  exact hx
