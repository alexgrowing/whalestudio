import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Formalism.LocalToGlobal.ProjectiveLattices.VAtVNeBot
import Formalism.LocalToGlobal.ProjectiveLattices.RulInst
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.FrameTri

open MonoidalCategory CartesianMonoidalCategory MonObj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem comp_list_prod {B : Scheme.{0}} {G T T' : Over B} [GrpObj G] (f : T' ⟶ T) (L : List (T ⟶ G)) :
    f ≫ L.prod = (L.map fun a => f ≫ a).prod := by
  induction L with
  | nil => simpa using MonObj.comp_one f
  | cons a L ih => rw [List.prod_cons, List.map_cons, List.prod_cons, MonObj.comp_mul, ih]

theorem dualMap_comp_algebraMap {S F : Type} [CommRing S] [CommRing F] (ψ : S →+* F) :
    (Formalism.L2.Pj.dualMap ψ).comp (algebraMap S (DualNumber S)) = (algebraMap F (DualNumber F)).comp ψ := by
  ext s <;> simp [Formalism.L2.Pj.dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem dualMap_comp_epsMul' {S F : Type} [CommRing S] [CommRing F] (ψ : S →+* F) (a : S) :
    (Formalism.L2.Pj.dualMap ψ).comp (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul a) =
      (GlobalTheory.CompanionTheory.Ar.epsMul (ψ a)).comp (Formalism.L2.Pj.dualMap ψ) := by
  ext s <;> simp [Formalism.L2.Pj.dualMap, ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul, GlobalTheory.CompanionTheory.Ar.epsMul,
    TrivSqZeroExt.algebraMap_eq_inl]

theorem isComb_of_isCombAt {Xo : Moduli D l} {S F : Type} [CommRing S] [CommRing F] (ψ : S →+* F)
    {x : Sp S ⟶ Xo.X} {x' : Sp F ⟶ Xo.X} (hx : x' = spMap ψ ≫ x) {m : ℕ}
    {vS : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)} {cf : Fin m → S}
    {wS : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (h : Formalism.L2.Pj.IsCombAt x vS cf wS)
    {v : Fin m → (epsAt x' ⟶ Xo.univ.t.G)} {w : epsAt x' ⟶ Xo.univ.t.G}
    (hv : ∀ i, (v i).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ vS i)
    (hw : w.left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ wS) :
    Fl.IsComb (fun i => ψ (cf i)) v w := by
  subst hx
  obtain ⟨u, hu, hp⟩ := h
  have hf : spMap (Formalism.L2.Pj.dualMap ψ) ≫ (Formalism.L2.Pj.tEps x).hom = (epsAt (spMap ψ ≫ x)).hom := by
    show spMap (Formalism.L2.Pj.dualMap ψ) ≫ spMap (algebraMap S (DualNumber S)) ≫ x =
      Spec.map (CommRingCat.ofHom (algebraMap F (DualNumber F))) ≫ spMap ψ ≫ x
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      dualMap_comp_algebraMap]
  let f : epsAt (spMap ψ ≫ x) ⟶ Formalism.L2.Pj.tEps x := Over.homMk (spMap (Formalism.L2.Pj.dualMap ψ)) hf
  refine ⟨fun i => f ≫ u i, fun i => ?_, ?_⟩
  · show spMap (Formalism.L2.Pj.dualMap ψ) ≫ (u i).left = _
    rw [hu i, hv i, ← Category.assoc, ← Category.assoc]
    congr 1
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      dualMap_comp_epsMul']
  · have e : (List.ofFn fun i => f ≫ u i) = (List.ofFn u).map fun a => f ≫ a := by
      rw [List.map_ofFn]; rfl
    rw [e, ← comp_list_prod]
    apply Over.OverMorphism.ext
    rw [hw, ← hp]
    rfl

theorem exists_matrix {Xo : Moduli D l} {S F : Type} [CommRing S] [Field F] (ψ : S →+* F)
    {x : Sp S ⟶ Xo.X} {x' : Sp F ⟶ Xo.X} (hx : x' = spMap ψ ≫ x) {m n : ℕ} (hn : n = m)
    {u u' : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)} (d : Fin m → S)
    (h : ∀ i, ∃ cf : Fin m → S, cf i = d i ∧ (∀ j, i < j → cf j = 0) ∧ Formalism.L2.Pj.IsCombAt x u cf (u' i))
    {v v' : Fin n → (epsAt x' ⟶ Xo.univ.t.G)}
    (hv : ∀ i, (v i).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ u (i.cast hn))
    (hv' : ∀ i, (v' i).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ u' (i.cast hn)) :
    ∃ A : Matrix (Fin n) (Fin n) F, (∀ i, Fl.IsComb (A i) v (v' i)) ∧
      A.det = ∏ i : Fin n, ψ (d (i.cast hn)) := by
  subst hn
  choose cf h1 h2 h3 using h
  refine ⟨Matrix.of fun i j => ψ (cf i j), fun i => ?_, ?_⟩
  · exact isComb_of_isCombAt ψ hx (h3 i) hv (hv' i)
  · rw [Matrix.det_of_lowerTriangular]
    · exact Finset.prod_congr rfl fun i _ => by simp [h1]
    · intro i j hij
      have : i < j := hij
      simp [h2 i j this]

theorem exists_triangular_at_field (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l : Level H) (Xo : Moduli D l) (c : Coeff l) (τ : E →+* ℂ) (S : Type) [CommRing S] [Algebra c.F S]
    (t : Formalism.L2.Pj.Ix D → Sˣ) (z z' : Formalism.L2.Pj.FrPt Xo c S) (hb : Formalism.L2.Pj.FrBor t z z')
    (F : Type) [Field F] (ψ : S →+* F) (y : Sp F ⟶ Xo.XF c) (hp : D.mult τ = D.p)
    (hq : D.mult (ComplexEmbedding.conjugate τ) = D.q) (v v' : Vecs y D.p) (w w' : Vecs y D.q)
    (hy : under y = spMap ψ ≫ z.x)
    (hv : ∀ i, (v i).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u τ (i.cast hp.symm))
    (hw : ∀ j, (w j).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u (ComplexEmbedding.conjugate τ) (j.cast hq.symm))
    (hv' : ∀ i, (v' i).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z'.u τ (i.cast hp.symm))
    (hw' : ∀ j, (w' j).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z'.u (ComplexEmbedding.conjugate τ) (j.cast hq.symm)) :
    ∃ (A : Matrix (Fin D.p) (Fin D.p) F) (B : Matrix (Fin D.q) (Fin D.q) F),
      (∀ i, Fl.IsComb (A i) v (v' i)) ∧ (∀ j, Fl.IsComb (B j) w (w' j)) ∧
      A.det = ∏ i : Fin D.p, ψ (t (some ⟨τ, i.cast hp.symm⟩) : Sˣ) ∧
      B.det = ∏ j : Fin D.q, ψ (t (some ⟨ComplexEmbedding.conjugate τ, j.cast hq.symm⟩) : Sˣ) := by
  obtain ⟨-, hc, -⟩ := hb
  obtain ⟨A, hA, dA⟩ := exists_matrix ψ hy hp.symm (fun i => (t (some ⟨τ, i⟩) : S)) (hc τ) hv hv'
  obtain ⟨B, hB, dB⟩ := exists_matrix ψ hy hq.symm
    (fun i => (t (some ⟨ComplexEmbedding.conjugate τ, i⟩) : S)) (hc (ComplexEmbedding.conjugate τ)) hw hw'
  exact ⟨A, B, hA, hB, dA, dB⟩

end GlobalTheory.CompanionTheory.Ar.Flat.FrameTri
