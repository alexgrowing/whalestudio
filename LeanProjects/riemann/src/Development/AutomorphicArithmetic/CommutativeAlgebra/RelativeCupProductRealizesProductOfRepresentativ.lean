import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.FaceRes
import Development.AutomorphicArithmetic.CommutativeAlgebra.MemPullbackImageIffFactorsThroughOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCochainEvalOnSimplexBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceSimplicesOverSubCompositeStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.CohomologicalPurity LateralTheory.CohomologicalPurity.TubeCut UpperTheory.Et.Prd

private theorem inl_fold' (P : Arrow Spc) : dbl.inl P ≫ dbl.fold P = 𝟙 _ := pushout.inl_desc _ _ _

private theorem inl_map' {P' P : Arrow Spc} (φ : P' ⟶ P) : dbl.inl P' ≫ dbl.map φ = φ.right ≫ dbl.inl P :=
  pushout.inl_desc _ _ _

private theorem aw_last {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) {D : Spc} {n m : ℤ}
    (α : Cochain ((chains R).obj D) I n) (β : Cochain ((chains R).obj D) J m) {W : Scheme.{0}} {p : ℕ}
    (x : Sx D p W) (b : Sec (J.X m) W) (hp : p + 0 ≤ p)
    (hb : ev β 0 m (by simp) W (x.sub p 0 hp) = b) (r k : ℕ) (hr : r = p) (hk : k = 0) (s t w : ℤ) (h : s + t = w)
    (hs : -(r : ℤ) + n = s) (ht : -(k : ℤ) + m = t) (h0 : 0 + r ≤ p) (h1 : r + k ≤ p)
    (s' : ℤ) (hs' : -(p : ℤ) + n = s') (h' : s' + m = w) :
    μ.mul W s t w h (ev α r s hs W (x.sub 0 r h0)) (ev β k t ht W (x.sub r k h1)) =
      μ.mul W s' m w h' (ev α p s' hs' W x) b := by
  subst hr hk
  have ht' : m = t := by simpa using ht
  subst ht'
  subst hs
  subst hs'
  rw [(GlobalTheory.T.etaleSpaceSimplicesOver_sub_composite x).2.1, hb]

private theorem aw_eval {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) {D : Spc} {n m : ℤ}
    (α : Cochain ((chains R).obj D) I n) (β : Cochain ((chains R).obj D) J m)
    (γ : Cochain ((chains R).obj D) K (n + m)) (hγ : μ.IsAW rfl α β γ)
    (hβ : ∀ (k : ℕ), 0 < k → ∀ (s : ℤ) h (W : Scheme.{0}) (y : Sx D k W), ev β k s h W y = 0)
    {W : Scheme.{0}} {p : ℕ} (x : Sx D p W) (b : Sec (J.X m) W) (hp : p + 0 ≤ p)
    (hb : ev β 0 m (by simp) W (x.sub p 0 hp) = b) (w : ℤ) (h : -(p : ℤ) + (n + m) = w)
    (s : ℤ) (hs : -(p : ℤ) + n = s) (h' : s + m = w) :
    ev γ p w h W x = (m * (p : ℕ)).negOnePow • μ.mul W s m w h' (ev α p s hs W x) b := by
  rw [hγ p w h W x, Fin.sum_univ_castSucc, Finset.sum_eq_zero, zero_add]
  · exact congrArg _ (aw_last μ α β x b hp hb _ _ rfl (Nat.sub_self p) _ _ _ _ _ _ _ _ s hs h')
  · intro r _
    have hk : 0 < p - ((Fin.castSucc r : Fin (p + 1)) : ℕ) := by
      have := r.2
      simp only [Fin.val_castSucc]
      omega
    rw [hβ _ hk, map_zero, smul_zero]

private theorem last_vertex {X : Scheme.{0}} (U : X.Opens) {E : Spc} (π : E ⟶ sch.obj X) {p : ℕ} {W : Scheme.{0}}
    (z : Sx E p W) (h : p + 0 ≤ p) (ι' : E ⟶ dbl (abv U π)) (ι : sch.obj X ⟶ dbl (opn U))
    (hι : ι' ≫ dbl.map (abvMap U π) = π ≫ ι) :
    ((z.map ι').sub p 0 h).map (dbl.map (abvMap U π)) = Sx.map (E := sch.obj X) (p := 0) ι (under π z) := by
  rw [((GlobalTheory.T.etaleSpaceSimplicesOver_sub_composite z).2.2.1 p 0 h).2.1 ι']
  have h1 : ((z.sub p 0 h).map ι').map (dbl.map (abvMap U π)) = (z.sub p 0 h).map (ι' ≫ dbl.map (abvMap U π)) := rfl
  rw [h1, hι]
  have h2 : (z.sub p 0 h).map (π ≫ ι) = Sx.map (E := sch.obj X) (p := 0) ι (under π (z.sub p 0 h)) := rfl
  rw [h2, ((GlobalTheory.T.etaleSpaceSimplicesOver_sub_composite z).2.2.1 p 0 h).2.2, (UpperTheory.mem_pullbackImage_iff_factors_through_open U π p W z).2.2 0 _]

theorem UpperTheory.relativeCupProduct_realizes_product_of_representative :
    LeafAW → ∀ (q : ℕ) [NeZero q] {X : Scheme.{0}} (U : X.Opens) {E : Spc} (π : E ⟶ sch.obj X) (m j i n : ℤ) (c : Hs q (opn U) m j) (β : Sec ((res _ (tw q j)).X m) X), IsRep U β c.1 →
    ∀ Φ : (famDC (Sub.bot E) (res _ (tw q i)) 0).Hom (famDC (Sub.img (E := E) (pullback.fst π (sch.map U.ι))) (res _ (tw q (i + j))) m), IsProd (twPair q i j) π β Φ →
    ∀ (x : (famDC (Sub.bot E) (res _ (tw q i)) 0).Tot) (a : Ht q E n i), HRel x a → SRel (P := abv U π) (N := n + m) (Φ.tot x) (Hs.act q (P := abv U π) a (Hs.pull q (abvMap U π) _ _ c)).1 := by
  intro hAW q _ X U E π m j i n c β hrep Φ hΦ x a hx
  obtain ⟨-, -, γ₀, hγ₀, h0l, h0r, h0p⟩ := hrep
  obtain ⟨α, hα, hαx⟩ := hx
  let α' : Cocycle ((chains _).obj (dbl (abv U π))) (res _ (tw q i)) n :=
    zcomp (Cocycle.ofHom ((chains _).map (dbl.fold (abv U π)))) α (zero_add n)
  let β' : Cocycle ((chains _).obj (dbl (abv U π))) (res _ (tw q j)) m :=
    zcomp (Cocycle.ofHom ((chains _).map (dbl.map (abvMap U π)))) γ₀ (zero_add m)
  obtain ⟨γ, hγ, hcup⟩ := (hAW q i j).2 (dbl (abv U π)) n m α' β'
  have evα : ∀ (p : ℕ) (s : ℤ) h (W : Scheme.{0}) (y : Sx (dbl (abv U π)) p W),
      ev α'.1 p s h W y = ev α.1 p s h W (y.map (dbl.fold (abv U π))) := fun p s h W y =>
    (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties _).2.2.2.1 (dbl.fold (abv U π)) α.1 p s h W y
  have evβ : ∀ (p : ℕ) (s : ℤ) h (W : Scheme.{0}) (y : Sx (dbl (abv U π)) p W),
      ev β'.1 p s h W y = ev γ₀.1 p s h W (y.map (dbl.map (abvMap U π))) := fun p s h W y =>
    (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties _).2.2.2.1 (dbl.map (abvMap U π)) γ₀.1 p s h W y
  have hvan : ∀ (k : ℕ), 0 < k → ∀ (s : ℤ) h (W : Scheme.{0}) (y : Sx (dbl (abv U π)) k W), ev β'.1 k s h W y = 0 := by
    intro k hk s h W y
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [evβ]
    exact h0p k s _ W _
  have hinr : ∀ (p : ℕ) (s : ℤ) h (W : Scheme.{0}) (z : Sx (abv U π).right p W),
      ev γ.1 p s h W (z.map (dbl.inr (abv U π))) = 0 := by
    intro p s h W z
    have hb : ev β'.1 0 m (by simp) W ((z.map (dbl.inr (abv U π))).sub p 0 (by omega)) = 0 := by
      rw [evβ]
      refine (congrArg (fun y => ev γ₀.1 0 m (by simp) W y)
        (last_vertex U π z (by omega) (dbl.inr (abv U π)) (dbl.inr (opn U)) (dbl.inr_map (abvMap U π)))).trans ?_
      exact h0r W _
    rw [aw_eval _ α'.1 β'.1 γ.1 hγ hvan _ 0 (by omega) hb s h (-(p : ℤ) + n) rfl (by omega), map_zero, smul_zero]
  refine ⟨γ, ?_, ?_, hinr⟩
  · have hC : cup q (pull _ (dbl.fold (abv U π)) _ n a) (Hs.pull q (abvMap U π) _ _ c).1 = CohomologyClass.mk γ := by
      rw [← hcup, ← hα]
      change cup q _ (pull _ (dbl.map (abvMap U π)) _ m c.1) = _
      rw [← hγ₀]
      rfl
    have hz : pull _ (dbl.inr (abv U π)) (tw q (i + j)) (n + m) (CohomologyClass.mk γ) = 0 := by
      have h0 : zcomp (Cocycle.ofHom ((chains _).map (dbl.inr (abv U π)))) γ (zero_add (n + m)) = 0 := by
        have hc : (zcomp (Cocycle.ofHom ((chains _).map (dbl.inr (abv U π)))) γ (zero_add (n + m))).1 = 0 := by
          refine (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties _).2.2.1 _ _ fun p s h W z => ?_
          rw [((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties _).1 0 0 p s h W z).2.2.1]
          exact ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties _).2.2.2.1 (dbl.inr (abv U π)) γ.1 p s h W z).trans (hinr p s h W z)
        exact Cocycle.ext hc
      exact (congrArg CohomologyClass.mk h0).trans (CohomologyClass.mk_zero _ _ _)
    change CohomologyClass.mk γ = cup q (pull _ (dbl.fold (abv U π)) _ n a) (Hs.pull q (abvMap U π) _ _ c).1 -
      pull _ (dbl.fold (abv U π)) _ _ (pull _ (dbl.inr (abv U π)) _ _
        (cup q (pull _ (dbl.fold (abv U π)) _ n a) (Hs.pull q (abvMap U π) _ _ c).1))
    rw [hC, hz, map_zero, sub_zero]
  · intro p s h W z
    have hs : -(p : ℤ) + n = s + 0 := by omega
    have hb : ev β'.1 0 m (by simp) W ((z.map (dbl.inl (abv U π))).sub p 0 (by omega)) = Sec.res (under π z) β := by
      rw [evβ]
      refine (congrArg (fun y => ev γ₀.1 0 m (by simp) W y)
        (last_vertex U π z (by omega) (dbl.inl (abv U π)) (dbl.inl (opn U)) (inl_map' (abvMap U π)))).trans ?_
      exact h0l W _
    have e := hΦ p s (x p s) W z
    rw [hαx p s hs W z] at e
    refine e.trans ?_
    rw [aw_eval _ α'.1 β'.1 γ.1 hγ hvan _ _ (by omega) hb (s + m) h (s + 0) hs (by omega), evα]
    have hf : (z.map (dbl.inl (abv U π))).map (dbl.fold (abv U π)) = z.map (𝟙 E) := by
      have h1 : (z.map (dbl.inl (abv U π))).map (dbl.fold (abv U π)) = z.map (dbl.inl (abv U π) ≫ dbl.fold (abv U π)) := rfl
      rw [h1, inl_fold']
      rfl
    rw [hf]
