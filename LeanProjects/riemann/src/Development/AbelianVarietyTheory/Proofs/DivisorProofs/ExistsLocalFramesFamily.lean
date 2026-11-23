import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalModelNonvanishingWeights
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open GlobalTheory GlobalTheory.QCoh GlobalTheory.Vert GlobalTheory.MixedLocalChains

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.MinorDivide

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.VB GlobalTheory.CechPic
open GlobalTheory.TrueGeo.SmallSec (fnMap)

theorem chart_pullback {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (φ : Y ⟶ X)
    (hη : φ (genericPoint Y) ⤳ genericPoint X) {r m : ℕ} {E F : X.Modules}
    [SheafOfModules.IsQuasicoherent E] [SheafOfModules.IsQuasicoherent F] (u : F ⟶ E) {V : X.Opens}
    (hV : genericPoint X ∈ V)
    (eF : Fin m → Γ(F, V)) (eE : Fin r → Γ(E, V)) (a : Matrix (Fin r) (Fin m) Γ(X, V))
    (hF : IsFrame eF) (hE : IsFrame eE) (hu : ∀ j, u.app V (eF j) = ∑ k, a k j • eE k)
    (J : Fin r → Fin m) (y : Y) (hy : y ∈ φ ⁻¹ᵁ V)
    (hJ : fnOf V hV (a.submatrix id J).det ≠ 0)
    (hdiv : ∀ K : Fin r → Fin m, ∃ g, RegAt y g ∧
      g * fnMap φ hη (fnOf V hV (a.submatrix id J).det) = fnMap φ hη (fnOf V hV (a.submatrix id K).det)) :
    ∃ (V' : Y.Opens) (eF' : Fin m → Γ((Scheme.Modules.pullback φ).obj F, V'))
      (eE' : Fin r → Γ((Scheme.Modules.pullback φ).obj E, V')) (a' : Matrix (Fin r) (Fin m) Γ(Y, V')),
      y ∈ V' ∧ IsFrame eF' ∧ IsFrame eE' ∧
      (∀ j, ((Scheme.Modules.pullback φ).map u).app V' (eF' j) = ∑ k, a' k j • eE' k) ∧
      (a'.submatrix id J).det ≠ 0 ∧
      ∀ K : Fin r → Fin m, (a'.submatrix id J).det ∣ (a'.submatrix id K).det := by
  classical
  choose g hg hgJ using hdiv
  obtain ⟨W, hyW, hW⟩ := InvertIdeal.exists_common_open (x := y) hg
  choose s hs using hW
  have hle : W ⊓ φ ⁻¹ᵁ V ≤ φ ⁻¹ᵁ V := inf_le_right
  have hyV' : y ∈ W ⊓ φ ⁻¹ᵁ V := ⟨hyW, hy⟩
  have hgV' : genericPoint Y ∈ W ⊓ φ ⁻¹ᵁ V := gen_mem hyV'
  have hres (G : X.Modules) (t : Γ(G, V)) :
      Twist.resM _ hle (pullbackSections φ G le_rfl t) = pullbackSections φ G hle t :=
    res_pullbackSections φ G le_rfl hle t
  have hF' : IsFrame fun j => pullbackSections φ F hle (eF j) := by
    simpa only [hres] using (hF.pullback φ).res hle
  have hE' : IsFrame fun k => pullbackSections φ E hle (eE k) := by
    simpa only [hres] using (hE.pullback φ).res hle
  have hfn (K : Fin r → Fin m) : fnOf _ hgV' ((a.map (φ.appLE V _ hle).hom).submatrix id K).det =
      fnMap φ hη (fnOf V hV (a.submatrix id K).det) := by
    rw [CorankOne.fnMap_fnOf_appLE φ hη hle hV hgV', RingHom.map_det (φ.appLE V _ hle).hom]
    rfl
  refine ⟨_, _, _, a.map (φ.appLE V _ hle).hom, hyV', hF', hE', fun j => ?_, fun h0 => ?_, fun K => ?_⟩
  · rw [pullback_map_app_pullbackSections, hu, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [pullbackSections_smul]
    rfl
  · have e := hfn J
    rw [h0, map_zero] at e
    exact hJ ((map_eq_zero_iff _ (fnMap φ hη).injective).1 e.symm)
  · refine ⟨resG Y inf_le_left (s K), fnOf_injective _ hgV' ?_⟩
    rw [map_mul, hfn, hfn, fnOf_resG, hs, mul_comm, hgJ]

theorem exists_modification_minor_dvd : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (B : GlobalTheory.Vert.Model O), GlobalTheory.IsNormalScheme B.X → ∀ (n : ℕ) (r m : Fin n → ℕ) (E F : Fin n → B.X.Modules) (u : ∀ i, F i ⟶ E i), (∀ (i : Fin n) (x : B.X), ∃ (V : B.X.Opens) (eF : Fin (m i) → Γ(F i, V)) (eE : Fin (r i) → Γ(E i, V)) (a : Matrix (Fin (r i)) (Fin (m i)) Γ(B.X, V)), x ∈ V ∧ IsAffineOpen V ∧ GlobalTheory.VB.IsFrame eF ∧ GlobalTheory.VB.IsFrame eE ∧ (∀ j, (u i).app V (eF j) = ∑ k, a k j • eE k) ∧ ∃ J : Fin (r i) → Fin (m i), (a.submatrix id J).det ≠ 0) → ∃ (B' : GlobalTheory.Vert.Model O) (f : GlobalTheory.Vert.Model.Hom B' B), GlobalTheory.IsNormalScheme B'.X ∧ f.relDim = 0 ∧ ∀ (i : Fin n) (y : B'.X), ∃ (V : B'.X.Opens) (eF : Fin (m i) → Γ((Scheme.Modules.pullback f.f).obj (F i), V)) (eE : Fin (r i) → Γ((Scheme.Modules.pullback f.f).obj (E i), V)) (a : Matrix (Fin (r i)) (Fin (m i)) Γ(B'.X, V)) (J : Fin (r i) → Fin (m i)), y ∈ V ∧ GlobalTheory.VB.IsFrame eF ∧ GlobalTheory.VB.IsFrame eE ∧ (∀ j, ((Scheme.Modules.pullback f.f).map (u i)).app V (eF j) = ∑ k, a k j • eE k) ∧ (a.submatrix id J).det ≠ 0 ∧ ∀ K : Fin (r i) → Fin (m i), (a.submatrix id J).det ∣ (a.submatrix id K).det := by
  intro O _ _ _ _ B hn n r m E F u H
  classical
  choose V eF eE a hxV _ hF hE hu J hJ using H
  have hqF (i : Fin n) : SheafOfModules.IsQuasicoherent (F i) :=
    IsVB.isQuasicoherent (r := m i) fun x => ⟨V i x, eF i x, hxV i x, hF i x⟩
  have hqE (i : Fin n) : SheafOfModules.IsQuasicoherent (E i) :=
    IsVB.isQuasicoherent (r := r i) fun x => ⟨V i x, eE i x, hxV i x, hE i x⟩
  choose t ht using fun i => CompactSpace.elim_nhds_subcover (fun x => (V i x : Set B.X))
    fun x => (V i x).isOpen.mem_nhds (hxV i x)
  let D : ∀ α : (Σ i, (t i : Set B.X)), (Fin (r α.1) → Fin (m α.1)) → B.X.functionField :=
    fun α K => fnOf (V α.1 α.2) (gen_mem (hxV α.1 α.2)) ((a α.1 α.2).submatrix id K).det
  let w : (Σ i, (t i : Set B.X)) → (Σ i, (Fin (r i) → Fin (m i))) → B.X.functionField :=
    fun α j => if h : j.1 = α.1 then D α (h ▸ j.2) else 0
  have hw (i : Fin n) (x : B.X) (hx : x ∈ (t i : Set B.X)) (K : Fin (r i) → Fin (m i)) :
      w ⟨i, ⟨x, hx⟩⟩ ⟨i, K⟩ = D ⟨i, ⟨x, hx⟩⟩ K := by
    simp only [w, dif_pos rfl]
  have hw0 : ∀ α, ∃ j, w α j ≠ 0 := by
    rintro ⟨i, x, hx⟩
    refine ⟨⟨i, J i x⟩, ?_⟩
    rw [hw]
    exact (map_ne_zero_iff _ (fnOf_injective _ _)).2 (hJ i x)
  obtain ⟨B', f, hη, hN', hrel, hmod⟩ := CorankOneNormal.exists_modification O B hn _ _ w hw0
  refine ⟨B', f, hN', hrel, fun i y => ?_⟩
  have hm : f.f y ∈ ⋃ x ∈ t i, (V i x : Set B.X) := by rw [ht i]; trivial
  obtain ⟨x, hxt, hfy⟩ := Set.mem_iUnion₂.1 hm
  obtain ⟨⟨i', K₀⟩, hK₀, hdiv⟩ := hmod y ⟨i, ⟨x, hxt⟩⟩
  by_cases h : i' = i
  · subst h
    rw [hw] at hK₀
    obtain ⟨V', eF', eE', a', h1, h2, h3, h4, h5, h6⟩ := chart_pullback f.f (specializes_of_eq hη) (u i')
      (gen_mem (hxV i' x)) (eF i' x) (eE i' x) (a i' x) (hF i' x) (hE i' x) (hu i' x) K₀ y hfy hK₀
      fun K => by
        obtain ⟨g, hg, e⟩ := hdiv ⟨i', K⟩
        rw [hw, hw] at e
        exact ⟨g, hg, e⟩
    exact ⟨V', eF', eE', a', K₀, h1, h2, h3, h4, h5, h6⟩
  · exact absurd (dif_neg h) hK₀

end GlobalTheory.MinorDivide
