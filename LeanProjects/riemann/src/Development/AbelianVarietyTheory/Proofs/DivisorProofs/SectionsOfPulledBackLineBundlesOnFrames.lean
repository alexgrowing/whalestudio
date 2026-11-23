import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleLBOfFiniteFibres
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetMulExpand
open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.FlagMod GlobalTheory.FlagPlucker

namespace GlobalTheory.FlagPlucker

theorem det_mul_eq_sum_fun {R : Type} [CommRing R] {i N : ℕ} (A : Matrix (Fin i) (Fin N) R)
    (B : Matrix (Fin N) (Fin i) R) :
    (A * B).det = ∑ f : Fin i → Fin N, (∏ a, A a (f a)) * (B.submatrix f id).det :=
  _root_.GlobalTheory.DeterminantProductExpansion.main A B

theorem exists_sum_minors_eq_one {R : Type} [CommRing R] {n k d : ℕ} (hd : d ≤ k) (A : Matrix (Fin n) (Fin k) R)
    (B : Matrix (Fin k) (Fin n) R) (hBA : B * A = 1) :
    ∃ c : (Fin d → Fin n) → R, ∑ r, c r * (A.submatrix r (Fin.castLE hd)).det = 1 := by
  have e : B.submatrix (Fin.castLE hd) id * A.submatrix id (Fin.castLE hd) = 1 := by
    rw [← Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, hBA,
      Matrix.submatrix_one _ (Fin.castLE_injective _)]
  refine ⟨fun r => ∏ a, B (Fin.castLE hd a) (r a), ?_⟩
  have := congrArg Matrix.det e
  rw [det_mul_eq_sum_fun, Matrix.det_one] at this
  exact this

end GlobalTheory.FlagPlucker

noncomputable section
namespace GlobalTheory.FlagPlucker

open GlobalTheory.FlagMod Formalism.L2.Pj MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {Z : Scheme.{0}} {π : Z ⟶ Y.X}

theorem exists_mul_plkU_eq_one (F : Frames Y π) (Mc : MChart Y) (k : F.J) (σ : E →+* ℂ) :
    ∃ B : Matrix (Fin (Dw.mult σ)) (Fin Mc.n) Γ(Z, F.U k ⊓ π ⁻¹ᵁ Mc.U), B * plkU F Mc k σ = 1 := by
  obtain ⟨w, hw⟩ := F.split k σ
  have hm : ∀ (M M' : MChart Y) (hle : F.U k ⊓ π ⁻¹ᵁ Mc.U ≤ π ⁻¹ᵁ (M.U ⊓ M'.U)) (S : Type) [CommRing S]
      (z : Sp S ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ (F.U k ⊓ π ⁻¹ᵁ Mc.U)),
      ((chg M M').map (π.appLE _ _ hle).hom).map (ev z _ hz) =
        (chg M M').map (ev (z ≫ π) _ (le_preimage_map π hle hz)) := by
    intro M M' hle S _ z hz
    rw [Matrix.map_map]
    ext a b
    exact ev_appLE z π hle hz _ _
  have hle1 : F.U k ⊓ π ⁻¹ᵁ Mc.U ≤ π ⁻¹ᵁ ((F.M k).U ⊓ Mc.U) := fun _ hp => ⟨F.le k hp.1, hp.2⟩
  have hle2 : F.U k ⊓ π ⁻¹ᵁ Mc.U ≤ π ⁻¹ᵁ (Mc.U ⊓ (F.M k).U) := fun _ hp => ⟨hp.2, F.le k hp.1⟩
  have hC : (chg (F.M k).toMChart Mc).map (π.appLE _ _ hle1).hom *
      (chg Mc (F.M k).toMChart).map (π.appLE _ _ hle2).hom = 1 := by
    ext i j
    refine ext_ev fun S _ z hz => ?_
    have e : (((chg (F.M k).toMChart Mc).map (π.appLE _ _ hle1).hom *
        (chg Mc (F.M k).toMChart).map (π.appLE _ _ hle2).hom)).map (ev z _ hz) =
        (1 : Matrix (Fin (F.M k).n) (Fin (F.M k).n) Γ(Z, F.U k ⊓ π ⁻¹ᵁ Mc.U)).map (ev z _ hz) := by
      have hx := le_preimage_map π hle1 hz
      have hx' := le_preimage_map π hle2 hz
      rw [Matrix.map_mul, hm _ _ hle1, hm _ _ hle2,
        chg_map _ _ (z ≫ π) (le_preimage_mono inf_le_left hx) (le_preimage_mono inf_le_right hx),
        chg_map _ _ (z ≫ π) (le_preimage_mono inf_le_left hx') (le_preimage_mono inf_le_right hx'),
        Module.Basis.toMatrix_mul_toMatrix,
        Module.Basis.toMatrix_self, Matrix.map_one _ (map_zero _) (map_one _)]
    exact congrFun (congrFun e i) j
  refine ⟨(w.map (resG Z (inf_le_left : F.U k ⊓ π ⁻¹ᵁ Mc.U ≤ F.U k))) *
    (chg (F.M k).toMChart Mc).map (π.appLE _ _ hle1).hom, ?_⟩
  unfold plkU
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc ((chg (F.M k).toMChart Mc).map _), hC, Matrix.one_mul,
    ← Matrix.map_mul, hw, Matrix.map_one _ (map_zero _) (map_one _)]

theorem exists_mem_basicOpen_plkMinor (F : Frames Y π) (Mc : MChart Y) (k : F.J) (σ : E →+* ℂ)
    (m : Fin (Dw.mult σ)) (z : Z) (hz : z ∈ F.U k ⊓ π ⁻¹ᵁ Mc.U) :
    ∃ r, z ∈ Z.basicOpen (plkMinor F Mc k σ m r) := by
  obtain ⟨B, hB⟩ := exists_mul_plkU_eq_one F Mc k σ
  obtain ⟨cf, hc⟩ := exists_sum_minors_eq_one (d := (m : ℕ) + 1) m.2 _ B hB
  by_contra hno
  push_neg at hno
  have hmax : (Z.presheaf.germ _ z hz).hom (∑ r, cf r * plkMinor F Mc k σ m r) ∈
      IsLocalRing.maximalIdeal (Z.presheaf.stalk z) := by
    rw [map_sum]
    refine Ideal.sum_mem _ fun r _ => ?_
    rw [map_mul]
    refine Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).2 fun hu => hno r ?_)
    exact (Scheme.mem_basicOpen Z _ z hz).2 hu
  have h1 : ∑ r, cf r * plkMinor F Mc k σ m r = 1 := hc
  rw [h1, map_one] at hmax
  exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).2 hmax)

end GlobalTheory.FlagPlucker
end

noncomputable section
namespace GlobalTheory.FlagPlucker

open GlobalTheory.FlagMod Formalism.L2.Pj

theorem iSup_nonzeroLocus_plk : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {Z : Scheme.{0}} {π : Z ⟶ Y.X} (F : Frames Y π) (Mc : MChart Y) {T : Scheme.{0}} (g : T ⟶ Z) (hg : ⊤ ≤ (g ≫ π) ⁻¹ᵁ Mc.U) (σ : E →+* ℂ) (m : Fin (Dw.mult σ)) (t : Fin (plkNum Mc m + 1) → ((F.LL (ind σ m)).pull g).Sec), (∀ q, (t q).f = plkLoc F Mc g hg σ m q) → ⨆ q, nonzeroLocus (t q) = ⊤ := by
  intro E _ _ _ H Dw l Xo c O _ β Y Z π F Mc T g hg σ m t ht
  refine eq_top_iff.2 fun p _ => ?_
  obtain ⟨k, hk⟩ : ∃ k, g.base p ∈ F.U k := by
    have : g.base p ∈ (⨆ k, F.U k) := by rw [F.cover]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 this
  have hpM : g.base p ∈ π ⁻¹ᵁ Mc.U := by
    have := hg (show p ∈ (⊤ : T.Opens) from trivial)
    simpa using this
  obtain ⟨r, hr⟩ := exists_mem_basicOpen_plkMinor F Mc k σ m (g.base p) ⟨hk, hpM⟩
  let j : ((F.LL (ind σ m)).pull g).ι := fun _ => k
  have hpj : p ∈ ((F.LL (ind σ m)).pull g).U j := mem_pull.2 hk
  let q : Fin (plkNum Mc m + 1) := Fin.succ (Fintype.equivFin _ r)
  have hq : plkIdx Mc m q = some r := by simp [q, plkIdx]
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨q, (mem_nonzeroLocus_iff_basicOpen (t q) hpj).2 ?_⟩
  rw [congrFun (ht q) j]
  unfold plkLoc
  split
  · rename_i h; rw [hq] at h; exact absurd h (by simp)
  · rename_i r' h
    rw [hq] at h
    cases h
    rw [Scheme.basicOpen_appLE]
    exact ⟨hpj, hr⟩

end GlobalTheory.FlagPlucker
end
