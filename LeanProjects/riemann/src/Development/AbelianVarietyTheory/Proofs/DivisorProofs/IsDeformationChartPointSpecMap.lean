import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsChartPtChartPt
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
open GlobalTheory.CechKS

set_option autoImplicit false
noncomputable section
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechKS

theorem valR_spMap_comp {Z : Scheme.{0}} {S S' : Type} [CommRing S] [CommRing S'] (σ : S →+* S')
    (z : Sp S ⟶ Z) (U : Z.Opens) (h : ⊤ ≤ z ⁻¹ᵁ U) (f : Γ(Z, U)) :
    valR (spMap σ ≫ z) U f = σ (valR z U f) := by
  have h' := GlobalTheory.FlagMod.le_preimage_comp (spMap σ) h
  rw [valR_eq_ev _ _ h', valR_eq_ev _ _ h, GlobalTheory.FlagMod.ev_spMap σ z U h h']
  rfl

theorem top_le_transl {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {B : Type} [CommRing B] (φ : K →+* B)
    (x : Sp B ⟶ A.left) (hx : x ≫ A.hom = spMap φ) {v : epsR K ⟶ A} (hv : IsTangent v) {U : A.left.Opens}
    (h : ⊤ ≤ x ⁻¹ᵁ U) : ⊤ ≤ (transl φ x v) ⁻¹ᵁ U := by
  intro p _
  have hs : Function.Surjective (spMap (TrivSqZeroExt.fstHom B B B).toRingHom) := by
    intro q
    refine ⟨spMap (algebraMap B (DualNumber B)) q, ?_⟩
    refine PrimeSpectrum.ext (Ideal.ext fun c ↦ ?_)
    change algebraMap B (DualNumber B) c.fst ∈ q.asIdeal ↔ c ∈ q.asIdeal
    have hn : c - algebraMap B (DualNumber B) c.fst ∈ q.asIdeal := by
      refine q.isPrime.mem_of_pow_mem 2 ?_
      have : (c - algebraMap B (DualNumber B) c.fst) ^ 2 = 0 := by
        ext <;> simp [pow_two, TrivSqZeroExt.algebraMap_eq_inl]
      rw [this]; exact zero_mem _
    exact ⟨fun hc ↦ by simpa using add_mem hn hc, fun hc ↦ by simpa using sub_mem hc hn⟩
  obtain ⟨q, rfl⟩ := hs p
  have := h (Set.mem_univ q)
  rw [← (isTransl_transl φ x hx v).red hv] at this
  exact this

theorem transl_spMap {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {B B' : Type} [CommRing B] [CommRing B']
    (φ : K →+* B) (σ : B →+* B') (x : Sp B ⟶ A.left) (hx : x ≫ A.hom = spMap φ) (v : epsR K ⟶ A) :
    transl (σ.comp φ) (spMap σ ≫ x) v = spMap (dualMap σ) ≫ transl φ x v := by
  have hx' : (spMap σ ≫ x) ≫ A.hom = spMap (σ.comp φ) := by
    rw [Category.assoc, hx, Cris.spMap_comp]
  exact (isTransl_transl _ _ hx' v).unique ((isTransl_transl φ x hx v).map σ)

theorem baseMap_eq {K : Type} [Field K] {B B' : Type} [CommRing B] [Algebra (DualNumber K) B] [CommRing B']
    [Algebra (DualNumber K) B'] (ρ : B →ₐ[DualNumber K] B') :
    baseMap K B' = (ρ : B →+* B').comp (baseMap K B) :=
  RingHom.ext fun k ↦ by simp [baseMap]

theorem dualMap_snd {B B' : Type} [CommRing B] [CommRing B'] (σ : B →+* B') (c : DualNumber B) :
    (dualMap σ c).snd = σ c.snd := by
  simp [dualMap]

section Map

variable {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A]
  {B B' : Type} [CommRing B] [Algebra (DualNumber K) B] [CommRing B'] [Algebra (DualNumber K) B']

theorem dlogAt_spMap (ρ : B →ₐ[DualNumber K] B') {x : Sp B ⟶ A.left}
    (hx : x ≫ A.hom = spMap (baseMap K B)) {v : epsR K ⟶ A} (hv : IsTangent v) {Wo : A.left.Opens}
    (g : Γ(A.left, Wo)ˣ) (hxWo : ⊤ ≤ x ⁻¹ᵁ Wo) :
    dlogAt (baseMap K B') (spMap (ρ : B →+* B') ≫ x) v Wo g = ρ (dlogAt (baseMap K B) x v Wo g) := by
  rw [dlogAt, dlogAt, baseMap_eq ρ, transl_spMap _ _ x hx v,
    valR_spMap_comp _ _ _ (top_le_transl _ x hx hv hxWo), valR_spMap_comp _ _ _ hxWo, dualMap_snd, map_mul]
  rfl

theorem chartVal_spMap {Z : Scheme.{0}} (m : A.left ⟶ Z) (Ω : Z.Opens) (δ : Γ(Z, Ω) → Γ(Z, Ω))
    {n : ℕ} (u : Fin n → (epsR K ⟶ A)) (θ : Matrix (Fin n) (Fin n) K) (Wo : A.left.Opens) (g : Γ(A.left, Wo)ˣ)
    (ρ : B →ₐ[DualNumber K] B') {x : Sp B ⟶ A.left}
    (hx : x ≫ A.hom = spMap (baseMap K B)) (hxΩ : ⊤ ≤ x ⁻¹ᵁ (m ⁻¹ᵁ Ω)) (hxWo : ⊤ ≤ x ⁻¹ᵁ Wo)
    (hut : ∀ a, IsTangent (u a)) (f : Γ(Z, Ω)) :
    chartVal m Ω δ u θ Wo g (spMap (ρ : B →+* B') ≫ x) f = ρ (chartVal m Ω δ u θ Wo g x f) := by
  have hxm : ⊤ ≤ (x ≫ m) ⁻¹ᵁ Ω := hxΩ
  have ht : ∀ a, ⊤ ≤ (transl (baseMap K B) x (u a) ≫ m) ⁻¹ᵁ Ω := fun a ↦
    top_le_transl _ x hx (hut a) hxΩ
  have hd : ∀ b, dlogAt (baseMap K B') (spMap (ρ : B →+* B') ≫ x) (u b) Wo g =
      ρ (dlogAt (baseMap K B) x (u b) Wo g) := fun b ↦ dlogAt_spMap ρ hx (hut b) g hxWo
  have htr : ∀ a, transl (baseMap K B') (spMap (ρ : B →+* B') ≫ x) (u a) =
      spMap (dualMap (ρ : B →+* B')) ≫ transl (baseMap K B) x (u a) := fun a ↦ by
    rw [baseMap_eq ρ]; exact transl_spMap _ _ x hx (u a)
  simp only [chartVal, hd, htr, Category.assoc]
  simp only [valR_spMap_comp _ _ _ hxm, valR_spMap_comp _ _ _ (ht _), dualMap_snd, map_add, map_mul, map_sum]
  simp only [RingHom.coe_coe, AlgHom.commutes, baseMap_eq ρ, RingHom.comp_apply]

end Map

theorem isChartPt_spMap : ∀ {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {A' : Over (Sp (DualNumber K))} {Z : Scheme.{0}} {m : A.left ⟶ Z} {m' : A'.left ⟶ Z} {Ω : Z.Opens} {δ : Γ(Z, Ω) → Γ(Z, Ω)} {n : ℕ} {u : Fin n → (epsR K ⟶ A)} {θ : Matrix (Fin n) (Fin n) K} {Wo : A.left.Opens} {g : Γ(A.left, Wo)ˣ} {B : Type} [CommRing B] [Algebra (DualNumber K) B] {x : Sp B ⟶ A.left} {l : Sp B ⟶ A'.left} (hx : x ≫ A.hom = spMap (baseMap K B)) (hxΩ : ⊤ ≤ x ⁻¹ᵁ (m ⁻¹ᵁ Ω)) (hxWo : ⊤ ≤ x ⁻¹ᵁ Wo) (hut : ∀ a, IsTangent (u a)) (hl : IsChartPt A' m m' Ω δ u θ Wo g x l) (B' : Type) [CommRing B'] [Algebra (DualNumber K) B'] (ρ : B →ₐ[DualNumber K] B'), IsChartPt A' m m' Ω δ u θ Wo g (spMap (ρ : B →+* B') ≫ x) (spMap (ρ : B →+* B') ≫ l) := by
  intro K _ A _ A' Z m m' Ω δ n u θ Wo g B _ _ x l hx hxΩ hxWo hut hl B' _ _ ρ
  obtain ⟨h1, h2, h3⟩ := hl
  refine ⟨?_, ?_, fun f ↦ ?_⟩
  · rw [Category.assoc, h1, ← Cris.spMap_comp, AlgHom.comp_algebraMap]
  · rw [Category.assoc]
    exact GlobalTheory.FlagMod.le_preimage_comp _ h2
  · rw [Category.assoc, valR_spMap_comp _ _ _ h2, h3 f, chartVal_spMap m Ω δ u θ Wo g ρ hx hxΩ hxWo hut f]
    rfl

end GlobalTheory.CechKS
