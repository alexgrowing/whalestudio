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

namespace GlobalTheory.CechKS

theorem valR_comp_app {Y Z : Scheme.{0}} {S : Type} [CommRing S] (z : Sp S ⟶ Y) (m : Y ⟶ Z) (O : Z.Opens)
    (f : Γ(Z, O)) : valR (z ≫ m) O f = valR z (m ⁻¹ᵁ O) ((m.app O).hom f) := by
  by_cases h : ⊤ ≤ z ⁻¹ᵁ (m ⁻¹ᵁ O)
  · rw [valR_eq_ev _ _ h, valR_eq_ev (z ≫ m) O h, ← GlobalTheory.FlagMod.ev_appLE z m le_rfl h h, Scheme.Hom.appLE_eq_app]
  · rw [valR, valR, dif_neg h]
    exact dif_neg h

theorem le_preimage_of_red {Y : Scheme.{0}} {B : Type} [CommRing B] {x : Sp B ⟶ Y} {w : Sp (DualNumber B) ⟶ Y}
    (hw : spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ w = x) {O : Y.Opens} (h : ⊤ ≤ x ⁻¹ᵁ O) : ⊤ ≤ w ⁻¹ᵁ O := by
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
  rw [← hw] at this
  exact this

theorem valR_resG {Z : Scheme.{0}} {S : Type} [CommRing S] (z : Sp S ⟶ Z) {U V : Z.Opens} (e : V ≤ U)
    (h : ⊤ ≤ z ⁻¹ᵁ V) (a : Γ(Z, U)) : valR z V (resG Z e a) = valR z U a := by
  rw [valR_eq_ev _ _ h, valR_eq_ev _ _ (GlobalTheory.FlagMod.le_preimage_mono e h), GlobalTheory.FlagMod.ev_res]

theorem isAffineHom_of_field {K : Type} [Field K] {X : Scheme.{0}} (x0 : Sp K ⟶ X) : IsAffineHom x0 := by
  refine ⟨fun U _ => ?_⟩
  by_cases h : (default : PrimeSpectrum K) ∈ x0 ⁻¹ᵁ U
  · have e : x0 ⁻¹ᵁ U = ⊤ := eq_top_iff.2 fun p _ => by
      rwa [Subsingleton.elim (α := PrimeSpectrum K) p default]
    rw [e]
    exact isAffineOpen_top _
  · have e : x0 ⁻¹ᵁ U = ⊥ := eq_bot_iff.2 fun p hp => by
      rw [Subsingleton.elim (α := PrimeSpectrum K) p default] at hp
      exact (h hp).elim
    rw [e]
    exact isAffineOpen_bot _

theorem IsChartPt.of_le {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {A' : Over (Sp (DualNumber K))}
    {Z : Scheme.{0}} {m : A.left ⟶ Z} {m' : A'.left ⟶ Z} {W₀ : Z.Opens} {d : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)}
    (hd : LogKS.IsField W₀ d) {Ω₀ Ω : Z.Opens} (h0 : Ω₀ ≤ Ω) (h1 : Ω ≤ W₀) {n : ℕ} {u : Fin n → (epsR K ⟶ A)}
    {θ : Matrix (Fin n) (Fin n) K} {Wo : A.left.Opens} {g : Γ(A.left, Wo)ˣ} {B : Type} [CommRing B]
    [Algebra (DualNumber K) B] {x : Sp B ⟶ A.left} {l : Sp B ⟶ A'.left} (hx : x ≫ A.hom = spMap (baseMap K B))
    (hxΩ : ⊤ ≤ x ⁻¹ᵁ (m ⁻¹ᵁ Ω₀)) (hut : ∀ a, IsTangent (u a)) (hl : IsChartPt A' m m' Ω₀ (d Ω₀) u θ Wo g x l) :
    IsChartPt A' m m' Ω (d Ω) u θ Wo g x l := by
  obtain ⟨h₁, h₂, h₃⟩ := hl
  refine ⟨h₁, GlobalTheory.FlagMod.le_preimage_mono h0 h₂, fun f => ?_⟩
  have hxm : ⊤ ≤ (x ≫ m) ⁻¹ᵁ Ω₀ := hxΩ
  have hw : ∀ a, ⊤ ≤ (transl (baseMap K B) x (u a) ≫ m) ⁻¹ᵁ Ω₀ := fun a =>
    le_preimage_of_red ((isTransl_transl _ x hx (u a)).red (hut a)) hxΩ
  rw [← valR_resG _ h0 h₂, h₃, chartVal, chartVal, hd.2.2 Ω Ω₀ h0 h1, valR_resG _ h0 hxm, valR_resG _ h0 hxm]
  simp only [valR_resG _ h0 (hw _)]

end GlobalTheory.CechKS
