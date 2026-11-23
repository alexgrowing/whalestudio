import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsChartPtChartPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineHomOfField
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

namespace GlobalTheory.CechKS.LinTan

open GlobalTheory.FlagMod

theorem spMap_comp_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm

theorem le_preimage_top {T Z : Scheme.{0}} (z : T ⟶ Z) : ⊤ ≤ z ⁻¹ᵁ ⊤ := le_rfl

theorem eq_of_ev {Y : Scheme.{0}} {S : Type} [CommRing S] {U : Y.Opens} (hU : IsAffineOpen U) {z z' : Sp S ⟶ Y}
    (h : ⊤ ≤ z ⁻¹ᵁ U) (h' : ⊤ ≤ z' ⁻¹ᵁ U) (e : ∀ f, ev z U h f = ev z' U h' f) : z = z' := by
  rw [← spMap_ev z hU h, ← spMap_ev z' hU h', RingHom.ext e]

theorem le_preimage_of_fst {Y : Scheme.{0}} {B : Type} [CommRing B] {n : ℕ} {x : Sp B ⟶ Y}
    {w : Sp (TrivSqZeroExt B (Fin n → B)) ⟶ Y}
    (hw : spMap (TrivSqZeroExt.fstHom B B (Fin n → B)).toRingHom ≫ w = x) {O : Y.Opens} (h : ⊤ ≤ x ⁻¹ᵁ O) :
    ⊤ ≤ w ⁻¹ᵁ O := by
  intro p _
  have hs : Function.Surjective (spMap (TrivSqZeroExt.fstHom B B (Fin n → B)).toRingHom) := by
    intro q
    refine ⟨spMap (algebraMap B (TrivSqZeroExt B (Fin n → B))) q, ?_⟩
    refine PrimeSpectrum.ext (Ideal.ext fun c ↦ ?_)
    change algebraMap B (TrivSqZeroExt B (Fin n → B)) c.fst ∈ q.asIdeal ↔ c ∈ q.asIdeal
    have hn : c - algebraMap B (TrivSqZeroExt B (Fin n → B)) c.fst ∈ q.asIdeal := by
      refine q.isPrime.mem_of_pow_mem 2 ?_
      have : (c - algebraMap B (TrivSqZeroExt B (Fin n → B)) c.fst) ^ 2 = 0 := by
        ext <;> simp [pow_two, TrivSqZeroExt.algebraMap_eq_inl]
      rw [this]; exact zero_mem _
    exact ⟨fun hc ↦ by simpa using add_mem hn hc, fun hc ↦ by simpa using sub_mem hc hn⟩
  obtain ⟨q, rfl⟩ := hs p
  have := h (Set.mem_univ q)
  rw [← hw] at this
  exact this

theorem exists_glue {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (e : A →+* B) (d : Fin n → (A →+* DualNumber B))
    (hd : ∀ a f, (d a f).fst = e f) : ∃ q : A →+* TrivSqZeroExt B (Fin n → B),
      ∀ f, (q f).fst = e f ∧ ∀ a, (q f).snd a = (d a f).snd := by
  refine ⟨{ toFun := fun f => TrivSqZeroExt.inl (e f) + TrivSqZeroExt.inr fun a => (d a f).snd,
            map_one' := ?_, map_mul' := fun f g => ?_,
            map_zero' := ?_, map_add' := fun f g => ?_ }, fun f => ⟨add_zero (e f), fun a => zero_add (d a f).snd⟩⟩
  · ext <;> simp
  · ext
    · simp
    · simp [hd, mul_comm]
  · ext <;> simp
  · ext <;> simp

theorem exists_linComb {K B : Type} [CommRing K] [CommRing B] {Y : Scheme.{0}} (p : Y ⟶ Sp K) (Y₀ : Y.affineOpens)
    (φ : K →+* B) (x : Sp B ⟶ Y) (hx : x ≫ p = spMap φ) (hxY : ⊤ ≤ x ⁻¹ᵁ Y₀.1) {n : ℕ}
    (w : Fin n → (Sp (DualNumber B) ⟶ Y)) (hwp : ∀ a, w a ≫ p = spMap ((algebraMap B (DualNumber B)).comp φ))
    (hwx : ∀ a, spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ w a = x) (c : Fin n → B) :
    ∃ S : Sp (DualNumber B) ⟶ Y, S ≫ p = spMap ((algebraMap B (DualNumber B)).comp φ) ∧
      spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ S = x ∧
      ∀ O : Y.Opens, ⊤ ≤ x ⁻¹ᵁ O → ∀ f : Γ(Y, O), (valR S O f).snd = ∑ a, c a * (valR (w a) O f).snd := by
  have hwY : ∀ a, ⊤ ≤ w a ⁻¹ᵁ Y₀.1 := fun a => le_preimage_of_red (hwx a) hxY
  obtain ⟨q, hq⟩ := exists_glue (ev x Y₀.1 hxY) (fun a => ev (w a) Y₀.1 (hwY a)) (fun a f => by
    have := ev_spMap (TrivSqZeroExt.fstHom B B B).toRingHom (w a) Y₀.1 (hwY a) (le_preimage_comp _ (hwY a))
    rw [ev_congr (hwx a) _ _ hxY] at this
    rw [this]; rfl)
  let T : Sp (TrivSqZeroExt B (Fin n → B)) ⟶ Y := spMap q ≫ tau Y₀.2
  have hT : ∀ {S : Type} [CommRing S] (σ : TrivSqZeroExt B (Fin n → B) →+* S) (z : Sp S ⟶ Y) (hz : ⊤ ≤ z ⁻¹ᵁ Y₀.1),
      (∀ f, σ (q f) = ev z Y₀.1 hz f) → spMap σ ≫ T = z := fun σ z hz e => by
    rw [← spMap_ev z Y₀.2 hz, ← RingHom.ext (f := σ.comp q) e, ← spMap_comp_spMap, Category.assoc]
    rfl
  let σ : ((Fin n → B) →ₗ[B] B) → (TrivSqZeroExt B (Fin n → B) →+* DualNumber B) := fun l =>
    (TrivSqZeroExt.map l).toRingHom
  have hσ1 : ∀ l r, (σ l r).fst = r.fst := fun l r => TrivSqZeroExt.fst_map l r
  have hσ2 : ∀ l r, (σ l r).snd = l r.snd := fun l r => TrivSqZeroExt.snd_map l r
  have hTx : spMap (TrivSqZeroExt.fstHom B B (Fin n → B)).toRingHom ≫ T = x := hT _ x hxY fun f => (hq f).1
  have hTw : ∀ a, spMap (σ (LinearMap.proj a)) ≫ T = w a := fun a => hT _ _ (hwY a) fun f => by
    ext
    · rw [hσ1, (hq f).1]
      have := ev_spMap (TrivSqZeroExt.fstHom B B B).toRingHom (w a) Y₀.1 (hwY a) (le_preimage_comp _ (hwY a))
      rw [ev_congr (hwx a) _ _ hxY] at this
      rw [this]; rfl
    · rw [hσ2]; exact (hq f).2 a
  let l : (Fin n → B) →ₗ[B] B := Fintype.linearCombination B c
  have hSx : spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ (spMap (σ l) ≫ T) = x := by
    rw [← Category.assoc, spMap_comp_spMap, ← hTx]
    congr 2
    exact RingHom.ext fun r => hσ1 l r
  have hS : ∀ O : Y.Opens, ⊤ ≤ x ⁻¹ᵁ O → ∀ f : Γ(Y, O),
      (valR (spMap (σ l) ≫ T) O f).snd = ∑ a, c a * (valR (w a) O f).snd := fun O hO f => by
    have hTO : ⊤ ≤ T ⁻¹ᵁ O := le_preimage_of_fst hTx hO
    have key : ∀ l', valR (spMap (σ l') ≫ T) O f = σ l' (ev T O hTO f) := fun l' => by
      rw [valR_eq_ev _ _ (le_preimage_comp _ hTO), ev_spMap _ _ _ hTO]; rfl
    rw [key, hσ2, Fintype.linearCombination_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← hTw a, key, hσ2, smul_eq_mul, mul_comm]; rfl
  refine ⟨spMap (σ l) ≫ T, ?_, hSx, hS⟩
  have hv : ∀ {S : Type} [CommRing S] (ψ : K →+* S) (f : Γ(Sp K, ⊤)),
      valR (spMap ψ) ⊤ f = ψ (ev (𝟙 (Sp K)) ⊤ (le_preimage_top _) f) := fun ψ f => by
    rw [← Category.comp_id (spMap ψ), valR_eq_ev _ _ (le_preimage_top _), ev_spMap _ _ _ (le_preimage_top _)]; rfl
  refine eq_of_ev (isAffineOpen_top (Sp K)) (le_preimage_top _) (le_preimage_top _) fun f => ?_
  rw [← valR_eq_ev, ← valR_eq_ev, hv]
  ext
  · have := ev_spMap (TrivSqZeroExt.fstHom B B B).toRingHom ((spMap (σ l) ≫ T) ≫ p) ⊤ (le_preimage_top _) (le_preimage_top _)
    rw [ev_congr (z' := spMap φ) (by rw [← Category.assoc, hSx, hx]) _ _ (le_preimage_top _)] at this
    have h2 := RingHom.congr_fun this f
    rw [← valR_eq_ev, hv] at h2
    rw [valR_eq_ev _ _ (le_preimage_top _)]
    exact h2.symm
  · rw [valR_comp_app, hS (p ⁻¹ᵁ ⊤) (le_preimage_top (x ≫ p))]
    simp only [← valR_comp_app, hwp, hv]
    simp [TrivSqZeroExt.algebraMap_eq_inl]

end GlobalTheory.CechKS.LinTan
