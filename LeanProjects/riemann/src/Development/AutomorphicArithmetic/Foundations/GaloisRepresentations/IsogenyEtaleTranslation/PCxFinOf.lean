import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.EtCancel
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PEigSame

set_option autoImplicit false

noncomputable section

open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo
open scoped Matrix TensorProduct Classical

namespace UpperTheory.Gal.FixZ.ComplexFinitenessOfFixed

variable {p : ℕ} [Fact p.Prime] {G : HTGroup p} {v : InfinitePlace G.F}

private abbrev SameB (v : InfinitePlace G.F) (B : GlobalTheory.LKCx.Form G) (Kf : Subgroup G.GAf) :
    GlobalTheory.LKCx.Dat G v B.β → GlobalTheory.LKCx.Dat G v B.β → Prop :=
  GlobalTheory.LKCx.Same G v B.β B.trivAf.choose B.trivAf.choose_spec.choose B.trivAf.choose_spec.choose_spec Kf
    (KHT p G.m G.n 1 G.Fw)

private def shf {β : G.Cˣ} (a : GlobalTheory.LKCx.Dat G v β) (k : G.GAf) : GlobalTheory.LKCx.Dat G v β := ((a.1.1 * k, a.1.2), a.2)

private theorem toV_mul' {β : G.Cˣ} (y y' : GlobalTheory.LKCx.grp G β) (z : Fin G.n → ℂ) :
    ((GlobalTheory.LKCx.toV G v β (y * y') : GL (Fin G.n) ℂ) : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z =
      (GlobalTheory.LKCx.toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ
        ((GlobalTheory.LKCx.toV G v β y' : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z) := by
  rw [map_mul, Units.val_mul, Matrix.mulVec_mulVec]

private theorem toV_inv' {β : G.Cˣ} (y : GlobalTheory.LKCx.grp G β) (z : Fin G.n → ℂ) :
    (GlobalTheory.LKCx.toV G v β y⁻¹ : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ
      ((GlobalTheory.LKCx.toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z) = z := by
  rw [← toV_mul', inv_mul_cancel, map_one, Units.val_one, Matrix.one_mulVec]

private theorem same_symm' {B : GlobalTheory.LKCx.Form G} {Kf : Subgroup G.GAf} {a b : GlobalTheory.LKCx.Dat G v B.β}
    (h : SameB v B Kf a b) : SameB v B Kf b a := by
  obtain ⟨y, k, c, hk1, hk2, hc, h1, h2⟩ := h
  refine ⟨y⁻¹, k⁻¹, c⁻¹, Kf.inv_mem hk1, (KHT p G.m G.n 1 G.Fw).inv_mem hk2, inv_ne_zero hc, ?_, ?_⟩
  · have e : ((B.toAf y⁻¹, GlobalTheory.LKCx.toP1 G B.β y⁻¹) : G.GAf × Gr G 1) = (B.toAf y, GlobalTheory.LKCx.toP1 G B.β y)⁻¹ := by
      simp [map_inv]
    have h1 : b.1 = (B.toAf y, GlobalTheory.LKCx.toP1 G B.β y) * a.1 * k := h1
    show a.1 = (B.toAf y⁻¹, GlobalTheory.LKCx.toP1 G B.β y⁻¹) * b.1 * k⁻¹
    rw [e, h1]
    show _ = (B.toAf y, GlobalTheory.LKCx.toP1 G B.β y)⁻¹ * ((B.toAf y, GlobalTheory.LKCx.toP1 G B.β y) * a.1 * k) * k⁻¹
    group
  · rw [h2, Matrix.mulVec_smul, toV_inv', smul_smul, inv_mul_cancel₀ hc, one_smul]

private theorem same_trans' {B : GlobalTheory.LKCx.Form G} {Kf : Subgroup G.GAf} {a b d : GlobalTheory.LKCx.Dat G v B.β}
    (h : SameB v B Kf a b) (h' : SameB v B Kf b d) : SameB v B Kf a d := by
  obtain ⟨y, k, c, hk1, hk2, hc, h1, h2⟩ := h
  obtain ⟨y', k', c', hk1', hk2', hc', h1', h2'⟩ := h'
  refine ⟨y' * y, k * k', c' * c, Kf.mul_mem hk1 hk1', (KHT p G.m G.n 1 G.Fw).mul_mem hk2 hk2',
    mul_ne_zero hc' hc, ?_, ?_⟩
  · have e : ((B.toAf (y' * y), GlobalTheory.LKCx.toP1 G B.β (y' * y)) : G.GAf × Gr G 1) =
        (B.toAf y', GlobalTheory.LKCx.toP1 G B.β y') * (B.toAf y, GlobalTheory.LKCx.toP1 G B.β y) := by
      simp [map_mul]
    show d.1 = (B.toAf (y' * y), GlobalTheory.LKCx.toP1 G B.β (y' * y)) * a.1 * (k * k')
    have h1a : b.1 = (B.toAf y, GlobalTheory.LKCx.toP1 G B.β y) * a.1 * k := h1
    have h1b : d.1 = (B.toAf y', GlobalTheory.LKCx.toP1 G B.β y') * b.1 * k' := h1'
    rw [h1b, h1a, e]
    simp only [_root_.mul_assoc]
  · rw [h2', h2, Matrix.mulVec_smul, smul_smul, toV_mul']

private theorem same_of_eq {B : GlobalTheory.LKCx.Form G} {Kf : Subgroup G.GAf} {a b : GlobalTheory.LKCx.Dat G v B.β}
    (h : Quot.mk (SameB v B Kf) a = Quot.mk (SameB v B Kf) b) : SameB v B Kf a b :=
  (Equivalence.eqvGen_iff ⟨GlobalTheory.LKCx.same_refl G v B.β _ _ _ _ _, same_symm', same_trans'⟩).1 (Quot.eqvGen_exact h)

private theorem step1 {B : GlobalTheory.LKCx.Form G} {K K' : Subgroup G.GAf} (hle : K' ≤ K) {a a' : GlobalTheory.LKCx.Dat G v B.β}
    {k k' : G.GAf} (hk : k ∈ K) (hk' : k' ∈ K) (hs : SameB v B K' (shf a k) (shf a' k')) : SameB v B K a a' := by
  obtain ⟨y, κ, c, h1, h2, hc, e, e2⟩ := hs
  have e1 : a'.1.1 * k' = B.toAf y * (a.1.1 * k) * κ.1 := congrArg Prod.fst e
  have e3 : a'.1.2 = GlobalTheory.LKCx.toP1 G B.β y * a.1.2 * κ.2 := congrArg Prod.snd e
  refine ⟨y, (k * κ.1 * k'⁻¹, κ.2), c, K.mul_mem (K.mul_mem hk (hle h1)) (K.inv_mem hk'), h2, hc, ?_, e2⟩
  refine Prod.ext ?_ e3
  show a'.1.1 = B.toAf y * a.1.1 * (k * κ.1 * k'⁻¹)
  calc a'.1.1 = (a'.1.1 * k') * k'⁻¹ := by group
    _ = _ := by rw [e1]; group

private theorem step2 {B : GlobalTheory.LKCx.Form G} {K K' : Subgroup G.GAf} (hle : K' ≤ K)
    (hK : ∀ (a : GlobalTheory.LKCx.Dat G v B.β) y, W2.Sees B (K : Set G.GAf) a y → y = 1) {a : GlobalTheory.LKCx.Dat G v B.β}
    {k k' : G.GAf} (hk : k ∈ K) (hk' : k' ∈ K) (hs : SameB v B K' (shf a k) (shf a k')) :
    ∃ κ ∈ K', k' = k * κ := by
  obtain ⟨y, κ, c, h1, h2, hc, e, e2⟩ := hs
  have e1 : a.1.1 * k' = B.toAf y * (a.1.1 * k) * κ.1 := congrArg Prod.fst e
  have e3 : a.1.2 = GlobalTheory.LKCx.toP1 G B.β y * a.1.2 * κ.2 := congrArg Prod.snd e
  have e4 : a.2.1 = c • ((GlobalTheory.LKCx.toV G v B.β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ a.2.1) := e2
  have hy : y = 1 := by
    refine hK a y ⟨⟨c⁻¹, ?_⟩, ?_, ?_⟩
    · calc (GlobalTheory.LKCx.toV G v B.β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ a.2.1
          = c⁻¹ • (c • ((GlobalTheory.LKCx.toV G v B.β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ a.2.1)) := by
            rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
        _ = c⁻¹ • a.2.1 := by rw [← e4]
    · have e5 : B.toAf y * a.1.1 = a.1.1 * k' * κ.1⁻¹ * k⁻¹ := by rw [e1]; group
      have e6 : a.1.1⁻¹ * B.toAf y * a.1.1 = k' * κ.1⁻¹ * k⁻¹ := by
        rw [_root_.mul_assoc, e5]; group
      show a.1.1⁻¹ * B.toAf y * a.1.1 ∈ K
      rw [e6]
      exact K.mul_mem (K.mul_mem hk' (K.inv_mem (hle h1))) (K.inv_mem hk)
    · have e5 : GlobalTheory.LKCx.toP1 G B.β y * a.1.2 = a.1.2 * κ.2⁻¹ := by
        conv_rhs => rw [e3]
        group
      have e6 : a.1.2⁻¹ * GlobalTheory.LKCx.toP1 G B.β y * a.1.2 = κ.2⁻¹ := by
        rw [_root_.mul_assoc, e5]; group
      rw [e6]
      exact (KHT p G.m G.n 1 G.Fw).inv_mem h2
  subst hy
  rw [map_one, _root_.one_mul, _root_.mul_assoc] at e1
  exact ⟨κ.1, h1, mul_left_cancel e1⟩

private theorem step3 {B : GlobalTheory.LKCx.Form G} {K K' : Subgroup G.GAf} {h : G.GAf} (hle : K' ≤ K)
    (hconj : ∀ u ∈ K', h * u * h⁻¹ ∈ K)
    (hK : ∀ (a : GlobalTheory.LKCx.Dat G v B.β) y, W2.Sees B (K : Set G.GAf) a y → y = 1) {a : GlobalTheory.LKCx.Dat G v B.β}
    {k κ : G.GAf} (hk : k ∈ K) (hκ : κ ∈ K') {y y' : GlobalTheory.LKCx.grp G B.β}
    (hs : W2.Sees B {g | h * g ∈ K} (shf a k) y) (hs' : W2.Sees B {g | h * g ∈ K} (shf a (k * κ)) y') : y = y' := by
  obtain ⟨⟨e, he⟩, h1, h2⟩ := hs
  obtain ⟨⟨e', he'⟩, h1', h2'⟩ := hs'
  have he0 : (GlobalTheory.LKCx.toV G v B.β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ a.2.1 = e • a.2.1 := he
  have he1 : (GlobalTheory.LKCx.toV G v B.β y' : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ a.2.1 = e' • a.2.1 := he'
  have g1 : h * ((a.1.1 * k)⁻¹ * B.toAf y * (a.1.1 * k)) ∈ K := h1
  have g2 : h * ((a.1.1 * (k * κ))⁻¹ * B.toAf y' * (a.1.1 * (k * κ))) ∈ K := h1'
  have g3 : a.1.2⁻¹ * GlobalTheory.LKCx.toP1 G B.β y * a.1.2 ∈ KHT p G.m G.n 1 G.Fw := h2
  have g4 : a.1.2⁻¹ * GlobalTheory.LKCx.toP1 G B.β y' * a.1.2 ∈ KHT p G.m G.n 1 G.Fw := h2'
  have g5 : h * ((a.1.1 * k)⁻¹ * B.toAf y' * (a.1.1 * k)) ∈ K := by
    have := K.mul_mem (K.mul_mem (hconj κ hκ) g2) (K.inv_mem (hle hκ))
    convert this using 1
    group
  have hz : a.2.1 ≠ 0 := by
    intro h0
    have := a.2.2
    rw [h0] at this
    simp at this
  have hinv : e • ((GlobalTheory.LKCx.toV G v B.β y⁻¹ : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ a.2.1) = a.2.1 := by
    rw [← Matrix.mulVec_smul, ← he0, toV_inv']
  have he2 : e ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hinv
    exact hz hinv.symm
  have hinv' : (GlobalTheory.LKCx.toV G v B.β y⁻¹ : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ a.2.1 = e⁻¹ • a.2.1 := by
    conv_rhs => rw [← hinv]
    rw [smul_smul, inv_mul_cancel₀ he2, one_smul]
  have hone := hK a (y⁻¹ * y') ⟨⟨e' * e⁻¹, ?_⟩, ?_, ?_⟩
  · exact inv_mul_eq_one.1 hone
  · rw [toV_mul', he1, Matrix.mulVec_smul, hinv', smul_smul]
  · show a.1.1⁻¹ * B.toAf (y⁻¹ * y') * a.1.1 ∈ K
    have := K.mul_mem (K.mul_mem hk (K.mul_mem (K.inv_mem g1) g5)) (K.inv_mem hk)
    rw [map_mul, map_inv]
    convert this using 1
    group
  · have := (KHT p G.m G.n 1 G.Fw).mul_mem ((KHT p G.m G.n 1 G.Fw).inv_mem g3) g4
    rw [map_mul, map_inv]
    convert this using 1
    group

end UpperTheory.Gal.FixZ.ComplexFinitenessOfFixed

open UpperTheory.Gal.FixZ.ComplexFinitenessOfFixed in
theorem UpperTheory.Gal.FixZ.cxFinOf_of : UpperTheory.Gal.FixZ.CxFinOf := by
  intro p _ G v K K' h hle hconj hfin hK
  have hS : ∀ u ∈ K', ∀ g, u⁻¹ * g * u ∈ ({g | h * g ∈ K} : Set G.GAf) ↔ g ∈ ({g | h * g ∈ K} : Set G.GAf) := by
    intro u hu g
    constructor
    · intro hg
      have hg' : h * (u⁻¹ * g * u) ∈ K := hg
      have := K.mul_mem (K.mul_mem (hconj u hu) hg') (K.inv_mem (hle hu))
      show h * g ∈ K
      convert this using 1
      group
    · intro hg
      have hg' : h * g ∈ K := hg
      have := K.mul_mem (K.mul_mem (K.inv_mem (hconj u hu)) hg') (hle hu)
      show h * (u⁻¹ * g * u) ∈ K
      convert this using 1
      group
  have hch : ∀ z : (Σ q : GlobalTheory.LKCx.FCls G, UpperTheory.Gal.LocalSmoothExtension.PtsOf G v K q × GlobalTheory.LKCx.grp G (Quot.out q).β),
      UpperTheory.Gal.LocalSmoothExtension.Seen G v K (UpperTheory.Gal.G3.ind ℂ K h⁻¹) z.1 z.2.1 z.2.2 →
      ∃ k, k ∈ K ∧ UpperTheory.Gal.W2.Sees (Quot.out z.1) {g | h * g ∈ K} (shf (Quot.out z.2.1) k) z.2.2 := by
    rintro ⟨q, a, y⟩ ⟨hf, hi, ho⟩
    have hm := Set.mem_of_indicator_ne_zero hi
    obtain ⟨k₁, hk₁, k₂, hk₂, e⟩ := DoubleCoset.mem_doubleCoset.1 hm
    refine ⟨k₁, hk₁, hf, ?_, Set.mem_of_indicator_ne_zero ho⟩
    have e' : (Quot.out a).1.1⁻¹ * (Quot.out q).toAf y * (Quot.out a).1.1 = k₁ * h⁻¹ * k₂ := e
    show h * (((Quot.out a).1.1 * k₁)⁻¹ * (Quot.out q).toAf y * ((Quot.out a).1.1 * k₁)) ∈ K
    have e2 : h * (((Quot.out a).1.1 * k₁)⁻¹ * (Quot.out q).toAf y * ((Quot.out a).1.1 * k₁)) =
        h * (k₁⁻¹ * ((Quot.out a).1.1⁻¹ * (Quot.out q).toAf y * (Quot.out a).1.1) * k₁) := by group
    rw [e2, e']
    have e3 : h * (k₁⁻¹ * (k₁ * h⁻¹ * k₂) * k₁) = k₂ * k₁ := by group
    rw [e3]
    exact K.mul_mem hk₂ hk₁
  choose! κ hκK hκS using hch
  refine Set.Finite.of_injOn
    (f := fun z => (⟨z.1, Quot.mk _ (shf (Quot.out z.2.1) (κ z))⟩ : GlobalTheory.LKCx.AllPts G v K' (UpperTheory.Gal.LocalSmoothExtension.Kp G)))
    ?_ ?_ hfin
  · intro z hz
    obtain ⟨E, -, hE⟩ := UpperTheory.Gal.W2.eigSame_of p G v (fun _ _ => 0) (Quot.out z.1) K' {g | h * g ∈ K} hS
      (shf (Quot.out z.2.1) (κ z)) _ (Quot.out_eq _).symm
    exact ⟨E z.2.2, ((hE z.2.2).1).1 (hκS z hz)⟩
  · rintro ⟨q, a, y⟩ hz ⟨q', a', y'⟩ hz' heq
    obtain ⟨rfl, hh⟩ := Sigma.mk.inj_iff.1 heq
    have hh' := eq_of_heq hh
    have hsame := same_of_eq (v := v) (B := Quot.out q) (Kf := K') hh'
    have hk := hκK _ hz
    have hk' := hκK _ hz'
    have hsame0 := step1 hle hk hk' hsame
    have haa : a = a' := (Quot.out_eq (r := SameB v (Quot.out q) K) a).symm.trans
      ((Quot.sound hsame0).trans (Quot.out_eq (r := SameB v (Quot.out q) K) a'))
    subst haa
    obtain ⟨u, hu, e⟩ := step2 hle (hK _) hk hk' hsame
    have hs := hκS _ hz
    have hs' := hκS _ hz'
    simp only [e] at hs'
    have : y = y' := step3 hle hconj (hK _) hk hu hs hs'
    subst this
    rfl

end
