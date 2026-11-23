import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DcOpCommOfCommute
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVectorStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HkDict

theorem lift_cosets {H G : Type} [Group H] [Group G] (φ : H →* G) (N J₀ L₀ L₁ : Subgroup H) (J : Subgroup G) (K : Set H)
    (hs : ∀ x, ∃ g ∈ N, φ g = x) (hi : ∀ g g', g ∈ N → g' ∈ N → φ g = φ g' → g = g')
    (hJ : ∀ g, g ∈ N → (φ g ∈ J ↔ g ∈ J₀)) (hLN : ∀ g ∈ L₀, g ∈ N)
    (hc : ∀ g g', g ∈ L₀ → g' ∈ L₁ → Commute g g') (hd : ∀ g, g ∈ L₀ → g ∈ L₁ → g = 1)
    (hK : ∀ g, g ∈ L₀ → (g ∈ J₀ ↔ g ∈ K))
    (hsp : ∀ k ∈ J₀, ∃ k₁ ∈ J₀, ∃ k₂ ∈ J₀, k₁ ∈ L₀ ∧ k₂ ∈ L₁ ∧ k = k₁ * k₂)
    (α : H) (hα : α ∈ L₀) (B : Finset G) (hB : ∀ a ∈ B, ∃ g ∈ L₀, φ g = a) (hDC : Bridge.IsDC J (φ α) B) :
    ∃ R : Finset H, (∀ γ ∈ R, γ ∈ L₀) ∧
      (∀ γ ∈ R, ∃ k₁, (k₁ ∈ K ∧ k₁ ∈ L₀) ∧ ∃ k₂, (k₂ ∈ K ∧ k₂ ∈ L₀) ∧ γ = k₁ * α * k₂) ∧
      (∀ x : H, (∃ k₁, (k₁ ∈ K ∧ k₁ ∈ L₀) ∧ ∃ k₂, (k₂ ∈ K ∧ k₂ ∈ L₀) ∧ x = k₁ * α * k₂) →
        ∃! γ, γ ∈ R ∧ (γ⁻¹ * x ∈ K ∧ γ⁻¹ * x ∈ L₀)) ∧
      ∀ (W : Type) [AddCommMonoid W] (F : G → W), ∑ a ∈ B, F a = ∑ γ ∈ R, F (φ γ) := by
  classical
  choose s hs1 hs2 using hs
  have hsL : ∀ a ∈ B, s a ∈ L₀ := fun a ha => by
    obtain ⟨g, hg, rfl⟩ := hB a ha
    rw [hi _ _ (hs1 _) (hLN g hg) (hs2 _)]
    exact hg
  have hsinj : Function.Injective s := fun a b h => by rw [← hs2 a, ← hs2 b, h]
  have hKJ : ∀ k, k ∈ K ∧ k ∈ L₀ → φ k ∈ J := fun k hk => (hJ k (hLN k hk.2)).2 ((hK k hk.2).2 hk.1)
  refine ⟨B.image s, ?_, ?_, ?_, ?_⟩
  · intro γ hγ
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hγ
    exact hsL a ha
  · intro γ hγ
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hγ
    obtain ⟨⟨k₁, h₁⟩, ⟨k₂, h₂⟩, hk⟩ := hDC.1 a ha
    have j₁ : s k₁ ∈ J₀ := (hJ _ (hs1 _)).1 (by rwa [hs2])
    have j₂ : s k₂ ∈ J₀ := (hJ _ (hs1 _)).1 (by rwa [hs2])
    obtain ⟨a₁, ha₁, b₁, hb₁, la₁, lb₁, e₁⟩ := hsp _ j₁
    obtain ⟨a₂, ha₂, b₂, hb₂, la₂, lb₂, e₂⟩ := hsp _ j₂
    have e : s a = s k₁ * α * s k₂ := by
      refine hi _ _ (hs1 _) (N.mul_mem (N.mul_mem (hs1 _) (hLN _ hα)) (hs1 _)) ?_
      rw [map_mul, map_mul, hs2, hs2, hs2]
      exact hk
    have e' : s a = (a₁ * α * a₂) * (b₁ * b₂) := by
      rw [e, e₁, e₂]
      have c := (hc _ _ (L₀.mul_mem hα la₂) lb₁).eq
      calc a₁ * b₁ * α * (a₂ * b₂) = a₁ * (b₁ * (α * a₂)) * b₂ := by simp only [mul_assoc]
        _ = _ := by rw [← c]; simp only [mul_assoc]
    have hb : b₁ * b₂ = 1 := by
      refine hd _ ?_ (L₁.mul_mem lb₁ lb₂)
      have : b₁ * b₂ = (a₁ * α * a₂)⁻¹ * s a := by rw [e', inv_mul_cancel_left]
      rw [this]
      exact L₀.mul_mem (L₀.inv_mem (L₀.mul_mem (L₀.mul_mem la₁ hα) la₂)) (hsL a ha)
    exact ⟨a₁, ⟨(hK _ la₁).1 ha₁, la₁⟩, a₂, ⟨(hK _ la₂).1 ha₂, la₂⟩, by rw [e', hb, mul_one]⟩
  · rintro x ⟨k₁, h₁, k₂, h₂, hx⟩
    have hxL : x ∈ L₀ := hx ▸ L₀.mul_mem (L₀.mul_mem h₁.2 hα) h₂.2
    obtain ⟨a, ⟨ha, haJ⟩, hu⟩ := hDC.2 (φ x) ⟨⟨φ k₁, hKJ _ h₁⟩, ⟨φ k₂, hKJ _ h₂⟩, by rw [hx, map_mul, map_mul]⟩
    have hL : (s a)⁻¹ * x ∈ L₀ := L₀.mul_mem (L₀.inv_mem (hsL a ha)) hxL
    refine ⟨s a, ⟨Finset.mem_image_of_mem s ha, (hK _ hL).1 ((hJ _ (hLN _ hL)).1 ?_), hL⟩, ?_⟩
    · rwa [map_mul, map_inv, hs2]
    · rintro γ ⟨hγ, hγK⟩
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hγ
      have := hKJ _ hγK
      rw [map_mul, map_inv, hs2] at this
      rw [hu b ⟨hb, this⟩]
  · intro W _ F
    rw [Finset.sum_image fun a _ b _ h => hsinj h]
    simp only [hs2]

def rightTr {H G : Type} [Group H] [Group G] (φ : H →* G) (W : Type) [AddCommGroup W] [Module ℂ W] :
    H →* Module.End ℂ (G → W) where
  toFun g := { toFun := fun F h => F (h * φ g), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  map_one' := by ext F h; simp
  map_mul' g g' := by ext F h; simp [mul_assoc]

theorem supp_both {D : D7} (V : HSp D) (f : Formalism.L2.Theta.AE D) (g : GA D V) (h : SuppF V f g) (h' : SuppF V (1 - f) g) :
    g = 1 := by
  apply Subtype.ext
  apply Units.ext
  have : Formalism.L2.Theta.mt V g - 1 = 0 := by
    ext i j
    have a := h i j
    have b := h' i j
    rw [sub_mul, one_mul, a, sub_self] at b
    exact b.symm
  exact sub_eq_zero.1 this

set_option maxHeartbeats 1000000 in
open GlobalTheory.SplitHeckeAdj in

theorem dcOp_eq_label : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ) (L : LevDat D.host.E ℂ V.rank), IsBaseFrame V β Λ N → ∀ P : Pl D.host.E, ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → (∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P) → ∀ (d : List ℤ) (x : Bridge.Gf V) (B : Finset (Bridge.Gf V)), d.Pairwise (fun a b => b ≤ a) → IsLabElt V P d x → (∀ a ∈ B, IsLocElt V P a) → Bridge.IsDC (levEnv V β L).J x B → IsLab V P d ∧ ∀ (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (Φ : Bridge.Gf V → W), (∀ h (k : (levEnv V β L).J), IsLocElt V P k → Φ (h * k) = Φ h) → Bridge.dcOp B Φ = hkF V P (Finsupp.single d 1) Φ := by
  intro D V β Λ N L hβ P hN hoff d x B hd hx hB hDC
  obtain ⟨e, f, ϖ, α, hP, hϖ, hϖ', -, hxα, hα, hdiv⟩ := hx
  have hG := GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V
  have h01 := hG.2.2.1 P e f hP
  have hff := h01.1
  have hcf := h01.2.1
  have hff' : (1 - f) * (1 - f) = 1 - f := by
    rw [mul_sub, mul_one, sub_mul, one_mul, hff, sub_self, sub_zero]
  have hcf' : cA D (1 - f) = 1 - f := by rw [map_sub, map_one, hcf]
  obtain ⟨L₀, hL₀⟩ := (hG.1 f hff hcf).1
  obtain ⟨L₁, hL₁⟩ := (hG.1 _ hff' hcf').1
  have h03 := (GlobalTheory.LevSplit.lev_split V β Λ N (flag1L L) hβ).2 P e f hP hN hoff
  have hK := h03.1
  have hsp := h03.2.2
  have hx' : x = fin V α := Subtype.ext hxα
  subst hx'
  have hB' : ∀ a ∈ B, ∃ g ∈ L₀, fin V g = a := fun a ha => by
    obtain ⟨e', f', g, hP', -, h1, h2⟩ := hB a ha
    have h3 : f' = f := (h01.2.2.2.1 e' f' hP').2
    rw [h3] at h2
    exact ⟨g, (hL₀ g).2 h2, Subtype.ext h1.symm⟩
  have main := lift_cosets (fin V) (GfC V) (levG V β (flag1L L)) L₀ L₁ (levEnv V β L).J (KsphC V ∅)
    (fin_lift V) (fun g g' => fin_inj V) (fun g => mem_J V β L)
    (fun g hg => h01.2.2.1 g ((hL₀ g).1 hg))
    (fun g g' h h' => commute_compl V _ hff hcf ((hL₀ g).1 h) ((hL₁ g').1 h'))
    (fun g h h' => supp_both V f g ((hL₀ g).1 h) ((hL₁ g).1 h'))
    (fun g h => hK g ((hL₀ g).1 h))
    (fun k hk => by
      obtain ⟨k₁, h₁, k₂, h₂, s₁, s₂, h⟩ := hsp k hk
      exact ⟨k₁, h₁, k₂, h₂, (hL₀ _).2 s₁, (hL₁ _).2 s₂, h⟩)
    α ((hL₀ α).2 hα) B hB' hDC
  obtain ⟨R, r1, r2, r3, r4⟩ := main
  simp only [hL₀] at r1 r2 r3
  have hR : SphOp V P d R :=
    ⟨e, f, ϖ, α, fun v hv => absurd hv (Finset.notMem_empty v), hP, hϖ, hϖ', hd, fun _ _ => Iff.rfl, fun _ _ _ => rfl,
      hα, hdiv, r1, fun γ hγ => ⟨h01.2.2.1 γ (r1 γ hγ), r2 γ hγ⟩, r3⟩
  refine ⟨⟨R, hR⟩, fun W _ _ Φ hΦ => ?_⟩
  have hfix : ∀ k ∈ hyp V P, rightTr (fin V) W k Φ = Φ := by
    rintro k ⟨hk, e', f', hP', hs⟩
    have h3 : f' = f := (h01.2.2.2.1 e' f' hP').2
    rw [h3] at hs
    have hkf := h01.2.2.1 k hs
    funext h
    exact hΦ h ⟨fin V k, (mem_J V β L hkf).2 ((hK k hs).2 hk)⟩ ⟨e, f, k, hP, hkf, rfl, hs⟩
  have h := ((GlobalTheory.T.spherical_label_operators_on_hyperspecial_fixed_vectors V P).1 d R hR).2 _ (rightTr (fin V) W) Φ hfix
  funext g
  have h1 := congrFun h g
  have h2 : Bridge.dcOp B Φ g = ∑ γ ∈ R, Φ (g * fin V γ) := r4 W fun a => Φ (g * a)
  rw [h2]
  simp only [opOf, hkF, zero_smul, Finsupp.sum_single_index, one_smul, Finset.sum_apply, LinearMap.sum_apply] at h1 ⊢
  exact h1

end GlobalTheory.HkDict
