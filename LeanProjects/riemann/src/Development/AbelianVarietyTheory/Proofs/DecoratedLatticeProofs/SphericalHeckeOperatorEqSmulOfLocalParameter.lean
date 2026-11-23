import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BcParamEqOfSatUEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SatakeDeterminesSphericalHeckeCharacterGLStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitarySatakeTransformEqOfBaseChangeSatakeParameStatement

noncomputable section

namespace GlobalTheory.LFun.EigLoc

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun
open Formalism.MainNotions.SchurIrreducible (IsSplit)

section General

variable {G H : Type} [Group G] [Group H]

theorem comp_symm_mem_hecke (e : G ≃* H) {K : Subgroup G} {K' : Subgroup H} (hK : ∀ g, g ∈ K ↔ e g ∈ K')
    {φ : G → ℂ} (hφ : φ ∈ Hecke ℂ K) : φ ∘ e.symm ∈ Hecke ℂ K' := by
  classical
  have hφ' : IsBiInv K φ ∧ FinDosetSupp K φ := hφ
  obtain ⟨hb, S, hS⟩ := hφ'
  have hsymm : ∀ y : H, y ∈ K' → e.symm y ∈ K := fun y hy => by
    rw [hK, MulEquiv.apply_symm_apply]; exact hy
  show IsBiInv K' (φ ∘ e.symm) ∧ FinDosetSupp K' (φ ∘ e.symm)
  refine ⟨fun a b g => ?_, ⟨S.image e, fun g hg => ?_⟩⟩
  · have := hb ⟨_, hsymm a a.2⟩ ⟨_, hsymm b b.2⟩ (e.symm g)
    simpa only [Function.comp_apply, map_mul] using this
  · obtain ⟨s, hs, a, b, hab⟩ := hS (e.symm g) hg
    refine ⟨e s, ?_, ⟨e a, (hK _).1 a.2⟩, ⟨e b, (hK _).1 b.2⟩, ?_⟩
    · first
        | exact Finset.mem_image_of_mem _ hs
        | exact Set.mem_image_of_mem _ hs
    · have := congrArg e hab
      simpa only [MulEquiv.apply_symm_apply, map_mul] using this

theorem heckeVec_eq_comp_symm {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    (e : G ≃* H) {K : Subgroup G} {K' : Subgroup H} (hK : ∀ g, g ∈ K ↔ e g ∈ K')
    {φ : G → ℂ} (hφ : φ ∈ Hecke ℂ K) {x : V} (hx : x ∈ fixed ρ K) :
    heckeVec ρ K φ x = heckeVec (ρ.comp e.symm.toMonoidHom) K' (φ ∘ e.symm) x := by
  classical
  have hfix : ∀ k, k ∈ K → ρ k x = x := fun k hk => by
    have hx' : ∀ h : K, ρ h x = ((1 : K →* ℂˣ) h : ℂ) • x := hx
    simpa using hx' ⟨k, hk⟩
  have hT : ∀ g k, k ∈ K → φ (g * k) • ρ (g * k) x = φ g • ρ g x := by
    intro g k hk
    have hb : IsBiInv K φ := hφ.1
    have h1 : φ (g * k) = φ g := by simpa using hb 1 ⟨k, hk⟩ g
    rw [h1, map_mul, Module.End.mul_apply, hfix k hk]
  let Q : G ⧸ K ≃ H ⧸ K' := Quotient.congr e.toEquiv (fun a b => by
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply, hK]
    simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, map_mul, map_inv])
  have hQ : ∀ g : G, Q (g : G ⧸ K) = ((e g : H) : H ⧸ K') := fun g => rfl
  unfold heckeVec
  rw [← finsum_comp_equiv Q]
  refine finsum_congr fun c => ?_
  have h1 : (((Q c).out : H) : H ⧸ K') = ((e c.out : H) : H ⧸ K') := by
    rw [QuotientGroup.out_eq', ← hQ, QuotientGroup.out_eq']
  have h2 : (e c.out)⁻¹ * (Q c).out ∈ K' := QuotientGroup.eq.1 h1.symm
  have h3 : c.out⁻¹ * e.symm (Q c).out ∈ K := by
    rw [hK]
    simpa only [map_mul, map_inv, MulEquiv.apply_symm_apply] using h2
  have h4 := hT c.out _ h3
  rw [mul_inv_cancel_left] at h4
  exact h4.symm

private theorem cell_unif_lemma {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {c : L →+* L}
    {n q m : ℕ} {ϖ ϖ' : L} (hU : IsUnramInv ϖ c q) (hU' : IsUnramInv ϖ' c q) (hm : 2 * m ≤ n)
    (a : Fin m → ℤ) (y : GU c n)
    (H : ∃ u : GU c n, IsUnipU u ∧ ∃ k ∈ KU c n,
      (((y : GU c n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
        tMat ϖ n m a * (((u : GU c n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
          (((k : GU c n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) :
    ∃ u : GU c n, IsUnipU u ∧ ∃ k ∈ KU c n,
      (((y : GU c n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
        tMat ϖ' n m a * (((u : GU c n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
          (((k : GU c n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
  obtain ⟨u, hu, k, hk, hy⟩ := H
  have hne : ∀ t : L, IsUnramInv t c q → t ≠ 0 := fun t ht h0 => by
    have h := ht.2.2.2.1
    simp [h0] at h
  have hg0 : ∀ t : L, t ≠ 0 → ∀ i, tMat t n m a i i ≠ 0 := by
    intro t ht i
    simp only [tMat, Matrix.diagonal_apply_eq]
    split_ifs <;> first | exact zpow_ne_zero _ ht | exact one_ne_zero
  have hvv : Valued.v ϖ = Valued.v ϖ' := hU.2.2.2.1.trans hU'.2.2.2.1.symm
  have hgv : ∀ i, Valued.v (tMat ϖ n m a i i) = Valued.v (tMat ϖ' n m a i i) := by
    intro i
    simp only [tMat, Matrix.diagonal_apply_eq]
    split_ifs <;> simp only [map_zpow₀, hvv]
  have htm : ∀ t : L, tMat t n m a = Matrix.diagonal (fun i => tMat t n m a i i) := by
    intro t
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · rw [Matrix.diagonal_apply_ne _ hij]
      simp only [tMat, Matrix.diagonal_apply_ne _ hij]
  set e : Fin n → L := fun i => tMat ϖ n m a i i / tMat ϖ' n m a i i with he_def
  have he0 : ∀ i, e i ≠ 0 := fun i => div_ne_zero (hg0 ϖ (hne ϖ hU) i) (hg0 ϖ' (hne ϖ' hU') i)
  obtain ⟨t, ht⟩ := Formalism.UG.P.fSatake_tMat_exists hU hm a
  obtain ⟨t', ht'⟩ := Formalism.UG.P.fSatake_tMat_exists hU' hm a
  have hb : ∀ i, c (tMat ϖ n m a i i) * tMat ϖ n m a i.rev i.rev = 1 := fun i => by
    have := Formalism.UG.P.fSatake_unit_diag (Formalism.UG.P.fSatake_borel_tMat ht) i
    rwa [ht] at this
  have hb' : ∀ i, c (tMat ϖ' n m a i i) * tMat ϖ' n m a i.rev i.rev = 1 := fun i => by
    have := Formalism.UG.P.fSatake_unit_diag (Formalism.UG.P.fSatake_borel_tMat ht') i
    rwa [ht'] at this
  have hce : ∀ i, c (e i) * e i.rev = 1 := fun i => by
    simp only [he_def, map_div₀]
    rw [div_mul_div_comm, hb i, hb' i, div_one]
  obtain ⟨D, hD, hD'⟩ := Formalism.UG.P.fSatake_diag_exists e hce
  have hev : ∀ i, Valued.v (e i) = 1 := fun i => by
    simp only [he_def]
    rw [map_div₀, hgv i, div_self]
    exact (Valuation.ne_zero_iff _).2 (hg0 ϖ' (hne ϖ' hU') i)
  have hDK : D ∈ KU c n := Formalism.UG.P.fSatake_diag_mem_K hD hD' hev
  have hDD : (((D⁻¹ : GU c n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
      (((D : GU c n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]
    rfl
  have hsplit : tMat ϖ n m a = tMat ϖ' n m a * (((D : GU c n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
    rw [hD, htm ϖ, htm ϖ', Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    simp only [he_def]
    rw [mul_div_cancel₀ _ (hg0 ϖ' (hne ϖ' hU') i)]
  obtain ⟨hub, hud⟩ := hu
  refine ⟨D * u * D⁻¹, ?_, D * k, Subgroup.mul_mem _ hDK hk, ?_⟩
  · have hmat : ∀ i j, (((D * u * D⁻¹ : GU c n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j =
        e i * (((u : GU c n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j * (e j)⁻¹ := by
      intro i j
      simp only [Subgroup.coe_mul, Units.val_mul, hD, hD', Matrix.mul_diagonal, Matrix.diagonal_mul]
    unfold IsUnipU IsBorelU
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · rw [hmat, hub i j hij, mul_zero, zero_mul]
    · rw [hmat, hud i, mul_one, mul_inv_cancel₀ (he0 i)]
  · rw [hy, hsplit]
    simp only [Subgroup.coe_mul, Units.val_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (((D⁻¹ : GU c n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L), hDD, Matrix.one_mul]

private theorem satU_eq_of_isUnramInv {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {c : L →+* L}
    {n q m : ℕ} {ϖ ϖ' : L} (hU : IsUnramInv ϖ c q) (hU' : IsUnramInv ϖ' c q) (hm : 2 * m ≤ n)
    (f : GU c n → ℂ) (α : Fin m → ℂ) : SatU ϖ q f α = SatU ϖ' q f α := by
  unfold SatU
  refine finsum_congr fun a => ?_
  congr 1
  refine finsum_congr fun x => ?_
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (cell_unif_lemma hU hU' hm a _ h1) h2
  · exact absurd (cell_unif_lemma hU' hU hm a _ h2) h1
  · rfl

end General

theorem heckeVec_eq_smul_of_isParamVec : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (h : w.under (𝓞 F) = v) (B : Multiset ℂˣ), ∀ φ ∈ Hecke ℂ (stabLoc σ J L v), ∃ z : ℂ, ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GLoc σ J v) V) (x : V), IsParamVec σ J L h ρ x B → heckeVec ρ (stabLoc σ J L v) φ x = z • x := by
  intro F E _ _ _ _ _ σ n J L v w h B φ hφ
  classical
  by_cases hsp : IsSplit (E := E) v ∧
      ∃ e : GLoc σ J v ≃* GL (Fin n) (w.adicCompletion E), IsSplitChart σ J L h e
  · obtain ⟨hv, e0, he0⟩ := hsp
    obtain ⟨z, hz⟩ := GlobalTheory.T.satake_determines_sphericalHeckeCharacter_GL E w n B (φ ∘ e0.symm) (comp_symm_mem_hecke e0 he0.2 hφ)
    refine ⟨z, fun V _ _ ρ x hx => ?_⟩
    rw [heckeVec_eq_comp_symm e0 he0.2 hφ hx.mem_fixed]
    exact hz V (ρ.comp e0.symm.toMonoidHom) x (hx.isSatVecGL hv he0)
  by_cases hin : ∃ (c : w.adicCompletion E →+* w.adicCompletion E) (ϖ : w.adicCompletion E)
      (e : GLoc σ J v ≃* GU c n) (α : Fin (n / 2) → ℂˣ),
      IsUnramInv ϖ c (qV F v) ∧ IsInertChart σ J L h c e ∧ B = GlobalTheory.LGrp.bcParam n α
  · obtain ⟨c0, ϖ0, e0, α0, hU0, hC0, hB0⟩ := hin
    have hmem := comp_symm_mem_hecke e0 hC0.2.2 hφ
    refine ⟨SatU ϖ0 (qV F v) (φ ∘ e0.symm) (fun i => (α0 i : ℂ)), fun V _ _ ρ x hx => ?_⟩
    have hfx := hx.mem_fixed
    rcases hx with ⟨hv, e, he, -⟩ | ⟨-, c, ϖ, e, α, hU, hC, hS, hB⟩
    · exact (hsp ⟨hv, e, he⟩).elim
    · obtain rfl : c = c0 := IsConjAt.unique hC.1 hC0.1
      have hS0 := IsSatVecU.of_chart hC hC0 hS
      rw [heckeVec_eq_comp_symm e0 hC0.2.2 hφ hfx, hS0.2.2 _ hmem]
      congr 1
      rw [satU_eq_of_isUnramInv hU hU0 (Nat.mul_div_le n 2)]
      exact GlobalTheory.T.unitarySatakeTransform_eq_of_baseChangeSatakeParameter_eq _ ϖ0 c (qV F v) n hU0 α α0 (hB.symm.trans hB0) _ hmem
  · refine ⟨0, fun V _ _ ρ x hx => ?_⟩
    rcases hx with ⟨hv, e, he, -⟩ | ⟨-, c, ϖ, e, α, hU, hC, -, hB⟩
    · exact (hsp ⟨hv, e, he⟩).elim
    · exact (hin ⟨c, ϖ, e, α, hU, hC, hB⟩).elim

end GlobalTheory.LFun.EigLoc
