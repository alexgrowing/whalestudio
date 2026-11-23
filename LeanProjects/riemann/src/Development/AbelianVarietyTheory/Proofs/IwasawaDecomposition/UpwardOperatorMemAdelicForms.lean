import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply

noncomputable section

namespace GlobalTheory.LevelHecke.UpKeeps

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

section Fr

variable {ι : Type} [Fintype ι] {n : ℕ} {E : Type} [Field E]

theorem atInf_mul_inv' (emb : ι → E →+* ℂ) (γ : GL (Fin n) E) (τ : ι) :
    atInf emb (γ : Matrix (Fin n) (Fin n) E) τ * atInf emb ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ = 1 := by
  simp only [atInf]
  rw [← Matrix.map_mul, Units.mul_inv]
  simp

theorem atInf_inv_mul' (emb : ι → E →+* ℂ) (γ : GL (Fin n) E) (τ : ι) :
    atInf emb ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ * atInf emb (γ : Matrix (Fin n) (Fin n) E) τ = 1 := by
  simp only [atInf]
  rw [← Matrix.map_mul, Units.inv_mul]
  simp

def trans (emb : ι → E →+* ℂ) (γ : GL (Fin n) E) {G : ι → Matrix (Fin n) (Fin n) ℂ} (y : Frames G) : Frames G :=
  ⟨fun τ => atInf emb (γ : Matrix (Fin n) (Fin n) E) τ * y.1 τ, fun τ => by
    rw [det_mul]
    exact (Matrix.isUnit_det_of_right_inverse (atInf_mul_inv' emb γ τ)).mul (y.2 τ)⟩

theorem isTr_iff (emb : ι → E →+* ℂ) (γ : GL (Fin n) E) {G : ι → Matrix (Fin n) (Fin n) ℂ} (y' y : Frames G) :
    IsTr (atInf emb (γ : Matrix (Fin n) (Fin n) E)) y' y ↔ y' = trans emb γ⁻¹ y := by
  constructor
  · intro h
    apply Subtype.ext
    funext τ
    show y'.1 τ = _ * y.1 τ
    rw [h τ, ← Matrix.mul_assoc, atInf_inv_mul', Matrix.one_mul]
  · rintro rfl τ
    show y.1 τ = _ * (_ * y.1 τ)
    rw [← Matrix.mul_assoc, atInf_mul_inv', Matrix.one_mul]

def twist (emb : ι → E →+* ℂ) (γ : GL (Fin n) E) (G : ι → Matrix (Fin n) (Fin n) ℂ) (c : ℂ) :
    (Frames G → ℂ) →+ (Frames G → ℂ) where
  toFun h := fun y => c * h (trans emb γ⁻¹ y)
  map_zero' := by funext y; simp
  map_add' a b := by funext y; simp [mul_add]

theorem twist_eq_zero (emb : ι → E →+* ℂ) (γ : GL (Fin n) E) (G : ι → Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (hc : c ≠ 0)
    (h : Frames G → ℂ) (h0 : twist emb γ G c h = 0) : h = 0 := by
  funext z
  have e : z = trans emb γ⁻¹ (trans emb γ z) := (isTr_iff emb γ _ _).1 fun _ => rfl
  have h1 : c * h (trans emb γ⁻¹ (trans emb γ z)) = 0 := congrFun h0 (trans emb γ z)
  rw [← e] at h1
  exact (mul_eq_zero.1 h1).resolve_left hc

end Fr

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {ι : Type} [Fintype ι]

theorem atV_conj {v : HeightOneSpectrum (𝓞 F)} {η : GA σ J} (h : AtV v η) (κ : GA σ J) : AtV v (κ * η * κ⁻¹) := by
  intro v' hv'
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_mul, map_inv, h v' hv', mul_one, mul_inv_cancel]

variable (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal)
  {k : Type} [Field k] (p : GA σ J → Pr (𝓞 E) (Fin n → E) k)

theorem pair_move (hp : PMap S v hv p) (γ : GL (Fin n) E) (hγ : γ ∈ UJ (σ : E →+* E) J) (x x' κ : GA σ J)
    (hx : x'.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * x.1 * κ.1) (η : GA σ J) :
    p (x' * η) = (p (x * (κ * η))).act (glE γ) := by
  apply hp.1 γ hγ
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, hx, mul_assoc, mul_assoc]

theorem valAt_move (hb : v ∉ bad) (hp : PMap S v hv p) (g : GA σ J → Frames (gramC J emb) → ℂ) (hg : g ∈ AdFun S emb)
    (γ : GL (Fin n) E) (hγ : γ ∈ UJ (σ : E →+* E) J) (x x' : GA σ J) (κ : S.U)
    (hx : x'.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * x.1 * κ.1) (q : Pr (𝓞 E) (Fin n → E) k) :
    valAt v p g x' (q.act (glE γ)) = twist emb γ (gramC J emb) (S.chi κ : ℂ) (valAt v p g x q) := by
  have hκ := (S.U_eq κ.1).1 κ.2
  let c : GA σ J := ⟨κ.1, hκ.1⟩
  have hcv : p (x * c) = p x := (hp.2.1 x c).2 (hκ.2 v)
  have hmv := pair_move S v hv p hp γ hγ x x' c hx
  have hU : ∀ z : GA σ J, p (z * c) = p z := fun z => (hp.2.1 z c).2 (hκ.2 v)
  unfold valAt
  by_cases h : ∃ η, AtV v η ∧ p (x * η) = q
  · have h' : ∃ η, AtV v η ∧ p (x' * η) = q.act (glE γ) := by
      obtain ⟨η, h1, h2⟩ := h
      refine ⟨c⁻¹ * η * c⁻¹⁻¹, atV_conj h1 _, ?_⟩
      rw [hmv, ← h2, ← hU (x * η)]
      congr 2
      group
    rw [dif_pos h, dif_pos h']
    obtain ⟨h1, h2⟩ := h.choose_spec
    obtain ⟨h1', h2'⟩ := h'.choose_spec
    generalize h.choose = η at h1 h2
    generalize h'.choose = η' at h1' h2'
    rw [hmv] at h2'
    have h3 := Pr.act_injective _ h2'
    have h4 : p (x * η * (η⁻¹ * c * η')) = p (x * η) := by
      rw [h2, ← h3]; congr 1; group
    have h5 := (hp.2.1 _ _).1 h4
    have hoff : ∀ v', v' ≠ v → bc (prV (E := E) v') (η⁻¹ * c * η' : GA σ J).1 = bc (prV (E := E) v') κ.1 := by
      intro v' hv'
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_mul, map_inv, h1 v' hv', h1' v' hv',
        inv_one, one_mul, mul_one]
    have hmem : (η⁻¹ * c * η' : GA σ J).1 ∈ S.U := by
      refine (S.U_eq _).2 ⟨(η⁻¹ * c * η' : GA σ J).2, fun v' => ?_⟩
      by_cases e : v' = v
      · subst e; exact h5
      · rw [hoff v' e]; exact hκ.2 v'
    have hchi : S.chi ⟨_, hmem⟩ = S.chi κ := by
      have := S.chi_triv (κ⁻¹ * ⟨_, hmem⟩) fun v' hv' => by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
        show _ * bc (prV (E := E) v') (η⁻¹ * c * η' : GA σ J).1 = 1
        rw [hoff v' (fun e => hb (e ▸ hv')), inv_mul_cancel]
      rw [map_mul, map_inv, inv_mul_eq_one] at this
      exact this.symm
    funext y
    have := hg γ hγ (x * η) (x' * η') ⟨_, hmem⟩ (by
      show (x' * η').1 = _ * (x * η).1 * (η⁻¹ * c * η' : GA σ J).1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hx]
      show _ = _ * _ * (_ * κ.1 * _)
      group) y (trans emb γ⁻¹ y) ((isTr_iff emb γ _ _).2 rfl)
    rw [this, hchi]
    rfl
  · have h' : ¬ ∃ η, AtV v η ∧ p (x' * η) = q.act (glE γ) := by
      rintro ⟨η, h1, h2⟩
      rw [hmv] at h2
      have h3 := Pr.act_injective _ h2
      refine h ⟨c * η * c⁻¹, atV_conj h1 _, ?_⟩
      rw [← h3, ← hU (x * (c * η * c⁻¹))]
      congr 1
      group
    rw [dif_neg h, dif_neg h', map_zero]

theorem upAd_mem_adForms : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (ι : Type) [Fintype ι] (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal) (k : Type) [Field k] (p : GA σ J → Pr (𝓞 E) (Fin n → E) k), v ∉ bad → PMap S v hv p → ∀ (res : 𝓞 E →+* k) (t : 𝓞 E) (lam : ι → DomWeight n), ∀ g ∈ AdForms S emb lam, upAd res t v p g ∈ AdForms S emb lam := by
  intro F E _ _ _ _ _ σ n J T f bad ι _ S emb v hv k _ p hb hp res t lam g hg
  refine ⟨?_, fun x _ => ?_⟩
  · intro γ hγ x x' κ hx y y' hy
    have hκ := (S.U_eq κ.1).1 κ.2
    have hpx : p x' = (p x).act (glE γ) := by
      have := pair_move S v hv p hp γ hγ x x' ⟨κ.1, hκ.1⟩ hx 1
      rwa [mul_one, mul_one, (hp.2.1 x ⟨κ.1, hκ.1⟩).2 (hκ.2 v)] at this
    have key : upAd res t v p g x' = twist emb γ (gramC J emb) (S.chi κ : ℂ) (upAd res t v p g x) := by
      have hz := twist_eq_zero emb γ (gramC J emb) (S.chi κ : ℂ) (Units.ne_zero _)
      unfold upAd
      rw [AddMonoidHom.map_finsum_of_preimage_zero _ hz]
      simp only [AddMonoidHom.map_finsum_of_preimage_zero _ hz]
      symm
      refine finsum_mem_eq_of_bijOn (Pr.act (glE γ)) ⟨fun q hq => ?_, (Pr.act_injective _).injOn, fun q hq => ?_⟩ fun q _ => ?_
      · rw [hpx]; exact Pr.Inc.act hq _
      · have e : (q.act (glE γ).symm).act (glE γ) = q := by
          rw [Pr.act_act, LinearEquiv.symm_trans_self, Pr.act_refl]
        refine ⟨q.act (glE γ).symm, ?_, e⟩
        rw [hpx, ← e] at hq
        exact (Pr.inc_act_iff _ _ _).1 hq
      · exact (valAt_move S emb v hv p hb hp g hg.1 γ hγ x x' κ hx q).symm
    rw [key, (isTr_iff emb γ _ _).1 hy]
    rfl
  · have hval : ∀ q, valAt v p g x q ∈ ValC (gramC J emb) lam := by
      intro q
      unfold valAt
      split_ifs with h
      · exact hg.2 _ (Set.mem_univ _)
      · exact zero_mem _
    show upAd res t v p g x ∈ ValC (gramC J emb) lam
    unfold upAd
    refine finsum_induction (· ∈ ValC (gramC J emb) lam) (zero_mem _) (fun _ _ => add_mem) fun q => ?_
    exact finsum_induction (· ∈ ValC (gramC J emb) lam) (zero_mem _) (fun _ _ => add_mem) fun _ => hval q

end GlobalTheory.LevelHecke.UpKeeps

end
