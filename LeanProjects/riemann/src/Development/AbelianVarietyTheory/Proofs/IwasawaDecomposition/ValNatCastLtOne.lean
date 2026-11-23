import Mathlib
import Formalism.LocalToGlobal.HermitianForms.DefsGH
import Formalism.LocalToGlobal.Columns.RecLevelLocT

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.UG Formalism.L2.Forms Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.LevCong

variable {F : Type} [Field F] [NumberField F]

theorem val_natCast_lt_one (v : HeightOneSpectrum (𝓞 F)) (p : ℕ) (hv : (p : 𝓞 F) ∈ v.asIdeal) :
    Valued.v (p : v.adicCompletion F) < 1 := by
  have : (p : v.adicCompletion F) = algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F (p : 𝓞 F)) := by simp
  rw [this]
  have h2 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (K := F) v (algebraMap (𝓞 F) F (p : 𝓞 F))
  have h3 := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v _).2 hv
  exact h2 ▸ h3

theorem redM_eq_one {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (p : ℕ) (hv : (p : 𝓞 F) ∈ v.asIdeal)
    (M : Matrix (Fin n) (Fin n) (v.adicCompletion F))
    (hM : ∀ r c, ∃ t ∈ v.adicCompletionIntegers F, M r c = (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) r c + p * t) :
    redM F v M = 1 := by
  have hp : IsLocalRing.residue (v.adicCompletionIntegers F) (p : v.adicCompletionIntegers F) = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff]
    refine (Valuation.mem_maximalIdeal_iff _ _).2 ?_
    simpa using val_natCast_lt_one v p hv
  ext r c
  obtain ⟨t, ht, e⟩ := hM r c
  set u : v.adicCompletionIntegers F := (if r = c then 1 else 0) + p * ⟨t, ht⟩ with hu
  have e' : M r c = (u : v.adicCompletion F) := by
    rw [e, hu, Matrix.one_apply]
    split_ifs <;> simp
  have hm : M r c ∈ v.adicCompletionIntegers F := e' ▸ u.2
  unfold redM
  rw [dif_pos hm]
  have : (⟨M r c, hm⟩ : v.adicCompletionIntegers F) = u := Subtype.ext e'
  rw [this, hu, map_add, map_mul, hp, zero_mul, add_zero, Matrix.one_apply]
  split_ifs <;> simp

theorem mem_Uloc_of_cong : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} {gp : Fin 2 → ℕ}
    (S : Formalism.L2.Forms.StepLevel F E σ J T f bad) (G : GLoc F E σ gp)
    {H : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp a : 𝓞 F) ∈ v.asIdeal → Subgroup (GL (Fin n) (kv F v))}
    {lam : ∀ a v h, H a v h →* ℂˣ} (_ : GLevH S G H lam) (a : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (_ : (gp a : 𝓞 F) ∈ v.asIdeal)
    (x : GL (Fin n) (E ⊗[F] v.adicCompletion F)) (_ : x ∈ levelVL σ J v S.Lb)
    (_ : ∀ y ∈ latS (F := F) (v.adicCompletion F) (intV E v) S.Lb, ∃ z ∈ latS (F := F) (v.adicCompletion F) (intV E v) S.Lb,
      (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y - y = ((gp a : ℕ) : E ⊗[F] v.adicCompletion F) • z),
    x ∈ S.Uloc v := by
  intro F E _ _ _ _ _ σ n J T f bad gp S G H lam L a v h x hx hc
  refine (L.mem a v h x hx).2 ⟨1, (H a v h).one_mem, ?_⟩
  rw [Units.val_one]
  refine (redM_eq_one v (gp a) h _ fun r c => ?_).symm
  set fr := L.fr a v h with hfr
  set φ := G.phi a v h with hφ
  have hinv : ∀ w : Fin n → v.adicCompletion F,
      ((fr⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *ᵥ
        ((fr : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *ᵥ w) = w := fun w => by
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  obtain ⟨y, hy, hyw⟩ := (L.fr_lat a v h ((fr : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *ᵥ Pi.single c 1)).2 (fun b => by
    show (((fr⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *ᵥ _) b ∈ _
    rw [hinv, Pi.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _)
  obtain ⟨z, hz, e⟩ := hc y hy
  have ht := (L.fr_lat a v h (fun b => φ (z b))).1 ⟨z, hz, fun _ => rfl⟩ r
  refine ⟨_, ht, ?_⟩
  have hy' : (fr : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *ᵥ Pi.single c 1 = φ ∘ y := (funext hyw).symm
  have e2 : ((bc φ x : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *ᵥ (φ ∘ y) =
      φ ∘ y + ((gp a : ℕ) : v.adicCompletion F) • fun b => φ (z b) := by
    funext b
    have e3 := congrArg φ (congrFun e b)
    rw [Pi.sub_apply, map_sub, RingHom.map_mulVec, Pi.smul_apply, smul_eq_mul, map_mul, map_natCast, sub_eq_iff_eq_add'] at e3
    exact e3
  have e4 : G.mat a v h fr x *ᵥ Pi.single c 1 = Pi.single c 1 + ((gp a : ℕ) : v.adicCompletion F) •
      (((fr⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *ᵥ fun b => φ (z b)) := by
    unfold GLoc.mat
    rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hy', ← hφ, e2, Matrix.mulVec_add,
      Matrix.mulVec_smul, ← hy', hinv]
  have e5 := congrFun e4 r
  rw [Matrix.mulVec_single_one, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply] at e5
  rw [Matrix.one_apply]
  exact e5

end GlobalTheory.Mem.LevCong
