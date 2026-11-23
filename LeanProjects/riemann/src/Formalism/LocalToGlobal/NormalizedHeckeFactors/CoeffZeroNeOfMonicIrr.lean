import Formalism.PadicSubsetSums.CentralIdempotents.GaloisConjCentralIdempotent
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs

noncomputable section

open Polynomial Formalism.IrreducibleCountingLemmas.TYPES CategoryTheory

namespace Formalism.L2.NT

variable {g : ℕ} [Fact g.Prime]

def convC (ι : Formalism.CyclotomicNorms.Fbar g →* ℂ) (hι : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → ι x = ι y → x = y)
    (ζ : ℕ → Formalism.CyclotomicNorms.Fbar g) (hζ : IsGenSys ζ) : LabelConv (ZMod g) where
  ι := ι
  ι_inj := hι
  gen := ζ
  gen_order d hd := by
    rw [ZMod.card]
    exact (hζ d hd).1
  gen_norm d e hd he := by
    rw [ZMod.card]
    exact (hζ d hd).2 (d * e) (dvd_mul_right d e) (Nat.mul_pos hd he)

def LabTwLawO {K : Type} [Field K] [Fintype K] [DecidableEq K] {C : LabelConv K} (O : LabelMap K C) : Prop :=
  ∀ (d : ℕ) (τ τ' : FDRep ℂ (GL (Fin d) K)) (x : K), 1 ≤ d → x ≠ 0 → Simple τ → IsCuspidal K τ → Simple τ' →
    IsCuspidal K τ' →
    (∀ (γ : GL (Fin d) K) (m : ℕ),
      C.gen 1 ^ m = algebraMap K (AlgebraicClosure K) (Matrix.det (γ : Matrix (Fin d) (Fin d) K)) →
      LinearMap.trace ℂ τ' (τ'.ρ γ) = C.ι (algebraMap K (AlgebraicClosure K) x) ^ m * LinearMap.trace ℂ τ (τ.ρ γ)) →
    rootsBar K (O.lab d τ') = (rootsBar K (O.lab d τ)).map (· * algebraMap K (AlgebraicClosure K) x)

def eSerO {C : LabelConv (ZMod g)} (O : LabelMap (ZMod g) C) (r : ℕ) (f : (ZMod g)[X]) :
    MonoidAlgebra ℂ (GL (Fin r) (ZMod g)) :=
  ∑ᶠ (z : MonoidAlgebra ℂ (GL (Fin r) (ZMod g)))
    (_ : ∃ τ : FDRep ℂ (GL (Fin r) (ZMod g)), Simple τ ∧ zIdem τ = z ∧ HasLabelO O τ f), z

theorem coeff_zero_ne_of_monic_irr {K : Type} [Field K] {P : K[X]} (hm : P.Monic) (hi : Irreducible P) (hX : P ≠ X) :
    P.coeff 0 ≠ 0 := by
  intro h0
  obtain ⟨q, hq⟩ := X_dvd_iff.mpr h0
  rcases hi.isUnit_or_isUnit hq with hX' | hq'
  · exact not_isUnit_X hX'
  · apply hX
    have hmq : q.Monic := Monic.of_mul_monic_left monic_X (by rw [← hq]; exact hm)
    rw [hq, hmq.isUnit_iff.mp hq', mul_one]

end Formalism.L2.NT

namespace Formalism.L2.PT

open Polynomial CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES

section Transp

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem coe_glEquiv (e : ι ≃ κ) (u : GL ι K) :
    ((glEquiv K e u : GL κ K) : Matrix κ κ K) = Matrix.reindex e e (u : Matrix ι ι K) := rfl

theorem coe_glEquiv_symm (e : ι ≃ κ) (γ : GL κ K) :
    (((glEquiv K e).symm γ : GL ι K) : Matrix ι ι K) = Matrix.reindex e.symm e.symm (γ : Matrix κ κ K) := rfl

theorem transp_ρ (e : ι ≃ κ) (τ : FDRep ℂ (GL ι K)) (γ : GL κ K) :
    (transp e τ).ρ γ = τ.ρ ((glEquiv K e).symm γ) := rfl

theorem character_transp (e : ι ≃ κ) (τ : FDRep ℂ (GL ι K)) (γ : GL κ K) :
    (transp e τ).character γ = τ.character ((glEquiv K e).symm γ) := rfl

theorem simple_transp (e : ι ≃ κ) {τ : FDRep ℂ (GL ι K)} (h : Simple τ) : Simple (transp e τ) := by
  rw [FDRep.simple_iff_char_is_norm_one] at h ⊢
  have hc : Fintype.card (GL κ K) = Fintype.card (GL ι K) := Fintype.card_congr (glEquiv K e).symm.toEquiv
  have hs : ∑ g : GL κ K, (transp e τ).character g * (transp e τ).character g⁻¹ =
      ∑ g : GL ι K, τ.character g * τ.character g⁻¹ := by
    simp only [character_transp]
    symm
    refine Fintype.sum_equiv (glEquiv K e).toEquiv _ _ (fun g => ?_)
    first
      | simp
      | simp [map_inv]
      | rfl
  rw [hs]
  first
    | (rw [hc]; exact h)
    | (simp only [hc]; exact h)
    | (simp only [invOf_eq_inv] at h ⊢; rw [hc]; exact h)
    | (convert h using 3; simp [hc])
    | (convert h using 2; simp [hc])

theorem mem_unip_glEquiv {s : ℕ} (b : κ → Fin s) (e : ι ≃ κ) {u : GL ι K} (hu : u ∈ unip K (b ∘ e)) :
    glEquiv K e u ∈ unip K b := by
  obtain ⟨hp, hu2⟩ := hu
  refine ⟨?_, ?_⟩
  · unfold parab at hp ⊢
    obtain ⟨h1, h2⟩ := hp
    have key : ∀ M : Matrix ι ι K, IsBlockUT K (b ∘ e) M → IsBlockUT K b (Matrix.reindex e e M) := by
      intro M hM
      unfold IsBlockUT at *
      intro i j hij
      rw [Matrix.reindex_apply, Matrix.submatrix_apply]
      exact hM _ _ (by simpa using hij)
    show _ ∧ _
    refine ⟨?_, ?_⟩
    · rw [coe_glEquiv]
      exact key _ h1
    · rw [← map_inv, coe_glEquiv]
      exact key _ h2
  · intro i j hij
    rw [coe_glEquiv, Matrix.reindex_apply, Matrix.submatrix_apply, hu2 (e.symm i) (e.symm j) (by simpa using hij)]
    simp [e.symm.injective.eq_iff]

theorem isCuspidal_transp (e : ι ≃ κ) {τ : FDRep ℂ (GL ι K)} (h : IsCuspidal K τ) :
    IsCuspidal K (transp e τ) := by
  intro s b hb hs v hv
  exact h s (b ∘ e) (hb.comp e.surjective) hs v (fun u hu => by
    have := hv _ (mem_unip_glEquiv b e hu)
    rwa [transp_ρ, MulEquiv.symm_apply_apply] at this)

theorem hasCuspLabel_transp (cv : LabelConv K) (e : ι ≃ κ) {τ : FDRep ℂ (GL ι K)} {P : K[X]}
    (h : HasCuspLabel cv τ P) : HasCuspLabel cv (transp e τ) P := by
  unfold HasCuspLabel at *
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hc : Fintype.card κ = Fintype.card ι := (Fintype.card_congr e).symm
  refine ⟨h1, h2, h3, by rw [h4, hc], ?_⟩
  intro x hx γ hγ z hz m hm
  have hcp : (((glEquiv K e).symm γ : GL ι K) : Matrix ι ι K).charpoly = (γ : Matrix κ κ K).charpoly := by
    first
      | rw [coe_glEquiv_symm, Matrix.charpoly_reindex]
      | simp [coe_glEquiv_symm, Matrix.charpoly_reindex]
  rw [hc] at hm ⊢
  have key := h5 x hx ((glEquiv K e).symm γ) (by rw [hcp]; exact hγ) z (by rw [hcp]; exact hz) m hm
  first
    | (rw [transp_ρ]; exact key)
    | exact key
    | simpa [transp_ρ] using key

end Transp

end Formalism.L2.PT

namespace Formalism.L2.NT

open Formalism.L2.PT

variable {g : ℕ} [Fact g.Prime]

theorem hasLabelO_spec {C : LabelConv (ZMod g)} (O : LabelMap (ZMod g) C) {r : ℕ}
    {τ : FDRep ℂ (GL (Fin r) (ZMod g))} {f : (ZMod g)[X]} (h : HasLabelO O τ f) :
    f.Monic ∧ f.natDegree = r ∧ f.coeff 0 ≠ 0 := by
  obtain ⟨s, b, lam, hb, hlam, -, rfl⟩ := h
  have hfac : ∀ c, (labO O (lam c)).Monic ∧ Irreducible (labO O (lam c)) ∧ labO O (lam c) ≠ X ∧
      (labO O (lam c)).natDegree = Fintype.card {i // b i = c} := by
    intro c
    obtain ⟨i, hi⟩ := hb c
    have hpos : 1 ≤ Fintype.card {i // b i = c} := Fintype.card_pos_iff.mpr ⟨⟨i, hi⟩⟩
    exact O.lab_spec _ _ hpos (simple_transp _ (hlam c).1) (isCuspidal_transp _ (hlam c).2)
  have hmon : ∀ c ∈ (Finset.univ : Finset (Fin s)), (labO O (lam c)).Monic := fun c _ => (hfac c).1
  refine ⟨monic_prod_of_monic _ _ hmon, ?_, ?_⟩
  · rw [natDegree_prod_of_monic _ _ hmon, Finset.sum_congr rfl (fun c _ => (hfac c).2.2.2)]
    first
      | (rw [← Fintype.card_sigma, Fintype.card_congr (Equiv.sigmaFiberEquiv b), Fintype.card_fin])
      | (simp only [Fintype.card_subtype]
         rw [← Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ (b x)), Finset.card_univ,
           Fintype.card_fin])
      | (simp only [Fintype.card_subtype]
         rw [← Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ (b x))]
         simp)
  · rw [coeff_zero_eq_eval_zero, eval_prod]
    refine Finset.prod_ne_zero_iff.mpr fun c _ => ?_
    rw [← coeff_zero_eq_eval_zero]
    exact coeff_zero_ne_of_monic_irr (hfac c).1 (hfac c).2.1 (hfac c).2.2.1

theorem eSerO_eq_zero {C : LabelConv (ZMod g)} (O : LabelMap (ZMod g) C) (r : ℕ) (f : (ZMod g)[X])
    (hf : ¬ (f.Monic ∧ f.natDegree = r ∧ f.coeff 0 ≠ 0)) : eSerO O r f = 0 := by
  unfold eSerO
  apply finsum_eq_zero_of_forall_eq_zero
  intro z
  have hne : ¬ ∃ τ : FDRep ℂ (GL (Fin r) (ZMod g)), Simple τ ∧ zIdem τ = z ∧ HasLabelO O τ f :=
    fun ⟨_, _, _, hτ⟩ => hf (hasLabelO_spec O hτ)
  haveI : IsEmpty (∃ τ : FDRep ℂ (GL (Fin r) (ZMod g)), Simple τ ∧ zIdem τ = z ∧ HasLabelO O τ f) := ⟨hne⟩
  exact finsum_of_isEmpty _

end Formalism.L2.NT

end
