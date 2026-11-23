import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Formalism.LocalToGlobal.IndefiniteReal.DatumF
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsFundamentalDomainOfHaar
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.ResEtaFOfPow

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sig_invol {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := ⟨(IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := E)).toRingHom⟩
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem sig_ne {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : ∃ x, σ x ≠ x := by
  by_contra hc
  push_neg at hc
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := ⟨(IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := E)).toRingHom⟩
  have hr : NumberField.ComplexEmbedding.IsReal τ := by
    ext x
    simp only [NumberField.ComplexEmbedding.conjugate_coe_eq]
    have e := h.2.2.2 τ x
    rw [hc] at e
    exact e.symm
  have hc2 := h.2.1.isComplex (NumberField.InfinitePlace.mk τ)
  exact (NumberField.InfinitePlace.isComplex_mk_iff.1 hc2) hr

variable (F E) in

abbrev normI : (AF F ⊗[F] E)ˣ →* (AF F)ˣ := Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F)

variable (F E) in

abbrev normGrp : Subgroup (AF F)ˣ :=
  (Units.map (algebraMap F (AF F)).toMonoidHom).range ⊔ (normI F E).range

theorem algebraMap_inj : Function.Injective (algebraMap (AF F) (AF F ⊗[F] E)) :=
  Algebra.TensorProduct.includeLeft_injective (S := F) (algebraMap F E).injective

theorem exists_form {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : ∃ δ : F, ¬ IsSquare δ ∧
    ∀ a : (AF F)ˣ, a ∈ (normI F E).range ↔
      ∃ x y : AF F, (a : AF F) = x ^ 2 - algebraMap F (AF F) δ * y ^ 2 := by
  obtain ⟨δ, hδ, hh⟩ := GlobalTheory.T.quadraticExt_norm_form_over_algebra F E σ h.2.2.1 (sig_invol h) (sig_ne h)
  obtain ⟨h1, h2⟩ := hh (AF F)
  have hN : ∀ z : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) (Algebra.norm (AF F) z) =
      z * sigR (AF F) σ z := fun z => by
    obtain ⟨x, y, e1, e2⟩ := h1 z
    rw [e1, e2]
  refine ⟨δ, hδ, fun a => ⟨?_, ?_⟩⟩
  · rintro ⟨z, rfl⟩
    obtain ⟨x, y, e1, -⟩ := h1 z
    exact ⟨x, y, e1⟩
  · rintro ⟨x, y, e⟩
    obtain ⟨z, hz⟩ := h2 x y
    rw [← e] at hz
    have hu : IsUnit z := isUnit_of_mul_isUnit_left (hz ▸ a.isUnit.map _)
    refine ⟨hu.unit, Units.ext (algebraMap_inj (F := F) (E := E) ?_)⟩
    exact (hN z).trans hz

theorem isOpen_normGrp {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : IsOpen (normGrp F E : Set (AF F)ˣ) := by
  obtain ⟨δ, hδ, hf⟩ := exists_form h
  have h0 : δ ≠ 0 := fun e => hδ (e ▸ IsSquare.zero)
  refine Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset (GlobalTheory.T.quadraticForm_ideleValues_mem_nhds_one F δ h0) fun a ha => ?_)
  exact Subgroup.mem_sup_right ((hf a).2 ha)

theorem normGrp_ne_top {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : normGrp F E ≠ ⊤ := by
  obtain ⟨δ, hδ, hf⟩ := exists_form h
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_idele_ne_algebraMap_mul_norm_of_not_isSquare F δ hδ
  intro e
  have hm : a ∈ normGrp F E := e ▸ Subgroup.mem_top a
  obtain ⟨_, ⟨t, rfl⟩, n, hn, rfl⟩ := Subgroup.mem_sup.1 hm
  obtain ⟨x, y, e⟩ := (hf n).1 hn
  exact ha t x y (by rw [Units.val_mul, e]; rfl)

theorem sq_mem_normGrp {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (a : (AF F)ˣ) : a * a ∈ normGrp F E := by
  obtain ⟨δ, -, hf⟩ := exists_form h
  exact Subgroup.mem_sup_right ((hf _).2 ⟨a, 0, by simp [pow_two]⟩)

theorem exists_isEtaF {σ : E →ₐ[F] E} (h : IsCMExt F E σ) :
    ∃ η : (AF F)ˣ →* Circle, Formalism.IndefR.DatumF.IsEtaF E η := by
  obtain ⟨a, ha⟩ : ∃ a, a ∉ normGrp F E := by
    by_contra hc
    push_neg at hc
    exact normGrp_ne_top h (eq_top_iff.2 fun a _ => hc a)
  obtain ⟨η, h1, h2⟩ := GlobalTheory.VolHeckeCompare.exists_char_of_not_mem _ (sq_mem_normGrp h) a ha
  refine ⟨η, ?_, fun b => h1 (Subgroup.mem_sup_left ⟨b, rfl⟩), fun x => h1 (Subgroup.mem_sup_right ⟨x, rfl⟩),
    fun e => h2 (by rw [e]; rfl)⟩
  refine continuous_of_continuousAt_one η ?_
  refine (continuousAt_const (y := (1 : Circle))).congr ?_
  filter_upwards [(isOpen_normGrp h).mem_nhds (one_mem _)] with b hb
  exact (h1 hb).symm

open Classical in

theorem resEtaF_of_resEtaPow : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (χ : (AF F ⊗[F] E)ˣ →* Circle) (n : ℕ),
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ n → Formalism.IndefR.DatumF.ResEtaF χ n := by
  intro F E _ _ _ _ _ σ B hB χ n hχ
  have hcm : IsCMExt F E σ := hB.cm
  refine ⟨exists_isEtaF hcm, fun η hη a => ?_⟩
  obtain ⟨-, h1, h2, h3⟩ := hη
  have hS : ∀ x ∈ normGrp F E, η x = 1 := by
    have : normGrp F E ≤ η.ker := sup_le (by rintro _ ⟨y, rfl⟩; exact h1 y) (by rintro _ ⟨y, rfl⟩; exact h2 y)
    exact fun x hx => this hx
  have hsq : ∀ x, η x * η x = 1 := fun x => by rw [← map_mul]; exact hS _ (sq_mem_normGrp hcm x)
  have key : ∀ x, ((χ (Formalism.IndefR.DatumF.idFF F E x) : Circle) : ℂ) = if x ∈ normGrp F E then 1 else (-1) ^ n :=
    fun x => hχ x
  apply Circle.ext
  rw [key a, Circle.coe_pow]
  by_cases ha : a ∈ normGrp F E
  · rw [if_pos ha, hS a ha]; simp
  rw [if_neg ha]
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | hn
  · rw [← two_mul, pow_mul, pow_mul, neg_one_sq, one_pow, ← Circle.coe_pow, sq, hsq a]; simp
  have hn1 : ((-1 : ℂ)) ^ n = -1 := hn.neg_one_pow
  obtain ⟨b, hb⟩ : ∃ b, η b ≠ 1 := by
    by_contra hh
    push_neg at hh
    exact h3 (MonoidHom.ext hh)
  have hbS : b ∉ normGrp F E := fun hm => hb (hS b hm)
  have hab : a * b ∈ normGrp F E := by
    by_contra hn2
    have e := key (a * b)
    rw [map_mul, map_mul, Circle.coe_mul, key a, key b, if_neg ha, if_neg hbS, if_neg hn2, hn1] at e
    norm_num at e
  have hηb : (η b : ℂ) = -1 := GlobalTheory.VolHeckeCompare.circle_eq_neg_one (hsq b) hb
  have e2 : (η a : ℂ) * η b = 1 := by rw [← Circle.coe_mul, ← map_mul, hS _ hab]; simp
  rw [hηb] at e2
  have hηa : (η a : ℂ) = -1 := by linear_combination -e2
  rw [hηa]

end GlobalTheory.ResEtaFOfPow
