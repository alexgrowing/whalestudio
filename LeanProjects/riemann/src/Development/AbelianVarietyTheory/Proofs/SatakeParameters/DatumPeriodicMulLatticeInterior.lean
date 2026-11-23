import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.WeightedChainData

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions

namespace GlobalTheory

section General

variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}

open NumberField IsDedekindDomain in
variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ} in

theorem _root_.GlobalTheory.phiT_add_smul_homAt (K : Type) [Field K]
    {ST SG SG' S : Finset (HeightOneSpectrum (𝓞 E))}
    (d : _root_.Formalism.L2.Col.Deco E a ST SG) (d' : _root_.Formalism.L2.Col.Deco E b ST SG') (hd' : d'.Ok) (hS : ST ⊆ S) (c : 𝓞 E)
    (hc : ∀ P : ST, c ∈ P.1.asIdeal) (x y₀ : _root_.Formalism.L2.Col.HomE E a b) (hy : y₀ ∈ _root_.Formalism.L2.Col.homAt S d.N d'.N) :
    _root_.Formalism.L2.Col.phiT K d d' (x + c • y₀) = _root_.Formalism.L2.Col.phiT K d d' x := by
  unfold _root_.Formalism.L2.Col.phiT
  have key : ∀ P : ST, ∀ y ∈ d.at P,
      ((x + c • y₀) y ∈ d'.at P ∧ d'.f P ((x + c • y₀) y) = d.f P y) ↔
        (x y ∈ d'.at P ∧ d'.f P (x y) = d.f P y) := by
    intro P y hyP
    have hy0 : y₀ y ∈ d'.at P := hy P.1 (hS P.2) y hyP
    have hcy : c • y₀ y ∈ d'.at P := Submodule.smul_mem _ c hy0
    have hf0 : d'.f P (c • y₀ y) = 0 := by
      rw [hd'.f_smul P c _ hy0, Ideal.Quotient.eq_zero_iff_mem.2 (hc P), zero_mul]
    have happ : (x + c • y₀) y = x y + c • y₀ y := rfl
    rw [happ, Submodule.add_mem_iff_left _ hcy]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rw [← h2, hd'.f_add P _ h1 _ hcy, hf0, add_zero]⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rw [hd'.f_add P _ h1 _ hcy, hf0, add_zero, h2]⟩
  have hiff : (∀ P : ST, ∀ y ∈ d.at P,
      (x + c • y₀) y ∈ d'.at P ∧ d'.f P ((x + c • y₀) y) = d.f P y) ↔
      (∀ P : ST, ∀ y ∈ d.at P, x y ∈ d'.at P ∧ d'.f P (x y) = d.f P y) :=
    forall_congr' fun P => forall₂_congr fun y hyP => key P y hyP
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (hiff.1 h1) h2
  · exact absurd (hiff.2 h2) h1
  · rfl

open NumberField IsDedekindDomain in
variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ} in
omit [NumberField E] [StarRing E] in
theorem _root_.GlobalTheory.inFr_add (f : _root_.Formalism.L2.Col.Sp E a ≃ₗ[E] _root_.Formalism.L2.Col.Sp E a) (f' : _root_.Formalism.L2.Col.Sp E b ≃ₗ[E] _root_.Formalism.L2.Col.Sp E b)
    (x y : _root_.Formalism.L2.Col.HomE E a b) :
    _root_.Formalism.L2.Col.inFr f f' (x + y) = _root_.Formalism.L2.Col.inFr f f' x + _root_.Formalism.L2.Col.inFr f f' y := by
  unfold _root_.Formalism.L2.Col.inFr
  rw [LinearMap.add_comp, LinearMap.comp_add]

open NumberField IsDedekindDomain in
variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ} in

theorem _root_.GlobalTheory.intAt_inFr_smul_homAt {S : Finset (HeightOneSpectrum (𝓞 E))}
    {N : Submodule (𝓞 E) (_root_.Formalism.L2.Col.Sp E a)}
    {N' : Submodule (𝓞 E) (_root_.Formalism.L2.Col.Sp E b)} {P : HeightOneSpectrum (𝓞 E)} (hP : P ∈ S)
    (f : _root_.Formalism.L2.Col.Sp E a ≃ₗ[E] _root_.Formalism.L2.Col.Sp E a) (f' : _root_.Formalism.L2.Col.Sp E b ≃ₗ[E] _root_.Formalism.L2.Col.Sp E b)
    (hf : ∀ x, f x ∈ _root_.Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N ↔ x ∈ _root_.Formalism.L2.Col.stdAt E a P)
    (hf' : ∀ x, f' x ∈ _root_.Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N' ↔ x ∈ _root_.Formalism.L2.Col.stdAt E b P)
    (c r : 𝓞 E) (e : E) (he : e ≠ 0) (hc : algebraMap (𝓞 E) E c = e * algebraMap (𝓞 E) E r)
    (y₀ : _root_.Formalism.L2.Col.HomE E a b) (hy : y₀ ∈ _root_.Formalism.L2.Col.homAt S N N') (s : Fin a) (l : Fin b) :
    _root_.Formalism.L2.Col.IntAt P (e⁻¹ * _root_.Formalism.L2.Col.inFr f f' (c • y₀) (Pi.single s 1) l) := by
  have hv : (Pi.single s 1 : _root_.Formalism.L2.Col.Sp E a) ∈ _root_.Formalism.L2.Col.stdAt E a P := by
    refine ⟨1, P.asIdeal.primeCompl.one_mem, ?_⟩
    rw [one_smul]
    refine Submodule.mem_pi.2 fun i _ => ?_
    by_cases h : i = s
    · subst h
      rw [Pi.single_eq_same]
      exact Submodule.mem_one.2 ⟨1, map_one _⟩
    · rw [Pi.single_eq_of_ne h]
      exact Submodule.zero_mem _
  have hz : y₀ (f (Pi.single s 1)) ∈ _root_.Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N' := hy P hP _ ((hf _).2 hv)
  have hw : f'.symm (y₀ (f (Pi.single s 1))) ∈ _root_.Formalism.L2.Col.stdAt E b P :=
    (hf' _).1 (by rw [LinearEquiv.apply_symm_apply]; exact hz)
  obtain ⟨t, ht, htw⟩ := hw
  have hl : (t • f'.symm (y₀ (f (Pi.single s 1)))) l ∈ (1 : Submodule (𝓞 E) E) :=
    Submodule.mem_pi.1 htw l (Set.mem_univ l)
  obtain ⟨r', hr'⟩ := Submodule.mem_one.1 hl
  have hval : _root_.Formalism.L2.Col.inFr f f' (c • y₀) (Pi.single s 1) l =
      algebraMap (𝓞 E) E c * f'.symm (y₀ (f (Pi.single s 1))) l := by
    show (f'.symm (c • y₀ (f (Pi.single s 1)))) l = _
    rw [← algebraMap_smul E c (y₀ (f (Pi.single s 1))), map_smul, Pi.smul_apply, smul_eq_mul]
  unfold _root_.Formalism.L2.Col.IntAt
  refine ⟨r * r', t, ht, ?_⟩
  rw [hval, hc, map_mul, hr', Pi.smul_apply, Algebra.smul_def]
  calc _ = (e⁻¹ * e) * (algebraMap (𝓞 E) E t * (algebraMap (𝓞 E) E r *
        f'.symm (y₀ (f (Pi.single s 1))) l)) := by ring
    _ = _ := by rw [inv_mul_cancel₀ he, one_mul]; ring

end General

end GlobalTheory
