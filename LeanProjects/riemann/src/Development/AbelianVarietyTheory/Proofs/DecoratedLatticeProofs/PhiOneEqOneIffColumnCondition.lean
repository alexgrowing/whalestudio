import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ColCond
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PhiOneVal

namespace GlobalTheory.PhiOneVal

section
variable {E : Type} [Field E] [NumberField E] [StarRing E]

omit [StarRing E] in
theorem phit_mem_loc {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (M : Submodule (𝓞 E) (Fin n → E)) (y : Fin n → E) :
    y ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal M ↔ ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ s • y ∈ M := Iff.rfl

omit [StarRing E] in
theorem phit_mem_std {n : ℕ} (y : Fin n → E) :
    y ∈ Formalism.L2.Col.stdLat E n ↔ ∀ i, ∃ c : 𝓞 E, algebraMap (𝓞 E) E c = y i := by
  simp [Formalism.L2.Col.stdLat, Submodule.mem_pi, Submodule.mem_one]

omit [StarRing E] in
theorem phit_single_std {n : ℕ} (r : Fin n) : (Pi.single r 1 : Fin n → E) ∈ Formalism.L2.Col.stdLat E n := by
  rw [phit_mem_std]
  intro i
  by_cases h : i = r
  · subst h; exact ⟨1, by simp⟩
  · exact ⟨0, by simp [h]⟩

omit [StarRing E] in
theorem phit_mk_ne (P : HeightOneSpectrum (𝓞 E)) {s : 𝓞 E} (hs : s ∉ P.asIdeal) :
    Ideal.Quotient.mk P.asIdeal s ≠ 0 := fun h => hs (Ideal.Quotient.eq_zero_iff_mem.1 h)

theorem phit_local {a b : ℕ} {ST SG SG' : Finset (HeightOneSpectrum (𝓞 E))}
    (d : Formalism.L2.Col.Deco E a ST SG) (d' : Formalism.L2.Col.Deco E b ST SG') (t : 𝓞 E) (hd : d.Ok) (hd' : d'.Ok)
    (hN : d.N = Formalism.L2.Col.stdLat E a) (hN' : d'.N = Formalism.L2.Col.stdLat E b) (P : ST)
    (hf : ∀ x ∈ Formalism.L2.Col.stdLat E a, ∀ r : Fin a, r.1 + 1 = a → ∀ c : 𝓞 E, algebraMap (𝓞 E) E c = x r →
      d.f P x = Ideal.Quotient.mk P.1.asIdeal (t * c))
    (hf' : ∀ x ∈ Formalism.L2.Col.stdLat E b, ∀ r : Fin b, r.1 + 1 = b → ∀ c : 𝓞 E, algebraMap (𝓞 E) E c = x r →
      d'.f P x = Ideal.Quotient.mk P.1.asIdeal (t * c))
    (x : Formalism.L2.Col.HomE E a b) :
    (∀ y ∈ d.at P.1, x y ∈ d'.at P.1 ∧ d'.f P (x y) = d.f P y) ↔ ColCond P.1 t x := by
  haveI := P.1.isPrime
  have hle : ∀ y ∈ Formalism.L2.Col.stdLat E a, y ∈ d.at P.1 := fun y hy =>
    (phit_mem_loc P.1 _ _).2 ⟨1, (Ideal.ne_top_iff_one _).1 P.1.isPrime.ne_top, by rw [hN, one_smul]; exact hy⟩
  have hxs : ∀ (s : 𝓞 E) (y : Fin a → E), x (s • y) = s • x y := fun s y => x.map_smul_of_tower s y

  have hfe : ∀ r : Fin a, d.f P (Pi.single r 1) =
      Ideal.Quotient.mk P.1.asIdeal (t * if r.1 + 1 = a then 1 else 0) := by
    intro r
    have hr := r.2
    refine hf _ (phit_single_std r) ⟨a - 1, by omega⟩ (by simp only; omega) _ ?_
    by_cases h : r.1 + 1 = a
    · have : (⟨a - 1, by omega⟩ : Fin a) = r := Fin.ext (by simp only; omega)
      rw [this]; simp [h]
    · have : (⟨a - 1, by omega⟩ : Fin a) ≠ r := fun e => h (by have := congrArg Fin.val e; simp only at this; omega)
      simp [h, this]
  have hsm : ∀ (s : 𝓞 E) (z : Fin b → E) (q : Fin b), (s • z) q = algebraMap (𝓞 E) E s * z q := by
    intro s z q
    rw [Pi.smul_apply, Algebra.smul_def]
  constructor
  · intro h r
    obtain ⟨h1, h2⟩ := h _ (hle _ (phit_single_std r))
    obtain ⟨s, hs, hsx⟩ := (phit_mem_loc P.1 _ _).1 h1
    rw [hN'] at hsx
    choose c hc using (phit_mem_std _).1 hsx
    refine ⟨s, hs, c, fun q => by rw [hc, hsm], fun q hq => ?_⟩
    have e1 := hf' _ hsx q hq (c q) (hc q)
    rw [hd'.f_smul P s _ h1, h2, hfe, ← map_mul] at e1
    have e2 := Ideal.Quotient.eq.1 e1.symm
    convert e2 using 1
    split_ifs <;> ring
  · intro h
    have hb : b ≠ 0 := by
      rintro rfl
      obtain ⟨z, hz, hz0⟩ := hd'.f_ne P
      apply hz0
      have h0 := hd'.f_smul P 0 0 (Submodule.zero_mem _)
      rw [Subsingleton.elim z 0]
      simpa using h0
    let M : Submodule (𝓞 E) (Fin a → E) :=
      { carrier := {y | y ∈ d.at P.1 ∧ x y ∈ d'.at P.1 ∧ d'.f P (x y) = d.f P y}
        add_mem' := by
          rintro y z ⟨h1, h2, h3⟩ ⟨k1, k2, k3⟩
          refine ⟨Submodule.add_mem _ h1 k1, by rw [map_add]; exact Submodule.add_mem _ h2 k2, ?_⟩
          rw [map_add, hd'.f_add P _ h2 _ k2, hd.f_add P _ h1 _ k1, h3, k3]
        zero_mem' := by
          refine ⟨Submodule.zero_mem _, by rw [map_zero]; exact Submodule.zero_mem _, ?_⟩
          have h0 := hd.f_smul P 0 0 (Submodule.zero_mem _)
          have h0' := hd'.f_smul P 0 0 (Submodule.zero_mem _)
          simp only [smul_zero, map_zero, zero_mul] at h0 h0'
          rw [map_zero, h0, h0']
        smul_mem' := by
          rintro s y ⟨h1, h2, h3⟩
          refine ⟨Submodule.smul_mem _ s h1, by rw [hxs]; exact Submodule.smul_mem _ s h2, ?_⟩
          rw [hxs, hd'.f_smul P s _ h2, hd.f_smul P s _ h1, h3] }
    have hM : ∀ y, y ∈ M ↔ (y ∈ d.at P.1 ∧ x y ∈ d'.at P.1 ∧ d'.f P (x y) = d.f P y) := fun _ => Iff.rfl
    have he : ∀ r : Fin a, (Pi.single r 1 : Fin a → E) ∈ M := by
      intro r
      obtain ⟨s, hs, c, hc, hq⟩ := h r
      have hsx : s • x (Pi.single r 1) ∈ Formalism.L2.Col.stdLat E b :=
        (phit_mem_std _).2 fun q => ⟨c q, by rw [hc, hsm]⟩
      have h1 : x (Pi.single r 1) ∈ d'.at P.1 := (phit_mem_loc P.1 _ _).2 ⟨s, hs, by rw [hN']; exact hsx⟩
      refine (hM _).2 ⟨hle _ (phit_single_std r), h1, ?_⟩
      have hq' : (⟨b - 1, by omega⟩ : Fin b).1 + 1 = b := by simp only; omega
      have e1 := hf' _ hsx _ hq' (c _) (by rw [hc, hsm])
      rw [hd'.f_smul P s _ h1] at e1
      apply mul_left_cancel₀ (phit_mk_ne P.1 hs)
      rw [e1, hfe, ← map_mul]
      refine Ideal.Quotient.eq.2 ?_
      convert hq _ hq' using 1
      split_ifs <;> ring
    have hstd : ∀ y ∈ Formalism.L2.Col.stdLat E a, y ∈ M := by
      intro y hy
      choose c hc using (phit_mem_std _).1 hy
      have : y = ∑ r, c r • (Pi.single r 1 : Fin a → E) := by
        funext i
        simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def, ← hc]
      rw [this]
      exact Submodule.sum_mem _ fun r _ => Submodule.smul_mem _ _ (he r)
    intro y hy
    obtain ⟨s, hs, hsy⟩ := (phit_mem_loc P.1 _ _).1 hy
    rw [hN] at hsy
    obtain ⟨-, h2, h3⟩ := (hM _).1 (hstd _ hsy)
    rw [hxs] at h2 h3
    obtain ⟨u, hu, huy⟩ := (phit_mem_loc P.1 _ _).1 h2
    have h1 : x y ∈ d'.at P.1 := (phit_mem_loc P.1 _ _).2
      ⟨u * s, fun hm => (P.1.isPrime.mem_or_mem hm).elim hu hs, by rw [mul_smul]; exact huy⟩
    refine ⟨h1, ?_⟩
    rw [hd'.f_smul P s _ h1, hd.f_smul P s _ hy] at h3
    exact mul_left_cancel₀ (phit_mk_ne P.1 hs) h3

end

theorem phiT_eq_one_iff_colCond : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ} {ST SG SG' : Finset (HeightOneSpectrum (𝓞 E))}
    (K : Type) [Field K] (d : Formalism.L2.Col.Deco E a ST SG) (d' : Formalism.L2.Col.Deco E b ST SG') (t : 𝓞 E), d.Ok → d'.Ok →
    d.N = Formalism.L2.Col.stdLat E a → d'.N = Formalism.L2.Col.stdLat E b →
    (∀ P : ST, ∀ x ∈ Formalism.L2.Col.stdLat E a, ∀ r : Fin a, r.1 + 1 = a → ∀ c : 𝓞 E, algebraMap (𝓞 E) E c = x r →
      d.f P x = Ideal.Quotient.mk P.1.asIdeal (t * c)) →
    (∀ P : ST, ∀ x ∈ Formalism.L2.Col.stdLat E b, ∀ r : Fin b, r.1 + 1 = b → ∀ c : 𝓞 E, algebraMap (𝓞 E) E c = x r →
      d'.f P x = Ideal.Quotient.mk P.1.asIdeal (t * c)) →
    ∀ x : Formalism.L2.Col.HomE E a b, (Formalism.L2.Col.phiT K d d' x = 1 ↔ ∀ P : ST, ColCond P.1 t x) := by
  intro E _ _ _ a b ST SG SG' K _ d d' t hd hd' hN hN' hf hf' x
  classical
  unfold Formalism.L2.Col.phiT
  rw [ite_eq_left_iff]
  simp only [zero_ne_one, imp_false, not_not]
  exact forall_congr' fun P => phit_local d d' t hd hd' hN hN' P (hf P) (hf' P) x

end GlobalTheory.PhiOneVal
