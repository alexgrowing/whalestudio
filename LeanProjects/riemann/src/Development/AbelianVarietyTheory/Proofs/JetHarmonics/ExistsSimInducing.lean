import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueFramedPointMoveUniversalTriple
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrMoveTransfer
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSimilitudeOfAutModLevelIdeal

open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Classical

namespace GlobalTheory.CoverCharacter

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem sup_eq_top_of_level (l l₂ : Level H) (p : ℕ) (I : Ideal (𝓞 E)) (hM : l₂.M = l.M * p)
    (hp : Nat.Coprime p l.M) (hI : l₂.Mb = l.Mb * I) : l.Mb ⊔ I = ⊤ := by
  have h0 : (Ideal.span {(l.M : 𝓞 E)} : Ideal (𝓞 E)) ≠ 0 := by
    have := l.three_le
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
    omega
  have h1 : Ideal.span {(l.M : 𝓞 E)} * (I * I.map (H.bar : 𝓞 E →+* 𝓞 E)) =
      Ideal.span {(l.M : 𝓞 E)} * Ideal.span {(p : 𝓞 E)} := by
    have h := l₂.prod
    rw [hI, Ideal.map_mul, hM, Nat.cast_mul, ← Ideal.span_singleton_mul_span_singleton] at h
    rw [← h, ← l.prod]
    ring
  have h2 := mul_left_cancel₀ h0 h1
  have hpI : (p : 𝓞 E) ∈ I := by
    have : (p : 𝓞 E) ∈ I * I.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [h2]; exact Ideal.mem_span_singleton_self _
    exact (Ideal.mul_le_inf this).1
  have hMM : (l.M : 𝓞 E) ∈ l.Mb := by
    have : (l.M : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [l.prod]; exact Ideal.mem_span_singleton_self _
    exact (Ideal.mul_le_inf this).1
  obtain ⟨u, v, huv⟩ := (Nat.isCoprime_iff_coprime.2 hp).map (Int.castRingHom (𝓞 E))
  rw [Ideal.eq_top_iff_one, ← huv]
  refine Ideal.add_mem _ (Ideal.mem_sup_right (I.mul_mem_left _ ?_)) (Ideal.mem_sup_left (l.Mb.mul_mem_left _ ?_))
  · simpa using hpI
  · simpa using hMM

theorem exists_sim_inducing (D : Datum H) (hpq : 1 ≤ D.p + D.q) (l l₂ : Level H) (p : ℕ) (I : Ideal (𝓞 E))
    (hd : l.Dvd l₂) (hM : l₂.M = l.M * p) (hp : Nat.Coprime p l.M) (hI : l₂.Mb = l.Mb * I) (hA : l₂.A = 1)
    (k : (D.La ⧸ (I • ⊤ : Submodule (𝓞 E) D.La)) ≃ₗ[𝓞 E] (D.La ⧸ (I • ⊤ : Submodule (𝓞 E) D.La))) :
    ∃ g : Sim D, g.InGam l l₂ ∧
      ∀ a : D.La, (Submodule.Quotient.mk (g.f l₂.M a) : D.La ⧸ (I • ⊤ : Submodule (𝓞 E) D.La)) =
        k (Submodule.Quotient.mk a) := by
  obtain ⟨e, he, e', he', hee⟩ := Submodule.mem_sup.1
    (show (1 : 𝓞 E) ∈ l.Mb ⊔ I by rw [sup_eq_top_of_level l l₂ p I hM hp hI]; trivial)
  haveI : Module.Projective (𝓞 E) D.La := D.proj
  obtain ⟨f, hf⟩ := Module.projective_lifting_property (I • ⊤ : Submodule (𝓞 E) D.La).mkQ
    (k.toLinearMap ∘ₗ (I • ⊤ : Submodule (𝓞 E) D.La).mkQ) (Submodule.mkQ_surjective _)
  have hf' : ∀ a, (Submodule.Quotient.mk (f a) : D.La ⧸ (I • ⊤ : Submodule (𝓞 E) D.La)) =
      k (Submodule.Quotient.mk a) := fun a => LinearMap.congr_fun hf a
  set F : D.La →ₗ[𝓞 E] D.La := e • f + e' • LinearMap.id with hF
  have h1 : ∀ x, F x - f x ∈ (I • ⊤ : Submodule (𝓞 E) D.La) := fun x => by
    have : F x - f x = e' • (x - f x) := by
      have h : e = 1 - e' := by linear_combination hee
      simp only [hF, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply]
      rw [h, sub_smul, one_smul, smul_sub]; abel
    rw [this]
    exact Submodule.smul_mem_smul he' Submodule.mem_top
  have h2 : ∀ x, F x - x ∈ (l.Mb • ⊤ : Submodule (𝓞 E) D.La) := fun x => by
    have : F x - x = e • (f x - x) := by
      have h : e' = 1 - e := by linear_combination hee
      simp only [hF, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply]
      rw [h, sub_smul, one_smul, smul_sub]; abel
    rw [this]
    exact Submodule.smul_mem_smul he Submodule.mem_top
  have lM : (l₂.Mb • ⊤ : Submodule (𝓞 E) D.La) ≤ l.Mb • ⊤ := Submodule.smul_mono_left hd.2.1
  have lI : (l₂.Mb • ⊤ : Submodule (𝓞 E) D.La) ≤ I • ⊤ :=
    Submodule.smul_mono_left (by rw [hI]; exact Ideal.mul_le_inf.trans inf_le_right)
  obtain ⟨g, g1, -⟩ := GlobalTheory.exists_sim_of_aut_mod E H D l₂ 1 F hpq one_pos (Nat.coprime_one_left _) (by
    intro x hx
    have x1 : x ∈ (l.Mb • ⊤ : Submodule (𝓞 E) D.La) := by
      have := Submodule.sub_mem _ (lM hx) (h2 x)
      rwa [sub_sub_cancel] at this
    have x2 : x ∈ (I • ⊤ : Submodule (𝓞 E) D.La) := by
      have := Submodule.sub_mem _ (lI hx) (h1 x)
      rw [sub_sub_cancel, ← Submodule.Quotient.mk_eq_zero, hf', k.map_eq_zero_iff,
        Submodule.Quotient.mk_eq_zero] at this
      exact this
    have : x = e • x + e' • x := by rw [← add_smul, hee, one_smul]
    rw [this, hI]
    refine Submodule.add_mem _ ?_ ?_
    · rw [Submodule.mul_smul]; exact Submodule.smul_mem_smul he x2
    · rw [mul_comm, Submodule.mul_smul]; exact Submodule.smul_mem_smul he' x1)
  have hM0 : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  have hp0 : 0 < p := by
    have := l₂.three_le
    rcases Nat.eq_zero_or_pos p with h | h
    · rw [hM, h] at this; omega
    · exact h
  have hMM : (l.M : 𝓞 E) ∈ l.Mb := by
    have : (l.M : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [l.prod]; exact Ideal.mem_span_singleton_self _
    exact (Ideal.mul_le_inf this).1
  have hA1 : l.A = 1 := Nat.dvd_one.1 (hA ▸ hd.2.2)
  refine ⟨g, ⟨by rw [hA]; simp, fun a => ?_, fun a => ⟨g.f l.A a - a, by rw [hA1, one_smul]⟩⟩, fun a => ?_⟩
  · obtain ⟨b, hb⟩ := g.tower l.M p hM0 hp0 a
    rw [← hM] at hb
    have h3 : g.f l₂.M a - g.f l.M a ∈ (l.Mb • ⊤ : Submodule (𝓞 E) D.La) := by
      rw [hb, ← Nat.cast_smul_eq_nsmul (𝓞 E)]
      exact Submodule.smul_mem_smul hMM Submodule.mem_top
    have := Submodule.sub_mem _ (Submodule.add_mem _ (lM (g1 a)) (h2 a)) h3
    convert this using 1
    abel
  · rw [← hf', Submodule.Quotient.eq]
    have := Submodule.add_mem _ (lI (g1 a)) (h1 a)
    rwa [sub_add_sub_cancel] at this

theorem psi_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), 1 ≤ Dw.p + Dw.q → d.IsLev → d.l₂.A = 1 → ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra d.c₂.F k], Nonempty (FrPt d.Xo₂ d.c₂ k) → ∀ ψ ψ' : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ, d.PsiTie ψ → d.PsiTie ψ' → ψ = ψ' := by
  intro E _ _ _ H Dw l Xo c n d hpq hlev hA K _ _ _ ⟨y⟩ ψ ψ' h h'
  obtain ⟨hd, hM, hp, hI, -, -, -, -, hne⟩ := hlev
  ext k
  obtain ⟨g, hg, hk⟩ := exists_sim_inducing Dw hpq l d.l₂ d.pd d.I hd hM hp hI hA k
  obtain ⟨ρ, hρ⟩ := GlobalTheory.LevelActionLaws.exists_levAut hpq d.Xo₂ g hg.1
  obtain ⟨hs, ν, -⟩ := id hρ
  obtain ⟨y', hy'⟩ := (GlobalTheory.exists_unique_frMove E H Dw d.l₂ d.Xo₂ d.c₂ ρ.hom ν hs K y).1
  have hgA : ∀ a, Dw.ModN d.l₂.A (g.f d.l₂.A a - a) := fun a => ⟨g.f d.l₂.A a - a, by rw [hA, one_smul]⟩
  have e1 := h k g ρ hg hgA hρ hk K y y' hy'.1
  have e2 := h' k g ρ hg hgA hρ hk K y y' hy'.1
  have e3 := mul_right_cancel₀ (hne K y) (e1.symm.trans e2)
  have e4 := d.eF.injective ((algebraMap d.c₂.F K).injective e3)
  rw [e4]

end GlobalTheory.CoverCharacter
