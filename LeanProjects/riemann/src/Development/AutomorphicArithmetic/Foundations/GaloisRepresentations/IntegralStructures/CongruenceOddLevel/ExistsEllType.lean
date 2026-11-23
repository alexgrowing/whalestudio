import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LimWPhi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionFreeSurjZmod

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.CongW

namespace UpperTheory.Gal.Int.Cong

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ} {l : ℕ} [Fact l.Prime]

theorem exists_ellType (ha : 1 ≤ a) (w₀ : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal)
    (N : Set (GL (Fin a) (w₀.adicCompletion E))) (hN : N ∈ nhds (1 : GL (Fin a) (w₀.adicCompletion E))) (m₀ : ℕ) :
    ∃ (m : ℕ) (J : Subgroup (GL (Fin a) (w₀.adicCompletion E))) (θ : J →* Multiplicative (ZMod (l ^ m))), m₀ ≤ m ∧
      (J : Set (GL (Fin a) (w₀.adicCompletion E))) ⊆ N ∧ IsOpen (J : Set (GL (Fin a) (w₀.adicCompletion E))) ∧
      IsCompact (J : Set (GL (Fin a) (w₀.adicCompletion E))) ∧ (∀ x ∈ J, ∀ k : ℕ, 0 < k → x ^ k = 1 → x = 1) ∧
      Function.Surjective θ ∧ ∀ χ : Multiplicative (ZMod (l ^ m)) →* ℂˣ, χ ≠ 1 →
        ∀ (σ : SmIrr (GL (Fin a) (w₀.adicCompletion E))) (v : σ.V), v ≠ 0 →
          (∀ g : J, σ.ρ g v = ((χ (θ g) : ℂˣ) : ℂ) • v) → GlobalTheory.SmGL.IsCuspidal σ.ρ := by
  classical
  have hlp : l.Prime := Fact.out
  have hchar : ∀ {M : ℕ} [NeZero M] (χ : Multiplicative (ZMod M) →* ℂˣ) (z : Multiplicative (ZMod M)),
      χ z = χ (Multiplicative.ofAdd 1) ^ (Multiplicative.toAdd z).val := by
    intro M _ χ z
    rw [← map_pow, ← ofAdd_nsmul, nsmul_one, ZMod.natCast_zmod_val, ofAdd_toAdd]
  rcases Nat.lt_or_ge a 2 with ha1 | ha2
  · obtain rfl : a = 1 := by omega
    obtain ⟨N', hN'N, hN'o, h1N'⟩ := mem_nhds_iff.1 hN
    obtain ⟨J, θ, hJN, hJo, hJc, hJtf, hθ⟩ :=
      TypeExists.exists_congruence_surj (E := E) (l := l) (a := 1) le_rfl w₀ hl m₀ N' hN'o h1N'
    refine ⟨m₀, J, θ, le_rfl, hJN.trans hN'N, hJo, hJc, hJtf, hθ, fun χ _ σ _ _ _ => ⟨σ.smooth, fun s d e he => absurd ?_ he⟩⟩
    refine (Subgroup.eq_bot_iff_forall _).2 fun u hu => ?_
    refine Units.ext (Matrix.ext fun i j => ?_)
    obtain rfl : i = j := Subsingleton.elim _ _
    obtain ⟨⟨b, i⟩, rfl⟩ := e.surjective i
    have h := (GlobalTheory.SmGL.mem_unipRad.1 hu).2 b i i
    rw [Matrix.one_apply_eq] at h
    rw [h, Units.val_one, Matrix.one_apply_eq]
  · obtain ⟨m, hmm, J, lam, hJo, hJc, hJN, hJtf, hsurj, hsc⟩ :=
      TypeExists.exists_type_surj E w₀ a l hlp hl ha2 N hN m₀
    refine ⟨m, J, lam, hmm, hJN, hJo, hJc,
      fun x hx k hk hxk => hJtf x hx (isOfFinOrder_iff_pow_eq_one.2 ⟨k, hk, hxk⟩), hsurj, fun χ hχ σ v hv0 hv => ?_⟩
    haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ hlp.ne_zero⟩
    refine hsc (χ (Multiplicative.ofAdd 1)) ?_ (fun h => hχ (MonoidHom.ext fun z => ?_)) σ v hv0 fun g => ?_
    · rw [← map_pow, ← ofAdd_nsmul, nsmul_one, ZMod.natCast_self, ofAdd_zero, map_one]
    · rw [hchar χ z, h, one_pow, MonoidHom.one_apply]
    · rw [hv g, hchar χ (lam g)]

end UpperTheory.Gal.Int.Cong

end
