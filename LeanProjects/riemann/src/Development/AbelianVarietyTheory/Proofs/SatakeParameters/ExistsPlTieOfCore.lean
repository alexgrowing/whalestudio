import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsDvrFrobeniusLiftStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsDvrExtensionEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FrobeniusDecompositionUnramifiedPrimeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FrobeniusNontrivialOnInertQuadraticStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CosetDecompositionEvenOrderStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GaloisIndexTwoCmConjugationStatement

open NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.Col Formalism.BasicNotions

noncomputable section

namespace GlobalTheory.GO

def primeUnder {E : Type} [Field E] [NumberField E] (g : E ≃ₐ[ℚ] E) (Q : HeightOneSpectrum (𝓞 E)) :
    HeightOneSpectrum (𝓞 E) :=
  Q.comap (MulSemiringAction.toRingHom (E ≃ₐ[ℚ] E) (𝓞 E) g) fun x => ⟨g⁻¹ • x, by simp⟩

theorem mem_primeUnder {E : Type} [Field E] [NumberField E] (g : E ≃ₐ[ℚ] E) (Q : HeightOneSpectrum (𝓞 E)) (x : 𝓞 E) :
    x ∈ (primeUnder g Q).asIdeal ↔ g • x ∈ Q.asIdeal := Iff.rfl

theorem intAt_primeUnder {E : Type} [Field E] [NumberField E] (g : E ≃ₐ[ℚ] E) (Q : HeightOneSpectrum (𝓞 E)) (x : E) :
    IntAt (primeUnder g Q) x ↔ IntAt Q (g x) := by
  constructor
  · rintro ⟨r, s, hs, h⟩
    refine ⟨g • r, g • s, hs, ?_⟩
    have := congrArg g h
    rw [map_mul] at this
    exact this
  · rintro ⟨r, s, hs, h⟩
    refine ⟨g⁻¹ • r, g⁻¹ • s, by rwa [mem_primeUnder, smul_inv_smul], ?_⟩
    have := congrArg g.symm h
    rw [map_mul, AlgEquiv.symm_apply_apply] at this
    exact this

theorem exists_plTie_of_core (X : Fields) (hX : X.Core) (hG : IsGalois ℚ X.E) (hab : ∀ s t : X.E ≃ₐ[ℚ] X.E, s * t = t * s)
    (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (hur : Algebra.IsUnramifiedIn (𝓞 X.E) (Ideal.span {(p : ℤ)}))
    (hin : (Ideal.span {((p : ℕ) : 𝓞 X.Kq)}).IsPrime)
    (hsp : ∀ Q : HeightOneSpectrum (𝓞 X.E), ((p : ℕ) : 𝓞 X.E) ∈ Q.asIdeal → Q ≠ conjPrime₂ Q)
    (m r : ℕ) (lam : X.Tau → DomWeight (m + 1)) (c : ℤ) :
    ∃ (O Kf : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O) (_ : Field Kf) (_ : Algebra O Kf)
      (P : Places p O Kf) (hm : P.m = m), P.r = r ∧ 0 < P.nV ∧
        ∃ T : PlTie X P, T.WtEq (congrArg (· + 1) hm.symm) lam c := by
  obtain ⟨Q, φ, hpQ, hpQ2, hφ, hcard, hstab, htr⟩ := GlobalTheory.T.frobenius_decomposition_unramified_prime X.E p hp hur
  obtain ⟨τ₀, H, γ, cc, hH, hfix, hγ, hcc, hcH⟩ := GlobalTheory.T.galois_index_two_cm_conjugation X hX hG
  have hcO : ∀ x : 𝓞 X.E, cO X.E x = cc • x := fun x => RingOfIntegers.ext (hcc x).symm
  have hc2 : cc * cc = 1 := AlgEquiv.ext fun x => by simp [hcc]
  have hφH : φ ∉ H := fun h => by
    obtain ⟨x, hx, hne⟩ := GlobalTheory.T.frobenius_nontrivial_on_inert_quadratic X.E X.Kq p Q φ hp hX.quad hin hpQ hφ
    exact hne (hfix φ h x hx)
  have hcz : cc ∉ Subgroup.zpowers φ := fun h => hsp Q hpQ (HeightOneSpectrum.ext (Ideal.ext fun x => by
    rw [mem_conjP, hcO, (hstab cc).2 h]))
  obtain ⟨h2, hev, N, g, pos, hN, hpos, hinj, hne, hall⟩ := GlobalTheory.T.coset_decomposition_even_order _ H φ cc hab hH hφH hcH hc2 hcz
  obtain ⟨W, Qq, _, _, _, _, _, i, σ, hfr, hirr, hres, hcomp, hfrob, hper, hσ, hint, hden⟩ :=
    GlobalTheory.T.exists_dvr_frobenius_lift X.E p (orderOf φ) Q φ hp hpQ hpQ2 hφ (pow_orderOf_eq_one φ)
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal W) W := by rwa [hirr.maximalIdeal_eq]
  obtain ⟨O, Kf, _, _, _, _, _, ι, j, w, eK, hfO, hι, hfin, hcO', hw, heK⟩ := GlobalTheory.T.exists_dvr_extension_embedding W Qq X.E X.K i (X.emb τ₀) p
  have hS : HidaSetting p (orderOf φ) W Qq O Kf ι σ j w :=
    ⟨hp, h5, h2, hev, hfr, hfO, hirr, hres.trans hcard, hcomp, hfrob, hper, hι, hfin, hcO', by rw [hw, map_natCast]⟩
  have hσs : ∀ (s : ℕ) (x : X.E), (σ ^ s) (i x) = i ((φ ^ s) x) := by
    intro s x
    induction s with
    | zero => rfl
    | succ s ih => rw [pow_succ', pow_succ', RingAut.mul_apply, ih, hσ]; rfl
  have hcev : ∀ s : ℕ, Even s → cc ^ s = 1 := by
    rintro _ ⟨k, rfl⟩
    rw [← two_mul, pow_mul, pow_two, hc2, one_pow]
  let P : Places p O Kf :=
    { w := w, nV := N, n' := fun _ => orderOf φ, W := fun _ => W, Qq := fun _ => Qq, ι := fun _ => ι, σ := fun _ => σ,
      j := fun _ => j, setting := fun _ => hS, m := m, r := r,
      lam0 := fun v s k => (lam (γ (pos ⟨v, s⟩))).w k + c,
      dom := fun v s a b h => by simpa using (lam (γ (pos ⟨v, s⟩))).anti h }
  refine ⟨O, Kf, _, _, _, _, _, P, rfl, rfl, hN,
    { pr := fun v => primeUnder (g v) Q
      iw := fun v => i.comp (g v : X.E →+* X.E)
      eK := eK
      pos := pos.trans γ
      pr_inj := fun v v' h => hinj v v' ((hstab _).1 fun x => ?_)
      pr_ne := fun v v' h => hne v v' ((hstab _).1 fun x => ?_)
      pr_all := fun Q' => ⟨fun h => ?_, ?_⟩
      iw_int := fun v x => (intAt_primeUnder _ _ _).trans (hint _)
      iw_dense := fun v y k => ?_
      even := fun v s hs x => ?_
      odd := fun v s hs x => ?_ }, fun v s k => rfl⟩
  · rw [mul_smul, ← mem_primeUnder, ← show primeUnder (g v) Q = primeUnder (g v') Q from h, mem_primeUnder, smul_inv_smul]
  · rw [mul_smul, mul_smul, ← mem_primeUnder, ← hcO, ← mem_conjP,
      ← show primeUnder (g v) Q = conjPrime₂ (primeUnder (g v') Q) from h, mem_primeUnder, smul_inv_smul]
  · obtain ⟨a, ha⟩ := htr Q' h
    obtain ⟨v, hv | hv⟩ := hall a
    · refine ⟨v, Or.inl (HeightOneSpectrum.ext (Ideal.ext fun x => ?_))⟩
      rw [ha, ← (hstab _).2 hv, mul_smul, inv_smul_smul]
      rfl
    · refine ⟨v, Or.inr (HeightOneSpectrum.ext (Ideal.ext fun x => ?_))⟩
      rw [ha, ← (hstab _).2 hv, mul_smul, inv_smul_smul, mul_smul, mem_conjP, hcO]
      rfl
  · have hg : ∀ a : X.E ≃ₐ[ℚ] X.E, a • ((p : ℕ) : 𝓞 X.E) = p := fun a =>
      map_natCast (MulSemiringAction.toRingHom (X.E ≃ₐ[ℚ] X.E) (𝓞 X.E) a) p
    rintro ⟨v, rfl | rfl⟩
    · rw [mem_primeUnder, hg]; exact hpQ
    · rw [mem_conjP, map_natCast, mem_primeUnder, hg]; exact hpQ
  · obtain ⟨x, z, h⟩ := hden y k
    refine ⟨(g v)⁻¹ • x, z, Eq.trans ?_ h⟩
    exact congrArg i ((g v).apply_symm_apply _)
  · change eK (X.emb (γ (pos ⟨v, s⟩)) x) = ι ((σ ^ s.val) (i (g v x)))
    rw [hγ, heK, hσs, hpos, hcev _ hs, mul_one]
    rfl
  · change eK (X.emb (γ (pos ⟨v, s⟩)) (star x)) = ι ((σ ^ s.val) (i (g v x)))
    rw [hγ, heK, hσs, hpos, ← hcc, ← AlgEquiv.mul_apply, mul_assoc, ← pow_succ,
      hcev _ (Nat.even_add_one.2 hs), mul_one]
    rfl

end GlobalTheory.GO
