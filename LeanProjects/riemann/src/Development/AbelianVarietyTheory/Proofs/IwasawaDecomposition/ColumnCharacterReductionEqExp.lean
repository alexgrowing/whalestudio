import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGLocIdGChiTied
import Formalism.LocalRingCardinality.ConjSqrtMinusD
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.Mem.TypePrimes.Red

section Place

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem absNorm_and_unram {p : ℕ} (hp : p.Prime) (hs : GlobalTheory.St.G.SplitsIn E p) (v : HeightOneSpectrum (𝓞 F))
    (h : (p : 𝓞 F) ∈ v.asIdeal) : Ideal.absNorm v.asIdeal = p ∧ (p : 𝓞 F) ∉ v.asIdeal ^ 2 := by
  have := v.isPrime
  have hM : v.asIdeal.IsMaximal := v.isMaximal
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hZ : (Ideal.span {(p : ℤ)}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp'.irreducible
  obtain ⟨⟨w, hwp, hwl⟩⟩ : Nonempty (v.asIdeal.primesOver (𝓞 E)) := inferInstance
  have key := GlobalTheory.St.G.SplitPrime.ram_inertia_tower (F := F) (E := E) p hp hs v.asIdeal h w
  have hL : v.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := (Ideal.liesOver_span_iff v.isPrime.ne_top hp').2 (by simpa using h)
  have hu : Ideal.under ℤ v.asIdeal = Ideal.span {(p : ℤ)} := hL.over.symm
  constructor
  · rw [Ideal.absNorm_eq_pow_inertiaDeg' v.asIdeal hp, Ideal.inertiaDeg'_eq_inertiaDeg, key.1.2, pow_one]
  · intro h2
    have e : (Ideal.span {(p : ℤ)}).ramificationIdx' v.asIdeal = v.asIdeal.ramificationIdx ℤ := by
      rw [← hu]; exact Ideal.ramificationIdx'_eq_ramificationIdx _ _ (by rw [hu, Ne, Ideal.span_singleton_eq_bot]; exact hp'.ne_zero)
    have h3 := Ideal.ramificationIdx_ne_one_iff (p := Ideal.span {(p : ℤ)}) (P := v.asIdeal) (by simpa [Ideal.map_span] using h)
    exact (h3.2 (by simpa [Ideal.map_span] using h2)) (e.trans key.1.1)

end Place

section Low

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) (f : E →+* v.adicCompletion F)

theorem val_le_one (x : 𝓞 E) : Valued.v (f (x : E)) ≤ 1 := by
  obtain ⟨p, hm, h0⟩ := RingOfIntegers.isIntegral_coe x
  have h3 : IsIntegral (Valued.v : Valuation (v.adicCompletion F) _).integer (f (x : E)) := by
    refine ⟨p.map (Int.castRingHom _), hm.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have e : (algebraMap (Valued.v : Valuation (v.adicCompletion F) _).integer (v.adicCompletion F)).comp (Int.castRingHom _) =
        f.comp (algebraMap ℤ E) := RingHom.ext_int _ _
    rw [e, ← Polynomial.hom_eval₂, h0, map_zero]
  exact (Valuation.integer.integers _).mem_of_integral h3

def lowIdeal : Ideal (𝓞 E) where
  carrier := {x | Valued.v (f (x : E)) < 1}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    have e : f ((a + b : 𝓞 E) : E) = f (a : E) + f (b : E) := by simp
    rw [e]
    exact Valuation.map_add_lt _ ha hb
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_setOf_eq, smul_eq_mul] at hx ⊢
    have e : f ((c * x : 𝓞 E) : E) = f (c : E) * f (x : E) := by simp
    rw [e, map_mul]
    exact lt_of_le_of_lt (by simpa using mul_le_mul' (val_le_one v f c) (le_refl (Valued.v (f (x : E))))) hx

theorem mem_lowIdeal {x : 𝓞 E} : x ∈ lowIdeal v f ↔ Valued.v (f (x : E)) < 1 := Iff.rfl

theorem lowIdeal_isPrime : (lowIdeal v f).IsPrime := by
  refine ⟨fun h => ?_, fun {a b} hab => ?_⟩
  · have : (1 : 𝓞 E) ∈ lowIdeal v f := by rw [h]; trivial
    simp [mem_lowIdeal] at this
  · rw [mem_lowIdeal] at hab ⊢
    rw [mem_lowIdeal]
    by_contra hc
    push Not at hc
    have e : f ((a * b : 𝓞 E) : E) = f (a : E) * f (b : E) := by simp
    rw [e, map_mul] at hab
    exact absurd hab (not_lt.2 (one_le_mul hc.1 hc.2))

theorem residue_eq_zero_of_val (x : v.adicCompletionIntegers F) (h : Valued.v (x : v.adicCompletion F) < 1) :
    IsLocalRing.residue _ x = 0 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  rintro ⟨u, rfl⟩
  have h1 : Valued.v (((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) : v.adicCompletion F) ≤ 1 :=
    ((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F).2
  have h2 : ((u : v.adicCompletionIntegers F) : v.adicCompletion F) *
      (((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) : v.adicCompletion F) = 1 := by
    rw [← MulMemClass.coe_mul, Units.mul_inv]; rfl
  have h3 := congrArg Valued.v h2
  rw [map_mul, map_one] at h3
  exact absurd h3 (ne_of_lt (lt_of_le_of_lt (by simpa using mul_le_mul' (le_refl _) h1) h))

end Low

section Generic

variable {X : Fields} {Pr : Primes X} {m : ℕ}

theorem exists_nat_sub_mem {A : Type} [CommRing A] (J : Ideal A) {p : ℕ} (hp : p.Prime) (h : Nat.card (A ⧸ J) = p) (a : A) :
    ∃ n : ℕ, a - (n : A) ∈ J := by
  obtain ⟨e⟩ := nonempty_equiv_zmod (A ⧸ J) hp h
  have := Fact.mk hp
  refine ⟨(e.symm (Ideal.Quotient.mk J a)).val, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero, map_natCast]
  have h2 := map_natCast e (e.symm (Ideal.Quotient.mk J a)).val
  rw [ZMod.natCast_zmod_val, RingEquiv.apply_symm_apply] at h2
  exact h2

theorem columnCharacter_reduction_eq_exp (Ch : Chars X Pr m) (hPr : Pr.Ok) (cm : CMData X.F X.E) (σ₀ : X.K →+* ℂ) (xi : X.E)
    (hW : Ch.WeilTied σ₀ xi) (t : 𝓞 X.E) (ht : xi * (t : X.E) = 1) (G : GLoc X.F X.E cm.sig Pr.g) (hpi : G.piG = Pr.piG)
    (hsig : ∀ x : 𝓞 X.E, cm.sig (x : X.E) = (X.conjO x : X.E))
    (hpsi : ∀ j v h (w : {w // w ∈ Pr.vGs}), w.1.under (𝓞 X.F) = v → ∀ n : ℕ,
      G.psi0 j v h (n : kv X.F v) = σ₀ (Ch.psi0 w (n : 𝓞 X.E ⧸ w.1.asIdeal)))
    (k : Fin 2) (v : HeightOneSpectrum (𝓞 X.F)) (h : ((Pr.g k : ℕ) : 𝓞 X.F) ∈ v.asIdeal)
    (hN : Ideal.absNorm v.asIdeal = Pr.g k) (c y : 𝓞 X.F)
    (hc : Valued.v (algebraMap X.F (v.adicCompletion X.F) (c : X.F) -
      G.phi k v h (inclE (F := X.F) (v.adicCompletion X.F) xi)) < 1)
    (z : v.adicCompletionIntegers X.F) (hz : (z : v.adicCompletion X.F) = algebraMap X.F (v.adicCompletion X.F) (y : X.F)) :
    ∃ b : ℕ, c * y - (b : 𝓞 X.F) ∈ v.asIdeal ∧ G.psi0 k v h (IsLocalRing.residue _ z) =
      Complex.exp (2 * Real.pi * Complex.I * (b : ℤ) / ((Pr.g k : ℕ) : ℂ)) := by
  classical
  have hgp := hPr.g_prime k
  let f : X.E →+* v.adicCompletion X.F := (G.phi k v h).comp (inclE (F := X.F) (v.adicCompletion X.F))
  have hf : ∀ a : X.F, f (algebraMap X.F X.E a) = algebraMap X.F (v.adicCompletion X.F) a := by
    intro a
    show (G.sp k v h ((algebraMap X.F X.E a) ⊗ₜ[X.F] (1 : v.adicCompletion X.F))).1 = _
    have e : (algebraMap X.F X.E a) ⊗ₜ[X.F] (1 : v.adicCompletion X.F) =
        (1 : X.E) ⊗ₜ[X.F] algebraMap X.F (v.adicCompletion X.F) a := by
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    rw [e, G.sp_alg]
  have hlow : ∀ a : 𝓞 X.F, algebraMap (𝓞 X.F) (𝓞 X.E) a ∈ lowIdeal v f ↔ a ∈ v.asIdeal := by
    intro a
    rw [mem_lowIdeal, ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := X.F) v a]
    have e : f ((algebraMap (𝓞 X.F) (𝓞 X.E) a : 𝓞 X.E) : X.E) = algebraMap X.F (v.adicCompletion X.F) (a : X.F) := hf _
    rw [e, Examples₂.adicCompl_val_algebraMap]
  have hg0 : ((Pr.g k : ℕ) : 𝓞 X.E) ≠ 0 := Nat.cast_ne_zero.2 hgp.ne_zero
  have hpr := lowIdeal_isPrime v f
  let w : HeightOneSpectrum (𝓞 X.E) := ⟨lowIdeal v f, hpr, fun e => hg0 (by
    have h1 := (hlow _).2 h
    rw [e, map_natCast] at h1
    exact Ideal.mem_bot.1 h1)⟩
  have hunder : w.under (𝓞 X.F) = v := by
    apply HeightOneSpectrum.ext
    ext a
    exact hlow a
  have hcp : X.conjO (Pr.piG k) ≠ 0 := by
    intro e
    have h1 := hPr.piG_norm k
    rw [e, mul_zero] at h1
    exact hg0 h1.symm
  have hwG : w ∈ Pr.vG k := by
    refine (Formalism.L2.Col.mem_divs hcp _).2 ?_
    show Valued.v (f ((X.conjO (Pr.piG k) : 𝓞 X.E) : X.E)) < 1
    rw [← hsig, ← hpi]
    exact G.sp_pi k v h
  have hwN : Ideal.absNorm w.asIdeal = Pr.g k := hPr.vG_norm k w hwG
  let w' : {w // w ∈ Pr.vGs} := ⟨w, mem_vGs hwG⟩
  have hcard : Nat.card (𝓞 X.F ⧸ v.asIdeal) = Pr.g k := by
    rw [← hN, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  obtain ⟨n, hn⟩ := exists_nat_sub_mem v.asIdeal hgp hcard y
  obtain ⟨b, hb⟩ := exists_nat_sub_mem v.asIdeal hgp hcard (c * y)
  refine ⟨b, hb, ?_⟩

  have hres : IsLocalRing.residue (v.adicCompletionIntegers X.F) z = (n : kv X.F v) := by
    have h1 : IsLocalRing.residue (v.adicCompletionIntegers X.F) (z - (n : v.adicCompletionIntegers X.F)) = 0 := by
      apply residue_eq_zero_of_val
      have e : ((z - (n : v.adicCompletionIntegers X.F) : v.adicCompletionIntegers X.F) : v.adicCompletion X.F) =
          algebraMap X.F (v.adicCompletion X.F) (((y - (n : 𝓞 X.F) : 𝓞 X.F)) : X.F) := by
        push_cast
        rw [hz]
      rw [e, Examples₂.adicCompl_val_algebraMap]
      exact (HeightOneSpectrum.valuation_lt_one_iff_mem (K := X.F) v _).2 hn
    rw [map_sub, sub_eq_zero, map_natCast] at h1
    exact h1
  rw [hres, hpsi k v h w' hunder n]
  have hfx : f xi * f (t : X.E) = 1 := by rw [← map_mul, ht, map_one]
  have hc' : Valued.v (f (algebraMap X.F X.E (c : X.F)) - f xi) < 1 := by
    rw [hf]; exact hc
  have hcv : Valued.v (f (algebraMap X.F X.E (c : X.F))) ≤ 1 := val_le_one v f (algebraMap (𝓞 X.F) (𝓞 X.E) c)
  have hxv : Valued.v (f xi) ≤ 1 := by
    have e : f xi = f (algebraMap X.F X.E (c : X.F)) - (f (algebraMap X.F X.E (c : X.F)) - f xi) := by ring
    rw [e]
    exact (Valuation.map_sub _ _ _).trans (max_le hcv hc'.le)
  have htw : t ∉ w.asIdeal := by
    intro hm
    have h1 : Valued.v (f (t : X.E)) < 1 := hm
    have h2 := congrArg Valued.v hfx
    rw [map_mul, map_one] at h2
    exact absurd h2 (ne_of_lt (lt_of_le_of_lt (by simpa using mul_le_mul' hxv (le_refl _)) h1))
  have hred : redP w xi = Ideal.Quotient.mk w.asIdeal (algebraMap (𝓞 X.F) (𝓞 X.E) c) := by
    refine redP_eq w (r := 1) (s := t) htw (by rw [map_one, mul_comm]; exact ht) ?_
    rw [← map_mul, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    show Valued.v (f ((t * algebraMap (𝓞 X.F) (𝓞 X.E) c - 1 : 𝓞 X.E) : X.E)) < 1
    have e : f ((t * algebraMap (𝓞 X.F) (𝓞 X.E) c - 1 : 𝓞 X.E) : X.E) =
        f (t : X.E) * (f (algebraMap X.F X.E (c : X.F)) - f xi) := by
      have e1 : ((t * algebraMap (𝓞 X.F) (𝓞 X.E) c - 1 : 𝓞 X.E) : X.E) = (t : X.E) * algebraMap X.F X.E (c : X.F) - 1 := by
        push_cast
        rfl
      rw [e1, map_sub, map_mul, map_one, mul_sub, mul_comm (f (t : X.E)) (f xi), hfx]
    rw [e, map_mul]
    exact lt_of_le_of_lt (by simpa using mul_le_mul' (val_le_one v f t) (le_refl _)) hc'
  have hcong : redP w xi * ((n : ℕ) : 𝓞 X.E ⧸ w.asIdeal) = (((b : ℤ)) : 𝓞 X.E ⧸ w.asIdeal) := by
    rw [hred]
    have h1 : c * (n : 𝓞 X.F) - (b : 𝓞 X.F) ∈ v.asIdeal := by
      have e : c * (n : 𝓞 X.F) - (b : 𝓞 X.F) = (c * y - (b : 𝓞 X.F)) - c * (y - (n : 𝓞 X.F)) := by ring
      rw [e]
      exact sub_mem hb (Ideal.mul_mem_left _ _ hn)
    have h2 := (hlow _).2 h1
    have h3 := (Ideal.Quotient.eq_zero_iff_mem (I := lowIdeal v f)).2 h2
    rw [map_sub, map_sub, map_mul, map_mul, map_natCast, map_natCast, map_natCast, map_natCast, sub_eq_zero] at h3
    simpa using h3
  have hfin := hW w' (n : 𝓞 X.E ⧸ w.asIdeal) (b : ℤ) hcong
  have hq : (qOf w'.1 : ℂ) = ((Pr.g k : ℕ) : ℂ) := by
    show ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) = _
    rw [hwN]
  rw [hq] at hfin
  exact hfin

end Generic

section Host

theorem exists_hostXi0_inverse_integer {R : Ranks} (H : Host R) : ∃ t : 𝓞 H.E, H.xi0 * (t : H.E) = 1 := by
  have hd : (H.d : H.E) ≠ 0 := Nat.cast_ne_zero.2 H.hyp.2.1.ne_zero
  have hsq := H.sqrtMinusD_sq
  have hb0 : H.sqrtMinusD ≠ 0 := by
    intro h0
    rw [h0] at hsq
    exact hd (by simpa using hsq.symm)
  have hN0 : ((Ideal.absNorm H.ccK : ℕ) : H.E) ≠ 0 :=
    Nat.cast_ne_zero.2 fun e => H.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 e)
  have hi : IsIntegral ℤ H.sqrtMinusD := by
    refine IsIntegral.of_pow (n := 2) two_pos ?_
    rw [hsq]
    simpa using (isIntegral_algebraMap (R := ℤ) (A := H.E) (x := -(H.d : ℤ)))
  have hiN : IsIntegral ℤ ((Ideal.absNorm H.ccK : ℕ) : H.E) := by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := H.E) (x := ((Ideal.absNorm H.ccK : ℕ) : ℤ)))
  refine ⟨⟨-(((Ideal.absNorm H.ccK : ℕ) : H.E) * H.sqrtMinusD), (hiN.mul hi).neg⟩, ?_⟩
  show H.xi0 * (-(((Ideal.absNorm H.ccK : ℕ) : H.E) * H.sqrtMinusD)) = 1
  rw [Host.xi0]
  field_simp

end Host

section Main
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem psiG_of_loc (hloc : ∀ (D : D7) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ), Formalism.L2.Theta.IsStdChar D ψ (-1) → ∀ (p : ℕ), p.Prime → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)), Ideal.absNorm v.asIdeal = p → (p : 𝓞 D.host.F) ∉ v.asIdeal ^ 2 → ∀ ε, Formalism.L2.Theta.IsPlaceIdem D v ε → ∀ (a : 𝓞 D.host.F) (b : ℤ), a - (b : 𝓞 D.host.F) ∈ v.asIdeal → ψ (ε * algebraMap D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ((a : D.host.F) / (p : D.host.F))) = Complex.exp (2 * Real.pi * Complex.I * b / (p : ℂ))) :
  ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (G : GLoc (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (I.rec7 l Z).host.g), I.IdG l Z G → ∀ ψ, Formalism.L2.Theta.IsStdChar (I.rec7 l Z) ψ (-1) → ∀ (k : Fin 2) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (h : ((I.rec7 l Z).host.g k : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal) (ε : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF (I.rec7 l Z).host.F), Formalism.L2.Theta.IsPlaceIdem (I.rec7 l Z) v ε → ∀ c y : 𝓞 (I.rec7 l Z).host.F, Valued.v (algebraMap (I.rec7 l Z).host.F (v.adicCompletion (I.rec7 l Z).host.F) (c : (I.rec7 l Z).host.F) - G.phi k v h (inclE (F := (I.rec7 l Z).host.F) (v.adicCompletion (I.rec7 l Z).host.F) (I.rec7 l Z).host.xi0)) < 1 → ∀ z : v.adicCompletionIntegers (I.rec7 l Z).host.F, (z : v.adicCompletion (I.rec7 l Z).host.F) = algebraMap (I.rec7 l Z).host.F (v.adicCompletion (I.rec7 l Z).host.F) (y : (I.rec7 l Z).host.F) → G.psi0 k v h (IsLocalRing.residue _ z) = ψ (ε * algebraMap (I.rec7 l Z).host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF (I.rec7 l Z).host.F) ((c : (I.rec7 l Z).host.F) * (y : (I.rec7 l Z).host.F) / ((I.rec7 l Z).host.g k : (I.rec7 l Z).host.F))) := by
  intro B X I hI hP l Z G hG ψ hψ k v h ε hε c y hc z hz
  have hs := (I.rec7 l Z).nd.g_split k
  have hgp := l.pr.g_prime k
  obtain ⟨hN, hsq⟩ := absNorm_and_unram hgp hs v h
  obtain ⟨t, ht⟩ := exists_hostXi0_inverse_integer B.host
  obtain ⟨b, hb, e⟩ := columnCharacter_reduction_eq_exp (X := B.fields) (Pr := B.primes X) I.Ch l.pr B.sp.cm B.embLL B.host.xi0 hI.weil t ht G hG.piG
    (fun x => rfl) hG.psi k v h hN c y hc z hz
  refine e.trans ?_
  have := hloc (I.rec7 l Z) ψ hψ _ hgp v hN hsq ε hε (c * y) (b : ℤ) (by rw [Int.cast_natCast]; exact hb)
  exact this.symm

end Main

end GlobalTheory.Mem.TypePrimes.Red
