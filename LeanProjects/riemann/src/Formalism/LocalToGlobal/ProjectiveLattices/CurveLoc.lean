import Formalism.LocalToGlobal.ProjectiveLattices.CurveComp
import Formalism.LocalToGlobal.ProjectiveLattices.CurveCountA

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor TensorProduct

namespace CurveLoc

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO))
  (N : ℕ) {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL)

def fr0 (k : ℕ) (F : X.Forms) (hF : emb X la N F ∈ Vw X la N (addL (wt0 D j) wL k)) : ↥(Frac0 X la w) :=
  ⟨frac X la w k (emb X la N F),
    (Algebra.subset_adjoin (frac_mem_Hfr X la w hF) : frac X la w k (emb X la N F) ∈ Frac0 X la w)⟩

def constF : B.KO →+* ↥(Frac0 X la w) :=
  (algebraMap (Kp X la N) ↥(Frac0 X la w)).comp ((algebraMap (X.Kl la) (Kp X la N)).comp (algebraMap B.KO (X.Kl la)))

theorem emb_inc_mem (i : Fin N) : emb X la N (X.inc wL (w i)) ∈ Vw X la N (addL (wt0 D j) wL 1) := by
  rw [add_zero_weight_one_eq]
  exact emb_mem_Vw X la N wL (w i)

def xw (i : Fin N) : ↥(Frac0 X la w) := fr0 X la N w 1 (X.inc wL (w i)) (emb_inc_mem X la N w i)

def polX (Pw : MvPolynomial (Fin N) B.KO) : ↥(Frac0 X la w) := MvPolynomial.eval₂ (constF X la N w) (xw X la N w) Pw

def secOf (g : Fin N → B.Cusp j wL) : Rp X la N :=
  ∑ k, (algebraMap (Op X la N) (Kp X la N) (Tv X la N (0, k))) • emb X la N (X.inc wL (g k))

theorem secOf_self : secOf X la N w = Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0 := rfl

theorem secOf_mem (g : Fin N → B.Cusp j wL) : secOf X la N g ∈ Vw X la N wL :=
  Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (emb_mem_Vw X la N wL (g k))

section One

variable {Ω : Type} [CommRing Ω] [Algebra B.KO Ω] (gF : X.Forms →ₐ[B.KO] Ω)

def psiZ : Ω →+* RZs X la N Ω gF w :=
  (algebraMap (RZ X la N Ω) (RZs X la N Ω gF w)).comp
    ((Algebra.TensorProduct.includeRight : (X.Kl la ⊗[B.KO] Ω) →ₐ[X.Kl la] RZ X la N Ω).toRingHom.comp
      (Algebra.TensorProduct.includeRight : Ω →ₐ[B.KO] X.Kl la ⊗[B.KO] Ω).toRingHom)

theorem psiZ_apply (ω : Ω) : psiZ X la N w gF ω =
    algebraMap (RZ X la N Ω) (RZs X la N Ω gF w) ((1 : Kp X la N) ⊗ₜ[X.Kl la] ((1 : X.Kl la) ⊗ₜ[B.KO] ω)) := rfl

theorem alg_rzMap_emb (F : X.Forms) :
    algebraMap (RZ X la N Ω) (RZs X la N Ω gF w) (rzMap X la N Ω gF (emb X la N F)) = psiZ X la N w gF (gF F) := by
  rw [rzMap_emb]
  rfl

def invS : RZs X la N Ω gF w := lwZ X la N Ω gF w (w0inv X la w)

theorem weight_zero_section_mul_inv :
    algebraMap (RZ X la N Ω) (RZs X la N Ω gF w) (rzMap X la N Ω gF (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0)) * invS X la N w gF = 1 := by
  have h := congrArg (lwZ X la N Ω gF w) (section_mul_inverse_eq_one X la w)
  rw [map_mul, lwZ_alg, map_one] at h
  exact h

theorem phiZ_of_eq (x : ↥(Frac0 X la w)) (k : ℕ) (g : Rp X la N) (hx : (x : Lw X la w) = frac X la w k g) :
    phiZ X la N Ω gF w x =
      algebraMap (RZ X la N Ω) (RZs X la N Ω gF w) (rzMap X la N Ω gF g) * invS X la N w gF ^ k := by
  rw [phiZ_apply, hx, frac_apply, map_mul, map_pow, lwZ_alg]
  rfl

theorem phiZ_fraction_base (k : ℕ) (F : X.Forms) (hF : emb X la N F ∈ Vw X la N (addL (wt0 D j) wL k)) :
    phiZ X la N Ω gF w (fr0 X la N w k F hF) = psiZ X la N w gF (gF F) * invS X la N w gF ^ k := by
  rw [phiZ_of_eq X la N w gF _ k _ rfl, alg_rzMap_emb]

theorem phiZ_const (c : B.KO) :
    phiZ X la N Ω gF w (constF X la N w c) = psiZ X la N w gF (algebraMap B.KO Ω c) := by
  rw [constF, RingHom.comp_apply, (phiZ X la N Ω gF w).commutes, psiZ_apply,
    IsScalarTower.algebraMap_apply (Kp X la N) (RZ X la N Ω) (RZs X la N Ω gF w)]
  congr 1
  show (algebraMap (X.Kl la) (Kp X la N) (algebraMap B.KO (X.Kl la) c)) ⊗ₜ[X.Kl la] (1 : X.Kl la ⊗[B.KO] Ω) = _
  rw [Algebra.algebraMap_eq_smul_one (algebraMap B.KO (X.Kl la) c), TensorProduct.smul_tmul,
    Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
    Algebra.algebraMap_eq_smul_one c, TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one]

theorem phiZ_xw (i : Fin N) :
    phiZ X la N Ω gF w (xw X la N w i) = psiZ X la N w gF (gF (X.inc wL (w i))) * invS X la N w gF := by
  rw [xw, phiZ_fraction_base, pow_one]

theorem phiZ_polX {Pw : MvPolynomial (Fin N) B.KO} {k : ℕ} (hPw : Pw.IsHomogeneous k) :
    phiZ X la N Ω gF w (polX X la N w Pw) =
      invS X la N w gF ^ k * psiZ X la N w gF (MvPolynomial.aeval (fun i => gF (X.inc wL (w i))) Pw) := by
  have h := MvPolynomial.eval₂_comp_left (phiZ X la N Ω gF w).toRingHom (constF X la N w) (xw X la N w) Pw
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h
  have hc : (phiZ X la N Ω gF w : ↥(Frac0 X la w) →+* RZs X la N Ω gF w).comp (constF X la N w) =
      (psiZ X la N w gF).comp (algebraMap B.KO Ω) := RingHom.ext fun c => phiZ_const X la N w gF c
  have hx : (⇑(phiZ X la N Ω gF w) ∘ xw X la N w) =
      fun i => invS X la N w gF * psiZ X la N w gF (gF (X.inc wL (w i))) := by
    funext i
    rw [Function.comp_apply, phiZ_xw, mul_comm]
  rw [polX, h, hc, hx, CurveCount.eval₂_mul_homog _ _ _ hPw, MvPolynomial.map_aeval]
  rfl

theorem rzMap_secOf (g g' : Fin N → B.Cusp j wL) (h : ∀ k, gF (X.inc wL (g k)) = gF (X.inc wL (g' k))) :
    rzMap X la N Ω gF (secOf X la N g) = rzMap X la N Ω gF (secOf X la N g') := by
  simp only [secOf, map_sum, map_smul, rzMap_emb, h]

theorem rzMap_secOf_zero (g : Fin N → B.Cusp j wL) (h : ∀ k, gF (X.inc wL (g k)) = 0) :
    rzMap X la N Ω gF (secOf X la N g) = 0 := by
  simp only [secOf, map_sum, map_smul, rzMap_emb, h, TensorProduct.tmul_zero, smul_zero, Finset.sum_const_zero]

end One

section Fam

variable {ι : Type} (Ω : ι → Type) [∀ Z, CommRing (Ω Z)] [∀ Z, Algebra B.KO (Ω Z)] (gF : ∀ Z, X.Forms →ₐ[B.KO] Ω Z)

theorem one_of_split
    (hsplit : ∀ (Z : ι) (k : Fin N), ∃ g : B.Cusp j wL, gF Z (X.inc wL g) = gF Z (X.inc wL (w k)) ∧
      ∀ Z', Z' ≠ Z → gF Z' (X.inc wL g) = 0)
    (𝔮 : Ideal ↥(Frac0 X la w)) (h𝔮 : 𝔮.IsPrime) (Z Z' : ι)
    (hZ : RingHom.ker (phiZ X la N (Ω Z) (gF Z) w) ≤ 𝔮) (hZ' : RingHom.ker (phiZ X la N (Ω Z') (gF Z') w) ≤ 𝔮) :
    Z = Z' := by
  by_contra hne
  choose g hg using hsplit Z
  have hmem : frac X la w 1 (secOf X la N g) ∈ Frac0 X la w :=
    Algebra.subset_adjoin (frac_mem_Hfr X la w (by rw [add_zero_weight_one_eq]; exact secOf_mem X la N g))
  have h1 : (⟨_, hmem⟩ : ↥(Frac0 X la w)) - 1 ∈ 𝔮 := hZ (by
    rw [RingHom.mem_ker, map_sub, map_one, phiZ_of_eq X la N w (gF Z) _ 1 _ rfl,
      rzMap_secOf X la N (gF Z) g w (fun k => (hg k).1), secOf_self, pow_one, weight_zero_section_mul_inv, sub_self])
  have h2 : (⟨_, hmem⟩ : ↥(Frac0 X la w)) ∈ 𝔮 := hZ' (by
    rw [RingHom.mem_ker, phiZ_of_eq X la N w (gF Z') _ 1 _ rfl, rzMap_secOf_zero X la N (gF Z') g (fun k => (hg k).2 Z' (Ne.symm hne)),
      map_zero, zero_mul])
  have h3 := 𝔮.sub_mem h2 h1
  rw [sub_sub_cancel] at h3
  exact h𝔮.ne_top ((Ideal.eq_top_iff_one _).2 h3)

end Fam

section Loc

variable {Ω : Type} [Field Ω] [Algebra B.KO Ω] (gF : X.Forms →ₐ[B.KO] Ω)

def CountQAt : Prop :=
  ∀ 𝔮 : Ideal ↥(Frac0 X la w), 𝔮.IsPrime → Jid X la w ≤ 𝔮 → RingHom.ker (phiZ X la N Ω gF w) ≤ 𝔮 →
    ∀ (Pw : MvPolynomial (Fin N) B.KO) {k : ℕ}, Pw.IsHomogeneous k →
      MvPolynomial.aeval (fun i => gF (X.inc wL (w i))) Pw ≠ 0 → polX X la N w Pw ∉ 𝔮

def BirAt : Prop :=
  ∀ a : Ω, ∃ (k : ℕ) (g : B.Cusp j (wsmul k wL)) (Pw : MvPolynomial (Fin N) B.KO), Pw.IsHomogeneous k ∧
    MvPolynomial.aeval (fun i => gF (X.inc wL (w i))) Pw ≠ 0 ∧
    a * MvPolynomial.aeval (fun i => gF (X.inc wL (w i))) Pw = gF (X.inc (wsmul k wL) g)

def Den (p : ↥(Frac0 X la w)) : Prop :=
  ∀ 𝔮 : Ideal ↥(Frac0 X la w), 𝔮.IsPrime → Jid X la w ≤ 𝔮 → RingHom.ker (phiZ X la N Ω gF w) ≤ 𝔮 → p ∉ 𝔮

def Good (r : RZs X la N Ω gF w) : Prop :=
  ∃ a p : ↥(Frac0 X la w), Den X la N w gF p ∧ phiZ X la N Ω gF w p * r = phiZ X la N Ω gF w a

theorem den_one : Den X la N w gF 1 := fun _ h𝔮 _ _ h => h𝔮.ne_top ((Ideal.eq_top_iff_one _).2 h)

theorem den_mul {p p' : ↥(Frac0 X la w)} (hp : Den X la N w gF p) (hp' : Den X la N w gF p') :
    Den X la N w gF (p * p') := fun 𝔮 h𝔮 hJ hK h =>
  (h𝔮.mem_or_mem h).elim (hp 𝔮 h𝔮 hJ hK) (hp' 𝔮 h𝔮 hJ hK)

theorem good_phi (f : ↥(Frac0 X la w)) : Good X la N w gF (phiZ X la N Ω gF w f) :=
  ⟨f, 1, den_one X la N w gF, by rw [map_one, one_mul]⟩

theorem good_add {r s : RZs X la N Ω gF w} (hr : Good X la N w gF r) (hs : Good X la N w gF s) :
    Good X la N w gF (r + s) := by
  obtain ⟨a, p, hp, he⟩ := hr
  obtain ⟨a', p', hp', he'⟩ := hs
  refine ⟨p' * a + p * a', p * p', den_mul X la N w gF hp hp', ?_⟩
  rw [map_mul, map_add, map_mul, map_mul, ← he, ← he']
  ring

theorem good_mul {r s : RZs X la N Ω gF w} (hr : Good X la N w gF r) (hs : Good X la N w gF s) :
    Good X la N w gF (r * s) := by
  obtain ⟨a, p, hp, he⟩ := hr
  obtain ⟨a', p', hp', he'⟩ := hs
  refine ⟨a * a', p * p', den_mul X la N w gF hp hp', ?_⟩
  rw [map_mul, map_mul, ← he, ← he']
  ring

theorem good_pow {r : RZs X la N Ω gF w} (hr : Good X la N w gF r) (n : ℕ) : Good X la N w gF (r ^ n) := by
  induction n with
  | zero => rw [pow_zero]; simpa using good_phi X la N w gF 1
  | succ n ih => rw [pow_succ]; exact good_mul X la N w gF ih hr

theorem good_smul (c : Kp X la N) {r : RZs X la N Ω gF w} (hr : Good X la N w gF r) : Good X la N w gF (c • r) := by
  rw [Algebra.smul_def, ← (phiZ X la N Ω gF w).commutes c]
  exact good_mul X la N w gF (good_phi X la N w gF _) hr

theorem good_psi (hB : BirAt X N w gF) (hC : CountQAt X la N w gF) (ω : Ω) :
    Good X la N w gF (psiZ X la N w gF ω) := by
  obtain ⟨k, g, Pw, hPw, hne, he⟩ := hB ω
  have hG : emb X la N (X.inc (wsmul k wL) g) ∈ Vw X la N (addL (wt0 D j) wL k) := by
    rw [addL, zero_weight_add]
    exact emb_mem_Vw X la N _ g
  refine ⟨fr0 X la N w k _ hG, polX X la N w Pw, fun 𝔮 h𝔮 hJ hK => hC 𝔮 h𝔮 hJ hK Pw hPw hne, ?_⟩
  rw [phiZ_polX X la N w gF hPw, phiZ_fraction_base, ← he, map_mul]
  ring

theorem good_invS (hB : BirAt X N w gF) (hC : CountQAt X la N w gF) (k0 : Fin N)
    (hk0 : gF (X.inc wL (w k0)) ≠ 0) : Good X la N w gF (invS X la N w gF) := by
  have h1 : emb X la N (X.inc wL (w k0)) ∈ Vw X la N (addL (wt0 D j) wL 1) := by
    rw [add_zero_weight_one_eq]; exact emb_mem_Vw X la N wL (w k0)
  have e : invS X la N w gF =
      phiZ X la N Ω gF w (fr0 X la N w 1 _ h1) * psiZ X la N w gF (gF (X.inc wL (w k0)))⁻¹ := by
    rw [phiZ_fraction_base, pow_one, mul_right_comm, ← map_mul, mul_inv_cancel₀ hk0, map_one, one_mul]
  rw [e]
  exact good_mul X la N w gF (good_phi X la N w gF _) (good_psi X la N w gF hB hC _)

theorem tmul_eq (κ : Kp X la N) (l : X.Kl la) (ω : Ω) :
    (κ ⊗ₜ[X.Kl la] (l ⊗ₜ[B.KO] ω) : RZ X la N Ω) =
      (κ * algebraMap (X.Kl la) (Kp X la N) l) • ((1 : Kp X la N) ⊗ₜ[X.Kl la] ((1 : X.Kl la) ⊗ₜ[B.KO] ω)) := by
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have h : (l ⊗ₜ[B.KO] ω : X.Kl la ⊗[B.KO] Ω) = l • ((1 : X.Kl la) ⊗ₜ[B.KO] ω) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_comm]

theorem loc_of_bir (hB : BirAt X N w gF) (hC : CountQAt X la N w gF) (r : RZs X la N Ω gF w) :
    ∃ a p : ↥(Frac0 X la w), (∀ 𝔮 : Ideal ↥(Frac0 X la w), 𝔮.IsPrime → Jid X la w ≤ 𝔮 →
      RingHom.ker (phiZ X la N Ω gF w) ≤ 𝔮 → p ∉ 𝔮) ∧ phiZ X la N Ω gF w p * r = phiZ X la N Ω gF w a := by
  by_cases hk : ∃ k, gF (X.inc wL (w k)) ≠ 0
  · obtain ⟨k0, hk0⟩ := hk
    have hRZ : ∀ x : RZ X la N Ω, Good X la N w gF (algebraMap (RZ X la N Ω) (RZs X la N Ω gF w) x) := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => rw [map_zero]; simpa using good_phi X la N w gF 0
      | tmul κ v =>
        induction v using TensorProduct.induction_on with
        | zero => rw [TensorProduct.tmul_zero, map_zero]; simpa using good_phi X la N w gF 0
        | tmul l ω =>
          rw [tmul_eq, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, ← Algebra.smul_def]
          exact good_smul X la N w gF _ (good_psi X la N w gF hB hC ω)
        | add v₁ v₂ h₁ h₂ => rw [TensorProduct.tmul_add, map_add]; exact good_add X la N w gF h₁ h₂
      | add x y hx hy => rw [map_add]; exact good_add X la N w gF hx hy
    obtain ⟨⟨x, y⟩, hr⟩ :=
      IsLocalization.mk'_surjective (Submonoid.powers (rzMap X la N Ω gF (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0))) r
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp y.2
    have e : r = algebraMap (RZ X la N Ω) (RZs X la N Ω gF w) x * invS X la N w gF ^ n := by
      rw [← hr]
      show IsLocalization.mk' (RZs X la N Ω gF w) x y = _
      rw [IsLocalization.mk'_eq_iff_eq_mul, ← hn, map_pow, mul_assoc, ← mul_pow, mul_comm (invS X la N w gF),
        weight_zero_section_mul_inv, one_pow, mul_one]
    rw [e]
    obtain ⟨a, p, hp, he⟩ :=
      good_mul X la N w gF (hRZ x) (good_pow X la N w gF (good_invS X la N w gF hB hC k0 hk0) n)
    exact ⟨a, p, hp, he⟩
  · push Not at hk
    have hz : rzMap X la N Ω gF (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0) = 0 := rzMap_secOf_zero X la N gF w hk
    have h2 : algebraMap (RZ X la N Ω) (RZs X la N Ω gF w) (rzMap X la N Ω gF (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0)) = 0 :=
      (congrArg (algebraMap (RZ X la N Ω) (RZs X la N Ω gF w)) hz).trans (map_zero _)
    have h0 : (1 : RZs X la N Ω gF w) = 0 := by
      rw [← weight_zero_section_mul_inv X la N w gF, h2, zero_mul]
    have := subsingleton_of_zero_eq_one h0.symm
    exact ⟨0, 1, den_one X la N w gF, Subsingleton.elim _ _⟩

end Loc

end CurveLoc

end Formalism.L2.Pj
