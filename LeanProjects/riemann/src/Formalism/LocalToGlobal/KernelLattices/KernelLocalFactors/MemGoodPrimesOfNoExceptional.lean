import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ColInst
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ColInst
import Formalism.LocalToGlobal.Columns.ChainInstY
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.KerEquivFr
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.KerEquivGen
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.KerEquivStmt

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

section Copy

variable {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S)

theorem mem_vGs_of_QE_empty (hQ : QE sel (mu : Chr X.F X.E X.K) = ∅) (P : rowSG Pr sel mu) : P.1 ∈ Pr.vGs := by
  have h := P.2
  simp only [rowSG, uSG, hQ, Finset.union_empty] at h
  exact h

theorem levQFam_chr_eq_one_of_QE_empty (hQ : QE sel (mu : Chr X.F X.E X.K) = ∅) {n : ℕ} (Θ : LevQFam X.E X.K n (QE sel (mu : Chr X.F X.E X.K))) (c : ↥Θ.grp) :
    Θ.chr c = 1 := by
  have hE : IsEmpty ↥(QE sel (mu : Chr X.F X.E X.K)) := by rw [hQ]; infer_instance
  have key : ∀ c' : ↥(Subgroup.pi Set.univ fun P => (Θ P).H),
      piChar (fun P => (Θ P).H) (fun P => (Θ P).lam) c' = 1 := by
    intro c'
    rw [piChar, MonoidHom.finset_prod_apply]
    exact Fintype.prod_empty _
  exact key c

open Classical in
theorem prod_rowSG_eq_prod_vGs_of_QE_empty (hQ : QE sel (mu : Chr X.F X.E X.K) = ∅) {M : Type} [CommMonoid M] (f : {w // w ∈ Pr.vGs} → M) :
    ∏ P : rowSG Pr sel mu, f ⟨P.1, mem_vGs_of_QE_empty sel mu hQ P⟩ = ∏ w : {w // w ∈ Pr.vGs}, f w := by
  exact Fintype.prod_equiv (Equiv.subtypeEquivRight (fun x => by
    show x ∈ Pr.vGs ∪ QE sel (mu : Chr X.F X.E X.K) ↔ _
    rw [hQ, Finset.union_empty])) _ _ (fun _ => rfl)

theorem prod_mul_eq_of_forall_cross_mul_eq {ι K : Type} [Fintype ι] [CommRing K] (a b y z : ι → K) (φ : K) (h : ∀ i, a i * z i = b i * y i) :
    (∏ i, a i) * (φ * ∏ i, z i) = (∏ i, b i) * (φ * ∏ i, y i) := by
  have h2 : ∏ i, (a i * z i) = ∏ i, (b i * y i) := Finset.prod_congr rfl (fun i _ => h i)
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib] at h2
  calc (∏ i, a i) * (φ * ∏ i, z i) = φ * ((∏ i, a i) * ∏ i, z i) := by ring
    _ = φ * ((∏ i, b i) * ∏ i, y i) := by rw [h2]
    _ = (∏ i, b i) * (φ * ∏ i, y i) := by ring

theorem piChar_apply_coe' {K : Type} [Field K] {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)] (H : ∀ i, Subgroup (G i))
    (lam : ∀ i, ↥(H i) →* Kˣ) (x : ↥(Subgroup.pi Set.univ H)) :
    ((piChar H lam x : Kˣ) : K) = ∏ i, ((lam i ⟨x.1 i, x.2 i (Set.mem_univ i)⟩ : Kˣ) : K) := by
  simp only [piChar, MonoidHom.finset_prod_apply, Units.coe_prod, MonoidHom.comp_apply]
  rfl

theorem levFam_chr_apply_coe {E K : Type} [Field E] [NumberField E] [Field K] {n : ℕ} {SG : Finset (HeightOneSpectrum (𝓞 E))}
    (Λ : LevFam E K n SG) (x : ↥Λ.grp) :
    ((Λ.chr x : Kˣ) : K) = ∏ w, (((Λ w).lam ⟨x.1 w, x.2 w (Set.mem_univ w)⟩ : Kˣ) : K) := by
  show ((piChar (fun w => (Λ w).H) (fun w => (Λ w).lam) x : Kˣ) : K) = _
  exact piChar_apply_coe' _ _ x

end Copy

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem funLeft_extUH2 {N n : ℕ} (hN : N = n + 1) (f : Fin n → Fin N) (hf : ∀ i, (f i).1 = i.1) (γ : UF E n) (v : Sp E N) :
    LinearMap.funLeft E E f ((extUH hN γ).1 v) = γ.1 (LinearMap.funLeft E E f v) := by
  subst hN
  have hf' : f = Fin.castSucc := funext fun i => Fin.ext (hf i)
  subst hf'
  exact initL_extE γ.1 v

theorem atNL_extUH2 {N n : ℕ} (hN : N = n + 1) (γ : UF E n) (v : Sp E N) :
    atNL E N n ((extUH hN γ).1 v) = atNL E N n v := by
  subst hN
  have h : n < n + 1 := Nat.lt_succ_self n
  simp only [atNL, dif_pos h, LinearMap.proj_apply]
  exact extE_last γ.1 v

theorem intAt_natCast_kernel_local_factors (P : HeightOneSpectrum (𝓞 E)) (k : ℕ) : IntAt P (k : E) := by
  simpa using IntAt.coe P (k : 𝓞 E)

theorem intAt_neg_kernel_local_factors {P : HeightOneSpectrum (𝓞 E)} {a : E} (h : IntAt P a) : IntAt P (-a) := by
  obtain ⟨r, s, hs, e⟩ := h
  exact ⟨-r, s, hs, by rw [mul_neg, e, map_neg]⟩

theorem intAt_linear_form_on_std {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (η : Sp E n →ₗ[E] E) (hη : ∀ i : Fin n, IntAt P (η (Pi.single i 1)))
    {v : Sp E n} (hv : v ∈ stdAt E n P) : IntAt P (η v) := by
  rw [ciMem_stdAt] at hv
  have hv' : v = ∑ i, v i • (Pi.single i 1 : Sp E n) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hv', map_sum]
  refine Finset.sum_induction _ (IntAt P) (fun a b ha hb => IntAt.add ha hb) (by simpa using IntAt.coe P 0) ?_
  intro i _
  rw [map_smul, smul_eq_mul]
  exact IntAt.mul (hv i) (hη i)

end Gen

section FtY

variable {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

theorem ftY_move2 (hcst : cst.Ok) (w : rowSG Pr sel mu) (hw : w.1 ∈ Pr.vGs) {n : ℕ} (κ : ↥(GLint X.E n w.1))
    (η : Sp X.E n →ₗ[X.E] X.E) (y y₁ : Sp X.E n) (hδ : κ.1 y₁ - y ∈ stdAt X.E n w.1)
    (hq : ((qOf w.1 : ℕ) : X.E) • y ∈ stdAt X.E n w.1) :
    ftY sel mu cst w (η ∘ₗ κ.1.toLinearMap) y₁ = ftY sel mu cst w η y := by
  have hκ : ∀ x, κ.1 x ∈ stdAt X.E n w.1 ↔ x ∈ stdAt X.E n w.1 := κ.2
  have hsg : ∀ i : Fin n, (Pi.single i 1 : Sp X.E n) ∈ stdAt X.E n w.1 := by
    intro i
    rw [ciMem_stdAt]
    intro j
    rw [Pi.single_apply]
    split_ifs
    · simpa using intAt_natCast_kernel_local_factors w.1 1
    · simpa using intAt_natCast_kernel_local_factors w.1 0
  have hcond : (∀ i : Fin n, IntAt w.1 ((η ∘ₗ κ.1.toLinearMap) (Pi.single i 1))) ↔
      ∀ i : Fin n, IntAt w.1 (η (Pi.single i 1)) := by
    constructor
    · intro h i
      have hs : κ.1.symm (Pi.single i 1) ∈ stdAt X.E n w.1 := by
        rw [← hκ, LinearEquiv.apply_symm_apply]
        exact hsg i
      have h' := intAt_linear_form_on_std w.1 (η ∘ₗ κ.1.toLinearMap) h hs
      simpa using h'
    · intro h i
      have hs : κ.1 (Pi.single i 1) ∈ stdAt X.E n w.1 := (hκ _).2 (hsg i)
      simpa using intAt_linear_form_on_std w.1 η h hs
  unfold ftY
  rw [if_pos hw, if_pos hw]
  by_cases hη : ∀ i : Fin n, IntAt w.1 (η (Pi.single i 1))
  · rw [if_pos (hcond.2 hη), if_pos hη]
    have hd : IntAt w.1 (η (κ.1 y₁ - y)) := intAt_linear_form_on_std w.1 η hη hδ
    have e0 : (η ∘ₗ κ.1.toLinearMap) y₁ = η y + η (κ.1 y₁ - y) := by
      rw [map_sub]
      simp
    have hqη : IntAt w.1 ((Col.qOf w.1 : X.E) * η y) := by
      have h' := intAt_linear_form_on_std w.1 η hη hq
      rwa [map_smul, smul_eq_mul] at h'
    have hD := hcst.D_pos w
    have hqD : ∀ x : X.E, IntAt w.1 ((Col.qOf w.1 : X.E) * x) → IntAt w.1 ((Col.qOf w.1 : X.E) ^ cst.D w * x) := by
      intro x hx
      have e : (Col.qOf w.1 : X.E) ^ cst.D w * x = ((Col.qOf w.1 ^ (cst.D w - 1) : ℕ) : X.E) * ((Col.qOf w.1 : X.E) * x) := by
        push_cast
        rw [← mul_assoc, ← pow_succ, Nat.sub_add_cancel hD]
      rw [e]
      exact IntAt.mul (intAt_natCast_kernel_local_factors _ _) hx
    have hζe : IntAt w.1 ((epsSg : X.E) * η (κ.1 y₁ - y)) := by
      have h' := intAt_neg_kernel_local_factors hd
      simpa [epsSg] using h'
    have hA : IntAt w.1 ((Col.qOf w.1 : X.E) ^ cst.D w * ((epsSg : X.E) * η y)) := by
      apply hqD
      have h' := intAt_neg_kernel_local_factors hqη
      simpa [epsSg] using h'
    have hB : IntAt w.1 ((Col.qOf w.1 : X.E) ^ cst.D w * ((epsSg : X.E) * η (κ.1 y₁ - y))) :=
      hqD _ (IntAt.mul (intAt_natCast_kernel_local_factors _ _) hζe)
    rw [e0, mul_add, hcst.psi_add w _ _ hA hB, hcst.psi_int w _ hζe, mul_one]
  · rw [if_neg (fun h => hη (hcond.1 h)), if_neg hη]

open Classical in

theorem ybSet_props2 {n : ℕ} {N : Submodule (𝓞 X.E) (Sp X.E n)} {Y : Set (Sp X.E n)} (hY : Y ∈ ybSet sel mu cst N)
    (w : rowSG Pr sel mu) (hw : w.1 ∈ Pr.vGs) :
    Y.Nonempty ∧ (∀ a ∈ Y, ∀ a' ∈ Y, a - a' ∈ localization₂ w.1.asIdeal N) ∧
      ∀ a ∈ Y, ((qOf w.1 : ℕ) : X.E) • a ∈ localization₂ w.1.asIdeal N := by
  obtain ⟨y, hy, rfl⟩ := hY
  have key : ∀ (e : rowSG Pr sel mu → ℤ) (x : Sp X.E n), x ∈ locLat (rowSG Pr sel mu) N e →
      ((Col.qOf w.1 : X.E) ^ e w)⁻¹ • x ∈ localization₂ w.1.asIdeal N := by
    intro e x hx
    exact Submodule.mem_comap.1 ((Submodule.mem_iInf _).1 hx w)
  have hD : ∀ a ∈ {z | z - y ∈ locLat (rowSG Pr sel mu) N (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ))},
      a - y ∈ localization₂ w.1.asIdeal N := by
    intro a ha
    have h1 := key _ _ ha
    simp only [if_pos hw, zpow_zero, inv_one, one_smul] at h1
    exact h1
  have hyw : ((Col.qOf w.1 : ℕ) : X.E) • y ∈ localization₂ w.1.asIdeal N := by
    have h1 := key _ _ hy
    simp only [if_pos hw, zpow_neg, zpow_one, inv_inv] at h1
    exact h1
  refine ⟨⟨y, ?_⟩, ?_, ?_⟩
  · show y - y ∈ locLat (rowSG Pr sel mu) N (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ))
    rw [sub_self]
    exact zero_mem _
  · intro a ha a' ha'
    have e : a - a' = (a - y) - (a' - y) := by abel
    rw [e]
    exact sub_mem (hD a ha) (hD a' ha')
  · intro a ha
    have e2 : ((Col.qOf w.1 : ℕ) : X.E) • a = ((Col.qOf w.1 : ℕ) : X.E) • (a - y) + ((Col.qOf w.1 : ℕ) : X.E) • y := by
      rw [← smul_add, sub_add_cancel]
    rw [e2]
    refine add_mem ?_ hyw
    rw [Nat.cast_smul_eq_nsmul]
    exact nsmul_mem (hD a ha) _

theorem representative_mem {n : ℕ} {Y : Set (Sp X.E n)} (h : Y.Nonempty) : repY Y ∈ Y := Classical.epsilon_spec h

end FtY

section Inv2

theorem mem_asIdeal_of_mem_divs {A : Type} [CommRing A] [IsDedekindDomain A] {a : A} {P : HeightOneSpectrum A} (h : P ∈ divs a) :
    a ∈ P.asIdeal := by
  unfold divs at h
  split_ifs at h with hf
  · simpa using h
  · simp at h

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem tilde_lattice_restrict_mem {N n : ℕ} (hN : N = n + 1) {ST SG : Finset (HeightOneSpectrum (𝓞 E))} (pi : 𝓞 E) (d : DecoSet E n ∅ SG)
    (hT : ∀ P : ST, cO E pi ∉ P.1.asIdeal) (hG : ∀ w : SG, pi ∉ w.1.asIdeal)
    (f : Fin n → Fin N) (hf : ∀ i, (f i).1 = i.1) (Q : HeightOneSpectrum (𝓞 E)) (v : Sp E N)
    (hv : v ∈ localization₂ Q.asIdeal (DecoSet.tilH (ST := ST) hN pi d).1.N) :
    LinearMap.funLeft E E f v ∈ localization₂ Q.asIdeal d.1.N ∧ IntAt Q (atNL E N n v) := by
  subst hN
  have hf' : f = Fin.castSucc := funext fun i => Fin.ext (hf i)
  subst hf'
  have hv' : v ∈ localization₂ Q.asIdeal (tilN d.1.N) := by
    have e : (DecoSet.til (ST := ST) pi d).1 = d.1.til (ST := ST) pi := by
      unfold DecoSet.til
      rw [dif_pos (d.2.til hT hG)]
    have hv2 : v ∈ localization₂ Q.asIdeal (DecoSet.til (ST := ST) pi d).1.N := hv
    rw [e] at hv2
    exact hv2
  obtain ⟨s, hs, hsv⟩ := hv'
  rw [tilN, Submodule.mem_sup] at hsv
  obtain ⟨a, ha, b, hb, hab⟩ := hsv
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 ha
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hb
  have h1 : LinearMap.funLeft E E Fin.castSucc (s • v) = x := by
    rw [← hab]
    funext i
    simp [LinearMap.funLeft_apply, incl, eLast, Pi.single_apply, Fin.castSucc_ne_last]
  have h2 : (s • v) (Fin.last n) = algebraMap (𝓞 E) E c := by
    rw [← hab]
    simp [incl, eLast, Algebra.smul_def]
  constructor
  · refine ⟨s, hs, ?_⟩
    rw [← LinearMap.map_smul_of_tower, h1]
    exact hx
  · have h3 : atNL E (n + 1) n v = v (Fin.last n) := by
      simp only [atNL, dif_pos (Nat.lt_succ_self n), LinearMap.proj_apply]
      rfl
    rw [h3]
    rw [Pi.smul_apply, Algebra.smul_def] at h2
    exact ⟨c, s, hs, h2⟩

theorem fourierTwist_add_integral {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
    (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (hcst : cst.Ok) (w : rowSG Pr sel mu) (hw : w.1 ∈ Pr.vGs) {n : ℕ}
    (η ζ : Sp X.E n →ₗ[X.E] X.E) (y : Sp X.E n) (hζ : ∀ i : Fin n, IntAt w.1 (ζ (Pi.single i 1))) (hζy : IntAt w.1 (ζ y))
    (hq : ((qOf w.1 : ℕ) : X.E) • y ∈ stdAt X.E n w.1) :
    ftY sel mu cst w (η + ζ) y = ftY sel mu cst w η y := by
  have hcond : (∀ i : Fin n, IntAt w.1 ((η + ζ) (Pi.single i 1))) ↔ ∀ i : Fin n, IntAt w.1 (η (Pi.single i 1)) := by
    constructor
    · intro h i
      have h' := IntAt.add (h i) (intAt_neg_kernel_local_factors (hζ i))
      rw [LinearMap.add_apply, add_neg_cancel_right] at h'
      exact h'
    · intro h i
      rw [LinearMap.add_apply]
      exact IntAt.add (h i) (hζ i)
  unfold ftY
  rw [if_pos hw, if_pos hw]
  by_cases hη : ∀ i : Fin n, IntAt w.1 (η (Pi.single i 1))
  · rw [if_pos (hcond.2 hη), if_pos hη]
    have hqη : IntAt w.1 ((Col.qOf w.1 : X.E) * η y) := by
      have h' := intAt_linear_form_on_std w.1 η hη hq
      rwa [map_smul, smul_eq_mul] at h'
    have hD := hcst.D_pos w
    have hqD : ∀ x : X.E, IntAt w.1 ((Col.qOf w.1 : X.E) * x) → IntAt w.1 ((Col.qOf w.1 : X.E) ^ cst.D w * x) := by
      intro x hx
      have e : (Col.qOf w.1 : X.E) ^ cst.D w * x = ((Col.qOf w.1 ^ (cst.D w - 1) : ℕ) : X.E) * ((Col.qOf w.1 : X.E) * x) := by
        push_cast
        rw [← mul_assoc, ← pow_succ, Nat.sub_add_cancel hD]
      rw [e]
      exact IntAt.mul (intAt_natCast_kernel_local_factors _ _) hx
    have hζe : IntAt w.1 ((epsSg : X.E) * ζ y) := by
      have h' := intAt_neg_kernel_local_factors hζy
      simpa [epsSg] using h'
    have hA : IntAt w.1 ((Col.qOf w.1 : X.E) ^ cst.D w * ((epsSg : X.E) * η y)) := by
      apply hqD
      have h' := intAt_neg_kernel_local_factors hqη
      simpa [epsSg] using h'
    have hB : IntAt w.1 ((Col.qOf w.1 : X.E) ^ cst.D w * ((epsSg : X.E) * ζ y)) :=
      hqD _ (IntAt.mul (intAt_natCast_kernel_local_factors _ _) hζe)
    rw [LinearMap.add_apply, mul_add, hcst.psi_add w _ _ hA hB, hcst.psi_int w _ hζe, mul_one]
  · rw [if_neg (fun h => hη (hcond.1 h)), if_neg hη]

end Inv2

section Top

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))

def TopLaw (P : LevFam X.E X.K R.r Pr.vGs) (m2 : ℕ) (b : L.β (m2 + 1)) : Prop :=
  ∀ (w : rowSG Pr sel mu) (hw : w.1 ∈ Pr.vGs) (h : ↥(L.levG (m2 + 1) b ⟨w.1, hw⟩).H)
    (h₁ : GLG X.E (R.N R.m - 1) (rowSG Pr sel mu)) (hh₁ : h₁ w ∈ ((rowTy Ch sel mu P).inv w).H)
    (κ : ↥(GLint X.E (R.N (m2 + 1)) w.1)) (κr : ↥(GLint X.E (R.N R.m - 1) w.1)) (κt : ↥(GLint X.E (R.N R.m) w.1)),
    (∀ x ∈ stdAt X.E (R.N (m2 + 1)) w.1, redV w.1 (κ.1 x) = (h.1⁻¹).1.mulVec (redV w.1 x)) →
    (∀ x ∈ stdAt X.E (R.N R.m - 1) w.1, redV w.1 (κr.1 x) = ((h₁ w)⁻¹).1.mulVec (redV w.1 x)) →
    (∀ x ∈ stdAt X.E (R.N R.m) w.1, redV w.1 (κt.1 x) = ((extGH (N_m_succ R) h₁ w)⁻¹).1.mulVec (redV w.1 x)) →
    ∀ y : HomE X.E (R.N (m2 + 1)) (R.N R.m - 1),
      rhoS Ch sel mu (m2 + 1) w (LinearEquiv.det κ.1 : X.Eˣ) * rhoT Ch sel mu (m2 + 1) w (LinearEquiv.det κt.1 : X.Eˣ) *
          PhiTop Ch mu cst.sharp m2 w.1 (κr.1.symm.toLinearMap ∘ₗ y ∘ₗ κ.1.toLinearMap ∘ₗ
            LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) =
        (((((rowTy Ch sel mu P).inv w).lam ⟨h₁ w, hh₁⟩)⁻¹ : X.Kˣ) : X.K) * ((((L.levG (m2 + 1) b ⟨w.1, hw⟩).lam h)⁻¹ : X.Kˣ) : X.K) *
          PhiTop Ch mu cst.sharp m2 w.1 (y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1))))

theorem prXp_extUH2 (γ₁ : UF X.E (R.N R.m - 1)) (v : Sp X.E (R.N R.m)) :
    prXp X.E R ((extUH (N_m_succ R) γ₁).1 v) = γ₁.1 (prXp X.E R v) := funLeft_extUH2 (E := X.E) (N_m_succ R) _ (fun i => rfl) γ₁ v

end Top

section Inv3

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) {u : Pr.Word}

def TopInv (m2 : ℕ) : Prop :=
  ∀ (w : rowSG Pr sel mu), w.1 ∈ Pr.vGs → ∀ (y z : HomE X.E (R.N (m2 + 1) + cOf R (m2 + 1)) ((R.N R.m - 1) + 0)),
    (∀ s l, IntAt w.1 (((qOf w.1 : X.E) ^ cst.B)⁻¹ * z (Pi.single s 1) l)) →
      PhiTop Ch mu cst.sharp m2 w.1 (y + z) = PhiTop Ch mu cst.sharp m2 w.1 y

theorem frame_mem_lattice_iff_std' {j : ℕ} (p : ChPt (R := R) sel mu u j) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs) (v : Sp X.E (R.N j)) :
    frsF sel mu p P v ∈ p.deco.1.at P.1 ↔ v ∈ stdAt X.E (R.N j) P.1 := by
  have e : frsF sel mu p P = p.deco.1.liftFr ⟨P.1, hP⟩ := by simp only [frsF, dif_pos hP]
  rw [e]
  exact (Deco.liftFr_spec (p.deco.2.hasLift ⟨P.1, hP⟩)).1 v

open Classical in
theorem intAt_inv_qOf_pow_mul_cBof (P : rowSG Pr sel mu) :
    IntAt P.1 (((Col.qOf P.1 : X.E) ^ cst.B)⁻¹ * ((cBof sel mu cst u : ℕ) : X.E)) := by
  have hq0 : (Col.qOf P.1 : X.E) ≠ 0 := by
    have : Col.qOf P.1 ≠ 0 := fun h => P.1.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
    exact_mod_cast this
  have hdvd : (∏ Q : rowSG Pr sel mu, Col.qOf Q.1) = Col.qOf P.1 * ∏ Q ∈ Finset.univ.erase P, Col.qOf Q.1 :=
    (Finset.mul_prod_erase _ _ (Finset.mem_univ P)).symm
  have e : ((Col.qOf P.1 : X.E) ^ cst.B)⁻¹ * ((cBof sel mu cst u : ℕ) : X.E) =
      ((Pr.T u * (∏ Q ∈ Finset.univ.erase P, Col.qOf Q.1) ^ cst.B : ℕ) : X.E) := by
    rw [cBof, hdvd]
    push_cast
    rw [mul_pow]
    field_simp
  rw [e]
  exact intAt_natCast_kernel_local_factors _ _

open Classical in

theorem xiCpl2_inv (hQ : QE sel (mu : Chr X.F X.E X.K) = ∅) (hPr : Pr.Ok) (hcst : cst.Ok) {m2 : ℕ} (hTI : TopInv Ch sel mu cst m2)
    (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))) (d : RowPt Pr R sel mu)
    (x z : HomE X.E (R.N (m2 + 1)) (R.N R.m)) (hYm : Y ∈ ybSet sel mu cst p.deco.1.N)
    (hz : z ∈ mulLat (cBof sel mu cst u) (homAt (Sall sel mu u) p.deco.1.N (tilQ sel mu u d).1.N)) :
    XiCpl2 Ch sel mu cst m2 p Y d (x + z) = XiCpl2 Ch sel mu cst m2 p Y d x := by
  classical
  obtain ⟨z', hz', hzeq⟩ := Submodule.mem_map.1 hz
  have hzE : z = ((cBof sel mu cst u : ℕ) : X.E) • z' := by
    rw [← hzeq]
    simp only [LinearMap.smul_apply, LinearMap.id_apply]
    rw [Nat.cast_smul_eq_nsmul (𝓞 X.E), Nat.cast_smul_eq_nsmul X.E]
  subst hzE
  have hz'' : ∀ P ∈ Sall sel mu u, ∀ y ∈ localization₂ P.asIdeal p.deco.1.N, z' y ∈ localization₂ P.asIdeal (tilQ sel mu u d).1.N := hz'
  have hsm : ∀ {k : ℕ} (v : Sp X.E k), ((cBof sel mu cst u : ℕ) : X.E) • v = ((cBof sel mu cst u : ℕ) : 𝓞 X.E) • v := by
    intro k v
    rw [Nat.cast_smul_eq_nsmul (𝓞 X.E), Nat.cast_smul_eq_nsmul X.E]
  have hvG : ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs := mem_vGs_of_QE_empty sel mu hQ
  have hSr : ∀ P : rowSG Pr sel mu, P.1 ∈ Sall sel mu u := fun P => by
    have h := P.2
    simp only [rowSG, uSG, Finset.mem_union] at h
    simp only [Sall, Finset.mem_union]
    exact Or.inr h
  have hST : ∀ P : Pr.vT u, P.1 ∈ Sall sel mu u := fun P => by
    simp only [Sall, Finset.mem_union]; exact Or.inl P.2
  have hpiG : ∀ w : rowSG Pr sel mu, Pr.piT u ∉ w.1.asIdeal := fun w => piT_notMem_vGs hPr u ⟨w.1, hvG w⟩
  have htil : ∀ (P : rowSG Pr sel mu) (v : Sp X.E (R.N R.m)), v ∈ (tilQ sel mu u d).1.at P.1 →
      prXp X.E R v ∈ d.1.at P.1 ∧ IntAt P.1 (atNL X.E (R.N R.m) (R.N R.m - 1) v) :=
    fun P v hv => tilde_lattice_restrict_mem (N_m_succ R) (Pr.piT u) d (conj_piT_notMem hPr u) hpiG
      (fun i : Fin (R.N R.m - 1) => (⟨i.1, by have := i.2; omega⟩ : Fin (R.N R.m))) (fun i => rfl) P.1 v hv
  have hcBT : ∀ P : Pr.vT u, ((cBof sel mu cst u : ℕ) : 𝓞 X.E) ∈ P.1.asIdeal := by
    intro P
    have hpi : Pr.piT u ∈ P.1.asIdeal := mem_asIdeal_of_mem_divs P.2
    have hTu : ((Pr.T u : ℕ) : 𝓞 X.E) ∈ P.1.asIdeal := by
      rw [← hPr.piT_norm u]
      exact Ideal.mul_mem_right _ _ hpi
    rw [cBof, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hTu
  have hqdvd : ∀ P : rowSG Pr sel mu, Col.qOf P.1 ∣ cBof sel mu cst u := by
    intro P
    unfold cBof
    exact Dvd.dvd.mul_left (dvd_pow (Finset.dvd_prod_of_mem _ (Finset.mem_univ P)) (by have := hcst.B_pos; omega)) _
  have hsg : ∀ (P : rowSG Pr sel mu) {k : ℕ} (i : Fin k), (Pi.single i 1 : Sp X.E k) ∈ stdAt X.E k P.1 := by
    intro P k i
    rw [ciMem_stdAt]
    intro j
    rw [Pi.single_apply]
    split_ifs
    · simpa using intAt_natCast_kernel_local_factors P.1 1
    · simpa using intAt_natCast_kernel_local_factors P.1 0
  have hF : ∀ (P : rowSG Pr sel mu) (v : Sp X.E (R.N (m2 + 1))), v ∈ stdAt X.E (R.N (m2 + 1)) P.1 →
      frsF sel mu p P v ∈ p.deco.1.at P.1 :=
    fun P v hv => (frame_mem_lattice_iff_std' sel mu p P (hvG P) v).2 hv
  have hFs : ∀ (P : rowSG Pr sel mu) (v : Sp X.E (R.N (m2 + 1))), v ∈ p.deco.1.at P.1 →
      (frsF sel mu p P).symm v ∈ stdAt X.E (R.N (m2 + 1)) P.1 := by
    intro P v hv
    apply (frame_mem_lattice_iff_std' sel mu p P (hvG P) _).1
    rw [LinearEquiv.apply_symm_apply]
    exact hv
  have hLs : ∀ (P : rowSG Pr sel mu) (v : Sp X.E (R.N R.m - 1)), v ∈ d.1.at P.1 →
      (d.1.liftFr P).symm v ∈ stdAt X.E (R.N R.m - 1) P.1 := by
    intro P v hv
    apply ((Deco.liftFr_spec (d.2.hasLift P)).1 _).1
    rw [LinearEquiv.apply_symm_apply]
    exact hv
  have hA : phiT X.K p.deco.1 (tilQ sel mu u d).1 (x + ((cBof sel mu cst u : ℕ) : X.E) • z') =
      phiT X.K p.deco.1 (tilQ sel mu u d).1 x := by
    have hiff : ∀ (P : Pr.vT u) (y : Sp X.E (R.N (m2 + 1))), y ∈ p.deco.1.at P.1 →
        (((x + ((cBof sel mu cst u : ℕ) : X.E) • z') y ∈ (tilQ sel mu u d).1.at P.1 ∧
          (tilQ sel mu u d).1.f P ((x + ((cBof sel mu cst u : ℕ) : X.E) • z') y) = p.deco.1.f P y) ↔
        (x y ∈ (tilQ sel mu u d).1.at P.1 ∧ (tilQ sel mu u d).1.f P (x y) = p.deco.1.f P y)) := by
      intro P y hy
      have hzy : z' y ∈ (tilQ sel mu u d).1.at P.1 := hz'' P.1 (hST P) y hy
      have hzy2 : (((cBof sel mu cst u : ℕ) : X.E) • z') y ∈ (tilQ sel mu u d).1.at P.1 := by
        rw [LinearMap.smul_apply, hsm]
        exact Submodule.smul_mem _ _ hzy
      have hf0 : (tilQ sel mu u d).1.f P ((((cBof sel mu cst u : ℕ) : X.E) • z') y) = 0 := by
        rw [LinearMap.smul_apply, hsm, (tilQ sel mu u d).2.f_smul P _ _ hzy,
          Ideal.Quotient.eq_zero_iff_mem.2 (hcBT P), zero_mul]
      rw [LinearMap.add_apply]
      constructor
      · rintro ⟨h1, h2⟩
        have hx : x y ∈ (tilQ sel mu u d).1.at P.1 := by
          have h3 := sub_mem h1 hzy2
          rwa [add_sub_cancel_right] at h3
        refine ⟨hx, ?_⟩
        rw [← h2, (tilQ sel mu u d).2.f_add P _ hx _ hzy2, hf0, add_zero]
      · rintro ⟨h1, h2⟩
        refine ⟨add_mem h1 hzy2, ?_⟩
        rw [(tilQ sel mu u d).2.f_add P _ h1 _ hzy2, hf0, add_zero, h2]
    unfold phiT
    by_cases hc : ∀ P : Pr.vT u, ∀ y ∈ p.deco.1.at P.1,
        x y ∈ (tilQ sel mu u d).1.at P.1 ∧ (tilQ sel mu u d).1.f P (x y) = p.deco.1.f P y
    · rw [if_pos hc, if_pos (fun P y hy => (hiff P y hy).2 (hc P y hy))]
    · rw [if_neg hc, if_neg (fun h => hc (fun P y hy => (hiff P y hy).1 (h P y hy)))]
  have hPhi : ∀ P : rowSG Pr sel mu,
      PhiTop Ch mu cst.sharp m2 P.1 ((d.1.liftFr P).symm.toLinearMap ∘ₗ prXp X.E R ∘ₗ (x + ((cBof sel mu cst u : ℕ) : X.E) • z') ∘ₗ
          (frsF sel mu p P).toLinearMap ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) =
      PhiTop Ch mu cst.sharp m2 P.1 ((d.1.liftFr P).symm.toLinearMap ∘ₗ prXp X.E R ∘ₗ x ∘ₗ
          (frsF sel mu p P).toLinearMap ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) := by
    intro P
    rw [LinearMap.add_comp, LinearMap.comp_add, LinearMap.comp_add]
    refine hTI P (hvG P) _ _ ?_
    intro s l
    have hs : LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1))) (Pi.single s 1) ∈ stdAt X.E (R.N (m2 + 1)) P.1 := by
      rw [ciMem_stdAt]
      intro j
      exact (ciMem_stdAt P.1 _).1 (hsg P s) _
    have hV := hLs P _ (htil P _ (hz'' P.1 (hSr P) _ (hF P _ hs))).1
    rw [ciMem_stdAt] at hV
    have hq := intAt_inv_qOf_pow_mul_cBof sel mu cst (u := u) P
    have e : (((d.1.liftFr P).symm.toLinearMap ∘ₗ prXp X.E R ∘ₗ (((cBof sel mu cst u : ℕ) : X.E) • z') ∘ₗ
          (frsF sel mu p P).toLinearMap ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) (Pi.single s 1)) l =
        ((cBof sel mu cst u : ℕ) : X.E) * (d.1.liftFr P).symm (prXp X.E R (z' (frsF sel mu p P
          (LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1))) (Pi.single s 1))))) l := by
      simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearEquiv.coe_coe, map_smul, Pi.smul_apply, smul_eq_mul]
    rw [e, ← mul_assoc]
    exact IntAt.mul hq (hV l)
  have hft : ∀ P : rowSG Pr sel mu,
      ftY sel mu cst P ((((Pr.piT u : 𝓞 X.E) : X.E)⁻¹ • atNL X.E (R.N R.m) (R.N R.m - 1)) ∘ₗ
          (x + ((cBof sel mu cst u : ℕ) : X.E) • z') ∘ₗ (frsF sel mu p P).toLinearMap) ((frsF sel mu p P).symm (repY Y)) =
      ftY sel mu cst P ((((Pr.piT u : 𝓞 X.E) : X.E)⁻¹ • atNL X.E (R.N R.m) (R.N R.m - 1)) ∘ₗ
          x ∘ₗ (frsF sel mu p P).toLinearMap) ((frsF sel mu p P).symm (repY Y)) := by
    intro P
    have hYP := ybSet_props2 sel mu cst hYm P (hvG P)
    have hr := representative_mem hYP.1
    have hqr : ((Col.qOf P.1 : ℕ) : X.E) • repY Y ∈ p.deco.1.at P.1 := hYP.2.2 _ hr
    have hpiI : IntAt P.1 (((Pr.piT u : 𝓞 X.E) : X.E)⁻¹) := by
      have h0 : ((Pr.piT u : 𝓞 X.E) : X.E) ≠ 0 := by
        intro h
        apply hpiG P
        have h1 : Pr.piT u = 0 := (IsFractionRing.injective (𝓞 X.E) X.E) (by rw [map_zero]; exact h)
        rw [h1]
        exact zero_mem _
      refine ⟨1, Pr.piT u, hpiG P, ?_⟩
      rw [map_one]
      exact mul_inv_cancel₀ h0
    rw [LinearMap.add_comp, LinearMap.comp_add]
    refine fourierTwist_add_integral sel mu cst hcst P (hvG P) _ _ _ ?_ ?_ ?_
    · intro i
      have hv := (htil P _ (hz'' P.1 (hSr P) _ (hF P _ (hsg P i)))).2
      have e : ((((Pr.piT u : 𝓞 X.E) : X.E)⁻¹ • atNL X.E (R.N R.m) (R.N R.m - 1)) ∘ₗ
          (((cBof sel mu cst u : ℕ) : X.E) • z') ∘ₗ (frsF sel mu p P).toLinearMap) (Pi.single i 1) =
          ((Pr.piT u : 𝓞 X.E) : X.E)⁻¹ * (((cBof sel mu cst u : ℕ) : X.E) *
            atNL X.E (R.N R.m) (R.N R.m - 1) (z' (frsF sel mu p P (Pi.single i 1)))) := by
        simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearEquiv.coe_coe, map_smul, smul_eq_mul] <;> ring
      rw [e]
      exact IntAt.mul hpiI (IntAt.mul (intAt_natCast_kernel_local_factors _ _) hv)
    · have hv := (htil P _ (hz'' P.1 (hSr P) _ hqr)).2
      rw [map_smul, map_smul, smul_eq_mul] at hv
      obtain ⟨m, hm⟩ := hqdvd P
      have e : ((((Pr.piT u : 𝓞 X.E) : X.E)⁻¹ • atNL X.E (R.N R.m) (R.N R.m - 1)) ∘ₗ
          (((cBof sel mu cst u : ℕ) : X.E) • z') ∘ₗ (frsF sel mu p P).toLinearMap) ((frsF sel mu p P).symm (repY Y)) =
          ((Pr.piT u : 𝓞 X.E) : X.E)⁻¹ * (((cBof sel mu cst u : ℕ) : X.E) *
            atNL X.E (R.N R.m) (R.N R.m - 1) (z' (repY Y))) := by
        simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
          map_smul, smul_eq_mul] <;> ring
      rw [e, hm, Nat.cast_mul]
      have e3 : ((Col.qOf P.1 : ℕ) : X.E) * (m : X.E) * atNL X.E (R.N R.m) (R.N R.m - 1) (z' (repY Y)) =
          (m : X.E) * (((Col.qOf P.1 : ℕ) : X.E) * atNL X.E (R.N R.m) (R.N R.m - 1) (z' (repY Y))) := by ring
      rw [e3]
      exact IntAt.mul hpiI (IntAt.mul (intAt_natCast_kernel_local_factors _ _) hv)
    · rw [← LinearEquiv.map_smul]
      exact hFs P _ hqr
  unfold XiCpl2
  rw [hA]
  congr 1
  refine Finset.prod_congr rfl (fun P _ => ?_)
  rw [hPhi P, hft P]

end Inv3

section Cp2Thm

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  (A : Amb X) (u : Pr.Word) (m2 : ℕ)

theorem cp2EquivOn_of (hQ : QE sel (mu : Chr X.F X.E X.K) = ∅) (hT : 0 < Pr.T u) (hPr : Pr.Ok) (hcst : cst.Ok)
    (hOk : ChTh.Ok (Ch := Ch) cst (chTh W Ch sel mu cst A u m2))
    (b : L.β (m2 + 1)) (hY : YbHyp (R := R) sel mu cst L u m2 b) (P : LevFam X.E X.K R.r Pr.vGs)
    (hTI : TopInv Ch sel mu cst m2)
    (hTop : TopLaw Ch sel mu cst L P m2 b) :
    Cp2EquivOn W Ch sel mu cst L (chTh W Ch sel mu cst A u m2) b hY P := by
  intro g g₁ p Y d hYm
  change Y ∈ ybSet sel mu cst p.deco.1.N at hYm
  have hG := mem_vGs_of_QE_empty (Pr := Pr) sel mu hQ
  choose κ hκ hκr using fun w : rowSG Pr sel mu =>
    frsF_smul sel mu p (L.levG (m2 + 1) b) (L.levQ (m2 + 1) b) g w (hG w)
  have hfr : frsF sel mu (g • p) = fun w => g.1.1 * frsF sel mu p w * (κ w).1 := funext hκ
  have hTc : ∀ Q : Pr.vT u, cO X.E (Pr.piT u) ∉ Q.1.asIdeal := conj_piT_notMem hPr u
  have hGc : ∀ w : rowSG Pr sel mu, Pr.piT u ∉ w.1.asIdeal := fun w => piT_notMem_vGs hPr u ⟨w.1, hG w⟩
  have hgd : g₁ • d = ((g₁.1, (g₁.2.1 : GLG X.E (R.N R.m - 1) (rowSG Pr sel mu))) :
      UF X.E (R.N R.m - 1) × GLG X.E (R.N R.m - 1) (rowSG Pr sel mu)) • d := rfl
  have htil : tilQ sel mu u (g₁ • d) = (extUH (N_m_succ R) g₁.1, extGH (N_m_succ R) (g₁.2.1 : GLG X.E (R.N R.m - 1) (rowSG Pr sel mu))) •
      tilQ sel mu u d := by
    rw [hgd]
    exact DecoSet.tilH_smul (N_m_succ R) _ d hTc hGc
  choose κt hκt hκtr using fun w : rowSG Pr sel mu =>
    liftFr_smul (tilQ sel mu u d) (extUH (N_m_succ R) g₁.1, extGH (N_m_succ R) (g₁.2.1 : GLG X.E (R.N R.m - 1) (rowSG Pr sel mu))) w
  have hfrT : frsT sel mu u (g₁ • d) = fun w => (extUH (N_m_succ R) g₁.1).1 * frsT sel mu u d w * (κt w).1 := by
    funext w
    unfold frsT
    rw [htil]
    exact hκt w
  choose κr hκr' hκrr using fun w : rowSG Pr sel mu =>
    liftFr_smul d ((g₁.1, (g₁.2.1 : GLG X.E (R.N R.m - 1) (rowSG Pr sel mu))) :
      UF X.E (R.N R.m - 1) × GLG X.E (R.N R.m - 1) (rowSG Pr sel mu)) w
  have hlr : ∀ w, (g₁ • d).1.liftFr w = g₁.1.1 * d.1.liftFr w * (κr w).1 := fun w => hκr' w
  have hN : IsSdLat p.deco.1.N := ⟨p.deco.2.lat, p.deco.2.uni⟩
  have hN' : IsSdLat (tilQ sel mu u d).1.N := ⟨(tilQ sel mu u d).2.lat, (tilQ sel mu u d).2.uni⟩
  have hdeco : (g • p).deco = (g.1, (g.2.1 : GLG X.E (R.N (m2 + 1)) Pr.vGs)) • p.deco := rfl
  have hYm1 : (fun v => g.1.1 v) '' Y ∈ ybSet sel mu cst (gmap g.1.1 p.deco.1.N) :=
    (ybSet_gmap sel mu cst p.deco.1.N g.1.1 Y).2 hYm
  have hc : ((((rowTy Ch sel mu P).inv.chr g₁.2)⁻¹ * ((L.levG (m2 + 1) b).chr g.2.1)⁻¹ : X.Kˣ) : X.K) =
      ∏ w : rowSG Pr sel mu,
        (((((rowTy Ch sel mu P).inv w).lam ⟨(g₁.2.1 : GLG X.E (R.N R.m - 1) (rowSG Pr sel mu)) w, g₁.2.2 w (Set.mem_univ w)⟩)⁻¹ : X.Kˣ) : X.K) *
          ((((L.levG (m2 + 1) b ⟨w.1, hG w⟩).lam ⟨(g.2.1 : GLG X.E (R.N (m2 + 1)) Pr.vGs) ⟨w.1, hG w⟩, g.2.1.2 _ (Set.mem_univ _)⟩)⁻¹ : X.Kˣ) : X.K) := by
    rw [Finset.prod_mul_distrib, prod_rowSG_eq_prod_vGs_of_QE_empty sel mu hQ (fun w =>
      ((((L.levG (m2 + 1) b w).lam ⟨(g.2.1 : GLG X.E (R.N (m2 + 1)) Pr.vGs) w, g.2.1.2 _ (Set.mem_univ _)⟩)⁻¹ : X.Kˣ) : X.K))]
    rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, levFam_chr_apply_coe, levFam_chr_apply_coe]
    simp only [Units.val_inv_eq_inv_val, Finset.prod_inv_distrib]
  unfold cp2K
  split_ifs with h1 h2 <;> first | exact absurd hYm1 h1 | exact absurd hYm h2 | skip
  rw [hfr, hfrT, htil]
  refine (kerOf_move hOk.top (cBof_pos sel mu cst u hT) hN hN' (frsF sel mu p) (frsT sel mu u d) g.1 (extUH (N_m_succ R) g₁.1) κ κt
    _ _ ((((rowTy Ch sel mu P).inv.chr g₁.2)⁻¹ * ((L.levG (m2 + 1) b).chr g.2.1)⁻¹ : X.Kˣ) : X.K)
    (fun x z hz => xiCpl2_inv Ch sel mu cst hQ hPr hcst hTI p Y d x z hYm hz) ?_).trans ?_
  · intro x
    unfold XiCpl2
    rw [hdeco, htil, phiT_smul]
    simp only [hfr, hlr]
    rw [hc]
    refine prod_mul_eq_of_forall_cross_mul_eq _ _ _ _ _ fun w => ?_
    have hw := hG w
    obtain ⟨hne, hdiff, hqm⟩ := ybSet_props2 sel mu cst hYm w hw
    have hF : frsF sel mu p w = p.deco.1.liftFr ⟨w.1, hw⟩ := by
      unfold frsF
      rw [dif_pos hw]
    have hLift := Deco.liftFr_spec (p.deco.2.hasLift ⟨w.1, hw⟩)
    have hFst : ∀ z, z ∈ localization₂ w.1.asIdeal p.deco.1.N → (frsF sel mu p w).symm z ∈ stdAt X.E (R.N (m2 + 1)) w.1 := by
      intro z hz
      rw [hF]
      apply (hLift.1 _).1
      rw [LinearEquiv.apply_symm_apply]
      exact hz
    obtain ⟨a, ha, hra⟩ : repY ((fun v => g.1.1 v) '' Y) ∈ (fun v => g.1.1 v) '' Y := representative_mem (hne.image _)
    have hr0 := representative_mem hne
    have e2 : (κ w).1 ((g.1.1 * frsF sel mu p w * (κ w).1).symm (g.1.1 a)) = (frsF sel mu p w).symm a := by
      rw [LinearEquiv.eq_symm_apply]
      apply g.1.1.injective
      have := LinearEquiv.apply_symm_apply (g.1.1 * frsF sel mu p w * (κ w).1) (g.1.1 a)
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply] at this
      exact this
    have hδ : (κ w).1 ((g.1.1 * frsF sel mu p w * (κ w).1).symm (g.1.1 a)) - (frsF sel mu p w).symm (repY Y) ∈
        stdAt X.E (R.N (m2 + 1)) w.1 := by
      rw [e2, ← map_sub]
      exact hFst _ (hdiff _ ha _ hr0)
    have hq : ((qOf w.1 : ℕ) : X.E) • (frsF sel mu p w).symm (repY Y) ∈ stdAt X.E (R.N (m2 + 1)) w.1 := by
      rw [← LinearEquiv.map_smul]
      exact hFst _ (hqm _ hr0)
    have hA : PhiTop Ch mu cst.sharp m2 w.1
        ((g₁.1.1 * d.1.liftFr w * (κr w).1).symm.toLinearMap ∘ₗ prXp X.E R ∘ₗ
          ((extUH (N_m_succ R) g₁.1).1.toLinearMap ∘ₗ x ∘ₗ g.1.1.symm.toLinearMap) ∘ₗ
            (g.1.1 * frsF sel mu p w * (κ w).1).toLinearMap ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) =
        PhiTop Ch mu cst.sharp m2 w.1 ((κr w).1.symm.toLinearMap ∘ₗ
          ((d.1.liftFr w).symm.toLinearMap ∘ₗ prXp X.E R ∘ₗ x ∘ₗ (frsF sel mu p w).toLinearMap) ∘ₗ (κ w).1.toLinearMap ∘ₗ
            LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) := by
      congr 1
      refine LinearMap.ext fun v => ?_
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [LinearEquiv.symm_apply_eq]
      simp only [LinearEquiv.mul_apply, LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply, prXp_extUH2]
    have hη : ((((Pr.piT u : 𝓞 X.E) : X.E))⁻¹ • atNL X.E (R.N R.m) (R.N R.m - 1)) ∘ₗ
          ((extUH (N_m_succ R) g₁.1).1.toLinearMap ∘ₗ x ∘ₗ g.1.1.symm.toLinearMap) ∘ₗ (g.1.1 * frsF sel mu p w * (κ w).1).toLinearMap =
        (((((Pr.piT u : 𝓞 X.E) : X.E))⁻¹ • atNL X.E (R.N R.m) (R.N R.m - 1)) ∘ₗ x ∘ₗ (frsF sel mu p w).toLinearMap) ∘ₗ
          (κ w).1.toLinearMap := by
      refine LinearMap.ext fun v => ?_
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.mul_apply, LinearEquiv.symm_apply_apply,
        LinearMap.smul_apply, atNL_extUH2]
    have key := hTop w hw ⟨(g.2.1 : GLG X.E (R.N (m2 + 1)) Pr.vGs) ⟨w.1, hw⟩, g.2.1.2 _ (Set.mem_univ _)⟩
      (g₁.2.1 : GLG X.E (R.N R.m - 1) (rowSG Pr sel mu)) (g₁.2.2 w (Set.mem_univ w)) (κ w) (κr w) (κt w) (hκr w) (hκrr w) (hκtr w)
      ((d.1.liftFr w).symm.toLinearMap ∘ₗ prXp X.E R ∘ₗ x ∘ₗ (frsF sel mu p w).toLinearMap)
    rw [hA, hη, ftY_move2 sel mu cst hcst w hw (κ w) _ _ _ ?_ hq, ← mul_assoc, key, mul_assoc]
    try rfl
    change (κ w).1 ((g.1.1 * frsF sel mu p w * (κ w).1).symm (repY ((fun v => g.1.1 v) '' Y))) - (frsF sel mu p w).symm (repY Y) ∈
      stdAt X.E (R.N (m2 + 1)) w.1
    rw [← hra]
    exact hδ
  · show _ = (evRho W Ch sel mu P u g₁) ∘ₗ _ ∘ₗ (frmRho (colValF W sel mu u (m2 + 1)) (L.levG (m2 + 1) b) (L.levQ (m2 + 1) b) g⁻¹)
    simp only [evRho, frmRho, MonoidHom.coe_mk, OneHom.coe_mk, levQFam_chr_eq_one_of_QE_empty sel mu hQ, mul_one, Prod.fst_inv, Prod.snd_inv, map_inv,
      LinearMap.smul_comp, LinearMap.comp_smul, smul_smul]
    congr 1
    simp only [Units.val_mul, Units.val_inv_eq_inv_val]
    ring

end Cp2Thm

end Formalism.L2.Ker
