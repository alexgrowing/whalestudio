import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameFixedAway
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPlaceOverMoveValCc
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.RootsCharpolyPowEqMapPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaCharpolyEqStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsReductionTeichmullerEmbeddingAtLocalisatioStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WildEqOneOfCharpolyUnipotentModLStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualRepKerIsOpenStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOrderPreservingPowerHomAlgClosurePrimeFielStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameGeneratorImageEqCoprimePowStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaCompatibleConjugationRepresentationStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameAnyAtPlaceStatement

noncomputable section

namespace GlobalTheory.TypeLeaf.ConjPlace

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.TameLabels GlobalTheory.AntiRamConj GlobalTheory.TwistDet
open scoped Pointwise

section Galois

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

theorem mem_ine_of_wild {A : ValuationSubring Ω} {s : G E Ω}
    (hs : ∀ y : Ω, y ≠ 0 → A.valuation (s y / y - 1) < 1) : s ∈ Ine (F := E) A := by
  have hv : ∀ y, A.valuation (s y) = A.valuation y := by
    intro y
    rcases eq_or_ne y 0 with rfl | hy
    · simp
    have h1 : A.valuation (s y / y) = 1 := by
      have := Valuation.map_one_add_of_lt A.valuation (hs y hy)
      simpa using this
    rw [map_div₀, div_eq_one_iff_eq (by simpa using hy)] at h1
    exact h1
  refine ⟨?_, fun x hx => ?_⟩
  · show s • A = A
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def,
      ← A.valuation_le_one_iff, ← A.valuation_le_one_iff, ← hv, mul_inv_apply]
  · rcases eq_or_ne x 0 with rfl | hx0
    · simp
    have e : s x - x = (s x / x - 1) * x := by field_simp
    rw [e, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' hx) (hs x hx0)

theorem tameGenAt_move (c : Ω ≃+* Ω)
    (hc : ∀ x : E, ∃ y : E, c.symm (algebraMap E Ω x) = algebraMap E Ω y)
    (hc' : ∀ x : E, ∃ y : E, c.symm.symm (algebraMap E Ω x) = algebraMap E Ω y)
    (f : G E Ω →* G E Ω) (hf : ∀ σ x, f σ x = c (σ (c.symm x))) (hcont : Continuous f)
    {B : ValuationSubring Ω} {γ : G E Ω} (h : TameGenAt B γ) : TameGenAt (moveVal c B) (f γ) := by
  have e : ∀ σ, f σ = conjAut c hc σ := fun σ => AlgEquiv.ext (hf σ)
  refine ⟨by rw [e]; exact conjAut_mem_ine c hc h.1, fun σ hσ => ?_⟩
  have h1 := conjAut_mem_ine c.symm hc' hσ
  have e2 : moveVal c.symm (moveVal c B) = B := by
    ext x
    simp [mem_moveVal]
  rw [e2] at h1
  have e3 : σ = f (conjAut c.symm hc' σ) := by
    ext x
    rw [hf, conjAut_apply]
    simp
  rw [e3]
  refine map_mem_closure hcont (h.2 h1) fun τ hτ => ?_
  have h2 := Subgroup.mem_map_of_mem f hτ
  rw [MonoidHom.map_closure] at h2
  refine Subgroup.closure_mono ?_ h2
  rintro _ ⟨a, ha | ha, rfl⟩
  · exact Or.inl (congrArg f ha)
  · refine Or.inr fun y hy => ?_
    rw [moveVal_lt_one, map_sub, map_div₀, map_one, hf, RingEquiv.symm_apply_apply]
    exact ha _ ((map_ne_zero_iff _ c.symm.injective).2 hy)

end Galois

theorem continuous_cConj (D : D7) : Continuous (cConj D.ntw) := by
  refine continuous_of_continuousAt_one _ ?_
  rw [ContinuousAt, map_one]
  intro U hU
  obtain ⟨L, hL, hLU⟩ := (krullTopology_mem_nhds_one_iff D.host.E D.nd.Om U).1 hU
  have h := isOpen_comap_cConj D.ntw (IntermediateField.fixingSubgroup_isOpen L)
  exact Filter.mem_map.2 (Filter.mem_of_superset (h.mem_nhds (Subgroup.one_mem _)) fun g hg => hLU hg)

theorem exists_tameGenAt_conj (D : D7) {P w : PlE D.host} (h : IsConjPl D.host P w) {γ : G D.host.E D.nd.Om}
    (hγ : TameGenAt (D.nd.plOm.1 w) γ) :
    ∃ g : G D.host.E D.nd.Om, TameGenAt (D.nd.plOm.1 P) (g * cConj D.ntw γ * g⁻¹) := by
  have h2 := isPlaceOver_moveVal_cc D.ntw (isConjPl_symm h) (D.nd.plOm.2 w)
  obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver (F := D.host.E) h2 (D.nd.plOm.2 P)
  have h3 := tameGenAt_move D.ntw.cc (cc_symm_mem D.ntw) (fun x => ⟨_, cc_algebraMap D.ntw x⟩) (cConj D.ntw)
    (cConj_apply D.ntw) (continuous_cConj D) hγ
  have h4 := tameGenAt_move g.toRingEquiv (fun x => ⟨x, g.symm.commutes x⟩) (fun x => ⟨x, g.commutes x⟩)
    (MulAut.conj g).toMonoidHom (fun _ _ => rfl) (by
      change Continuous fun x => g * x * g⁻¹
      fun_prop) h3
  have e : moveVal g.toRingEquiv (moveVal D.ntw.cc (D.nd.plOm.1 w)) = D.nd.plOm.1 P := by
    rw [← hg]
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    rfl
  rw [e] at h4
  exact ⟨g, h4⟩

section Alg

theorem charpoly_pow_of_prod {K ι : Type} [Field K] [IsAlgClosed K] {r : ℕ} (A : Matrix (Fin r) (Fin r) K)
    (s : Multiset ι) (f : ι → K) (h : A.charpoly = (s.map fun x => X - C (f x)).prod) (n : ℕ) :
    (A ^ n).charpoly = (s.map fun x => X - C (f x ^ n)).prod := by
  have h1 : A.charpoly.roots = s.map f := by
    rw [h, ← roots_multiset_prod_X_sub_C (s.map f), Multiset.map_map]
    rfl
  have h2 := GlobalTheory.CharpolyPow.roots_charpoly_pow K r n A
  rw [(IsAlgClosed.splits (A ^ n).charpoly).eq_prod_roots_of_monic (Matrix.charpoly_monic _), h2, h1,
    Multiset.map_map, Multiset.map_map]
  rfl

theorem pow_eq_one_of_prod {K ι : Type} [Field K] [IsAlgClosed K] {r : ℕ} (A : Matrix (Fin r) (Fin r) K)
    (s : Multiset ι) (f : ι → K) (h : A.charpoly = (s.map fun x => X - C (f x)).prod) {n : ℕ} (hn : A ^ n = 1)
    {x : ι} (hx : x ∈ s) : f x ^ n = 1 := by
  have h1 := charpoly_pow_of_prod A s f h n
  have h2 : (X - C (f x ^ n)) ∣ (A ^ n).charpoly := by
    rw [h1]
    exact Multiset.dvd_prod (Multiset.mem_map.2 ⟨x, hx, rfl⟩)
  rw [hn, Matrix.charpoly_one, dvd_iff_isRoot] at h2
  simp only [IsRoot.def, eval_pow, eval_sub, eval_X, eval_one] at h2
  exact sub_eq_zero.1 (eq_zero_of_pow_eq_zero h2)

variable {g : ℕ} [Fact g.Prime]

theorem map_zero_of_injective {θ : Formalism.CyclotomicNorms.Fbar g →* Formalism.CyclotomicNorms.Fbar g} (h : Function.Injective θ) : θ 0 = 0 := by
  by_contra h0
  have h1 : θ 0 * θ 0 = θ 0 * θ 1 := by rw [← map_mul, ← map_mul, zero_mul, zero_mul]
  exact zero_ne_one (h (mul_left_cancel₀ h0 h1))

theorem coprime_primeToPart {l : ℕ} (hl : l.Prime) (x : Formalism.CyclotomicNorms.Fbar g) (h : Formalism.CyclotomicNorms.primeToPart l x ≠ 0) :
    (orderOf (Formalism.CyclotomicNorms.primeToPart l x)).Coprime l := by
  rcases eq_or_ne x 0 with rfl | hx
  · unfold Formalism.CyclotomicNorms.primeToPart at h ⊢
    generalize (_ * _ : ℕ) = m at h ⊢
    rcases m with _ | m
    · simp
    · simp at h
  · have h0 : orderOf x ≠ 0 := (isOfFinOrder_of_ne_zero hx).orderOf_pos.ne'
    refine Nat.Coprime.coprime_dvd_left ?_ (Nat.coprime_ordCompl hl h0).symm
    unfold Formalism.CyclotomicNorms.primeToPart
    rw [pow_mul]
    refine (orderOf_pow_dvd _).trans ?_
    rw [orderOf_pow_of_dvd (pow_ne_zero _ hl.ne_zero) (Nat.ordProj_dvd _ _)]

theorem comp_pow_eq {K : Type} [Field K] {l M n : ℕ} (hl : l.Prime) (hM : 0 < M) {ι : Formalism.CyclotomicNorms.Fbar g →* K}
    (hι : InjPrimeTo l ι) {θ : Formalism.CyclotomicNorms.Fbar g →* Formalism.CyclotomicNorms.Fbar g} (hθ : Function.Injective θ)
    (hθn : ∀ x, x ^ M = 1 → θ x = x ^ n) {e : ℤ} (he : e = 1 ∨ e = -1) (x : Formalism.CyclotomicNorms.Fbar g)
    (h : (ι (Formalism.CyclotomicNorms.primeToPart l x) ^ e) ^ M = 1) :
    (ι.comp θ) (Formalism.CyclotomicNorms.primeToPart l x) ^ e = (ι (Formalism.CyclotomicNorms.primeToPart l x) ^ e) ^ n := by
  have hc := coprime_primeToPart hl x
  set y := Formalism.CyclotomicNorms.primeToPart l x
  have h1 : ι y ^ M = 1 := by
    rcases he with rfl | rfl
    · simpa using h
    · simpa using h
  have h2 : ι (θ y) = ι y ^ n := by
    rcases eq_or_ne y 0 with hy | hy
    · have h0 : ι y ≠ 0 := fun h0 => by
        rw [h0, zero_pow hM.ne'] at h1
        exact zero_ne_one h1
      have h3 : ι y * ι y = ι y * 1 := by rw [← map_mul, hy, zero_mul, mul_one]
      have h4 := mul_left_cancel₀ h0 h3
      rw [h4, one_pow, hy, map_zero_of_injective hθ, ← hy, h4]
    · have h3 : y ^ M = 1 := hι _ _ (pow_ne_zero _ hy) one_ne_zero
        (Nat.Coprime.coprime_dvd_left (orderOf_pow_dvd _) (hc hy)) (by simp) (by rw [map_pow, h1, map_one])
      rw [hθn y h3, map_pow]
  rw [MonoidHom.comp_apply, h2, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]

theorem injPrimeTo_comp {K : Type} [Field K] {l : ℕ} {ι : Formalism.CyclotomicNorms.Fbar g →* K}
    (hι : InjPrimeTo l ι) {θ : Formalism.CyclotomicNorms.Fbar g →* Formalism.CyclotomicNorms.Fbar g} (hθ : Function.Injective θ)
    (ho : ∀ x, orderOf (θ x) = orderOf x) : InjPrimeTo l (ι.comp θ) := by
  have hne : ∀ x, x ≠ 0 → θ x ≠ 0 := fun x hx h => hx (hθ (h.trans (map_zero_of_injective hθ).symm))
  intro x y hx hy cx cy h
  exact hθ (hι _ _ (hne x hx) (hne y hy) (by rwa [ho]) (by rwa [ho]) h)

end Alg

def chiBar (D : D7) (i : D.nd.Loc) : G D.host.E D.nd.Om →* (Formalism.CyclotomicNorms.Fbar (D.nd.l i))ˣ :=
  (Units.map ((D.naut.kFbar i).comp (IsLocalRing.residue (D.nd.O i))).toMonoidHom).comp (D.nd.chi i 1)

theorem chiBar_val (D : D7) (i : D.nd.Loc) (s : G D.host.E D.nd.Om) :
    (chiBar D i s : Formalism.CyclotomicNorms.Fbar (D.nd.l i)) = D.naut.kFbar i (IsLocalRing.residue (D.nd.O i) (chi1 D.nd i s)) := rfl

theorem isOpen_ker_chiBar (D : D7) (i : D.nd.Loc) : IsOpen ((chiBar D i).ker : Set (G D.host.E D.nd.Om)) := by
  have h := (isAdic_iff.1 (D.nd.O_adic i)).1 1
  rw [pow_one] at h
  have hc : Continuous fun s : G D.host.E D.nd.Om => chi1 D.nd i s - 1 := (D.nd.chi_cont i 1).sub continuous_const
  have e : ((chiBar D i).ker : Set (G D.host.E D.nd.Om)) =
      (fun s => chi1 D.nd i s - 1) ⁻¹' (IsLocalRing.maximalIdeal (D.nd.O i) : Set (D.nd.O i)) := by
    ext s
    rw [SetLike.mem_coe, MonoidHom.mem_ker, Units.ext_iff, chiBar_val, Units.val_one, Set.mem_preimage,
      SetLike.mem_coe, ← IsLocalRing.residue_eq_zero_iff, map_sub, map_one, sub_eq_zero,
      map_eq_one_iff _ (D.naut.kFbar i).injective]
  rw [e]
  exact h.preimage hc

theorem tameAnyAt_of_isConjPl : ∀ D : D7, WildOne D → (∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k), D.nd.l i ≠ D.host.g k → ∀ s ∈ wildSet D.nd (D.nd.plOm.1 (D.naut.plGw k v)), D.nd.chi i 1 s = 1) → GalAway D → FrobDense D → ∀ (i : D.nd.Loc) (π : D.naut.CG D.R.r) (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)), D.naut.csd π → D.naut.ralg π → FullLab D [⟨D.R.r, π, 1⟩] → IsRepOfSig D.nd D.naut i [⟨D.R.r, π, 1⟩] ρ → ∀ k : Fin 2, D.nd.l i ≠ D.host.g k → ∀ (v : D.nd.PlG k) (w : PlE D.host), IsConjPl D.host (D.naut.plGw k v) w → TameGen D.nd (D.nd.plOm.1 w) (D.nd.gam0 i w) → TameAnyAt D i [⟨D.R.r, π, 1⟩] ρ k w := by
  intro D hW hχ hG hF i π ρ hc ha hfull hρ k hl v w hvw hgen
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  have hP := not_mem_of_ne (D := D) (v := v) (D.nd.lPrime i).out hl
  have hw : w ∉ placesOver D.host.E (D.nd.l i) := fun h => hP (mem_placesOver_conj (isConjPl_symm hvw) h)
  have hγ0 : TameGenAt (D.nd.plOm.1 (D.naut.plGw k v)) (D.nd.gam0 i (D.naut.plGw k v)) := by
    refine D.nd.restN_tameGenerator_generates i _ (Or.inl ((D.nd.S_def i _).2 ⟨?_, hP⟩))
    have hv := D.naut.plGw_over k v
    fin_cases k
    · exact Or.inl hv
    · exact Or.inr (Or.inl hv)
  have hγw : TameGenAt (D.nd.plOm.1 w) (D.nd.gam0 i w) := ⟨D.nd.locNd_chebotarevPlace_mem i w, hgen⟩
  obtain ⟨g, hg⟩ := exists_tameGenAt_conj D hvw hγw
  have hkill : ∀ s : G D.host.E D.nd.Om,
      (∀ y : D.nd.Om, y ≠ 0 → (D.nd.plOm.1 (D.naut.plGw k v)).valuation (s y / y - 1) < 1) →
      ((redF D i ρ).prod (chiBar D i)) s = 1 := by
    intro u hu
    have huI := mem_ine_of_wild hu
    obtain ⟨ι, -, hred⟩ := GlobalTheory.T.exists_reduction_teichmullerEmbedding_at_localisation D i k hl
    have hf := hfull k v
    unfold labSig at hf
    rw [isoLoc_single] at hf
    have h1 := (GlobalTheory.T.inertia_charpoly_eq D hG hF i π ρ hc ha hρ _ hP u huI).trans (hW k v _ hf u huI hu)
    rw [D.naut.locG_dim] at h1
    have h2 : ((redF D i ρ u : GL (Fin D.R.r) _) :
        Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.CyclotomicNorms.Fbar (D.nd.l i))).charpoly = (X - 1) ^ D.R.r := by
      rw [charpoly_redF, hred _ (Multiset.replicate D.R.r 1) (by rw [h1]; simp)]
      simp
    have hgv : (D.nd.plOm.1 (D.naut.plGw k v)).valuation ((D.host.g k : ℕ) : D.nd.Om) < 1 := by
      have h4 := D.nd.plOm.2 (D.naut.plGw k v)
      have h5 : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw k v).asIdeal := D.naut.plGw_over k v
      simpa using (h4 _).2 h5
    have h3 := GlobalTheory.T.wild_eq_one_of_charpoly_unipotent_mod_l _ _ _ (D.host.g k) (D.nd.l i) D.R.r hl hgv _ (redF D i ρ)
      (GlobalTheory.T.residualRep_ker_isOpen D i ρ hρ.1) u hu h2
    refine Prod.ext h3 ?_
    change Units.map _ (D.nd.chi i 1 u) = 1
    rw [hχ i k v hl u hu, map_one]
  have hopen : IsOpen ((((redF D i ρ).prod (chiBar D i)).ker : Subgroup _) : Set (G D.host.E D.nd.Om)) := by
    rw [MonoidHom.ker_prod, Subgroup.coe_inf]
    exact (GlobalTheory.T.residualRep_ker_isOpen D i ρ hρ.1).inter (isOpen_ker_chiBar D i)
  obtain ⟨n, hn, hM, hpow⟩ := GlobalTheory.T.tameGenerator_image_eq_coprime_pow _ _ _ _ _ hγ0 hg _ _ hopen hkill
  set γ0 := D.nd.gam0 i (D.naut.plGw k v) with hγ0def
  set M := orderOf (((redF D i ρ).prod (chiBar D i)) γ0) with hMdef
  have hone : ((redF D i ρ).prod (chiBar D i)) γ0 ^ M = 1 := pow_orderOf_eq_one _
  have hinv : ((redF D i ρ).prod (chiBar D i)) (g * cConj D.ntw (D.nd.gam0 i w) * g⁻¹)⁻¹ =
      ((redF D i ρ).prod (chiBar D i)) γ0 ^ (n * (M - 1)) := by
    rw [map_inv, hpow, inv_eq_iff_mul_eq_one, ← pow_add, ← mul_one_add, show 1 + (M - 1) = M by omega, mul_comm, pow_mul,
      hone, one_pow]
  have hn' : (n * (M - 1)).Coprime M := hn.mul_left ((Nat.coprime_self_sub_left hM).2 (Nat.coprime_one_left _))
  obtain ⟨θ, hθ, hθo, hθn⟩ := GlobalTheory.T.exists_order_preserving_power_hom_algClosure_primeField (D.host.g k) M _ hM hn'
  obtain ⟨hcp, hcχ⟩ := GlobalTheory.T.inertia_compatible_conjugation_representation D hF i π ρ hc hρ w _ hw (D.nd.plOm.2 w) _ (Subgroup.inv_mem _ hγw.1)
    (cConj D.ntw (D.nd.gam0 i w)⁻¹) (fun y => by rw [cConj_apply, RingEquiv.symm_apply_apply])
  rw [inv_inv] at hcp hcχ
  have econj : (g * cConj D.ntw (D.nd.gam0 i w) * g⁻¹)⁻¹ = g * cConj D.ntw (D.nd.gam0 i w)⁻¹ * g⁻¹ := by
    rw [map_inv]
    group
  rw [econj] at hinv
  have hρ1 : redF D i ρ (g * cConj D.ntw (D.nd.gam0 i w)⁻¹ * g⁻¹) = redF D i ρ γ0 ^ (n * (M - 1)) :=
    congrArg Prod.fst hinv
  have hχ1 : chiBar D i (g * cConj D.ntw (D.nd.gam0 i w)⁻¹ * g⁻¹) = chiBar D i γ0 ^ (n * (M - 1)) :=
    congrArg Prod.snd hinv
  have hρM : redF D i ρ γ0 ^ M = 1 := congrArg Prod.fst hone
  have hχM : chiBar D i γ0 ^ M = 1 := congrArg Prod.snd hone
  obtain ⟨v', j, ι, e₁, e₂, he₁, he₂, hι, hch, hχ0⟩ := GlobalTheory.T.tame_any_at_place D hG hF i π ρ hc ha hfull hρ k hl v
  refine ⟨v', j, ι.comp θ, e₁, e₂, he₁, he₂, injPrimeTo_comp hι hθ hθo, ?_, ?_⟩
  · have h1 := charpoly_pow_of_prod _ _ _ hch (n * (M - 1))
    rw [← Units.val_pow_eq_pow_val, ← hρ1, map_mul, map_mul, map_inv _ g, Units.val_mul, Units.val_mul, Matrix.coe_units_inv,
      Matrix.charpoly_units_conj, charpoly_redF, hcp, ← charpoly_redF] at h1
    rw [h1]
    refine congrArg _ (Multiset.map_congr rfl fun x hx => ?_)
    rw [comp_pow_eq (D.nd.lPrime i).out hM hι hθ hθn he₁ x
      (pow_eq_one_of_prod _ _ _ hch (by rw [← Units.val_pow_eq_pow_val, hρM, Units.val_one]) hx)]
  · rw [← chiBar_val] at hχ0
    rw [comp_pow_eq (D.nd.lPrime i).out hM hι hθ hθn he₂ _
      (by rw [← hχ0, ← Units.val_pow_eq_pow_val, hχM, Units.val_one]), ← hχ0, ← Units.val_pow_eq_pow_val, ← hχ1,
      map_mul, map_mul, map_inv _ g, mul_inv_cancel_comm, chiBar_val, chi1, chi1, hcχ]

end GlobalTheory.TypeLeaf.ConjPlace
