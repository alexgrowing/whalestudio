import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.TwistedGLMassFormulaStatement

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.MassU

theorem grp_iff {G : Type} [Group G] (τ : G →* G) (hτ : ∀ g, τ (τ g) = g) (B γ z : G) (hz : ∀ g, g * z = z * g)
    (hN : B * τ B = γ * z) (hB : ∀ g, g * γ = γ * g → g * B = B * g) (g : G) :
    g * B = B * τ g ↔ τ g = g ∧ g * γ = γ * g := by
  constructor
  · intro h
    have h1 : τ g * τ B = τ B * g := by simpa [hτ] using congrArg τ h
    have h2 : g * (B * τ B) = (B * τ B) * g := by rw [← mul_assoc, h, mul_assoc, h1, mul_assoc]
    rw [hN, mul_assoc γ z g, ← hz g, ← mul_assoc, ← mul_assoc] at h2
    have h3 := mul_right_cancel h2
    exact ⟨(mul_left_cancel ((hB g h3).symm.trans h)).symm, h3⟩
  · rintro ⟨h1, h2⟩
    rw [h1, hB g h2]

section Ring

variable {R S : Type} [CommRing R] [CommRing S] {n : ℕ}

def tau (n : ℕ) (c : R →+* R) : GL (Fin n) R →* GL (Fin n) R := (invT n R).comp (GeneralLinearGroup.map c)

theorem theta_eq (c : R →+* R) (g : GL (Fin n) R) : thetaGL n c g = PhiU n R * tau n c g * (PhiU n R)⁻¹ := rfl

theorem tau_inv_val (c : R →+* R) (g : GL (Fin n) R) : ((tau n c g)⁻¹).val = cT c g.val := rfl

theorem tau_val (c : R →+* R) (g : GL (Fin n) R) : (tau n c g).val = cT c (g⁻¹).val := rfl

theorem tau_tau (c : R →+* R) (hc : ∀ x, c (c x) = x) (g : GL (Fin n) R) : tau n c (tau n c g) = g := by
  apply Units.ext
  rw [tau_val, tau_inv_val]
  ext i j
  exact hc _

theorem tau_eq_iff (c : R →+* R) (g : GL (Fin n) R) : tau n c g = g ↔ cT c g.val * g.val = 1 := by
  rw [← tau_inv_val, ← Units.val_mul, Units.val_eq_one, inv_mul_eq_one]

theorem map_tau (p : R →+* S) (c : R →+* R) (d : S →+* S) (h : ∀ y, p (c y) = d (p y)) (g : GL (Fin n) R) :
    GeneralLinearGroup.map p (tau n c g) = tau n d (GeneralLinearGroup.map p g) := by
  apply Units.ext
  ext i j
  exact h _

theorem map_PhiU (p : R →+* S) : GeneralLinearGroup.map p (PhiU n R) = PhiU n S := by
  apply Units.ext
  ext i j
  change p (GlobalTheory.Tw.Phi n R i j) = GlobalTheory.Tw.Phi n S i j
  simp only [GlobalTheory.Tw.Phi, Matrix.of_apply]
  split_ifs <;> simp

theorem tau_PhiU (c : R →+* R) : tau n c (PhiU n R) = PhiU n R := by
  change invT n R (GeneralLinearGroup.map c (PhiU n R)) = _
  rw [map_PhiU]
  exact Units.ext (Matrix.transpose_transpose _)

theorem Phi_transpose : (GlobalTheory.Tw.Phi n R)ᵀ = (-1 : R) ^ (n + 1) • GlobalTheory.Tw.Phi n R := by
  ext i j
  simp only [GlobalTheory.Tw.Phi, Matrix.of_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul]
  by_cases h : (i : ℕ) + j + 1 = n
  · rw [if_pos h, if_pos (by omega), ← pow_add, show n + 1 + i = j + 2 * (i + 1) by omega, pow_add, pow_mul]
    simp
  · rw [if_neg h, if_neg (by omega), mul_zero]

theorem PhiU_sq : (PhiU n R * PhiU n R).val = (-1 : R) ^ (n + 1) • (1 : Matrix (Fin n) (Fin n) R) := by
  rw [← Phi_mul_transpose n R, Phi_transpose, mul_smul_comm, smul_smul, ← mul_pow]
  simp [PhiU]

theorem PhiU_sq_comm (g : GL (Fin n) R) : g * (PhiU n R * PhiU n R) = (PhiU n R * PhiU n R) * g := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul _ g, PhiU_sq]
  simp

theorem mem_twCent (c : R →+* R) (B g : GL (Fin n) R) :
    g ∈ twCent (thetaGL n c) (B * (PhiU n R)⁻¹) ↔ g * B = B * tau n c g := by
  change g * (B * (PhiU n R)⁻¹) = B * (PhiU n R)⁻¹ * thetaGL n c g ↔ _
  rw [theta_eq, ← mul_assoc, ← mul_assoc, mul_left_inj]
  simp only [mul_assoc, inv_mul_cancel_left]

theorem norm_eq (c : R →+* R) (B γ : GL (Fin n) R) (h : B * tau n c B = γ * (PhiU n R * PhiU n R)) :
    B * (PhiU n R)⁻¹ * thetaGL n c (B * (PhiU n R)⁻¹) = γ := by
  rw [theta_eq, map_mul, map_inv, tau_PhiU]
  calc _ = B * tau n c B * (PhiU n R * PhiU n R)⁻¹ := by group
    _ = γ := by rw [h, mul_inv_cancel_right]

end Ring

theorem exists_B {K : Type} [Field K] [CharZero K] {n : ℕ} (c : K →+* K) (hc : ∀ x, c (c x) = x) (s : K) (hs : c s ≠ s)
    (γ : GL (Fin n) K) (hγ : cT c γ.val * γ.val = 1) :
    ∃ (B : GL (Fin n) K) (a b : K), B.val = a • 1 + b • γ.val ∧ B * tau n c B = γ * (PhiU n K * PhiU n K) := by
  set ε : K := (-1) ^ (n + 1) with hε
  have hε2 : ε * ε = 1 := by rw [hε, ← mul_pow]; simp
  have hcε : c ε = ε := by simp [hε]
  have h0 : ∀ m : ℕ, (m : K) + c s ≠ 0 := fun m h => hs (by
    have h' := congrArg c h
    rw [map_add, map_natCast, hc, map_zero] at h'
    linear_combination h - h')
  have hinj : Function.Injective fun m : ℕ => ((m : K) + s) / ((m : K) + c s) := fun m k h => by
    simp only at h
    rw [div_eq_div_iff (h0 m) (h0 k)] at h
    have : ((m : K) - k) * (c s - s) = 0 := by linear_combination h
    exact_mod_cast sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hs))
  obtain ⟨_, ⟨m, rfl⟩, hm⟩ := (Set.infinite_range_of_injective hinj).exists_notMem_finset
    ((-ε) • γ.val).charpoly.roots.toFinset
  rw [Multiset.mem_toFinset, mem_roots (Matrix.charpoly_monic _).ne_zero, IsRoot.def, Matrix.eval_charpoly] at hm
  beta_reduce at hm
  set a : K := m + s with ha
  have hca : c a = m + c s := by simp [ha]
  rw [← hca] at hm
  have hca0 : c a ≠ 0 := hca ▸ h0 m
  have hB : a • (1 : Matrix (Fin n) (Fin n) K) + (ε * c a) • γ.val =
      c a • (Matrix.scalar (Fin n) (a / c a) - (-ε) • γ.val) := by
    rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, smul_sub, smul_smul, smul_smul, mul_div_cancel₀ _ hca0]
    module
  have hdet : (a • (1 : Matrix (Fin n) (Fin n) K) + (ε * c a) • γ.val).det ≠ 0 := by
    rw [hB, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hca0) hm
  refine ⟨GeneralLinearGroup.mkOfDetNeZero _ hdet, a, ε * c a, rfl, ?_⟩
  rw [← eq_mul_inv_iff_mul_eq]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, PhiU_sq, tau_inv_val]
  change a • (1 : Matrix (Fin n) (Fin n) K) + (ε * c a) • γ.val =
    γ.val * ε • (1 : Matrix (Fin n) (Fin n) K) * cT c (a • (1 : Matrix (Fin n) (Fin n) K) + (ε * c a) • γ.val)
  have e : cT c (a • (1 : Matrix (Fin n) (Fin n) K) + (ε * c a) • γ.val) = c a • 1 + (ε * a) • cT c γ.val := by
    ext i j
    simp only [cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add,
      map_mul, hcε, hc, Matrix.one_apply, apply_ite c, map_one, map_zero, eq_comm (a := j)]
  rw [e, mul_smul_comm, mul_one, smul_mul_assoc, mul_add, mul_smul_comm, mul_smul_comm, mul_one, mul_eq_one_comm.1 hγ,
    smul_add, smul_smul, smul_smul, ← mul_assoc, hε2, one_mul, add_comm]

section Adelic

open GlobalTheory.DefU.ClassFin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem conjFin_conjFin (x : Af E) : conjFin (cc E) (conjFin (cc E) x) = x := by
  obtain ⟨y, rfl⟩ := (GlobalTheory.LFun.finAdEquiv (Fr E) E).surjective x
  change conjFin (cc E) (conjFin (cc E) (AEq y)) = AEq y
  rw [← AEq_sig, ← AEq_sig]
  congr 1
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a x =>
    change a ⊗ₜ[Fr E] (IsCMField.complexConj E (IsCMField.complexConj E x)) = _
    rw [IsCMField.complexConj_apply_apply]

def pU : finU E n →* GL (Fin n) (Af E) :=
  ((GeneralLinearGroup.map (pFin E)).comp (UA E n).subtype).comp (finU E n).subtype

theorem finGL_pU (k : finU E n) : finGL E n (pU k) = k.1.1 := finGL_pFin k

theorem pU_injective : Function.Injective (pU (E := E) (n := n)) := fun a b h =>
  Subtype.ext (Subtype.ext (by rw [← finGL_pU, h, finGL_pU]))

theorem continuous_pU : Continuous (pU (E := E) (n := n)) :=
  (Continuous.units_map _ (continuous_id.matrix_map (continuous_snd : Continuous (pFin E)))).comp
    (continuous_subtype_val.comp continuous_subtype_val)

theorem tau_pU (k : finU E n) : tau n (conjFin (cc E)) (pU k) = pU k := (tau_eq_iff _ _).2 (cT_pFin k.1)

def sU (g : GL (Fin n) (Af E)) (h : tau n (conjFin (cc E)) g = g) : finU E n :=
  ⟨⟨finGL E n g, finGL_mem_UA _ ((tau_eq_iff _ _).1 h)⟩, pInf_finGL _⟩

theorem pU_sU (g : GL (Fin n) (Af E)) (h : tau n (conjFin (cc E)) g = g) : pU (sU g h) = g := pFin_finGL g

theorem ratF_tau (g : GL (Fin n) E) :
    ratF E n (tau n (cc E).toRingHom g) = tau n (conjFin (cc E)) (ratF E n g) :=
  map_tau _ _ _ (fun y => (conjFin_algebraMap (cc E) y).symm) g

theorem mem_UE (g : GL (Fin n) E) : g ∈ UE E n ↔ tau n (cc E).toRingHom g = g := by
  rw [tau_eq_iff]
  change cT _ g.val * 1 * g.val = 1 ↔ _
  rw [mul_one]

theorem ratF_injective : Function.Injective (ratF E n) := fun a b h => by
  apply Units.ext
  ext i j
  obtain ⟨w⟩ : Nonempty (HeightOneSpectrum (𝓞 E)) := by
    obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 E)
    exact ⟨⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField E)⟩⟩
  haveI : Nontrivial (Af E) := (pLoc E w).domain_nontrivial
  have h' : (ratF E n a).val = (ratF E n b).val := congrArg Units.val h
  exact (algebraMap E (Af E)).injective (congrFun₂ h' i j)

theorem pU_finPt (γ : UE E n) : pU (finPt γ) = ratF E n γ.1 := by
  have h : tau n (conjFin (cc E)) (ratF E n γ.1) = ratF E n γ.1 := by rw [← ratF_tau, (mem_UE _).1 γ.2]
  have e : finPt γ = sU _ h := by
    have h1 : toSub (UA E n) (finGL E n (ratF E n γ.1)) = (sU _ h).1 := dif_pos (sU _ h).1.2
    rw [finPt, h1]
    exact dif_pos (sU _ h).2
  rw [e, pU_sU]

theorem mem_ratFinU (k : finU E n) : k ∈ ratFinU E n ↔ pU k ∈ (ratF E n).range := by
  constructor
  · rintro ⟨g, -, hg⟩
    exact ⟨g, (pFin_finGL _).symm.trans (congrArg (GeneralLinearGroup.map (pFin E)) hg)⟩
  · rintro ⟨g, hg⟩
    refine ⟨g, (mem_UE g).2 (ratF_injective ?_), (congrArg (finGL E n) hg).trans (finGL_pU k)⟩
    rw [ratF_tau, hg, tau_pU]

def centEquiv (x : finU E n) (δ : GL (Fin n) (Af E))
    (h : ∀ g, g ∈ twCent (thF E n) δ ↔ tau n (conjFin (cc E)) g = g ∧ g * pU x = pU x * g) :
    twCent (MonoidHom.id (finU E n)) x ≃ₜ* twCent (thF E n) δ where
  toFun t := ⟨pU t.1, (h _).2 ⟨tau_pU _, by
    have ht : t.1 * x = x * t.1 := t.2
    rw [← map_mul, ht, map_mul]⟩⟩
  invFun g := ⟨sU g.1 ((h _).1 g.2).1, pU_injective (by
    rw [MonoidHom.id_apply, map_mul, map_mul, pU_sU]
    exact ((h _).1 g.2).2)⟩
  left_inv t := Subtype.ext (pU_injective (pU_sU _ (tau_pU t.1)))
  right_inv g := Subtype.ext (pU_sU _ ((h _).1 g.2).1)
  map_mul' a b := Subtype.ext (map_mul pU a.1 b.1)
  continuous_toFun := Continuous.subtype_mk (continuous_pU.comp continuous_subtype_val) _
  continuous_invFun := Continuous.subtype_mk (Continuous.subtype_mk (Continuous.subtype_mk
    (continuous_finGL.comp continuous_subtype_val) _) _) _

theorem isClosed_twCent {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] (θ : G →* G)
    (hθ : Continuous θ) (δ : G) : IsClosed (twCent θ δ : Set G) :=
  isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul hθ)

theorem continuous_thF : Continuous (thF E n) := by
  have h : Continuous (tau n (conjFin (cc E))) := Units.continuous_iff.2
    ⟨(Units.continuous_coe_inv.matrix_map (continuous_conjFin _)).matrix_transpose,
      (Units.continuous_val.matrix_map (continuous_conjFin _)).matrix_transpose⟩
  exact (continuous_const.mul h).mul continuous_const

theorem exists_norm (γ : UE E n) : ∃ δ : GL (Fin n) E, δ * thE E n δ = γ.1 ∧
    mass (MonoidHom.id _) (ratFinU E n) (finPt γ) = mass (thF E n) (ratF E n).range (ratF E n δ) := by
  obtain ⟨s, hs⟩ := DFunLike.ne_iff.1 (IsCMField.complexConj_ne_one E)
  obtain ⟨B, a, b, hB, hN⟩ := exists_B (cc E).toRingHom (IsCMField.complexConj_apply_apply E) s hs γ.1
    ((tau_eq_iff _ _).1 ((mem_UE _).1 γ.2))
  refine ⟨B * (PhiU n E)⁻¹, norm_eq _ B γ.1 hN, ?_⟩
  have hΦ : ratF E n (PhiU n E) = PhiU n (Af E) := map_PhiU _
  haveI : T2Space (Af E) := inferInstanceAs (T2Space (RestrictedProduct _ _ _))
  haveI : T2Space (GL (Fin n) (Af E)) := Units.isEmbedding_embedProduct.t2Space
  haveI : T2Space (finU E n) := T2Space.of_injective_continuous pU_injective continuous_pU
  refine GlobalTheory.T.twistedCentralizerMass_eq_of_topEquiv _ _ _ _ _ _ _ _ (isClosed_twCent _ continuous_id _) (isClosed_twCent _ continuous_thF _)
    (centEquiv (finPt γ) (ratF E n (B * (PhiU n E)⁻¹)) fun g => ?_) fun t => mem_ratFinU t.1
  rw [map_mul, map_inv, hΦ, pU_finPt]
  refine (mem_twCent _ _ g).trans (grp_iff _ (tau_tau _ conjFin_conjFin) _ _ _ PhiU_sq_comm ?_ (fun g hg => ?_) g)
  · rw [← ratF_tau, ← map_mul, hN, map_mul, map_mul, hΦ]
  · have e : (ratF E n B).val = algebraMap E (Af E) a • 1 + algebraMap E (Af E) b • (ratF E n γ.1).val := by
      change B.val.map _ = _ + _ • γ.1.val.map _
      rw [hB]
      ext i j
      simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul, Matrix.one_apply,
        apply_ite (algebraMap E (Af E)), map_one, map_zero]
    have hg' : g.val * (ratF E n γ.1).val = (ratF E n γ.1).val * g.val := congrArg Units.val hg
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, e, mul_add, add_mul, mul_smul_comm, mul_smul_comm, smul_mul_assoc, smul_mul_assoc,
      hg', mul_one, one_mul]

end Adelic

theorem mass_unitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ γ : UE E n, γ.1.val.charpoly ∈ Ell E n → mass (MonoidHom.id _) (ratFinU E n) (finPt γ) = kap γ.1.val.charpoly * 2 ^ nfac γ.1.val.charpoly := by
  intro E _ _ _ hE n _ γ hγ
  obtain ⟨δ, hδ, hm⟩ := exists_norm γ
  rw [hm, ← hδ]
  exact GlobalTheory.T.twisted_GL_mass_formula E hE n δ (hδ ▸ hγ)

end GlobalTheory.BCT.MassU
