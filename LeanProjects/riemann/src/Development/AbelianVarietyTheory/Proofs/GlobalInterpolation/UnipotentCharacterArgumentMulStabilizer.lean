import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SandwichNormalForm
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SourceLatticeInvariance
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LatticeNormalFormUnipotent
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalFormAtPrime

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.QNormal

open Formalism.L2.Col

variable {E : Type} [Field E] [NumberField E] {K : Type} [Field K]

def IntV (P : HeightOneSpectrum (𝓞 E)) {N : ℕ} (v : Fin N → E) : Prop := ∀ l, IntAt P (v l)

def IntHom (P : HeightOneSpectrum (𝓞 E)) {a b : ℕ} (y : (Fin a → E) →ₗ[E] (Fin b → E)) : Prop :=
  ∀ v, IntV P v → IntV P (y v)

def HomBdd (P : HeightOneSpectrum (𝓞 E)) (N : ℕ) {a b : ℕ} (Psi : Loc.SF E K a b) : Prop :=
  (∀ x, Psi x ≠ 0 → IntHom P (((qOf P : E) ^ N) • x)) ∧
    ∀ x y, IntHom P y → Psi (x + ((qOf P : E) ^ N) • y) = Psi x

def FunBdd (P : HeightOneSpectrum (𝓞 E)) (N : ℕ) {ι : Type} (f : (ι → E) → K) : Prop :=
  (∀ t, f t ≠ 0 → ∀ i, IntAt P ((qOf P : E) ^ N * t i)) ∧
    ∀ t u : ι → E, (∀ i, IntAt P (u i)) → f (t + ((qOf P : E) ^ N) • u) = f t

def CharTo (P : HeightOneSpectrum (𝓞 E)) (D : ℕ) (psi : E → K) : Prop :=
  (∀ x y : E, IntAt P ((qOf P : E) ^ D * x) → IntAt P ((qOf P : E) ^ D * y) → psi (x + y) = psi x * psi y) ∧
    ∀ x : E, IntAt P x → psi x = 1

def boxSum (P : HeightOneSpectrum (𝓞 E)) (A B : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι] (f : (ι → E) → K) : K :=
  (((qOf P : K) ^ B)⁻¹) ^ Fintype.card ι * ∑ t ∈ Fintype.piFinset fun _ : ι => LocE.valsQ E (qOf P) A B, f t

def integrand (psi : E → K) {n' c' n c : ℕ} (Psi : Loc.SF E K (n' + c') (n + c)) (xj : (Fin n' → E) →ₗ[E] (Fin n → E))
    (t : Loc.FC n' c' n c → E) : K :=
  Psi (Loc.xx1 xj t) * psi (-Loc.chArg (Loc.xx1 xj t))

def UnfNe (P : HeightOneSpectrum (𝓞 E)) (psi : E → K) {n' c' n c : ℕ} (Psi : Loc.SF E K (n' + c') (n + c)) : Prop :=
  ∃ A₀ B₀ : ℕ, ∀ A B, A₀ ≤ A → B₀ ≤ B → IndefiniteRowSideFullHecke.SourceLatticeInvariance.unfoldAB P psi A B Psi ≠ 0

theorem IntV.zero (P : HeightOneSpectrum (𝓞 E)) {N : ℕ} : IntV P (0 : Fin N → E) := fun _ => IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P

theorem IntV.add {P : HeightOneSpectrum (𝓞 E)} {N : ℕ} {v w : Fin N → E} (hv : IntV P v) (hw : IntV P w) : IntV P (v + w) :=
  fun l => (hv l).add (hw l)

theorem IntV.neg {P : HeightOneSpectrum (𝓞 E)} {N : ℕ} {v : Fin N → E} (hv : IntV P v) : IntV P (-v) :=
  fun l => IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_neg (hv l)

theorem IntV.smul {P : HeightOneSpectrum (𝓞 E)} {N : ℕ} {u : E} {v : Fin N → E} (hu : IntAt P u) (hv : IntV P v) :
    IntV P (u • v) := fun l => hu.mul (hv l)

theorem intAt_one (P : HeightOneSpectrum (𝓞 E)) : IntAt P (1 : E) := by simpa using IntAt.coe P 1

theorem intAt_sum {P : HeightOneSpectrum (𝓞 E)} {ι : Type} (s : Finset ι) (f : ι → E) (h : ∀ i ∈ s, IntAt P (f i)) :
    IntAt P (∑ i ∈ s, f i) :=
  Finset.sum_induction f (IntAt P) (fun _ _ => IntAt.add) (IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P) h

theorem intV_single (P : HeightOneSpectrum (𝓞 E)) {N : ℕ} (s : Fin N) : IntV P (Pi.single s (1 : E) : Fin N → E) := by
  intro l
  rw [Pi.single_apply]
  split_ifs
  · exact intAt_one P
  · exact IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P

theorem intHom_iff {P : HeightOneSpectrum (𝓞 E)} {a b : ℕ} (y : (Fin a → E) →ₗ[E] (Fin b → E)) :
    IntHom P y ↔ ∀ s l, IntAt P (y (Pi.single s 1) l) := by
  refine ⟨fun h s l => h _ (intV_single P s) l, fun h v hv l => ?_⟩
  have e : y v = ∑ s, v s • y (Pi.single s 1) := by
    conv_lhs => rw [show v = ∑ s, v s • (Pi.single s (1 : E) : Fin a → E) from by
      funext k
      simp [Finset.sum_apply, Pi.single_apply]]
    simp only [map_sum, map_smul]
  rw [e, Finset.sum_apply]
  exact intAt_sum _ _ fun s _ => (hv s).mul (h s l)

theorem mem_stdAt_iff [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {N : ℕ} (v : Fin N → E) : v ∈ stdAt E N P ↔ IntV P v :=
  mem_localization_standardLattice P v

open Classical in

example (P : HeightOneSpectrum (𝓞 E)) (a b : ℕ) :
    HomBdd P 0 (fun x : (Fin a → E) →ₗ[E] (Fin b → E) => if IntHom P x then (1 : K) else 0) := by
  refine ⟨fun x hx => ?_, fun x y hy => ?_⟩
  · by_contra h
    rw [pow_zero, one_smul] at h
    simp [h] at hx
  · have : IntHom P (x + y) ↔ IntHom P x := by
      refine ⟨fun h v hv => ?_, fun h v hv => (h v hv).add (hy v hv)⟩
      have := (h v hv).add (hy v hv).neg
      simpa using this
    simp [this]

section Flags

variable {F : Type} [Field F] {n c : ℕ}

theorem inX_apply (x : Fin n → F) (l : Fin (n + c)) : Loc.inX F n c x l = if h : l.1 < n then x ⟨l.1, h⟩ else 0 := by
  unfold Loc.inX
  rw [LinearMap.pi_apply]
  split_ifs <;> simp

theorem mem_Ufl {i : ℕ} {v : Fin (n + c) → F} : v ∈ Loc.Ufl F n c i ↔ ∀ l : Fin (n + c), ¬ l.1 < n + i → v l = 0 := Iff.rfl

theorem inX_mem_Ufl (i : ℕ) (x : Fin n → F) : Loc.inX F n c x ∈ Loc.Ufl F n c i :=
  mem_Ufl.2 fun l hl => by rw [inX_apply, dif_neg (by omega)]

theorem Ufl_mono {i j : ℕ} (h : i ≤ j) : Loc.Ufl F n c i ≤ Loc.Ufl F n c j :=
  fun _ hv => mem_Ufl.2 fun l hl => mem_Ufl.1 hv l (by omega)

theorem eN_mem_Ufl {i s : ℕ} (h : s < n + i) : Loc.eN F (n + c) s ∈ Loc.Ufl F n c i :=
  mem_Ufl.2 fun l hl => by
    unfold Loc.eN
    rw [if_neg (by omega)]

theorem inX_castAdd (x : Fin n → F) (a : Fin n) : Loc.inX F n c x (Fin.castAdd c a) = x a := by
  rw [inX_apply, dif_pos (by simp)]
  rfl

theorem inX_of_mem_Ufl {v : Fin (n + c) → F} (hv : v ∈ Loc.Ufl F n c 0) :
    Loc.inX F n c (fun a => v (Fin.castAdd c a)) = v := by
  funext l
  rw [inX_apply]
  split_ifs with h
  · rfl
  · exact (mem_Ufl.1 hv l (by omega)).symm

theorem inX_injective : Function.Injective (Loc.inX F n c) := fun x y h => by
  funext a
  rw [← inX_castAdd (c := c) x, h, inX_castAdd]

theorem exists_res {r : (Fin (n + c) → F) ≃ₗ[F] (Fin (n + c) → F)} (hr : r ∈ Loc.R1 F n c) :
    ∃ γ : (Fin n → F) ≃ₗ[F] (Fin n → F), ∀ x, r (Loc.inX F n c x) = Loc.inX F n c (γ x) := by
  have key : ∀ s : (Fin (n + c) → F) ≃ₗ[F] (Fin (n + c) → F), Loc.R1cond F n c s → ∀ x,
      Loc.inX F n c ((LinearMap.funLeft F F (Fin.castAdd c) ∘ₗ s.toLinearMap ∘ₗ Loc.inX F n c) x) = s (Loc.inX F n c x) :=
    fun s hs x => inX_of_mem_Ufl (hs.1 0 _ (inX_mem_Ufl 0 x))
  refine ⟨LinearEquiv.ofLinear (LinearMap.funLeft F F (Fin.castAdd c) ∘ₗ r.toLinearMap ∘ₗ Loc.inX F n c)
    (LinearMap.funLeft F F (Fin.castAdd c) ∘ₗ (r⁻¹).toLinearMap ∘ₗ Loc.inX F n c) ?_ ?_, fun x => (key r hr.1 x).symm⟩
  · refine LinearMap.ext fun x => inX_injective (c := c) ?_
    rw [LinearMap.comp_apply, key r hr.1, key r⁻¹ hr.2]
    exact r.apply_symm_apply _
  · refine LinearMap.ext fun x => inX_injective (c := c) ?_
    rw [LinearMap.comp_apply, key r⁻¹ hr.2, key r hr.1]
    exact r.symm_apply_apply _

theorem atN_add {N : ℕ} (v w : Fin N → F) (i : ℕ) : Loc.atN (v + w) i = Loc.atN v i + Loc.atN w i := by
  unfold Loc.atN
  split_ifs <;> simp

theorem atN_sub {N : ℕ} (v w : Fin N → F) (i : ℕ) : Loc.atN (v - w) i = Loc.atN v i - Loc.atN w i := by
  unfold Loc.atN
  split_ifs <;> simp

theorem atN_smul {N : ℕ} (a : F) (v : Fin N → F) (i : ℕ) : Loc.atN (a • v) i = a * Loc.atN v i := by
  unfold Loc.atN
  split_ifs <;> simp

theorem atN_of_mem_Ufl {i : ℕ} {v : Fin (n + c) → F} (hv : v ∈ Loc.Ufl F n c i) : Loc.atN v (n + i) = 0 := by
  unfold Loc.atN
  split_ifs with h
  · exact mem_Ufl.1 hv _ (by simp)
  · rfl

theorem atN_of_R1cond {r : (Fin (n + c) → F) ≃ₗ[F] (Fin (n + c) → F)} (hr : Loc.R1cond F n c r) {i : ℕ}
    {v : Fin (n + c) → F} (hv : v ∈ Loc.Ufl F n c (i + 1)) : Loc.atN (r v) (n + i) = Loc.atN v (n + i) := by
  have h1 : v - Loc.atN v (n + i) • Loc.eN F (n + c) (n + i) ∈ Loc.Ufl F n c i := mem_Ufl.2 fun l hl => by
    simp only [Pi.sub_apply, Pi.smul_apply, Loc.eN, smul_eq_mul]
    split_ifs with h
    · unfold Loc.atN
      rw [dif_pos (h ▸ l.2), mul_one, sub_eq_zero]
      congr 1
      exact Fin.ext h
    · rw [mem_Ufl.1 hv l (by omega)]
      simp
  have h2 := atN_of_mem_Ufl (hr.1 i _ h1)
  have h3 := atN_of_mem_Ufl (hr.2.2 i)
  have h4 := atN_of_mem_Ufl h1
  rw [map_sub, map_smul, atN_sub, atN_smul] at h2
  rw [atN_sub] at h3
  rw [atN_sub, atN_smul] at h4
  linear_combination h2 - h4 + Loc.atN v (n + i) * h3

theorem unipotentCharacterArgument_mul_stabilizer {r s : (Fin (n + c) → F) ≃ₗ[F] (Fin (n + c) → F)} (hr : Loc.R1cond F n c r) (hs : Loc.R1cond F n c s) :
    Loc.n1Arg (r * s) = Loc.n1Arg r + Loc.n1Arg s := by
  unfold Loc.n1Arg
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 := atN_of_R1cond hr (hs.2.2 (i + 1))
  have h2 : Loc.atN (Loc.eN F (n + c) (n + (i + 1))) (n + i) = 0 := by
    unfold Loc.atN Loc.eN
    split_ifs with h h'
    · simp at h'
    · rfl
    · rfl
  rw [map_sub, atN_sub, atN_sub, h2] at h1
  change Loc.atN (r (s (Loc.eN F (n + c) (n + (i + 1))))) (n + i) =
    Loc.atN (r (Loc.eN F (n + c) (n + (i + 1)))) (n + i) + Loc.atN (s (Loc.eN F (n + c) (n + (i + 1)))) (n + i)
  linear_combination h1

theorem linearMap_unfolding_apply_single {n' c' : ℕ} (xj : (Fin n' → F) →ₗ[F] (Fin n → F)) (t : Loc.FC n' c' n c → F) (s : Fin (n' + c'))
    (l : Fin (n + c)) : Loc.xx1 xj t (Pi.single s 1) l =
      if hf : Loc.IsFree n' n c l.1 s.1 then t ⟨(l, s), hf⟩
      else if hs : s.1 < n' then (if hl : l.1 < n then xj (Pi.single ⟨s.1, hs⟩ 1) ⟨l.1, hl⟩ else 0)
      else if l.1 = n + (s.1 - n') then 1 else 0 := by
  unfold Loc.xx1
  rw [Matrix.toLin'_apply, Matrix.mulVec_single_one]
  simp only [Matrix.col_apply, Matrix.of_apply, LinearMap.toMatrix'_apply]

theorem unfoldingAffinePointMap_apply_inclusion {n' c' : ℕ} (xj : (Fin n' → F) →ₗ[F] (Fin n → F)) (t : Loc.FC n' c' n c → F) (v : Fin n' → F) :
    Loc.xx1 xj t (Loc.inX F n' c' v) = Loc.inX F n c (xj v) := by
  have : Loc.xx1 xj t ∘ₗ Loc.inX F n' c' = Loc.inX F n c ∘ₗ xj := by
    refine LinearMap.pi_ext' fun a => LinearMap.ext_ring ?_
    have e : Loc.inX F n' c' (Pi.single a 1) = Pi.single (Fin.castAdd c' a) 1 := by
      funext l
      rw [inX_apply, Pi.single_apply]
      split_ifs with h1 h2 h2
      · subst h2
        simp
      · rw [Pi.single_apply, if_neg]
        rintro rfl
        exact h2 rfl
      · subst h2
        simp at h1
      · rfl
    funext l
    change Loc.xx1 xj t (Loc.inX F n' c' (Pi.single a 1)) l = Loc.inX F n c (xj (Pi.single a 1)) l
    rw [e, linearMap_unfolding_apply_single, dif_neg (fun h => by have := h.1; have := a.2; simp at *; omega), dif_pos (by simp), inX_apply]
    rfl
  exact LinearMap.congr_fun this v

end Flags

end GlobalTheory.QNormal
