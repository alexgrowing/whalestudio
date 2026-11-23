import Formalism.WachLatticeTwists.RealDisplaySplitting.GaloisTheoremThirdForms

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

open Finset Classical

noncomputable section

namespace Formalism.MainNotions.N.K

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.SF

section Ko
variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem ko_faithful (c : O) (h : ∀ z : KO O, c • z = 0) : c = 0 := by
  by_contra hc
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  let ι := algebraMap O (FractionRing O)
  have hc' : ι c ≠ 0 := fun h0 => hc (IsFractionRing.injective O (FractionRing O) (h0.trans (map_zero ι).symm))
  have hϖ' : ι ϖ ≠ 0 := fun h0 => hϖ0 (IsFractionRing.injective O (FractionRing O) (h0.trans (map_zero ι).symm))
  have h1 := h (Submodule.Quotient.mk ((ι c * ι ϖ)⁻¹))
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Algebra.smul_def, mul_inv,
    ← mul_assoc, mul_inv_cancel₀ hc', one_mul] at h1
  obtain ⟨o, ho⟩ := Submodule.mem_one.1 h1
  apply hϖ.not_isUnit
  refine isUnit_iff_exists_inv.2 ⟨o, IsFractionRing.injective O (FractionRing O) ?_⟩
  rw [map_mul, map_one]
  change ι ϖ * ι o = 1
  rw [ho, mul_inv_cancel₀ hϖ']

end Ko

section Blocks
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {A : Type} [Ring A] [Algebra O A]
  {n : Type} [Fintype n] [DecidableEq n]

theorem latQ_act (ρ : A →ₐ[O] Matrix n n O) (x : A) (m : LatQ O n ρ.toRingHom) (i : n) :
    (x • m) i = ∑ j, ρ x i j • (m j : KO O) := rfl

theorem mat_eq_of_act (ρ : A →ₐ[O] Matrix n n O) (x : A) (y : O)
    (h : ∀ m : LatQ O n ρ.toRingHom, x • m = y • m) : ρ x = y • (1 : Matrix n n O) := by
  ext i j
  apply sub_eq_zero.1
  apply ko_faithful O
  intro z
  have h1 := congrFun (h (Pi.single j z : n → KO O)) i
  change ∑ j', ρ x i j' • (Pi.single j z : n → KO O) j' = y • (Pi.single j z : n → KO O) i at h1
  rw [Finset.sum_eq_single j (fun b _ hb => by simp [hb]) (by simp)] at h1
  have h2 : ρ x i j • z = y • (Pi.single j z : n → KO O) i := by
    have h3 := h1
    rwa [Pi.single_eq_same] at h3
  rw [sub_smul, h2, Matrix.smul_apply, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

theorem act_trace (ρ : A →ₐ[O] Matrix n n O) (h1 : Fintype.card n = 1) (x : A) (m : LatQ O n ρ.toRingHom) :
    x • m = (ρ x).trace • m := by
  obtain ⟨i0, hi0⟩ := Fintype.card_eq_one_iff.1 h1
  funext i
  rw [latQ_act]
  change _ = (ρ x).trace • (m i : KO O)
  have hu : ∀ j : n, j = i := fun j => (hi0 j).trans (hi0 i).symm
  rw [Finset.sum_eq_single i (fun b _ hb => absurd (hu b) hb) (by simp), Matrix.trace,
    Finset.sum_eq_single i (fun b _ hb => absurd (hu b) hb) (by simp)]
  rfl

end Blocks

section ZlStr
variable {ℓ : ℕ} [Fact ℓ.Prime]

abbrev zlMod (O : Type) [CommRing O] [Algebra ℤ_[ℓ] O] (M : Type) [AddCommGroup M] [Module O M] : Module ℤ_[ℓ] M :=
  Module.compHom M (algebraMap ℤ_[ℓ] O)

theorem zlTower (O : Type) [CommRing O] [Algebra ℤ_[ℓ] O] (M : Type) [AddCommGroup M] [Module O M] :
    @IsScalarTower ℤ_[ℓ] O M _ _ (zlMod O M).toSMul :=
  @IsScalarTower.mk ℤ_[ℓ] O M _ _ (zlMod O M).toSMul fun a b m => by
    show (a • b) • m = algebraMap ℤ_[ℓ] O a • (b • m)
    rw [Algebra.smul_def, mul_smul]

end ZlStr

section Lat
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {A : Type} [Ring A] [Algebra O A]
  {n : Type} [Fintype n] [DecidableEq n]

instance {ℓ : ℕ} [Fact ℓ.Prime] [Algebra ℤ_[ℓ] O] (ρ : A →ₐ[O] Matrix n n O) :
    Module ℤ_[ℓ] (LatM O O n ρ.toRingHom) := zlMod O _
instance {ℓ : ℕ} [Fact ℓ.Prime] [Algebra ℤ_[ℓ] O] (ρ : A →ₐ[O] Matrix n n O) :
    IsScalarTower ℤ_[ℓ] O (LatM O O n ρ.toRingHom) := zlTower O _

def vOne (ρ : A →ₐ[O] Matrix n n O) (e₁ : A) (h : SurjectionRankOneIdempotent O A n ρ.toRingHom e₁) : LatM O O n ρ.toRingHom := h.choose

theorem vOne_spec (ρ : A →ₐ[O] Matrix n n O) (e₁ : A) (h : SurjectionRankOneIdempotent O A n ρ.toRingHom e₁) :
    (∀ (a : A) v x, tensM O n ρ.toRingHom (a • v) x = a • tensM O n ρ.toRingHom v x) ∧
    (∀ m : LatQ O n ρ.toRingHom, e₁ • m = m → ∃ x, m = tensM O n ρ.toRingHom (vOne ρ e₁ h) x) ∧
    (∀ (a : A) v, iLM O n ρ.toRingHom (a • v) = a • iLM O n ρ.toRingHom v) ∧
    (∀ (a : A) v, qVM O n ρ.toRingHom (a • v) = a • qVM O n ρ.toRingHom v) ∧
    (∀ v (x : FractionRing O), tensM O n ρ.toRingHom v (Submodule.Quotient.mk x) =
      qVM O n ρ.toRingHom (x • iLM O n ρ.toRingHom v)) ∧
    Function.Injective (iLM O n ρ.toRingHom) ∧ Function.Surjective (qVM O n ρ.toRingHom) ∧
    LinearMap.ker (qVM O n ρ.toRingHom) = LinearMap.range (iLM O n ρ.toRingHom) ∧
    (∀ v : LatM O (FractionRing O) n ρ.toRingHom, ∃ c : O, c ≠ 0 ∧ c • v ∈ LinearMap.range (iLM O n ρ.toRingHom)) ∧
    e₁ • vOne ρ e₁ h = vOne ρ e₁ h ∧ (∀ v : LatM O O n ρ.toRingHom, ∃ c : A, (c * e₁) • vOne ρ e₁ h = v) :=
  h.choose_spec

end Lat

def LeftId (O : Type) [CommRing O] {A : Type} [Ring A] [Algebra O A] (x : A) : Type :=
  ↥(Submodule.span A ({x} : Set A))

section LeftId
variable (O : Type) [CommRing O] {A : Type} [Ring A] [Algebra O A] (x : A)

instance : AddCommGroup (LeftId O x) := inferInstanceAs (AddCommGroup ↥(Submodule.span A ({x} : Set A)))
instance : Module A (LeftId O x) := inferInstanceAs (Module A ↥(Submodule.span A ({x} : Set A)))
instance : Module O (LeftId O x) := inferInstanceAs (Module O ↥(Submodule.span A ({x} : Set A)))

def lv (p : LeftId O x) : A := @Subtype.val A (· ∈ Submodule.span A ({x} : Set A)) p

def lmk (a : A) (h : a ∈ Submodule.span A ({x} : Set A)) : LeftId O x := ⟨a, h⟩

theorem lv_lmk (a : A) (h : a ∈ Submodule.span A ({x} : Set A)) : lv O x (lmk O x a h) = a := rfl
theorem lv_add (p q : LeftId O x) : lv O x (p + q) = lv O x p + lv O x q := rfl
theorem lv_smul (c : O) (p : LeftId O x) : lv O x (c • p) = c • lv O x p := rfl
theorem lv_smulA (a : A) (p : LeftId O x) : lv O x (a • p) = a * lv O x p := rfl
theorem lv_mem (p : LeftId O x) : lv O x p ∈ Submodule.span A ({x} : Set A) := p.2

instance : SMulCommClass A O (LeftId O x) :=
  ⟨fun a c p => Subtype.ext (by
    show a * (c • lv O x p) = c • (a * lv O x p)
    exact mul_smul_comm c a _)⟩
instance {ℓ : ℕ} [Fact ℓ.Prime] [Algebra ℤ_[ℓ] O] : Module ℤ_[ℓ] (LeftId O x) := zlMod O _
instance {ℓ : ℕ} [Fact ℓ.Prime] [Algebra ℤ_[ℓ] O] : IsScalarTower ℤ_[ℓ] O (LeftId O x) := zlTower O _

def incl : LeftId O x →ₗ[A] A := (Submodule.span A ({x} : Set A)).subtype

theorem incl_apply (p : LeftId O x) : incl O x p = lv O x p := rfl

theorem incl_mul (p : LeftId O x) : ∃ c : A, incl O x p = c * x := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (lv_mem O x p)
  exact ⟨c, by rw [incl_apply, ← hc, smul_eq_mul]⟩

theorem incl_smul (a : A) (p : LeftId O x) : incl O x (a • p) = a * incl O x p := rfl

end LeftId

section Pe
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {A : Type} [Ring A] [Algebra O A]
  {n : Type} [Fintype n] [DecidableEq n]

def eveM (ρ : A →ₐ[O] Matrix n n O) (e₁ : A) (v₁ : LatM O O n ρ.toRingHom) :
    LeftId O e₁ →ₗ[O] LatM O O n ρ.toRingHom where
  toFun p := incl O e₁ p • v₁
  map_add' p q := by rw [map_add, add_smul]
  map_smul' c p := by
    rw [RingHom.id_apply, incl_apply, incl_apply, lv_smul]
    funext i
    show ∑ j, ρ (c • lv O e₁ p) i j * (v₁ j : O) = c * ∑ j, ρ (lv O e₁ p) i j * (v₁ j : O)
    rw [map_smul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [Matrix.smul_apply, smul_eq_mul, mul_assoc]

theorem eveM_apply (ρ : A →ₐ[O] Matrix n n O) (e₁ : A) (v₁ : LatM O O n ρ.toRingHom) (p : LeftId O e₁) :
    eveM ρ e₁ v₁ p = incl O e₁ p • v₁ := rfl

theorem eveM_onto (ρ : A →ₐ[O] Matrix n n O) (e₁ : A) (h : SurjectionRankOneIdempotent O A n ρ.toRingHom e₁) :
    Function.Surjective (eveM ρ e₁ (vOne ρ e₁ h)) := by
  intro v
  obtain ⟨c, hc⟩ := (vOne_spec ρ e₁ h).2.2.2.2.2.2.2.2.2.2 v
  refine ⟨lmk O e₁ (c * e₁) (Submodule.mem_span_singleton.2 ⟨c, rfl⟩), ?_⟩
  rw [eveM_apply, incl_apply, lv_lmk]
  exact hc

end Pe

section PE
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {A : Type} [Ring A] [Algebra O A]
  {m : Type} [Fintype m] [DecidableEq m]

theorem trace_mem (ρ₁ : A →ₐ[O] Matrix m m O) (E : A) (δO : O) (hE : ρ₁ E = δO • (1 : Matrix m m O))
    (p : LeftId O E) : (ρ₁ (incl O E p)).trace ∈ Ideal.span ({δO} : Set O) := by
  obtain ⟨c, hc⟩ := incl_mul O E p
  rw [hc, map_mul, hE, Matrix.mul_smul, mul_one, Matrix.trace_smul, smul_eq_mul]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self δO)

def evEM (ρ₁ : A →ₐ[O] Matrix m m O) (E : A) (δO : O) (hE : ρ₁ E = δO • (1 : Matrix m m O)) :
    LeftId O E →ₗ[O] ↥(Ideal.span ({δO} : Set O)) where
  toFun p := ⟨(ρ₁ (incl O E p)).trace, trace_mem ρ₁ E δO hE p⟩
  map_add' p q := Subtype.ext (by
    show (ρ₁ (incl O E (p + q))).trace = (ρ₁ (incl O E p)).trace + (ρ₁ (incl O E q)).trace
    rw [map_add, map_add, Matrix.trace_add])
  map_smul' c p := Subtype.ext (by
    show (ρ₁ (lv O E (c • p))).trace = c * (ρ₁ (lv O E p)).trace
    rw [lv_smul, map_smul, Matrix.trace_smul, smul_eq_mul])

theorem evEM_val (ρ₁ : A →ₐ[O] Matrix m m O) (E : A) (δO : O) (hE : ρ₁ E = δO • (1 : Matrix m m O))
    (p : LeftId O E) : ((evEM ρ₁ E δO hE p : ↥(Ideal.span ({δO} : Set O))) : O) = (ρ₁ (incl O E p)).trace := rfl

theorem evEM_act (ρ₁ : A →ₐ[O] Matrix m m O) (h1 : Fintype.card m = 1) (E : A) (δO : O)
    (hE : ρ₁ E = δO • (1 : Matrix m m O)) (p : LeftId O E) (v : LatQ O m ρ₁.toRingHom) :
    incl O E p • v = ((evEM ρ₁ E δO hE p : ↥(Ideal.span ({δO} : Set O))) : O) • v := by
  rw [evEM_val]; exact act_trace ρ₁ h1 _ v

theorem evEM_onto (ρ₁ : A →ₐ[O] Matrix m m O) (h1 : Fintype.card m = 1) (E : A) (δO : O)
    (hE : ρ₁ E = δO • (1 : Matrix m m O)) : Function.Surjective (evEM ρ₁ E δO hE) := by
  rintro ⟨x, hx⟩
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hx
  refine ⟨lmk O E (y • E) (Submodule.smul_of_tower_mem _ y (Submodule.mem_span_singleton_self E)), Subtype.ext ?_⟩
  rw [evEM_val, incl_apply, lv_lmk]
  show (ρ₁ (y • E)).trace = y * δO
  rw [map_smul, hE, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_one, h1, smul_eq_mul, smul_eq_mul]
  simp

theorem evEM_inv {T' G : Type} [CommRing T'] [Algebra T' A] [Group G] (r : G →* A) (χ : G →* T'ˣ)
    (ρ₁ : A →ₐ[O] Matrix m m O) (E : A) (δO : O) (hE : ρ₁ E = δO • (1 : Matrix m m O))
    (hu : ∀ g (v : LatQ O m ρ₁.toRingHom), uElt r χ g • v = v) (g : G) (p : LeftId O E) :
    evEM ρ₁ E δO hE (uElt r χ g • p) = evEM ρ₁ E δO hE p := by
  apply Subtype.ext
  rw [evEM_val, evEM_val, incl_smul, map_mul,
    mat_eq_of_act ρ₁ (uElt r χ g) 1 (fun v => by rw [one_smul]; exact hu g v), one_smul, one_mul]

end PE

section T12
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {A : Type} [Ring A] [Algebra O A]
  {n : Type} [Fintype n] [DecidableEq n] {T' G : Type} [CommRing T'] [Algebra T' A] [Group G]

def rhoTwo (ρ : A →ₐ[O] Matrix n n O) (r : G →* A) (χ : G →* T'ˣ) (ε : G →* Oˣ) : Representation O G (n → O) where
  toFun g := Matrix.mulVecLin (((ε g : Oˣ) : O) • (ρ (uElt r χ g⁻¹)).transpose)
  map_one' := by
    rw [inv_one, uElt_one, map_one ρ, Matrix.transpose_one, map_one ε, Units.val_one, one_smul]
    exact Matrix.mulVecLin_one
  map_mul' g h := by
    rw [Module.End.mul_eq_comp, ← Matrix.mulVecLin_mul, mul_inv_rev, uElt_mul, map_mul ρ, Matrix.transpose_mul,
      map_mul ε, Units.val_mul, smul_mul_smul_comm]

theorem rhoTwo_apply (ρ : A →ₐ[O] Matrix n n O) (r : G →* A) (χ : G →* T'ˣ) (ε : G →* Oˣ) (g : G) (t : n → O) :
    rhoTwo ρ r χ ε g t = (((ε g : Oˣ) : O) • (ρ (uElt r χ g⁻¹)).transpose).mulVec t := rfl

def gamM (ρ : A →ₐ[O] Matrix n n O) : (n → O) →ₗ[O] LatQ O n ρ.toRingHom →ₗ[O] KO O :=
  LinearMap.mk₂ O (fun (t : n → O) (m : LatQ O n ρ.toRingHom) => ∑ a, t a • (m a : KO O))
    (fun t t' m => by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib])
    (fun c t m => by simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum])
    (fun t m m' => by
      show ∑ a, t a • ((m a : KO O) + m' a) = _
      simp only [smul_add, Finset.sum_add_distrib])
    (fun c t m => by
      show ∑ a, t a • (c • (m a : KO O)) = c • ∑ a, t a • (m a : KO O)
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun a _ => smul_comm _ _ _)

theorem gamM_apply (ρ : A →ₐ[O] Matrix n n O) (t : n → O) (m : LatQ O n ρ.toRingHom) :
    gamM ρ t m = ∑ a, t a • (m a : KO O) := rfl

def lamM (ρ : A →ₐ[O] Matrix n n O) (w : n → O) : LatQ O n ρ.toRingHom →ₗ[O] KO O := gamM ρ w

def piM (ρ : A →ₐ[O] Matrix n n O) (e₁ : A) (w : n → O) : FirstSummandSubmodule O e₁ →ₗ[O] (n → O) where
  toFun b := Matrix.vecMul w (ρ (b : A))
  map_add' b b' := by rw [Submodule.coe_add, map_add, Matrix.vecMul_add]
  map_smul' c b := by rw [Submodule.coe_smul, map_smul, Matrix.vecMul_smul, RingHom.id_apply]

theorem piM_apply (ρ : A →ₐ[O] Matrix n n O) (e₁ : A) (w : n → O) (b : FirstSummandSubmodule O e₁) :
    piM ρ e₁ w b = Matrix.vecMul w (ρ (b : A)) := rfl

theorem gam_pi (ρ : A →ₐ[O] Matrix n n O) (e₁ : A) (w : n → O) (b : FirstSummandSubmodule O e₁) (m : LatQ O n ρ.toRingHom) :
    gamM ρ (piM ρ e₁ w b) m = lamM ρ w ((FirstSummandSubmodule O e₁).subtype b • m) := by
  show ∑ a, (Matrix.vecMul w (ρ (b : A))) a • (m a : KO O) = ∑ i, w i • (((b : A) • m) i : KO O)
  simp only [latQ_act, Matrix.vecMul, dotProduct, Finset.sum_smul, Finset.smul_sum, mul_smul]
  exact Finset.sum_comm

theorem pi_equiv (ρ : A →ₐ[O] Matrix n n O) (r : G →* A) (χ : G →* T'ˣ) (e₁ : A) (ε : G →* Oˣ) (w : n → O) :
    IsEquivMap (firstSummandRep O r χ e₁ ε) (rhoTwo ρ r χ ε) (piM ρ e₁ w) := by
  intro g b
  have hu : ((χ g : T'ˣ) : T') • ((b : A) * r g⁻¹) = (b : A) * uElt r χ g⁻¹ := by
    rw [uElt, map_inv χ, inv_inv, mul_smul_comm]
  rw [rhoTwo_apply, piM_apply, piM_apply]
  show Matrix.vecMul w (ρ (((ε g : Oˣ) : O) • (((χ g : T'ˣ) : T') • ((b : A) * r g⁻¹)))) = _
  rw [hu, map_smul, map_mul, Matrix.vecMul_smul]
  funext a
  simp only [Matrix.vecMul, Matrix.mulVec, dotProduct, Matrix.smul_apply, Matrix.transpose_apply, Matrix.mul_apply,
    Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem pi_onto (ρ : A →ₐ[O] Matrix n n O) (hs : Function.Surjective ρ) (e₁ : A) (v w : n → O)
    (hvw : ∀ i j, ρ e₁ i j = v i * w j) (hwv : ∑ j, w j * v j = 1) : Function.Surjective (piM ρ e₁ w) := by
  intro t
  obtain ⟨b', hb'⟩ := hs (Matrix.vecMulVec v t)
  refine ⟨⟨e₁ * b', b', rfl⟩, ?_⟩
  rw [piM_apply]
  show Matrix.vecMul w (ρ (e₁ * b')) = t
  rw [map_mul, ← Matrix.vecMul_vecMul, hb']
  have h1 : Matrix.vecMul w (ρ e₁) = w := by
    funext j
    simp only [Matrix.vecMul, dotProduct, hvw, ← mul_assoc]
    rw [← Finset.sum_mul, hwv, one_mul]
  rw [h1]
  funext j
  simp only [Matrix.vecMul, dotProduct, Matrix.vecMulVec_apply, ← mul_assoc]
  rw [← Finset.sum_mul, hwv, one_mul]

theorem inc_equiv (r : G →* A) (χ : G →* T'ˣ) (e₁ : A) (ε : G →* Oˣ) (g : G) (b : FirstSummandSubmodule O e₁) :
    (FirstSummandSubmodule O e₁).subtype (firstSummandRep O r χ e₁ ε g b) =
      ((ε g : Oˣ) : O) • (((χ g : T'ˣ) : T') • ((FirstSummandSubmodule O e₁).subtype b * r g⁻¹)) := rfl

end T12

omit hT2Core in

instance submoduleContinuousConstSMul {O M : Type} [Semiring O] [AddCommMonoid M] [Module O M] [TopologicalSpace M]
    [ContinuousConstSMul O M] (S : Submodule O M) : ContinuousConstSMul O ↥S :=
  ⟨fun c => (continuous_subtype_val.const_smul c).subtype_mk _⟩

section Top
variable {O : Type} [CommRing O] {A : Type} [Ring A] [Algebra O A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [ContinuousConstSMul O A] (e₁ : A)

example : TopologicalSpace (FirstSummandSubmodule O e₁) := inferInstance
example : IsTopologicalAddGroup (FirstSummandSubmodule O e₁) := inferInstance
example : ContinuousConstSMul O (FirstSummandSubmodule O e₁) := inferInstance

theorem inc_cont : Continuous (FirstSummandSubmodule O e₁).subtype := continuous_subtype_val

end Top

section Dd
open Formalism.RepresentationBoundsCohomology.ringDataObjects

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X d G : Type}
  [Fintype d] [DecidableEq d] [Group G] {t : ℕ} {bl : d → Fin (t + 1)}

def cOne (ht : 1 ≤ t) : Fin (t + 1) := ⟨1, by omega⟩

theorem cOne_ne (ht : 1 ≤ t) : cOne ht ≠ 0 := by
  intro h
  have := congrArg Fin.val h
  simp [cOne] at this

variable (Dd : RingData O X d G t bl) (T : Subalgebra O (X → O)) (ht : 1 ≤ t)
  [∀ k, SMulCommClass Dd.R' O (blockRestrictedRepresentationType bl Dd.ρk k)]

theorem top_facts (hT : Dd.Top T ht) :
    Dd.e₁ * Dd.e₁ = Dd.e₁ ∧ (∀ k, Function.Surjective (Dd.ρk k)) ∧ Fintype.card {a // bl a = cOne ht} = 1 ∧
    Dd.ρk (cOne ht) Dd.E = Dd.δO • (1 : Matrix {a // bl a = cOne ht} {a // bl a = cOne ht} O) ∧
    (∀ g (m : blockRestrictedRepresentationType bl Dd.ρk (cOne ht)), uElt Dd.r Dd.χ g • m = m) := by
  obtain ⟨-, -, -, -, hee, -, -, -, hsurj, -, hcard1, -, -, -, -, -, -, hOne⟩ := hT
  obtain ⟨p1, -, p3, -⟩ := hOne
  exact ⟨hee, hsurj, hcard1 _ (cOne_ne ht), mat_eq_of_act _ _ _ p3, p1⟩

theorem rank_reduction_idempotent_one {T : Subalgebra O (X → O)} {r₀ : G →* (X → Matrix d d O)} {π : X} {χ₁ ε : G →* Oˣ} {g₀ : G}
    {eB e₁ s : X → Matrix d d O} (hI : IdemHyp O T r₀ π bl eB e₁) (hD : RingDef O T r₀ π χ₁ ε g₀ eB e₁ s Dd) :
    ((Dd.ρk 0 Dd.e₁).map (algebraMap O (FractionRing O))).rank = 1 :=
  idempotent_rank_one_at_point hI hD

theorem rho_hypotheses_of_ring_data (hT : Dd.Top T ht) (hrk : ((Dd.ρk 0 Dd.e₁).map (algebraMap O (FractionRing O))).rank = 1) :
    SurjectionRankOneIdempotent O Dd.R' {a // bl a = 0} (Dd.ρk 0).toRingHom Dd.e₁ :=
  surjection_of_rank_one_idempotent O Dd.R' _ (Dd.ρk 0).toRingHom Dd.e₁ ((top_facts Dd T ht hT).2.1 0) (top_facts Dd T ht hT).1 hrk

theorem rankOne_Dd (hT : Dd.Top T ht) (hrk : ((Dd.ρk 0 Dd.e₁).map (algebraMap O (FractionRing O))).rank = 1) :
    ∃ v w : {a // bl a = 0} → O, (∀ i j, Dd.ρk 0 Dd.e₁ i j = v i * w j) ∧ ∑ j, w j * v j = 1 :=
  rank_one_factor O _ (Dd.ρk 0 Dd.e₁) (by rw [← map_mul, (top_facts Dd T ht hT).1]) hrk

def v1Dd (hT : Dd.Top T ht) (hrk : ((Dd.ρk 0 Dd.e₁).map (algebraMap O (FractionRing O))).rank = 1) :
    LatM O O {a // bl a = 0} (Dd.ρk 0).toRingHom :=
  vOne (Dd.ρk 0) Dd.e₁ (rho_hypotheses_of_ring_data Dd T ht hT hrk)

def wDd (hT : Dd.Top T ht) (hrk : ((Dd.ρk 0 Dd.e₁).map (algebraMap O (FractionRing O))).rank = 1) :
    {a // bl a = 0} → O :=
  (rankOne_Dd Dd T ht hT hrk).choose_spec.choose

def eveDd (hT : Dd.Top T ht) (hrk : ((Dd.ρk 0 Dd.e₁).map (algebraMap O (FractionRing O))).rank = 1) :
    LeftId O Dd.e₁ →ₗ[O] LatM O O {a // bl a = 0} (Dd.ρk 0).toRingHom :=
  eveM (Dd.ρk 0) Dd.e₁ (v1Dd Dd T ht hT hrk)

def evEDd (hT : Dd.Top T ht) : LeftId O Dd.E →ₗ[O] ↥(Ideal.span ({Dd.δO} : Set O)) :=
  evEM (Dd.ρk (cOne ht)) Dd.E Dd.δO (top_facts Dd T ht hT).2.2.2.1

def piDd (hT : Dd.Top T ht) (hrk : ((Dd.ρk 0 Dd.e₁).map (algebraMap O (FractionRing O))).rank = 1) :
    FirstSummandSubmodule O Dd.e₁ →ₗ[O] ({a // bl a = 0} → O) :=
  piM (Dd.ρk 0) Dd.e₁ (wDd Dd T ht hT hrk)

def lamDd (hT : Dd.Top T ht) (hrk : ((Dd.ρk 0 Dd.e₁).map (algebraMap O (FractionRing O))).rank = 1) :
    blockRestrictedRepresentationType bl Dd.ρk 0 →ₗ[O] KO O :=
  lamM (Dd.ρk 0) (wDd Dd T ht hT hrk)

theorem tensor_lattice_facts (hT : Dd.Top T ht) (hrk : ((Dd.ρk 0 Dd.e₁).map (algebraMap O (FractionRing O))).rank = 1)
    (ε : G →* Oˣ) :
    let ρ0 := (Dd.ρk 0).toRingHom
    let v₁ := v1Dd Dd T ht hT hrk
    let c1 : Fin (t + 1) := ⟨1, by omega⟩

    ((∀ (a : Dd.R') v x, tensM O _ ρ0 (a • v) x = a • tensM O _ ρ0 v x) ∧
      (∀ m : blockRestrictedRepresentationType bl Dd.ρk 0, Dd.e₁ • m = m → ∃ x, m = tensM O _ ρ0 v₁ x) ∧
      (∀ (a : Dd.R') v, iLM O _ ρ0 (a • v) = a • iLM O _ ρ0 v) ∧
      (∀ (a : Dd.R') v, qVM O _ ρ0 (a • v) = a • qVM O _ ρ0 v) ∧
      (∀ v (x : FractionRing O), tensM O _ ρ0 v (Submodule.Quotient.mk x) = qVM O _ ρ0 (x • iLM O _ ρ0 v)) ∧
      Function.Injective (iLM O _ ρ0) ∧ Function.Surjective (qVM O _ ρ0) ∧
      LinearMap.ker (qVM O _ ρ0) = LinearMap.range (iLM O _ ρ0) ∧
      (∀ v : LatM O (FractionRing O) {a // bl a = 0} ρ0, ∃ c : O, c ≠ 0 ∧ c • v ∈ LinearMap.range (iLM O _ ρ0)) ∧
      Dd.e₁ • v₁ = v₁) ∧

    (∀ a, eveDd Dd T ht hT hrk a = incl O Dd.e₁ a • v₁) ∧ Function.Surjective (eveDd Dd T ht hT hrk) ∧

    (∀ g a, evEDd Dd T ht hT (uElt Dd.r Dd.χ g • a) = evEDd Dd T ht hT a) ∧
    Function.Surjective (evEDd Dd T ht hT) ∧ (∀ a, ∃ c : Dd.R', incl O Dd.E a = c * Dd.E) ∧
    (∀ a (m : blockRestrictedRepresentationType bl Dd.ρk c1),
      incl O Dd.E a • m = ((evEDd Dd T ht hT a : ↥(Ideal.span ({Dd.δO} : Set O))) : O) • m) ∧

    (∀ g b, (FirstSummandSubmodule O Dd.e₁).subtype (firstSummandRep O Dd.r Dd.χ Dd.e₁ ε g b) =
      ((ε g : Oˣ) : O) • (((Dd.χ g : Dd.T'ˣ) : Dd.T') • ((FirstSummandSubmodule O Dd.e₁).subtype b * Dd.r g⁻¹))) ∧
    IsEquivMap (firstSummandRep O Dd.r Dd.χ Dd.e₁ ε) (rhoTwo (Dd.ρk 0) Dd.r Dd.χ ε) (piDd Dd T ht hT hrk) ∧
    (∀ b m, gamM (Dd.ρk 0) (piDd Dd T ht hT hrk b) m = lamDd Dd T ht hT hrk ((FirstSummandSubmodule O Dd.e₁).subtype b • m)) ∧
    Function.Surjective (piDd Dd T ht hT hrk) := by
  intro ρ0 v₁ c1
  have hs := vOne_spec (Dd.ρk 0) Dd.e₁ (rho_hypotheses_of_ring_data Dd T ht hT hrk)
  have hf := top_facts Dd T ht hT
  have hvw := (rankOne_Dd Dd T ht hT hrk).choose_spec.choose_spec
  refine ⟨⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.1, hs.2.2.2.2.2.1, hs.2.2.2.2.2.2.1,
      hs.2.2.2.2.2.2.2.1, hs.2.2.2.2.2.2.2.2.1, hs.2.2.2.2.2.2.2.2.2.1⟩,
    fun a => rfl, eveM_onto _ _ _,
    evEM_inv Dd.r Dd.χ _ _ _ _ hf.2.2.2.2, evEM_onto _ hf.2.2.1 _ _ _, incl_mul O Dd.E,
    evEM_act _ hf.2.2.1 _ _ _,
    inc_equiv Dd.r Dd.χ Dd.e₁ ε, pi_equiv _ _ _ _ _ _, gam_pi _ _ _,
    pi_onto _ (hf.2.1 0) _ _ _ hvw.1 hvw.2⟩

end Dd

section Checks
variable {ℓ : ℕ} [Fact ℓ.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[ℓ] O]
  {A : Type} [Ring A] [Algebra O A] [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousConstSMul O A]
  {n : Type} [Fintype n] [DecidableEq n] (ρ : A →ₐ[O] Matrix n n O) (x e₁ : A)

example : Module ℤ_[ℓ] (LatM O O n ρ.toRingHom) := inferInstance
example : IsScalarTower ℤ_[ℓ] O (LatM O O n ρ.toRingHom) := inferInstance
example : SMulCommClass A O (LeftId O x) := inferInstance
example : Module ℤ_[ℓ] (LeftId O x) := inferInstance
example : IsScalarTower ℤ_[ℓ] O (LeftId O x) := inferInstance
example : IsTopologicalAddGroup (FirstSummandSubmodule O e₁) := inferInstance
example : ContinuousConstSMul O (FirstSummandSubmodule O e₁) := inferInstance

end Checks

section Cont
open ReciprocityTheory.ChartRestriction.T2 (PadicCoeff IsFGTop)

variable {ℓ : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
  {A : Type} [Ring A] [Algebra O A] [TopologicalSpace A] [IsTopologicalAddGroup A]

theorem lin_cont (hO : PadicCoeff ℓ O) (hA : IsFGTop O A) {N : Type} [AddCommGroup N] [Module O N] [TopologicalSpace N]
    [ContinuousAdd N] [ContinuousSMul O N] (g : A →ₗ[O] N) : Continuous g := by
  have := hO.ring; have := hO.compact; have := hA.t2; have := hA.csmul; have := hA.fg
  obtain ⟨k, f, hf⟩ := Module.Finite.exists_fin' O A
  have hfc : Continuous f := LinearMap.continuous_on_pi f
  have hq : Topology.IsQuotientMap f := hfc.isClosedMap.isQuotientMap hfc hf
  exact hq.continuous_iff.2 (LinearMap.continuous_on_pi (g ∘ₗ f))

variable {n : Type} [Fintype n] [DecidableEq n]

def piA (ρ : A →ₐ[O] Matrix n n O) (w : n → O) : A →ₗ[O] (n → O) where
  toFun b := Matrix.vecMul w (ρ b)
  map_add' b b' := by rw [map_add, Matrix.vecMul_add]
  map_smul' c b := by rw [map_smul, Matrix.vecMul_smul, RingHom.id_apply]

theorem piM_cont (hO : PadicCoeff ℓ O) (hA : IsFGTop O A) (ρ : A →ₐ[O] Matrix n n O) (e₁ : A) (w : n → O) :
    Continuous (piM ρ e₁ w) := by
  have := hO.ring
  exact (lin_cont hO hA (piA ρ w)).comp continuous_subtype_val

theorem rho_cont (hO : PadicCoeff ℓ O) (hA : IsFGTop O A) (ρ : A →ₐ[O] Matrix n n O) : Continuous ρ := by
  have := hO.ring
  exact lin_cont hO hA ρ.toLinearMap

end Cont

end Formalism.MainNotions.N.K
