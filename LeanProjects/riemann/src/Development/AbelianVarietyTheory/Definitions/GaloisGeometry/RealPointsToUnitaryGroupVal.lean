import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FinrankPartTrivialMulRel
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinrankGroupCohomologyFunRep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianCongrOfPositiveIndexEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveRealTensorToProdMatrixAlgebrasInfPlaces
import Development.AbelianVarietyTheory.Definitions.Divisors.JmMulJm

noncomputable section

open NumberField Matrix GlobalTheory.LKTrip GlobalTheory.Mt.Adelic ReciprocityTheory.ChartRestriction.DS GlobalTheory.Kg
open scoped TensorProduct Matrix.Norms.L2Operator

namespace GlobalTheory.HTBetti

variable {p : ℕ} [Fact p.Prime] (G : HTGroup p)

abbrev Gf : Type := G.GAf × G.GQp

def toF : G.GQ →* Gf G := G.toAf.prod (ubc ℚ_[p])

theorem toF_apply (γ : G.GQ) : toF G γ = (G.toAf γ, ubc ℚ_[p] γ) := rfl

def level (L : G.Level) (Kp : Subgroup G.GQp) : Subgroup (Gf G) := (L.K : Subgroup G.GAf).prod Kp

theorem isOpen_level (L : G.Level) {Kp : Subgroup G.GQp} (h : IsOpen (Kp : Set G.GQp)) :
    IsOpen (level G L Kp : Set (Gf G)) := by
  rw [level, Subgroup.coe_prod]
  exact L.K.isOpen.prod h

theorem isCompact_level (L : G.Level) {Kp : Subgroup G.GQp} (h : IsCompact (Kp : Set G.GQp)) :
    IsCompact (level G L Kp : Set (Gf G)) := by
  rw [level, Subgroup.coe_prod]
  exact L.compact.prod h

abbrev coh (Kf : Subgroup (Gf G)) {d : ℕ} (ξ₀ : G.GQ →* Matrix (Fin d) (Fin d) ℂ) (q : ℕ) : Type :=
  groupCohomology (Rep.of (funRepY (toF G) Kf ξ₀)) q

def hecke {Kf : Subgroup (Gf G)} {n : ℕ} {z : Fin n → Gf G} (hz : IsHeckeFam Kf z) {d : ℕ}
    (ξ₀ : G.GQ →* Matrix (Fin d) (Fin d) ℂ) (q : ℕ) : Module.End ℂ (coh G Kf ξ₀ q) :=
  heckeCoh (ρf := toF G) hz ξ₀ q

def heckeRel (Kf : Subgroup (Gf G)) {d : ℕ} (ξ₀ : G.GQ →* Matrix (Fin d) (Fin d) ℂ) (q : ℕ) :
    GlobalTheory.HkPart.HeckeRel ℂ Kf (coh G Kf ξ₀ q) :=
  GlobalTheory.HkPart.HeckeRel.ofFun fun z hz => hecke G hz ξ₀ q

abbrev piPart {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (Gf G) V) (Kf : Subgroup (Gf G))
    {d : ℕ} (ξ₀ : G.GQ →* Matrix (Fin d) (Fin d) ℂ) (q : ℕ) :
    Submodule ℂ (GlobalTheory.HkPart.fix π Kf →ₗ[ℂ] coh G Kf ξ₀ q) :=
  GlobalTheory.HkPart.part π Kf (heckeRel G Kf ξ₀ q)

theorem mem_piPart {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (Gf G) V}
    {Kf : Subgroup (Gf G)} {d : ℕ} {ξ₀ : G.GQ →* Matrix (Fin d) (Fin d) ℂ} {q : ℕ}
    {φ : GlobalTheory.HkPart.fix π Kf →ₗ[ℂ] coh G Kf ξ₀ q} :
    φ ∈ piPart G π Kf ξ₀ q ↔ ∀ ⦃n : ℕ⦄ (z : Fin n → Gf G) (hz : IsHeckeFam Kf z),
      φ ∘ₗ GlobalTheory.HkPart.op π hz = hecke G hz ξ₀ q ∘ₗ φ :=
  GlobalTheory.HkPart.mem_part_ofFun

section Classes

variable (Kf : Subgroup (Gf G))

abbrev act : MulAction G.GQ (Gf G ⧸ Kf) := yAct (toF G) Kf

abbrev Classes : Type := letI := act G Kf; MulAction.orbitRel.Quotient G.GQ (Gf G ⧸ Kf)

def pt (c : Classes G Kf) : Gf G ⧸ Kf := letI := act G Kf; Quotient.out c

def gam (y : Gf G ⧸ Kf) : Subgroup G.GQ := letI := act G Kf; MulAction.stabilizer G.GQ y

theorem mem_gam_mk (x : Gf G) (γ : G.GQ) : γ ∈ gam G Kf (x : Gf G ⧸ Kf) ↔ x⁻¹ * toF G γ * x ∈ Kf := by
  letI := act G Kf
  change (toF G γ • (x : Gf G ⧸ Kf) : Gf G ⧸ Kf) = x ↔ _
  rw [MulAction.Quotient.smul_mk, QuotientGroup.eq, smul_eq_mul, _root_.mul_inv_rev, ← Kf.inv_mem_iff,
    show (x⁻¹ * (toF G γ)⁻¹ * x : Gf G)⁻¹ = x⁻¹ * toF G γ * x by group]

theorem pt_cover : letI := act G Kf; ∀ y : Gf G ⧸ Kf, ∃ c : Classes G Kf, ∃ g : G.GQ, g • pt G Kf c = y := by
  letI := act G Kf
  intro y
  refine ⟨Quotient.mk'' y, ?_⟩
  have h : pt G Kf (Quotient.mk'' y) ∈ MulAction.orbit G.GQ y :=
    MulAction.orbitRel_apply.1 (Quotient.exact (Quotient.out_eq (Quotient.mk'' y : Classes G Kf)))
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.1 h
  exact ⟨g⁻¹, by rw [← hg, inv_smul_smul]⟩

theorem pt_disjoint : letI := act G Kf;
    ∀ (i j : Classes G Kf) (g : G.GQ), g • pt G Kf i = pt G Kf j → i = j := by
  letI := act G Kf
  intro i j g h
  rw [← Quotient.out_eq i, ← Quotient.out_eq j]
  apply Quotient.sound
  refine MulAction.orbitRel_apply.2 (MulAction.mem_orbit_iff.2 ⟨g⁻¹, ?_⟩)
  change g⁻¹ • pt G Kf j = pt G Kf i
  rw [← h, inv_smul_smul]

def cohEquivPi {d : ℕ} (ξ₀ : G.GQ →* Matrix (Fin d) (Fin d) ℂ) (q : ℕ) :
    coh G Kf ξ₀ q ≃ₗ[ℂ] ∀ c : Classes G Kf,
      groupCohomology (Rep.of (GlobalTheory.BorelCoh.matVecRep (ξ₀.comp (gam G Kf (pt G Kf c)).subtype))) q :=
  letI := act G Kf
  GlobalTheory.BorelCoh.Shapiro.cohEquiv ξ₀ (pt G Kf) (pt_cover G Kf) (pt_disjoint G Kf) q

end Classes

section UJpm

variable {T : Type} [Fintype T] {n : ℕ}

def UJpm (ε : T → Fin n → Bool) : Subgroup (MatT T n)ˣ where
  carrier := {g | ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∀ τ, (g.val τ)ᴴ * Jm (ε τ) * g.val τ = (s : ℂ) • Jm (ε τ)}
  one_mem' := ⟨1, Or.inl rfl, fun τ => by simp⟩
  mul_mem' := by
    rintro g h ⟨s, hs, hg⟩ ⟨t, ht, hh⟩
    refine ⟨s * t, ?_, fun τ => ?_⟩
    · rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> norm_num
    · simp only [Units.val_mul, Pi.mul_apply, Matrix.conjTranspose_mul]
      calc (h.val τ)ᴴ * (g.val τ)ᴴ * Jm (ε τ) * (g.val τ * h.val τ)
          = (h.val τ)ᴴ * ((g.val τ)ᴴ * Jm (ε τ) * g.val τ) * h.val τ := by simp only [Matrix.mul_assoc]
        _ = ((s * t : ℝ) : ℂ) • Jm (ε τ) := by
          rw [hg τ, Matrix.mul_smul, Matrix.smul_mul, hh τ, smul_smul]
          push_cast; ring_nf
  inv_mem' := by
    rintro g ⟨s, hs, hg⟩
    refine ⟨s, hs, fun τ => ?_⟩
    have h1 : g.val τ * (g⁻¹).val τ = 1 := by
      rw [← Pi.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one, Pi.one_apply]
    have hss : (s : ℂ) * s = 1 := by rcases hs with rfl | rfl <;> norm_num
    calc ((g⁻¹).val τ)ᴴ * Jm (ε τ) * (g⁻¹).val τ
        = (s : ℂ) • (((g⁻¹).val τ)ᴴ * ((s : ℂ) • Jm (ε τ)) * (g⁻¹).val τ) := by
          rw [Matrix.mul_smul, Matrix.smul_mul, smul_smul, hss, one_smul]
      _ = (s : ℂ) • ((g.val τ * (g⁻¹).val τ)ᴴ * Jm (ε τ) * (g.val τ * (g⁻¹).val τ)) := by
          rw [← hg τ]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (s : ℂ) • Jm (ε τ) := by rw [h1]; simp

theorem UJfam_le_UJpm (ε : T → Fin n → Bool) : UJfam ε ≤ UJpm ε :=
  fun g hg => ⟨1, Or.inl rfl, fun τ => by simpa using hg τ⟩

end UJpm

section Frame

def eps (v : InfinitePlace G.F) : Fin G.n → Bool := fun i => decide (0 < (G.gram_herm v).eigenvalues i)

theorem Jm_eps (v : InfinitePlace G.F) :
    Jm (eps G v) = diagonal (GlobalTheory.HermCongruence.signVec (G.gram_herm v)) := by
  unfold Jm eps GlobalTheory.HermCongruence.signVec
  congr 1
  funext i
  by_cases h : 0 < (G.gram_herm v).eigenvalues i <;> simp [h]

theorem pOf_eps (v : InfinitePlace G.F) : pOf (eps G v) = sigPosH (G.gram_herm v) := by
  unfold pOf eps sigPosH
  rw [Fintype.card_subtype]
  congr 1
  ext i
  simp

def frame (v : InfinitePlace G.F) : GL (Fin G.n) ℂ :=
  (GlobalTheory.HermCongruence.exists_congr_signVec (G.gram_herm v) (G.gram_det v)).choose

theorem frame_spec (v : InfinitePlace G.F) :
    ((frame G v : Matrix (Fin G.n) (Fin G.n) ℂ))ᴴ * G.gram v * (frame G v : Matrix (Fin G.n) (Fin G.n) ℂ) =
      Jm (eps G v) := by
  rw [Jm_eps]
  exact (GlobalTheory.HermCongruence.exists_congr_signVec (G.gram_herm v) (G.gram_det v)).choose_spec

def conjGL {m : ℕ} (P : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ →ₐ[ℝ] Matrix (Fin m) (Fin m) ℂ where
  toFun X := ((P⁻¹ : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ) * X * P
  map_one' := by
    rw [Matrix.mul_one, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  map_mul' X Y := by
    have h : ((P : Matrix (Fin m) (Fin m) ℂ) * ((P⁻¹ : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ)) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    show ((P⁻¹ : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ) * (X * Y) * P =
      ((P⁻¹ : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ) * X * P * (((P⁻¹ : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ) * Y * P)
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (P : Matrix (Fin m) (Fin m) ℂ), h, Matrix.one_mul]
  map_zero' := by simp
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
  commutes' r := by
    show ((P⁻¹ : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ) * algebraMap ℝ (Matrix (Fin m) (Fin m) ℂ) r * P = _
    rw [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, ← Units.val_mul,
      inv_mul_cancel, Units.val_one]

theorem conjGL_apply {m : ℕ} (P : GL (Fin m) ℂ) (X : Matrix (Fin m) (Fin m) ℂ) :
    conjGL P X = ((P⁻¹ : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ) * X * P := rfl

theorem conjGL_sim {m : ℕ} (P : GL (Fin m) ℂ) (h X : Matrix (Fin m) (Fin m) ℂ) (c : ℂ)
    (hX : Xᴴ * h * X = c • h) :
    (conjGL P X)ᴴ * ((P : Matrix (Fin m) (Fin m) ℂ)ᴴ * h * P) * conjGL P X =
      c • ((P : Matrix (Fin m) (Fin m) ℂ)ᴴ * h * P) := by
  have h1 : (((P⁻¹ : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ))ᴴ * (P : Matrix (Fin m) (Fin m) ℂ)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.conjTranspose_one]
  have h2 : (P : Matrix (Fin m) (Fin m) ℂ) * ((P⁻¹ : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [conjGL_apply]
  calc _ = (P : Matrix (Fin m) (Fin m) ℂ)ᴴ * Xᴴ *
        ((((P⁻¹ : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ))ᴴ * (P : Matrix (Fin m) (Fin m) ℂ)ᴴ) * h *
        ((P : Matrix (Fin m) (Fin m) ℂ) * ((P⁻¹ : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ)) * X * P := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (P : Matrix (Fin m) (Fin m) ℂ)ᴴ * (Xᴴ * h * X) * P := by
        rw [h1, h2]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = _ := by rw [hX, Matrix.mul_smul, Matrix.smul_mul]

def mat : ℝ ⊗[ℚ] G.C →ₐ[ℝ] MatT (InfinitePlace G.F) G.n :=
  Pi.algHom ℝ _ fun v => (conjGL (frame G v)).comp (G.psiR v)

theorem mat_apply (x : ℝ ⊗[ℚ] G.C) (v : InfinitePlace G.F) : mat G x v = conjGL (frame G v) (G.psiR v x) := rfl

theorem psiR_star (v : InfinitePlace G.F) (x : ℝ ⊗[ℚ] G.C) :
    G.psiR v (starT G.star ℝ x).unop = (G.gram v)⁻¹ * (G.psiR v x)ᴴ * G.gram v := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r c =>
    rw [starT_tmul, HTGroup.psiR_tmul, HTGroup.psiR_tmul, G.psi_star, Matrix.conjTranspose_smul, star_trivial,
      Matrix.mul_smul, Matrix.smul_mul]
  | add x y hx hy =>
    simp only [map_add, MulOpposite.unop_add, hx, hy, Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul]

theorem psiR_sim (g : G.GR) (v : InfinitePlace G.F) :
    (G.psiR v ((g : (ℝ ⊗[ℚ] G.C)ˣ × ℝˣ).1 : ℝ ⊗[ℚ] G.C))ᴴ * G.gram v *
        G.psiR v ((g : (ℝ ⊗[ℚ] G.C)ˣ × ℝˣ).1 : ℝ ⊗[ℚ] G.C) =
      ((((g : (ℝ ⊗[ℚ] G.C)ˣ × ℝˣ).2 : ℝˣ) : ℝ) : ℂ) • G.gram v := by
  set x : ℝ ⊗[ℚ] G.C := ((g : (ℝ ⊗[ℚ] G.C)ˣ × ℝˣ).1 : ℝ ⊗[ℚ] G.C)
  set c : ℝ := (((g : (ℝ ⊗[ℚ] G.C)ˣ × ℝˣ).2 : ℝˣ) : ℝ)
  have hx : x * (starT G.star ℝ x).unop = algebraMap ℝ (ℝ ⊗[ℚ] G.C) c := g.2
  have hc : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Units.ne_zero _)
  have hdet : IsUnit (G.gram v).det := (G.gram_det v).isUnit
  have h1 := congrArg (G.psiR v) hx
  rw [map_mul, psiR_star, AlgHom.commutes, Algebra.algebraMap_eq_smul_one,
    RCLike.real_smul_eq_coe_smul (K := ℂ)] at h1
  have h2 : (G.gram v)⁻¹ * (G.psiR v x)ᴴ * G.gram v * G.psiR v x = (c : ℂ) • 1 :=
    (mul_eq_smul_one_comm hc).1 h1
  calc (G.psiR v x)ᴴ * G.gram v * G.psiR v x
      = G.gram v * ((G.gram v)⁻¹ * (G.psiR v x)ᴴ * G.gram v * G.psiR v x) := by
        simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mul]
    _ = _ := by rw [h2, Matrix.mul_smul, Matrix.mul_one]

end Frame

section Norm

def invSqrtAbs : ℝˣ →* ℝˣ where
  toFun c := Units.mk0 (Real.sqrt |(c : ℝ)|)⁻¹ (inv_ne_zero (Real.sqrt_pos.2 (abs_pos.2 c.ne_zero)).ne')
  map_one' := by ext; simp
  map_mul' a b := by
    ext
    simp [abs_mul, Real.sqrt_mul (abs_nonneg _), mul_inv, mul_comm]

theorem invSqrtAbs_sq (c : ℝˣ) : ((invSqrtAbs c : ℝˣ) : ℝ) * (invSqrtAbs c : ℝˣ) * c = SignType.sign (c : ℝ) := by
  have hc := c.ne_zero
  have hpos : 0 < |(c : ℝ)| := abs_pos.2 hc
  show (Real.sqrt |(c : ℝ)|)⁻¹ * (Real.sqrt |(c : ℝ)|)⁻¹ * c = _
  rw [← mul_inv, Real.mul_self_sqrt hpos.le]
  rcases lt_or_gt_of_ne hc with h | h
  · rw [abs_of_neg h, sign_neg h]; field_simp; simp
  · rw [abs_of_pos h, sign_pos h]; field_simp; simp

def normR : G.GR →* (ℝ ⊗[ℚ] G.C)ˣ where
  toFun g := Units.map (algebraMap ℝ (ℝ ⊗[ℚ] G.C) : ℝ →* ℝ ⊗[ℚ] G.C) (invSqrtAbs (uSimR ℝ g)) *
    (g : (ℝ ⊗[ℚ] G.C)ˣ × ℝˣ).1
  map_one' := by simp
  map_mul' g h := by
    ext
    simp only [map_mul, Units.val_mul, Units.coe_map, MonoidHom.coe_coe, Subgroup.coe_mul, Prod.fst_mul]
    rw [mul_assoc, mul_assoc]
    congr 1
    rw [← mul_assoc, ← mul_assoc, Algebra.commutes]

theorem normR_val (g : G.GR) : ((normR G g : (ℝ ⊗[ℚ] G.C)ˣ) : ℝ ⊗[ℚ] G.C) =
    algebraMap ℝ (ℝ ⊗[ℚ] G.C) ((invSqrtAbs (uSimR ℝ g) : ℝˣ) : ℝ) * ((g : (ℝ ⊗[ℚ] G.C)ˣ × ℝˣ).1 : ℝ ⊗[ℚ] G.C) := rfl

theorem mat_normR_sim (g : G.GR) (v : InfinitePlace G.F) :
    (mat G (normR G g : ℝ ⊗[ℚ] G.C) v)ᴴ * Jm (eps G v) * mat G (normR G g : ℝ ⊗[ℚ] G.C) v =
      (((SignType.sign (((g : (ℝ ⊗[ℚ] G.C)ˣ × ℝˣ).2 : ℝˣ) : ℝ) : ℝ)) : ℂ) • Jm (eps G v) := by
  set t : ℝ := ((invSqrtAbs (uSimR ℝ g) : ℝˣ) : ℝ)
  set c : ℝˣ := (g : (ℝ ⊗[ℚ] G.C)ˣ × ℝˣ).2
  have hY := conjGL_sim (frame G v) (G.gram v) _ _ (psiR_sim G g v)
  rw [frame_spec] at hY
  have hM : mat G (normR G g : ℝ ⊗[ℚ] G.C) v = (t : ℂ) • conjGL (frame G v)
      (G.psiR v ((g : (ℝ ⊗[ℚ] G.C)ˣ × ℝˣ).1 : ℝ ⊗[ℚ] G.C)) := by
    rw [normR_val, map_mul, AlgHom.commutes, Pi.mul_apply, mat_apply]
    rw [Pi.algebraMap_apply, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.one_mul,
      RCLike.real_smul_eq_coe_smul (K := ℂ)]
    rfl
  have hs' : t * t * (c : ℝ) = (SignType.sign (c : ℝ) : ℝ) := invSqrtAbs_sq (uSimR ℝ g)
  have hst : star (t : ℂ) = t := Complex.conj_ofReal t
  rw [hM, Matrix.conjTranspose_smul]
  simp only [Matrix.smul_mul, Matrix.mul_smul]
  rw [hY, smul_smul, smul_smul, hst]
  congr 1
  exact_mod_cast hs'

def realPointsToUnitaryGroup : G.GR →* UJpm (eps G) :=
  ((Units.map (mat G).toMonoidHom).comp (normR G)).codRestrict _ fun g =>
    ⟨SignType.sign (((g : (ℝ ⊗[ℚ] G.C)ˣ × ℝˣ).2 : ℝˣ) : ℝ), by
      rcases lt_or_gt_of_ne (((g : (ℝ ⊗[ℚ] G.C)ˣ × ℝˣ).2 : ℝˣ).ne_zero) with h | h
      · right; rw [sign_neg h]; rfl
      · left; rw [sign_pos h]; rfl,
     fun v => mat_normR_sim G g v⟩

theorem realPointsToUnitaryGroup_val (g : G.GR) (v : InfinitePlace G.F) :
    ((realPointsToUnitaryGroup G g : (MatT (InfinitePlace G.F) G.n)ˣ) : MatT (InfinitePlace G.F) G.n) v =
      mat G (normR G g : ℝ ⊗[ℚ] G.C) v := rfl

def PosSim : Prop := ∀ g : G.GR, 0 < (((g : (ℝ ⊗[ℚ] G.C)ˣ × ℝˣ).2 : ℝˣ) : ℝ)

def toUJ (h : PosSim G) : G.GR →* UJfam (eps G) :=
  ((Units.map (mat G).toMonoidHom).comp (normR G)).codRestrict _ fun g v => by
    have := mat_normR_sim G g v
    rw [sign_pos (h g)] at this
    simpa using this

theorem coe_toUJ (h : PosSim G) (g : G.GR) :
    ((toUJ G h g : UJfam (eps G)) : (MatT (InfinitePlace G.F) G.n)ˣ) = realPointsToUnitaryGroup G g := rfl

def rho1 : G.GQ →* UJpm (eps G) := (realPointsToUnitaryGroup G).comp G.toR

def rhoI (h : PosSim G) : G.GQ →* UJfam (eps G) := (toUJ G h).comp G.toR

def gamR (h : PosSim G) (Kf : Subgroup (Gf G)) (y : Gf G ⧸ Kf) : Subgroup (UJfam (eps G)) :=
  (gam G Kf y).map (rhoI G h)

end Norm

def Aniso : Prop := ∀ x : G.C, (G.star x).unop * x = 0 → x = 0

theorem aniso_of_division (h : ∀ x : G.C, x ≠ 0 → IsUnit x) : Aniso G := by
  intro x hx
  by_contra hne
  obtain ⟨u, rfl⟩ := h x hne
  have h0 : (G.star (u : G.C)).unop = 0 := by
    have := congrArg (· * ((u⁻¹ : G.Cˣ) : G.C)) hx
    simpa [mul_assoc] using this
  apply hne
  rw [← G.star_star (u : G.C), h0]
  simp

section Inhabitant

variable (Kf : Subgroup (Gf G))

abbrev xiTriv : G.GQ →* Matrix (Fin 1) (Fin 1) ℂ := 1

theorem const_mem_invariants :
    (fun _ _ => (1 : ℂ) : Gf G ⧸ Kf → Fin 1 → ℂ) ∈ (funRepY (toF G) Kf (xiTriv G)).invariants := by
  intro γ
  funext y i
  induction y using QuotientGroup.induction_on with
  | H x => rw [funRepY_apply]; simp

instance nontrivial_coh_zero : Nontrivial (coh G Kf (xiTriv G) 0) := by
  haveI : Nontrivial (funRepY (toF G) Kf (xiTriv G)).invariants :=
    ⟨⟨⟨_, const_mem_invariants G Kf⟩, 0, fun h => by
      have := congrFun (congrFun (congrArg Subtype.val h) (QuotientGroup.mk 1)) 0
      simp at this⟩⟩
  exact (groupCohomology.H0Iso _).toLinearEquiv.toEquiv.nontrivial

end Inhabitant

section Examples

open GlobalTheory.LKTrip.Example

example (v : InfinitePlace QI) : eps (ex 1 one_ne_zero) v ⟨0, Nat.one_pos⟩ = true := by
  unfold eps
  have h := eig_Hc 1 v.embedding ⟨0, Nat.one_pos⟩
  change decide (0 < (isHermitian_gramAt (herm_Hc 1) v.embedding).eigenvalues ⟨0, Nat.one_pos⟩) = true
  rw [h]; norm_num

example (v : InfinitePlace QI) : eps (ex (-1) (by norm_num)) v ⟨0, Nat.one_pos⟩ = false := by
  unfold eps
  have h := eig_Hc (-1) v.embedding ⟨0, Nat.one_pos⟩
  change decide (0 < (isHermitian_gramAt (herm_Hc (-1)) v.embedding).eigenvalues ⟨0, Nat.one_pos⟩) = false
  rw [h]; norm_num

example (c : ℚ) (hc : c ≠ 0) : Aniso (ex c hc) := by
  refine aniso_of_division _ fun x hx => ?_
  let y : Matrix (Fin 1) (Fin 1) QI := x
  have h : IsUnit y := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_unique]
    refine (Ne.isUnit fun h0 => hx ?_)
    show y = 0
    ext i j
    fin_cases i; fin_cases j
    exact h0
  exact h

example : Nontrivial (coh (ex 1 one_ne_zero) ⊤ (xiTriv _) 0) := inferInstance

example (Kf : Subgroup (Gf (ex 1 one_ne_zero))) :
    piPart (ex 1 one_ne_zero) (Representation.trivial ℂ _ ℂ) Kf (xiTriv _) 0 ≤ ⊤ := le_top

end Examples

end GlobalTheory.HTBetti
