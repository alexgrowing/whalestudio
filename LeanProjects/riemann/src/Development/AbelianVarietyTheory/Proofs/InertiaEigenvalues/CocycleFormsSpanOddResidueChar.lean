import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsDualDualRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameInertiaElementActsByScalar
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.CyclotomicTotient.SkolemNoether
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.UnramifiedNoJump

noncomputable section

namespace GlobalTheory.ResSel.SpanOddPf

open Matrix

section Algebra

variable {G K : Type} [Group G] [Field K] {r : ℕ}

theorem lift_surj (ρ : G →* Matrix (Fin r) (Fin r) K) (h : Submodule.span K (Set.range ρ) = ⊤) :
    Function.Surjective (MonoidAlgebra.lift K (Matrix (Fin r) (Fin r) K) G ρ) := by
  have : LinearMap.range (MonoidAlgebra.lift K (Matrix (Fin r) (Fin r) K) G ρ).toLinearMap = ⊤ := by
    rw [eq_top_iff, ← h, Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    exact ⟨MonoidAlgebra.of K G g, by simp⟩
  exact LinearMap.range_eq_top.1 this

theorem coeff_eq_zero (ρ₁ ρ₂ : G →* Matrix (Fin r) (Fin r) K) (h₁ : Submodule.span K (Set.range ρ₁) = ⊤)
    (h₂ : Submodule.span K (Set.range ρ₂) = ⊤)
    (hd : ¬ ∃ A : Matrix (Fin r) (Fin r) K, IsUnit A ∧ ∀ g, ρ₂ g * A = A * ρ₁ g)
    (f₁ f₂ : Matrix (Fin r) (Fin r) K →ₗ[K] K) (hf : ∀ g, f₁ (ρ₁ g) = f₂ (ρ₂ g)) : f₁ = 0 := by
  by_contra hne
  set R₁ := MonoidAlgebra.lift K (Matrix (Fin r) (Fin r) K) G ρ₁ with hR₁
  set R₂ := MonoidAlgebra.lift K (Matrix (Fin r) (Fin r) K) G ρ₂ with hR₂
  have s₁ : Function.Surjective R₁ := lift_surj ρ₁ h₁
  have s₂ : Function.Surjective R₂ := lift_surj ρ₂ h₂
  have hf' : ∀ a, f₁ (R₁ a) = f₂ (R₂ a) := by
    intro a
    induction a using MonoidAlgebra.induction_on with
    | of g => simp [hR₁, hR₂, hf]
    | add a b ha hb => simp only [map_add, ha, hb]
    | smul c a ha => simp only [map_smul, ha]
  have hker : ∀ a, R₂ a = 0 → R₁ a = 0 := by
    intro a ha
    by_contra hY
    obtain ⟨i, j, hij⟩ : ∃ i j, R₁ a i j ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hY (Matrix.ext hc)
    apply hne
    apply Matrix.ext_linearMap
    intro p q
    ext
    obtain ⟨b, hb⟩ := s₁ (Matrix.single p i 1)
    obtain ⟨c, hc⟩ := s₁ (Matrix.single j q 1)
    have := hf' (b * a * c)
    rw [map_mul R₁, map_mul R₁, map_mul R₂, map_mul R₂, ha, hb, hc, mul_zero, zero_mul, map_zero,
      Matrix.single_mul_mul_single] at this
    have e : (Matrix.single p q (1 * R₁ a i j * 1) : Matrix (Fin r) (Fin r) K) = R₁ a i j • Matrix.single p q 1 := by
      simp [Matrix.smul_single]
    rw [e, map_smul, smul_eq_mul, mul_eq_zero] at this
    simpa using this.resolve_left hij
  let φ₀ := RingHom.liftOfSurjective R₂.toRingHom s₂ ⟨R₁.toRingHom, fun a ha => hker a ha⟩
  have hφ₀ : ∀ a, φ₀ (R₂ a) = R₁ a := fun a => RingHom.liftOfSurjective_comp_apply R₂.toRingHom s₂ _ a
  let φ : Matrix (Fin r) (Fin r) K →ₐ[K] Matrix (Fin r) (Fin r) K :=
    ⟨φ₀, fun c => by
      have := hφ₀ (algebraMap K _ c)
      rwa [AlgHom.commutes, AlgHom.commutes] at this⟩
  obtain ⟨J, hJ⟩ := KStar.Tree.exists_conj_of_algHom φ
  refine hd ⟨((J⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K), Units.isUnit _, fun g => ?_⟩
  have h1 := hJ (R₂ (MonoidAlgebra.of K G g))
  have e : φ (R₂ (MonoidAlgebra.of K G g)) = R₁ (MonoidAlgebra.of K G g) := hφ₀ _
  have e1 : R₁ (MonoidAlgebra.of K G g) = ρ₁ g := by simp [hR₁]
  have e2 : R₂ (MonoidAlgebra.of K G g) = ρ₂ g := by simp [hR₂]
  rw [e, e1, e2] at h1
  rw [Units.mul_inv_eq_iff_eq_mul, mul_assoc, h1, Units.inv_mul_cancel_left]

theorem cob_of_vanish (ρ : G →* Matrix (Fin r) (Fin r) K) (L : Subgroup G) (z : G) (d : K) (hL : ∀ h ∈ L, ρ h = 1)
    (hz : ∀ g, g * z * g⁻¹ * z⁻¹ ∈ L) (hd : ρ z = d • (1 : Matrix (Fin r) (Fin r) K)) (hd1 : d ≠ 1)
    (c : G → Fin r → K) (hc : ∀ g h, c (g * h) = c g + ρ g *ᵥ c h) (h0 : ∀ h ∈ L, c h = 0) :
    ∃ m, ∀ g, c g = ρ g *ᵥ m - m := by
  refine ⟨(d - 1)⁻¹ • c z, fun g => ?_⟩
  have e : g * z = (g * z * g⁻¹ * z⁻¹) * (z * g) := by group
  have h1 := hc g z
  rw [e, hc, h0 _ (hz g), hL _ (hz g), hc, hd, one_mulVec, zero_add, smul_mulVec, one_mulVec] at h1
  have hu : d - 1 ≠ 0 := sub_ne_zero.2 hd1
  have h2 : (d - 1) • c g = ρ g *ᵥ c z - c z := by
    rw [sub_smul, one_smul]
    linear_combination (exp := 1) h1
  rw [mulVec_smul, ← smul_sub, ← h2, smul_smul, inv_mul_cancel₀ hu, one_smul]

theorem coc_conj (ρ : G →* Matrix (Fin r) (Fin r) K) (c : G → Fin r → K) (hc : ∀ g h, c (g * h) = c g + ρ g *ᵥ c h)
    (g h : G) (hh : ρ h = 1) : c (g * h * g⁻¹) = ρ g *ᵥ c h := by
  have h1 := hc (g * h * g⁻¹) g
  have h2 : ρ (g * h * g⁻¹) = 1 := by rw [map_mul, map_mul, hh, mul_one, ← map_mul, mul_inv_cancel, map_one]
  rw [inv_mul_cancel_right, hc, h2, one_mulVec] at h1
  linear_combination (exp := 1) -h1

theorem span_abstract (ρ₁ ρ₂ : G →* Matrix (Fin r) (Fin r) K) (σ : G →* G) (L : Subgroup G) [hn : L.Normal] (z : G) (d e : K)
    (hσ : ∀ h ∈ L, σ h ∈ L) (hL₁ : ∀ h ∈ L, ρ₁ h = 1) (hL₂ : ∀ h ∈ L, ρ₂ h = 1)
    (hde : d ≠ e) (z₁ : ρ₁ z = d • (1 : Matrix (Fin r) (Fin r) K)) (z₂ : ρ₂ z = e • (1 : Matrix (Fin r) (Fin r) K))
    (z₃ : ρ₂ (σ z) = d • (1 : Matrix (Fin r) (Fin r) K)) (z₄ : ρ₁ (σ z) = e • (1 : Matrix (Fin r) (Fin r) K))
    (h₁ : Submodule.span K (Set.range ρ₁) = ⊤) (h₂ : Submodule.span K (Set.range (ρ₂.comp σ)) = ⊤)
    (hd : ¬ ∃ A : Matrix (Fin r) (Fin r) K, IsUnit A ∧ ∀ g, ρ₂ (σ g) * A = A * ρ₁ g) {n n' : ℕ} (x : Fin n → G → Fin r → K) (y : Fin n' → G → Fin r → K)
    (hx : ∀ a g h, x a (g * h) = x a g + ρ₁ g *ᵥ x a h) (hy : ∀ a g h, y a (g * h) = y a g + ρ₂ g *ᵥ y a h)
    (ix : ∀ u : Fin n → K, (∀ h ∈ L, ∑ a, u a • x a h = 0) → u = 0)
    (iy : ∀ u : Fin n' → K, (∀ h ∈ L, ∑ a, u a • y a h = 0) → u = 0) (c : Fin n → Fin n' → K)
    (hc : ∀ h ∈ L, ∑ a, ∑ b, c a b * (x a h ⬝ᵥ y b h - x a (σ h) ⬝ᵥ y b (σ h)) = 0) : c = 0 := by
  let B : (Fin n → Fin r → K) → (Fin n' → Fin r → K) → K := fun u v => ∑ a, ∑ b, c a b * (u a ⬝ᵥ v b)
  have hc' : ∀ h ∈ L, B (x · h) (y · h) - B (x · (σ h)) (y · (σ h)) = 0 := by
    intro h hh
    rw [← hc h hh]
    simp only [B, mul_sub, Finset.sum_sub_distrib]
  have Badd : ∀ u u' v v', B (fun a => u a + u' a) (fun b => v b + v' b) = B u v + B u v' + B u' v + B u' v' := by
    intro u u' v v'
    simp only [B, add_dotProduct, dotProduct_add, mul_add, Finset.sum_add_distrib]
    ring
  have Bl : ∀ (t : K) u v, B (fun a => t • u a) v = t * B u v := by
    intro t u v
    simp only [B, smul_dotProduct, smul_eq_mul, Finset.mul_sum, mul_left_comm]
  have Br : ∀ (t : K) u v, B u (fun a => t • v a) = t * B u v := by
    intro t u v
    simp only [B, dotProduct_smul, smul_eq_mul, Finset.mul_sum, mul_left_comm]
  have pol : ∀ h ∈ L, ∀ k ∈ L, B (x · h) (y · k) + B (x · k) (y · h) - B (x · (σ h)) (y · (σ k))
      - B (x · (σ k)) (y · (σ h)) = 0 := by
    intro h hh k hk
    have h3 := hc' _ (L.mul_mem hh hk)
    simp only [map_mul, hx, hy, hL₁ h hh, hL₂ h hh, hL₁ _ (hσ h hh), hL₂ _ (hσ h hh), one_mulVec] at h3
    rw [Badd, Badd] at h3
    linear_combination h3 - hc' h hh - hc' k hk
  have pol' : ∀ h ∈ L, ∀ k ∈ L, ∀ g, B (x · h) (fun b => ρ₂ g *ᵥ y b k) + B (fun a => ρ₁ g *ᵥ x a k) (y · h)
      - B (x · (σ h)) (fun b => ρ₂ (σ g) *ᵥ y b (σ k)) - B (fun a => ρ₁ (σ g) *ᵥ x a (σ k)) (y · (σ h)) = 0 := by
    intro h hh k hk g
    have h3 := pol h hh _ (hn.conj_mem k hk g)
    simp only [map_mul, map_inv, coc_conj ρ₁ _ (hx _) _ _ (hL₁ k hk), coc_conj ρ₂ _ (hy _) _ _ (hL₂ k hk),
      coc_conj ρ₁ _ (hx _) _ _ (hL₁ _ (hσ k hk)), coc_conj ρ₂ _ (hy _) _ _ (hL₂ _ (hσ k hk))] at h3
    exact h3
  have sep : ∀ h ∈ L, ∀ k ∈ L, ∀ g, B (fun a => ρ₁ g *ᵥ x a k) (y · h) =
      B (x · (σ h)) (fun b => ρ₂ (σ g) *ᵥ y b (σ k)) := by
    intro h hh k hk g
    have h3 := pol' h hh k hk (g * z)
    simp only [map_mul, z₁, z₂, z₃, z₄, Matrix.mul_smul, mul_one, smul_mulVec] at h3
    rw [Bl, Bl, Br, Br] at h3
    apply mul_left_cancel₀ (sub_ne_zero.2 hde)
    linear_combination h3 - e * pol' h hh k hk g
  have key : ∀ h ∈ L, ∀ k ∈ L, ∀ Y : Matrix (Fin r) (Fin r) K, B (fun a => Y *ᵥ x a k) (y · h) = 0 := by
    intro h hh k hk Y
    let f₁ : Matrix (Fin r) (Fin r) K →ₗ[K] K :=
      { toFun := fun Y => B (fun a => Y *ᵥ x a k) (y · h)
        map_add' := fun Y Y' => by
          simp only [B, add_mulVec, add_dotProduct, mul_add, Finset.sum_add_distrib]
        map_smul' := fun t Y => by simp only [smul_mulVec, Bl, RingHom.id_apply, smul_eq_mul] }
    let f₂ : Matrix (Fin r) (Fin r) K →ₗ[K] K :=
      { toFun := fun Y => B (x · (σ h)) (fun b => Y *ᵥ y b (σ k))
        map_add' := fun Y Y' => by
          simp only [B, add_mulVec, dotProduct_add, mul_add, Finset.sum_add_distrib]
        map_smul' := fun t Y => by simp only [smul_mulVec, Br, RingHom.id_apply, smul_eq_mul] }
    have := coeff_eq_zero ρ₁ (ρ₂.comp σ) h₁ h₂ hd f₁ f₂ (sep h hh k hk)
    exact LinearMap.congr_fun this Y
  have step : ∀ k ∈ L, ∀ q, (fun b => ∑ a, c a b * x a k q) = 0 := by
    intro k hk q
    apply iy
    intro h hh
    funext p
    have := key h hh k hk (Matrix.single p q 1)
    simp only [B, single_mulVec, one_mul] at this
    rw [Finset.sum_comm] at this
    rw [Pi.zero_apply, ← this, Finset.sum_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [show (Function.update (0 : Fin r → K) p (x a k q)) = Pi.single p (x a k q) from rfl, single_dotProduct, mul_assoc]
  funext a b
  have := ix (fun a => c a b) (fun k hk => by
    funext q
    simpa [Finset.sum_apply] using congrFun (step k hk q) b)
  exact congrFun this a

end Algebra

section Main

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedNoJump (conjHom conjElt_apply conj_conj conj_symm)

def matOf {Γ O : Type} [Group Γ] [CommRing O] {r : ℕ} (ρ : Γ →* GL (Fin r) O) (K : Type) [Field K] [Algebra O K] :
    Γ →* Matrix (Fin r) (Fin r) K :=
  (algebraMap O K).mapMatrix.toMonoidHom.comp ((Units.coeHom _).comp ρ)

theorem matOf_apply {Γ O : Type} [Group Γ] [CommRing O] {r : ℕ} (ρ : Γ →* GL (Fin r) O) (K : Type) [Field K] [Algebra O K]
    (g : Γ) : matOf ρ K g = (ρ g : Matrix (Fin r) (Fin r) O).map (algebraMap O K) := rfl

theorem repOn_one_apply {Γ O : Type} [Group Γ] [CommRing O] {r : ℕ} (ρ : Γ →* GL (Fin r) O) (K : Type) [Field K]
    [Algebra O K] (g : Γ) (v : Fin r → K) : repOn ρ (1 : Γ →* Kˣ) K g v = matOf ρ K g *ᵥ v := by
  funext a
  simp [repOn, matAct, matOf_apply, mulVec, dotProduct]

theorem indep_on {Γ O : Type} [Group Γ] [TopologicalSpace Γ] [CommRing O] {r : ℕ} (ρ : Γ →* GL (Fin r) O) (K : Type) [Field K]
    [Algebra O K] [TopologicalSpace K] [DiscreteTopology K] (L : Subgroup Γ) (z : Γ) (d : K)
    (hL : ∀ h ∈ L, matOf ρ K h = 1) (hz : ∀ g, g * z * g⁻¹ * z⁻¹ ∈ L)
    (hd : matOf ρ K z = d • (1 : Matrix (Fin r) (Fin r) K)) (hd1 : d ≠ 1) {n : ℕ}
    (x : Fin n → Z1 (repOn ρ (1 : Γ →* Kˣ) K))
    (hx : LinearIndependent K (fun a => (Submodule.Quotient.mk (x a) : H1 (repOn ρ (1 : Γ →* Kˣ) K))))
    (u : Fin n → K) (hu : ∀ h ∈ L, ∑ a, u a • (x a).1 h = 0) : u = 0 := by
  funext a
  refine Fintype.linearIndependent_iff.1 hx u ?_ a
  have e : ∑ a, u a • (Submodule.Quotient.mk (x a) : H1 (repOn ρ (1 : Γ →* Kˣ) K)) =
      Submodule.Quotient.mk (∑ a, u a • x a) := by
    rw [← Submodule.mkQ_apply, map_sum]
    simp
  rw [e, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, mem_coboundaries1]
  obtain ⟨m, hm⟩ := cob_of_vanish (matOf ρ K) L z d hL hz hd hd1 (∑ a, u a • x a).1
    (fun g h => by rw [← repOn_one_apply]; exact (∑ a, u a • x a).2.2 g h)
    (fun h hh => by rw [← hu h hh]; simp [Finset.sum_apply])
  exact ⟨m, fun g => by rw [repOn_one_apply]; exact hm g⟩

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N)

theorem eps0_conj (i : X.Tw) (g : GE N) : eps0 X i (conjHom X.cc_cm g) = eps0 X i g := by
  have e : MulSemiringAction.toRingAut (GE N) N.Om (conjHom X.cc_cm g) =
      (X.cc : RingAut N.Om) * MulSemiringAction.toRingAut (GE N) N.Om g * (X.cc : RingAut N.Om)⁻¹ := by
    ext x; rfl
  have : cycZ D.host.E N.Om (X.l i) (conjHom X.cc_cm g) = cycZ D.host.E N.Om (X.l i) g := by
    simp only [cycZ, MonoidHom.comp_apply]
    rw [e, map_mul, map_mul, map_inv, mul_inv_cancel_comm]
  simp only [eps0, MonoidHom.comp_apply]
  rw [this]

theorem conj_conjHom (g : GE N) : conjHom X.cc_cm (conjHom X.cc_cm g) = g := by
  ext x
  change X.cc (X.cc (g (X.cc.symm (X.cc.symm x)))) = g x
  rw [conj_conj X.cc_cm, conj_symm X.cc_cm, conj_symm X.cc_cm, conj_conj X.cc_cm]

theorem spanOdd : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X)
    (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → SpanOdd i s := by
  intro D N X bkP i s hG K _ _ _ _ hK hni ρ hρ z hz L hL n n' x y hx hy c hc
  obtain ⟨hA1, hA2, ⟨A, hA⟩, -, -, -, -⟩ := hG
  obtain ⟨-, hnorm, hcj, hcen, htriv⟩ := hL
  obtain ⟨d, hd, hd2, hd1, hε⟩ := GlobalTheory.TwSys.TameScalar.exists_scalar_tmat_of_tame_inertia D N X bkP i s z hA1 hz
  set φ := algebraMap (X.O0 i) K with hφ
  let ψ : IsLocalRing.ResidueField (X.O0 i) →+* K := Ideal.Quotient.lift _ φ hK
  have hψ : ∀ a, ψ (IsLocalRing.residue _ a) = φ a := fun a => rfl
  set σ := conjHom X.cc_cm with hσ
  have hσc : ∀ g, IsCj X g (σ g) := fun g x => rfl
  set ρ₁ := matOf (Tgl i s) K with hρ₁
  set ρ₂ := matOf ρ K with hρ₂
  let ε : GE N → K := fun g => φ ((eps0 X i g : (X.O0 i)ˣ) : X.O0 i)
  have hε0 : ∀ g, ε g ≠ 0 := fun g => ((eps0 X i g).isUnit.map φ).ne_zero
  have e₁ : ∀ g, ρ₁ g = (Tmat i s g).map φ := fun g => by rw [hρ₁, matOf_apply, Tgl_coe]
  have e₂ : ∀ g, ρ₂ g = ε g • (ρ₁ g⁻¹)ᵀ := fun g => by
    rw [hρ₂, matOf_apply, hρ g, Tdual, ← Tgl_coe, ← Matrix.coe_units_inv, ← map_inv, hρ₁, matOf_apply]
    ext a b
    simp [ε, hφ]
  set A' := (A : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)).map φ with hA'
  set B' := ((A⁻¹ : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)).map φ with hB'
  have hAB : A' * B' = 1 := by rw [hA', hB', ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero φ) (map_one φ)]
  have hBA : B' * A' = 1 := by rw [hA', hB', ← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero φ) (map_one φ)]
  have sd : ∀ g, ρ₂ (σ g) = ε g ^ D.R.t • (A' * ρ₁ g * B') := fun g => by
    rw [hρ₂, matOf_apply, hρ, hA g (σ g) (hσc g), Matrix.map_mul, Matrix.map_mul, e₁, ← smul_mul_assoc, ← mul_smul_comm]
    congr 2
    ext a b
    simp [ε, hφ]
  have hL₁ : ∀ h ∈ L, ρ₁ h = 1 := fun h hh => by
    have : (Tmat i s h).map φ = ((Tmat i s h).map (IsLocalRing.residue _)).map ψ := rfl
    rw [e₁, this, (htriv h hh).1, Matrix.map_one _ (map_zero ψ) (map_one ψ)]
  have hL₂ : ∀ h ∈ L, ρ₂ h = 1 := fun h hh => by
    have : ε h = 1 := by
      change φ _ = 1
      rw [← hψ, (htriv h hh).2, map_one]
    rw [e₂, this, hL₁ _ (L.inv_mem hh), one_smul, transpose_one]
  have hεz : ε z = 1 := by simp [ε, hε]
  set d' := φ (d : X.O0 i) with hd'
  have hd0 : d' ≠ 0 := (d.isUnit.map φ).ne_zero
  have hd1' : d' ≠ 1 := by
    have := (hd1.map φ).ne_zero
    rwa [map_sub, map_one, sub_ne_zero] at this
  have hd2' : d' ≠ d'⁻¹ := by
    have := (hd2.map φ).ne_zero
    rw [map_sub, map_one, map_pow, sub_ne_zero] at this
    intro h
    apply this
    rw [sq, ← hd']
    nth_rewrite 2 [h]
    exact mul_inv_cancel₀ hd0
  have z₁ : ρ₁ z = d' • (1 : Matrix (Fin D.R.r) (Fin D.R.r) K) := by
    rw [e₁, hd]
    ext a b
    simp [hd', Matrix.one_apply, apply_ite φ]
  have z₂ : ρ₂ z = d'⁻¹ • (1 : Matrix (Fin D.R.r) (Fin D.R.r) K) := by
    have h1 : ρ₁ z⁻¹ * ρ₁ z = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
    rw [z₁, Matrix.mul_smul, mul_one] at h1
    have h3 : ρ₁ z⁻¹ = d'⁻¹ • (1 : Matrix (Fin D.R.r) (Fin D.R.r) K) := by rw [← h1, smul_smul, inv_mul_cancel₀ hd0, one_smul]
    rw [e₂, hεz, h3, one_smul, transpose_smul, transpose_one]
  have z₃ : ρ₂ (σ z) = d' • (1 : Matrix (Fin D.R.r) (Fin D.R.r) K) := by
    rw [sd, hεz, one_pow, one_smul, z₁, Matrix.mul_smul, mul_one, Matrix.smul_mul, hAB]
  have z₄ : ρ₁ (σ z) = d'⁻¹ • (1 : Matrix (Fin D.R.r) (Fin D.R.r) K) := by
    have h1 := sd (σ z)
    have h3 : ε (σ z) = 1 := by
      rw [← hεz]
      simp only [ε, hσ, eps0_conj]
    rw [hσ, conj_conjHom, ← hσ, z₂, h3, one_pow, one_smul] at h1
    have h4 : ρ₁ (σ z) = B' * (A' * ρ₁ (σ z) * B') * A' := by
      rw [← mul_assoc, ← mul_assoc, hBA, one_mul, mul_assoc, hBA, mul_one]
    rw [h4, ← h1, Matrix.mul_smul, mul_one, Matrix.smul_mul, hBA]
  have s₁ : Submodule.span K (Set.range ρ₁) = ⊤ := by
    have h1 : ∀ M : Matrix (Fin D.R.r) (Fin D.R.r) (IsLocalRing.ResidueField (X.O0 i)),
        M.map ψ ∈ Submodule.span K (Set.range ρ₁) := by
      intro M
      have hM : M ∈ Submodule.span (IsLocalRing.ResidueField (X.O0 i)) (Set.range (rbar X i s)) := by
        rw [hA2.1]; trivial
      induction hM using Submodule.span_induction with
      | mem _ h =>
        obtain ⟨g, rfl⟩ := h
        have : (rbar X i s g).map ψ = φ ((chiS i s g : (X.O0 i)ˣ) : X.O0 i) • ρ₁ g := by
          rw [e₁]
          ext a b
          simp only [rbar, Tmat, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, hψ]
          rw [← map_mul, Units.mul_inv_cancel_left]
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)
      | zero => rw [Matrix.map_zero _ (map_zero ψ)]; exact Submodule.zero_mem _
      | add a b _ _ ha hb => rw [Matrix.map_add _ (map_add ψ)]; exact Submodule.add_mem _ ha hb
      | smul t a _ ha =>
        have : (t • a).map ψ = ψ t • a.map ψ := by ext; simp
        rw [this]; exact Submodule.smul_mem _ _ ha
    rw [eq_top_iff]
    intro M _
    rw [Matrix.matrix_eq_sum_single M]
    refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_
    have : Matrix.single a b (M a b) = M a b • (Matrix.single a b 1).map ψ := by
      rw [Matrix.map_single, map_one, Matrix.smul_single, smul_eq_mul, mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ (h1 _)
  have s₂ : Submodule.span K (Set.range (ρ₂.comp σ)) = ⊤ := by
    have h1 : ∀ M : Matrix (Fin D.R.r) (Fin D.R.r) K, A' * M * B' ∈ Submodule.span K (Set.range (ρ₂.comp σ)) := by
      intro M
      have hM : M ∈ Submodule.span K (Set.range ρ₁) := by rw [s₁]; trivial
      induction hM using Submodule.span_induction with
      | mem _ h =>
        obtain ⟨g, rfl⟩ := h
        have : A' * ρ₁ g * B' = (ε g ^ D.R.t)⁻¹ • ρ₂ (σ g) := by
          rw [sd, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ (hε0 g)), one_smul]
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)
      | zero => rw [mul_zero, zero_mul]; exact Submodule.zero_mem _
      | add a b _ _ ha hb => rw [mul_add, add_mul]; exact Submodule.add_mem _ ha hb
      | smul t a _ ha => rw [Matrix.mul_smul, Matrix.smul_mul]; exact Submodule.smul_mem _ _ ha
    rw [eq_top_iff]
    intro M _
    have := h1 (B' * M * A')
    rwa [← mul_assoc, ← mul_assoc, hAB, one_mul, mul_assoc, hAB, mul_one] at this
  have hdet : ¬ ∃ A₁ : Matrix (Fin D.R.r) (Fin D.R.r) K, IsUnit A₁ ∧ ∀ g, ρ₂ (σ g) * A₁ = A₁ * ρ₁ g := by
    rintro ⟨A₁, hu, h⟩
    refine hni ⟨A₁, hu, fun g g' hg => ?_⟩
    obtain rfl : g' = σ g := hg.unique (hσc g)
    have := h g
    rwa [hρ₂, matOf_apply, hρ, e₁] at this
  exact span_abstract ρ₁ ρ₂ σ L z d' d'⁻¹ (fun h hh => (hcj h _ (hσc h)).1 hh) hL₁ hL₂ hd2' z₁ z₂ z₃ z₄ s₁ s₂ hdet
    (fun a => (x a).1) (fun b => (y b).1)
    (fun a g h => by rw [← repOn_one_apply]; exact (x a).2.2 g h)
    (fun a g h => by rw [← repOn_one_apply]; exact (y a).2.2 g h)
    (indep_on _ K L z d' hL₁ hcen z₁ hd1' x hx)
    (indep_on _ K L z d'⁻¹ hL₂ hcen z₂ (by simpa using hd1') y hy) c
    (fun h hh => hc h hh _ (hσc h))

end Main

end GlobalTheory.ResSel.SpanOddPf
