import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DatVtEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FramesStdMatched
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteRationalConjMemBoundedCompact
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open Matrix

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.HLatStd

variable {D : D7} {V : HSp D}

def invM (h : Bridge.Gf V) : Matrix (Fin V.rank) (Fin V.rank) (EAf D) :=
  (Units.val ((h⁻¹ : Bridge.Gf V) : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E))).map (swapAE D)

def iv (x : Fin V.rank → D.host.E) : Fin V.rank → EAf D := fun i => x i ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F)

theorem mem_set_iff (hV : Seed.FrmC.StdLat V) (h : Bridge.Gf V) (x : Fin V.rank → D.host.E) :
    (Units.val ((h⁻¹ : Bridge.Gf V) : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E))).mulVec
          (fun i => (1 : Af D.host.F) ⊗ₜ[D.host.F] x i) ∈ latHat D.host.F D.host.E (L0c D V) ↔
      ∀ i, (invM h *ᵥ iv x) i ∈ GlobalTheory.StdFrameExist.SI D := by
  rw [GlobalTheory.StdFrameExist.latHat_iff hV]
  refine forall_congr' fun i => ?_
  rw [RingHom.map_mulVec]
  rfl

theorem iv_natCast_smul (N : ℕ) (x : Fin V.rank → D.host.E) : iv ((N : D.host.E) • x) = (N : EAf D) • iv x := by
  funext i
  simp only [iv, Pi.smul_apply, smul_eq_mul]
  rw [← map_natCast (Algebra.TensorProduct.includeLeftRingHom (R := D.host.F) (A := D.host.E)
    (B := Formalism.L2.Herm.Af D.host.F)) N]
  rw [Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one]

theorem iv_mem_of_int {x : Fin V.rank → D.host.E} (hx : ∀ i, IsIntegral ℤ (x i)) (i : Fin V.rank) :
    iv x i ∈ GlobalTheory.StdFrameExist.SI D := by
  obtain ⟨o, ho⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 D.host.E)).1 (hx i)
  show x i ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F) ∈ _
  rw [← ho]
  exact GlobalTheory.StdFrameExist.tmul_one_mem o

theorem int_of_iv_mem {e : D.host.E} (he : (e ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F) : EAf D) ∈ GlobalTheory.StdFrameExist.SI D) :
    IsIntegral ℤ e := by
  rw [← GlobalTheory.StdFrameExist.mem_ALint_iff] at he
  exact GlobalTheory.StabFin.isIntegral_of_mem e he

theorem mulVec_natCast_smul (M : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) (N : ℕ) (z : Fin V.rank → EAf D) :
    M *ᵥ ((N : EAf D) • z) = ((N : EAf D) • M) *ᵥ z := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem invM_mul (h : Bridge.Gf V) :
    (Units.val ((h : Bridge.Gf V) : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E))).map (swapAE D) * invM h = 1 := by
  rw [invM, ← Matrix.map_mul, ← Units.val_mul, Subgroup.coe_inv, mul_inv_cancel, Units.val_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem invM_hmul (h x : Bridge.Gf V) : invM (h * x) = invM x * invM h := by
  rw [invM, invM, invM, _root_.mul_inv_rev, Subgroup.coe_mul, Units.val_mul, Matrix.map_mul]

theorem fg_of_le_fg {R M : Type*} [CommRing R] [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    {P Q : Submodule R M} (hQ : Q.FG) (hPQ : P ≤ Q) : P.FG := by
  haveI := isNoetherian_of_fg_of_noetherian Q hQ
  have h1 : (P.comap Q.subtype).FG := IsNoetherian.noetherian _
  have h2 := h1.map Q.subtype
  rwa [Submodule.map_comap_subtype, inf_eq_right.mpr hPQ] at h2

theorem mem_hLat_of (hV : Seed.FrmC.StdLat V) (h : Bridge.Gf V) {x : Fin V.rank → D.host.E}
    (hx : ∀ i, (invM h *ᵥ iv x) i ∈ GlobalTheory.StdFrameExist.SI D) : x ∈ Bridge.hLat V h :=
  Submodule.subset_span ((mem_set_iff hV h x).2 hx)

theorem isLattice (hV : Seed.FrmC.StdLat V) (h : Bridge.Gf V) : Submodule.IsLattice D.host.E (Bridge.hLat V h) := by
  obtain ⟨N, hN, hNm⟩ := GlobalTheory.PlaceDatum.exists_den_matrix (GlobalTheory.StdFrameExist.SI D) GlobalTheory.PlaceDatum.exists_den_adele
    ((Units.val ((h : Bridge.Gf V) : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E))).map (swapAE D))
  obtain ⟨N₁, hN₁, hN₁m⟩ := GlobalTheory.PlaceDatum.exists_den_matrix (GlobalTheory.StdFrameExist.SI D) GlobalTheory.PlaceDatum.exists_den_adele
    (invM h)
  have hNE : (N : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  refine ⟨?_, ?_⟩
  ·
    let T : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) :=
      Submodule.span (𝓞 D.host.E) (Set.range fun j : Fin V.rank => (N : D.host.E)⁻¹ • (Pi.single j (1 : D.host.E)))
    refine fg_of_le_fg (Q := T) (Submodule.fg_span (Set.finite_range _)) (Submodule.span_le.2 fun x hx => ?_)
    have hx' := (mem_set_iff hV h x).1 hx
    have hint : ∀ i, IsIntegral ℤ ((N : D.host.E) * x i) := by
      intro i
      refine int_of_iv_mem ?_
      have e1 : ((N : D.host.E) * x i) ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F) =
          (((N : EAf D) • (Units.val ((h : Bridge.Gf V) : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E))).map (swapAE D))
            *ᵥ (invM h *ᵥ iv x)) i := by
        rw [Matrix.smul_mulVec, Matrix.mulVec_mulVec, invM_mul, Matrix.one_mulVec, ← iv_natCast_smul]
        rfl
      rw [e1]
      exact GlobalTheory.StdFrameExist.intV (fun a b => by rw [Matrix.smul_apply, smul_eq_mul]; exact hNm a b) hx' i
    choose c hc using fun i => (IsIntegralClosure.isIntegral_iff (A := 𝓞 D.host.E)).1 (hint i)
    refine (Submodule.mem_span_range_iff_exists_fun (𝓞 D.host.E)).2 ⟨c, ?_⟩
    funext l
    rw [Finset.sum_apply, Finset.sum_eq_single l]
    · rw [Pi.smul_apply, Pi.smul_apply, Pi.single_eq_same, Algebra.smul_def, smul_eq_mul, mul_one, hc]
      field_simp
    · intro b _ hb
      rw [Pi.smul_apply, Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hb), smul_zero, smul_zero]
    · simp
  ·
    refine eq_top_iff.2 ?_
    rw [← (Pi.basisFun D.host.E (Fin V.rank)).span_eq, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rw [Pi.basisFun_apply]
    have hN₁E : (N₁ : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hN₁.ne'
    have hint : ∀ k, IsIntegral ℤ ((Pi.single j (1 : D.host.E) : Fin V.rank → D.host.E) k) := by
      intro k
      rw [Pi.single_apply]
      split_ifs
      · exact isIntegral_one
      · exact isIntegral_zero
    have hA : GlobalTheory.StdFrameExist.IntM (GlobalTheory.StdFrameExist.SI D) ((N₁ : EAf D) • invM h) := fun a b => by
      rw [Matrix.smul_apply, smul_eq_mul]; exact hN₁m a b
    have hmem : (N₁ : D.host.E) • (Pi.single j (1 : D.host.E) : Fin V.rank → D.host.E) ∈ Bridge.hLat V h := by
      refine mem_hLat_of hV h fun i => ?_
      rw [iv_natCast_smul, mulVec_natCast_smul]
      exact GlobalTheory.StdFrameExist.intV hA (iv_mem_of_int hint) i
    have h2 : (N₁ : D.host.E) • (Pi.single j (1 : D.host.E) : Fin V.rank → D.host.E) ∈
        Submodule.span D.host.E (Bridge.hLat V h : Set (Fin V.rank → D.host.E)) := Submodule.subset_span hmem
    have h3 := Submodule.smul_mem _ (N₁ : D.host.E)⁻¹ h2
    rwa [smul_smul, inv_mul_cancel₀ hN₁E, one_smul] at h3

theorem smul_mem_hLat_mul (hV : Seed.FrmC.StdLat V) (h x : Bridge.Gf V) (p : ℕ)
    (hp : ∀ a b, (p : EAf D) * swapAE D ((x⁻¹ : Bridge.Gf V).1.val a b) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    ∀ y ∈ Bridge.hLat V h, (p : 𝓞 D.host.E) • y ∈ Bridge.hLat V (h * x) := by
  have hA : GlobalTheory.StdFrameExist.IntM (GlobalTheory.StdFrameExist.SI D) ((p : EAf D) • invM x) := fun a b => by
    rw [Matrix.smul_apply, smul_eq_mul]; exact hp a b
  have key : ∀ y, (∀ i, (invM h *ᵥ iv y) i ∈ GlobalTheory.StdFrameExist.SI D) → (p : 𝓞 D.host.E) • y ∈ Bridge.hLat V (h * x) := by
    intro y hy
    refine mem_hLat_of hV _ fun i => ?_
    have e : (p : 𝓞 D.host.E) • y = (p : D.host.E) • y := by rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
    rw [e, iv_natCast_smul, mulVec_natCast_smul, invM_hmul, ← Matrix.smul_mul, ← Matrix.mulVec_mulVec]
    exact GlobalTheory.StdFrameExist.intV hA hy i
  intro y hy
  have hle : Bridge.hLat V h ≤ (Bridge.hLat V (h * x)).comap ((p : 𝓞 D.host.E) • LinearMap.id) :=
    Submodule.span_le.2 fun y hy => key y ((mem_set_iff hV h y).1 hy)
  exact hle hy

theorem ratF_val (γ : Formalism.L2.Theta.GQ V) (γE : GL (Fin V.rank) D.host.E) (hγ : Bridge.IsRatMat V γ γE) :
    Units.val ((Bridge.ratF V γ : Bridge.Gf V) : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) =
      γE.val.map (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Af D.host.F ⊗[D.host.F] D.host.E) := by
  show Units.val (finHom V (γ : GA D V)) = _
  rw [finHom, MonoidHom.comp_apply, hγ]
  ext i j
  simp only [Formalism.UG.bc, incA]
  show (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)) ((1 : AF D.host.F) ⊗ₜ[D.host.F] (γE.val i j)) =
    (1 : Af D.host.F) ⊗ₜ[D.host.F] γE.val i j
  rw [Algebra.TensorProduct.map_tmul, map_one]
  rfl

theorem gl_cancel {R : Type} [CommRing R] {n : ℕ} (a b : GL (Fin n) R) (v : Fin n → R) :
    Units.val (b * a)⁻¹ *ᵥ (b.val *ᵥ v) = Units.val a⁻¹ *ᵥ v := by
  rw [Matrix.mulVec_mulVec, _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]

theorem vec_move (γ : Formalism.L2.Theta.GQ V) (γE : GL (Fin V.rank) D.host.E) (hγ : Bridge.IsRatMat V γ γE)
    (h : Bridge.Gf V) (y : Fin V.rank → D.host.E) :
    (Units.val ((Bridge.ratF V γ * h)⁻¹ : Bridge.Gf V).1) *ᵥ (fun i => (1 : Af D.host.F) ⊗ₜ[D.host.F] (γE.val *ᵥ y) i) =
      (Units.val (h⁻¹ : Bridge.Gf V).1) *ᵥ (fun i => (1 : Af D.host.F) ⊗ₜ[D.host.F] y i) := by
  have hv : (fun i => (1 : Af D.host.F) ⊗ₜ[D.host.F] (γE.val *ᵥ y) i) =
      Units.val ((Bridge.ratF V γ : Bridge.Gf V) : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) *ᵥ
        (fun i => (1 : Af D.host.F) ⊗ₜ[D.host.F] y i) := by
    rw [ratF_val γ γE hγ]
    funext i
    exact RingHom.map_mulVec (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Af D.host.F ⊗[D.host.F] D.host.E).toRingHom γE.val y i
  rw [hv]
  exact gl_cancel ((h : Bridge.Gf V) : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E))
    ((Bridge.ratF V γ : Bridge.Gf V) : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) _

theorem mulVec_mem_hLat (γ : Formalism.L2.Theta.GQ V) (γE : GL (Fin V.rank) D.host.E) (hγ : Bridge.IsRatMat V γ γE)
    (h : Bridge.Gf V) : ∀ y ∈ Bridge.hLat V h, γE.val *ᵥ y ∈ Bridge.hLat V (Bridge.ratF V γ * h) := by
  intro y hy
  have hle : Bridge.hLat V h ≤ (Bridge.hLat V (Bridge.ratF V γ * h)).comap
      ((Matrix.mulVecLin γE.val).restrictScalars (𝓞 D.host.E)) :=
    Submodule.span_le.2 fun y hy => Submodule.subset_span (show _ ∈ latHat D.host.F D.host.E (L0c D V) by
      rw [LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply, vec_move γ γE hγ h y]
      exact hy)
  exact hle hy

theorem isRatMat_inv (γ : Formalism.L2.Theta.GQ V) (γE : GL (Fin V.rank) D.host.E) (hγ : Bridge.IsRatMat V γ γE) :
    Bridge.IsRatMat V γ⁻¹ γE⁻¹ := by
  unfold Bridge.IsRatMat at *
  rw [Subgroup.coe_inv, map_inv, map_inv, hγ]

theorem mem_hLat_iff (γ : Formalism.L2.Theta.GQ V) (γE : GL (Fin V.rank) D.host.E) (hγ : Bridge.IsRatMat V γ γE)
    (h : Bridge.Gf V) (y : Fin V.rank → D.host.E) :
    y ∈ Bridge.hLat V h ↔ γE.val *ᵥ y ∈ Bridge.hLat V (Bridge.ratF V γ * h) := by
  refine ⟨mulVec_mem_hLat γ γE hγ h y, fun hy => ?_⟩
  have := mulVec_mem_hLat γ⁻¹ γE⁻¹ (isRatMat_inv γ γE hγ) _ _ hy
  have e1 : Units.val γE⁻¹ *ᵥ (γE.val *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have e2 : Bridge.ratF V γ⁻¹ * (Bridge.ratF V γ * h) = h := by rw [map_inv, inv_mul_cancel_left]
  rw [e1, e2] at this
  exact this

theorem hLat_props : ∀ (D : D7) (V : HSp D), Seed.FrmC.StdLat V → (∀ h, Submodule.IsLattice D.host.E (Bridge.hLat V h)) ∧ (∀ (h x : Bridge.Gf V) (p : ℕ), (∀ a b, (p : EAf D) * swapAE D ((x⁻¹ : Bridge.Gf V).1.val a b) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → ∀ y ∈ Bridge.hLat V h, (p : 𝓞 D.host.E) • y ∈ Bridge.hLat V (h * x)) ∧ ∀ (γ : Formalism.L2.Theta.GQ V) (γE : GL (Fin V.rank) D.host.E), Bridge.IsRatMat V γ γE → ∀ h y, y ∈ Bridge.hLat V h ↔ γE.val.mulVec y ∈ Bridge.hLat V (Bridge.ratF V γ * h) :=
  fun _ _ hV => ⟨isLattice hV, smul_mem_hLat_mul hV, mem_hLat_iff⟩

end GlobalTheory.HLatStd
