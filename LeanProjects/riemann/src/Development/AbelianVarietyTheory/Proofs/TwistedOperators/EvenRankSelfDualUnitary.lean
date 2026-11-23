import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitOff
import Formalism.LocalToGlobal.InertKernelTheory.DefsInt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JetKapIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsOrthonormalBasisFamily
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaPullbackConstantSqEqDet
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DetRationalMatrixTwoSidedMulEqProdEmbeddings
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalisedThetaFamilyNormalisedAllPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormNatCastCoprime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVacuumMovedThetaVacuum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open GlobalTheory.RatMoveJets

noncomputable section

namespace GlobalTheory.RatMoveIop

open Formalism.L2.KerInert Formalism.L2.KerInert.PullbackComparison GlobalTheory.ThLoc.AllPlaces

def NormOne {F : Type} [NormedField F] (lam : Qbar →+* F) (x : ℂ) : Prop := ∃ h : x ∈ Qbar, ‖lam ⟨x, h⟩‖ = 1

section Arith

variable {F : Type} [NormedField F] {lam : Qbar →+* F}

theorem NormOne.one : NormOne lam 1 := ⟨one_mem _, by
  rw [show (⟨1, one_mem _⟩ : Qbar) = 1 from rfl, map_one, norm_one]⟩

theorem NormOne.mul {x y : ℂ} (hx : NormOne lam x) (hy : NormOne lam y) : NormOne lam (x * y) := by
  obtain ⟨h1, h2⟩ := hx
  obtain ⟨h3, h4⟩ := hy
  refine ⟨mul_mem h1 h3, ?_⟩
  rw [show (⟨x * y, mul_mem h1 h3⟩ : Qbar) = ⟨x, h1⟩ * ⟨y, h3⟩ from rfl, map_mul, norm_mul, h2, h4, one_mul]

theorem NormOne.pow {x : ℂ} (hx : NormOne lam x) (n : ℕ) : NormOne lam (x ^ n) := by
  induction n with
  | zero => simpa using NormOne.one
  | succ n ih => rw [pow_succ]; exact ih.mul hx

theorem NormOne.prod {ι : Type} (s : Finset ι) {f : ι → ℂ} (h : ∀ i, NormOne lam (f i)) :
    NormOne lam (∏ i ∈ s, f i) :=
  Finset.prod_induction f (NormOne lam) (fun _ _ => NormOne.mul) NormOne.one fun i _ => h i

theorem NormOne.of_pow {x : ℂ} {n : ℕ} (hn : 0 < n) (hx : NormOne lam (x ^ n)) : NormOne lam x := by
  obtain ⟨h1, h2⟩ := hx
  have h3 : x ∈ Qbar := mem_algebraicClosure_iff.2 ((mem_algebraicClosure_iff.1 h1).of_pow hn)
  refine ⟨h3, ?_⟩
  rw [show (⟨x ^ n, h1⟩ : Qbar) = ⟨x, h3⟩ ^ n from rfl, map_pow, norm_pow] at h2
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h2

theorem NormOne.root {x : ℂ} {n : ℕ} (hn : 0 < n) (hx : x ^ n = 1) : NormOne lam x :=
  NormOne.of_pow hn (hx ▸ NormOne.one)

theorem norm_le_one_of_int {q : ℕ} [Fact q.Prime] {x : ℂ_[q]} (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  have h1 : IsIntegral (NormedField.valuation (K := ℂ_[q])).integer x := hx.tower_top
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := ℂ_[q]))).mem_of_integral h1
  have h3 : ‖x‖₊ ≤ 1 := h2
  exact_mod_cast h3

theorem norm_nat_eq_one {q : ℕ} [Fact q.Prime] {n : ℕ} (hn : n.Coprime q) : ‖(n : ℂ_[q])‖ = 1 := by
  have e : ((n : ℕ) : ℂ_[q]) = algebraMap ℚ_[q] ℂ_[q] ((n : ℕ) : ℚ_[q]) := (map_natCast _ n).symm
  rw [e]
  have h : ‖algebraMap ℚ_[q] ℂ_[q] ((n : ℕ) : ℚ_[q])‖ = ‖((n : ℕ) : ℚ_[q])‖ := PadicComplex.norm_extends' (p := q) _
  rw [h]
  exact Padic.norm_natCast_eq_one_iff.mpr hn.symm

end Arith

variable {D : D7} {N N' : ℕ}

def via {F : Type} [NormedField F] (lam : Qbar →+* F) (φ : D.host.E →+* ℂ) : D.host.E →+* F :=
  lam.comp (φ.codRestrict Qbar (emb_mem D φ))

theorem normOne_emb {F : Type} [NormedField F] (lam : Qbar →+* F) (φ : D.host.E →+* ℂ) {a : D.host.E}
    (h : ‖via lam φ a‖ = 1) : NormOne lam (φ a) := ⟨emb_mem D φ a, h⟩

theorem det_mul_det_star (A : Matrix.unitaryGroup (Fin N) D.host.E) : A.1.det * (star A.1).det = 1 := by
  rw [← Matrix.det_mul, Matrix.mem_unitaryGroup_iff.1 A.2, Matrix.det_one]

theorem norm_det_complex (ρ : D.host.E →+* ℂ) (A : Matrix.unitaryGroup (Fin N) D.host.E) :
    ‖ρ A.1.det‖ = 1 ∧ ‖ρ (star A.1).det‖ = 1 := by
  have h := congrArg (fun x => ‖ρ x‖) (det_mul_det_star A)
  have e : ‖ρ (star A.1).det‖ = ‖ρ A.1.det‖ := by
    rw [Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose, emb_star, RCLike.norm_conj]
  simp only [map_mul, norm_mul, map_one, norm_one, e] at h
  rw [e, and_self]
  nlinarith [norm_nonneg (ρ A.1.det)]

theorem mem_stdL (x : Fin N → D.host.E) : x ∈ stdL D N ↔ ∀ k, IsIntegral ℤ (x k) := by
  have hr : ∀ x : D.host.E, x ∈ (algebraMap (𝓞 D.host.E) D.host.E).range ↔ IsIntegral ℤ x := fun x =>
    ⟨by rintro ⟨a, rfl⟩; exact a.2, fun h => ⟨⟨x, h⟩, rfl⟩⟩
  simp only [stdL, Submodule.mem_pi, Set.mem_univ, forall_true_left, Submodule.mem_one]
  exact forall_congr' fun k => hr (x k)

theorem norm_det_le {q : ℕ} [Fact q.Prime] (ρ : D.host.E →+* ℂ_[q]) (A : Matrix (Fin N) (Fin N) D.host.E) {s : ℕ}
    (hs : s.Coprime q) (h : ∀ x ∈ stdL D N, (s : D.host.E) • A.mulVec x ∈ stdL D N) : ‖ρ A.det‖ ≤ 1 := by
  have h1 : IsIntegral ℤ ((s : D.host.E) • A).det := by
    refine IsIntegral.det fun i j => ?_
    have hj : (Pi.single j 1 : Fin N → D.host.E) ∈ stdL D N := by
      rw [mem_stdL]
      intro k
      rw [Pi.single_apply]
      split_ifs
      · exact isIntegral_one
      · exact isIntegral_zero
    simpa using (mem_stdL _).1 (h _ hj) i
  have h2 : ‖ρ ((s : D.host.E) • A).det‖ ≤ 1 :=
    norm_le_one_of_int (by convert map_isIntegral_int ρ h1; exact Subsingleton.elim _ _)
  rwa [Matrix.det_smul, map_mul, map_pow, map_natCast, norm_mul, norm_pow, norm_nat_eq_one hs, one_pow, one_mul] at h2

theorem norm_det_padic {q : ℕ} [Fact q.Prime] (ρ : D.host.E →+* ℂ_[q]) (A : Matrix.unitaryGroup (Fin N) D.host.E)
    {M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} (h1 : EqAt D q M (stdL D N))
    (h2 : EqAt D q (SDLat.smulLat A.1 M) (stdL D N)) : ‖ρ A.1.det‖ = 1 ∧ ‖ρ (star A.1).det‖ = 1 := by
  obtain ⟨s, hs, a1, a2⟩ := h1
  obtain ⟨t, ht, b1, b2⟩ := h2
  have c1 : ‖ρ A.1.det‖ ≤ 1 := by
    refine norm_det_le ρ _ (Nat.Coprime.mul_left ht hs) fun x hx => ?_
    have := b1 _ ((PullbackComparison.mem_smulLat A.1 M _).2 ⟨_, a2 x hx, rfl⟩)
    rwa [Matrix.mulVec_smul, smul_smul, ← Nat.cast_mul] at this
  have c2 : ‖ρ (star A.1).det‖ ≤ 1 := by
    refine norm_det_le ρ _ (Nat.Coprime.mul_left hs ht) fun x hx => ?_
    obtain ⟨y, hy, e⟩ := (PullbackComparison.mem_smulLat A.1 M _).1 (b2 x hx)
    have e2 : y = (t : D.host.E) • (star A.1).mulVec x := by
      rw [← Matrix.mulVec_smul, ← e, Matrix.mulVec_mulVec, Matrix.mem_unitaryGroup_iff'.1 A.2, Matrix.one_mulVec]
    have := a1 y hy
    rwa [e2, smul_smul, ← Nat.cast_mul] at this
  have h := congrArg (fun x => ‖ρ x‖) (det_mul_det_star A)
  simp only [map_mul, norm_mul, map_one, norm_one] at h
  constructor <;> nlinarith [norm_nonneg (ρ A.1.det), norm_nonneg (ρ (star A.1).det)]

theorem mulV_embV (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (P : Matrix (Fin N') (Fin N') D.host.E)
    (Q : Matrix (Fin N) (Fin N) D.host.E) (B : Matrix (Fin N') (Fin N) D.host.E) :
    GlobalTheory.RatEqui.mulV D P Q (embV D (tor0 D cc δ) B) = embV D (tor0 D cc δ) (P * B * Q) := by
  funext τ
  change P.map (embT D τ) * B.map (embT D τ) * Q.map (embT D τ) = (P * B * Q).map (embT D τ)
  simp only [Matrix.map_mul]

theorem det_move (hG : admG1 D) (P : Matrix (Fin N') (Fin N') D.host.E) (Q : Matrix (Fin N) (Fin N) D.host.E) {r : ℕ}
    {b : Fin r → Matrix (Fin N') (Fin N) D.host.E} (hb : OnB D b) :
    D.host.φ₀ (((Matrix.of fun i j => hYY D (P * b j * Q) (b i)).det : D.host.K) : D.host.E) =
      ∏ τ, embT D τ P.det ^ N * embT D τ Q.det ^ N' := by
  obtain ⟨-, h2, -, -, h5⟩ := GlobalTheory.OnCoord.coords_of_orthonormal_basis D hG ⊤ 1 N N' r b hb
  let e : VC D N N' ≃ₗ[ℂ] (Fin r → ℂ) :=
    LinearEquiv.ofBijective (LinearMap.pi fun j => GlobalTheory.PullNorm.coordLin D (tor0 D ⊤ 1) b j) h5
  have he : ∀ z j, e z j = coordB D (tor0 D ⊤ 1) b j z := fun _ _ => rfl
  refine ((D.host.φ₀.comp (algebraMap D.host.K D.host.E)).map_det _).trans ?_
  rw [← GlobalTheory.TwoSidedDet.det_mulV, ← LinearMap.det_conj _ e, ← LinearMap.det_toLin']
  congr 1
  refine LinearMap.pi_ext' fun i => LinearMap.ext_ring ?_
  have hi : e.symm (Pi.single i 1) = embV D (tor0 D ⊤ 1) (b i) := by
    rw [LinearEquiv.symm_apply_eq]
    funext j
    rw [he, h2, Pi.single_apply, if_congr (eq_comm (a := i)) rfl rfl]
  funext j
  simp only [LinearMap.comp_apply, LinearMap.coe_single, LinearEquiv.coe_coe,
    Matrix.toLin'_apply, Matrix.mulVec_single_one]
  rw [hi, he, mulV_embV, GlobalTheory.OnCoord.coord_emb hG]
  rfl

variable (A : Matrix.unitaryGroup (Fin N) D.host.E) (A' : Matrix.unitaryGroup (Fin N') D.host.E)

theorem back (B : Matrix (Fin N') (Fin N) D.host.E) : star A'.1 * (A'.1 * B * star A.1) * A.1 = B := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mem_unitaryGroup_iff'.1 A'.2, Matrix.one_mul, Matrix.mul_assoc,
    Matrix.mem_unitaryGroup_iff'.1 A.2, Matrix.mul_one]

theorem forth (B : Matrix (Fin N') (Fin N) D.host.E) : A'.1 * (star A'.1 * B * A.1) * star A.1 = B := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mem_unitaryGroup_iff.1 A'.2, Matrix.one_mul, Matrix.mul_assoc,
    Matrix.mem_unitaryGroup_iff.1 A.2, Matrix.mul_one]

theorem onB_move {r : ℕ} {b : Fin r → Matrix (Fin N') (Fin N) D.host.E} (hb : OnB D b) :
    OnB D (fun j => A'.1 * b j * star A.1) := by
  refine ⟨?_, ?_⟩
  · have := ortho_pull (star A.1) (star A'.1) (by rw [star_star]; exact Matrix.mem_unitaryGroup_iff'.1 A.2)
      (by rw [star_star]; exact Matrix.mem_unitaryGroup_iff'.1 A'.2) b hb.1
    simpa only [star_star] using this
  · have e : (Set.range fun j => A'.1 * b j * star A.1) = PQK A'.1 (star A.1) '' Set.range b := by
      rw [← Set.range_comp]; rfl
    rw [e, ← Submodule.map_span, hb.2, Submodule.map_top, LinearMap.range_eq_top]
    exact fun B => ⟨_, forth A A' B⟩

variable (cc : Ideal (𝓞 D.host.K)) (δ : ℂ)

def push : VC D N N' ≃+ VC D N N' := (tPullEquiv cc δ A A').symm.toAddEquiv

theorem push_symm (z : VC D N N') : (push A A' cc δ).symm z = tPull D (tor0 D cc δ) A.1 A'.1 z := rfl

theorem hf_symm (x y : VC D N N') :
    Hf D (tor0 D cc δ) ((push A A' cc δ).symm x) ((push A A' cc δ).symm y) = Hf D (tor0 D cc δ) x y :=
  Hf_tPull cc δ _ _ (Matrix.mem_unitaryGroup_iff.1 A.2) (Matrix.mem_unitaryGroup_iff.1 A'.2) x y

theorem hf_push (x y : VC D N N') :
    Hf D (tor0 D cc δ) (push A A' cc δ x) (push A A' cc δ y) = Hf D (tor0 D cc δ) x y := by
  rw [← hf_symm A A', AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]

theorem symm_emb (w : ℂ) (B : Matrix (Fin N') (Fin N) D.host.E) :
    (push A A' cc δ).symm (w • embV D (tor0 D cc δ) (A'.1 * B * star A.1)) = w • embV D (tor0 D cc δ) B := by
  rw [push_symm, PullbackComparison.tPull_smul, tPull_embV, back]

theorem push_LaB {r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (x : VC D N N') :
    push A A' cc δ x ∈ LaB D (tor0 D cc δ) (fun j => A'.1 * b j * star A.1) ↔ x ∈ LaB D (tor0 D cc δ) b := by
  refine GlobalTheory.RatEquiv.closure_iff _ ?_ ?_ x
  · rintro _ ⟨w, hw, j, rfl⟩
    refine AddSubgroup.subset_closure ⟨w, hw, j, ?_⟩
    rw [← symm_emb A A', AddEquiv.apply_symm_apply]
  · rintro _ ⟨w, hw, j, rfl⟩
    exact AddSubgroup.subset_closure ⟨w, hw, j, symm_emb A A' cc δ w _⟩

theorem push_La (M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (x : VC D N N') :
    push A A' cc δ x ∈ Formalism.MainNotions.TaylorLogMetric.La D (tor0 D cc δ) (SDLat.smulLat A.1 M) (SDLat.smulLat A'.1 M') ↔
      x ∈ Formalism.MainNotions.TaylorLogMetric.La D (tor0 D cc δ) M M' := by
  rw [mem_La_smulLat_iff, ← push_symm, AddEquiv.symm_apply_apply]

theorem pullB_move (hC : Crv D cc δ) {r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (g : ℂ → ℂ) :
    pullB D (tor0 D cc δ) (fun j => A'.1 * b j * star A.1) g =
      fun z => pullB D (tor0 D cc δ) b g ((push A A' cc δ).symm z) := by
  funext z
  unfold pullB
  refine Finset.prod_congr rfl fun j _ => ?_
  congr 1
  have h := hf_symm A A' cc δ z ((1 : ℂ) • embV D (tor0 D cc δ) (A'.1 * b j * star A.1))
  rw [symm_emb, one_smul, one_smul] at h
  have ha : ((area (tor0 D cc δ).abelian₂ : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (GlobalTheory.UnitaryTheta.area_pos D cc δ hC).ne'
  exact ((div_left_inj' ha).1 h).symm

theorem iop_move (hI : GlobalTheory.NormSum.Inp D) {t0 : ℂ} (hC : Crv D cc δ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0)
    {e0 : VC D N N' → ℂ} (hE : ThetaVectorUpToUnits D (tor0 D cc δ) t0 (stdL D N) (stdL D N') e0)
    {M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (hM : SD D M) (hM' : SD D M') :
    ∃ ε : ℂ, (∀ (F : Type) [NormedField F] (lam : Qbar →+* F),
        (∀ τ, ‖via lam (embT D τ) A'.1.det‖ = 1 ∧ ‖via lam (embT D τ) (star A.1).det‖ = 1) → NormOne lam ε) ∧
      ∀ z, Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D cc δ) M M') e0
          (tPull D (tor0 D cc δ) A.1 A'.1 z) =
        ε * Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N')
          (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D cc δ) (SDLat.smulLat A.1 M) (SDLat.smulLat A'.1 M')) e0 z := by
  obtain ⟨b, κ, hb, -, he⟩ := hE
  have hb' := onB_move A A' hb
  obtain ⟨hP, hP0, -⟩ := GlobalTheory.UnitaryTheta.pullB_mem D cc δ hC t0 ht N N' _ b hb
  have hKb : KLat D (tor0 D cc δ) (LaB D (tor0 D cc δ) b) := Or.inl ⟨_, b, hb, rfl⟩
  have hKb' : KLat D (tor0 D cc δ) (LaB D (tor0 D cc δ) fun j => A'.1 * b j * star A.1) := Or.inl ⟨_, _, hb', rfl⟩
  have hK0 : KLat D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') :=
    Or.inr ⟨_, _, GlobalTheory.MovedVacuum.sd_stdL D N, GlobalTheory.MovedVacuum.sd_stdL D N', rfl⟩
  have hK1 : KLat D (tor0 D cc δ) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D cc δ) M M') := Or.inr ⟨_, _, hM, hM', rfl⟩
  have hK2 : KLat D (tor0 D cc δ)
      (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D cc δ) (SDLat.smulLat A.1 M) (SDLat.smulLat A'.1 M')) :=
    Or.inr ⟨_, _, GlobalTheory.UnitaryBases.isSDLat_smulLat A hM, GlobalTheory.UnitaryBases.isSDLat_smulLat A' hM', rfl⟩
  obtain ⟨c, ζ, m, hm, hζ, hc, hpull⟩ := GlobalTheory.UnitaryTheta.const_sq_eq_det D cc δ hC t0 ht N N' _ b _ hb hb'
  rw [det_move hI.g1 _ _ hb] at hc
  obtain ⟨μ₁, hμ₁, hI₁⟩ := hI.mu cc δ hC N N' _ _ _ hKb hK0 hK1 _ hP
  obtain ⟨μ₂, hμ₂, hI₂⟩ := hI.mu cc δ hC N N' _ _ _ hKb hK0 hK2 _ hP
  obtain ⟨μ₃, hμ₃, hI₃⟩ := hI.mu cc δ hC N N' _ _ _ hKb hKb' hK2 _ hP
  change e0 = fun z => κ * Iop D (tor0 D cc δ) (LaB D (tor0 D cc δ) b) (La0 D (tor0 D cc δ) N N')
    (pullB D (tor0 D cc δ) b (GL3Theta.th0 (lamOf D cc δ) t0)) z at he
  obtain ⟨-, hH, -, hII⟩ := hI.uni cc δ hC N N' _ _ hKb hK1 _ hP
  have hH0 : Iop D (tor0 D cc δ) (LaB D (tor0 D cc δ) b) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D cc δ) M M')
      (pullB D (tor0 D cc δ) b (GL3Theta.th0 (lamOf D cc δ) t0)) ≠ 0 := by
    intro h
    rw [h] at hII
    rw [← hII] at hP0
    simp [Iop, Formalism.MainNotions.TaylorLogMetric.U] at hP0
  refine ⟨c * μ₁ * μ₃ * μ₂ ^ 7, fun F _ lam h => ?_, fun z => ?_⟩
  · have h8 : 0 < 8 := by norm_num
    refine (((NormOne.of_pow two_pos ?_).mul (.root h8 hμ₁)).mul (.root h8 hμ₃)).mul ((NormOne.root h8 hμ₂).pow 7)
    rw [hc]
    exact (NormOne.root hm hζ).mul (NormOne.prod _ fun τ =>
      ((normOne_emb lam _ (h τ).1).pow N).mul ((normOne_emb lam _ (h τ).2).pow N'))
  · have h1 := GlobalTheory.RatEquiv.iop_transport (tor0 D cc δ) (push A A' cc δ) (hf_push A A' cc δ) (push_LaB A A' cc δ b)
      (push_La A A' cc δ M M') hP hH hH0 ((push A A' cc δ).symm z)
    rw [← pullB_move A A' cc δ hC, AddEquiv.apply_symm_apply, hpull, GlobalTheory.RatEquiv.Iop_smul, hI₃, push_symm] at h1
    rw [he, GlobalTheory.RatEquiv.Iop_smul, GlobalTheory.RatEquiv.Iop_smul, hI₁, hI₂]
    beta_reduce at h1 ⊢
    rw [← h1]
    linear_combination (-(c * μ₁ * μ₃ * κ * Iop D (tor0 D cc δ) (LaB D (tor0 D cc δ) b)
      (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D cc δ) (SDLat.smulLat A.1 M) (SDLat.smulLat A'.1 M'))
      (pullB D (tor0 D cc δ) b (GL3Theta.th0 (lamOf D cc δ) t0)) z)) * hμ₂

theorem iop_pull_rat : GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {δ t0 : ℂ}, Crv D D.host.ccK δ →
    GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D D.host.ccK δ) t0 → ∀ {N N' : ℕ} {e0 : VC D N N' → ℂ}, oddE0 D D.host.ccK δ t0 N N' e0 → Even (N * N') →
    ∀ (M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), SD D M → SD D M' →
    ∀ (U : Matrix.unitaryGroup (Fin N) D.host.E) (U' : Matrix.unitaryGroup (Fin N') D.host.E),
    ∃ ε : ℂ, Mod1All ε ∧ (∀ (q : ℕ) [Fact q.Prime], EqAt D q M (stdL D N) → EqAt D q M' (stdL D N') →
        EqAt D q (SDLat.smulLat U.1 M) (stdL D N) → EqAt D q (SDLat.smulLat U'.1 M') (stdL D N') → GlobalTheory.MovedKappaEx.UnitAt q ε) ∧
      ∀ z, Iop D (tor0 D D.host.ccK δ) (La0 D (tor0 D D.host.ccK δ) N N') (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK δ) M M') e0
          (Formalism.L2.KerInert.tPull D (tor0 D D.host.ccK δ) U.1 U'.1 z) =
        ε * Iop D (tor0 D D.host.ccK δ) (La0 D (tor0 D D.host.ccK δ) N N')
          (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK δ) (SDLat.smulLat U.1 M) (SDLat.smulLat U'.1 M')) e0 z := by
  intro _ hI D δ t0 hC ht N N' e0 he _ M M' hM hM' A A'
  obtain ⟨ε, h1, h2⟩ := iop_move A A' D.host.ccK δ (hI D) hC ht he.2.2.2.1 hM hM'
  have hc : ∀ σ : Qbar →+* ℂ, NormOne σ ε := fun σ =>
    h1 ℂ σ fun τ => ⟨(norm_det_complex _ A').1, (norm_det_complex _ A).2⟩
  refine ⟨ε, ⟨(hc (algebraMap Qbar ℂ)).1, fun σ => (hc σ).2⟩, fun q _ a1 a2 a3 a4 lam => ?_, h2⟩
  obtain ⟨h3, h4⟩ := h1 ℂ_[q] lam fun τ => ⟨(norm_det_padic _ A' a2 a4).1, (norm_det_padic _ A a1 a3).2⟩
  rw [lamC, dif_pos h3]
  exact h4

end GlobalTheory.RatMoveIop
