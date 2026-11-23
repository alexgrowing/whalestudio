import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KmapEq
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KmapOfOkOfVecP
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ThetaStepDistributionEquivariantRational
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.XiEntryInvariant
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FirstCoupledKernelEquivariantCosets
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KAtTopEquiv
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThetaLocalEquivalence.ThEquivPOf
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThetaLocalEquivalence.ThEquivPStepCIff
import Formalism.LocalToGlobal.KernelLattices.ENatEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrdSubConjEqNeg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GmapToAddSubgroup
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.RkVolLaHyp
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.RkConj

noncomputable section

namespace GlobalTheory.KerDia.Eqv

section Chi

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2
  GlobalTheory.Mem.ChiIdeal GlobalTheory.Mem.Chr.DetOrd
open scoped nonZeroDivisors

theorem isChi_car : ∀ (D : Formalism.L2.Ker.Car) (χ : Formalism.L2.Host.HChar D.host.E), Formalism.L2.Host.IsChiPsi D.host χ → Formalism.L2.Ker.Cd.TaylorLogMetric.IsChi D (chiId χ) := by
  intro D χ hχ
  obtain ⟨c, hc, hcm, hr, -⟩ := GlobalTheory.Mem.HostCM.host_cm D.R D.host
  have hv := prod_val_above χ hχ.unr hχ.triv hr
  have hpl := fun w w' => (under_eq_iff_conjPl c hcm.rank hcm.ne w w').1
  refine ⟨?_, ?_⟩
  · rintro A B ⟨A', hA', hA⟩ ⟨B', hB', hB⟩
    obtain ⟨fA, a, ha⟩ := frac_of_mul_eq_one hA
    obtain ⟨fB, b, hb⟩ := frac_of_mul_eq_one hB
    have nA := ordSub_finite fA a ha
    have nB := ordSub_finite fB b hb
    have nAB : {w | ordSub w A + ordSub w B ≠ 0}.Finite := (nA.union nB).subset fun w hw => by
      by_contra h0
      simp only [Set.mem_union, not_or, Set.mem_setOf_eq, not_not] at h0
      exact hw (by rw [h0.1, h0.2, add_zero])
    unfold chiId
    rw [← Units.val_mul]
    congr 1
    simp only [← zpow_natCast, ordSub_mul fA a ha fB b hb]
    rw [← finprod_val_add χ _ _ (finite_toNat nA) (finite_toNat nB)]
    refine finprod_val_congr χ hv _ _ (finite_toNat nAB) ((nA.union nB).subset fun w hw => ?_) fun w w' h => ?_
    · by_contra h0
      simp only [Set.mem_union, not_or, Set.mem_setOf_eq, not_not] at h0
      exact hw (by simp [h0.1, h0.2])
    · rcases hpl w w' h with rfl | h
      · rfl
      · rw [ordSub_conj_eq_neg h (fun x => (hA' x).trans (by rw [← hc]; rfl)) hA,
          ordSub_conj_eq_neg h (fun x => (hB' x).trans (by rw [← hc]; rfl)) hB]
        omega
  · letI := D.host.cmStar
    intro z
    have hcmf : IsCMField D.host.E := D.host.isCMField_hostE
    have hcc : ∀ x, IsCMField.complexConj D.host.E x = D.host.conj x := fun x => bridge_star_holds D.R D.host x
    have hinv : ∀ x, c (c x) = x := fun x => by
      rw [hc, hc, ← hcc, ← hcc, IsCMField.complexConj_apply_apply]
    have hz : (z : D.host.E) * c (z : D.host.E) = 1 := by
      rw [hc, ← bridge_star_holds D.R D.host]
      exact z.2.2
    obtain ⟨k, hk⟩ := exists_mul_conj_eq (c : D.host.E →+* D.host.E) hinv
      (by by_contra hn; push Not at hn; exact hcm.ne (AlgEquiv.ext hn)) z hz
    have hk' : (z : D.host.E) * c (k : D.host.E) = k := hk
    have z0 : (z : D.host.E) ≠ 0 := left_ne_zero_of_mul_eq_one hz
    have k0 : c (k : D.host.E) ≠ 0 := by simp
    have hu : Units.mk0 _ z0 * Units.mk0 _ k0 = k := Units.ext hk'
    have e1 := chiId_span_singleton χ (Units.mk0 _ z0)
    rw [Units.val_mk0] at e1
    have e2 : ∏ᶠ w, χ.val w ^ (Formalism.L2.Host.ordF w (Units.mk0 _ z0)).toNat = ∏ᶠ w, χ.val w ^ Formalism.L2.Host.ordF w k := by
      simp only [← zpow_natCast]
      refine finprod_val_congr χ hv _ _ (finite_toNat (ordF_finite _)) (ordF_finite _) fun w w' h => ?_
      rcases hpl w w' h with rfl | h
      · rfl
      · have a1 := ordF_mul' w (Units.mk0 _ z0) (Units.mk0 _ k0)
        have a2 := ordF_mul' w' (Units.mk0 _ z0) (Units.mk0 _ k0)
        have a3 := ordF_conj h k (Units.mk0 _ k0) rfl
        have a4 := ordF_conj h (Units.mk0 _ k0) k (hinv _).symm
        rw [hu] at a1 a2
        omega
    have e3 := GlobalTheory.HeckeProduct.productRule χ ∅ (fun v _ => hχ.unr v) k
    simp only [Finset.prod_empty, mul_one, Finset.notMem_empty, not_false_eq_true, finprod_true] at e3
    rw [mul_comm, mul_eq_one_iff_eq_inv] at e3
    rw [e1, e2, e3, Units.val_inv_eq_inv_val, hχ.inf k, ← Finset.prod_inv_distrib]
    refine (Fintype.prod_equiv D.eTau _ _ fun τ => ?_).symm
    congr 1
    refine (phase_sq_eq ((map_ne_zero _).2 k.ne_zero) ?_).symm
    have hcj : Formalism.L2.Host.embPsi D.host (D.eTau τ) (D.host.conj (k : D.host.E)) =
        starRingEnd ℂ (Formalism.L2.Host.embPsi D.host (D.eTau τ) (k : D.host.E)) := Formalism.HC.HostAx.conjE_apply _ _ _
    rw [← hcj, ← hc]
    exact (map_mul (Formalism.L2.Host.embPsi D.host (D.eTau τ)) _ _).symm.trans (congrArg _ hk')

end Chi

section Ana

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2
attribute [local instance] GlobalTheory.Mem.Col2.starE

def carOf (B : GlobalTheory.Mem.Base) : Car := ⟨B.R, B.host, ⟨B.R.Psi, by
  rw [Formalism.BasicNotions.Examples₂.card_Psi, Ranks.f, Ranks.n]⟩, Equiv.refl _⟩

def seamC (B : GlobalTheory.Mem.Base) : Cd.Seam (carOf B) B.fields := ⟨RingEquiv.refl _, Equiv.refl _, B.embLL⟩

theorem seamC_ok (B : GlobalTheory.Mem.Base) : (seamC B).Ok :=
  ⟨fun τ x => DFunLike.congr_fun (B.fields_embC τ) x, fun x => B.fields_star x⟩

theorem seamC_lat (B : GlobalTheory.Mem.Base) {n : ℕ} (M : Submodule (𝓞 B.host.E) (Fin n → B.host.E)) : (seamC B).lat M = M := by
  have h : (seamC B).lat M = Submodule.span (𝓞 B.host.E) (id '' (M : Set (Fin n → B.host.E))) := rfl
  rw [h, Set.image_id, Submodule.span_eq]

def vacC (B : GlobalTheory.Mem.Base) (J : AmbIn B.host) : Cd.Base (carOf B) ⊤ J.δ :=
  ⟨J.V.L, J.V.lat, J.V.ω₀, J.V.t0, J.V.γ₀, J.V.gC, J.V.gC_spec,
    ⟨J.V.kc.pp, J.V.kc.pp_over, J.V.kc.pi, J.V.kc.pi_gen, J.V.kc.gaP, J.V.kc.gaP_at, J.V.kc.rt, J.V.kc.rt_pow⟩⟩

theorem amb_eq (B : GlobalTheory.Mem.Base) (J : AmbIn B.host) (χ : Submodule (𝓞 B.host.E) B.host.E → ℂ) :
    J.amb B χ = Cd.ambOf (seamC B) (vacC B J) χ J.cD := by
  unfold Cd.ambOf
  simp only [seamC_lat]
  rfl

theorem thCEq_of_ind {X : Fields} (A : Amb X) (a b : ℕ) (Sa : Finset (HeightOneSpectrum (𝓞 X.E))) (hL : A.LaHyp a b Sa) (h0 : A.AA ≠ ⊥)
    (hT : ∀ D, 0 < D → A.ThIndEq a b Sa D) : A.ThCEq a b Sa := by
  intro γ γ' N N' cA cB Ξ hN hN' hA hB hΞ hS z
  have key : ∀ (M : Submodule (𝓞 X.E) (Sp X.E a)) (M' : Submodule (𝓞 X.E) (Sp X.E b)) (Φ : HomE X.E a b → ℂ), IsSdLat M → IsSdLat M' →
      (∀ x, Φ x ≠ 0 → x ∈ divLat cA (homAt Sa M M')) → (∀ x y, y ∈ mulLat cB (homAt Sa M M') → Φ (x + y) = Φ x) → ∀ w,
      thC (X.embC A.σ₀) A.δ A.d A.sc A.AA Sa M M' (cA * cB) Φ (A.e a b M M') w =
        latSum (divLat cA (homAt Sa M M')) (mulLat cB (homAt Sa M M')) fun x => Φ x * A.thInd Sa M M' cB x w :=
    fun M M' Φ hM hM' h1 h2 w => (GlobalTheory.latSum_thInd_eq_thC X A a b Sa M M' cA cB Φ (indTieD_of_la A a b Sa _ (Nat.mul_pos hA hB) hL)
      hM hM' hA hB (GlobalTheory.ThetaMove.VolumePos.volC_pos X.E a b A.AA Sa M M' hM.1.fg hM'.1.fg hM.1.span_eq_top hM'.1.span_eq_top
        hL.2.2.2.2.1 h0) (GlobalTheory.finite_divLat_quot_mulLat_homAt X.E a b Sa M M' cA cB hM.1 hM'.1 hA hB) h1 h2 w).symm
  have hmul : mulLat cB (homAt Sa (Formalism.HermitianLatticesTheory.gmap γ.1 N) (Formalism.HermitianLatticesTheory.gmap γ'.1 N')) =
      (mulLat cB (homAt Sa N N')).map (conjE γ.1 γ'.1 : HomE X.E a b →ₗ[𝓞 X.E] HomE X.E a b) := by rw [homAt_gmap, mulLat_map]
  have hdiv : divLat cA (homAt Sa (Formalism.HermitianLatticesTheory.gmap γ.1 N) (Formalism.HermitianLatticesTheory.gmap γ'.1 N')) =
      (divLat cA (homAt Sa N N')).map (conjE γ.1 γ'.1 : HomE X.E a b →ₗ[𝓞 X.E] HomE X.E a b) := by rw [homAt_gmap, divLat_map]
  have hinv : ∀ x w, w ∈ mulLat cB (homAt Sa (Formalism.HermitianLatticesTheory.gmap γ.1 N) (Formalism.HermitianLatticesTheory.gmap γ'.1 N')) →
      Ξ ((conjE γ.1 γ'.1).symm (x + w)) = Ξ ((conjE γ.1 γ'.1).symm x) := fun x w hw => by
    rw [hmul] at hw
    obtain ⟨y, hy, rfl⟩ := hw
    rw [map_add]
    exact (congrArg (fun t => Ξ (_ + t)) (LinearEquiv.symm_apply_apply _ y)).trans (hΞ _ y hy)
  have hadd : ∀ x w, w ∈ mulLat cB (homAt Sa (Formalism.HermitianLatticesTheory.gmap γ.1 N) (Formalism.HermitianLatticesTheory.gmap γ'.1 N')) →
      A.thInd Sa (Formalism.HermitianLatticesTheory.gmap γ.1 N) (Formalism.HermitianLatticesTheory.gmap γ'.1 N') cB (x + w) = A.thInd Sa (Formalism.HermitianLatticesTheory.gmap γ.1 N) (Formalism.HermitianLatticesTheory.gmap γ'.1 N') cB x :=
    fun x w hw => by
      have h : A.IsLift Sa (Formalism.HermitianLatticesTheory.gmap γ.1 N) (Formalism.HermitianLatticesTheory.gmap γ'.1 N') cB (x + w) =
          A.IsLift Sa (Formalism.HermitianLatticesTheory.gmap γ.1 N) (Formalism.HermitianLatticesTheory.gmap γ'.1 N') cB x := by
        funext s
        refine propext (and_congr_right fun _ => ?_)
        rw [← sub_sub]
        exact Submodule.sub_mem_iff_left _ hw
      unfold Amb.thInd Amb.liftW
      rw [h]
  rw [key N N' _ hN hN' (fun x hx => by_contra fun h => hx (by rw [hS x h, map_zero])) fun x y hy => congrArg A.σ₀ (hΞ x y hy)]
  refine (key _ _ (fun x => A.σ₀ (Ξ ((conjE γ.1 γ'.1).symm x))) (isSdLat_gmap hN γ) (isSdLat_gmap hN' γ') (fun x hx => ?_)
    (fun x y hy => congrArg A.σ₀ (hinv x y hy)) z).trans ?_
  · rw [hdiv, Submodule.mem_map_equiv]
    exact by_contra fun h => hx (by rw [hS _ h, map_zero])
  rw [hdiv, hmul, latSum_map]
  · unfold latSum
    refine finsum_congr fun q => ?_
    beta_reduce
    rw [LinearEquiv.symm_apply_apply, conjE_apply,
      hT (cA * cB) (Nat.mul_pos hA hB) γ γ' N N' cB _ ⟨hN, hN', hB, Dvd.intro_left _ rfl, divLat_mul_of cA cB _ (Subtype.prop _)⟩ z]
  · intro x w hw
    rw [← hmul] at hw
    rw [hinv x w hw, hadd x w hw]

theorem ana {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (h : I.Ok) (a : I.ι) (u : B.Word) (i j : ℕ) :
    I.A.ThCEq (B.R.N i) (B.R.N j) (Sall (Pr := B.primes X) I.sel (I.tup a) u) ∧ I.A.ChiLaw (B.R.N i) (B.R.N j) ∧
      I.A.EOmega (B.R.N i) (B.R.N j) := by
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  have he : ∀ k, Even (B.R.N k) := fun k => Formalism.L2.Ker.even_rankN B.R k
  have bad := GlobalTheory.ThetaMove.BadPrimes.bad_primes B.fields (B.primes X) I.sel I.S (I.tup a) u hX hPr h.sel_ok (h.T_mem u) h.g_mem
  have hcc : Cd.TaylorLogMetric.IsCurveIdeal (carOf B) ⊤ := ⟨top_ne_bot, by simp⟩
  have hδ : Cd.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice (carOf B) ⊤ I.J.δ := h.amb_ok.delta
  have hχ : Cd.TaylorLogMetric.IsChi (carOf B) I.chi := isChi_car (carOf B) _ I.C.isChi
  have h0 : I.A.AA ≠ ⊥ := by
    rw [I.A_AA, Ne, FractionalIdeal.coeToSubmodule_eq_bot]
    exact inv_ne_zero (FractionalIdeal.coeIdeal_ne_zero.2 (Cd.half_ne_bot (carOf B)))
  have hL := Cd.laHyp_ambOf_top (seamC B) I.chi I.J.cD (vacC B I.J) (seamC_ok B) hδ (he i) (he j) _ (fun P hP => (bad P hP).1)
    fun P hP => Cd.primeTo_half _ (by
      have := P.isPrime
      obtain ⟨t, ht, ht'⟩ := SetLike.not_le_iff_exists.1 fun hle => GlobalTheory.PeriodIdealUnit.not_dvd_different (K := B.host.K) (E := B.host.E)
        (bad P hP).2.1 P.asIdeal (Ideal.absNorm_mem _) (bad P hP).2.2.1 (Ideal.dvd_iff_le.2 hle)
      exact ⟨t, ht, ht'⟩)
  have hE := Cd.CarC.eqLaw_ambOf_of (seamC B) (vacC B I.J) I.chi I.J.cD (seamC_ok B)
    (Cd.PairingIndexBounds.Eq.SqG.eqP_car (vacC B I.J) hcc hδ I.chi hχ) (he i) (he j)
  have hC := Cd.CarC.chiLaw_ambOf_of (seamC B) (vacC B I.J) I.chi I.J.cD (seamC_ok B) hχ (he i) (he j)
  have hO := Cd.CarC.eOmega_ambOf_of (seamC B) (vacC B I.J) I.chi I.J.cD ((vacC B I.J).stdOK hcc hδ) (B.R.N i) (B.R.N j)
  rw [← amb_eq] at hL hE hC hO
  exact ⟨thCEq_of_ind I.A _ _ _ hL h0 fun D hD => IndEq.thIndEq_of_vacEq B.fields I.A _ _ _ D hX hL h0 hD hE, hC, hO⟩

end Ana

section Frames

open Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.Mem.Col2 MvPolynomial

variable {E K ι : Type} [Field E] [Field K] [Fintype ι] (emb : ι → E →+* K) (σ : K →+* ℂ)

def matAt {n : ℕ} (γ : GL (Fin n) E) (τ : ι) : Matrix (Fin n) (Fin n) ℂ := (γ : Matrix (Fin n) (Fin n) E).map (embAt σ emb τ)

def detPow {n : ℕ} (γ : GL (Fin n) E) (s : ι → ℤ) : ℂ := ∏ τ, embAt σ emb τ (γ : Matrix (Fin n) (Fin n) E).det ^ s τ

variable {n : ℕ}

theorem emb_det_ne (γ : GL (Fin n) E) (τ : ι) : embAt σ emb τ (γ : Matrix (Fin n) (Fin n) E).det ≠ 0 :=
  (map_ne_zero _).2 ((Matrix.isUnit_iff_isUnit_det _).1 γ.isUnit).ne_zero

theorem detPow_ne (γ : GL (Fin n) E) (s : ι → ℤ) : detPow emb σ γ s ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun τ _ => zpow_ne_zero _ (emb_det_ne emb σ γ τ)

theorem de_move (s : ι → ℤ) (γ : GL (Fin n) E) (y : Fr emb σ n) :
    ∏ τ, deFr y τ ^ s τ = detPow emb σ γ s * ∏ τ, deFr (GlobalTheory.Mem.Col2.frMul emb σ γ⁻¹ y) τ ^ s τ := by
  rw [detPow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← mul_zpow]
  congr 1
  have e : y = GlobalTheory.Mem.Col2.frMul emb σ γ (GlobalTheory.Mem.Col2.frMul emb σ γ⁻¹ y) := by rw [← GlobalTheory.Mem.Col2.frMul_mul, mul_inv_cancel, GlobalTheory.Mem.Col2.frMul_one]
  conv_lhs => rw [e]
  show ((γ : Matrix (Fin n) (Fin n) E).map (embAt σ emb τ) * _).det = _
  rw [Matrix.det_mul, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  rfl

theorem fnOf_apply (P : Pol ℂ ι n) (y : Fr emb σ n) :
    fnOf (Gr emb σ n) 0 1 P y = eval (fun v : ι × Fin n × Fin n => y.1 v.1 v.2.1 v.2.2) P := by
  simp [fnOf]

theorem fnOf_move (γ : GL (Fin n) E) (P : Pol ℂ ι n) (y : Fr emb σ n) :
    fnOf (Gr emb σ n) 0 1 P (GlobalTheory.Mem.Col2.frMul emb σ γ y) = fnOf (Gr emb σ n) 0 1 (Formalism.GradedWeylDivisibility.blockAct ℂ (matAt emb σ γ) P) y := by
  rw [fnOf_apply, fnOf_apply, TE.eval_blockAct]
  rfl

theorem polOf_fnOf_one (P : Pol ℂ ι n) : polOf (Gr emb σ n) 0 (fr0 emb σ n) (fnOf (Gr emb σ n) 0 1 P) = P := by
  have e : (fun τ => ((fr0 emb σ n).1 τ)⁻¹) = (1 : ι → Matrix (Fin n) (Fin n) ℂ) := funext fun _ => inv_one
  rw [← e]
  exact polOf_fnOf _ _ _ P

theorem blockAct_inv (γ : GL (Fin n) E) (P : Pol ℂ ι n) :
    Formalism.GradedWeylDivisibility.blockAct ℂ (matAt emb σ γ) (Formalism.GradedWeylDivisibility.blockAct ℂ (matAt emb σ γ⁻¹) P) = P := by
  refine fnOf_injective (Gr emb σ n) 0 1 (fun _ => by simp) (fr0 emb σ n) (funext fun y => ?_)
  rw [← fnOf_move, ← fnOf_move, ← GlobalTheory.Mem.Col2.frMul_mul, inv_mul_cancel, GlobalTheory.Mem.Col2.frMul_one]

def opOf {a b : ℕ} (s' s : ι → ℤ) (cD : ι → ℂ) (G : VCx ι a b → ℂ) (x : Fr emb σ a → ℂ) (y' : Fr emb σ b) : ℂ :=
  (∏ τ, deFr y' τ ^ s τ)⁻¹ * fnOf (Gr emb σ b) 0 1 (jetMap (jetC cD G) 0
    (polOf (Gr emb σ a) 0 (fr0 emb σ a) fun y => (∏ τ, deFr y τ ^ s' τ) * x y)) y'

theorem opOf_move {a b : ℕ} (s' s : ι → ℤ) (cD : ι → ℂ) {G G' : VCx ι a b → ℂ} (hG : ContDiff ℂ ⊤ G) (γ : GL (Fin a) E)
    (γ' : GL (Fin b) E) (c : Kˣ) (κ : ℂ) (h : ∀ z, G' z = κ * G (TE.mulL (matAt emb σ γ'⁻¹) (matAt emb σ γ) z))
    {x : Fr emb σ a → ℂ} {P : Pol ℂ ι a} (hP : fnOf (Gr emb σ a) 0 1 P = fun y => (∏ τ, deFr y τ ^ s' τ) * x y) (y' : Fr emb σ b) :
    detPow emb σ γ' s * opOf emb σ s' s cD G' (trFr emb σ γ c x) y' =
      κ * (σ c * detPow emb σ γ s') * opOf emb σ s' s cD G x (GlobalTheory.Mem.Col2.frMul emb σ γ'⁻¹ y') := by
  have h1 : (fun y => (∏ τ, deFr y τ ^ s' τ) * trFr emb σ γ c x y) =
      (σ c * detPow emb σ γ s') • fnOf (Gr emb σ a) 0 1 (Formalism.GradedWeylDivisibility.blockAct ℂ (matAt emb σ γ⁻¹) P) := by
    funext y
    rw [Pi.smul_apply, smul_eq_mul, ← fnOf_move, hP, trFr_apply, de_move emb σ s' γ y]
    ring
  have hj : ∀ m, jetC cD G' m = κ * jetC cD (fun z => G (TE.mulL (matAt emb σ γ'⁻¹) (matAt emb σ γ) z)) m := fun m => by
    have hs : ContDiff ℂ ⊤ fun z => G (TE.mulL (matAt emb σ γ'⁻¹) (matAt emb σ γ) z) :=
      hG.comp (LinearMap.toContinuousLinearMap (TE.mulL (matAt emb σ γ'⁻¹) (matAt emb σ γ))).contDiff
    have e : G' = κ • fun z => G (TE.mulL (matAt emb σ γ'⁻¹) (matAt emb σ γ) z) := funext h
    unfold jetC derivAt0
    rw [e, iteratedFDeriv_const_smul_apply (hs.of_le le_top).contDiffAt, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    ring
  have h2 := TE.jetMap_pull (RingHom.id ℂ) cD G hG (matAt emb σ γ) (matAt emb σ γ'⁻¹) (TE.mulL (matAt emb σ γ'⁻¹) (matAt emb σ γ))
    (TE.mulL_coordX _ _) (jetC cD G) (jetC cD G') 1 κ (fun m => (one_mul _).symm) hj κ (mul_one _).symm 0
    (Formalism.GradedWeylDivisibility.blockAct ℂ (matAt emb σ γ⁻¹) P)
  rw [blockAct_inv] at h2
  have hd : ∏ τ, deFr (GlobalTheory.Mem.Col2.frMul emb σ γ'⁻¹ y') τ ^ s τ ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun τ _ => zpow_ne_zero _ ((GlobalTheory.Mem.Col2.frMul emb σ γ'⁻¹ y').2 τ).ne_zero
  have hd' := detPow_ne emb σ γ' s
  unfold opOf
  rw [h1, ← hP, map_smul, polOf_fnOf_one, polOf_fnOf_one, map_smul, h2, map_smul, map_smul, Pi.smul_apply, Pi.smul_apply, ← fnOf_move,
    de_move emb σ s γ' y']
  simp only [Pi.zero_apply, pow_zero, Finset.prod_const_one, mul_one, smul_eq_mul]
  field_simp

theorem opOf_equiv {a b : ℕ} (s' s : ι → ℤ) (cD : ι → ℂ) {G G' : VCx ι a b → ℂ} (hG : ContDiff ℂ ⊤ G) (γ : GL (Fin a) E)
    (γ' : GL (Fin b) E) (c c' : Kˣ) {ρ ρ' : ℂ} (hρ : ρ' ≠ 0)
    (h : ∀ z, ρ' * G' z = (detPow emb σ γ s')⁻¹ * detPow emb σ γ' s * σ ((c' * c⁻¹ : Kˣ) : K) * ρ *
      G (TE.mulL (matAt emb σ γ'⁻¹) (matAt emb σ γ) z))
    {x : Fr emb σ a → ℂ} {P : Pol ℂ ι a} (hP : fnOf (Gr emb σ a) 0 1 P = fun y => (∏ τ, deFr y τ ^ s' τ) * x y) (y' : Fr emb σ b) :
    ρ' * opOf emb σ s' s cD G' (trFr emb σ γ c x) y' = σ c' * (ρ * opOf emb σ s' s cD G x (GlobalTheory.Mem.Col2.frMul emb σ γ'⁻¹ y')) := by
  have key := opOf_move emb σ s' s cD hG γ γ' c _
    (fun z => ((eq_inv_mul_iff_mul_eq₀ hρ).2 (h z)).trans (mul_assoc _ _ _).symm) hP y'
  have d1 := detPow_ne emb σ γ s'
  have d2 := detPow_ne emb σ γ' s
  have c1 : σ (c : K) ≠ 0 := (map_ne_zero _).2 (Units.ne_zero _)
  rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀] at key
  refine mul_left_cancel₀ d2 ?_
  rw [mul_left_comm, key]
  field_simp

end Frames

section Theta

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker

variable {E : Type} [Field E] [NumberField E] [StarRing E] {ι : Type} [Fintype ι] {a b : ℕ} (emb : ι → E →+* ℂ) (δ : ℂ)
  (d : ℕ) (sc : ℝ) (AA : Submodule (𝓞 E) E) (SS : Finset (HeightOneSpectrum (𝓞 E))) (N : Submodule (𝓞 E) (Sp E a))
  (N' : Submodule (𝓞 E) (Sp E b)) (c : ℕ)

theorem thC_contDiff (Ξ : HomE E a b → ℂ) {θ : VCx ι a b → ℂ} (h : ContDiff ℂ ⊤ θ) :
    ContDiff ℂ ⊤ (thC emb δ d sc AA SS N N' c Ξ θ : VCx ι a b → ℂ) := by
  unfold thC xiV xiL xiS
  exact ContDiff.sum fun x _ => contDiff_const.mul (TE.contDiff_opU_top _ _ _ (TE.contDiff_sumU_top _ _ _ _ h))

theorem thC_mul (r : ℂ) (Ξ : HomE E a b → ℂ) (θ : VCx ι a b → ℂ) (z : VCx ι a b) :
    thC emb δ d sc AA SS N N' c (fun x => r * Ξ x) θ z = r * thC emb δ d sc AA SS N N' c Ξ θ z := by
  have h : ∀ v : VCx ι a b, onV emb δ (fun x => r * Ξ x) v = r * onV emb δ Ξ v := fun v => by
    unfold onV
    split_ifs
    · rfl
    · rw [mul_zero]
  simp only [thC, xiV, xiL, xiS, hatS, Formalism.L2.Th1.H.sumU, Formalism.L2.Th1.H.opU, h, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

end Theta

section Datum

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2 GlobalTheory.TopStep GlobalTheory.TopLaw

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ} {u : Pr.Word}

theorem xiOver_law (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (hL : L.Ok Ch sel mu cst G m2) (hs : cst.sharp = true)
    {j : ℕ} (h : j = R.m) (al : L.β (m2 + 1)) {Λ : LevFam X.E X.K (R.N j) Pr.vGs}
    {Θ : LevQFam X.E X.K (R.N j) (QE sel (mu : Chr X.F X.E X.K))}
    (hΛ : Λ = (topLev Ch sel mu cst (rPsymF (R := R) Ch)).levG j) (hΘ : Θ = (topLev Ch sel mu cst (rPsymF (R := R) Ch)).levQ j)
    {γ : UF X.E (R.N (m2 + 1))} {γ' : UF X.E (R.N j)} {p q : ChPt (R := R) sel mu u (m2 + 1)} {p' q' : ChPt (R := R) sel mu u j}
    {Y : Set (Sp X.E (R.N (m2 + 1)))} (hp1 : Y ∈ ybSet sel mu cst p.deco.1.N)
    (hp2 : (fun v => γ.1 v) '' Y ∈ ybSet sel mu cst q.deco.1.N)
    {κ : GLQ X.E (R.N (m2 + 1)) (rowSG Pr sel mu)} {κ' : GLQ X.E (R.N j) (rowSG Pr sel mu)} {a a' : rowSG Pr sel mu → X.Kˣ}
    (hκ : ∀ P, frsF sel mu q P = γ.1 * (frsF sel mu p P * ((κ P)⁻¹).1))
    (hκ' : ∀ P, frsF sel mu q' P = γ'.1 * (frsF sel mu p' P * ((κ' P)⁻¹).1))
    (ha : ∀ P, LevAt (L.levG (m2 + 1) al) (L.levQ (m2 + 1) al) P (κ P) (a P)) (ha' : ∀ P, LevAt Λ Θ P (κ' P) (a' P))
    (x : HomE X.E (R.N (m2 + 1)) (R.N j))
    (e0 : phiT X.K q.deco.1 q'.deco.1 (γ'.1.toLinearMap ∘ₗ x ∘ₗ γ.1.symm.toLinearMap) = phiT X.K p.deco.1 p'.deco.1 x) :
    xiOver Ch sel mu cst m2 h q ((fun v => γ.1 v) '' Y) q' (γ'.1.toLinearMap ∘ₗ x ∘ₗ γ.1.symm.toLinearMap) *
        ∏ P : rowSG Pr sel mu, (rhoS Ch sel mu (m2 + 1) P ((LinearEquiv.det (κ⁻¹ P).1 : X.Eˣ) : X.E) *
          rhoT Ch sel mu (m2 + 1) P ((LinearEquiv.det (κ'⁻¹ P).1 : X.Eˣ) : X.E)) =
      (((∏ P, a' P) * (∏ P, a P)⁻¹ : X.Kˣ) : X.K) * xiOver Ch sel mu cst m2 h p Y p' x := by
  subst h
  obtain rfl := hΛ.trans (topLev_levG_m_eq Ch sel mu cst _)
  obtain rfl := hΘ.trans (topLev_levQ_m_eq Ch sel mu cst _)
  exact xiTop_law default hX hPr hsel hL (Or.inr ⟨hs, rfl⟩) hp1 hp2 hκ hκ' ha ha' x e0

variable (Ch sel mu cst L u) in

abbrev St (j : ℕ) : GStep X.E X.K (R.N j) := stepAt sel mu cst L (topLev Ch sel mu cst (rPsymF (R := R) Ch)) u j

set_option maxHeartbeats 1000000 in

theorem xiAt_law (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (hT : Pr.T u ∈ S) (hg : ∀ k, Pr.g k ∈ S)
    (hL : L.Ok Ch sel mu cst G m2) (hs : cst.sharp = true) {i : ℕ} (hi : i < R.m) (b : Idx sel mu L i) (b' : Idx sel mu L (i + 1))
    (g : (St Ch sel mu cst L u i).G b) (g' : (St Ch sel mu cst L u (i + 1)).G b') (p : (St Ch sel mu cst L u i).D b)
    (p' : (St Ch sel mu cst L u (i + 1)).D b') :
    ∃ (κ : GLQ X.E (R.N i) (rowSG Pr sel mu)) (κ' : GLQ X.E (R.N (i + 1)) (rowSG Pr sel mu)),
      (∀ P, frsF sel mu ((St Ch sel mu cst L u i).act b g p).1.1 P = g.1.1 * (frsF sel mu p.1.1 P * (κ P).1)) ∧
      (∀ P, frsF sel mu ((St Ch sel mu cst L u (i + 1)).act b' g' p').1.1 P = g'.1.1 * (frsF sel mu p'.1.1 P * (κ' P).1)) ∧
      ∀ x, xiAt Ch sel mu cst L u i b b' ((St Ch sel mu cst L u i).act b g p) ((St Ch sel mu cst L u (i + 1)).act b' g' p')
          (g'.1.1.toLinearMap ∘ₗ x ∘ₗ g.1.1.symm.toLinearMap) *
        ∏ P : rowSG Pr sel mu, (rhoS Ch sel mu i P ((LinearEquiv.det (κ P).1 : X.Eˣ) : X.E) *
          rhoT Ch sel mu i P ((LinearEquiv.det (κ' P).1 : X.Eˣ) : X.E)) =
        (((St Ch sel mu cst L u (i + 1)).chr b' g' * ((St Ch sel mu cst L u i).chr b g)⁻¹ : X.Kˣ) : X.K) *
          xiAt Ch sel mu cst L u i b b' p p' x := by
  have hm := hL.hm
  have hd := (tilOk_of_avoid (mu := mu) hPr hsel u ⟨hT, hg⟩).2.2
  obtain ⟨κ, a, hκ, ha, ea⟩ := exists_pass hd g p.1.1
  obtain ⟨κ', a', hκ', ha', ea'⟩ := exists_pass hd g' p'.1.1
  refine ⟨κ⁻¹, κ'⁻¹, hκ, hκ', fun x => ?_⟩
  have e1 : (St Ch sel mu cst L u i).chr b g = ∏ P, a P := ea.symm
  have e2 : (St Ch sel mu cst L u (i + 1)).chr b' g' = ∏ P, a' P := ea'.symm
  rw [e1, e2]
  obtain ⟨al, rfl⟩ : ∃ al, b = Idx.of al hi := ⟨_, (Idx.of_get b hi _).symm⟩
  rcases lt_trichotomy (i + 2) R.m with h | h | h
  · obtain ⟨be, rfl⟩ : ∃ be, b' = Idx.of be (by omega) := ⟨_, (Idx.of_get b' (by omega) _).symm⟩
    rw [xiAt_entry Ch sel mu cst L h rfl rfl, xiAt_entry Ch sel mu cst L h rfl rfl]
    exact MatLaw.xiEntry_law hX hPr hsel hL (by omega) hκ hκ' ha ha' x (phiT_act _ _ _ _ _ _ _)
  · obtain rfl : m2 = i := by omega
    obtain ⟨be, rfl⟩ : ∃ be, b' = Idx.of be (by omega) := ⟨_, (Idx.of_get b' (by omega) _).symm⟩
    rw [xiAt_penultimate_eq_xiCpl1 Ch sel mu cst L h rfl, xiAt_penultimate_eq_xiCpl1 Ch sel mu cst L h rfl]
    have hY := PtAt.mem_ybSet p' h
    exact CoupledLaw.xiCpl1_law hX hPr hL hY (PtAt.mem_ybSet ((St Ch sel mu cst L u (m2 + 1)).act _ g' p') h) hκ hκ' ha ha' x (phiT_act _ _ _ _ _ _ _)
  · obtain rfl : i = m2 + 1 := by omega
    have h1 : m2 + 1 + 1 = R.m := by omega
    rw [xiAt_last Ch sel mu cst L h1, xiAt_last Ch sel mu cst L h1]
    have hY := PtAt.mem_ybSet p h1
    exact xiOver_law hX hPr hsel hL hs h1 al (levGAt_of_le sel mu L _ h1.ge b') (levQAt_of_le sel mu L _ h1.ge b') hY
      (PtAt.mem_ybSet ((St Ch sel mu cst L u (m2 + 1)).act _ g p) h1) hκ hκ' ha ha' x (phiT_act _ _ _ _ _ _ _)

end Datum

section Scalar

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker

variable {X : Fields} (A : Amb X) {a b : ℕ} {Sa SB : Finset (HeightOneSpectrum (𝓞 X.E))}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ} {mI sS sT : SB → X.E → X.K}

theorem scal_theta {e : X.Tau → ℤ} (hC : A.ThCEq a b Sa) (hχ : A.ChiLaw a b) (hMa : MuProdLaw a sel SB mU mI e)
    (hMb : MuProdLaw b sel SB mU mI e) (hDa : MuDetLaw a mI sS) (hDb : MuDetLaw b mI sS) (hU : UnitInv sS sT)
    (γ : UF X.E a) (γ' : UF X.E b) {N : Submodule (𝓞 X.E) (Sp X.E a)} {N' : Submodule (𝓞 X.E) (Sp X.E b)} (hN : IsSdLat N)
    (hN' : IsSdLat N') (fr : Frs X.E a SB) (fr' : Frs X.E b SB) (κ : GLQ X.E a SB) (κ' : GLQ X.E b SB) {cA cB : ℕ} (hA : 0 < cA)
    (hB : 0 < cB) {Ξ Ξ' : HomE X.E a b → X.K} (hΞ : GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree.InBox Sa cA cB N N' Ξ) (r : X.K)
    (law : ∀ x, Ξ' (γ'.1.toLinearMap ∘ₗ x ∘ₗ γ.1.symm.toLinearMap) * ∏ P : SB, (sS P ((LinearEquiv.det (κ P).1 : X.Eˣ) : X.E) *
      sT P ((LinearEquiv.det (κ' P).1 : X.Eˣ) : X.E)) = r * Ξ x) (z : VCx X.Tau a b) :
    A.σ₀ (muInvDet sel SB mU mI (gmap γ.1 N) (fun P => γ.1 * (fr P * (κ P).1)) *
        (muInvDet sel SB mU mI (gmap γ'.1 N') fun P => γ'.1 * (fr' P * (κ' P).1))⁻¹) * (A.chiF a b (gmap γ.1 N) (gmap γ'.1 N'))⁻¹ *
        thC (X.embC A.σ₀) A.δ A.d A.sc A.AA Sa (gmap γ.1 N) (gmap γ'.1 N') (cA * cB) (fun x => A.σ₀ (Ξ' x))
          (A.e a b (gmap γ.1 N) (gmap γ'.1 N')) z =
      (∏ τ, X.embC A.σ₀ τ ((LinearEquiv.det γ.1 : X.Eˣ) : X.E) ^ (e τ - ((b / 2 : ℕ) : ℤ)))⁻¹ *
        (∏ τ, X.embC A.σ₀ τ ((LinearEquiv.det γ'.1 : X.Eˣ) : X.E) ^ (e τ - ((a / 2 : ℕ) : ℤ))) * A.σ₀ r *
        (A.σ₀ (muInvDet sel SB mU mI N fr * (muInvDet sel SB mU mI N' fr')⁻¹) * (A.chiF a b N N')⁻¹) *
        thC (X.embC A.σ₀) A.δ A.d A.sc A.AA Sa N N' (cA * cB) (fun x => A.σ₀ (Ξ x)) (A.e a b N N') (A.pullV a b γ.1 γ'.1 z) := by
  set Pi : X.K := ∏ P : SB, (sS P ((LinearEquiv.det (κ P).1 : X.Eˣ) : X.E) * sT P ((LinearEquiv.det (κ' P).1 : X.Eˣ) : X.E)) with hPi
  have h1 : muInvDet sel SB mU mI N (fun P => fr P * (κ P).1) * (muInvDet sel SB mU mI N' fun P => fr' P * (κ' P).1)⁻¹ =
      Pi * (muInvDet sel SB mU mI N fr * (muInvDet sel SB mU mI N' fr')⁻¹) := by
    unfold muInvDet
    simp only [hPi, hDa _ _ _, hDb _ _ _, hU _ _, Finset.prod_mul_distrib, Finset.prod_inv_distrib, mul_inv]
    ring
  have h2 : (fun y => A.σ₀ Pi * A.σ₀ (Ξ' y)) = fun y => A.σ₀ r * A.σ₀ (Ξ (γ'.1.symm.toLinearMap ∘ₗ y ∘ₗ γ.1.toLinearMap)) := by
    funext y
    rw [← map_mul, ← map_mul, ← law, mul_comm]
    congr 3
    exact LinearMap.ext fun v => by simp
  have h3 := thC_mul (X.embC A.σ₀) A.δ A.d A.sc A.AA Sa (gmap γ.1 N) (gmap γ'.1 N') (cA * cB) (A.σ₀ Pi) (fun x => A.σ₀ (Ξ' x))
    (A.e a b (gmap γ.1 N) (gmap γ'.1 N')) z
  rw [h2, thC_mul, hC γ γ' N N' cA cB Ξ hN hN' hA hB (fun x y => hΞ.2 x y) (fun x hx => by_contra fun h0 => hx (hΞ.1 x h0))] at h3
  rw [hMa γ N (fun P => fr P * (κ P).1) hN, hMb γ' N' (fun P => fr' P * (κ' P).1) hN', hχ γ γ' N N' hN hN', mul_inv, mul_mul_mul_comm,
    h1, map_mul, map_mul, map_mul A.σ₀ Pi, map_inv₀, map_prod, map_prod]
  have d0 : ∀ τ, X.embC A.σ₀ τ ((LinearEquiv.det γ.1 : X.Eˣ) : X.E) ≠ 0 := fun τ => (map_ne_zero _).2 (Units.ne_zero _)
  have d0' : ∀ τ, X.embC A.σ₀ τ ((LinearEquiv.det γ'.1 : X.Eˣ) : X.E) ≠ 0 := fun τ => (map_ne_zero _).2 (Units.ne_zero _)
  have e1 : ∀ τ (w : X.E) (k : ℤ), A.σ₀ (X.emb τ w ^ k) = X.embC A.σ₀ τ w ^ k := fun τ w k => map_zpow₀ _ _ _
  simp only [e1]
  simp only [zpow_sub₀ (d0 _), zpow_sub₀ (d0' _), zpow_neg, Finset.prod_div_distrib, Finset.prod_inv_distrib, Finset.prod_zpow,
    mul_inv, inv_inv, div_eq_mul_inv, Finset.prod_mul_distrib]
  generalize thC (X.embC A.σ₀) A.δ A.d A.sc A.AA Sa (gmap γ.1 N) (gmap γ'.1 N') (cA * cB) (fun x => A.σ₀ (Ξ' x))
    (A.e a b (gmap γ.1 N) (gmap γ'.1 N')) z = t' at h3 ⊢
  generalize thC (X.embC A.σ₀) A.δ A.d A.sc A.AA Sa N N' (cA * cB) (fun x => A.σ₀ (Ξ x)) (A.e a b N N') (A.pullV a b γ.1 γ'.1 z) = t at h3 ⊢
  rw [show ∀ x y p m w s : ℂ, x * y * (p * m) * w * s = x * y * m * w * (p * s) from fun _ _ _ _ _ _ => by ring, ← h3]
  ring

end Scalar

section Main

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.KerDia
attribute [local instance] GlobalTheory.Mem.Col2.starE

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (h : I.Ok) (u : B.Word) (a : I.ι) (i : ℕ)
  {b : (I.stp u a i).β} {b' : (I.stp u a (i + 1)).β} (q : (I.stp u a i).D b) (q' : (I.stp u a (i + 1)).D b')

include h in

theorem th_contDiff : ContDiff ℂ ⊤ (I.th u a i b b' q q') :=
  thC_contDiff _ _ _ _ _ _ _ _ _ _ ((ana I h a u i (i + 1)).2.2 _ _ ⟨q.1.1.deco.2.lat, q.1.1.deco.2.uni⟩
    ⟨q'.1.1.deco.2.lat, q'.1.1.deco.2.uni⟩)

theorem half_cast (R : Ranks) (k : ℕ) : (((R.N k / 2 : ℕ) : ℤ) : ℚ) = (R.N k : ℚ) / 2 := by
  obtain ⟨c, hc⟩ := N_even R k
  have : R.N k / 2 = c := by omega
  rw [this, hc]
  push_cast
  ring

include h in
set_option maxHeartbeats 1000000 in

theorem th_move (g : (I.stp u a i).G b) (g' : (I.stp u a (i + 1)).G b') (z : VCx B.fields.Tau (B.R.N i) (B.R.N (i + 1))) :
    I.rho u a i b ((I.stp u a i).act b g q) * I.rho' u a i b' ((I.stp u a (i + 1)).act b' g' q') *
        I.th u a i b b' ((I.stp u a i).act b g q) ((I.stp u a (i + 1)).act b' g' q') z =
      (detPow B.fields.emb B.embLL ((I.stp u a i).gam b g) ((I.chain l u a).sSharp i))⁻¹ *
        detPow B.fields.emb B.embLL ((I.stp u a (i + 1)).gam b' g') ((I.chain l u a).sDiv i) *
        B.embLL (((I.stp u a (i + 1)).chr b' g' * ((I.stp u a i).chr b g)⁻¹ : B.fields.Kˣ) : B.fields.K) *
        (I.rho u a i b q * I.rho' u a i b' q') *
        I.th u a i b b' q q' (TE.mulL (matAt B.fields.emb B.embLL ((I.stp u a (i + 1)).gam b' g')⁻¹)
          (matAt B.fields.emb B.embLL ((I.stp u a i).gam b g)) z) := by
  by_cases hi : i < B.R.m
  swap
  · unfold TC.th
    rw [thAt_of_le _ _ _ _ _ _ (by omega), thAt_of_le _ _ _ _ _ _ (by omega)]
    simp
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  obtain ⟨hC, hχ, -⟩ := ana I h a u i (i + 1)
  choose ez hez using fun τ => (B.hcW u τ).e_int ⟨i, hi⟩
  have hmu := fun n => GlobalTheory.KerT.RatLaw.muProdLaw (Pr := B.primes X) (GlobalTheory.Mem.FieldsLaws.fields_satisfy_definite_laws B).1 hPr h.sel_ok u (h.T_mem u) h.g_mem
    h.ch_tied (h.idx_ok a).muqG ⟨i, hi⟩ ez (fun τ => by rw [← B.hcW_e u τ]; exact hez τ) n
  have hD := fun n => muDetLaw_chain (Pr := B.primes X) I.Ch I.sel (I.tup a) (I.cst a) i n
  rw [muAt_eq_muAtT I.Ch I.sel (I.tup a) (I.cst a) (muqTie_of_ok _ _ _ _ _ (h.idx_ok a)) i hi] at hD
  obtain ⟨κ, κ', hκ, hκ', law⟩ := xiAt_law (Pr := B.primes X) hX hPr h.sel_ok (h.T_mem u) h.g_mem (h.idx_ok a) (h.sharp a) hi b b' g g' q q'
  have hbox := GlobalTheory.LvT.Built.Box.inBox_xiAt B.fields (B.primes X) B.R I.Ch I.sel I.S (I.tup a) (I.cst a) (I.idx a) I.glob (B.R.m - 2) u i
    hX hPr h.sel_ok (h.T_mem u) h.g_mem (h.idx_ok a) hi ⟨_, _, _, _, h.ch_tied⟩ b b' q q'
  have key := scal_theta I.A hC hχ (hmu _) (hmu _) (hD _) (hD _) (unitInv_rho I.Ch I.sel (I.tup a) i) g.1 g'.1
    ⟨q.1.1.deco.2.lat, q.1.1.deco.2.uni⟩ ⟨q'.1.1.deco.2.lat, q'.1.1.deco.2.uni⟩ (frsF I.sel (I.tup a) q.1.1) (frsF I.sel (I.tup a) q'.1.1)
    κ κ' (pow_pos (Finset.prod_pos fun P _ => qOf_pos P.1) _ : 0 < cAof (Pr := B.primes X) I.sel (I.tup a) (I.cst a))
    (GlobalTheory.MoveCompare.cBof_pos hPr I.sel (I.tup a) (I.cst a) u) hbox _ law z
  have r1 := GlobalTheory.LvT.Built.KMap.rhoIs I h a u hi b q b' q'
  have r2 := GlobalTheory.LvT.Built.KMap.rhoIs I h a u hi b ((I.stp u a i).act b g q) b' ((I.stp u a (i + 1)).act b' g' q')
  have s1 : (I.chain l u a).sSharp i = fun τ => ez τ - ((B.R.N (i + 1) / 2 : ℕ) : ℤ) := funext fun τ => by
    apply Int.cast_injective (α := ℚ)
    rw [Int.cast_sub, half_cast, ← hez]
    exact (congrArg _ (dif_pos hi)).trans (floor_sub_half _ _ _)
  have s2 : (I.chain l u a).sDiv i = fun τ => ez τ - ((B.R.N i / 2 : ℕ) : ℤ) := funext fun τ => by
    apply Int.cast_injective (α := ℚ)
    rw [Int.cast_sub, half_cast, ← hez]
    exact (congrArg _ (dif_pos hi)).trans (floor_sub_half _ _ _)
  have d1 : ∀ {n : ℕ} (γ : UF B.fields.E n) (s : B.fields.Tau → ℤ), detPow B.fields.emb B.embLL (ufGL B.fields.E n γ) s =
      ∏ τ, B.fields.embC I.A.σ₀ τ ((LinearEquiv.det γ.1 : B.fields.Eˣ) : B.fields.E) ^ s τ := fun γ s => by
    rw [detPow, TE.det_ufGL]
    rfl
  have m1 : ∀ {n : ℕ} (γ : UF B.fields.E n), (fun τ => (TE.matT B.fields.emb γ τ).map I.A.σ₀) =
      matAt B.fields.emb B.embLL (ufGL B.fields.E n γ) := fun γ => funext fun τ => Matrix.map_map
  rw [← funext hκ, ← funext hκ', Formalism.L2.Ker.pullV_eq, m1, m1, map_inv, ← d1, ← d1, ← s1, ← s2] at key
  exact (congrArg (· * _) r2).trans (key.trans (congrArg (fun w => _ * w * _) r1.symm))

theorem ent_apply (x : GlobalTheory.Mem.Col2.Fr B.fields.emb B.embLL (B.R.N i) → ℂ) (y' : GlobalTheory.Mem.Col2.Fr B.fields.emb B.embLL (B.R.N (i + 1))) :
    ent I l u a i q q' x y' = I.rho u a i b q * I.rho' u a i b' q' *
      opOf B.fields.emb B.embLL ((I.chain l u a).sSharp i) ((I.chain l u a).sDiv i) I.J.cD (I.th u a i b b' q q') x y' := rfl

end Main

end GlobalTheory.KerDia.Eqv
