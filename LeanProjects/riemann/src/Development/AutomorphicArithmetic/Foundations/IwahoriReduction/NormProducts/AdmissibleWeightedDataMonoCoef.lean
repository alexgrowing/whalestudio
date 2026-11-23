import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.Ml
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KatoTameRelationProjected
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.SmoothedZetaClassHodgeTateLawStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormSubMulAddLeOfUltrametricReplace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormEqOneOfIsUnitToZModPow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoefSpanFinset
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ZetaSystemExponentRaiseOfPrimePowSmul
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ShCocWsumProps

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KA
open scoped Matrix MatrixGroups

namespace UpperTheory.Kd.K4

theorem g3 : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ)
  (gN : Newform (2 * e + 1)) (A : ValuationSubring Ω) (W : R2 Ω l) (ε : Ω →+* ℂ) (X : Tower Ω ε)
  (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (cw : ZMod N → Qbar l) (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ))
  (ψ : ZMod l → Qbar l) (cf : Coef l),
  (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
  (∀ r₀, gm r₀ ∈ CongruenceSubgroup.Gamma1 N) → Nat.Coprime l N → l ≠ 2 → 1 ≤ e → (∃ x, cw x ≠ 0) →
  AdmWn ι e gN A W X pr N cw c d gm ψ cf → Continuous W → (∀ s i j, mat W s i j ∈ cf.O) →
  ∃ (c₀ : ℕ) (Y : ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l),
    IsZWc X l pr W e ψ N cw c d (2 * e + 1) gm cf c₀ Y ∧
    (∀ r, ShCoc (rhoK W e ψ) (cycMod (F := ℚ) (Ω := Ω) l r)⁻¹ (Y r)) ∧
    (∀ r, Y r = push (redL l r) (Y (r + 1))) ∧ (∀ r y i, Continuous fun s => Y r s y i) ∧ (∀ r s u i, Y r s u i ∈ cf.O) := by
  intro l _ Ω _ _ _ ι e gN A W ε X pr N _ cw c d gm ψ cf hφ hgm hcop hl2 he hcw hadm _hWc _hWO
  obtain ⟨x₀, hx₀⟩ := hcw
  have h3 : ∀ x : ZMod N, AdmissibleNewformZetaData ι e gN A W X pr N x c d gm ψ cf := fun x => hadm.1 x₀ hx₀
  have hml := fun x : ZMod N => UpperTheory.Kd.K4.ml l Ω ι e gN A W ε X pr N x c d gm ψ cf hgm hcop hl2 he hφ (h3 x)
  choose c₁ hc₁ using hml
  let C : ℕ := Finset.univ.sup c₁
  have hC : ∀ x, c₁ x ≤ C := fun x => Finset.le_sup (f := c₁) (Finset.mem_univ x)
  have hY := fun x : ZMod N => hc₁ x C (hC x)
  choose Yx hZ hS hP hCt hO using hY
  obtain ⟨k1, k2, k3, k4⟩ := GlobalTheory.K4.shCoc_wsum_props l Ω (rhoK W e ψ) cf (ZMod N) cw Yx hS hP hCt hO hadm.2
  refine ⟨C, fun r s y => ∑ x, cw x • Yx x r s y, ⟨Yx, hZ, fun r s y => rfl⟩, k1, k2, k3, k4⟩

end UpperTheory.Kd.K4

namespace UpperTheory.Kd.K4.ZetaTop

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} {l : ℕ} [Fact l.Prime]

theorem admissibleWeightedData_mono_coef {ι : Qbar l ≃+* ℂ} {e : ℕ} {g : Newform (2 * e + 1)} {A : ValuationSubring Ω} {W : R2 Ω l}
    {X : Tower Ω ε} {pr : X.Fn l → Fin 2 → Qbar l} {N : ℕ} [NeZero N] {cw : ZMod N → Qbar l} {c d : ℕ}
    {gm : (ZMod l)ˣ → SL(2, ℤ)} {ψ : ZMod l → Qbar l} {cf cf' : Coef l} (hle : cf.O ≤ cf'.O)
    (h : AdmWn ι e g A W X pr N cw c d gm ψ cf) : AdmWn ι e g A W X pr N cw c d gm ψ cf' := by
  refine ⟨fun x hx => ?_, fun x => hle (h.2 x)⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h.1 x hx
  exact ⟨h1, h2, h3, h4, h5, h6, fun b hb i => hle (h7 b hb i), h8⟩

theorem isZWc_mono {X : Tower Ω ε} {pr : X.Fn l → Fin 2 → Qbar l} {W : R2 Ω l} {e : ℕ} {ψ : ZMod l → Qbar l}
    {N : ℕ} [NeZero N] {cw : ZMod N → Qbar l} {c d k : ℕ} {gm : (ZMod l)ˣ → SL(2, ℤ)} {cf cf' : Coef l} {c₀ : ℕ}
    {Y : ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l} (hle : cf.O ≤ cf'.O)
    (h : IsZWc X l pr W e ψ N cw c d k gm cf c₀ Y) : IsZWc X l pr W e ψ N cw c d k gm cf' c₀ Y := by
  obtain ⟨Yx, hx, hs⟩ := h
  refine ⟨Yx, fun x r n => ?_, hs⟩
  obtain ⟨bB, hB, b, hb, hY⟩ := hx x r n
  exact ⟨bB, hB, b, fun y i => hle (hb y i), hY⟩

theorem isZWc_raise {X : Tower Ω ε} {pr : X.Fn l → Fin 2 → Qbar l} {W : R2 Ω l} {e : ℕ} {ψ : ZMod l → Qbar l}
    {N : ℕ} [NeZero N] {cw : ZMod N → Qbar l} {c d k : ℕ} {gm : (ZMod l)ˣ → SL(2, ℤ)} {cf : Coef l} {c₀ : ℕ}
    {Y : ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l} (m : ℕ)
    (hadd : ∀ b b', pr (b + b') = pr b + pr b')
    (hsm : ∀ (a : ℤ_[l]) b, pr (a • b) = algebraMap ℚ_[l] (Qbar l) (a : ℚ_[l]) • pr b)
    (h : IsZWc X l pr W e ψ N cw c d k gm cf c₀ Y) :
    IsZWc X l pr W e ψ N cw c d k gm cf (c₀ + m) (fun r s y => ((l : Qbar l) ^ m) • Y r s y) := by
  obtain ⟨Yx, hY, hsum⟩ := h
  refine ⟨fun x r s y => ((l : Qbar l) ^ m) • Yx x r s y,
    fun x => GlobalTheory.K4.zetaSystem_exponent_raise_of_prime_pow_smul l Ω ε X pr W e ψ N x c d k gm cf c₀ m (Yx x) hadd hsm (hY x), ?_⟩
  intro r s y
  simp only
  rw [hsum r s y, Finset.smul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [smul_comm]

theorem shCoc_smul {Γ X R : Type*} [Group Γ] [Monoid X] [CommRing R] {ρ : Γ → Matrix (Fin 2) (Fin 2) R} {κ : Γ →* X}
    {Y : Γ → X → Fin 2 → R} (a : R) (h : ShCoc ρ κ Y) : ShCoc ρ κ (fun s y => a • Y s y) := by
  intro s t x
  simp only [h s t x, smul_add, Matrix.mulVec_smul]

theorem push_smul {Γ X X' R : Type*} [Fintype X'] [DecidableEq X] [CommRing R] (π : X' → X)
    (Y : Γ → X' → Fin 2 → R) (a : R) :
    GlobalTheory.KA.push π (fun s y => a • Y s y) = fun s y => a • GlobalTheory.KA.push π Y s y := by
  funext s y
  simp only [GlobalTheory.KA.push, Finset.smul_sum]

theorem spec_smul {Γ X R : Type*} [Fintype X] [CommRing R] (η : X → R) (Y : Γ → X → Fin 2 → R) (a : R) (s : Γ) :
    GlobalTheory.KA.spec η (fun s y => a • Y s y) s = a • GlobalTheory.KA.spec η Y s := by
  simp only [GlobalTheory.KA.spec, Finset.smul_sum, smul_comm a]

theorem exists_finset_unif [IsAlgClosure ℚ Ω] {T Q : Type} [Finite T] [SeminormedAddCommGroup Q]
    (f : (Ω ≃ₐ[ℚ] Ω) → T → Q) (hf : ∀ x, Continuous fun s => f s x) {δ : ℝ} (hδ : 0 < δ) :
    ∃ E0 : Finset Ω, ∀ (s s' : Ω ≃ₐ[ℚ] Ω) (x : T), (∀ z ∈ E0, s' z = z) → ‖f (s * s') x - f s x‖ ≤ δ := by
  classical
  haveI := Fintype.ofFinite T
  have hU : ∀ x, ∀ᶠ s' in nhds (1 : Ω ≃ₐ[ℚ] Ω), ∀ s ∈ (Set.univ : Set (Ω ≃ₐ[ℚ] Ω)),
      ‖f (s * s') x - f s x‖ < δ := by
    intro x
    refine isCompact_univ.eventually_forall_of_forall_eventually fun s _ => ?_
    have hc : Continuous fun z : (Ω ≃ₐ[ℚ] Ω) × (Ω ≃ₐ[ℚ] Ω) => ‖f (z.2 * z.1) x - f z.2 x‖ :=
      (((hf x).comp (continuous_snd.mul continuous_fst)).sub ((hf x).comp continuous_snd)).norm
    have h0 : ‖f (s * 1) x - f s x‖ < δ := by simpa using hδ
    exact hc.continuousAt.eventually (gt_mem_nhds h0)
  have hV : {s' : Ω ≃ₐ[ℚ] Ω | ∀ x, ∀ s, ‖f (s * s') x - f s x‖ < δ} ∈ nhds (1 : Ω ≃ₐ[ℚ] Ω) := by
    have := Filter.eventually_all.2 hU
    filter_upwards [this] with s' hs' x s using hs' x s (Set.mem_univ _)
  obtain ⟨E, hEfin, hEsub⟩ := (krullTopology_mem_nhds_one_iff ℚ Ω _).1 hV
  have hfg : (Subalgebra.toSubmodule E.toSubalgebra).FG :=
    (Submodule.fg_iff_finiteDimensional _).2 hEfin
  obtain ⟨t, ht⟩ := hfg
  refine ⟨t, fun s s' x hfix => ?_⟩
  have hmem : s' ∈ E.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    have hy' : y ∈ Subalgebra.toSubmodule E.toSubalgebra := hy
    rw [← ht] at hy'
    clear hy
    induction hy' using Submodule.span_induction with
    | mem z hz => exact hfix z hz
    | zero => exact map_zero s'
    | add u v _ _ hu hv => rw [map_add, hu, hv]
    | smul a u _ hu => rw [map_smul, hu]
  exact (hEsub hmem x s).le

end UpperTheory.Kd.K4.ZetaTop

namespace UpperTheory.Kd.K4

open UpperTheory.Kd.K4.ZetaTop

theorem top : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (S : Finset Pl)
    (A : ValuationSubring Ω) (W : R2 Ω l) (g : Newform (2 * e + 1)), Nf e S A W → SrcUr ι e A W g →
  ∀ (ε : Ω →+* ℂ) (X : Tower Ω ε) (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (cw : ZMod N → Qbar l) (c d : ℕ)
    (gm : (ZMod l)ˣ → SL(2, ℤ)) (ψ : ZMod l → Qbar l) (cf : Coef l),
    (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
    (∀ r₀, gm r₀ ∈ CongruenceSubgroup.Gamma1 N) → Nat.Coprime l N → l ≠ 2 → 1 ≤ e →
    (∃ x, cw x ≠ 0) → AdmWn ι e g A W X pr N cw c d gm ψ cf → Continuous W → (∀ s i j, mat W s i j ∈ cf.O) →
    ∃ (c₀ m : ℕ) (cf' : Coef l) (S' : Finset Pl) (Y : ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l)
      (y : G ℚ Ω → Fin 2 → Qbar l),
      IsZWc X l pr W e ψ N cw c d (2 * e + 1) gm cf c₀ Y ∧
      (∀ r, GlobalTheory.KA.ShCoc (rhoK W e ψ) (cycMod (F := ℚ) (Ω := Ω) l r)⁻¹ (Y r)) ∧
      (∀ r, Y r = GlobalTheory.KA.push (redL l r) (Y (r + 1))) ∧
      (∀ r y i, Continuous fun s => Y r s y i) ∧
      (∀ (r n : ℕ), ∃ E0 : Finset Ω, ∀ (s s' : Ω ≃ₐ[ℚ] Ω) (y : (ZMod (l ^ r))ˣ), (∀ z ∈ E0, s' z = z) → Cg n (Y r (s * s') y 1) (Y r s y 1)) ∧ (∀ r s y i, Y r s y i ∈ cf.O) ∧ (∀ z, z ∈ cf.O → z ∈ cf'.O) ∧
      (∀ r s, Cv r (y s) (GlobalTheory.KA.spec (fun u : (ZMod (l ^ r))ˣ => ((((u : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * chiK l ψ r u) (Y r) s)) ∧
      Sys W cf' (fun s => ((l : Qbar l) ^ m) • y s) S' ∧
      IwSys2 cf' A (nuD W e ψ) (fun r s u => (l : Qbar l) ^ m * Y r s u 1) ∧
      SpLink A e (chiK l ψ) (fun r s u => (l : Qbar l) ^ m * Y r s u 1) (fun s => ((l : Qbar l) ^ m) • y s) := by
  intro l _ Ω _ _ _ ι e S A W g hNf hSrc ε X pr N _ cw c d gm ψ cf hφ hgm hlN hl2 he hcw hAdm hWc hmat
  classical
  obtain ⟨c₀, Y, hZ, hSh, hPush, hCont, hO⟩ :=
    g3 l Ω ι e g A W ε X pr N cw c d gm ψ cf hφ hgm hlN hl2 he hcw hAdm hWc hmat
  obtain ⟨x₀, hx₀⟩ := hcw
  obtain ⟨-, -, -, -, hadd, hsm, -⟩ := hAdm.1 x₀ hx₀
  obtain ⟨θ, hθc, hmatθ, hρO, hχO, hχcong, hηtw, hθIne, hDec, hη⟩ :=
    GlobalTheory.K4.twist_clauses l Ω ι e g A W ε X pr N cw c d gm ψ cf S hNf hl2 ⟨x₀, hx₀⟩ hAdm
  obtain ⟨k, S', hIne, hfam⟩ := UpperTheory.V.Z.Kato.Nb.kato_tame_relation_projected l Ω ι e g A W ε X pr N cw c d gm ψ cf S hNf hmat hgm hlN
    hl2 he ⟨x₀, hx₀⟩ hφ hAdm c₀ Y hZ
  set Y' : ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l :=
    fun r s y => ((l : Qbar l) ^ k) • Y r s y with hY'
  have hlk : ((l : Qbar l) ^ k) ∈ cf.O := pow_mem (natCast_mem _ _) _
  have hSh' : ∀ r, GlobalTheory.KA.ShCoc (rhoK W e ψ) (cycMod (F := ℚ) (Ω := Ω) l r)⁻¹ (Y' r) :=
    fun r => shCoc_smul _ (hSh r)
  have hCont' : ∀ r y i, Continuous fun s => Y' r s y i := by
    intro r y i
    simp only [hY', Pi.smul_apply, smul_eq_mul]
    exact continuous_const.mul (hCont r y i)
  have hO' : ∀ r s u i, Y' r s u i ∈ cf.O := by
    intro r s u i
    simp only [hY', Pi.smul_apply, smul_eq_mul]
    exact mul_mem hlk (hO r s u i)
  have hPush' : ∀ r, Y' r = GlobalTheory.KA.push (redL l r) (Y' (r + 1)) := by
    intro r
    simp only [hY']
    rw [push_smul, ← hPush r]
  obtain ⟨m, y, S'', hy, hSys, hIw, hSp⟩ :=
    GlobalTheory.KZ.middle_glue2 l Ω W cf A e S' (chiK l (Function.update ψ 0 0)) θ (rhoK W e ψ) (nuD W e ψ) Y'
      hWc hθc hmat hmatθ (hρO cf hmat) (hχO cf) hχcong hηtw hSh' hCont' hO'
      (fun r s => congrFun (hPush' r) s) hDec hIne hθIne (by
        intro n hn w hw hdvd ψw hk hs
        obtain ⟨Yw, P, u, b, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hfam n hn w hw hdvd ψw hk hs
        refine ⟨Yw, P, u, b, h1, h2, h3, h4, h5, h6, h7, ?_, h9⟩
        intro r s i
        rw [hη r]
        simp only [hY', spec_smul]
        exact h8 r s i)
  refine ⟨c₀ + k, m, cf, S'', Y', y, isZWc_raise k hadd hsm hZ, hSh', hPush', hCont', ?_, hO',
    fun z hz => hz, ?_, hSys, hIw, ?_⟩
  · intro r n
    have hpos : (0 : ℝ) < ‖((l : Qbar l) ^ n)‖ := by
      rw [norm_pos_iff]
      exact pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
    obtain ⟨E0, hE0⟩ := exists_finset_unif (fun s y => Y' r s y 1) (fun y => hCont' r y 1) hpos
    exact ⟨E0, fun s s' y hfix => hE0 s s' y hfix⟩
  · intro r s i
    have := hy r s i
    rw [hη r] at this
    exact this
  · intro n
    obtain ⟨r₀, hr⟩ := hSp n
    refine ⟨r₀, fun r hr' s hs hc => ?_⟩
    have := hr r hr' s hs hc
    rwa [hη r] at this

end UpperTheory.Kd.K4

theorem UpperTheory.Kd.K4.kato_eulerSystem_integrality : UpperTheory.V.Z.Kato.Joint.KatoEulerSystemIwasawaClassStatement := UpperTheory.Kd.K4.top
