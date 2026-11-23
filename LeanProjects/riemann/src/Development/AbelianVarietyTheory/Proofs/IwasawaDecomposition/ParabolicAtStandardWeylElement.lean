import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowSetFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SplitOffDetection
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.HkSupSizedOfHkSup
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeValueIntegrality
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGoodRowHeckeOfOcc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EigenCompatibleOfBadSet
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplexConjugationMapsMultiplicitySpace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelOfDualParameter
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsFundamentalDomainOfHaar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceModelImp

noncomputable section

namespace GlobalTheory.HeckeField

open Polynomial

section Abstract

variable {k : Type} [Field k] [NumberField k] (σ : k →+* ℂ) {W X : Type} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
  [AddCommGroup X] [Module ℂ X] (ι : W →ₛₗ[σ] X)

omit [NumberField k] [FiniteDimensional k W] in

theorem aeval_read {φ : Module.End k W} {T : Module.End ℂ X} (h : ∀ x, T (ι x) = ι (φ x)) (p : k[X]) (x : W) :
    aeval T (p.map σ) (ι x) = ι (aeval φ p x) := by
  have hp : ∀ (n : ℕ) (x : W), (T ^ n) (ι x) = ι ((φ ^ n) x) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih => intro x; rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, h, ih]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a => simp [aeval_monomial, hp, map_smulₛₗ]

theorem exists_finset_eig {κ : Type} (φ : κ → Module.End k W) (T : κ → Module.End ℂ X) (h : ∀ t x, T t (ι x) = ι (φ t x)) :
    ∃ S : Finset ℂ, (∀ z ∈ S, IsAlgebraic ℚ z) ∧ ∀ L : IntermediateField ℚ ℂ, (∀ z ∈ S, z ∈ L) →
      ∀ U ∈ Submodule.span ℂ (Set.range ι), U ≠ 0 → ∀ c : κ → ℂ, (∀ t, T t U = c t • U) → ∀ t, c t ∈ L := by
  classical
  obtain ⟨s, hs⟩ : ∃ s : Finset κ, ∀ t, φ t ∈ Submodule.span k (φ '' s) := by
    obtain ⟨b, hb, hsp, hli⟩ := exists_linearIndependent k (Set.range φ)
    have hfin : b.Finite := hli.setFinite
    obtain ⟨s, -, hs, e⟩ := Set.Finite.exists_finset_coe (s := (∅ : Set κ)) Set.finite_empty |>.elim fun _ _ =>
      (Set.exists_subset_image_finite_and (f := φ) (s := Set.univ) (p := fun u => u = b)).1
        ⟨b, by simpa using hb, hfin, rfl⟩
    exact ⟨hs.toFinset, fun t => by
      rw [Set.Finite.coe_toFinset, e, hsp]; exact Submodule.subset_span ⟨t, rfl⟩⟩
  let b := Module.finBasis ℚ k
  have halg : ∀ a : k, IsAlgebraic ℚ (σ a) := fun a =>
    (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) a).algHom σ.toRatAlgHom
  refine ⟨Finset.univ.image (fun i => σ (b i)) ∪ s.biUnion fun t => ((minpoly k (φ t)).map σ).roots.toFinset, ?_, ?_⟩
  · intro z hz
    rcases Finset.mem_union.1 hz with hz | hz
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hz
      exact halg _
    · obtain ⟨t, -, hz⟩ := Finset.mem_biUnion.1 hz
      letI : Algebra k ℂ := σ.toAlgebra
      have hi : IsIntegral k z := ⟨minpoly k (φ t), minpoly.monic (Algebra.IsIntegral.isIntegral _), by
        rw [eval₂_eq_eval_map]; exact (mem_roots'.1 (Multiset.mem_toFinset.1 hz)).2⟩
      exact (isIntegral_trans (R := ℚ) z hi).isAlgebraic
  · intro L hL U hU h0 c hc t
    have hk : ∀ a : k, σ a ∈ L := fun a => by
      rw [← b.sum_repr a, map_sum]
      refine L.sum_mem fun i _ => ?_
      rw [map_rat_smul]
      exact L.smul_mem (hL _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))))
    have hroot : ∀ u ∈ s, c u ∈ L := fun u hu => by
      refine hL _ (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨u, hu, Multiset.mem_toFinset.2 ?_⟩))
      have hm := minpoly.monic (Algebra.IsIntegral.isIntegral (R := k) (φ u))
      refine (mem_roots (hm.map σ).ne_zero).2 ?_
      have hz : aeval (T u) ((minpoly k (φ u)).map σ) U = 0 := by
        refine Submodule.span_le (p := LinearMap.ker (aeval (T u) ((minpoly k (φ u)).map σ))).2 ?_ hU
        rintro _ ⟨x, rfl⟩
        show aeval (T u) ((minpoly k (φ u)).map σ) (ι x) = 0
        rw [aeval_read σ ι (h u), minpoly.aeval, LinearMap.zero_apply, map_zero]
      rw [Module.End.aeval_apply_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 (hc u), h0⟩] at hz
      exact (smul_eq_zero.1 hz).resolve_right h0
    have key : ∀ ψ ∈ Submodule.span k (φ '' s), ∃ (T' : Module.End ℂ X) (a : ℂ), (∀ x, T' (ι x) = ι (ψ x)) ∧ a ∈ L ∧ T' U = a • U := by
      intro ψ hψ
      induction hψ using Submodule.span_induction with
      | mem ψ hψ =>
        obtain ⟨u, hu, rfl⟩ := hψ
        exact ⟨T u, c u, h u, hroot u hu, hc u⟩
      | zero => exact ⟨0, 0, fun x => by simp, L.zero_mem, by simp⟩
      | add ψ ψ' _ _ h1 h2 =>
        obtain ⟨T1, a1, e1, m1, f1⟩ := h1
        obtain ⟨T2, a2, e2, m2, f2⟩ := h2
        exact ⟨T1 + T2, a1 + a2, fun x => by simp [e1, e2], L.add_mem m1 m2, by simp [f1, f2, add_smul]⟩
      | smul a ψ _ h1 =>
        obtain ⟨T1, a1, e1, m1, f1⟩ := h1
        exact ⟨σ a • T1, σ a * a1, fun x => by simp [e1, map_smulₛₗ], L.mul_mem (hk a) m1, by simp [f1, mul_smul]⟩
    obtain ⟨T', a, e, m, f⟩ := key _ (hs t)
    have : T t U = T' U := by
      refine LinearMap.eqOn_span (s := Set.range ι) ?_ hU
      rintro _ ⟨x, rfl⟩
      rw [h, e]
    rw [hc, f] at this
    rwa [smul_left_injective ℂ h0 this]

end Abstract

section Level

open Formalism.L2.DIV Formalism.L2.Herm Formalism.UG Formalism.BasicNotions NumberField IsDedekindDomain
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

omit [StarRing E] in

theorem frame_int {β β' : GL (Fin n) (E ⊗[F] Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)} (h : IsFrame β Λ) (h' : IsFrame β' Λ)
    (i j : Fin n) : ((β'⁻¹ * β : GL (Fin n) (E ⊗[F] Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Af F)) i j ∈ intAf F E := by
  have h1 : (β : Matrix (Fin n) (Fin n) (E ⊗[F] Af F)).mulVec (Pi.single j 1) ∈ hatL (F := F) Λ := by
    refine (h _).2 fun a => ?_
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec, Pi.single_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  have h2 := (h' _).1 h1 i
  rwa [Matrix.mulVec_mulVec, ← Units.val_mul, Matrix.mulVec_single_one] at h2

omit [StarRing E] in

theorem princ_frame {β β' : GL (Fin n) (E ⊗[F] Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)} (h : IsFrame β Λ) (h' : IsFrame β' Λ)
    {x : GL (Fin n) (E ⊗[F] Af F)} (hx : x ∈ St β) : x ∈ St β' ∧ ∀ PP, redFn β PP x = 1 → redFn β' PP x = 1 := by
  have inj : ∀ {A B : Matrix (Fin n) (Fin n) (intAf F E)}, A.map (intAf F E).subtype = B.map (intAf F E).subtype → A = B :=
    fun e => Matrix.map_injective Subtype.val_injective e
  let A : Matrix (Fin n) (Fin n) (intAf F E) := Matrix.of fun i j => ⟨_, frame_int h h' i j⟩
  let B : Matrix (Fin n) (Fin n) (intAf F E) := Matrix.of fun i j => ⟨_, frame_int h' h i j⟩
  have eA : A.map (intAf F E).subtype = ((β'⁻¹ * β : GL (Fin n) (E ⊗[F] Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Af F)) := rfl
  have eB : B.map (intAf F E).subtype = ((β⁻¹ * β' : GL (Fin n) (E ⊗[F] Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Af F)) := rfl
  let y : GL (Fin n) (intAf F E) := ⟨A, B,
    inj (by rw [Matrix.map_mul, eA, eB, ← Units.val_mul, Matrix.map_one _ (map_zero _) (map_one _)]; simp),
    inj (by rw [Matrix.map_mul, eA, eB, ← Units.val_mul, Matrix.map_one _ (map_zero _) (map_one _)]; simp)⟩
  have ey : intGL F E n y = β'⁻¹ * β := Units.ext eA
  obtain ⟨z, rfl⟩ := hx
  have e : frGL β z = frGL β' (y * z * y⁻¹) := by
    show β * intGL F E n z * β⁻¹ = β' * intGL F E n (y * z * y⁻¹) * β'⁻¹
    rw [map_mul, map_mul, map_inv, ey]
    group
  refine ⟨⟨_, e.symm⟩, fun PP hP => ?_⟩
  rw [redFn_frGL] at hP
  rw [e, redFn_frGL, map_mul, map_mul, hP, mul_one, map_inv, mul_inv_cancel]

theorem eq_one_of_full_upper_block_eq_one {κ : Type} [CommRing κ] {r : ℕ} (hr : r ≤ n) (hn : n ≤ r) {g : GL (Fin n) κ} (h : upperLeftBlock hr g = 1) : g = 1 := by
  obtain rfl : r = n := le_antisymm hr hn
  have hg : g ∈ blockTri (blk2 r) := fun i j hij => by simp [blk2] at hij
  have := upper_block_val_submatrix hr hg
  rw [h] at this
  exact Units.ext this.symm

end Level

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
  Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.HeightCounting GlobalTheory.HeightCounting.RatSide

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Models

variable {D : D7} {V : HSp D} {S S' : D.what₂.Tau → SPar}

theorem mult_mono (θ : Formalism.IndefR.Datum.InfFam D) (M : DSModel V S) {J J' : Set (GA D V)} {χ χ' : GA D V → ℂ}
    (h : ∀ k ∈ J', k ∈ J ∧ χ k = χ' k) : Mult θ M J χ ≤ Mult θ M J' χ' :=
  Submodule.span_mono fun _ hT => ⟨hT.aut, hT.cusp, fun v k hk g => (h k hk).2 ▸ hT.lev v k (h k hk).1 g, hT.equiv, hT.cont⟩

theorem eig_conj (θ : Formalism.IndefR.Datum.InfFam D) (M : DSModel V S) (M' : DSModel V S') (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ)
    (hc : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w, c τ (M'.rep τ g w) = M.rep τ g (c τ w)) (J : Set (GA D V))
    {U : MMap M} (hU : U ∈ Mult θ M J fun _ => 1) (h0 : U ≠ 0) :
    ∃ U' ∈ Mult θ M' J fun _ => 1, U' ≠ 0 ∧ ∀ Rr (a : ℂ), heckeOn M Rr U = a • U → heckeOn M' Rr U' = star a • U' := by
  obtain ⟨h1, h2⟩ := GlobalTheory.ConjMult.conj_mult θ M M' c hc
  obtain ⟨U', hU', e⟩ := h2 J _ U hU
  refine ⟨U', by simpa only [star_one] using hU', fun hz => h0 ?_, fun Rr a ha => ?_⟩
  · refine MultilinearMap.ext fun v => funext fun g => ?_
    have := e (fun τ => ⟨(c τ).symm (v τ), (h1 τ _).2 (by rw [(c τ).apply_symm_apply]; exact (v τ).2)⟩) v
      (fun τ => ((c τ).apply_symm_apply _).symm) g
    rw [hz] at this
    exact star_eq_zero.1 this.symm
  · refine MultilinearMap.ext fun v' => funext fun g => ?_
    let v : M.Vec := fun τ => ⟨c τ (v' τ), (h1 τ _).1 (v' τ).2⟩
    have e' := e v' v fun _ => rfl
    have ha' : ∑ γ ∈ Rr, U v (g * γ) = a * U v g := congrFun (congrArg (fun T : MMap M => T v) ha) g
    show ∑ γ ∈ Rr, U' v' (g * γ) = star a * U' v' g
    simp only [e']
    rw [← star_sum, ha', star_mul']

variable (V S) in

def Occ (J : Set (GA D V)) (I : Finset (GA D V) → ℂ → Prop) : Prop :=
  ∃ θ : Formalism.IndefR.Datum.InfFam D, IsInfFam θ ∧ ∃ M : DSModel V S, ∃ U ∈ Mult θ M J fun _ => 1, U ≠ 0 ∧
    ∀ Rr a, I Rr a → heckeOn M Rr U = a • U

theorem Occ.model (hU : GlobalTheory.Published.DiscreteSeriesUpqUnique) {J : Set (GA D V)} {I : Finset (GA D V) → ℂ → Prop} (h : Occ V S J I)
    (θ : Formalism.IndefR.Datum.InfFam D) (hθ : IsInfFam θ) (M' : DSModel V S) :
    ∃ U ∈ Mult θ M' J fun _ => 1, U ≠ 0 ∧ ∀ Rr a, I Rr a → heckeOn M' Rr U = a • U := by
  obtain ⟨θ', hθ', M, U, hM, h0, he⟩ := h
  obtain rfl := GlobalTheory.VolHeckeCompare.infFam_unique hθ hθ'
  obtain ⟨N, c, hc⟩ := GlobalTheory.ConjDS.exists_conjModel M
  obtain ⟨u, hu⟩ := hU.exists_intertwiner M M'
  obtain ⟨U1, m1, n1, e1⟩ := eig_conj θ M N c hc J hM h0
  obtain ⟨U2, m2, n2, e2⟩ := eig_conj θ N M' (fun τ => (u τ).trans (c τ).symm) (fun τ g hg w => (c τ).injective (by
    show c τ ((c τ).symm (u τ _)) = c τ (N.rep τ g ((c τ).symm (u τ w)))
    rw [(c τ).apply_symm_apply, hc τ g hg, (c τ).apply_symm_apply, hu τ g hg])) J m1 n1
  exact ⟨U2, m2, n2, fun Rr a ha => by simpa only [star_star] using e2 Rr _ (e1 Rr a (he Rr a ha))⟩

end Models

section Record

variable {D : D7}

def princ (V : HSp D) (Z : Set (Pl D.host.E)) : Subgroup (GA D V) :=
  ⨅ (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (_ : IsFrame β Λ ∧ (Λ : Set (Fin V.rank → D.host.E)) = L0c D V),
    levA V (UA D.sp.cm V.gram ⊓ St β ⊓ ⨅ PP ∈ Z, princAt β PP)

def typl (C : CharFrame D) : Set (Pl D.host.E) := {PP | ∃ k, C.P.Div k PP}

theorem levTriv_eq {T : Type} {L : LevCh D T} {μ0 : T} (hL : L.Is μ0) (i : Fin D.R.m) :
    levG (Wc D i) (L.βW i) (L.datWp i L.triv) = princ (Wc D i) (typl L.C) := by
  obtain ⟨c, hf, -, -, h1, h2⟩ := hL.βW i
  have hΛ : (L.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) = L0c D (Wc D i) :=
    Set.ext fun x => ⟨fun h => by simpa using h2 x h, fun h => by simpa using h1 x h⟩
  ext κ
  simp only [princ, Subgroup.mem_iInf]
  constructor
  · rintro ⟨hκ, hp, ht⟩ β Λ ⟨hβ, e⟩
    obtain rfl : Λ = L.ΛW i := SetLike.coe_injective (e.trans hΛ.symm)
    obtain ⟨s1, s2⟩ := princ_frame hf hβ (parLev_St hp)
    refine ⟨hκ, ⟨parLev_UA hp, s1⟩, Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => mem_princAt.2 ⟨s1, s2 PP ?_⟩⟩
    exact eq_one_of_full_upper_block_eq_one (r_le_rank_Wc i) (GlobalTheory.EigRows.rank_Wc i).le (congrFun (Subgroup.mem_bot.1 ht) ⟨PP, (hL.Pg PP).2 hP⟩)
  · intro h
    obtain ⟨hκ, hp, ht⟩ := h (L.βW i) (L.ΛW i) ⟨hf, hΛ⟩
    refine ⟨hκ, Kg_le_lev (T := L.Pg) (Finset.Subset.refl _) (Finset.empty_subset _) ⟨hp, ?_⟩⟩
    exact Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP =>
      Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 ht PP) ((hL.Pg PP).1 hP)

open Classical in

def parOf (W : HSp D) (l : D.what₂.Tau → (D.host.E →+* ℂ)) (ρ : D.what₂.Tau) : SPar :=
  let τ : D.what₂.Tau := if h : ∃ τ, l τ = tauE D ρ ∨ l τ = (starRingEnd ℂ).comp (tauE D ρ) then h.choose else ρ
  if l τ = tauE D ρ then Formalism.L2.NTheta.holPar _ _ (Formalism.L2.NTheta.kapW (D.hc τ) (W.sig (tauE D ρ)).1 (W.sig (tauE D ρ)).2)
  else dualPar (Formalism.L2.NTheta.holPar _ _ (Formalism.L2.NTheta.kapW (D.hc τ) (W.sig (tauE D ρ)).1 (W.sig (tauE D ρ)).2))

def parHost (W : HSp D) : D.what₂.Tau → SPar :=
  parOf W fun τ => D.host.φ₀.comp (D.host.sigmaOf (D.eTau τ).1 : D.host.E →+* D.host.E)

theorem parAt_emb (W : HSp D) : parAt W D.what₂.embLL = parHost W := by
  have e : labE (D := D) D.what₂.embLL = fun τ => D.host.φ₀.comp (D.host.sigmaOf (D.eTau τ).1 : D.host.E →+* D.host.E) := by
    funext τ
    rw [← D.embE_φ₀]
    rfl
  show parOf W (labE D.what₂.embLL) = _
  rw [e]
  rfl

def HkAt (C : CharFrame D) (i : Fin D.R.m) (k : ℕ) (P : PlE D.host) (α : GA D (Wc D i)) (Rr : Finset (GA D (Wc D i))) : Prop :=
  IsSplitPl D.host P ∧ P ∉ SbD D ∧ ((2 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ∧ k ≤ D.R.r ∧ IsHeckeAt (Wc D i) P k α ∧
    Bridge.IsDC (princ (Wc D i) (typl C)) α Rr

def nrm (C : CharFrame D) (i : Fin D.R.m) (k : ℕ) (P : PlE D.host) : ℂ :=
  (((C.mu0 i).val P : ℂˣ) : ℂ)⁻¹ ^ k * (((Nat.card (kP P) : ℕ) : ℂ) ^ (k * (D.R.nV / 2)))⁻¹

def EigSys (C : CharFrame D) (i : Fin D.R.m) (c : ℕ → PlE D.host → ℂ) : Prop :=
  Occ (Wc D i) (parHost (Wc D i)) (princ (Wc D i) (typl C)) fun Rr a => ∃ k P α, HkAt C i k P α Rr ∧ a = c k P

def BoundAt (C : CharFrame D) (i : Fin D.R.m) (S : Finset ℂ) : Prop :=
  ∀ L : IntermediateField ℚ ℂ, (∀ z ∈ S, z ∈ L) → ∀ c, EigSys C i c → ∀ k P α Rr, HkAt C i k P α Rr → nrm C i k P * c k P ∈ L

variable {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem hkDat_iff {R : RealDat3 D A3 Ks} (hL : R.toLevCh.Is A3.A.μ0) {i : Fin D.R.m} {k : ℕ} {P : PlE D.host} {α Rr} :
    HkDat R (SbD D) i k P α Rr ↔ HkAt R.C i k P α Rr :=
  ⟨fun h => ⟨h.split, h.offS, h.odd, h.le, h.elt, levTriv_eq hL i ▸ h.reps⟩,
    fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, (levTriv_eq hL i).symm ▸ h.2.2.2.2.2⟩⟩

theorem parabolic_at_standard_weyl_element (R : RealDat D A3.A Ks) (W : HSp D) : parAt W (sg0 D A3.A) = parHost W := by
  rw [← parAt_emb]
  exact congrArg _ (sgAt_mk _ R.hv0)

theorem eigSys_row {R : RealDat3 D A3 Ks} {F : Face D A3.A} {X0} (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F X0)
    (hL : R.toLevCh.Is A3.A.μ0) (hθ : IsInfFam R.θ) {i : Fin D.R.m} {σ : D.what₂.FT} (h : D.what₂.isot (i.1 + 1) σ ≠ ⊥) :
    EigSys R.C i fun k P => GlobalTheory.EigRows.rowEig Y i σ P (GlobalTheory.EigRows.diagLab D.R.r k) := by
  obtain ⟨U, hU, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (GlobalTheory.EigRows.partR_ne_bot Y h)
  unfold EigSys
  rw [← parabolic_at_standard_weyl_element (A3 := A3) R.toRealDat]
  refine ⟨R.θ, hθ, R.MW i (sg0 D A3.A), U, mult_mono _ _ (fun k hk => ?_) (GlobalTheory.EigRows.partR_le_partFull Y ∅ i σ hU).1, h0, ?_⟩
  · rw [← levTriv_eq hL i] at hk
    exact GlobalTheory.HeckeParts.triv_le (V := Wc D i) (β := R.βW i) (R.levL F false (sg0 D A3.A)) k hk
  · rintro Rr a ⟨k, P, α, hd, rfl⟩
    have hd' := (hkDat_iff hL).2 hd
    exact GlobalTheory.EigRows.heckeOn_partR Y hL i ((GlobalTheory.TwInputs.Eig.low_SbD D).offPg hL hd'.offS) hd'.le hd'.elt hd'.reps σ hU

theorem exists_boundAt (hU : GlobalTheory.Published.DiscreteSeriesUpqUnique) (R : RealDat3 D A3 Ks) (hL : R.toLevCh.Is A3.A.μ0)
    (hθ : IsInfFam R.θ) (hW : R.toRealDat.models_HW) (hu : R.toRealDat.LUnif) (i : Fin D.R.m) (hK : (R.FW i).IsKsForm)
    (h : ℕ → PlE D.host → Module.End D.what₂.LL (Fin (R.nW i) → D.what₂.LL))
    (hs : ∀ k P x, x ∈ (R.FW i).WK → h k P x ∈ (R.FW i).WK)
    (hr : ∀ k P α Rr, HkDat R (SbD D) i k P α Rr → ∀ x, (R.HW i (sg0 D A3.A)).e ((R.FW i).j (sg0 D A3.A) (h k P x)) =
      hkNorm R i k P • heckeOn (R.MW i (sg0 D A3.A)) Rr ((R.HW i (sg0 D A3.A)).e ((R.FW i).j (sg0 D A3.A) x))) :
    ∃ S : Finset ℂ, (∀ z ∈ S, IsAlgebraic ℚ z) ∧ BoundAt R.C i S := by
  obtain ⟨n, b, hb, -, hsp, -, hsp'⟩ := hK
  haveI : FiniteDimensional Ks (R.FW i).WK := by
    rw [← hsp]
    exact FiniteDimensional.span_of_finite Ks (Set.finite_range b)
  let ι : (R.FW i).WK →ₛₗ[(sg0 D A3.A).comp (algebraMap Ks D.what₂.LL)] MMap (R.MW i (sg0 D A3.A)) :=
    { toFun := fun x => (R.HW i (sg0 D A3.A)).e ((R.FW i).j (sg0 D A3.A) x)
      map_add' := fun x y => by rw [Submodule.coe_add, map_add, map_add]
      map_smul' := fun a x => by rw [Submodule.coe_smul, ← algebraMap_smul D.what₂.LL a, map_smulₛₗ, map_smul]; rfl }
  let κ := {t : ℕ × PlE D.host × GA D (Wc D i) × Finset (GA D (Wc D i)) // HkAt R.C i t.1 t.2.1 t.2.2.1 t.2.2.2}
  obtain ⟨S, h1, h2⟩ := exists_finset_eig _ ι
    (fun t : κ => ((h t.1.1 t.1.2.1).restrictScalars Ks).restrict (hs t.1.1 t.1.2.1))
    (fun t : κ => hkNorm R i t.1.1 t.1.2.1 • heckeOn (R.MW i (sg0 D A3.A)) t.1.2.2.2)
    (fun t x => (hr _ _ _ _ ((hkDat_iff hL).2 t.2) x).symm)
  refine ⟨S, h1, fun L hS c hc k P α Rr hd => ?_⟩
  unfold EigSys at hc
  rw [← parabolic_at_standard_weyl_element (A3 := A3) R.toRealDat] at hc
  obtain ⟨U, hM, h0, he⟩ := hc.model hU R.θ hθ (R.MW i (sg0 D A3.A))
  refine h2 L hS U ?_ h0 (fun t => nrm R.C i t.1.1 t.1.2.1 * c t.1.1 t.1.2.1) (fun t => ?_) ⟨(k, P, α, Rr), hd⟩
  · have hM' : U ∈ R.Wall i (sg0 D A3.A) := by
      refine mult_mono _ _ (fun k hk => ?_) hM
      have := GlobalTheory.HeckeParts.triv_le (V := Wc D i) (β := R.βW i) R.triv k hk
      exact ⟨by rw [← levTriv_eq hL i]; exact hk, this.2.symm⟩
    rw [← (hW i _).2.1] at hM'
    obtain ⟨y, rfl⟩ := hM'
    have hy : y ∈ Submodule.span ℂ (Set.range ((R.FW i).j (sg0 D A3.A))) := (hu i _).2.1 ▸ Submodule.mem_top
    refine Submodule.span_le (p := (Submodule.span ℂ (Set.range ι)).comap (R.HW i (sg0 D A3.A)).e).2 ?_ hy
    rintro _ ⟨x, rfl⟩
    have hx : x ∈ Submodule.span D.what₂.LL (Set.range b) := hsp' ▸ Submodule.mem_top
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hx
    show (R.HW i (sg0 D A3.A)).e _ ∈ Submodule.span ℂ (Set.range ι)
    rw [map_sum, map_sum]
    refine Submodule.sum_mem _ fun l _ => ?_
    rw [map_smulₛₗ, map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨b l, hb l⟩, rfl⟩)
  · show hkNorm R i t.1.1 t.1.2.1 • heckeOn (R.MW i (sg0 D A3.A)) t.1.2.2.2 U = _
    rw [he _ _ ⟨_, _, _, t.2, rfl⟩, smul_smul]
    rfl

end Record

end GlobalTheory.HeckeField

namespace GlobalTheory.HeckeField

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
  Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.HeightCounting GlobalTheory.HeightCounting.RatSide
  GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.R3.Tr

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mem_mult_iff {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {θ : Formalism.IndefR.Datum.InfFam D} {M : DSModel V S}
    {J : Set (GA D V)} {χ : GA D V → ℂ} {U : MMap M} :
    U ∈ Mult θ M J χ ↔ ∃ s : Set (MMap M), (∀ T ∈ s, IsMultMap θ M J χ T) ∧ U ∈ Submodule.span ℂ s :=
  ⟨fun h => ⟨_, fun _ hT => hT, h⟩, fun ⟨_, hs, h⟩ => Submodule.span_mono hs h⟩

set_option maxHeartbeats 4000000 in

theorem boundAt_tr (X X' : Stages) (h : X.B.toPre = X'.B.toPre) (f : Fr X.B.toPre) (f' : Fr X'.B.toPre) (hf : HEq f f')
    (S : Finset ℂ) (H : ∀ i, BoundAt (Fr.at X f) i S) : ∀ i, BoundAt (Fr.at X' f') i S := by
  obtain ⟨B, C, W, V, S₀, N, G⟩ := X
  obtain ⟨B', C', W', V', S₀', N', G'⟩ := X'
  cases B
  cases B'
  dsimp only at h
  subst h
  cases hf
  intro i L hL c hc k P α Rr hd
  have H' := H ((by with_unfolding_all exact (i :))) L hL ((by with_unfolding_all exact (c :))) ?_ ((by with_unfolding_all exact (k :))) ((by with_unfolding_all exact (P :))) ((by with_unfolding_all exact (α :))) ((by with_unfolding_all exact (Rr :))) ((by with_unfolding_all exact (hd :)))
  · exact (by with_unfolding_all exact (H' :))
  obtain ⟨θ, hθ, M, U, hM, h0, he⟩ := hc
  refine ⟨(by with_unfolding_all exact (θ :)), (by with_unfolding_all exact (hθ :)),
    { H := (by with_unfolding_all exact (M.H :)), nacg := (by with_unfolding_all exact (M.nacg :)), ips := (by with_unfolding_all exact (M.ips :)), σ := (by with_unfolding_all exact (M.σ :)), lam := (by with_unfolding_all exact (M.lam :)), ε := (by with_unfolding_all exact (M.ε :)), fr := (by with_unfolding_all exact (M.fr :)),
      enum := (by with_unfolding_all exact (M.enum :)), ds := (by with_unfolding_all exact (M.ds :)), fr_unit := (by with_unfolding_all exact (M.fr_unit :)), fr_gram := (by with_unfolding_all exact (M.fr_gram :)) }, (by with_unfolding_all exact (U :)), ?_, (by with_unfolding_all exact (h0 :)), (by with_unfolding_all exact (he :))⟩
  obtain ⟨s, hs, hU⟩ := mem_mult_iff.1 hM
  refine mem_mult_iff.2 ⟨(by with_unfolding_all exact (s :)), fun T hT => ?_, (by with_unfolding_all exact (hU :))⟩
  have q := hs ((by with_unfolding_all exact (T :))) ((by with_unfolding_all exact (hT :)))
  exact ⟨fun v => ⟨⟨(by with_unfolding_all exact ((q.aut ((v))).left : _)), (by with_unfolding_all exact ((q.aut ((v))).level : _)), (by with_unfolding_all exact ((q.aut ((v))).cont : _))⟩, (by with_unfolding_all exact ((q.aut ((v))).smooth : _)),
    (by with_unfolding_all exact ((q.aut ((v))).zfin : _)), (by with_unfolding_all exact ((q.aut ((v))).growth : _))⟩, (by with_unfolding_all exact (q.cusp :)), (by with_unfolding_all exact (q.lev :)), (by with_unfolding_all exact (q.equiv :)), (by with_unfolding_all exact (q.cont :))⟩

end GlobalTheory.HeckeField

namespace GlobalTheory.HeckeField

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

theorem exists_bound (hU : GlobalTheory.Published.DiscreteSeriesUpqUnique) {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat3 D A3 Ks) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (kKs : Ks →+* ↥D.LL0)
    (hk : ∀ x : Ks, ((kKs x : ↥D.LL0) : D.what₂.LL) = algebraMap Ks D.what₂.LL x) (hL : R.toLevCh.Is A3.A.μ0)
    (hθ : IsInfFam R.θ) (hW : R.toRealDat.models_HW) (hu : R.toRealDat.LUnif) (hK : ∀ i, (R.FW i).IsKsForm)
    (h : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL ((ratDatR R cG kKs hk).WL j)) (hs : StabC (ratDatR R cG kKs hk) h)
    (hr : HeckeRd R cG kKs hk (SbD D) h) : ∃ S : Finset ℂ, (∀ z ∈ S, IsAlgebraic ℚ z) ∧ ∀ i, BoundAt R.C i S := by
  classical
  have key : ∀ i : Fin D.R.m, ∃ S : Finset ℂ, (∀ z ∈ S, IsAlgebraic ℚ z) ∧ BoundAt R.C i S := fun i => by
    have h1 : 1 ≤ i.1 + 1 := Nat.le_add_left _ _
    have := exists_boundAt hU R hL hθ hW hu (idxOf D (i.1 + 1)) (hK _) (h (i.1 + 1)) (hs _ h1 i.2)
      (fun k P α Rr hd => hr _ k P α Rr h1 i.2 hd)
    rwa [NX.idxOf_succ] at this
  choose S h1 h2 using key
  refine ⟨Finset.univ.biUnion S, fun z hz => ?_, fun i L hS => h2 i L fun z hz => hS z ?_⟩
  · obtain ⟨i, -, hz⟩ := Finset.mem_biUnion.1 hz
    exact h1 i z hz
  · exact Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hz⟩

def Bounds (Q : Pre) (f : Fr Q) (S : Finset ℂ) : Prop :=
  (∀ z ∈ S, IsAlgebraic ℚ z) ∧ ∀ (X : Stages) (f' : Fr X.B.toPre), Q = X.B.toPre → HEq f f' → ∀ i, BoundAt (Fr.at X f') i S

open Classical in

def gens (Q : Pre) (f : Fr Q) : Finset ℂ := if h : ∃ S, Bounds Q f S then h.choose else ∅

theorem gens_alg (Q : Pre) (f : Fr Q) : ∀ z ∈ gens Q f, IsAlgebraic ℚ z := by
  unfold gens
  split_ifs with h
  exacts [h.choose_spec.1, fun z hz => absurd hz (Finset.notMem_empty z)]

theorem boundAt_gens (X : Stages) (f : Fr X.B.toPre) {S : Finset ℂ} (h1 : ∀ z ∈ S, IsAlgebraic ℚ z)
    (h2 : ∀ i, BoundAt (Fr.at X f) i S) : ∀ i, BoundAt (Fr.at X f) i (gens X.B.toPre f) := by
  have h : ∃ S, Bounds X.B.toPre f S := ⟨S, h1, fun X' f' e hf => boundAt_tr X X' e f f' hf S h2⟩
  unfold gens
  rw [dif_pos h]
  exact h.choose_spec.2 X f rfl HEq.rfl

theorem rowEig_mem_fixedField : GlobalTheory.Published.DiscreteSeriesUpqUnique → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), LA hL x → ∀ hL' : ∀ j, ℕ → PlE (Dof x).host → Module.End (Dof x).what₂.LL ((SOf x).WL j), StabC (SOf x) hL' → HeckeRd x.m.z.R x.m.z.cG (kKsOf x) (hkOf x) (SbD (Dof x)) hL' → ∀ (i : Fin (Dof x).R.m) (σ : (Dof x).what₂.FT) (k : ℕ) (Pl : PlE (Dof x).host) α Rr, HkDat x.m.z.R (SbD (Dof x)) i k Pl α Rr → (Dof x).nd.goodRow σ → (Dof x).what₂.isot (i.1 + 1) σ ≠ ⊥ → ∃ c : ↥(Dof x).LL0, (Dof x).what₂.embLL (c : (Dof x).what₂.LL) = hkNorm x.m.z.R i k Pl * GlobalTheory.EigRows.rowEig x.r.Y i σ Pl (GlobalTheory.EigRows.diagLab (Dof x).R.r k) := by
  intro hU hL
  refine evG_all fun K => ⟨fun Q f _ => gens Q f, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun _ _ _ _ _ => ∅,
    fun Q f _ => gens_alg Q f, by simp, fun B f T _ hH _ _ _ _ _ w _ P x _ hL' hs hr i σ k Pl α Rr hd _ h0 => ?_⟩
  have hC : x.m.z.R.C = Fr.at (w.st x.o.Z) f := x.m.z.lev.C.trans (congrArg (Fr.at (w.st x.o.Z)) w.C_eq)
  have hb := x.m.z.pins.char.base
  obtain ⟨S, h1, h2⟩ := exists_bound hU x.m.z.R x.m.z.cG (kKsOf x) (hkOf x) hb.lev hb.models.inf hb.models.HW
    x.m.intersectionNumber_baseChange.prim.unif x.m.z.geo.fw.ks hL' hs hr
  rw [hC] at h2
  have h3 := boundAt_gens (w.st x.o.Z) f h1 h2 i
  rw [← hC] at h3
  obtain ⟨c, hc, e⟩ := B.mem_LL0C.1
    (h3 B.fixedCoefficientFieldInComplex hH.1 _ (eigSys_row x.r.Y hb.lev hb.models.inf h0) k Pl α Rr ((hkDat_iff hb.lev).1 hd))
  exact ⟨⟨c, hc⟩, e⟩

end GlobalTheory.HeckeField
