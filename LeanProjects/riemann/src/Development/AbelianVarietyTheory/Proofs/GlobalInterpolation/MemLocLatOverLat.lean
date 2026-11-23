import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.OverLatticeIffSelfDualOverBase
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdelicLatticeCompletionLocalGlobalStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLatticeVectorApproxAllFinitePlacesStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemDualSetOfMemSpan
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DualOfDualFrames
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ImportsExtra
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsSplittingOfCharacter
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsAddEquivField
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsSecondFunctional
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MulVecMemIff
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemRangeBcOfTransposeMulEqOne

noncomputable section

namespace GlobalTheory.OverLat

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection GlobalTheory.OverCompare
open scoped TensorProduct

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {k : ℕ}

local instance (priority := high) acgLat {v : HeightOneSpectrum (𝓞 F)}
    (L : Submodule (intV E v) (Fin k → E ⊗[F] v.adicCompletion F)) : AddCommGroup L := L.addCommGroup

abbrev loc (v : HeightOneSpectrum (𝓞 F)) (x : Fin k → E) : Fin k → E ⊗[F] v.adicCompletion F :=
  fun i => inclE (F := F) (v.adicCompletion F) (x i)

theorem loc_mem (v : HeightOneSpectrum (𝓞 F)) {Λ : Submodule (𝓞 E) (Fin k → E)} {x : Fin k → E}
    (hx : x ∈ Λ) : loc v x ∈ locLat v Λ := Submodule.subset_span ⟨x, hx, rfl⟩

theorem loc_add (v : HeightOneSpectrum (𝓞 F)) (x y : Fin k → E) :
    loc v (x + y) = loc v x + loc v y := by
  funext i; simp [loc]

theorem loc_zero (v : HeightOneSpectrum (𝓞 F)) : loc v (0 : Fin k → E) = 0 := by
  funext i; simp [loc]

theorem loc_smul (v : HeightOneSpectrum (𝓞 F)) (a : 𝓞 E) (x : Fin k → E) :
    loc v (a • x) = GlobalTheory.IndefiniteRowSideFullHecke.OverPlaceIntegralForm.toIntV E v a • loc v x := by
  funext i
  show inclE (F := F) (v.adicCompletion F) ((a : E) * x i) = _
  rw [map_mul]; rfl

theorem locLat_mono (v : HeightOneSpectrum (𝓞 F)) {Λ Λ' : Submodule (𝓞 E) (Fin k → E)} (h : Λ ≤ Λ') :
    locLat v Λ ≤ locLat v Λ' := Submodule.span_mono (Set.image_mono h)

theorem nsmul_mem_locLat (v : HeightOneSpectrum (𝓞 F)) {Λ Λ' : Submodule (𝓞 E) (Fin k → E)} {T : ℕ}
    (h : ∀ x ∈ Λ', T • x ∈ Λ) : ∀ y ∈ locLat v Λ', T • y ∈ locLat v Λ := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    have := loc_mem v (h x hx)
    convert this using 1
    funext i; simp [loc]
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx

theorem mem_span_dualSet (σ : E →+* E) (J : Matrix (Fin k) (Fin k) E)
    (Λ : Submodule (𝓞 E) (Fin k → E)) (y : Fin k → E) :
    y ∈ Submodule.span (𝓞 E) (dualSet σ J Λ) ↔ y ∈ dualSet σ J Λ := by
  refine ⟨fun hy => ?_, fun hy => Submodule.subset_span hy⟩
  induction hy using Submodule.span_induction with
  | mem y hy => exact hy
  | zero => intro x _; simp [hform]
  | add y z _ _ hy hz =>
    intro x hx
    have : hform σ J x (y + z) = hform σ J x y + hform σ J x z := by
      simp [hform, mul_add, Finset.sum_add_distrib]
    rw [this]; exact add_mem (hy x hx) (hz x hx)
  | smul a y _ hy =>
    intro x hx
    have : hform σ J x (a • y) = algebraMap (𝓞 E) E a * hform σ J x y := by
      simp only [hform, Finset.mul_sum, Pi.smul_apply, Algebra.smul_def]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [this]; exact mul_mem ⟨a, rfl⟩ (hy x hx)

theorem approx_one {Λ Λ' : Submodule (𝓞 E) (Fin k → E)} (hfin : Module.Finite (𝓞 E) Λ') {T : ℕ}
    (hT : T ≠ 0) (h : ∀ x ∈ Λ', T • x ∈ Λ) (v : HeightOneSpectrum (𝓞 F))
    (y : Fin k → E ⊗[F] v.adicCompletion F) (hy : y ∈ locLat v Λ') :
    ∃ x ∈ Λ', y - loc v x ∈ locLat v Λ ∧ ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → loc w x ∈ locLat w Λ := by
  classical
  obtain ⟨x, hx, H⟩ := GlobalTheory.T.exists_lattice_vector_approx_all_finitePlaces F E k Λ' hfin T hT
    (Pi.single (M := fun w : HeightOneSpectrum (𝓞 F) => Fin k → E ⊗[F] w.adicCompletion F) v y) (fun w => by
      by_cases hw : w = v
      · subst hw; rw [Pi.single_eq_same]; exact hy
      · rw [Pi.single_eq_of_ne hw]; exact zero_mem _)
  refine ⟨x, hx, ?_, fun w hw => ?_⟩
  · obtain ⟨z, hz, e⟩ := H v
    rw [Pi.single_eq_same] at e
    rw [e, add_sub_cancel_left]
    exact nsmul_mem_locLat v h z hz
  · obtain ⟨z, hz, e⟩ := H w
    rw [Pi.single_eq_of_ne hw] at e
    rw [show loc w x = -(T • z) from eq_neg_of_add_eq_zero_left e.symm]
    exact neg_mem (nsmul_mem_locLat w h z hz)

set_option synthInstance.maxHeartbeats 200000 in

theorem mem_of_count {Λ Λ' : Submodule (𝓞 E) (Fin k → E)} (hfin : Module.Finite (𝓞 E) Λ') {T f : ℕ}
    (hT : T ≠ 0) (hf : f ≠ 0) (h : ∀ x ∈ Λ', T • x ∈ Λ)
    (hidx : Λ.toAddSubgroup.relIndex Λ'.toAddSubgroup = T ^ (2 * f))
    (hpl : Nat.card {v : HeightOneSpectrum (𝓞 F) // (T : 𝓞 F) ∈ v.asIdeal} = f)
    (Q : ∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∈ v.asIdeal → Type) [∀ v h, AddCommGroup (Q v h)]
    (hQ : ∀ v h, Nat.card (Q v h) = T * T) (ψ : ∀ v h, locLat v Λ' →+ Q v h)
    (hsur : ∀ v h, Function.Surjective (ψ v h))
    (hker : ∀ v h (x : locLat v Λ'), x.1 ∈ locLat v Λ → ψ v h x = 0) :
    ∀ v h (x : locLat v Λ'), ψ v h x = 0 → x.1 ∈ locLat v Λ := by
  classical
  haveI : Finite {v : HeightOneSpectrum (𝓞 F) // (T : 𝓞 F) ∈ v.asIdeal} :=
    Nat.finite_of_card_ne_zero (hpl ▸ hf)
  haveI := Fintype.ofFinite {v : HeightOneSpectrum (𝓞 F) // (T : 𝓞 F) ∈ v.asIdeal}
  let Ψ : Λ'.toAddSubgroup →+ ∀ p : {v : HeightOneSpectrum (𝓞 F) // (T : 𝓞 F) ∈ v.asIdeal}, Q p.1 p.2 :=
    { toFun := fun x p => ψ p.1 p.2 ⟨loc p.1 x.1, loc_mem p.1 (Λ := Λ') x.2⟩
      map_zero' := funext fun p => by
        exact (congrArg (ψ p.1 p.2) (Subtype.ext (loc_zero p.1))).trans (ψ p.1 p.2).map_zero
      map_add' := fun x y => funext fun p => by
        exact (congrArg (ψ p.1 p.2) (Subtype.ext (loc_add p.1 x.1 y.1))).trans
          ((ψ p.1 p.2).map_add ⟨_, loc_mem p.1 (Λ := Λ') x.2⟩ ⟨_, loc_mem p.1 (Λ := Λ') y.2⟩) }
  have hΨ : Function.Surjective Ψ := by
    intro t
    choose y hy using fun p : {v : HeightOneSpectrum (𝓞 F) // (T : 𝓞 F) ∈ v.asIdeal} => hsur p.1 p.2 (t p)
    obtain ⟨x, hx, H⟩ := GlobalTheory.T.exists_lattice_vector_approx_all_finitePlaces F E k Λ' hfin T hT
      (fun v => if hv : (T : 𝓞 F) ∈ v.asIdeal then (y ⟨v, hv⟩).1 else 0) (fun v => by
        by_cases hv : (T : 𝓞 F) ∈ v.asIdeal
        · rw [dif_pos hv]; exact (y ⟨v, hv⟩).2
        · rw [dif_neg hv]; exact zero_mem _)
    refine ⟨⟨x, hx⟩, funext fun p => ?_⟩
    obtain ⟨z, hz, e⟩ := H p.1
    rw [dif_pos p.2] at e
    have h0 := hker p.1 p.2 (T • ⟨z, hz⟩) (nsmul_mem_locLat p.1 h z hz)
    have e' : y p = ⟨loc p.1 x, loc_mem p.1 hx⟩ + T • ⟨z, hz⟩ := Subtype.ext e
    have e2 := (congrArg (ψ p.1 p.2) e').trans ((ψ p.1 p.2).map_add _ _)
    exact (((hy p).symm.trans e2).trans ((congrArg (_ + ·) h0).trans (add_zero _))).symm
  have hcard : Ψ.ker.index = T ^ (2 * f) := by
    rw [AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hΨ, AddSubgroup.card_top, Nat.card_pi]
    simp only [hQ]
    rw [Finset.prod_const, Finset.card_univ, ← Nat.card_eq_fintype_card, hpl, ← sq, ← pow_mul]
  have hle : Λ.toAddSubgroup.addSubgroupOf Λ'.toAddSubgroup ≤ Ψ.ker := fun x hx =>
    funext fun p => hker p.1 p.2 _ (loc_mem p.1 (Λ := Λ) hx)
  have hge : Ψ.ker ≤ Λ.toAddSubgroup.addSubgroupOf Λ'.toAddSubgroup := by
    have h1 := AddSubgroup.relIndex_mul_index hle
    rw [hcard, show (Λ.toAddSubgroup.addSubgroupOf Λ'.toAddSubgroup).index = T ^ (2 * f) from hidx] at h1
    exact AddSubgroup.relIndex_eq_one.1 (Nat.eq_of_mul_eq_mul_right (by positivity) (h1.trans (one_mul _).symm))
  intro v hv x hx
  obtain ⟨x₀, hx₀, h1, h2⟩ := approx_one hfin hT h v x.1 x.2
  have : (⟨x₀, hx₀⟩ : Λ'.toAddSubgroup) ∈ Ψ.ker := by
    funext p
    obtain ⟨w, hw⟩ := p
    by_cases hwv : w = v
    · subst hwv
      have := hker w hw (x - ⟨loc w x₀, loc_mem w hx₀⟩) h1
      exact (sub_eq_zero.1 (((ψ w hw).map_sub _ _).symm.trans this)).symm.trans hx
    · exact hker w hw _ (h2 w hwv)
  have h3 := add_mem h1 (loc_mem v (show x₀ ∈ Λ from hge this))
  rwa [sub_add_cancel] at h3

end General

section Split

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {k : ℕ}
  {σ : E →ₐ[F] E} {v : HeightOneSpectrum (𝓞 F)}
  {s : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F}

def e₁ (hs : IsSplitting σ v s) : intV E v :=
  ⟨s.symm (1, 0), (hs.2.2 _).2 (by rw [s.apply_symm_apply]; exact ⟨one_mem _, zero_mem _⟩)⟩

def e₂ (hs : IsSplitting σ v s) : intV E v :=
  ⟨s.symm (0, 1), (hs.2.2 _).2 (by rw [s.apply_symm_apply]; exact ⟨zero_mem _, one_mem _⟩)⟩

theorem prP_e₁ (hs : IsSplitting σ v s) : prP s (e₁ hs) = 1 := congrArg Prod.fst (s.apply_symm_apply _)
theorem prPbar_e₁ (hs : IsSplitting σ v s) : prPbar s (e₁ hs) = 0 := congrArg Prod.snd (s.apply_symm_apply _)
theorem prP_e₂ (hs : IsSplitting σ v s) : prP s (e₂ hs) = 0 := congrArg Prod.fst (s.apply_symm_apply _)
theorem prPbar_e₂ (hs : IsSplitting σ v s) : prPbar s (e₂ hs) = 1 := congrArg Prod.snd (s.apply_symm_apply _)

theorem vec_ext (s : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)
    {x y : Fin k → E ⊗[F] v.adicCompletion F} (h1 : ∀ i, prP s (x i) = prP s (y i))
    (h2 : ∀ i, prPbar s (x i) = prPbar s (y i)) : x = y :=
  funext fun i => s.injective (Prod.ext (h1 i) (h2 i))

theorem map_smul_vec (p : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F) (a : intV E v)
    (x : Fin k → E ⊗[F] v.adicCompletion F) (i : Fin k) : p ((a • x) i) = p a * p (x i) := map_mul p _ _

theorem e₁_add_e₂ (hs : IsSplitting σ v s) (x : Fin k → E ⊗[F] v.adicCompletion F) :
    e₁ hs • x + e₂ hs • x = x :=
  vec_ext s (fun i => by rw [Pi.add_apply, map_add, map_smul_vec, map_smul_vec, prP_e₁, prP_e₂]; ring)
    (fun i => by rw [Pi.add_apply, map_add, map_smul_vec, map_smul_vec, prPbar_e₁, prPbar_e₂]; ring)

theorem e₂_e₁ (hs : IsSplitting σ v s) (x : Fin k → E ⊗[F] v.adicCompletion F) :
    e₂ hs • e₁ hs • x = 0 :=
  vec_ext s (fun i => by rw [map_smul_vec, prP_e₂]; simp)
    (fun i => by rw [map_smul_vec, map_smul_vec, prPbar_e₁]; simp)

theorem prP_sig (hs : IsSplitting σ v s) (a : E ⊗[F] v.adicCompletion F) :
    prP s (sigR σ (v.adicCompletion F) a) = prPbar s a := congrArg Prod.fst (hs.2.1 a)

theorem prPbar_sig (hs : IsSplitting σ v s) (a : E ⊗[F] v.adicCompletion F) :
    prPbar s (sigR σ (v.adicCompletion F) a) = prP s a := congrArg Prod.snd (hs.2.1 a)

theorem sig_e₁ (hs : IsSplitting σ v s) : sigR σ (v.adicCompletion F) (e₁ hs) = e₂ hs :=
  s.injective (Prod.ext ((prP_sig hs _).trans ((prPbar_e₁ hs).trans (prP_e₂ hs).symm))
    ((prPbar_sig hs _).trans ((prP_e₁ hs).trans (prPbar_e₂ hs).symm)))

theorem sig_e₂ (hs : IsSplitting σ v s) : sigR σ (v.adicCompletion F) (e₂ hs) = e₁ hs :=
  s.injective (Prod.ext ((prP_sig hs _).trans ((prPbar_e₂ hs).trans (prP_e₁ hs).symm))
    ((prPbar_sig hs _).trans ((prP_e₂ hs).trans (prPbar_e₁ hs).symm)))

theorem map_gram {A K : Type} [CommRing A] [CommRing K] (τ : A →+* A) (p q : A →+* K)
    (h : ∀ a, p (τ a) = q a) (X J Y Z : Matrix (Fin k) (Fin k) A) (H : cT τ X * J * Y = Z) :
    (X.map q)ᵀ * J.map p * Y.map p = Z.map p := by
  rw [← H, Matrix.map_mul, Matrix.map_mul]
  congr 2
  ext i j
  exact (h _).symm

theorem hform_smul_left {A : Type} [CommRing A] (τ : A →+* A) (J : Matrix (Fin k) (Fin k) A) (a : A)
    (x y : Fin k → A) : hform τ J (a • x) y = hform τ J x (τ a • y) := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, map_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hform_add_left {A : Type} [CommRing A] (τ : A →+* A) (J : Matrix (Fin k) (Fin k) A)
    (x x' y : Fin k → A) : hform τ J (x + x') y = hform τ J x y + hform τ J x' y := by
  simp [hform, add_mul, Finset.sum_add_distrib]

theorem hform_loc (J : Matrix (Fin k) (Fin k) E) (x y : Fin k → E) :
    hform (sigR σ (v.adicCompletion F)) (J.map (inclE (F := F) (v.adicCompletion F))) (loc v x) (loc v y) =
      inclE (F := F) (v.adicCompletion F) (hform (σ : E →+* E) J x y) := by
  simp only [hform, map_sum, map_mul]
  rfl

end Split

section Level

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι : Type} [Fintype ι] {hc : ι → HCParam R} {C : ColumnChain R ι hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in

theorem localAtT (L : ColLevel R F E sp gp C A clsLat) (N : Submodule (𝓞 E) (Fin R.k → E))
    (v : HeightOneSpectrum (𝓞 F)) (hv : (A.T : 𝓞 F) ∈ v.asIdeal)
    {s : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F}
    (hs : IsSplitting sp.cm.sig v s)
    (hfac : ∀ x : locLat v (dualLb L), (∀ i, prP s (x.1 i) = 0) → L.fT v hv x = 0)
    (ε : L.fM v hv ≃+ IsLocalRing.ResidueField (v.adicCompletionIntegers F))
    (hε : ∀ (a : intV E v) (a' : v.adicCompletionIntegers F), (a' : v.adicCompletion F) = prP s a →
      ∀ m, ε (a • m) = a' • ε m)
    (iso : Nonempty ((locLat v (dualLb L) ⧸ (locLat v L.Lb).submoduleOf (locLat v (dualLb L))) ≃ₗ[intV E v]
      (intV E v ⧸ primeOf (prP s)) × (intV E v ⧸ primeOf (prPbar s))))
    (hle : locLat v L.Lb ≤ locLat v (dualLb L))
    (hker : ∀ x : locLat v (dualLb L), L.fT v hv x = 0 → e₁ hs • x.1 ∈ locLat v L.Lb)
    (hN : ∀ y, y ∈ locLat v N ↔ y ∈ locLat v (dualLb L) ∧ e₂ hs • y ∈ locLat v L.Lb) :
    LocalAtT L N v hv s := by
  obtain ⟨B, C', hBC, hB, hC⟩ := GlobalTheory.DualFrame.exists_dual_frames F E sp.cm.sig R.k sp.gram0 (gram_matrix_det_unit sp) L.Lb
    L.Lb_fin L.Lb_span v
  obtain ⟨m₁, st₁, fr₁⟩ := GlobalTheory.OverCompare.StabPart.stabPart F E sp.cm.sig v s hs R.k (locLat v L.Lb)
  obtain ⟨m₂, st₂, fr₂⟩ := GlobalTheory.OverCompare.StabPart.stabPart F E sp.cm.sig v s hs R.k (locLat v (dualLb L))
  obtain ⟨-, stN, -⟩ := GlobalTheory.OverCompare.StabPart.stabPart F E sp.cm.sig v s hs R.k (locLat v N)
  obtain ⟨fB1, fB2⟩ := fr₁ B hB
  obtain ⟨firstChern_family, fC2⟩ := fr₂ C' hC
  have hpart1 : partOf (prP s) (locLat v N) = partOf (prP s) (locLat v (dualLb L)) := by
    ext y
    rw [mem_partOf _ (sur_prP hs), mem_partOf _ (sur_prP hs)]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, ((hN x).1 hx).1, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨e₁ hs • x, (hN _).2 ⟨Submodule.smul_mem _ _ hx, ?_⟩, funext fun i => ?_⟩
      · rw [e₂_e₁]; exact zero_mem _
      · rw [map_smul_vec, prP_e₁, one_mul]
  have hpart2 : partOf (prPbar s) (locLat v N) = partOf (prPbar s) (locLat v L.Lb) := by
    ext y
    rw [mem_partOf _ (sur_prPbar hs), mem_partOf _ (sur_prPbar hs)]
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨e₂ hs • x, ((hN x).1 hx).2, funext fun i => ?_⟩
      rw [map_smul_vec, prPbar_e₂, one_mul]
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, (hN x).2 ⟨hle hx, Submodule.smul_mem _ _ hx⟩, rfl⟩
  have d1 : ∀ g ∈ UPts sp.cm.sig sp.gram0 (v.adicCompletion F),
      bc (prPbar s) g ∈ stabGL (partOf (prPbar s) (locLat v L.Lb)) ↔
        bc (prP s) g ∈ stabGL (partOf (prP s) (locLat v (dualLb L))) := fun g hg =>
    GlobalTheory.OverCompare.mem_stabGL_iff_of_dual_frames _ _ R.k _ _ _ _ _ _ _ fB2 firstChern_family
      ((map_gram _ (prP s) (prPbar s) (prP_sig hs) _ _ _ _ hBC).trans
        (Matrix.map_one _ (map_zero _) (map_one _)))
      (map_gram _ (prP s) (prPbar s) (prP_sig hs) _ _ _ _ hg)
  have d2 : ∀ g ∈ UPts sp.cm.sig sp.gram0 (v.adicCompletion F),
      bc (prP s) g ∈ stabGL (partOf (prP s) (locLat v L.Lb)) ↔
        bc (prPbar s) g ∈ stabGL (partOf (prPbar s) (locLat v (dualLb L))) := fun g hg =>
    GlobalTheory.OverCompare.mem_stabGL_iff_of_dual_frames _ _ R.k _ _ _ _ _ _ _ fB1 fC2
      ((map_gram _ (prPbar s) (prP s) (prPbar_sig hs) _ _ _ _ hBC).trans
        (Matrix.map_one _ (map_zero _) (map_one _)))
      (map_gram _ (prPbar s) (prP s) (prPbar_sig hs) _ _ _ _ hg)
  have hstab : ∀ g ∈ UPts sp.cm.sig sp.gram0 (v.adicCompletion F),
      g ∈ levelVL sp.cm.sig sp.gram0 v N ↔ bc (prP s) g ∈ stabGL (partOf (prP s) (locLat v N)) := by
    intro g hg
    refine ⟨fun h => ((stN g).1 h.2).1, fun h => ⟨hg, (stN g).2 ⟨h, ?_⟩⟩⟩
    rw [hpart2, d1 g hg, ← hpart1]; exact h
  have hb : IsFrame (partOf (prP s) (locLat v N)) (bc (prP s) C') := hpart1 ▸ firstChern_family
  have hΛ : ∀ y, y ∈ partOf (prP s) (locLat v N) ↔
      ∃ x ∈ locLat v (dualLb L), (fun i => prP s (x i)) = y := fun y => by
    rw [hpart1, mem_partOf _ (sur_prP hs)]
  have hcong : ∀ x x' : locLat v (dualLb L), (∀ i, prP s (x.1 i) = prP s (x'.1 i)) →
      L.fT v hv x = L.fT v hv x' := by
    intro x x' h
    have := hfac (x - x') (fun i => by
      show prP s (x.1 i - x'.1 i) = 0
      rw [map_sub, h, sub_self])
    exact sub_eq_zero.1 (((L.fT v hv).map_sub _ _).symm.trans this)
  choose lift hlift hlift' using fun y : partOf (prP s) (locLat v N) => (hΛ y.1).1 y.2
  let f : partOf (prP s) (locLat v N) →ₗ[v.adicCompletionIntegers F]
      IsLocalRing.ResidueField (v.adicCompletionIntegers F) :=
    { toFun := fun y => ε (L.fT v hv ⟨lift y, hlift y⟩)
      map_add' := fun y z => by
        refine Eq.trans (congrArg ε ?_) (ε.map_add _ _)
        refine (hcong _ (⟨lift y, hlift y⟩ + ⟨lift z, hlift z⟩) fun i => ?_).trans ((L.fT v hv).map_add _ _)
        show prP s (lift (y + z) i) = prP s (lift y i + lift z i)
        rw [map_add, congrFun (hlift' (y + z)) i, congrFun (hlift' y) i, congrFun (hlift' z) i]
        rfl
      map_smul' := fun a y => by
        obtain ⟨d, hd, hda⟩ := sur_prP hs a a.2
        refine Eq.trans (congrArg ε ?_) (hε ⟨d, hd⟩ a hda.symm _)
        refine (hcong _ ((⟨d, hd⟩ : intV E v) • ⟨lift y, hlift y⟩) fun i => ?_).trans
          ((L.fT v hv).map_smul _ _)
        show prP s (lift (a • y) i) = prP s (d * lift y i)
        rw [map_mul, congrFun (hlift' (a • y)) i, congrFun (hlift' y) i, hda]
        rfl }
  have hfe : ∀ (x : locLat v (dualLb L)) (y : partOf (prP s) (locLat v N)),
      (∀ i, y.1 i = prP s (x.1 i)) → f y = ε (L.fT v hv x) := fun x y h =>
    congrArg ε (hcong _ _ fun i => (congrFun (hlift' y) i).trans (h i))
  have hk : ∀ y, f y = 0 ↔ y.1 ∈ partOf (prP s) (locLat v L.Lb) := by
    intro y
    rw [mem_partOf _ (sur_prP hs)]
    constructor
    · intro h
      have h0 : L.fT v hv ⟨lift y, hlift y⟩ = 0 := (map_eq_zero_iff _ ε.injective).1 h
      refine ⟨_, hker _ h0, funext fun i => ?_⟩
      rw [map_smul_vec, prP_e₁, one_mul]
      exact congrFun (hlift' y) i
    · rintro ⟨x, hx, hxy⟩
      exact (hfe ⟨x, hle hx⟩ y fun i => (congrFun hxy i).symm).trans
        ((congrArg ε (L.fT_L v hv ⟨x, hle hx⟩ hx)).trans ε.map_zero)
  refine ⟨hs, hfac, iso, hpart1, hpart2,
    existsUnique_upts sp.cm.sig sp.gram0 sp.baseGram_isHermitian (gram_matrix_det_unit sp) _ s hs.2.1, hstab,
    ⟨bc (prP s) C', hb, fun g hg => (hstab g hg).trans (hb.mem_stabGL_iff _)⟩, f, ε, hε, hfe, ?_, ?_, hk, ?_⟩
  · intro h0
    apply L.fT_ne v hv
    ext x
    have := hfe x ⟨_, (hΛ _).2 ⟨x.1, x.2, rfl⟩⟩ (fun _ => rfl)
    rw [h0, LinearMap.zero_apply] at this
    exact (map_eq_zero_iff _ ε.injective).1 this.symm
  · intro y
    refine (hfe ((A.T : intV E v) • ⟨lift y, hlift y⟩) _ fun i => ?_).trans
      ((congrArg ε (L.fT_T v hv _)).trans ε.map_zero)
    show ((A.T : v.adicCompletionIntegers F) : v.adicCompletion F) * y.1 i =
      prP s (((A.T : intV E v) : E ⊗[F] v.adicCompletion F) * lift y i)
    rw [map_mul, congrFun (hlift' y) i]
    simp
  · intro g
    rw [L.UlocAlt v hv, Subgroup.mem_inf]
    constructor
    · rintro ⟨h1, h2⟩
      have h3 : bc (prP s) g ∈ stabGL (partOf (prP s) (locLat v N)) := hpart1 ▸ ((st₂ g).1 h2.1).1
      exact ⟨(hstab g h1.1).2 h3, (mem_stabFun_iff_part (prP s) _ _ hΛ _ f ε hfe g h2.1 h3).1 h2⟩
    · rintro ⟨h1, h3, h4⟩
      have hsub : ∀ y ∈ partOf (prP s) (locLat v L.Lb), y ∈ partOf (prP s) (locLat v N) := fun y hy => by
        obtain ⟨x, hx, hxy⟩ := (mem_partOf _ (sur_prP hs) _ _).1 hy
        exact (hΛ y).2 ⟨x, hle hx, hxy⟩
      have h5 : bc (prP s) g ∈ stabGL (partOf (prP s) (locLat v L.Lb)) := by
        intro y
        constructor
        · intro hy
          exact (hk ⟨_, (h3 y).1 (hsub y hy)⟩).1 ((h4 ⟨y, hsub y hy⟩).trans ((hk ⟨y, hsub y hy⟩).2 hy))
        · intro hy
          have hy' := (h3 y).2 (hsub _ hy)
          exact (hk ⟨y, hy'⟩).1 ((h4 ⟨y, hy'⟩).symm.trans ((hk ⟨_, hsub _ hy⟩).2 hy))
      have h6 : bc (prP s) g ∈ stabGL (partOf (prP s) (locLat v (dualLb L))) := hpart1 ▸ h3
      have h7 : g ∈ stabGL (locLat v (dualLb L)) := (st₂ g).2 ⟨h6, (d2 g h1.1).1 h5⟩
      exact ⟨⟨h1.1, (st₁ g).2 ⟨h5, (d1 g h1.1).2 h6⟩⟩,
        (mem_stabFun_iff_part (prP s) _ _ hΛ _ f ε hfe g h7 h3).2 ⟨h3, h4⟩⟩

omit [StarRing E] in
theorem sigR_mem_intV (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) :
    ∀ a ∈ intV E v, sigR σ (v.adicCompletion F) a ∈ intV E v := by
  have : intV E v ≤ (intV E v).comap (sigR σ (v.adicCompletion F)) := by
    refine Subring.closure_le.2 ?_
    rintro _ (⟨⟨_, a, rfl⟩, rfl⟩ | ⟨a, rfl⟩)
    · exact tmul_mem_intV (⟨σ a, (a.isIntegral_coe).map (σ.restrictScalars ℤ)⟩ : 𝓞 E)
    · show (σ 1) ⊗ₜ[F] (a : v.adicCompletion F) ∈ intV E v
      rw [map_one]
      exact Subring.subset_closure (Or.inr ⟨a, rfl⟩)
  exact this

theorem dual_loc (L : ColLevel R F E sp gp C A clsLat) (v : HeightOneSpectrum (𝓞 F)) :
    (∀ y, y ∈ locLat v (dualLb L) ↔ ∀ x ∈ locLat v L.Lb, hform (sigR sp.cm.sig (v.adicCompletion F))
      (sp.gram0.map (inclE (F := F) (v.adicCompletion F))) x y ∈ intV E v) ∧
    (∀ y, y ∈ locLat v L.Lb ↔ ∀ x ∈ locLat v (dualLb L), hform (sigR sp.cm.sig (v.adicCompletion F))
      (sp.gram0.map (inclE (F := F) (v.adicCompletion F))) x y ∈ intV E v) ∧
    (∀ x, x ∈ locLat v L.Lb ↔ ∀ y ∈ locLat v (dualLb L), hform (sigR sp.cm.sig (v.adicCompletion F))
      (sp.gram0.map (inclE (F := F) (v.adicCompletion F))) x y ∈ intV E v) := by
  obtain ⟨B, C', hBC, hB, hC⟩ := GlobalTheory.DualFrame.exists_dual_frames F E sp.cm.sig R.k sp.gram0 (gram_matrix_det_unit sp) L.Lb
    L.Lb_fin L.Lb_span v
  refine GlobalTheory.DualFrames.dual_of_dual_frames _ (intV E v) _ (fun a => ?_) (sigR_mem_intV _ v) R.k _ ?_ B C' _ _ hBC hB hC
  · induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      show (star (star a)) ⊗ₜ[F] b = _
      rw [star_star]
    | add a b ha hb => rw [map_add, map_add, ha, hb]
  · ext i j
    exact congrArg (inclE (F := F) (v.adicCompletion F)) (congrFun (congrFun sp.baseGram_isHermitian i) j)

theorem le_dualLb (L : ColLevel R F E sp gp C A clsLat) : L.Lb ≤ dualLb L :=
  fun x hx => Submodule.subset_span (L.Lb_int x hx)

theorem nsmul_mem (L : ColLevel R F E sp gp C A clsLat) : ∀ x ∈ dualLb L, A.T • x ∈ L.Lb := by
  intro x hx
  have := L.Lb_dual x ((mem_span_dualSet _ _ _ _).1 hx)
  rwa [Nat.cast_smul_eq_nsmul] at this

theorem finite_dualLb (L : ColLevel R F E sp gp C A clsLat) : Module.Finite (𝓞 E) (dualLb L) := by
  haveI := L.Lb_fin
  let φ : dualLb L →ₗ[𝓞 E] L.Lb :=
    LinearMap.codRestrict _ (A.T • (dualLb L).subtype) (fun x => nsmul_mem L x.1 x.2)
  refine Module.Finite.of_injective φ fun x y h => Subtype.ext ?_
  have h' : A.T • x.1 = A.T • y.1 := congrArg Subtype.val h
  exact nsmul_right_injective A.T_prime.ne_zero h'

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in

theorem exists_local (L : ColLevel R F E sp gp C A clsLat)
    (v : HeightOneSpectrum (𝓞 F)) (hv : (A.T : 𝓞 F) ∈ v.asIdeal) :
    ∃ s : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F,
      IsSplitting sp.cm.sig v s ∧
      (∀ x : locLat v (dualLb L), (∀ i, prP s (x.1 i) = 0) → L.fT v hv x = 0) ∧
      (∃ ε : L.fM v hv ≃+ IsLocalRing.ResidueField (v.adicCompletionIntegers F),
        ∀ (a : intV E v) (a' : v.adicCompletionIntegers F), (a' : v.adicCompletion F) = prP s a →
          ∀ m, ε (a • m) = a' • ε m) ∧
      Nonempty (L.fM v hv ≃ₗ[intV E v] (intV E v ⧸ primeOf (prP s))) ∧
      Nat.card (intV E v ⧸ primeOf (prPbar s)) = A.T ∧
      ∃ f₂ : locLat v (dualLb L) →ₗ[intV E v] (intV E v ⧸ primeOf (prPbar s)),
        Function.Surjective ((L.fT v hv).prod f₂) ∧
        (∀ x : locLat v (dualLb L), x.1 ∈ locLat v L.Lb → f₂ x = 0) ∧
        ∀ x : locLat v (dualLb L), (∀ i, prPbar s (x.1 i) = 0) → f₂ x = 0 := by
  obtain ⟨χ, hχ⟩ := GlobalTheory.PrimeOrderModule.exists_character (intV E v) (L.fM v hv) A.T A.T_prime (L.fM_card v hv)
  obtain ⟨s, hs, hsχ⟩ := GlobalTheory.OverSplit.exists_splitting_of_character F E sp.cm.sig sp.cm.deg2 (fun x => star_star x)
    (fun x hx => (sp.cm.fixed x).1 hx) sp.cm.cmUnram.2.2 v A.T A.T_prime χ
  obtain ⟨hε, hiso, hcard⟩ := GlobalTheory.OverResidue.residue_of_prime_card F E sp.cm.sig v s hs (L.fM v hv) A.T A.T_prime
    (L.fM_card v hv) (fun a m ha => hχ a m (hsχ a ha))
  have hfac : ∀ x : locLat v (dualLb L), (∀ i, prP s (x.1 i) = 0) → L.fT v hv x = 0 := by
    intro x hx
    have e : x = e₂ hs • x := Subtype.ext (vec_ext s
      (fun i => (hx i).trans (by
        show _ = prP s ((e₂ hs • x.1) i)
        rw [map_smul_vec, prP_e₂, zero_mul]))
      (fun i => by
        show _ = prPbar s ((e₂ hs • x.1) i)
        rw [map_smul_vec, prPbar_e₂, one_mul]))
    exact (congrArg (L.fT v hv) e).trans (((L.fT v hv).map_smul _ _).trans
      (hχ _ _ (hsχ _ (by rw [prP_e₂]; simp))))
  have h1 : ∀ x : locLat v (dualLb L), L.fT v hv (e₁ hs • x) = L.fT v hv x := by
    intro x
    have e : x = e₁ hs • x + e₂ hs • x := Subtype.ext (e₁_add_e₂ hs x.1).symm
    have h0 := hfac (e₂ hs • x) (fun i => by
      show prP s ((e₂ hs • x.1) i) = 0
      rw [map_smul_vec, prP_e₂, zero_mul])
    exact (((congrArg (L.fT v hv) e).trans ((L.fT v hv).map_add _ _)).trans
      ((congrArg (_ + ·) h0).trans (add_zero _))).symm
  obtain ⟨x₀, hx₀⟩ := DFunLike.ne_iff.1 (L.fT_ne v hv)
  obtain ⟨-, hd2, hd3⟩ := dual_loc L v
  obtain ⟨f₂, hsur, hk, hk2⟩ := GlobalTheory.SecondFunctional.exists_second_functional F E sp.cm.sig v s hs R.k _ (locLat v L.Lb)
    (locLat v (dualLb L)) (fun y hy => (hd2 y).1 hy) hd3 A.T A.T_prime.ne_zero
    (nsmul_mem_locLat v (nsmul_mem L))
    ⟨(e₁ hs • x₀).1, (e₁ hs • x₀).2, fun h => hx₀ ((h1 x₀).symm.trans (L.fT_L v hv _ h)), fun i => by
      show prPbar s ((e₁ hs • x₀.1) i) = 0
      rw [map_smul_vec, prPbar_e₁, zero_mul]⟩
  have hsur1 : Function.Surjective (L.fT v hv) := by
    haveI : Fact (Nat.card (L.fM v hv)).Prime := ⟨(L.fM_card v hv).symm ▸ A.T_prime⟩
    rcases (LinearMap.range (L.fT v hv)).toAddSubgroup.eq_bot_or_eq_top_of_prime_card with h | h
    · have : L.fT v hv x₀ ∈ (LinearMap.range (L.fT v hv)).toAddSubgroup := ⟨x₀, rfl⟩
      rw [h] at this
      exact absurd this hx₀
    · intro m
      have : m ∈ (LinearMap.range (L.fT v hv)).toAddSubgroup := h ▸ AddSubgroup.mem_top m
      exact this
  refine ⟨s, hs, hfac, hε, hiso, hcard, f₂, ?_, hk, hk2⟩
  rintro ⟨m, n⟩
  obtain ⟨x, rfl⟩ := hsur1 m
  obtain ⟨y, rfl⟩ := hsur n
  have a1 := hfac (e₂ hs • y) (fun i => by
    show prP s ((e₂ hs • y.1) i) = 0
    rw [map_smul_vec, prP_e₂, zero_mul])
  have a2 : ∀ z : locLat v (dualLb L), f₂ (e₁ hs • z) = 0 := fun z => hk2 _ (fun i => by
    show prPbar s ((e₁ hs • z.1) i) = 0
    rw [map_smul_vec, prPbar_e₁, zero_mul])
  have e : e₁ hs • y + e₂ hs • y = y := Subtype.ext (e₁_add_e₂ hs y.1)
  refine ⟨e₁ hs • x + e₂ hs • y, Prod.ext ?_ ?_⟩
  · exact ((L.fT v hv).map_add _ _).trans ((congrArg (_ + ·) a1).trans ((add_zero _).trans (h1 x)))
  · exact (f₂.map_add _ _).trans ((congrArg (· + _) ((a2 x).trans (a2 y).symm)).trans
      ((f₂.map_add _ _).symm.trans (congrArg f₂ e)))

omit [StarRing E] in

theorem mem_of_nsmul_mem {k T : ℕ} {v : HeightOneSpectrum (𝓞 F)} (hv : (T : 𝓞 F) ∉ v.asIdeal)
    (Λ : Submodule (intV E v) (Fin k → E ⊗[F] v.adicCompletion F)) {y} (hy : T • y ∈ Λ) : y ∈ Λ := by
  have h1 : Valued.v (T : v.adicCompletion F) = 1 := by
    have h2 := (valued_algebraMap_lt_one_iff (v := v) (T : 𝓞 F)).not.2 hv
    have h3 : (T : v.adicCompletion F) ∈ v.adicCompletionIntegers F := natCast_mem _ T
    simp only [map_natCast, not_lt] at h2
    exact le_antisymm h3 (by simpa using h2)
  have h0 : (T : v.adicCompletion F) ≠ 0 := fun h => by simp [h] at h1
  have hu : (1 : E) ⊗ₜ[F] ((T : v.adicCompletion F)⁻¹) ∈ intV E v :=
    Subring.subset_closure (Or.inr ⟨⟨_, show Valued.v (T : v.adicCompletion F)⁻¹ ≤ 1 by
      rw [map_inv₀, h1, inv_one]⟩, rfl⟩)
  have := Λ.smul_mem ⟨_, hu⟩ hy
  convert this using 1
  funext i
  show y i = ((1 : E) ⊗ₜ[F] ((T : v.adicCompletion F)⁻¹)) * (T • y i)
  rw [nsmul_eq_mul, ← mul_assoc,
    show ((T : ℕ) : E ⊗[F] v.adicCompletion F) = (1 : E) ⊗ₜ[F] (T : v.adicCompletion F) from
      (map_natCast (Algebra.TensorProduct.includeRight (R := F) (A := E)) T).symm,
    Algebra.TensorProduct.tmul_mul_tmul, inv_mul_cancel₀ h0, one_mul, ← Algebra.TensorProduct.one_def, one_mul]

def overLat (L : ColLevel R F E sp gp C A clsLat)
    (e : ∀ v : HeightOneSpectrum (𝓞 F), (A.T : 𝓞 F) ∈ v.asIdeal → intV E v) :
    Submodule (𝓞 E) (Fin R.k → E) where
  carrier := {x | x ∈ dualLb L ∧ ∀ v hv, e v hv • loc v x ∈ locLat v L.Lb}
  zero_mem' := ⟨zero_mem _, fun v hv => by rw [loc_zero, smul_zero]; exact zero_mem _⟩
  add_mem' := fun {x y} hx hy => ⟨add_mem hx.1 hy.1, fun v hv => by
    rw [loc_add, smul_add]; exact add_mem (hx.2 v hv) (hy.2 v hv)⟩
  smul_mem' := fun a x hx => ⟨Submodule.smul_mem _ _ hx.1, fun v hv => by
    rw [loc_smul, smul_comm]; exact Submodule.smul_mem _ _ (hx.2 v hv)⟩

theorem le_overLat (L : ColLevel R F E sp gp C A clsLat) (e) : L.Lb ≤ overLat L e :=
  fun _ hx => ⟨le_dualLb L hx, fun v _ => Submodule.smul_mem _ _ (loc_mem v hx)⟩

theorem overLat_le (L : ColLevel R F E sp gp C A clsLat) (e) : overLat L e ≤ dualLb L :=
  fun _ hx => hx.1

theorem mem_locLat_overLat (L : ColLevel R F E sp gp C A clsLat) (e)
    (v : HeightOneSpectrum (𝓞 F)) (hv : (A.T : 𝓞 F) ∈ v.asIdeal) (y) :
    y ∈ locLat v (overLat L e) ↔ y ∈ locLat v (dualLb L) ∧ e v hv • y ∈ locLat v L.Lb := by
  constructor
  · intro hy
    refine ⟨locLat_mono v (overLat_le L e) hy, ?_⟩
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x, hx, rfl⟩ := hy
      exact hx.2 v hv
    | zero => rw [smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx
  · rintro ⟨h1, h2⟩
    obtain ⟨x, hx, h3, h4⟩ := approx_one (finite_dualLb L) A.T_prime.ne_zero (nsmul_mem L) v y h1
    have hxN : x ∈ overLat L e := ⟨hx, fun w hw => by
      by_cases hwv : w = v
      · subst hwv
        have := sub_mem h2 (Submodule.smul_mem _ (e w hv) h3)
        rwa [← smul_sub, sub_sub_cancel] at this
      · exact Submodule.smul_mem _ _ (h4 w hwv)⟩
    have := add_mem (locLat_mono v (le_overLat L e) h3) (loc_mem v hxN)
    rwa [sub_add_cancel] at this

theorem locLat_dual_le (L : ColLevel R F E sp gp C A clsLat) (v : HeightOneSpectrum (𝓞 F))
    (hv : (A.T : 𝓞 F) ∉ v.asIdeal) : locLat v (dualLb L) ≤ locLat v L.Lb :=
  fun y hy => mem_of_nsmul_mem hv _ (nsmul_mem_locLat v (nsmul_mem L) y hy)

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in

theorem exists_overLattice (L : ColLevel R F E sp gp C A clsLat)
    (hpl : Nat.card {v : HeightOneSpectrum (𝓞 F) // (A.T : 𝓞 F) ∈ v.asIdeal} = R.f) :
    ∃ N : Submodule (𝓞 E) (Fin R.k → E), IsOverLattice L N ∧
      (∀ (v : HeightOneSpectrum (𝓞 F)) (h : (A.T : 𝓞 F) ∈ v.asIdeal), ∃ φ, LocalAtT L N v h φ) ∧
      (∀ v, L.Uloc v ≤ levelVL sp.cm.sig sp.gram0 v N) ∧
      L.U ≤ levelAfL sp.cm.sig sp.gram0 N := by
  choose s hs hfac hε hiso hcard f₂ hsur hk hk2 using exists_local L
  have hcount := mem_of_count (finite_dualLb L) A.T_prime.ne_zero
    (show R.f ≠ 0 by unfold Ranks.f Ranks.n; positivity) (nsmul_mem L) L.Lb_index hpl
    (fun v h => L.fM v h × (intV E v ⧸ primeOf (prPbar (s v h))))
    (fun v h => by rw [Nat.card_prod, L.fM_card, hcard])
    (fun v h => ((L.fT v h).prod (f₂ v h)).toAddMonoidHom) hsur
    (fun v h x hx => Prod.ext (L.fT_L v h x hx) (hk v h x hx))
  let N := overLat L (fun v hv => e₂ (hs v hv))
  have hN := mem_locLat_overLat L (fun v hv => e₂ (hs v hv))
  have hLN : L.Lb ≤ N := le_overLat L _
  have hNL : N ≤ dualLb L := overLat_le L _
  have hfin : Module.Finite (𝓞 E) N := by
    haveI := finite_dualLb L
    exact Module.Finite.of_injective (Submodule.inclusion hNL) (Submodule.inclusion_injective hNL)
  have hspan : Submodule.span E (N : Set (Fin R.k → E)) = ⊤ :=
    top_le_iff.1 (L.Lb_span ▸ Submodule.span_mono hLN)
  have hoff : ∀ v : HeightOneSpectrum (𝓞 F), (A.T : 𝓞 F) ∉ v.asIdeal → locLat v N = locLat v L.Lb :=
    fun v hv => le_antisymm ((locLat_mono v hNL).trans (locLat_dual_le L v hv)) (locLat_mono v hLN)
  obtain ⟨hAd, -, hint⟩ := GlobalTheory.T.adelicLatticeCompletion_local_global F E R.k N hfin
  have hloc : ∀ (v : HeightOneSpectrum (𝓞 F)) (h : (A.T : 𝓞 F) ∈ v.asIdeal), LocalAtT L N v h (s v h) := by
    intro v hv
    obtain ⟨ε, hε⟩ := hε v hv
    obtain ⟨i₁⟩ := hiso v hv
    refine localAtT L N v hv (hs v hv) (hfac v hv) ε hε ?_ (locLat_mono v (le_dualLb L)) ?_ (hN v hv)
    · have hker : (locLat v L.Lb).submoduleOf (locLat v (dualLb L)) =
          LinearMap.ker ((L.fT v hv).prod (f₂ v hv)) := by
        ext x
        exact ⟨fun hx => Prod.ext (L.fT_L v hv x hx) (hk v hv x hx), fun hx => hcount v hv x hx⟩
      exact ⟨(Submodule.quotEquivOfEq _ _ hker).trans
        ((LinearMap.quotKerEquivOfSurjective _ (hsur v hv)).trans (i₁.prodCongr (LinearEquiv.refl _ _)))⟩
    · intro x hx
      refine hcount v hv (e₁ (hs v hv) • x) (Prod.ext ?_ (hk2 v hv _ fun i => ?_))
      · exact ((L.fT v hv).map_smul _ _).trans ((congrArg (e₁ (hs v hv) • ·) hx).trans (smul_zero _))
      · show prPbar (s v hv) ((e₁ (hs v hv) • x.1) i) = 0
        rw [map_smul_vec, prPbar_e₁, zero_mul]
  have hU : ∀ v, L.Uloc v ≤ levelVL sp.cm.sig sp.gram0 v N := by
    intro v
    by_cases hv : (A.T : 𝓞 F) ∈ v.asIdeal
    · obtain ⟨-, -, -, -, -, -, -, -, f, ε, -, -, -, -, -, h⟩ := hloc v hv
      exact fun g hg => ((h g).1 hg).1
    · have : levelVL sp.cm.sig sp.gram0 v N = levelVL sp.cm.sig sp.gram0 v L.Lb :=
        congrArg (level _ _) (hoff v hv)
      rw [this]; exact L.Uloc_lev v
  refine ⟨N, ⟨hfin, hspan, ?_, hLN, hNL, hoff⟩, fun v h => ⟨_, hloc v h⟩, hU, ?_⟩
  · ext y
    constructor
    · intro hy
      refine ⟨Submodule.subset_span fun x hx => hy x (hLN hx), fun v hv => ?_⟩
      have key : ∀ z ∈ locLat v N, hform (sigR sp.cm.sig (v.adicCompletion F))
          (sp.gram0.map (inclE (F := F) (v.adicCompletion F))) z (loc v y) ∈ intV E v := by
        intro z hz
        induction hz using Submodule.span_induction with
        | mem z hz =>
          obtain ⟨x, hx, rfl⟩ := hz
          obtain ⟨a, ha⟩ := hy x hx
          have := hform_loc (σ := sp.cm.sig) (v := v) sp.gram0 x y
          rw [← ha] at this
          exact this ▸ tmul_mem_intV a
        | zero => simp [hform]
        | add x z _ _ hx hz => rw [hform_add_left]; exact add_mem hx hz
        | smul a x _ hx =>
          have : hform (sigR sp.cm.sig (v.adicCompletion F))
              (sp.gram0.map (inclE (F := F) (v.adicCompletion F))) (a • x) (loc v y) =
              sigR sp.cm.sig (v.adicCompletion F) a * hform (sigR sp.cm.sig (v.adicCompletion F))
              (sp.gram0.map (inclE (F := F) (v.adicCompletion F))) x (loc v y) := by
            simp only [hform, Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
            rw [show (a • x) i = (a : E ⊗[F] v.adicCompletion F) * x i from rfl, map_mul]
            ring
          rw [this]
          exact mul_mem (sigR_mem_intV _ v _ a.2) hx
      refine ((dual_loc L v).2.1 _).2 fun z hz => ?_
      have h1 := key (e₁ (hs v hv) • z) ((hN v hv _).2 ⟨Submodule.smul_mem _ _ hz, by
        rw [e₂_e₁]; exact zero_mem _⟩)
      have h2 := hform_smul_left (sigR sp.cm.sig (v.adicCompletion F))
        (sp.gram0.map (inclE (F := F) (v.adicCompletion F))) (e₁ (hs v hv)) z (loc v y)
      rw [sig_e₁] at h2
      exact h2 ▸ h1
    · intro hy x hx
      refine hint _ fun v => ?_
      rw [← hform_loc]
      by_cases hv : (A.T : 𝓞 F) ∈ v.asIdeal
      · rw [← e₁_add_e₂ (hs v hv) (loc v x), hform_add_left]
        refine add_mem ?_ (((dual_loc L v).1 _).1 (loc_mem v hy.1) _ (hx.2 v hv))
        have h2 := hform_smul_left (sigR sp.cm.sig (v.adicCompletion F))
          (sp.gram0.map (inclE (F := F) (v.adicCompletion F))) (e₁ (hs v hv)) (loc v x) (loc v y)
        rw [sig_e₁] at h2
        exact h2.symm ▸ ((dual_loc L v).2.1 _).1 (hy.2 v hv) _ (loc_mem v hx.1)
      · exact ((dual_loc L v).1 _).1 (loc_mem v hy.1) _ (locLat_dual_le L v hv (loc_mem v hx.1))
  · intro g hg
    obtain ⟨h1, h2⟩ := (L.U_eq g).1 hg
    refine ⟨h1, fun u => ?_⟩
    rw [hAd, hAd]
    refine forall_congr' fun v => ((hU v (h2 v)).2 _).trans ?_
    exact Iff.of_eq (congrArg (· ∈ locLat v N)
      (funext fun i => (RingHom.map_mulVec (prV (E := E) v) g.val u i).symm))

end Level

theorem T_ne_g (D : D7) (u : D.what₂.Word) (i : Fin 2) : (D.mem u).A.T ≠ D.host.g i := by
  intro h
  obtain ⟨π, -, hπ, hmod⟩ := D.T_norm u
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hmod
  have hd : D.host.g i ∣ D.host.QS * D.host.q * D.host.d * (D.host.g 0 * D.host.g 1) ^ 2 := by
    refine Dvd.dvd.mul_left (Dvd.dvd.pow ?_ two_ne_zero) _
    fin_cases i
    · exact Dvd.intro _ rfl
    · exact Dvd.intro_left _ rfl
  obtain ⟨m, hm⟩ := hd
  let c := RingOfIntegers.mapRingHom (D.host.conj : D.host.E →+* D.host.E)
  have h1 : π = 1 + (D.host.g i : 𝓞 D.host.E) * (a * m) := by
    rw [hm] at ha; push_cast at ha; linear_combination -ha
  have h2 : c π = 1 + (D.host.g i : 𝓞 D.host.E) * c (a * m) := by
    conv_lhs => rw [h1]
    rw [map_add, map_one, map_mul c (D.host.g i : 𝓞 D.host.E), map_natCast]
  have h3 : π * c π = (D.host.g i : 𝓞 D.host.E) := by
    apply RingOfIntegers.ext
    rw [← h]
    exact hπ.trans (map_natCast (algebraMap (𝓞 D.host.E) D.host.E) _).symm
  have h4 : IsUnit (D.host.g i : 𝓞 D.host.E) := by
    refine isUnit_of_dvd_one ⟨1 - a * m - c (a * m) - (D.host.g i : 𝓞 D.host.E) * (a * m) * c (a * m), ?_⟩
    rw [h2] at h3
    rw [h1] at h3
    linear_combination h3
  have h5 := h4.map (Algebra.norm ℤ)
  rw [show (D.host.g i : 𝓞 D.host.E) = algebraMap ℤ _ (D.host.g i : ℤ) by simp, Algebra.norm_algebraMap,
    isUnit_pow_iff Module.finrank_pos.ne', Int.isUnit_iff_natAbs_eq, Int.natAbs_natCast] at h5
  exact (D.host.g_prime i).ne_one h5

theorem overLattice : GlobalTheory.IndefiniteRowSideFullHecke.OverPlaceIntegralForm.OverLattice :=
  overLattice_iff_selfDualOverBase.2 fun D Lv u =>
    letI := D.host.cmStar
    fun hT => ⟨T_ne_g D u, exists_overLattice (Lv u) hT.1⟩

end GlobalTheory.OverLat

end
