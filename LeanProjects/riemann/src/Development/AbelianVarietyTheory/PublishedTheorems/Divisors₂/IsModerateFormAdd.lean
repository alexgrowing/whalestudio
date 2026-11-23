import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EisensteinIsotropicLine
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsInertPlOfInertOff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPreHasLetters
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAHEqOfMemRatPts

noncomputable section

open NumberField MeasureTheory Matrix Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisLine
open Formalism.UG (cT)
open GlobalTheory.Doubling (absE)
open scoped TensorProduct NNReal

namespace GlobalTheory.EisLineModel

open Formalism.BasicNotions in
attribute [local instance] Formalism.BasicNotions.Host.cmStar in

theorem data_inhabited : ∃ (F E : Type) (_ : Field F) (_ : NumberField F) (_ : Field E) (_ : NumberField E) (_ : Algebra F E)
    (σ : E →ₐ[F] E) (J : Matrix (Fin 2) (Fin 2) E) (X Y : Matrix (Fin 2) (Fin (0 + 1)) E) (L : Submodule (𝓞 E) (Fin 2 → E))
    (a : GL (Fin 2) (AF F ⊗[F] E)), IsCMExt F E σ ∧ Algebra.Unramified (𝓞 F) (𝓞 E) ∧ IsHermND σ J ∧
      IsWittFrame σ J X Y ∧ IsAdapted σ J X Y L a := by
  obtain ⟨D⟩ := GlobalTheory.Mem.nonempty_record
  obtain ⟨L, a, h⟩ := exists_isAdapted_plane D.sp.cm.sig
  refine ⟨_, _, _, _, _, _, _, D.sp.cm.sig, _, _, _, L, a, isCMExt_host D, GlobalTheory.InertOfConj.unram D, ⟨fun i j => ?_, ?_⟩,
    isWittFrame_plane, h⟩
  · fin_cases i <;> fin_cases j <;> simp
  · simp [det_fin_two]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem pos {x : Matrix (Fin n) (Fin 1) E} {K : Subgroup (GAd σ J)} {h : GAd σ J → ℝ}
    (h1 : ∀ g, ∃ p, ∃ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J p).1 * adMat F x = l.1 • adMat F x ∧ ∃ k ∈ K, g = p * k)
    (h2 : ∀ p, ∀ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J p).1 * adMat F x = l.1 • adMat F x → ∀ k ∈ K, h (p * k) = absE F E l) :
    (∀ g, 0 < h g) ∧ h 1 = 1 := by
  refine ⟨fun g => ?_, by simpa using h2 1 1 (by simp) 1 (one_mem _)⟩
  obtain ⟨p, l, hp, k, hk, rfl⟩ := h1 g
  rw [h2 p l hp k hk]
  exact_mod_cast GlobalTheory.Doubling.hom_pos _ _

theorem exists_h {x y : Matrix (Fin n) (Fin 1) E} (hxy : cT (σ : E →+* E) y * J * x = 1) {K : Subgroup (GAd σ J)}
    (hK : IsCompact (K : Set (GAd σ J))) : ∃ h : GAd σ J → ℝ, ∀ p, ∀ l : (AF F ⊗[F] E)ˣ,
      (matHom _ σ J p).1 * adMat F x = l.1 • adMat F x → ∀ k ∈ K, h (p * k) = absE F E l := by
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  haveI : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI := GlobalTheory.Doubling.t2Space_tensorProduct_finiteExtension (F := F) (E := E) (R := AF F)
  let φ : GAd σ J → AF F ⊗[F] E := fun p => (adMat F (cT (σ : E →+* E) y * J) * ((matHom _ σ J p).1 * adMat F x)) 0 0
  have hφ : ∀ p (l : AF F ⊗[F] E), (matHom _ σ J p).1 * adMat F x = l • adMat F x → φ p = l := fun p l e => by
    simp only [φ, e, Matrix.mul_smul, adMat, ← Matrix.map_mul, hxy]
    simp
  have hm : Continuous fun p : GAd σ J => (matHom _ σ J p).1 := Units.continuous_val.comp continuous_subtype_val
  have cφ : Continuous φ := (continuous_const.matrix_mul (hm.matrix_mul continuous_const)).matrix_elem 0 0
  let Q : GAd σ J → Prop := fun p => (matHom _ σ J p).1 * adMat F x = φ p • adMat F x
  have hmul : ∀ p q, Q p → Q q → (matHom _ σ J (p * q)).1 * adMat F x = (φ p * φ q) • adMat F x := fun p q hp hq => by
    rw [map_mul, Units.val_mul, Matrix.mul_assoc, hq, Matrix.mul_smul, hp, smul_smul, mul_comm]
  have hQ : ∀ p q, Q p → Q q → Q (p * q) := fun p q hp hq => by
    have := hmul p q hp hq
    rw [← hφ _ _ this] at this; exact this
  have h1 : φ 1 = 1 := hφ 1 1 (by simp)
  let P : Subgroup (GAd σ J) :=
    { carrier := {p | Q p ∧ Q p⁻¹}
      one_mem' := by simp [Q, h1]
      mul_mem' := fun {p q} hp hq => ⟨hQ _ _ hp.1 hq.1, by rw [_root_.mul_inv_rev]; exact hQ _ _ hq.2 hp.2⟩
      inv_mem' := fun {p} hp => ⟨hp.2, by rw [inv_inv]; exact hp.1⟩ }
  have hi : ∀ p : P, φ p * φ (p : GAd σ J)⁻¹ = 1 := fun p => by
    rw [← hφ _ _ (hmul _ _ p.2.1 p.2.2), mul_inv_cancel, h1]
  let u : P →* (AF F ⊗[F] E)ˣ :=
    { toFun := fun p => ⟨φ p, φ (p : GAd σ J)⁻¹, hi p, by rw [mul_comm]; exact hi p⟩
      map_one' := Units.ext h1
      map_mul' := fun p q => Units.ext (hφ _ _ (hmul _ _ p.2.1 q.2.1)) }
  have cu : Continuous u := Units.continuous_iff.2
    ⟨cφ.comp continuous_subtype_val, cφ.comp continuous_subtype_val.inv⟩
  have cQ : IsClosed {p | Q p} := isClosed_eq (hm.matrix_mul continuous_const) (cφ.smul continuous_const)
  have cP : IsClosed (P : Set (GAd σ J)) := cQ.inter (cQ.preimage continuous_inv)
  have ht := GlobalTheory.Doubling.triv_of_isCompact (δ := (absE F E).comp u) cP (GlobalTheory.Doubling.continuous_absE.comp cu) hK
  refine ⟨fun g => GlobalTheory.Doubling.iwAbs ((absE F E).comp u) K g, fun p l hp k hk => ?_⟩
  have hp' : (matHom _ σ J p⁻¹).1 * adMat F x = l⁻¹.1 • adMat F x := by
    have := congrArg (fun z => l⁻¹.1 • ((matHom _ σ J p⁻¹).1 * z)) hp
    simp only [← Matrix.mul_assoc, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mul,
      Matrix.mul_smul, smul_smul] at this
    simpa using this.symm
  have hP : p ∈ P := ⟨by have := hp; rw [← hφ _ _ hp] at this; exact this, by have := hp'; rw [← hφ _ _ hp'] at this; exact this⟩
  have := GlobalTheory.Doubling.iwAbs_mul_of_triv ht ⟨p, hP⟩ hk
  have e : u ⟨p, hP⟩ = l := Units.ext (hφ _ _ hp)
  simp only [MonoidHom.comp_apply, e] at this
  exact congrArg NNReal.toReal this

theorem exists_h_levelAll (hc : IsCMExt F E σ) {x y : Matrix (Fin n) (Fin 1) E} (hxy : cT (σ : E →+* E) y * J * x = 1)
    (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L] (a : GL (Fin n) (AF F ⊗[F] E)) :
    ∃ h : GAd σ J → ℝ, ∀ p, ∀ l : (AF F ⊗[F] E)ˣ,
      (matHom _ σ J p).1 * adMat F x = l.1 • adMat F x → ∀ k ∈ levelAll σ J L a, h (p * k) = absE F E l :=
  exists_h hxy (GlobalTheory.Doubling.isCompact_levelAll hc _ _ _)

theorem isModerateForm_add {μ ν : (GAd σ J → ℂ) →ₗ[ℂ] ℂ} (hμ : IsModerateForm σ J μ) (hν : IsModerateForm σ J ν) :
    IsModerateForm σ J (μ + ν) := fun N => by
  obtain ⟨S, C, h1, h2⟩ := hμ N
  obtain ⟨S', C', h1', h2'⟩ := hν N
  refine ⟨S ++ S', C + C', fun l hl => (List.mem_append.1 hl).elim (h1 l) (h1' l), fun f hf hB hS => ?_⟩
  exact (norm_add_le _ _).trans (add_le_add (h2 f hf hB fun l hl => hS l (List.mem_append_left _ hl))
    (h2' f hf hB fun l hl => hS l (List.mem_append_right _ hl)))

theorem eisensteinIsotropicLine_of_isWittFrame (hP : GlobalTheory.Published.EisensteinIsotropicLine) (hc : IsCMExt F E σ) (hu : Algebra.Unramified (𝓞 F) (𝓞 E))
    (hJ : IsHermND σ J) {r : ℕ} {X Y : Matrix (Fin n) (Fin (r + 1)) E} (hW : IsWittFrame σ J X Y)
    {L : Submodule (𝓞 E) (Fin n → E)} {a : GL (Fin n) (AF F ⊗[F] E)} (hA : IsAdapted σ J X Y L a) {h : GAd σ J → ℝ}
    (h1 : ∀ g, ∃ p, ∃ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J p).1 * adMat F (X.submatrix id fun _ : Fin 1 => 0) =
      l.1 • adMat F (X.submatrix id fun _ : Fin 1 => 0) ∧ ∃ k ∈ levelAll σ J L a, g = p * k)
    (h2 : ∀ p, ∀ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J p).1 * adMat F (X.submatrix id fun _ : Fin 1 => 0) =
      l.1 • adMat F (X.submatrix id fun _ : Fin 1 => 0) → ∀ k ∈ levelAll σ J L a, h (p * k) = absE F E l) :
    ∃ (Eis : ℂ → GAd σ J → ℂ) (c : ℂ → ℂ), MeromorphicOn c Set.univ ∧ (∀ s₀ : ℂ, ∀ᶠ s in 𝓝[≠] s₀, c s ≠ 0) ∧
      ∀ g s₀, MeromorphicAt (fun s => Eis s g) s₀ := by
  obtain ⟨Eis, c, -, -, h3, h4, h5⟩ := hP F E σ hc hu n J hJ r X Y hW _ _ rfl rfl L a hA h h1 h2
  refine ⟨Eis, c, h3, fun s₀ => (h5 s₀).mono fun s hs => left_ne_zero_of_mul_eq_one hs.1, fun g s₀ => ?_⟩
  obtain ⟨k, U, H, hU, e, -, hd⟩ := h4 s₀
  have a1 : AnalyticAt ℂ (fun s => H s g) s₀ := (hd _ (isModerateForm_proj σ J g)).analyticAt hU
  have a2 : MeromorphicAt (fun s => H s g / (s - s₀) ^ k) s₀ :=
    a1.meromorphicAt.fun_div (by fun_prop)
  refine a2.congr ?_
  filter_upwards [mem_nhdsWithin_of_mem_nhds hU, self_mem_nhdsWithin] with s hs hs'
  rw [e s hs hs' g, mul_div_cancel_left₀ _ (pow_ne_zero _ (sub_ne_zero.2 hs'))]

end GlobalTheory.EisLineModel

end
