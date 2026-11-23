import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveResidueCompEtaleHenselianStatement
open IsLocalRing

namespace GlobalTheory.IndEtaleHensel

theorem algHom_ext_localization {R A P : Type} [CommRing R] [CommRing A] [CommRing P]
    [Algebra R A] [Algebra R P] (q : Ideal A) [q.IsPrime]
    (φ₁ φ₂ : Localization.AtPrime q →ₐ[R] P)
    (h : φ₁.comp (IsScalarTower.toAlgHom R A (Localization.AtPrime q)) =
      φ₂.comp (IsScalarTower.toAlgHom R A (Localization.AtPrime q))) : φ₁ = φ₂ := by
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext q.primeCompl
  exact RingHom.ext fun a => DFunLike.congr_fun h a

theorem bijective_of_algEquiv {R X Y T : Type} [CommRing R] [CommRing X] [CommRing Y] [CommRing T]
    [Algebra R X] [Algebra R Y] [Algebra R T] [IsLocalRing T] (e : X ≃ₐ[R] Y)
    (h : Function.Bijective
      (fun φ : X →ₐ[R] T => (IsScalarTower.toAlgHom R T (ResidueField T)).comp φ)) :
    Function.Bijective
      (fun φ : Y →ₐ[R] T => (IsScalarTower.toAlgHom R T (ResidueField T)).comp φ) := by
  constructor
  · intro φ₁ φ₂ hφ
    have hc : φ₁.comp (e : X →ₐ[R] Y) = φ₂.comp (e : X →ₐ[R] Y) := by
      apply h.1
      simp only at hφ ⊢
      rw [← AlgHom.comp_assoc, ← AlgHom.comp_assoc, hφ]
    ext y
    have := DFunLike.congr_fun hc (e.symm y)
    simpa using this
  · intro ψ
    obtain ⟨φ, hφ⟩ := h.2 (ψ.comp (e : X →ₐ[R] Y))
    refine ⟨φ.comp (e.symm : Y →ₐ[R] X), ?_⟩
    simp only at hφ ⊢
    rw [← AlgHom.comp_assoc, hφ]
    ext y; simp

theorem bijective_localization {R A T : Type} [CommRing R] [CommRing A] [CommRing T]
    [Algebra R A] [Algebra R T] [IsLocalRing T] (q : Ideal A) [q.IsPrime]
    (hA : Function.Bijective
      (fun φ : A →ₐ[R] T => (IsScalarTower.toAlgHom R T (ResidueField T)).comp φ)) :
    Function.Bijective (fun φ : Localization.AtPrime q →ₐ[R] T =>
      (IsScalarTower.toAlgHom R T (ResidueField T)).comp φ) := by
  set π := IsScalarTower.toAlgHom R T (ResidueField T)
  set ι := IsScalarTower.toAlgHom R A (Localization.AtPrime q)
  constructor
  · intro φ₁ φ₂ hφ
    apply algHom_ext_localization q
    apply hA.1
    simp only at hφ ⊢
    rw [← AlgHom.comp_assoc, ← AlgHom.comp_assoc, hφ]
  · intro ψ
    obtain ⟨φ, hφ⟩ := hA.2 (ψ.comp ι)
    simp only at hφ
    have hu : ∀ y : q.primeCompl, IsUnit (φ y) := by
      intro y
      have h1 : IsUnit (ψ (algebraMap A (Localization.AtPrime q) y)) :=
        (IsLocalization.map_units (Localization.AtPrime q) y).map ψ
      have h2 : π (φ y) = ψ (algebraMap A (Localization.AtPrime q) y) := DFunLike.congr_fun hφ (y : A)
      rw [← h2] at h1
      have h3 : π (φ y) = residue T (φ y) := by
        simp [π, IsScalarTower.toAlgHom_apply, ResidueField.algebraMap_eq]
      rw [h3] at h1
      exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mp h1.ne_zero
    refine ⟨IsLocalization.liftAlgHom (M := q.primeCompl) (S := Localization.AtPrime q) hu, ?_⟩
    apply algHom_ext_localization q
    ext a
    have := DFunLike.congr_fun hφ a
    simp only [AlgHom.comp_apply] at this ⊢
    rw [← this]
    congr 1
    simp [ι, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]

theorem bijective_residue_comp : ∀ (R S T : Type) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] [HenselianLocalRing T], (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra R S), Monotone Si ∧ (∀ s : S, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Si i)) → Function.Bijective (fun φ : S →ₐ[R] T => (IsScalarTower.toAlgHom R T (ResidueField T)).comp φ) := by
  intro R S T _ _ _ _ _ _ hS
  obtain ⟨ι, _, _, _, Si, hmono, hcov, hloc⟩ := hS
  have hbij : ∀ i, Function.Bijective (fun φ : Si i →ₐ[R] T =>
      (IsScalarTower.toAlgHom R T (ResidueField T)).comp φ) := by
    intro i
    obtain ⟨A, _, _, _, q, _, ⟨e⟩⟩ := hloc i
    exact bijective_of_algEquiv e (bijective_localization q (GlobalTheory.T.bijective_residue_comp_etale_henselian R A T))
  have dir : Directed (· ≤ ·) Si := hmono.directed_le
  have htop : (⊤ : Subalgebra R S) ≤ iSup Si := fun s _ => by
    obtain ⟨i, hi⟩ := hcov s
    exact le_iSup Si i hi
  constructor
  · intro φ₁ φ₂ h
    simp only at h
    ext s
    obtain ⟨i, hi⟩ := hcov s
    have hc : φ₁.comp (Si i).val = φ₂.comp (Si i).val := by
      apply (hbij i).1
      simp only
      rw [← AlgHom.comp_assoc, ← AlgHom.comp_assoc, h]
    exact DFunLike.congr_fun hc ⟨s, hi⟩
  · intro ψ
    choose f hf using fun i => (hbij i).2 (ψ.comp (Si i).val)
    simp only at hf
    have compat : ∀ i j (h : Si i ≤ Si j), f i = (f j).comp (Subalgebra.inclusion h) := by
      intro i j h
      apply (hbij i).1
      simp only
      rw [hf i, ← AlgHom.comp_assoc, hf j]
      ext x; rfl
    refine ⟨(Subalgebra.iSupLift Si dir f compat ⊤ htop).comp
      (Subalgebra.topEquiv.symm : S ≃ₐ[R] (⊤ : Subalgebra R S)).toAlgHom, ?_⟩
    ext s
    obtain ⟨i, hi⟩ := hcov s
    have h1 := DFunLike.congr_fun (hf i) ⟨s, hi⟩
    simp only [AlgHom.comp_apply] at h1 ⊢
    refine Eq.trans ?_ h1
    congr 1
    exact Subalgebra.iSupLift_of_mem (K := Si) (dir := dir) (f := f) (hf := compat)
      (T := ⊤) (hT := htop) ⟨s, trivial⟩ hi

end GlobalTheory.IndEtaleHensel
