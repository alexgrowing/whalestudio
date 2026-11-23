import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraMapEqMk
open scoped TensorProduct

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PicTorsionForm

open CommRing Module

variable {B : Type} [CommRing B]

theorem exists_local_generator (M : Type) [AddCommGroup M] [Module B M] [Module.Invertible B M]
    (p : Ideal B) [p.IsPrime] : ∃ e : M, ∀ x : M, ∃ w a : B, w ∉ p ∧ w • x = a • e := by
  have ⟨f⟩ := Invertible.free_iff_linearEquiv.mp
    (inferInstance : Free (Localization.AtPrime p) (LocalizedModule p.primeCompl M))
  obtain ⟨e, s, he⟩ : ∃ (e : M) (s : p.primeCompl), LocalizedModule.mk e s = f.symm 1 :=
    LocalizedModule.induction_on (β := fun y => ∃ (e : M) (s : p.primeCompl), LocalizedModule.mk e s = y)
      (fun e s => ⟨e, s, rfl⟩) (f.symm 1)
  refine ⟨e, fun x => ?_⟩
  obtain ⟨a, t, ht⟩ : ∃ (a : B) (t : p.primeCompl), Localization.mk a t = f (LocalizedModule.mk x 1) :=
    Localization.induction_on (f (LocalizedModule.mk x 1)) fun z => ⟨z.1, z.2, rfl⟩
  have key : LocalizedModule.mk x (1 : p.primeCompl) = LocalizedModule.mk (a • e) (t * s) := by
    rw [← f.symm_apply_apply (LocalizedModule.mk x 1), ← ht, ← mul_one (Localization.mk a t),
      ← smul_eq_mul, map_smul, ← he, LocalizedModule.mk_smul_mk]
  obtain ⟨u, hu⟩ := (LocalizedModule.mk_eq).mp key
  refine ⟨(u : B) * ((t : B) * s), u * a, ?_, ?_⟩
  · exact p.primeCompl.mul_mem u.2 (p.primeCompl.mul_mem t.2 s.2)
  · simpa only [Submonoid.smul_def, Submonoid.coe_mul, OneMemClass.coe_one, one_smul, smul_smul] using hu

theorem tensorPow_equiv (c : Pic B) (n : ℕ) :
    Nonempty (Pic.AsModule (c ^ n) ≃ₗ[B] ⨂[B] _ : Fin n, Pic.AsModule c) := by
  induction n with
  | zero =>
    have ⟨e⟩ := Pic.ext_iff.mp (pow_zero c)
    have ⟨g⟩ := Pic.mk_eq_one_iff.mp (Pic.mk_eq_self (M := (1 : Pic B)))
    exact ⟨e ≪≫ₗ g ≪≫ₗ (PiTensorProduct.isEmptyEquiv (Fin 0)).symm⟩
  | succ n ih =>
    obtain ⟨ih⟩ := ih
    have ⟨e1⟩ := Pic.ext_iff.mp (pow_succ c n)
    have ⟨e2⟩ := Pic.ext_iff.mp (Pic.mul_eq_tensor (c ^ n) c)
    exact ⟨e1 ≪≫ₗ e2 ≪≫ₗ Pic.mk.linearEquiv B _ ≪≫ₗ TensorProduct.congr ih
      (PiTensorProduct.subsingletonEquiv (R := B) (s := fun _ : Fin 1 => Pic.AsModule c) 0).symm ≪≫ₗ
      PiTensorProduct.tmulEquiv B (Pic.AsModule c) ≪≫ₗ PiTensorProduct.reindex B _ finSumFinEquiv⟩

theorem exists_form : ∀ (B : Type) [CommRing B] (q : ℕ) (c : CommRing.Pic B), c ^ q = 1 →
    ∃ φ : MultilinearMap B (fun _ : Fin q => CommRing.Pic.AsModule c) B,
      ∀ p : Ideal B, p.IsPrime → ∃ e : CommRing.Pic.AsModule c, φ (fun _ => e) ∉ p := by
  intro B _ q c hc
  obtain ⟨T⟩ := tensorPow_equiv c q
  have ⟨e1⟩ := Pic.ext_iff.mp hc
  have ⟨g⟩ := Pic.mk_eq_one_iff.mp (Pic.mk_eq_self (M := (1 : Pic B)))
  let ψ : (⨂[B] _ : Fin q, Pic.AsModule c) ≃ₗ[B] B := T.symm ≪≫ₗ e1 ≪≫ₗ g
  refine ⟨ψ.toLinearMap.compMultilinearMap (PiTensorProduct.tprod B), fun p hp => ?_⟩
  obtain ⟨x, hx⟩ : ∃ x : Fin q → Pic.AsModule c, ψ (PiTensorProduct.tprod B x) ∉ p := by
    by_contra! h
    have hall : ∀ t, ψ t ∈ p := fun t => by
      induction t using PiTensorProduct.induction_on with
      | smul_tprod r x => rw [map_smul, smul_eq_mul]; exact p.mul_mem_left r (h x)
      | add a b ha hb => rw [map_add]; exact p.add_mem ha hb
    exact hp.ne_top ((Ideal.eq_top_iff_one p).mpr (by simpa using hall (ψ.symm 1)))
  obtain ⟨e, he⟩ := exists_local_generator (Pic.AsModule c) p
  choose w a hw hwa using fun i => he (x i)
  refine ⟨e, fun hmem => ?_⟩
  have hmem' : ψ (PiTensorProduct.tprod B fun _ => e) ∈ p := hmem
  have h1 : ψ (PiTensorProduct.tprod B (fun i => w i • x i)) =
      (∏ i, w i) * ψ (PiTensorProduct.tprod B x) := by
    rw [MultilinearMap.map_smul_univ, map_smul, smul_eq_mul]
  have h2 : ψ (PiTensorProduct.tprod B (fun i => w i • x i)) =
      (∏ i, a i) * ψ (PiTensorProduct.tprod B (fun _ => e)) := by
    simp_rw [hwa]; rw [MultilinearMap.map_smul_univ, map_smul, smul_eq_mul]
  have hin : (∏ i, w i) * ψ (PiTensorProduct.tprod B x) ∈ p := by
    rw [← h1, h2]; exact p.mul_mem_left _ hmem'
  rcases hp.mem_or_mem hin with h | h
  · exact (p.primeCompl.prod_mem fun i _ => hw i) h
  · exact hx h

end GlobalTheory.PicTorsionForm
