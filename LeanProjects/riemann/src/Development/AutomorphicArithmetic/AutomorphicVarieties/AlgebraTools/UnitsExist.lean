import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.InvAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.EqLagIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.SqrtOneAdd

open Polynomial Matrix IsLocalRing TensorProduct UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.units_exist :
    ∀ {B E : Type} [CommRing B] [Ring E] [Algebra B E] (T : TrInv B E) {F : Type} [CommRing F] [Algebra B F] [HenselianRing B (RingHom.ker (algebraMap B F))] {ι : Type} [Fintype ι] [DecidableEq ι] (o : ι → ι) (r : E →ₐ[B] Matrix ι ι F) (ep : ι → E), IsUnit (2 : B) → (∀ i, o (o i) = o i) → (∀ x, r (T.st x) = (r x)ᵀ) → (∀ i, ∃ y, r y = single (o i) i 1) → CompleteOrthogonalIdempotents ep → (∀ i, T.st (ep i) = ep i) → (∀ i, r (ep i) = single i i 1) → (∀ i, T.tr (ep i) = 1) → (∀ i y, ∃ b : B, ep i * y * ep i = b • ep i) → ∃ U : T.Units ι o, U.ep = ep ∧ ∀ i, r (U.x i) = single (o i) i 1 := by
  intro B E _ _ _ T F _ _ _ ι _ _ o r ep h2 ho hr hy hco hst hre htr hrank
  have idem : ∀ i, ep i * ep i = ep i := fun i => (hco.idem i).eq
  have idem' : ∀ i x, ep i * (ep i * x) = ep i * x := fun i x => by rw [← mul_assoc, idem]
  choose y hy using hy
  obtain ⟨z, hz⟩ : ∃ z : ι → E, ∀ i, z i = ep (o i) * y i * ep i := ⟨_, fun i => rfl⟩
  have hz_mem : ∀ i, ep (o i) * z i * ep i = z i := by
    intro i
    rw [hz]
    simp only [mul_assoc, idem, idem']
  have hstz : ∀ i, T.st (z i) = ep i * (T.st (y i) * ep (o i)) := by
    intro i
    rw [hz, T.st_mul, T.st_mul, hst, hst]
  have hrz : ∀ i, r (z i) = single (o i) i 1 := by
    intro i
    rw [hz, map_mul, map_mul, hre, hre, hy]
    simp only [Matrix.single_mul_single_same, mul_one]
  choose b hb using fun i => hrank i (T.st (y i) * ep (o i) * y i)
  choose b' hb2 using fun i => hrank (o i) (y i * ep i * T.st (y i))
  have hb' : ∀ i, T.st (z i) * z i = b i • ep i := by
    intro i
    rw [hstz, hz, ← hb i]
    simp only [mul_assoc, idem, idem']
  have hzst : ∀ i, z i * T.st (z i) = b' i • ep (o i) := by
    intro i
    rw [hstz, hz, ← hb2 i]
    simp only [mul_assoc, idem, idem']
  have hbb : ∀ i, b' i = b i := by
    intro i
    have h := congrArg T.tr (hzst i)
    rw [T.tr_comm, hb', map_smul, map_smul, htr, htr, smul_eq_mul, smul_eq_mul, mul_one, mul_one] at h
    exact h.symm
  have hbF : ∀ i, algebraMap B F (b i) = 1 := by
    intro i
    have h := congrArg r (hb' i)
    rw [map_mul, hr, hrz, map_smul, hre, Matrix.transpose_single, Matrix.single_mul_single_same,
      mul_one] at h
    have h' := congrArg (fun M : Matrix ι ι F => M i i) h
    simp only [Matrix.smul_apply, Matrix.single_apply_same, Algebra.smul_def, mul_one] at h'
    exact h'.symm
  have hb1 : ∀ i, b i - 1 ∈ RingHom.ker (algebraMap B F) := by
    intro i
    rw [RingHom.mem_ker, map_sub, hbF, map_one, sub_self]
  choose α hα hα1 using fun i => UpperTheory.V.AlgebraTools.sqrt_one_add (RingHom.ker (algebraMap B F)) (b i) h2 (hb1 i)
  have hαinvF : ∀ i, algebraMap B F (↑(α i)⁻¹ : B) = 1 := by
    intro i
    have h1 := hα1 i
    rw [RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at h1
    have h := congrArg (algebraMap B F) (Units.inv_mul (α i))
    rw [map_mul, map_one, h1, mul_one] at h
    exact h
  have hinv : ∀ i, (↑(α i)⁻¹ : B) * ↑(α i)⁻¹ * b i = 1 := by
    intro i
    rw [← hα, sq, mul_assoc, ← mul_assoc (↑(α i)⁻¹ : B) (↑(α i)) (↑(α i)), Units.inv_mul, one_mul,
      Units.inv_mul]
  refine ⟨⟨ep, fun i => if o i = i then ep i else (↑(α i)⁻¹ : B) • z i, ho, hco, hst, htr, hrank,
    ?_, ?_, ?_, ?_⟩, rfl, ?_⟩
  · intro i
    by_cases h : o i = i
    · rw [if_pos h, h, idem, idem]
    · rw [if_neg h, mul_smul_comm, smul_mul_assoc, hz_mem]
  · intro i
    rw [if_pos (ho i)]
  · intro i
    by_cases h : o i = i
    · rw [if_pos h, hst, idem, h]
    · rw [if_neg h, map_smul, smul_mul_assoc, mul_smul_comm, smul_smul, hzst, hbb, smul_smul, hinv,
        one_smul]
  · intro i
    by_cases h : o i = i
    · rw [if_pos h, hst, idem]
    · rw [if_neg h, map_smul, smul_mul_assoc, mul_smul_comm, smul_smul, hb', smul_smul, hinv, one_smul]
  · intro i
    dsimp only
    by_cases h : o i = i
    · rw [if_pos h, hre, h]
    · rw [if_neg h, map_smul, hrz, ← algebraMap_smul (A := F), hαinvF, one_smul]
