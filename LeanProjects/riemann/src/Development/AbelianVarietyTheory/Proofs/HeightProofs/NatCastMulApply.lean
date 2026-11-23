import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.DenomBound
import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct NNReal

namespace GlobalTheory.AdeleDenominators

section Local

variable {F : Type} [Field F] [NumberField F]

theorem valued_absNorm_le (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v ((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F) ≤ WithZero.exp (-1 : ℤ) := by
  have h1 : ((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F) =
      FinitePlace.embedding v (algebraMap (𝓞 F) F (Ideal.absNorm v.asIdeal : ℕ)) := by
    simp
  rw [h1, FinitePlace.embedding_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
    HeightOneSpectrum.valuation_of_algebraMap]
  have h2 := (HeightOneSpectrum.intValuation_le_pow_iff_mem v
    ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F) 1).2 (by simpa using Ideal.absNorm_mem v.asIdeal)
  simpa using h2

theorem local_den (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) :
    ∃ n : ℕ, 0 < n ∧ (n : ℝ≥0) ≤ max 1 ‖x‖₊ ∧ (n : v.adicCompletion F) * x ∈ v.adicCompletionIntegers F := by
  by_cases hx : Valued.v x ≤ 1
  · exact ⟨1, one_pos, by simp, by simpa [HeightOneSpectrum.mem_adicCompletionIntegers] using hx⟩
  · have h1 : 1 < Valued.v x := not_le.1 hx
    have h0 : Valued.v x ≠ 0 := (zero_lt_one.trans h1).ne'
    obtain ⟨e, he⟩ : ∃ e : ℤ, Valued.v x = WithZero.exp e := ⟨_, (WithZero.exp_log h0).symm⟩
    have hpos : 0 < e := by
      rw [he, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h1; exact h1
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hpos.le
    refine ⟨Ideal.absNorm v.asIdeal ^ k,
      pow_pos (zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm v)) k, ?_, ?_⟩
    · refine le_max_of_le_right (le_of_eq ?_)
      apply NNReal.eq
      rw [coe_nnnorm, FinitePlace.norm_def, he, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
      simp [WithZero.exp]
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, he, Nat.cast_pow, map_pow]
      calc _ ≤ (WithZero.exp (-1 : ℤ)) ^ k * WithZero.exp (k : ℤ) := by
            gcongr; exact valued_absNorm_le v
        _ = 1 := by rw [← WithZero.exp_nsmul, ← WithZero.exp_add]; simp

theorem adele_den (c : FiniteAdeleRing (𝓞 F) F) (h : HeightOneSpectrum (𝓞 F) → ℝ≥0)
    (hf : (Function.mulSupport h).Finite) (h1 : ∀ v, 1 ≤ h v) (hc : ∀ v, ‖c v‖₊ ≤ h v) :
    ∃ n : ℕ, 0 < n ∧ (n : ℝ≥0) ≤ ∏ᶠ v, h v ∧
      ∀ v, (n : v.adicCompletion F) * c v ∈ v.adicCompletionIntegers F := by
  classical
  choose m hm0 hm1 hm2 using fun v => local_den v (c v)
  have hm3 : ∀ v, (m v : ℝ≥0) ≤ h v := fun v => (hm1 v).trans (max_le (h1 v) (hc v))
  refine ⟨∏ v ∈ hf.toFinset, m v, Finset.prod_pos fun v _ => hm0 v, ?_, fun v => ?_⟩
  · rw [finprod_eq_prod h hf, Nat.cast_prod]
    exact Finset.prod_le_prod' fun v _ => hm3 v
  · by_cases hv : v ∈ hf.toFinset
    · rw [← Finset.prod_erase_mul _ _ hv, Nat.cast_mul, mul_assoc]
      exact mul_mem (natCast_mem _ _) (hm2 v)
    · have hv1 : h v = 1 := by simpa using hv
      have hm : m v = 1 := by
        have := hm3 v
        rw [hv1] at this
        have h' : m v ≤ 1 := by exact_mod_cast this
        have := hm0 v
        omega
      have := hm2 v
      rw [hm, Nat.cast_one, one_mul] at this
      exact mul_mem (natCast_mem _ _) this

theorem family_den {ι : Type} [Fintype ι] (c : ι → FiniteAdeleRing (𝓞 F) F) (h : HeightOneSpectrum (𝓞 F) → ℝ≥0)
    (hf : (Function.mulSupport h).Finite) (h1 : ∀ v, 1 ≤ h v) (hc : ∀ p v, ‖c p v‖₊ ≤ h v) :
    ∃ n : ℕ, 0 < n ∧ (n : ℝ≥0) ≤ (∏ᶠ v, h v) ^ Fintype.card ι ∧
      ∀ p v, (n : v.adicCompletion F) * c p v ∈ v.adicCompletionIntegers F := by
  choose n hn using fun p => adele_den (c p) h hf h1 (hc p)
  refine ⟨∏ p, n p, Finset.prod_pos fun p _ => (hn p).1, ?_, ?_⟩
  · push_cast
    calc ∏ p, (n p : ℝ≥0) ≤ ∏ _p : ι, ∏ᶠ v, h v := Finset.prod_le_prod' fun p _ => (hn p).2.1
      _ = (∏ᶠ v, h v) ^ Fintype.card ι := by rw [Finset.prod_const, Finset.card_univ]
  · intro p v
    classical
    have e : ((∏ q, n q : ℕ) : v.adicCompletion F) * c p v =
        ((∏ q ∈ Finset.univ.erase p, n q : ℕ) : v.adicCompletion F) * ((n p : v.adicCompletion F) * c p v) := by
      rw [← mul_assoc, ← Nat.cast_mul, Finset.prod_erase_mul _ _ (Finset.mem_univ p)]
    rw [e]
    exact mul_mem (natCast_mem _ _) ((hn p).2.2 v)

end Local

section Lattice

variable {E : Type} [Field E] [NumberField E]

theorem exists_nat_mem (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hI : I ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ (n : E) ∈ I := by
  obtain ⟨α, hα, hαI⟩ := FractionalIdeal.exists_ne_zero_mem_isInteger hI
  have hn : Ideal.absNorm (Ideal.span {α}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hα
  refine ⟨_, Nat.pos_of_ne_zero hn, ?_⟩
  obtain ⟨β, hβ⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {α}))
  have : ((Ideal.absNorm (Ideal.span {α}) : ℕ) : E) = β • algebraMap (𝓞 E) E α := by
    rw [Algebra.smul_def, ← map_mul, hβ, map_natCast]
  rw [this]
  exact Submodule.smul_mem (I : Submodule (𝓞 E) E) β hαI

theorem exists_nat_smul_mem {W : Type} [AddCommGroup W] [Module E W] [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W]
    (L : Submodule (𝓞 E) W) (hL : Submodule.span E (L : Set W) = ⊤) (x : W) :
    ∃ n : ℕ, 0 < n ∧ (n : E) • x ∈ L := by
  have hx : x ∈ Submodule.span E (L : Set W) := by rw [hL]; trivial
  have key : ∀ (n : ℕ) (y : W), y ∈ L → (n : E) • y ∈ L := fun n y hy => by
    rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hy n
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_pos, by simpa using hy⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨s, hs, hsy⟩ := hy
    obtain ⟨t, ht, htz⟩ := hz
    refine ⟨s * t, mul_pos hs ht, ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [mul_comm, Nat.cast_mul, mul_smul]; exact key _ _ hsy
    · rw [Nat.cast_mul, mul_smul]; exact key _ _ htz
  | smul e y _ hy =>
    obtain ⟨s, hs, hsy⟩ := hy
    obtain ⟨m, hm, hint⟩ := exists_integral_multiples ℤ ℚ ({e} : Finset E)
    have hi : IsIntegral ℤ ((m.natAbs : E) * e) := by
      have h0 := hint e (Finset.mem_singleton_self e)
      rw [zsmul_eq_mul] at h0
      rcases Int.natAbs_eq m with h | h
      · rw [h] at h0; simpa using h0
      · rw [h] at h0; simpa using h0.neg
    refine ⟨m.natAbs * s, mul_pos (Int.natAbs_pos.2 hm) hs, ?_⟩
    obtain ⟨r, hr⟩ : ∃ r : 𝓞 E, algebraMap (𝓞 E) E r = (m.natAbs : E) * e := ⟨⟨_, hi⟩, rfl⟩
    have : ((m.natAbs * s : ℕ) : E) • e • y = r • ((s : E) • y) := by
      rw [← algebraMap_smul E r, smul_smul, smul_smul, hr]
      congr 1
      push_cast; ring
    rw [this]
    exact L.smul_mem _ hsy

end Lattice

theorem column_expand {F E R W n κ : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R]
    [AddCommGroup W] [Module E W] [Fintype n] [DecidableEq n] [Fintype κ] (b : Module.Basis κ F E)
    (f : Module.Basis n E W) (M : Matrix n n (R ⊗[F] E)) (i : n) (B N : ℕ) :
    M.mulVec (fun l => (1 : R) ⊗ₜ[F] (Pi.single i ((B * N : ℕ) : E) : n → E) l) =
      ∑ j, ∑ k, fun l => ((N : R) * (Algebra.TensorProduct.basis R b).repr (M j i) k) ⊗ₜ[F]
        f.repr (((B : E) * b k) • f j) l := by
  have hv : (fun l => (1 : R) ⊗ₜ[F] (Pi.single i ((B * N : ℕ) : E) : n → E) l) =
      Pi.single i ((B * N : ℕ) : R ⊗[F] E) := by
    funext l
    by_cases hl : l = i
    · subst hl
      rw [Pi.single_eq_same, Pi.single_eq_same]
      exact map_natCast (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E) _
    · rw [Pi.single_eq_of_ne hl, Pi.single_eq_of_ne hl, TensorProduct.tmul_zero]
  have e1 : ((B * N : ℕ) : R ⊗[F] E) = (N : R) ⊗ₜ[F] (B : E) := by
    have a1 : ((B : ℕ) : R ⊗[F] E) = (1 : R) ⊗ₜ[F] (B : E) :=
      (map_natCast (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E) _).symm
    rw [Nat.cast_mul, a1, Algebra.TensorProduct.natCast_def N, Algebra.TensorProduct.tmul_mul_tmul,
      one_mul, mul_one]
  rw [hv, Matrix.mulVec_single]
  funext l
  rw [Finset.sum_apply, Finset.sum_eq_single l]
  · rw [Finset.sum_apply]
    have hy2 := (Algebra.TensorProduct.basis R b).sum_repr (M l i)
    change M l i * _ = _
    conv_lhs => rw [← hy2, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [MulOpposite.unop_op, e1, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul',
      Algebra.TensorProduct.tmul_mul_tmul,
      smul_eq_mul, mul_one, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same,
      smul_eq_mul, mul_one, mul_comm (b k), mul_comm _ (N : R)]
  · intro j _ hj
    rw [Finset.sum_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_of_ne hj.symm, smul_zero,
      TensorProduct.tmul_zero]
  · intro h; exact absurd (Finset.mem_univ l) h

theorem natCast_mul_apply {F : Type} [Field F] [NumberField F] (N : ℕ) (a : FiniteAdeleRing (𝓞 F) F)
    (v : HeightOneSpectrum (𝓞 F)) :
    ((N : FiniteAdeleRing (𝓞 F) F) * a) v = (N : v.adicCompletion F) * a v := by first | rfl | simp

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem denomBound (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) :
    GlobalTheory.SmoothForms.DenomBound θ V := by
  classical
  obtain ⟨A, hA0, hA⟩ := exists_nat_mem D.host.AA (Formalism.L2.Pj.AA_ne_zero Formalism.IndefR.Fin.factPrincipalDatum D)
  set b := Module.finBasis D.host.F D.host.E with hb
  obtain ⟨B, hB0, hB⟩ : ∃ B : ℕ, 0 < B ∧ ∀ j k, ((B : D.host.E) * b k) • V.frame j ∈ V.L0 := by
    choose m hm0 hm using fun p : Fin V.rank × Fin (Module.finrank D.host.F D.host.E) =>
      exists_nat_smul_mem V.L0 V.standardTuple_isLattice.span_eq_top (b p.2 • V.frame p.1)
    refine ⟨∏ p, m p, Finset.prod_pos fun p _ => hm0 p, fun j k => ?_⟩
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ (j, k)), Nat.cast_mul, mul_assoc, mul_smul, mul_smul,
      Nat.cast_smul_eq_nsmul]
    exact nsmul_mem (hm (j, k)) _
  refine ⟨A * B, Fintype.card (Fin V.rank × Fin V.rank × Fin (Module.finrank D.host.F D.host.E)), fun g => ?_⟩
  obtain ⟨N, hN0, hN1, hN⟩ := family_den
    (fun p : Fin V.rank × Fin V.rank × Fin (Module.finrank D.host.F D.host.E) =>
      GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D (Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram g⁻¹ p.1 p.2.1) p.2.2)
    (fun v => GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finHt V v g) (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finHt_mulSupport_finite V g)
    (fun v => le_max_left _ _)
    (fun p v => le_max_of_le_right (le_max_of_le_right (Finset.le_sup (f := fun p : Fin V.rank × Fin V.rank × Fin (Module.finrank D.host.F D.host.E) =>
      ‖evalV D.host.F v (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D (Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram g⁻¹ p.1 p.2.1) p.2.2)‖₊)
      (Finset.mem_univ p))))
  refine ⟨A * (B * N), by positivity, ?_, fun i => ?_⟩
  · have h1 : (∏ᶠ v, GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finHt V v g) ≤ GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V g :=
      le_mul_of_one_le_left' (Finset.one_le_prod' fun _ _ => le_max_left _ _)
    have h2 : (N : ℝ≥0) ≤ GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V g ^ _ := hN1.trans (pow_le_pow_left' h1 _)
    have h3 : (N : ℝ) ≤ (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V g : ℝ) ^
        Fintype.card (Fin V.rank × Fin V.rank × Fin (Module.finrank D.host.F D.host.E)) := by exact_mod_cast h2
    push_cast
    rw [← mul_assoc]
    gcongr
  · refine Submodule.subset_span ⟨A, hA, Pi.single i ((B * N : ℕ) : D.host.E), ?_, ?_⟩
    · refine ⟨(finHom V g⁻¹).1.mulVec (Formalism.L2.Pj.finVec V (Pi.single i ((B * N : ℕ) : D.host.E))), ?_, ?_⟩
      · have hz : (finHom V g⁻¹).1.mulVec (Formalism.L2.Pj.finVec V (Pi.single i ((B * N : ℕ) : D.host.E))) =
            ∑ j, ∑ k, fun l => ((N : Af D.host.F) *
              GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D (Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram g⁻¹ j i) k) ⊗ₜ[D.host.F]
              V.frame.repr (((B : D.host.E) * b k) • V.frame j) l :=
          column_expand b V.frame (Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram g⁻¹) i B N
        rw [hz]
        refine sum_mem fun j _ => sum_mem fun k _ => AddSubgroup.subset_closure ⟨_, fun v => ?_, _, hB j k, rfl⟩
        rw [natCast_mul_apply]; exact hN (j, i, k) v
      · rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one,
          Matrix.one_mulVec]
    · rw [← Pi.single_smul, smul_eq_mul, ← Nat.cast_mul]

end GlobalTheory.AdeleDenominators

end
