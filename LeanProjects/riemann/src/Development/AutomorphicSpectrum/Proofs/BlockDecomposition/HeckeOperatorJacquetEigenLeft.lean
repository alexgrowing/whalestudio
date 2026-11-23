import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeOperatorsCommuteOnFixed
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantOrbit
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsOpenOhat

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.HeckeNilp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mem_Km_of_entries {N : ℕ} (m : ℕ) (g : GL (Fin N) k)
    (h1 : ∀ i j, (g : Matrix (Fin N) (Fin N) k) i j ∈ 𝒪[k])
    (h2 : ∀ i j, ((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j ∈ 𝒪[k])
    (h3 : ∀ i j, ∃ y ∈ 𝒪[k], y * (((Zls.unif k ^ m : 𝒪[k])) : k) =
      (g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) :
    g ∈ Zls.Km k N m :=
  GlobalTheory.CuspNF.KprOpen.mem_map_ker 𝒪[k] (Zls.unif k ^ m) g h1 h2 h3

theorem Km_le_KO (N m : ℕ) : Zls.Km k N m ≤ KO k (Fin N) := by
  rintro _ ⟨u, -, rfl⟩
  exact ⟨u, rfl⟩

theorem unif_pow_ne_zero (m : ℕ) : (((Zls.unif k ^ m : 𝒪[k])) : k) ≠ 0 := by
  have h : Zls.unif k ≠ 0 := Zls.irreducible_unif.ne_zero
  have := pow_ne_zero m h
  simpa using this

theorem isOpen_Km (N m : ℕ) : IsOpen (Zls.Km k N m : Set (GL (Fin N) k)) := by
  set c : k := (((Zls.unif k ^ m : 𝒪[k])) : k) with hc
  have hc0 : c ≠ 0 := unif_pow_ne_zero m
  have hU : IsOpen {g : GL (Fin N) k | ∀ i j, ((g : Matrix (Fin N) (Fin N) k) i j -
      (1 : Matrix (Fin N) (Fin N) k) i j) * c⁻¹ ∈ 𝒪[k]} := by
    simp only [Set.setOf_forall]
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
    have ho : IsOpen (𝒪[k] : Set k) := Valuation.isOpen_integer
    refine ho.preimage (f := fun g : GL (Fin N) k =>
      ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) * c⁻¹) ?_
    have := Units.continuous_val (M := Matrix (Fin N) (Fin N) k)
    fun_prop
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset
    ((hU.inter (GlobalTheory.SplitFlip.isOpen_KO (k := k) (n := Fin N))).mem_nhds ?_) ?_)
  · refine ⟨fun i j => ?_, one_mem _⟩
    simp
  · rintro g ⟨hg, hK⟩
    have hK' := (GlobalTheory.SplitFlip.mem_KO_iff g).1 hK
    exact mem_Km_of_entries m g hK'.1 hK'.2 fun i j => ⟨_, hg i j, by
      rw [mul_assoc, inv_mul_cancel₀ hc0, mul_one]⟩

theorem isCompact_Km (N m : ℕ) : IsCompact (Zls.Km k N m : Set (GL (Fin N) k)) :=
  GlobalTheory.SplitFlip.isCompact_KO.of_isClosed_subset
    (Subgroup.isClosed_of_isOpen _ (isOpen_Km N m)) (Km_le_KO N m)

theorem eq_zero_of_forms {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin N) k) V} (hπ : IsSmooth π) {m : ℕ} {w : V}
    (hw : w ∈ fixed π (Zls.Km k N m))
    (h : ∀ l : Module.Dual ℂ V, (∀ x ∈ Zls.Km k N m, l ∘ₗ π x = l) → l w = 0) : w = 0 := by
  by_contra hne
  have hnot : w ∉ twKer π (Zls.Km k N m) 1 :=
    fun h' => hne (GlobalTheory.IwahoriInj.eq_zero_of_fixed hπ (isCompact_Km N m) hw h')
  have hq : (twKer π (Zls.Km k N m) 1).mkQ w ≠ 0 := by
    rwa [Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual ℂ (V ⧸ twKer π (Zls.Km k N m) 1),
      f ((twKer π (Zls.Km k N m) 1).mkQ w) ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hq ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 hc)
  refine hf (h (f ∘ₗ (twKer π (Zls.Km k N m) 1).mkQ) fun x hx => LinearMap.ext fun u => ?_)
  show f ((twKer π (Zls.Km k N m) 1).mkQ (π x u)) = f ((twKer π (Zls.Km k N m) 1).mkQ u)
  congr 1
  exact (Submodule.Quotient.eq _).2 (GlobalTheory.IwahoriInj.sub_mem_twKer hx u)

end GlobalTheory.CompanionTheory.HeckeNilp

namespace GlobalTheory.CompanionTheory.HeckeNilp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_diagPow (N : ℕ) (a : Fin N → ℤ) :
    ((Zls.diagPow k N a : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) =
      Matrix.diagonal fun i => ((Zls.unifU k ^ a i : kˣ) : k) := rfl

theorem diagPow_zero (N : ℕ) : Zls.diagPow k N 0 = 1 := by
  refine Units.ext ?_
  rw [val_diagPow]
  simp

theorem diagPow_inv (N : ℕ) (a : Fin N → ℤ) : (Zls.diagPow k N a)⁻¹ = Zls.diagPow k N (-a) := by
  refine (eq_inv_of_mul_eq_one_left ?_).symm
  refine Units.ext ?_
  rw [Units.val_mul, val_diagPow, val_diagPow, Matrix.diagonal_mul_diagonal, Units.val_one,
    ← Matrix.diagonal_one]
  congr 1
  funext i
  rw [← Units.val_mul, ← zpow_add]
  simp

theorem conj_apply (N : ℕ) (a : Fin N → ℤ) (x : GL (Fin N) k) (i j : Fin N) :
    ((Zls.diagPow k N a * x * (Zls.diagPow k N a)⁻¹ : GL (Fin N) k) :
        Matrix (Fin N) (Fin N) k) i j =
      ((Zls.unifU k ^ a i : kˣ) : k) * (x : Matrix (Fin N) (Fin N) k) i j *
        ((Zls.unifU k ^ (-a j) : kˣ) : k) := by
  rw [diagPow_inv, Units.val_mul, Units.val_mul, val_diagPow, val_diagPow, Matrix.mul_diagonal,
    Matrix.diagonal_mul]
  rfl

theorem nsmul_omegaVec_apply (N j r : ℕ) (i : Fin N) :
    (r • Zls.omegaVec N j) i = if (i : ℕ) < j then (r : ℤ) else 0 := by
  simp [Zls.omegaVec]

theorem antitone_omegaVec (N j : ℕ) : Antitone (Zls.omegaVec N j) := by
  intro a b hab
  have hab' : (a : ℕ) ≤ b := hab
  unfold Zls.omegaVec
  split_ifs <;> first | omega | exact le_rfl | norm_num

theorem antitone_nsmul_omegaVec (N j r : ℕ) : Antitone (r • Zls.omegaVec N j) := by
  intro a b hab
  simp only [Pi.smul_apply, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_left (antitone_omegaVec N j hab) (Int.natCast_nonneg r)

theorem isHeckeOp_pow {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin N) k) V} (hπ : IsSmooth π) {m : ℕ} (hm : 1 ≤ m) (j : ℕ)
    {T : Module.End ℂ (fixed π (Zls.Km k N m))}
    (hT : Zls.IsHeckeOp π m (Zls.diagPow k N (Zls.omegaVec N j)) T) (r : ℕ) :
    Zls.IsHeckeOp π m (Zls.diagPow k N (r • Zls.omegaVec N j)) (T ^ r) := by
  induction r with
  | zero =>
    intro v l _
    simp [diagPow_zero]
  | succ r ih =>
    have h := GlobalTheory.CompanionTheory.HeckeOpMul.isHeckeOp_mul k N V π hπ m hm (r • Zls.omegaVec N j) (Zls.omegaVec N j)
      (antitone_nsmul_omegaVec N j r) (antitone_omegaVec N j) (T ^ r) T ih hT
    rwa [← succ_nsmul, ← pow_succ] at h

theorem exists_mul_pow_mem (a : k) : ∃ e : ℕ, a * ((Zls.unif k : 𝒪[k]) : k) ^ e ∈ 𝒪[k] := by
  obtain ⟨b, c, hc, rfl⟩ := IsFractionRing.div_surjective (A := 𝒪[k]) a
  have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
  obtain ⟨e, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hc0 Zls.irreducible_unif
  refine ⟨e, ?_⟩
  have hc1 : algebraMap 𝒪[k] k c ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective 𝒪[k] k)).2 hc0
  have hu' : ((Zls.unif k : 𝒪[k]) : k) ^ e = algebraMap 𝒪[k] k c * ((u : 𝒪[k]) : k) := by
    have := congrArg (algebraMap 𝒪[k] k) hu
    rw [map_mul, map_pow] at this
    exact this.symm
  rw [hu']
  have : algebraMap 𝒪[k] k b / algebraMap 𝒪[k] k c * (algebraMap 𝒪[k] k c * ((u : 𝒪[k]) : k)) =
      ((b * (u : 𝒪[k]) : 𝒪[k]) : k) := by
    have hb : algebraMap 𝒪[k] k b = (b : k) := rfl
    push_cast
    rw [hb]
    field_simp
  rw [this]
  exact (b * (u : 𝒪[k])).2

theorem exists_matrix_mul_pow_mem {N : ℕ} (A : Matrix (Fin N) (Fin N) k) :
    ∃ e : ℕ, ∀ e', e ≤ e' → ∀ i j, A i j * ((Zls.unif k : 𝒪[k]) : k) ^ e' ∈ 𝒪[k] := by
  choose f hf using fun p : Fin N × Fin N => exists_mul_pow_mem (A p.1 p.2)
  refine ⟨Finset.univ.sup f, fun e' he i j => ?_⟩
  have h1 : f (i, j) ≤ e' := (Finset.le_sup (Finset.mem_univ (i, j))).trans he
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h1
  rw [pow_add, ← mul_assoc]
  exact mul_mem (hf (i, j)) (pow_mem (Zls.unif k).2 t)

variable {N : ℕ} (d : Fin 2 → ℕ) (hd : ∑ a, d a = N)

theorem stdBlocks_lt_iff (a : Fin 2) (s : Fin (d a)) :
    ((stdBlocks d hd ⟨a, s⟩ : Fin N) : ℕ) < d 0 ↔ a = 0 := by
  rw [stdBlocks_val]
  obtain rfl | rfl : a = 0 ∨ a = 1 := by omega
  · have := s.2
    simpa using this
  · simp

theorem unipRad_same (x : GL (Fin N) k) (hx : x ∈ unipRad k (stdBlocks d hd)) (i j : Fin N)
    (hij : (i : ℕ) < d 0 ↔ (j : ℕ) < d 0) :
    (x : Matrix (Fin N) (Fin N) k) i j = (1 : Matrix (Fin N) (Fin N) k) i j := by
  obtain ⟨⟨a, s⟩, rfl⟩ := (stdBlocks d hd).surjective i
  obtain ⟨⟨b, t⟩, rfl⟩ := (stdBlocks d hd).surjective j
  rw [stdBlocks_lt_iff, stdBlocks_lt_iff] at hij
  obtain rfl : a = b := by omega
  rw [(mem_unipRad.1 hx).2 a s t]
  by_cases h : s = t
  · subst h; simp
  · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne]
    intro h'
    have := (stdBlocks d hd).injective h'
    simp at this
    exact h this

theorem unipRad_lower (x : GL (Fin N) k) (hx : x ∈ unipRad k (stdBlocks d hd)) (i j : Fin N)
    (hi : d 0 ≤ (i : ℕ)) (hj : (j : ℕ) < d 0) : (x : Matrix (Fin N) (Fin N) k) i j = 0 := by
  obtain ⟨⟨a, s⟩, rfl⟩ := (stdBlocks d hd).surjective i
  obtain ⟨⟨b, t⟩, rfl⟩ := (stdBlocks d hd).surjective j
  rw [stdBlocks_lt_iff] at hj
  have ha : a ≠ 0 := fun h => by
    have := (stdBlocks_lt_iff d hd a s).2 h
    omega
  subst hj
  exact mem_parab_iff.1 (mem_unipRad.1 hx).1 a 0 s t (by omega)

end GlobalTheory.CompanionTheory.HeckeNilp

namespace GlobalTheory.CompanionTheory.HeckeNilp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {N : ℕ} (d : Fin 2 → ℕ) (hd : ∑ a, d a = N)

theorem one_entry_mem (i j : Fin N) : (1 : Matrix (Fin N) (Fin N) k) i j ∈ 𝒪[k] := by
  by_cases h : i = j
  · subst h
    simpa using one_mem 𝒪[k]
  · simpa [Matrix.one_apply_ne h] using zero_mem 𝒪[k]

theorem conj_entries {m r : ℕ} (hmr : m ≤ r) (x : GL (Fin N) k)
    (hx : x ∈ unipRad k (stdBlocks d hd))
    (hi : ∀ i j, (x : Matrix (Fin N) (Fin N) k) i j * ((Zls.unif k : 𝒪[k]) : k) ^ (r - m) ∈ 𝒪[k])
    (i j : Fin N) :
    ∃ y ∈ 𝒪[k], y * (((Zls.unif k ^ m : 𝒪[k])) : k) =
      ((Zls.diagPow k N (r • Zls.omegaVec N (d 0)) * x *
        (Zls.diagPow k N (r • Zls.omegaVec N (d 0)))⁻¹ : GL (Fin N) k) :
          Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j := by
  have hcancel : ((Zls.unifU k ^ (r : ℤ) : kˣ) : k) * ((Zls.unifU k ^ (-(r : ℤ)) : kˣ) : k) = 1 := by
    rw [← Units.val_mul, ← zpow_add]
    simp
  rw [conj_apply, nsmul_omegaVec_apply, nsmul_omegaVec_apply]
  by_cases h1 : (i : ℕ) < d 0 <;> by_cases h2 : (j : ℕ) < d 0
  · rw [if_pos h1, if_pos h2, unipRad_same d hd x hx i j (by simp [h1, h2])]
    refine ⟨0, zero_mem _, ?_⟩
    rw [mul_right_comm, hcancel]
    simp
  · have hne : i ≠ j := fun h => h2 (h ▸ h1)
    rw [if_pos h1, if_neg h2, Matrix.one_apply_ne hne]
    refine ⟨_, hi i j, ?_⟩
    have hu : ((Zls.unifU k ^ (r : ℤ) : kˣ) : k) = ((Zls.unif k : 𝒪[k]) : k) ^ r := by
      rw [zpow_natCast, Units.val_pow_eq_pow_val]
      rfl
    rw [hu]
    push_cast
    simp only [neg_zero, zpow_zero, Units.val_one, mul_one, sub_zero]
    rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hmr, mul_comm]
  · have hne : i ≠ j := fun h => h1 (h ▸ h2)
    rw [if_neg h1, if_pos h2, Matrix.one_apply_ne hne, unipRad_lower d hd x hx i j (by omega) h2]
    exact ⟨0, zero_mem _, by simp⟩
  · rw [if_neg h1, if_neg h2, unipRad_same d hd x hx i j (by simp [h1, h2])]
    exact ⟨0, zero_mem _, by simp⟩

theorem conj_mem_Km {m r : ℕ} (hmr : m ≤ r) (x : GL (Fin N) k)
    (hx : x ∈ unipRad k (stdBlocks d hd))
    (hi : ∀ i j, (x : Matrix (Fin N) (Fin N) k) i j * ((Zls.unif k : 𝒪[k]) : k) ^ (r - m) ∈ 𝒪[k])
    (hi' : ∀ i j, ((x⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j *
      ((Zls.unif k : 𝒪[k]) : k) ^ (r - m) ∈ 𝒪[k]) :
    Zls.diagPow k N (r • Zls.omegaVec N (d 0)) * x *
      (Zls.diagPow k N (r • Zls.omegaVec N (d 0)))⁻¹ ∈ Zls.Km k N m := by
  set D := Zls.diagPow k N (r • Zls.omegaVec N (d 0)) with hD
  have hc : (((Zls.unif k ^ m : 𝒪[k])) : k) ∈ 𝒪[k] := (Zls.unif k ^ m).2
  have hint : ∀ z : GL (Fin N) k, (∀ i j, ∃ y ∈ 𝒪[k], y * (((Zls.unif k ^ m : 𝒪[k])) : k) =
      (z : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) →
      ∀ i j, (z : Matrix (Fin N) (Fin N) k) i j ∈ 𝒪[k] := fun z hz i j => by
    obtain ⟨y, hy, e⟩ := hz i j
    have : (z : Matrix (Fin N) (Fin N) k) i j =
        y * (((Zls.unif k ^ m : 𝒪[k])) : k) + (1 : Matrix (Fin N) (Fin N) k) i j := by
      rw [e]; ring
    rw [this]
    exact add_mem (mul_mem hy hc) (one_entry_mem i j)
  have h1 := conj_entries d hd hmr x hx hi
  have h2 := conj_entries d hd hmr x⁻¹ (inv_mem hx) hi'
  have hinv : (D * x * D⁻¹)⁻¹ = D * x⁻¹ * D⁻¹ := by group
  refine mem_Km_of_entries m _ (hint _ h1) ?_ h1
  rw [hinv]
  exact hint _ h2

theorem exists_forms_vanish {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (m : ℕ) {u : V}
    (hu : u ∈ twKer π (unipRad k (stdBlocks d hd)) 1) :
    ∃ r₀ : ℕ, ∀ r, r₀ ≤ r → ∀ l : Module.Dual ℂ V, (∀ x ∈ Zls.Km k N m, l ∘ₗ π x = l) →
      l (π (Zls.diagPow k N (r • Zls.omegaVec N (d 0))) u) = 0 := by
  unfold twKer at hu
  induction hu using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨n, v, rfl⟩ := hw
    obtain ⟨e₁, h₁⟩ := exists_matrix_mul_pow_mem ((n : GL (Fin N) k) : Matrix (Fin N) (Fin N) k)
    obtain ⟨e₂, h₂⟩ := exists_matrix_mul_pow_mem
      (((n : GL (Fin N) k)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k)
    refine ⟨e₁ + e₂ + m, fun r hr l hl => ?_⟩
    set D := Zls.diagPow k N (r • Zls.omegaVec N (d 0)) with hD
    have hc : D * (n : GL (Fin N) k) * D⁻¹ ∈ Zls.Km k N m :=
      conj_mem_Km d hd (by omega) _ n.2 (h₁ _ (by omega)) (h₂ _ (by omega))
    have hcomm : π D (π (n : GL (Fin N) k) v) = π (D * (n : GL (Fin N) k) * D⁻¹) (π D v) := by
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      congr 2
      group
    have hinv := LinearMap.congr_fun (hl _ hc) (π D v)
    simp only [LinearMap.comp_apply] at hinv
    simp only [MonoidHom.one_apply, Units.val_one, one_smul, map_sub]
    rw [hcomm, hinv, sub_self]
  | zero => exact ⟨0, fun r _ l _ => by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨r₁, h₁⟩ := ha
    obtain ⟨r₂, h₂⟩ := hb
    refine ⟨max r₁ r₂, fun r hr l hl => ?_⟩
    rw [map_add, map_add, h₁ r (le_of_max_le_left hr) l hl, h₂ r (le_of_max_le_right hr) l hl,
      add_zero]
  | smul c a _ ha =>
    obtain ⟨r₁, h₁⟩ := ha
    refine ⟨r₁, fun r hr l hl => ?_⟩
    rw [map_smul, map_smul, h₁ r hr l hl, smul_zero]

theorem hecke_nilpotent : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → ∀ m : ℕ, 1 ≤ m → ∀ (d : Fin 2 → ℕ) (hd : ∑ a, d a = N), 0 < d 0 → 0 < d 1 → ∀ T : Module.End ℂ (fixed π (Zls.Km k N m)), Zls.IsHeckeOp π m (Zls.diagPow k N (Zls.omegaVec N (d 0))) T → ∀ v : fixed π (Zls.Km k N m), (Submodule.Quotient.mk (v : V) : Jacquet π (unipRad k (stdBlocks d hd))) = 0 → ∃ r : ℕ, (T ^ r) v = 0 := by
  intro k _ _ _ _ N V _ _ π hπ m hm d hd _ _ T hT v hv
  have hmem : (v : V) ∈ twKer π (unipRad k (stdBlocks d hd)) 1 :=
    (Submodule.Quotient.mk_eq_zero _).1 hv
  obtain ⟨r, hr⟩ := exists_forms_vanish d hd π m hmem
  refine ⟨r, Subtype.ext ?_⟩
  refine eq_zero_of_forms hπ ((T ^ r) v).2 fun l hl => ?_
  rw [← isHeckeOp_pow hπ hm (d 0) hT r v l hl]
  exact hr r le_rfl l hl

end GlobalTheory.CompanionTheory.HeckeNilp
