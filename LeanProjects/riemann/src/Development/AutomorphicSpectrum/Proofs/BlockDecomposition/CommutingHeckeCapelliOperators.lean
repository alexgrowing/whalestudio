import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UfamConst
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.CommonEigenvectors.KillPoly
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.DiagonalInfinityValues.InfGLValDiag
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.NormalisedExistence.ExistsNormed
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.CasimirOnParabolicInduction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieOneLMemZalg
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsStableBdSub
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapelliLeviFactorizationSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShiftedCapelliDeterminantSubleadingCoeffTrace
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

noncomputable section

namespace GlobalTheory.CompanionTheory.CapCoeff

theorem coeff_mem_of_values {A : Type} [AddCommGroup A] [Module ℂ A] (W : Submodule ℂ A) (n : ℕ) (c : ℕ → A)
    (h : ∀ u : ℂ, ∑ k ∈ Finset.range n, u ^ k • c k ∈ W) : ∀ k < n, c k ∈ W := by
  intro k hk
  rw [← Submodule.Quotient.mk_eq_zero W]
  refine (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun f => ?_
  let p : ℂ[X] := ∑ i ∈ Finset.range n, Polynomial.C (f (Submodule.Quotient.mk (c i))) * Polynomial.X ^ i
  have hp : p = 0 := by
    refine Polynomial.funext fun u => ?_
    have h0 : (Submodule.Quotient.mk (∑ i ∈ Finset.range n, u ^ i • c i) : A ⧸ W) = 0 :=
      (Submodule.Quotient.mk_eq_zero W).2 (h u)
    have h1 := congrArg f h0
    rw [← Submodule.mkQ_apply, map_sum, map_sum, map_zero] at h1
    simp only [p, Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_zero]
    rw [← h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, map_smul, smul_eq_mul, mul_comm]
    rfl
  have hc := congrArg (fun q : ℂ[X] => q.coeff k) hp
  simp only [p, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero] at hc
  rw [Finset.sum_ite_eq] at hc
  simpa [Finset.mem_range, hk] using hc

theorem qdet_coeffs {A : Type} [Ring A] [Algebra ℂ A] (W : Subalgebra ℂ A) (m : ℕ)
    (X : Fin (m + 1) → Fin (m + 1) → A) (s : ℂ) (hW : ∀ u, Formalism.REAL.qdet X u ∈ W) :
    ∃ (c : ℕ → A) (t : ℂ), (∀ k, c k ∈ W) ∧ c (m + 1) = 1 ∧ c m = ∑ i, X i i + t • (1 : A) ∧
      ∀ u : ℂ, Formalism.REAL.qdet X (u - s) = ∑ k ∈ Finset.range (m + 1 + 1), u ^ k • c k := by
  obtain ⟨c, t, h1, h2, h3⟩ := GlobalTheory.CapelliNext.qdet_shift_next_coeff A m X s
  have hm : ∀ k < m + 1 + 1, c k ∈ Subalgebra.toSubmodule W :=
    coeff_mem_of_values _ _ c fun u => by
      rw [← h3 u]
      exact hW _
  refine ⟨fun k => if k < m + 1 + 1 then c k else 0, t, fun k => ?_, ?_, ?_, fun u => ?_⟩
  · by_cases hk : k < m + 1 + 1
    · simp only [if_pos hk]
      exact hm k hk
    · simp only [if_neg hk]
      exact W.zero_mem
  · simpa only [if_pos (Nat.lt_succ_self (m + 1))] using h1
  · simpa only [if_pos (show m < m + 1 + 1 by omega)] using h2
  · rw [h3 u]
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [if_pos (Finset.mem_range.1 hk)]

theorem qdet_commute_of {A : Type} [Ring A] [Algebra ℂ A] {n p : ℕ} (X : Fin n → Fin n → A) (Y : Fin p → Fin p → A)
    (h : ∀ i j k l, X i j * Y k l = Y k l * X i j) (u v : ℂ) :
    Formalism.REAL.qdet X u * Formalism.REAL.qdet Y v = Formalism.REAL.qdet Y v * Formalism.REAL.qdet X u := by
  have h1 : Formalism.REAL.qdet X u ∈ Subalgebra.centralizer ℂ (Set.range fun kl : Fin p × Fin p => Y kl.1 kl.2) := by
    refine GlobalTheory.CompanionTheory.CTFin.CapFactor.qdet_mem _ _ (fun i j => ?_) _
    rw [Subalgebra.mem_centralizer_iff]
    rintro _ ⟨kl, rfl⟩
    exact (h i j kl.1 kl.2).symm
  have h2 : Formalism.REAL.qdet Y v ∈ Subalgebra.centralizer ℂ {Formalism.REAL.qdet X u} := by
    refine GlobalTheory.CompanionTheory.CTFin.CapFactor.qdet_mem _ _ (fun k l => ?_) _
    rw [Subalgebra.mem_centralizer_iff]
    rintro _ rfl
    exact ((Subalgebra.mem_centralizer_iff ℂ).1 h1 _ ⟨(k, l), rfl⟩).symm
  exact (Subalgebra.mem_centralizer_iff ℂ).1 h2 _ rfl

theorem qdet_commute_self {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (X : Fin n → Fin n → A) (hX : Formalism.REAL.GlRel X)
    (u v : ℂ) : Formalism.REAL.qdet X u * Formalism.REAL.qdet X v = Formalism.REAL.qdet X v * Formalism.REAL.qdet X u := by
  have h : Formalism.REAL.qdet X v ∈ Subalgebra.centralizer ℂ {Formalism.REAL.qdet X u} := by
    refine GlobalTheory.CompanionTheory.CTFin.CapFactor.qdet_mem _ _ (fun c d => ?_) _
    rw [Subalgebra.mem_centralizer_iff]
    rintro _ rfl
    exact Formalism.REAL.qDetCentral A n X hX u c d
  exact (Subalgebra.mem_centralizer_iff ℂ).1 h _ rfl

theorem glRel_comp {A : Type} [Ring A] {n p : ℕ} {X : Fin n → Fin n → A} (hX : Formalism.REAL.GlRel X) {f : Fin p → Fin n}
    (hf : Function.Injective f) : Formalism.REAL.GlRel fun i j => X (f i) (f j) := by
  intro a b c d
  have h := hX (f a) (f b) (f c) (f d)
  simpa only [hf.eq_iff] using h

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

theorem Eop_mem_of_lie {N : ℕ} (S : Subalgebra ℂ (Module.End ℂ (Sm E N))) (hL : ∀ X, lie E N X ∈ S) (τ : E →+* ℂ)
    (p q : Fin N) : Eop τ p q ∈ S :=
  Subalgebra.smul_mem _ (Subalgebra.sub_mem _ (hL _) (Subalgebra.smul_mem _ (hL _) _)) _

def gens (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s : ℕ) : Set (Module.End ℂ (Sm E (r + s))) :=
  Set.range (fun p : (E →+* ℂ) × ℂ => GlobalTheory.CompanionTheory.CTFin.capR r s p.1 p.2) ∪
    Set.range (fun p : (E →+* ℂ) × ℂ => GlobalTheory.CompanionTheory.CTFin.capS r s p.1 p.2)

def capAlg (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s : ℕ) :
    Subalgebra ℂ (Module.End ℂ (Sm E (r + s))) :=
  Algebra.adjoin ℂ (gens E r s)

theorem capR_mem (r s : ℕ) (τ : E →+* ℂ) (u : ℂ) : GlobalTheory.CompanionTheory.CTFin.capR r s τ u ∈ capAlg E r s :=
  Algebra.subset_adjoin (Or.inl ⟨(τ, u), rfl⟩)

theorem capS_mem (r s : ℕ) (τ : E →+* ℂ) (u : ℂ) : GlobalTheory.CompanionTheory.CTFin.capS r s τ u ∈ capAlg E r s :=
  Algebra.subset_adjoin (Or.inr ⟨(τ, u), rfl⟩)

theorem capR_mul_capS (r s : ℕ) (τ τ' : E →+* ℂ) (u v : ℂ) :
    GlobalTheory.CompanionTheory.CTFin.capR r s τ u * GlobalTheory.CompanionTheory.CTFin.capS r s τ' v =
      GlobalTheory.CompanionTheory.CTFin.capS r s τ' v * GlobalTheory.CompanionTheory.CTFin.capR r s τ u := by
  by_cases h : τ = τ'
  · subst h
    exact (GlobalTheory.CompanionTheory.CTFin.CapFactor.capR_commute_capS r s τ u v).eq
  · unfold GlobalTheory.CompanionTheory.CTFin.capR GlobalTheory.CompanionTheory.CTFin.capS
    exact qdet_commute_of _ _ (fun i j k l => Eop_comm h _ _ _ _) _ _

theorem capR_mul_capR (r s : ℕ) (τ τ' : E →+* ℂ) (u v : ℂ) :
    GlobalTheory.CompanionTheory.CTFin.capR r s τ u * GlobalTheory.CompanionTheory.CTFin.capR r s τ' v =
      GlobalTheory.CompanionTheory.CTFin.capR r s τ' v * GlobalTheory.CompanionTheory.CTFin.capR r s τ u := by
  unfold GlobalTheory.CompanionTheory.CTFin.capR
  by_cases h : τ = τ'
  · subst h
    exact qdet_commute_self _ (glRel_comp (glRel_Eop τ) (Fin.castAdd_injective r s)) _ _
  · exact qdet_commute_of _ _ (fun i j k l => Eop_comm h _ _ _ _) _ _

theorem capS_mul_capS (r s : ℕ) (τ τ' : E →+* ℂ) (u v : ℂ) :
    GlobalTheory.CompanionTheory.CTFin.capS r s τ u * GlobalTheory.CompanionTheory.CTFin.capS r s τ' v =
      GlobalTheory.CompanionTheory.CTFin.capS r s τ' v * GlobalTheory.CompanionTheory.CTFin.capS r s τ u := by
  unfold GlobalTheory.CompanionTheory.CTFin.capS
  by_cases h : τ = τ'
  · subst h
    exact qdet_commute_self _ (glRel_comp (glRel_Eop τ) (Fin.natAdd_injective s r)) _ _
  · exact qdet_commute_of _ _ (fun i j k l => Eop_comm h _ _ _ _) _ _

theorem gens_comm (r s : ℕ) : ∀ a ∈ gens E r s, ∀ b ∈ gens E r s, a * b = b * a := by
  rintro a (⟨⟨τ, u⟩, rfl⟩ | ⟨⟨τ, u⟩, rfl⟩) b (⟨⟨τ', v⟩, rfl⟩ | ⟨⟨τ', v⟩, rfl⟩)
  · exact capR_mul_capR r s _ _ _ _
  · exact capR_mul_capS r s _ _ _ _
  · exact (capR_mul_capS r s _ _ _ _).symm
  · exact capS_mul_capS r s _ _ _ _

theorem capAlg_comm (r s : ℕ) : ∀ x ∈ capAlg E r s, ∀ y ∈ capAlg E r s, x * y = y * x := by
  intro x hx y hy
  letI := Algebra.adjoinCommRingOfComm ℂ (gens_comm (E := E) r s)
  exact congrArg Subtype.val (mul_comm (⟨x, hx⟩ : Algebra.adjoin ℂ (gens E r s)) ⟨y, hy⟩)

theorem capAlg_le (r s : ℕ) (T : Subalgebra ℂ (Module.End ℂ (Sm E (r + s))))
    (hT : ∀ τ p q, Eop (a := r + s) τ p q ∈ T) : capAlg E r s ≤ T := by
  refine Algebra.adjoin_le ?_
  rintro _ (⟨⟨τ, u⟩, rfl⟩ | ⟨⟨τ, u⟩, rfl⟩)
  · exact GlobalTheory.CompanionTheory.CTFin.CapFactor.qdet_mem T _ (fun i j => hT τ _ _) _
  · exact GlobalTheory.CompanionTheory.CTFin.CapFactor.qdet_mem T _ (fun i j => hT τ _ _) _

theorem capAlg_commute_cap (r s : ℕ) {x : Module.End ℂ (Sm E (r + s))} (hx : x ∈ capAlg E r s) (τ : E →+* ℂ) (u : ℂ) :
    Commute (cap (a := r + s) τ u) x := by
  have hc : capAlg E r s ≤ Subalgebra.centralizer ℂ {cap (a := r + s) τ u} := by
    refine capAlg_le r s _ fun τ' p q => Eop_mem_of_lie _ (fun X => ?_) τ' p q
    rw [Subalgebra.mem_centralizer_iff]
    rintro _ rfl
    exact (commute_cap_lie τ u X).eq
  exact (Subalgebra.mem_centralizer_iff ℂ).1 (hc hx) _ rfl

theorem capR_coeffs (m s : ℕ) (τ : E →+* ℂ) :
    ∃ (c : ℕ → Module.End ℂ (Sm E (m + 1 + s))) (t : ℂ),
      (∀ k, c k ∈ capAlg E (m + 1) s) ∧ c (m + 1) = 1 ∧
      c m = ∑ i : Fin (m + 1), Eop (a := m + 1 + s) τ (Fin.castAdd s i) (Fin.castAdd s i) + t • 1 ∧
      ∀ u : ℂ, GlobalTheory.CompanionTheory.CTFin.capR (m + 1) s τ (u - (s : ℂ) / 2) =
        ∑ k ∈ Finset.range (m + 1 + 1), u ^ k • c k := by
  obtain ⟨c, t, h0, h1, h2, h3⟩ := qdet_coeffs (capAlg E (m + 1) s) m
    (fun i j : Fin (m + 1) => Eop (a := m + 1 + s) τ (Fin.castAdd s i) (Fin.castAdd s j))
    ((s : ℂ) / 2 - (((m + 1 : ℕ) : ℂ) - 1) / 2) (fun u => by
      have := capR_mem (E := E) (m + 1) s τ (u - (((m + 1 : ℕ) : ℂ) - 1) / 2)
      rwa [GlobalTheory.CompanionTheory.CTFin.capR, sub_add_cancel] at this)
  refine ⟨c, t, h0, h1, h2, fun u => ?_⟩
  rw [← h3 u, GlobalTheory.CompanionTheory.CTFin.capR]
  congr 1
  ring

theorem capS_coeffs (r n : ℕ) (τ : E →+* ℂ) :
    ∃ c : ℕ → Module.End ℂ (Sm E (r + (n + 1))),
      (∀ k, c k ∈ capAlg E r (n + 1)) ∧ c (n + 1) = 1 ∧
      ∀ u : ℂ, GlobalTheory.CompanionTheory.CTFin.capS r (n + 1) τ (u + (r : ℂ) / 2) =
        ∑ k ∈ Finset.range (n + 1 + 1), u ^ k • c k := by
  obtain ⟨c, t, h0, h1, -, h3⟩ := qdet_coeffs (capAlg E r (n + 1)) n
    (fun i j : Fin (n + 1) => Eop (a := r + (n + 1)) τ (Fin.natAdd r i) (Fin.natAdd r j))
    (-((r : ℂ) / 2) - (((n + 1 : ℕ) : ℂ) - 1) / 2) (fun u => by
      have := capS_mem (E := E) r (n + 1) τ (u - (((n + 1 : ℕ) : ℂ) - 1) / 2)
      rwa [GlobalTheory.CompanionTheory.CTFin.capS, sub_add_cancel] at this)
  refine ⟨c, h0, h1, fun u => ?_⟩
  rw [← h3 u, GlobalTheory.CompanionTheory.CTFin.capS]
  congr 1
  ring

theorem leftInv_closure {N r : ℕ} (F : Sm E N)
    (hF : ∀ (v : BlockIx N r → Ad E) (g : GA E N), F.1 (unip v * g) = F.1 g) :
    ∀ w ∈ Subgroup.closure (Set.range (unip : (BlockIx N r → Ad E) → GA E N)), ∀ g, F.1 (w * g) = F.1 g := by
  intro w hw
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    exact hF v
  | one => intro g; rw [one_mul]
  | mul x y _ _ hx hy => intro g; rw [mul_assoc, hx, hy]
  | inv x _ hx => intro g; rw [← hx (x⁻¹ * g), mul_inv_cancel_left]

theorem capAlg_leftInv (r s : ℕ) {x : Module.End ℂ (Sm E (r + s))} (hx : x ∈ capAlg E r s) (F : Sm E (r + s))
    (hF : ∀ (v : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), F.1 (unip v * g) = F.1 g)
    (v : BlockIx (r + s) r → Ad E) (g : GA E (r + s)) : (x F).1 (unip v * g) = (x F).1 g := by
  have hc := capAlg_le (E := E) r s (GlobalTheory.SpehInfChar.leftInvAlg (Subgroup.closure
    (Set.range (unip : (BlockIx (r + s) r → Ad E) → GA E (r + s)))))
    (fun τ p q => GlobalTheory.SpehInfChar.Eop_mem_leftInvAlg _ τ p q)
  exact hc hx F (leftInv_closure F hF) (unip v) (Subgroup.subset_closure ⟨v, rfl⟩) g

theorem exists_coeffs : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s : ℕ), 0 < r → 0 < s →
  ∃ (S : Subalgebra ℂ (Module.End ℂ (Sm E (r + s)))) (a b : (E →+* ℂ) → ℕ → Module.End ℂ (Sm E (r + s))) (t : (E →+* ℂ) → ℂ),
    (∀ x ∈ S, ∀ y ∈ S, x * y = y * x) ∧
    (∀ x ∈ S, ∀ (τ : E →+* ℂ) (u : ℂ), Commute (cap (a := r + s) τ u) x) ∧
    (∀ x ∈ S, ∀ F : Sm E (r + s), (∀ (v : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), F.1 (unip v * g) = F.1 g) →
      ∀ (v : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), (x F).1 (unip v * g) = (x F).1 g) ∧
    (∀ τ k, a τ k ∈ S) ∧ (∀ τ k, b τ k ∈ S) ∧ (∀ τ, a τ r = 1) ∧ (∀ τ, b τ s = 1) ∧
    (∀ τ, a τ (r - 1) = ∑ i : Fin r, Eop (a := r + s) τ (Fin.castAdd s i) (Fin.castAdd s i) + t τ • 1) ∧
    (∀ τ u, GlobalTheory.CompanionTheory.CTFin.capR r s τ (u - (s : ℂ) / 2) = ∑ k ∈ Finset.range (r + 1), u ^ k • a τ k) ∧
    (∀ τ u, GlobalTheory.CompanionTheory.CTFin.capS r s τ (u + (r : ℂ) / 2) = ∑ k ∈ Finset.range (s + 1), u ^ k • b τ k) := by
  intro E _ _ _ r s hr hs
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n, s = n + 1 := ⟨s - 1, by omega⟩
  choose a t ha0 ha1 ha2 ha3 using capR_coeffs (E := E) m (n + 1)
  choose b hb0 hb1 hb2 using capS_coeffs (E := E) (m + 1) n
  exact ⟨capAlg E (m + 1) (n + 1), a, b, t, capAlg_comm _ _, fun x hx τ u => capAlg_commute_cap _ _ hx τ u,
    fun x hx F hF v g => capAlg_leftInv _ _ hx F hF v g, ha0, hb0, ha1, hb1, ha2, ha3, hb2⟩

end GlobalTheory.CompanionTheory.CapCoeff

end
