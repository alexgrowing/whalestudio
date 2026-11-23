import Formalism.LocalToGlobal.InertKernelTheory.DefsBasis
import Formalism.FrobeniusOrbits.RealSubfieldLeCompositum
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.OrderOfSignGroupDvdTwo
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.CardTrivialFirstComponent
import Formalism.LocalToGlobal.GlobalTheory.GL3.IsometryLinkageTrivialLevel
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IntRing

noncomputable section

namespace Formalism.L2.KerInert

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.FrobeniusOrbits

namespace IntegralOrthonormalChange

variable {p : ℕ} [Fact p.Prime]

noncomputable def intRing (p : ℕ) [Fact p.Prime] : Subring ℂ_[p] :=
  _root_.UpperTheory.Reformulated.B.CapelliIdentity₂.intRing p

theorem integral_iff {σ : Type*} (F : MvPowerSeries σ ℂ_[p]) :
    IntegralMv F ↔ ∃ G : MvPowerSeries σ (intRing p), MvPowerSeries.map (intRing p).subtype G = F := by
  constructor
  · intro h
    refine ⟨fun e => ⟨MvPowerSeries.coeff e F, h e⟩, ?_⟩
    ext e
    rfl
  · rintro ⟨G, rfl⟩ e
    rw [MvPowerSeries.coeff_map]
    exact (MvPowerSeries.coeff e G).2

theorem integral_mul {σ : Type*} {F G : MvPowerSeries σ ℂ_[p]} (hF : IntegralMv F) (hG : IntegralMv G) :
    IntegralMv (F * G) := by
  obtain ⟨F', rfl⟩ := (integral_iff F).1 hF
  obtain ⟨G', rfl⟩ := (integral_iff G).1 hG
  exact (integral_iff _).2 ⟨F' * G', map_mul _ _ _⟩

theorem constantCoeff_lift {σ : Type*} (G : MvPowerSeries σ (intRing p)) :
    ((MvPowerSeries.constantCoeff G : intRing p) : ℂ_[p]) =
      MvPowerSeries.constantCoeff (MvPowerSeries.map (intRing p).subtype G) := by
  rw [MvPowerSeries.constantCoeff_map]
  rfl

theorem integral_subst {σ τ : Type*} [Finite σ] (a : σ → MvPowerSeries τ ℂ_[p])
    (ha0 : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (haI : ∀ i, IntegralMv (a i))
    {f : MvPowerSeries σ ℂ_[p]} (hf : IntegralMv f) : IntegralMv (MvPowerSeries.subst a f) := by
  choose a' ha' using fun i => (integral_iff (a i)).1 (haI i)
  obtain ⟨f', rfl⟩ := (integral_iff f).1 hf
  have h0 : ∀ i, MvPowerSeries.constantCoeff (a' i) = 0 := by
    intro i
    apply Subtype.ext
    rw [constantCoeff_lift, ha', ha0]
    rfl
  have hs : MvPowerSeries.HasSubst a' := MvPowerSeries.hasSubst_of_constantCoeff_zero h0
  refine (integral_iff _).2 ⟨MvPowerSeries.subst a' f', ?_⟩
  rw [MvPowerSeries.map_subst hs]
  simp only [ha']

theorem galE_sigmaOf (D : D7) (g : D.R.GG) :
    D.host.galE (D.host.sigmaOf g) = g := by
  exact D.host.gal.apply_symm_apply _

theorem embT_K (D : D7) (τ : D.what₂.Tau) (x : D.host.E) (hx : x ∈ D.host.K) :
    embT D τ x = D.host.φ₀ x := by
  set σ := D.host.sigmaOf ((D.eTau τ : D.R.Psi) : D.R.GG)
  have hb : σ (D.host.sqd) = D.host.sqd := by
    rw [← D.host.galE_mem_Psi_iff, galE_sigmaOf]
    exact (D.eTau τ).2
  have hfix : σ x = x := by
    have hx' : x ∈ IntermediateField.adjoin ℚ {D.host.sqd} := hx
    clear hx
    induction hx' using IntermediateField.adjoin_induction with
    | mem y hy => rw [Set.mem_singleton_iff.mp hy]; exact hb
    | algebraMap r => rw [eq_ratCast (algebraMap ℚ D.host.E) r]; exact map_ratCast σ r
    | add y z _ _ h1 h2 => rw [map_add, h1, h2]
    | inv y _ h1 => rw [map_inv₀, h1]
    | mul y z _ _ h1 h2 => rw [map_mul, h1, h2]
  show D.host.φ₀ (σ x) = _
  rw [hfix]

theorem emb_mem (D : D7) (τ : D.what₂.Tau) (x : D.host.E) : embT D τ x ∈ Qbar := by
  rw [mem_algebraicClosure_iff']
  exact (Algebra.IsIntegral.isIntegral x).map (embT D τ).toRatAlgHom

def embQ (D : D7) (τ : D.what₂.Tau) : D.host.E →+* Qbar := (embT D τ).codRestrict Qbar (emb_mem D τ)

theorem lamC_embT (D : D7) (lam : Qbar →+* ℂ_[p]) (τ : D.what₂.Tau) (x : D.host.E) :
    lamC lam (embT D τ x) = lam (embQ D τ x) := by
  unfold lamC
  rw [dif_pos (emb_mem D τ x)]
  rfl

theorem flog_constantCoeff (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    PowerSeries.constantCoeff (flog W wq) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [flog]

theorem subst_subst_X {r : ℕ} (S : Fin r → MvPowerSeries (Fin r) ℂ_[p]) (hS : MvPowerSeries.HasSubst S)
    (f : PowerSeries ℂ_[p]) (i : Fin r) :
    MvPowerSeries.subst S (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin r) ℂ_[p]) f) =
      PowerSeries.subst (S i) f := by
  have hX : MvPowerSeries.HasSubst (fun _ : Unit => (MvPowerSeries.X i : MvPowerSeries (Fin r) ℂ_[p])) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => MvPowerSeries.constantCoeff_X i)
  unfold PowerSeries.subst
  rw [MvPowerSeries.subst_comp_subst_apply hX hS]
  simp only [MvPowerSeries.subst_X hS]

theorem atLog_change (D : D7) {N N' r : ℕ} (lam : Qbar →+* ℂ_[p]) (Λ : AddSubgroup ℂ)
    (C : WeierstrassCurve.VariableChange ℂ_[p]) (wq : PowerSeries ℂ_[p])
    (b b' : Fin r → Matrix (Fin N') (Fin N) D.host.E) (A : Fin r → Fin r → D.host.E)
    (hAK : ∀ i j, A i j ∈ D.host.K) (hb' : ∀ j, b' j = ∑ i, A i j • b i)
    (S : Fin r → MvPowerSeries (Fin r) ℂ_[p]) (hS0 : ∀ i, MvPowerSeries.constantCoeff (S i) = 0)
    (hSl : ∀ i, PowerSeries.subst (S i) (flog (C • wModel lam Λ) wq) =
      ∑ j, algebraMap ℂ_[p] (MvPowerSeries (Fin r) ℂ_[p]) (lamC lam (D.host.φ₀ (A i j))) *
        PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries (Fin r) ℂ_[p]) (flog (C • wModel lam Λ) wq))
    (F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) :
    atLog D lam Λ C wq b' F = MvPowerSeries.subst S (atLog D lam Λ C wq b F) := by
  have hl0 := flog_constantCoeff (C • wModel lam Λ) wq
  have hX : ∀ i, MvPowerSeries.constantCoeff
      (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin r) ℂ_[p]) (flog (C • wModel lam Λ) wq)) = 0 :=
    fun i => PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X i) _ hl0
  have hY : MvPowerSeries.HasSubst (fun k : D.what₂.Tau × Fin N' × Fin N =>
      ∑ i, algebraMap ℂ_[p] (MvPowerSeries (Fin r) ℂ_[p])
          (((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * lamC lam (embT D k.1 (b i k.2.1 k.2.2))) *
        PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin r) ℂ_[p]) (flog (C • wModel lam Λ) wq)) := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero
    intro k
    simp [map_sum, hX]
  have hSs : MvPowerSeries.HasSubst S := MvPowerSeries.hasSubst_of_constantCoeff_zero hS0
  unfold atLog
  simp only []
  rw [MvPowerSeries.subst_comp_subst_apply hY hSs]
  congr 1
  funext k
  rw [← MvPowerSeries.coe_substAlgHom hSs, map_sum]
  simp only [map_mul, AlgHom.commutes, MvPowerSeries.coe_substAlgHom, subst_subst_X S hSs, hSl]
  have hx : ∀ j, lamC lam (embT D k.1 (b' j k.2.1 k.2.2)) =
      ∑ i, lam (embQ D k.1 (A i j)) * lam (embQ D k.1 (b i k.2.1 k.2.2)) := by
    intro j
    rw [lamC_embT, hb' j, Matrix.sum_apply]
    simp only [Matrix.smul_apply, smul_eq_mul, map_sum, map_mul]
  have hy : ∀ i j, lamC lam (D.host.φ₀ (A i j)) = lam (embQ D k.1 (A i j)) := by
    intro i j
    rw [← embT_K D k.1 _ (hAK i j), lamC_embT]
  simp only [hx, hy, lamC_embT, Finset.mul_sum, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [map_mul]
  ring

theorem smul_eq_K (D : D7) {N N' : ℕ} (a : D.host.E) (ha : a ∈ D.host.K) (M : Matrix (Fin N') (Fin N) D.host.E) :
    a • M = (⟨a, ha⟩ : D.host.K) • M := by
  ext i j
  rw [Matrix.smul_apply, Matrix.smul_apply, Algebra.smul_def]
  rfl

theorem exists_coeffs (D : D7) {p N N' : ℕ} (hp : p.Prime)
    {Y : Submodule (𝓞 D.host.E) (Matrix (Fin N') (Fin N) D.host.E)} {r r' : ℕ}
    {b : Fin r → Matrix (Fin N') (Fin N) D.host.E} {b' : Fin r' → Matrix (Fin N') (Fin N) D.host.E}
    (hb : LocBasis D p Y b) (hb' : LocBasis D p Y b') :
    ∃ A : Fin r → Fin r' → D.host.E, (∀ i j, A i j ∈ D.host.K) ∧
      (∀ i j, ∃ s : ℕ, Nat.Coprime s p ∧ ∃ c : 𝓞 D.host.K, (s : D.host.E) * A i j = ((c : D.host.K) : D.host.E)) ∧
      ∀ j, b' j = ∑ i, A i j • b i := by
  choose s1 hs1 hm1 using hb'.2.1
  choose s2 hs2 c hc using fun j => hb.2.2 _ (hm1 j)
  have hcop : ∀ j, Nat.Coprime (s2 j * s1 j) p := fun j => Nat.Coprime.mul (hs2 j) (hs1 j)
  have hn : ∀ j, ((s2 j * s1 j : ℕ) : D.host.E) ≠ 0 := by
    intro j
    have : s2 j * s1 j ≠ 0 := by
      intro h0
      have h := hcop j
      rw [h0, Nat.coprime_zero_left] at h
      exact hp.one_lt.ne' h
    exact_mod_cast this
  refine ⟨fun i j => ((c j i : D.host.K) : D.host.E) / ((s2 j * s1 j : ℕ) : D.host.E), ?_, ?_, ?_⟩
  · intro i j
    exact D.host.K.div_mem (SetLike.coe_mem _) (by push_cast; exact mul_mem (by simp) (by simp))
  · intro i j
    exact ⟨s2 j * s1 j, hcop j, c j i, mul_div_cancel₀ _ (hn j)⟩
  · intro j
    have h := hc j
    rw [smul_smul, ← Nat.cast_mul] at h
    calc b' j = (((s2 j * s1 j : ℕ) : D.host.E))⁻¹ • ((((s2 j * s1 j : ℕ) : D.host.E)) • b' j) := by
          rw [smul_smul, inv_mul_cancel₀ (hn j), one_smul]
      _ = ∑ i, (((c j i : D.host.K) : D.host.E) / ((s2 j * s1 j : ℕ) : D.host.E)) • b i := by
          rw [h, Finset.smul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [smul_smul, div_eq_inv_mul]

theorem card_le (D : D7) {N N' r r' : ℕ} {b : Fin r → Matrix (Fin N') (Fin N) D.host.E}
    {b' : Fin r' → Matrix (Fin N') (Fin N) D.host.E} (A : Fin r → Fin r' → D.host.E)
    (hAK : ∀ i j, A i j ∈ D.host.K) (hli : LinearIndependent D.host.K b') (hb' : ∀ j, b' j = ∑ i, A i j • b i) :
    r' ≤ r := by
  classical
  have hs : Set.range b' ≤ Submodule.span D.host.K (Set.range b) := by
    rintro _ ⟨j, rfl⟩
    rw [hb' j]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [smul_eq_K D (A i j) (hAK i j)]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have h := linearIndependent_le_span' b' hli (Set.range b) hs
  rw [Cardinal.mk_fintype, Fintype.card_fin] at h
  exact (Nat.cast_le.1 h).trans ((Fintype.card_range_le b).trans (Fintype.card_fin r).le)

theorem sum4 {α β γ κ M : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype κ] [AddCommMonoid M]
    (f : α → β → γ → κ → M) : ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ a, ∑ c, ∑ b, ∑ d, f a b c d :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a, ∑ c, ∑ d, ∑ b, f a b c d :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ d, ∑ b, f a b c d := Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := Finset.sum_congr rfl fun c _ => Finset.sum_comm

theorem hYY_comb (D : D7) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (x y : Fin r → D.host.E)
    (hx : ∀ i, x i ∈ D.host.K) (hy : ∀ i, y i ∈ D.host.K) :
    ((hYY D (∑ i, x i • b i) (∑ i, y i • b i) : D.host.K) : D.host.E) =
      ∑ i, ∑ i', x i * D.host.conj (y i') * ((hYY D (b i) (b i') : D.host.K) : D.host.E) := by
  have hk : ∀ i i', x i * D.host.conj (y i') ∈ D.host.K := fun i i' =>
    mul_mem (hx i) (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.G0.conj_mem D ⟨y i', hy i'⟩)
  have e1 : (∑ a, ∑ c, (∑ i, x i • b i) a c * D.host.conj ((∑ i, y i • b i) a c)) =
      ∑ i, ∑ i', (x i * D.host.conj (y i')) * ∑ a, ∑ c, b i a c * D.host.conj (b i' a c) := by
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.sum_mul,
      Finset.mul_sum]
    rw [sum4, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ =>
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    ring
  have e2 : ∀ i i', (x i * D.host.conj (y i')) * ∑ a, ∑ c, b i a c * D.host.conj (b i' a c) =
      (⟨x i * D.host.conj (y i'), hk i i'⟩ : D.host.K) • ∑ a, ∑ c, b i a c * D.host.conj (b i' a c) := by
    intro i i'
    rw [Algebra.smul_def]
    rfl
  unfold hYY
  rw [e1]
  simp only [e2, map_sum, map_smul, smul_eq_mul, IntermediateField.coe_sum, IntermediateField.coe_mul]

theorem orthChange_core : OrthChange := by
  intro D p hp N N' L L' r r' b b' hbL hbO hb'L hb'O
  obtain ⟨A, hAK, hAp, hb'⟩ := exists_coeffs D hp hbL hb'L
  obtain ⟨A', hAK', -, hb⟩ := exists_coeffs D hp hb'L hbL
  have h1 := card_le D A hAK hb'L.1 hb'
  have h2 := card_le D A' hAK' hbL.1 hb
  refine ⟨le_antisymm h1 h2, A, hAK, hAp, ?_, hb'⟩
  intro j j'
  have hbO' : ∀ i i', hYY D (b i) (b i') = if i = i' then 1 else 0 := hbO
  have hb'O' : ∀ i i', hYY D (b' i) (b' i') = if i = i' then 1 else 0 := hb'O
  have h := hYY_comb D b (fun i => A i j) (fun i => A i j') (fun i => hAK i j) (fun i => hAK i j')
  rw [← hb' j, ← hb' j', hb'O' j j'] at h
  simp only [hbO', apply_ite (fun x : D.host.K => (x : D.host.E)), IntermediateField.coe_one,
    IntermediateField.coe_zero, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true] at h
  first
  | exact h.symm
  | (rw [← h]; split_ifs <;> simp)

end IntegralOrthonormalChange

open IntegralOrthonormalChange in

theorem basisInv_of (hO : OrthChange) (hU : UnitSubst) : BasisInv := by
  intro D cc δ hcc hδ p _ hp5 hin lam N N' L L' F hS
  obtain ⟨r, b, hbL, hbO, hI⟩ := hS
  intro C wq r' b' hC hW hb'L hb'O
  obtain ⟨hrr, A, hAK, hAp, hAu, hb'⟩ := hO D p Fact.out N N' L L' r r' b b' hbL hbO hb'L hb'O
  subst hrr
  obtain ⟨S, hS0, hSI, hSl, V, hV, hPV⟩ := hU D cc δ hcc hδ p hp5 hin lam C wq hC hW _ A hAK hAp hAu
  have hSs : MvPowerSeries.HasSubst S := MvPowerSeries.hasSubst_of_constantCoeff_zero hS0
  have key := atLog_change D lam (lamOf D cc δ) C wq b b' A hAK hb' S hS0 hSl F
  show IntegralMv (atLog D lam (lamOf D cc δ) C wq b' F * ePh lam (lamOf D cc δ) C wq _)
  rw [key, hPV, ← mul_assoc, ← MvPowerSeries.subst_mul hSs]
  exact integral_mul (integral_subst S hS0 hSI (hI C wq hC hW)) hV

theorem orthonormal_change_unitary_integral : OrthChange := IntegralOrthonormalChange.orthChange_core

theorem basisInv_of_unitSubst (hU : UnitSubst) : BasisInv := basisInv_of orthonormal_change_unitary_integral hU

end Formalism.L2.KerInert
