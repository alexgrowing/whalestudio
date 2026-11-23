import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeAdelicMatrixIntegralTranslate
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNatSmulMemLattice
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.LatCongImage

variable {E : Type} [Field E] [NumberField E]

def intT (F : Subfield E) : Subring (FiniteAdeleRing (𝓞 F) F ⊗[F] E) :=
  Subring.closure ({x | ∃ a : FiniteAdeleRing (𝓞 F) F, (∀ v, a v ∈ v.adicCompletionIntegers F) ∧ x = a ⊗ₜ[F] (1 : E)} ∪
    {x | ∃ y : 𝓞 E, x = (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (y : E)})

end GlobalTheory.LatCongImage

namespace GlobalTheory.LatCongImage

variable {E : Type} [Field E] [NumberField E]

theorem swap_mem [IsCMField E] (F : Subfield E) (h : F = maximalRealSubfield E) {x : FiniteAdeleRing (𝓞 F) F ⊗[F] E}
    (hx : x ∈ intT F) : swapCast h x ∈ ReciprocityTheory.Aut.ALint E := by
  subst h
  induction hx using Subring.closure_induction with
  | mem y hy =>
    apply Subring.subset_closure
    rcases hy with ⟨a, ha, rfl⟩ | ⟨z, rfl⟩
    · right
      refine ⟨a, ha, ?_⟩
      show (Algebra.TensorProduct.comm _ _ _) (a ⊗ₜ[_] (1 : E)) = _
      rw [Algebra.TensorProduct.comm_tmul]
    · left
      refine ⟨z, ?_⟩
      show (Algebra.TensorProduct.comm _ _ _) ((1 : FiniteAdeleRing _ _) ⊗ₜ[_] (z : E)) = _
      rw [Algebra.TensorProduct.comm_tmul]
  | zero => rw [map_zero]; exact zero_mem _
  | one => rw [map_one]; exact one_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

theorem natCast_eq_tmul (F : Subfield E) (m : ℕ) :
    (m : FiniteAdeleRing (𝓞 F) F ⊗[F] E) = (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (m : E) := by
  rw [Algebra.TensorProduct.natCast_def']

theorem exists_nat_mul_mem (F : Subfield E) (x : FiniteAdeleRing (𝓞 F) F ⊗[F] E) :
    ∃ d : ℕ, 0 < d ∧ (d : FiniteAdeleRing (𝓞 F) F ⊗[F] E) * x ∈ intT F := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨1, one_pos, by simp⟩
  | tmul a e =>
    obtain ⟨d₁, hd₁, ha⟩ := GlobalTheory.AdelicMatLat.exists_nat_mul_mem F a
    obtain ⟨d₂, hd₂, r, hr⟩ := GlobalTheory.AdelicMatLat.exists_nat_denom E e
    refine ⟨d₁ * d₂, Nat.mul_pos hd₁ hd₂, ?_⟩
    have e1 : ((d₁ * d₂ : ℕ) : FiniteAdeleRing (𝓞 F) F ⊗[F] E) * (a ⊗ₜ[F] e) =
        ((d₁ : FiniteAdeleRing (𝓞 F) F) * a) ⊗ₜ[F] (1 : E) * (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (r : E) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, hr, Nat.cast_mul]
      have c1 : (d₁ : FiniteAdeleRing (𝓞 F) F ⊗[F] E) = (d₁ : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (1 : E) :=
        Algebra.TensorProduct.natCast_def _
      have c2 : (d₂ : FiniteAdeleRing (𝓞 F) F ⊗[F] E) = (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (d₂ : E) :=
        Algebra.TensorProduct.natCast_def' _
      rw [c1, c2, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [e1]
    exact mul_mem (Subring.subset_closure (Or.inl ⟨_, ha, rfl⟩)) (Subring.subset_closure (Or.inr ⟨r, rfl⟩))
  | add x y hx hy =>
    obtain ⟨d₁, hd₁, h₁⟩ := hx
    obtain ⟨d₂, hd₂, h₂⟩ := hy
    refine ⟨d₁ * d₂, Nat.mul_pos hd₁ hd₂, ?_⟩
    rw [mul_add, Nat.cast_mul]
    refine add_mem ?_ ?_
    · rw [mul_comm (d₁ : FiniteAdeleRing (𝓞 F) F ⊗[F] E), mul_assoc]
      exact mul_mem (natCast_mem _ _) h₁
    · rw [mul_assoc]
      exact mul_mem (natCast_mem _ _) h₂

theorem exists_nat_denom_family {ι : Type} [Fintype ι] (x : ι → E) :
    ∃ d : ℕ, 0 < d ∧ ∀ i, ∃ r : 𝓞 E, (r : E) = d * x i := by
  classical
  choose d hd r hr using fun i => GlobalTheory.AdelicMatLat.exists_nat_denom E (x i)
  refine ⟨∏ i, d i, Finset.prod_pos fun i _ => hd i, fun i => ⟨((∏ j ∈ Finset.univ.erase i, d j : ℕ) : 𝓞 E) * r i, ?_⟩⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), Nat.cast_mul, mul_assoc, ← hr i]
  push_cast
  rfl

theorem smul_eq {D : D7} (V : HSp D) (s : 𝓞 D.host.E) (w : V.V) : s • w = (s : D.host.E) • w :=
  (algebraMap_smul D.host.E s w).symm

theorem exists_nat_smul_mem_L0 {D : D7} (V : HSp D) (v : V.V) : ∃ d : ℕ, 0 < d ∧ (d : 𝓞 D.host.E) • v ∈ V.L0 := by
  first
  | exact @_root_.GlobalTheory.NatSmulMemLattice.exists_nat_smul_mem_lattice
  | exact _root_.GlobalTheory.NatSmulMemLattice.exists_nat_smul_mem_lattice
  | (apply _root_.GlobalTheory.NatSmulMemLattice.exists_nat_smul_mem_lattice <;> assumption)
  | (intros; apply _root_.GlobalTheory.NatSmulMemLattice.exists_nat_smul_mem_lattice <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NatSmulMemLattice.exists_nat_smul_mem_lattice <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NatSmulMemLattice.exists_nat_smul_mem_lattice ..)

theorem exists_nat_smul_frame {D : D7} (V : HSp D) :
    ∃ d : ℕ, 0 < d ∧ ∀ j, (d : 𝓞 D.host.E) • V.frame j ∈ V.L0 := by
  classical
  choose d hd h using fun j => exists_nat_smul_mem_L0 V (V.frame j)
  refine ⟨∏ j, d j, Finset.prod_pos fun j _ => hd j, fun j => ?_⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j), Nat.cast_mul, mul_smul]
  exact V.L0.smul_mem _ (h j)

theorem exists_single_mem_latHat {D : D7} (V : HSp D) : ∃ d : ℕ, 0 < d ∧
    ∀ j, (Pi.single j (d : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :
      Fin V.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) ∈ Formalism.L2.Pj.latHat V := by
  classical
  obtain ⟨d, hd, h⟩ := exists_nat_smul_frame V
  refine ⟨d, hd, fun j => ?_⟩
  apply AddSubgroup.subset_closure
  refine ⟨1, fun v => ?_, _, h j, ?_⟩
  · exact one_mem _
  · funext i
    rw [smul_eq V, map_smul, V.frame.repr_self, Finsupp.smul_apply]
    by_cases hij : i = j
    · subst hij
      rw [Pi.single_eq_same, Finsupp.single_eq_same, smul_eq_mul, mul_one, natCast_eq_tmul]
      simp
    · rw [Pi.single_eq_of_ne hij]
      simp [Ne.symm hij]

theorem exists_nat_mul_mem_of_latHat {D : D7} (V : HSp D) : ∃ d : ℕ, 0 < d ∧
    ∀ z ∈ Formalism.L2.Pj.latHat V, ∀ i, (d : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) * z i ∈ intT D.host.F := by
  classical
  obtain ⟨S, hS⟩ := V.standardTuple_isLattice.fg
  obtain ⟨d, hd, hr⟩ := exists_nat_denom_family (E := D.host.E)
    (fun p : S × Fin V.rank => V.frame.repr (p.1 : V.V) p.2)
  have hL : ∀ x ∈ V.L0, ∀ i, ∃ r : 𝓞 D.host.E, (r : D.host.E) = d * V.frame.repr x i := by
    intro x hx
    rw [← hS] at hx
    induction hx using Submodule.span_induction with
    | mem x hx => intro i; exact hr (⟨x, hx⟩, i)
    | zero => intro i; exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      intro i
      obtain ⟨a, ha⟩ := hx i
      obtain ⟨b, hb⟩ := hy i
      exact ⟨a + b, by rw [map_add, Finsupp.add_apply, mul_add, ← ha, ← hb]; push_cast; rfl⟩
    | smul c x _ hx =>
      intro i
      obtain ⟨a, ha⟩ := hx i
      refine ⟨c * a, ?_⟩
      rw [smul_eq V, map_smul, Finsupp.smul_apply, smul_eq_mul, ← mul_assoc, mul_comm (d : D.host.E), mul_assoc, ← ha]
      exact map_mul (algebraMap (𝓞 D.host.E) D.host.E) c a
  refine ⟨d, hd, fun z hz => ?_⟩
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hz
    intro i
    obtain ⟨r, hr'⟩ := hL x hx i
    have e : (d : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) * (a ⊗ₜ[D.host.F] V.frame.repr x i) =
        (a ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (r : D.host.E)) := by
      rw [natCast_eq_tmul, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one,
        one_mul, hr']
    rw [e]
    exact mul_mem (Subring.subset_closure (Or.inl ⟨a, ha, rfl⟩)) (Subring.subset_closure (Or.inr ⟨r, rfl⟩))
  | zero => intro i; simp
  | add x y _ _ hx hy => intro i; rw [Pi.add_apply, mul_add]; exact add_mem (hx i) (hy i)
  | neg x _ hx => intro i; rw [Pi.neg_apply, mul_neg]; exact neg_mem (hx i)

theorem exists_nat_mul_mem_family (F : Subfield E) {ι : Type} [Fintype ι] (x : ι → FiniteAdeleRing (𝓞 F) F ⊗[F] E) :
    ∃ d : ℕ, 0 < d ∧ ∀ i, (d : FiniteAdeleRing (𝓞 F) F ⊗[F] E) * x i ∈ intT F := by
  classical
  choose d hd h using fun i => exists_nat_mul_mem F (x i)
  refine ⟨∏ i, d i, Finset.prod_pos fun i _ => hd i, fun i => ?_⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), Nat.cast_mul, mul_assoc]
  exact mul_mem (natCast_mem _ _) (h i)

theorem mul_apply_mem {R : Type} [CommRing R] (S : Subring R) {a b c : ℕ} (A : Matrix (Fin a) (Fin b) R)
    (B : Matrix (Fin b) (Fin c) R) (hA : ∀ i j, A i j ∈ S) (hB : ∀ i j, B i j ∈ S) (i : Fin a) (j : Fin c) :
    (A * B) i j ∈ S := by
  rw [Matrix.mul_apply]
  exact sum_mem fun l _ => mul_mem (hA i l) (hB l j)

theorem natCast_isUnit (F : Subfield E) {m : ℕ} (hm : 0 < m) : IsUnit (m : FiniteAdeleRing (𝓞 F) F ⊗[F] E) := by
  rw [← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F ⊗[F] E))]
  exact (IsUnit.mk0 _ (Nat.cast_ne_zero.2 hm.ne')).map _

end GlobalTheory.LatCongImage

open GlobalTheory.LatCongImage in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem GlobalTheory.LatCongImage.finCong_mem_levN : ∀ (D : D7) (V : HSp D) (n : ℕ) (P : principalLevelFrame.RowPsi V n) (hF : D.host.F = maximalRealSubfield D.host.E), StdFrame hF P → ∀ N : ℕ, 0 < N → ∃ N' : ℕ, 0 < N' ∧ ∀ k ∈ GfC V, GlobalTheory.Member.FinCong V N' k → k ∈ principalLevelFrame.levN P N := by
  intro D V n P hF hstd N hN
  obtain ⟨⟨β, β', hββ', hβ'β, hmat⟩, -⟩ := hstd
  obtain ⟨d₁, hd₁, h₁⟩ := exists_single_mem_latHat V
  obtain ⟨d₂, hd₂, h₂⟩ := exists_nat_mul_mem_of_latHat V
  obtain ⟨d, hd, hβd⟩ := exists_nat_mul_mem_family D.host.F
    (fun p : (Fin V.rank × Fin n) ⊕ (Fin n × Fin V.rank) => Sum.elim (fun q => β q.1 q.2) (fun q => β' q.1 q.2) p)
  refine ⟨N * d ^ 2 * d₁ * d₂, by positivity, ?_⟩
  intro k hk hc
  obtain ⟨κ, rfl⟩ := P.onto k hk
  refine ⟨κ, ?_, rfl⟩
  set M := finMat D.sp.cm.sig V.gram (P.ψ κ) with hM

  have hent : ∀ a b, ∃ y ∈ intT D.host.F,
      (M - 1) a b = ((N * d ^ 2 : ℕ) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) * y := by
    intro a b
    obtain ⟨y, hy, e⟩ := hc _ (h₁ b)
    refine ⟨(d₂ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) * y a, h₂ y hy a, ?_⟩
    have e1 := congrFun e a
    have e2 : (finHom V (P.ψ κ)).1.mulVec (Pi.single b (d₁ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) a -
        (Pi.single b (d₁ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) : Fin V.rank → _) a = (M - 1) a b * d₁ := by
      have hfm : (finHom V (P.ψ κ)).1 = M := rfl
      rw [hfm, Matrix.mulVec_single, Matrix.sub_apply, Matrix.one_apply, Pi.single_apply, sub_mul]
      split_ifs <;> simp
    rw [Pi.sub_apply, e2, Pi.smul_apply, nsmul_eq_mul] at e1
    have hu := natCast_isUnit (E := D.host.E) D.host.F hd₁
    apply hu.mul_left_injective
    simp only
    rw [e1]
    push_cast
    ring
  choose Y hY hYe using hent
  have hmk := hmat κ
  rw [← hM] at hmk
  have hK : κ.1.1.map (swapCast hF).symm - 1 = β' * (M - 1) * β := by
    rw [hmk, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hβ'β]
    congr 1
    rw [show β' * (β * (κ.1.1.map (swapCast hF).symm) * β') * β =
      (β' * β) * (κ.1.1.map (swapCast hF).symm) * (β' * β) by simp only [Matrix.mul_assoc], hβ'β, Matrix.one_mul,
      Matrix.mul_one]
  have hMY : M - 1 = ((N * d ^ 2 : ℕ) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) • Matrix.of Y := by
    ext a b
    rw [hYe a b, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
  have hK2 : ∀ i j, ∃ w ∈ intT D.host.F, (κ.1.1.map (swapCast hF).symm - 1) i j =
      (N : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) * w := by
    intro i j
    refine ⟨(((d : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) • β') * Matrix.of Y *
      ((d : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) • β)) i j, ?_, ?_⟩
    · refine mul_apply_mem _ _ _ (fun a b => mul_apply_mem _ _ _ ?_ ?_ a b) ?_ i j
      · intro a b; simpa using hβd (Sum.inr (a, b))
      · intro a b; exact hY a b
      · intro a b; simpa using hβd (Sum.inl (a, b))
    · rw [hK, hMY]
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
      generalize (β' * Matrix.of Y * β) i j = x
      push_cast
      ring
  have hC : ∀ i j, ∃ y ∈ ReciprocityTheory.Aut.ALint D.host.E,
      (κ.1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL D.host.E)) i j -
        (1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL D.host.E)) i j = (N : ReciprocityTheory.Aut.AL D.host.E) * y := by
    intro i j
    obtain ⟨w, hw, e⟩ := hK2 i j
    refine ⟨swapCast hF w, swap_mem D.host.F hF hw, ?_⟩
    have e' := congrArg (swapCast hF) e
    rw [Matrix.sub_apply, map_sub, Matrix.map_apply, RingEquiv.apply_symm_apply, map_mul, map_natCast] at e'
    rw [← e']
    congr 1
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  refine ⟨?_, hC⟩
  show ∀ i j, (κ.1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL D.host.E)) i j ∈ ReciprocityTheory.Aut.ALint D.host.E
  intro i j
  obtain ⟨y, hy, e⟩ := hC i j
  rw [sub_eq_iff_eq_add] at e
  rw [e]
  refine add_mem (mul_mem (natCast_mem _ _) hy) ?_
  rw [Matrix.one_apply]
  split_ifs
  exacts [one_mem _, zero_mem _]
