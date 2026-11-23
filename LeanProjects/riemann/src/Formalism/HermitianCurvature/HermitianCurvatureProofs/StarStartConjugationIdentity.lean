import Formalism.HermitianCurvature.StatementTL
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RuleGD
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameOfAdmissibleWord

namespace Formalism.FourierDecayAlt.P.TLA.M2

open Matrix Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.TL Formalism.FourierDecayAlt.P.RuleGD

noncomputable section

section

variable {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] {r : ℕ}

theorem star_fns (L : LevelData A r) (hL : IsStarLevel L) :
    star L.ζ = L.ζb ∧ star L.ζb = L.ζ ∧ star L.ζi = L.ζbi ∧ star L.ζbi = L.ζi ∧ star L.GG = L.GG ∧
      star L.GGi = L.GGi := by
  unfold IsStarLevel at hL
  obtain ⟨h1, -, h3⟩ := hL
  have h2 : star L.ζb = L.ζ := by rw [← h1, star_star]
  have h4 : star L.ζi = L.ζbi := by
    calc star L.ζi = star L.ζi * (L.ζb * L.ζbi) := by rw [L.ζb_ζbi, mul_one]
      _ = star (L.ζ * L.ζi) * L.ζbi := by rw [star_mul, h1, mul_assoc]
      _ = L.ζbi := by rw [L.ζ_ζi, star_one, one_mul]
  have h5 : star L.ζbi = L.ζi := by rw [← h4, star_star]
  have h6 : star L.GG = L.GG := by
    rw [L.GG_def, star_sub, star_mul, h1, h2, ← algebraMap_star_comm, h3]
  have h7 : star L.GGi = L.GGi := by
    calc star L.GGi = star L.GGi * (L.GG * L.GGi) := by rw [L.GG_GGi, mul_one]
      _ = star (L.GG * L.GGi) * L.GGi := by rw [star_mul, h6, mul_assoc]
      _ = L.GGi := by rw [L.GG_GGi, star_one, one_mul]
  exact ⟨h1, h2, h4, h5, h6, h7⟩

theorem zfns_fns (L : LevelData A r) {g : A} (hg : g ∈ zfns L) : g ∈ L.fns := by
  unfold LevelData.fns
  exact Set.mem_union_right _ hg

theorem star_zfns (L : LevelData A r) (hL : IsStarLevel L) {g : A} (hg : g ∈ zfns L) : star g ∈ zfns L := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := star_fns L hL
  unfold zfns at *
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [h1, h2, h3, h4, h5, h6]

theorem star_comm_zfns (L : LevelData A r) (hL : IsStarLevel L) {u : A} (hu : ∀ g ∈ zfns L, Commute u g) :
    ∀ g ∈ zfns L, Commute (star u) g := by
  intro g hg
  have hc := (hu (star g) (star_zfns L hL hg)).star_star
  rwa [star_star] at hc

theorem xi_comm {L : LevelData A r} {st : Start A} (h : IsLevelStart L st) {Y : ℂ} (hY : Y ∈ st.inv) {g : A}
    (hg : Commute (st.x Y) g) : Commute (st.xi Y) g := by
  obtain ⟨h1, h2⟩ := h.x_xi Y hY
  show st.xi Y * g = g * st.xi Y
  calc st.xi Y * g = st.xi Y * g * (st.x Y * st.xi Y) := by rw [h1, mul_one]
    _ = st.xi Y * (st.x Y * g) * st.xi Y := by rw [hg.eq]; simp only [mul_assoc]
    _ = st.xi Y * st.x Y * g * st.xi Y := by simp only [mul_assoc]
    _ = g * st.xi Y := by rw [h2, one_mul]

def Cz (st : Start A) (a : A) : Prop := ∀ b ∈ kAlg st, Commute b a

theorem cz_zfns {L : LevelData A r} {st : Start A} (h : IsLevelStart L st) {g : A} (hg : g ∈ zfns L) : Cz st g := by
  unfold Cz kAlg
  intro b hb
  have hle : Algebra.adjoin ℂ ({a | ∃ Y, star Y = Y ∧ a = st.x Y} ∪ {a | ∃ Y ∈ st.inv, star Y = Y ∧ a = st.xi Y}) ≤
      Subalgebra.centralizer ℂ {g} := by
    rw [Algebra.adjoin_le_iff]
    rintro a (⟨Y, -, rfl⟩ | ⟨Y, hY, -, rfl⟩)
    · simp only [SetLike.mem_coe, Subalgebra.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
      exact (h.x_fn Y g hg).eq.symm
    · simp only [SetLike.mem_coe, Subalgebra.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
      exact (xi_comm h hY (h.x_fn Y g hg)).eq.symm
  have hb' := hle hb
  simp only [Subalgebra.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq] at hb'
  exact hb'.symm

theorem cz_mul {st : Start A} {a b : A} (ha : Cz st a) (hb : Cz st b) : Cz st (a * b) := by
  unfold Cz at *
  intro c hc
  exact (ha c hc).mul_right (hb c hc)

theorem cz_smul {st : Start A} {a : A} (z : ℂ) (ha : Cz st a) : Cz st (z • a) := by
  unfold Cz at *
  intro c hc
  exact (ha c hc).smul_right z

theorem star_xi {L : LevelData A r} {st : Start A} (h : IsLevelStart L st) {Y : ℂ} (hr : star Y = Y)
    (hY : Y ∈ st.inv) : star (st.xi Y) = st.xi Y := by
  obtain ⟨h1, -⟩ := h.x_xi Y hY
  have hx := h.x_star Y hr
  calc star (st.xi Y) = star (st.xi Y) * (st.x Y * st.xi Y) := by rw [h1, mul_one]
    _ = star (st.x Y * st.xi Y) * st.xi Y := by rw [star_mul, hx, mul_assoc]
    _ = st.xi Y := by rw [h1, star_one, one_mul]

theorem kAlg_star {L : LevelData A r} {st : Start A} (h : IsLevelStart L st) {a : A} (ha : a ∈ kAlg st) :
    star a ∈ kAlg st := by
  unfold kAlg at *
  let T : Subalgebra ℂ A :=
    { carrier := {b | star b ∈ Algebra.adjoin ℂ ({a | ∃ Y, star Y = Y ∧ a = st.x Y} ∪ {a | ∃ Y ∈ st.inv, star Y = Y ∧ a = st.xi Y})}
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq, star_mul] at hx hy ⊢
        exact Subalgebra.mul_mem _ hy hx
      one_mem' := by
        simp only [Set.mem_setOf_eq, star_one]
        exact Subalgebra.one_mem _
      add_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq, star_add] at hx hy ⊢
        exact Subalgebra.add_mem _ hx hy
      zero_mem' := by
        simp only [Set.mem_setOf_eq, star_zero]
        exact Subalgebra.zero_mem _
      algebraMap_mem' := fun z => by
        simp only [Set.mem_setOf_eq, ← algebraMap_star_comm]
        exact Subalgebra.algebraMap_mem _ _ }
  have hle : Algebra.adjoin ℂ ({a | ∃ Y, star Y = Y ∧ a = st.x Y} ∪ {a | ∃ Y ∈ st.inv, star Y = Y ∧ a = st.xi Y}) ≤ T := by
    rw [Algebra.adjoin_le_iff]
    rintro b (⟨Y, hY, rfl⟩ | ⟨Y, hYi, hY, rfl⟩)
    · change star (st.x Y) ∈ Algebra.adjoin ℂ ({a | ∃ Y, star Y = Y ∧ a = st.x Y} ∪ {a | ∃ Y ∈ st.inv, star Y = Y ∧ a = st.xi Y})
      rw [h.x_star Y hY]
      exact Algebra.subset_adjoin (Set.mem_union_left _ (show st.x Y ∈ {a | ∃ Y, star Y = Y ∧ a = st.x Y} from ⟨Y, hY, rfl⟩))
    · change star (st.xi Y) ∈ Algebra.adjoin ℂ ({a | ∃ Y, star Y = Y ∧ a = st.x Y} ∪ {a | ∃ Y ∈ st.inv, star Y = Y ∧ a = st.xi Y})
      rw [star_xi h hY hYi]
      exact Algebra.subset_adjoin (Set.mem_union_right _ (show st.xi Y ∈ {a | ∃ Y ∈ st.inv, star Y = Y ∧ a = st.xi Y} from ⟨Y, hYi, hY, rfl⟩))
  exact hle ha

variable {S : Type} [Fintype S] [DecidableEq S]

theorem kMat_mul {st : Start A} {M N : SlopeTestRemainingChoices S A} (hM : kMat st M) (hN : kMat st N) : kMat st (M * N) := by
  unfold kMat at *
  intro i j
  rw [Matrix.mul_apply]
  exact Subalgebra.sum_mem _ fun k _ => Subalgebra.mul_mem _ (hM i k) (hN k j)

theorem kMat_one (st : Start A) : kMat st (1 : SlopeTestRemainingChoices S A) := by
  unfold kMat
  intro i j
  rw [Matrix.one_apply]
  split_ifs
  · exact Subalgebra.one_mem _
  · exact Subalgebra.zero_mem _

theorem kMat_smul {st : Start A} (z : ℂ) {M : SlopeTestRemainingChoices S A} (hM : kMat st M) : kMat st (z • M) := by
  unfold kMat at *
  intro i j
  rw [Matrix.smul_apply]
  exact Subalgebra.smul_mem _ (hM i j) z

theorem kMat_star {L : LevelData A r} {st : Start A} (h : IsLevelStart L st) {M : SlopeTestRemainingChoices S A} (hM : kMat st M) :
    kMat st (star M) := by
  unfold kMat at *
  intro i j
  rw [Matrix.star_apply]
  exact kAlg_star h (hM j i)

theorem io_mul (a b : A) : (io (a * b) : SlopeTestRemainingChoices S A) = io a * io b := by
  unfold io
  exact map_mul _ a b

theorem io_add (a b : A) : (io (a + b) : SlopeTestRemainingChoices S A) = io a + io b := by
  unfold io
  exact map_add _ a b

theorem io_sub (a b : A) : (io (a - b) : SlopeTestRemainingChoices S A) = io a - io b := by
  unfold io
  exact map_sub _ a b

theorem io_star (a : A) : star (io a : SlopeTestRemainingChoices S A) = io (star a) := by
  unfold io
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Matrix.star_apply, Matrix.scalar_apply]
  · simp [Matrix.star_apply, Matrix.scalar_apply, Matrix.diagonal_apply, hij, Ne.symm hij]

theorem io_comm {a : A} {M : SlopeTestRemainingChoices S A} (h : ∀ i j, Commute a (M i j)) : Commute (io a) M := by
  unfold io Commute SemiconjBy
  ext i j
  rw [Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  exact (h i j).eq

theorem io_comm_kMat {st : Start A} {a : A} {M : SlopeTestRemainingChoices S A} (hM : kMat st M) (ha : Cz st a) : Commute (io a) M := by
  unfold Cz kMat at *
  exact io_comm fun i j => (ha _ (hM i j)).symm

theorem io_comm_io {a b : A} (h : Commute a b) : Commute (io a : SlopeTestRemainingChoices S A) (io b) := by
  unfold io
  exact h.map _

end

end

section Fn

variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ}

def FC (L : LevelData A r) (a : A) : Prop := ∀ g ∈ L.fns, Commute a g

def FP (L : LevelData A r) (a : A) : Prop := ∀ b, FC L b → Commute b a

theorem fc_fns (L : LevelData A r) {a : A} (ha : a ∈ L.fns) : FC L a := by
  unfold FC
  intro g hg
  exact L.fns_comm a ha g hg
theorem fp_fns (L : LevelData A r) {a : A} (ha : a ∈ L.fns) : FP L a := by
  unfold FP FC
  intro b hb
  exact hb a ha
theorem fc_mul {L : LevelData A r} {a b : A} (ha : FC L a) (hb : FC L b) : FC L (a * b) := by
  unfold FC at *
  intro g hg
  exact (ha g hg).mul_left (hb g hg)
theorem fp_mul {L : LevelData A r} {a b : A} (ha : FP L a) (hb : FP L b) : FP L (a * b) := by
  unfold FP at *
  intro c hc
  exact (ha c hc).mul_right (hb c hc)
theorem fc_smul {L : LevelData A r} (z : ℂ) {a : A} (ha : FC L a) : FC L (z • a) := by
  unfold FC at *
  intro g hg
  exact (ha g hg).smul_left z
theorem fp_smul {L : LevelData A r} (z : ℂ) {a : A} (ha : FP L a) : FP L (z • a) := by
  unfold FP at *
  intro c hc
  exact (ha c hc).smul_right z

theorem fc3 (L : LevelData A r) {a b c : A} (ha : a ∈ L.fns) (hb : b ∈ L.fns) (hc : c ∈ L.fns) : FC L (a * b * c) := fc_mul (fc_mul (fc_fns L ha) (fc_fns L hb)) (fc_fns L hc)
theorem fp3 (L : LevelData A r) {a b c : A} (ha : a ∈ L.fns) (hb : b ∈ L.fns) (hc : c ∈ L.fns) : FP L (a * b * c) := fp_mul (fp_mul (fp_fns L ha) (fp_fns L hb)) (fp_fns L hc)

theorem nabs_wt (L : LevelData A r) :
    L.nabs * (L.ζ * L.ζb * L.GGi) = L.ζ * L.ζb * L.GGi * L.nabs + L.TT • (L.ζ * L.GGi * L.GGi) := by
  have hz : L.ζb * L.ζ = L.ζ * L.ζb := L.fns_comm _ (by simp) _ (by simp)
  have hone : L.GG * L.GGi * L.GGi = L.GGi := by rw [L.GG_GGi, one_mul]
  calc L.nabs * (L.ζ * L.ζb * L.GGi) = L.nabs * L.ζ * L.ζb * L.GGi := by simp only [mul_assoc]
    _ = L.ζ * (L.nabs * L.ζb) * L.GGi := by rw [L.nabs_ζ]; simp only [mul_assoc]
    _ = L.ζ * (L.ζb * L.nabs - 1) * L.GGi := by rw [L.nabs_ζb]
    _ = L.ζ * L.ζb * (L.nabs * L.GGi) - L.ζ * (L.GG * L.GGi * L.GGi) := by rw [hone]; noncomm_ring
    _ = L.ζ * L.ζb * (L.GGi * L.nabs + L.ζ * L.GGi * L.GGi) - L.ζ * (L.GG * L.GGi * L.GGi) := by
          rw [L.nabs_GGi]
    _ = L.ζ * L.ζb * L.GGi * L.nabs + (L.ζ * (L.ζb * L.ζ) - L.ζ * L.GG) * L.GGi * L.GGi := by noncomm_ring
    _ = L.ζ * L.ζb * L.GGi * L.nabs + L.ζ * algebraMap ℂ A L.TT * L.GGi * L.GGi := by
          rw [hz, L.GG_def]; noncomm_ring
    _ = L.ζ * L.ζb * L.GGi * L.nabs + L.TT • (L.ζ * L.GGi * L.GGi) := by
          rw [← Algebra.commutes, ← Algebra.smul_def, smul_mul_assoc, smul_mul_assoc]

theorem wti_wt (L : LevelData A r) : L.GG * L.ζi * L.ζbi * (L.ζ * L.ζb * L.GGi) = 1 := by
  have h : L.ζbi * L.ζ = L.ζ * L.ζbi := L.fns_comm _ (by simp) _ (by simp)
  calc L.GG * L.ζi * L.ζbi * (L.ζ * L.ζb * L.GGi) = L.GG * L.ζi * (L.ζbi * L.ζ) * L.ζb * L.GGi := by
        simp only [mul_assoc]
    _ = L.GG * L.ζi * (L.ζ * L.ζbi) * L.ζb * L.GGi := by rw [h]
    _ = L.GG * (L.ζi * L.ζ) * (L.ζbi * L.ζb) * L.GGi := by simp only [mul_assoc]
    _ = 1 := by rw [L.ζi_ζ, L.ζbi_ζb, mul_one, mul_one, L.GG_GGi]

theorem weight_inverse_identity (L : LevelData A r) : L.GG * L.ζi * L.ζbi * (L.ζ * L.GGi * L.GGi) = L.ζbi * L.GGi := by
  have h : L.ζbi * L.ζ = L.ζ * L.ζbi := L.fns_comm _ (by simp) _ (by simp)
  have h2 : L.GG * L.ζbi = L.ζbi * L.GG := L.fns_comm _ (by simp) _ (by simp)
  calc L.GG * L.ζi * L.ζbi * (L.ζ * L.GGi * L.GGi) = L.GG * L.ζi * (L.ζbi * L.ζ) * L.GGi * L.GGi := by
        simp only [mul_assoc]
    _ = L.GG * L.ζi * (L.ζ * L.ζbi) * L.GGi * L.GGi := by rw [h]
    _ = L.GG * (L.ζi * L.ζ) * L.ζbi * L.GGi * L.GGi := by simp only [mul_assoc]
    _ = L.GG * L.ζbi * L.GGi * L.GGi := by rw [L.ζi_ζ, mul_one]
    _ = L.ζbi * (L.GG * L.GGi) * L.GGi := by rw [h2]; simp only [mul_assoc]
    _ = L.ζbi * L.GGi := by rw [L.GG_GGi, mul_one]

theorem phi_tau (L : LevelData A r) : L.ζ * L.ζbi * L.GGi * (L.TT • L.ζi) = L.TT • (L.ζbi * L.GGi) := by
  have h1 : L.GGi * L.ζi = L.ζi * L.GGi := L.fns_comm _ (by simp) _ (by simp)
  have h2 : L.ζbi * L.ζi = L.ζi * L.ζbi := L.fns_comm _ (by simp) _ (by simp)
  rw [mul_smul_comm]
  congr 1
  calc L.ζ * L.ζbi * L.GGi * L.ζi = L.ζ * L.ζbi * (L.GGi * L.ζi) := by simp only [mul_assoc]
    _ = L.ζ * L.ζbi * (L.ζi * L.GGi) := by rw [h1]
    _ = L.ζ * (L.ζbi * L.ζi) * L.GGi := by simp only [mul_assoc]
    _ = L.ζ * (L.ζi * L.ζbi) * L.GGi := by rw [h2]
    _ = L.ζbi * L.GGi := by rw [← mul_assoc L.ζ, L.ζ_ζi, one_mul]

end Fn

section Span

variable {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] {r : ℕ} {S : Type} [Fintype S]
  [DecidableEq S]

theorem swap3 {R : Type} [Monoid R] {a b c : R} (h1 : Commute b a) (h2 : Commute c a) (h3 : Commute b c) :
    a * (c * b) = b * c * a := by
  rw [← mul_assoc, ← h2.eq, mul_assoc, ← h1.eq, ← mul_assoc, ← h3.eq]

theorem dSpan_le {st : Start A} {X φ τ : SlopeTestRemainingChoices S A} {T : Submodule ℂ (SlopeTestRemainingChoices S A)} (f : SlopeTestRemainingChoices S A → SlopeTestRemainingChoices S A)
    (hadd : ∀ a b, f (a + b) = f a + f b) (hsm : ∀ (z : ℂ) a, ∃ z' : ℂ, f (z • a) = z' • f a)
    (h1 : ∀ α β γ, kMat st α → kMat st β → kMat st γ → f (α * (X * β - β * X) * γ) ∈ T)
    (h2 : ∀ γ, kMat st γ → f (φ * γ) ∈ T) (h3 : ∀ γ, kMat st γ → f (φ * τ * γ) ∈ T)
    {M : SlopeTestRemainingChoices S A} (hM : M ∈ dSpan st X φ τ) : f M ∈ T := by
  unfold dSpan at hM
  induction hM using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨α, β, γ, hα, hβ, hγ, rfl⟩ | ⟨γ, hγ, rfl | rfl⟩
    · exact h1 α β γ hα hβ hγ
    · exact h2 γ hγ
    · exact h3 γ hγ
  | zero =>
    have h := hadd 0 0
    rw [add_zero] at h
    have h0 : f 0 = 0 := by
      calc f 0 = f 0 + f 0 - f 0 := by abel
        _ = f 0 - f 0 := by rw [← h]
        _ = 0 := sub_self _
    rw [h0]
    exact T.zero_mem
  | add x y _ _ hx hy =>
    rw [hadd]
    exact T.add_mem hx hy
  | smul a x _ hx =>
    obtain ⟨z', hz'⟩ := hsm a x
    rw [hz']
    exact T.smul_mem z' hx

theorem g1 {st : Start A} {X φ τ α β γ : SlopeTestRemainingChoices S A} (hα : kMat st α) (hβ : kMat st β) (hγ : kMat st γ) :
    α * (X * β - β * X) * γ ∈ dSpan st X φ τ := by
  unfold dSpan
  exact Submodule.subset_span (Or.inl ⟨α, β, γ, hα, hβ, hγ, rfl⟩)

theorem g2 {st : Start A} {X φ τ γ : SlopeTestRemainingChoices S A} (hγ : kMat st γ) : φ * γ ∈ dSpan st X φ τ := by
  unfold dSpan
  exact Submodule.subset_span (Or.inr ⟨γ, hγ, Or.inl rfl⟩)

theorem g3 {st : Start A} {X φ τ γ : SlopeTestRemainingChoices S A} (hγ : kMat st γ) : φ * τ * γ ∈ dSpan st X φ τ := by
  unfold dSpan
  exact Submodule.subset_span (Or.inr ⟨γ, hγ, Or.inr rfl⟩)

theorem star_kapL (L : LevelData A r) (hL : IsStarLevel L) :
    star (kapL L : SlopeTestRemainingChoices S A) = io (L.ζ * L.ζbi * L.GGi) := by
  obtain ⟨-, h2, h3, -, -, h6⟩ := star_fns L hL
  have hc1 : L.ζbi * L.ζ = L.ζ * L.ζbi := L.fns_comm _ (by simp) _ (by simp)
  have hc2 : L.GGi * L.ζ = L.ζ * L.GGi := L.fns_comm _ (by simp) _ (by simp)
  have hc3 : L.GGi * L.ζbi = L.ζbi * L.GGi := L.fns_comm _ (by simp) _ (by simp)
  unfold kapL
  rw [io_star]
  congr 1
  rw [star_mul, star_mul, h2, h3, h6, hc1, ← mul_assoc, hc2, mul_assoc, hc3, ← mul_assoc]

theorem star_tz (L : LevelData A r) (hL : IsStarLevel L) : star (tz L : SlopeTestRemainingChoices S A) = io (L.TT • L.ζi) := by
  have hL' := hL
  unfold IsStarLevel at hL'
  obtain ⟨-, -, hT⟩ := hL'
  obtain ⟨-, -, -, h4, -, -⟩ := star_fns L hL
  unfold tz
  rw [io_star]
  congr 1
  rw [star_smul, hT, h4]

theorem cz_phi {L : LevelData A r} {st : Start A} (h : IsLevelStart L st) : Cz st (L.ζ * L.ζbi * L.GGi) := by
  have m1 : L.ζ ∈ zfns L := by unfold zfns; simp
  have m2 : L.ζbi ∈ zfns L := by unfold zfns; simp
  have m3 : L.GGi ∈ zfns L := by unfold zfns; simp
  exact cz_mul (cz_mul (cz_zfns h m1) (cz_zfns h m2)) (cz_zfns h m3)

theorem cz_tau {L : LevelData A r} {st : Start A} (h : IsLevelStart L st) : Cz st (L.TT • L.ζi) := by
  have m1 : L.ζi ∈ zfns L := by unfold zfns; simp
  exact cz_smul L.TT (cz_zfns h m1)

theorem comm_phi_tau (L : LevelData A r) :
    Commute (io (L.ζ * L.ζbi * L.GGi) : SlopeTestRemainingChoices S A) (io (L.TT • L.ζi)) := by
  have c1 : Commute L.ζ L.ζi := L.fns_comm _ (by simp) _ (by simp)
  have c2 : Commute L.ζbi L.ζi := L.fns_comm _ (by simp) _ (by simp)
  have c3 : Commute L.GGi L.ζi := L.fns_comm _ (by simp) _ (by simp)
  exact io_comm_io (((c1.mul_left c2).mul_left c3).smul_right L.TT)

theorem star_dSpan {L : LevelData A r} {st : Start A} (hL : IsStarLevel L) (h : IsLevelStart L st)
    {X0 M : SlopeTestRemainingChoices S A} (hM : M ∈ dSpan st X0 (kapL L) (tz L)) :
    star M ∈ dSpan st (star X0) (io (L.ζ * L.ζbi * L.GGi)) (io (L.TT • L.ζi)) := by
  refine dSpan_le (T := dSpan st (star X0) (io (L.ζ * L.ζbi * L.GGi)) (io (L.TT • L.ζi))) star
    (fun a b => star_add a b) (fun z a => ⟨star z, star_smul z a⟩) ?_ ?_ ?_ hM
  · intro α β γ hα hβ hγ
    have e : star (α * (X0 * β - β * X0) * γ) =
        ((-1 : ℂ) • star γ) * (star X0 * star β - star β * star X0) * star α := by
      simp only [star_mul, star_sub, neg_one_smul]
      noncomm_ring
    rw [e]
    exact g1 (kMat_smul (-1) (kMat_star h hγ)) (kMat_star h hβ) (kMat_star h hα)
  · intro γ hγ
    have hc : Commute (io (L.ζ * L.ζbi * L.GGi) : SlopeTestRemainingChoices S A) (star γ) := io_comm_kMat (kMat_star h hγ) (cz_phi h)
    rw [star_mul, star_kapL L hL, ← hc.eq]
    exact g2 (kMat_star h hγ)
  · intro γ hγ
    have hc : Commute (io (L.ζ * L.ζbi * L.GGi) : SlopeTestRemainingChoices S A) (star γ) := io_comm_kMat (kMat_star h hγ) (cz_phi h)
    have hd : Commute (io (L.TT • L.ζi) : SlopeTestRemainingChoices S A) (star γ) := io_comm_kMat (kMat_star h hγ) (cz_tau h)
    rw [star_mul, star_mul, star_kapL L hL, star_tz L hL, swap3 hc hd (comm_phi_tau L)]
    exact g3 (kMat_star h hγ)

theorem conj_dSpan {st : Start A} {X φ τ W Wi s : SlopeTestRemainingChoices S A} (hWW : Wi * W = 1)
    (hk : ∀ M, kMat st M → Commute W M ∧ Commute Wi M ∧ Commute s M)
    (hφ : Commute Wi φ) (hτ : Commute Wi τ)
    (hX : Wi * X * W = X - s) {M : SlopeTestRemainingChoices S A} (hM : M ∈ dSpan st X φ τ) : Wi * M * W ∈ dSpan st X φ τ := by
  refine dSpan_le (T := dSpan st X φ τ) (fun M => Wi * M * W) (fun a b => by simp only [mul_add, add_mul])
    (fun z a => ⟨z, by simp only [mul_smul_comm, smul_mul_assoc]⟩) ?_ ?_ ?_ hM
  · intro α β γ hα hβ hγ
    show Wi * (α * (X * β - β * X) * γ) * W ∈ _
    obtain ⟨-, hWiα, -⟩ := hk α hα
    obtain ⟨hWβ, hWiβ, hsβ⟩ := hk β hβ
    obtain ⟨hWγ, -, -⟩ := hk γ hγ
    have hγW : γ * W = W * γ := hWγ.symm.eq
    have e1 : Wi * (X * β) * W = Wi * X * W * β := by
      rw [← mul_assoc Wi X β, mul_assoc (Wi * X) β W, hWβ.symm.eq, ← mul_assoc]
    have e2 : Wi * (β * X) * W = β * (Wi * X * W) := by
      rw [← mul_assoc Wi β X, hWiβ.eq, mul_assoc β Wi X, mul_assoc β (Wi * X) W]
    have hD : Wi * (X * β - β * X) * W = X * β - β * X := by
      rw [mul_sub, sub_mul, e1, e2, hX, sub_mul, mul_sub, hsβ.eq]; abel
    have e : Wi * (α * (X * β - β * X) * γ) * W = α * (X * β - β * X) * γ := by
      calc Wi * (α * (X * β - β * X) * γ) * W = Wi * α * (X * β - β * X) * (γ * W) := by
            simp only [mul_assoc]
        _ = α * Wi * (X * β - β * X) * (W * γ) := by rw [hWiα.eq, hγW]
        _ = α * (Wi * (X * β - β * X) * W) * γ := by simp only [mul_assoc]
        _ = α * (X * β - β * X) * γ := by rw [hD]
    rw [e]
    exact g1 hα hβ hγ
  · intro γ hγ
    show Wi * (φ * γ) * W ∈ _
    obtain ⟨hWγ, -, -⟩ := hk γ hγ
    have hγW : γ * W = W * γ := hWγ.symm.eq
    have e : Wi * (φ * γ) * W = φ * γ := by
      calc Wi * (φ * γ) * W = Wi * φ * (γ * W) := by simp only [mul_assoc]
        _ = φ * Wi * (W * γ) := by rw [hφ.eq, hγW]
        _ = φ * (Wi * W) * γ := by simp only [mul_assoc]
        _ = φ * γ := by rw [hWW, mul_one]
    rw [e]
    exact g2 hγ
  · intro γ hγ
    show Wi * (φ * τ * γ) * W ∈ _
    obtain ⟨hWγ, -, -⟩ := hk γ hγ
    have hγW : γ * W = W * γ := hWγ.symm.eq
    have e : Wi * (φ * τ * γ) * W = φ * τ * γ := by
      calc Wi * (φ * τ * γ) * W = Wi * φ * τ * (γ * W) := by simp only [mul_assoc]
        _ = φ * Wi * τ * (W * γ) := by rw [hφ.eq, hγW]
        _ = φ * (Wi * τ) * (W * γ) := by simp only [mul_assoc]
        _ = φ * (τ * Wi) * (W * γ) := by rw [hτ.eq]
        _ = φ * τ * (Wi * W) * γ := by simp only [mul_assoc]
        _ = φ * τ * γ := by rw [hWW, mul_one]
    rw [e]
    exact g3 hγ

theorem cconj_dSpan {st : Start A} {X φ τ c ci : SlopeTestRemainingChoices S A} (hc : kMat st c) (hci : kMat st ci)
    (hφ : Commute ci φ) (hτ : Commute ci τ) {M : SlopeTestRemainingChoices S A} (hM : M ∈ dSpan st X φ τ) :
    ci * M * c ∈ dSpan st X φ τ := by
  refine dSpan_le (T := dSpan st X φ τ) (fun M => ci * M * c) (fun a b => by simp only [mul_add, add_mul])
    (fun z a => ⟨z, by simp only [mul_smul_comm, smul_mul_assoc]⟩) ?_ ?_ ?_ hM
  · intro α β γ hα hβ hγ
    show ci * (α * (X * β - β * X) * γ) * c ∈ _
    have e : ci * (α * (X * β - β * X) * γ) * c = ci * α * (X * β - β * X) * (γ * c) := by
      simp only [mul_assoc]
    rw [e]
    exact g1 (kMat_mul hci hα) hβ (kMat_mul hγ hc)
  · intro γ hγ
    show ci * (φ * γ) * c ∈ _
    have e : ci * (φ * γ) * c = φ * (ci * γ * c) := by
      calc ci * (φ * γ) * c = ci * φ * (γ * c) := by simp only [mul_assoc]
        _ = φ * ci * (γ * c) := by rw [hφ.eq]
        _ = φ * (ci * γ * c) := by simp only [mul_assoc]
    rw [e]
    exact g2 (kMat_mul (kMat_mul hci hγ) hc)
  · intro γ hγ
    show ci * (φ * τ * γ) * c ∈ _
    have e : ci * (φ * τ * γ) * c = φ * τ * (ci * γ * c) := by
      calc ci * (φ * τ * γ) * c = ci * φ * τ * (γ * c) := by simp only [mul_assoc]
        _ = φ * (ci * τ) * (γ * c) := by rw [hφ.eq]; simp only [mul_assoc]
        _ = φ * (τ * ci) * (γ * c) := by rw [hτ.eq]
        _ = φ * τ * (ci * γ * c) := by simp only [mul_assoc]
    rw [e]
    exact g3 (kMat_mul (kMat_mul hci hγ) hc)

theorem pow_conj_mem {st : Start A} {X φ τ Wi W : SlopeTestRemainingChoices S A}
    (hstep : ∀ M ∈ dSpan st X φ τ, Wi * M * W ∈ dSpan st X φ τ) (N : ℕ) {M : SlopeTestRemainingChoices S A}
    (hM : M ∈ dSpan st X φ τ) : Wi ^ N * M * W ^ N ∈ dSpan st X φ τ := by
  induction N with
  | zero => simpa using hM
  | succ n ih =>
    have hn := hstep _ ih
    rw [pow_succ', pow_succ]
    simpa [mul_assoc] using hn

theorem pow_conj {Wi W X s : SlopeTestRemainingChoices S A} (hWW : Wi * W = 1) (hs : Commute s W) (hX : Wi * X * W = X - s) (N : ℕ) :
    Wi ^ N * X * W ^ N = X - (N : ℂ) • s := by
  induction N with
  | zero => simp
  | succ n ih =>
    have hs' : Wi * s * W = s := by rw [mul_assoc, hs.eq, ← mul_assoc, hWW, one_mul]
    calc Wi ^ (n + 1) * X * W ^ (n + 1) = Wi * (Wi ^ n * X * W ^ n) * W := by
          rw [pow_succ', pow_succ]; simp only [mul_assoc]
      _ = Wi * (X - (n : ℂ) • s) * W := by rw [ih]
      _ = Wi * X * W - (n : ℂ) • (Wi * s * W) := by
          rw [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc]
      _ = X - ((n + 1 : ℕ) : ℂ) • s := by
          rw [hX, hs']; push_cast; rw [add_smul, one_smul]; abel

end Span

section Main

variable {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] {r : ℕ}

theorem star_start_conjugation_identity (L : LevelData A r) (st : Start A) (hL : IsStarLevel L) (h : IsLevelStart L st) (Y : ℂ) :
    L.GG * L.ζi * L.ζbi * star (L.l0 Y + L.ζb * L.ζi * L.GGi * st.ee Y) * (L.ζ * L.ζb * L.GGi) =
      star (L.l0 Y + L.ζb * L.ζi * L.GGi * st.ee Y) - L.TT • (L.ζbi * L.GGi) := by
  have hL' := hL
  unfold IsStarLevel at hL'
  obtain ⟨-, hnab, -⟩ := hL'
  have mz : ∀ {g : A}, g ∈ zfns L → ∀ x ∈ ({L.ζ, L.ζi, L.ζb, L.ζbi, L.GG, L.GGi} : Set A), Commute x g := by
    intro g hg x hx
    exact L.fns_comm x (Set.mem_union_right _ hx) g (zfns_fns L hg)
  obtain ⟨Q, hQdef⟩ : ∃ Q : A, Q = -(algebraMap ℂ A (Y + 1 / 2) * (L.ζb * L.GGi)) + L.ζb * L.ζi * L.GGi * st.ee Y :=
    ⟨_, rfl⟩
  have hQ : ∀ g ∈ zfns L, Commute Q g := by
    intro g hg
    rw [hQdef]
    refine Commute.add_left (Commute.neg_left ?_) ?_
    · exact (Algebra.commute_algebraMap_left _ _).mul_left ((mz hg _ (by simp)).mul_left (mz hg _ (by simp)))
    · exact (((mz hg _ (by simp)).mul_left (mz hg _ (by simp))).mul_left (mz hg _ (by simp))).mul_left
        (h.ee_fn Y g hg)
  have hsQ := star_comm_zfns L hL hQ
  have hcw : Commute (star Q) (L.ζ * L.ζb * L.GGi) :=
    ((hsQ _ (by unfold zfns; simp)).mul_right (hsQ _ (by unfold zfns; simp))).mul_right (hsQ _ (by unfold zfns; simp))
  have e : L.l0 Y + L.ζb * L.ζi * L.GGi * st.ee Y = -L.nab + Q := by
    rw [hQdef]
    unfold LevelData.l0
    abel
  rw [e, star_add, star_neg, hnab]
  calc L.GG * L.ζi * L.ζbi * (-L.nabs + star Q) * (L.ζ * L.ζb * L.GGi)
      = -(L.GG * L.ζi * L.ζbi * (L.nabs * (L.ζ * L.ζb * L.GGi))) +
          L.GG * L.ζi * L.ζbi * (star Q * (L.ζ * L.ζb * L.GGi)) := by noncomm_ring
    _ = -(L.GG * L.ζi * L.ζbi * (L.ζ * L.ζb * L.GGi * L.nabs + L.TT • (L.ζ * L.GGi * L.GGi))) +
          L.GG * L.ζi * L.ζbi * (L.ζ * L.ζb * L.GGi * star Q) := by rw [nabs_wt L, hcw.eq]
    _ = -(L.GG * L.ζi * L.ζbi * (L.ζ * L.ζb * L.GGi) * L.nabs +
            L.TT • (L.GG * L.ζi * L.ζbi * (L.ζ * L.GGi * L.GGi))) +
          L.GG * L.ζi * L.ζbi * (L.ζ * L.ζb * L.GGi) * star Q := by
          rw [mul_add, mul_smul_comm]; simp only [mul_assoc]
    _ = -L.nabs + star Q - L.TT • (L.ζbi * L.GGi) := by
          rw [wti_wt L, weight_inverse_identity L]; simp only [one_mul]; abel

variable {S : Type} [Fintype S] [DecidableEq S]

theorem frame_l (L : LevelData A r) (st : Start A) (Y : ℂ) :
    (st.frame : FrameData S A).l L Y = io (L.l0 Y + L.ζb * L.ζi * L.GGi * st.ee Y) := by
  show io (L.l0 Y) + kapL L * io (st.ee Y) = io (L.l0 Y + L.ζb * L.ζi * L.GGi * st.ee Y)
  unfold kapL
  rw [io_add, io_mul (L.ζb * L.ζi * L.GGi) (st.ee Y)]

theorem frame_m (L : LevelData A r) (st : Start A) (Y : ℂ) :
    (st.frame : FrameData S A).m L Y = star ((st.frame : FrameData S A).l L (Y - 1)) := by
  unfold FrameData.m FrameData.di FrameData.d
  show 1 * wti L ^ 0 * star ((st.frame : FrameData S A).l L (Y - 1)) * (wt L ^ 0 * 1) = _
  simp only [pow_zero, one_mul, mul_one]

theorem cz3 {L : LevelData A r} {st : Start A} (h : IsLevelStart L st) {a b c : A} (ha : a ∈ zfns L)
    (hb : b ∈ zfns L) (hc : c ∈ zfns L) : Cz st (a * b * c) := cz_mul (cz_mul (cz_zfns h ha) (cz_zfns h hb)) (cz_zfns h hc)

end Main

theorem mShape_of (hLS : LShape) : MShape := by
  intro A S _ _ _ _ _ _ r L st w hL h hA Y hY hr hY1
  obtain ⟨hc, hci, hl⟩ := hLS A S r L st w hL h hA
  have hδ := hl (Y - 1) hY1 (by rw [sub_add_cancel]; exact hY)
  have hfr := Formalism.FourierDecayAlt.P.frame_of_admissible_word A S r L st w hL h hA
  have hcic : (ofWord L st w).ci * (ofWord L st w).c = 1 := hfr.c_ci.2
  have hX0 : star ((st.frame : FrameData S A).l L (Y - 1)) =
      io (star (L.l0 (Y - 1) + L.ζb * L.ζi * L.GGi * st.ee (Y - 1))) := by
    rw [frame_l, io_star]
  have hS := star_dSpan hL h hδ
  rw [hX0] at hS
  have hm0 : (st.frame : FrameData S A).m L Y = io (star (L.l0 (Y - 1) + L.ζb * L.ζi * L.GGi * st.ee (Y - 1))) := by
    rw [frame_m, hX0]
  have hm : (ofWord L st w).m L Y = (ofWord L st w).ci * (wti L ^ (ofWord L st w).N *
        io (star (L.l0 (Y - 1) + L.ζb * L.ζi * L.GGi * st.ee (Y - 1))) * wt L ^ (ofWord L st w).N) *
        (ofWord L st w).c +
      (ofWord L st w).ci * (wti L ^ (ofWord L st w).N *
        star ((ofWord L st w).l L (Y - 1) - (st.frame : FrameData S A).l L (Y - 1)) * wt L ^ (ofWord L st w).N) *
        (ofWord L st w).c := by
    rw [← hX0]
    simp only [FrameData.m, FrameData.di, FrameData.d]
    rw [star_sub]
    noncomm_ring
  have hXc : (wti L : SlopeTestRemainingChoices S A) * io (star (L.l0 (Y - 1) + L.ζb * L.ζi * L.GGi * st.ee (Y - 1))) * wt L =
      io (star (L.l0 (Y - 1) + L.ζb * L.ζi * L.GGi * st.ee (Y - 1))) - io (L.TT • (L.ζbi * L.GGi)) := by
    unfold wti wt
    rw [← io_mul, ← io_mul, star_start_conjugation_identity L st hL h, io_sub]
  have hWW : wti L * wt L = (1 : SlopeTestRemainingChoices S A) := by
    unfold wti wt
    rw [← io_mul, wti_wt]
    exact map_one (Matrix.scalar (Ix S))
  have hk : ∀ M : SlopeTestRemainingChoices S A, kMat st M → Commute (wt L) M ∧ Commute (wti L) M ∧
      Commute (io (L.TT • (L.ζbi * L.GGi))) M := fun M hM =>
    ⟨io_comm_kMat hM (cz3 h (by simp [zfns]) (by simp [zfns]) (by simp [zfns])),
      io_comm_kMat hM (cz3 h (by simp [zfns]) (by simp [zfns]) (by simp [zfns])),
      io_comm_kMat hM (cz_smul _ (cz_mul (cz_zfns h (by simp [zfns])) (cz_zfns h (by simp [zfns]))))⟩
  have hφ : Commute (wti L : SlopeTestRemainingChoices S A) (io (L.ζ * L.ζbi * L.GGi)) :=
    io_comm_io (fp3 L (m_ζ L) (m_ζbi L) (m_GGi L) _ (fc3 L (m_GG L) (m_ζi L) (m_ζbi L)))
  have hτ : Commute (wti L : SlopeTestRemainingChoices S A) (io (L.TT • L.ζi)) :=
    io_comm_io (fp_smul _ (fp_fns L (m_ζi L)) _ (fc3 L (m_GG L) (m_ζi L) (m_ζbi L)))
  have hs : Commute (io (L.TT • (L.ζbi * L.GGi)) : SlopeTestRemainingChoices S A) (wt L) :=
    io_comm_io (fp3 L (m_ζ L) (m_ζb L) (m_GGi L) _ (fc_smul _ (fc_mul (fc_fns L (m_ζbi L)) (fc_fns L (m_GGi L)))))
  have hφc : Commute (ofWord L st w).ci (io (L.ζ * L.ζbi * L.GGi)) := (io_comm_kMat hci (cz_phi h)).symm
  have hτc : Commute (ofWord L st w).ci (io (L.TT • L.ζi)) := (io_comm_kMat hci (cz_tau h)).symm
  have hcs : (ofWord L st w).ci * io (L.TT • (L.ζbi * L.GGi)) * (ofWord L st w).c = io (L.TT • (L.ζbi * L.GGi)) := by
    rw [mul_assoc, (hk _ hc).2.2.eq, ← mul_assoc, hcic, one_mul]
  have hφτ : (io (L.ζ * L.ζbi * L.GGi) : SlopeTestRemainingChoices S A) * io (L.TT • L.ζi) = io (L.TT • (L.ζbi * L.GGi)) := by
    rw [← io_mul, phi_tau]
  rw [hm0, hm]
  generalize (io (star (L.l0 (Y - 1) + L.ζb * L.ζi * L.GGi * st.ee (Y - 1))) : SlopeTestRemainingChoices S A) = X at hS hXc ⊢
  generalize star ((ofWord L st w : FrameData S A).l L (Y - 1) - (st.frame : FrameData S A).l L (Y - 1)) = D at hS ⊢
  generalize (ofWord L st w : FrameData S A).N = N
  have T1 : (ofWord L st w).ci * (wti L ^ N * X * wt L ^ N) * (ofWord L st w).c - X ∈
      dSpan st X (io (L.ζ * L.ζbi * L.GGi)) (io (L.TT • L.ζi)) := by
    rw [pow_conj hWW hs hXc N]
    have e : (ofWord L st w).ci * (X - (N : ℂ) • io (L.TT • (L.ζbi * L.GGi))) * (ofWord L st w).c - X =
        (ofWord L st w).ci * (X * (ofWord L st w).c - (ofWord L st w).c * X) * 1 +
          io (L.ζ * L.ζbi * L.GGi) * io (L.TT • L.ζi) * ((-(N : ℂ)) • 1) := by
      calc (ofWord L st w).ci * (X - (N : ℂ) • io (L.TT • (L.ζbi * L.GGi))) * (ofWord L st w).c - X =
          (ofWord L st w).ci * X * (ofWord L st w).c -
            (N : ℂ) • ((ofWord L st w).ci * io (L.TT • (L.ζbi * L.GGi)) * (ofWord L st w).c) - X := by
            rw [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc]
        _ = (ofWord L st w).ci * X * (ofWord L st w).c - (ofWord L st w).ci * (ofWord L st w).c * X +
            (-(N : ℂ)) • io (L.TT • (L.ζbi * L.GGi)) := by
            rw [hcs, hcic, one_mul, neg_smul]; abel
        _ = _ := by
            rw [hφτ, mul_smul_comm, mul_one, mul_one, mul_sub, ← mul_assoc, ← mul_assoc]
    rw [e]
    exact add_mem (g1 hci hc (kMat_one st)) (g3 (kMat_smul _ (kMat_one st)))
  have T2 : (ofWord L st w).ci * (wti L ^ N * D * wt L ^ N) * (ofWord L st w).c ∈
      dSpan st X (io (L.ζ * L.ζbi * L.GGi)) (io (L.TT • L.ζi)) :=
    cconj_dSpan hc hci hφc hτc (pow_conj_mem (fun M hM => conj_dSpan hWW hk hφ hτ hXc hM) N hS)
  rw [add_sub_right_comm]
  exact add_mem T1 T2

end Formalism.FourierDecayAlt.P.TLA.M2
